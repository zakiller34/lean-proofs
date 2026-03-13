import Mathlib.Tactic
import BDDs.BDDTree

/-!
# Zero-Suppressed Decision Diagrams (ZDDs)

Stub for Phase 2. ZDDs use a different reduction rule:
a node is suppressed iff its HI branch points to ⊥.
Based on Knuth TAOCP 7.1.4 (Minato).
-/

namespace BDD

/-- A ZDD tree node. Same structure as BDDTree but with different reduction semantics. -/
inductive ZDDTree (n : ℕ) where
  | empty  -- ⊥: represents the empty family
  | unit   -- ⊤: represents the family {∅}
  | node (v : Fin n) (lo hi : ZDDTree n)
  deriving Repr, DecidableEq

namespace ZDDTree

variable {n : ℕ}

/-- Evaluate a ZDD: returns the family of sets it represents.
    A path to ⊤ defines a set containing exactly the variables
    whose nodes were exited via HI. -/
def families : ZDDTree n → Finset (Finset (Fin n))
  | .empty => ∅
  | .unit => {∅}
  | .node v lo hi =>
    lo.families ∪ (hi.families.image (insert v))

/-- ZDD reduction rule: suppress nodes where HI = ⊥. -/
def isZReduced : ZDDTree n → Prop
  | .empty => True
  | .unit => True
  | .node _ lo hi => hi ≠ .empty ∧ isZReduced lo ∧ isZReduced hi

/-- ZDD ordering: variables along any path are strictly ascending. -/
inductive IsOrdered : ZDDTree n → Prop where
  | empty : IsOrdered .empty
  | unit : IsOrdered .unit
  | node : ∀ {v : Fin n} {lo hi : ZDDTree n},
      (∀ v' lo' hi', lo = .node v' lo' hi' → v < v') →
      (∀ v' lo' hi', hi = .node v' lo' hi' → v < v') →
      IsOrdered lo → IsOrdered hi →
      IsOrdered (.node v lo hi)

/-- Size of a ZDD tree (for termination). -/
def size : ZDDTree n → ℕ
  | .empty => 0
  | .unit => 0
  | .node _ lo hi => 1 + lo.size + hi.size

/-- Union of two ZDD families. -/
def union : ZDDTree n → ZDDTree n → ZDDTree n
  | .empty, t => t
  | t, .empty => t
  | .unit, .unit => .unit
  | .unit, .node v lo hi => .node v (union .unit lo) hi
  | .node v lo hi, .unit => .node v (union lo .unit) hi
  | .node v₁ lo₁ hi₁, .node v₂ lo₂ hi₂ =>
    if v₁ < v₂ then
      .node v₁ (union lo₁ (.node v₂ lo₂ hi₂)) hi₁
    else if v₂ < v₁ then
      .node v₂ (union (.node v₁ lo₁ hi₁) lo₂) hi₂
    else -- v₁ = v₂
      .node v₁ (union lo₁ lo₂) (union hi₁ hi₂)
termination_by t₁ t₂ => t₁.size + t₂.size
decreasing_by all_goals (simp only [size]; omega)

/-- Intersection of two ZDD families. -/
def inter : ZDDTree n → ZDDTree n → ZDDTree n
  | .empty, _ => .empty
  | _, .empty => .empty
  | .unit, .unit => .unit
  | .unit, .node _ lo _ => inter .unit lo
  | .node _ lo _, .unit => inter lo .unit
  | .node v₁ lo₁ hi₁, .node v₂ lo₂ hi₂ =>
    if v₁ < v₂ then
      inter lo₁ (.node v₂ lo₂ hi₂)
    else if v₂ < v₁ then
      inter (.node v₁ lo₁ hi₁) lo₂
    else
      let lo' := inter lo₁ lo₂
      let hi' := inter hi₁ hi₂
      if hi' = .empty then lo'
      else .node v₁ lo' hi'
termination_by t₁ t₂ => t₁.size + t₂.size
decreasing_by all_goals (simp only [size]; omega)

/-- Difference of two ZDD families. -/
def diff : ZDDTree n → ZDDTree n → ZDDTree n
  | .empty, _ => .empty
  | t, .empty => t
  | .unit, .unit => .empty
  | .unit, .node _ lo _ => diff .unit lo
  | .node v lo hi, .unit => .node v (diff lo .unit) hi
  | .node v₁ lo₁ hi₁, .node v₂ lo₂ hi₂ =>
    if v₁ < v₂ then
      .node v₁ (diff lo₁ (.node v₂ lo₂ hi₂)) hi₁
    else if v₂ < v₁ then
      diff (.node v₁ lo₁ hi₁) lo₂
    else
      let lo' := diff lo₁ lo₂
      let hi' := diff hi₁ hi₂
      if hi' = .empty then lo'
      else .node v₁ lo' hi'
termination_by t₁ t₂ => t₁.size + t₂.size
decreasing_by all_goals (simp only [size]; omega)

/-- Union correctness. -/
theorem union_correct (t₁ t₂ : ZDDTree n) :
    (union t₁ t₂).families = t₁.families ∪ t₂.families := by
  sorry

/-- Intersection correctness. -/
theorem inter_correct (t₁ t₂ : ZDDTree n) :
    (inter t₁ t₂).families = t₁.families ∩ t₂.families := by
  sorry

/-- Difference correctness. -/
theorem diff_correct (t₁ t₂ : ZDDTree n) :
    (diff t₁ t₂).families = t₁.families \ t₂.families := by
  sorry

end ZDDTree

end BDD

