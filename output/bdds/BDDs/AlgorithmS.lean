import Mathlib.Tactic
import BDDs.BDDTree
import BDDs.BoolFun

/-!
# Algorithm S: Synthesis (Apply)

Combines two BDDs using a binary Boolean operator (AND, OR, XOR, etc.).
Based on Knuth TAOCP 7.1.4 Algorithm S.
-/

namespace BDD

variable {n : ℕ}

/-- A binary Boolean operator represented as a function. -/
abbrev BinOp := Bool → Bool → Bool

/-- Synthesize (apply) a binary operator to two BDD trees. -/
def BDDTree.apply (op : BinOp) (t₁ t₂ : BDDTree n) : BDDTree n :=
  match t₁, t₂ with
  | .leaf a, .leaf b => .leaf (op a b)
  | .leaf a, .node v lo hi => .node v (BDDTree.apply op (.leaf a) lo) (BDDTree.apply op (.leaf a) hi)
  | .node v lo hi, .leaf b => .node v (BDDTree.apply op lo (.leaf b)) (BDDTree.apply op hi (.leaf b))
  | .node v₁ lo₁ hi₁, .node v₂ lo₂ hi₂ =>
    if v₁ < v₂ then
      .node v₁ (BDDTree.apply op lo₁ (.node v₂ lo₂ hi₂)) (BDDTree.apply op hi₁ (.node v₂ lo₂ hi₂))
    else if v₂ < v₁ then
      .node v₂ (BDDTree.apply op (.node v₁ lo₁ hi₁) lo₂) (BDDTree.apply op (.node v₁ lo₁ hi₁) hi₂)
    else -- v₁ = v₂
      .node v₁ (BDDTree.apply op lo₁ lo₂) (BDDTree.apply op hi₁ hi₂)
termination_by t₁.size + t₂.size
decreasing_by all_goals (simp only [BDDTree.size]; omega)

/-- **Synthesis correctness**: applying op to two trees produces a tree
    that evaluates as the pointwise application of op. -/
theorem BDDTree.apply_correct (op : BinOp) (t₁ t₂ : BDDTree n) (σ : Fin n → Bool) :
    (BDDTree.apply op t₁ t₂).eval σ = op (t₁.eval σ) (t₂.eval σ) := by
  induction t₁, t₂ using BDDTree.apply.induct (op := op) with
  | case1 a b => simp [BDDTree.apply, eval]
  | case2 a v lo hi ih_lo ih_hi =>
    simp only [BDDTree.apply, eval]
    split <;> simp only [] <;> assumption
  | case3 v lo hi b ih_lo ih_hi =>
    simp only [BDDTree.apply, eval]
    split <;> simp only [] <;> assumption
  | case4 v₁ lo₁ hi₁ v₂ lo₂ hi₂ hlt ih_lo ih_hi =>
    simp only [BDDTree.apply, eval, hlt, ite_true]
    split <;> simp only [] <;> assumption
  | case5 v₁ lo₁ hi₁ v₂ lo₂ hi₂ hlt₁ hlt₂ ih_lo ih_hi =>
    simp only [BDDTree.apply, eval, hlt₁, ite_false, hlt₂, ite_true]
    split <;> simp only [] <;> assumption
  | case6 v₁ lo₁ hi₁ v₂ lo₂ hi₂ hlt₁ hlt₂ ih_lo ih_hi =>
    have heq : v₁ = v₂ := by omega
    subst heq
    simp only [BDDTree.apply, eval, hlt₁, ite_false, hlt₂]
    split <;> simp only [] <;> assumption

/-- BDD AND. -/
def BDDTree.and (t₁ t₂ : BDDTree n) : BDDTree n := t₁.apply (· && ·) t₂

/-- BDD OR. -/
def BDDTree.or (t₁ t₂ : BDDTree n) : BDDTree n := t₁.apply (· || ·) t₂

/-- BDD XOR. -/
def BDDTree.xor (t₁ t₂ : BDDTree n) : BDDTree n := t₁.apply (· ^^ ·) t₂

/-- BDD NOT. -/
def BDDTree.not : BDDTree n → BDDTree n
  | .leaf b => .leaf (!b)
  | .node v lo hi => .node v lo.not hi.not

/-- NOT correctness. -/
theorem BDDTree.not_correct (t : BDDTree n) (σ : Fin n → Bool) :
    t.not.eval σ = !(t.eval σ) := by
  induction t with
  | leaf b => simp [BDDTree.not, eval]
  | node v lo hi ih_lo ih_hi =>
    simp [BDDTree.not, eval]
    cases σ v <;> simp [ih_lo, ih_hi]

end BDD

