import Mathlib.Tactic
import BDDs.BDDTree
import BDDs.ROBDD
import BDDs.Ordered
import BDDs.Reduced

/-!
# Algorithm R: Reduction

Transforms an ordered (unreduced) BDD into an ROBDD by eliminating
redundant nodes and merging duplicates.
Based on Knuth TAOCP 7.1.4 Algorithm R.
-/

namespace BDD

variable {n : ℕ}

/-- Reduce a BDDTree by eliminating redundant nodes (lo = hi)
    and merging semantically equivalent subtrees. -/
def BDDTree.reduce : BDDTree n → BDDTree n
  | .leaf b => .leaf b
  | .node v lo hi =>
    let lo' := lo.reduce
    let hi' := hi.reduce
    if lo' = hi' then lo'
    else .node v lo' hi'

/-- Reduction preserves semantics. -/
theorem BDDTree.reduce_semEq (t : BDDTree n) :
    BDDTree.semEq t t.reduce := by
  intro σ
  induction t with
  | leaf b => rfl
  | node v lo hi ih_lo ih_hi =>
    simp only [BDDTree.reduce]
    split
    · next h =>
      simp only [BDDTree.eval]
      cases σ v <;> simp
      · exact ih_lo
      · have : lo.reduce.eval σ = hi.reduce.eval σ := congrFun (congrArg BDDTree.eval h) σ
        rw [ih_hi, ← this, ← ih_lo]
    · next h =>
      simp only [BDDTree.eval]
      cases σ v <;> simp [ih_lo, ih_hi]

/-- Helper: reduce preserves variable bounds from subtrees. -/
private theorem reduce_preserves_var_bound (t : BDDTree n) (v : Fin n)
    (hord : t.IsOrdered)
    (hbound : ∀ v' lo' hi', t = .node v' lo' hi' → v < v') :
    ∀ v' lo' hi', t.reduce = .node v' lo' hi' → v < v' := by
  intro v' lo' hi' heq
  match t, hord, hbound with
  | .leaf b, _, _ => simp [BDDTree.reduce] at heq
  | .node w tlo thi, hord, hbound =>
    simp only [BDDTree.reduce] at heq
    have hvw : v < w := hbound w tlo thi rfl
    split at heq
    · next h =>
      cases hord with
      | node hlo_bound _ hlo_ord _ =>
        have : ∀ v' lo' hi', tlo = .node v' lo' hi' → w < v' := hlo_bound
        exact reduce_preserves_var_bound tlo v hlo_ord
          (fun v'' lo'' hi'' h' => lt_trans hvw (hlo_bound v'' lo'' hi'' h'))
          v' lo' hi' heq
    · next h =>
      have hinj := BDDTree.node.inj heq
      exact hinj.1 ▸ hvw

/-- Helper: reduce of an ordered tree is ordered. -/
private theorem reduce_isOrdered (t : BDDTree n) (h : t.IsOrdered) :
    t.reduce.IsOrdered := by
  induction t with
  | leaf b => simp [BDDTree.reduce]; exact BDDTree.IsOrdered.leaf b
  | node v lo hi ih_lo ih_hi =>
    cases h with
    | node hlo hhi hlo_ord hhi_ord =>
      simp only [BDDTree.reduce]
      split
      · next heq => exact ih_lo hlo_ord
      · next hne =>
        apply BDDTree.IsOrdered.node
        · exact reduce_preserves_var_bound lo v hlo_ord hlo
        · exact reduce_preserves_var_bound hi v hhi_ord hhi
        · exact ih_lo hlo_ord
        · exact ih_hi hhi_ord

/-- Helper: reduce of an ordered tree is reduced.
    Key insight: if lo.reduce ≠ hi.reduce (DecidableEq), they can't be semEq
    because this reduce function merges structurally equal subtrees,
    and for ordered trees structural equality ↔ semantic equality
    (which is the canonicity theorem). We use a weaker argument:
    the reduce function only skips merging when lo' ≠ hi', and
    semEq of lo.reduce and hi.reduce would require them to be equal
    by the structure of reduce on ordered trees. -/
private theorem reduce_isReduced (t : BDDTree n) (h : t.IsOrdered) :
    t.reduce.IsReduced := by
  induction t with
  | leaf b => simp [BDDTree.reduce]; exact BDDTree.IsReduced.leaf b
  | node v lo hi ih_lo ih_hi =>
    cases h with
    | node hlo hhi hlo_ord hhi_ord =>
      simp only [BDDTree.reduce]
      split
      · next heq => exact ih_lo hlo_ord
      · next hne =>
        apply BDDTree.IsReduced.node
        · -- Need: ¬semEq lo.reduce hi.reduce
          -- This requires canonicity (robdd_canonical) which we haven't proved yet.
          -- For now, we note this is the hard direction and leave it.
          sorry
        · exact ih_lo hlo_ord
        · exact ih_hi hhi_ord

/-- **Reduce produces ROBDD**: reducing an ordered BDDTree yields an ROBDD. -/
theorem reduce_produces_robdd (t : BDDTree n) (h : t.IsOrdered) :
    t.reduce.IsROBDD := by
  exact ⟨reduce_isOrdered t h, reduce_isReduced t h⟩

end BDD
