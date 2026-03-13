import Mathlib.Tactic
import BDDs.BDDTree
import BDDs.BoolFun

/-!
# Algorithm B: Maximum-Weight Satisfying Assignment

Bottom-up DP on a BDD tree to find the maximum weight among all satisfying
assignments. Weights are real-valued per Knuth TAOCP 7.1.4.
-/

noncomputable section

namespace BDD

variable {n : ℕ}

/-- Weight of an assignment given per-variable weights. -/
def assignmentWeight (w : Fin n → ℝ) (σ : Fin n → Bool) : ℝ :=
  ∑ i : Fin n, if σ i then w i else 0

/-- Bottom-up maximum weight computation on a BDDTree.
    Returns `⊥` if the function is unsatisfiable (all paths lead to false),
    or the max weight among satisfying assignments. -/
def BDDTree.maxWeight (w : Fin n → ℝ) : BDDTree n → WithBot ℝ
  | .leaf true => ↑(0 : ℝ)
  | .leaf false => ⊥
  | .node v lo hi =>
    match lo.maxWeight w, hi.maxWeight w with
    | ⊥, ⊥ => ⊥
    | ⊥, some h_wt => ↑(h_wt + w v)
    | some l_wt, ⊥ => ↑l_wt
    | some l_wt, some h_wt => ↑(max l_wt (h_wt + w v))

/-- The set of satisfying assignments for a BDDTree. -/
def BDDTree.satSet (t : BDDTree n) : Set (Fin n → Bool) :=
  { σ | t.eval σ = true }

/-- maxWeight returns ⊥ iff the function is unsatisfiable. -/
theorem BDDTree.maxWeight_bot_iff_unsat (t : BDDTree n) (w : Fin n → ℝ) :
    t.maxWeight w = ⊥ ↔ t.satSet = ∅ := by
  sorry

/-- Correctness: maxWeight equals the supremum of weights over satisfying assignments. -/
theorem BDDTree.maxWeight_correct (t : BDDTree n) (w : Fin n → ℝ)
    (hsat : t.satSet.Nonempty) :
    ∃ σ ∈ t.satSet, t.maxWeight w = ↑(assignmentWeight w σ) ∧
      ∀ τ ∈ t.satSet, assignmentWeight w τ ≤ assignmentWeight w σ := by
  sorry

end BDD

end
