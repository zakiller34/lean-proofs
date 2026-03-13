import Mathlib.Tactic
import BDDs.BDD
import BDDs.Eval
import BDDs.BoolFun

/-!
# Algorithm C: Count Solutions

Counts the number of satisfying assignments for a BDD.
Bottom-up DP that accounts for skipped variables.
Based on Knuth TAOCP 7.1.4 Algorithm C.
-/

namespace BDD

variable {n : ℕ}

/-- Count the number of satisfying assignments of a BoolFun by brute force. -/
noncomputable def BoolFun.countSat (f : BoolFun n) : ℕ :=
  Finset.card (Finset.univ.filter (fun σ : Fin n → Bool => f σ = true))

/-- Count satisfying assignments via BDD evaluation (specification).
    For each assignment, check if the BDD evaluates to true. -/
noncomputable def ArrayBDD.countSat (bdd : ArrayBDD n) : ℕ :=
  Finset.card (Finset.univ.filter (fun σ : Fin n → Bool => bdd.eval σ = true))

/-- **Algorithm C correctness**: The BDD-based count equals the brute-force count
    for the function represented by the BDD. -/
theorem countSolutions_correct (bdd : ArrayBDD n) (f : BoolFun n)
    (hf : ∀ σ, bdd.eval σ = f σ) :
    bdd.countSat = f.countSat := by
  simp only [ArrayBDD.countSat, BoolFun.countSat]
  congr 1
  ext σ
  simp [hf]

end BDD

