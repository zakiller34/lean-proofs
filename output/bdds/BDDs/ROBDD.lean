import Mathlib.Tactic
import BDDs.BoolFun
import BDDs.BDDTree
import BDDs.Ordered
import BDDs.Reduced

/-!
# Reduced Ordered BDD (ROBDD)

The ROBDD combining both ordered and reduced invariants, plus the
canonicity theorem (the main result: ROBDDs are canonical forms).
Based on Knuth TAOCP 7.1.4.
-/

namespace BDD

variable {n : ℕ}

/-- A BDDTree is an ROBDD if it is both ordered and reduced. -/
def BDDTree.IsROBDD (t : BDDTree n) : Prop :=
  t.IsOrdered ∧ t.IsReduced

/-- **Canonicity Theorem**: Two ROBDDs representing the same Boolean function
    are structurally equal.
    This is the fundamental theorem of BDDs (Bryant 1986). -/
theorem robdd_canonical (t₁ t₂ : BDDTree n)
    (h₁ : t₁.IsROBDD) (h₂ : t₂.IsROBDD)
    (heq : BDDTree.semEq t₁ t₂) : t₁ = t₂ := by
  sorry

/-- Corollary: ROBDD size is a function of the Boolean function alone. -/
theorem robdd_size_unique (t₁ t₂ : BDDTree n)
    (h₁ : t₁.IsROBDD) (h₂ : t₂.IsROBDD)
    (heq : BDDTree.semEq t₁ t₂) : t₁.size = t₂.size := by
  rw [robdd_canonical t₁ t₂ h₁ h₂ heq]

end BDD
