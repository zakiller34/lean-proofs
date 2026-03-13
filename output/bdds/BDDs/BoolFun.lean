import Mathlib.Tactic

/-!
# Boolean Functions

Core definitions for Boolean functions of `n` variables and the Shannon expansion.
Based on Knuth TAOCP 7.1.4.
-/

namespace BDD

/-- A Boolean function of `n` variables. -/
def BoolFun (n : ℕ) := (Fin n → Bool) → Bool

variable {n : ℕ}

/-- Restrict variable `i` to value `b` in assignment `σ`. -/
def restrict (σ : Fin n → Bool) (i : Fin n) (b : Bool) : Fin n → Bool :=
  fun j => if j = i then b else σ j

/-- Shannon cofactor: fix variable `i` to `b`. -/
def cofactor (f : BoolFun n) (i : Fin n) (b : Bool) : BoolFun n :=
  fun σ => f (restrict σ i b)

/-- Restricting variable `i` to `σ i` is identity. -/
theorem restrict_self (σ : Fin n → Bool) (i : Fin n) :
    restrict σ i (σ i) = σ := by
  ext j; simp only [restrict]
  split
  · next h => rw [h]
  · rfl

/-- Shannon expansion: f = (¬xᵢ ∧ f|_{xᵢ=0}) ∨ (xᵢ ∧ f|_{xᵢ=1}). -/
theorem shannon_expansion (f : BoolFun n) (i : Fin n) (σ : Fin n → Bool) :
    f σ = ((!(σ i) && cofactor f i false σ) || (σ i && cofactor f i true σ)) := by
  unfold cofactor
  cases h : σ i <;> simp
  all_goals (show f σ = f (restrict σ i _); congr 1; rw [← h, restrict_self])

/-- A function is independent of variable `i` if both cofactors agree. -/
def independent (f : BoolFun n) (i : Fin n) : Prop :=
  cofactor f i false = cofactor f i true

end BDD
