import Mathlib.Tactic
import BDDs.BDDTree
import BDDs.AlgorithmS

/-!
# BDD Quantification

Single-variable quantification (restriction, existential, universal)
for BDD trees. Based on Knuth TAOCP 7.1.4.
-/

namespace BDD

variable {n : ℕ}

/-- Restrict variable `v` to constant `b` in a BDD tree (cofactor). -/
def BDDTree.restrictVar (v : Fin n) (b : Bool) : BDDTree n → BDDTree n
  | .leaf val => .leaf val
  | .node w lo hi =>
    if w = v then
      if b then hi.restrictVar v b else lo.restrictVar v b
    else
      .node w (lo.restrictVar v b) (hi.restrictVar v b)

/-- Restriction correctness: restricting v to b gives the same result
    as evaluating with σ[v↦b]. -/
theorem BDDTree.restrictVar_correct (t : BDDTree n) (v : Fin n) (b : Bool)
    (σ : Fin n → Bool) :
    (t.restrictVar v b).eval σ = t.eval (Function.update σ v b) := by
  induction t with
  | leaf val => simp [restrictVar, eval]
  | node w lo hi ih_lo ih_hi =>
    simp only [restrictVar]
    split
    · next heq =>
      subst heq
      simp only [eval, Function.update_self]
      cases b <;> simp [ih_lo, ih_hi]
    · next hne =>
      simp only [eval]
      rw [Function.update_of_ne (Ne.symm hne)]
      cases σ w <;> simp [ih_lo, ih_hi]

/-- Existential quantification: ∃ v. f(v). -/
def BDDTree.exists (v : Fin n) (t : BDDTree n) : BDDTree n :=
  BDDTree.apply (· || ·) (t.restrictVar v false) (t.restrictVar v true)

/-- Universal quantification: ∀ v. f(v). -/
def BDDTree.forall (v : Fin n) (t : BDDTree n) : BDDTree n :=
  BDDTree.apply (· && ·) (t.restrictVar v false) (t.restrictVar v true)

/-- Existential quantification correctness. -/
theorem BDDTree.exists_correct (t : BDDTree n) (v : Fin n) (σ : Fin n → Bool) :
    (t.exists v).eval σ =
      (t.eval (Function.update σ v false) || t.eval (Function.update σ v true)) := by
  simp only [BDDTree.exists]
  rw [BDDTree.apply_correct]
  rw [BDDTree.restrictVar_correct, BDDTree.restrictVar_correct]

/-- Universal quantification correctness. -/
theorem BDDTree.forall_correct (t : BDDTree n) (v : Fin n) (σ : Fin n → Bool) :
    (t.forall v).eval σ =
      (t.eval (Function.update σ v false) && t.eval (Function.update σ v true)) := by
  simp only [BDDTree.forall]
  rw [BDDTree.apply_correct]
  rw [BDDTree.restrictVar_correct, BDDTree.restrictVar_correct]

end BDD
