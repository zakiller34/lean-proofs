import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic

/-!
# Chapter 7: Tensors

Schuller defines (p,q)-tensors as multilinear maps
V* × ⋯ × V* × V × ⋯ × V → K. Key constructions: dual space V*,
tensor product V ⊗ W, alternating maps, and the exterior algebra ΛV.
The determinant is defined intrinsically via the top exterior power.
-/

/-! ## Dual Space Recap

V* = Hom(V, K) — the space of linear functionals. -/

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- The dual space is the space of K-linear maps V → K. -/
theorem dual_is_linear_maps : Module.Dual K V = (V →ₗ[K] K) := rfl

/-! ## Multilinear Maps

A multilinear map is linear in each argument separately. -/

variable {ι : Type*} [DecidableEq ι]

/-- A multilinear map preserves addition in each slot. -/
theorem multilinear_map_add {M : ι → Type*} [∀ i, AddCommMonoid (M i)]
    [∀ i, Module K (M i)] {N : Type*} [AddCommMonoid N] [Module K N]
    (f : MultilinearMap K M N) (m : ∀ i, M i) (i : ι) (x y : M i) :
    f (Function.update m i (x + y)) = f (Function.update m i x) + f (Function.update m i y) :=
  f.map_update_add m i x y

/-- A multilinear map preserves scalar multiplication in each slot. -/
theorem multilinear_map_smul {M : ι → Type*} [∀ i, AddCommMonoid (M i)]
    [∀ i, Module K (M i)] {N : Type*} [AddCommMonoid N] [Module K N]
    (f : MultilinearMap K M N) (m : ∀ i, M i) (i : ι) (c : K) (x : M i) :
    f (Function.update m i (c • x)) = c • f (Function.update m i x) :=
  f.map_update_smul m i c x

/-! ## (p,q)-Tensors

A (p,q)-tensor over V is a multilinear map taking p covectors and q vectors
and producing a scalar. We model this as a multilinear map on
a product of copies of V* and V. -/

/-- Type of (p,0)-tensors: multilinear maps V^p → K (covariant tensors). -/
def CovariantTensor (K : Type*) [CommSemiring K] (V : Type*) [AddCommMonoid V]
    [Module K V] (p : ℕ) : Type _ :=
  MultilinearMap K (fun _ : Fin p => V) K

/-- Type of (0,q)-tensors: multilinear maps (V*)^q → K (contravariant tensors). -/
def ContravariantTensor (K : Type*) [CommSemiring K] (V : Type*) [AddCommMonoid V]
    [Module K V] (q : ℕ) : Type _ :=
  MultilinearMap K (fun _ : Fin q => Module.Dual K V) K

/-! ## Alternating Maps

An alternating map vanishes when two arguments are equal.
This captures antisymmetric tensors (needed for differential forms). -/

/-- An alternating map vanishes when two inputs are equal. -/
theorem alternating_vanishes_on_equal {n : ℕ}
    (f : AlternatingMap K V K (Fin n)) (v : Fin n → V)
    (i j : Fin n) (hij : i ≠ j) (heq : v i = v j) :
    f v = 0 :=
  f.map_eq_zero_of_eq v heq hij

/-- An alternating map is a multilinear map (coercion). -/
theorem alternating_is_multilinear {n : ℕ}
    (f : AlternatingMap K V K (Fin n)) :
    ∃ g : MultilinearMap K (fun _ : Fin n => V) K, ∀ x, g x = f x :=
  ⟨f.toMultilinearMap, fun _ => rfl⟩

/-! ## Exterior Algebra

The exterior algebra ΛV is the quotient of the tensor algebra by
v ⊗ v = 0. It captures alternating tensors algebraically. -/

/-- The canonical injection V → ΛV. -/
noncomputable def exterior_ι : V →ₗ[K] ExteriorAlgebra K V :=
  ExteriorAlgebra.ι K

/-- In the exterior algebra, v ∧ v = 0 for all v. -/
theorem exterior_sq_zero (v : V) :
    ExteriorAlgebra.ι K v * ExteriorAlgebra.ι K v = 0 :=
  ExteriorAlgebra.ι_sq_zero v

/-- The exterior algebra is a graded algebra: ΛV = ⊕ₙ Λⁿ V. -/
noncomputable example : GradedAlgebra (fun i : ℕ => ⋀[K]^i V) :=
  ExteriorAlgebra.gradedAlgebra K V

/-! ## Tensor Product Universal Property

The tensor product V ⊗ W is characterized by a universal property:
bilinear maps V × W → N factor uniquely through V ⊗ W. -/

variable {W : Type*} [AddCommGroup W] [Module K W]

/-- The universal property: bilinear maps factor through the tensor product. -/
noncomputable def tensor_lift {N : Type*} [AddCommMonoid N] [Module K N]
    (f : V →ₗ[K] W →ₗ[K] N) : TensorProduct K V W →ₗ[K] N :=
  TensorProduct.lift f

/-- Tensor product is bilinear: distributes over addition in the left slot. -/
theorem tmul_add_left (v₁ v₂ : V) (w : W) :
    (v₁ + v₂) ⊗ₜ[K] w = v₁ ⊗ₜ[K] w + v₂ ⊗ₜ[K] w :=
  TensorProduct.add_tmul v₁ v₂ w
