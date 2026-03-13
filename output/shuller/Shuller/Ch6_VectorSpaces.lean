import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic

/-!
# Chapter 6: Vector Spaces and Modules

Schuller distinguishes vector spaces (modules over a field) from
general modules (over a ring). Key results: every vector space has a
basis (requires AC), modules over rings need not. Dual spaces and
tensor products prepare for tensor calculus.
-/

/-! ## Fields

A field is a commutative division ring. ℝ and ℂ are the main examples. -/

/-- ℝ is a field. -/
theorem real_is_field : Field ℝ := inferInstance

/-- ℚ is a field. -/
theorem rat_is_field : Field ℚ := inferInstance

/-! ## Vector Spaces = Modules over a Field

In Mathlib, a vector space over K is `Module K V` where K is a `Field`. -/

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- A vector space is a module: scalar multiplication distributes over addition. -/
theorem smul_add_dist (a : K) (v w : V) : a • (v + w) = a • v + a • w :=
  smul_add a v w

/-- Scalar multiplication is associative with field multiplication. -/
theorem smul_assoc_field (a b : K) (v : V) : (a * b) • v = a • (b • v) :=
  mul_smul a b v

/-- One acts as identity for scalar multiplication. -/
theorem one_smul_vec (v : V) : (1 : K) • v = v :=
  one_smul K v

/-! ## Subspaces

A subspace is a `Submodule K V`. -/

/-- The zero subspace {0} is a subspace. -/
theorem bot_is_subspace : (⊥ : Submodule K V) = ⊥ := rfl

/-- The whole space V is a subspace. -/
theorem top_is_subspace : (⊤ : Submodule K V) = ⊤ := rfl

/-! ## Linear Maps

A linear map preserves addition and scalar multiplication. -/

/-- A linear map preserves addition. -/
theorem linear_map_add {W : Type*} [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (v w : V) : f (v + w) = f v + f w :=
  f.map_add v w

/-- A linear map preserves scalar multiplication. -/
theorem linear_map_smul {W : Type*} [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (a : K) (v : V) : f (a • v) = a • f v :=
  f.map_smul a v

/-! ## Basis and Dimension

Every vector space has a basis (requires Axiom of Choice). -/

/-- Every vector space over a division ring has a basis.
    This is Schuller's key theorem distinguishing vector spaces from modules. -/
noncomputable def vector_space_basis : Basis (Basis.ofVectorSpaceIndex K V) K V :=
  Basis.ofVectorSpace K V

/-- The dimension of ℝ^n is n. -/
theorem finrank_fin_fun (n : ℕ) : Module.finrank ℝ (Fin n → ℝ) = n := by
  simp [Module.finrank_fin_fun]

/-! ## Dual Space

The dual space V* = Hom(V, K) is the space of linear functionals. -/

/-- The dual space of V is the space of K-linear maps V → K. -/
theorem dual_def : Module.Dual K V = (V →ₗ[K] K) := rfl

/-! ## Modules over Rings (Not Fields)

Schuller emphasizes: modules over rings need not have bases.
ℤ-modules are abelian groups; ℤ/2ℤ as a ℤ-module has no basis. -/

/-- ℤ is a module over itself. -/
theorem int_self_module : Module ℤ ℤ := inferInstance

/-- Every abelian group is a ℤ-module. -/
theorem abelian_group_is_Z_module {G : Type*} [AddCommGroup G] : Module ℤ G :=
  inferInstance

/-! ## Tensor Products

The tensor product V ⊗ W is the universal bilinear construction. -/

variable {W : Type*} [AddCommGroup W] [Module K W]

/-- Tensor product is defined for K-modules. -/
theorem tensor_product_exists : Nonempty (TensorProduct K V W) := by
  exact ⟨0⟩

/-- The tensor product map is bilinear. -/
theorem tmul_add_right (v : V) (w₁ w₂ : W) :
    v ⊗ₜ[K] (w₁ + w₂) = v ⊗ₜ[K] w₁ + v ⊗ₜ[K] w₂ :=
  TensorProduct.tmul_add v w₁ w₂

/-- The tensor product map respects scalar multiplication. -/
theorem smul_tmul_left (a : K) (v : V) (w : W) :
    (a • v) ⊗ₜ[K] w = a • (v ⊗ₜ[K] w) := by
  rw [TensorProduct.smul_tmul']

/-! ## Concrete Example: ℝ^n

ℝ^n modeled as `Fin n → ℝ` is a finite-dimensional vector space. -/

/-- ℝ^n has a standard basis. -/
noncomputable def std_basis_Rn (n : ℕ) : Basis (Fin n) ℝ (Fin n → ℝ) :=
  Pi.basisFun ℝ (Fin n)
