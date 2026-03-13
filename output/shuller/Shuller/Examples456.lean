import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic

/-!
# Examples for Chapters 4–6

Concrete demonstrations of manifolds, smooth maps, vector spaces,
and tensor products.
-/

/-! ## Chapter 4: Manifold Examples -/

/-- ℝ is a charted space over itself (trivially a 1-manifold). -/
example : ChartedSpace ℝ ℝ := inferInstance

/-- ℝ is a topological manifold. -/
example : IsManifold (modelWithCornersSelf ℝ ℝ) ℝ := inferInstance

/-- ℝ² is a charted space. -/
example : ChartedSpace (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) :=
  inferInstance

/-- ℝ³ is a topological manifold. -/
example : IsManifold
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
    (EuclideanSpace ℝ (Fin 3)) :=
  inferInstance

/-- Every point of ℝ lies in a chart. -/
example (x : ℝ) : x ∈ (chartAt ℝ x).source := mem_chart_source ℝ x

/-! ## Chapter 5: Smooth Map Examples -/

/-- The identity on ℝ is smooth. -/
example : ContMDiff (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) ⊤ (id : ℝ → ℝ) :=
  contMDiff_id

/-- A constant map ℝ → ℝ is smooth. -/
example : ContMDiff (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) ⊤
    (fun _ : ℝ => (0 : ℝ)) :=
  contMDiff_const

/-- ℝ is a smooth manifold. -/
example : SmoothManifoldWithCorners (modelWithCornersSelf ℝ ℝ) ℝ := inferInstance

/-- ℝ^2 is a smooth manifold. -/
example : SmoothManifoldWithCorners
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
    (EuclideanSpace ℝ (Fin 2)) :=
  inferInstance

/-! ## Chapter 6: Vector Space Examples -/

/-- ℝ³ is a vector space over ℝ. -/
example : Module ℝ (Fin 3 → ℝ) := inferInstance

/-- ℝ² has dimension 2. -/
example : Module.finrank ℝ (Fin 2 → ℝ) = 2 := by simp [Module.finrank_fin_fun]

/-- The standard basis of ℝ². -/
noncomputable example : Basis (Fin 2) ℝ (Fin 2 → ℝ) := Pi.basisFun ℝ (Fin 2)

/-- A linear map ℝ² → ℝ³. -/
example : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
  LinearMap.pi (fun i => LinearMap.proj (R := ℝ) (i % 2))

/-- The dual space of ℝ³. -/
example : Module.Dual ℝ (Fin 3 → ℝ) = ((Fin 3 → ℝ) →ₗ[ℝ] ℝ) := rfl

/-- Tensor product: ℝ² ⊗ ℝ³ contains a nonzero element. -/
example : TensorProduct ℝ (Fin 2 → ℝ) (Fin 3 → ℝ) := 0

/-- Tensor product is bilinear: (v₁ + v₂) ⊗ w = v₁ ⊗ w + v₂ ⊗ w. -/
example (v₁ v₂ : Fin 2 → ℝ) (w : Fin 3 → ℝ) :
    (v₁ + v₂) ⊗ₜ[ℝ] w = v₁ ⊗ₜ[ℝ] w + v₂ ⊗ₜ[ℝ] w :=
  TensorProduct.add_tmul v₁ v₂ w

/-- ℤ is a ℤ-module (abelian group = ℤ-module). -/
example : Module ℤ ℤ := inferInstance

/-- ℤ/2ℤ is a ℤ-module (but has no basis over ℤ — Schuller's point). -/
example : Module ℤ (ZMod 2) := inferInstance

/-- Scalar multiplication in ℝ³. -/
example : (3 : ℝ) • (fun _ : Fin 3 => (1 : ℝ)) = fun _ : Fin 3 => (3 : ℝ) := by
  ext; simp
