import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Tactic

/-!
# Chapter 5: Differentiable Structures

Schuller refines the atlas to enable calculus. A C^k-atlas has
transition maps that are k-times differentiable. A smooth manifold
uses a C^∞-atlas. In Mathlib, `SmoothManifoldWithCorners` and
`contDiffGroupoid` model this.
-/

/-! ## Smooth Manifolds

A smooth manifold is a charted space whose atlas belongs to the
`contDiffGroupoid ∞` structure groupoid — all chart transitions are C^∞. -/

/-- ℝ is a smooth manifold. -/
theorem real_smooth_manifold :
    SmoothManifoldWithCorners (modelWithCornersSelf ℝ ℝ) ℝ :=
  inferInstance

/-- ℝ^n is a smooth manifold for any n. -/
theorem euclidean_smooth_manifold (n : ℕ) :
    SmoothManifoldWithCorners
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (EuclideanSpace ℝ (Fin n)) :=
  inferInstance

/-! ## Smooth Maps

A map f : M → N between smooth manifolds is smooth (C^∞) if its coordinate
representations are smooth. In Mathlib: `ContMDiff I J ⊤ f`. -/

/-- The identity map is smooth. -/
theorem smooth_id {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]
    [SmoothManifoldWithCorners (modelWithCornersSelf ℝ ℝ) M]
    {I : ModelWithCorners ℝ ℝ} :
    ContMDiff I I ⊤ (id : M → M) :=
  contMDiff_id

/-- Composition of smooth maps is smooth. -/
theorem smooth_comp {M N P : Type*}
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
    {I : ModelWithCorners ℝ ℝ} {J : ModelWithCorners ℝ ℝ} {K : ModelWithCorners ℝ ℝ}
    [ChartedSpace ℝ M] [ChartedSpace ℝ N] [ChartedSpace ℝ P]
    [SmoothManifoldWithCorners I M] [SmoothManifoldWithCorners J N]
    [SmoothManifoldWithCorners K P]
    {f : N → P} {g : M → N}
    (hf : ContMDiff J K ⊤ f) (hg : ContMDiff I J ⊤ g) :
    ContMDiff I K ⊤ (f ∘ g) :=
  hf.comp g hg

/-! ## Constant Maps are Smooth -/

/-- A constant map between smooth manifolds is smooth. -/
theorem smooth_const {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N]
    {I : ModelWithCorners ℝ ℝ} {J : ModelWithCorners ℝ ℝ}
    [ChartedSpace ℝ M] [ChartedSpace ℝ N]
    [SmoothManifoldWithCorners I M] [SmoothManifoldWithCorners J N]
    (c : N) :
    ContMDiff I J ⊤ (fun _ : M => c) :=
  contMDiff_const

/-! ## Radon-Moise Theorem (Informal)

**Remark.** For dim ≤ 3, every topological manifold admits a unique
smooth structure (Radon 1925, Moise 1952). For dim = 4 (relevant to
spacetime), exotic smooth structures exist — Donaldson (1983) showed
ℝ⁴ has uncountably many distinct smooth structures.

This result is not yet formalized in Mathlib. -/
