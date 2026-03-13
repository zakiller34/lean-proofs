import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Tactic

/-!
# Chapter 4: Topological Manifolds

Schuller defines a d-dimensional topological manifold as a
paracompact Hausdorff space locally homeomorphic to ℝ^d.
In Mathlib, `ChartedSpace` encodes the atlas structure.
-/

/-! ## Charts and Atlases

A chart is a homeomorphism from an open subset of M to an open subset of ℝ^d.
In Mathlib, `PartialHomeomorph` models this. An atlas is a collection of charts
covering the manifold, encoded by `ChartedSpace`. -/

/-- A chart's source is open. -/
theorem chart_source_open {M H : Type*} [TopologicalSpace M] [TopologicalSpace H]
    [ChartedSpace H M] (e : PartialHomeomorph M H) (he : e ∈ atlas H M) :
    IsOpen e.source :=
  e.open_source

/-- A chart's target is open. -/
theorem chart_target_open {M H : Type*} [TopologicalSpace M] [TopologicalSpace H]
    [ChartedSpace H M] (e : PartialHomeomorph M H) (he : e ∈ atlas H M) :
    IsOpen e.target :=
  e.open_target

/-- The atlas covers the manifold: every point lies in some chart. -/
theorem atlas_covers {M H : Type*} [TopologicalSpace M] [TopologicalSpace H]
    [ChartedSpace H M] (x : M) :
    ∃ e ∈ atlas H M, x ∈ e.source := by
  exact ⟨chartAt H x, chart_mem_atlas H x, mem_chart_source H x⟩

/-! ## ℝ as a 1-dimensional Manifold

ℝ is trivially charted over itself via the identity homeomorphism. -/

/-- ℝ is a charted space over itself. -/
theorem real_charted_space : ChartedSpace ℝ ℝ :=
  inferInstance

/-- ℝ is a topological manifold (Hausdorff, second countable, charted). -/
theorem real_is_manifold : IsManifold (modelWithCornersSelf ℝ ℝ) ℝ :=
  inferInstance

/-! ## EuclideanSpace as a Manifold

ℝ^n (modeled as `EuclideanSpace ℝ (Fin n)`) is a manifold. -/

/-- ℝ^2 is a charted space over itself. -/
theorem euclidean2_charted_space :
    ChartedSpace (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) :=
  inferInstance

/-- ℝ^n is a manifold for any n. -/
theorem euclidean_is_manifold (n : ℕ) :
    IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (EuclideanSpace ℝ (Fin n)) :=
  inferInstance

/-! ## Hausdorff and Paracompactness Requirements

Schuller requires manifolds to be Hausdorff and paracompact. -/

/-- ℝ^n is Hausdorff. -/
theorem euclidean_t2 (n : ℕ) : T2Space (EuclideanSpace ℝ (Fin n)) :=
  inferInstance

/-- ℝ^n is paracompact. -/
theorem euclidean_paracompact (n : ℕ) : ParacompactSpace (EuclideanSpace ℝ (Fin n)) :=
  inferInstance

/-! ## Chart Transitions

Chart transition maps are compositions of partial homeomorphisms. -/

/-- A chart transition map is a partial homeomorphism on the model space. -/
theorem chart_transition_is_partial_homeomorph {M H : Type*}
    [TopologicalSpace M] [TopologicalSpace H] [ChartedSpace H M]
    (e e' : PartialHomeomorph M H) (he : e ∈ atlas H M) (he' : e' ∈ atlas H M) :
    PartialHomeomorph H H :=
  e.symm.trans e'
