# Chapters 4–6: Pedagogy Notes

## Architecture

Three chapters bridging topology to differential geometry and algebra.

| File | Schuller Topic | Mathlib Core | Theorems |
|------|---------------|-------------|----------|
| `Ch4_Manifolds.lean` | Topological manifolds | `Mathlib.Geometry.Manifold.ChartedSpace` | 10 |
| `Ch5_SmoothStructures.lean` | Differentiable structures | `Mathlib.Geometry.Manifold.ContMDiff.*` | 6 |
| `Ch6_VectorSpaces.lean` | Vector spaces & modules | `Mathlib.LinearAlgebra.*` | 18 |
| `Examples456.lean` | Concrete demonstrations | Mixed | 16 |

## How Mathlib Models Manifolds

### Textbook vs Mathlib

Schuller defines a manifold as a topological space (M, O) that is:
1. Paracompact
2. Hausdorff (T2)
3. Locally homeomorphic to ℝ^d

Mathlib splits this into layers:
- **`ChartedSpace H M`**: M has an atlas of `PartialHomeomorph M H` (local homeomorphisms to model space H)
- **`IsManifold I M`**: the charted space is Hausdorff + second countable (implies paracompact)
- **`ModelWithCorners ℝ H`**: how the model space H embeds in a normed space (handles boundaries, corners)

For ℝ^n without boundary: `modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))`.

### Why `ModelWithCorners`?

Schuller only treats manifolds without boundary. Mathlib's `ModelWithCorners` generalizes to manifolds with boundary/corners (needed for integration). For our purposes, `modelWithCornersSelf` is the identity embedding.

## Smooth Structures via Groupoids

### Textbook: C^k atlas
Schuller defines a C^k atlas where all transition maps y ∘ x⁻¹ are C^k on ℝ^d.

### Mathlib: `contDiffGroupoid`
Mathlib uses structure groupoids: `contDiffGroupoid n I` is the groupoid of partial homeomorphisms whose maps (and inverses) are C^n. A `SmoothManifoldWithCorners I M` requires the atlas to be compatible with `contDiffGroupoid ⊤ I`.

### Smooth maps
`ContMDiff I J n f` means f : M → N is C^n in charts. `n = ⊤` means C^∞ (smooth). Key API:
- `contMDiff_id`: identity is smooth
- `ContMDiff.comp`: composition preserves smoothness
- `contMDiff_const`: constant maps are smooth

## Vector Space vs Module in Lean

### The distinction
Schuller emphasizes: vector space = module over a *field*. In Mathlib:
- `Module R M` works for any `Semiring R`
- A "vector space" is just `Module K V` where `[Field K]`

### Why it matters
- Over a field: every vector space has a basis (`Basis.ofVectorSpace`, needs AC)
- Over a ring: modules need not have bases (e.g., ℤ/2ℤ as a ℤ-module)
- Schuller's application: sections of vector bundles Γ(E) form a C^∞(M)-module, not a vector space

### Key Mathlib API surface

| Concept | Mathlib type | Notes |
|---------|-------------|-------|
| Vector space | `Module K V` with `[Field K]` | No separate typeclass |
| Subspace | `Submodule K V` | Closed under +, • |
| Linear map | `V →ₗ[K] W` (`LinearMap`) | Preserves + and • |
| Basis | `Basis ι K V` | Indexed family |
| Dimension | `Module.finrank K V` | Cardinal for infinite dim |
| Dual space | `Module.Dual K V = V →ₗ[K] K` | Definitional equality |
| Tensor product | `TensorProduct K V W` (`V ⊗[K] W`) | Universal bilinear |

### Concrete examples in the formalization
- `Fin n → ℝ` as ℝ^n (Mathlib's preferred model for finite-dim)
- `EuclideanSpace ℝ (Fin n)` for manifold model spaces (has inner product)
- `Pi.basisFun ℝ (Fin n)` for the standard basis
- `ZMod 2` as a ℤ-module without basis
