# Formalizing a Physics Textbook in Lean 4

## What happens when you take an axiomatic physics course and feed it to a proof assistant?

Frederic Schuller's "Geometric Anatomy of Theoretical Physics" is unusual among physics lectures: it builds general relativity from scratch using rigorous mathematics, starting with propositional logic and ending with quantum field theory. Every definition is precise. Every theorem has a proof. This makes it a natural target for formalization.

We're working through all 20 chapters in Lean 4 with Mathlib. Six chapters are now complete — 110+ theorems, zero sorry statements, zero custom axioms.

## The journey so far

**Chapters 1–3 (Foundations)** cover logic, ZFC set theory, and topology. These mapped almost trivially to Lean: propositional logic *is* Lean's type theory, ZFC lives in Mathlib's `ZFSet`, and topology has extensive Mathlib coverage. The Heine-Borel theorem for ℝ was a two-line proof combining `IsCompact.isClosed`, `IsCompact.isBounded`, and `Metric.isCompact_of_isClosed_isBounded`.

**Chapter 4 (Topological Manifolds)** was the first real encounter with Mathlib's manifold library. Schuller defines a manifold as "paracompact + Hausdorff + locally homeomorphic to ℝ^d." Mathlib uses `ChartedSpace` (atlas of partial homeomorphisms) + `IsManifold` (Hausdorff + second countable). The concepts match, but the API is more general — it handles manifolds with boundary and corners via `ModelWithCorners`, which Schuller doesn't need until much later.

**Chapter 5 (Smooth Structures)** required understanding Mathlib's groupoid-based approach. Where Schuller says "C^k atlas," Mathlib uses `contDiffGroupoid` — the groupoid of partial homeomorphisms with C^k regularity. `SmoothManifoldWithCorners` then asks the atlas to live in `contDiffGroupoid ⊤`. The key smooth map API (`contMDiff_id`, `ContMDiff.comp`, `contMDiff_const`) wrapped cleanly.

**Chapter 6 (Vector Spaces & Modules)** was the most algebraically rich. Schuller's key pedagogical point — that modules over rings lack guaranteed bases, unlike vector spaces over fields — formalized naturally. `Basis.ofVectorSpace` (using Choice) gives every vector space a basis; meanwhile `ZMod 2` as a ℤ-module demonstrates a module without one. Dual spaces, tensor products, and finite dimension all have mature Mathlib APIs.

## What was easy

Anything Mathlib already has is almost embarrassingly easy to formalize. `inferInstance` proves that ℝ is Hausdorff, paracompact, a smooth manifold, a field, and a metric space. The real work is *choosing the right Mathlib concepts* and understanding how they relate to the textbook presentation.

Logic and basic topology are so well-covered that most proofs are one-liners. The value isn't in the proofs themselves but in the *verified correspondence* between Schuller's definitions and Mathlib's.

## What was hard

**The manifold API gap.** Schuller's presentation is clean and simple — a manifold is three properties. Mathlib's is industrial-strength — `ModelWithCorners`, `PartialHomeomorph`, `StructureGroupoid`, `ChartedSpace` form a sophisticated hierarchy designed for maximum generality. Bridging the two requires understanding *why* Mathlib made its design choices (boundaries, corners, infinite dimension).

**Naming.** Finding the right Mathlib lemma is half the battle. `isCompact_Icc` vs `IsCompact.isClosed` vs `Metric.isCompact_of_isClosed_isBounded` — the naming conventions are consistent but the namespace is vast.

## What's next

Chapters 7–8 (tensors and tensor fields) will be the bridge to differential geometry proper. Chapter 9 (connections) and 10 (curvature) are where the physics really starts. The question is whether Mathlib's differential geometry coverage — which is substantial but still growing — will carry us through, or whether we'll need to build custom infrastructure.

The ultimate goal: Einstein's field equations in Chapter 14, stated and verified in Lean 4.
