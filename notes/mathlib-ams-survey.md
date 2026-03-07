# Mathlib AMS (MSC2020) Classification Survey

**Date**: 2026-02-21
**Library**: [leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4) — The math library of Lean 4
**Lean version**: v4.29.0-rc1
**Classification**: [MSC2020](https://msc2020.org/)

---

## A. Existing Formalization by AMS Code

Each top-level module counted once under its primary AMS code (no double-counting).
Counts estimated from web data — prefixed with `~`.

| AMS Code | Field | Mathlib Module | ~Decls | Coverage Depth |
|----------|-------|----------------|--------|----------------|
| 03B | Mathematical logic | `Logic` | ~2,000 | Propositional, first-order, classical/intuitionistic |
| 03C | Model theory | `ModelTheory` | ~1,500 | First-order structures, compactness, Löwenheim-Skolem |
| 03D | Computability | `Computability` | ~2,000 | DFA/NFA/ε-NFA, CFG, Turing machines, recursive functions, halting problem, Rice, Arden |
| 03E | Set theory | `SetTheory` | ~1,500 | Ordinals, cardinals, ZFC models, cofinality |
| 05 | Combinatorics | `Combinatorics` | ~5,000 | Pigeonhole, Hall, Catalan, Sperner, Kruskal-Katona, Turán, Ramsey, Roth, regularity lemma |
| 06 | Order theory | `Order` | ~8,000 | Lattices, complete lattices, Galois connections, well-orderings, conditionally complete |
| 08/13/16 | General/commutative/associative algebra | `Algebra` | ~40,000 | Groups, rings, modules, tensor products, Lie algebras, Clifford algebras, homological algebra |
| 11 | Number theory | `NumberTheory` | ~5,000 | Quadratic reciprocity, sum of squares, Pell, Bernoulli, Witt vectors, class number finiteness, Dirichlet units |
| 12 | Field theory | `FieldTheory` | ~3,000 | Algebraic closure, Galois correspondence, splitting fields, separability |
| 13 | Commutative algebra | `RingTheory` | ~6,000 | Localization, Noetherian, PIDs, UFDs, Hilbert basis, primary decomposition (Lasker) |
| 14 | Algebraic geometry | `AlgebraicGeometry` | ~3,000 | Prime spectrum, Zariski topology, schemes, sheaves, Nullstellensatz |
| 15 | Linear algebra | `LinearAlgebra` | ~8,000 | Modules, dual spaces, determinants, eigenvalues, Cayley-Hamilton, bilinear/quadratic forms, structure theorem (PID) |
| 18 | Category theory | `CategoryTheory` | ~12,000 | Categories, functors, Yoneda, adjunctions, limits/colimits, abelian categories, sites, sheaves, descent |
| 20 | Group theory | `GroupTheory` | ~4,000 | Sylow, Schreier, Burnside, class formula, abelian group structure, alternating groups |
| 20C | Representation theory | `RepresentationTheory` | ~1,000 | Group representations, characters |
| 22 | Topological/Lie groups | (within `Topology`, `Geometry`) | ~2,000 | Topological groups, Lie groups, Lie algebras, integral curves |
| 26 | Real functions | (within `Analysis`) | ~6,000 | Derivatives, FTC, Taylor, mean value, monotone functions, convexity |
| 28 | Measure & integration | `MeasureTheory` | ~10,000 | Lebesgue, Hausdorff, Bochner integral, L^p, Fubini, disintegration, Haar measure |
| 30 | Complex analysis | (within `Analysis`) | ~2,000 | Cauchy integral formula, Liouville, maximum modulus, Schwarz lemma, FTA |
| 33 | Special functions | (within `Analysis`) | ~1,500 | exp, log, sin, cos, Gamma, zeta (partial) |
| 34 | Ordinary DEs | (within `Analysis`) | ~200 | Picard-Lindelöf existence/uniqueness only |
| 37 | Dynamical systems | `Dynamics` | ~500 | Circle dynamics, translation numbers, omega-limit sets, fixed/periodic points |
| 42 | Harmonic analysis | (within `Analysis`) | ~2,000 | Fourier transforms, inversion, Parseval, Riemann-Lebesgue |
| 46 | Functional analysis | (within `Analysis`) | ~5,000 | Banach-Steinhaus, open mapping, Hahn-Banach, Fréchet-Riesz, Lax-Milgram, Schwartz spaces |
| 51/53 | Geometry | (within `Geometry`) | ~2,000 | Affine/Euclidean spaces, manifolds with boundary/corners, tangent bundles, Riemannian |
| 54 | General topology | `Topology` | ~10,000 | Filters, compactness, connectedness, Stone-Čech, Urysohn, Stone-Weierstrass, uniform spaces |
| 55 | Algebraic topology | `AlgebraicTopology` | ~2,000 | Simplicial sets, chain complexes, fundamental groupoid |
| 60 | Probability | `Probability` | ~2,000 | Conditional expectation, SLLN, martingales, Markov kernels, Kolmogorov 0-1 |
| 94 | Information theory | `InformationTheory` | ~500 | Shannon entropy, mutual information |
| — | Infrastructure | `Data`, `Control`, `Tactic`, `Util`, `Lean`, `Condensed`, `Deprecated` | ~15,000 | Data structures, tactics (200+), meta-programming |

### Totals

- **~8,000 modules**, **~2,000,000 lines** of Lean 4
- **~258,900 theorems**, **~124,654 definitions**
- **~0 sorry** (CI enforced: no sorry in master)
- **~100% proved**

### Key Formalized Results

| Result | AMS | Module |
|--------|-----|--------|
| Picard-Lindelöf (ODE existence/uniqueness) | 34A12 | `Analysis.ODE` |
| Cauchy integral formula | 30 | `Analysis.Complex` |
| Hahn-Banach theorem | 46 | `Analysis.NormedSpace` |
| Banach-Steinhaus (uniform boundedness) | 46 | `Analysis.NormedSpace` |
| Open mapping theorem | 46 | `Analysis.NormedSpace` |
| Lax-Milgram theorem | 46 | `Analysis.InnerProductSpace` |
| Fundamental theorem of calculus | 26 | `MeasureTheory.Integral` |
| Fubini's theorem | 28 | `MeasureTheory.Integral` |
| Cayley-Hamilton theorem | 15 | `LinearAlgebra.Matrix` |
| Structure theorem (modules over PID) | 15 | `LinearAlgebra` |
| Galois correspondence | 12 | `FieldTheory.Galois` |
| Sylow theorems | 20 | `GroupTheory.Sylow` |
| Hilbert basis theorem | 13 | `RingTheory.Polynomial` |
| Lasker 1st uniqueness (primary decomposition) | 13 | `RingTheory.Lasker` |
| Nullstellensatz | 14 | `RingTheory.MvPolynomial` |
| Fourier inversion + Parseval | 42 | `Analysis.Fourier` |
| Strong law of large numbers | 60 | `Probability.StrongLaw` |
| Divergence theorem | 28 | `MeasureTheory` |
| Euler-Lagrange equation | 49 | `Analysis.Calculus` |
| Quadratic reciprocity | 11 | `NumberTheory` |
| Rice's theorem | 03D | `Computability` |
| Halting problem undecidability | 03D | `Computability` |
| Turán's theorem | 05 | `Combinatorics.SimpleGraph` |
| Szemerédi regularity lemma | 05 | `Combinatorics.SimpleGraph` |

---

## B. Community Activity (Open PRs by AMS Code)

Source: [leanprover-community/mathlib4 PRs](https://github.com/leanprover-community/mathlib4/pulls) as of 2026-02-21. PR numbers in ~35,500 range (35k+ lifetime PRs).

| AMS Code | Field | Label | Open PRs | Key PRs | Activity |
|----------|-------|-------|----------|---------|----------|
| 18 | Category theory | `t-category-theory` | ~8 | #35598 (short exactness), #35584 (monoidal sheaves), #35586 (preradicals) | HIGH |
| 13 | Ring theory | `t-ring-theory` | ~5 | #35595 (adic completion), #35594 (cotangent space), #35574 (prime spectrum) | HIGH |
| 08 | Algebra | `t-algebra` | ~4 | #35590 (AlgHom.ulift), #35587 (root systems perf) | HIGH |
| 54 | Topology | `t-topology` | ~3 | #35597 (adic topology), #35589 (SeparatelyContinuousMul) | MEDIUM |
| 26/46 | Analysis | `t-analysis` | ~2 | #35582 (adjoint, kernel, orthogonal complement) | MEDIUM |
| 11 | Number theory | `t-number-theory` | ~2 | #35573 (Chebyshev theta function) | MEDIUM |
| 06 | Order theory | `t-order` | ~1 | #35592 (deprecate Transitive for IsTrans) | LOW |
| — | Meta/tactics | `t-meta` | ~2 | #35591 (gsimp tactic), #35588 (Qq cleanup) | MEDIUM |
| 05 | Combinatorics | `t-combinatorics` | ~1 | — | LOW |

### Community Stats (as of 2026-02-21)

- **Stars**: 2,923 / **Forks**: 1,097
- **Contributors**: 759
- **Lifetime PRs**: ~35,600+
- **Lean version**: v4.29.0-rc1
- CI enforces: no sorry, linting, style checks

### What the Community is Prioritizing

1. **Category theory** — heaviest activity: sites/descent, abelian categories, monoidal structures
2. **Ring theory / commutative algebra** — adic completions, cotangent complexes, primary decomposition
3. **Algebra infrastructure** — root systems, module/algebra morphisms
4. **Analysis** — inner product space adjoint theory, topological algebra
5. **Number theory** — analytic number theory (Chebyshev bounds)

---

## C. Fields Not Yet Touched (Gaps)

Focus: project target areas from CLAUDE.md (MSC 34, 35, 49, 65, 68Q, 90, 93).

| AMS Code | Field | Status | What Exists | What's Missing |
|----------|-------|--------|-------------|----------------|
| 34 | Ordinary DEs | **THIN** | Picard-Lindelöf, integral curves on manifolds | Stability (Lyapunov), BVP, Sturm-Liouville, phase portraits, nonlinear systems |
| 35 | Partial DEs | **ABSENT** | Partial derivatives as algebraic objects only | Sobolev spaces (beyond distributions), elliptic/parabolic/hyperbolic theory, weak solutions |
| 49 | Calculus of variations / optimization | **THIN** | Euler-Lagrange equation, convexity theory (Jensen, Carathéodory) | Optimal control (Pontryagin), 2nd-order conditions, algorithmic optimization |
| 65 | Numerical analysis | **ABSENT** | — | Everything: floating-point, discretization, quadrature, numerical linear algebra, FEM, Euler/RK methods |
| 68Q | CS (model checking) | **PARTIAL** | DFA/NFA/ε-NFA, CFG, Turing machines, Arden's lemma | Temporal logic (LTL/CTL), Büchi automata (in cslib but not Mathlib), model checking algorithms |
| 90 | Operations research | **ABSENT** | Simplex in `linarith` tactic internals (not standalone) | LP duality, integer programming, combinatorial optimization, network flows |
| 93 | Systems/control theory | **ABSENT** | — | Controllability, observability, state-space models, transfer functions, Lyapunov stability |

### Observations

- **Mathlib's strengths** are pure math: algebra, analysis, category theory, topology, number theory. Applied/computational math is the major frontier.
- **ODE → PDE → numerical methods** is a natural progression. Picard-Lindelöf exists; Sobolev spaces and basic PDE theory are the next stepping stone.
- **Optimization gap** is bridgeable: convexity theory is solid, gradient/Fréchet derivatives exist. Missing piece is connecting these to algorithmic convergence.
- **Numerical analysis** is a greenfield — no existing Mathlib infrastructure. Would need to build from scratch (floating-point models, discretization error frameworks).
- **CS/model checking** has better coverage in cslib than in Mathlib. Temporal logic and Büchi automata should extend cslib, not duplicate Mathlib's DFA.
- **Operations research** is fully absent. The simplex algorithm exists only as a proof tactic implementation detail, not a formalized mathematical object.
- **"Folklore lemma" problem**: even in well-covered areas, users report missing intermediate lemmas that textbooks use without proof. This affects all areas equally.
