# formal-conjectures AMS (MSC2020) Classification Survey

**Date**: 2026-02-21
**Library**: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures) — Formalized conjecture statements in Lean 4
**Lean version**: v4.27.0 (Mathlib v4.27.0)
**Classification**: [MSC2020](https://msc2020.org/)

---

## A. Existing Formalization by AMS Code

The library uses built-in `@[category ..., AMS N]` annotations. Counts below are from those annotations (combining single/double-digit forms, e.g. `AMS 5` + `AMS 05` → 05). Each annotation counted once.

### By AMS annotation (from `@[category ..., AMS N]`)

| AMS Code | Field | Annotations | % of Total |
|----------|-------|-------------|------------|
| 11 | Number theory | 1120 | 55.9% |
| 05 | Combinatorics | 512 | 25.5% |
| 52 | Convex & discrete geometry | 57 | 2.8% |
| 12 | Field theory & polynomials | 51 | 2.5% |
| 51 | Geometry | 38 | 1.9% |
| 20 | Group theory | 27 | 1.3% |
| 03 | Mathematical logic & foundations | 21 | 1.0% |
| 30 | Functions of a complex variable | 18 | 0.9% |
| 54 | General topology | 17 | 0.8% |
| 26 | Real functions | 17 | 0.8% |
| 68 | Computer science | 15 | 0.7% |
| 33 | Special functions | 15 | 0.7% |
| 16 | Associative rings & algebras | 15 | 0.7% |
| 37 | Dynamical systems & ergodic theory | 12 | 0.6% |
| 15 | Linear & multilinear algebra | 10 | 0.5% |
| 28 | Measure & integration | 9 | 0.4% |
| 13 | Commutative algebra | 7 | 0.3% |
| 42 | Harmonic analysis | 6 | 0.3% |
| 14 | Algebraic geometry | 6 | 0.3% |
| 08 | General algebraic systems | 5 | 0.2% |
| 47 | Operator theory | 5 | 0.2% |
| 32 | Several complex variables | 3 | 0.1% |
| 40 | Sequences, series, summability | 2 | 0.1% |
| 60 | Probability theory | 1 | <0.1% |
| 18 | Category theory | 1 | <0.1% |

### By subdirectory

| Subdirectory | Files | Thms | Lems | Defs | Sorry | Primary AMS |
|-------------|-------|------|------|------|-------|-------------|
| ErdosProblems | 371 | 1088 | 57 | 170 | 1434 | 11, 05 |
| Wikipedia | 97 | 373 | 25 | 98 | 372 | 11, 20, 14, 52 |
| GreensOpenProblems | 27 | 61 | 0 | 18 | 86 | 05, 11, 20, 43 |
| OEIS | 20 | 88 | 8 | 25 | 35 | 11, 68 |
| Paper | 14 | 37 | 11 | 19 | 46 | 05, 68, 14, 12 |
| Arxiv | 13 | 55 | 2 | 16 | 35 | 05, 14, 11, 68 |
| Util | 12 | 8 | 0 | 30 | 24 | — (infrastructure) |
| WrittenOnTheWallII | 11 | 95 | 0 | 3 | 95 | 05 (graph theory) |
| Mathoverflow | 9 | 34 | 6 | 6 | 30 | 28, 54, 52 |
| Other | 4 | 12 | 6 | 0 | 21 | 68, 03, 05 |
| Kourovka | 2 | 2 | 0 | 0 | 4 | 20 |
| Millenium | 2 | 7 | 0 | 5 | 5 | 11, 68 |
| HilbertProblems | 1 | 6 | 0 | 1 | 3 | 12, 14 |
| Books | 1 | 4 | 0 | 4 | 6 | 11, 43 |

### Totals

- **584 files**, **42,555 lines** of Lean 4
- **1,870 theorems**, **115 lemmas**, **395 definitions**, **22 instances**
- **2,196 sorry** (this is by design — statements only, proofs left as sorry)
- **~0% proved** (library purpose is formalized *statements*, not proofs)

### Category breakdown

| Category | Count | Description |
|----------|-------|-------------|
| research open | 822 | Open conjectures |
| research solved | 626 | Solved but not formally proved |
| test | 344 | Sanity checks for definitions |
| API | 77 | Basic theory around definitions |
| undergraduate | 74 | Undergraduate-level problems |
| high_school | 28 | High school-level problems |
| graduate | 9 | Graduate-level problems |
| research formally solved | 8 | Formally proved (in this repo or elsewhere) |

### Key Formalized Results

| Result | AMS | Subdirectory |
|--------|-----|-------------|
| Generalized Riemann Hypothesis | 11 | Millenium |
| P vs NP | 68 | Millenium |
| Hilbert's 17th Problem (sum of squares) | 12 | HilbertProblems |
| abc Conjecture | 11 | Wikipedia |
| Collatz Conjecture | 11 | Wikipedia |
| Modularity Conjecture (elliptic curves) | 11 | Wikipedia |
| Poincaré Conjecture (in PR) | 57 | Millenium |
| Gromov Polynomial Growth | 20 | Wikipedia |
| Kakeya Set Problem | 28 | Wikipedia |
| Kaplansky Zero Divisor Conjecture | 16, 20 | Wikipedia |
| Erdős problems (371 files, 1000+ problems) | 11, 05 | ErdosProblems |
| Green's Open Problems (27 problems) | 05, 11 | GreensOpenProblems |
| Casas-Alvero Conjecture | 12 | Paper |
| Hartshorne Conjecture | 14 | Paper |
| Zariski Cancellation | 14 | Arxiv |
| Strong Sensitivity Conjecture | 68 | Paper |
| Busy Beaver (Σ(6)) | 68 | Wikipedia |
| Euler Brick / perfect cuboid | 11 | Wikipedia |

---

## B. Community Activity (Open PRs by AMS Code)

Source: [google-deepmind/formal-conjectures PRs](https://github.com/google-deepmind/formal-conjectures/pulls) as of 2026-02-21.

| AMS Code | Field | Open PRs | Key PRs | Activity |
|----------|-------|----------|---------|----------|
| 11 | Number theory | ~40 | Erdős 400, 254, 241, 184, 156; Noncototients; Amicable numbers | HIGH |
| 05 | Combinatorics | ~25 | Erdős 323, 193; Green 26, 25, 22; Degree sequences | HIGH |
| 20 | Group theory | ~3 | Kourovka problems | MEDIUM |
| 68 | Computer science | ~2 | P vs NP related | LOW |
| 57 | Manifolds | ~1 | Poincaré conjecture | LOW |
| 52 | Geometry | ~2 | Borwein; Taxicab | LOW |
| — | Infrastructure | ~10 | Mathlib bump v4.28.0; CI; linters; FormalConjecturesForMathlib | MEDIUM |

### Community Stats (as of 2026-02-21)

- **827 stars**, **225 forks**
- **124 contributors**
- **735 open issues** (mostly conjecture formalization requests)
- **89 open PRs**, **1,007 closed PRs**
- Validation via AlphaProof for misformalization detection

### What the Community is Prioritizing

1. **Erdős problems** — bulk of activity, many open issues assigned as formalization tasks
2. **Green's open problems** — active new additions
3. **Wikipedia conjectures** — steady stream of new formalizations
4. **Infrastructure** — Mathlib version bumps, linters (misformalization detection, AMS tagging)
5. **Misformalization fixes** — PRs explicitly labeled `misformalization` to correct wrong statements

---

## C. Fields Not Yet Touched (Gaps)

Compared against project target areas from CLAUDE.md:

| AMS Code | Field | Status | Notes |
|----------|-------|--------|-------|
| 34 | Ordinary differential equations | **NOT COVERED** | Target area. Zero files, zero annotations |
| 35 | Partial differential equations | **NOT COVERED** | Target area. Zero files, zero annotations |
| 49 | Calculus of variations & optimization | **NOT COVERED** | Target area. Zero files, zero annotations |
| 65 | Numerical analysis | **NOT COVERED** | Target area. Zero files, zero annotations |
| 90 | Operations research | **NOT COVERED** | Target area. Zero files, zero annotations |
| 93 | Systems theory & control | **NOT COVERED** | Target area. Zero files, zero annotations |
| 94 | Information & communication | **NOT COVERED** | Future target. Zero files |
| 46 | Functional analysis | Not covered | Some adjacent content in Topology/Analysis |
| 22 | Topological groups, Lie groups | Not covered | Gromov result touches this |
| 55 | Algebraic topology | Not covered | — |
| 57 | Manifolds & cell complexes | Minimal | Poincaré conjecture PR pending |
| 58 | Global analysis | Not covered | — |
| 60 | Probability theory | Minimal | 1 annotation only |

### Observations

- **Number theory (11) and combinatorics (05) dominate** — together 81.4% of annotations. Reflects the library's Erdős-problem-heavy design.
- **All six project target areas (34, 35, 49, 65, 90, 93) have zero coverage.** This library is pure-math conjectures, not applied/computational.
- **Library is statements-only by design.** 2,196 sorry across 584 files. The 8 formally-solved results are exceptions.
- **Active community** — 124 contributors, 827 stars, 89 open PRs. High velocity on Erdős + Green problems.
- **Built-in AMS classification** — library already tags theorems via `@[category ..., AMS N]`. Good infrastructure for tracking.
- **Nearest bridging points** to project targets:
  - **37 (Dynamical systems)** → could bridge to **34 (ODE)** via Collatz-like iteration problems
  - **26 (Real functions)** → could bridge to **35 (PDE)** and **65 (Numerical analysis)** via analysis conjectures
  - **52 (Geometry)** → could bridge to **49 (Optimization)** via convexity problems
- **Opportunity**: Formalizing conjectures in target areas (ODE/PDE/numerical/optimization) would be novel contributions — no existing coverage in this library.
