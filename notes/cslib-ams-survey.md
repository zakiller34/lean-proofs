# CSLib AMS (MSC2020) Classification Survey

**Date**: 2026-02-21
**Library**: [leanprover/cslib](https://github.com/leanprover/cslib) — Lean Computer Science Library
**Lean version**: v4.29.0-rc1
**Classification**: [MSC2020](https://msc2020.org/)

---

## A. Existing Formalization by AMS Code

Each file counted once under its primary AMS code (no double-counting).

| AMS Code | Field | cslib Path | Files | Thms+Lem | Defs | Sorry | % Proved |
|----------|-------|------------|-------|----------|------|-------|----------|
| 03Bxx | Type theory / lambda calculus | `Languages/LambdaCalculus/`, `Foundations/Syntax/` | 21 | ~200 | ~90 | 1 | ~99% |
| 03B40 | Combinatory logic (SKI) | `Languages/CombinatoryLogic/` | 6 | ~130 | ~35 | 0 | 100% |
| 03B45 | Modal logic (HML) | `Logics/HML/` | 1 | ~15 | ~4 | 0 | 100% |
| 03D05 | Automata & formal grammars | `Computability/Automata/`, `Computability/Languages/` | 27 | ~260 | ~40 | 0 | 100% |
| 03Dxx | Computability (URM) | `Computability/URM/` | 6 | ~50 | ~26 | 0 | 100% |
| 03F52 | Linear logic (CLL) | `Logics/LinearLogic/` | 4 | ~28 | ~37 | 0 | 100% |
| 05D10 | Ramsey theory | `Foundations/Combinatorics/` | 1 | 2 | 0 | 0 | 100% |
| 68Q17 | Computational complexity | `Algorithms/Lean/TimeM.lean` | 1 | ~3 | ~4 | 0 | 100% |
| 68Q60 | Formal semantics (LTS/FLTS) | `Foundations/Semantics/` | 8 | ~130 | ~10 | 0 | 100% |
| 68Q85 | Process calculi (CCS) | `Languages/CCS/` | 3 | ~30 | ~8 | 0 | 100% |
| 68W40 | Analysis of algorithms | `Algorithms/Lean/MergeSort/` | 1 | ~9 | ~4 | 0 | 100% |
| — | Infrastructure (data, control, lint) | `Foundations/Data/`, `Foundations/Control/` | 17 | ~160 | ~30 | 0 | 100% |

### Totals

- **113 files**, **15,735 lines** of Lean 4
- **676 theorems**, **93 lemmas**, **254 definitions**
- **1 sorry** (`Term.subst_comm` in named untyped lambda calculus)
- **~99.9% proved**

### Key Formalized Results

| Result | AMS | File |
|--------|-----|------|
| MergeSort correctness + O(n log n) complexity | 68W40 | `Algorithms/Lean/MergeSort/` |
| Powerset construction (NFA → DFA) | 03D05 | `Computability/Automata/NA/ToDA.lean` |
| Buchi/Muller automata on omega-words | 03D05 | `Computability/Automata/DA/`, `NA/` |
| Confluence of full beta-reduction | 03Bxx | `Languages/LambdaCalculus/LocallyNameless/Untyped/FullBetaConfluence.lean` |
| STLC progress + preservation | 03Bxx | `Languages/LambdaCalculus/LocallyNameless/STLC/Safety.lean` |
| System Fsub subtyping (133 declarations) | 03Bxx | `Languages/LambdaCalculus/LocallyNameless/Fsub/` |
| SKI confluence + bracket abstraction correctness | 03B40 | `Languages/CombinatoryLogic/` |
| Y combinator + fixed-point recursion | 03B40 | `Languages/CombinatoryLogic/Recursion.lean` |
| Bisimulation theory (46 declarations) | 68Q60 | `Foundations/Semantics/LTS/Bisimulation.lean` |
| Phase semantics for linear logic | 03F52 | `Logics/LinearLogic/CLL/PhaseSemantics/` |

---

## B. Community Activity (Open PRs by AMS Code)

Source: [leanprover/cslib PRs](https://github.com/leanprover/cslib/pulls) as of 2026-02-21. cslib only (no Mathlib).

| AMS Code | Field | Open PRs | Key PRs | Activity |
|----------|-------|----------|---------|----------|
| 68Q17 | Complexity classes | 3 | #192 (complexity classes), #275 (query complexity, 73 comments), #201 (query complexity via free monads) | HIGH |
| 68W40 | Algorithm analysis | 3 | #343 (insertion sort + time), #280 (insertion sort correctness), #237 (binary search) | HIGH |
| 03D10 | Turing machines | 1 | #269 (single tape TM, 49 comments) | HIGH |
| 03D05 | Automata / languages | 3 | #329 (omega-regular complement), #208 (NFA empty check), #286 (transducers) | MEDIUM |
| 03Bxx | Lambda calc / types | 2 | #327 (strong normalization, draft), #28 (Fsub, 30 comments) | MEDIUM |
| 03F52 / 03B45 | Logic / semantics | 5 | #89,#91,#93 (propositional logic + natural deduction), #220 (tau-str), #325 (Buchi congruence, 23 comments) | MEDIUM |
| 03B40 | Combinatory logic | 1 | #331 (Church-encoded lists for SKI) | LOW |
| — | Infrastructure | 2 | #360 (additive writer monad), #353 (deterministic relations) | LOW |

### Community Stats (as of 2026-02-21)
- 317 stars, 70 forks, 385 commits
- 33 contributors, 19 collaborators
- 24 open issues, 21 open PRs, 278 closed PRs
- Steering: Clark Barrett (Stanford/Amazon), Leonardo de Moura (Lean FRO), Pushmeet Kohli (DeepMind)
- Lead maintainer: Fabrizio Montesi (Univ. of Southern Denmark)

### What the Community is Prioritizing
1. **Computational complexity** — multiple concurrent PRs defining complexity classes and query complexity models
2. **Algorithm verification with bounds** — sorting algorithms (insertion, merge) and binary search with formal time analysis
3. **Turing machines** — foundational computability model, long-running PR with heavy discussion
4. **Omega-regular languages** — closure properties, complementation
5. **Propositional logic** — definitions, natural deduction, Heyting algebra semantics

---

## C. Fields Not Yet Touched (Gaps)

These are target areas from the project objectives with **zero cslib coverage**:

| AMS Code | Field | Status | Notes |
|----------|-------|--------|-------|
| 34 | Ordinary differential equations | NOT STARTED | No ODEs in cslib. Mathlib has some analysis foundations. |
| 35 | Partial differential equations | NOT STARTED | No PDEs in cslib. Requires Mathlib's measure theory + functional analysis. |
| 49 | Optimization | NOT STARTED | No optimization theory. Mathlib has convexity basics. |
| 65 | Numerical analysis | NOT STARTED | No numerical methods. Would need error analysis, convergence proofs. |
| 90 | Operations research | NOT STARTED | No linear programming, scheduling, etc. |
| 93 | Systems theory / control / model checking | MINIMAL | Only HML logic exists. No CTL, LTL, CTL*, mu-calculus, or model checking algorithms. |

### Observations
- cslib is purely **discrete/foundational CS** — no continuous math, no numerical methods
- The gap between cslib's strengths (03, 68) and target areas (34, 35, 49, 65) is large
- Model checking (93) is the closest gap to bridge — LTS/bisimulation infrastructure exists, just needs temporal logics on top
- Numerical analysis (65) would likely live in a separate sub-project using Mathlib's real analysis
