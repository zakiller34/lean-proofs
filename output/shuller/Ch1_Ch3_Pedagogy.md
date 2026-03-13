# Chapters 1–3: Pedagogy Notes

## Architecture

Three foundation chapters mirroring Schuller's progression: logic → sets → topology.

| File | Schuller Topic | Mathlib Core | Theorems |
|------|---------------|-------------|----------|
| `Ch1_Logic.lean` | Propositional & predicate logic | `Mathlib.Logic.Basic` | 15 |
| `Ch2_SetTheory.lean` | ZFC axioms, number constructions | `Mathlib.SetTheory.ZFC.Basic` | 12 |
| `Ch3_Topology.lean` | Topological spaces, compactness | `Mathlib.Topology.*` | 12 |
| `Examples.lean` | Concrete demonstrations | Mixed | 21 |

## Key Design Decisions

### Ch1: Logic lives in Lean's type theory
Schuller teaches propositional/predicate logic as a formal system. In Lean 4, the type theory *is* the logic — `Prop` is a universe, `∧`/`∨`/`→` are type constructors. We restate Schuller's key results (modus ponens, contrapositive, de Morgan, excluded middle) as Lean theorems, showing they're provable from the foundations.

### Ch2: ZFSet for set theory
Schuller uses ZFC. Lean's native `Set α` is typed and doesn't match ZFC's untyped ∈-relation. We use Mathlib's `ZFSet` which models ZFC within type theory, letting us state all 9 axioms. The number construction chain ℕ → ℤ → ℚ → ℝ uses Lean's native types with coercion.

### Ch3: Mathlib topology covers everything
Schuller's topology (open/closed sets, Hausdorff, compactness, paracompactness, Heine-Borel) maps directly to Mathlib's `TopologicalSpace`, `T2Space`, `IsCompact`, `ParacompactSpace`. Most proofs are one-liners wrapping Mathlib lemmas.

## Definition Walkthrough

### Ch1 Highlights
- `ex_falso_quodlibet`: From `False`, anything — uses `False.elim`
- `contrapositive`: (p → q) ↔ (¬q → ¬p) — one direction by composition, reverse by `tauto`
- `excluded_middle`: `Classical.em p` — Lean has classical logic built in
- `no_universal_set`: Russell's paradox via `ZFSet.sep` — the diagonal argument

### Ch2 Highlights
- ZFC axioms 1–6 + 9 stated as `∃` theorems about `ZFSet`
- Axiom 7 (Infinity) and 8 (Replacement) omitted — Infinity is implicit in ℕ's existence, Replacement is universe-level
- Russell's paradox: construct R = {x ∈ U | x ∉ x}, derive contradiction via `tauto`

### Ch3 Highlights
- Topology axioms restated as theorems: `isOpen_empty`, `isOpen_univ`, `IsOpen.inter`, `isOpen_sUnion`
- `t2_separation`: unpacks `T2Space.t2` to get the explicit open sets
- `heine_borel_real`: forward direction from `IsCompact.isClosed` + `IsCompact.isBounded`; reverse from `Metric.isCompact_of_isClosed_isBounded`
- `compact_implies_paracompact`: `inferInstance` — Mathlib derives it automatically
