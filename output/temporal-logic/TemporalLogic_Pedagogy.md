# Temporal Logic Formalization — Pedagogical Guide

Formalization of Chapter 8 (Liveness and Fairness) from Lamport's *Specifying Systems*.

## Architecture

Semantic approach: temporal operators on behaviors (`ℕ → α`) via suffix semantics.
- `σ ⊨ □F` means `∀ n, F(suffix n σ)`
- `σ ⊨ ◇F` means `∃ n, F(suffix n σ)`

State predicates lifted via `lift P σ = P(σ 0)`. Bridge to Mathlib filters for `□◇`/`◇□`.

## File Map

| File | Content | Lamport ref |
|------|---------|-------------|
| `Defs.lean` | D1-D16: behaviors, temporal ops, fairness, safety/liveness | §8.1, §8.4, §8.6, §8.9 |
| `Tautologies.lean` | T1-T9: □∧, ◇∨, duality, □◇∨, ◇□∧, proof rules + examples | §8.2-8.3 |
| `FilterBridge.lean` | T10-T11: □◇↔Frequently, ◇□↔Eventually | — |
| `Fairness.lean` | T12-T15: WF/SF equivalences, SF→WF + toggle example | §8.4, §8.6 |
| `MachineClosure.lean` | T16-T18: LeadsTo transitivity, safety/liveness defs | §8.9 |
| `CslibBridge.lean` | T19-T21: correspondence with cslib ωSequence | — |

## Key Design Decisions

1. **Suffix-based semantics** (not Kripke structures): matches Lamport's TLA directly
2. **`lift` for state predicates**: cleanly separates temporal from state-level reasoning
3. **Filter bridge**: connects to Mathlib's `Filter.Frequently`/`Filter.Eventually` at `atTop`
4. **Classical logic**: T6 (□◇ distributes over ∨) requires `Classical.em`
5. **No cslib import** (toolchain mismatch rc1/rc2): CslibBridge proves correspondence abstractly

## Definitions (Defs.lean)

- `Behavior α := ℕ → α` — infinite state sequence
- `suffix n σ k = σ(n + k)` — behavior suffix
- `Always F σ = ∀ n, F(suffix n σ)` — □
- `Eventually F σ = ∃ n, F(suffix n σ)` — ◇
- `InfOften F = Always (Eventually F)` — □◇
- `EventuallyAlways F = Eventually (Always F)` — ◇□
- `LeadsTo F G = Always (fun σ => F σ → Eventually G σ)` — ↝
- `lift P σ = P(σ 0)` — state predicate → temporal formula
- `liftAction A σ = A(σ 0)(σ 1)` — action → temporal formula
- `Enabled A s = ∃ s', A s s'`
- `AngleAction A v s s' = A s s' ∧ v s ≠ v s'` — non-stuttering step
- `WF A v = □(□ENABLED⟨A⟩_v → ◇⟨A⟩_v)` — weak fairness
- `SF A v = ◇□(¬ENABLED⟨A⟩_v) ∨ □◇⟨A⟩_v` — strong fairness
- `IsSafetyProperty S` — violation witnessed by finite prefix
- `IsLivenessProperty L` — every finite prefix extends to a member
- `IsMachineClosed S L` — every finite S-behavior extends to S ∩ L

## Tautologies (Tautologies.lean)

| # | Statement | Key tactic |
|---|-----------|------------|
| T1 | `□(F ∧ G) ↔ □F ∧ □G` | `forall_and` |
| T2 | `◇(F ∨ G) ↔ ◇F ∨ ◇G` | `exists_or` |
| T3 | `□F ↔ ¬◇¬F` | `not_exists, not_not` |
| T4 | `◇F ↔ ¬□¬F` | `not_forall, not_not` |
| T5 | `□F → ◇F` | instantiate n=0 |
| T6 | `□◇(F ∨ G) ↔ □◇F ∨ □◇G` | Classical contradiction + suffix arithmetic |
| T7 | `◇□(F ∧ G) ↔ ◇□F ∧ ◇□G` | max of witnesses |
| T8 | `(∀ σ, F σ) → ∀ σ, □F σ` | trivial |
| T9 | `(∀ σ, F→G) → ∀ σ, □F→□G` | pointwise |

### Examples
- E1: `fun _ => 0` satisfies `□(lift (· = 0))`
- E2: `fun n => n % 2` satisfies `□◇(lift (· = 0))`
- E3: `fun n => if n < 5 then 0 else 1` satisfies `◇□(lift (· = 1))`

## Fairness (Fairness.lean)

| # | Statement | Ref |
|---|-----------|-----|
| T12 | `WF ↔ □◇(¬ENABLED) ∨ □◇⟨A⟩_v` | p.98 |
| T13 | `WF ↔ ◇□ENABLED → □◇⟨A⟩_v` | p.98 |
| T14 | `SF ↔ □◇ENABLED → □◇⟨A⟩_v` | p.106 |
| T15 | `SF → WF` (via `◇□P → □◇P`) | p.106 |

## Machine Closure (MachineClosure.lean)

- T16: `LeadsTo` is transitive
- T17: `◇□F → □◇F`
- T18: `SafetySpec Init Next v` is a safety property (proved)
- Machine closure realizability: `IsMachineClosed S L → S-witness → (S ∩ L).Nonempty`

## Status

- 0 `sorry` — all theorems fully proved
- All examples type-check
- Axioms: only standard (propext, Classical.choice, Quot.sound)
