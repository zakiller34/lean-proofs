# Formalizing Binary Decision Diagrams in Lean 4

## Why BDDs?

Binary Decision Diagrams are the workhorse of hardware verification, model checking, and symbolic computation. Knuth devotes an entire section of TAOCP Vol. 4 (7.1.4) to them — over 100 pages of definitions, algorithms, and theorems. Despite their ubiquity, BDDs have seen surprisingly little formal verification in proof assistants.

## Design: Two Representations

We use a **dual representation** pattern inspired by `Std.Sat.AIG` in Lean's standard library:

1. **`BDDTree n`** — an inductive tree type for proofs. Easy to pattern match, do structural induction, and reason about semantics.
2. **`ArrayBDD n`** — an array-backed DAG for algorithms. Indices 0/1 are ⊥/⊤ sinks, with a DAG proof (`is_dag`) ensuring well-foundedness.

The connection: `ArrayBDD.toTree` converts the array form to a tree, and `eval_eq_tree_eval` proves evaluation consistency.

## Core Types

**Boolean functions** (`BoolFun n`): simply `(Fin n → Bool) → Bool`. Assignments are `Fin n → Bool` — more ergonomic than vectors in Lean 4.

**Nodes** (`Decl n`): either `sink b` (terminal with value `b`) or `branch v lo hi` (tests variable `v ∈ Fin n`, with children at indices `lo` and `hi`).

## Shannon Expansion: The Foundation

The Shannon expansion `f(σ) = (¬σᵢ ∧ f|_{xᵢ=0}(σ)) ∨ (σᵢ ∧ f|_{xᵢ=1}(σ))` is the mathematical foundation of BDDs. Every branch node implements exactly this decomposition. We prove it as `shannon_expansion` in `BoolFun.lean`.

## Ordered + Reduced = Canonical

An **ordered** BDD tests variables in strictly ascending order along every path. A **reduced** BDD has no redundant nodes (where lo = hi) and no semantically equivalent subtrees.

The **canonicity theorem** (`robdd_canonical`): two ROBDDs representing the same function are structurally identical. This is Bryant's 1986 result and the reason BDDs are useful — semantic equality reduces to pointer equality.

## Algorithms

- **Algorithm C** (count solutions): bottom-up DP counting satisfying assignments
- **Algorithm R** (reduction): eliminates redundant/duplicate nodes from an ordered BDD
- **Algorithm S** (synthesis/apply): combines two BDDs with any binary Boolean operator
- **NOT**: simple recursive flip of leaves

## Truth Tables and Beads

A truth table of order `n` has `2^n` entries. It's a **square** if its top half equals its bottom half (function is independent of `x₁`). A **bead** is a non-square table. Knuth's insight: ROBDD nodes biject with beads.

## Size Bounds

Three fundamental results (statement-only for now):
- **Theorem U**: every function has BDD size ≤ roughly `2^{n+1}/n`
- **Theorem M**: network model gives tighter bounds for structured functions
- **Theorem B** (Bryant): hidden weighted bit requires exponential size for ALL orderings

## What's Proved vs Sorry

Fully proved: Shannon expansion, BDDTree eval, NOT correctness, countSolutions correctness, basic structural lemmas.

Sorry (Phase 1 targets): eval consistency, reduce semantics, apply correctness.

Sorry (hard): canonicity theorem, node-bead bijection, all bounds theorems.

## ZDDs

Zero-suppressed Decision Diagrams (Minato) use a different reduction rule: suppress when HI → ⊥ (vs BDD: suppress when LO = HI). Better for sparse set families. Stubbed for Phase 2.
