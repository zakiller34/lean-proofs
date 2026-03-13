# BDD Extensions: Quantification, ZDD Algebra, Algorithm B

New formalizations added to the BDD library, based on Knuth TAOCP 7.1.4.

## Quantification (Quantify.lean)

### Restriction (Cofactor)

`BDDTree.restrictVar v b t` sets variable `v` to constant `b` in tree `t`. Implementation: when we hit a node testing `v`, follow the `lo` (b=false) or `hi` (b=true) branch; otherwise recurse on both children.

Correctness: `(t.restrictVar v b).eval σ = t.eval (Function.update σ v b)`. Proved by structural induction — the key step uses `Function.update_self` when `w = v` and `Function.update_of_ne` when `w ≠ v`.

### Existential and Universal Quantification

Built on top of restriction and the `apply` operator:

```
∃v. f  =  f|_{v=0} ∨ f|_{v=1}
∀v. f  =  f|_{v=0} ∧ f|_{v=1}
```

In Lean:
```lean
def BDDTree.exists v t := apply (· || ·) (t.restrictVar v false) (t.restrictVar v true)
def BDDTree.forall v t := apply (· && ·) (t.restrictVar v false) (t.restrictVar v true)
```

Correctness follows directly from `apply_correct` and `restrictVar_correct` — each proof is a two-line rewrite chain.

## ZDD Family Algebra (ZDD.lean)

### New Operations

Three family-algebra operations on ZDD trees:

- **Union** (`ZDDTree.union`): merge two families. Like BDD apply, but handles the `empty`/`unit` base cases and ZDD's asymmetric structure.
- **Intersection** (`ZDDTree.inter`): families in both. When hi-branch intersection yields `empty`, suppress the node (ZDD reduction).
- **Difference** (`ZDDTree.diff`): families in first but not second. Same suppression rule.

All three are well-founded recursive on `size t₁ + size t₂`, with the same variable-comparison logic as BDD apply for the node-node case.

### New Predicates

- `ZDDTree.IsOrdered`: variables strictly ascending along paths (mirrors BDD ordering)
- `ZDDTree.size`: structural size for termination proofs

### Correctness Statements

```lean
theorem union_correct : (union t₁ t₂).families = t₁.families ∪ t₂.families
theorem inter_correct : (inter t₁ t₂).families = t₁.families ∩ t₂.families
theorem diff_correct  : (diff t₁ t₂).families  = t₁.families \ t₂.families
```

These are stated with `Finset` operations and left as sorry — they require functional induction similar to `apply_correct`, plus `Finset.image_union`, `Finset.image_inter`, etc.

## Algorithm B: Maximum Weight (AlgorithmB.lean)

### The Problem

Given a BDD representing a Boolean function and real-valued weights `w : Fin n → ℝ` for each variable, find the maximum-weight satisfying assignment (where weight = sum of `w i` for variables set to true).

### The Algorithm

Bottom-up DP on the tree:
- `leaf true` → weight 0 (empty assignment satisfies)
- `leaf false` → ⊥ (unsatisfiable)
- `node v lo hi` → combine lo-weight (don't include v) with hi-weight + w(v) (include v)

Uses `WithBot ℝ` to handle the unsatisfiable case cleanly.

### Definitions

```lean
def assignmentWeight (w : Fin n → ℝ) (σ : Fin n → Bool) : ℝ :=
  ∑ i : Fin n, if σ i then w i else 0

def BDDTree.maxWeight (w : Fin n → ℝ) : BDDTree n → WithBot ℝ
```

### Correctness Statements

Two theorems (sorry):
1. `maxWeight_bot_iff_unsat`: returns ⊥ iff no satisfying assignment
2. `maxWeight_correct`: the weight returned is achieved by some satisfying assignment, and is maximal

These require induction on the tree with careful `WithBot` case analysis.

## Module Map (Updated)

```
BoolFun ← Node ← BDDTree ← BDD ← Eval
                     ↑
              Ordered  Reduced ← ROBDD
                     ↑
         AlgorithmC  AlgorithmR  AlgorithmS ← Quantify
                     ↑
              TruthTable  NodeBead  Bounds
                     ↑
              AlgorithmB  ZDD
```
