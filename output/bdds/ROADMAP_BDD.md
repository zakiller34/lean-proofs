# BDD Formalization Roadmap

Based on Knuth TAOCP 7.1.4. AMS codes: 68Q05 (formal languages/automata), 94C10 (switching theory).

## Module Status

| Module | Description | Status | Sorries |
|--------|-------------|--------|---------|
| BoolFun | Boolean functions, Shannon expansion | DONE | 0 |
| Node | Inductive node declarations | DONE | 0 |
| BDDTree | Spec-side inductive tree + eval | DONE | 0 |
| BDD | Array-based DAG BDD (AIG-style) | DONE | 0 |
| Eval | BDD.eval, toTree, consistency | DONE | 0 |
| Ordered | IsOrdered predicate on BDDTree | DONE | 0 |
| Reduced | IsReduced predicate on BDDTree | DONE | 0 |
| ROBDD | IsROBDD + canonicity theorem | PARTIAL | 1 (robdd_canonical) |
| TruthTable | TruthTable, isSquare, isBead | DONE | 0 |
| NodeBead | Node-bead bijection | STUB | deferred |
| AlgorithmC | countSolutions + correctness | DONE | 0 |
| AlgorithmR | reduce + semantics + ROBDD | PARTIAL | 1 (reduce_isReduced needs canonicity) |
| AlgorithmS | apply (AND/OR/XOR) + NOT | DONE | 0 |
| Bounds | Theorems M, U, Bryant | STMT ONLY | 3 |
| Quantify | restrictVar, exists, forall | DONE | 0 |
| AlgorithmB | Max-weight satisfying assignment | PARTIAL | 2 |
| ZDD | ZDD trees, family algebra | PARTIAL | 3 (union/inter/diff correctness) |

## Sorry Inventory

### Proved (Phase 1 complete)

| Theorem | File | Technique |
|---------|------|-----------|
| `eval_eq_tree_eval` | Eval.lean | `Nat.strongRecOn`, unfold both defs |
| `reduce_semEq` | AlgorithmR.lean | Structural induction, split on lo'=hi' |
| `reduce_isOrdered` | AlgorithmR.lean | Helper `reduce_preserves_var_bound` |
| `apply_correct` | AlgorithmS.lean | Functional induction via `apply.induct` |
| `restrictVar_correct` | Quantify.lean | Structural induction + `Function.update` |
| `exists_correct` | Quantify.lean | Rewrite chain from apply_correct + restrictVar_correct |
| `forall_correct` | Quantify.lean | Same |

### Remaining — Hard / Deferred

| Theorem | File | Notes |
|---------|------|-------|
| `robdd_canonical` | ROBDD.lean | Bryant's theorem; induction on n, Shannon expansion |
| `reduce_isReduced` (1 sorry) | AlgorithmR.lean | Needs canonicity: structural ≠ → semantic ≠ |
| `maxWeight_bot_iff_unsat` | AlgorithmB.lean | Induction on tree, WithBot case analysis |
| `maxWeight_correct` | AlgorithmB.lean | Induction + witness construction |
| `union_correct` | ZDD.lean | Functional induction + Finset lemmas |
| `inter_correct` | ZDD.lean | Same + ZDD suppression |
| `diff_correct` | ZDD.lean | Same |
| `node_bead_bijection` | NodeBead.lean | Needs bead counting infrastructure |
| `theorem_U` | Bounds.lean | Combinatorial counting |
| `theorem_M` | Bounds.lean | Network model / communication complexity |
| `theorem_Bryant` | Bounds.lean | Exponential lower bound |

## Documentation

- `bdd-proofs-blog.md` — Phase 1 proof techniques
- `bdd-extensions-blog.md` — Quantification, ZDD algebra, Algorithm B
