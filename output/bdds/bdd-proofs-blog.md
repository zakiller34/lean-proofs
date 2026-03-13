# BDD Proofs: Filling the Phase 1 Sorries

How we proved the 4 core BDD theorems in Lean 4.

## 1. `eval_eq_tree_eval` (Eval.lean)

**Statement**: Evaluating an array-based BDD equals evaluating its tree representation.

**Technique**: Strong induction on the node index via `Nat.strongRecOn`. Both `evalNode` and `toTreeNode` share identical recursive structure — they pattern-match on `bdd.nodes[i]`, handle sinks trivially, and recurse on lo/hi children (which have smaller indices by the DAG property).

The proof:
1. Generalize to a helper lemma for arbitrary index `i`
2. `unfold evalNode toTreeNode` to expose the match
3. Sink case: `simp [BDDTree.eval_leaf]`
4. Branch case: `congr 1` reduces to IH applications on lo and hi (both `< i` from `is_dag`)

**Key pattern**: When two recursive functions share the same termination argument and branching structure, prove their equivalence by strong induction on that argument and unfold both simultaneously.

## 2. `apply_correct` (AlgorithmS.lean)

**Statement**: `(apply op t₁ t₂).eval σ = op (t₁.eval σ) (t₂.eval σ)`

**Technique**: Lean 4's functional induction via `BDDTree.apply.induct`. This generates one case per match arm in the `apply` definition — 6 cases total:

| Case | t₁ | t₂ | Key step |
|------|----|----|----------|
| 1 | leaf a | leaf b | `simp` |
| 2 | leaf a | node v lo hi | `split` on σ v, apply IH |
| 3 | node v lo hi | leaf b | same |
| 4 | node v₁ _ _ | node v₂ _ _ (v₁<v₂) | `split` on σ v₁, IH |
| 5 | node v₁ _ _ | node v₂ _ _ (v₂<v₁) | `split` on σ v₂, IH |
| 6 | node v₁ _ _ | node v₂ _ _ (v₁=v₂) | `subst`, `split`, IH |

Each case after unfolding `apply` and `eval` reduces to `split <;> simp only [] <;> assumption`.

**Key pattern**: Functional induction (`f.induct`) is the ideal tactic for proving properties of well-founded recursive functions — it gives you exactly the cases the function considers.

## 3. `reduce_semEq` (AlgorithmR.lean)

**Statement**: `∀ σ, t.eval σ = t.reduce.eval σ`

**Technique**: Structural induction on `t`, then `split` on whether `lo.reduce = hi.reduce`.

- **Leaf**: `rfl`
- **Node, lo'=hi'** (redundant elimination): If `σ v = false`, use `ih_lo`. If `σ v = true`, chain `ih_hi` with the equality `lo.reduce.eval σ = hi.reduce.eval σ` from `congrFun (congrArg eval h) σ`.
- **Node, lo'≠hi'**: Both branches follow directly from IH.

**Key pattern**: When a function has an `if` branch, use `split` to case-split, then exploit the condition in each branch.

## 4. `reduce_isOrdered` + `reduce_isReduced` (AlgorithmR.lean)

**Ordering preservation** needed a helper lemma `reduce_preserves_var_bound`: if all top-level variables in `t` are `> v`, the same holds for `t.reduce`. Proved by matching on `t` — the redundancy-elimination case recurses into the lo subtree; the non-redundant case uses `BDDTree.node.inj`.

**Reducedness** is the hard direction: proving `lo.reduce ≠ hi.reduce → ¬semEq lo.reduce hi.reduce`. This is essentially the canonicity theorem (structural distinctness ↔ semantic distinctness for ordered reduced trees), which is `robdd_canonical` — a Phase 2 result. Left as the one remaining sorry in AlgorithmR.

## Tactic Patterns Summary

| Pattern | When to use |
|---------|-------------|
| `Nat.strongRecOn` | WF recursion on ℕ with `termination_by i` |
| `f.induct` | Functional induction matching recursive definition |
| `split` after `simp only [f]` | Case-split on `if` inside unfolded definition |
| `congr 1` | Reduce `f x₁ = f x₂` to `x₁ = x₂` |
| `congrFun (congrArg f h) x` | From `a = b` derive `f a x = f b x` |
