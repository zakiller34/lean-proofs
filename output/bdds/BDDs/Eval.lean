import Mathlib.Tactic
import BDDs.BDD
import BDDs.BDDTree

/-!
# BDD Evaluation

Evaluation functions for array-based BDDs and consistency with BDDTree evaluation.
Based on Knuth TAOCP 7.1.4.
-/

namespace BDD

variable {n : ℕ}

/-- Evaluate a node in an array BDD by recursive descent. -/
def ArrayBDD.evalNode (bdd : ArrayBDD n) (σ : Fin n → Bool) (i : ℕ) (hi : i < bdd.nodes.size) : Bool :=
  match h : bdd.nodes[i] with
  | .sink b => b
  | .branch v lo hi_idx =>
    have dag := bdd.is_dag i hi
    have hdag : lo < i ∧ hi_idx < i := by rwa [h] at dag
    let lo_val := bdd.evalNode σ lo (by omega)
    let hi_val := bdd.evalNode σ hi_idx (by omega)
    if σ v then hi_val else lo_val
termination_by i

/-- Evaluate a BDD at an assignment. -/
def ArrayBDD.eval (bdd : ArrayBDD n) (σ : Fin n → Bool) : Bool :=
  bdd.evalNode σ bdd.root bdd.root_valid

/-- Convert a node in an array BDD to a BDDTree. -/
def ArrayBDD.toTreeNode (bdd : ArrayBDD n) (i : ℕ) (hi : i < bdd.nodes.size) : BDDTree n :=
  match h : bdd.nodes[i] with
  | .sink b => .leaf b
  | .branch v lo hi_idx =>
    have dag := bdd.is_dag i hi
    have hdag : lo < i ∧ hi_idx < i := by rwa [h] at dag
    .node v (bdd.toTreeNode lo (by omega)) (bdd.toTreeNode hi_idx (by omega))
termination_by i

/-- Convert a BDD to a BDDTree (from the root). -/
def ArrayBDD.toTree (bdd : ArrayBDD n) : BDDTree n :=
  bdd.toTreeNode bdd.root bdd.root_valid

/-- Helper: evalNode agrees with toTreeNode.eval at any valid index. -/
theorem ArrayBDD.evalNode_eq_toTreeNode_eval (bdd : ArrayBDD n) (σ : Fin n → Bool)
    (i : ℕ) (hi : i < bdd.nodes.size) :
    bdd.evalNode σ i hi = (bdd.toTreeNode i hi).eval σ := by
  induction i using Nat.strongRecOn with
  | _ i ih =>
    unfold evalNode toTreeNode
    split
    · -- sink case
      simp [BDDTree.eval_leaf]
    · -- branch case
      next v lo hi_idx h =>
      simp [BDDTree.eval_node]
      have dag := bdd.is_dag i hi
      rw [h] at dag
      congr 1
      · -- hi branch
        exact ih hi_idx (by omega) (by omega)
      · -- lo branch
        exact ih lo (by omega) (by omega)

/-- Evaluating a BDD equals evaluating its tree. -/
theorem ArrayBDD.eval_eq_tree_eval (bdd : ArrayBDD n) (σ : Fin n → Bool) :
    bdd.eval σ = bdd.toTree.eval σ := by
  exact bdd.evalNode_eq_toTreeNode_eval σ bdd.root bdd.root_valid

end BDD
