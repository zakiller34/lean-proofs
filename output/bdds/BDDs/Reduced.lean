import Mathlib.Tactic
import BDDs.BDDTree

/-!
# Reduced BDD Predicate

Defines the reduction invariant: no redundant nodes (LO ≠ HI) and
no semantically equivalent subtrees.
Based on Knuth TAOCP 7.1.4.
-/

namespace BDD

variable {n : ℕ}

/-- Reduced predicate on BDDTree: no redundant nodes, no semantically equiv subtrees. -/
inductive BDDTree.IsReduced : BDDTree n → Prop where
  | leaf : ∀ b, BDDTree.IsReduced (.leaf b)
  | node : ∀ {v : Fin n} {lo hi : BDDTree n},
      ¬BDDTree.semEq lo hi →
      BDDTree.IsReduced lo →
      BDDTree.IsReduced hi →
      BDDTree.IsReduced (.node v lo hi)

end BDD
