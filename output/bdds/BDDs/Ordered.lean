import Mathlib.Tactic
import BDDs.BDDTree

/-!
# Ordered BDD Predicate

Defines the ordering invariant for BDDs: variables are tested in strictly ascending order
along any root-to-sink path.
Based on Knuth TAOCP 7.1.4.
-/

namespace BDD

variable {n : ℕ}

/-- Ordering on BDDTree: variables along any path are strictly ascending. -/
inductive BDDTree.IsOrdered : BDDTree n → Prop where
  | leaf : ∀ b, BDDTree.IsOrdered (.leaf b)
  | node : ∀ {v : Fin n} {lo hi : BDDTree n},
      (∀ v' lo' hi', lo = .node v' lo' hi' → v < v') →
      (∀ v' lo' hi', hi = .node v' lo' hi' → v < v') →
      BDDTree.IsOrdered lo →
      BDDTree.IsOrdered hi →
      BDDTree.IsOrdered (.node v lo hi)

/-- An ordered tree's lo subtree is ordered. -/
theorem BDDTree.IsOrdered.lo_ordered {v : Fin n} {lo hi : BDDTree n}
    (h : BDDTree.IsOrdered (.node v lo hi)) : BDDTree.IsOrdered lo := by
  cases h; assumption

/-- An ordered tree's hi subtree is ordered. -/
theorem BDDTree.IsOrdered.hi_ordered {v : Fin n} {lo hi : BDDTree n}
    (h : BDDTree.IsOrdered (.node v lo hi)) : BDDTree.IsOrdered hi := by
  cases h; assumption

end BDD
