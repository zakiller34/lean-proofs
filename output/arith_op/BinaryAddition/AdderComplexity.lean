/-
  BinaryAddition/AdderComplexity.lean — Adder-specific complexity definitions

  Formalizes adder-specific results from "On the Addition of Binary Numbers" (Brent 1970):
  - D12: Group propagate/generate definitions
  - T9: Carry group decomposition (Lemma 1)
-/
import BinaryAddition.Defs
import BinaryAddition.ParallelAdders
import BinaryAddition.CircuitDefs
import Mathlib.Tactic

namespace BinaryAddition

/-! ## D12: Group propagate and group generate -/

/-- Group propagate: AND of propagate bits in range [lo, hi). -/
def groupPropagate (lo hi : Nat) (x y : BitVec w) : Bool :=
  (blockGP_range lo hi x y).propagate

/-- Group generate: carry generated within [lo, hi) with carry-in = 0.
    Equals the first component of blockGP_range. -/
def groupGenerate (lo hi : Nat) (x y : BitVec w) : Bool :=
  (blockGP_range lo hi x y).generate

/-! ## T9: Carry group decomposition (Brent 1970, Lemma 1)

    The carry at position hi+1 decomposes as:
    c_{hi+1} = G_{[lo,hi+1)} ∨ (P_{[lo,hi+1)} ∧ c_lo)

    This is carry_decompose from ParallelAdders, restated with group terminology. -/

theorem carry_group_decomposition (lo hi : Nat) (hlo : lo ≤ hi) (x y : BitVec w) :
    BitVec.carry (hi + 1) x y false =
      (groupGenerate lo (hi + 1) x y ||
       (groupPropagate lo (hi + 1) x y && BitVec.carry lo x y false)) := by
  exact carry_decompose lo hi hlo x y

end BinaryAddition
