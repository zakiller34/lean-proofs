/-
  BinaryAddition/BrentKung.lean — Brent-Kung 1982 theorems

  Core results from "A Regular Layout for Parallel Adders" (Brent & Kung 1982):
  - T1: ∘ is associative (Lemma 2)
  - T2: carry equals block generate (Lemma 1)
  - T3: sum bit = propagate XOR carry (derived from getLsbD_add)
  - T4: block GP splits at any point (enables divide-and-conquer)
-/
import BinaryAddition.Defs

namespace BinaryAddition

/-! ## ∘ identity lemmas -/

@[simp] theorem gpOp_id_right (a : GenPropPair) : a ∘ ⟨false, true⟩ = a := by
  obtain ⟨g, p⟩ := a; simp [gpOp]

@[simp] theorem gpOp_id_left (a : GenPropPair) : ⟨false, true⟩ ∘ a = a := by
  obtain ⟨g, p⟩ := a; simp [gpOp]

/-! ## T1: Associativity of ∘ (Brent-Kung Lemma 2) -/

theorem gpOp_assoc (a b c : GenPropPair) :
    (a ∘ b) ∘ c = a ∘ (b ∘ c) := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b; obtain ⟨c1, c2⟩ := c
  simp only [gpOp, GenPropPair.mk.injEq]
  constructor <;> cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> cases c1 <;> cases c2 <;> rfl

/-! ## T2: Carry equals block generate (Brent-Kung Lemma 1) -/

theorem carry_eq_blockGenerate (i : Nat) (x y : BitVec w) :
    BitVec.carry i x y false = (blockGP i x y).generate := by
  induction i with
  | zero => simp [blockGP]
  | succ n ih =>
    simp only [BitVec.carry_succ, atLeastTwo_eq_gp, blockGP_succ, gpOp_generate,
      ih, generate, propagate]

/-! ## T3: Sum bit = propagate XOR carry -/

theorem sum_eq_propagate_xor_carry {w : Nat} (i : Nat) (hi : i < w)
    (x y : BitVec w) :
    (x + y).getLsbD i = (propagate i x y ^^ BitVec.carry i x y false) := by
  rw [BitVec.getLsbD_add hi]
  simp [propagate]

/-! ## T4: Block GP splits at any point -/

/-- Block generate/propagate for bits [lo, hi). -/
def blockGP_range (lo hi : Nat) (x y : BitVec w) : GenPropPair :=
  match hi with
  | 0 => ⟨false, true⟩
  | n + 1 =>
    if n < lo then ⟨false, true⟩
    else ⟨generate n x y, propagate n x y⟩ ∘ blockGP_range lo n x y

theorem blockGP_range_zero (hi : Nat) (x y : BitVec w) :
    blockGP_range 0 hi x y = blockGP hi x y := by
  induction hi with
  | zero => rfl
  | succ n ih =>
    unfold blockGP_range
    rw [if_neg (by omega : ¬ n < 0)]
    rw [ih, ← blockGP_succ]

theorem blockGP_split (i j : Nat) (hj : j ≤ i) (x y : BitVec w) :
    blockGP i x y = (blockGP_range j i x y) ∘ (blockGP j x y) := by
  induction i generalizing j with
  | zero =>
    have := Nat.eq_zero_of_le_zero hj; subst this
    simp [blockGP_range, blockGP]
  | succ n ih =>
    by_cases hjn : j = n + 1
    · subst hjn; simp [blockGP_range]
    · have hjn' : j ≤ n := by omega
      conv_lhs => rw [blockGP_succ]
      unfold blockGP_range
      rw [if_neg (by omega : ¬ n < j)]
      rw [ih j hjn', gpOp_assoc]

/-- Carry decomposes at a split point. -/
theorem carry_decompose (lo hi : Nat) (hlo : lo ≤ hi) (x y : BitVec w) :
    BitVec.carry (hi + 1) x y false =
      ((blockGP_range lo (hi + 1) x y).generate ||
       ((blockGP_range lo (hi + 1) x y).propagate && BitVec.carry lo x y false)) := by
  rw [carry_eq_blockGenerate (hi + 1), blockGP_split (hi + 1) lo (by omega)]
  simp [gpOp, carry_eq_blockGenerate lo]

end BinaryAddition
