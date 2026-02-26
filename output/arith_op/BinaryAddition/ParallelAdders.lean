/-
  BinaryAddition/ParallelAdders.lean — Parallel adder equations and theorems

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

/-! ## Algebraic instances -/

instance : Mul GenPropPair := ⟨gpOp⟩
instance : One GenPropPair := ⟨⟨false, true⟩⟩

@[simp] theorem mul_def (a b : GenPropPair) : a * b = a ∘ b := rfl
@[simp] theorem one_def : (1 : GenPropPair) = ⟨false, true⟩ := rfl

instance : Monoid GenPropPair where
  mul_assoc := gpOp_assoc
  one_mul := gpOp_id_left
  mul_one := gpOp_id_right

theorem mul_eq_gpOp (a b : GenPropPair) : a * b = a ∘ b := rfl

/-! ## Named elements -/

/-- Kill: absorbs carry (neither generates nor propagates). Bottom element. -/
def gpKill : GenPropPair := ⟨false, false⟩
/-- Propagate: passes carry through. Equals `1` (identity for ∘). -/
def gpPropagate : GenPropPair := ⟨false, true⟩
/-- Generate: creates a new carry. -/
def gpGenerate : GenPropPair := ⟨true, false⟩

@[simp] theorem gpPropagate_eq_one : gpPropagate = 1 := rfl

/-! ## Partial order (product order on Bool × Bool) -/

instance : LE GenPropPair :=
  ⟨fun a b => a.generate ≤ b.generate ∧ a.propagate ≤ b.propagate⟩

instance : LT GenPropPair :=
  ⟨fun a b => a ≤ b ∧ ¬b ≤ a⟩

@[simp] theorem GenPropPair.le_def (a b : GenPropPair) :
    a ≤ b ↔ a.generate ≤ b.generate ∧ a.propagate ≤ b.propagate := Iff.rfl

instance : PartialOrder GenPropPair where
  le_refl a := ⟨le_refl _, le_refl _⟩
  le_trans _ _ _ hab hbc := ⟨le_trans hab.1 hbc.1, le_trans hab.2 hbc.2⟩
  le_antisymm _ _ hab hba :=
    GenPropPair.ext (le_antisymm hab.1 hba.1) (le_antisymm hab.2 hba.2)

/-! ## Order lemmas -/

@[simp] theorem gpKill_le (a : GenPropPair) : gpKill ≤ a :=
  ⟨Bool.false_le _, Bool.false_le _⟩

theorem gpGenerate_gpPropagate_incomparable :
    ¬(gpGenerate ≤ gpPropagate) ∧ ¬(gpPropagate ≤ gpGenerate) := by
  constructor
  · intro ⟨h, _⟩; exact absurd h (by decide)
  · intro ⟨_, h⟩; exact absurd h (by decide)

/-! ## Monotonicity of ∘ -/

theorem gpOp_right_mono (a : GenPropPair) {b b' : GenPropPair} (h : b ≤ b') :
    a ∘ b ≤ a ∘ b' := by
  obtain ⟨hg, hp⟩ := h
  constructor
  · simp only [gpOp_generate]
    cases a.generate <;> cases a.propagate <;> simp_all
  · simp only [gpOp_propagate]
    cases a.propagate <;> simp_all

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
