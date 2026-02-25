/-
  BinaryAddition/Defs.lean — Shared definitions for binary addition formalization

  Defines generate, propagate, the carry-pair operator ∘, and block generate/propagate.
  These are the building blocks shared across Brent-Kung 1982, Kogge-Stone 1973, and Brent 1970.

  References:
  - Brent & Kung 1982, "A Regular Layout for Parallel Adders", §2
  - Kogge & Stone 1973, "A Parallel Algorithm for the Efficient Solution of a General
    Class of Recurrence Equations", §3
-/
import Mathlib.Tactic

namespace BinaryAddition

/-! ## D1, D2: Generate and Propagate bits -/

/-- Generate bit at position i: both input bits are 1 (carry is generated). -/
def generate (i : Nat) (x y : BitVec w) : Bool :=
  x.getLsbD i && y.getLsbD i

/-- Propagate bit at position i: exactly one input bit is 1 (carry is propagated). -/
def propagate (i : Nat) (x y : BitVec w) : Bool :=
  x.getLsbD i ^^ y.getLsbD i

/-! ## D3: GenPropPair — a (generate, propagate) pair -/

/-- A carry pair where `generate` = "generates carry" and `propagate` = "propagates carry". -/
@[ext] structure GenPropPair where
  generate  : Bool
  propagate : Bool
  deriving DecidableEq, Repr

/-! ## D4: The ∘ operator on carry pairs (Brent-Kung §2) -/

/-- The carry-pair composition operator.
    (g, p) ∘ (g', p') = (g ∨ (p ∧ g'), p ∧ p')
    This composes the carry behavior of two adjacent bit-blocks. -/
def gpOp (a b : GenPropPair) : GenPropPair :=
  ⟨a.generate || (a.propagate && b.generate), a.propagate && b.propagate⟩

scoped infixl:70 " ∘ " => gpOp

/-! ## D5: Block generate/propagate — prefix fold of gpOp -/

/-- Block generate/propagate for bits [0, i).
    Computes the cumulative carry behavior from bit 0 through bit i-1.
    - blockGP 0 returns ⟨false, true⟩ as identity for ∘.
    - blockGP (n+1) = ⟨generate n, propagate n⟩ ∘ (blockGP n).
    The key invariant is: (blockGP i x y).generate = BitVec.carry i x y false. -/
def blockGP (i : Nat) (x y : BitVec w) : GenPropPair :=
  match i with
  | 0 => ⟨false, true⟩  -- identity: no generation, full propagation
  | n + 1 => ⟨generate n x y, propagate n x y⟩ ∘ blockGP n x y

/-! ## Unfolding lemmas -/

@[simp] theorem blockGP_zero (x y : BitVec w) :
    blockGP 0 x y = ⟨false, true⟩ := rfl

theorem blockGP_succ (i : Nat) (x y : BitVec w) :
    blockGP (i + 1) x y =
      ⟨generate i x y, propagate i x y⟩ ∘ blockGP i x y := rfl

@[simp] theorem gpOp_generate (a b : GenPropPair) :
    (a ∘ b).generate = (a.generate || (a.propagate && b.generate)) := rfl

@[simp] theorem gpOp_propagate (a b : GenPropPair) :
    (a ∘ b).propagate = (a.propagate && b.propagate) := rfl

/-! ## Key bridge lemma: atLeastTwo ↔ generate/propagate formulation -/

/-- Bool.atLeastTwo a b c equals (a && b) || ((a ^^ b) && c).
    This bridges stdlib's carry definition with the generate/propagate formulation. -/
theorem atLeastTwo_eq_gp (a b c : Bool) :
    Bool.atLeastTwo a b c = ((a && b) || ((a ^^ b) && c)) := by
  cases a <;> cases b <;> cases c <;> rfl

end BinaryAddition
