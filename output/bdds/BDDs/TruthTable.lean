import Mathlib.Tactic
import BDDs.BoolFun

/-!
# Truth Tables

Truth table representation and the bead/square classification.
Based on Knuth TAOCP 7.1.4.
-/

namespace BDD

/-- A truth table of order `n` is a vector of `2^n` booleans. -/
def TruthTable (n : ℕ) := Fin (2 ^ n) → Bool

/-- Construct a truth table from a Boolean function. -/
def BoolFun.toTruthTable {n : ℕ} (f : BoolFun n) : TruthTable n :=
  fun i => f (fun k => (i.val / 2 ^ (n - 1 - k.val)) % 2 == 1)

/-- A truth table is a "square" if its top half equals its bottom half.
    That is, τ(i) = τ(i + 2^(n-1)) for all i < 2^(n-1). -/
def TruthTable.isSquare {n : ℕ} (t : TruthTable (n + 1)) : Prop :=
  ∀ i : Fin (2 ^ n),
    t ⟨i.val, by omega⟩ = t ⟨i.val + 2 ^ n, by omega⟩

/-- A truth table is a "bead" if it is NOT a square.
    Beads correspond 1-1 with nodes of the ROBDD. -/
def TruthTable.isBead {n : ℕ} (t : TruthTable (n + 1)) : Prop :=
  ¬t.isSquare

end BDD

