import Mathlib.Tactic

/-!
# BDD Node Declarations

The fundamental node type for BDDs: sink (terminal) or branch (internal).
Based on Knuth TAOCP 7.1.4.
-/

namespace BDD

/-- A BDD node declaration. Variables indexed by `Fin n` for an `n`-variable function.
    - `sink b`: terminal node with value `b`
    - `branch v lo hi`: tests variable `v`, with `lo` (x_v=0) and `hi` (x_v=1) children -/
inductive Decl (n : ℕ) where
  | sink (val : Bool)
  | branch (v : Fin n) (lo hi : ℕ)
  deriving Repr, DecidableEq

/-- Get the variable index of a branch node, or `none` for sinks. -/
def Decl.var? {n : ℕ} : Decl n → Option (Fin n)
  | .sink _ => none
  | .branch v _ _ => some v

/-- Check if a declaration is a sink. -/
def Decl.isSink {n : ℕ} : Decl n → Bool
  | .sink _ => true
  | .branch _ _ _ => false

end BDD

