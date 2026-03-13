import Mathlib.Tactic
import BDDs.BoolFun

/-!
# BDD Tree (Specification Side)

Inductive tree type for BDDs used in proofs. This is the "spec" representation
that's easy to reason about, as opposed to the array-based "impl" representation.
Based on Knuth TAOCP 7.1.4.
-/

namespace BDD

/-- Inductive BDD tree for `n`-variable Boolean functions.
    This is the specification-side type used for proofs. -/
inductive BDDTree (n : ℕ) where
  | leaf (val : Bool)
  | node (v : Fin n) (lo hi : BDDTree n)
  deriving Repr, DecidableEq

namespace BDDTree

variable {n : ℕ}

/-- Evaluate a BDD tree on an assignment. -/
def eval : BDDTree n → (Fin n → Bool) → Bool
  | .leaf b, _ => b
  | .node v lo hi, σ => if σ v then hi.eval σ else lo.eval σ

/-- The constant-false tree. -/
def falseTree : BDDTree n := .leaf false

/-- The constant-true tree. -/
def trueTree : BDDTree n := .leaf true

/-- A leaf evaluates to its constant. -/
@[simp]
theorem eval_leaf (b : Bool) (σ : Fin n → Bool) : (leaf b).eval σ = b := rfl

/-- A node evaluates by branching on its variable. -/
@[simp]
theorem eval_node (v : Fin n) (lo hi : BDDTree n) (σ : Fin n → Bool) :
    (node v lo hi).eval σ = if σ v then hi.eval σ else lo.eval σ := rfl

/-- BDD tree evaluation agrees with Shannon expansion. -/
theorem eval_shannon (t : BDDTree n) (v : Fin n) (lo hi : BDDTree n)
    (h : t = node v lo hi) (σ : Fin n → Bool) :
    t.eval σ = ((!(σ v) && lo.eval σ) || (σ v && hi.eval σ)) := by
  subst h
  simp [eval]
  cases σ v <;> simp

/-- Two trees are semantically equivalent if they evaluate the same on all inputs. -/
def semEq (t₁ t₂ : BDDTree n) : Prop :=
  ∀ σ, t₁.eval σ = t₂.eval σ

/-- Number of internal nodes in a tree. -/
def size : BDDTree n → ℕ
  | .leaf _ => 0
  | .node _ lo hi => 1 + lo.size + hi.size

end BDDTree

end BDD

