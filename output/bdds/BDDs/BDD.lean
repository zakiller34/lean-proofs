import Mathlib.Tactic
import BDDs.Node

/-!
# Array-Based BDD

Array-backed BDD representation for algorithms, following the AIG pattern from `Std.Sat.AIG`.
Convention: index 0 = ⊥ (false sink), index 1 = ⊤ (true sink).
Based on Knuth TAOCP 7.1.4.
-/

namespace BDD

/-- An array-based BDD for `n`-variable Boolean functions.
    Nodes are stored in a topologically sorted array.
    Indices 0 and 1 are reserved for ⊥ and ⊤ sinks.
    `root` is the index of the root node. -/
structure ArrayBDD (n : ℕ) where
  nodes : Array (Decl n)
  root : ℕ
  size_pos : nodes.size ≥ 2
  root_valid : root < nodes.size
  false_sink : nodes[0]'(by omega) = Decl.sink false
  true_sink : nodes[1]'(by omega) = Decl.sink true
  is_dag : ∀ i (hi : i < nodes.size),
    match nodes[i] with
    | .sink _ => True
    | .branch _ lo hi_idx => lo < i ∧ hi_idx < i

namespace ArrayBDD

variable {n : ℕ}

/-- Number of nodes in the BDD (including sinks). -/
def size (bdd : ArrayBDD n) : ℕ := bdd.nodes.size

/-- Number of internal (branch) nodes. -/
def numBranches (bdd : ArrayBDD n) : ℕ := bdd.size - 2

/-- Get the declaration at index `i`. -/
def getDecl (bdd : ArrayBDD n) (i : ℕ) (h : i < bdd.nodes.size) : Decl n :=
  bdd.nodes[i]

private def sinkArray : Array (Decl n) := #[Decl.sink false, Decl.sink true]

private theorem sinkArray_size : (sinkArray : Array (Decl n)).size = 2 := by
  simp [sinkArray]

private theorem sinkArray_dag (i : ℕ) (hi : i < (sinkArray : Array (Decl n)).size) :
    match (sinkArray : Array (Decl n))[i] with
    | .sink _ => True
    | .branch _ lo hi_idx => lo < i ∧ hi_idx < i := by
  have h2 : i < 2 := by rwa [sinkArray_size] at hi
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl <;> simp [sinkArray]

/-- The trivial BDD representing `false`. -/
def mkFalse : ArrayBDD n where
  nodes := sinkArray
  root := 0
  size_pos := by rw [sinkArray_size]
  root_valid := by rw [sinkArray_size]; omega
  false_sink := by simp [sinkArray]
  true_sink := by simp [sinkArray]
  is_dag := sinkArray_dag

/-- The trivial BDD representing `true`. -/
def mkTrue : ArrayBDD n where
  nodes := sinkArray
  root := 1
  size_pos := by rw [sinkArray_size]
  root_valid := by rw [sinkArray_size]; omega
  false_sink := by simp [sinkArray]
  true_sink := by simp [sinkArray]
  is_dag := sinkArray_dag

end ArrayBDD

end BDD
