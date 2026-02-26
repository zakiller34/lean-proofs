/-
  BinaryAddition/CircuitDefs.lean — Circuit model definitions

  Defines a concrete circuit model: a BoolCircuit is a DAG of AND/OR/XOR/NOT gates
  with bounded fan-in r. The depth is the longest path from any input to an output.

  Reference: Brent 1970, "On the Addition of Binary Numbers"
-/
import Mathlib.Tactic

namespace BinaryAddition

/-- A circuit gate type. -/
inductive GateOp where
  | and | or | xor | not
  deriving DecidableEq

/-- A circuit is a list of gates, each referencing inputs by index.
    Gate i can reference any input or gate j < i. -/
structure BoolCircuit (numInputs : Nat) where
  /-- Number of gates -/
  numGates : Nat
  /-- Each gate's operation -/
  ops : Fin numGates → GateOp
  /-- Each gate's input indices (into inputs ++ previous gates) -/
  inputs : Fin numGates → List (Fin (numInputs + numGates))
  /-- Fan-in bound -/
  fanIn : Nat
  /-- All gates respect fan-in -/
  fanIn_bound : ∀ g, (inputs g).length ≤ fanIn

/-- Depth of a node in the circuit.
    Computing this requires the circuit to be acyclic (gates only reference earlier indices).
    We constrain: gate i can only reference inputs or gates j with j < numInputs + i. -/
structure AcyclicCircuit (numInputs : Nat) extends BoolCircuit numInputs where
  /-- Acyclicity: each gate references only earlier nodes -/
  acyclic : ∀ (g : Fin numGates) (inp : Fin (numInputs + numGates)),
    inp ∈ inputs g → inp.val < numInputs + g.val

end BinaryAddition
