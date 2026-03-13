import Mathlib.Tactic
import Mathlib.Logic.Basic
import Mathlib.SetTheory.ZFC.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Topology.Basic
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.Irrational

/-!
# Examples for Chapters 1–3

Concrete computations and demonstrations for each chapter of
Schuller's "Geometric Anatomy of Theoretical Physics."
-/

/-! ## Chapter 1: Logic Examples -/

/-- Tautology: p → p is always true. -/
example (p : Prop) : p → p := id

/-- Modus ponens in action. -/
example (p q : Prop) (hp : p) (hpq : p → q) : q := hpq hp

/-- Contrapositive in action. -/
example (p q : Prop) (hnq : ¬q) (hpq : p → q) : ¬p := fun hp => hnq (hpq hp)

/-- Ex falso quodlibet: False implies anything. -/
example : False → (2 + 2 = 5) := False.elim

/-- Double negation elimination (classical). -/
example (p : Prop) (h : ¬¬p) : p := by tauto

/-- Law of excluded middle. -/
example (p : Prop) : p ∨ ¬p := em p

/-- De Morgan's laws. -/
example (p q : Prop) : ¬(p ∧ q) ↔ ¬p ∨ ¬q := by tauto
example (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by tauto

/-- Unique existence: there is exactly one natural number that is
    both ≤ 0 and ≥ 0 (namely 0). -/
example : ∃! n : ℕ, n ≤ 0 := by
  exact ⟨0, le_refl _, fun _ h => Nat.le_zero.mp h⟩

/-! ## Chapter 2: Set Theory / Arithmetic Examples -/

/-- Integer arithmetic via coercion from ℕ. -/
example : (2 : ℤ) + (-3 : ℤ) = -1 := by norm_num

/-- Rational arithmetic. -/
example : (1 : ℚ) / 3 + (1 : ℚ) / 6 = (1 : ℚ) / 2 := by norm_num

/-- ℕ coercion into ℤ preserves multiplication. -/
example (a b : ℕ) : (↑(a * b) : ℤ) = ↑a * ↑b := by push_cast; ring

/-- ℤ coercion into ℚ preserves subtraction. -/
example (a b : ℤ) : (↑(a - b) : ℚ) = ↑a - ↑b := by push_cast; ring

/-- The square root of 2 is irrational (a key fact in the ℚ → ℝ
    construction motivation). -/
example : Irrational (Real.sqrt 2) :=
  irrational_sqrt_two

/-- ZFSet: the empty set has no elements. -/
example : ∀ x : ZFSet, x ∉ (∅ : ZFSet) :=
  fun _ => ZFSet.not_mem_empty

/-! ## Chapter 3: Topology Examples -/

/-- ℝ is Hausdorff. -/
example : T2Space ℝ := inferInstance

/-- ℝ is paracompact. -/
example : ParacompactSpace ℝ := inferInstance

/-- [0, 1] is compact in ℝ. -/
example : IsCompact (Set.Icc (0 : ℝ) 1) :=
  isCompact_Icc

/-- The empty set is compact. -/
example : IsCompact (∅ : Set ℝ) := isCompact_empty

/-- A singleton is compact. -/
example (x : ℝ) : IsCompact ({x} : Set ℝ) := isCompact_singleton

/-- The open interval (0, 1) is NOT compact in ℝ. -/
example : ¬IsCompact (Set.Ioo (0 : ℝ) 1) := by
  intro h
  have hc := h.isClosed.closure_eq
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at hc
  have : (0 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [hc]; exact Set.left_mem_Icc.mpr (by norm_num)
  exact lt_irrefl 0 this.1

/-- In the discrete topology, every set is open. -/
example : IsOpen ({1, 2, 3} : Set (Fin 5)) :=
  isOpen_discrete _

/-- ℝ is a metric space. -/
example : MetricSpace ℝ := inferInstance

/-- Distance is symmetric. -/
example (x y : ℝ) : dist x y = dist y x := dist_comm x y

/-- Distance is non-negative. -/
example (x y : ℝ) : 0 ≤ dist x y := dist_nonneg
