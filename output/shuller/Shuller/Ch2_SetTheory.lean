/-!
# Chapter 2: Zermelo-Fraenkel Set Theory (ZFC)

Schuller rejects naive set theory (Russell's Paradox) and builds the
mathematical universe using the ∈-relation and 9 axioms. We showcase
these via Mathlib's `ZFSet` and demonstrate the number constructions.
-/

import Mathlib.SetTheory.ZFC.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic

/-! ## ZFC Axioms via Mathlib's ZFSet

Mathlib's `ZFSet` (also known as `Set.{u}` in the ZFC module) provides
a model of ZFC within Lean's type theory. We state the key axioms
as theorems about `ZFSet`. -/

/-- Axiom 1 (Extensionality): Two sets are equal iff they have the
    same elements. This is `ZFSet.ext` in Mathlib. -/
theorem zfc_extensionality (a b : ZFSet) :
    (∀ x, x ∈ a ↔ x ∈ b) → a = b := by
  exact ZFSet.ext

/-- Axiom 2 (Empty Set): The empty set exists. -/
theorem zfc_empty_set_exists : ∃ e : ZFSet, ∀ x, x ∉ e := by
  exact ⟨∅, ZFSet.notMem_empty⟩

/-- Axiom 3 (Separation/Specification): For any set and predicate,
    the subset satisfying the predicate exists. -/
theorem zfc_separation (a : ZFSet) (P : ZFSet → Prop) :
    ∃ b : ZFSet, ∀ x, x ∈ b ↔ x ∈ a ∧ P x := by
  exact ⟨a.sep P, fun x => ZFSet.mem_sep⟩

/-- Axiom 4 (Pairing): For any two sets, their pair exists. -/
theorem zfc_pairing (a b : ZFSet) :
    ∃ c : ZFSet, a ∈ c ∧ b ∈ c := by
  exact ⟨{a, b}, ZFSet.mem_pair.mpr (Or.inl rfl), ZFSet.mem_pair.mpr (Or.inr rfl)⟩

/-- Axiom 5 (Union): The union of a set of sets exists. -/
theorem zfc_union (a : ZFSet) :
    ∃ u : ZFSet, ∀ x, x ∈ u ↔ ∃ y ∈ a, x ∈ y := by
  exact ⟨⋃₀ a, fun x => ZFSet.mem_sUnion⟩

/-- Axiom 6 (Power Set): The power set exists. -/
theorem zfc_powerset (a : ZFSet) :
    ∃ p : ZFSet, ∀ x, x ∈ p ↔ x ⊆ a := by
  exact ⟨ZFSet.powerset a, fun x => ZFSet.mem_powerset⟩

/-- Axiom 9 (Foundation/Regularity): Every nonempty set has an
    ∈-minimal element (no infinite descending ∈-chains). -/
theorem zfc_foundation (a : ZFSet) (h : a ≠ ∅) :
    ∃ x ∈ a, ∀ y ∈ x, y ∉ a := by
  obtain ⟨x, hx, hinter⟩ := ZFSet.regularity a h
  exact ⟨x, hx, fun y hy hya => ZFSet.notMem_empty y
    (hinter ▸ ZFSet.mem_inter.mpr ⟨hya, hy⟩)⟩

/-! ## Russell's Paradox

Schuller motivates ZFC by showing naive comprehension is contradictory.
In ZFC, separation avoids this by requiring a pre-existing set.
We show that no set contains all sets (there is no universal set). -/

/-- There is no universal set in ZFC: no set contains all sets.
    This is a consequence of Russell's paradox. -/
theorem no_universal_set : ¬∃ (U : ZFSet), ∀ x, x ∈ U := by
  intro ⟨U, hU⟩
  -- Russell set: R = {x ∈ U | x ∉ x}
  let R := U.sep (fun x => x ∉ x)
  have hR : ∀ x, x ∈ R ↔ x ∈ U ∧ x ∉ x := fun x => ZFSet.mem_sep
  -- Does R ∈ R?
  have := hR R
  tauto

/-! ## Number Constructions

Schuller traces the chain ℕ → ℤ → ℚ → ℝ.
In Lean/Mathlib these are all defined types with the expected
algebraic structures. We demonstrate the coercion chain. -/

/-- ℕ embeds into ℤ. -/
theorem nat_embeds_in_int : ∀ n : ℕ, ∃ z : ℤ, z = ↑n := by
  intro n; exact ⟨↑n, rfl⟩

/-- ℤ embeds into ℚ. -/
theorem int_embeds_in_rat : ∀ z : ℤ, ∃ q : ℚ, q = ↑z := by
  intro z; exact ⟨↑z, rfl⟩

/-- ℚ embeds into ℝ. -/
theorem rat_embeds_in_real : ∀ q : ℚ, ∃ r : ℝ, r = ↑q := by
  intro q; exact ⟨↑q, rfl⟩

/-- The coercion chain preserves addition: (a + b : ℕ) maps to
    the same value in ℤ. -/
theorem nat_add_cast_int (a b : ℕ) : (↑(a + b) : ℤ) = ↑a + ↑b := by
  push_cast; ring

/-- ℝ is a complete ordered field (Archimedean property as witness). -/
theorem real_archimedean : ∀ (x : ℝ), ∃ n : ℕ, x < ↑n := by
  intro x
  obtain ⟨n, hn⟩ := exists_nat_gt x
  exact ⟨n, hn⟩
