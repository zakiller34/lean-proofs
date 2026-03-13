/-!
# Chapter 1: Propositional and Predicate Logic

Schuller's presentation of logic as the foundation of mathematics.
In Lean 4, the type theory IS the logic, so we demonstrate the key
results from Schuller's lecture as formal theorems.
-/

import Mathlib.Logic.Basic
import Mathlib.Tactic

/-! ## Propositional Logic -/

/-- Ex falso quodlibet: from False, anything follows.
    Schuller emphasizes this as a key property of implication. -/
theorem ex_falso_quodlibet : ∀ (p : Prop), False → p := by
  intro p h; exact h.elim

/-- Modus ponens: the fundamental rule of inference. -/
theorem modus_ponens (p q : Prop) : p → (p → q) → q := by
  intro hp hpq; exact hpq hp

/-- Contrapositive equivalence: (p → q) ↔ (¬q → ¬p).
    Schuller presents this as a key logical equivalence. -/
theorem contrapositive (p q : Prop) : (p → q) ↔ (¬q → ¬p) := by
  exact ⟨fun hpq hnq hp => hnq (hpq hp), fun h => by tauto⟩

/-- Double negation elimination (classical logic).
    Requires the law of excluded middle. -/
theorem double_negation_elim (p : Prop) : ¬¬p → p := by
  intro h; by_contra hn; exact h hn

/-- Law of excluded middle: every proposition is true or false. -/
theorem excluded_middle (p : Prop) : p ∨ ¬p := by
  exact Classical.em p

/-- De Morgan's law for conjunction. -/
theorem de_morgan_and (p q : Prop) : ¬(p ∧ q) ↔ ¬p ∨ ¬q := by
  tauto

/-- De Morgan's law for disjunction. -/
theorem de_morgan_or (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  tauto

/-- Implication truth table: p → q is equivalent to ¬p ∨ q (classically). -/
theorem imp_iff_not_or (p q : Prop) : (p → q) ↔ (¬p ∨ q) := by
  tauto

/-! ## Consistency

Schuller states that propositional logic is consistent: there exists
a proposition that cannot be proven. We formalize this by exhibiting
`False` as an unprovable proposition. -/

/-- Propositional logic is consistent: False is not provable. -/
theorem logic_consistent : ¬False := by
  intro h; exact h

/-! ## Predicate Logic

Schuller introduces universal, existential, and unique existential quantifiers. -/

/-- Universal instantiation: if P holds for all x, it holds for any specific a. -/
theorem universal_instantiation {α : Type*} (P : α → Prop) (a : α)
    (h : ∀ x, P x) : P a := by
  exact h a

/-- Existential introduction: exhibiting a witness proves ∃. -/
theorem existential_intro {α : Type*} (P : α → Prop) (a : α) (ha : P a) :
    ∃ x, P x := by
  exact ⟨a, ha⟩

/-- Unique existence implies existence. -/
theorem unique_implies_exists {α : Type*} (P : α → Prop)
    (h : ∃! x, P x) : ∃ x, P x := by
  obtain ⟨x, hx, _⟩ := h; exact ⟨x, hx⟩

/-- Unique existence means the witness is unique. -/
theorem unique_existence_unique {α : Type*} (P : α → Prop)
    (h : ∃! x, P x) : ∀ a b, P a → P b → a = b := by
  obtain ⟨x, _, huniq⟩ := h
  intro a b ha hb
  exact (huniq a ha).symm.trans (huniq b hb)

/-! ## Tautologies -/

/-- A tautology is a proposition provable without assumptions.
    Identity is a tautology. -/
theorem tautology_identity (p : Prop) : p → p := by
  exact id

/-- Syllogism (transitivity of implication). -/
theorem syllogism (p q r : Prop) : (p → q) → (q → r) → (p → r) := by
  intro hpq hqr hp; exact hqr (hpq hp)

/-- Proof by contradiction: if assuming ¬p leads to False, then p. -/
theorem proof_by_contradiction (p : Prop) : (¬p → False) → p := by
  intro h; by_contra hn; exact h hn
