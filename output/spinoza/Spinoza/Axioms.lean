import Spinoza.Definitions
/-!
# Axioms A1–A7 and the Symmetric PSR (MSC 03A05, 03B45)

Spinoza's seven axioms from Part I of the *Ethics*, plus the Principle of
Sufficient Reason (PSR) in its symmetric form (used in 1P7d2 and 1P11d2).
-/
namespace Spinoza

variable {Entity : Type*} [SpinozaFramework Entity]

open SpinozaFramework

/-! ## A1 — Exhaustion of Being (1a1) -/

/-- A1: Everything that exists is either in itself or in another. -/
axiom A1 : ∀ x : Entity,
  InheresIn x x ∨ ∃ y : Entity, y ≠ x ∧ InheresIn x y

/-! ## A2 — Conceivability Completeness (1a2) -/

/-- A2: What cannot be conceived through another must be conceived through itself. -/
axiom A2 : ∀ x : Entity,
  (¬∃ y : Entity, y ≠ x ∧ ConceivedThrough x y) → ConceivedThrough x x

/-! ## A3 — Causal Determination (1a3) -/

/-- A3a: From a determinate cause an effect necessarily follows. -/
axiom A3 : ∀ x y : Entity, Causes x y → Necessarily (∃ z : Entity, z = y)

/-- A3b: Uncaused substance/mode cannot exist (ex nihilo nihil). -/
axiom A3b : ∀ y : Entity,
  (¬∃ c : Entity, Causes c y) → ¬(IsSubstance y ∨ IsMode y)

/-! ## A4 — Knowledge Requires Cause (1a4) -/

/-- A4: The concept of an effect involves the concept of its cause.
    Epistemic bridge: causation → conceptual dependence. -/
axiom A4 : ∀ x y : Entity, Causes x y → ConceivedThrough y x

/-! ## A5 — No Common Causation Without Common Nature (1a5) -/

/-- A5: Things sharing no attribute cannot cause each other. -/
axiom A5 : ∀ x y : Entity,
  (¬∃ a : Entity, HasAttribute x a ∧ HasAttribute y a) →
  ¬Causes x y ∧ ¬Causes y x

/-! ## A7 — Conceivable Non-Existence Implies Not Causa Sui (1a7) -/

/-- A7: If a thing can be conceived as not existing, it is not causa sui. -/
axiom A7 : ∀ x : Entity,
  Possibly (¬∃ y : Entity, y = x) → ¬IsCausaSui x

/-! ## Symmetric PSR (for 1P7d2, 1P11d2) -/

/-- Symmetric PSR: For any entity, there must be a reason either
    for its existence or for its non-existence. -/
axiom PSR_symmetric : ∀ x : Entity,
  (∃ c : Entity, Causes c x) ∨ (∃ c : Entity, Prevents c x)

/-- For substances, nothing internal prevents existence. -/
axiom no_internal_prevention : ∀ s : Entity,
  IsSubstance s → ¬∃ c : Entity, c = s ∧ Prevents c s

/-! ## God-Specific Axioms (needed for 1P11) -/

/-- God's possibility: there exists an entity satisfying IsGod. -/
axiom God_is_possible : ∃ g : Entity, IsGod g

/-- The God constant of SpinozaFramework satisfies IsGod. -/
axiom isGod_axiom : IsGod (God : Entity)

/-- Every attribute conceived-through-itself is had by God (D6 consequence). -/
theorem god_has_attribute (a : Entity) (ha : ConceivedThrough a a) :
    HasAttribute (God : Entity) a := by
  sorry -- from isGod_axiom + D6 infinity interpretation

end Spinoza
