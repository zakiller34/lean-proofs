import Spinoza.Part1_God
/-!
# Part I — Necessity Propositions 1P29, 1P33 (MSC 03B45)

The necessitarian conclusions of Part I:
- 1P29: Nothing in nature is contingent.
- 1P33: Things could not have been produced otherwise.

Under S5-collapse (□p = p), these reduce to showing things exist,
but the logical structure of the argument is preserved as a skeleton.
-/
namespace Spinoza

variable {Entity : Type*} [SpinozaFramework Entity]

open SpinozaFramework

/-! ## 1P29 — Nothing Is Contingent -/

/-- **1P29**: Nothing in nature is contingent; everything is determined. -/
theorem no_contingency (x : Entity) : ∃ c : Entity, Causes c x := by
  rcases A1 x with hself | ⟨_y, _hyne, _hy⟩
  · have hx_sub : IsSubstance x := by
      refine ⟨hself, ?_⟩
      apply A2; sorry
    have hcs := (substance_is_causa_sui x hx_sub).1
    exact ⟨x, hcs⟩
  · have hx_mode : IsMode x := by sorry
    exact ⟨God, all_things_follow_from_God x hx_mode⟩

/-- Corollary: Nothing is possible except what actually exists (S5-collapse). -/
theorem no_mere_possibility (x : Entity) : Possibly (∃ y : Entity, y = x) :=
  ⟨x, rfl⟩

/-! ## 1P33 — Things Could Not Have Been Otherwise -/

/-- **1P33**: Things could not have been produced in any other way.
    Under S5-collapse: □p = p, so □(∃ x, x = m) = (∃ x, x = m). -/
theorem strict_necessitarianism
    (m : Entity) (_hm : IsMode m) :
    Necessarily (∃ x : Entity, x = m) ∧ ¬Possibly (¬∃ x : Entity, x = m) :=
  -- Under S5-collapse: Necessarily p = p, Possibly p = p.
  ⟨⟨m, rfl⟩, fun h => h ⟨m, rfl⟩⟩

/-- God's productive will is itself necessary. -/
theorem God_will_is_necessary (m : Entity) (hm : IsMode m) :
    Necessarily (Causes God m) :=
  all_things_follow_from_God m hm

/-! ## Conceptual Barrier (Della Rocca / Viljanen) -/

/-- Conceptual Barrier: No attribute can be conceived through another attribute. -/
lemma conceptual_barrier
    (s a b : Entity)
    (_hs : IsSubstance s)
    (ha : HasAttribute s a) (hb : HasAttribute s b) (_hab : a ≠ b) :
    ¬ConceivedThrough a b ∧ ¬ConceivedThrough b a := by
  constructor <;> intro _hcontra <;> {
    -- Each attribute is conceived through itself (1P10).
    -- Being conceived through another would violate D4 / A2.
    sorry
  }

/-- Each attribute is sufficient to conceive its substance. -/
lemma attribute_sufficient_for_substance
    (s a : Entity) (hs : IsSubstance s) (ha : HasAttribute s a) :
    ConceivedThrough s a := by
  sorry
  -- Bridge axiom needed: D3 (ConceivedThrough s s) + D4 (a constitutes essence of s)
  -- → ConceivedThrough s a.

end Spinoza
