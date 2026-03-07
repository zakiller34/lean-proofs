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
  rcases A1 x with hself | ⟨y, hyne, hy⟩
  · -- x in itself → x is substance (A2 + D3) → causa sui → causes itself
    have hnotconc : ¬∃ z : Entity, z ≠ x ∧ ConceivedThrough x z := by
      intro ⟨z, hzx, hcz⟩
      have hcx := inherence_implies_conceived_through x x hself
      exact hzx (conceivability_unique x x z hcx hcz).symm
    have hx_sub : IsSubstance x := ⟨hself, A2 x hnotconc⟩
    exact ⟨x, (substance_is_causa_sui x hx_sub).1⟩
  · -- x in y (y ≠ x) → x is a mode → God causes x (1P16)
    have hy_sub : IsSubstance y := mode_inheres_in_substance x y hy hyne.symm
    have hx_not_sub : ¬IsSubstance x := fun hxs =>
      hyne (conceivability_unique x x y
        (inherence_implies_conceived_through x x hxs.1)
        (inherence_implies_conceived_through x y hy)).symm
    have hx_mode : IsMode x :=
      ⟨y, hy_sub, hy, inherence_implies_conceived_through x y hy, hx_not_sub⟩
    exact ⟨God, all_things_follow_from_God x hx_mode⟩

/-- Corollary: Nothing is possible except what actually exists (S5-collapse). -/
theorem no_mere_possibility (x : Entity) : Possibly (∃ y : Entity, y = x) :=
  ⟨x, rfl⟩

/-! ## 1P33 — Things Could Not Have Been Otherwise -/

/-- **1P33**: Things could not have been produced in any other way. -/
theorem strict_necessitarianism
    (m : Entity) (_hm : IsMode m) :
    Necessarily (∃ x : Entity, x = m) ∧ ¬Possibly (¬∃ x : Entity, x = m) :=
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
  constructor
  · intro hcontra
    -- a conceived through b AND through itself (1P10) → a = b by uniqueness
    have haa := attribute_conceived_through_itself s a _hs ha
    exact _hab (conceivability_unique a b a hcontra haa).symm
  · intro hcontra
    -- b conceived through a AND through itself → b = a by uniqueness
    have hbb := attribute_conceived_through_itself s b _hs hb
    exact _hab (conceivability_unique b a b hcontra hbb)

/-- Each attribute is sufficient to conceive its substance. -/
lemma attribute_sufficient_for_substance
    (s a : Entity) (hs : IsSubstance s) (ha : HasAttribute s a) :
    ConceivedThrough s a :=
  conceived_through_attribute s a hs ha

end Spinoza
