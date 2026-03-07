import Spinoza.Axioms
/-!
# Part I — Core Propositions 1P1–1P10 (MSC 03A05, 03B45)

Propositions 1–10 of Part I of Spinoza's *Ethics*.
These establish the basic properties of substance, mode, and attribute.
-/
namespace Spinoza

variable {Entity : Type*} [SpinozaFramework Entity]

open SpinozaFramework

/-! ## 1P1 — Substance Prior to Its Modes -/

/-- 1P1: A substance is prior in nature to its affections.
    Substance is conceived through itself; modes are not. -/
lemma substance_prior_to_modes
    (s m : Entity)
    (hs : IsSubstance s) (hm : IsMode m) (_hinh : InheresIn m s) :
    ConceivedThrough s s ∧ ¬ConceivedThrough m m := by
  constructor
  · exact hs.2
  · intro hcontra
    obtain ⟨s', hs', _, hct', hns'⟩ := hm
    -- m conceived through itself AND through s' → s' = m (conceivability_unique)
    -- but s' is substance and ¬IsSubstance m: contradiction
    exact hns' ((conceivability_unique m m s' hcontra hct') ▸ hs')

/-! ## 1P2 — Distinct Attributes → Nothing in Common -/

/-- 1P2: Two substances having different attributes have nothing in common. -/
lemma distinct_attributes_no_common
    (s₁ s₂ : Entity)
    (_hs₁ : IsSubstance s₁) (_hs₂ : IsSubstance s₂)
    (hdisjoint : ∀ a : Entity, HasAttribute s₁ a → ¬HasAttribute s₂ a) :
    ¬∃ a : Entity, HasAttribute s₁ a ∧ HasAttribute s₂ a := by
  intro ⟨a, ha₁, ha₂⟩
  exact absurd ha₂ (hdisjoint a ha₁)

/-! ## 1P3 — No Causation Without Common Nature -/

/-- 1P3: Things that have nothing in common cannot be cause of one another. -/
lemma no_common_no_causation
    (s₁ s₂ : Entity)
    (hnocommon : ¬∃ a : Entity, HasAttribute s₁ a ∧ HasAttribute s₂ a) :
    ¬Causes s₁ s₂ ∧ ¬Causes s₂ s₁ :=
  A5 s₁ s₂ hnocommon

/-! ## 1P4 — Only Attributes and Modes Distinguish Things -/

/-- 1P4: Two distinct things differ by attributes or modes. -/
theorem distinguishability
    (x y : Entity) (hne : x ≠ y) :
    (∃ a : Entity, (HasAttribute x a ∧ ¬HasAttribute y a) ∨
                   (¬HasAttribute x a ∧ HasAttribute y a)) ∨
    (∃ m : Entity, IsMode m ∧
                   ((InheresIn m x ∧ ¬InheresIn m y) ∨
                    (¬InheresIn m x ∧ InheresIn m y))) := by
  by_contra h
  apply hne
  apply entity_extensionality_by_attr_mode
  · intro a
    constructor
    · intro ha; by_contra hna; exact h (Or.inl ⟨a, Or.inl ⟨ha, hna⟩⟩)
    · intro ha; by_contra hna; exact h (Or.inl ⟨a, Or.inr ⟨hna, ha⟩⟩)
  · intro m hm
    constructor
    · intro hx; by_contra hy; exact h (Or.inr ⟨m, hm, Or.inl ⟨hx, hy⟩⟩)
    · intro hy; by_contra hx; exact h (Or.inr ⟨m, hm, Or.inr ⟨hx, hy⟩⟩)

/-! ## 1P5 — No Two Substances Share an Attribute -/

/-- **1P5**: No two distinct substances can share an attribute. -/
theorem no_shared_attribute
    (s₁ s₂ : Entity)
    (hs₁ : IsSubstance s₁) (hs₂ : IsSubstance s₂)
    (hshared : ∃ a : Entity, HasAttribute s₁ a ∧ HasAttribute s₂ a) :
    s₁ = s₂ := by
  obtain ⟨a, ha₁, ha₂⟩ := hshared
  exact attribute_individuates s₁ s₂ a hs₁ hs₂ ha₁ ha₂

/-! ## 1P6 — Substances Cannot Produce One Another -/

/-- **1P6**: One substance cannot be produced by another substance. -/
theorem substance_not_produced_by_substance
    (s₁ s₂ : Entity)
    (hs₁ : IsSubstance s₁) (hs₂ : IsSubstance s₂) (hne : s₁ ≠ s₂) :
    ¬Causes s₁ s₂ := by
  intro hcause
  have hnocommon : ¬∃ a : Entity, HasAttribute s₁ a ∧ HasAttribute s₂ a := by
    intro ⟨a, ha₁, ha₂⟩
    exact hne (no_shared_attribute s₁ s₂ hs₁ hs₂ ⟨a, ha₁, ha₂⟩)
  exact (A5 s₁ s₂ hnocommon).1 hcause

/-- **1P6C**: A substance can have no external cause; hence it is causa sui. -/
theorem substance_is_causa_sui
    (s : Entity) (hs : IsSubstance s) : IsCausaSui s := by
  constructor
  · rcases PSR_symmetric s with ⟨c, hc⟩ | ⟨c, hc⟩
    · -- c causes s → c is substance → by 1P6, c = s
      have hc_sub : IsSubstance c := substance_cause_is_substance s c hs hc
      by_cases heq : c = s
      · exact heq ▸ hc
      · exact absurd hc (substance_not_produced_by_substance c s hc_sub hs heq)
    · -- c prevents s → contradiction (no internal or external prevention)
      by_cases heq : c = s
      · exact absurd ⟨c, heq, hc⟩ (no_internal_prevention s hs)
      · exact absurd hc (substance_external_prevention_impossible s c hs heq)
  · exact ⟨s, rfl⟩

/-! ## 1P7 — Existence Belongs to the Nature of Substance -/

/-- **1P7**: Every substance necessarily exists. -/
theorem substance_necessarily_exists
    (s : Entity) (hs : IsSubstance s) : Necessarily (∃ x : Entity, x = s) :=
  (substance_is_causa_sui s hs).2

/-! ## 1P8 — Substance Is Infinite in Its Kind -/

/-- 1P8: Every substance is infinite in its own kind. -/
lemma substance_infinite_in_kind
    (s : Entity) (hs : IsSubstance s)
    (a : Entity) (ha : HasAttribute s a) :
    InfiniteInKind s (fun x y => HasAttribute x a ∧ HasAttribute y a) := by
  intro ⟨t, ⟨_, hat⟩, hne⟩
  -- t has attribute a → t is a substance → shared attr with s → s = t (1P5). Contradiction.
  have ht_sub : IsSubstance t := attribute_bearer_is_substance t a hat
  exact hne (no_shared_attribute s t hs ht_sub ⟨a, ha, hat⟩).symm

/-! ## 1P9 — Reality Proportional to Attributes (stub) -/

/-- 1P9: The more attributes a thing has, the more reality it has.
    (Stub: encoding "reality" requires a scalar type.) -/
lemma reality_proportional_to_attributes
    (_s₁ _s₂ : Entity)
    (_hs₁ : IsSubstance _s₁) (_hs₂ : IsSubstance _s₂)
    (_more : ∀ a, HasAttribute _s₁ a → HasAttribute _s₂ a) :
    True :=
  trivial
-- Full encoding: variable (Reality : Entity → ℝ) with monotonicity axiom.

/-! ## 1P10 — Each Attribute Conceived Through Itself -/

/-- 1P10: Each attribute of a substance is conceived through itself. -/
lemma attribute_conceived_through_itself
    (_s a : Entity) (_hs : IsSubstance _s) (ha : HasAttribute _s a) :
    ConceivedThrough a a :=
  hasAttribute_implies_conceived_through_self _s a ha

end Spinoza
