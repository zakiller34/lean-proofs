import Spinoza.Part1_Core
/-!
# Part I — God Propositions 1P11–1P17 (MSC 03A05, 03B45)

Propositions 11–17 of Part I of Spinoza's *Ethics*.
Core: 1P11 (God necessarily exists), 1P14 (monism), 1P15–1P17.
-/
namespace Spinoza

variable {Entity : Type*} [SpinozaFramework Entity]

open SpinozaFramework

/-! ## 1P11 — God Necessarily Exists -/

/-- **1P11** (PSR demonstration): God necessarily exists. -/
theorem God_necessarily_exists :
    Necessarily (∃ g : Entity, IsGod g) :=
  God_is_possible

/-- 1P11 (reductio): God's non-existence is not possible. -/
theorem God_necessarily_exists_reductio :
    ¬Possibly (¬∃ g : Entity, IsGod g) :=
  fun h => h God_is_possible

/-! ## 1P14 — Substance Monism (proved first; used in 1P12) -/

/-- **1P14**: Besides God, no substance can exist or be conceived. -/
theorem substance_monism
    (s : Entity) (hs : IsSubstance s) : s = God := by
  have hGod_sub := (@isGod_axiom Entity _).1
  by_contra hne
  obtain ⟨a, ha⟩ := substance_has_attribute s hs
  have hca : ConceivedThrough a a := hasAttribute_implies_conceived_through_self s a ha
  have hGa : HasAttribute (God : Entity) a := god_has_attribute a hca
  exact hne (no_shared_attribute s God hs hGod_sub ⟨a, ha, hGa⟩)

/-! ## 1P12 — Substance Cannot Be Divided -/

/-- 1P12: No substance can be truly divided. -/
theorem substance_indivisible
    (s : Entity) (_hs : IsSubstance s) :
    ¬∃ s₁ s₂ : Entity,
      s₁ ≠ s₂ ∧ IsSubstance s₁ ∧ IsSubstance s₂ ∧
      ∀ a, HasAttribute s a ↔ (HasAttribute s₁ a ∨ HasAttribute s₂ a) := by
  intro ⟨s₁, s₂, hne, hs₁, hs₂, _hunion⟩
  exact hne ((substance_monism s₁ hs₁).trans (substance_monism s₂ hs₂).symm)

/-! ## 1P14 Corollaries -/

/-- **1P14C1**: God is unique. -/
theorem God_unique
    (g₁ g₂ : Entity) (hg₁ : IsGod g₁) (hg₂ : IsGod g₂) : g₁ = g₂ :=
  (substance_monism g₁ hg₁.1).trans (substance_monism g₂ hg₂.1).symm

/-- **1P14C2**: Everything inheres in God. -/
theorem all_things_in_God (x : Entity) : InheresIn x God := by
  rcases A1 x with hself | ⟨y, hyne, hy⟩
  · -- x in itself → x is substance (D3 + A2) → x = God
    have hnotconc : ¬∃ z : Entity, z ≠ x ∧ ConceivedThrough x z := by
      intro ⟨z, hzx, hcz⟩
      have hcx := inherence_implies_conceived_through x x hself
      exact hzx (conceivability_unique x x z hcx hcz).symm
    have hx_sub : IsSubstance x := ⟨hself, A2 x hnotconc⟩
    rw [substance_monism x hx_sub]
    exact (@isGod_axiom Entity _).1.1
  · -- x in y (y ≠ x) → y is substance → y = God → x in God
    have hy_sub : IsSubstance y := mode_inheres_in_substance x y hy hyne.symm
    rw [substance_monism y hy_sub] at hy
    exact hy

/-! ## 1P15 — Whatever Is, Is in God -/

/-- 1P15: Whatever is, is in God. -/
theorem everything_in_God (x : Entity) :
    InheresIn x God ∧ ConceivedThrough x God :=
  let h := all_things_in_God x
  ⟨h, inherence_implies_conceived_through x God h⟩

/-! ## 1P16 — All Things Follow from God's Nature -/

/-- 1P16: All modes are caused by God. -/
theorem all_things_follow_from_God (m : Entity) (_hm : IsMode m) : Causes God m := by
  obtain ⟨s, hs, hinh, _, hns⟩ := _hm
  have hs_god := substance_monism s hs
  rw [hs_god] at hinh
  have hne : m ≠ God := fun h => hns (h ▸ (@isGod_axiom Entity _).1)
  exact inherence_implies_causation m God hinh hne

/-! ## 1P17 — God Acts from His Own Nature Alone -/

/-- 1P17: God is free — acts solely from the laws of His own nature. -/
theorem God_free : IsFree (God : Entity) := by
  constructor
  · exact substance_is_causa_sui God (@isGod_axiom Entity _).1
  · intro y hy
    by_contra hne
    have hy_sub : IsSubstance y := substance_cause_is_substance God y (@isGod_axiom Entity _).1 hy
    exact substance_not_produced_by_substance y God hy_sub (@isGod_axiom Entity _).1 hne hy

end Spinoza
