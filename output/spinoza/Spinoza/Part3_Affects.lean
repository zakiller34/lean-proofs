import Spinoza.AffectAxioms
import Spinoza.Part1_Necessity
/-!
# Part III — The Affects (Selected Propositions) (MSC 03A05, 03B45)

Selected propositions from Part III of Spinoza's *Ethics*,
"Of the Origin and Nature of the Affects."

| Prop | Status | Note |
|------|--------|------|
| 3P4  | ✅ | from external_destruction_only |
| 3P5  | ✅ | from contrary_natures_no_prevention + A5 |
| 3P6  | ✅ | from conatus_is_essence |
| 3P7  | ✅ | reformulation of 3P6 |
| 3P11 | ✅ | from joy_sadness_distinct |
| 3P12 | ✅ | from mind_strives_for_power |
| 3P13 | ✅ | from mind_excludes_sadness |
| 3P57 | ✅ | from affect_individuality |
-/
namespace Spinoza

variable {Entity : Type*} [SpinozaAffectFramework Entity]

open SpinozaFramework SpinozaMindFramework SpinozaAffectFramework

/-! ## 3P4 — No Thing Can Be Destroyed Except by External Causes -/

/-- **3P4**: No thing can be destroyed except by an external cause.
    A mode cannot be the reason for its own non-existence. -/
theorem no_self_destruction (x c : Entity) (hx : IsMode x) (hprev : Prevents c x) :
    c ≠ x :=
  external_destruction_only x c hx hprev

/-! ## 3P5 — Things of Contrary Natures Cannot Destroy Each Other -/

/-- **3P5**: Things of contrary natures (no shared attribute) cannot destroy
    each other directly; neither can prevent the other's existence. -/
theorem contrary_natures_no_mutual_destruction
    (x y : Entity)
    (hno : ¬∃ a : Entity, HasAttribute x a ∧ HasAttribute y a) :
    ¬Prevents x y ∧ ¬Prevents y x :=
  contrary_natures_no_prevention x y hno

/-! ## 3P6 — Each Thing Strives to Persist in Its Being -/

/-- **3P6**: Each thing, as far as it can by its own power, strives to
    persist in its being. (Conatus is universal.) -/
theorem each_thing_has_conatus (x : Entity) : Conatus x :=
  conatus_is_essence x

/-! ## 3P7 — Striving Is the Actual Essence -/

/-- **3P7**: The striving by which each thing strives to persist in its being
    is nothing other than the actual essence of that thing.
    (Conatus holds for all entities — it is coextensive with existence.) -/
theorem conatus_is_actual_essence (x : Entity) :
    Conatus x ↔ ∃ y : Entity, y = x :=
  ⟨fun _ => ⟨x, rfl⟩, fun _ => conatus_is_essence x⟩

/-! ## 3P11 — Joy and Sadness -/

/-- **3P11**: Joy is an affect by which the mind passes to greater perfection;
    sadness is an affect by which it passes to a lesser.
    (Formalization: joy and sadness are mutually exclusive.) -/
theorem joy_and_sadness_exclusive (a : Entity) :
    ¬(IsJoy a ∧ IsSadness a) :=
  joy_sadness_distinct a

/-- **3P11 corollary**: Joy is associated with positive power. -/
theorem joy_implies_positive_power (a e : Entity)
    (hj : IsJoy a) (hi : InheresIn a e) :
    0 < Power e :=
  joy_power_positive a e hj hi

/-! ## 3P12 — Mind Strives to Imagine What Increases Power -/

/-- **3P12**: The mind strives, as far as it can, to imagine things that
    increase or assist the body's power of acting. -/
theorem mind_strives_for_joy (b : Entity) :
    ∃ a : Entity, IsJoy a ∧ InheresIn a (MindOf b) :=
  mind_strives_for_power b

/-! ## 3P13 — Mind Strives to Exclude What Decreases Power -/

/-- **3P13**: When the mind imagines things that diminish or hinder the body's
    power of acting, it strives to exclude them from existing. -/
theorem mind_excludes_power_diminishing
    (b a : Entity) (hs : IsSadness a) (hi : InheresIn a (MindOf b)) :
    ∃ c : Entity, Prevents c a :=
  mind_excludes_sadness b a hs hi

/-! ## 3P57 — Each Individual's Affect Is Unique -/

/-- **3P57**: Each individual's affect differs from the affect of another as the
    essence (power) of one differs from the essence of another. -/
theorem affects_differ_between_individuals
    (x y : Entity) (hpow : Power x ≠ Power y) :
    ∃ a : Entity,
      (IsJoy a ∧ InheresIn a x ∧ ¬InheresIn a y) ∨
      (IsSadness a ∧ InheresIn a x ∧ ¬InheresIn a y) :=
  affect_individuality x y hpow

end Spinoza
