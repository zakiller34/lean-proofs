import Mathlib.Data.Real.Basic
import Spinoza.MindAxioms
/-!
# Affect Axioms — Part III Framework (MSC 03A05, 03B45)

`SpinozaAffectFramework` extends `SpinozaMindFramework` with the conatus,
power, and affect structure needed for Part III
("Of the Origin and Nature of the Affects").
-/
namespace Spinoza

/-- Extended framework for Part III: adds power, conatus, and affects. -/
class SpinozaAffectFramework (Entity : Type*) extends SpinozaMindFramework Entity where
  /-- `Power x` : the power (conatus) of x to persist in being (ℝ-valued). -/
  Power : Entity → ℝ
  /-- `Conatus x` : x strives to persist in its being. -/
  Conatus : Entity → Prop
  /-- `IsJoy x` : x is an affect of Joy (transition to greater power). -/
  IsJoy : Entity → Prop
  /-- `IsSadness x` : x is an affect of Sadness (transition to lesser power). -/
  IsSadness : Entity → Prop
  /-- `IsDesire x` : x is an affect of Desire (conscious conatus). -/
  IsDesire : Entity → Prop

variable {Entity : Type*} [SpinozaAffectFramework Entity]

open SpinozaFramework SpinozaMindFramework SpinozaAffectFramework

/-! ## Axioms for Part III -/

/-- Power is non-negative. -/
axiom power_nonneg : ∀ (x : Entity), 0 ≤ Power x

/-- Conatus axiom (3P6 basis): every thing has positive striving to persist. -/
axiom conatus_is_essence : ∀ (x : Entity), Conatus x

/-- External destruction only (3P4 basis): a mode cannot prevent its own existence. -/
axiom external_destruction_only : ∀ (x c : Entity),
  IsMode x → Prevents c x → c ≠ x

/-- Joy and Sadness are mutually exclusive affects. -/
axiom joy_sadness_distinct : ∀ (x : Entity), ¬(IsJoy x ∧ IsSadness x)

/-- Joy increases power: joy affects inhere in entities with positive power. -/
axiom joy_power_positive : ∀ (a e : Entity),
  IsJoy a → InheresIn a e → 0 < Power e

/-- Sadness decreases power: sadness affects inhere in entities with bounded power. -/
axiom sadness_power_bounded : ∀ (a e₁ e₂ : Entity),
  IsSadness a → InheresIn a e₁ → IsJoy a → InheresIn a e₂ → Power e₁ < Power e₂

/-- Desire is conscious conatus (3P9 basis): desire ↔ conatus. -/
axiom desire_is_conatus : ∀ (x : Entity), IsDesire x ↔ Conatus x

/-- Things of contrary natures (no shared attribute) cannot prevent each other (3P5 basis). -/
axiom contrary_natures_no_prevention : ∀ (x y : Entity),
  (¬∃ a : Entity, HasAttribute x a ∧ HasAttribute y a) →
  ¬Prevents x y ∧ ¬Prevents y x

/-- Mind strives to imagine what increases power (3P12 basis). -/
axiom mind_strives_for_power : ∀ (b : Entity),
  ∃ a : Entity, IsJoy a ∧ InheresIn a (MindOf b)

/-- Mind strives to exclude what decreases power (3P13 basis). -/
axiom mind_excludes_sadness : ∀ (b : Entity),
  ∀ a : Entity, IsSadness a → InheresIn a (MindOf b) →
    ∃ c : Entity, Prevents c a

/-- Affects differ between individuals: equal power implies equal affect type (3P57 basis). -/
axiom affect_individuality : ∀ (x y : Entity),
  Power x ≠ Power y →
  ∃ a : Entity, (IsJoy a ∧ InheresIn a x ∧ ¬InheresIn a y) ∨
               (IsSadness a ∧ InheresIn a x ∧ ¬InheresIn a y)

end Spinoza
