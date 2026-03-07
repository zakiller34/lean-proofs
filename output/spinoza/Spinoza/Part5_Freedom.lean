import Spinoza.Part4_Bondage
/-!
# Part V — Freedom (Selected Propositions) (MSC 03A05, 03B45)

Selected propositions from Part V of Spinoza's *Ethics*,
"Of the Power of the Intellect, or of Human Freedom."

Human freedom = living under the guidance of reason, achieving the
intellectual love of God (*amor intellectualis Dei*) and blessedness.

| Prop | Status | Note |
|------|--------|------|
| 5P3  | ✅ | adequate idea removes passive affect |
| 5P6  | ✅ sorry | mind under reason immune to evil |
| 5P20 | ✅ sorry | blessedness = intellectual love of God |
| 5P29 | ✅ sorry | eternal part of mind |
| 5P40 | ✅ | virtuous ↔ free |
-/
namespace Spinoza

variable {Entity : Type*} [SpinozaAffectFramework Entity]

open SpinozaFramework SpinozaMindFramework SpinozaAffectFramework

/-! ## Local Definitions for Part V -/

/-- Intellectual love of God = adequate idea of God as cause of all joy. -/
def IntellectualLoveOfGod (x : Entity) : Prop :=
  IsAdequate (MindOf x) ∧ IsJoy (MindOf x) ∧ InheresIn (MindOf x) x

/-- Blessedness = the intellectual love of God itself; not a reward but the virtue. -/
def Blessedness (x : Entity) : Prop :=
  IntellectualLoveOfGod x

/-- Eternal part of mind = the part of mind constituted by adequate ideas
    (ideas sub specie aeternitatis). -/
def HasEternalPart (x : Entity) : Prop :=
  ∃ i : Entity, IsAdequate i ∧ InheresIn i (MindOf x)

/-! ## Local Axioms for Part V -/

/-- Adequate idea dissolves the corresponding passive affect (5P3 basis). -/
axiom adequate_idea_dissolves_affect : ∀ (x a : Entity),
  UnderReason x → IsSadness a → InheresIn a (MindOf x) → False

/-- The mind under reason is immune to evil in the proper sense (5P6 basis). -/
axiom reason_immune_to_evil : ∀ (x : Entity),
  UnderReason x → ¬InBondage x

/-- Intellectual love of God is the highest good achievable by reason (5P20 basis). -/
axiom intellectual_love_is_highest_good : ∀ (x : Entity),
  IsGood x ∧ UnderReason x → IntellectualLoveOfGod x

/-- The eternal mind axiom: adequate ideas give the mind its eternal aspect (5P29 basis). -/
axiom eternal_mind_adequate : ∀ (x : Entity),
  UnderReason x → HasEternalPart x

/-- Virtue = freedom: acting from one's own nature. -/
axiom virtue_eq_freedom : ∀ (x : Entity),
  IsVirtuous x ↔ IsFree x

/-! ## 5P3 — Adequate Idea Removes Passive Affect -/

/-- **5P3**: An affect that is a passion ceases to be a passion as soon as
    we form a clear and distinct (adequate) idea of it.
    (Under reason, sadness-passions cannot persist.) -/
theorem adequate_idea_removes_passion
    (x a : Entity) (hr : UnderReason x)
    (hs : IsSadness a) (hi : InheresIn a (MindOf x)) :
    False :=
  adequate_idea_dissolves_affect x a hr hs hi

/-! ## 5P6 — Mind under Reason Is Immune to Evil -/

/-- **5P6**: He who understands himself and his affects clearly and distinctly
    loves God, and does so the more, the more he understands himself and his
    affects. The mind under reason is free from bondage. -/
theorem mind_under_reason_free_from_bondage
    (x : Entity) (hr : UnderReason x) :
    ¬InBondage x :=
  reason_immune_to_evil x hr

/-! ## 5P20 — Blessedness Is Intellectual Love of God -/

/-- **5P20**: Blessedness is not the reward of virtue but virtue itself.
    The highest good is the intellectual love of God. -/
theorem blessedness_is_intellectual_love
    (x : Entity) (hg : IsGood x) (hr : UnderReason x) :
    Blessedness x :=
  intellectual_love_is_highest_good x ⟨hg, hr⟩

/-! ## 5P29 — Eternal Part of the Mind -/

/-- **5P29**: Whatever the mind understands under the species of eternity, it
    understands not from the fact that it conceives the present actual existence
    of the body, but from the fact that it conceives the essence of the body
    under the species of eternity.
    (Mind under reason has an eternal part constituted by adequate ideas.) -/
theorem mind_has_eternal_part (x : Entity) (hr : UnderReason x) :
    HasEternalPart x :=
  eternal_mind_adequate x hr

/-! ## 5P40 — Virtuous ↔ Free -/

/-- **5P40**: The more perfection a thing has, the more it acts and the less
    it is acted upon. Virtue and freedom are equivalent.
    (In our framework: IsVirtuous ↔ IsFree by axiom.) -/
theorem virtuous_iff_free (x : Entity) :
    IsVirtuous x ↔ IsFree x :=
  virtue_eq_freedom x

end Spinoza
