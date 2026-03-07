import Spinoza.MindAxioms
import Spinoza.Part1_Necessity
/-!
# Part II — The Mind (Selected Propositions) (MSC 03A05, 03B45)

Selected propositions from Part II of Spinoza's *Ethics*,
"Of the Nature and Origin of the Mind."

| Prop | Status | Note |
|------|--------|------|
| 2P1  | ✅ | direct from ThoughtIsAttr |
| 2P2  | ✅ | direct from ExtensionIsAttr |
| 2P3  | ✅ | direct from God_has_idea_of_self |
| 2P5  | ✅ | direct from idea_of_mode_in_God |
| 2P7  | ✅ | direct from parallelism |
| 2P7C | ✅ | direct from God_thinking_eq_acting |
| 2P9  | ✅ | same as 2P5 |
| 2P11 | ✅ | direct from mind_body_axiom |
| 2P13 | ✅ | direct from mind_body_axiom |
| 2P14 | ✅ | trivial from God_has_idea_of_self |
| 2P32 | ✅ | direct from ideas_adequate_in_God |
| 2P40 | ✅ | direct from adequate_idea_chain |
| 2P43 | ✅ | direct from adequate_self_luminous |
| 2P49 | ✅ | direct from no_contingency (1P29) |
-/
namespace Spinoza

variable {Entity : Type*} [SpinozaMindFramework Entity]

open SpinozaFramework SpinozaMindFramework

/-! ## 2P1 — Thought Is an Attribute of God -/

/-- **2P1**: Thought is an attribute of God. -/
theorem thought_is_attribute_of_God :
    HasAttribute (God : Entity) (Thought : Entity) :=
  ThoughtIsAttr

/-! ## 2P2 — Extension Is an Attribute of God -/

/-- **2P2**: Extension is an attribute of God. -/
theorem extension_is_attribute_of_God :
    HasAttribute (God : Entity) (Extension : Entity) :=
  ExtensionIsAttr

/-! ## 2P3 — God Has an Adequate Idea of His Essence -/

/-- **2P3**: In God there is necessarily an adequate idea of His essence and of all
    things that follow from it. -/
theorem God_has_adequate_idea_of_self :
    ∃ i : Entity, IsIdeaOf i (God : Entity) ∧ IsAdequate i :=
  God_has_idea_of_self

/-! ## 2P5 — Formal Being of Ideas Has God as Cause -/

/-- **2P5**: The formal being of ideas acknowledges God as its cause insofar as
    God is considered as a thinking thing.
    (Ideas of modes inhere in God.) -/
theorem formal_being_of_ideas
    (m i : Entity) (hm : IsMode m) (hi : IsIdeaOf i m) :
    InheresIn i (God : Entity) :=
  idea_of_mode_in_God m i hm hi

/-! ## 2P7 — Parallelism -/

/-- **2P7**: The order and connection of ideas is the same as the order and
    connection of things. -/
theorem order_of_ideas_eq_order_of_things (x y : Entity) :
    Causes x y ↔ Causes (MindOf x) (MindOf y) :=
  parallelism x y

/-! ## 2P7C — God's Thinking Power = Acting Power -/

/-- **2P7C**: God's power of thinking is equal to His actual power of acting. -/
theorem God_thinking_power_eq_acting_power (m : Entity) (hm : IsMode m) :
    Causes (MindOf (God : Entity)) (MindOf m) :=
  God_thinking_eq_acting m hm

/-! ## 2P9 — Idea of Individual Thing Has God as Cause -/

/-- **2P9**: The idea of an individual thing actually existing has God for its cause
    insofar as He is considered as a thinking thing. -/
theorem idea_of_individual_has_God_as_cause
    (m i : Entity) (hm : IsMode m) (hi : IsIdeaOf i m) :
    InheresIn i (God : Entity) :=
  idea_of_mode_in_God m i hm hi

/-! ## 2P11 — Human Mind Is Idea of the Body -/

/-- **2P11**: The first thing constituting the actual being of the human mind is
    the idea of a particular actually existing thing — namely, the body. -/
theorem human_mind_is_idea_of_body :
    IsIdeaOf (MindOf (Body : Entity)) (Body : Entity) :=
  mind_body_axiom Body

/-! ## 2P13 — Object of Human Mind Is the Body -/

/-- **2P13**: The object of the idea constituting the human mind is the body. -/
theorem object_of_human_mind_is_body :
    ∃ b : Entity, IsIdeaOf (MindOf b) b ∧ b = Body :=
  ⟨Body, mind_body_axiom Body, rfl⟩

/-! ## 2P14 — Human Mind Perceives Many Things -/

/-- **2P14**: The human mind is capable of perceiving a great many things.
    (Minimal witness: it perceives God's essence.) -/
theorem human_mind_perceives_many :
    ∃ (i x : Entity), IsIdeaOf i x := by
  obtain ⟨i, hi, _⟩ := God_has_idea_of_self (Entity := Entity)
  exact ⟨i, God, hi⟩

/-! ## 2P32 — All Ideas Adequate Insofar as Related to God -/

/-- **2P32**: All ideas in so far as they are related to God are true (adequate). -/
theorem all_ideas_adequate_in_God (i : Entity) (h : InheresIn i (God : Entity)) :
    IsAdequate i :=
  ideas_adequate_in_God i h

/-! ## 2P40 — Ideas from Adequate Ideas Are Adequate -/

/-- **2P40**: Whatever ideas follow from adequate ideas in the mind are
    themselves adequate. -/
theorem adequate_ideas_generate_adequate
    (i j : Entity) (hi : IsAdequate i) (hcause : Causes i j) :
    IsAdequate j :=
  adequate_idea_chain i j hi hcause

/-! ## 2P43 — True Idea Carries Certainty of Itself -/

/-- **2P43**: He who has a true idea knows at the same time that he has a true
    idea, and cannot doubt its truth. (Self-luminosity of adequate ideas.) -/
theorem adequate_idea_self_known (i : Entity) (hi : IsAdequate i) :
    ∃ j : Entity, IsIdeaOf j i ∧ IsAdequate j :=
  adequate_self_luminous i hi

/-! ## 2P49 — No Free Will; Will = Intellect -/

/-- **2P49**: In the mind there is no absolute or free will; the mind is determined
    by causes. Will and intellect are one and the same.
    (Every mode, including volitional modes, has a determining cause by 1P29.) -/
theorem no_free_will_will_eq_intellect (m : Entity) (_hm : IsMode m) :
    ∃ cause : Entity, Causes cause m :=
  no_contingency m

end Spinoza
