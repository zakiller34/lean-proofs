import Spinoza.Axioms
/-!
# Mind Axioms — Part II Framework (MSC 03A05, 03B45)

`SpinozaMindFramework` extends `SpinozaFramework` with the attributes Thought
and Extension, plus the mind-body correspondence structure needed for Part II.
-/
namespace Spinoza

/-- Extended framework for Part II: adds mind-body structure. -/
class SpinozaMindFramework (Entity : Type*) extends SpinozaFramework Entity where
  /-- The attribute Thought (constitutes God's thinking essence). -/
  Thought : Entity
  /-- The attribute Extension (constitutes God's bodily essence). -/
  Extension : Entity
  /-- `IsIdeaOf i x` : i is an idea of (represents) x. -/
  IsIdeaOf : Entity → Entity → Prop
  /-- `IsAdequate i` : idea i is adequate (complete, intrinsically true). -/
  IsAdequate : Entity → Prop
  /-- `MindOf b` : the idea/mind that corresponds to object b. -/
  MindOf : Entity → Entity
  /-- The human body (a finite mode of Extension). -/
  Body : Entity

variable {Entity : Type*} [SpinozaMindFramework Entity]

open SpinozaFramework SpinozaMindFramework

/-! ## Axioms for Part II -/

/-- 2P1 basis: Thought is an attribute of God. -/
axiom ThoughtIsAttr : HasAttribute (God : Entity) (Thought : Entity)

/-- 2P2 basis: Extension is an attribute of God. -/
axiom ExtensionIsAttr : HasAttribute (God : Entity) (Extension : Entity)

/-- Thought and Extension are distinct attributes. -/
axiom thought_extension_distinct : (Thought : Entity) ≠ (Extension : Entity)

/-- 2P7 (Parallelism): Order and connection of ideas = order and connection of things. -/
axiom parallelism : ∀ (x y : Entity),
  Causes x y ↔ Causes (MindOf x) (MindOf y)

/-- Mind-body axiom: every object b has a corresponding idea (its mind). -/
axiom mind_body_axiom : ∀ (b : Entity), IsIdeaOf (MindOf b) b

/-- Common notions: an idea present in all minds is adequate (2P38 basis). -/
axiom common_notions_adequate : ∀ (i : Entity),
  (∀ x : Entity, IsIdeaOf i x) → IsAdequate i

/-- 2P9 basis: if i is an idea of mode m, then i inheres in God. -/
axiom idea_of_mode_in_God : ∀ (m i : Entity),
  IsMode m → IsIdeaOf i m → InheresIn i (God : Entity)

/-- 2P3 basis: God has an adequate idea of His own essence. -/
axiom God_has_idea_of_self : ∃ i : Entity, IsIdeaOf i (God : Entity) ∧ IsAdequate i

/-- 2P32 basis: every idea inhering in God is adequate. -/
axiom ideas_adequate_in_God : ∀ (i : Entity),
  InheresIn i (God : Entity) → IsAdequate i

/-- 2P40 basis: ideas caused by adequate ideas are adequate. -/
axiom adequate_idea_chain : ∀ (i j : Entity),
  IsAdequate i → Causes i j → IsAdequate j

/-- 2P43 basis: adequate ideas are self-luminous (knowing → knowing-that-one-knows). -/
axiom adequate_self_luminous : ∀ (i : Entity),
  IsAdequate i → ∃ j : Entity, IsIdeaOf j i ∧ IsAdequate j

/-- 2P7C basis: God's thinking power equals His acting power (via parallelism). -/
axiom God_thinking_eq_acting : ∀ (m : Entity),
  IsMode m → Causes (MindOf (God : Entity)) (MindOf m)

end Spinoza
