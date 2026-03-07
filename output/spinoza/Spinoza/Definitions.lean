import Mathlib.Data.Set.Finite.Basic
import Spinoza.Domain
import Spinoza.Relations
/-!
# Definitions D1–D8 (MSC 03A05, 03B45)

Formal encodings of Spinoza's eight definitions from Part I of the *Ethics*.
-/
namespace Spinoza

variable {Entity : Type*} [SpinozaFramework Entity]

open SpinozaFramework

/-! ## D1 — Causa Sui (1d1) -/

/-- D1: A thing is *causa sui* whose essence involves existence;
    whose nature cannot be conceived except as existing. -/
def IsCausaSui (x : Entity) : Prop :=
  Causes x x ∧ Necessarily (∃ y : Entity, y = x)

/-! ## D2 — Finite in Its Kind (1d2) -/

/-- D2: x is finite in its own kind if it can be limited by
    another thing of the same nature. -/
def FiniteInKind (x : Entity) (SameKind : Entity → Entity → Prop) : Prop :=
  ∃ y : Entity, SameKind x y ∧ y ≠ x

/-- D2b: x is infinite in its kind if it is not finite in its kind. -/
def InfiniteInKind (x : Entity) (SameKind : Entity → Entity → Prop) : Prop :=
  ¬FiniteInKind x SameKind

/-! ## D6 — God (1d6) -/

/-- D6: God is a substance consisting of infinitely many attributes,
    each of which expresses eternal and infinite essence. -/
def IsGod (g : Entity) : Prop :=
  IsSubstance g ∧
  Set.Infinite {a : Entity | HasAttribute g a}

/-! ## D7 — Free vs. Necessitated Thing (1d7) -/

/-- D7a: A thing is *free* if it exists by the necessity of its own
    nature alone and is determined to act by itself alone. -/
def IsFree (x : Entity) : Prop :=
  IsCausaSui x ∧ ∀ y : Entity, Causes y x → y = x

/-- D7b: A thing is *necessitated* if it is determined by something
    external to exist and act in a fixed way. -/
def IsNecessitated (x : Entity) : Prop :=
  ∃ y : Entity, y ≠ x ∧ Causes y x

/-! ## D8 — Eternity (1d8) -/

/-- D8: Eternity is existence itself insofar as it is conceived to follow
    necessarily from the definition of an eternal thing alone. -/
def IsEternal (x : Entity) : Prop :=
  Necessarily (∃ y : Entity, y = x)
  -- Note: "not bounded by time" deferred — requires a Time type.

/-! ## D4 — Attribute (1d4) -/

/-- D4 (objectivist reading): An attribute is what constitutes a substance's essence;
    conceived through itself. -/
def IsAttributeOf (a s : Entity) : Prop :=
  HasAttribute s a ∧ ConceivedThrough a a

end Spinoza
