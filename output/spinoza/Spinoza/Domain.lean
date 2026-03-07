import Mathlib.Data.Set.Basic
import Spinoza.ModalLogic
/-!
# Domain — Primitive Sorts and Framework (MSC 03B45, 03A05)

Spinoza's ontology has three kinds: substance, mode, attribute.
We bundle all primitive relations into `SpinozaFramework`,
a typeclass parameterized over an entity domain `Entity : Type*`.
-/
namespace Spinoza

/-- Bundle of all primitive Spinoza relations over an entity domain. -/
class SpinozaFramework (Entity : Type*) where
  /-- `InheresIn x y` : x exists in y as a subject (ontological inherence) -/
  InheresIn : Entity → Entity → Prop
  /-- `ConceivedThrough x y` : the concept of x requires the concept of y -/
  ConceivedThrough : Entity → Entity → Prop
  /-- `HasAttribute s a` : substance s has attribute a constituting its essence -/
  HasAttribute : Entity → Entity → Prop
  /-- `Causes x y` : x is an efficient cause of y -/
  Causes : Entity → Entity → Prop
  /-- `Prevents x y` : x is a reason for the non-existence of y -/
  Prevents : Entity → Entity → Prop
  /-- The unique individual: God or Nature (Deus sive Natura) -/
  God : Entity

variable {Entity : Type*} [SpinozaFramework Entity]

open SpinozaFramework

/-- D3: A substance is what is in itself and conceived through itself. -/
def IsSubstance (x : Entity) : Prop :=
  InheresIn x x ∧ ConceivedThrough x x

/-- D5: A mode is an affection of substance — in another, conceived through another. -/
def IsMode (x : Entity) : Prop :=
  ∃ s : Entity, IsSubstance s ∧
    InheresIn x s ∧
    ConceivedThrough x s ∧
    ¬IsSubstance x

/-- An attribute is conceived through itself (objectivist reading — Viljanen). -/
def IsAttributeDef (a : Entity) : Prop :=
  ConceivedThrough a a

end Spinoza
