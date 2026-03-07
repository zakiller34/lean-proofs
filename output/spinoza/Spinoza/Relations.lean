import Spinoza.Domain
/-!
# Relations — Derived Relational Facts (MSC 03B45)

Convenience lemmas and type aliases for Spinoza's primitive relations.
-/
namespace Spinoza

variable {Entity : Type*} [SpinozaFramework Entity]

open SpinozaFramework

/-- A substance inheres in itself (D3). -/
def substanceInheresInSelf (s : Entity) (hs : IsSubstance s) : InheresIn s s :=
  hs.1

/-- A substance is conceived through itself (D3). -/
def substanceConceivedThroughSelf (s : Entity) (hs : IsSubstance s) : ConceivedThrough s s :=
  hs.2

/-- A mode is not a substance (from D5). -/
lemma mode_not_substance (x : Entity) (hm : IsMode x) : ¬IsSubstance x := by
  obtain ⟨_, _, _, _, hns⟩ := hm
  exact hns

/-- Substance and mode are mutually exclusive. -/
lemma substance_or_mode_exclusive (x : Entity) :
    IsSubstance x → IsMode x → False := by
  intro hs hm
  exact mode_not_substance x hm hs

/-- x is its own cause iff Causes x x. -/
def IsCausallySelfsufficient (x : Entity) : Prop :=
  Causes x x

end Spinoza
