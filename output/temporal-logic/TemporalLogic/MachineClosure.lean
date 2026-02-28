/-
Temporal Logic — Machine Closure
Safety, liveness, and machine closure from Lamport Ch.8 §8.9.
-/
import TemporalLogic.Defs
import TemporalLogic.Tautologies
import TemporalLogic.Fairness

namespace TemporalLogic

open TemporalLogic

variable {α : Type*} {F G H : Behavior α → Prop} {σ : Behavior α}

/-! ## T16: LeadsTo is transitive (Lamport p.91) -/

theorem leadsTo_trans :
    LeadsTo F G σ → LeadsTo G H σ → LeadsTo F H σ := by
  intro hFG hGH n hF
  obtain ⟨m, hG⟩ := hFG n hF
  rw [suffix_suffix] at hG
  obtain ⟨k, hH⟩ := hGH (n + m) hG
  rw [suffix_suffix] at hH
  exact ⟨m + k, by rwa [suffix_suffix, show n + (m + k) = n + m + k from by omega]⟩

-- T17 (◇□P → □◇P) is `eventuallyAlways_imp_infOften` from Fairness.lean

/-! ## T18: Safety, Liveness, Machine Closure -/

-- Safety property: if σ ∉ S, some finite prefix witnesses the violation
-- IsSafetyProperty defined in Defs.lean

-- Liveness property: every finite prefix extends to a member
-- IsLivenessProperty defined in Defs.lean

-- Machine closure: every finite S-behavior extends to S ∩ L
-- IsMachineClosed defined in Defs.lean

-- Machine closure with explicit safety witness → S ∩ L is nonempty
theorem machineClosed_inter_nonempty {S L : Set (Behavior α)}
    (hMC : IsMachineClosed S L) (σ₀ : Behavior α) (hσ₀ : σ₀ ∈ S) :
    (S ∩ L).Nonempty := by
  obtain ⟨σ', hσ', _⟩ := hMC σ₀ hσ₀ 0
  exact ⟨σ', hσ'⟩

-- Machine closure + S nonempty → S ∩ L nonempty
-- (hS/hL kept in Lamport's statement but not needed for this direction)
theorem machineClosed_nonempty {S L : Set (Behavior α)}
    (hMC : IsMachineClosed S L) (hne : S.Nonempty) :
    (S ∩ L).Nonempty := by
  obtain ⟨σ₀, hσ₀⟩ := hne
  exact machineClosed_inter_nonempty hMC σ₀ hσ₀

-- Liveness is nonempty
theorem liveness_nonempty {L : Set (Behavior α)} [Nonempty α]
    (hL : IsLivenessProperty L) : L.Nonempty := by
  obtain ⟨σ, hσ, _⟩ := hL (fun _ => Classical.arbitrary α) 0
  exact ⟨σ, hσ⟩

-- Stuttering closure: □[N]_v — every step is N or stuttering
def StutterClosed (N : α → α → Prop) (v : α → β) : Behavior α → Prop :=
  Always (fun σ => N (σ 0) (σ 1) ∨ v (σ 0) = v (σ 1))

-- Safety spec: Init ∧ □[Next]_v
def SafetySpec (Init : α → Prop) (Next : α → α → Prop) (v : α → β) :
    Set (Behavior α) :=
  { σ | Init (σ 0) ∧ StutterClosed Next v σ }

-- SafetySpec is indeed a safety property
-- (violation at step n means Init fails or some Next step fails before n)
theorem safetySpec_is_safety (Init : α → Prop) (Next : α → α → Prop) (v : α → β) :
    IsSafetyProperty (SafetySpec Init Next v) := by
  intro σ hσ
  simp only [SafetySpec, Set.mem_setOf_eq, not_and_or] at hσ
  cases hσ with
  | inl hInit =>
    -- Init fails: prefix of length 0 witnesses violation
    exact ⟨0, fun σ' hpfx => by
      simp only [SafetySpec, Set.mem_setOf_eq, not_and_or]
      left; rw [hpfx 0 (le_refl 0)]; exact hInit⟩
  | inr hNext =>
    -- Some step violates □[Next]_v
    simp only [StutterClosed, Always, not_forall] at hNext
    obtain ⟨n, hn⟩ := hNext
    simp only [suffix_apply, not_or] at hn
    exact ⟨n + 1, fun σ' hpfx => by
      simp only [SafetySpec, StutterClosed, Always, Set.mem_setOf_eq]
      intro ⟨_, hAll⟩
      have := hAll n
      simp only [suffix_apply, Nat.add_zero] at this hn
      rw [hpfx n (by omega), hpfx (n + 1) (by omega)] at this
      exact hn.1 (this.elim id (absurd · hn.2))⟩

end TemporalLogic
