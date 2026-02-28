/-
Temporal Logic — Tautologies
Basic temporal tautologies and proof rules from Lamport Ch.8 §8.2-8.3.
-/
import TemporalLogic.Defs

namespace TemporalLogic

open TemporalLogic

variable {α : Type*} {F G : Behavior α → Prop} {σ : Behavior α}

/-! ## T1-T2: Distributivity (Lamport p.92) -/

-- T1: □(F ∧ G) ↔ □F ∧ □G
theorem always_and :
    (□ fun σ => F σ ∧ G σ) σ ↔ (□ F) σ ∧ (□ G) σ := by
  simp only [Always]
  exact forall_and

-- T2: ◇(F ∨ G) ↔ ◇F ∨ ◇G
theorem eventually_or :
    (◇ fun σ => F σ ∨ G σ) σ ↔ (◇ F) σ ∨ (◇ G) σ := by
  simp only [Eventually]
  exact exists_or

/-! ## T3-T4: Duality (Lamport p.91) -/

-- T3: □F ↔ ¬◇¬F
theorem always_iff_not_eventually_not :
    (□ F) σ ↔ ¬ (◇ fun σ => ¬ F σ) σ := by
  simp only [Always, Eventually, not_exists, not_not]

-- T4: ◇F ↔ ¬□¬F
theorem eventually_iff_not_always_not :
    (◇ F) σ ↔ ¬ (□ fun σ => ¬ F σ) σ := by
  simp only [Always, Eventually, not_forall, not_not]

/-! ## T5: □F → ◇F -/

-- T5: Always implies Eventually (instantiate at n=0)
theorem always_imp_eventually (h : (□ F) σ) : (◇ F) σ :=
  ⟨0, h 0⟩

/-! ## T6-T7: Distributivity for □◇ and ◇□ (Lamport p.94) -/

-- T6: □◇(F ∨ G) ↔ □◇F ∨ □◇G
-- The → direction needs classical logic
theorem infOften_or :
    (□◇ fun σ => F σ ∨ G σ) σ ↔ InfOften F σ ∨ InfOften G σ := by
  -- Unfold to ℕ-level for cleaner arithmetic
  simp only [InfOften, Always, Eventually, suffix_suffix]
  constructor
  · -- → direction: by classical contradiction
    intro h
    by_contra h_neg
    push_neg at h_neg
    obtain ⟨hF, hG⟩ := h_neg
    obtain ⟨nF, hF⟩ := hF
    obtain ⟨nG, hG⟩ := hG
    -- At n = nF + nG, neither can hold
    obtain ⟨m, hm⟩ := h (nF + nG)
    cases hm with
    | inl hFm =>
      exact hF (nG + m) (by rwa [show nF + (nG + m) = nF + nG + m from by omega])
    | inr hGm =>
      exact hG (nF + m) (by rwa [show nG + (nF + m) = nF + nG + m from by omega])
  · -- ← direction: straightforward
    intro h n
    cases h with
    | inl hF =>
      obtain ⟨m, hm⟩ := hF n
      exact ⟨m, Or.inl hm⟩
    | inr hG =>
      obtain ⟨m, hm⟩ := hG n
      exact ⟨m, Or.inr hm⟩

-- T7: ◇□(F ∧ G) ↔ ◇□F ∧ ◇□G
theorem eventuallyAlways_and :
    (◇□ fun σ => F σ ∧ G σ) σ ↔ EventuallyAlways F σ ∧ EventuallyAlways G σ := by
  constructor
  · -- → direction: project out each conjunct
    intro ⟨n, h⟩
    exact ⟨⟨n, fun m => (h m).1⟩, ⟨n, fun m => (h m).2⟩⟩
  · -- ← direction: take max of witnesses
    intro ⟨⟨nF, hF⟩, ⟨nG, hG⟩⟩
    simp only [EventuallyAlways, Eventually, Always, suffix_suffix] at *
    refine ⟨nF + nG, fun m => ?_⟩
    constructor
    · have := hF (nG + m)
      rwa [show nF + (nG + m) = nF + nG + m from by omega] at this
    · have := hG (nF + m)
      rwa [show nG + (nF + m) = nF + nG + m from by omega] at this

/-! ## T8-T9: Proof Rules (Lamport p.95) -/

-- T8: Generalization: if F holds for all behaviors, then □F holds for all behaviors
theorem generalization (h : ∀ σ, F σ) : ∀ σ, (□ F) σ :=
  fun σ n => h (suffix n σ)

-- T9: Implies Generalization: if F→G for all behaviors, then □F→□G
theorem implies_generalization (h : ∀ σ, F σ → G σ) :
    ∀ σ, (□ F) σ → (□ G) σ :=
  fun σ hF n => h (suffix n σ) (hF n)

/-! ## Concrete examples -/

-- E1: Constant-zero behavior satisfies □(lift (· = 0))
example : (□ (lift (· = 0))) (fun _ : ℕ => (0 : ℕ)) := by
  intro n; simp [lift, suffix]

-- E2: Alternating 0/1 behavior satisfies □◇(lift (· = 0))
example : (□◇ (lift (· = 0))) (fun n : ℕ => n % 2) := by
  intro n
  by_cases h : (n % 2 = 0)
  · exact ⟨0, by simp [lift, suffix, h]⟩
  · exact ⟨1, by simp [lift, suffix]; omega⟩

-- E3: Eventually-constant behavior satisfies ◇□(lift (· = 1))
example : (◇□ (lift (· = 1))) (fun n : ℕ => if n < 5 then 0 else 1) := by
  refine ⟨5, fun m => ?_⟩
  simp only [lift, suffix_apply]
  split <;> omega

end TemporalLogic
