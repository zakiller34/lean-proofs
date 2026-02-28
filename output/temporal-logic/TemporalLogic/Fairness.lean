/-
Temporal Logic — Fairness
Weak and Strong Fairness equivalences from Lamport Ch.8 §8.4, §8.6.
-/
import TemporalLogic.Defs
import TemporalLogic.Tautologies

namespace TemporalLogic

open TemporalLogic

variable {α β : Type*} {A : α → α → Prop} {v : α → β} {σ : Behavior α}

/-! ## Fairness abbreviations for readability -/

private abbrev enabledAv (A : α → α → Prop) (v : α → β) : α → Prop :=
  fun s => Enabled (AngleAction A v) s

private abbrev angleAv (A : α → α → Prop) (v : α → β) : Behavior α → Prop :=
  liftAction (AngleAction A v)

/-! ## Helper: unfold WF/SF to ℕ arithmetic -/

-- WF unfolded: □(□ENABLED → ◇action)
-- = ∀ n, (∀ m, ENABLED(σ(n+m))) → ∃ m, action(σ(n+m), σ(n+m+1))
private theorem wf_unfold :
    WF A v σ ↔
      ∀ n, (∀ m, Enabled (AngleAction A v) (σ (n + m))) →
        ∃ m, AngleAction A v (σ (n + m)) (σ (n + m + 1)) := by
  unfold WF Always Eventually lift liftAction suffix Enabled AngleAction
  simp only [Nat.add_zero, Nat.add_assoc]

-- InfOften (¬ENABLED) unfolded
private theorem infOften_not_enabled_unfold :
    InfOften (lift (fun s => ¬ enabledAv A v s)) σ ↔
      ∀ n, ∃ m, ¬ Enabled (AngleAction A v) (σ (n + m)) := by
  unfold InfOften Always Eventually lift suffix enabledAv
  simp only [Nat.add_zero]

-- InfOften (action) unfolded
private theorem infOften_action_unfold :
    InfOften (angleAv A v) σ ↔
      ∀ n, ∃ m, AngleAction A v (σ (n + m)) (σ (n + m + 1)) := by
  unfold InfOften Always Eventually angleAv liftAction suffix
  simp only [Nat.add_zero, Nat.add_assoc]

-- EventuallyAlways (ENABLED) unfolded
private theorem evAlw_enabled_unfold :
    EventuallyAlways (lift (enabledAv A v)) σ ↔
      ∃ n, ∀ m, Enabled (AngleAction A v) (σ (n + m)) := by
  unfold EventuallyAlways Eventually Always lift suffix enabledAv
  simp only [Nat.add_zero]

-- EventuallyAlways (¬ENABLED) unfolded
private theorem evAlw_not_enabled_unfold :
    EventuallyAlways (fun σ' => ¬ Enabled (AngleAction A v) (σ' 0)) σ ↔
      ∃ n, ∀ m, ¬ Enabled (AngleAction A v) (σ (n + m)) := by
  unfold EventuallyAlways Eventually Always suffix
  simp only [Nat.add_zero]

-- InfOften (ENABLED) unfolded
private theorem infOften_enabled_unfold :
    InfOften (lift (enabledAv A v)) σ ↔
      ∀ n, ∃ m, Enabled (AngleAction A v) (σ (n + m)) := by
  unfold InfOften Always Eventually lift suffix enabledAv
  simp only [Nat.add_zero]

/-! ## T12: WF ↔ □◇(¬ENABLED) ∨ □◇⟨A⟩_v (Lamport p.98, eq 1↔2) -/

theorem wf_iff_infOften_not_enabled_or_infOften_action :
    WF A v σ ↔
      InfOften (lift (fun s => ¬ enabledAv A v s)) σ ∨
      InfOften (angleAv A v) σ := by
  rw [wf_unfold, infOften_not_enabled_unfold, infOften_action_unfold]
  constructor
  · -- → : by contradiction
    intro h
    by_contra h_neg
    -- h_neg : ¬((∀ n, ∃ m, ¬en) ∨ (∀ n, ∃ m, act))
    rw [not_or] at h_neg
    obtain ⟨hEn, hAct⟩ := h_neg
    -- hEn : ¬∀ n, ∃ m, ¬en  →  ∃ n₁, ∀ m, en
    rw [not_forall] at hEn hAct
    obtain ⟨n₁, hEn⟩ := hEn
    obtain ⟨n₂, hAct⟩ := hAct
    rw [not_exists] at hEn hAct
    -- hEn : ∀ m, ¬¬en = ∀ m, en;  hAct : ∀ m, ¬act
    -- WF at n₁+n₂: if □ENABLED then ◇action
    have hWF := h (n₁ + n₂)
    have hAllEn : ∀ m, Enabled (AngleAction A v) (σ (n₁ + n₂ + m)) := by
      intro m
      have := hEn (n₂ + m)
      rw [not_not] at this
      rwa [show n₁ + (n₂ + m) = n₁ + n₂ + m from by omega] at this
    obtain ⟨m, hm⟩ := hWF hAllEn
    have := hAct (n₁ + m)
    rw [show n₂ + (n₁ + m) = n₁ + n₂ + m from by omega] at this
    exact this hm
  · -- ← : case split
    intro h n hEn
    cases h with
    | inl hNotEn =>
      obtain ⟨m, hm⟩ := hNotEn n
      exact absurd (hEn m) hm
    | inr hAct =>
      obtain ⟨m, hm⟩ := hAct n
      exact ⟨m, hm⟩

/-! ## T13: WF ↔ ◇□ENABLED → □◇⟨A⟩_v (Lamport p.98, eq 1↔3) -/

theorem wf_iff_eventuallyAlways_enabled_imp_infOften_action :
    WF A v σ ↔
      (EventuallyAlways (lift (enabledAv A v)) σ →
       InfOften (angleAv A v) σ) := by
  rw [wf_iff_infOften_not_enabled_or_infOften_action,
      infOften_not_enabled_unfold, infOften_action_unfold, evAlw_enabled_unfold]
  constructor
  · intro h hEvAlw
    cases h with
    | inl hNotEn =>
      exfalso
      obtain ⟨n, hAlw⟩ := hEvAlw
      obtain ⟨m, hNot⟩ := hNotEn n
      exact hNot (hAlw m)
    | inr hAct => exact hAct
  · intro h
    by_cases hEvAlw : ∃ n, ∀ m, Enabled (AngleAction A v) (σ (n + m))
    · exact Or.inr (h hEvAlw)
    · left
      push_neg at hEvAlw
      exact hEvAlw

/-! ## T14: SF ↔ □◇ENABLED → □◇⟨A⟩_v (Lamport p.106) -/

theorem sf_iff_infOften_enabled_imp_infOften_action :
    SF A v σ ↔
      (InfOften (lift (enabledAv A v)) σ →
       InfOften (angleAv A v) σ) := by
  rw [SF, evAlw_not_enabled_unfold, infOften_action_unfold, infOften_enabled_unfold]
  constructor
  · intro h hInfEn
    cases h with
    | inl hEvAlwNot =>
      exfalso
      obtain ⟨n, hNot⟩ := hEvAlwNot
      obtain ⟨m, hEn⟩ := hInfEn n
      exact hNot m hEn
    | inr hAct => exact hAct
  · intro h
    by_cases hInfEn : ∀ n, ∃ m, Enabled (AngleAction A v) (σ (n + m))
    · exact Or.inr (h hInfEn)
    · left
      push_neg at hInfEn
      exact hInfEn

/-! ## T15: SF → WF (Lamport p.106) -/

-- Key lemma: ◇□P → □◇P (eventuallyAlways implies infOften)
theorem eventuallyAlways_imp_infOften {F : Behavior α → Prop} :
    EventuallyAlways F σ → InfOften F σ := by
  intro ⟨n₀, hAlw⟩ n
  refine ⟨n₀, ?_⟩
  simp only [Always, suffix_suffix] at hAlw ⊢
  convert hAlw n using 2; omega

-- SF_v(A) → WF_v(A)
theorem sf_imp_wf (h : SF A v σ) : WF A v σ := by
  rw [wf_iff_eventuallyAlways_enabled_imp_infOften_action]
  rw [sf_iff_infOften_enabled_imp_infOften_action] at h
  intro hEvAlw
  exact h (eventuallyAlways_imp_infOften hEvAlw)

/-! ## Example E5: Toggle system -/

private def toggleAction : ℕ → ℕ → Prop := fun s s' => (s = 0 ∧ s' = 1) ∨ (s = 1 ∧ s' = 0)
private def idFun : ℕ → ℕ := id
private def toggleBeh : Behavior ℕ := fun n => n % 2

example : WF toggleAction idFun toggleBeh := by
  rw [wf_iff_infOften_not_enabled_or_infOften_action, infOften_action_unfold]
  right
  intro n
  refine ⟨0, ?_⟩
  simp only [AngleAction, toggleAction, toggleBeh, idFun, id]
  constructor
  · by_cases h : (n % 2 = 0) <;> [left; right] <;> omega
  · omega

end TemporalLogic
