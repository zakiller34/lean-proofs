/-
Temporal Logic — CsLib Bridge
Correspondence between suffix-based temporal operators and cslib ωSequence.

Note: cslib uses lean-toolchain rc1, output uses rc2. Direct imports would
require toolchain alignment. Instead, we prove the correspondence abstractly
by defining the bridge locally, matching cslib's API:
  - ωSequence.drop n s = fun i => s (i + n)
  - ωSequence.LeadsTo xs p q = ∀ k, xs k ∈ p → ∃ k' ≥ k, xs k' ∈ q

When toolchains are aligned, replace local defs with `import Cslib.Foundations...`.
-/
import TemporalLogic.Defs
import TemporalLogic.FilterBridge
import Mathlib.Order.Filter.AtTopBot.Basic

namespace TemporalLogic.CslibBridge

open TemporalLogic Filter

variable {α : Type*}

/-! ## Local cslib-compatible definitions -/

-- Mirrors cslib ωSequence.drop
def drop (n : ℕ) (σ : ℕ → α) : ℕ → α := fun i => σ (i + n)

-- Mirrors cslib ωSequence.LeadsTo
def OmegaLeadsTo (σ : ℕ → α) (p q : Set α) : Prop :=
  ∀ k, σ k ∈ p → ∃ k', k ≤ k' ∧ σ k' ∈ q

/-! ## T19: suffix ↔ drop -/

-- suffix n σ = drop n σ (same function, different arg order in cslib)
theorem suffix_eq_drop (n : ℕ) (σ : Behavior α) :
    suffix n σ = drop n σ := by
  funext k
  simp [suffix, drop, Nat.add_comm]

/-! ## T20: LeadsTo (lift P) (lift Q) ↔ OmegaLeadsTo -/

-- Our LeadsTo on lifted predicates corresponds to cslib's LeadsTo
theorem leadsTo_lift_iff_omegaLeadsTo (P Q : Set α) (σ : Behavior α) :
    LeadsTo (lift (· ∈ P)) (lift (· ∈ Q)) σ ↔ OmegaLeadsTo σ P Q := by
  simp only [LeadsTo, Always, Eventually, lift, suffix, OmegaLeadsTo, Nat.add_zero]
  constructor
  · intro h k hP
    obtain ⟨m, hm⟩ := h k hP
    exact ⟨k + m, Nat.le_add_right k m, hm⟩
  · intro h n hP
    obtain ⟨k', hk', hQ⟩ := h n hP
    exact ⟨k' - n, by rwa [Nat.add_sub_cancel' hk']⟩

/-! ## T21: InfOften (lift P) ↔ frequently in cslib sense -/

-- cslib uses: ∃ᶠ k in atTop, xs k ∈ P (via Filter.Frequently)
-- This is exactly our T10 (infOften_lift_iff_frequently)
theorem infOften_lift_iff_omega_frequently (P : Set α) (σ : Behavior α) :
    InfOften (lift (· ∈ P)) σ ↔ ∃ᶠ k in atTop, σ k ∈ P :=
  infOften_lift_iff_frequently

-- Additional: drop commutes with suffix
theorem drop_drop_eq_suffix_suffix (n m : ℕ) (σ : Behavior α) :
    drop n (drop m σ) = drop (m + n) σ := by
  funext k; simp only [drop]; congr 1; omega

end TemporalLogic.CslibBridge
