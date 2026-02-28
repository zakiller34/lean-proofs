/-
Temporal Logic — Filter Bridge
Bridge between suffix-based temporal operators and Mathlib's Filter.Eventually/Frequently.

For state predicates:
- □◇(lift P) σ ↔ ∃ᶠ n in atTop, P(σ n)  (Frequently)
- ◇□(lift P) σ ↔ ∀ᶠ n in atTop, P(σ n)  (Eventually)
-/
import TemporalLogic.Defs
import Mathlib.Order.Filter.AtTopBot.Basic

namespace TemporalLogic

open Filter

variable {α : Type*} {P : α → Prop} {σ : Behavior α}

-- Helper: lift P on a suffix evaluates P at σ(n)
private theorem lift_suffix (P : α → Prop) (σ : Behavior α) (n : ℕ) :
    lift P (suffix n σ) ↔ P (σ n) := by
  simp [lift, suffix]

-- T10: □◇(lift P) σ ↔ ∃ᶠ n in atTop, P(σ n)
theorem infOften_lift_iff_frequently :
    InfOften (lift P) σ ↔ ∃ᶠ n in atTop, P (σ n) := by
  simp only [InfOften, Always, Eventually, frequently_atTop]
  constructor
  · intro h a
    obtain ⟨m, hm⟩ := h a
    rw [lift_suffix] at hm
    exact ⟨a + m, Nat.le_add_right a m, by rwa [suffix_apply] at hm⟩
  · intro h n
    obtain ⟨b, hb, hP⟩ := h n
    refine ⟨b - n, ?_⟩
    rw [lift_suffix, suffix_apply, Nat.add_sub_cancel' hb]
    exact hP

-- T11: ◇□(lift P) σ ↔ ∀ᶠ n in atTop, P(σ n)
theorem eventuallyAlways_lift_iff_eventually :
    EventuallyAlways (lift P) σ ↔ ∀ᶠ n in atTop, P (σ n) := by
  simp only [EventuallyAlways, Eventually, Always, eventually_atTop]
  constructor
  · intro ⟨n, h⟩
    refine ⟨n, fun b hb => ?_⟩
    have := h (b - n)
    rw [lift_suffix, suffix_apply, Nat.add_sub_cancel' hb] at this
    exact this
  · intro ⟨a, h⟩
    refine ⟨a, fun m => ?_⟩
    rw [lift_suffix, suffix_apply]
    exact h (a + m) (Nat.le_add_right a m)

end TemporalLogic
