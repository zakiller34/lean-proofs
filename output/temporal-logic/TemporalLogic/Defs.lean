/-
Temporal Logic — Definitions
Formalization of Chapter 8 (Liveness and Fairness) from Lamport's "Specifying Systems".

Semantic approach: temporal operators on behaviors (ℕ → α) via suffix semantics.
- σ ⊨ □F  means  ∀ n, F(suffix n σ)
- σ ⊨ ◇F  means  ∃ n, F(suffix n σ)
-/
import Mathlib.Order.Filter.AtTopBot.Basic

namespace TemporalLogic

open Filter

variable {α : Type*}

-- D1: A behavior is an infinite sequence of states (Lamport p.88)
abbrev Behavior (α : Type*) := ℕ → α

-- D2: Suffix operator — σ^{+n} (Lamport p.89)
def suffix (n : ℕ) (σ : Behavior α) : Behavior α :=
  fun k => σ (n + k)

-- Key helper: suffix composition (needed throughout)
-- suffix n (suffix m σ) = suffix (m + n) σ
theorem suffix_suffix (n m : ℕ) (σ : Behavior α) :
    suffix n (suffix m σ) = suffix (m + n) σ := by
  funext k
  simp [suffix, Nat.add_assoc]

@[simp] theorem suffix_zero (σ : Behavior α) : suffix 0 σ = σ := by
  funext k; simp [suffix]

@[simp] theorem suffix_apply (n : ℕ) (σ : Behavior α) (k : ℕ) :
    suffix n σ k = σ (n + k) := rfl

-- D3: Always / Box □ (Lamport p.89)
-- σ ⊨ □F  iff  ∀ n, F(σ^{+n})
def Always (F : Behavior α → Prop) (σ : Behavior α) : Prop :=
  ∀ n, F (suffix n σ)

-- D4: Eventually / Diamond ◇ (Lamport p.91)
-- σ ⊨ ◇F  iff  ∃ n, F(σ^{+n})
def Eventually (F : Behavior α → Prop) (σ : Behavior α) : Prop :=
  ∃ n, F (suffix n σ)

-- D5: Infinitely Often □◇ (Lamport p.91)
def InfOften (F : Behavior α → Prop) : Behavior α → Prop :=
  Always (Eventually F)

-- D6: Eventually Always ◇□ (Lamport p.92)
def EventuallyAlways (F : Behavior α → Prop) : Behavior α → Prop :=
  Eventually (Always F)

-- D7: Leads-To ↝ (Lamport p.91)
-- F ↝ G  ≡  □(F ⇒ ◇G)
def LeadsTo (F G : Behavior α → Prop) : Behavior α → Prop :=
  Always (fun σ => F σ → Eventually G σ)

-- D8: Lift a state predicate to a temporal formula
-- (lift P) σ = P(σ 0)  — evaluates P on the first state of the behavior
def lift (P : α → Prop) : Behavior α → Prop :=
  fun σ => P (σ 0)

-- D9: Lift an action (relation on pairs of states) to a temporal formula
-- (liftAction A) σ = A(σ 0)(σ 1)
def liftAction (A : α → α → Prop) : Behavior α → Prop :=
  fun σ => A (σ 0) (σ 1)

-- D10: Enabled — an action A is enabled in state s iff some successor exists (Lamport p.97)
def Enabled (A : α → α → Prop) (s : α) : Prop :=
  ∃ s', A s s'

-- D11: Angle-action ⟨A⟩_v — action A that changes state function v (Lamport p.97)
-- A non-stuttering step of A with respect to v
def AngleAction (A : α → α → Prop) (v : α → β) : α → α → Prop :=
  fun s s' => A s s' ∧ v s ≠ v s'

-- D12: Weak Fairness WF_v(A) (Lamport p.97)
-- □(□ENABLED⟨A⟩_v ⇒ ◇⟨A⟩_v)
def WF (A : α → α → Prop) (v : α → β) : Behavior α → Prop :=
  Always (fun σ => Always (lift (Enabled (AngleAction A v))) σ →
    Eventually (liftAction (AngleAction A v)) σ)

-- D13: Strong Fairness SF_v(A) (Lamport p.106)
-- ◇□(¬ENABLED⟨A⟩_v) ∨ □◇⟨A⟩_v
def SF (A : α → α → Prop) (v : α → β) : Behavior α → Prop :=
  fun σ => EventuallyAlways (fun σ' => ¬ Enabled (AngleAction A v) (σ' 0)) σ ∨
    InfOften (liftAction (AngleAction A v)) σ

-- D14: Safety property (Lamport p.111)
-- A set of behaviors is a safety property if it is closed under prefix-extension:
-- if σ ∉ S, then some finite prefix of σ cannot be extended to stay in S
def IsSafetyProperty (S : Set (Behavior α)) : Prop :=
  ∀ σ, σ ∉ S → ∃ n, ∀ σ', (∀ k ≤ n, σ' k = σ k) → σ' ∉ S

-- D15: Liveness property (Lamport p.111)
-- Every finite prefix can be extended to a member
def IsLivenessProperty (L : Set (Behavior α)) : Prop :=
  ∀ σ : Behavior α, ∀ n : ℕ, ∃ σ' ∈ L, ∀ k ≤ n, σ' k = σ k

-- D16: Machine closure (Lamport p.111)
-- (S, L) is machine closed iff every finite S-behavior extends to S ∧ L behavior
def IsMachineClosed (S L : Set (Behavior α)) : Prop :=
  ∀ σ ∈ S, ∀ n : ℕ, ∃ σ' ∈ S ∩ L, ∀ k ≤ n, σ' k = σ k

-- Scoped notation
scoped prefix:max "□ " => Always
scoped prefix:max "◇ " => Eventually
scoped notation:max "□◇ " => InfOften
scoped notation:max "◇□ " => EventuallyAlways
scoped notation F " ↝ " G => LeadsTo F G

end TemporalLogic
