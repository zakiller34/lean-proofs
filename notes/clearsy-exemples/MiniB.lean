/-! Mini-B en Lean 4 : une machine = invariant + initialisation + opérations
    vues comme relations avant/après. Les obligations de preuve (PO) de B
    deviennent deux champs d'une structure. -/

structure Machine (σ : Type) where
  inv  : σ → Prop
  init : σ → Prop
  ops  : List (σ → σ → Prop)

/-- Les deux familles de PO de B : initialisation et préservation. -/
structure Correct {σ : Type} (M : Machine σ) : Prop where
  po_init : ∀ s, M.init s → M.inv s
  po_ops  : ∀ op ∈ M.ops, ∀ s s', M.inv s → op s s' → M.inv s'

/-- Théorème de « méta-niveau » : si les PO sont prouvées, l'invariant
    tient sur toute exécution (c'est l'induction que B fait pour vous). -/
theorem inv_toujours {σ : Type} (M : Machine σ) (h : Correct M) (b : Nat → σ)
    (h0 : M.init (b 0)) (hpas : ∀ n, ∃ op ∈ M.ops, op (b n) (b (n+1))) :
    ∀ n, M.inv (b n) := by
  intro n
  induction n with
  | zero => exact h.po_init _ h0
  | succ k ih =>
    obtain ⟨op, hop, hs⟩ := hpas k
    exact h.po_ops op hop _ _ ih hs

-- L'exemple fil rouge : la porte du train.
inductive Porte | ouverte | fermee deriving DecidableEq

structure Etat where
  porte   : Porte
  vitesse : Nat

def inv (s : Etat) : Prop := s.vitesse > 0 → s.porte = .fermee

def ouvrir (s s' : Etat) : Prop := s.vitesse = 0 ∧ s' = { s with porte := .ouverte }
def accelerer (s s' : Etat) : Prop :=
  ∃ dv > 0, s.porte = .fermee ∧ s' = { s with vitesse := s.vitesse + dv }

theorem po_ouvrir : ∀ s s', inv s → ouvrir s s' → inv s' := by
  rintro s s' _ ⟨h0, rfl⟩ hv
  simp at hv
  omega

theorem po_accelerer : ∀ s s', inv s → accelerer s s' → inv s' := by
  rintro s s' _ ⟨dv, _, hp, rfl⟩ _
  exact hp

/-- Sans la garde `vitesse = 0`, la PO est fausse : contre-exemple. -/
def ouvrir_bug (s s' : Etat) : Prop := s' = { s with porte := .ouverte }

theorem po_ouvrir_bug_fausse : ¬ ∀ s s', inv s → ouvrir_bug s s' → inv s' := by
  intro h
  have := h ⟨.fermee, 1⟩ ⟨.ouverte, 1⟩ (fun _ => rfl) rfl (by decide)
  cases this
