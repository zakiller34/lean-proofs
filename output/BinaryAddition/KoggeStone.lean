/-
  BinaryAddition/KoggeStone.lean — Kogge-Stone 1973 general framework

  Formalizes the parallel prefix framework from "A Parallel Algorithm for the
  Efficient Solution of a General Class of Recurrence Equations" (Kogge & Stone 1973).

  - D6-D9: ParallelPrefix structure with three restrictions + h associativity
  - D10: Generalized composition Q(m,n)
  - T5: Splitting theorem (Theorem 1)
  - T6: Solution correctness (Theorem 2)
  - D11, T7: Algorithm A and its correctness (Theorem 3)
  - T8: Carry-pair instantiates the framework
-/
import BinaryAddition.Defs
import BinaryAddition.BrentKung

namespace BinaryAddition

/-! ## D6-D9: ParallelPrefix — the Kogge-Stone algebraic framework -/

/-- The Kogge-Stone parallel prefix structure.
    Three restrictions on f, g, h plus h associativity (implied by the paper). -/
structure ParallelPrefix (α β : Type*) where
  f : α → α → α
  g : β → α → α
  h : β → β → β
  /-- Restriction 1: f is associative -/
  f_assoc : ∀ x y z, f (f x y) z = f x (f y z)
  /-- Restriction 2: g distributes over f on the left -/
  g_distrib : ∀ a x y, g a (f x y) = f (g a x) (g a y)
  /-- Restriction 3: semi-associativity of g via h -/
  g_semi_assoc : ∀ a b x, g a (g b x) = g (h a b) x
  /-- h is associative (follows from restrictions when g is sufficiently injective;
      included as a field for generality) -/
  h_assoc : ∀ a b c, h (h a b) c = h a (h b c)

variable {α β : Type*}

/-! ## D10: Generalized composition Q(m, n)

    Q(m, n) represents the solution over the range [n, m]. -/

/-- Product of h-coefficients: H(hi, lo) = h(a_hi, h(a_{hi-1}, ...a_lo...)) -/
def hProd (pp : ParallelPrefix α β) (a : Nat → β) (lo hi : Nat) : β :=
  match hi with
  | 0 => a 0
  | n + 1 =>
    if n + 1 ≤ lo then a lo
    else pp.h (a (n + 1)) (hProd pp a lo n)

/-- Generalized composition Q(m, n) over [n, m].
    Base case: Q(n, n) = b_n
    Recursive: Q(m, n) = f(Q(m, n+1), g(hProd(m, n+1), b_n)) -/
noncomputable def Q (pp : ParallelPrefix α β) (a : Nat → β) (b : Nat → α)
    (m n : Nat) : α :=
  if m ≤ n then b n
  else pp.f (Q pp a b m (n + 1)) (pp.g (hProd pp a (n + 1) m) (b n))
  termination_by m - n

/-! ## Helper lemmas for Q and hProd -/

/-- Q base case: when m ≤ n, Q(m,n) = b n -/
theorem Q_base (pp : ParallelPrefix α β) (a : Nat → β) (b : Nat → α)
    (m n : Nat) (h : m ≤ n) : Q pp a b m n = b n := by
  unfold Q; simp [h]

/-- Q recursive case: when ¬(m ≤ n), Q unfolds -/
theorem Q_unfold (pp : ParallelPrefix α β) (a : Nat → β) (b : Nat → α)
    (m n : Nat) (h : ¬(m ≤ n)) :
    Q pp a b m n = pp.f (Q pp a b m (n + 1)) (pp.g (hProd pp a (n + 1) m) (b n)) := by
  conv_lhs => unfold Q
  simp [h]

/-- hProd base: when hi ≤ lo, hProd(lo, hi) = a lo (or a 0 for hi=0) -/
theorem hProd_base_le (pp : ParallelPrefix α β) (a : Nat → β)
    (lo : Nat) (hi : Nat) (h : hi ≤ lo) :
    hProd pp a lo hi = if hi = 0 then a 0 else a lo := by
  cases hi with
  | zero => simp [hProd]
  | succ n =>
    unfold hProd
    simp [h]

/-- hProd at a single point: hProd(lo, lo) = a lo when lo > 0 -/
theorem hProd_self (pp : ParallelPrefix α β) (a : Nat → β)
    (n : Nat) (hn : 0 < n) :
    hProd pp a n n = a n := by
  cases n with
  | zero => omega
  | succ k => unfold hProd; simp

/-- hProd unfold: hProd(lo, hi+1) = h(a(hi+1), hProd(lo, hi)) when lo ≤ hi -/
theorem hProd_succ (pp : ParallelPrefix α β) (a : Nat → β)
    (lo hi : Nat) (h : lo ≤ hi) :
    hProd pp a lo (hi + 1) = pp.h (a (hi + 1)) (hProd pp a lo hi) := by
  simp only [hProd, show ¬(hi + 1 ≤ lo) from by omega, ↓reduceIte]

/-- Key: hProd(lo, hi) = h(hProd(mid+1, hi), hProd(lo, mid)) when lo ≤ mid < hi -/
theorem hProd_split (pp : ParallelPrefix α β) (a : Nat → β)
    (lo mid hi : Nat) (hlo : lo ≤ mid) (hmid : mid < hi) :
    hProd pp a lo hi = pp.h (hProd pp a (mid + 1) hi) (hProd pp a lo mid) := by
  induction hi with
  | zero => omega
  | succ n ih =>
    rw [hProd_succ pp a lo n (by omega)]
    by_cases heq : mid = n
    · subst heq
      rw [hProd_self pp a (mid + 1) (by omega)]
    · have hmid' : mid < n := by omega
      rw [ih hmid', hProd_succ pp a (mid + 1) n (by omega), pp.h_assoc]

/-! ## T5: Splitting theorem (Kogge-Stone Theorem 1) -/

/-- Q "right unfold": Q(m+1, n) = f(b(m+1), g(a(m+1), Q(m, n))) when n ≤ m.
    This peels off the high end of Q instead of the low end. -/
theorem Q_unfold_hi (pp : ParallelPrefix α β) (a : Nat → β) (b : Nat → α)
    (m n : Nat) (h : n ≤ m) :
    Q pp a b (m + 1) n = pp.f (b (m + 1)) (pp.g (a (m + 1)) (Q pp a b m n)) := by
  -- Induction on the gap d = m - n
  obtain ⟨d, rfl⟩ : ∃ d, m = n + d := ⟨m - n, by omega⟩
  clear h
  induction d generalizing n with
  | zero =>
    -- m = n + 0 = n: Q(n+1, n) = f(b(n+1), g(a(n+1), Q(n, n)))
    simp only [Nat.add_zero]
    rw [Q_unfold pp a b (n + 1) n (by omega)]
    rw [Q_base pp a b (n + 1) (n + 1) (Nat.le_refl _)]
    rw [Q_base pp a b n n (Nat.le_refl _)]
    rw [hProd_self pp a (n + 1) (by omega)]
  | succ d' ihd =>
    -- m = n + (d' + 1), so m + 1 = n + d' + 2
    -- Normalize the arithmetic
    show Q pp a b (n + (d' + 1) + 1) n =
      pp.f (b (n + (d' + 1) + 1)) (pp.g (a (n + (d' + 1) + 1)) (Q pp a b (n + (d' + 1)) n))
    -- Unfold Q at the low end
    rw [Q_unfold pp a b (n + (d' + 1) + 1) n (by omega)]
    rw [Q_unfold pp a b (n + (d' + 1)) n (by omega)]
    -- LHS: f(Q(n+d'+2, n+1), g(H(n+1, n+d'+2), b n))
    -- RHS: f(b(n+d'+2), g(a(n+d'+2), f(Q(n+d'+1, n+1), g(H(n+1, n+d'+1), b n))))
    rw [pp.g_distrib, pp.g_semi_assoc, ← pp.f_assoc]
    -- Need: f(Q(n+d'+2, n+1), g(H(n+1, n+d'+2), b n))
    --     = f(f(b(n+d'+2), g(a(n+d'+2), Q(n+d'+1, n+1))),
    --        g(h(a(n+d'+2), H(n+1, n+d'+1)), b n))
    -- (1) Q(n+d'+2, n+1) = f(b(n+d'+2), g(a(n+d'+2), Q(n+d'+1, n+1)))
    --     This is IH at (n+1) since n+(d'+1) = (n+1)+d'
    have h1 : Q pp a b (n + (d' + 1) + 1) (n + 1) =
        pp.f (b (n + (d' + 1) + 1))
          (pp.g (a (n + (d' + 1) + 1)) (Q pp a b (n + (d' + 1)) (n + 1))) := by
      have heq1 : n + (d' + 1) = (n + 1) + d' := by omega
      conv_lhs => rw [show n + (d' + 1) + 1 = (n + 1) + d' + 1 from by omega]
                  rw [show n + 1 = n + 1 from rfl]
      conv_rhs => rw [show n + (d' + 1) + 1 = (n + 1) + d' + 1 from by omega]
                  rw [show n + (d' + 1) = (n + 1) + d' from by omega]
      exact ihd (n + 1)
    rw [h1]
    -- (2) H(n+1, n+d'+2) = h(a(n+d'+2), H(n+1, n+d'+1))
    congr 1
    rw [hProd_succ pp a (n + 1) (n + (d' + 1)) (by omega)]

theorem splitting_theorem (pp : ParallelPrefix α β) (a : Nat → β) (b : Nat → α)
    (m n j : Nat) (hn : n ≤ j) (hj : j < m) :
    Q pp a b m n = pp.f (Q pp a b m (j + 1))
      (pp.g (hProd pp a (j + 1) m) (Q pp a b j n)) := by
  -- Induction on the gap d = j - n
  obtain ⟨d, rfl⟩ : ∃ d, j = n + d := ⟨j - n, by omega⟩
  clear hn
  induction d generalizing n with
  | zero =>
    -- j = n + 0 = n
    simp only [Nat.add_zero]
    -- Q(m, n) = f(Q(m, n+1), g(H(n+1, m), Q(n, n)))
    rw [Q_base pp a b n n (Nat.le_refl n)]
    -- Q(m, n) = f(Q(m, n+1), g(H(n+1, m), b n))
    exact Q_unfold pp a b m n (by omega)
  | succ d' ihd =>
    -- j = n + (d' + 1), need:
    -- Q(m, n) = f(Q(m, n+d'+2), g(H(n+d'+2, m), Q(n+d'+1, n)))
    show Q pp a b m n = pp.f (Q pp a b m (n + (d' + 1) + 1))
      (pp.g (hProd pp a (n + (d' + 1) + 1) m) (Q pp a b (n + (d' + 1)) n))
    -- By IH with j = n + d': Q(m, n) = f(Q(m, n+d'+1), g(H(n+d'+1, m), Q(n+d', n)))
    have ih_applied : Q pp a b m n = pp.f (Q pp a b m (n + d' + 1))
        (pp.g (hProd pp a (n + d' + 1) m) (Q pp a b (n + d') n)) := by
      have : n + d' = n + d' := rfl
      exact ihd n (by omega)
    rw [ih_applied]
    -- Goal: f(Q(m, n+d'+1), g(H(n+d'+1, m), Q(n+d', n)))
    --     = f(Q(m, n+d'+2), g(H(n+d'+2, m), Q(n+d'+1, n)))
    -- Unfold Q(m, n+d'+1) using Q_unfold (since n+d'+1 < m iff n+d'+1 < m)
    -- Wait, is n+d'+1 < m? We have j = n+d'+1 < m, so yes.
    rw [Q_unfold pp a b m (n + d' + 1) (by omega)]
    -- LHS: f(f(Q(m, n+d'+2), g(H(n+d'+2, m), b(n+d'+1))), g(H(n+d'+1, m), Q(n+d', n)))
    rw [pp.f_assoc]
    -- LHS: f(Q(m, n+d'+2), f(g(H(n+d'+2, m), b(n+d'+1)), g(H(n+d'+1, m), Q(n+d', n))))
    congr 1
    -- Need: f(g(H(n+d'+2,m), b(n+d'+1)), g(H(n+d'+1,m), Q(n+d',n)))
    --     = g(H(n+d'+2,m), Q(n+d'+1, n))
    -- Normalize n + (d' + 1) to n + d' + 1 in the goal
    show pp.f (pp.g (hProd pp a (n + d' + 1 + 1) m) (b (n + d' + 1)))
        (pp.g (hProd pp a (n + d' + 1) m) (Q pp a b (n + d') n)) =
      pp.g (hProd pp a (n + d' + 1 + 1) m) (Q pp a b (n + d' + 1) n)
    -- Use Q_unfold_hi: Q(n+d'+1, n) = f(b(n+d'+1), g(a(n+d'+1), Q(n+d', n)))
    rw [Q_unfold_hi pp a b (n + d') n (by omega)]
    -- RHS: g(H(n+d'+2, m), f(b(n+d'+1), g(a(n+d'+1), Q(n+d', n))))
    rw [pp.g_distrib]
    -- RHS: f(g(H(n+d'+2,m), b(n+d'+1)), g(H(n+d'+2,m), g(a(n+d'+1), Q(n+d',n))))
    rw [pp.g_semi_assoc]
    -- RHS: f(g(H(n+d'+2,m), b(n+d'+1)), g(h(H(n+d'+2,m), a(n+d'+1)), Q(n+d',n)))
    congr 1
    -- Need: g(H(n+d'+1, m), Q(n+d', n)) = g(h(H(n+d'+2, m), a(n+d'+1)), Q(n+d', n))
    -- i.e., H(n+d'+1, m) = h(H(n+d'+2, m), a(n+d'+1))
    -- hProd_split: H(lo, hi) = h(H(mid+1, hi), H(lo, mid)) when lo ≤ mid < hi
    -- With lo = n+d'+1, mid = n+d'+1, hi = m:
    -- H(n+d'+1, m) = h(H(n+d'+2, m), H(n+d'+1, n+d'+1))
    rw [hProd_split pp a (n + d' + 1) (n + d' + 1) m (by omega) (by omega)]
    -- Now: g(h(H(n+d'+2,m), H(n+d'+1,n+d'+1)), Q(n+d',n))
    --    = g(h(H(n+d'+2,m), a(n+d'+1)), Q(n+d',n))
    rw [hProd_self pp a (n + d' + 1) (by omega)]

/-! ## T6: Solution correctness (Kogge-Stone Theorem 2) -/

/-- The recurrence solution: x_1 = b_1, x_i = f(b_i, g(a_i, x_{i-1})). -/
noncomputable def recurrenceSolution (pp : ParallelPrefix α β) (a : Nat → β) (b : Nat → α)
    : Nat → α
  | 0 => b 0
  | 1 => b 1
  | n + 2 => pp.f (b (n + 2)) (pp.g (a (n + 2)) (recurrenceSolution pp a b (n + 1)))

theorem solution_correct (pp : ParallelPrefix α β) (a : Nat → β) (b : Nat → α)
    (i : Nat) (hi : 1 ≤ i) :
    recurrenceSolution pp a b i = Q pp a b i 1 := by
  induction i with
  | zero => omega
  | succ n ihn =>
    cases n with
    | zero =>
      -- i = 1: recurrenceSolution gives b 1, Q(1,1) = b 1 by Q_base
      simp [recurrenceSolution, Q_base pp a b 1 1 (Nat.le_refl 1)]
    | succ m =>
      -- i = m + 2: unfold recurrenceSolution, apply IH, match Q_unfold_hi
      simp only [recurrenceSolution]
      rw [ihn (by omega)]
      rw [← Q_unfold_hi pp a b (m + 1) 1 (by omega)]

/-! ## D11: Algorithm A — parallel prefix iteration -/

/-- Algorithm A state after k steps for processor i.
    Returns (A^(k)(i), B^(k)(i)). -/
noncomputable def algorithmA (pp : ParallelPrefix α β) (a : Nat → β) (b : Nat → α)
    (k i : Nat) : β × α :=
  match k with
  | 0 => (a i, b i)
  | k' + 1 =>
    let prev_i := algorithmA pp a b k' i
    if i ≤ 2^k' then prev_i
    else
      let prev_shifted := algorithmA pp a b k' (i - 2^k')
      (pp.h prev_i.1 prev_shifted.1,
       pp.f prev_i.2 (pp.g prev_i.1 prev_shifted.2))

/-! ## T7: Algorithm A correctness (Kogge-Stone Theorem 3) -/

/-- Joint invariant: after k steps, algorithmA returns (hProd(lo,i), Q(i,lo))
    where lo = i - 2^k + 1 (in Nat, so lo = 1 when 2^k >= i). -/
theorem algorithmA_invariant (pp : ParallelPrefix α β) (a : Nat → β) (b : Nat → α)
    (k i : Nat) (hi : 1 ≤ i) :
    let lo := i - 2^k + 1
    (algorithmA pp a b k i).1 = hProd pp a lo i ∧
    (algorithmA pp a b k i).2 = Q pp a b i lo := by
  induction k generalizing i with
  | zero =>
    -- k = 0: lo = i - 1 + 1 = i, algorithmA returns (a i, b i)
    simp only [algorithmA, Nat.pow_zero]
    constructor
    · show a i = hProd pp a (i - 1 + 1) i
      rw [show i - 1 + 1 = i from by omega, hProd_self pp a i hi]
    · show b i = Q pp a b i (i - 1 + 1)
      rw [show i - 1 + 1 = i from by omega, Q_base pp a b i i (le_refl i)]
  | succ k' ih =>
    simp only [algorithmA]
    by_cases hle : i ≤ 2 ^ k'
    · -- Case: i ≤ 2^k', algorithmA returns prev_i unchanged
      simp only [hle, ↓reduceIte]
      have ih_i := ih i hi
      have ih1 : (algorithmA pp a b k' i).1 = hProd pp a (i - 2 ^ k' + 1) i := ih_i.1
      have ih2 : (algorithmA pp a b k' i).2 = Q pp a b i (i - 2 ^ k' + 1) := ih_i.2
      have hlo_old : i - 2 ^ k' + 1 = 1 := by omega
      have hlo_new : i - 2 ^ (k' + 1) + 1 = 1 := by
        have : 2 ^ k' ≤ 2 ^ (k' + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      rw [hlo_old] at ih1 ih2; rw [hlo_new]
      exact ⟨ih1, ih2⟩
    · -- Case: i > 2^k', algorithmA merges prev_i with prev_shifted
      simp only [hle, ↓reduceIte]
      push_neg at hle
      have hi_shifted : 1 ≤ i - 2 ^ k' := by omega
      have ihi := ih i hi
      have ihs := ih (i - 2 ^ k') hi_shifted
      have ih_i1 : (algorithmA pp a b k' i).1 = hProd pp a (i - 2 ^ k' + 1) i := ihi.1
      have ih_i2 : (algorithmA pp a b k' i).2 = Q pp a b i (i - 2 ^ k' + 1) := ihi.2
      have ih_s1 : (algorithmA pp a b k' (i - 2 ^ k')).1 =
          hProd pp a ((i - 2 ^ k') - 2 ^ k' + 1) (i - 2 ^ k') := ihs.1
      have ih_s2 : (algorithmA pp a b k' (i - 2 ^ k')).2 =
          Q pp a b (i - 2 ^ k') ((i - 2 ^ k') - 2 ^ k' + 1) := ihs.2
      have hlo_s_eq : (i - 2 ^ k') - 2 ^ k' + 1 = i - 2 ^ (k' + 1) + 1 := by
        have : 2 ^ (k' + 1) = 2 * 2 ^ k' := by ring
        omega
      rw [hlo_s_eq] at ih_s1 ih_s2
      have hpow : 2 ^ (k' + 1) = 2 * 2 ^ k' := by ring
      have hpow_pos : 0 < 2 ^ k' := Nat.pos_of_ne_zero (by positivity)
      have hlo_le_mid : i - 2 ^ (k' + 1) + 1 ≤ i - 2 ^ k' := by omega
      have hmid_lt_hi : i - 2 ^ k' < i := by omega
      constructor
      · -- .1: h(hProd(lo_i, i), hProd(lo_new, i-2^k')) = hProd(lo_new, i)
        rw [ih_i1, ih_s1]
        rw [hProd_split pp a (i - 2 ^ (k' + 1) + 1) (i - 2 ^ k') i hlo_le_mid hmid_lt_hi]
      · -- .2: f(Q(i, lo_i), g(hProd(lo_i, i), Q(i-2^k', lo_new))) = Q(i, lo_new)
        rw [ih_i2, ih_i1, ih_s2]
        symm
        conv_rhs => rw [show i - 2 ^ k' + 1 = (i - 2 ^ k') + 1 from by omega]
        exact splitting_theorem pp a b i (i - 2 ^ (k' + 1) + 1) (i - 2 ^ k')
          hlo_le_mid hmid_lt_hi

theorem algorithmA_correct (pp : ParallelPrefix α β) (a : Nat → β) (b : Nat → α)
    (k i : Nat) (hi : 1 ≤ i) (hk : 2^k ≥ i) :
    (algorithmA pp a b k i).2 = Q pp a b i 1 := by
  have inv := (algorithmA_invariant pp a b k i hi).2
  simp only at inv
  have hlo : i - 2 ^ k + 1 = 1 := by omega
  rwa [hlo] at inv

/-! ## T8: Carry-pair operator instantiates the framework -/

/-- cpOp satisfies all Kogge-Stone restrictions (f = g = h = cpOp). -/
def carryPairPP : ParallelPrefix CarryPair CarryPair where
  f := cpOp
  g := cpOp
  h := cpOp
  f_assoc := cpOp_assoc
  g_distrib := by
    intro a x y
    obtain ⟨ga, pa⟩ := a; obtain ⟨gx, px⟩ := x; obtain ⟨gy, py⟩ := y
    simp only [cpOp, Prod.mk.injEq]
    constructor <;> cases ga <;> cases pa <;> cases gx <;> cases px <;> cases gy <;> cases py <;> rfl
  g_semi_assoc := fun a b x => (cpOp_assoc a b x).symm
  h_assoc := cpOp_assoc

end BinaryAddition
