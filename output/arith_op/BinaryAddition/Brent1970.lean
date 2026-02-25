/-
  BinaryAddition/Brent1970.lean — Brent 1970 complexity theorems

  Formalizes results from "On the Addition of Binary Numbers" (Brent 1970):
  - D12: Group propagate/generate definitions
  - T9: Carry group decomposition (Lemma 1)
  - D13: Circuit depth function model
  - T10-T12: Complexity bounds (Lemmas 2-3, Theorem 1)

  Note: Brent 1970 uses x_i = a_i ∨ b_i (propagate), y_i = a_i ∧ b_i (generate).
-/
import BinaryAddition.Defs
import BinaryAddition.BrentKung
import Mathlib.Tactic
import Mathlib.Data.Nat.Log

namespace BinaryAddition

/-! ## D12: Group propagate and group generate -/

/-- Group propagate: AND of propagate bits in range [lo, hi). -/
def groupPropagate (lo hi : Nat) (x y : BitVec w) : Bool :=
  (blockGP_range lo hi x y).propagate

/-- Group generate: carry generated within [lo, hi) with carry-in = 0.
    Equals the first component of blockGP_range. -/
def groupGenerate (lo hi : Nat) (x y : BitVec w) : Bool :=
  (blockGP_range lo hi x y).generate

/-! ## T9: Carry group decomposition (Brent 1970, Lemma 1)

    The carry at position hi+1 decomposes as:
    c_{hi+1} = G_{[lo,hi+1)} ∨ (P_{[lo,hi+1)} ∧ c_lo)

    This is carry_decompose from BrentKung, restated with group terminology. -/

theorem carry_group_decomposition (lo hi : Nat) (hlo : lo ≤ hi) (x y : BitVec w) :
    BitVec.carry (hi + 1) x y false =
      (groupGenerate lo (hi + 1) x y ||
       (groupPropagate lo (hi + 1) x y && BitVec.carry lo x y false)) := by
  exact carry_decompose lo hi hlo x y

/-! ## D13: Circuit depth model

    We define a concrete circuit model: a BoolCircuit is a DAG of AND/OR/XOR/NOT gates
    with bounded fan-in r. The depth is the longest path from any input to an output. -/

/-- A circuit gate type. -/
inductive GateOp where
  | and | or | xor | not
  deriving DecidableEq

/-- A circuit is a list of gates, each referencing inputs by index.
    Gate i can reference any input or gate j < i. -/
structure BoolCircuit (numInputs : Nat) where
  /-- Number of gates -/
  numGates : Nat
  /-- Each gate's operation -/
  ops : Fin numGates → GateOp
  /-- Each gate's input indices (into inputs ++ previous gates) -/
  inputs : Fin numGates → List (Fin (numInputs + numGates))
  /-- Fan-in bound -/
  fanIn : Nat
  /-- All gates respect fan-in -/
  fanIn_bound : ∀ g, (inputs g).length ≤ fanIn

/-- Depth of a node in the circuit.
    Computing this requires the circuit to be acyclic (gates only reference earlier indices).
    We constrain: gate i can only reference inputs or gates j with j < numInputs + i. -/
structure AcyclicCircuit (numInputs : Nat) extends BoolCircuit numInputs where
  /-- Acyclicity: each gate references only earlier nodes -/
  acyclic : ∀ (g : Fin numGates) (inp : Fin (numInputs + numGates)),
    inp ∈ inputs g → inp.val < numInputs + g.val

/-! ## Complexity bounds using DepthBound abstraction

    Rather than proving bounds for the concrete circuit model (which requires
    constructing explicit circuits), we use an abstract depth function satisfying
    the grouping recurrence. This captures any circuit family achieving the bound. -/

/-- L(x) = ⌈log_r x⌉, the depth of a balanced tree with x leaves. -/
noncomputable def L (r : Nat) (x : Nat) : Nat := Nat.clog r x

/-- A depth function for carry computation with fan-in r. -/
structure DepthBound (r : Nat) where
  t : Nat → Nat
  base : t 1 = 1
  monotone : ∀ m n, m ≤ n → t m ≤ t n
  recurrence : ∀ p q, 2 ≤ p → 1 ≤ q →
    t (p * q) ≤ 1 + L r p + max (t q) (L r q + L r (p - 1))

/-! ## T10: Time recurrence (Brent 1970, Lemma 2) -/

noncomputable def Tstep (db : DepthBound r) (x : Nat) : Nat :=
  db.t (r ^ x) - x

-- T_step_bound: T(a + k·T(a) + k(k-1)/2) ≤ k + T(a)
-- Proof requires careful Nat arithmetic with the recurrence.
-- Deferred: the key difficulty is relating r^(complex exponent) to the recurrence.

/-! ### Arithmetic helpers for triangular number identities

    These handle nonlinear Nat arithmetic (products of variables) which omega cannot solve.
    Key identities: k + k*(k-1)/2 = (k+1)*k/2 and 1 + k + k*(k+1)/2 = (k+1)*(k+2)/2. -/

private lemma two_dvd_mul_succ (n : Nat) : 2 ∣ (n + 1) * n := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact ⟨(n+1) * m, by nlinarith⟩
  · exact ⟨(m+1) * n, by nlinarith⟩

/-- k + k*(k-1)/2 = (k+1)*k/2: the exponent step for the induction. -/
private lemma tri_exponent_step (k : Nat) (hk : 1 ≤ k) :
    k + k * (k - 1) / 2 = (k + 1) * k / 2 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simp
  have hd := two_dvd_mul_succ n
  obtain ⟨m, hm⟩ := hd
  have hm' : (n+2)*(n+1) = 2*(m + (n+1)) := by nlinarith
  rw [hm, hm']
  simp
  omega

/-- 1 + k + k*(k+1)/2 = (k+1)*(k+2)/2: the bound step for the induction. -/
private lemma tri_bound_step (k : Nat) :
    1 + k + k * (k + 1) / 2 = (k + 1) * (k + 2) / 2 := by
  have hd : 2 ∣ k * (k + 1) := by
    rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact ⟨m * (k+1), by nlinarith⟩
    · exact ⟨k * (m+1), by nlinarith⟩
  obtain ⟨m, hm⟩ := hd
  have : (k+1)*(k+2) = 2*(m + k + 1) := by nlinarith
  rw [hm, this]
  simp
  omega

/-- n*(n-1)/2 + n = n*(n+1)/2: rearrangement for bounding the second branch. -/
private lemma tri_sum_step (n : Nat) (hn : 1 ≤ n) :
    n * (n - 1) / 2 + n = n * (n + 1) / 2 := by
  have hd : 2 ∣ n * (n - 1) := by
    cases n with
    | zero => simp
    | succ m => simpa using two_dvd_mul_succ m
  obtain ⟨m, hm⟩ := hd
  have h1 : n * (n + 1) = 2 * (m + n) := by
    have h2 : n + 1 = (n - 1) + 2 := by omega
    rw [h2, Nat.mul_add]; ring_nf; linarith
  rw [hm, h1]
  simp

private lemma clog_pow_pred_le (r k : Nat) (_ : 2 ≤ r) (_ : 1 ≤ k) :
    Nat.clog r (r ^ k - 1) ≤ k :=
  Nat.clog_le_of_le_pow (Nat.sub_le _ _)

/-! ## T12: Finite upper bound (Brent 1970, Theorem 1)

    t(r^(k(k-1)/2)) ≤ k(k+1)/2 for k ≥ 1.

    Proof by induction on k. Base: t(1) = 1. Step: apply the grouping recurrence
    with p = r^k, q = r^(k*(k-1)/2), using clog(r^k) = k and the IH. -/

theorem finite_upper_bound (hr : 2 ≤ r) (db : DepthBound r) (k : Nat) (hk : 1 ≤ k) :
    db.t (r ^ (k * (k - 1) / 2)) ≤ k * (k + 1) / 2 := by
  induction k with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 0
    · subst hn; simp [db.base]
    · have hn1 : 1 ≤ n := by omega
      have ih' := ih hn1
      have hr1 : 1 < r := by omega
      -- Exponent identity: r^n * r^(n*(n-1)/2) = r^((n+1)*n/2)
      have hexp : n + n * (n - 1) / 2 = (n + 1) * n / 2 :=
        tri_exponent_step n hn1
      have hpq : r ^ n * r ^ (n * (n - 1) / 2) = r ^ ((n + 1) * n / 2) := by
        rw [← Nat.pow_add, hexp]
      -- Preconditions for recurrence: p = r^n ≥ 2, q = r^(n*(n-1)/2) ≥ 1
      have hp : 2 ≤ r ^ n :=
        calc 2 ≤ r := hr
             _ = r ^ 1 := (Nat.pow_one r).symm
             _ ≤ r ^ n := Nat.pow_le_pow_right (by omega) hn1
      have hq : 1 ≤ r ^ (n * (n - 1) / 2) := Nat.one_le_pow _ _ (by omega)
      -- Apply the grouping recurrence
      have hrec := db.recurrence (r ^ n) (r ^ (n * (n - 1) / 2)) hp hq
      rw [hpq] at hrec
      -- Evaluate ceiling logs: L(r, r^n) = n, L(r, r^(n*(n-1)/2)) ≤ n*(n-1)/2
      have hLp : L r (r ^ n) = n := by simp [L, Nat.clog_pow _ _ hr1]
      have hLq : L r (r ^ (n * (n - 1) / 2)) ≤ n * (n - 1) / 2 := by
        simp [L, Nat.clog_pow _ _ hr1]
      have hLpred : L r (r ^ n - 1) ≤ n := clog_pow_pred_le r n hr hn1
      -- Bound the max of the two branches
      have hbranch2 : L r (r ^ (n * (n - 1) / 2)) + L r (r ^ n - 1) ≤ n * (n + 1) / 2 :=
        calc L r (r ^ (n * (n - 1) / 2)) + L r (r ^ n - 1)
            ≤ n * (n - 1) / 2 + n := Nat.add_le_add hLq hLpred
          _ = n * (n + 1) / 2 := tri_sum_step n hn1
      have hmax : max (db.t (r ^ (n * (n - 1) / 2)))
            (L r (r ^ (n * (n - 1) / 2)) + L r (r ^ n - 1))
          ≤ n * (n + 1) / 2 := max_le ih' hbranch2
      -- Combine: 1 + n + n*(n+1)/2 = (n+1)*(n+2)/2
      calc db.t (r ^ ((n + 1) * n / 2))
          ≤ 1 + L r (r ^ n) + max (db.t (r ^ (n * (n - 1) / 2)))
              (L r (r ^ (n * (n - 1) / 2)) + L r (r ^ n - 1)) := hrec
        _ ≤ 1 + n + n * (n + 1) / 2 := by
            rw [hLp]; exact Nat.add_le_add_left hmax (1 + n)
        _ = (n + 1) * (n + 2) / 2 := tri_bound_step n

/-! ## T13: Asymptotic bound (Brent 1970, Theorem 2)

    For any ε > 0, t(n) ≤ (1+ε) ⌈log_r n⌉ for sufficiently large n.

    Proof outline:
    1. From T12: t(r^(k(k-1)/2)) ≤ k(k+1)/2 for all k ≥ 1.
    2. For n, let L = ⌈log_r n⌉ so n ≤ r^L.
    3. Find k ≥ 2 with (k-1)(k-2)/2 < L ≤ k(k-1)/2 (triangular enclosure).
    4. Then t(n) ≤ t(r^L) ≤ t(r^(k(k-1)/2)) ≤ k(k+1)/2.
    5. For large k: k(k+1) ≤ (1+ε)(k-1)(k-2), so k(k+1)/2 ≤ (1+ε)·L. -/

/-- Triangular numbers cover all positive naturals:
    for L ≥ 1, ∃ k ≥ 2 with T(k-1) < L ≤ T(k) where T(k) = k(k-1)/2. -/
private lemma tri_enclosure (L : ℕ) (hL : 1 ≤ L) :
    ∃ k : ℕ, 2 ≤ k ∧ (k - 1) * (k - 2) / 2 < L ∧ L ≤ k * (k - 1) / 2 := by
  -- Use well-ordering: find the minimal k ≥ 2 with L ≤ k*(k-1)/2
  -- First show L+1 is in the set (so the set is nonempty)
  have h_exists : ∃ k, 2 ≤ k ∧ L ≤ k * (k - 1) / 2 := by
    refine ⟨L + 1, by omega, ?_⟩
    show L ≤ (L + 1) * (L + 1 - 1) / 2
    simp only [Nat.add_sub_cancel]
    have h2L : 2 * L ≤ (L + 1) * L := by nlinarith
    omega
  -- Use Nat.find on a decidable predicate
  let P : ℕ → Prop := fun k => 2 ≤ k ∧ L ≤ k * (k - 1) / 2
  have hP_exists : ∃ k, P k := h_exists
  set k₀ := Nat.find hP_exists with hk₀_def
  have hk₀_spec : P k₀ := Nat.find_spec hP_exists
  have hk₀_min : ∀ m, m < k₀ → ¬P m := fun m hm => Nat.find_min hP_exists hm
  refine ⟨k₀, hk₀_spec.1, ?_, hk₀_spec.2⟩
  -- Show (k₀ - 1) * (k₀ - 2) / 2 < L by minimality
  by_contra h_not_lt
  push_neg at h_not_lt
  -- So L ≤ (k₀ - 1) * (k₀ - 2) / 2
  have hk₀_ge2 := hk₀_spec.1
  -- If k₀ = 2, then (k₀-1)*(k₀-2)/2 = 0, contradicting L ≥ 1
  by_cases hk₀2 : k₀ = 2
  · simp only [hk₀2] at h_not_lt; omega
  · -- k₀ ≥ 3, so k₀ - 1 ≥ 2 and k₀ - 1 is in P, contradicting minimality
    have hP_pred : P (k₀ - 1) := ⟨by omega, h_not_lt⟩
    exact hk₀_min (k₀ - 1) (by omega) hP_pred

/-- For large k, the ratio k(k+1)/((k-1)(k-2)) is close to 1:
    for any ε > 0, ∃ k₀ s.t. k ≥ k₀ → k(k+1) ≤ (1+ε)(k-1)(k-2) in ℝ. -/
private lemma ratio_bound_eventually (ε : ℝ) (hε : 0 < ε) :
    ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      (k * (k + 1) : ℝ) ≤ (1 + ε) * (((k : ℝ) - 1) * ((k : ℝ) - 2)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / ε + 3)
  refine ⟨max 3 N, le_max_left _ _, ?_⟩
  intro k hk
  have hk3 : 3 ≤ k := le_trans (le_max_left 3 N) hk
  have hkN : N ≤ k := le_trans (le_max_right 3 N) hk
  have hkN_r : (N : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hkN
  have hk_large : 4 / ε + 3 < (k : ℝ) := lt_of_lt_of_le hN hkN_r
  have hk3r : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk3
  have hkm1_pos : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hkm2_pos : (0 : ℝ) < (k : ℝ) - 2 := by linarith
  -- From k > 4/ε + 3: ε*(k-3) > 4
  have hεkm3 : ε * ((k : ℝ) - 3) > 4 := by
    have h1 : ε * (4 / ε + 3) < ε * (k : ℝ) := by nlinarith
    rw [mul_add, mul_div_cancel₀ _ (ne_of_gt hε)] at h1
    linarith
  -- ε*k*(k-3) ≥ 4*k
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have key : ε * ((k : ℝ) - 3) * (k : ℝ) ≥ 4 * (k : ℝ) :=
    mul_le_mul_of_nonneg_right (le_of_lt hεkm3) (le_of_lt hk_pos)
  -- 4k-2 ≤ ε(k²-3k+2) since ε(k²-3k+2) = ε*k*(k-3) + 2ε ≥ 4k + 2ε > 4k-2
  nlinarith [mul_pos hkm1_pos hkm2_pos]

/-- Monotonicity of triangular numbers: k ≥ j → T(k) ≥ T(j). -/
private lemma tri_mono {j k : ℕ} (hjk : j ≤ k) : j * (j - 1) / 2 ≤ k * (k - 1) / 2 :=
  Nat.div_le_div_right (Nat.mul_le_mul hjk (Nat.sub_le_sub_right hjk 1))

/-- Nat.cast preserves exact division for consecutive products. -/
private lemma cast_tri_div (k : ℕ) (hk : 2 ≤ k) :
    ((k * (k - 1) / 2 : ℕ) : ℝ) = ((k : ℝ) * ((k : ℝ) - 1)) / 2 := by
  have hdvd : (2 : ℕ) ∣ k * (k - 1) := by
    have h := two_dvd_mul_succ (k - 1)
    rwa [show k - 1 + 1 = k from by omega] at h
  rw [Nat.cast_div hdvd (by norm_num : (2 : ℝ) ≠ 0),
      Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ k)]
  norm_num

/-- T13: Asymptotic bound (Brent 1970, Theorem 2).
    For any ε > 0, t(n) ≤ (1+ε) ⌈log_r n⌉ for sufficiently large n. -/
theorem asymptotic_bound (hr : 2 ≤ r) (db : DepthBound r) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, (db.t n : ℝ) ≤ (1 + ε) * (Nat.clog r n : ℝ) := by
  -- Get k₀ from ratio bound
  obtain ⟨k₀, hk₀_ge, hk₀_ratio⟩ := ratio_bound_eventually ε hε
  -- Threshold: N = r^(k₀*(k₀-1)/2)
  rw [Filter.eventually_atTop]
  refine ⟨r ^ (k₀ * (k₀ - 1) / 2) + 1, ?_⟩
  intro n hn
  -- Let L = ⌈log_r n⌉
  set L := Nat.clog r n with hL_def
  -- n ≥ 2 (since n ≥ r^(...) + 1 ≥ 2)
  have hr1 : 1 < r := by omega
  have hn2 : 2 ≤ n := by
    have : 1 ≤ r ^ (k₀ * (k₀ - 1) / 2) := Nat.one_le_pow _ _ (by omega)
    omega
  -- L ≥ 1
  have hL_pos : 1 ≤ L := Nat.clog_pos hr1 (by omega)
  -- L > k₀*(k₀-1)/2: since n > r^(k₀*(k₀-1)/2)
  have hL_gt : k₀ * (k₀ - 1) / 2 < L := by
    rw [hL_def]
    exact (Nat.lt_clog_iff_pow_lt hr1).mpr (by omega)
  -- Use tri_enclosure to get k ≥ 2 with (k-1)*(k-2)/2 < L ≤ k*(k-1)/2
  obtain ⟨k, hk2, hk_lo, hk_hi⟩ := tri_enclosure L hL_pos
  -- k ≥ k₀: if k < k₀ then k ≤ k₀-1, T(k) ≤ T(k₀-1) = (k₀-1)*(k₀-2)/2 < k₀*(k₀-1)/2 < L ≤ T(k)
  have hk_ge_k0 : k₀ ≤ k := by
    -- We have k₀*(k₀-1)/2 < L ≤ k*(k-1)/2.
    -- If k < k₀ then k ≤ k₀-1, and tri_mono gives k*(k-1)/2 ≤ (k₀-1)*(k₀-2)/2.
    -- But (k₀-1)*(k₀-2)/2 < k₀*(k₀-1)/2 for k₀ ≥ 3, contradiction.
    by_contra h_lt
    push_neg at h_lt
    have hTk : k * (k - 1) / 2 ≤ (k₀ - 1) * ((k₀ - 1) - 1) / 2 := tri_mono (by omega)
    -- Show (k₀-1)*((k₀-1)-1) < k₀*(k₀-1) (since (k₀-1)-1 < k₀ and k₀-1 > 0)
    have hprod_lt : (k₀ - 1) * ((k₀ - 1) - 1) < k₀ * (k₀ - 1) := by
      rw [Nat.mul_comm (k₀ - 1) ((k₀ - 1) - 1)]
      exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    -- Both products divisible by 2, so a/2 < b/2
    have hd1 : 2 ∣ (k₀ - 1) * ((k₀ - 1) - 1) := by
      have := two_dvd_mul_succ ((k₀ - 1) - 1)
      rwa [show (k₀ - 1) - 1 + 1 = k₀ - 1 from by omega] at this
    have hd2 : 2 ∣ k₀ * (k₀ - 1) := by
      have := two_dvd_mul_succ (k₀ - 1)
      rwa [show k₀ - 1 + 1 = k₀ from by omega] at this
    obtain ⟨a, ha⟩ := hd1; obtain ⟨b, hb⟩ := hd2
    rw [ha, Nat.mul_div_cancel_left _ (by omega : 0 < 2)] at hTk
    rw [hb, Nat.mul_div_cancel_left _ (by omega : 0 < 2)] at hL_gt
    -- hTk: k*(k-1)/2 ≤ a, hL_gt: b < L, hk_hi: L ≤ k*(k-1)/2
    -- hprod_lt: 2*a < 2*b, so a < b
    -- Chain: b < L ≤ k*(k-1)/2 ≤ a, but a < b, contradiction
    omega
  -- k ≥ 1 (since k ≥ 2)
  have hk1 : 1 ≤ k := by omega
  -- Chain: n ≤ r^L ≤ r^(k*(k-1)/2), so t(n) ≤ t(r^(k*(k-1)/2)) ≤ k*(k+1)/2
  have hn_le_rL : n ≤ r ^ L := Nat.le_pow_clog hr1 n
  have hrL_le : r ^ L ≤ r ^ (k * (k - 1) / 2) :=
    Nat.pow_le_pow_right (by omega) hk_hi
  have ht_bound : db.t n ≤ db.t (r ^ (k * (k - 1) / 2)) :=
    db.monotone n _ (le_trans hn_le_rL hrL_le)
  have hfub := finite_upper_bound hr db k hk1
  have ht_le : db.t n ≤ k * (k + 1) / 2 := le_trans ht_bound hfub
  -- Cast to ℝ
  have ht_le_R : (db.t n : ℝ) ≤ ((k * (k + 1) / 2 : ℕ) : ℝ) := Nat.cast_le.mpr ht_le
  -- k*(k+1)/2 = (k+1)*((k+1)-1)/2, use cast_tri_div (k+1)
  have hkk1_div_eq : k * (k + 1) / 2 = (k + 1) * ((k + 1) - 1) / 2 := by
    have : (k + 1) - 1 = k := by omega
    rw [this, Nat.mul_comm]
  have hcast_kk1 : ((k * (k + 1) / 2 : ℕ) : ℝ) = (k : ℝ) * ((k : ℝ) + 1) / 2 := by
    rw [hkk1_div_eq, cast_tri_div (k + 1) (by omega)]
    push_cast; ring
  -- ratio bound: k*(k+1) ≤ (1+ε)*(k-1)*(k-2) in ℝ, so k*(k+1)/2 ≤ (1+ε)*(k-1)*(k-2)/2
  have hk_ratio := hk₀_ratio k hk_ge_k0
  have hkk1_le_eps : (k : ℝ) * ((k : ℝ) + 1) / 2 ≤
      (1 + ε) * (((k : ℝ) - 1) * ((k : ℝ) - 2)) / 2 := by
    exact div_le_div_of_nonneg_right hk_ratio (by positivity)
  -- (k-1)*(k-2)/2 < L in ℕ → ((k-1)*(k-2)/2 : ℝ) < (L : ℝ)
  -- Cast (k-1)*(k-2)/2 using cast_tri_div (k-1) (need k-1 ≥ 2, i.e. k ≥ 3)
  have hk3 : 3 ≤ k := by omega
  have hkm1_simp : (k - 1) * ((k - 1) - 1) = (k - 1) * (k - 2) := by
    have : (k - 1) - 1 = k - 2 := by omega
    rw [this]
  have hcast_km1' : (((k - 1) * (k - 2) / 2 : ℕ) : ℝ) =
      ((k : ℝ) - 1) * ((k : ℝ) - 2) / 2 := by
    have hsub : (k - 1) * (k - 2) = (k - 1) * ((k - 1) - 1) := by congr 1
    rw [hsub, cast_tri_div (k - 1) (by omega)]
    simp only [Nat.cast_sub (show 1 ≤ k by omega)]
    ring
  -- (1+ε) * ((k-1)*(k-2)/2 : ℝ) < (1+ε) * (L : ℝ) since (k-1)*(k-2)/2 < L
  have heps_pos : (0 : ℝ) < 1 + ε := by linarith
  have hk_lo_R : (((k - 1) * (k - 2) / 2 : ℕ) : ℝ) < (L : ℝ) := Nat.cast_lt.mpr hk_lo
  calc (db.t n : ℝ)
      ≤ ((k * (k + 1) / 2 : ℕ) : ℝ) := ht_le_R
    _ = (k : ℝ) * ((k : ℝ) + 1) / 2 := hcast_kk1
    _ ≤ (1 + ε) * (((k : ℝ) - 1) * ((k : ℝ) - 2)) / 2 := hkk1_le_eps
    _ = (1 + ε) * (((k : ℝ) - 1) * ((k : ℝ) - 2) / 2) := by ring
    _ = (1 + ε) * (((k - 1) * (k - 2) / 2 : ℕ) : ℝ) := by rw [hcast_km1']
    _ ≤ (1 + ε) * (L : ℝ) := by
        exact mul_le_mul_of_nonneg_left (le_of_lt hk_lo_R) heps_pos.le
    _ = (1 + ε) * (Nat.clog r n : ℝ) := by rw [hL_def]

end BinaryAddition
