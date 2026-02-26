# Binary Addition Formalization — Pedagogical Guide

Lean 4 formalization of foundational results from three papers on binary addition and parallel prefix computation:

1. **Brent 1970** — "On the Addition of Binary Numbers" (complexity bounds)
2. **Kogge & Stone 1973** — "A Parallel Algorithm for the Efficient Solution of a General Class of Recurrence Equations" (general framework)
3. **Brent & Kung 1982** — "A Regular Layout for Parallel Adders" (carry-pair operator, VLSI layout)

## Connection to Lean stdlib

The key insight: Lean's stdlib already defines `BitVec.carry` (the carry bit at each position) and proves its recurrence via `carry_succ` using `Bool.atLeastTwo`. Our formalization shows this is equivalent to a parallel prefix computation over carry pairs.

### What we reuse from stdlib (`Init.Data.BitVec.Bitblast`):
- `BitVec.carry i x y c` — carry at position i
- `carry_zero` / `carry_succ` — carry recurrence
- `getLsbD_add` — sum bit in terms of XOR and carry
- `Bool.atLeastTwo a b c = a && b || a && c || b && c`

### What we reuse from Mathlib:
- `Nat.clog` — ceiling log for complexity bounds
- `Mathlib.Tactic` — `omega`, `simp`, etc.

---

## File: `BinaryAddition/Defs.lean` — Shared Definitions

### D1: Generate bit
```lean
def generate (i : Nat) (x y : BitVec w) : Bool :=
  x.getLsbD i && y.getLsbD i
```
**Paper reference**: Brent-Kung §2, `g_i = a_i ∧ b_i`. A carry is *generated* at position i when both input bits are 1.

### D2: Propagate bit
```lean
def propagate (i : Nat) (x y : BitVec w) : Bool :=
  x.getLsbD i ^^ y.getLsbD i
```
**Paper reference**: Brent-Kung §2, `p_i = a_i ⊕ b_i`. A carry is *propagated* through position i when exactly one input bit is 1.

**Note**: Brent 1970 defines propagate as OR (`a_i ∨ b_i`) rather than XOR. The XOR definition (Brent-Kung) is standard in modern texts because it also gives the sum bit directly: `s_i = p_i ⊕ c_{i-1}`.

### D3: GenPropPair
```lean
@[ext] structure GenPropPair where
  generate  : Bool
  propagate : Bool
```
A pair where `generate` = "block generates a carry" and `propagate` = "block propagates a carry".

### D4: The ∘ operator (`gpOp`)
```lean
def gpOp (a b : GenPropPair) : GenPropPair :=
  ⟨a.generate || (a.propagate && b.generate), a.propagate && b.propagate⟩

scoped infixl:70 " ∘ " => gpOp
```
**Paper reference**: Brent-Kung §3, p.261. The carry-pair composition operator:
```
(g, p) ∘ (g', p') = (g ∨ (p ∧ g'), p ∧ p')
```
Intuitively: a combined block generates a carry if either the upper block generates, or the upper block propagates and the lower block generates. The combined block propagates only if both blocks propagate.

### D5: Block generate/propagate (`blockGP`)
```lean
def blockGP (i : Nat) (x y : BitVec w) : GenPropPair :=
  match i with
  | 0 => ⟨false, true⟩
  | n + 1 => ⟨generate n x y, propagate n x y⟩ ∘ blockGP n x y
```
**Paper reference**: Brent-Kung Lemma 1. The prefix fold: `(G_i, P_i) = (g_i, p_i) ∘ (g_{i-1}, p_{i-1}) ∘ ... ∘ (g_1, p_1)`.

**Indexing convention**: We use 0-indexed bits. `blockGP i` covers bits `[0, i)`. The identity `⟨false, true⟩` at position 0 means "no carry generated, carry propagated" — matching `carry 0 x y false = false`.

### Bridge lemma: `atLeastTwo_eq_gp`
```lean
theorem atLeastTwo_eq_gp (a b c : Bool) :
    Bool.atLeastTwo a b c = ((a && b) || ((a ^^ b) && c)) := by
  cases a <;> cases b <;> cases c <;> rfl
```
**Why this matters**: stdlib defines `carry (i+1) = atLeastTwo x[i] y[i] (carry i)`, which expands to `x[i]&&y[i] || x[i]&&c || y[i]&&c`. Our generate/propagate formulation uses `g || (p && c)` where `g = x&&y` and `p = x^^y`. This lemma proves they're equal, bridging stdlib to the parallel prefix world.

---

## File: `BinaryAddition/ParallelAdders.lean` — Parallel Adder Equations & Theorems

### T1: `gpOp_assoc` — Associativity (Brent-Kung Lemma 2)
```lean
theorem gpOp_assoc (a b c : GenPropPair) :
    (a ∘ b) ∘ c = a ∘ (b ∘ c)
```
**Paper reference**: Brent-Kung §3, p.262.

**Why it matters**: Associativity is THE key property. It means we can compute `(g_n, p_n) ∘ ... ∘ (g_1, p_1)` in any order — enabling a balanced binary tree (parallel prefix) instead of a linear chain (ripple carry).

**Proof**: Destructure all three pairs into 6 Bools, then exhaustive case-split (64 cases, all closed by `rfl`).

### T2: `carry_eq_blockGenerate` — Carry = Block Generate (Brent-Kung Lemma 1)
```lean
theorem carry_eq_blockGenerate (i : Nat) (x y : BitVec w) :
    BitVec.carry i x y false = (blockGP i x y).generate
```
**Paper reference**: Brent-Kung Lemma 1, p.261.

**This is the central theorem**: it connects stdlib's `BitVec.carry` (defined semantically via `decide (... ≥ 2^i)`) to the algebraic carry-pair formulation. Once proven, all carry computation can be done via prefix scans of `∘`.

**Proof strategy**: Induction on `i`.
- Base (`i=0`): `carry 0 x y false = false` by `carry_zero`, and `(blockGP 0).generate = false` by definition.
- Step (`i=n+1`): `carry (n+1) = atLeastTwo x[n] y[n] (carry n)` by `carry_succ`. Apply `atLeastTwo_eq_gp` to get `generate n || (propagate n && carry n)`. By IH, replace `carry n` with `(blockGP n).generate`. This equals `(⟨g_n, p_n⟩ ∘ blockGP n).generate = (blockGP (n+1)).generate`.

### T3: `sum_eq_propagate_xor_carry`
```lean
theorem sum_eq_propagate_xor_carry {w : Nat} (i : Nat) (hi : i < w) (x y : BitVec w) :
    (x + y).getLsbD i = (propagate i x y ^^ BitVec.carry i x y false)
```
**Paper reference**: Brent-Kung §2, `s_i = p_i ⊕ c_{i-1}`.

**Proof**: Direct from stdlib's `getLsbD_add`: the sum bit at position i is `x[i] ^^ y[i] ^^ carry_i`. Since `propagate i = x[i] ^^ y[i]`, this is `propagate i ^^ carry_i`.

### T4: `blockGP_split` — Splitting at any point
```lean
theorem blockGP_split (i j : Nat) (hj : j ≤ i) (x y : BitVec w) :
    blockGP i x y = (blockGP_range j i x y) ∘ (blockGP j x y)
```
**Why it matters**: This is the structural lemma for divide-and-conquer. To compute all carries for an n-bit addition, split the prefix computation at any point. Combined with `gpOp_assoc`, this enables:
- Brent-Kung tree (O(n) gates, O(log n) depth)
- Kogge-Stone tree (O(n log n) gates, O(log n) depth)
- Hybrid architectures

---

## File: `BinaryAddition/GeneralizedRecurrenceEquations.lean` — General Framework

### D6-D9: `ParallelPrefix` structure
```lean
structure ParallelPrefix (α β : Type*) where
  f : α → α → α           -- combines partial results
  g : β → α → α           -- applies coefficient to result
  h : β → β → β           -- composes coefficients
  f_assoc : ...            -- Restriction 1
  g_distrib : ...          -- Restriction 2
  g_semi_assoc : ...       -- Restriction 3
```
**Paper reference**: Kogge-Stone §3, Restrictions 1-3.

The framework captures any first-order recurrence `x_i = f(b_i, g(a_i, x_{i-1}))` that can be solved in O(log N) parallel steps, provided f, g, h satisfy three algebraic restrictions.

### Applications (from Kogge-Stone Table II):
| Recurrence | f | g | h |
|-----------|---|---|---|
| Linear: x_i = a_i·x_{i-1} + b_i | + | × | × |
| Carry computation | ∘ | ∘ | ∘ |
| Minimum of N numbers | min | min | min |
| Polynomial evaluation | + | × | × |

### T5: `splitting_theorem` — The Splitting Theorem (Theorem 1)
Allows splitting Q(m,n) at any intermediate point j, enabling recursive doubling.

### T6: `solution_correct` — Q(i,1) = x_i (Theorem 2)
Proves the generalized composition equals the recurrence solution.

### T7: `algorithmA_correct` — Algorithm A converges in ⌈log₂ N⌉ steps (Theorem 3)
After enough doubling steps, each processor has the full solution.

### T8: `genPropPP` — Carry pairs instantiate the framework
Shows that `(GenPropPair, ∘, ∘, ∘)` satisfies all four Kogge-Stone restrictions. Notably, `∘` IS left-distributive over itself (Restriction 2), proven by exhaustive Bool case-split (64 cases). This was initially suspected to be false but turns out to hold.

---

## File: `BinaryAddition/CircuitDefs.lean` — Circuit Model

### D13: Circuit model
Defines `GateOp`, `BoolCircuit`, and `AcyclicCircuit` — a concrete DAG of AND/OR/XOR/NOT gates with bounded fan-in, used to model circuit depth.

---

## File: `BinaryAddition/AdderComplexity.lean` — Adder-Specific Complexity

### D12: Group propagate/generate
Defines the carry behavior of groups of bits, used to decompose the carry computation into a two-level structure.

### T9: `carry_group_decomposition` — Carry decomposes at split points
Restates `carry_decompose` from `ParallelAdders` using group terminology.

---

## File: `BinaryAddition/ParallelComplexity.lean` — Complexity Bounds

### `DepthBound` — Abstract depth function
```lean
structure DepthBound (r : Nat) where
  t : Nat → Nat
  base : t 1 = 1
  monotone : ∀ m n, m ≤ n → t m ≤ t n
  recurrence : ∀ p q, 2 ≤ p → 1 ≤ q →
    t (p * q) ≤ 1 + L r p + max (t q) (L r q + L r (p - 1))
```
Rather than axiomatizing, we define a concrete structure capturing any depth function satisfying Brent's Lemma 2 recurrence. This is option (b): define the circuit depth model.

### T12: `finite_upper_bound` — t(r^(k(k-1)/2)) ≤ k(k+1)/2 (Theorem 1)
The main finite complexity result, proved by induction on k using the T-step lemma.

### T13: `asymptotic_bound` — τ(n) ≤ (1+ε) ⌈log_r n⌉ for large n (Theorem 2)
```lean
theorem asymptotic_bound (hr : 2 ≤ r) (db : DepthBound r) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, (db.t n : ℝ) ≤ (1 + ε) * (Nat.clog r n : ℝ)
```
**Paper reference**: Brent 1970, Theorem 2.

**Statement**: Uses Mathlib's `Filter.Eventually` (`∀ᶠ n in atTop`) which unfolds to `∃ N, ∀ n ≥ N, ...`. The bound is stated with `Nat.clog` (ceiling log) rather than `Real.logb`, keeping the proof entirely in Nat arithmetic + basic real inequalities.

**Human-readable proof**:

Given ε > 0:

1. **Ratio bound**: Choose k₀ ≥ 3 such that for all k ≥ k₀, k(k+1) ≤ (1+ε)(k-1)(k-2) in ℝ. This is possible because (4k-2)/((k-1)(k-2)) → 0 as k → ∞, so eventually it falls below ε. Concretely, k₀ = max(3, ⌈4/ε + 3⌉) works.

2. **Threshold**: Set N = r^(k₀(k₀-1)/2) + 1.

3. **For n ≥ N**: Let L = ⌈log_r n⌉. Since n > r^(k₀(k₀-1)/2), we get L > k₀(k₀-1)/2 ≥ 1.

4. **Triangular enclosure**: Find k ≥ 2 with (k-1)(k-2)/2 < L ≤ k(k-1)/2. (The triangular numbers T(k) = k(k-1)/2 grow without bound and cover all positive integers.)

5. **k ≥ k₀**: Since k(k-1)/2 ≥ L > k₀(k₀-1)/2, monotonicity of triangular numbers gives k ≥ k₀.

6. **Chain**:
   - t(n) ≤ t(r^L) [monotonicity, since n ≤ r^L by definition of ceiling log]
   - ≤ t(r^(k(k-1)/2)) [monotonicity, since L ≤ k(k-1)/2]
   - ≤ k(k+1)/2 [by T12]
   - ≤ (1+ε)·(k-1)(k-2)/2 [by ratio bound, since k ≥ k₀]
   - < (1+ε)·L [since (k-1)(k-2)/2 < L]
   - = (1+ε)·⌈log_r n⌉ □

**Key helpers**:
- `tri_enclosure`: Every L ≥ 1 falls between consecutive triangular numbers (proved via `Nat.find` + minimality)
- `ratio_bound_eventually`: Archimedean witness + `nlinarith` for the quadratic inequality
- `cast_tri_div`: Nat→ℝ cast of k(k-1)/2 using divisibility of consecutive products
- `tri_mono`: Monotonicity of triangular numbers

---

---

## Proof Status

| ID | Theorem | File | Status |
|----|---------|------|--------|
| T1 | `gpOp_assoc` | ParallelAdders | **Proved** — Bool case-split |
| T2 | `carry_eq_blockGenerate` | ParallelAdders | **Proved** — induction + bridge lemma |
| T3 | `sum_eq_propagate_xor_carry` | ParallelAdders | **Proved** — direct from `getLsbD_add` |
| T4 | `blockGP_split` | ParallelAdders | **Proved** — induction + `gpOp_assoc` |
| T5 | `splitting_theorem` | GeneralizedRecurrenceEquations | **Proved** — gap induction + g_distrib/g_semi_assoc |
| T6 | `solution_correct` | GeneralizedRecurrenceEquations | **Proved** — 3-case induction + Q_unfold_hi |
| T7 | `algorithmA_correct` | GeneralizedRecurrenceEquations | **Proved** — joint invariant on both components |
| T8 | `genPropPP` | GeneralizedRecurrenceEquations | **Proved** — all 4 restrictions verified |
| T9 | `carry_group_decomposition` | AdderComplexity | **Proved** — direct from T2+T4 |
| T12 | `finite_upper_bound` | ParallelComplexity | **Proved** — induction + triangular number arithmetic |
| T13 | `asymptotic_bound` | ParallelComplexity | **Proved** — Filter.Eventually + ratio bound + tri enclosure |

### Proof difficulty assessment
- **Easy** (proved by `decide`/`simp`/`rfl`): T1, T3, T8 identity/id lemmas
- **Medium** (induction + 3-5 lines): T2, T4, T6, T9
- **Hard** (multi-step induction, algebraic manipulation): T5, T7
- **Very Hard** (Nat arithmetic with division, nlinarith): T12
- **Hard** (real analysis + Nat/ℝ casts): T13

### Key observations from the proving process
1. **atLeastTwo_eq_gp was critical** — the bridge between stdlib's `Bool.atLeastTwo` and the generate/propagate formulation is what makes T2 work.
2. **0-indexing matters** — paper uses 1-indexed bits, Lean uses 0-indexed. We define `blockGP i` covering `[0, i)` which aligns with `carry i` being the carry *into* position i.
3. **∘ IS distributive** — initially feared g_distrib would fail for carry pairs, but exhaustive case-split shows `a ∘ (x ∘ y) = (a ∘ x) ∘ (a ∘ y)` holds.
4. **The Kogge-Stone proofs are inherently harder** than Brent-Kung because the framework is more abstract. The splitting theorem requires careful management of Q's well-founded recursion.
5. **Q_unfold_hi was the key helper** — peeling Q from the high end (instead of the low end as in the definition) required its own gap induction and unlocked both T5 and T6.
6. **T5 needed strict inequality** — the original `j ≤ m` was changed to `j < m` because the case `j = m = n` is unprovable without an identity element assumption.
7. **T7 required a joint invariant** — proving both components of `algorithmA` simultaneously via `algorithmA_invariant`, then specializing to `2^k ≥ i`.
8. **Nonlinear Nat arithmetic** — `omega` cannot handle products of variables. T12 needed `nlinarith` and explicit divisibility witnesses (`two_dvd_mul_succ`) for triangular number identities.

## Verification Checklist

- [x] `lake build` passes with no errors
- [x] Count remaining `sorry` — **0** (all theorems proved)
- [x] `lean_verify` on all key theorems — only standard axioms (propext, Classical.choice, Quot.sound)
- [x] Misformalization check: Lean statements match paper statements
- [x] Edge cases: w=0 works (blockGP 0 = identity), w=1 works

## Key Mathlib/stdlib lemmas used

| Lemma | Source | Used in |
|-------|--------|---------|
| `BitVec.carry_zero` | Init.Data.BitVec.Bitblast | T2 base case |
| `BitVec.carry_succ` | Init.Data.BitVec.Bitblast | T2 step |
| `BitVec.getLsbD_add` | Init.Data.BitVec.Bitblast | T3 |
| `Bool.and_or_distrib_left` | Init.Data.Bool | T1 (implicitly) |
| `Bool.xor_assoc` | Init.Data.Bool | T3 |
| `Nat.clog` | Mathlib.Data.Nat.Log | Brent 1970 complexity |
| `Nat.clog_pow` | Mathlib.Data.Nat.Log | T12 — evaluating ⌈log_r(r^k)⌉ = k |
| `Nat.clog_le_of_le_pow` | Mathlib.Data.Nat.Log | T12 — bounding ⌈log_r(r^k - 1)⌉ ≤ k |
| `Nat.le_pow_clog` | Mathlib.Data.Nat.Log | T13 — n ≤ r^⌈log_r n⌉ |
| `Filter.eventually_atTop` | Mathlib.Order.Filter.AtTopBot.Basic | T13 — "for sufficiently large n" |
| `exists_nat_gt` | Mathlib.Algebra.Order.Archimedean.Basic | T13 — Archimedean witness for k₀ |
| `Nat.cast_div` | Init.Data.Nat.Cast | T13 — Nat→ℝ cast of exact division |
