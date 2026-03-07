# Formalization of Erdos Problems — Blog Summary

**Source**: Boris Alexeev, "Formalization of Erdos Problems", Xena Project blog, 2025-12-05
**URL**: https://xenaproject.wordpress.com/2025/12/05/formalization-of-erdos-problems/

## Background

- [erdosproblems.com](https://erdosproblems.com) catalogs ~1200 problems posed by Paul Erdos
- The **Formal Conjectures** project (GitHub: `formal-conjectures`) aims to formalize open conjectures in Lean 4
- Erdos problems are a major target due to their precise, self-contained nature

## Human Formalization Timeline

- Initial human formalization was slow — each problem required deep Mathlib knowledge
- Formalizers needed to find/create missing definitions, translate notation, handle edge cases
- Community collaboration via Lean Zulip and GitHub PRs was essential

## AI-Assisted Formalization Pipeline

1. **ChatGPT** used for initial translation of informal math to Lean sketch
2. **Aristotle** (cloud prover) used to fill `sorry` statements
3. Human review for correctness — checking that the Lean statement matches the math
4. Key insight: AI dramatically sped up the process but introduced misformalization risk

## AI-Only Formalization Breakthroughs

- **Problem 124**: AI produced a formalization that compiled and was provable, but captured a *different* problem than intended (high-level misformalization)
- **Problem 481**: Successfully formalized with AI assistance
- **Problem 488**: Successfully formalized with AI assistance
- The speed was remarkable but required careful human oversight

## Misformalization Taxonomy

The blog identifies misformalization as "a big issue and was more frequent than I had expected." Three levels:

### Level 1: Low-Level Technical Bugs
- Wrong variable: `m != 0` instead of `n != 0`
- Flipped inequalities: `<` vs `<=`, `<` vs `>`
- Forgotten zero/empty cases
- Reversed quantifier order: `forall x, exists y` vs `exists y, forall x`
- Junk values: Lean's `n / 0 = 0` silently passes type-checking

### Level 2: Missing Hypotheses
- Informal math implicitly assumes conditions not stated in the Lean formalization
- Results in statements that admit trivial counterexamples the real theorem doesn't have
- E.g., missing positivity, finiteness, or non-degeneracy conditions

### Level 3: High-Level / Wrong Problem
- The Lean statement captures a different mathematical problem than intended
- Can be syntactically reasonable and even provable, but doesn't match the conjecture
- Example: Erdos Problem 124 — AI formalization was provable but wrong problem

## Key Takeaways

1. **Misformalization is the bottleneck**: As AI makes formalization faster, checking correctness becomes the main challenge
2. **Community infrastructure matters**: erdosproblems.com + Formal Conjectures + Lean Zulip created an effective pipeline
3. **Human review remains essential**: AI can draft, but humans must verify faithfulness to the mathematics
4. **Speed vs correctness tradeoff**: AI enables rapid formalization but each statement needs line-by-line checking
5. **Future prospects**: AI formalization will continue accelerating; the community needs better tools for detecting misformalization
