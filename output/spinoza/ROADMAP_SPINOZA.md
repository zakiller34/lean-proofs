# Spinoza Ethics — Formalization Roadmap

## Status

| Part | Description | Status | Sorries |
|------|-------------|--------|---------|
| Part I | On God (1P1–1P33) | ✅ complete | 0 |
| Part II | On the Nature and Origin of the Mind | 🔲 not started | — |
| Part III | On the Origin and Nature of the Affects | 🔲 not started | — |
| Part IV | On Human Bondage | 🔲 not started | — |
| Part V | On the Power of the Intellect | 🔲 not started | — |

---

## Part I — Summary (Complete)

All 20 sorries filled. 13 bridge axioms added. `lake build` passes.

Key theorems proved:
- `substance_monism` (1P14): axioms = {attribute_individuates, god_has_attribute, hasAttribute_implies_conceived_through_self, isGod_axiom, substance_has_attribute}
- `God_necessarily_exists` (1P11): axioms = {God_is_possible}
- `strict_necessitarianism` (1P33): axioms = {} — pure logic under S5-collapse

Bridge axioms added (all philosophically motivated):
- `attribute_individuates` — each attr belongs to at most one substance
- `hasAttribute_implies_conceived_through_self` — D4 bridge
- `attribute_bearer_is_substance` — only substances have attrs
- `substance_has_attribute` — every substance has at least one attr
- `substance_cause_is_substance` — causes of substances are substances
- `substance_external_prevention_impossible` — no external prevention of substances
- `inherence_implies_causation` — inherence (non-reflexive) → causation
- `inherence_implies_conceived_through` — ontological dependence bridge
- `conceivability_unique` — x conceived through at most one thing
- `mode_inheres_in_substance` — only substances can be ultimate substrata
- `conceived_through_attribute` — D3+D4 bridge
- `entity_extensionality_by_attr_mode` — ontological extensionality
- `god_has_attribute` — God has every self-conceived attribute (D6 consequence)

---

## Part II — On the Nature and Origin of the Mind

### Assessment
Requires richer infrastructure: idea/mind types, adequacy predicate, parallelism axiom.
Most structurally formalizable after Part I.

### New Infrastructure

**New typeclass extension (MindAxioms.lean):**
```lean
class SpinozaMindFramework (Entity : Type*) extends SpinozaFramework Entity where
  Thought : Entity           -- the attribute of Thought
  Extension : Entity         -- the attribute of Extension
  IsIdeaOf : Entity → Entity → Prop   -- idea corresponds to object
  IsAdequate : Entity → Entity → Prop -- idea is adequate in a mind
  MindOf : Entity → Entity   -- the mind corresponding to a body
  Body : Entity              -- the human body (representative individual)
```

**Key new axioms:**
- `ThoughtIsAttr` — Thought is an attribute of God
- `ExtensionIsAttr` — Extension is an attribute of God
- `parallelism` — causal order of ideas = causal order of things (2P7)
- `mind_body_axiom` — human mind is the idea of the human body (2P11)
- `adequate_self_luminous` — the mind knows when it has adequate ideas (2P43)
- `common_notions_adequate` — common notions are adequate ideas (2P40)
- `idea_of_mode_in_God` — God has the idea of every existing mode (2P9)

### Target Propositions (14)

| Prop | Statement | Difficulty | Strategy |
|------|-----------|------------|----------|
| 2P1 | Thought is an attribute of God | easy | axiom `ThoughtIsAttr` |
| 2P2 | Extension is an attribute of God | easy | axiom `ExtensionIsAttr` |
| 2P3 | God has infinite intellect | medium | `Set.Infinite` + idea axioms |
| 2P5 | Ideas have God as their efficient cause | medium | 1P16 + Thought attr |
| 2P7 | Order of ideas = order of things (parallelism) | hard | axiom `parallelism` |
| 2P7C | Thinking/extended substance are same substance | medium | follows from 2P7 + 1P14 |
| 2P9 | Idea of actual mode exists in God | medium | 2P7 + 1P15 |
| 2P11 | Human mind = idea of actually existing body | medium | axiom `mind_body_axiom` |
| 2P13 | Object of human mind is the body | easy | definitional from 2P11 |
| 2P14 | Human mind perceives many things | medium | `Set.Nonempty` |
| 2P32 | All ideas are true in God | medium | A6 + 2P7 |
| 2P40 | Common notions are adequate ideas | hard | axiom `common_notions_adequate` |
| 2P43 | Mind knows adequate ideas are adequate | medium | axiom `adequate_self_luminous` |
| 2P49 | Will = intellect (no separate will) | hard | definitional unification |

### File: `Part2_Mind.lean`
Imports: `Spinoza.Part1_Necessity`, `Spinoza.MindAxioms`

---

## Part III — On the Origin and Nature of the Affects

### Assessment
Requires scalar (ℝ-valued) power, conatus predicate, and affect types.
3P4, 3P6, 3P7 are structurally formalizable. Later propositions about specific emotions are harder.

### New Infrastructure

**New typeclass extension (AffectAxioms.lean):**
```lean
class SpinozaAffectFramework (Entity : Type*) extends SpinozaMindFramework Entity where
  Power : Entity → ℝ            -- power of acting (real-valued)
  Conatus : Entity → Entity → Prop  -- x strives to persevere as y
  Joy : Entity → Prop           -- x is experiencing joy
  Sadness : Entity → Prop       -- x is experiencing sadness
  Desire : Entity → Prop        -- x has a desire
```

**Key new axioms:**
- `conatus_axiom` — every thing strives to persevere in its being (3P7)
- `external_destruction_only` — no thing destroys itself (3P4)
- `joy_power_increase` — joy = transition to greater power (3P11 def)
- `sadness_power_decrease` — sadness = transition to lesser power (3P11 def)
- `desire_is_conatus` — desire is conscious conatus (3Def1)
- `affect_strength_ordering` — stronger affect overcomes weaker (4P7 basis)

### Target Propositions (8)

| Prop | Statement | Difficulty | Strategy |
|------|-----------|------------|----------|
| 3P4 | No thing destroyed except by external cause | easy | axiom `external_destruction_only` |
| 3P5 | Things of opposed natures can't destroy same thing | medium | from A5 + power axioms |
| 3P6 | Each thing strives to persevere in being | easy | axiom `conatus_axiom` |
| 3P7 | Striving = actual essence of that thing | medium | definitional: conatus = essence |
| 3P11 | Power increase/decrease = Joy/Sadness | easy | definitional from affect axioms |
| 3P12 | Mind strives to imagine power-increasing things | medium | from 3P7 + 2P13 |
| 3P13 | Mind avoids imagining power-decreasing things | medium | follows from 3P12 |
| 3P57 | Affect of same kind differs across individuals | medium | from Power variation |

### File: `Part3_Affects.lean`
Imports: `Spinoza.Part2_Mind`, `Spinoza.AffectAxioms`

---

## Part IV — On Human Bondage

### Assessment
Mostly ethical/normative content. Few propositions admit clean formal proofs without
rich normative infrastructure. Target key structural results only; rest are stubs.

### New Infrastructure

**New predicates:**
- `Good : Entity → Entity → Prop` — x is good for y
- `Virtue : Entity → Prop` — x acts with virtue (from adequate ideas)
- `UnderReason : Entity → Prop` — guided by reason
- `HumanBondage : Entity → Prop` — subject to passions, finite power

**Key axioms:**
- `reason_seeks_preservation` — acting from reason = seeking self-preservation (4P18)
- `finite_power_passion` — finite beings necessarily undergo passions (4P4)

### Target Propositions (6, mostly stubs)

| Prop | Statement | Difficulty | Strategy |
|------|-----------|------------|----------|
| 4P2 | We are passive when only part-cause | medium | from `IsMode` + Power |
| 4P4 | We are subject to passions | easy | axiom `finite_power_passion` |
| 4P7 | Affect only overcome by stronger affect | easy | axiom `affect_strength` |
| 4P18 | Reason seeks self-preservation | easy | axiom + 3P7 |
| 4P26 | Acting under reason alone is virtuous | medium | definitional |
| 4P67 | Free person thinks of death least | stub | `sorry` + proof strategy |

### File: `Part4_Bondage.lean`
Imports: `Spinoza.Part3_Affects`

---

## Part V — On the Power of the Intellect / Human Freedom

### Assessment
Most philosophical, least directly formalizable.
Key results about intellectual love of God and eternity of the mind are stubs.
5P20 (blessedness = intellectual love) and 5P40 are definitional.

### New Infrastructure

**New predicates:**
- `IntellectualLove : Entity → Entity → Prop` — x intellectually loves y
- `EternalPart : Entity → Entity → Prop` — x's eternal aspect is y
- `Blessedness : Entity → Prop` — x is blessed

**Key axioms:**
- `intellectual_love_of_God` — blessedness is intellectual love of God (5P20 def)
- `eternal_mind_adequate` — the eternal part of mind = its adequate ideas (5P29)

### Target Propositions (5, most stubs)

| Prop | Statement | Difficulty | Strategy |
|------|-----------|------------|----------|
| 5P3 | Active affect follows from adequate idea | medium | from 2P43 + affect defs |
| 5P6 | Mind can understand things under eternity | stub | `sorry` + strategy |
| 5P20 | Blessedness = intellectual love of God | easy | definitional |
| 5P29 | Eternal part of mind = adequate ideas | stub | `sorry` + strategy |
| 5P40 | Highest good = knowledge of God | easy | definitional + 5P20 |

### File: `Part5_Freedom.lean`
Imports: `Spinoza.Part4_Bondage`

---

## File Structure (Target)

```
output/spinoza/Spinoza/
├── ModalLogic.lean           ✅ S5-collapse modal operators
├── Domain.lean               ✅ SpinozaFramework typeclass
├── Relations.lean            ✅ derived relational facts
├── Definitions.lean          ✅ D1–D8
├── Axioms.lean               ✅ A1–A7, PSR, bridge axioms (13)
├── Part1_Core.lean           ✅ 1P1–1P10
├── Part1_God.lean            ✅ 1P11–1P17
├── Part1_Necessity.lean      ✅ 1P29, 1P33, conceptual barrier
├── MindAxioms.lean           🔲 SpinozaMindFramework + 7 axioms
├── Part2_Mind.lean           🔲 2P1–2P49 (14 props, some sorries)
├── AffectAxioms.lean         🔲 SpinozaAffectFramework + 6 axioms
├── Part3_Affects.lean        🔲 3P4–3P57 (8 props)
├── Part4_Bondage.lean        🔲 4P2–4P67 (6 props, mostly stubs)
└── Part5_Freedom.lean        🔲 5P3–5P40 (5 props, mostly stubs)
```

---

## Agent Team Plan

### Team: `spinoza-parts-2-5`

| Agent | Model | Role |
|-------|-------|------|
| researcher | Sonnet 4.6 | Survey Mathlib for relevant lemmas; check if any Parts II–V exist in Lean community; identify formalization pitfalls |
| writer | Opus | Create MindAxioms.lean + Part2_Mind.lean, then AffectAxioms.lean + Part3_Affects.lean; stubs for IV–V |
| prover | Opus | Fill sorries in Parts II–III using lean_goal, lean_state_search, Aristotle |
| reviewer | Opus | `lake build` must pass; grep for `sorry` in II–III (must be 0); `lean_verify` on key theorems |

### Pipeline

```
researcher → writer (Part II) → prover (Part II) → writer (Part III) → prover (Part III) → writer (IV–V stubs) → reviewer
```

### Researcher Tasks
- Search Lean community for any prior Ethics formalizations (Lean 3 or 4)
- Check Mathlib for: `IsEquiv`, `Equiv`, `Real.continuousAt`, category theory for parallelism
- Identify whether `parallelism` (2P7) is best as axiom or structure
- Report: which of the 14+8+6+5 targets are likely to require new axioms vs. pure logic

### Writer Tasks (Phase 1 — Part II)
1. Create `MindAxioms.lean` extending `SpinozaFramework` with mind/idea primitives
2. Create `Part2_Mind.lean` with all 14 propositions as theorems with `sorry`
3. Compile with `lake build` — must pass before prover starts

### Writer Tasks (Phase 2 — Parts III–V)
1. Create `AffectAxioms.lean` extending mind framework with power/conatus
2. Create `Part3_Affects.lean` with 8 propositions
3. Create `Part4_Bondage.lean` and `Part5_Freedom.lean` as stubs
4. Update `lakefile.toml` to include all new modules

### Prover Tasks
- Fill sorries bottom-up in dependency order
- Part II first, then Part III
- Use `lean_multi_attempt ["simp", "exact", "tauto", "omega"]` for trivial goals
- Use Aristotle for hard sorries
- Leave IV–V stubs (tagged `-- TODO: requires additional axioms`)

### Reviewer Checklist
- `lake build` from `output/spinoza/` — must succeed
- `grep -r "sorry" Spinoza/ | grep -v "Part4\|Part5"` — must be empty
- `lean_verify` on: `substance_monism_part2`, `parallelism_consequence`, `conatus_is_essence`
- Flag any misformalization vs. blueprint

---

## Misformalization Risks

| Risk | Mitigation |
|------|------------|
| Parallelism (2P7) as identity vs. isomorphism | Use bijection `f : Entity → Entity` with axiom `IsIdeaOf x (f x)` |
| Conatus as predicate vs. function | Use `Conatus x x` predicate (strives = self-directed) |
| `Power : Entity → ℝ` — negative power? | Add `axiom power_nonneg : ∀ x, 0 ≤ Power x` |
| Will = Intellect (2P49) — circular? | Encode as: no `Will` field separate from `Intellect` |
| Joy/Sadness as binary vs. graded | Use `Power` differential: `δPower x > 0 ↔ Joy x` |
| Eternity of mind (Part V) — temporal types | Add stub `Time : Type` with `IsTimeless : Entity → Prop` |

---

## AMS Classification (MSC2020)

| Part | Codes |
|------|-------|
| Part I (complete) | 03A05 (philosophical foundations), 03B45 (modal logic) |
| Part II | 03B65 (epistemic logic), 18A05 (category theory — parallelism), 03B42 (relevance logic) |
| Part III | 93A05 (dynamical systems — conatus), 49J99 (optimization — power maximization) |
| Parts IV–V | 03A05 (ethics as logic), 03B45 (modal — eternity) |

---

## Open Questions

1. **Parallelism encoding**: axiom `parallelism` vs. `Equiv`-based bijection — which is more faithful to 2P7?
2. **Power type**: `ℝ` (continuous) vs. `ℕ` (discrete) vs. `Ordinal` — recommend `ℝ` for compatibility with Mathlib analysis lemmas
3. **Will = Intellect (2P49)**: encode as a theorem (will and intellect are the same thing) or by absence of a separate `Will` field?
4. **Parts IV–V scope**: should they be full propositions with sorries, or just documentation stubs?
5. **SpinozaMindFramework extension**: should it `extend SpinozaFramework` or be a separate typeclass that `includes` it? (Recommendation: `extends` for simplicity)
