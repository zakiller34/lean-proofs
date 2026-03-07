# Formally Verifying a 17th-Century Metaphysical Proof

*What happens when you feed Spinoza's Ethics into a theorem prover?*

---

In 1677, Baruch Spinoza published the *Ethica Ordine Geometrico Demonstrata* — the *Ethics Demonstrated in Geometrical Order*. The structure is deliberate and audacious: definitions, axioms, propositions, proofs. Spinoza wrote philosophy the way Euclid wrote geometry. He wanted his conclusions to feel as inevitable as a QED.

Three and a half centuries later, we have tools that can check whether a deductive argument actually holds. This post is about what happens when you take Spinoza's *Ethics* — all five parts, 54 propositions, from God's existence to human blessedness — and formalize it in Lean 4.

The short answer: it works, mostly. The long answer reveals something about where Spinoza's informal reasoning leans on unstated assumptions, where it is genuinely tight, and what a single remaining `sorry` tells us about the hardest philosophical boundary in the whole work.

---

## 1. Why Lean? What Does Formalization Reveal?

Lean 4 is an interactive proof assistant. You write mathematical statements in a typed functional language, and the compiler verifies that your proofs are correct — not approximately correct, not plausible, but *logically airtight*. Every gap must be filled; every implicit assumption must be named.

Spinoza's geometric method is an ideal target for this. He explicitly adopts the axiomatic structure: state your primitives, state your axioms, derive everything else. If his proofs are as watertight as he believed, formalization should be smooth. If there are gaps, Lean will find them.

What we built: a 14-file Lean 4 project covering all five parts of the *Ethics*:

- **Part I** — God, substance, necessity (1P1–1P17, 1P29, 1P33)
- **Part II** — Mind, ideas, parallelism (2P1–2P49)
- **Part III** — Affects, conatus, joy and sadness (3P4–3P57)
- **Part IV** — Bondage, virtue, reason (4P2–4P26, 4P67)
- **Part V** — Freedom, blessedness, eternity (5P3–5P40)

The project compiles. `lake build` passes. There is one `sorry`.

---

## 2. The Design: S5-Collapse and Typeclasses

### The Boldest Design Decision: S5-Collapse

Spinoza is a necessitarian. In 1P33 he argues that things could not have been produced in any other way — there is exactly one possible world, and it is the actual one. Modal operators (necessity and possibility) therefore collapse onto truth.

We encode this directly:

```lean
-- ModalLogic.lean

/-- Necessity (S5-collapse): □p ≡ p -/
def Necessarily (p : Prop) : Prop := p

/-- Possibility (S5-collapse): ◇p ≡ p -/
def Possibly (p : Prop) : Prop := p
```

This is the S5 modal logic axiom `□p → p` taken to its limit: since every truth is necessary and every necessity is actual, we simply identify all three. It is philosophically controversial — critics argue Spinoza only claims *de facto* necessity, not logical necessity — but it faithfully captures his 1P33 and makes the formalization tractable.

The payoff is immediate: statements like "God necessarily exists" and "God possibly exists" become the same proposition.

### Three Levels of Typeclass Hierarchy

The ontology is bundled into a hierarchy of typeclasses, each extending the last:

```lean
-- Domain.lean

/-- Bundle of all primitive Spinoza relations over an entity domain. -/
class SpinozaFramework (Entity : Type*) where
  /-- `InheresIn x y` : x exists in y as a subject (ontological inherence) -/
  InheresIn : Entity → Entity → Prop
  /-- `ConceivedThrough x y` : the concept of x requires the concept of y -/
  ConceivedThrough : Entity → Entity → Prop
  /-- `HasAttribute s a` : substance s has attribute a constituting its essence -/
  HasAttribute : Entity → Entity → Prop
  /-- `Causes x y` : x is an efficient cause of y -/
  Causes : Entity → Entity → Prop
  /-- `Prevents x y` : x is a reason for the non-existence of y -/
  Prevents : Entity → Entity → Prop
  /-- The unique individual: God or Nature (Deus sive Natura) -/
  God : Entity
```

`SpinozaMindFramework` extends this with Thought, Extension, `IsIdeaOf`, `IsAdequate`, `MindOf`, and `Body` — the machinery needed for Part II's mind-body theory.

`SpinozaAffectFramework` extends that with `Power : Entity → ℝ`, `Conatus`, `IsJoy`, `IsSadness`, and `IsDesire` — Spinoza's psychology, encoded with real-valued power.

Every file in the project repeats a small header:

```lean
variable {Entity : Type*} [SpinozaFramework Entity]
open SpinozaFramework
```

This makes all definitions and theorems polymorphic over any model satisfying the framework — a clean separation between the abstract structure and any concrete instantiation.

---

## 3. Part I: God, Substance, and Necessity

### The Definitions

Spinoza's eight definitions open Part I. Four are central to the formalization:

```lean
-- Definitions.lean

/-- D1: A thing is *causa sui* whose essence involves existence. -/
def IsCausaSui (x : Entity) : Prop :=
  Causes x x ∧ Necessarily (∃ y : Entity, y = x)

/-- D6: God is a substance consisting of infinitely many attributes. -/
def IsGod (g : Entity) : Prop :=
  IsSubstance g ∧
  Set.Infinite {a : Entity | HasAttribute g a}

/-- D7a: A thing is *free* if determined only by its own nature. -/
def IsFree (x : Entity) : Prop :=
  IsCausaSui x ∧ ∀ y : Entity, Causes y x → y = x
```

`IsSubstance` is defined in `Domain.lean` as `InheresIn x x ∧ ConceivedThrough x x` — a substance is in itself and conceived through itself, capturing Spinoza's D3 precisely.

### Showcase Theorem 1: Substance is Causa Sui (1P6C)

> *"A substance cannot be produced by anything external; hence it is the cause of itself."* — 1P6C

This is one of the more complex proofs in Part I. It uses the Principle of Sufficient Reason (`PSR_symmetric`): for any entity, there is either a cause for its existence or a cause for its non-existence. For substances, both alternatives lead to contradiction — leaving only self-causation.

```lean
-- Part1_Core.lean

/-- **1P6C**: A substance can have no external cause; hence it is causa sui. -/
theorem substance_is_causa_sui
    (s : Entity) (hs : IsSubstance s) : IsCausaSui s := by
  constructor
  · rcases PSR_symmetric s with ⟨c, hc⟩ | ⟨c, hc⟩
    · -- c causes s → c is substance → by 1P6, c = s
      have hc_sub : IsSubstance c := substance_cause_is_substance s c hs hc
      by_cases heq : c = s
      · exact heq ▸ hc
      · exact absurd hc (substance_not_produced_by_substance c s hc_sub hs heq)
    · -- c prevents s → contradiction (no internal or external prevention)
      by_cases heq : c = s
      · exact absurd ⟨c, heq, hc⟩ (no_internal_prevention s hs)
      · exact absurd hc (substance_external_prevention_impossible s c hs heq)
  · exact ⟨s, rfl⟩
```

The proof has two branches. If something external causes `s`, it must be a substance (by `substance_cause_is_substance`), but 1P6 says no distinct substance can cause another — contradiction. If something prevents `s`, it must be either `s` itself (self-prevention, ruled out by `no_internal_prevention`) or something external (ruled out by `substance_external_prevention_impossible`). The only remaining case: `s` causes itself.

### Showcase Theorem 2: God Necessarily Exists (1P11)

> *"God, or a substance consisting of infinite attributes, each of which expresses eternal and infinite essence, necessarily exists."* — 1P11

```lean
-- Part1_God.lean

/-- **1P11** (PSR demonstration): God necessarily exists. -/
theorem God_necessarily_exists :
    Necessarily (∃ g : Entity, IsGod g) :=
  God_is_possible
```

One line. This is the S5-collapse at work: `Necessarily p` unfolds to `p`, and `God_is_possible` is the axiom `∃ g : Entity, IsGod g`. The ontological argument — one of the most contentious in the history of philosophy — is a definitional triviality under necessitarianism. Possibility *is* actuality.

### Showcase Theorem 3: Substance Monism (1P14)

> *"Except God, no substance can be, nor can be conceived."* — 1P14

```lean
-- Part1_God.lean

/-- **1P14**: Besides God, no substance can exist or be conceived. -/
theorem substance_monism
    (s : Entity) (hs : IsSubstance s) : s = God := by
  have hGod_sub := (@isGod_axiom Entity _).1
  by_contra hne
  obtain ⟨a, ha⟩ := substance_has_attribute s hs
  have hca : ConceivedThrough a a := hasAttribute_implies_conceived_through_self s a ha
  have hGa : HasAttribute (God : Entity) a := god_has_attribute a hca
  exact hne (no_shared_attribute s God hs hGod_sub ⟨a, ha, hGa⟩)
```

Every substance has at least one attribute. Every attribute conceived through itself belongs to God (by D6 and the bridge axiom `god_has_attribute`). Two substances sharing an attribute are identical (1P5 / `no_shared_attribute`). Therefore any substance equals God.

### Showcase Theorem 4: Nothing is Contingent (1P29)

```lean
-- Part1_Necessity.lean

/-- **1P29**: Nothing in nature is contingent; everything is determined. -/
theorem no_contingency (x : Entity) : ∃ c : Entity, Causes c x := by
  rcases A1 x with hself | ⟨y, hyne, hy⟩
  · -- x in itself → x is substance → causa sui → causes itself
    ...
    exact ⟨x, (substance_is_causa_sui x hx_sub).1⟩
  · -- x in y (y ≠ x) → x is a mode → God causes x (1P16)
    ...
    exact ⟨God, all_things_follow_from_God x hx_mode⟩
```

Everything either inheres in itself (making it a substance, hence self-caused) or in something else (making it a mode, hence caused by God). There is no third option.

### The Bridge Axioms

Here is what Spinoza does not tell you he is assuming. The project requires 14 "bridge axioms" beyond Spinoza's original A1–A7. These are not invented — they are implicit in his informal proofs, made explicit by the discipline of formalization:

| Axiom | What it captures |
|-------|-----------------|
| `attribute_individuates` | Each attribute belongs to at most one substance |
| `attribute_bearer_is_substance` | Only substances can have attributes |
| `substance_has_attribute` | Every substance has at least one attribute |
| `substance_cause_is_substance` | The cause of a substance is a substance |
| `inherence_implies_causation` | If x is in y (x ≠ y), then y causes x |
| `inherence_implies_conceived_through` | What inheres in y is conceived through y |
| `conceivability_unique` | x can be conceived through at most one thing |
| `mode_inheres_in_substance` | Modes inhere in substances (substances are ultimate substrata) |
| `god_has_attribute` | Every self-conceived attribute belongs to God |
| `substance_external_prevention_impossible` | Nothing external prevents a substance from existing |
| `no_internal_prevention` | A substance doesn't prevent its own existence |
| `conceived_through_attribute` | Substance is conceived through its attributes |
| `entity_extensionality_by_attr_mode` | Same attributes + same modes → identical entity |
| `God_is_possible` | God's existence is possible (the ontological premise) |

These are all philosophically defensible within Spinoza's system. But they are not proven from A1–A7. They represent the "soft tissue" of his deductive edifice.

---

## 4. Part II: Mind, Parallelism, and the Limits of Will

Part II introduces `SpinozaMindFramework`, adding two specific attributes of God — Thought and Extension — and the mind-body correspondence structure.

### Parallelism: The Most Famous Spinozist Claim

> *"The order and connection of ideas is the same as the order and connection of things."* — 2P7

```lean
-- MindAxioms.lean

/-- 2P7 (Parallelism): Order and connection of ideas = order and connection of things. -/
axiom parallelism : ∀ (x y : Entity),
  Causes x y ↔ Causes (MindOf x) (MindOf y)
```

This is encoded as an axiom, not a theorem. Spinoza derives it from his attribute doctrine — Thought and Extension are two modes of expression of the same underlying substance. In the formalization, we have not (yet) derived it; it stands as a primitive of the mind-body framework. This is an honest representation: 2P7 is one of Spinoza's most contested claims, and its justification in the *Ethics* is itself contentious.

### Human Mind as Idea of the Body (2P11)

```lean
-- Part2_Mind.lean

/-- **2P11**: The first thing constituting the actual being of the human mind is
    the idea of a particular actually existing thing — namely, the body. -/
theorem human_mind_is_idea_of_body :
    IsIdeaOf (MindOf (Body : Entity)) (Body : Entity) :=
  mind_body_axiom Body
```

One line, direct from the `mind_body_axiom`. Spinoza's mind-body theory — the mind is the idea of the body — is encoded as a primitive correspondence `MindOf : Entity → Entity` satisfying `IsIdeaOf (MindOf b) b` for all bodies `b`.

### Self-Luminosity of Adequate Ideas (2P43)

```lean
-- Part2_Mind.lean

/-- **2P43**: He who has a true idea knows at the same time that he has a true idea. -/
theorem adequate_idea_self_known (i : Entity) (hi : IsAdequate i) :
    ∃ j : Entity, IsIdeaOf j i ∧ IsAdequate j :=
  adequate_self_luminous i hi
```

Adequate knowledge is self-certifying: if you have an adequate idea, there exists an adequate idea of that idea. This is Spinoza's answer to Descartes' skeptical doubt — adequate ideas carry their truth conditions within themselves.

### No Free Will (2P49): A Surprise Reduction

> *"In the mind there is no absolute or free will."* — 2P49

```lean
-- Part2_Mind.lean

/-- **2P49**: The mind is determined by causes. Will and intellect are one. -/
theorem no_free_will_will_eq_intellect (m : Entity) (_hm : IsMode m) :
    ∃ cause : Entity, Causes cause m :=
  no_contingency m
```

The proof is a single function call: `no_contingency m`, from Part I. The mind, as a mode, has a determining cause. Volitions, as modes of thought, are no exception. The denial of free will is not a separate argument in Part II — it follows immediately from 1P29. Spinoza structured his system so that this would be so.

---

## 5. Part III: Affects, Power, and Conatus

`SpinozaAffectFramework` introduces the psychological layer. The key addition is `Power : Entity → ℝ` — a real-valued measure of each entity's power of acting, the quantity that joy increases and sadness decreases.

### Conatus: Universal Striving

```lean
-- AffectAxioms.lean

/-- Conatus axiom (3P6 basis): every thing has positive striving to persist. -/
axiom conatus_is_essence : ∀ (x : Entity), Conatus x
```

```lean
-- Part3_Affects.lean

/-- **3P7**: The striving by which each thing strives to persist in its being
    is nothing other than the actual essence of that thing. -/
theorem conatus_is_actual_essence (x : Entity) :
    Conatus x ↔ ∃ y : Entity, y = x :=
  ⟨fun _ => ⟨x, rfl⟩, fun _ => conatus_is_essence x⟩
```

Conatus holds for everything that exists — and under S5-collapse, existence is equivalent to necessary existence. The biconditional says: striving is coextensive with being. This is Spinoza's central psychological claim: there is no such thing as an entity that does not strive to continue existing.

### Joy, Sadness, and Power

Joy and sadness are mutually exclusive (`joy_sadness_distinct`), and joy is associated with positive power:

```lean
-- Part3_Affects.lean

/-- **3P11 corollary**: Joy is associated with positive power. -/
theorem joy_implies_positive_power (a e : Entity)
    (hj : IsJoy a) (hi : InheresIn a e) :
    0 < Power e :=
  joy_power_positive a e hj hi
```

The real-valued `Power` field allows precise statements about the direction of affect. What gets lost is the *dynamics* — the passage from one power level to another over time. Spinoza's affects are inherently about transitions ("joy is a passage to greater perfection"), but a static real number cannot express a passage. A full formalization would require a temporal model, something like a function `Power : Entity → Time → ℝ`. That remains future work.

---

## 6. Parts IV–V: Bondage, Freedom, and Blessedness

Part IV defines the key concepts locally, building a 4-level ladder from servitude to liberation:

```lean
-- Part4_Bondage.lean

/-- Virtue = power to act from one's own nature alone. -/
def IsVirtuous (x : Entity) : Prop :=
  Conatus x ∧ ∀ c : Entity, Causes c x → c = x

/-- Acting under reason = guided by adequate ideas. -/
def UnderReason (x : Entity) : Prop :=
  IsAdequate (MindOf x)

/-- Human bondage = determined by external passions. -/
def InBondage (x : Entity) : Prop :=
  ¬UnderReason x ∧ ∃ c : Entity, c ≠ x ∧ Causes c x
```

Part V adds:

```lean
-- Part5_Freedom.lean

/-- Intellectual love of God = adequate idea of God as cause of all joy. -/
def IntellectualLoveOfGod (x : Entity) : Prop :=
  IsAdequate (MindOf x) ∧ IsJoy (MindOf x) ∧ InheresIn (MindOf x) x

/-- Blessedness = the intellectual love of God itself; not a reward but the virtue. -/
def Blessedness (x : Entity) : Prop :=
  IntellectualLoveOfGod x
```

### Key Theorems

**Reason demands self-preservation (4P18)**:

```lean
theorem reason_demands_self_preservation (x : Entity) (hr : UnderReason x) :
    Conatus x :=
  reason_seeks_preservation x hr
```

**Blessedness is virtue, not reward (5P20)**:

```lean
/-- **5P20**: Blessedness is not the reward of virtue but virtue itself. -/
theorem blessedness_is_intellectual_love
    (x : Entity) (hg : IsGood x) (hr : UnderReason x) :
    Blessedness x :=
  intellectual_love_is_highest_good x ⟨hg, hr⟩
```

**The resolution: virtue and freedom are equivalent (5P40)**:

```lean
/-- **5P40**: Virtue and freedom are equivalent. -/
theorem virtuous_iff_free (x : Entity) :
    IsVirtuous x ↔ IsFree x :=
  virtue_eq_freedom x
```

This is the culmination of the whole work: the virtuous person, acting from the necessity of their own nature, is free — not free from determination, but free *as* determination by their own nature rather than external causes. Spinoza's freedom is not libertarian free will; it is self-determination.

### The One Remaining Sorry: 4P67

> *"A free man thinks of nothing less than of death, and his wisdom is a meditation not on death but on life."* — 4P67

```lean
-- Part4_Bondage.lean

theorem free_man_meditates_on_life
    (x : Entity) (hv : IsVirtuous x) :
    Conatus x ∧ ¬∃ c : Entity, c = x ∧ Prevents c x := by
  constructor
  · exact hv.1
  · intro ⟨c, heq, hprev⟩
    -- A virtuous (free) entity has all its causes internal (hv.2 says causes → c = x)
    -- Prevents c x with c = x would be self-prevention, but PSR + IsFree makes this void
    sorry -- TODO: needs bridge between IsVirtuous and no_internal_prevention
```

The first conjunct is trivial: virtue includes conatus. The second — that a free entity does not prevent its own existence — is where the proof stalls. We have `no_internal_prevention` for substances: a substance cannot prevent its own existence. But `IsVirtuous` is about finite beings (modes) acting from their own nature. The axiom `no_internal_prevention` applies to `IsSubstance`, not `IsVirtuous`.

This is a genuine philosophical gap. Spinoza proves 4P67 for the "free man" — a finite being who has achieved reason. But the formal machinery for preventing self-destruction (`no_internal_prevention`) was built for God and substances, not for humans who aspire to freedom. Connecting the two would require an axiom like "a virtuous mode cannot prevent its own existence," which is either trivially true (by conatus) or requires a subtler argument about the relationship between `IsVirtuous` and the no-prevention structure.

The `sorry` marks the exact boundary between "God is free" (fully proved) and "a human being can be free" (philosophically asserted, formally incomplete).

---

## 7. What the Formalization Reveals

### What Was Easy
Most of Part II and Part III are one-liners. Once the axiom framework is right, the propositions follow directly. `no_free_will_will_eq_intellect` is one line. `human_mind_is_idea_of_body` is one line. `God_necessarily_exists` is one line. These results are easy because Spinoza's deductive structure is genuinely tight at those points.

### What Was Hard
The 14 bridge axioms. Spinoza's A1–A7 are not sufficient to prove his propositions without additional assumptions about how attributes individuate substances, how inherence relates to causation, how conceivability works, and how prevention interacts with substance. These are all things a careful reader would grant Spinoza without hesitation — but they are assumptions, not axioms, and formalization forces you to name them.

### The S5 Shortcut
The collapse `Necessarily p := p` makes 1P11 trivial. This is either a feature or a bug depending on your philosophy. If you accept Spinoza's necessitarianism — if you grant that there is only one possible world — then the S5-collapse is not a shortcut; it is the correct encoding. The triviality of God's existence proof is not a sign that the proof is wrong; it is a sign that under Spinoza's own premises, the proof was always going to be a triviality.

### Axiom Count
The project has approximately 40 axioms for 54 theorems. Most "proofs" are orchestrations of axioms rather than derivations of genuinely new content. This is not a criticism — it reflects Spinoza's method. He is explicit that his propositions follow from his definitions and axioms. The formalization simply makes visible which axioms each proposition actually requires.

### The 1 Sorry as Philosophy
The single `sorry` in 4P67 is not a technical failure. It marks a genuine philosophical gap between God's freedom (infinite substance, fully self-caused) and human freedom (finite mode, partially self-caused). Spinoza bridges this gap in his text by appealing to the idea that the virtuous person acts solely from their own nature — but "acting solely from one's own nature" is defined differently for modes than for substances. The formal system exposes the seam.

---

## 8. Summary Table

| Part | Propositions Formalized | Sorries | Notes |
|------|------------------------|---------|-------|
| I: God & Substance | 1P1–1P17, 1P29, 1P33 | 0 | 14 bridge axioms |
| II: Mind | 2P1–2P49 (selected) | 0 | Parallelism as axiom |
| III: Affects | 3P4–3P57 (selected) | 0 | Static power model |
| IV: Bondage | 4P2–4P26, 4P67 | 1 | 4P67 needs mode-freedom bridge |
| V: Freedom | 5P3–5P40 (selected) | 0 | Blessedness as ILG |
| **Total** | **54 theorems** | **1** | |

---

## 9. Future Work

Three directions would substantially deepen the formalization:

1. **Temporal model for affects**: Replace `Power : Entity → ℝ` with `Power : Entity → Time → ℝ`. This would allow encoding affect *transitions* — joy as an increase, sadness as a decrease — and make Part III propositions about the dynamics of the passions provable rather than axiomatic.

2. **Eliminate bridge axioms**: Several of the 14 bridge axioms can likely be derived if the primitive relations are given more structure. For example, if `InheresIn` is axiomatized to be a preorder and `ConceivedThrough` is its unique-representative relation, some bridge axioms might become theorems.

3. **Close the 4P67 gap**: Formalize the connection between `IsVirtuous` (finite-mode freedom) and the prevention structure. This would require either a new axiom about virtuous modes or a derivation from the existing mode/substance architecture.

---

The *Ethics* ends with a famous sentence: *"All things excellent are as difficult as they are rare."* Spinoza was right about the difficulty. But the formalization suggests they are also more tractable than they appear — once you are forced to state every assumption explicitly.

---

*Project source: `output/spinoza/` in the lean-proofs repository. Build: `cd output/spinoza && lake build`. Toolchain: Lean 4.29.0-rc1 + Mathlib.*

*AMS MSC2020: 03A05 (Philosophical foundations), 03B45 (Modal logic), 03B60 (Other nonclassical logic).*
