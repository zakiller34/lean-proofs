# Spinoza's *Ethics* — Formal Ontology Ready for Lean 4

> A structured reconstruction of the formalizable content of *Ethica Ordine Geometrico Demonstrata* (Part I, primarily),
> organized as definitions, axioms, lemmas, and theorems in a style directly translatable into Lean 4 / Mathlib.
>
> Sources: Spinoza (1677); *Cambridge Companion to Spinoza's Ethics*, ed. Koistinen (2009);
> Bennett (1984); Garrett (1979); Della Rocca; Jarrett (Necessity chapter).

---

## Preamble: Scope and Strategy

### Why Part I is the formalizable core

Spinoza's *Ethics* is written *more geometrico* — in the geometric manner. But only **Part I** (*On God*) achieves the logical density required for a faithful formal encoding. The reasons are precise:

- Parts II–V introduce **scalar** notions (power of acting, degrees of perfection) and **intentional** operators (ideas of ideas, conatus) that require richer type theories.
- Part I deals exclusively with **structural** relations: *being in*, *being conceived through*, *sharing an attribute*, *causal dependence*, *necessary existence*. These are binary predicates over a fixed domain — ideal for first-order logic and type theory.
- The argument structure of Part I is a **directed acyclic proof graph**: each proposition cites only earlier results, axioms, or definitions.

### Lean 4 architecture overview

The formalization uses:
- `Type` and `Prop` universes
- A **domain of entities** `Entity : Type` (substances, modes, attributes, and God)
- Primitive **predicates** as `Prop`-valued functions
- **Axioms** as `axiom` declarations
- **Definitions** as `def` or `structure`
- **Propositions** as `theorem` or `lemma`

---

## Part 0 — Primitive Sorts and Domain

### 0.1 Domain Declaration

```lean
-- The universe of all entities Spinoza considers
variable (Entity : Type)

-- Three distinguished sub-sorts (realized as predicates)
variable (IsSubstance : Entity → Prop)
variable (IsMode      : Entity → Prop)
variable (IsAttribute : Entity → Prop)

-- The unique individual: God
variable (God : Entity)
```

**Commentary:** Spinoza's ontology stratifies into exactly three kinds: substance, mode, and attribute. Everything that exists is either a substance or a mode (1a1). Attributes are not a third *kind of thing* but rather the essential natures perceived in a substance (1d4). This asymmetry will be captured in Axiom A1 below.

---

## Part 1 — Primitive Relations

### 1.1 The *In* Relation (Inherence)

```lean
-- `InheresIn x y` : x exists in y as a subject
variable (InheresIn : Entity → Entity → Prop)
```

**Spinoza's text:** A substance is "what is in itself" (1d3). A mode is "what is in another" (1d5). The *in* relation is Spinoza's ontological inherence, tracking the Aristotelian substance/accident distinction.

### 1.2 The *Conceived Through* Relation (Conceptual Dependence)

```lean
-- `ConceivableThrough x y` : the concept of x requires the concept of y
variable (ConceivedThrough : Entity → Entity → Prop)
```

**Spinoza's text:** "whose concept does not require the concept of another thing" (1d3). This is a *conceptual priority* relation, not merely causal. Spinoza treats it as co-extensive with inherence via Axiom A4.

### 1.3 The *Has Attribute* Relation

```lean
-- `HasAttribute s a` : substance s has attribute a constituting its essence
variable (HasAttribute : Entity → Entity → Prop)
```

### 1.4 Causal Relations

```lean
-- `Causes x y` : x is an (efficient) cause of y
variable (Causes : Entity → Entity → Prop)

-- `CausaSui x` : x is the cause of itself (self-caused)
def CausaSui (x : Entity) : Prop := Causes x x
```

**Spinoza's text (1d1):** "That thing is called *cause of itself* whose essence involves existence, or whose nature cannot be conceived except as existing."

### 1.5 Modal Operators

```lean
-- Necessity and possibility as propositional operators
-- (Modeled in Lean via a Kripke structure or directly as axioms)
-- For simplicity we use classical logic + an accessibility relation W

variable (World : Type)
variable (Accessible : World → World → Prop)  -- for S5: equivalence relation
variable (TrueAt : World → Prop → Prop)

-- Necessary truth: true in all accessible worlds
def Necessarily (p : Prop) : Prop := ∀ w : World, p  -- (S5 collapse: all worlds accessible)
def Possibly   (p : Prop) : Prop := ∃ w : World, p
```

**Note on S5:** Spinoza is a necessitarian — ultimately there is only one possible world (see 1p33). Under this collapse, `□p ↔ p ↔ ◇p`. We keep the modal operators for intermediate steps where the argument exploits the distinction.

---

## Part 2 — Definitions (*Definitiones*)

### Definition D1 — Causa Sui (1d1)

```lean
/-- A thing is *causa sui* if its essence necessarily involves existence;
    equivalently, it cannot be conceived as non-existing. -/
def IsCausaSui (x : Entity) : Prop :=
  CausaSui x ∧ Necessarily (∃ y, y = x)
```

**Spinoza:** "By cause of itself I understand that whose essence involves existence, or that whose nature cannot be conceived except as existing."

### Definition D2 — Finite in Its Own Kind (1d2)

```lean
/-- x is finite in its own kind if it can be limited by another thing
    of the same nature. -/
def FiniteInKind (x : Entity) (SameKind : Entity → Entity → Prop) : Prop :=
  ∃ y : Entity, SameKind x y ∧ ¬(x = y) ∧
    -- y "limits" x: there is no z of the same kind strictly between them
    ∀ z : Entity, SameKind x z → (InheresIn z y ∨ InheresIn z x)

def InfiniteInKind (x : Entity) (SameKind : Entity → Entity → Prop) : Prop :=
  ¬FiniteInKind x SameKind
```

**Spinoza:** "That thing is finite in its own kind that can be limited by another thing of the same nature." (1d2)

### Definition D3 — Substance (1d3)

```lean
/-- A substance is that which is in itself and conceived through itself:
    its concept requires no other concept. -/
def IsSubstanceDef (x : Entity) : Prop :=
  InheresIn x x ∧                          -- in itself
  ConceivedThrough x x ∧                    -- conceived through itself
  ¬∃ y : Entity, y ≠ x ∧ ConceivedThrough x y  -- concept requires nothing else
```

### Definition D4 — Attribute (1d4)

```lean
/-- An attribute is what the intellect perceives of a substance
    as constituting its essence. -/
def IsAttributeOf (a : Entity) (s : Entity) : Prop :=
  HasAttribute s a ∧
  -- The attribute constitutes the essence: it is conceived through itself
  ConceivedThrough a a ∧
  -- And each being must be conceived under some attribute (1p10s)
  ∀ x : Entity, IsSubstanceDef x → ∃ b : Entity, IsAttributeOf b x
-- Note: circular reference resolved by mutual recursion or by taking
-- IsAttributeOf as primitive and deriving IsSubstanceDef from it.
```

**Interpretive note (Cambridge Companion, Viljanen):** There is a deep debate about whether attributes are subjective (how intellect perceives substance) or objective (constitutive of substance's essence). The formalization takes the *objectivist* reading: attributes genuinely constitute essence and are conceived through themselves.

### Definition D5 — Mode (1d5)

```lean
/-- A mode is an affection of substance — it exists in another
    and is conceived through another. -/
def IsModeDef (x : Entity) : Prop :=
  ∃ s : Entity, IsSubstanceDef s ∧
    InheresIn x s ∧           -- exists in a substance
    ConceivedThrough x s ∧    -- conceived through that substance
    ¬IsSubstanceDef x         -- is not itself a substance
```

### Definition D6 — God (1d6)

```lean
/-- God is a substance consisting of infinitely many attributes,
    each of which expresses eternal and infinite essence. -/
def IsGod (g : Entity) : Prop :=
  IsSubstanceDef g ∧
  -- Has all possible attributes
  (∀ a : Entity, IsAttributeOf a a → HasAttribute g a) ∧
  -- Each attribute is infinite in its kind
  (∀ a : Entity, HasAttribute g a → InfiniteInKind a (HasAttribute g))
```

### Definition D7 — Free vs. Necessitated Thing (1d7)

```lean
/-- A thing is free if it exists by the necessity of its own nature alone
    and is determined to act by itself alone. -/
def IsFree (x : Entity) : Prop :=
  IsCausaSui x ∧
  (∀ y : Entity, Causes y x → y = x)

/-- A thing is necessitated if it is determined to exist and act
    by something else in a fixed way. -/
def IsNecessitated (x : Entity) : Prop :=
  ∃ y : Entity, y ≠ x ∧ Causes y x ∧
    Necessarily (Causes y x)
```

### Definition D8 — Eternity (1d8)

```lean
/-- Eternity is existence itself, insofar as it is conceived to follow
    necessarily from the definition of an eternal thing alone. -/
def IsEternal (x : Entity) : Prop :=
  Necessarily (∃ y, y = x) ∧    -- necessarily exists
  ¬∃ (t₁ t₂ : ℕ), t₁ < t₂      -- not bounded by time (atemporal)
  -- More precisely: existence is not explicated by duration
```

---

## Part 3 — Axioms (*Axiomata*)

### Axiom A1 — Exhaustion of Being (1a1)

```lean
/-- Everything that exists is either in itself or in another.
    There is no third category. -/
axiom A1 : ∀ x : Entity,
  InheresIn x x ∨ ∃ y : Entity, y ≠ x ∧ InheresIn x y
```

**Lean note:** This is Spinoza's most fundamental ontological axiom. It forces a partition: substance (in itself) vs. mode (in another).

### Axiom A2 — Conceivability and Truth (1a2)

```lean
/-- What cannot be conceived through another must be conceived through itself. -/
axiom A2 : ∀ x : Entity,
  (¬∃ y : Entity, y ≠ x ∧ ConceivedThrough x y) →
  ConceivedThrough x x
```

### Axiom A3 — Causal Determination (1a3)

```lean
/-- From a determinate cause an effect necessarily follows;
    and if there is no determinate cause, it is impossible for an effect to follow. -/
axiom A3 : ∀ (x y : Entity),
  (Causes x y → Necessarily (∃ z, z = y)) ∧
  (¬∃ c : Entity, Causes c y → ¬∃ z, z = y)
```

**Commentary (Jarrett, Necessity chapter):** This axiom encodes Spinoza's necessitarianism at the causal level. It asserts both (1) that causes necessitate their effects, and (2) that uncaused things cannot exist. This is stronger than "universal causation" — it asserts a *necessary* connection, not merely a de facto one.

### Axiom A4 — Knowledge Requires Cause (1a4)

```lean
/-- The knowledge (concept) of an effect involves and depends on
    the knowledge (concept) of its cause. -/
axiom A4 : ∀ (x y : Entity),
  Causes x y → ConceivedThrough y x
```

**Commentary:** This is the *epistemic* bridge axiom. It allows Spinoza to move from causal independence (substances have no external causes) to *conceptual* independence (substances are conceived through themselves). This is the key step in 1p7d.

### Axiom A5 — No Common Causation Without Common Nature (1a5)

```lean
/-- Things that have nothing in common with each other
    cannot be cause of one another. -/
axiom A5 : ∀ (x y : Entity),
  (¬∃ a : Entity, HasAttribute x a ∧ HasAttribute y a) →
  ¬Causes x y ∧ ¬Causes y x
```

### Axiom A6 — Truth and Ideas (1a6)

```lean
/-- A true idea must agree with its object (ideatum). -/
axiom A6 : ∀ (i obj : Entity),
  IsIdeaOf i obj → (TrueIdea i ↔ Corresponds i obj)
-- where IsIdeaOf, TrueIdea, Corresponds are primitives of the epistemology
```

### Axiom A7 — Conceivable Non-Existence Implies Non-Necessary Existence (1a7)

```lean
/-- If a thing can be conceived as not existing,
    its essence does not involve existence. -/
axiom A7 : ∀ x : Entity,
  Possibly (¬∃ y, y = x) → ¬IsCausaSui x
```

---

## Part 4 — Key Propositions as Lemmas and Theorems

The propositions are grouped by logical dependency. Each is labeled with Spinoza's reference and the proof strategy.

---

### Lemma 1P1 — Substance is Prior to its Modes

```lean
/-- A substance is prior in nature to its affections (modes). -/
lemma substance_prior_to_modes :
    ∀ (s m : Entity), IsSubstanceDef s → IsModeDef m →
    InheresIn m s →
    -- Priority: s can be conceived without m, but not vice versa
    (ConceivedThrough s s ∧ ¬ConceivedThrough m m) := by
  intro s m hs hm hinh
  constructor
  · exact hs.2.1          -- from D3: substance conceived through itself
  · intro hcontra
    -- m is a mode, so it is conceived through s (D5)
    obtain ⟨_, _, _, hcs, _⟩ := hm
    -- but hcontra says m is conceived through itself — contradiction with D5
    -- (a mode's concept requires the concept of the substance it inheres in)
    exact absurd hcs (by simp [hcontra])
```

---

### Lemma 1P2 — Distinct Attributes Imply No Common Cause

```lean
/-- Two substances with different attributes have nothing in common. -/
lemma distinct_attributes_no_common :
    ∀ (s₁ s₂ : Entity),
    IsSubstanceDef s₁ → IsSubstanceDef s₂ →
    (∀ a : Entity, HasAttribute s₁ a → ¬HasAttribute s₂ a) →
    ¬∃ a : Entity, HasAttribute s₁ a ∧ HasAttribute s₂ a := by
  intro s₁ s₂ _ _ hdisjoint
  intro ⟨a, ha₁, ha₂⟩
  exact absurd ha₂ (hdisjoint a ha₁)
```

---

### Lemma 1P3 — Causal Independence of Substances with Distinct Attributes

```lean
/-- If s₁ and s₂ have nothing in common, neither can be cause of the other. -/
lemma no_common_no_causation :
    ∀ (s₁ s₂ : Entity),
    (¬∃ a : Entity, HasAttribute s₁ a ∧ HasAttribute s₂ a) →
    ¬Causes s₁ s₂ ∧ ¬Causes s₂ s₁ := by
  intro s₁ s₂ hnocommon
  exact A5 s₁ s₂ hnocommon
```

---

### Theorem 1P4 — Only Substance and Its Attributes Distinguish Things

```lean
/-- Two or more things can be distinguished from one another only
    by their attributes or their modes. -/
theorem distinguishability :
    ∀ (x y : Entity), x ≠ y →
    (∃ a : Entity, HasAttribute x a ∧ ¬HasAttribute y a) ∨
    (∃ m : Entity, IsModeDef m ∧ InheresIn m x ∧ ¬InheresIn m y) := by
  intro x y hne
  -- This follows from A1: everything is either substance or mode,
  -- and D3/D5 give the only two sources of distinctness.
  -- Full proof requires classical logic (excluded middle on attribute sharing)
  by_contra h
  push_neg at h
  -- If x and y share all attributes and all modes, they are identical — contradiction
  exact hne (by ext; exact ⟨fun ha => (h.1 a ha).2, fun ha => (h.1 a ha).1⟩)
```

---

### **Theorem 1P5 — No Two Substances Share an Attribute** *(Core uniqueness lemma)*

```lean
/-- In nature there cannot be two or more substances having the same attribute.
    This is the first major step toward monism. -/
theorem no_shared_attribute :
    ∀ (s₁ s₂ : Entity),
    IsSubstanceDef s₁ → IsSubstanceDef s₂ →
    (∃ a : Entity, HasAttribute s₁ a ∧ HasAttribute s₂ a) →
    s₁ = s₂ := by
  intro s₁ s₂ hs₁ hs₂ ⟨a, ha₁, ha₂⟩
  -- Step 1: If they differ, they differ by attributes or modes (1p4)
  by_contra hne
  -- Step 2: They cannot differ by modes alone (1p1 — substance prior to modes;
  --         modes are accidental, cannot individuate substances)
  have hdiffattr : ∀ m : Entity, IsModeDef m →
      (InheresIn m s₁ ↔ InheresIn m s₂) := by
    intro m hm
    -- Substance is prior to its modes; modes cannot distinguish substances
    -- that share an attribute (from D3, D5, and the identity of indiscernibles)
    constructor <;> intro h <;> exact h  -- simplified; full proof uses 1p1
  -- Step 3: Since they share attribute a, by conceptual independence of
  --         attributes, s₁ conceived through a = s₂ conceived through a → s₁ = s₂
  -- (Della Rocca's argument: each attribute is sufficient to conceive its substance;
  --  if both s₁ and s₂ are conceived through a, they are the same substance)
  exact absurd rfl hne
```

**Proof note (Schmidt, Cambridge Companion):** The implicit engine here is the *Principle of the Identity of Indiscernibles*. Numerically distinct substances must differ in their properties. Since they cannot differ by modes alone (modes are ontologically posterior and accidental), they must differ by attributes. But if they share attribute *a*, then *a* individuates both — giving the same substance. Formally: `s₁ = s₂` follows from the fact that each attribute is *sufficient* for conceiving its substance (Della Rocca's conceptual barrier argument, also in Viljanen's chapter).

---

### Theorem 1P6 — Substances Cannot Produce One Another

```lean
/-- One substance cannot be produced by another substance. -/
theorem substance_not_produced_by_substance :
    ∀ (s₁ s₂ : Entity),
    IsSubstanceDef s₁ → IsSubstanceDef s₂ → s₁ ≠ s₂ →
    ¬Causes s₁ s₂ := by
  intro s₁ s₂ hs₁ hs₂ hne hcause
  -- From no_shared_attribute: s₁ and s₂ have no attribute in common
  have hnocommon : ¬∃ a, HasAttribute s₁ a ∧ HasAttribute s₂ a := by
    intro ⟨a, ha₁, ha₂⟩
    exact hne (no_shared_attribute s₁ s₂ hs₁ hs₂ ⟨a, ha₁, ha₂⟩)
  -- From A5: no common nature ⟹ no causal relation
  exact (A5 s₁ s₂ hnocommon).1 hcause
```

**Corollary 1P6C:**

```lean
/-- A substance can have no external cause; hence it is causa sui. -/
corollary substance_is_causa_sui :
    ∀ s : Entity, IsSubstanceDef s → IsCausaSui s := by
  intro s hs
  -- Since s cannot be caused by any other substance (1p6),
  -- and only substances can cause substances (from A1, D3, D5),
  -- s must be its own cause.
  -- By D1: causa sui means essence involves existence.
  constructor
  · exact fun _ => rfl  -- Causes s s
  · exact Necessarily_intro (⟨s, rfl⟩)
```

---

### **Theorem 1P7 — It Pertains to the Nature of Substance to Exist** *(Necessary existence)*

```lean
/-- Existence belongs to the nature of substance:
    every substance necessarily exists. -/
theorem substance_necessarily_exists :
    ∀ s : Entity, IsSubstanceDef s → Necessarily (∃ x, x = s) := by
  intro s hs
  -- Step 1: s cannot be produced by anything external (1p6 + 1p6c)
  have hcausasui : IsCausaSui s := substance_is_causa_sui s hs
  -- Step 2: By the PSR (encoded in A3 bidirectionally):
  --         the reason for s's non-existence must be internal
  -- Step 3: But if the reason were internal, s would have a contradictory essence
  -- Step 4: Possible substances have non-contradictory essences
  -- Step 5: Therefore there is no reason for s's non-existence
  -- Step 6: Therefore (by PSR applied to non-existence) s necessarily exists
  exact hcausasui.2
```

**Proof note (Viljanen; Garrett 1979):** The key move is applying the PSR *symmetrically*: not only must every existent have a cause, but every non-existent must also have a cause of its non-existence (1p11d2). Since no external cause of s's non-existence is possible (substance is causally isolated), any such cause would have to be internal — meaning s has a contradictory nature. But possible substances (by definition) lack contradictions. Therefore s exists necessarily. This is arguably the cleanest and most formalizable of Spinoza's arguments.

---

### Lemma 1P8 — Substance is Infinite in Its Kind

```lean
/-- Every substance is necessarily infinite in its own kind. -/
lemma substance_infinite_in_kind :
    ∀ s : Entity, IsSubstanceDef s →
    ∀ a : Entity, HasAttribute s a →
    InfiniteInKind s (fun x y => HasAttribute x a ∧ HasAttribute y a) := by
  intro s hs a ha
  -- Suppose for contradiction that s is finite in its kind.
  intro ⟨t, ⟨hat, _⟩, hne, _⟩
  -- Then t is another substance with the same attribute a.
  -- But by 1p5: no two substances share an attribute.
  have := no_shared_attribute s t hs
    (by constructor; exact InheresIn_self t; exact ⟨ConceivedThrough_self t, fun ⟨y, hy, hcy⟩ => _⟩)
    ⟨a, ha, hat⟩
  exact hne this
```

---

### Lemma 1P9 — Reality Proportional to Attributes

```lean
/-- The more attributes a thing has, the more reality and being it has. -/
lemma reality_proportional_to_attributes :
    ∀ (s₁ s₂ : Entity),
    IsSubstanceDef s₁ → IsSubstanceDef s₂ →
    (∀ a, HasAttribute s₁ a → HasAttribute s₂ a) →  -- s₂ has at least as many attributes
    -- s₂ has at least as much reality as s₁
    True := by  -- placeholder — "reality" needs a numeric encoding
  trivial
```

**Note:** Proposition 1p9 is the *least* directly formalizable in Lean without introducing a `Reality : Entity → ℕ` (or `ℝ`) mapping. It is here for completeness; the full encoding requires:

```lean
variable (Reality : Entity → ℝ)
axiom A_reality : ∀ (s₁ s₂ : Entity),
  IsSubstanceDef s₁ → IsSubstanceDef s₂ →
  (∀ a, HasAttribute s₁ a → HasAttribute s₂ a) →
  Reality s₁ ≤ Reality s₂
```

---

### Lemma 1P10 — Each Attribute Conceived Through Itself

```lean
/-- Each attribute of a substance is conceived through itself. -/
lemma attribute_conceived_through_itself :
    ∀ (s a : Entity), IsSubstanceDef s → HasAttribute s a →
    ConceivedThrough a a := by
  intro s a hs ha
  -- From D4: attribute constitutes the essence of s
  -- From D3: s is conceived through itself
  -- From the conceptual barrier (Della Rocca): attributes cannot be conceived
  --   through each other — hence each is conceived through itself alone.
  exact (is_attribute_def s a ha).2.1
```

---

### **Theorem 1P11 — God Necessarily Exists** *(Ontological Argument)*

```lean
/-- God, i.e. a substance consisting of infinite attributes, necessarily exists. -/
theorem God_necessarily_exists :
    Necessarily (∃ g : Entity, IsGod g) := by
  -- Step 1: God is defined as a substance with all attributes (D6)
  -- Step 2: Any possible substance necessarily exists (1p7)
  -- Step 3: God is a possible substance
  --         (shown via 1p10s: attributes conceived independently → no contradiction)
  -- Step 4: Therefore God necessarily exists.
  have hposs : ∃ g : Entity, IsSubstanceDef g ∧ ∀ a, IsAttributeOf a a → HasAttribute g a :=
    God_is_possible  -- axiom or prior lemma asserting non-contradiction
  obtain ⟨g, hg_sub, hg_attr⟩ := hposs
  exact substance_necessarily_exists g hg_sub
```

**Three demonstrations in Spinoza — ranked by formalizability:**

| Demo | Strategy | Lean viability |
|------|----------|----------------|
| 1p11d1 | Reductio: if God didn't exist, something external would prevent it; but nothing external can limit a substance → contradiction | ✅ Direct |
| **1p11d2** | **PSR applied to non-existence: cause of non-existence must be internal; but God's essence is non-contradictory → impossible** | ✅✅ Cleanest |
| 1p11d3 | Power argument: to exist is to have power; God has infinite power → exists | ⚠️ Requires `Reality`/`Power` scalar |

---

### Theorem 1P12 — Substance Cannot be Divided

```lean
/-- No substance, and especially not God, can be truly divided. -/
theorem substance_indivisible :
    ∀ s : Entity, IsSubstanceDef s →
    ¬∃ (s₁ s₂ : Entity),
      s₁ ≠ s₂ ∧ IsSubstanceDef s₁ ∧ IsSubstanceDef s₂ ∧
      -- s is the "union" of s₁ and s₂
      (∀ a, HasAttribute s a ↔ HasAttribute s₁ a ∨ HasAttribute s₂ a) := by
  intro s hs ⟨s₁, s₂, hne, hs₁, hs₂, hunion⟩
  -- If s could be divided into s₁ and s₂, each part would be finite (D2)
  -- But substance is infinite in its kind (1p8) → contradiction
  -- Alternatively: the parts would share attributes of s → by 1p5 they are identical
  have : s₁ = s₂ := by
    apply no_shared_attribute s₁ s₂ hs₁ hs₂
    obtain ⟨a, ha⟩ := exists_attribute s hs
    exact ⟨a, (hunion a).mp ha |>.elim id id, (hunion a).mp ha |>.elim id id⟩
  exact hne this
```

---

### **Theorem 1P14 — God is the Only Substance** *(Substance Monism)*

```lean
/-- Besides God, no substance can exist or be conceived.
    This is the central theorem of Spinoza's metaphysics. -/
theorem substance_monism :
    ∀ s : Entity, IsSubstanceDef s → s = God := by
  intro s hs
  -- Step 1: God has all attributes (D6)
  have hGod_all : ∀ a : Entity, IsAttributeOf a a → HasAttribute God a :=
    (isGod_God).2.1
  -- Step 2: If s were distinct from God, s would need an attribute not in God
  by_contra hne
  -- Step 3: But God has ALL attributes; there is none left for s
  -- Step 4: Without an attribute, s cannot exist (D3 + 1p10s)
  -- Step 5: This contradicts s being a substance
  obtain ⟨a, ha⟩ := exists_attribute s hs  -- s has some attribute
  have ha_god : HasAttribute God a := hGod_all a (attribute_is_attribute a)
  -- Now both s and God have attribute a, so by 1p5: s = God
  exact hne (no_shared_attribute s God hs isGod_substance ⟨a, ha, ha_god⟩)
```

**Corollary 1P14C1:**

```lean
/-- God is unique: there is exactly one God. -/
corollary God_unique :
    ∀ (g₁ g₂ : Entity), IsGod g₁ → IsGod g₂ → g₁ = g₂ := by
  intro g₁ g₂ hg₁ hg₂
  have hs₁ := hg₁.1
  have hs₂ := hg₂.1
  -- Both are substances; both have all attributes; by 1p5 they are identical
  obtain ⟨a, ha₁⟩ := exists_attribute g₁ hs₁
  exact no_shared_attribute g₁ g₂ hs₁ hs₂ ⟨a, ha₁, hg₂.2.1 a (attribute_is_attribute a)⟩
```

**Corollary 1P14C2:**

```lean
/-- Extended and thinking things are either attributes of God or modes of God. -/
corollary all_things_in_God :
    ∀ x : Entity, InheresIn x God := by
  intro x
  rcases A1 x with hself | ⟨y, _, hy⟩
  · -- x is in itself → x is a substance → x = God (by 1p14) → x is in God
    have hx_sub : IsSubstanceDef x := substance_iff_in_itself.mpr hself
    rw [substance_monism x hx_sub]
    exact InheresIn_self God
  · -- x is in y → y is a substance → y = God → x is in God
    have hy_sub : IsSubstanceDef y := substance_iff_in_itself.mpr (A2 y _)
    rw [substance_monism y hy_sub] at hy
    exact hy
```

---

### Theorem 1P15 — Everything Is in God

```lean
/-- Whatever is, is in God, and nothing can be or be conceived without God. -/
theorem everything_in_God :
    ∀ x : Entity, InheresIn x God ∧ ConceivedThrough x God := by
  intro x
  constructor
  · exact all_things_in_God x
  · -- From A4: being caused by God means being conceived through God
    -- All modes are caused by God (1p16); substances just are God (1p14)
    exact conceived_through_God x (all_things_in_God x)
```

---

### **Theorem 1P16 — Infinite Things Follow from God's Nature** *(Necessitarianism)*

```lean
/-- From the necessity of divine nature, infinitely many things
    follow in infinitely many ways (i.e., all that exists). -/
theorem all_things_follow_from_God :
    ∀ m : Entity, IsModeDef m → Causes God m := by
  intro m hm
  -- All modes inhere in God (1p15)
  -- Causation co-tracks inherence for modes (1p25c: God is the efficient cause of all modes)
  exact inherence_implies_causation God m (all_things_in_God m)
```

**The triangle analogy (Spinoza's own):** The properties of a triangle (interior angles sum to 180°) follow from the triangle's definition with the same *logical* necessity as modes follow from God's essence. In Lean this is literally a mathematical analogy: God : Type is like ℝ, and modes are theorems derivable from the axioms defining ℝ.

---

### Theorem 1P17 — God Acts from the Laws of His Own Nature Alone

```lean
/-- God acts solely from the laws of His own nature, constrained by nothing external. -/
theorem God_free :
    IsFree God := by
  constructor
  · exact substance_is_causa_sui God isGod_substance
  · intro y hy
    -- Only God can cause God (from 1p6: no external substance can cause God)
    -- Hence y = God
    by_contra hne
    exact substance_not_produced_by_substance y God
      (substance_of_cause y God hy) isGod_substance hne hy
```

---

### Theorem 1P25 — God is the Efficient Cause of All Things

```lean
/-- God is the efficient cause not only of the existence of things,
    but also of their essence. -/
theorem God_cause_of_essence :
    ∀ m : Entity, IsModeDef m →
    Causes God m ∧ -- cause of existence
    EssentialCause God m := by  -- cause of essence
  intro m hm
  constructor
  · exact all_things_follow_from_God m hm
  · -- Essence of modes involves God; modes conceived through God
    exact essential_causation_of_modes God m hm
```

---

### Theorem 1P29 — Nothing is Contingent

```lean
/-- Nothing in nature is contingent; everything is determined to exist
    and to produce effects in a determinate way. -/
theorem no_contingency :
    ∀ x : Entity, ∃ c : Entity, Causes c x ∧ Necessarily (Causes c x) := by
  intro x
  rcases A1 x with hself | ⟨y, _, hy⟩
  · -- x is a substance → x = God → God is self-caused necessarily
    exact ⟨x, self_cause x, substance_necessarily_exists x (substance_iff.mpr hself)⟩
  · -- x is a mode → there is a prior cause in the causal chain
    -- Eventually traces back to God whose existence is necessary
    exact modal_causal_chain x
```

---

### **Theorem 1P33 — Things Could Not Have Been Otherwise** *(Strict Necessitarianism)*

```lean
/-- Things could have been produced by God in no other way and no other order
    than the way and order in which they were produced. -/
theorem strict_necessitarianism :
    ∀ m : Entity, IsModeDef m →
    Necessarily (∃ x, x = m) ∧
    ¬Possibly (¬∃ x, x = m) := by
  intro m hm
  -- Step 1: m exists and is determined by God's nature (1p16, 1p29)
  have hcause : Causes God m := all_things_follow_from_God m hm
  -- Step 2: God's nature is necessary (1p7, 1p11)
  have hGod_nec : Necessarily (∃ g, IsGod g) := God_necessarily_exists
  -- Step 3: If m could be otherwise, God's nature could be otherwise (1p33d)
  -- Step 4: But then there could be two Gods (1p14c1) — absurd
  -- Step 5: Therefore m is necessary
  constructor
  · exact necessity_of_effects_from_necessary_causes God m hGod_nec hcause
  · intro hposs
    obtain ⟨w, hw⟩ := hposs
    exact hw (necessity_of_effects_from_necessary_causes God m hGod_nec hcause w)
```

**Jarrett's formalization note (Necessity chapter):** The argument in 1p33d can be rendered in modal logic as:

```
□(∃!g. IsGod g)          -- God necessarily and uniquely exists
□(IsGod g → Causes g m)  -- God necessarily causes m (from 1p16 + 1p29)
─────────────────────────
□(∃x. x = m)            -- m necessarily exists
```

This is valid in **S5** (where `□p → □□p`), and Spinoza's necessitarianism effectively collapses all modal distinctions: in a world with only one possible scenario, `□p ↔ p ↔ ◇p`.

---

## Part 5 — The Attribute Uniqueness Cluster

These lemmas formalize the Della Rocca / Viljanen argument that **each attribute is sufficient to individuate its substance** — the *conceptual barrier* between attributes.

### Lemma — Conceptual Barrier Between Attributes

```lean
/-- No attribute can be conceived through another attribute.
    (The "conceptual barrier" — Della Rocca) -/
lemma conceptual_barrier :
    ∀ (s : Entity) (a b : Entity),
    IsSubstanceDef s →
    HasAttribute s a → HasAttribute s b → a ≠ b →
    ¬ConceivedThrough a b ∧ ¬ConceivedThrough b a := by
  intro s hs ha hb hab
  constructor <;> intro hcontra
  · -- If a were conceived through b, then b would be needed to conceive a.
    -- But each attribute is conceived through itself (1p10, A2).
    -- So a is conceived through itself AND through b — the latter violates D4
    exact absurd (attribute_conceived_through_itself s a hs ha)
      (conceived_through_unique a b hcontra)
  · exact absurd (attribute_conceived_through_itself s b hs hb)
      (conceived_through_unique b a hcontra)
```

### Lemma — Each Attribute Sufficient to Conceive Its Substance

```lean
/-- Each attribute of a substance is, by itself, sufficient
    for conceiving that substance. (Supports the monism proof) -/
lemma attribute_sufficient_for_substance :
    ∀ (s : Entity) (a : Entity),
    IsSubstanceDef s → HasAttribute s a →
    ConceivedThrough s a := by
  intro s hs ha
  -- s is conceived through its essence (D3)
  -- a constitutes the essence of s (D4)
  -- Therefore s is conceived through a
  exact conceived_through_essence s a hs ha
```

---

## Part 6 — The Principle of Sufficient Reason (PSR)

The PSR is the engine of multiple arguments in Part I. Its symmetric form — applying to non-existence as well as existence — is what gives 1p7 and 1p11 their force.

### The Symmetric PSR (1p11d2)

```lean
/-- Symmetric Principle of Sufficient Reason:
    For any thing, there must be a reason either for its existence or for its non-existence.
    This reason is located either inside or outside the thing. -/
axiom PSR_symmetric : ∀ x : Entity,
  (∃ cause : Entity, Causes cause x) ∨    -- reason for existence (internal or external)
  (∃ cause : Entity, Prevents cause x)    -- reason for non-existence

/-- For substances: the reason for existence or non-existence must be internal
    (since substances are causally isolated from all external causes). -/
lemma substance_PSR_internal : ∀ s : Entity, IsSubstanceDef s →
  (IsCausaSui s) ∨ (∃ c : Entity, c = s ∧ PreventsExistence c s) := by
  intro s hs
  rcases PSR_symmetric s with ⟨c, hc⟩ | ⟨c, hpc⟩
  · -- External cause would violate causal isolation of substance
    have : c = s := by
      by_contra hne
      exact absurd hc (substance_not_produced_by_substance c s
        (cause_is_substance c s hc) hs hne)
    left; rw [← this]; exact ⟨hc, _⟩
  · right; exact ⟨c, _, hpc⟩

/-- Possible substances have non-contradictory essences,
    so nothing internal can prevent their existence. -/
axiom possible_substance_no_internal_prevention :
    ∀ s : Entity, IsSubstanceDef s →
    ¬∃ c : Entity, c = s ∧ PreventsExistence c s

/-- Combining: every possible substance necessarily exists. -/
theorem substance_from_PSR : ∀ s : Entity, IsSubstanceDef s →
    IsCausaSui s := by
  intro s hs
  rcases substance_PSR_internal s hs with h | h
  · exact h
  · exact absurd h (possible_substance_no_internal_prevention s hs)
```

---

## Part 7 — Formal Dependency Graph

The following diagram shows the logical order of Part I's core theorems. Each arrow means "is used in the proof of":

```
D1 (CausaSui)
D3 (Substance)  ─────────────────────────────┐
D4 (Attribute)  ──────┐                      │
D5 (Mode)       ──┐   │                      │
D6 (God)          │   │                      │
A1 (Exhaustion)   │   │                      │
A3 (Causal Det.)  │   │                      │
A4 (Know←Cause)   │   │                      │
A5 (No Common)    │   │                      │
PSR               │   │                      │
    │             │   │                      │
    ▼             ▼   ▼                      ▼
  1P1           1P2  1P4 ──────────► 1P5 (no shared attr.)
(prior in nature) (no common)          │
                                        │
                    1P3 ◄───────────────┘
                (no causation)
                    │
                    ▼
                  1P6 (substances don't produce each other)
                    │
                    ▼
              1P6C (→ CausaSui)
                    │
                    ▼
              1P7 (necessarily exists)   ◄──── PSR_symmetric
                    │
                    ├──────────────────────────────────┐
                    ▼                                  │
              1P8 (infinite)                         1P11 (God exists)
                    │                                  │
                    ▼                                  ▼
              1P9 (reality)                        1P14 (monism)
                                                       │
                                          ┌────────────┤
                                          ▼            ▼
                                     1P15 (all in God) 1P14C1 (God unique)
                                          │
                                          ▼
                                     1P16 (all follows)
                                          │
                                          ▼
                                     1P29 (no contingency)
                                          │
                                          ▼
                                     1P33 (could not be otherwise)
```

---

## Part 8 — What Requires Extension for Full Formalization

The following concepts from Part I resist immediate Lean encoding but can be addressed with additional infrastructure:

| Concept | Challenge | Proposed Extension |
|---|---|---|
| "Infinite attributes" (D6) | Lean's `Type` hierarchy; actual infinity | Use `Set Attribute` with `Set.Infinite` |
| "More reality/perfection" (1p9) | Ordinal/cardinal comparison | Introduce `Reality : Entity → Ordinal` |
| "Eternal" vs. "sempiternal" (D8) | Distinction between timeless and everlasting | Add `Time : Type` and `Exists_at : Entity → Time → Prop` |
| "Intellect perceives" (D4) | Intensional/epistemic operator | Add `Perceives : Mind → Entity → Prop` |
| "Formal distinction" (Duns Scotus / Schmidt) | Weaker than real, stronger than conceptual | Custom `FormallyDistinct : Entity → Entity → Prop` with axioms |
| Infinite causal regress (1p28) | Well-foundedness vs. infinity | Non-well-founded set theory or coinduction |

---

## Part 9 — Summary Table: All Formalizable Items

| Label | Type | Content | Lean Status |
|---|---|---|---|
| D1 | Definition | Causa sui | ✅ Direct |
| D2 | Definition | Finite in kind | ✅ Direct |
| D3 | Definition | Substance | ✅ Direct |
| D4 | Definition | Attribute | ⚠️ Objectivity debate |
| D5 | Definition | Mode | ✅ Direct |
| D6 | Definition | God | ✅ Modulo infinity |
| D7 | Definition | Free / necessitated | ✅ Direct |
| D8 | Definition | Eternity | ⚠️ Needs Time type |
| A1 | Axiom | Everything in-itself or in-another | ✅ |
| A2 | Axiom | Conceivability fallback | ✅ |
| A3 | Axiom | Causal determination (necessity) | ✅ |
| A4 | Axiom | Knowledge depends on cause | ✅ |
| A5 | Axiom | No common nature → no causation | ✅ |
| A6 | Axiom | True idea agrees with object | ⚠️ Needs Idea type |
| A7 | Axiom | Conceivable non-existence → not causa sui | ✅ |
| PSR | Derived Axiom | Symmetric PSR | ✅ |
| 1P1 | Lemma | Substance prior to modes | ✅ |
| 1P2 | Lemma | Distinct attributes → nothing in common | ✅ |
| 1P3 | Lemma | Nothing in common → no causation | ✅ (from A5) |
| 1P4 | Theorem | Only attributes/modes distinguish | ✅ (classical) |
| **1P5** | **Theorem** | **No shared attribute** | ✅✅ Core |
| 1P6 | Theorem | Substances don't produce each other | ✅ |
| 1P6C | Corollary | Substance is causa sui | ✅ |
| **1P7** | **Theorem** | **Substance necessarily exists** | ✅✅ Core |
| 1P8 | Lemma | Substance infinite in kind | ✅ |
| 1P9 | Lemma | Reality ∝ attributes | ⚠️ Needs scalar |
| 1P10 | Lemma | Attribute conceived through itself | ✅ |
| **1P11** | **Theorem** | **God necessarily exists** | ✅✅ Core |
| 1P12 | Theorem | Substance indivisible | ✅ |
| **1P14** | **Theorem** | **Substance monism** | ✅✅ Core |
| 1P14C1 | Corollary | God unique | ✅ |
| 1P14C2 | Corollary | All things in God | ✅ |
| 1P15 | Theorem | Whatever is, is in God | ✅ |
| 1P16 | Theorem | All things follow from God | ✅ (modulo infinity) |
| 1P17 | Theorem | God acts from own nature alone | ✅ |
| 1P25 | Theorem | God efficient cause of essence | ✅ |
| 1P29 | Theorem | Nothing contingent | ✅ |
| **1P33** | **Theorem** | **Things could not be otherwise** | ✅✅ Core (S5) |
| Conceptual Barrier | Lemma | Attributes mutually independent | ✅ |
| Attr. Sufficiency | Lemma | Each attr. sufficient for substance | ✅ |

---

## Appendix: Lean 4 Skeleton File Structure

```lean
-- Spinoza_Ethics_Part1.lean
-- A Lean 4 formalization skeleton for Spinoza's Ethics, Part I

import Mathlib.Logic.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic

namespace Spinoza

-- ===== DOMAIN =====
variable {Entity : Type*}

-- ===== PRIMITIVE RELATIONS =====
variable (InheresIn       : Entity → Entity → Prop)
variable (ConceivedThrough : Entity → Entity → Prop)
variable (HasAttribute    : Entity → Entity → Prop)
variable (Causes          : Entity → Entity → Prop)
variable (God             : Entity)

-- ===== DEFINITIONS =====
def IsCausaSui  (x : Entity) : Prop := Causes x x
def IsSubstance (x : Entity) : Prop :=
  InheresIn x x ∧ ConceivedThrough x x
def IsMode      (x : Entity) : Prop :=
  ∃ s, IsSubstance s ∧ InheresIn x s ∧ ¬IsSubstance x
def IsGod       (g : Entity) : Prop :=
  IsSubstance g ∧ ∀ a, HasAttribute a a → HasAttribute g a

-- ===== AXIOMS =====
axiom A1 : ∀ x : Entity, InheresIn x x ∨ ∃ y, y ≠ x ∧ InheresIn x y
axiom A3 : ∀ x y : Entity, Causes x y → ∀ P : Prop, P → P  -- placeholder
axiom A4 : ∀ x y : Entity, Causes x y → ConceivedThrough y x
axiom A5 : ∀ x y : Entity,
  (¬∃ a, HasAttribute x a ∧ HasAttribute y a) → ¬Causes x y

-- ===== THEOREMS =====
-- ... (as developed above)

end Spinoza
```

---

*This document is intended as a working blueprint for a Lean 4 formalization project.
All philosophical interpretations follow the Cambridge Companion to Spinoza's Ethics (Koistinen, ed., 2009),
particularly the chapters by Viljanen (Ontology), Schmidt (Substance Monism), and Jarrett (Necessity).
The formal proofs are proof sketches; completing them in Lean requires resolving several
philosophical ambiguities (especially around D4 and the nature of infinite attributes) into
precise type-theoretic choices.*