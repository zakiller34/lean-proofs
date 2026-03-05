Here is a formal analysis of **Chapter 3: Spinoza’s Ontology**, written by Valtteri Viljanen.

This analysis reconstructs Viljanen’s exposition of Spinoza’s metaphysics, translating the prose into a formalized system of ontological dependence, individuation, and causation.

***

# Formal Analysis of Spinoza’s Ontology

## I. The Fundamental Categories: Subsistence and Inherence

Viljanen argues that Spinoza’s radical conclusions rest upon a conservative, traditional Aristotelian/Cartesian categorical framework. The primary distinction is between that which exists on its own and that which exists in another.

Let the Domain of Discourse ($D$) be all that exists.
We define two primitive relations:
1.  **Ontological Inherence ($I(x, y)$):** Entity $x$ exists in entity $y$.
2.  **Conceptual Dependence ($C(x, y)$):** Concept $x$ is conceived through concept $y$.

### 1.1 Definition of Substance ($S$)
A Substance is an entity that is ontologically and conceptually independent.
$$ \forall x \in D, S(x) \iff [I(x, x) \land C(x, x)] $$
*   *Interpretation:* "In itself" ($in se$) and "conceived through itself" ($per se concipitur$).

### 1.2 Definition of Mode ($M$)
A Mode is an entity that is ontologically and conceptually dependent on a Substance.
$$ \forall x \in D, M(x) \iff \exists y [S(y) \land I(x, y) \land C(x, y) \land x \neq y] $$
*   *Interpretation:* Modes are "affections" or properties. They do not subsist; they inhere.
*   *Viljanen’s Thesis:* Contra Curley (who views the mode-substance relation as purely causal), Viljanen argues Spinoza retains the traditional notion of **inherence**. Finite things are predicated of God.

## II. The Attribute Function and Individuation

The definition of Attribute (1d4) introduces the problem of the relationship between the intellect and reality.

### 2.1 The Objectivity of Attributes
Let $Att(a, s)$ denote "$a$ is an attribute of substance $s$."
Spinoza’s definition: $a$ is what the intellect perceives of $s$ as constituting the essence of $s$.

**The Subjectivist Interpretation (Rejected):** Attributes are merely artifacts of perception.
**The Objectivist Interpretation (Accepted by Viljanen):** Perception tracks reality.
$$ P(Intellect, \phi) \implies \phi \text{ is Real} $$
Therefore, if the intellect perceives $a$ as the essence of $s$, then $a$ *is* the essence of $s$.

### 2.2 The Identity of Substance and Attribute
How can a simple Substance have multiple Attributes?
Viljanen endorses Koistinen’s predicative analysis.
Let $E$ be an essence/attribute.
The statement is not merely "$S$ has $E$," but rather the identity statement:
$$ S \equiv E $$
However, because ideas are affirmations (judgments), the idea of Substance involves the affirmation of the Attribute.
$$ Idea(S) \iff Idea(S \text{ is } E) $$
*Conclusion:* Substance and Attribute are numerically identical entities referenced through distinct conceptual operations.

### 2.3 The No-Shared-Attribute Theorem (1p5)
This is the engine of Spinoza’s Monism.
Let $S_1$ and $S_2$ be distinct substances.
Let $\Phi(x)$ be the set of attributes of $x$.

**Principle of Identity of Indiscernibles (PII):**
$$ (\Phi(S_1) = \Phi(S_2)) \implies (S_1 = S_2) $$

**Argument:**
1.  Substances cannot be distinguished by Modes (since Modes are posterior to Substance).
2.  Substances must be distinguished by Attributes (Essence).
3.  If $S_1$ and $S_2$ share an attribute $A$, they cannot be distinguished by $A$.
4.  Therefore, if $S_1$ and $S_2$ share $A$, they are identical.
$$ \therefore \neg \exists x, y [S(x) \land S(y) \land x \neq y \land (\Phi(x) \cap \Phi(y) \neq \emptyset)] $$

## III. The Derivation of Monism (The Existence Function)

Spinoza bridges the gap between concepts and reality using the Principle of Sufficient Reason (PSR).

### 3.1 The Necessary Existence of Substance
**The PSR Formulation (1p11d2):** For every thing $x$, there must be a cause/reason ($R$) for its existence ($E!$) or non-existence ($\neg E!$).
$$ \forall x [\exists R (R \implies E!(x)) \lor \exists R (R \implies \neg E!(x))] $$

**Proof of 1p7 (Substance exists necessarily):**
1.  $S$ cannot be caused by external $S'$ (due to lack of shared attributes/conceptual connection).
2.  Therefore, the reason for $S$'s existence must be internal (Self-Caused / *Causa Sui*).
3.  Internal reason $\implies$ Essence involves Existence.
$$ S(x) \implies \Box E!(x) $$
*(Where $\Box$ denotes metaphysical necessity).*

### 3.2 The Monism Proof (1p14)
1.  Define God ($G$) as a substance consisting of infinite attributes (all possible attributes).
    $$ \forall A [Possible(A) \implies A \in \Phi(G)] $$
2.  God exists necessarily (by 3.1).
3.  Suppose a substance $S_{other}$ exists distinct from $G$.
4.  $S_{other}$ must possess some attribute $A_k$.
5.  But $A_k \in \Phi(G)$ (since God has *all* attributes).
6.  Therefore, $S_{other}$ and $G$ share an attribute.
7.  By 1p5 (No shared attributes), $S_{other} = G$.
8.  **Conclusion:** Only one substance exists.

## IV. The Status of Finite Things (Modes)

If only God exists as a substance, what is the ontological status of humans, trees, and rocks?

### 4.1 From Independence to Dependence
Finite things are Modes ($M$).
$$ \forall x (x \neq G \implies M(x)) $$
This implies a radical **Property Theory of Particulars**:
*   Finite things are not self-subsistent subjects.
*   Finite things are "adjectives" or predicates of God.
*   $Human(x) \rightarrow God \text{ is } human\text{-ish here and now.}$

### 4.2 Inherence vs. Causation
Viljanen addresses the debate on whether the relation between God and World is purely causal.
*   **Thesis:** It is both.
    1.  **Inherence:** $M$ is *in* $S$. (Ontological dependence).
    2.  **Causation:** $S$ produces $M$. (Dynamic production).
*   **The Spinozistic Synthesis:** The essence of God is **Power** (*Potentia*).
    *   Inhering in God means participating in God’s power.
    *   God does not just "contain" modes like a vessel; God "expresses" modes like a force.

## V. Epistemology of Ontology

How do finite minds grasp this ontology?

### 5.1 The "Top-Down" Cognitive Requirement
*   Knowledge of the Effect ($M$) involves knowledge of the Cause ($S$) (1a4).
*   Therefore, any idea of a finite thing involves the idea of God.
*   **Cognitive Accessibility:** God is not a hidden mystery; God is the immediate background of every thought. To think "table" is to think "Extension modified table-wise," which is to think "God modified table-wise."

***

# Glossary of Formalized Concepts

**Substance ($Substantia$)**
*Definition:* That which is in itself and conceived through itself.
*Formal Role:* The independent variable of reality. The domain of subsistence. In Spinoza's system, the set containing only $\{God\}$.

**Mode ($Modus$)**
*Definition:* That which is in another and conceived through another.
*Formal Role:* The dependent variable. Affections or states of a substance. All finite things (humans, thoughts, bodies) are elements of this set. They act as properties predicated of Substance.

**Attribute ($Attributum$)**
*Definition:* What the intellect perceives of substance as constituting its essence.
*Nuance:* Viljanen emphasizes the **objective** reading. Attributes are not illusions or mere perspectives; they are the real, distinct lines of force (essence) of the single Substance. (e.g., Extension, Thought).

**Inherence ($Inesse$)**
*Definition:* The ontological relation of "being in."
*Nuance:* Traditional Scholastic term for the relationship of accident to substance. Spinoza applies this to the relationship of World to God. The world "inheres" in God.

**Causa Sui**
*Definition:* Cause of self.
*Formal Meaning:* An entity whose essence entails existence ($Essence \implies Existence$). It is not temporal self-creation, but logical necessity.

**Principle of Sufficient Reason (PSR)**
*Definition:* The axiom that for every fact, there is a reason why it is so and not otherwise.
*Role:* The logical engine that forces Spinoza from the *possibility* of Substance to the *necessity* of Substance, and eventually to strict Determinism.

**Monism**
*Definition:* The thesis that $|\{S\}| = 1$.
*Derivation:* Derived from the definition of God (infinite attributes) and the prohibition on shared attributes. If God has all attributes, no "attribute-space" is left for another substance.

**Potentia (Power)**
*Definition:* The actual essence of God/Substance.
*Nuance:* Ontology is dynamic. To "be" is to have causal power. Modes are not static furniture of the universe; they are varying degrees of intensity of God’s power.