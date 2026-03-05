Here is a formal analysis of **Chapter 4: Substance Monism and Identity Theory in Spinoza**, written by Andreas Schmidt.

This analysis reconstructs Schmidt’s argument using logic and set theory to formalize the relationship between Spinoza’s theological monism and his solution to the Mind-Body problem via the medieval logic of Duns Scotus.

***

# Formal Analysis: Monism, Simplicity, and the Formal Distinction

## I. The Derivation of Substance Monism

Schmidt begins by analyzing Spinoza’s proof that God is the *only* substance ($1p14$). This relies on the "No-Shared-Attribute" theorem ($1p5$).

**Definitions:**
Let $S$ be the set of all Substances.
Let $\mathbb{A}$ be the set of all Attributes.
Let $Att(x)$ be the set of attributes possessed by substance $x$.

**Axiom (Identity of Indiscernibles - PII):**
$$ \forall x, y \in S: (Att(x) = Att(y)) \implies (x = y) $$

### 1.1 The Challenge to 1p5
**Spinoza’s Thesis ($1p5$):** Substances cannot share an attribute.
$$ \forall x, y \in S: (Att(x) \cap Att(y) \neq \emptyset) \implies (x = y) $$

**The Leibnizian Objection:**
Assume substance $x$ has attributes $\{A_1, A_2\}$ and substance $y$ has $\{A_2, A_3\}$.
They share $A_2$, yet $Att(x) \neq Att(y)$. Therefore, by PII, $x \neq y$.
This allows for pluralism despite shared attributes.

### 1.2 Spinoza’s Defense (The Nature of Essence)
Schmidt argues Spinoza defends $1p5$ by redefining the relationship between Attribute and Essence.
Let $E(x)$ be the essence of $x$.

**Premise 1 (Simplicity of Essence):** An attribute constitutes the *entire* essence of a substance, not a part.
$$ \forall A \in Att(x): A \equiv E(x) $$

**Premise 2 (Uniqueness of Essence):** A substance cannot have two distinct essences. Therefore, if a substance has multiple attributes, those attributes must be identical in their function as essence.

**The Counter-Argument to Leibniz:**
1.  Assume $x$ has $\{A_1, A_2\}$ and $y$ has $\{A_2, A_3\}$.
2.  If $A_2 \in Att(x)$, then $A_2 \equiv E(x)$.
3.  If $A_2 \in Att(y)$, then $A_2 \equiv E(y)$.
4.  Therefore, $E(x) \equiv E(y)$.
5.  If essences are identical, the substances are identical.
6.  Therefore, $x = y$.
$$ \therefore \text{No shared attributes without identity.} $$

**The Monism Proof ($1p14$):**
1.  God ($G$) possesses all attributes ($Att(G) = \mathbb{A}$).
2.  If any other substance $S'$ exists, it must possess some attribute $A_k$.
3.  Since $G$ has *all* attributes, $A_k \in Att(G)$.
4.  $S'$ and $G$ share $A_k$.
5.  By $1p5$, $S' = G$.
6.  Conclusion: $\forall x \in S, x = G$.

## II. The Simplicity Paradox

If Monism holds, Spinoza faces a contradiction regarding Divine Simplicity.

**The Paradox:**
1.  **Simplicity:** God is absolutely simple (non-composite). $$ Sim(G) \implies \neg \exists \text{ parts in } G $$
2.  **Identity of Properties:** In a simple being, the subject and its properties are identical.
    $$ \forall P \in Properties(G): P = G $$
3.  **Multiplicity:** God has distinct attributes (Thought $\neq$ Extension).
    $$ T \in Att(G), E \in Att(G), T \neq E $$
4.  **Transitivity Failure:** If $T = G$ and $E = G$, then $T = E$. But Thought is not Extension.

**Possible Solutions (Rejected):**
*   *Equivocity:* God's attributes share only a name with human properties. (Rejected: Spinoza requires univocity for intelligibility).
*   *Subjectivism:* Attributes are merely how distinct minds *view* God. (Rejected: Attributes express the *real* essence of God, independent of observers).

## III. The Solution: The *Distinctio Formalis* (Formal Distinction)

Schmidt proposes that Spinoza adopts the logic of **Duns Scotus** to resolve the paradox. This requires splitting the concept of "Distinction" and "Identity."

### 3.1 Defining the Distinctions
Let $x$ and $y$ be entities/properties.

**1. Real Distinction ($ \neq_r $):**
Separability. $x$ and $y$ are really distinct if one can exist without the other.
$$ x \neq_r y \iff \Diamond(E!(x) \land \neg E!(y)) $$
*Cartesian Dualism:* Mind $\neq_r$ Body.

**2. Conceptual Distinction ($ \neq_c $):**
Distinction of Reason. $x$ and $y$ are identical in reality, distinct only in mental abstraction.
$$ x \neq_c y \iff (x =_{real} y) \land (Concept(x) \neq Concept(y)) $$

**3. Formal Distinction ($ \neq_f $):** (The Scotist Innovation)
$x$ and $y$ are really identical (inseparable in existence) but distinct in their *quiddity* (definition/essence) prior to any mental operation.
$$ x \neq_f y \iff (x =_r y) \land (Def(x) \cap Def(y) = \emptyset) $$

### 3.2 Applying to Spinoza’s Attributes
Schmidt argues that for Spinoza, attributes are **Really Identical** but **Formally Distinct**.

1.  **Real Identity:** In the infinite substance, Thought and Extension are the same logical substance.
    $$ T =_r E =_r G $$
    *(This preserves Divine Simplicity).*
2.  **Formal Distinction:** The definition of Thought does not involve Extension, and vice versa. They are "Formally" different essences.
    $$ T \neq_f E $$
    *(This preserves the Multiplicity of Attributes).*

*Formal Conclusion:* God is a simple reality ($=_r$) capable of being explicated through formally distinct essences ($ \neq_f $). Infinity fuses distinct formalities into a real unity.

## IV. The Identity Theory of Mind and Body

Schmidt demonstrates how this theological logic generates Spinoza’s philosophy of mind. The Mind-Body problem is treated as a modal instance of the Attribute problem.

### 4.1 The Identity Thesis
Let $m_T$ be a mode of Thought (a Mind).
Let $m_E$ be a mode of Extension (a Body).

The "Union" of Mind and Body is not interaction, but **Real Identity**:
$$ m_T =_r m_E $$
They are one and the same individual ($I$).

### 4.2 The Explanatory Gap (Non-Reductionism)
Despite being identical, they are **Formally Distinct**.
$$ Def(m_T) \cap Def(m_E) = \emptyset $$
*   You cannot explain a neural firing ($m_E$) using the vocabulary of pain ($m_T$), nor vice versa.
*   This creates **Parallelism**: The order of formal causes in Thought must map perfectly to the order of efficient causes in Extension, because they are tracking the *same* Real Identity.

### 4.3 Resolving Interaction
*   **Problem:** How do minds move bodies?
*   **Dualist Answer:** Transmission of energy/force. (Impossible given physics).
*   **Spinoza/Schmidt Answer:** They don't.
    *   Mental event $A$ causes Mental event $B$.
    *   Physical event $A'$ causes Physical event $B'$.
    *   Since $A=_r A'$ and $B=_r B'$, it *appears* as interaction, but it is actually the unfolding of one substance under two formally distinct descriptions.

## V. Conclusion

Spinoza’s Identity Theory is a direct corollary of his Substance Monism, mediated by the **Formal Distinction**.

*   **Monism:** There is only one Token substance.
*   **Identity:** Mind and Body are one Token mode.
*   **Property Dualism:** They are distinct *Types* (Formalities) that can never be reduced to one another conceptually, even though they are identical ontologically.

***

# Glossary of Equivalent and Nuanced Terms

**Distinctio Realis (Real Distinction)**
*Definition:* A distinction entailing separability.
*Formal:* $x$ and $y$ are really distinct iff God can produce $x$ without $y$.
*Context:* Spinoza denies a real distinction between attributes (in the sense of constituting two substances) and between mind and body.

**Distinctio Formalis (Formal Distinction)**
*Definition:* A distinction in definition/essence that exists objectively in the thing, not just in the mind of the observer, but does not entail separability.
*Context:* The crucial tool Schmidt extracts from Duns Scotus to explain how God can be Simple yet have different Attributes. Thought and Extension are formally distinct (different definitions) but really identical (same substance).

**Distinctio Rationis (Distinction of Reason/Conceptual)**
*Definition:* A distinction created solely by the mind comparing a thing to itself or others; a subjective distinction.
*Context:* Schmidt argues Spinoza rejects this for attributes. Attributes are not just "ways of seeing" God (Subjectivism); they are real expressions of God's essence.

**Univocity**
*Definition:* The predication of a term (e.g., "cause," "existence") in the same sense to different subjects (God and humans).
*Context:* Spinoza requires univocity to ensure God is intelligible. If God’s "wisdom" were totally different from human "wisdom" (Equivocity), we could not know God.

**Quiddity**
*Definition:* The "whatness" or definitional essence of a thing.
*Nuance:* In the Formal Distinction, $x$ and $y$ differ in quiddity but are identical in existence.

**Identity Theory (Non-Reductive)**
*Definition:* The view that mental states are physical states, but mental *properties* are not reducible to physical *properties*.
*Context:* Spinoza is a non-reductive identity theorist. Mind is Body (Identity), but the logic of Mind cannot be reduced to the logic of Body (Formal Distinction/Parallelism).

**Propria vs. Essence**
*Definition:* *Propria* are necessary properties that do not constitute the definition; *Essence* constitutes the definition.
*Context:* Modes are *propria* of God (they flow from him necessarily but don't define him). Attributes are *essence* (they define him). This distinction allows Spinoza to say finite things follow from God without being part of God's definition.