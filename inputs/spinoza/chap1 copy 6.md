Here is a formal analysis of **Chapter 6: Spinoza on Necessity**, written by Charles Jarrett.

This analysis reconstructs Jarrett’s logical critique of the "Moderate Necessitarian" interpretation (Curley/Walski) and his defense of "Strict Necessitarianism" using modal logic ($S5$) and comparisons to Gödel’s ontological proof.

***

# Formal Analysis: The Logic of Spinozistic Necessity

## I. The Domain: Modal Metaphysics

The central problem of the chapter is the modal status of finite modes (particular things/events).
Let $W$ be the set of possible worlds.
Let $w_{@}$ be the actual world.

**Definition 1 (Strict Necessitarianism - SN):**
$$ W = \{ w_{@} \} $$
*Interpretation:* There is only one possible world. Whatever is true is necessarily true. $\forall p (p \to \Box p)$.

**Definition 2 (Moderate Necessitarianism - MN):**
$$ |W| > 1 \land w_{@} \in W $$
*Interpretation:* Things could have been otherwise. There exist logically possible worlds distinct from the actual world, even if they are not causally accessible.

**Jarrett’s Thesis:** Spinoza is committed to **SN**. The text of the *Ethics* and the *Short Treatise* supports a unitary conception of necessity that collapses modality.

## II. The Argument from Causation (Short Treatise I.6)

Jarrett analyzes Spinoza’s early attempt to prove that there are no accidental things.

**Axiom 1 (Universal Causation):** Every event has a cause.
$$ \forall e, \exists c : Cause(c, e) $$

**Axiom 2 (Necessitation of Effect):** If a cause is given, the effect follows necessarily.
Let $C$ be the occurrence of the cause and $E$ be the occurrence of the effect.
$$ \Box(C \to E) $$

### 2.1 The Modal Scope Fallacy
Jarrett identifies a potential confusion in interpretations of determinism: the distinction between the necessity of the *consequence* and the necessity of the *consequent*.

1.  **Necessitas Consequentiae (Wide Scope):** $\Box(C \to E)$. (True in determinism).
2.  **Necessitas Consequentis (Narrow Scope):** $C \to \Box E$. (Required for SN).

*Critique:* From $C$ and $\Box(C \to E)$, one can deduce $E$, but one cannot deduce $\Box E$ unless one assumes $\Box C$.
$$ (C \land \Box(C \to E)) \not\implies \Box E $$

### 2.2 The Infinite Regress and Transfer of Necessity
Spinoza accepts an infinite regress of finite causes ($c_n \to ... \to c_2 \to c_1 \to e$).
For $e$ to be necessary ($\Box e$), the whole chain must be necessary.

**The Spinozistic Fix:**
1.  All things depend on God ($G$).
2.  God exists necessarily ($\Box G$).
3.  God is the cause of all things (directly or indirectly).

**Theorem 1 (Transfer of Necessity):**
In standard modal logic ($S5$ or $T$), if $p$ implies $q$ necessarily, and $p$ is necessary, then $q$ is necessary.
$$ (\Box p \land \Box(p \to q)) \to \Box q $$

**Application to Spinoza:**
If the causal chain is grounded in God ($\Box G$), and the laws of causation are necessary ($\Box(G \to ... \to e)$), then the effect is necessary ($\Box e$).
*Jarrett’s Conclusion:* Spinoza rejects the idea that an effect is contingent just because its *proximate* cause is finite. Since the ultimate ground is $\Box G$, the finite mode is $\Box e$.

## III. The Reductio Argument (Ethics 1p33)

Jarrett reconstructs Spinoza’s proof that "Things could not have been produced by God in any other way" (1p33) as a valid *Reductio ad Absurdum* against MN.

**Hypothesis ($H$):** God could have produced a different order of things.
Let $W'$ be a world distinct from $w_{@}$.
$$ H: \Diamond (God \text{ produced } W') $$

**The Deduction:**
1.  **Production implies Nature:** If God produced $W'$, God must have a nature ($N'$) capable of producing $W'$.
    $$ \Diamond W' \to \Diamond N' $$
2.  **Essence-Existence Identity (1p11):** God’s nature involves existence. If a nature of God is possible, it exists.
    $$ \Diamond N' \to E!(N') $$
3.  **Uniqueness of Substance (1p14):** There is only one Substance (God).
    $$ \exists! x : Substance(x) $$
4.  **The Contradiction:** If God could have been different ($\Diamond N'$), then by step 2, that different nature $N'$ would exist alongside the actual nature $N$. This implies two Gods or a composite God, violating Simplicity and Uniqueness.
    $$ H \implies \text{Absurdity} $$

**Theorem 2 (Impossibility of Alternative Worlds):**
Since God’s nature ($N$) is necessary ($\Box N$), and the order of things ($O$) follows from $N$ ($\Box(N \to O)$), then $O$ is necessary.
$$ \therefore \neg \Diamond (\neg O) $$

## IV. The Unitary Conception of Necessity

Jarrett attacks the "Dual Necessity" theory proposed by Curley.

**Curley's Distinction:**
1.  **Absolute Necessity:** Logical contradiction of the negation (e.g., Geometry, God).
2.  **Relative Necessity:** Causal determination given a set of antecedent conditions.

**Jarrett’s Counter-Argument:**
Spinoza equates the necessity of God's *existence* with the necessity of God's *action* (creation).

**Textual Evidence (2p3s):**
$$ \text{Necessity}_{Existence}(G) \equiv \text{Necessity}_{Action}(G) $$
"God acts with the same necessity by which he understands himself."

**The Logical Consequence:**
If the cause (God) is absolutely necessary, and the causal link is absolutely necessary, the effect is absolutely necessary. There is no ontological gap for "Relative Necessity" to occupy that is distinct from Absolute Necessity.
*Distinction Re-evaluated:* The distinction is not metaphysical, but **epistemological**. We call things "contingent" or "relatively necessary" only due to a deficiency in our knowledge of the infinite causal chain (1p33s1).

## V. Gödel, Spinoza, and Modal Collapse

Jarrett draws a parallel between Spinoza’s system and Kurt Gödel’s Ontological Argument (formalized in $S5$).

### 5.1 Gödel's Axioms vs. Spinoza
*   **Gödel:** Defines God via "Positive Properties" ($P(\phi)$).
*   **Spinoza:** Defines God via "Attributes" (expressing essence).

**Common Structure:**
1.  $God(x) \iff \forall \phi [P(\phi) \to \phi(x)]$ (A being with all positive properties/attributes).
2.  $P(NecessaryExistence)$.
3.  $\therefore \Box \exists x God(x)$.

### 5.2 The Modal Collapse
In Gödel’s system, as in Spinoza’s, if one accepts specific axioms about the nature of essence, the system suffers **Modal Collapse**:
$$ \phi \to \Box \phi $$
(Truth implies Necessity).

**Jarrett’s Observation:**
Sobel (logic scholar) views Modal Collapse as a "logical embarrassment" to be fixed. Spinoza views Modal Collapse as a **desideratum** (a desired result).
*   For Spinoza, if a system allows for $\Diamond p \land \neg p$ (unactualized possibilities), it implies an imperfection in the nature of God (an unactualized potency).

**Theorem 3 (Spinozistic Collapse):**
If God is the only substance ($\exists! x S(x)$) and God is fully actual ($Potency = Act$), then the set of possible worlds must collapse into the actual world.
$$ \forall w \in W, w = w_{@} $$

***

# Glossary of Formal Concepts

**Strict Necessitarianism (SN)**
*Definition:* The modal thesis that the actual world is the only possible world. $\forall p (p \leftrightarrow \Box p)$.
*Context:* Jarrett argues this is Spinoza's true position, contra Curley.

**Event Necessitarianism**
*Definition:* The thesis that every singular event that occurs, occurs necessarily.
*Nuance:* Distinct from "Universal Causation." A world could have universal causation but still be contingent if the *first* cause were contingent. Spinoza bridges this by making the first cause (God) necessary.

**Unitary Necessity**
*Definition:* The concept that there is only one type of necessity (absolute/logical).
*Nuance:* Opposed to the distinction between "logical necessity" (nature of triangles) and "physical necessity" (laws of motion). For Spinoza, the flow of modes from God is as rigid as the flow of properties from a triangle.

**Essence vs. Existence (in Finite Modes)**
*Definition:* For finite things, essence does not involve existence ($\neg \Box E!(x)$).
*Spinoza's Twist:* Curley uses this to argue for contingency. Jarrett argues that while the *definition* of a man does not involve existence, the *causal order* necessitates his existence. The non-necessity of the definition does not imply the non-necessity of the event.

**Transworld Identity**
*Definition:* The concept that the same entity can exist in different possible worlds.
*Context:* In Spinoza's 1p33d, the argument relies on the idea that if God were different, he would be a *different* God. Spinoza rejects transworld identity for God; a different nature implies a different entity.

**Modal Collapse**
*Definition:* A logical state where the operators $\Box$ (necessity) and $\Diamond$ (possibility) become redundant. $p \equiv \Box p \equiv \Diamond p$.
*Context:* A flaw in most modal logic systems, but a feature of Spinoza’s metaphysics.

**Ratio (Reason/Ground)**
*Definition:* The sufficient condition for a thing's existence.
*Nuance:* In 1p33s1, Spinoza says things are necessary by *reason* of essence or *reason* of cause. Jarrett argues this distinguishes the *source* of necessity (internal vs. external), not the *modality* itself. Both result in absolute necessity.