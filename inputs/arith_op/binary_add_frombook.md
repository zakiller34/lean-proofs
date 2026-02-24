Here is a comprehensive extraction of objects, theorems, lemmas, proofs, and definitions related to **binary addition** from the provided text.

# Mathematical Objects and Definitions: Binary Addition

## 1. Basic Addition Cells

### Definition: Full Adder (FA)
**Page 106-107**
The Full Adder is the fundamental building block of binary addition. It computes the sum of three input bits $x_i$, $y_i$, and $c_i$ (input carry).
*   **Inputs:** $x_i, y_i, c_i \in \{0, 1\}$
*   **Outputs:** Sum bit $s_i$ and Output Carry bit $c_{i+1}$.
*   **Mathematical Relation:** $x_i + y_i + c_i = 2c_{i+1} + s_i$
*   **Boolean Equations:**
    $$ s_i = x_i \oplus y_i \oplus c_i $$
    $$ c_{i+1} = (x_i \wedge c_i) \vee (y_i \wedge c_i) \vee (x_i \wedge y_i) $$
    *(Note: The carry is the majority function).*

### Definition: Half Adder (HA)
**Page 107**
A special case of the Full Adder where the input carry $c_i = 0$.
*   **Inputs:** $x_i, y_i \in \{0, 1\}$
*   **Outputs:** $s_i, c_{i+1}$
*   **Boolean Equations:**
    $$ s_i = x_i \oplus y_i $$
    $$ c_{i+1} = x_i \wedge y_i $$

---

## 2. Integer and Fixed-Point Addition Architectures

### Object: Ripple-Carry Adder (RCA)
**Page 108**
An adder for $w$-bit numbers constructed by chaining $w$ Full Adders. The critical path travels from the LSB input to the MSB output.
*   **Latency Formula:**
    $$ \tau_{\text{add}}(w) = (w - 1)\tau_{\text{cp}} + \max(\tau_{\text{cp}}, \tau_{\text{fa}}) $$
    Where $\tau_{\text{fa}}$ is the delay of a full adder and $\tau_{\text{cp}}$ is the carry propagation delay.

### Definition: Carry-Save Adder (CSA)
**Page 110-111**
An operator that adds three $w$-bit numbers $X, Y, Z$ and produces two $w$-bit numbers $C$ (Carry) and $S$ (Sum) without propagating carries.
*   **Equation:**
    $$ C + S = X + Y + Z $$
*   **Operation:**
    For each bit position $i$, a Full Adder computes $x_i + y_i + z_i = 2c_{i+1} + s_i$.
    The vector $S$ consists of all $s_i$, and vector $C$ consists of all $c_{i+1}$ (shifted left by 1).
*   **Property:** Delay is independent of the addition size $w$ ($O(1)$).

### Definition: High-Radix Carry-Save (HRCS)
**Page 111**
A variant of carry-save where carry propagation is kept for chunks of $\alpha$ bits.
*   **Structure:** Carries are output every $\alpha$ bits only.
*   **Representation:** A radix-$2^\alpha$ system with a redundant digit set $\{0, 1, \dots, 2^\alpha\}$ (one standard radix-$2^\alpha$ digit plus one unit bit).

---

## 3. Fast Adder Logic (Carry Propagation)

### Definitions: Carry States (Generate, Propagate, Kill)
**Page 112**
To accelerate carry propagation, the behavior of a Full Adder position $i$ is classified based on inputs $x_i, y_i$:
1.  **Generate ($g_i$):** A carry is generated regardless of the input carry.
    $$ g_i = x_i \wedge y_i $$
2.  **Propagate ($p_i$):** The input carry is propagated to the output.
    $$ p_i = x_i \oplus y_i $$
3.  **Kill ($k_i$):** The carry is stopped (output is 0) regardless of input carry.
    $$ k_i = \overline{x_i + y_i} $$
4.  **Alive ($a_i$):** Alternative to propagate, combines generate and propagate.
    $$ a_i = x_i \vee y_i $$

### Theorem: Carry Recurrence
**Page 113**
The output carry $c_{i+1}$ can be expressed as a function of the input carry $c_i$ and the local generate/propagate signals:
$$ c_{i+1} = g_i \vee (p_i \wedge c_i) $$
Or using the "Alive" definition:
$$ c_{i+1} = g_i \vee (a_i \wedge c_i) $$

### Definition: The Prefix Operator ($\circ$)
**Page 120**
To solve the carry recurrence in parallel, the problem is formulated as a prefix problem using the operator $\circ$ defined on pairs $(g, a)$ (generate, alive).
$$ (g_L, a_L) \circ (g_R, a_R) = (g_L \vee (a_L \wedge g_R), \quad a_L \wedge a_R) $$
*   $(g_L, a_L)$ represents the more significant bit/block.
*   $(g_R, a_R)$ represents the less significant bit/block.

### Theorem: Associativity of the Prefix Operator
**Page 120**
The operator $\circ$ is associative.
$$ (U \circ V) \circ W = U \circ (V \circ W) $$

**Proof:**
Let $U=(g_U, a_U)$, $V=(g_V, a_V)$, $W=(g_W, a_W)$.

**Left Side:** $(U \circ V) = (g_U \vee a_U g_V, \ a_U a_V)$.
Then $((U \circ V) \circ W) = ( (g_U \vee a_U g_V) \vee (a_U a_V)g_W, \ (a_U a_V) a_W )$.
Distributing the AND: $g_{result} = g_U \vee a_U g_V \vee a_U a_V g_W$.
$a_{result} = a_U a_V a_W$.

**Right Side:** $(V \circ W) = (g_V \vee a_V g_W, \ a_V a_W)$.
Then $U \circ (V \circ W) = ( g_U \vee a_U(g_V \vee a_V g_W), \ a_U(a_V a_W) )$.
Distributing the AND: $g_{result} = g_U \vee a_U g_V \vee a_U a_V g_W$.
$a_{result} = a_U a_V a_W$.

**Conclusion:** The results are identical. $\blacksquare$

### Object: Parallel Prefix Adder
**Page 118-121**
An adder that computes all carries $c_i$ in parallel using a tree of $\circ$ operators.
*   **Carry Calculation:**
    $$ (c_i, a_{i \dots 0}) = (g_i, a_i) \circ (g_{i-1}, a_{i-1}) \circ \dots \circ (g_0, a_0) \circ (c_0, 0) $$
    where $(c_0, 0)$ represents the input carry to the adder.
*   **Sum Calculation:** Once $c_i$ is known, $s_i = p_i \oplus c_i$.

---

## 4. Multi-Operand Addition (Bit Heaps and Compressors)

### Definition: Bit Heap
**Page 153**
A data structure representing a sum of weighted bits. It generalizes binary addition to multiple operands.
$$ S = \sum_{k} 2^{w_k} b_k $$
where $b_k$ are individual bits and $w_k$ are their weights (positions).

### Definition: (p; q) Counter / Compressor
**Page 180**
A combinational circuit that counts the number of 1s among $p$ input bits of the same weight and outputs the result as a $q$-bit binary number.
*   **Constraint:** To represent the count of $p$ bits, $q$ must satisfy:
    $$ q = \lceil \log_2(p+1) \rceil $$
*   **Example:** A Full Adder is a (3; 2) counter.

### Definition: Generalized Parallel Counter (GPC)
**Page 182**
A compressor that takes inputs of different weights. Denoted as $(p_{n-1}, \dots, p_0; q)$, where $p_j$ is the number of input bits of weight $2^j$.
*   **Output Size:**
    $$ q = \lceil \log_2(\sum_{j=0}^{n-1} p_j 2^j + 1) \rceil $$

### Theorem: Compression Ratio of a Full Adder
**Page 176**
One row of full adders takes 3 rows of bits and produces 2 rows of bits (Sum and Carry).
*   **Compression Factor:** $3/2$.
*   **Dadda Sequence:** The maximum height $m_l$ of a bit heap that can be compressed to 2 rows in $l$ levels of full adders is given by:
    $$ m_l = \lfloor 1.5 m_{l-1} \rfloor \quad \text{with } m_0 = 2 $$
    Sequence: 2, 3, 4, 6, 9, 13, 19...

---

## 5. Floating-Point Addition Specifics

### Definition: Effective Addition vs. Subtraction
**Page 331**
In floating-point addition $R = X + Y$:
*   **Effective Addition:** When $X$ and $Y$ have the same sign (operation increases magnitude).
*   **Effective Subtraction:** When $X$ and $Y$ have different signs (cancellation may occur).

### Theorem: Sterbenz Lemma (implied)
**Page 334 (referenced as related to exact result in "Near" case)**
If $X$ and $Y$ are floating-point numbers with $X/2 \le Y \le 2X$, then $X - Y$ is exactly representable in the same format (no rounding error occurs during the subtraction of the significands).

### Definition: Rounding to Nearest (Ties to Even)
**Page 68-69**
*   **Standard:** $RN(x)$ is the machine number closest to $x$.
*   **Tie-breaking:** If $x$ is exactly halfway between two machine numbers, select the one with an even least significant bit (LSB = 0).
*   **Implementation:** Requires a "Sticky bit" (OR of all discarded bits) to detect exact ties.

### Definition: Faithful Rounding (Last-Bit Accuracy)
**Page 76**
An operator is faithful if the error is strictly less than 1 unit in the last place (ulp).
$$ | \text{result} - \text{exact} | < 2^{\text{LSB}} $$
Unlike correct rounding (error $\le 0.5$ ulp), faithful rounding does not mandate a specific choice when the result is very close to a midpoint, but it is cheaper to implement.