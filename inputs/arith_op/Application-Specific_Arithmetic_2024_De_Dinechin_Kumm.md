Here is a detailed mathematical summary of *Application-Specific Arithmetic* by Florent de Dinechin and Martin Kumm. The summary prioritizes mathematical formulations, algorithms, and proofs, structured with informal intuition followed by formalization.

---

# Mathematical Summary of Application-Specific Arithmetic

## 1. Foundations of Arithmetic Operators

### Definition of an Arithmetic Operator
**Informal Sketch:**
An arithmetic operator in hardware isn't just a mathematical function (like addition on reals); it is a mapping from a specific set of discrete inputs to a discrete output. It must account for the finite precision of hardware, meaning we must strictly define how the mathematical result is approximated (rounded) to fit into the hardware format.

**Formal Definition:**
Let $\mathbb{F}$ be a set of machine numbers (a finite subset of $\mathbb{R}$). Let $f: \mathbb{R}^n \to \mathbb{R}$ be a mathematical function. Let $\approx$ be a rounding relation.
An operator $Op$ implements $f$ for the format $\mathbb{F}$ with rounding $\approx$ if and only if:
$$ \forall (X_1, \dots, X_n) \in \mathbb{F}^n, \quad Op(X_1, \dots, X_n) \approx f(X_1, \dots, X_n) $$
**[Page 8]**

### Number Formats
**Binary Integers (Unsigned and Two's Complement):**
The value $X$ of a $w$-bit vector $(x_{w-1}, \dots, x_0)$ is defined as:
*   **Unsigned:** $X = \sum_{i=0}^{w-1} 2^i x_i$ **[Page 34]**
*   **Two's Complement:** $X = -2^{w-1}x_{w-1} + \sum_{i=0}^{w-2} 2^i x_i$ **[Page 37]**
    *   *Property:* The range is $[-2^{w-1}, 2^{w-1}-1]$.
    *   *Negation:* $-X = \bar{X} + 1 \pmod{2^w}$.

**Fixed-Point Numbers:**
A fixed-point format is defined by a scaling factor $2^\ell$, where $\ell$ is the position of the Least Significant Bit (LSB).
*   **Value:** $X = \sum_{i=\ell}^{m} 2^i x_i$.
*   **Relation to Integers:** $X_{fixed} = X_{integer} \times 2^\ell$. **[Page 39]**

**Floating-Point Numbers (IEEE 754 & Nfloat):**
A value $X$ is determined by a sign $s$, a significand $M$, and an exponent $E$.
*   **Normal Numbers:** $X = (-1)^s \times (1 + F) \times 2^{E - E_0}$, where $E_0$ is the bias.
    *   Bias $E_0 = 2^{w_E-1} - 1$.
*   **Subnormal Numbers:** $X = (-1)^s \times (0 + F) \times 2^{e_{min}}$. **[Page 49-50]**

### Error Analysis and Accuracy
**Informal Sketch:**
When building custom operators, we often carry more precision internally than required at the output to ensure accuracy. The measure of "good enough" is the Unit in the Last Place (ulp).

**Formal Definitions:**
*   **Absolute Error:** $\delta = |\tilde{X} - X|$.
*   **Relative Error:** $\varepsilon = |\frac{\tilde{X} - X}{X}|$. **[Page 67]**
*   **Ulp (Fixed-Point):** For a format with LSB at position $\ell$, $ulp = 2^\ell$. **[Page 68]**
*   **Faithful Rounding:** An operator is faithful if the error is strictly less than $1$ ulp.
    $$ |\tilde{X} - X| < 2^\ell $$
    This implies the result is one of the two floating-point numbers surrounding the exact result. **[Page 76]**
*   **Correct Rounding (Nearest):** The result is the nearest representable number. Error bound: $|\delta| \leq 2^{\ell-1}$ ($0.5$ ulp).

---

## 2. Integer Addition and Subtraction

### Carry Propagation Logic
**Informal Sketch:**
The speed of an adder is limited by how fast the carry bit travels from the LSB to the MSB. To speed this up, we calculate whether a block of bits will *generate* a carry (output is 1 regardless of input carry), *propagate* a carry (output equals input carry), or *kill* a carry (output is 0).

**Formalization:**
For bits $x_i, y_i$:
*   **Generate ($g_i$):** $g_i = x_i y_i$ (carry is created).
*   **Propagate ($p_i$):** $p_i = x_i \oplus y_i$ (carry is passed through).
*   **Kill ($k_i$):** $k_i = \overline{x_i + y_i}$.
*   **Carry Recurrence:** $c_{i+1} = g_i \vee (p_i \wedge c_i)$. **[Page 112]**

### Parallel Prefix Addition
**Informal Sketch:**
Carry propagation is an associative operation. This means we can group the calculation of $(g, p)$ pairs in a tree structure rather than a linear chain, reducing latency from $O(n)$ to $O(\log n)$.

**Formal Operator ($\circ$):**
Define the operator $\circ$ on pairs $(g, p)$ (generate, propagate):
$$ (g_L, p_L) \circ (g_R, p_R) = (g_L \vee (p_L \wedge g_R), \quad p_L \wedge p_R) $$
*   **Proof of Associativity:**
    Let $A=(g_A, p_A)$, $B=(g_B, p_B)$, $C=(g_C, p_C)$.
    $(A \circ B) \circ C = (g_A \vee p_A g_B, p_A p_B) \circ C = (g_A \vee p_A g_B \vee p_A p_B g_C, p_A p_B p_C)$.
    $A \circ (B \circ C) = A \circ (g_B \vee p_B g_C, p_B p_C) = (g_A \vee p_A(g_B \vee p_B g_C), p_A p_B p_C)$.
    The terms are identical. **[Page 120]**

---

## 3. Multiplication

### The Bit Heap Concept
**Informal Sketch:**
Multiplication involves generating many partial products (e.g., $x_i y_j$) and summing them. Instead of summing them row-by-row, we treat them as a "heap" of bits weighted by powers of 2 ($2^{i+j}$). We use compressors (like Full Adders) to reduce the height of this heap until two rows remain, which are then summed.

**Formal Definition:**
A multiplication $X \times Y$ is a sum of weighted bits:
$$ X \times Y = \sum_{i=0}^{w_X-1} \sum_{j=0}^{w_Y-1} 2^{i+j} x_i y_j $$
**[Page 153]**

### Karatsuba Multiplication
**Informal Sketch:**
To multiply two large numbers, we can split them into halves. Standard multiplication requires 4 sub-multiplications. Karatsuba observes that $ac + ad + bc + bd$ can be reorganized to use only 3 multiplications by computing $(a+b)(c+d)$.

**Formal Proof:**
Let $X = X_1 2^w + X_0$ and $Y = Y_1 2^w + Y_0$.
$$ X \times Y = (X_1 2^w + X_0)(Y_1 2^w + Y_0) = X_1 Y_1 2^{2w} + (X_1 Y_0 + X_0 Y_1) 2^w + X_0 Y_0 $$
Standard approach: Calculate $X_1 Y_1$, $X_1 Y_0$, $X_0 Y_1$, $X_0 Y_0$ (4 mults).
Karatsuba identity:
$$ X_1 Y_0 + X_0 Y_1 = (X_0 + X_1)(Y_0 + Y_1) - X_0 Y_0 - X_1 Y_1 $$
Thus, we only compute $M_1 = X_0 Y_0$, $M_4 = X_1 Y_1$, and $M_3 = (X_0+X_1)(Y_0+Y_1)$. The middle term is $M_3 - M_1 - M_4$.
**[Page 244]**

**Generalized Karatsuba (Tiling):**
For any $i, j, k, \ell$ such that $i+j = k+\ell$, the terms $X_i Y_j$ and $X_k Y_\ell$ have the same weight.
$$ X_i Y_j + X_k Y_\ell = (X_i + X_k)(Y_j + Y_\ell) - X_i Y_\ell - X_k Y_j $$
This generalizes the reduction to arbitrary tiling locations in the partial product array. **[Page 249]**

---

## 4. Division and Square Root

### Restoring Division Recurrence
**Informal Sketch:**
This is the binary version of "long division". At each step, we shift the remainder, try to subtract the divisor. If the result is positive, the quotient bit is 1; if negative, the quotient bit is 0 and we "restore" the remainder.

**Formal Recurrence:**
Let $R_0 = X$ (Dividend), $D$ (Divisor).
$$ R_{i+1} = 2 R_i - q_{w-1-i} D $$
$$ q_{w-1-i} = \begin{cases} 1 & \text{if } 2 R_i - D \ge 0 \\ 0 & \text{otherwise} \end{cases} $$
**[Page 266]**

### SRT Division (Digit Recurrence with Redundancy)
**Informal Sketch:**
Selecting the exact quotient bit is hard because it requires a full precision comparison. If we allow the quotient digits to be redundant (e.g., $\{-1, 0, 1\}$ in radix 2, or $\{-2..2\}$ in radix 4), we can make mistakes in selection and correct them in subsequent steps. This allows selecting digits based on just a few MSBs of the remainder and divisor.

**Formalization:**
Radix $\beta$, digit set $D = \{-\gamma, \dots, \gamma\}$.
Redundancy factor $\rho = \frac{\gamma}{\beta-1}$. For valid redundancy, $\rho > 1/2$.
**Constraint:** The residual $W_i$ must remain bounded:
$$ -\rho D \le W_i \le \rho D $$
**Selection Function:** We must select $q_{i+1}$ such that $W_{i+1} = \beta W_i - q_{i+1}D$ stays within bounds.
This implies:
$$ \frac{\beta W_i}{D} - \rho \le q_{i+1} \le \frac{\beta W_i}{D} + \rho $$
The P-D diagram (Partial remainder vs Divisor) visualizes these overlapping selection regions.
**[Page 272-273]**

---

## 5. Constant Multiplication (SCM)

### Minimal-Adder Graph (MAG)
**Informal Sketch:**
Multiplying by a constant $C$ is cheaper than generic multiplication. It reduces to a sequence of shifts and additions. The problem is finding the sequence with the fewest adders.

**Formalization:**
Find the shortest sequence $v_0, v_1, \dots, v_n$ such that $v_0 = X$ and $v_n = C \cdot X$, where each $v_k$ is of the form:
$$ v_k = s_1 v_i \pm s_2 v_j \quad \text{with } i, j < k \text{ and } s_1, s_2 \text{ powers of 2} $$
**Lower Bound:**
If $nz(C)$ is the number of non-zeros in the CSD (Canonical Signed Digit) representation of $C$, the minimum adders required is roughly $\lceil \log_2(nz(C)) \rceil$.
**[Page 373]**

### KCM Algorithm (Table-Based)
**Informal Sketch:**
For FPGAs with LUTs (Look-Up Tables), we can chop the input $X$ into chunks (e.g., 4 bits). We use LUTs to store the pre-computed product of the constant $C$ with every possible 4-bit chunk value, then sum the results.

**Formalization:**
Let $X = \sum_{k=0}^{D-1} X_k 2^{k\alpha}$ where $X_k$ are $\alpha$-bit chunks.
$$ C \times X = \sum_{k=0}^{D-1} (C \cdot X_k) 2^{k\alpha} $$
The term $(C \cdot X_k)$ is computed via a LUT. The summation is performed by an adder tree/chain.
**[Page 384]**

---

## 6. Function Approximation

### Polynomial Approximation (Taylor vs. Remez)
**Informal Sketch:**
We approximate a function $f(x)$ using a polynomial $P(x)$. Taylor series are good near a single point but get worse away from it. The Remez algorithm finds the "minimax" polynomial, which minimizes the maximum error over an entire interval.

**Formalization:**
**Taylor:** $P(x) = \sum \frac{f^{(n)}(x_0)}{n!} (x-x_0)^n$.
**Remez:** Finds $P(x)$ such that the error function $E(x) = f(x) - P(x)$ equioscillates (hits its max/min peaks) $d+2$ times, where $d$ is the degree. This minimizes $\| f - P \|_\infty$.
**[Page 531-533]**

### Range Reduction
**Informal Sketch:**
To compute functions like $e^x$ or $\sin(x)$ over a large range, we use mathematical identities to map the input argument $X$ to a small interval (e.g., $[0, \ln 2)$ or $[0, \pi/4)$), compute the function there, and reconstruct the result.

**Example (Exponential):**
To compute $e^X$:
1.  Compute $k = \lfloor X / \ln 2 \rceil$ and $r = X - k \ln 2$.
2.  Then $e^X = e^{k \ln 2 + r} = 2^k \cdot e^r$.
3.  Compute $e^r$ (where $r$ is small) using a polynomial.
4.  Compute $2^k$ by adding $k$ to the floating-point exponent.
**[Page 646]**

---

## 7. Multipartite Table Method

**Informal Sketch:**
Instead of a high-degree polynomial, we can approximate a function using a table of initial values (TIV) and a table of offsets (TO). We split the input $X$ into three parts: $A$ (MSBs), $B$, and $C$.
$f(X) \approx f(A) + \text{slope}(A) \times (BC)$.
To save memory, the slope is approximated coarsely.

**Formalization:**
Input $X$ split into $A, B, C$.
Approximation:
$$ f(X) \approx TIV(A) + TO(A, B) $$
where $TIV(A) \approx f(A)$ and $TO(A, B) \approx f'(A) \times (B \cdot 2^{-k})$.
By exploiting symmetries and decomposing the offset table further (Multipartite), memory usage scales better than standard tabulation ($2^n$ vs $2^{2n/3}$).
**[Page 503]**

---

## 8. Digital Filters (LTI)

### Worst-Case Peak Gain (WCPG)
**Informal Sketch:**
When implementing recursive (IIR) filters in fixed-point, rounding errors recirculate and can cause instability or limit cycles. We need to determine the maximum possible value internal nodes can reach to prevent overflow.

**Formal Definition:**
The WCPG $\langle\langle \mathcal{H} \rangle\rangle$ is the maximum output peak for any input with peak 1.
$$ \langle\langle \mathcal{H} \rangle\rangle = \sum_{k=0}^{\infty} |h(k)| $$
where $h(k)$ is the impulse response.
**Stability Condition:** A hardware filter is faithful/stable if the internal error accumulation does not exceed the unit in the last place.
**[Page 689]**

---

## 9. Deep Learning Arithmetic

### Quantization for Inference
**Informal Sketch:**
Neural networks are robust to noise. We can replace 32-bit floating point with low-precision integers (e.g., 8-bit) for inference. The core operation is the Sum of Products (SOP).

**Formalization:**
**Convolution/SOP:**
$$ Y = \sum W_i X_i + B $$
In fixed-point, if weights $W$ and activations $X$ are quantized, the accumulator must be wide enough to prevent overflow before the final activation function (e.g., ReLU).
**Quantization-Aware Training (QAT):** Training the network while simulating the rounding errors of the hardware target to allow lower precision (e.g., binary or ternary weights) without accuracy loss.
**[Page 716, 733]**

### Logarithmic Number Systems (LNS) in NN
**Informal Sketch:**
In LNS, multiplication becomes addition ($ \log(AB) = \log A + \log B $). Since Neural Nets are dominated by multiplications, LNS is attractive.
**Cost:** Addition becomes complex: $\log(A+B) = \log A + \log(1 + b^{\log B - \log A})$.
**Approximation:** For Deep Learning, we can approximate $\log(A+B) \approx \max(\log A, \log B)$. This turns neurons into "max-sum" networks.
**[Page 727]**