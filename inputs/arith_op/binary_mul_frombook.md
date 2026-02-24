Here is a comprehensive extraction of objects, theorems, lemmas, proofs, and definitions related to **binary multiplication** from the provided text.

# Mathematical Objects and Definitions: Binary Multiplication

## 1. Fundamental Integer Multiplication

### Definition: Unsigned Integer Multiplication
**Page 214 (Eq 8.13, 8.14)**
The product $P$ of two unsigned integers $X$ (width $w_X$) and $Y$ (width $w_Y$) is defined as a double sum of weighted partial products:
$$ P = X \times Y = \sum_{i=0}^{w_X-1} \sum_{j=0}^{w_Y-1} 2^{i+j} x_i y_j $$
*   **Object:** **Partial Product Bit** $x_i y_j$. This is the logical AND of bit $x_i$ and $y_j$.
*   **Visual Representation:** **Dot Diagram / Bit Array**. A graphical representation where columns represent weights ($2^k$) and dots represent partial product bits to be summed.

### Derivation: Signed Multiplication (Two's Complement)
**Page 215 (Eq 8.15, 8.16)**
For two's complement numbers, the MSB has a negative weight. The product is derived as:
$$ X \times Y = \left( -2^{w_X-1}x_{w_X-1} + \sum_{i=0}^{w_X-2} 2^i x_i \right) \times Y $$
$$ = -2^{w_X-1}x_{w_X-1}Y + \sum_{i=0}^{w_X-2} 2^i x_i Y $$
*   **Implication for Hardware:**
    1.  Partial products $2^i x_i Y$ must be sign-extended to the full width of the product.
    2.  The last term corresponding to the MSB, $-2^{w_X-1}x_{w_X-1}Y$, requires **subtraction** of the multiplicand.
*   **Optimization (Baugh-Wooley-like):** Subtraction of $Y$ is implemented by adding the bitwise complement $\bar{Y}$ plus 1. The sign extension bits are usually constant and can be pre-calculated/compressed (Page 162, 215).

### Definition: Rectangular Multiplier
**Page 204**
A multiplier where the input bit-widths are different ($w_X \neq w_Y$). This contrasts with a Square Multiplier where inputs have equal width.

---

## 2. Optimization and Recoding Techniques

### Definition: Radix-$2^k$ Multiplication
**Page 216 (Eq 8.17, 8.18)**
Input $X$ is split into chunks $X_i$ of $k$ bits (digits in base $2^k$).
$$ P = \sum_{i=0}^{w/k - 1} 4^i X_i \times Y $$
*   This reduces the number of partial product lines by a factor of $k$.
*   Requires computing $X_i \times Y$ where $X_i \in \{0, \dots, 2^k-1\}$.

### Definition: Modified Booth Recoding (Radix-4)
**Page 217-218**
A technique to reduce the number of partial products by using a signed-digit representation.
$X$ is rewritten as:
$$ X = \sum_{j=0}^{m-1} Z_j 2^{2j} \quad \text{with } Z_j \in \{-2, -1, 0, 1, 2\} $$
*   **Recoding Formula:**
    $$ Z_j = -2x_{2j+1} + x_{2j} + x_{2j-1} $$
    (Requires padding $X$ with $x_{-1}=0$).
*   **Benefit:** Multiplication by $\{0, 1, 2\}$ involves only shifts. Multiplication by negative digits involves negation (bitwise NOT + 1). No "hard" multiples (like $\times 3$) are required.

### Object: Booth Encoded Digit ($Z_j$)
**Page 218 (Table 8.2)**
The truth table mapping 3 consecutive bits of $X$ ($x_{2j+1}, x_{2j}, x_{2j-1}$) to the signed digit $Z_j$.

---

## 3. Tiling and Decomposition (Karatsuba)

### Definition: Multiplier Tiling
**Page 227**
The decomposition of a large $w_X \times w_Y$ multiplication rectangle into smaller sub-multipliers (tiles) $M_i$.
*   **Reconstruction:** The final result is the weighted sum of the sub-multiplier outputs:
    $$ P = \sum_{i} 2^{x_i + y_i} M_i $$
    where $(x_i, y_i)$ are the coordinates of the tile.

### Theorem: Karatsuba Identity (2-Part Splitting)
**Page 244 (Eq 8.55)**
To multiply large numbers $X$ and $Y$, split them into high and low parts: $X = X_1 2^w + X_0$, $Y = Y_1 2^w + Y_0$.
The standard expansion requires 4 multiplications. Karatsuba reduces this to 3 using the identity:
$$ X_1 Y_0 + X_0 Y_1 = (X_0 + X_1)(Y_0 + Y_1) - X_0 Y_0 - X_1 Y_1 $$
*   **Trade-off:** Saves 1 multiplication at the cost of additions/subtractions (pre-additions of operands and post-additions of results).

### Theorem: Generalized Karatsuba (Tiling Rule)
**Page 249 (Eq 8.63)**
Any two sub-multipliers $X_i Y_j$ and $X_k Y_\ell$ in a tiling that share the same weight (i.e., $i+j = k+\ell$) can be paired to save one multiplication:
$$ X_i Y_j + X_k Y_\ell = (X_i + X_k)(Y_j + Y_\ell) - X_i Y_\ell - X_k Y_j $$
This allows applying Karatsuba-like optimizations to irregular or rectangular tilings.

---

## 4. Truncated Multiplication

### Definition: Truncated Multiplier
**Page 237**
A multiplier where the output precision $w_P$ is smaller than the full product width ($w_X + w_Y$). Specifically, bits with weight lower than $2^{\ell_P}$ are not computed.

### Definition: Faithful Rounding (for Multipliers)
**Page 209, 237**
A truncated multiplier is **faithful** if the total error $\delta_{total}$ satisfies:
$$ |\delta_{total}| < 2^{\ell_P} = \text{ulp}(P) $$
Where $\ell_P$ is the position of the LSB of the result.

### Algorithm/Heuristic: Bit Heap Truncation
**Page 169 (Eq 7.19), Page 237**
To minimize area while maintaining faithfulness, partial products are removed from the bit heap (starting from the LSB).
*   **Correction Constant ($C$):** Since truncation always introduces a negative error, a constant $C$ is added to recenter the error around 0.
    $$ C = 2^{\ell_P-1} - 2^{\ell_{ext}} $$
    where $\ell_{ext}$ is the column where bits stop being truncated.
*   **Guard Bits ($g$):** To ensure faithfulness, we compute internally with $g$ extra bits of precision. A rule of thumb (Table 8.4, Page 239) is that $g$ grows logarithmically with the width $w$.

---

## 5. Constant Multiplication (SCM)

### Definition: Single Constant Multiplication (SCM)
**Page 367 (Eq 12.1)**
Multiplication of a variable $X$ by a constant $C$.
$$ X \times C = \sum_{i=0}^{w_C-1} c_i 2^i X $$
Implemented as a graph of shifts and adders (Adder Graph).

### Definition: Canonical Signed Digit (CSD)
**Page 368**
A unique signed-digit representation of a constant $C$ using digits $\{-1, 0, 1\}$ that guarantees the minimal number of non-zero digits (Hamming weight). No two consecutive digits are non-zero.
*   **Property:** Minimizes the number of adders/subtractors in a shift-and-add multiplier.

### Definition: KCM (Ken Chapman's Multiplier)
**Page 384**
A table-based constant multiplication method optimized for FPGAs.
*   **Formula:**
    $$ C \times X = \sum_{k=0}^{\lceil w_X/\alpha \rceil - 1} (C \cdot X_k) 2^{k\alpha} $$
    where $X$ is split into $\alpha$-bit chunks $X_k$.
*   **Implementation:** The terms $(C \cdot X_k)$ are precomputed and stored in Look-Up Tables (LUTs).

---

## 6. Squaring ($X^2$)

### Theorem: Bit Complexity of Squaring
**Page 445 (Eq 14.1)**
Squaring an integer $X$ requires roughly half the partial products of a general multiplication $X \times Y$.
$$ X^2 = \sum_{i=0}^{n-1} 2^{2i} x_i + \sum_{0 \le j < i < n} 2^{i+j+1} x_i x_j $$
*   **Proof Sketch:** In the partial product matrix for $X \times X$, terms $x_i x_j$ and $x_j x_i$ (where $i \neq j$) are identical. They can be combined into $2 x_i x_j$ (a left shift). The diagonal terms are $x_i x_i = x_i$ (since $x \in \{0,1\}$).

---

## 7. Floating-Point Multiplication

### Definition: Floating-Point Product
**Page 343 (Eq 11.1)**
For inputs $X = (-1)^{s_X} 2^{E_X} M_X$ and $Y = (-1)^{s_Y} 2^{E_Y} M_Y$:
$$ X \times Y = (-1)^{s_X \oplus s_Y} \cdot 2^{E_X + E_Y - E_0} \cdot (M_X \times M_Y) $$
where $M_X, M_Y \in [1, 2)$ are normalized significands.

### Definition: Product Normalization
**Page 343-344**
The significand product $P = M_X \times M_Y$ lies in $[1, 4)$.
*   If $P \in [2, 4)$, the result must be shifted right by 1, and the exponent incremented.
*   If $P \in [1, 2)$, the result is already normalized.

### Definition: Injection Rounding
**Page 346**
A technique to perform rounding without a separate adder. A constant bit (value $2^{-\ell_{rounding}}$) is added into the partial product reduction tree (Bit Heap). Truncating the result after summation is then equivalent to rounding to nearest ties to away.