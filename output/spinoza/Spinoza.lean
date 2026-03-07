import Spinoza.ModalLogic
import Spinoza.Domain
import Spinoza.Relations
import Spinoza.Definitions
import Spinoza.Axioms
import Spinoza.Part1_Core
import Spinoza.Part1_God
import Spinoza.Part1_Necessity
import Spinoza.MindAxioms
import Spinoza.Part2_Mind
import Spinoza.AffectAxioms
import Spinoza.Part3_Affects
import Spinoza.Part4_Bondage
import Spinoza.Part5_Freedom

/-!
# Spinoza's *Ethics* Part I — Lean 4 Formalization

A formal encoding of the propositional structure of Part I of Spinoza's
*Ethica Ordine Geometrico Demonstrata* (1677).

## Architecture
- **S5-collapse**: necessity = truth (Spinoza's necessitarianism, 1P33)
- **SpinozaFramework**: typeclass bundling all primitive relations
- **Axioms**: Spinoza's A1–A7 + PSR_symmetric as Lean `axiom` declarations
- **Scope**: 1P1–1P17, 1P29, 1P33

## AMS Classification
- 03A05: Philosophical and critical (foundations)
- 03B45: Modal logic
- 03B60: Other nonclassical logic

## Module Dependency Order
ModalLogic → Domain → Relations → Definitions → Axioms
  → Part1_Core → Part1_God → Part1_Necessity

## Coverage (Skeleton)
| Item | Type | Status |
|------|------|--------|
| D1–D8 | Definitions | ✅ formalized |
| A1–A7 | Axioms | ✅ (A6 deferred) |
| PSR | Axiom | ✅ |
| 1P2, 1P3 | Lemmas | ✅ provable |
| 1P5, 1P6, 1P7 | Theorems | ⚠️ sorry (key sorries) |
| 1P11, 1P14 | Theorems | ⚠️ sorry (need attribute axiom) |
| 1P29, 1P33 | Theorems | ⚠️ sorry (need mode axiom) |
-/
