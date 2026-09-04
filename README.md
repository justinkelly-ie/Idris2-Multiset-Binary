# ⚡ Idris2-Multiset-Binary

**Layer 2a Binary Multiset Logic ($\mathbb{F}_2 = \{0, 1\}$), Mobius Transforms & Lifted Polynumbers for Idris 2**

`Idris2-Multiset-Binary` provides discrete truth-value logic, Boole-Mobius polynomial transforms, lifted polynumbers, and probability bounds for state classification within the **Constructive Multiset Physics Framework**.

---

## Key Modules & Specifications

| Module | Architectural Role & Domain Scope |
| :--- | :--- |
| **`Logic.BoolePolynumber`** | Boolean polynumber expansion (`Multiset Bit Nat`) and binary term addition/multiplication. |
| **`Logic.LiftedPolynumber`** | Row 2 Lifted Polynumbers over signed integer coefficients (`LiftedPolynumber v`). |
| **`Logic.MobiusTransform`** | Discrete Mobius transform, subset inversion, and Hailperin probability bounds (`ProbBounds`). |
| **`Logic.BooleFunction`** | Binary boolean functions ($\mathbb{F}_2^n \to \mathbb{F}_2$) over multiset singletons. |
| **`Logic.Circuit`** | Logic gate circuit resolution, AND/OR/XOR gates, and term cancellation. |
| **`Logic.Syllogism`** | Classical syllogisms (Barbara, Celarent) encoded over multiset intersections. |
| **`Logic.InformationTheory`** | KL divergence, self-information, entropy, and Shannon compression bounds. |
| **`Logic.FunctionalProbability`** | Normalized functional probability weights derived from binary multiset counts. |
| **`Logic.Bridge`** | Lifting bridges connecting $\mathbb{F}_2$ binary states to $\mathbb{Z}$ integer multisets. |

---

## Dependencies

- **`Idris2-Multiset-Core`**
- **`Idris2-Multiset-Transform`**

---

## Building & Usage

Build and install using Idris 2 (`0.8.0`):

```bash
idris2 --build Idris2-Multiset-Binary.ipkg
idris2 --install Idris2-Multiset-Binary.ipkg
```

---

© Justin Kelly. Formalized in pair-programming collaboration with Google Antigravity.
