# ⚡ Idris2-Multiset-Binary

**Layer 2a Binary Multiset Logic ($\mathbb{F}_2 = \{0, 1\}$) & Mobius Transforms for Idris 2**

`Idris2-Multiset-Binary` provides discrete truth-value logic, Mobius polynomial transforms, and bit vector circuit resolution for state classification within the **Constructive Multiset Physics Framework**.

---

## Key Modules & Specifications

| Module | Architectural Role & Domain Scope |
| :--- | :--- |
| **`Logic.BooleFunction`** | Binary boolean functions ($\mathbb{F}_2^n \to \mathbb{F}_2$) over multiset singletons. |
| **`Logic.BoolePolynumber`** | Boolean polynumber expansion and Mobius inversion polynomials. |
| **`Logic.MobiusTransform`** | Discrete Mobius transform and fast multiset subset inversion. |
| **`Logic.Circuit`** | Logic gate circuit resolution, AND/OR/XOR gates, and term cancellation. |
| **`Logic.Syllogism`** | Classical syllogisms and Aristotelian logic encoded over multiset intersections. |
| **`Logic.FunctionalProbability`** | Normalized functional probability weights derived from binary multiset counts. |

---

## Dependencies

- **`Idris2-Multiset-Core`**
- **`Idris2-Multiset-Transform`**

---

## Building & Usage

Build the package using `pack`:

```bash
pack build Idris2-Multiset-Binary.ipkg
```

---

&copy; Justin Kelly. Formalized in pair-programming collaboration with Google Antigravity.
