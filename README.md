# 🎛️ idris2-Boole

**A formalization of George Boole's and Norman Wildberger's *Algebra of Boole* using Multiset Algebra in [Idris 2](https://github.com/idris-lang/Idris2).**

[![Idris2](https://img.shields.io/badge/Idris2-Algebra-blue.svg)](https://github.com/idris-lang/Idris2)

---

## 🏛️ The Algebraic Nature of the Algebra of Boole

Wildberger's **Algebra of Boole** (originating from George Boole's 1847 foundation *The Mathematical Analysis of Logic*) is a system of **modulo-2 ring arithmetic** ($\mathbb{F}_2$), not symbolic logic. It differs fundamentally from Huntington and Shannon's modern *Boolean Algebra* by treating exclusive-or (XOR) as the primitive addition operator.

### The Fundamental Shift: Self-Annihilation and Multiset Representation

In standard Boolean algebra, addition is inclusive OR ($\lor$). Because $1 \lor 1 = 1$, elements lack an additive inverse—subtraction is impossible, and linear algebra techniques cannot be applied.

In the Algebra of Boole, addition is modulo-2 XOR ($+$). Because **$x + x = 0$**, every element is its own additive inverse. This property establishes a **Boolean Ring** (a commutative ring with identity where every element is idempotent, $x^2 = x$).

Rather than relying on primitive/native Idris 2 data types or custom boolean flags, this library implements all Boole expressions using **multisets** (`Multiset Bit state` / `Multiset Bit Nat` from `idris2-Multiset`). Term addition is multiset addition followed by modulo-2 term annihilation (`addMultiset` + `annihilateMultiset`), meaning duplicate terms naturally cancel out to $\emptyset$.

| Property | Algebra of Boole ($\mathbb{F}_2$ Commutative Ring) | Boolean Algebra (Distributive Lattice) |
|---|---|---|
| **Addition ($+$)** | `+` (XOR / Exclusive OR) | `∨` (OR / Inclusive OR) |
| **Multiplication ($\cdot$)** | `*` (AND) | `∧` (AND) |
| **Annihilation** | $1 + 1 = 0$ (Multiset term annihilation) | $1 \lor 1 = 1$ |
| **Additive Inverse** | Yes ($x + x = 0$) | No |
| **Subtraction** | Supported ($x - y \equiv x + y$) | Not defined |
| **Complement (NOT $x$)** | $1 + x$ (algebraically derived) | $\bar{x}$ (primitive connective) |
| **Inclusive OR ($x \lor y$)** | $x + y + xy$ (algebraically derived) | $x \lor y$ (primitive connective) |
| **Representation** | **Unique** multilinear polynomial (Boole polynumber multiset) | Non-unique sum-of-products |
| **Equivalence** | Direct multiset / coefficient vector comparison | SAT problem (NP-complete) |

---

## 🗃️ Core Multiset Architecture

All operations in `idris2-Boole` are implemented over multiset structures:

$$\text{BoolePolynumber} = \text{Multiset Bit Nat}$$

### Key Data Structures

#### 1. `Bit` (`Math.Unixel.Bit`)
The coefficient field $\mathbb{F}_2 = \{0, 1\}$. Addition (`addBit`) is modulo-2 XOR, and multiplication (`mulBit`) is logical AND.

#### 2. `BoolePolynumber` ([Logic.BoolePolynumber](file:///var/home/justin/Projects/Idris2-Boole/src/Logic/BoolePolynumber.idr))
A multiset `Multiset Bit Nat` where each entry `(k, One)` represents a product term with subset index $k$.
- **Addition**: `addBoolePoly p q = annihilateMultiset (addMultiset p q)`. Duplicate terms cancel automatically ($1 + 1 = 0$).
- **Multiplication**: `mulBoolePoly` applies Wildberger's idempotent rule ($x^2 = x$) via bitwise OR of subset indices ($a_k \cdot a_l = a_{k | l}$).

#### 3. `Circuit` ([Logic.Circuit](file:///var/home/justin/Projects/Idris2-Boole/src/Logic/Circuit.idr))
Aliased directly to `BoolePolynumber`. Circuit logic gates evaluate natively as multiset polynomials without AST tree traversal:
- $\text{NOT}(a) = 1 + a$
- $\text{OR}(a, b) = a + b + ab$
- $\text{NAND}(a, b) = 1 + ab$
- $\text{NOR}(a, b) = 1 + a + b + ab$
- $P \to Q = 1 + P + PQ$

#### 4. `LiftedPolynumber` & `LiftedBooleFraction` ([Logic.LiftedPolynumber](file:///var/home/justin/Projects/Idris2-Boole/src/Logic/LiftedPolynumber.idr))
Extends Row 1 $\mathbb{F}_2$ logic into Row 2 $\mathbb{Z}$ integer arithmetic. Monomials are multisets `Monomial v = Multiset BoxInt v` closed under $x^2 = x$ via `idempotentCollapse`. `LiftedBooleFraction` embeds an integer-weighted unixel numerator over a strictly positive unit denominator (`Unixel TrivialBase`).

#### 5. `ProbBounds` & Hailperin Bounds ([Logic.MobiusTransform](file:///var/home/justin/Projects/Idris2-Boole/src/Logic/MobiusTransform.idr))
Row 4 probability interval bounds $[lo, hi]$ derived directly from Möbius-inverted coefficients using inclusion-exclusion principles (including `threeEventUnionBounds` for George Boole's last challenge problem).

---

## 🔄 Algebraic Transforms & Bridges

### The Boole-Möbius Transform ([Logic.MobiusTransform](file:///var/home/justin/Projects/Idris2-Boole/src/Logic/MobiusTransform.idr))
A self-inverse linear transform ($T^2 = I$ over $\mathbb{F}_2$) mapping a function's truth table to its unique `BoolePolynumber` coefficients.

### Integer Möbius Transform ([Logic.Bridge](file:///var/home/justin/Projects/Idris2-Boole/src/Logic/Bridge.idr))
Connects Row 1 ($\mathbb{F}_2$) to Row 2 ($\mathbb{Z}$) via `bitsToBoxInts`, `booleToIntPoly`, `mobiusTransformZ`, and `mobiusInverseZ`.

### Ongoing Sequences ([Logic.OnCircuit](file:///var/home/justin/Projects/Idris2-Boole/src/Logic/OnCircuit.idr))
Supports dynamic finitist sequence streams (`OnCircuit`, `OnByte`, `OnTruthTable`) for unbounded expanding circuit evaluations and pointwise Möbius transforms.

---

## 📁 Module Organization

All modules are located under `Logic.*`:

| Module | Description |
|---|---|
| [Logic.BoolePolynumber](file:///var/home/justin/Projects/Idris2-Boole/src/Logic/BoolePolynumber.idr) | `BoolePolynumber` multiset type (`Multiset Bit Nat`), sparse/dense conversion, XOR addition, idempotent multiplication, evaluation, and equivalence checks. |
| [Logic.BooleFunction](file:///var/home/justin/Projects/Idris2-Boole/src/Logic/BooleFunction.idr) | `BooleFunction` truth table record, evaluation, and isomorphism with `BoolePolynumber`. |
| [Logic.MobiusTransform](file:///var/home/justin/Projects/Idris2-Boole/src/Logic/MobiusTransform.idr) | Self-inverse Boole-Möbius transform ($T^2 = I$), Hailperin probability bounds (`ProbBounds`), Boole-Fréchet bounds, George Boole's last challenge problem, and `OnSeq` sequence integration. |
| [Logic.LiftedPolynumber](file:///var/home/justin/Projects/Idris2-Boole/src/Logic/LiftedPolynumber.idr) | Row 2 multiset polynomials over $\mathbb{Z}$, monomial `idempotentCollapse`, `LiftedBooleFraction`, and standard `Num`/`Neg`/`Cast` instances. |
| [Logic.Bridge](file:///var/home/justin/Projects/Idris2-Boole/src/Logic/Bridge.idr) | Bit $\to$ BoxInt embedding, `booleToIntPoly`, forward and inverse integer Möbius transforms (`mobiusTransformZ` & `mobiusInverseZ`). |
| [Logic.Circuit](file:///var/home/justin/Projects/Idris2-Boole/src/Logic/Circuit.idr) | `Circuit` type alias to `BoolePolynumber`, pure algebraic gate definitions, and lifting to `IntPolynumber`. |
| [Logic.OnCircuit](file:///var/home/justin/Projects/Idris2-Boole/src/Logic/OnCircuit.idr) | Finitist ongoing sequences (`OnCircuit`, `ClipCircuit`, `OnByte`). |
| [Logic.FunctionalProbability](file:///var/home/justin/Projects/Idris2-Boole/src/Logic/FunctionalProbability.idr) | Hehner functional probability normalization (`MSetFractionVexel`, `stateProbability`, `normalizeFraction`). |
| [Logic.Syllogism](file:///var/home/justin/Projects/Idris2-Boole/src/Logic/Syllogism.idr) | Classical Aristotelian syllogisms (Barbara, Celarent, Darii, Ferio, Cesare, Camestres) and Stoic inference rules evaluated algebraically over multisets. |
| [Logic.Interfaces](file:///var/home/justin/Projects/Idris2-Boole/src/Logic/Interfaces.idr) | Conversions (`bitsToIntegers`, `integersToBits`) and linear vector helper utilities. |

---

## 🛠️ Installation & Pack Integration

To register `idris2-Boole` in your local Pack database, add the following to your `pack.toml`:

```toml
[custom.all.idris2-Boole]
type = "local"
path = "../Idris2-Boole"
ipkg = "idris2-Boole.ipkg"
```

Then add `idris2-Boole` to your `.ipkg` dependency list:

```
depends = base, contrib, linear, idris2-Multiset, idris2-Boole
```

---

## 📚 References

- **Norman J. Wildberger**: *Algebra of Boole* (Mathematical Foundations Lectures 255–280).
- **George Boole (1847)**: *The Mathematical Analysis of Logic*.
- **Theodore Hailperin (1986)**: *Boole's Logic and Probability*.
- **Eric Hehner**: *a Probability Theory*.

---

© Justin Kelly. All rights reserved.
