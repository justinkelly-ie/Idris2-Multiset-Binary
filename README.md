# FinSc-Multiset-Binary

[![Idris 2 Verification](https://img.shields.io/badge/Idris_2-0.8.0-blue.svg)](https://www.idris-lang.org/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

**Layer 2b Boolean Field Engines, Möbius Transforms & Functional Probability for Idris 2**

`FinSc-Multiset-Binary` forms **Layer 2b** of the 10-layer constructive non-linear multiset science framework. It provides binary logic field engines ($\mathbb{F}_2$), Boolean function representations, Möbius spectral inversion transforms, digital gate circuits, syllogistic inference engines, and discrete functional probability bounds.

---

## 📦 Core Library Architecture & Modules

### 1. `Logic.BooleFunction` & `Logic.Interfaces`
- **Boolean Logic Fields ($\mathbb{F}_2$):** Direct representations of Boolean functions, truth tables, and binary logic operations over discrete `Bit` singletons.
- **Algebraic Logic Interfaces:** Core open interfaces for binary logic functions, negation, conjunction, and disjunction.

### 2. `Logic.MobiusTransform`
- **Möbius Spectral Transforms:** Forward and inverse Möbius transforms mapping binary Boolean polynomials into functional probability distributions.
- **Binary State Sifting:** Discrete Möbius state sifting linking binary combinatorial state spaces to manifest grid dimensions.

### 3. `Logic.BoolePolynumber` & `Logic.LiftedPolynumber`
- **Boolean Polynomial Rings:** Generating polynomials over discrete `Bit` multisets.
- **Lifted Polynumber Algebra:** Higher-order polynomial lifting for multi-variable binary logic equations.

### 4. `Logic.Circuit`, `Logic.OnCircuit` & `Logic.Syllogism`
- **Digital Logic Gate Circuits:** Constructive gate circuits (`And`, `Or`, `Xor`, `Nand`, `Nor`) and circuit evaluation pipelines.
- **Syllogistic Inference:** Syllogistic logic engines for automated discrete reasoning over binary state assertions.

### 5. `Logic.FunctionalProbability` & `Logic.InformationTheory`
- **Discrete Functional Probability:** Exact rational probability bounds computed directly from Boolean multiset counts without real-number limits.
- **Information Theory:** Shannon-Huffman prefix coding, cross-entropy, and information quadrance over binary distributions.

### 6. `Logic.Bridge`
- **Binary Multiset Bridge:** Convertible bridge functions connecting binary logic quanta directly to multiset resource channels.

---

## 🚀 Building & Installing

```bash
idris2 --build FinSc-Multiset-Binary.ipkg
idris2 --install FinSc-Multiset-Binary.ipkg
```

---

## 🔬 Architectural Principles

- **Total Constructivism:** Enforces `%default total` across all binary logic and probability functions.
- **Exact Binary Spectral Analysis:** Discrete Möbius transforms replacing continuous probability density functions.
- **Zero Floating-Point Drift:** Rational probability bounds computed via Diophantine integer counts.
