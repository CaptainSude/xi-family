# A New Family of Normal Numbers

**[Read the eight-page paper](paper/a-new-family-of-normal-numbers.pdf)** · [Upload guide](START-HERE.md) · [Review the formal statements](REVIEWER-GUIDE.md)

This repository contains the paper, its editable LaTeX source, and the complete Lean proofs for the Xi family and its rational-combination theorem.

For integers `b >= 2` and positive generators `a, c`, define

$$
\xi_{b,c;a}=\sum_{m\in\{a^i c^k:i,k\ge0\}}\frac{1}{m b^m},
$$

counting each distinct integer `m` once.

## The two main theorems

- **Normality.** If `a, b, c >= 2` and `gcd(c, a*b) = 1`, then this number is normal in base `b`.
- **Rational combinations.** Fix `a, b >= 2`. Choose finitely many distinct eligible parameters `c`. Every rational linear combination of the corresponding Xi values with coefficients not all zero is normal in base `b`. Any rational constant may also be added. The parameters may share primes or be powers of one another.

Normality means the expected limiting frequency of every finite digit word, including leading-zero words, counting overlapping occurrences through every prefix length.

The definition includes the classical Stoneham boundary `xi(b,c;1) = 1/b + alpha(b,c)`. The two new formal theorems require `a >= 2`.

## Read and verify

- [Paper](paper/a-new-family-of-normal-numbers.pdf) and [LaTeX source](paper/a-new-family-of-normal-numbers.tex)
- [Independent statement file](XiFamilyChallenge.lean): explicit series and word frequencies; imports only mathlib
- [Solution](XiFamilySolution.lean): proves both statements
- [Definition correspondence](XiFamilyStatement.lean)
- [Individual normality](XiFamilyNormality.lean) and [rational combinations](XiArithmeticNormality.lean)
- [Guarded axiom checks](XiFamilyAxiomCheck.lean)
- [Verification record](VERIFICATION.md) and [saved local build log](verification-build.log)

Open **Actions → Verify Lean** to inspect the check for the exact commit you are reading. The workflow checks the fingerprints, builds the sources, and enforces the allowed axiom list. It runs on pushes, pull requests, and manual requests.

To reproduce the proof check locally, install [Lean's elan toolchain manager](https://lean-lang.org/install/) and run from the repository directory:

```text
lake --no-cache exe cache get
lake --no-cache build
lake --no-cache env lean XiFamilyAxiomCheck.lean
```

The toolchain and dependency revisions are pinned. The allowed endpoint axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`; the sources contain no unfinished proofs or additional axiom declarations. The analytic estimates are proved within the development.

The [reviewer guide](REVIEWER-GUIDE.md) explains how to check the correspondence between the paper and the formal statements. Local verification and a future GitHub run are distinguished in [the verification record](VERIFICATION.md).

## Context and credits

The paper explains the connections to Stoneham numbers and Dibag's localized logarithms, and credits the earlier normal-number constructions and the rational-orbit estimate of Vandehey. The Lean development independently proves sufficient analytic estimates and reuses supporting modules from the earlier [Xi normality project](https://github.com/CaptainSude/xi-normality) and [Stoneham sum project](https://github.com/CaptainSude/Stoneham-sum-normal), together with Lean and mathlib. Full mathematical references are in the paper.

The paper's linear-independence corollary is an ordinary consequence of the rational-combination theorem; the two main theorems are the explicit formal endpoints of this package.
