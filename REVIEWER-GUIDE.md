# Review the paper and its formal statements

Start with Theorems 1 and 2 of [A New Family of Normal Numbers](paper/a-new-family-of-normal-numbers.pdf), then inspect [XiFamilyChallenge.lean](XiFamilyChallenge.lean). Record the exact repository commit and the corresponding successful Actions run.

## Statement correspondence

| Paper | Independent formal statement | Proved solution |
| --- | --- | --- |
| Theorem 1: individual normality | `XiFamilyChallenge.IndividualNormality` | `XiFamilySolution.individual_normality` |
| Theorem 2: rational combinations | `XiFamilyChallenge.RationalCombinationNormality` | `XiFamilySolution.rational_combinations` |
| Both results | Conjunction of the two statements | `XiFamilySolution.full_statement` |

Check the following directly in the Challenge file:

- `value b c a` sums over distinct natural numbers of the form `a^i * c^k`, rather than counting representations. Under the theorem's lower bounds these indices are positive. Coprimality gives the displayed double-series identity.
- `normal b x` counts visits of the fractional parts of `b^n * x` to all half-open radix intervals. Such intervals represent all finite digit words, including leading zeros. Successive positions overlap, and the limit is taken through all natural prefix lengths.
- Theorem 1 requires `a,b,c >= 2` and `gcd(c,a*b)=1`.
- Theorem 2 fixes `a,b >= 2`, uses a finite set of distinct eligible `c` values, allows arbitrary rational coefficients with at least one nonzero coefficient, and allows any rational constant. It imposes no coprimality between different `c` values.
- The definition's `a=1` Stoneham boundary is not a substitution into either new main theorem, both of which assume `a>=2`.

[XiFamilyStatement.lean](XiFamilyStatement.lean) proves the correspondence with the internal value and normality definitions. [XiFamilySolution.lean](XiFamilySolution.lean) supplies proved terms for the complete explicit statements, without additional hypotheses.

## Reproduce the check

```text
lake --no-cache exe cache get
lake --no-cache build
lake --no-cache env lean XiFamilyAxiomCheck.lean
```

The final command enforces exactly `propext`, `Classical.choice`, and `Quot.sound` for all eleven listed endpoints. An unexpected axiom or unfinished proof causes its message guards to fail. The workflow also verifies `SHA256SUMS`, recording the exact source, toolchain, dependency, and paper bytes in this submission. The checksums identify files; the Lean build checks the proof terms.

The paper uses Vandehey's published orbit estimate for a concise analytic presentation. The Lean development independently proves sufficient estimates by repeated differencing. The ordinary linear-independence corollary is explained in the paper; it is not a separate formal endpoint.

## Record an independent review

A useful review identifies the commit, which statements and definitions were examined, whether the reviewer reran Lean, and the conclusion about the match between the paper and formal statements. The Challenge/Solution separation makes this comparison accessible; an external review is a separate contribution from the automated proof check. Neither the workflow nor the checksums establish bibliographic novelty.
