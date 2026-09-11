# Verification record

## Completed proof checks

The original export passed its full build on 10 September 2026. The submission ZIP was then extracted into a separate directory and rebuilt from its 86 project sources, using the same pinned, cached mathlib dependencies and no precompiled project files. The saved [build log](verification-build.log) records this fresh submission build and the subsequent explicit endpoint audit. Both returned exit code zero. All eleven guarded axiom checks passed, with exactly `propext`, `Classical.choice`, and `Quot.sound`.

This submission preserves all 86 Lean files, `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` byte for byte from that verified export. It adds the finished eight-page paper, its source, publication instructions, and the GitHub workflow. The paper files are unchanged from the rendered and reviewed version.

- Lean: `leanprover/lean4:v4.34.0-rc2`
- mathlib: `de2ef68216c6074f338c8e61890ee0a379ddfb9b`
- Final statements: `XiFamilyChallenge.IndividualNormality` and `XiFamilyChallenge.RationalCombinationNormality`
- Final assembly: `XiFamilySolution.lean`
- Guarded audit: `XiFamilyAxiomCheck.lean`

## Submission check

The final package is checked for completeness, unchanged proof and paper bytes, pinned dependency revisions, valid workflow configuration, and inclusion of `.github/workflows/verify.yml` in the ZIP. `SHA256SUMS` covers all Lean files, the three dependency configuration files, and both paper files.

## GitHub status

No GitHub Actions run for this new repository has been claimed in this package. After upload, open **Actions → Verify Lean** for the public result tied to your exact commit. The workflow retrieves the pinned dependency cache, builds the project sources, and runs the same endpoint checks. It does not reuse a GitHub cache of this project's compiled proofs.

For the meaning and scope of the statements, use [the reviewer guide](REVIEWER-GUIDE.md). Earlier internal source reviews are not represented as external mathematical certification.
