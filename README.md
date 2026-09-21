# An improved Littlewood constant and structural inverse theorems

Lean 4 formalization of *An improved Littlewood constant and structural inverse theorems*. The development covers the two main theorems, their supporting results, applications and examples, and both appendices.

The project uses **Lean 4.32.0** and **mathlib v4.32.0**. Seven external mathematical results are explicitly declared as Lean axioms; their statements, sources, and uses are documented below. The internal proofs contain no `sorry`, `admit`, or `native_decide`.

## Manuscript

- [Revised LaTeX source prepared for arXiv](manuscript/Littlewood_constant_inverse_arxiv.tex)
- [Reference manuscript PDF](manuscript/Littlewood_constant_inverse.pdf)
- [Reference manuscript LaTeX](manuscript/Littlewood_constant_inverse.tex)

The revised source contains presentation and contact-information updates. The reference snapshot dated 2026-09-06 is preserved for the proof-coverage map and archived manuscript checksums; the mathematical statements and proofs are unchanged.

## Main results and entry points

For a finite integer set $A$, write

$$
F_A(t)=\sum_{a\in A}e^{2\pi iat},\qquad
\|F_A\|_1=\int_0^1 |F_A(t)|\,dt.
$$

The quantitative theorem proves that, for every $\varepsilon>0$ and all sufficiently large finite integer sets $A$,

$$
\|F_A\|_1\ge(c_*-\varepsilon)\log |A|,
\qquad c_*>0.2459209213577253>0.2459209.
$$

Here $c_*$ is the constant defined by the manuscript's sinc integrals and convergent series. Its numerical lower bound is proved using exact certificates in Lean.

The structural theorem concerns the specified assembly class: dense separated blocks and long arithmetic blocks, assembled through Sidon residue sets with arbitrary finite tree depth, together with the permitted high-order Freiman models. For fixed geometric parameters, $\|F_A\|_1\le K\log|A|$ implies that all but an $\varepsilon$-fraction of $A$ can be covered by a bounded number of pairwise disjoint subsets of linear size and bounded doubling. The constants are uniform over the set and its assembly. Membership in this class is an explicit hypothesis; the theorem does not assert this conclusion for every set with small $L^1$ norm.

All theorem names below are in the namespace `LittlewoodInverse`.

| Manuscript result | Lean theorem | Source |
|---|---|---|
| Theorem 1.1: quantitative Littlewood bound | `quantitative_theorem` | [QuantitativeTheorem.lean](LittlewoodInverse/QuantitativeTheorem.lean) |
| Theorem 1.5: structural inverse theorem | `structural_inverse_theorem` | [TerminalCover.lean](LittlewoodInverse/TerminalCover.lean) |
| Corollary 1.6: macroscopic hereditary energy | `macroscopic_energy_corollary` | [Corollaries.lean](LittlewoodInverse/Corollaries.lean) |
| Corollary 9.3: exceptional perturbations | `exceptional_perturbation_corollary` | [Corollaries.lean](LittlewoodInverse/Corollaries.lean) |
| Long-block signed progression representation | `long_block_signed_progressions` | [LongBlockSigned.lean](LittlewoodInverse/LongBlockSigned.lean) |
| Appendix A: exact numerical bound | `NumericalConstant.littlewoodCoefficient_gt_sharp_decimal` | [NumericalConstant.lean](LittlewoodInverse/NumericalConstant.lean) |
| Appendix B: Landau bound and sharpness | `Landau.spectral_bound`, `Landau.extremizer_attains` | [LandauSpectral.lean](LittlewoodInverse/LandauSpectral.lean), [LandauSharpness.lean](LittlewoodInverse/LandauSharpness.lean) |
| Appendix B: two-sided completion asymptotic | `Landau.completion_log_asymptotic` | [LandauResults.lean](LittlewoodInverse/LandauResults.lean) |

The exact main-theorem specifications are in [Statements.lean](LittlewoodInverse/Statements.lean), and the geometric hypotheses are in [Geometry.lean](LittlewoodInverse/Geometry.lean). A `Prop` definition specifies a statement; the theorem entries above provide its proof. The [proof coverage map](verification/PROOF_COVERAGE.md) records the full manuscript correspondence, including general abelian-group versions and a necessary `0 < δ < 1` clarification in a Section 10 example.

## External inputs and trust boundary

There are exactly seven project-declared mathematical axioms:

| External input | Declaration | Role |
|---|---|---|
| Weighted McGehee–Pigno–Smith inequality | `External.mps_weighted` | Structural theorem |
| Polynomial Balog–Szemerédi–Gowers theorem | `External.polynomial_bsg` | Structural theorem |
| Schwarz–Poisson boundary theorem | `HardyExternal.schwarz_integral_boundary` | Quantitative theorem |
| Hardy radial boundary theorem and coefficient identification | `HardyExternal.bounded_holomorphic_radial_boundary` | Quantitative theorem |
| Green–Sanders quantitative idempotent theorem | `BackgroundExternal.green_sanders` | Additional signed representation result |
| Bloom–Green inverse theorem | `BackgroundExternal.bloom_green_inverse` | Background comparison only |
| Bloom–Green constant bound | `BackgroundExternal.bloom_green_constant` | Background comparison only |

The quantitative main theorem depends only on the two Hardy/Poisson inputs. The structural main theorem depends only on MPS and BSG. Neither main theorem uses Green–Sanders or the Bloom–Green comparisons. The numerical certificate and the final two-sided completion asymptotic use no project-declared mathematical axioms.

These seven results are assumed, not reproved by this repository. Lean checks the internal proofs relative to those declarations and its standard foundational axioms, such as `propext`, `Classical.choice`, and `Quot.sound`. See [external inputs](verification/EXTERNAL_INPUTS.md) for precise hypotheses and normalizations, and the [bibliography audit](verification/BIBLIOGRAPHY_AUDIT.md) for the role of each reference.

## Build and audit

Install [elan](https://github.com/leanprover/elan), then run the following from the repository root:

```text
lake exe cache get
lake build
lake env lean AuditAll.lean
lake env lean verification/MainTheoremsAudit.lean
lake env lean verification/AppendixBAudit.lean
```

[lean-toolchain](lean-toolchain) pins the Lean version, and [lake-manifest.json](lake-manifest.json) locks the dependencies. `AuditAll.lean` prints the axiom dependencies of every public project theorem. The focused audits inspect the main results and Appendix B.

To regenerate the declaration inventory and check for proof placeholders, unlisted axioms, and omitted formal modules, use Python 3:

```text
python verification/generate_audit.py --strict
lake env lean AuditAll.lean
```

The generated audit files are included, so ordinary building and Lean proof checking do not require Python. The numerical-certificate generator is also optional; the generated certificate is checked by Lean. See [verification instructions](verification/VERIFICATION.md) for the audit reports and their scope.

The included verification snapshot records 137 formal modules, 1,219 theorem declarations, and axiom-dependency reports for all 1,216 public theorems. The archived build and dependency logs are preserved in `verification/`. The [publication checks](verification/PUBLICATION.md) describe the source-integrity and audit checks performed when preparing this repository.

## Repository layout

| Path | Contents |
|---|---|
| [LittlewoodInverse.lean](LittlewoodInverse.lean) | Top-level import |
| [LittlewoodInverse/](LittlewoodInverse/) | Definitions, proofs, numerical certificates, and explicit external inputs |
| [verification/](verification/) | Manuscript coverage, source and dependency audits, reports, and certificate generation |
| [manuscript/](manuscript/) | Revised LaTeX source and the reference manuscript snapshot (2026-09-06) |
| [AuditAll.lean](AuditAll.lean) | Complete public-theorem dependency audit |
