# Publication checks

Prepared on 2026-09-22 from `LittlewoodInverse_Lean4_20260917.zip`.

- All 137 formal Lean module files match the proof-source SHA-256 values in `validation_summary.json`.
- The reference manuscript PDF and TeX match the archived manuscript SHA-256 values.
- The strict source audit was rerun: 1,219 theorem declarations, seven explicitly allowed external mathematical axioms, no forbidden proof placeholders, no unlisted axioms, and no omitted formal modules.
- The archived dependency reports match all 1,216 public theorem declarations, with no missing reports, unexpected dependencies, or reported errors.

The successful Lean build and kernel-dependency logs are the original verification records. Publication preparation checked their consistency with the source snapshot; it did not run a new Lean build.

The public README was rewritten, the root package name in `lake-manifest.json` was corrected from a residual project name to `LittlewoodInverse`, and internal attachment identifiers were removed from `manuscript/VERSION.txt`. The pinned dependency revisions and mathematical proof files were not changed. Git attributes preserve file bytes for checksum reproducibility.

`DELIVERY_MANIFEST.json` contains SHA-256 values for the published files other than the manifest itself, using the original `LittlewoodInverse/` archive prefix. It was regenerated after these publication edits. `validation_summary.json` continues to describe the original proof and manuscript verification snapshot.

## Manuscript presentation update

The revised source prepared for arXiv is included as `manuscript/Littlewood_constant_inverse_arxiv.tex`. It updates the title, abstract, typography, AI statement, affiliation, and contact details. The original manuscript PDF and TeX remain the reference snapshot for the archived verification records; the mathematical statements and proofs are unchanged.
