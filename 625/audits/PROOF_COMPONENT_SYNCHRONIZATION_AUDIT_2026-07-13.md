# Proof-component synchronization audit

**Date:** 2026-07-13
**Scope verdict:** **PASS for document propagation and traceability.**

This is a synchronization audit, not a new proof of the theorem.  It checks
that the concise draft and focused route notes state the repairs already
present in the authoritative manuscript
`../proofs/COMPLETE_PROOF_SELF_CONTAINED.md`.  The mathematical defects,
repairs, and route-specific regression reviews are recorded separately in
`ADVERSARIAL_LEAP_AUDIT_2026-07-13.md`.

## 1. Authority and method

The self-contained Markdown manuscript is the sole authoritative proof.  Its
generated TeX and the two byte-identical PDF copies are publication forms of
that same manuscript.  The other proof files are focused supporting notes and
route history; they are not an independent source of truth.  If future wording
diverges, the canonical manuscript controls and the discrepancy must be
logged rather than silently reconciled.

The audit compared each repaired proof obligation with its corresponding
component discussion, checked the direction and quantifiers of the statements,
and confirmed that the concise draft's dependency order does not substitute a
component assertion for the canonical lemma.  It did not rederive the
probabilistic or analytic estimates.

## 2. Traceability matrix

| Proof obligation | Authoritative location | Synchronized support | Propagation result |
|---|---|---|---|
| Uniform signed-root corridor | Canonical Lemma 3.1, especially (3.5)--(3.7) and proof (3.16)--(3.19) | `../proofs/ALPHA_MINUS_TWO_ROUTE.md`, (5.0a)--(5.0d); `../proofs/COMPLETE_PROOF_DRAFT.md`, (1.5a)--(1.5b) and (2.5a)--(2.6) | The support notes now localize every zero of `L_S(n,k)+ck`, uniformly for the relevant supports, phase, and `0<=c<=ln 2`, before applying the derivative estimate.  The signed-root location is no longer used to justify its own corridor. |
| Finite optimizer, effective multiplier, and tangent rounding | Canonical (3.9b), (5.13)--(5.19) | `../proofs/ALPHA_MINUS_TWO_ROUTE.md`, (4.1a)--(4.2a); `../proofs/COMPLETE_PROOF_DRAFT.md`, (2.8a)--(2.8c) | The support notes start from the exact finite-`n` constrained optimizer, distinguish the effective tilt from the raw multiplier, display the two signed rounding errors and their correction, and use tangency only after both integer constraints are restored. |
| Globalization of endpoint decorations and middle high cells | Canonical Lemma 8.3, (8.25a), (8.26a), and (8.29a)--(8.29b) | `../proofs/DENSE_FOUR_TYPE_MATCHING.md`, (5.5)--(5.9), Theorem 6.1, and Corollary 6.2; `../proofs/COMPLETE_PROOF_DRAFT.md`, (5.9a)--(5.9c); `../proofs/ALPHA_MINUS_TWO_ROUTE.md`, (8.4a)--(8.4c) | The support notes now include the endpoint-decoration product with no extra multiplicity, joint conditioned threshold expansion, both residual-mass branches, and the final sum over all high skeletons.  Per-cell estimates are not presented as if they already implied the global bound. |
| One-sided residual attachment estimate | Canonical Lemma 9.1 and Proposition 9.2, (9.3) and (9.23) | `../proofs/RESIDUAL_ATTACHMENT.md`, Theorem 2.1 and (2.2)--(2.4); `../proofs/COMPLETE_PROOF_DRAFT.md`, (4.1) | The synchronized claim is only the uniform upper bound actually proved and used.  No lower bound on the conditional attachment factor is asserted; nonnegativity of the final normalized logarithm comes separately from variance. |
| Growing amplification parameter and final events | Canonical Lemma 10.2, (10.10)--(10.13), and Section 11 | `../proofs/ALON_CONCENTRATION_EXTENSION.md`, Theorem 2.2 and (2.12a); `../proofs/ALPHA_MINUS_TWO_ROUTE.md`, (8.5)--(8.8); `../proofs/COMPLETE_PROOF_DRAFT.md`, (6.2)--(6.5) and the named events in Section 7 | The support notes choose a deterministic `r_n` tending to infinity, track the common deterministic `o(1)` exceptional term, define the deterministic additive error, and intersect the named chromatic and cocolouring events by a union bound.  They preserve the full integer-sequence quantifier. |

## 3. Historical-audit scope

`FULL_PROOF_AUDIT_1.md` through `FULL_PROOF_AUDIT_4.md`,
`DENSE_FOUR_TYPE_MATCHING_AUDIT.md`, and
`RESIDUAL_ATTACHMENT_AUDIT.md` retain their 2026-07-12 bodies and verdicts.
Concise notices at their tops now state that those verdicts apply to the bytes
then reviewed, not to the later repaired or synchronized files.  The notices
point readers to the adversarial audit and this traceability record.  No
historical verdict has been retroactively represented as review of new bytes.

The user-supplied report and checker under `../verification/` were not edited.
Their conclusions remain limited to the manuscript hash and finite diagnostics
identified in their existing provenance record.

## 4. Artifact scope and unchanged publication bytes

The proof-content synchronization changed supporting notes, indexes, work
records, audit notices, and repository/release metadata only.  It did not
change the canonical manuscript, generated TeX, or either PDF copy.  Their
SHA-256 identifiers remain:

```text
9EA27F617D95DAFA42991A3CAF2ACBF3A4E92CA16CA25D524D7B587954D95A83  proofs/COMPLETE_PROOF_SELF_CONTAINED.md
AAF38D8134015EC9AEAD6FEA4916F618C4479F6601E1EB34F68A5134B0E1B82A  output/tex/COMPLETE_PROOF_SELF_CONTAINED.tex
2ACD9BA34A7104976C65A007DF5132668605AFACA7407516B290545CB0634357  output/pdf/COMPLETE_PROOF_SELF_CONTAINED.pdf
2ACD9BA34A7104976C65A007DF5132668605AFACA7407516B290545CB0634357  COMPLETE_PROOF_SELF_CONTAINED.pdf
```

The release ZIP and its aggregate checksum are outside this document-level
audit.  They must be rebuilt after all synchronized files are finalized, and
their bytes will change because the updated supporting files are included;
that separate release step does not imply a change to the publication bytes
listed above.

## 5. Limitation

This PASS means only that the repaired obligations were propagated consistently
from the canonical manuscript into the supporting notes and repository
indexes.  It is internal document validation, not external peer review, formal
verification, publication, priority verification, or community acceptance of
the proposed resolution.
