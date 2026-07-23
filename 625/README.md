# Erdős Problem 625 candidate-proof dossier

This directory contains a candidate full-sequence solution of Erdős Problem 625,
its publication artifacts, finite diagnostics, internal audits, and an
incremental Lean 4 formalization.

## Status

The current mathematical claim is a **candidate result**.  It has undergone
substantial internal checking, but it has not been externally peer reviewed or
fully formalized.  In particular:

- the manuscript gives a self-contained proof of a polynomial-scale
  chromatic--cochromatic gap for `G(n,1/2)`;
- the internal audits report no presently known blocking logical defect;
- finite computations are diagnostics only and are not proof of the asymptotic
  theorem;
- the Lean development verifies many exact finite and asymptotic components,
  but `Erdos625Statement` remains unproved.

The accurate public description is therefore:

> **Candidate full-sequence solution, internally audited, with a substantial
> partial Lean formalization; not external peer review and not a completed
> machine-checked proof.**

## Start here

- [Reviewer guide](REVIEW_GUIDE.md)
- [Canonical self-contained manuscript (Markdown)](proofs/COMPLETE_PROOF_SELF_CONTAINED.md)
- [Generated self-contained manuscript (TeX)](output/tex/COMPLETE_PROOF_SELF_CONTAINED.tex)
- [Self-contained proof PDF](COMPLETE_PROOF_SELF_CONTAINED.pdf)
- [Publication-layout preprint PDF](arxiv_625.pdf)
- [Formalization ledger](formalization/FORMALIZATION_LEDGER.md)
- [Final internal verification record](FINAL_VERIFICATION.md)

A review-focused rewrite of the most concentrated passages is available in
both formats:

- [Markdown replacement text for Sections 7--9](proofs/SECTIONS_7_9_REVIEW_REWRITE.md)
- [TeX replacement text for Sections 7--9](proofs/SECTIONS_7_9_REVIEW_REWRITE.tex)

These rewrite files preserve the current mathematical route while making the
partial-diagonal rate, canonical high-cell decomposition, high-skeleton sum,
and cycle-to-walk argument more explicit.  They are proposed integration text,
not an additional independent proof verdict.

## Exact target

For `G_n ~ G(n,1/2)`, the manuscript claims

\[
 \Pr\!\left\{\chi(G_n)-\zeta(G_n)\ge
 \frac{(\ln2)^2}{32}\ln\!\left(\frac{200}{153}\right)
 \frac{n}{(\ln n)^3}\right\}\longrightarrow1.
\]

Here `chi` is the chromatic number and `zeta` is the cochromatic number.

## Artifact map

### Canonical proof

- `proofs/COMPLETE_PROOF_SELF_CONTAINED.md` is the editable canonical
  mathematical manuscript.
- `output/tex/COMPLETE_PROOF_SELF_CONTAINED.tex` is the generated TeX source.
- `COMPLETE_PROOF_SELF_CONTAINED.pdf` is the compiled internal-layout PDF.

### Publication package

- `arxiv/` contains the publication-layout source, bibliography, build notes,
  and compiled PDF.
- `arxiv_625.pdf` is the top-level publication-layout PDF.
- `../arxiv_preprints/arxiv_625/` contains the synchronized public preprint
  package.

### Audits and diagnostics

- `audits/ADVERSARIAL_LEAP_AUDIT_2026-07-13.md` records the later adversarial
  review and the repairs made after the original full-chain audits.
- `FINAL_VERIFICATION.md` records artifact synchronization, diagnostic runs,
  scope limitations, and hashes.
- `verification/erdos625_independent_checks.py` checks selected exact finite
  identities and inequalities.
- `experiments/` contains finite examples and asymptotic diagnostics.  None of
  these computations substitutes for proof.

### Lean formalization

- `formalization/Erdos625/Target.lean` defines the exact probability target.
- `formalization/FORMALIZATION_LEDGER.md` is the authoritative declaration-level
  status record.
- `formalization/Erdos625SelfContained.lean` is a generated single-file form of
  the accepted import closure.
- `formalization/SELF_CONTAINED_BUILD.md` records regeneration, compilation,
  and axiom checks.

The single-file checkpoint is a **partial formalization**.  Successful
compilation does not prove the manuscript theorem unless the ledger records a
proved final endpoint.

## Review priorities

The most valuable independent checks are concentrated in four places:

1. the uniform root and optimizer corridor in Section 3;
2. the complete partial-diagonal rate in Lemma 7.1;
3. the conditioned canonical high-skeleton expansion in Section 8;
4. the weighted residual cycle expansion and mixed-cycle traversal in
   Lemma 9.1.

The reviewer guide gives exact entry points and a checklist for each.

## Trust and provenance

The manuscript names Samuil Petkov as sole author and discloses AI assistance.
Raw proof-search outputs are not treated as authoritative.  Only reviewed Lean
source that passes the repository's placeholder, axiom, warning, and build
gates enters the accepted formalization.

Internal documents labelled `PASS` are scoped to the bytes and dates stated in
those documents.  They are not external peer review, professional
certification, bibliographic priority verification, or community acceptance.

## Licensing

See [`../LICENSE_SCOPE.md`](../LICENSE_SCOPE.md) for the scope of the repository
license and the treatment of third-party material.
