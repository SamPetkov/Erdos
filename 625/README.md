# Erdős Problem 625 research dossier

## Current status

`proofs/COMPLETE_PROOF_SELF_CONTAINED.md` contains a proposed all-`n` positive
resolution with the explicit bound

\[
 \chi(G(n,1/2))-\zeta(G(n,1/2))
 \ge \frac{(\ln2)^2\ln(200/153)}{32}
       \frac{n}{(\ln n)^3}
 \quad\text{with high probability}.
\]

The decisive overlap components passed focused independent audits, and
four independent end-to-end reconstructions each returned PASS for the
repaired proof.  This is internal validation of a new argument, not external
peer review, publication, priority confirmation, or community acceptance.

The clean packaged dossier is available at
[`releases/Erdos-625-proof-dossier-2026-07-12.zip`](releases/Erdos-625-proof-dossier-2026-07-12.zip).

## Main proof chain

- `proofs/COMPLETE_PROOF_SELF_CONTAINED.md` — consolidated paper-style proof
  with all substantive lemmas proved in one document.
- `proofs/COMPLETE_PROOF_DRAFT.md` — assembled theorem and proof.
- `proofs/ALPHA_MINUS_TWO_ROUTE.md` — all-phase first-moment comparison,
  explicit constants, unrestricted chromatic lower location, and integer
  midpoint profile.
- `proofs/FOUR_SIZE_PARTIAL_RATES.md` — exact common-diagonal sum `1+o(1)`.
- `proofs/DENSE_FOUR_TYPE_MATCHING.md` — all unequal-type containments,
  near-containments, and the mixed middle strip.
- `proofs/RESIDUAL_ATTACHMENT.md` — all residual local and even-subgraph
  attachments after the large-cell matching is exposed.
- `proofs/ALON_CONCENTRATION_EXTENSION.md` — rare-event-to-whp transfer.

## Independent audits

- `audits/RARE_EVENT_AMPLIFICATION_AUDIT.md` — pass.
- `audits/RESIDUAL_ATTACHMENT_AUDIT.md` — pass.
- `audits/DENSE_FOUR_TYPE_MATCHING_AUDIT.md` — pass.
- `audits/FULL_PROOF_AUDIT_1.md` through `_4.md` — independent full-chain
  reconstructions; all four pass.

## Literature and known results

- `sources/SOURCE_LEDGER.md`
- `sources/RECENT_WORK_AUDIT.md`
- `sources/HISTORICAL_SOURCE_AUDIT.md`
- `proofs/KNOWN_RESULTS_RECONSTRUCTION.md`
- `proofs/EXCEPTIONAL_REGIME.md`

The ledger records every source version and probability quantifier.  Four
historical originals could not be legally retrieved through the available
institutional or public routes; those failures are explicit rather than
silently replaced by secondary summaries.

## Reproducibility

- `experiments/alpha_minus_two_route.py` — phase-uniform entropy losses and
  certified constants.
- `experiments/dense_transport_scan.py` — exact finite falling-factorial
  diagnostics for dense typed transports.
- `experiments/constrained_profile_certify.py` and
  `experiments/finite_slack_profile.py` — exceptional-profile calculations.
- `experiments/exact_chi_zeta.py`, CSV, and report — certified finite graph
  computations (diagnostic only).

`WORK_LOG.md` and `MECHANISM_REGISTRY.md` record the investigation history,
failed routes, redirections, and precise remaining status.
`FINAL_VERIFICATION.md` records the four full-audit verdicts, reproducibility
checks, structural manuscript checks, final hashes, and source-access caveat.
