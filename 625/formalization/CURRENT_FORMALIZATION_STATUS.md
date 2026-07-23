# Erdős Problem 625 formalization status

**Snapshot:** 2026-07-24
**Authority:** tracked Lean sources plus successful GitHub Actions checks

## Status boundary

The repository contains a large, kernel-checked **partial formalization**.
It does not yet prove `Erdos625Statement`, and it must not be described as a
complete machine verification of the manuscript.

The generated checkpoint currently packages 370 local source modules into
64,868 lines in `Erdos625SelfContained.lean`. This is a reproducible
single-file presentation of the same partial development, not an additional
proof claim.

## Current accepted frontier

The `main` baseline includes the exact deficit-coordinate derivative
composition
`unrestrictedPhaseObjective_deriv_eq_deficitCoordinates_of_deficitTarget`
and its two audited coordinate/domain inputs.

This checkpoint adds:

- exact integral and natural-coordinate displacement control for the concrete
  four-coordinate midpoint rounding;
- `O(log log n)` bounds for the phase-root scalar term, Stirling residual, and
  unrestricted objective at the proposed center;
- a finite signed four-size root-corridor theorem from explicit center,
  feasibility, margin, and derivative-lower-bound hypotheses;
- synchronized root imports, axiom-audit declarations, ledger entries, and
  generated self-contained source.

These results strengthen the Section III and midpoint infrastructure. The
root-corridor theorem is conditional: the concrete uniform center, slope,
feasibility, and asymptotic hypotheses still have to be supplied.

## External proof-search queue

External services are proof-search assistants, not authorities. Every return
remains quarantined until exact-statement review, trust scanning, Lean 4.31
replay, axiom audit, integration, self-contained regeneration, and green
GitHub Actions.

| Service item | Snapshot status | Intended contribution |
|---|---|---|
| Aristotle `06eac8ab-581c-4337-8dcf-244ece334075` | running | Bound the error after replacing the deficit-coordinate derivative's affine factorial-log core by its quadratic main term. |

No second request should duplicate this obligation. If it succeeds cleanly,
the next request may address only a bounded theorem directly unlocked by it.

## Remaining theorem-level work

1. **Phase root and chromatic lower tail.** Supply the concrete phase-uniform
   center, slope, feasibility, root rounding, attained-profile comparison, and
   the full-sequence chromatic lower-tail limit.
2. **Signed four-size first moment.** Complete the uniform entropy certificate
   and optimized partition-ratio estimate in Lemma 5.1.
3. **Partial diagonal.** Prove the manuscript-specific empty-, central-, and
   full-corner asymptotics of Lemma 7.1 from the accepted finite identities.
4. **Canonical skeleton.** Prove the weighted unlabelled quotient, ratio
   bounds, endpoint/middle estimates, and the complete Section VIII
   probability estimate.
5. **Residual attachment.** Identify and integrate the conditioned residual
   law and prove the uniform large- and small-residual bounds completing
   Lemma 9.1 and Proposition 9.2.
6. **Concrete closing inputs.** Establish the Section IX seed/count/moment and
   `Lambda` asymptotics, the instantiated Section X upper tail, the concrete
   root separation, and finally discharge the explicit hypotheses of the
   Section XI adapter for `Erdos625Statement`.

Section VI's exact second-moment identity and the deterministic/conditional
closing adapters are already formalized; they should not be reimplemented.
The remaining work is the substantive quantitative mathematics listed above,
not final-event plumbing.

## Acceptance loop

For each bounded obligation:

1. fix the exact statement and quantifier order;
2. use cloud proof search only on an isolated copy;
3. reject weakened statements, new assumptions, circular dependencies,
   placeholders, unsafe code, or nonstandard axioms;
4. validate isolated candidates under Lean 4.31;
5. run the authoritative GitHub placeholder, warning-fatal modular,
   generated-source, self-contained, and axiom gates;
6. integrate only a green result and then select at most one genuinely
   unlocked next obligation.

The detailed declaration ledger remains
[`FORMALIZATION_LEDGER.md`](FORMALIZATION_LEDGER.md), and the dependency-level
plan remains
[`REMAINING_FORMALIZATION_PLAN_2026-07-16.md`](REMAINING_FORMALIZATION_PLAN_2026-07-16.md).
