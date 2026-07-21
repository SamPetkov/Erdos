# Aristotle wave: Section IX asymptotic leaves

**Date:** 21 July 2026  
**Status:** quarantined proof-search inputs, not accepted Lean source

This wave isolates three small, faithful arithmetic obligations from the current
Problem 625 checklist.  It does **not** ask Aristotle for Lemma 8.3, Lemma 9.1,
Proposition 9.2, or `Erdos625Statement` as a monolithic target.

## Targets

1. `smallResidualExponent_bound`
   converts the small-residual hypotheses `U ≤ C L` and `m ≤ n/L^6` into the
   exponent scale `O(n/L^5)` used after the deterministic bound
   `2^(U*m/2)`.
2. `ennreal_two_pow_nat_le_of_log_bound`
   is the exact finite bridge from a real logarithmic exponent comparison to
   the `ENNReal` power appearing in the residual attachment estimate.
3. `largeResidualEnvelope_bound`
   bounds the three terms of the strict large-residual envelope by one explicit
   multiple of `L^8`, under the exact algebraic growth hypotheses used when
   `L = log n`.

Each project is pinned to the Aristotle service toolchain recorded in
`ARISTOTLE_WORKFLOW.md`: Lean 4.28.0 and Mathlib commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`.  Each source contains exactly one
intentional target `sorry` and no project axiom or unsafe declaration.

## Acceptance boundary

A service return remains quarantined.  It may enter tracked `Erdos625/` source
only after:

- exact theorem-statement comparison;
- rejection of `sorry`, `admit`, new axioms, `unsafe`, `native_decide`, and
  unbounded or suggestion-enabled automation;
- warning-fatal replay under the accepted Lean/Mathlib 4.31 project;
- full `lake build --wfail` and generated self-contained-file checks;
- `#print axioms` no stronger than the repository's standard Mathlib baseline;
- independent mathematical review of signs, divisions, and asymptotic scope.

The GitHub workflow submits the projects only when the repository secret
`ARISTOTLE_API_KEY` is configured.  The key is never written to the repository
or passed as a command-line argument.  Returned archives are uploaded as CI
artifacts and are never committed automatically.
