# Aristotle Section IX asymptotic-leaf audit — 2026-07-21

## Scope

This record concerns three isolated finite arithmetic leaves from the remaining
Erdős 625 Section IX formalization.  It is not evidence for Lemma 8.3, Lemma
9.1, Proposition 9.2, or `Erdos625Statement` as a whole.

The requests were executed by GitHub Actions run `29817673879` from branch
`agent/aristotle-625-asymptotic-leaves`.  The repository secret
`ARISTOTLE_API_KEY` was supplied to the official client only as an environment
variable.  Its value was not printed, committed, or passed as a command-line
argument.

Each request used Lean 4.28.0 and Mathlib commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`, contained exactly one intentional
target hole, and forbade `admit`, new axioms, `unsafe`, `native_decide`,
unlimited heartbeats, and suggestion-enabled `grind`.

## Returns

| Target | Aristotle run | GitHub job | Artifact | GitHub artifact digest | Service result |
|---|---|---:|---:|---|---|
| `smallResidualExponent_bound` | `9f97dcca-bb41-4c28-abdf-e070d5da308b` | `88611659240` | `8492737499` | `sha256:349c51bb2dee059a66f56abe86543534de4387879b63e77e73eaeef7dc96d327` | complete |
| `ennreal_two_pow_nat_le_of_log_bound` | `efb48b17-e8cf-40ec-833a-95f6d799f202` | `88611659217` | `8492663280` | `sha256:6097f985c8ea1b1097252b5c022021efe669083c656cf5de18699fd8d586393b` | complete |
| `largeResidualEnvelope_bound` | `e0e1fcf8-89d6-4768-8ed6-6f0015e8ffd0` | `88611659276` | `8492870975` | `sha256:5e2085ab0cc94b7a219fe8cb74620f4ae1904a8dafad16a3cb10609533c91708` | complete |

The returned sources preserve all three theorem statements and introduce no
helper declaration, project axiom, or prohibited construct.  The service-side
summaries report only the standard `propext`, `Classical.choice`, and
`Quot.sound` axiom set.

## Mathematical scope review

- `smallResidualExponent_bound` is the real-algebra implication
  `U ≤ C L` and `m ≤ n/L^6` imply
  `log 2 * U m / 2 ≤ (C log 2 / 2) n/L^5`.
- `ennreal_two_pow_nat_le_of_log_bound` is the exact finite transport from
  `log 2 * N ≤ x` to `2^N ≤ ENNReal.ofReal (exp x)`.
- `largeResidualEnvelope_bound` combines the displayed strict-regime bounds
  `m ≥ n/L^6`, `U ≤ C_U L`, `A ≤ n`, `H U ≤ 2n`, `L^2 ≤ n`, and
  `L^28 ≤ n^3` into one explicit `O(L^8)` envelope.

These statements are valid local arithmetic consequences of their hypotheses.
They do not establish that the manuscript's concrete parameter sequences meet
those hypotheses; that eventual specialization remains a separate obligation.

## Acceptance gates

The candidate Lean 4.31 port is
`Erdos625/Section9ResidualAsymptoticArithmetic.lean`.  Acceptance requires:

1. exact theorem-statement comparison with the request sources;
2. warning-fatal Lean 4.31 compilation;
3. repository-wide placeholder, project-axiom, and unsafe-source scans;
4. full modular and generated self-contained builds;
5. a standard-axiom `#print axioms` report;
6. integration into the root import graph and formalization ledger.

All six acceptance gates passed on the integrated Lean 4.31 branch: exact
statement review, warning-fatal module replay, source and trust scans, the
full modular build, regenerated self-contained compilation, standard-axiom
output, and root-import integration. The tracked Lean 4.31 module is the
proof authority; raw Aristotle archives remain provenance only.
