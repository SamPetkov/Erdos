# Aristotle Section IX regime-adapter audit — 2026-07-21

## Scope

This record concerns four deterministic/asymptotic adapter theorems used after
the finite Section IX residual bounds:

- `smallResidual_two_pow_le_exp_scale`;
- `canonicalDemandRawAttachmentTerm_le_smallResidualExpScale`;
- `eventually_log_growth_bounds`;
- `eventually_largeResidualEnvelope_logScale`.

They convert already-proved finite estimates to the manuscript scales
`exp(O(n / (log n)^5))` and `O((log n)^8)`. They do not sum canonical skeletons,
prove a uniform attachment expectation, prove Lemma 9.1 or Proposition 9.2, or
establish `Erdos625Statement`.

## Aristotle requests

The isolated requests were executed in GitHub Actions run `29850301759` from
branch `agent/625-section9-regime-adapters`. The repository secret
`ARISTOTLE_API_KEY` was provided to the official client only as an environment
variable.

| Target | GitHub job | Artifact | Artifact digest | Service result |
|---|---:|---:|---|---|
| `smallResidual_two_pow_le_exp_scale` | `88701186311` | `8503448944` | `sha256:2f538008ae419733af6ad268275e3988a371dcff490eeb5b2cc760ecc246b217` | complete |
| `eventually_log_growth_bounds` | `88701186264` | `8503540107` | `sha256:6a0d5c3dd5293d73535e687a3af2b9b49c1cc1d14ebded86913a7cd97974f2fc` | complete |

Both request projects were pinned to Lean 4.28.0 and Mathlib commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`, contained exactly one intentional
hole, and forbade `admit`, new axioms, `unsafe`, `native_decide`, unlimited
heartbeats, and suggestion-enabled `grind`.

The accepted Lean 4.31 source is independently reviewed and authoritative. Raw
Aristotle archives are provenance only.

## Mathematical review

- The small-residual theorem first uses natural-division cast monotonicity to
  compare `U * m / 2` with its real half-product, then applies the accepted real
  exponent inequality and the accepted exact `ENNReal` two-power bridge.
- The canonical-demand theorem composes that scale conversion with the literal
  event-restricted small-residual attachment bound while keeping the bare reward
  and labelled-witness incidence factors explicit.
- The logarithmic-growth theorem uses `log(n)^r = o(n)` for fixed powers `r = 2`
  and `r = 28`, then strengthens the latter to `log(n)^28 <= n^3`.
- The large-residual theorem substitutes `L = log n` into the accepted finite
  envelope, uniformly over all finite parameters satisfying its displayed
  hypotheses.

## Acceptance status

<!-- ACCEPTANCE_STATUS -->
Pending complete Lean 4.31 integration: warning-fatal module replay, full
`lake build --wfail`, source/trust scan, root-import insertion, formalization
ledger update, and regenerated self-contained compilation.
