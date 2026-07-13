# Lean audit: Boolean-cube McDiarmid and phase estimates — 2026-07-13

## Verdict

**PASS for both imported modules at the pinned hashes below.** The uniform
Boolean-cube bounded-differences theorem is proved without an MGF premise, and
the finite Taylor, falling-factorial, and Robbins/Stirling bounds are proved
with explicit hypotheses. This verdict does not cover arbitrary vertex
blocks, the endpoint-uniform assembly (2.5)--(2.2), or the final theorem.

| File | SHA-256 |
|---|---|
| `Erdos625/BoundedDifferences.lean` | `EF24694E4C30A8770B5368268C62BE6A35F441AA5AB6F41174BF7423CAAAF3DA` |
| `Erdos625/PhaseEstimates.lean` | `6ACF24B080A1DCE14CBFFBE1CA92F4E3FE7C17398630D7B2583D4268C67F40AB` |

## Reproduced integration checks

The two files compiled independently with warnings treated as errors. After
importing them from the root and adding representative dependency checks,
`lake build --wfail` completed successfully with exactly **3,155 jobs**.
The strict source gate and `git diff --check` passed. All 32 tracked
`#print axioms` results were exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No placeholder axiom or project-defined axiom appears.

## Bounded-differences audit

An independent reviewer reconstructed the normalization and induction:

- `cubeMean` is exactly `2⁻ⁿ ∑ f`, including the singleton cube at
  `n=0`;
- coordinate oscillation passes correctly to the recursive tail and exposed
  head coordinate;
- the two-point estimate contributes `cᵢ²t²/8` to the MGF exponent;
- the recursive centers combine as `(m₀+m₁)/2` and the exact variance
  proxy is `Σcᵢ²/4`;
- the PMF integral is proved equal to `cubeMean`, so the final MGF is centered
  at the actual expectation;
- both fields of `HasSubgaussianMGF` and the stated one-/two-sided events are
  proved.

Zero variance and `n=0` are sound under Lean's totalized division, although
their displayed tail bounds are deliberately loose. The module closes the MGF
bridge for fair Boolean coordinates. It does **not** close the manuscript's
vertex-block use: flattening a block into its individual edge bits would lose
the `n-1` variance scale.

## Phase-estimate audit

The second reviewer checked the Taylor sign and domain, every positive factor
in the descending factorial, the sign of the linear correction, and the
coarse but valid `2s³/n²` error under `2s≤n`, including `s=0`. The Robbins
step telescopes in the correct direction, its limit passage preserves the
inequality, and the exact normalization gives `0≤Rₛ≤1/(12s)` for every
positive integer `s`. The eventual phase range uses `PhaseDomain`; no
unguarded small-`n` identity is asserted.

Equations (2.5), (2.6), and (2.2) are absent. Their algebraic and
endpoint-uniform asymptotic assembly remains the next phase obligation.
