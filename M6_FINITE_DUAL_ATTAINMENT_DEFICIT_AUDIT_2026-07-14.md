# M6 finite dual attainment and deficit audit — 2026-07-14

## Verdict

**PASS for the pinned declarations below.** This milestone closes the fixed
finite-support endpoint inversion, unique interior tilt, exact Gibbs
attainment, deficit-coordinate normalization, selected-optimum calculus, and
pointwise Gaussian residual-score layers used in Section 4.

This is not a certification of manuscript Lemma 3.1, a phase-uniform bounded
deficit tilt, growing-support partition tails, the `L_+` root corridor or slope,
integer rounding, the final chromatic probability limit, or
`Erdos625Statement`. Those obligations remain explicit below.

## Pinned source

| Module | Lines | SHA-256 |
|---|---:|---|
| `ColoringProfileDualTilt.lean` | 348 | `A04F68D852F4D6CF8399131252828F22B2E56665C50E8C0E300283E8CD9662D5` |
| `ColoringProfileDualOptimizer.lean` | 189 | `2D953C53D120026F8B9B69924D39824E83C2A0DFB1B7555D696D22280BADBEAA` |
| `ColoringProfileDeficitDual.lean` | 239 | `B8E5D863A7108A2BD44566EE4A12B9C2E2EAE15B508A492D8CA4F47309EBF0B1` |
| `ColoringProfileDualOptimalValue.lean` | 246 | `F17671CAB4D74B4AAB6CAE9CBA98D1D250243645669567D15C03339E7213CED8` |
| `ColoringProfileDeficitScoreBounds.lean` | 176 | `F77A9E8765D351E339E494144448DE7A94821DABF4CF0D255899496C87353028` |

Toolchain: Lean `v4.31.0`; mathlib commit
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.

## What is kernel-checked

### Endpoint inversion and exact finite attainment

For every support with `b ≥ 2`, the Gibbs mean is continuous and strictly
increasing, tends to `1` at negative infinity and to `b` at positive infinity,
and has a unique tilt for every target in `(1,b)`. The selected tilt is total
only by a documented zero fallback outside the interior; every specification,
uniqueness, derivative, and optimality theorem retains the strict interior
hypotheses.

For positive part count, the Gibbs profile is positive, has the exact part and
vertex masses, and attains the dual upper value when its mean matches `n/parts`.
It is proved to be an `IsGreatest` witness for the fixed finite real-profile
objective, not merely an upper bound.

### Exact deficit normalization and envelope calculus

On support `b = α+1`, class size is reindexed by deficit `d = α-size`. The
score decomposition proves the manuscript normalization `λ = B_α - t`, the
normalized weights are unchanged, the deficit target is `α - n/parts`, and
the dual value has the exact centered form. The signs were checked
independently against the expanded score identity.

On the strict interior target domain, the selected tilt derivative is the
reciprocal Gibbs variance, normalized entropy has derivative `-tilt`, and the
attained optimum has exact part-count derivative
`log Z_b(tilt) - log parts`.

These are finite envelope identities. They do not supply a phase-uniform
variance estimate or the manuscript's asymptotic root slope.

### Pointwise residual-score control

For `α > 0`, the unique top coordinate has deficit `-1` and exact residual
`-q/2 + log (α/(α+1))`.

Every non-top coordinate has an exact descending-factorial decomposition. The
inequality `α.descFactorial d ≤ α^d` then proves that every coordinate in the
full finite support satisfies residual score at most `-(q/2)d^2`. The top
coordinate is handled separately through its nonpositive logarithmic
correction; natural subtraction is never used for the negative deficit.

This is a pointwise score theorem. No Gaussian partition tail, bounded tilt,
uniform moment estimate, or growing-support convergence is claimed.

## Reproduced gates

- Integrated `lake build --wfail`: **PASS**, 3,733/3,733 jobs.
- Project inventory at the pinned Lean bytes: **55 Lean files, 11,936 physical
  lines**; all accepted modules are imported by `Erdos625.lean`.
- Recursive source gate for `sorry`, `admit`, line-leading project
  `axiom`/`constant`, `unsafe`, and `native_decide`: **PASS**.
- Integrated `Erdos625/AxiomAudit.lean`: **PASS**. Every representative new
  declaration reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Independent frozen-pin semantic audit of endpoint limits, optimizer
  attainment, deficit signs, inverse/envelope derivatives, and scope:
  **PASS, no blockers**.
- Independent frozen-pin audit of the score module, including `α=0`, `α=1`,
  the `d=-1` endpoint, factorial orientation, casts, logarithm positivity, and
  inequality directions: **PASS, no blockers**.
- `git diff --check`: **PASS**.

## Exact remaining Section 4 obligations

1. Exponentiate and sum the pointwise score estimate uniformly on the growing
   deficit support, including moment estimates needed for the optimizer.
2. Prove the effective deficit tilt remains in a fixed compact interval and
   compare the phase-dependent support with its limiting model.
3. Establish the scalar `L_+` root corridor and the required phase-uniform
   slope estimate.
4. Transfer the real root through the precise integer rounding decrement.
5. Prove that this parameter choice makes the already assembled dual main term
   tend to zero.

Only after these and all later signed-moment, overlap, residual, and
amplification obligations are closed may the project prove
`Erdos625Statement`.
