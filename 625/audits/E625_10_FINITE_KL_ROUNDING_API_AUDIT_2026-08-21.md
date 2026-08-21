# E625-10 finite midpoint-rounding entropy API audit

Date: 2026-08-21

## Scope

This audit covers only the finite tangent-rounding comparison on the exact
four-deficit support `2,3,4,5`.  The exported quantity is

```lean
midpointRoundedFourSizeEntropyLoss n alpha K
```

and the principal wrapper is

```lean
midpointRoundedFourSizeEntropyLoss_nonneg_and_le
    (n alpha K : Nat) (h : MidpointRoundingAdmissible n alpha K) :
    0 ≤ midpointRoundedFourSizeEntropyLoss n alpha K ∧
      midpointRoundedFourSizeEntropyLoss n alpha K ≤ (50 / 7 : Real)
```

The absolute-value form is

```lean
abs_midpointRoundedFourSizeEntropyLoss_le
    (n alpha K : Nat) (h : MidpointRoundingAdmissible n alpha K) :
    |midpointRoundedFourSizeEntropyLoss n alpha K| ≤ (50 / 7 : Real)
```

## Exact mathematical content

Let `p` be the exact finite Gibbs optimizer for `fourDeficitScore alpha` at

```text
T = fourSizeTarget n alpha K,
```

and let

```text
r_i = midpointMultiplicity n alpha K i / K.
```

Admissibility and the tangent correction machinery establish

```text
sum_i r_i = 1,
sum_i (i+2) r_i = T,
|midpointMultiplicity_i - K p_i| ≤ 5,
14 ≤ K p_i.
```

Because `p` and `r` lie on the same affine constraint plane, the finite Gibbs
gap is the relative-entropy sum.  The scalar logarithmic bound gives the
chi-square domination

```text
K * KL(r || p)
  ≤ sum_i (midpointMultiplicity_i - K p_i)^2 / (K p_i)
  ≤ 4 * 25/14
  = 50/7.
```

No limiting optimizer appears in this calculation.

## Dependency manifest

The wrapper API depends on the already proved finite module
`MidpointRoundedFourSizeEntropyLoss.lean`, in particular:

- exact midpoint proportion mass and support-mean identities;
- exact optimizer feasibility and positivity;
- tangent natural conservation and nonnegativity;
- the uniform displacement bound `≤ 5`;
- the optimizer coordinate lower bound `14 ≤ K p_i`;
- the finite Gibbs-gap/relative-entropy identity;
- the relative-entropy to chi-square inequality.

## Adversarial checks

### A. Wrong optimizer substitution

Replacing the exact finite optimizer by the limiting Gaussian optimizer is
invalid.  It destroys the exact Gibbs identity at finite `alpha` and changes
the support score.

### B. Wrong target substitution

Replacing `fourSizeTarget n alpha K` by a phase-center target is invalid.  The
linear term in the Gibbs comparison cancels only when both vectors have the
same exact support mean.

### C. Lost conservation

A coordinatewise displacement estimate alone does not imply the entropy-loss
identity.  Exact total mass and exact deficit moment are both required.

### D. Unsafe `Int.toNat`

The corrected integer vector must be proved nonnegative before converting to
natural multiplicities.  The API inherits this through
`MidpointRoundingAdmissible` and the existing conservation bridge.

### E. Hidden asymptotics

The constant `50/7` is finite and phase-independent.  No `O(1)`, eventual
statement, root corridor, or optimizer convergence is used.

## Explicit non-goals

This API proves none of the following:

- eventual midpoint admissibility;
- E625-08 phase/root estimates;
- E625-09 chromatic lower tail;
- the normalized E625-10 first-moment limit;
- partial-diagonal, full-corner, or skeleton estimates;
- a second moment or Paley--Zygmund argument;
- the final Erdős 625 theorem.
