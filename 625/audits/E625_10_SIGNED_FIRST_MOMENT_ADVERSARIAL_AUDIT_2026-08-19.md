# E625-10 signed first-moment adversarial audit

**Date:** 2026-08-19  
**Target:** `e625_10_signedFourSizeFirstMoment`  
**Status:** design audit; no Lean compilation or proof-closure claim

## Verdict

The correct E625-10 endpoint is the phase-resolved normalized logarithmic
first moment of the actual tangent-rounded midpoint profile. The theorem must
identify three objects exactly:

1. the real finite factorial expression used by Section VII;
2. the `toReal` of the graph-theoretic signed-profile expectation;
3. the finite signed four-size objective evaluated at the rounded midpoint.

The node is not closed by positivity alone. It must prove a phase-independent
exponential rate and preserve the full-sequence phase quantifier.

## Load-bearing claims

### A. Exact midpoint count

The canonical count is

```text
K_n = ceil((r_4^co(n) + r_+(n))/2).
```

The tangent correction preserves `sum_i m_i = K_n`. Therefore the theorem
must not introduce a second `+ O(1)` correction to the total class count.

### B. Exact integer conservation

The actual natural multiplicities must satisfy

```text
sum_i m_i = K_n,
sum_i (i+2)m_i = alpha_n K_n - n,
sum_i (alpha_n-(i+2))m_i = n.
```

The first two are supplied by the tangent-rounding API. The third must be
proved for the embedded profile, not assumed from the continuous optimizer.

### C. Exact expectation identity

The proof must establish

```text
(signedProfileExpectation n k_n).toReal
  = partialSignedFirstMoment n u_n m_n.
```

Without this equality the later partial-diagonal normalization may divide by a
different object from the one bounded in E625-10.

### D. Exact rounded-optimizer loss

The proposed finite theorem

```text
0 <= K_n * KL(r_n || p_n) <= 50/7
```

is valid because

```text
|m_i-K_n p_i| <= 5,
K_n p_i >= 14,
```

for all four coordinates. This replaces an unnamed Hessian `O(1)` and is
uniform by construction.

### E. Four-coordinate Stirling error

The active profile has four coordinates. Zero coordinates contribute
`log(0!) - factorialEntropyMain 0 = 0`. The finite log-weight error therefore
has a four-coordinate bound. An ambient `(alpha_n+1)` factor is safe only as a
coarse overbound and is not the exact theorem-facing interface.

### F. Phase-resolved normalized limit

The theorem must state

```text
log M_n / K_n - A_4(delta_n)/2 -> 0.
```

It must not state convergence to a fixed scalar, because `delta_n` varies over
the full sequence.

### G. Strict-margin endpoint

From

```text
log(200/153) < A_4(delta)
```

and a normalized error tending to zero, one obtains every fixed

```text
c < (1/2)log(200/153).
```

One does not automatically obtain the closed endpoint.

## Failure modes

### 1. Limiting optimizer substitution — REJECTED

Invalid substitution:

```lean
ProfileEntropyS4.optimizer fourGaussianScore
  (1 + 2 / q - phaseDelta n)
```

Required substitution:

```lean
midpointOptimizer n (phaseNat n) K_n
```

The limiting optimizer does not satisfy the exact finite target or finite
score equations.

### 2. Target equality at the midpoint — REJECTED

Invalid:

```text
alpha_n - n/K_n = 1 + 2/q - delta_n.
```

The right side is the phase-center target. E625-08 supplies a uniform
comparison, not this equality.

### 3. Arbitrary root choice — REJECTED

A selector produced from an unqualified existential root statement is
insufficient. The root must be the unique root in the concrete E625-08
corridor, because all derivative and target bounds are corridor-local.

### 4. Silent `Int.toNat` truncation — REJECTED

Before converting the ceiling midpoint to `Nat`, prove its integer value is
nonnegative. Otherwise a negative value becomes zero and all subsequent
identities are false.

### 5. Pointwise `2^K` count factor — REJECTED

The factor is exact after expectation. A fixed graph need not realize every
sign assignment on every ordinary profile partition.

### 6. Missing multiplicity factorials — REJECTED

Omitting `prod_i m_i!` labels equal-size classes. The resulting entropy differs
at leading order.

### 7. Wrong support loss — REJECTED

`finiteFourVsExtendedEntropyLoss` compares a finite four-point value with the
limiting extended value. It is not the exact finite-cutoff support loss used at
the unrestricted root.

### 8. Phase-dependent eventuality — REJECTED

A proof of

```text
forall delta, exists N(delta), forall n >= N(delta), ...
```

cannot be specialized to `delta = phaseDelta n`. The finite certificate and
root package must supply one threshold over the complete phase interval.

### 9. Closed endpoint margin — REJECTED

The strict entropy certificate and an unquantified `o(1)` do not prove

```text
log M_n >= (1/2)log(200/153) K_n
```

eventually. The theorem must quantify over all strictly smaller constants or
supply a separate fixed slack.

### 10. Circular second-moment input — REJECTED

No partial-diagonal, high-skeleton, residual attachment, or Paley--Zygmund
result is needed to calculate a first moment. Any such dependency is circular.

## Exact constant audit

The rounding constant is

```text
4 * 5^2 / 14 = 50/7.
```

The public entropy identity is based on

```text
2 / (153/100) = 200/153.
```

The stronger manuscript ledger satisfies

```text
(20000/12777) / (1000/639) = 12780/12777 > 1.
```

This stronger ledger may replace the public endpoint only after the
corresponding exact finite certificate is welded.

## Promotion checklist

E625-10 may move from design-frozen to running only after:

1. the private E625-08 selector names and exact signatures are recorded;
2. the finite certificate theorem name is recorded;
3. `eventually_signedFourMidpointRoundingAdmissible` is frozen;
4. the expectation-to-`partialSignedFirstMoment` theorem is frozen;
5. the `50/7` KL theorem is frozen;
6. the four-coordinate Stirling bridge is frozen;
7. the normalized midpoint objective theorem is frozen;
8. the top-level declaration is unchanged by the preceding choices.

It may move to welded only after warning-fatal Lean 4.31 replay, forbidden-
shortcut scan, axiom audit, import into the theorem-facing root, regenerated
self-contained source, and independent line-by-line mathematical review.

## Non-goals

This audit does not claim the phase-root theorem, chromatic lower tail,
partial-diagonal estimate, high-skeleton estimate, normalized second moment,
amplification, or final Erdős 625 statement.
