# E625-10 — exact signed four-size first-moment package

**Date:** 2026-08-19  
**Branch:** `agent/625-e625-10-first-moment-expansion`  
**Status:** theorem design and finite-proof decomposition; no proof-closure claim

## 1. Purpose

This document freezes the exact theorem-facing interface for E625-10. The node
constructs the actual tangent-rounded four-size midpoint profile, identifies
its exact real factorial first moment with the graph-theoretic signed-profile
expectation, and proves the phase-resolved normalized logarithmic asymptotic.

The package is intentionally downstream of E625-08. It consumes the concrete
ordinary and signed roots, their common corridor, the uniform class-count
slope estimate, and the phase-resolved root separation. It does not reprove or
restate the phase-root theorem.

The central normalized conclusion is

```text
log M_n / K_n
  - (log 2 - D_4(delta_n)) / 2
  -> 0,
```

where `M_n` is the exact real signed first moment of the integer profile and
`K_n` is the rounded midpoint class count.

The package also exports every fixed exponential margin strictly below the
sharp endpoint supplied by the welded entropy certificate. For the current
public certificate this endpoint is

```text
(1/2) * log(200/153).
```

No arbitrary smaller constant is baked into E625-10.

## 2. Exact manuscript objects

Write

```text
q       = log 2,
alpha_n = phaseNat n,
delta_n = phaseDelta n.
```

E625-08 must export two total real selectors. The names below are proposed
aliases if the private branch uses different identifiers:

```lean
noncomputable def phaseSignedFourSizeRoot : ℕ → ℝ
noncomputable def phaseUnrestrictedRoot : ℕ → ℝ
```

They must select the unique roots in the concrete E625-08 corridors. They must
not be arbitrary global choices among all positive zeros.

The exact midpoint count is

```lean
noncomputable def signedFourMidpointPartCount (n : ℕ) : ℕ :=
  (rootCochromaticIndex
      (phaseSignedFourSizeRoot n)
      (phaseUnrestrictedRoot n)).toNat
```

Thus, after the eventual nonnegativity proof,

```text
K_n = ceil((r_4^co(n) + r_+(n))/2).
```

There is no further correction to the number of classes. Tangent correction
changes the four type multiplicities but preserves their sum exactly.

The exact finite optimizer and integer multiplicities are

```lean
noncomputable def signedFourMidpointMultiplicity
    (n : ℕ) : Fin 4 → ℕ :=
  midpointMultiplicity n (phaseNat n)
    (signedFourMidpointPartCount n)
```

and the four class sizes are

```lean
fun i : Fin 4 => phaseNat n - fourDeficit i.
```

The exact real first moment used by the partial-diagonal denominator is

```lean
noncomputable def signedFourMidpointFirstMoment (n : ℕ) : ℝ :=
  partialSignedFirstMoment n
    (fun i : Fin 4 => phaseNat n - fourDeficit i)
    (signedFourMidpointMultiplicity n)
```

The embedded full profile is total, with a harmless zero branch outside the
eventual four-deficit domain:

```lean
noncomputable def signedFourMidpointProfile (n : ℕ) :
    ColoringProfile (phaseNat n + 1) :=
  dite (5 < phaseNat n)
    (fun hAlpha =>
      fourDeficitEmbedding (phaseNat n) hAlpha
        (signedFourMidpointMultiplicity n))
    (fun _ => fun _ => 0)
```

## 3. Exact top-level declaration

The largest honest one-purpose declaration is:

```lean
theorem e625_10_signedFourSizeFirstMoment :
    Tendsto
      (fun n : ℕ =>
        Real.log (signedFourMidpointFirstMoment n) /
            (signedFourMidpointPartCount n : ℝ) -
          (q - fourEntropyLoss
            (1 + 2 / q - phaseDelta n)) / 2)
      atTop (𝓝 0) ∧
    (∀ c : ℝ,
      c ∈ Set.Ioo (0 : ℝ)
          (Real.log (200 / 153 : ℝ) / 2) →
        ∀ᶠ n : ℕ in atTop,
          c * (signedFourMidpointPartCount n : ℝ) ≤
            Real.log (signedFourMidpointFirstMoment n)) ∧
    ∀ᶠ n : ℕ in atTop,
      let K := signedFourMidpointPartCount n
      let m := signedFourMidpointMultiplicity n
      let k := signedFourMidpointProfile n
      0 < K ∧
      MidpointRoundingAdmissible n (phaseNat n) K ∧
      (∑ i : Fin 4, m i) = K ∧
      (∑ i : Fin 4, tangentDeficitNat i * m i) =
        midpointDeficit n (phaseNat n) K ∧
      (∀ i : Fin 4,
        |(m i : ℝ) -
            (K : ℝ) * midpointOptimizer n (phaseNat n) K i| ≤ 5) ∧
      ColoringProfile.partCount k = K ∧
      ColoringProfile.vertexMass k = n ∧
      IsFourDeficitSupported (phaseNat n) k ∧
      0 < signedFourMidpointFirstMoment n ∧
      0 < signedProfileExpectation n k ∧
      signedProfileExpectation n k ≠ ⊤ ∧
      signedProfileExpectation n k =
        (2 : ENNReal) ^ K * profileColoringExpectation n k ∧
      (signedProfileExpectation n k).toReal =
        signedFourMidpointFirstMoment n ∧
      Real.log (signedFourMidpointFirstMoment n) =
        (K : ℝ) * q + profileLogWeight n k
```

This declaration contains no hypotheses. Every analytic input is supplied by
E625-08 or by the welded finite entropy certificate through ordinary theorem
dependencies.

If a stronger exact finite certificate with endpoint
`log (1000 / 639 : ℝ)` is welded, the only theorem-statement change is the
right endpoint of the `Set.Ioo` interval. A manuscript calculation or a
numerical checker is not sufficient to make this substitution.

## 4. Quantifier convention

The first conjunct means

```text
for every epsilon > 0,
there is one N,
such that for every n >= N,

  |log M_n / K_n - A_4(delta_n)/2| < epsilon.
```

The phase `delta_n` varies with `n`. This is not a fixed-phase limit and the
normalized logarithm need not converge to one scalar independent of the
phase.

The second conjunct means that every constant

```text
0 < c < (1/2) log(200/153)
```

is eventually a valid phase-independent exponential rate. The closed endpoint
must not be asserted from a strict entropy certificate plus an unspecified
vanishing error.

The third conjunct uses one eventuality threshold for all finite profile,
rounding, positivity, expectation, and logarithmic identities.

## 5. Probability convention

The random graph is the uniform labelled half-random graph

```text
G_n ~ G(n, 1/2)
```

represented by `randomGraphMeasure n` on `LabeledGraph n`.

The signed count is `signedProfileCount G k`, and its expectation is the exact
finite `ENNReal` sum

```lean
signedProfileExpectation n k =
  ∑ G : LabeledGraph n,
    (signedProfileCount G k : ENNReal) *
      randomGraphMeasure n {G}.
```

The identity

```lean
signedProfileExpectation n k =
  (2 : ENNReal) ^ ColoringProfile.partCount k *
    profileColoringExpectation n k
```

is an expectation-level witness-count identity. It does not assert the
pointwise count identity

```text
signedProfileCount G k = 2^K * ordinaryProfileCount G k.
```

Different sign assignments are different signed witnesses even when their
graph events overlap.

## 6. Dependency manifest

### E625-08 concrete root package

Required outputs:

- `phaseSignedFourSizeRoot`;
- `phaseUnrestrictedRoot`;
- eventual positivity and common-corridor membership;
- the phase-resolved root separation;
- the class-count derivative estimate on the whole intervening segment;
- `K_n ~ (q/2) n / log n` for the rounded midpoint;
- exact target transport to `1 + 2/q - phaseDelta n`;
- one phase-independent eventuality threshold.

### Existing finite optimizer and rounding infrastructure

- `fourSizeTarget`;
- `fourDeficitScore`;
- `fourSizeFiniteEntropy`;
- `midpointOptimizer`;
- `midpointMultiplicity`;
- `MidpointRoundingAdmissible`;
- `midpointMultiplicity_count_deficit_intDisplacement`;
- `midpointMultiplicity_uniform_displacement`;
- `midpointMultiplicity_cast_eq_correctedInt`.

### Existing profile and expectation infrastructure

- `fourDeficitEmbedding`;
- `fourDeficitEmbedding_profile_invariants`;
- `signedProfileExpectation_eq`;
- `profileColoringExpectation_pos`;
- `signedProfileExpectation_ne_top`;
- `log_profileColoringExpectation_toReal_eq_profileLogWeight`;
- the exact profile enumeration coefficient theorems.

### Existing entropy and objective infrastructure

- `ProfileEntropyS4.optimizer_entropy_score_eq_log_partition_sub_tilt_mul_target`;
- `ProfileEntropyS4.entropy_score_le_log_partition_sub_tilt_mul_target`;
- `signedFourSizeObjectiveAtTarget`;
- `signedFourSizeObjective`;
- `phaseSignedFourSizeObjective`;
- `profileDeficitResidualScore_fourDeficitCoordinate`;
- `profileDualScore_eq_deficitAffine_add_residual`.

### Existing factorial infrastructure

- `factorialEntropyMain`;
- `factorialLogErrorBound`;
- `factorialEntropyMain_le_log_factorial`;
- `log_factorial_le_factorialEntropyMain_add_error`;
- `profileDiscreteObjective_eq_profileManuscriptObjective`.

### Existing limiting certificate

- `uniform_limiting_entropy_certificate_for_delta`;
- `log_200_div_153_pos`.

The concrete finite certificate stipulated by E625-10 must bridge the exact
finite midpoint target and optimizer to the limiting certificate. It must not
assume a first-moment lower bound.

## 7. First dependency-ready theorem

The first theorem to prove is:

```lean
theorem eventually_signedFourMidpointRoundingAdmissible :
    ∀ᶠ n : ℕ in atTop,
      MidpointRoundingAdmissible n (phaseNat n)
        (signedFourMidpointPartCount n)
```

The exact substitution is

```lean
alpha  := phaseNat n
delta  := phaseDelta n
rCo    := phaseSignedFourSizeRoot n
rPlus  := phaseUnrestrictedRoot n
K      := signedFourMidpointPartCount n
target := fourSizeTarget n (phaseNat n) (K : ℝ)
score  := fourDeficitScore (phaseNat n)
p      := midpointOptimizer n (phaseNat n) K
```

The theorem must establish all five fields of
`MidpointRoundingAdmissible`:

```text
5 < phaseNat n,
0 < K,
n <= phaseNat n * K,
fourSizeTarget n (phaseNat n) K in (2,5),
14 <= K * midpointOptimizer_i for every i.
```

The exact midpoint target and exact finite optimizer are mandatory. The phase
center and limiting Gaussian optimizer are not substitutes.

## 8. Exact integer profile assembly

From `eventually_signedFourMidpointRoundingAdmissible`, use
`midpointMultiplicity_count_deficit_intDisplacement` to obtain

```text
sum_i m_i = K,
sum_i (i+2) m_i = alpha K - n,
|m_i - K p_i| <= 5.
```

The corresponding class-size mass is

```text
sum_i (alpha - (i+2)) m_i
  = alpha sum_i m_i - sum_i (i+2) m_i
  = n.
```

The Lean proof should cast the conservation equations to `ℝ`, rewrite each
`Nat.cast_sub` only after proving `fourDeficit i <= alpha`, finish by `ring`,
and cast the result back. `omega` alone cannot solve products such as
`alpha * m_i` where both factors vary.

Applying `fourDeficitEmbedding_profile_invariants` then proves

```text
partCount k = K,
vertexMass k = n,
IsFourDeficitSupported alpha k.
```

## 9. Exact expectation-to-real bridge

A dedicated finite theorem is required:

```lean
theorem signedProfileExpectation_toReal_eq_partialSignedFirstMoment_fourDeficit
    (n alpha : ℕ) (hAlpha : 5 < alpha)
    (m : Fin 4 → ℕ)
    (hMass :
      ∑ i : Fin 4, (alpha - fourDeficit i) * m i = n) :
    (signedProfileExpectation n
      (fourDeficitEmbedding alpha hAlpha m)).toReal =
      partialSignedFirstMoment n
        (fun i : Fin 4 => alpha - fourDeficit i) m
```

The proof is finite:

1. rewrite `signedProfileExpectation_eq`;
2. rewrite the exact ordinary profile expectation by the enumeration theorem;
3. use the exact multiplication-form factorial quotient before division;
4. reindex the four active profile coordinates;
5. use `hMass` to rewrite the unused-vertex factorial as `0!`;
6. cancel only positive finite factorial casts.

This theorem prevents E625-10 from proving a lower bound for an algebraic proxy
while E625-11 divides by a different first moment.

## 10. Exact finite rounding loss: `50/7`

Let

```text
T = fourSizeTarget n alpha K,
p_i = midpointOptimizer n alpha K i,
r_i = midpointMultiplicity n alpha K i / K.
```

Under `MidpointRoundingAdmissible`, both `p` and `r` satisfy

```text
sum p_i = sum r_i = 1,
sum (i+2) p_i = sum (i+2) r_i = T.
```

The Gibbs formula gives

```text
fourSizeFiniteEntropy alpha T
  - (-sum r_i log r_i + sum r_i fourDeficitScore alpha i)
  = sum r_i log (r_i / p_i).
```

The right side is `KL(r || p)`. Using `log x <= x - 1`,

```text
KL(r || p)
  <= sum_i (r_i - p_i)^2 / p_i.
```

Therefore

```text
K * KL(r || p)
  <= sum_i (m_i - K p_i)^2 / (K p_i).
```

The existing bounds

```text
|m_i - K p_i| <= 5,
K p_i >= 14
```

give, coordinatewise,

```text
(m_i - K p_i)^2 / (K p_i) <= 25/14.
```

There are four coordinates, so

```text
0 <= K * KL(r || p) <= 4 * 25/14 = 50/7.
```

The dependency-ready finite declaration is:

```lean
theorem midpointRoundedFourSizeEntropy_loss_le
    (n alpha K : ℕ)
    (h : MidpointRoundingAdmissible n alpha K) :
    let r : Fin 4 → ℝ :=
      fun i =>
        (midpointMultiplicity n alpha K i : ℝ) / (K : ℝ)
    0 <=
      (K : ℝ) *
        (fourSizeFiniteEntropy alpha
            (fourSizeTarget n alpha (K : ℝ)) -
          (-(∑ i : Fin 4, r i * Real.log (r i)) +
            ∑ i : Fin 4, r i * fourDeficitScore alpha i)) ∧
    (K : ℝ) *
        (fourSizeFiniteEntropy alpha
            (fourSizeTarget n alpha (K : ℝ)) -
          (-(∑ i : Fin 4, r i * Real.log (r i)) +
            ∑ i : Fin 4, r i * fourDeficitScore alpha i)) <=
      (50 / 7 : ℝ)
```

This theorem is preferable to an unnamed Hessian `O(1)` estimate. It is exact,
finite, uniform, and independent of the phase-root analysis.

## 11. Four-coordinate Stirling bridge

For

```text
rho(t) = log(t!) - factorialEntropyMain t,
```

the existing factorial bounds give

```text
0 <= rho(t) <= factorialLogErrorBound t.
```

For the four-supported profile,

```text
profileLogWeight n k - profileDiscreteObjective n k
  = rho(n) - sum_{i=0}^3 rho(m_i).
```

All off-support coordinates are zero and contribute exactly zero. Since each
`m_i <= n`,

```text
|profileLogWeight n k - profileDiscreteObjective n k|
  <= 4 * factorialLogErrorBound n.
```

The factor is `4`, not `phaseNat n + 1`. Using the full ambient profile bound
would pay a false nonzero error at every zero coordinate.

Combining this estimate with the `50/7` Gibbs rounding loss gives the exact
finite bridge

```text
|log M_n - phaseSignedFourSizeObjective n K_n|
  <= 4 * factorialLogErrorBound n + 50/7.
```

The theorem-facing declaration is:

```lean
theorem eventually_abs_log_signedFourMidpointFirstMoment_sub_objective_le :
    ∀ᶠ n : ℕ in atTop,
      |Real.log (signedFourMidpointFirstMoment n) -
          phaseSignedFourSizeObjective n
            (signedFourMidpointPartCount n : ℝ)| <=
        4 * factorialLogErrorBound n + 50 / 7
```

## 12. Root-to-midpoint objective asymptotic

Define

```text
A_n = q - fourEntropyLoss(1 + 2/q - phaseDelta n).
```

E625-08 gives

```text
r_+ - r_4^co
  = [(q^2/4) A_n + o(1)] n/(log n)^3,
```

and, uniformly throughout the interval between the roots,

```text
Phi_n'(x)/(log n)^2 = 2/q + o(1),
Phi_n(k) = phaseSignedFourSizeObjective n k.
```

For

```text
x_n = (r_4^co + r_+)/2,
K_n = ceil x_n,
```

the exact ceiling error is

```text
0 <= K_n - x_n < 1.
```

The root gap tends to infinity, so eventually `K_n` lies strictly between the
roots. The mean-value theorem gives

```text
Phi_n(K_n)
  = [(q/4) A_n + o(1)] n/log n.
```

The midpoint scale is

```text
K_n = [(q/2) + o(1)] n/log n.
```

Hence

```text
Phi_n(K_n)/K_n - A_n/2 -> 0.
```

The exact internal declaration is:

```lean
theorem tendsto_phaseSignedFourMidpointObjective_normalized :
    Tendsto
      (fun n : ℕ =>
        phaseSignedFourSizeObjective n
            (signedFourMidpointPartCount n : ℝ) /
            (signedFourMidpointPartCount n : ℝ) -
          (q - fourEntropyLoss
            (1 + 2 / q - phaseDelta n)) / 2)
      atTop (𝓝 0)
```

This theorem consumes E625-08 but does not restate its root theorem.

A necessary auxiliary bound is

```text
0 < A_n <= q.
```

The upper bound follows from nonnegativity of `fourEntropyLoss`; the lower
bound follows from the uniform entropy certificate. This boundedness is needed
when multiplying the varying phase coefficient by vanishing root and slope
errors.

## 13. Final asymptotic assembly

Write

```text
E_n = log M_n - Phi_n(K_n).
```

The exact bridge gives

```text
|E_n| <= 4(log(n+1)+4) + 50/7.
```

Since

```text
K_n ~ (q/2) n/log n,
```

we have

```text
E_n/K_n = O((log n)^2/n) -> 0.
```

Therefore

```text
log M_n/K_n - A_n/2
  = E_n/K_n + (Phi_n(K_n)/K_n - A_n/2)
  -> 0.
```

For every fixed

```text
0 < c < gamma_4/2,
gamma_4 = log(200/153),
```

choose

```text
epsilon = (gamma_4/2 - c)/2 > 0.
```

The normalized asymptotic and the strict certificate `gamma_4 < A_n` then give

```text
log M_n/K_n > c
```

eventually. Multiplication by the positive `K_n` yields the universal margin
conjunct in the top-level theorem.

## 14. Uniformity obligations

All of the following must hold after one common threshold independent of the
phase:

- the E625-08 root corridor;
- positivity of both roots and the midpoint integer;
- nonnegativity of `rootCochromaticIndex` before `Int.toNat` transport;
- midpoint target membership in a fixed compact subset of `(2,5)`;
- exact finite-score convergence;
- finite optimizer positivity;
- `14 <= K_n p_{n,i}` for every coordinate;
- the root separation and slope remainder;
- `K_n ~ (q/2)n/log n`;
- the finite entropy certificate;
- the factorial error divided by `K_n`.

The unsafe quantifier form is

```text
forall delta, eventually n, P n delta.
```

It cannot be specialized to `delta = phaseDelta n` unless a preceding theorem
has already produced a phase-independent threshold.

## 15. Coercion and positivity obligations

Before using `Int.toNat_of_nonneg`, prove

```lean
0 <= rootCochromaticIndex
  (phaseSignedFourSizeRoot n)
  (phaseUnrestrictedRoot n).
```

Before `Nat.cast_sub`, prove

```lean
n <= phaseNat n * signedFourMidpointPartCount n.
```

Before dividing by `(K : ℝ)`, prove `0 < K`.

Before using `ENNReal.toReal_mul`, `Real.log_mul`, or converting the signed
expectation to its real factorial expression, prove both positivity and
finiteness.

The class-size subtraction requires

```text
fourDeficit i <= 5 < phaseNat n.
```

The profile coordinate `j : Fin (alpha + 1)` represents class size
`j.val + 1`; the four embedded coordinates represent the sizes
`alpha-2`, `alpha-3`, `alpha-4`, and `alpha-5`.

## 16. Adversarial rejection checks

E625-10 is rejected if any of the following occurs.

1. The limiting Gaussian optimizer replaces `midpointOptimizer`.
2. The phase-center target replaces the exact midpoint target by equality.
3. A root is chosen without its E625-08 corridor membership.
4. `Int.toNat` is used before proving the midpoint integer nonnegative.
5. The signed factor `2^K` is asserted pointwise in each graph.
6. The multiplicity factorials `m_i!` are omitted.
7. The mixed finite-four/limiting-extended loss is used as the exact finite
   support loss in the root identity.
8. An `O(1)` tangent correction is assumed without exact conservation.
9. A scalar phase-independent limit is claimed for `log M_n/K_n`.
10. The endpoint `gamma_4/2` is claimed without a quantified uniform slack.
11. The full ambient profile length is charged in the Stirling remainder even
    though only four coordinates are active.
12. A second-moment, partial-diagonal, skeleton, or attachment theorem appears
    in the dependency graph.
13. The desired first-moment lower bound is inserted as a hypothesis of the
    finite entropy certificate.

## 17. Explicit non-goals

E625-10 does not prove:

- existence, uniqueness, or localization of either phase root;
- the chromatic lower-tail probability;
- a partial-diagonal estimate;
- a full-corner estimate;
- a high-skeleton estimate;
- a residual attachment estimate;
- a second-moment bound;
- Paley--Zygmund;
- positive probability of an actual cocoloring;
- amplification;
- the final Erdős 625 statement;
- the stronger `1000/639` endpoint without a welded exact finite certificate.

The retained midpoint location relative to the roots is an E625-08 corollary
consumed by the objective asymptotic. It need not be repeated in the
manuscript-facing E625-10 declaration.

## 18. Proof order

```text
E625-08 selectors and common uniform root data
  -> eventually_signedFourMidpointRoundingAdmissible
  -> exact tangent-rounded conservation
  -> exact embedded profile invariants
  -> expectation-to-partialSignedFirstMoment bridge
  -> finite KL rounding loss <= 50/7
  -> four-coordinate Stirling loss
  -> exact log-first-moment/objective bridge
  -> normalized midpoint objective asymptotic
  -> e625_10_signedFourSizeFirstMoment.
```

The finite `50/7` theorem is the principal new seam. It turns the rounded
integer profile into a quantitatively controlled competitor of the exact
finite Gibbs optimizer without introducing an asymptotic hypothesis or a
phase-dependent constant.
