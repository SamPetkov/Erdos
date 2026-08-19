# Erdős 625 proof-closure contracts

**Date:** 2026-08-05  
**E625-10 revision:** 2026-08-19  
**Scope:** public manuscript and theorem-facing interface  
**Branch:** `agent/625-e625-10-first-moment-expansion`  
**Status:** fail-closed planning document; no unresolved node is promoted by this file

## Purpose

The project has moved from proof discovery to proof closure, but the remaining work is not merely transcription into Lean. This document fixes the interfaces that must be reviewed before any global theorem can be described as closed. It separates:

1. finite deterministic identities already supported by exact proofs or checkers;
2. analytic statements that still require uniform asymptotic proofs;
3. global assembly statements that must be replayed on one dependency-consistent commit.

The contracts below are theorem-facing specifications. An implementation is accepted only if it preserves the manuscript definitions, quantifier order, constants, summation domains, and normalization exactly.

## Global acceptance conventions

Every asymptotic contract must satisfy all of the following.

- **One deterministic error sequence.** A statement uniform in the phase must use one error sequence for the entire phase interval, including integer sequences approaching either endpoint.
- **One eventuality threshold.** Any `eventually` statement must have a threshold independent of the phase and of the admissible profile within the stated corridor.
- **Exact integer profiles.** Conservation of the number of classes and the number of vertices must hold for the actual rounded integer profile. A continuous optimizer is not an acceptable substitute.
- **No hidden support change.** The four-size support, endpoint alphabets, selected cells, and residual families must be the manuscript objects, not enlarged or weakened surrogates.
- **No duplicated charge.** A factor paid in the high-skeleton quotient may not be paid again in the residual attachment sum, and conversely.
- **Normalized outputs.** Second-moment statements must expose the normalization by the square of the first moment rather than absorb it into an unnamed constant.
- **Fail-closed evidence.** Numerical experiments, exact rational checkers, isolated Lean lemmas, and stale branch builds are supporting evidence only. None closes a node without exact-statement review and integrated replay.

## Dependency spine

```text
E625-08  concrete phase center and slope
       ├── E625-09  chromatic lower tail
       └── E625-10  signed four-size first moment

E625-10 ── E625-11A/B/C/D  complete partial-diagonal package
E625-10 ── E625-12        high-skeleton quotient and endpoint transport
E625-12 ── E625-13        global residual attachment and normalized second moment

E625-09 + E625-10 + E625-11D + E625-13
       ── E625-14  concrete final instantiation
```

## E625-08 — concrete phase center and slope package

### Inputs

The exact finite-`n` phase parameter, the unrestricted coloring objective, the four-support signed objective, and the root corridor already used in Sections 1–5.

### Required output

A single theorem-facing package must provide, uniformly over the complete phase:

- existence and uniqueness of the ordinary root `r_+(n)` and the signed four-support root `r_4^co(n)` in the stated corridor;
- the concrete center estimates needed to locate both roots;
- the derivative estimate on every point between the two roots, with a uniform remainder of order at most `O((log n)(log log n))` relative to the leading `2(log n)^2/log 2` term;
- the phase-resolved separation

  ```text
  r_+(n) - r_4^co(n)
    = [((log 2)^2/4) A_4(delta_n) + o(1)] n/(log n)^3,
  ```

  with one deterministic `o(1)` sequence;
- the concrete corridor and feasibility facts consumed by tangent rounding and by the chromatic lower-tail theorem.

### Rejection conditions

The node remains open if the proof assumes a fixed interior phase, changes the support at an endpoint, proves only pointwise convergence, or exports a derivative bound that is too weak to retain the `n/(log n)^3` separation.

## E625-09 — chromatic lower-tail theorem

### Required output

There must be a deterministic integer sequence `k_chi^-(n)` such that

```text
P(chi(G_n) > k_chi^-(n)) -> 1
```

and

```text
|k_chi^-(n) - r_+(n)| = o(n/(log n)^3)
```

uniformly across the phase. The theorem must use the same ordinary root and phase convention as E625-08.

### Required audit points

- the lower-tail event is strict in the same direction used by the final union bound;
- all profile truncations are valid uniformly at both phase endpoints;
- integer rounding errors are absorbed at `o(n/(log n)^3)` scale;
- no density-one restriction on the integers remains.

## E625-10 — signed four-size first-moment assembly

### Exact design source

The frozen theorem package is

```text
625/formalization/E625_10_SIGNED_FOUR_SIZE_FIRST_MOMENT_PACKAGE_2026-08-19.md
```

and its adversarial review is

```text
625/audits/E625_10_SIGNED_FIRST_MOMENT_ADVERSARIAL_AUDIT_2026-08-19.md.
```

These files design the node; they do not promote it to welded status.

### Canonical objects

The total class count is exactly

```text
K_n = ceil((r_4^co(n) + r_+(n))/2),
```

after the eventual nonnegativity proof needed for `Int.toNat`. The tangent
correction changes the four multiplicities but preserves their total exactly.
There is no second bounded correction to `K_n`.

Let `m_n : Fin 4 -> Nat` be the exact tangent-rounded multiplicity vector and
let

```text
M_n = partialSignedFirstMoment n
        (fun i => phaseNat n - fourDeficit i) m_n.
```

The full embedded profile must be the literal four-deficit embedding in
`ColoringProfile (phaseNat n + 1)`.

### Required output

The manuscript-facing theorem must prove all of the following with one common
eventuality threshold.

1. **Exact finite admissibility.**

   ```text
   MidpointRoundingAdmissible n (phaseNat n) K_n.
   ```

2. **Exact integer conservation and support.**

   ```text
   sum_i m_i = K_n,
   sum_i (i+2)m_i = phaseNat n * K_n - n,
   vertexMass(k_n) = n,
   IsFourDeficitSupported (phaseNat n) k_n.
   ```

3. **Exact graph-expectation bridge.**

   ```text
   (signedProfileExpectation n k_n).toReal = M_n,
   signedProfileExpectation n k_n
     = 2^K_n * profileColoringExpectation n k_n.
   ```

4. **Exact finite optimizer-rounding loss.** The actual rounded profile must be
   compared with the exact finite Gibbs optimizer at the exact midpoint target,
   yielding

   ```text
   0 <= K_n * KL(r_n || p_n) <= 50/7.
   ```

5. **Four-coordinate Stirling bridge.** Since only four profile coordinates are
   active,

   ```text
   |log M_n - phaseSignedFourSizeObjective n K_n|
     <= 4 * factorialLogErrorBound n + 50/7.
   ```

6. **Phase-resolved normalized first moment.**

   ```text
   log M_n / K_n - A_4(delta_n)/2 -> 0.
   ```

7. **Uniform positive exponential margin.** For every fixed

   ```text
   0 < c < (1/2) log(200/153),
   ```

   the theorem must prove eventually

   ```text
   log M_n >= c K_n.
   ```

   If a stronger exact finite certificate is welded, the endpoint may be
   replaced by `(1/2) log(1000/639)` without changing the rest of the package.

### Required upstream input

E625-10 consumes, but does not restate, the E625-08 root selectors, common
corridor, phase-resolved root separation, class-count derivative estimate,
midpoint target transport, and `K_n ~ (log 2/2)n/log n`.

The retained midpoint location relative to the roots is therefore an E625-08
corollary used internally by the normalized objective proof, not an additional
probabilistic conclusion of E625-10.

### Rejection conditions

The node remains open if any of the following occurs:

- the limiting optimizer replaces `midpointOptimizer`;
- the phase-center target replaces the exact midpoint target by equality;
- an `O(1)` correction is used without exact count and mass conservation;
- `Int.toNat` is used before midpoint nonnegativity is proved;
- the exact expectation is not identified with `partialSignedFirstMoment`;
- multiplicity factorials are omitted;
- the finite KL loss `50/7` is replaced by a hidden equally difficult
  hypothesis;
- the normalized result is only pointwise in a fixed phase;
- the closed endpoint `(1/2)log(200/153)` is asserted without a quantified
  uniform slack;
- any partial-diagonal, skeleton, residual, or second-moment theorem appears as
  an input.

## E625-11 — complete partial-diagonal package

The existing exact identities, the scalar rate lemma, the four-deficit structural bridge, the full-corner reindexing, and the rational endpoint checker are ingredients. They do not by themselves prove the complete partial-diagonal sum.

### E625-11A — empty corner

Freeze the exact empty-corner range from Section 7 and prove that its normalized contribution has the manuscript bound, uniformly in the phase. The proof must retain the exact falling factorials in the range where replacing `(n)_m` by `n^m` is not uniform.

### E625-11B — central Stirling and rate theorem

For every admissible four-coordinate subprofile in the central range, prove the uniform extraction

```text
log A_ell
  <= K alpha Phi_T(z) + C K Y log(e/Y) + C log n
```

with one absolute `C`, followed by the structural reduction to

```text
Phi_T(z) <= -(1-R)/5000
```

on the complete stated range. The theorem must explicitly include:

- the relation between the residual vertex fraction and `R`;
- the lower bound that places `R` in the scalar-rate domain;
- the two structural endpoint inequalities;
- the convexity argument on both subintervals;
- uniform control of every Stirling and entropy remainder.

The exact checker now verifies the rational endpoint arithmetic only. Its success is not evidence for the omitted convexity, range-reduction, or uniform-error steps.

### E625-11C — full corner

Use the exact residual reindexing and local ratio bounds to prove the full-corner sum with the same first-moment normalization as the manuscript. The range must meet E625-11B without a gap or overlap ambiguity.

### E625-11D — partial-diagonal assembly

Prove that the empty, central, and full ranges are disjoint and exhaustive and combine their estimates into the complete partial-diagonal theorem consumed by the normalized second moment. The final output must be uniform in the phase and must state its deterministic error sequence explicitly.

## E625-12 — skeleton quotient and endpoint asymptotic assembly

### Already validated finite core

The completion-free physical-fiber factorization, exact one-cell deficit ratio, single ambient falling-factorial charge, optional-deficit product, weighted regrouping by realized endpoint table, and realized-table deficit product have substantial exact support.

### Required remaining output

A global theorem must combine those finite identities with the concrete phase estimates to bound the complete high-skeleton quotient over the manuscript summation domain. It must include:

- injective encoding or an exactly quantified multiplicity bound;
- endpoint-table feasibility and realization conditions;
- the phase-uniform common-charge estimate;
- the exact location where the single ambient loss is paid;
- the asymptotic summation over all admissible skeletons;
- an output in the normalization required by E625-13.

A random replay over feasible endpoint tables is adversarial evidence only; the theorem must cover every feasible table.

## E625-13 — global attachment and normalized second moment

### Required output

The global attachment theorem must combine the high-skeleton quotient with the conditioned residual law and the two residual regimes. It must derive, for the actual midpoint profile,

```text
E[X_n^2] / E[X_n]^2 <= exp(Lambda_n),
Lambda_n = o(n/(log n)^4),
```

with one deterministic error sequence uniform in the phase.

The proof must expose the chain

```text
threshold expansion
  -> exact restriction-product inequality
  -> exp(2 sum q_ab)
  -> intrinsic/complementary residual split
  -> global summation.
```

It must also show explicitly, at the upper endpoint of the quadratic-activity estimate, how the `U^2/8` contribution from the reward and the `-U^2/6` contribution from the activity combine to `-U^2/24`, up to `O(U log U)`.

### Rejection conditions

The node remains open if it assumes independence between residual cells, invokes the old cycle/walk route without proving equivalence, hides a skeleton multiplicity in the residual constant, or proves only fixed-phase smallness.

## E625-14 — concrete final instantiation

This is an adapter, not a place to introduce new analytic estimates. It may be promoted only after E625-08 through E625-13 are closed on the same commit.

Its output must instantiate the already-welded rare-seed amplifier and event assembly to prove

```text
P(
  chi(G_n) - zeta(G_n)
    >= ((log 2)^2/8) log(1000/639) n/(log n)^3
) -> 1.
```

The final replay must verify:

- the exact coefficient ledger;
- the strict uniform entropy margin;
- the seed exponent required by amplification;
- the `o(n/(log n)^3)` amplification loss;
- the direction of both final events;
- the union bound without an independence assumption;
- the complement corollary, separately from the main theorem.

## Promotion rule

A node may move from `needs-review` to `running` only after its exact theorem statement, constants, uniformity quantifiers, dependencies, and manuscript citation are frozen. It may move from `running` to `welded` only after:

1. isolated Lean 4.31 compilation with warnings fatal;
2. forbidden-shortcut and placeholder scans;
3. axiom audit;
4. import into the canonical theorem-facing root;
5. root replay on the integrated commit;
6. independent mathematical review of the paper argument corresponding to the declaration.

Until E625-14 passes this rule, `\ErdosProofClosedfalse` is mandatory and the manuscript remains a conditional verification draft.
