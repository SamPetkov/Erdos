# Erdős 625 partial-diagonal closure audit

**Date:** 2026-08-05  
**Scope:** E625-11, exact common-subprofile contribution  
**Branch:** `agent/625-referee-readable-tier-one-pass`  
**Status:** the scalar finite-dimensional rate core is closed; the full asymptotic package is not

## Verdict

The principal finite-dimensional obstruction in the central partial-diagonal range is no longer an open proof-design problem. The public Lean root contains both:

1. the scalar theorem

   ```text
   partialDiagonalRate T R Ir <= -(1-R)/5000,
   ```

   under the manuscript structural inequalities; and
2. the four-deficit bridge deriving those inequalities from the actual support `{2,3,4,5}`.

The manuscript now uses a direct analytic proof of the same margin. It combines the two structural inequalities before splitting the scalar interval, so it no longer depends on the former `47/100` endpoint or on a separate numerical certificate for `log(100/47)`.

This closes the **scalar geometry** of E625-11. It does not close E625-11 as a whole. The remaining work is the uniform asymptotic transport from exact factorial expressions to that scalar rate, together with the two singular corners and their exhaustive assembly.

## 1. Exact pieces already present

### 1.1 Scalar rate theorem

`PartialDiagonalRateBound.lean` proves the following finite deterministic statement. If

```text
1/64 <= R <= 1,
T <= 4,
Ir - T R <= (5-T)R,
Ir - T R <= (T-2)(1-R),
```

then

```text
R log R + (log 2)/2 (Ir-TR) <= -(1-R)/5000.
```

The endpoint `R=1` is included. No asymptotic notation occurs in this theorem.

### 1.2 Four-deficit structural bridge

`PartialDiagonalFourDeficitRateBridge.lean` derives the two structural inequalities from the actual four-coordinate profile, nonnegativity, coordinatewise domination, total mass one, and mean `T`. It therefore rules out a hidden replacement of the four-size geometry by an assumed scalar surrogate.

### 1.3 Empty-corner finite recurrence

`PartialDiagonalMidpointActivityBridge.lean` proves an exact cutoff-activity estimate for the empty corner and bounds the finite cutoff sum by

```text
exp(sum_i muCutoffActivity_i).
```

The denominator retains the exact residual first moment `mu(n-massCap,u_i)`. No invalid replacement of `(n)_m` by `n^m` is used.

### 1.4 Full-corner finite reindexing

`FullCornerSumReindexing.lean` proves the exact involutive reindexing by complementary residual profiles under the full-mass hypothesis. This isolates the remaining full-corner task as an estimate on the reindexed local ratios divided by the complete signed first moment.

## 2. Cleaner scalar proof now used in the manuscript

Put

```text
Y = 1-R,
q = log 2.
```

The two structural inequalities are

```text
Ir-TR <= (5-T)R,
Ir-TR <= (T-2)Y.
```

Multiplying the first by `Y`, the second by `R`, and adding gives the uniform combined bound

```text
Ir-TR <= 3 R Y.                                      (2.1)
```

For `0<R<=1`,

```text
log R <= 2(R-1)/(R+1).                               (2.2)
```

This follows by applying monotonicity to

```text
f(x) = log(1+x) - 2x/(2+x),
f'(x) = x^2/((1+x)(2+x)^2) >= 0,
```

with `x=(1-R)/R`.

The positive atanh series gives

```text
2/3 < q < 7/10.                                      (2.3)
```

### Range I: `1/64 <= R <= 3/4`

Equations (2.1)--(2.3) yield

```text
Phi_T
 <= -2R/(1+R) Y + 21/20 RY
 = -[2/(1+R)-21/20] RY.
```

Since `2/(1+R) >= 8/7`,

```text
Phi_T <= -(13/140) RY
      <= -(13/8960)Y
      <= -Y/5000.
```

### Range II: `3/4 <= R <= 1`

The phase corridor gives `T <= 1+2/q < 4`. Hence the second structural inequality gives `Ir-TR <= 2Y`. Together with `log R <= R-1=-Y`,

```text
Phi_T <= -RY + qY
      = (q-R)Y
      <= -Y/20
      <= -Y/5000.
```

This proof covers the complete scalar interval without an endpoint grid or a convexity reduction to `R=47/100`.

## 3. Exact checker and its boundary

`check_partial_diagonal_rate_v3.py` verifies, with `Fraction` arithmetic only,

```text
56/81 > 2/3,
25/36 < 7/10,
8/7 - 21/20 = 13/140,
(13/140)(1/64) = 13/8960 > 1/5000,
3/4 - 7/10 = 1/20 > 1/5000.
```

The checker is a reproducible ledger for the rational constants. It does **not** prove:

- the logarithmic inequality (2.2);
- the four-deficit structural reduction (2.1);
- the uniform Stirling extraction;
- the phase-to-midpoint hypotheses;
- the empty/central/full partition of the sum;
- the final asymptotic statement.

The analytic inequalities are proved in the manuscript and the finite scalar/structural core is mirrored in Lean. The asymptotic bridges below remain separate obligations.

## 4. Remaining E625-11 interfaces

### E625-11A — empty-corner asymptotic bridge

The finite activity theorem is present. What remains is a phase-uniform theorem showing that, for the actual midpoint profile and manuscript cutoff,

```text
sum_i muCutoffActivity_i = o(1)
```

or the exact stronger bound used in the paper. This requires the uniform adjacent-size estimates for `mu_s(n)`, the class-count asymptotics, and control of the cutoff shift in the residual vertex count.

### E625-11B — uniform central rate extraction

The scalar theorem is present. What remains is one exact theorem converting the finite factorial expression `A_ell` into

```text
log A_ell
 <= K alpha Phi_T(z)
    + C K Y log(e/Y)
    + C log n
```

with one absolute `C`, uniformly over:

- the complete phase corridor;
- every admissible integer four-subprofile in the central range;
- coordinates that may vanish;
- sequences approaching either phase endpoint.

This theorem must also prove the exact relation between the residual vertex fraction and `R`, and the implication from the central residual-mass cutoff to `R>=1/64`.

### E625-11C — full-corner asymptotic bridge

The complementary-profile reindexing is present. What remains is a uniform estimate showing that every allowed residual-block increment is at most one in the full-corner range, followed by division by the actual complete signed first moment. The proof must consume the phase-uniform exponential margin supplied by E625-10, not a merely positive first moment.

### E625-11D — exhaustive assembly

The final theorem must show that the three ranges are pairwise disjoint and exhaustive under the exact integer cutoffs, and then combine them into the normalized complete partial-diagonal bound with one deterministic error sequence. The boundary cases must be assigned explicitly; no mass vector may be omitted or counted twice.

## 5. Refined status ledger

| Component | Finite deterministic core | Uniform asymptotic application | Status |
|---|---:|---:|---|
| Scalar four-deficit geometry | proved in Lean and manuscript | not applicable | **welded** |
| Empty-corner recurrence/activity | proved in Lean | still required | **running / needs review** |
| Central scalar negativity | proved in Lean and manuscript | Stirling/range bridge still required | **running / needs review** |
| Full-corner reindexing | proved in Lean | local-ratio and first-moment bridge still required | **running / needs review** |
| Three-range assembly | finite partition not yet frozen theorem-facing | still required | **blocked** |
| E625-11 as a whole | incomplete | incomplete | **not closed** |

## 6. Acceptance test for promoting E625-11

E625-11 may be marked welded only after one integrated commit contains:

1. the exact midpoint-profile hypotheses from E625-10;
2. a uniform empty-corner activity asymptotic;
3. the uniform central Stirling/rate extraction;
4. the full-corner local-ratio asymptotic;
5. a disjoint and exhaustive range partition;
6. the final normalized partial-diagonal theorem;
7. Lean 4.31 compilation with warnings fatal, placeholder and shortcut scans, axiom audit, and root replay;
8. an independent mathematical review of every asymptotic implication.

Until then, the correct statement is:

> The scalar partial-diagonal rate obstruction is closed. The complete partial-diagonal asymptotic package remains open because its uniform finite-to-asymptotic bridges and global range assembly have not yet been independently welded.
