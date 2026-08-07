# Erdős 625 phase and root closure audit

**Date:** 2026-08-07  
**Branch:** `agent/625-referee-readable-tier-one-pass`  
**Manuscript sources:** `SECTION2_PHASE_PACKAGE_V3.tex`, `SECTION3_ROOT_GEOMETRY_V3.tex`  
**Status:** complete candidate paper interfaces; independent review and exact Lean replay still required

## Purpose

Sections 4 and 5 consume four facts from the phase/root calculation:

1. a phase-uniform independence-number cap;
2. a finite-to-limiting support comparison on a common compact target interval;
3. a unique root corridor with a positive derivative in the class-count variable;
4. error terms that remain uniform when the phase approaches either endpoint.

The previous manuscript contained the essential ideas, but packaged them in one long lemma with several unrelated `O(...)` terms. The replacement Sections 2 and 3 make the finite objects, uniform remainders, optimizer regularity, and theorem-facing error sequences explicit.

## 1. Uniform independence phase

The natural-log representation is now written exactly as

```text
alpha_0 = 2(L - ell + C)/q + 1,
q = log 2,
L = log n,
ell = log log n,
C = 1 + log q - q.
```

With `delta = alpha_0 - alpha` and `b = 1-delta`, this gives

```text
alpha = 2(L - ell + C)/q + b.
```

The phase expansion is stated with a deterministic uniform error:

```text
log mu_alpha
  = delta L
    + (2/q - 1/2 - delta) ell
    + K(delta)
    + E_n(delta),

sup_delta |E_n(delta)| <= epsilon_n^ph,
epsilon_n^ph = C_ph (1 + ell^2)/L -> 0.
```

The proof now identifies the three sources of this error separately:

- the falling-factorial remainder in `log (n)_alpha`;
- the Stirling remainder for `alpha!`;
- the uniform Taylor remainder after factoring `alpha=(2L/q)(1+x_n)`.

No endpoint-dependent constant is hidden in the expansion.

## 2. Adjacent-size control and the independence cap

The exact identity

```text
2^alpha = exp(2C + qb) n^2/L^2
```

makes the uniformity of the adjacent-size ratios immediate. For
`s=alpha+O(1)`,

```text
mu_{s+1}/mu_s = Theta(L/n),
mu_{s-1}/mu_s = Theta(n/L),
```

with absolute constants valid across the phase. This yields the sharpened
uniform expansions

```text
log mu_{alpha+2}
  = (delta-2)L + (2/q+3/2-delta)ell + O(1),

log mu_{alpha-2}
  = 2L + (2/q-5/2)ell
    + delta(L-ell) + K(delta) + O(1).
```

Consequently

```text
mu_{alpha+2} =: epsilon_n^cap -> 0,
mu_{alpha-2} >= c n^2 (log n)^(2/q-5/2).
```

The first sequence is exactly the deterministic cap error consumed by
Section 4.

## 3. Finite unrestricted support

The finite unrestricted deficit set is now named explicitly:

```text
S_+^(n) = {-1,0,...,alpha-1}.
```

This removes the former phrase “with the finite cutoff understood” from the
analytic core. The limiting support remains

```text
S_+ = {-1,0,1,...}.
```

The distinction is used throughout the partition functions, mean maps, and
dual values.

## 4. Exact affine cancellation

The decomposition

```text
-log d_{alpha-i} = A_n + B_n i + h_n(i)
```

is retained as an exact identity. Under the constraints

```text
sum p_i = 1,
sum i p_i = T,
```

`A_n+B_n T` is common to every support. Therefore the support comparison

```text
(L_R(n,k)-L_S(n,k))/k
  = F_{n,R}(T)-F_{n,S}(T)
```

is exact at finite `n`; it is not a consequence of the limiting Gaussian
model.

## 5. Uniform tilted-moment convergence

For bounded tilt, the finite weights satisfy the global majorant

```text
|i|^m exp(Lambda |i| - q i^2/2),
m=0,1,2.
```

The replacement proof uses the same majorant for:

- the finite-to-limiting convergence on fixed deficits;
- the infinite Gaussian tail;
- the tail omitted by the finite cutoff `alpha-1`.

It follows that `Z_{n,S}`, `M_{n,S}`, and `M'_{n,S}` converge uniformly on one
common compact tilt interval.

The limiting variance is positive and continuous. Its compact minimum gives a
single constant `v_*>0`, so the inverse mean maps are uniformly Lipschitz.
The manuscript consequently defines

```text
epsilon_n^dual
  = max_S sup_{T in K_*}
      (|F_{n,S}(T)-F_S(T)|
       + |lambda_{n,S}(T)-lambda_S(T)|)
  -> 0.
```

This is the deterministic finite-dual error needed by the Section 5 target
transport.

## 6. Optimizer regularity

Strict concavity gives the exact finite optimizer

```text
p_{n,S,T}(i)
  = exp(lambda_{n,S}(T)i+h_n(i))
    / Z_{n,S}(lambda_{n,S}(T)).
```

On the four-point support, uniform convergence and compactness imply

```text
sup_T max_i |p_{n,i}(T)-p_i(T)| -> 0,
inf_{n large,T,i} p_{n,i}(T) > 0.
```

This is precisely the positivity needed by tangent rounding and the boundary
entropy estimates in Section 7.

## 7. Root corridor and normalized slope error

Writing

```text
Psi_{n,S}(s) = L_S(n,n/s)/(n/s),
T = alpha-s,
```

the exact normalized exponent is

```text
Psi_{n,S}(s)
  = (s-1)L-s+1+log s
    + A_n+B_n(alpha-s)
    + F_{n,S}(alpha-s).
```

At the phase center, the scalar cancellations are displayed explicitly and
give

```text
Psi_{n,S}(s_0)=O(log log n)
```

uniformly in the phase. The derivative is

```text
Psi'_{n,S}(s)
  = L-1+s^(-1)-B_n+lambda_{n,S}(T)
  = -L+O(log log n).
```

A fixed corridor therefore has opposite signs at its endpoints and strict
monotonicity throughout. This proves existence and uniqueness of the corridor
root before any mean-value argument is used.

In the original class-count variable,

```text
d/dk (L_S(n,k)+ck)
  = 2/q L^2 + O(L ell).
```

The theorem now records the deterministic normalized error

```text
epsilon_{n,A}^slope
  = sup |(log n)^(-2) d/dk(L_S+ck)-2/q|
  -> 0.
```

This is a stronger and cleaner interface for Sections 4 and 5 than a bare
pointwise asymptotic.

## 8. Validation architecture

The canonical source remains frozen. The wrapper

`625/scripts/build_phase_root_self_contained_v3.py`

first invokes the existing manuscript generator and then replaces the legacy
Sections 2 and 3 exactly once. It fails if either marker drifts or if either
legacy section survives.

The checker

`625/experiments/check_phase_root_package_v3.py`

verifies:

- insertion of both theorem-facing sources;
- removal of the compressed legacy passages;
- the phase, cap, dual, slope, and root-transport interfaces;
- preservation and uniqueness of the equation tags;
- balanced TeX environments and braces;
- absence of placeholders, legacy `ln` notation, and manual-tagged numbered
equation environments.

The dedicated GitHub Actions workflow replays both the pre-existing manuscript
checks and the new checker under ordinary and optimized Python, then builds and
inspects the complete PDF.

## Remaining status

The replacement files are complete candidate paper proofs of the phase and
root package. They do not by themselves promote E625-08 or E625-10 to welded
status. Promotion still requires:

1. independent line-by-line verification of the asymptotic algebra and the
   finite-support dominated-convergence argument;
2. exact Lean theorem signatures with the same quantifier order and deterministic
   error sequences;
3. replay against the actual midpoint profile and Section 5 root transport;
4. one integrated axiom and dependency audit.

The publication switch must therefore remain disabled.