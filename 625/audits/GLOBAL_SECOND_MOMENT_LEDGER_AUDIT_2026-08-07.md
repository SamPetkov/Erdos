# Erdős 625 explicit global second-moment ledger audit

**Date:** 2026-08-07  
**Branch:** `agent/625-referee-readable-tier-one-pass`  
**Manuscript source:** `625/arxiv/SECTION9_EXPLICIT_GLOBAL_LEDGER_V3.tex`  
**Status:** complete candidate paper interface; independent review and exact Lean replay still required

## Purpose

The previous Section 9 concluded that the logarithm of the normalized second
moment is `o(n/(log n)^4)` by adding two asymptotic estimates in prose:

1. the total bare high-skeleton weight;
2. the conditioned residual attachment factor.

That argument had the correct architecture, but it did not give a named
finite-
`n` expression for either logarithmic cost. The new ledger defines both costs
explicitly, records their disjoint responsibilities, and defines the seed
exponent `Lambda_n` by exact addition.

## 1. Partial-diagonal input

The three disjoint Section 7 ranges produce deterministic errors

```text
epsilon_n^empty -> 0,
epsilon_n^central -> 0,
epsilon_n^full -> 0.
```

The ledger combines them as

```text
epsilon_n^pd
  = exp(epsilon_n^empty)-1
    + epsilon_n^central
    + epsilon_n^full.
```

Therefore

```text
sum_r D(r) <= 1 + epsilon_n^pd.
```

This is not a new estimate. It is the exact normalized form of the disjoint
three-range assembly, with the empty term `D(0)=1` separated from the error.

## 2. Endpoint transport with an explicit row sum

Let

```text
tau_n^end = 2^(3/2) sqrt((n+1)a/2^a),
a = alpha-2.
```

This is the quantity denoted by `eta_n` in the endpoint estimate of Section 8.
For sufficiently large `n`, `tau_n^end <= 1`. Since `Q_ii=1` and every row has
three off-diagonal positions,

```text
sum_j Q_ij <= 1 + 3 tau_n^end.
```

The proof uses only

```text
Q_ij <= (tau_n^end)^d_ij/d_ij! <= tau_n^end
```

for `i != j`. Repeating the exact multinomial summation from the endpoint-table
proof gives

```text
sum_L W(L)
  <= (1+3 tau_n^end)^K (1+epsilon_n^pd).
```

No table outside the realized finite domain is introduced.

## 3. Bare-skeleton logarithmic cost

The exact one-charge deficit reduction gives

```text
BareSkeletonSum_n
  <= (1+(alpha+1)rho_16)^K
     (1+3 tau_n^end)^K
     (1+epsilon_n^pd).
```

The ledger therefore defines

```text
Gamma_n^skel
  = K log(1+(alpha+1)rho_16)
    + K log(1+3 tau_n^end)
    + log(1+epsilon_n^pd).
```

The three terms have separate meanings:

- the first is the single ambient falling-factorial deficit charge;
- the second is the endpoint-transport charge;
- the third is the partial-diagonal reference mass.

The phase estimates already proved in Section 8 give

```text
K(alpha+1)rho_16 = O(n^(3/4) log n),
K tau_n^end       = O(sqrt(n log n)),
log(1+epsilon_n^pd) = o(1).
```

Thus

```text
epsilon_n^skel
  = (log n)^4 Gamma_n^skel/n
  -> 0.
```

## 4. Conditioned attachment logarithmic cost

The residual estimate has three cases.

### Zero residual mass

The residual matching is uniquely empty and the attachment factor is exactly
one. Its logarithmic cost is zero.

### Intrinsic regime

When `2^U <= m_0^3`, Section 9 proves

```text
A(M,j) <= exp(C_att U^2).
```

### Complementary regime

When `2^U > m_0^3`, one has `m_0 < 2^(U/3)` and

```text
A(M,j) <= 2^(U m_0/2)
       <= exp((log 2) U 2^(U/3)/2).
```

The ledger therefore defines the uniform deterministic cost

```text
Gamma_n^att
  = max(C_att U^2,
        (log 2) U 2^(U/3)/2).
```

Since

```text
U = O(log n),
2^U = Theta(n^2/(log n)^2),
```

one obtains

```text
Gamma_n^att
  = O((log n)^2
      + n^(2/3)(log n)^(1/3))
  = o(n/(log n)^4).
```

Equivalently,

```text
epsilon_n^att
  = (log n)^4 Gamma_n^att/n
  -> 0.
```

## 5. Exact global assembly

The exact conditioned decomposition is

```text
E[Z^2]/E[Z]^2
  = sum_(M,j) w(M,j) A(M,j).
```

All summands are nonnegative. The uniform attachment factor can therefore be
factored out without changing the skeleton domain:

```text
E[Z^2]/E[Z]^2
  <= exp(Gamma_n^att) BareSkeletonSum_n
  <= exp(Gamma_n^att+Gamma_n^skel).
```

Define

```text
Lambda_n = Gamma_n^skel + Gamma_n^att.
```

Then

```text
Lambda_n
  = (epsilon_n^skel+epsilon_n^att)
    n/(log n)^4
  = o(n/(log n)^4),
```

and

```text
1 <= E[Z^2]/E[Z]^2 <= exp(Lambda_n).
```

The lower bound is the nonnegativity-of-variance inequality.

## 6. No duplicated charge

The skeleton ledger contains:

- partial diagonals;
- the unique ambient deficit loss;
- endpoint transportation.

The attachment ledger contains:

- residual local rewards;
- residual cycle-space contributions.

The exact high cells are conditioned before the residual estimate is applied.
Accordingly, their multiplicities are not paid again in `Gamma_n^att`, and no
residual local or cycle factor appears in `Gamma_n^skel`.

This division of responsibilities is the principal logical value of the
explicit ledger.

## 7. Formalization target

A theorem-facing formalization should export three declarations:

1. `bareSkeletonSum_le_exp_GammaSkel`;
2. `residualAttachment_le_exp_GammaAtt`;
3. `normalizedSecondMoment_le_exp_Lambda` with
   `Lambda = GammaSkel + GammaAtt`.

The final declaration should consume the exact conditioned decomposition,
not a second independently defined overlap sum. Its theorem statement should
retain:

- the finite skeleton domain;
- the zero-residual branch;
- the exact definitions of both logarithmic costs;
- one phase-uniform eventuality threshold.

## Remaining status

The explicit ledger closes a manuscript-presentation gap and supplies a clean
formalization contract. It does not by itself make E625-12 or E625-13 welded.
The endpoint phase estimates, conditioned residual theorem, and final exact
summation still require independent line-by-line review and replay against the
private finite chain.

The publication switch must remain disabled.