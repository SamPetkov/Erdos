# Erdős 625: fused transport and critical-quarter refinement

Date: 2026-08-10  
Status: candidate theorem-facing refinement; not welded  
Base: `agent/625-referee-readable-tier-one-pass` at `bbe1a9441d16364aad94d9fa547f6282594be62b`

## Purpose

This pass asks whether the explicit Section 8--9 ledger can be made both
stronger and easier to formalize without changing the random variable, the
canonical high-cell decomposition, the four-size profile, or the final theorem
coefficient.

Two avoidable losses were identified.

1. The existing deficit sum forgets the endpoint type, bounds every term by
   `rho_16`, counts at most `alpha+1` possible deficits, and only afterward
   performs endpoint transport. This creates an artificial factor `alpha+1`.
2. The residual argument splits at `m_0 = 2^(U/3)`. The exponent `1/3` is a
   convenient interior point, not the structural threshold. The local reward
   at the endpoint `R=floor(U/2)` has quadratic exponent `U^2/8`, so the true
   exponential boundary is `m_0` of order `2^(U/4)`, with a fixed
   multiplicative buffer and only one factor of `U` needed to control the
   factorial remainder.

The refinement preserves the fail-closed status. It is a candidate paper
argument and a proposed simplification of the future Lean interface.

## Result 1: type-preserving deficit product

For a high cell of endpoint type `(i,j)`, the existing local comparison gives

```text
n^h R_{m,d}(h) <= rho_{ij}^h.
```

Once `rho_{ij}<1`, the entire optional deficit sum is bounded by the geometric
series

```text
1 + sum_{h in A_e} rho_{ij}^h <= 1/(1-rho_{ij}) =: B_{ij}.
```

Thus, for a fixed support `P`,

```text
sum_h w(P,m-h)
  <= w_full(P) product_{e in P} B_{type(e)}.
```

This is strictly sharper than the previous uniform bound

```text
w_full(P) (1+(alpha+1)rho_16)^|P|.
```

It also respects the endpoint table. If `L=(ell_ij)` is the realized table,
the deficit factor is exactly bounded by

```text
B^L = product_{i,j} B_ij^(ell_ij).
```

Weighted reference regrouping therefore gives

```text
BareSkeletonSum_n <= sum_L W(L) B^L.
```

No separate support-cardinality estimate is needed at this stage.

## Result 2: one fused `4 x 4` kernel

Let `Q` be the endpoint-transport kernel from Section 8 and define

```text
Qtilde_ij = B_ij Q_ij,
Sigma_n   = max_i sum_j Qtilde_ij.
```

Multiplying the square-free endpoint inequality by `(B^L)^2` gives

```text
(W(L)B^L)^2
  <= [D(r) A_L Qtilde^L] [D(c) C_L Qtilde^L].
```

The arithmetic--geometric mean inequality and one multinomial sum imply

```text
BareSkeletonSum_n
  <= Sigma_n^K sum_r D(r)
  <= Sigma_n^K (1+epsilon_n^pd).
```

This single proposition replaces the following sequence in the coarse ledger:

1. local deficit counting;
2. the factor `(alpha+1)rho_16`;
3. `|P|<=K`;
4. unweighted regrouping by `L`;
5. a separate endpoint row-sum estimate.

For Lean, the finite combinatorial core can be stated for an arbitrary finite
endpoint alphabet, a nonnegative reference kernel `Q`, and a nonnegative
multiplicative perturbation `B`. The four-size asymptotics enter only when
bounding `Sigma_n`.

## Result 3: exact phase scale for the deficit kernel

Write

```text
q = log 2,
L = log n,
ell = log log n,
alpha = 2(L-ell+C)/q + b,
0 <= b <= 1.
```

Every endpoint minimum satisfies `m_ij >= alpha-5`. Since

```text
floor((3m_ij-1)/4) >= (3alpha-20)/4,
```

one obtains

```text
q floor((3m_ij-1)/4)
  >= (3/2)(L-ell+C) - 5q.
```

Hence

```text
2^floor((3m_ij-1)/4)
  >= c_0 n^(3/2) (log n)^(-3/2)
```

with a fixed `c_0>0`, and therefore

```text
rho_16 = O((log n)^(5/2)/sqrt(n)).
```

Because `Q_ii=1`, the off-diagonal row mass is
`O((log n)^(3/2)/sqrt(n))`, and `B_ij=1+O(rho_ij)`,

```text
Sigma_n = 1+O((log n)^(5/2)/sqrt(n)).
```

With `K=Theta(n/log n)`, the fused skeleton exponent is

```text
Gamma_skel^sharp
  = K log Sigma_n + log(1+epsilon_n^pd)
  = O(sqrt(n) (log n)^(3/2)).
```

The previous coarse deficit contribution was `O(n^(3/4) log n)`.

## Result 4: fixed-buffer critical-quarter residual split

Set

```text
T_U = 64 U 2^(U/4).
```

The constant `64` is a convenient fixed buffer. It is not optimized; its role
is to leave a transparent negative linear margin after the quadratic endpoint
terms cancel.

### Large residual mass

If `m_0 >= T_U`, then every cell intensity satisfies

```text
theta_ab <= (eU/64) 2^(-U/4).
```

For

```text
a_x = g(x) theta^x/x!,
R   = floor(U/2),
```

the existing log-convexity argument reduces the higher activity to the two
endpoints `a_3` and `a_R`.

The first endpoint obeys

```text
R a_3 / theta^2 <= (eU^2/192)2^(-U/4) -> 0.
```

At the other endpoint,

```text
log_2(R a_R/theta^2)
 <= log_2 R + binom(R,2) - 1 - log_2(R!)
    + (R-2)(log_2 e + log_2 U - 6 - U/4).
```

Here `U` is either `2R` or `2R+1`. Hence

```text
binom(R,2) - U(R-2)/4 <= R/2,
U <= (7/3)R  for R>=3.
```

The integral estimate for the factorial gives

```text
log_2(R!) >= R log_2 R - R log_2 e.
```

Using `1<log_2 e<3/2` and `1<log_2(7/3)<5/4`, the endpoint logarithm is at
most

```text
7 - 5R/4 - log_2 R,
```

which is negative for `R>=6`. Consequently `q_ab <= C theta_ab^2`, and the
exact intensity-square identity gives

```text
sum_e q_e <= C U^2,
A(M,j) <= exp(C U^2).
```

### Small residual mass

If `m_0<T_U`, the existing crude estimate gives

```text
A(M,j) <= 2^(U m_0/2)
        <= exp(32 (log 2) U^2 2^(U/4)).
```

The case `m_0=0` contributes one and is included.

Thus one may take

```text
Gamma_att^sharp
  = max(C U^2, 32 (log 2) U^2 2^(U/4)).
```

Since `2^U=Theta(n^2/(log n)^2)` and `U=O(log n)`,

```text
Gamma_att^sharp
  = O(sqrt(n) (log n)^(3/2)).
```

This replaces the previous complementary exponent
`O(n^(2/3)(log n)^(1/3))`.

## Quantitative seed corollary

Combining the exact conditioned decomposition with the two sharpened exponents
gives a fixed constant `C_sharp` such that

```text
1 <= E[Z^2]/E[Z]^2
  <= exp(C_sharp sqrt(n) (log n)^(3/2)).
```

Therefore

```text
P(Z>0)
  >= exp(-C_sharp sqrt(n) (log n)^(3/2)).
```

The main theorem only needs an exponent `o(n/(log n)^4)`, so this is strictly
stronger than the existing seed input. It does not change the theorem
coefficient.

## Exact checks added

`625/experiments/check_sharpened_transport_attachment_v4.py` performs the
following fail-closed checks.

- It verifies the semantic theorem markers and the complete tag range
  `(9.43)--(9.57)`.
- It checks environment, brace, control-byte, and notation hygiene.
- It verifies the exact integer inequality
  `binom(R,2)-U(R-2)/4 <= R/2` for `8<=U<=4096`.
- It evaluates both endpoint ratios at the buffered critical intensity
  `theta=(eU/64)2^(-U/4)` and confirms that they are at most one for
  `12<=U<=4096`; smaller `U` is absorbed into the absolute constant.
- It verifies the exponent arithmetic for the fused skeleton and
  critical-quarter attachment rates.

The numerical range is a regression check, not a substitute for the analytic
factorial argument in the manuscript.

## Proposed Lean interfaces

The refinement suggests three declarations.

1. **Finite fused-kernel theorem.** Given a finite endpoint alphabet, a
   reference table weight satisfying the square-free transport inequality, and
   multiplicative cell perturbations `B`, prove the row-sum bound
   `sum_L W(L)B^L <= Sigma^K sum_r D(r)`.
2. **Critical-quarter scalar lemma.** For `R=floor(U/2)` and
   `theta<=(eU/64)2^(-U/4)`, prove
   `sum_{x=3}^R Delta_x theta^x/x! <= C theta^2`.
3. **Sharp ledger adapter.** Combine the fused skeleton exponent and the
   critical-quarter attachment exponent in the exact conditional
   decomposition.

This is a smaller interface than formalizing the coarse `alpha+1` deficit
count and the arbitrary `m_0^3` case split separately.

## Verification boundary

The refinement has been checked algebraically and compiled as an isolated AMS
source. It still requires:

- independent line-by-line review of the fused weighted regrouping;
- integrated compilation against the complete manuscript;
- exact replay against the private welded Section 8 finite chain;
- Lean statements with the same finite domains and quantifier order;
- one final axiom audit.

The publication switch must remain false.
