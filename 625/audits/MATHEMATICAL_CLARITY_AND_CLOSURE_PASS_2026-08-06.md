# Erdős 625 mathematical clarity and closure pass

**Date:** 2026-08-06  
**Branch:** `agent/625-referee-readable-tier-one-pass`  
**Scope:** Sections 5, 7, 8, 9, final constant ledger, and manuscript validation  
**Status:** fail-closed; this audit does not promote the main theorem

## Executive assessment

This pass addresses six places where a referee could reasonably object that a correct idea had not yet been expressed at the theorem-facing level:

1. Section 5 moved from the finite target mean at the unrestricted root to the phase center inside an unexplained `o(1)`;
2. the empty partial-diagonal corner did not display the uniform comparison between the intermediate and ambient first moments;
3. the central partial-diagonal proof compressed the uniform Stirling, entropy, and residual-fraction errors into prose;
4. the full partial-diagonal corner did not state why every reverse-recurrence step remains inside the small residual range, and the three ranges were not assembled as a literal partition;
5. Section 9 defined residual activities by dividing by the residual mass before separating the zero-residual case;
6. the final coefficient relied on a strict phase certificate without exhibiting a fixed margin capable of absorbing the deterministic `o(1)` error.

All six interfaces are now explicit. Section 7 now contains a complete candidate paper proof of its empty, central, and full ranges and their normalized assembly. This is a material proof-closure improvement, but it is not yet independent verification or a welded Lean theorem.

## 1. Finite-target transport in the signed root separation

The root comparison is isolated in
`625/arxiv/SECTION5_ROOT_TRANSPORT_V3.tex`. At the unrestricted root, the manuscript first records the exact finite identity

```text
Phi_n(r_+)
  = r_+ {log 2 - D_{4,n}(T_+(n))},
T_+(n) = alpha - n/r_+(n).
```

No limiting functional is substituted in this equality. The passage to the phase center is decomposed into the uniform convergence of the two finite dual values on `K_*` and the displacement

```text
T_+(n)-T_0 = O(log log n/log n).
```

The limiting dual derivative is `F_S'(T)=-lambda_S(T)`, and the tilts are uniformly bounded on `K_*`. Hence the limiting dual values are uniformly Lipschitz. The manuscript defines one deterministic error sequence

```text
omega_n^root
  = sup |F_{n,S+}-F_{S+}|
    + sup |F_{n,S4}-F_{S4}|
    + C |T_+(n)-T_0|,
```

proves `omega_n^root -> 0` uniformly in the phase, and obtains

```text
Phi_n(r_+)
  = r_+ {log 2 - D_4(delta) + O(omega_n^root)}.
```

The positive entropy margin and positive corridor derivative then prove
`r_4^co < r_+`, so the orientation and nonemptiness of the subsequent mean-value interval are explicit.

## 2. Empty partial-diagonal corner

The empty corner is isolated in
`625/arxiv/SECTION7_EMPTY_CORNER_V3.tex`. For an intermediate selected mass `m'` and block size `u_i`, the exact comparison is

```text
mu_{u_i}(n)/mu_{u_i}(n-m')
  = (n)_{u_i}/(n-m')_{u_i}.
```

In the range `m' <= eta n`, phase-uniform control of `u_i=O(log n)` gives

```text
mu_{u_i}(n)/mu_{u_i}(n-m')
  <= (1-2 eta)^(-u_i)
  <= (log n)^(3/8).
```

The exact one-block recurrence may therefore be iterated in any order. The resulting product is summed by enlarging to the complete nonnegative four-dimensional lattice. The exponent is

```text
(log n)^(3/8) Xi_empty
  = O((log n)^-(2/log 2-7/8)),
```

and the explicit inequality

```text
2/log 2 - 7/8 > 111/56 > 0
```

leaves a fixed power margin. Thus the range contributes

```text
1 <= sum_empty D(ell) <= exp(epsilon_n^empty) = 1+o(1)
```

for one deterministic phase-independent sequence `epsilon_n^empty -> 0`.

## 3. Central partial-diagonal range

The central argument is isolated in
`625/arxiv/SECTION7_CENTRAL_EXTRACTION_V3.tex`.

### Uniform Stirling and entropy errors

For every nonnegative factorial argument,

```text
log(t!) = t log t - t + sigma(t),
|sigma(t)| <= C_S log(t+2).
```

Only a fixed number of factorials occurs, so the total error is `O(log n)` uniformly, including zero coordinates. The exact rounded profile has all four proportions uniformly bounded below, and the coordinatewise entropy term is bounded by `C_H y log(e/y)`. The four-coordinate entropy inequality then gives

```text
sum_i y_i log(e/y_i) <= Y log(4e/Y).
```

### Affine phase and residual-fraction transport

Exact subtraction gives

```text
E_{i+1}-E_i = -(log 2) alpha/2 + O(1).
```

Averaging the affine correction and using only the upper bound supplied by the positive complete first moment yields

```text
sum_i y_i E_i
  <= ((log 2) alpha/2)(T Y-I)+O(Y).
```

The proof also displays

```text
rho-R = (I-TY)/(alpha-T),
|I-TY| <= 3Y,
```

and derives the missing bridge

```text
n rho log rho
  = k_co alpha R log R + O(k_co Y).
```

### Rate negativity and deterministic sum

The two four-deficit structural inequalities combine to

```text
I_r-TR <= 3R(1-R).
```

Together with `log R <= 2(R-1)/(R+1)`, this gives the two explicit margins

```text
1/64 <= R <= 3/4:  Phi_T <= -(13/8960)(1-R),
3/4  <= R <= 1:    Phi_T <= -(1/20)(1-R).
```

The proof defines `epsilon_n^diag -> 0`, obtains

```text
D(ell) <= exp(-c k_co log log n),
```

and names the total deterministic central error

```text
epsilon_n^central
  = (k_co+1)^4 exp(-c k_co log log n) -> 0.
```

Every threshold is independent of the phase.

## 4. Full partial-diagonal corner and exact range assembly

The full corner and assembly are isolated in
`625/arxiv/SECTION7_FULL_CORNER_V3.tex`.
For residual vertex mass `w <= n/32`, the exact first-moment ratio gives

```text
mu_{u_i}(w)/mu_{u_i}(n)
  <= (w/n)^(u_i),
```

and the phase expansion yields the uniform envelope

```text
mu_{u_i}(w) <= n^(-4+o(1)) <= n^-3.
```

If a residual profile `h` is exposed in any order, every next step satisfies

```text
v(a)+u_i <= v(h) <= n/32.
```

The exact reverse recurrence is therefore at most `2n^-2<1` at every step. Consequently `B(h)<=1`, and the positive signed first-moment margin gives

```text
D(k-h) <= exp(-c_Z k_co).
```

After summing the polynomial number of residual profiles, one obtains a deterministic phase-independent sequence `epsilon_n^full -> 0`.

For all sufficiently large `n`, `eta<31/32`, and the coordinate box is the disjoint union

```text
E_n = {m <= eta n},
C_n = {m > eta n and n-m > n/32},
F_n = {n-m <= n/32}.
```

The full and empty ranges cannot meet because the full range has `m>=31n/32`. The remaining profiles satisfy the two strict central inequalities. Hence no subprofile is omitted and no boundary contribution is counted twice. Adding the three deterministic estimates gives

```text
1 <= sum_ell D(ell)
  <= exp(epsilon_n^empty)
     + epsilon_n^central
     + epsilon_n^full
  = 1+o(1),
```

with one eventuality threshold for the complete phase.

### Status consequence

The manuscript now contains a complete candidate proof of E625-11A--D, conditional on the exact midpoint-profile and positive-first-moment inputs from E625-10. The node remains `needs review`: each standalone source must still receive independent line-by-line mathematical verification, be frozen as an exact theorem interface, and be replayed in Lean against the actual midpoint profile. The finite scalar and reindexing lemmas already welded privately do not by themselves perform this promotion.

## 5. Section 7--8 accounting interface

Section 7 does not remove, condition away, or subtract overlaps containing common whole classes. Its partial-diagonal weights form a one-sided normalized reference sum. Section 8 dominates endpoint-table weights by this reference sum through the square-free transport inequality.

The manuscript states this explicitly at the start and end of Section 8 and defines

```text
w_hi(P,j) := w(P,j),
```

so the bare high-skeleton weight in Section 8 is visibly the same object used in the exact conditional decomposition of Section 9. The one-sided reference vector is restricted to its actual finite coordinate box.

## 6. Zero residual mass and exact conditional decomposition

The activity `theta_ab=e d_a d'_b/m_0` is meaningful only for `m_0>0`. Section 9 now handles `m_0=0` first: the residual matching is uniquely empty, all residual local factors are one, and the exposed high cells form a matching with cycle rank zero. Therefore

```text
A(M,j)=1 when m_0=0.
```

The exact overlap decomposition is justified by the two-way reconstruction

```text
overlap matrix
  <-> canonical high-cell matching and multiplicities
      + capped residual matching with no return to exposed cells.
```

This makes uniqueness and absence of double counting explicit. The prescribed-cell estimate is a joint factorial-moment inequality; no independence between residual cells is asserted.

## 7. Fixed slack in the final constant

The exact rational checker now verifies

```text
L(49q/20) < 2629/10000,
H(29q/10) < 37/2500,
L(29q/10) < 329/2500,
H(83q/20) < 357/2500.
```

Both tilt ranges satisfy `L(lambda_4)+H(lambda_4)<2777/10000`, giving

```text
A_4(delta) > log(20000/12777).
```

The fixed slack over the displayed theorem constant is

```text
log(20000/12777)
  = log(1000/639) + log(12780/12777).
```

The final proof explicitly takes `n` large enough that the deterministic probability error is smaller than the coefficient corresponding to this positive slack. The theorem coefficient is unchanged.

## 8. Midpoint and PDF consistency

The total class count is fixed as

```text
k_co = ceil((r_4^co+r_+)/2).
```

The tangent correction changes only the four type multiplicities and preserves both conservation laws; it does not add another bounded correction to `k_co`.

Manually tagged displays are placed in unnumbered AMS environments. The PDF workflow fails on duplicate Hyperref destinations in addition to unresolved references, unresolved citations, and material overfull boxes.

The fail-closed checker and workflow now require and archive the standalone Section 5 source and all three Section 7 range sources, together with the exact numerical ledgers and representative rendered pages.

## Remaining proof-closure boundary

This pass does not close the following nodes:

1. the exact concrete phase center and slope package;
2. the full-sequence chromatic lower tail;
3. the complete signed four-size first-moment assembly;
4. independent mathematical verification and exact Lean replay of the complete candidate E625-11 partial-diagonal package;
5. the complete high-skeleton quotient and endpoint asymptotic theorem;
6. the global residual attachment and normalized-second-moment theorem;
7. the final integrated theorem-facing replay.

Accordingly, the publication switch must remain disabled and PR #58 must remain a draft.
