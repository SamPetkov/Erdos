# Canonical Version 2 mathematical rewrite specification

**Purpose:** a section-by-section replacement plan for `625/arxiv/main.tex` after the remaining Section VIII theorem is proved  
**Authority:** the exact theorem statements must be rechecked against the integrated Lean/public proof branch before manuscript substitution

## 1. Main theorem package

Let

\[
 q=\ln2,
 \qquad
 H_n=\frac{n}{(\ln n)^3},
 \qquad
 A_4(\delta)=\ln2-D_4(\delta).
\]

### Proposed main theorem

> **Theorem (phase-resolved chromatic--cochromatic gap).** Let
> `G_n~G(n,1/2)` and let `delta_n` be the complete independence-number phase.
> Then
> \[
>  \chi(G_n)-\zeta(G_n)
>  \ge
>  \left[
>   \frac{q^2}{8}A_4(\delta_n)-o(1)
>  \right]H_n
> \]
> with high probability, uniformly along the full sequence of integers `n`.

The `o(1)` is deterministic and uniform in the phase.

### Proposed certified corollary

Use the exact entropy certificate

\[
 A_4(\delta)>\ln(1000/639)
 \qquad(0\le\delta\le1)
\]

to state

\[
 \chi(G_n)-\zeta(G_n)
 \ge
 \frac{q^2}{8}\ln(1000/639)H_n
\]

with high probability. The coefficient is

\[
 0.0268964098083791186\ldots.
\]

### Proposed complement corollary

\[
 \min\{\chi(G_n),\chi(\overline G_n)\}-\zeta(G_n)
 \ge
 \frac{q^2}{8}\ln(1000/639)H_n
\]

with high probability.

## 2. Constant derivation to insert after the root calculation

Retain the exact phase-resolved root displacement

\[
 r_+(n)-r_4^{\rm co}(n)
 =\left[
   \frac{q^2}{4}A_4(\delta_n)+o(1)
  \right]H_n.
\]

For

\[
 k_{\rm co}=\left\lceil\frac{r_4^{\rm co}+r_+}{2}\right\rceil,
 \qquad
 k_\chi^- =\lfloor r_+\rfloor-\lceil\ln n\rceil,
\]

write directly

\[
\begin{aligned}
 k_\chi^- - k_{\rm co}
 &=\frac12(r_+-r_4^{\rm co})-O(\ln n)\\
 &=\left[
   \frac{q^2}{8}A_4(\delta_n)+o(1)
  \right]H_n.
\end{aligned}
\]

Since the amplifier adds `o(H_n)` parts, the same leading coefficient survives in the final gap. Do not introduce the intermediate fixed halvings currently appearing in (5.12), (5.20), and (11.2).

## 3. Section 5 entropy certificate replacement

Replace the old omitted-mass bounds by the exact rational certificate from PR #32. The replacement lemma should state only what is used downstream:

> **Lemma (uniform four-support entropy advantage).** For every
> `delta in [0,1]`,
> \[
>  D_4(\delta)<\ln(639/500),
>  \qquad
>  A_4(\delta)>\ln(1000/639).
> \]

The proof may be placed in a compact appendix if the exact rational interval calculations make the main narrative too long. Its required ingredients are:

1. the certified tilt interval
   \[
   \frac{49}{20}q<\lambda_4<\frac{83}{20}q;
   \]
2. a split at `29q/10`;
3. the four exact omitted-ratio inequalities;
4. monotonicity of the low and high omitted masses;
5. evaluation of the full-support dual function at the four-support optimizer.

## 4. Section 7 corrections and strengthening

### 4.1 Correct signed partial moment

Change

```tex
2^\ell_\bullet
```

to

```tex
2^{\ell_\bullet}.
```

### 4.2 Replace decimal central-rate verification

Use the exact strengthened central rate from PR #30. State it as a finite analytic lemma with rational logarithm bounds rather than decimal evaluations embedded in the proof. The target form is

\[
 \Phi_T(z)\le-c_0(1-R)
\]

on the complete central domain, with one explicit rational `c_0` no smaller than `1/100` if the final audited domain matches the PR #30 certificate.

### 4.3 Record margin dependence

For later non-midpoint work, parameterize the positive signed first-moment margin by

\[
 M_n(k)=L_{S_4}(n,k)+qk.
\]

At the midpoint, `M_n(k_co)>=c n/ln n`. The fixed-midpoint paper may keep this simpler bound. A separate proposition should record the exact dependence for moving placements rather than hiding it in `c_Z`.

## 5. New Section VIII finite parameterization

### 5.1 Block support and partial physical fibres

For each attained canonical high physical skeleton, define:

- a block-level bipartite matching `P` between row and column blocks;
- endpoint sizes `s_e,t_e` and `m_e=min(s_e,t_e)`;
- actual multiplicity `j_e` with `R_0<j_e<=m_e`;
- deficit `h_e=m_e-j_e`;
- one size-`j_e` partial physical matching inside each selected block pair.

Prove that these data give a disjoint parameterization of the attained canonical high-skeleton family. This theorem must be finite and exact; no asymptotic estimate belongs in its statement.

### 5.2 Aggregate fibre weight

After summing the local partial matching fibres, prove

\[
 w(P,j)=
 \frac{\prod_{e\in P}(s_e)_{j_e}(t_e)_{j_e}}
      {(n)_J\prod_{e\in P}j_e!}
 \prod_{e\in P}g(j_e),
 \qquad J=\sum_ej_e.
\]

For the full-containment reference `j_e=m_e`, this weight must agree with the decorated endpoint reference sum already identified with `W(L)`.

### 5.3 Exact aggregate ratio

For endpoint sizes `m,m+d`, prove

\[
 \frac{
  (m)_{m-h}(m+d)_{m-h}g(m-h)/(m-h)!
 }{
  (m)_m(m+d)_mg(m)/m!
 }
 =R_{m,d}(h),
\]

where

\[
 R_{m,d}(h)
 =\frac{\binom mh}{(d+1)\cdots(d+h)}
  2^{-hm+h(h+1)/2}.
\]

If `J_* = sum m_e = J+H`, then

\[
 \frac{(n)_{J_*}}{(n)_J}=(n-J)_H\le n^H.
\]

Hence

\[
 \frac{w(P,m-h)}{w(P,m)}
 \le\prod_{e\in P}n^{h_e}R_{m_e,d_e}(h_e).
\]

### 5.4 One all-high deficit estimate

The high condition implies `2h<m`. Use

\[
 h\left\lfloor\frac{2m}{3}\right\rfloor
 \le hm-\frac{h(h+1)}2
\]

to derive

\[
 n^hR_{m,d}(h)
 \le
 \left(
  \frac{nm}{2^{\lfloor2m/3\rfloor}}
 \right)^h.
\]

Define

\[
 \rho_n=
 \max_{\alpha-5\le m\le\alpha-2}
 \frac{nm}{2^{\lfloor2m/3\rfloor}}.
\]

The phase relation gives

\[
 \rho_n=O\!\left(\frac{(\ln n)^{7/3}}{n^{1/3}}\right)=o(1).
\]

Thus, for large `n`,

\[
 \sum_{h\ge1}\rho_n^h\le2\rho_n.
\]

For a fixed block support `P`, the whole deficit fibre is bounded by

\[
 w(P,m)(1+2\rho_n)^{|P|}
 \le w(P,m)(1+2\rho_n)^{k_{\rm co}}.
\]

### 5.5 Endpoint table sum

Use the exact endpoint reference normalization and the square-free AM--GM transportation inequality to prove

\[
 \sum_Pw(P,m)=\sum_LW(L)
 \le
 (1+C\eta_n)^{k_{\rm co}}\sum_rD(r),
\]

where

\[
 \eta_n=O\!\left(\frac{(\ln n)^{3/2}}{\sqrt n}\right).
\]

Since `sum_r D(r)=1+o(1)`, conclude

\[
\begin{aligned}
 \operatorname{BareSkeletonSum}_n
 &\le
 (1+2\rho_n)^{k_{\rm co}}
 (1+C\eta_n)^{k_{\rm co}}(1+o(1))\\
 &\le
 \exp\left\{
  O(n^{2/3}(\ln n)^{4/3})+O(\sqrt{n\ln n})
 \right\}\\
 &=\exp\left\{o\left(\frac n{(\ln n)^4}\right)\right\}.
\end{aligned}
\]

This replaces the entire near/middle split in the old Lemma 8.3.

## 6. New Section IX direct attachment theorem

### 6.1 Restriction-product lemma

State the generic finite lemma:

> If deletion of `I` is injective on a finite family `C` of subsets of `E`, then for nonnegative activities `q_e`,
> \[
>  \sum_{A\in\mathcal C}\prod_{e\in A\setminus I}q_e
>  \le\prod_{e\in E\setminus I}(1+q_e).
> \]

For the even-subgraph family, deletion of the exposed matching is injective.

### 6.2 Q-only local absorption

Outside the matching, use

\[
 q_{ab}=\frac{\theta_{ab}^2}{2}+\lambda_{ab}^{\rm loc},
 \qquad
 \lambda_{ab}^{\rm loc}\le q_{ab}.
\]

Therefore the local product and even-subgraph product are bounded together by

\[
 \exp\left\{2\sum_{a,b}q_{ab}\right\}.
\]

Under the degree caps and `2^U<=m^3`, the checked total-q estimate gives

\[
 \sum_{a,b}q_{ab}\le CU^2.
\]

### 6.3 Intrinsic complementary regime

If `2^U>m^3`, use the exact finite implication

\[
 m<2^{\lceil U/3\rceil}
\]

and the deterministic capped attachment bound. Assemble both regimes over the literal attained attachment sum.

### 6.4 Aggregate statement

The authoritative Section IX endpoint should be

\[
 \operatorname{AttachmentSum}_n
 \le
 \operatorname{BareSkeletonSum}_n
 \exp\left\{\varepsilon_n\frac n{(\ln n)^4}\right\},
 \qquad
 \varepsilon_n\to0.
\]

This statement composes directly with the exact normalized-second-moment identity. Do not reintroduce a polymer surrogate or independent demand law.

## 7. Proposition 9.2 replacement proof

Write the normalized signed second moment exactly as the attained attachment sum. Apply the aggregate Section IX theorem, then the Section VIII bare-skeleton estimate:

\[
\begin{aligned}
 \frac{\mathbb EZ^2}{(\mathbb EZ)^2}
 &\le
 \operatorname{BareSkeletonSum}_n
 \exp\left\{\varepsilon_n\frac n{N^4}\right\}\\
 &\le
 \exp\left\{o\left(\frac n{N^4}\right)\right\}.
\end{aligned}
\]

There is no need to take a supremum over skeletons or to enumerate simple cycles.

## 8. Section 10 named amplifier theorem

Retain Lemmas 10.1 and 10.2, but promote the following statement:

> **Proposition (rare-seed completion tail).** If
> \[
>  \Pr\{\zeta(G_n)\le k_n\}\ge e^{-\Lambda_n},
> \]
> then, uniformly for deterministic `r>0`,
> \[
> \Pr\!\left(
> \zeta(G_n)>k_n+C\left[
> \frac{\sqrt{n\Lambda_n}+\sqrt{nr}}{\ln n}+n^{1/3}+1
> \right]\right)
> \le e^{-r}+o(1).
> \]

This theorem should be phrased independently of the midpoint profile.

## 9. Version 2 conclusion

Intersect the unrestricted chromatic lower event with the amplified cocoloring upper event. Use

\[
 k_\chi^- - k_{\rm co}
 =\left[\frac{q^2}{8}A_4(\delta_n)+o(1)\right]H_n
\]

and the `o(H_n)` amplifier loss to obtain the phase-resolved theorem. Then state the fixed certificate and complement corollary.

## 10. Material to move out of the main proof

The following should be retained as historical/repository alternatives but removed from the canonical Version 2 proof:

- the Section VIII near/middle split;
- `E_mid`, `Xi_4`, and the Section VIII residual-mass dichotomy;
- simple-cycle decomposition of the residual even family;
- the residual walk kernel `S`;
- the mixed matching-cycle encoding;
- the parameters `tau` and `h tau`;
- the old conservative `/32` coefficient ledger.

## 11. Material for a separate “Further directions” section

Do not state the following as proved consequences of Version 2:

- shrinking near-root placement;
- exact phase minimum;
- global balance necessity for arbitrary cocolorings;
- slowly growing support;
- a two-sided `Theta(n/(log n)^3)` gap;
- fixed `p!=1/2`;
- the two-independent-graph coupling.

The balanced rare seed, finite restriction-product theorem, cycle-space factor, and tunable amplifier are rigorous enough to mention as proved method-level results, with their exact scopes.
