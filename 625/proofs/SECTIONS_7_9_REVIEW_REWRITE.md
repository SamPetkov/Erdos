# Review-focused replacement text for Sections 7--9

**Status.** This file supplies drop-in replacement passages for the most
concentrated parts of the canonical manuscript.  It does not change the theorem,
constant, four class sizes, or proof architecture.  Its purpose is to make the
quantifiers, finite decompositions, and multiplicity accounting explicit enough
for independent review and later formalization.

The text is organized as replacement blocks rather than as a second complete
manuscript.  Equation numbers refer to the canonical manuscript.

## Global notation and uniformity edits

Use

\[
 q=\ln2,\qquad N=\ln n,\qquad w=\ln N.
\]

Rename the affine coefficient in equation (3.12) from `B_n` to
\(b_n^{\mathrm{aff}}\).  Reserve

\[
 \mathcal B_n:=\frac{n}{N^4}
\]

for the amplification scale currently called `B_n` in equation (10.10).

Unless a statement says otherwise, every asymptotic estimate in the replacement
text is uniform over:

1. the complete phase interval \(0\le\delta<1\);
2. the exact tangent-rounded four-size profile from Section 5;
3. every feasible subprofile or canonical skeleton in the displayed finite
   sum;
4. every residual degree list satisfying the displayed cap and total-mass
   hypotheses.

The constants may depend on fixed numerical corridor widths, but not on the
phase, profile coordinates, skeleton, or residual table.

---

## Replacement block A: the central rate in Lemma 7.1

Insert the following lemma after equation (7.21), replacing the compressed
numerical paragraph leading to (7.25).

### Lemma 7.1A (uniform central-rate gap)

Let \(p=(p_i)_{i=2}^5\) be a probability vector with

\[
 \sum_{i=2}^5 i p_i=T,
 \qquad
 \frac2q\le T\le1+\frac2q.
\]

Let \(0\le z_i\le p_i\), and put

\[
 R=\sum_{i=2}^5 z_i,\qquad
 Y=1-R,\qquad
 I_r=\sum_{i=2}^5 i z_i.
\]

For

\[
 \Phi_T(z)=R\ln R+\frac q2(I_r-TR),
\]

with the convention \(0\ln0=0\), one has

\[
 \Phi_T(z)\le-\frac{Y}{100}
 \qquad\text{whenever}\qquad
 \frac1{64}\le R\le1.
 \tag{7.21a}
\]

#### Proof

Because every residual deficit lies in \(\{2,3,4,5\}\),

\[
 I_r-TR=\sum_i(i-T)z_i\le(5-T)R.
 \tag{7.21b}
\]

Since \(y_i=p_i-z_i\), the mean identity for \(p\) also gives

\[
 I_r-TR=\sum_i(T-i)y_i\le(T-2)Y.
 \tag{7.21c}
\]

First suppose \(1/64\le R\le47/100\).  Since \(T\ge2/q\),

\[
 \Phi_T(z)
 \le R\left\{\ln R+\frac q2\left(5-\frac2q\right)\right\}
 =R\{\ln R+5q/2-1\}.
 \tag{7.21d}
\]

The function

\[
 f(R)=R\{\ln R+5q/2-1\}+\frac{1-R}{100}
\]

is convex on \((0,\infty)\).  Hence its maximum on
\([1/64,47/100]\) occurs at an endpoint.  Using \(q<0.6932\),

\[
 f(1/64)<-0.0436,
 \qquad
 f(47/100)<-0.0051,
\]

so \(f(R)<0\) throughout the interval.

Now suppose \(47/100\le R\le1\).  Since
\(T\le1+2/q\), equation (7.21c) gives

\[
 \Phi_T(z)
 \le R\ln R+(1-q/2)(1-R).
 \tag{7.21e}
\]

Set

\[
 h(R)=R\ln R+(1-q/2+1/100)(1-R).
\]

This function is convex, \(h(1)=0\), and a direct evaluation gives
\(h(47/100)<-0.0032\).  Convexity therefore places \(h\) below the chord joining
these endpoint values, so \(h(R)\le0\) on \([47/100,1]\).  Thus

\[
 \Phi_T(z)\le-\frac{1-R}{100}.
\]

Combining the two ranges proves (7.21a).  \(\square\)

### Completion of the central range

Return to the notation of Lemma 7.1.  If

\[
 m>\eta n,
 \qquad
 n-m>n/32,
\]

then equation (7.13) gives \(R\ge1/64\) for all sufficiently large \(n\), and
the selected mass satisfies \(Y\ge\eta/2\).  Lemma 7.1A and equation (7.20)
therefore give

\[
 \ln D(\ell)
 \le-\frac{k_{co}\alpha Y}{100}
      +Ck_{co}Y\ln(e/Y)+CN.
 \tag{7.24a}
\]

Here \(Y\ge w/(64N)\), \(\alpha=(2/q+o(1))N\), and
\(k_{co}=\Theta(n/N)\).  Consequently

\[
 \frac{\ln(e/Y)}{\alpha}=o(1),
 \qquad
 \frac{N}{k_{co}\alpha Y}=o(1),
\]

uniformly in the phase and in the central subprofile.  After increasing the
eventual threshold for \(n\), the two error terms in (7.24a) are at most half
of the leading negative term.  Thus there is an absolute \(c>0\) such that

\[
 D(\ell)\le \exp(-c k_{co}w)
 \tag{7.25}
\]

throughout the central range.  Since there are at most
\((k_{co}+1)^4\) subprofile vectors, their total contribution is \(o(1)\).

This formulation isolates the only numerical analytic estimate used in the
central range and makes its domain independent of the later asymptotic error
comparison.

---

## Replacement block B: exact canonical exposure at the start of Section 8

Replace the prose following equation (8.3) with the following proposition.

### Proposition 8.0 (canonical high-cell exposure identity)

Fix row degrees \((s_a)_a\) and column degrees \((t_b)_b\), each summing to
\(n\), and let \(r=(r_{ab})\) be a feasible overlap table.  Put

\[
 U=\alpha-2,
 \qquad
 R_0=\lfloor U/2\rfloor,
 \qquad
 M(r)=\{(a,b):r_{ab}>R_0\}.
\]

Then the following hold.

1. **Matching property.**  The support \(M(r)\) is a partial matching.  Indeed,
   two cells in one row or column, each larger than \(U/2\), would use more
   than the available degree, which is at most \(U\).

2. **Canonical demand.**  For \(e=(a,b)\in M(r)\), set \(j_e=r_{ab}\) and
   \(J=\sum_{e\in M(r)}j_e\).  Remove the selected \(j_e\) row and column stubs
   and their prescribed pairings.  The residual degree lists are

   \[
    s_a'=s_a-\sum_{b:(a,b)\in M(r)}j_{ab},
    \qquad
    t_b'=t_b-\sum_{a:(a,b)\in M(r)}j_{ab},
   \]

   and both sum to \(n-J\).

3. **Residual table.**  Define

   \[
    r'_{ab}=
    \begin{cases}
      0,&(a,b)\in M(r),\\
      r_{ab},&(a,b)\notin M(r).
    \end{cases}
   \]

   Then \(r'\) has margins \((s_a')\) and \((t_b')\), it vanishes on the
   exposed matching, and \(r'_{ab}\le R_0\) off the matching.

4. **Unique reconstruction.**  Conversely, the tuple consisting of the
   matching \(M\), the demands \((j_e)_{e\in M}\), the selected labelled stub
   pairs, and a residual matching satisfying the zero-on-\(M\) and cap-off-\(M\)
   conditions reconstructs one full matching and one overlap table.  Applying
   the canonical extraction to that table recovers the same tuple.

5. **Exact mass cancellation.**  The incidence of the exposed cells is

   \[
    \pi(M,j)=
    \frac{
      \prod_a(s_a)_{d_a}
      \prod_b(t_b)_{d_b'}
    }{
      (n)_J\prod_{e\in M}j_e!
    },
    \qquad
    d_a=\sum_{b:(a,b)\in M}j_{ab},
    \quad
    d_b'=\sum_{a:(a,b)\in M}j_{ab}.
    \tag{8.3a}
   \]

   The residual contingency-table mass is

   \[
    p_{res}(r')=
    \frac{
      \prod_a(s_a-d_a)!
      \prod_b(t_b-d_b')!
    }{
      (n-J)!\prod_{a,b}r'_{ab}!
    }.
    \tag{8.3b}
   \]

   Since \((s)_d=s!/(s-d)!\) and \((n)_J=n!/(n-J)!\), multiplication gives

   \[
   \begin{split}
    \pi(M,j)p_{res}(r')
    &=
    \frac{\prod_a s_a!\prod_b t_b!}
         {n!\prod_{e\in M}j_e!\prod_{a,b}r'_{ab}!}\\
    &=
    \frac{\prod_a s_a!\prod_b t_b!}
         {n!\prod_{a,b}r_{ab}!}
     =p(r).
   \end{split}
   \tag{8.3c}
   \]

Hence the canonical exposure is an exact finite partition of the overlap law:
every table appears once, with no hidden multiplicity and no proportionality
constant.  \(\square\)

### Definition 8.0A (bare canonical-skeleton weight)

For a feasible canonical skeleton \((M,j)\), define its **bare weight** to be
its exact exposure incidence multiplied by the local high-cell rewards,

\[
 \operatorname{Bare}(M,j)
 =\pi(M,j)\prod_{e\in M}g(j_e),
 \tag{8.3d}
\]

with the residual cap and no-return event retained in the residual law but with
the capped residual local/cycle factor postponed to Section 9.

When the proof below dominates an unfinished high-cell completion by the full
residual integrand, it is using a larger nonnegative quantity only to bound the
bare completion sum.  That domination does not redefine
\(\operatorname{Bare}(M,j)\), and Section 9 is still applied exactly once to the
true residual factor.

---

## Replacement block C: split form of Lemma 8.3

Replace Lemma 8.3 by the following four lemmas and final proposition.  The
calculation is the same as the canonical proof, but every summation level is
named explicitly.

### Lemma 8.3A (one-cell near-containment sum)

Let the smaller slot have size \(m\), the larger size \(m+d\), where
\(0\le d\le3\).  Replacing an endpoint multiplicity \(m\) by \(m-e\) has the
exact local ratio

\[
 R_{m,d}(e)=
 \frac{\binom me}{(d+1)\cdots(d+e)}
 2^{-em+e(e+1)/2}.
 \tag{8.21}
\]

After charging the possible loss of \(e\) units in the one global falling
factorial by \(n^e\), one has, uniformly in the four cell types,

\[
 \sum_{1\le e<m/4}n^eR_{m,d}(e)=O(N^3/n).
 \tag{8.25}
\]

#### Proof

The consecutive ratio of the summands is

\[
 \rho_e=
 \frac{n(m-e)2^{-m+e+1}}{(e+1)(d+e+1)}.
 \tag{8.23}
\]

For real \(e\),

\[
 \frac{d^2}{de^2}\ln\rho_e
 =-\frac1{(m-e)^2}
   +\frac1{(e+1)^2}
   +\frac1{(d+e+1)^2}>0
 \tag{8.24a}
\]

on \(0\le e\le m/4\) for all sufficiently large \(m\).  Thus the ratios are
log-convex and attain their maximum at an endpoint.  At \(e=0\), equation
(8.15) gives \(\rho_0=O(N^3/n)\); at \(e=\lfloor m/4\rfloor\),
\(\rho_e=n^{-1/2+o(1)}\).  Both are eventually below \(1/2\), uniformly in the
cell type, so the series is geometrically decreasing and (8.25) follows.
\(\square\)

### Lemma 8.3B (global product over near-containment decorations)

Fix a typed full-containment table \(L\).  Temporarily distinguish every
endpoint cell occurrence of \(L\).  For each occurrence \(c\), independently
choose either deficit \(e_c=0\) or \(1\le e_c<m_c/4\), and let
\(\mathcal S(L)\) be the resulting finite family of decorated skeletons.
If \(w(S)\) denotes the exact incidence and local high-cell reward of a
decorated skeleton, then

\[
 \sum_{S\in\mathcal S(L)}w(S)
 \le W(L)
 \prod_{c\in L}
 \left(1+\sum_{1\le e<m_c/4}n^eR_{m_c,d_c}(e)\right).
 \tag{8.25a}
\]

Forgetting the temporary labels gives exactly the typed multinomial
multiplicity; no additional factorial is introduced.  Because a high skeleton
is a matching, it has at most \(k_{co}\) cells.  Lemma 8.3A therefore gives

\[
 \sum_{S\in\mathcal S(L)}w(S)
 \le W(L)(1+O(N^3/n))^{k_{co}}
 =W(L)\exp(O(N^2)).
 \tag{8.26}
\]

### Lemma 8.3C (middle strip with large residual mass)

Fix a near-containment skeleton \(S\), and let \(m_0\) be the remaining stub
mass.  On the event \(\mathcal N(S)\) that no additional near-containment cell
occurs, every unexposed high cell has

\[
 R_0<j\le 3a/4+O(1),
 \qquad a=\alpha-2.
\]

Let \(E_{mid}(S)\) be the conditional expectation of the product of the local
rewards truncated to this middle strip, multiplied by
\(\mathbf1_{\mathcal N(S)}\).  If \(m_0\ge n/N^6\), then

\[
 E_{mid}(S)\le\exp(\Xi_4),
 \tag{8.26a}
\]

where

\[
 \Xi_4\le k_{co}^2
 \sum_{a/2<j\le3a/4+O(1)}
 g(j)\frac{(ea^2/m_0)^j}{j!}.
 \tag{8.27}
\]

Moreover there is an absolute \(c_0>0\) such that, for all sufficiently large
\(n\), every summand satisfies

\[
 \log_2\left[
   k_{co}^2g(j)\frac{(ea^2/m_0)^j}{j!}
 \right]
 \le-c_0(\log_2n)^2.
 \tag{8.28a}
\]

Consequently \(\Xi_4=2^{-\Omega((\log n)^2)}\), uniformly in \(S\).

#### Proof

Expand over distinct residual cells and threshold demands before dropping any
constraints.  Lemma 6.2 applies jointly and yields (8.26a)--(8.27).  Put
\(L_2=\log_2n\) and \(j=xL_2\).  The hypotheses imply

\[
 1+o(1)\le x\le3/2+o(1),
 \qquad
 \log_2m_0\ge L_2-6\log_2N.
\]

Using \(g(j)\le2^{j^2/2}\), \(k_{co}\le n\), and
\(\log_2(j!)\ge0\),

\[
 \log_2\left[
   k_{co}^2g(j)\frac{(ea^2/m_0)^j}{j!}
 \right]
 \le
 2L_2+\left(\frac{x^2}{2}-x\right)L_2^2
 +O(L_2\log L_2).
\]

On the limiting interval \([1,3/2]\),
\(x^2/2-x\le-3/8\).  Choose, for example, \(c_0=1/4\); the lower-order term is
smaller than \(L_2^2/8\) for all sufficiently large \(n\), uniformly over the
floor perturbations and the four cell types.  This proves (8.28a).
\(\square\)

### Lemma 8.3D (small residual completion)

If \(m_0<n/N^6\), then every residual degree and every residual cell
multiplicity are at most \(a\).  Pointwise,

\[
 \beta(S\cup H_{res})
 \le |E(H_{res})|
 \le m_0/2,
 \qquad
 \sum_e\binom{r_e}{2}
 \le(a-1)m_0/2.
 \tag{8.29}
\]

Hence every nonnegative completion weight needed to dominate the unfinished
high-cell sum is at most

\[
 \exp(Cam_0)\le\exp(Cn/N^5).
 \tag{8.29a}
\]

This bound is deliberately stronger than needed for the bare completion: it may
include the full residual cycle factor as a pointwise majorant.  It is used only
as a numerical upper bound for the completion sum and does not change the exact
factorization used in Section 9.

### Proposition 8.4 (sum of all bare canonical skeletons)

Let the sum range over every feasible canonical matching, every allowed high
multiplicity, and the induced nonnegative residual degree lists.  Then

\[
 \sum_{(M,j)}\operatorname{Bare}(M,j)
 \le
 e^{O(N^2)}
 \left(\sum_LW(L)\right)
 \max\{e^{\Xi_4},e^{Cn/N^5}\}.
 \tag{8.29b}
\]

Using Lemma 8.2, Lemmas 8.3A--8.3D, and
\(\eta_nk_{co}=O(\sqrt{nN})\),

\[
 \sum_{(M,j)}\operatorname{Bare}(M,j)
 \le
 \exp\{O(\sqrt{nN})+O(N^2)+O(n/N^5)\}
 =\exp\{o(n/N^4)\}.
 \tag{8.30}
\]

Every multiplicity is included exactly once: endpoint and near-endpoint
multiplicities are generated from a typed endpoint table, while the remaining
high multiplicities are generated in the middle-strip expansion under the
no-further-near-cell event.

---

## Replacement block D: residual-restriction product bound in Lemma 9.1

Replace the cycle decomposition and traversal discussion surrounding equations
(9.15)--(9.18) by the following two finite lemmas.

### Lemma 9.1A (an even matching completion is unique)

Let \(M\) be a matching and let \(R\) be any finite residual edge set.  Write

\[
 \mathcal C_{\rm even}(M,R)
 =\{F\subseteq M\cup R:\deg_F(v)\text{ is even for every }v\}.
\]

Then the restriction map

\[
 \rho:\mathcal C_{\rm even}(M,R)
 \longrightarrow\mathcal P(R\setminus M),
 \qquad
 \rho(F)=F\setminus M,
 \tag{9.15a}
\]

is injective.

#### Proof

Suppose \(\rho(F)=\rho(F')\).  Then the symmetric difference
\(F\mathbin\triangle F'\) is contained in \(M\).  It is also even, because
symmetric difference preserves vertex parity.  A nonempty subset of a matching
has degree one at every incident vertex, and therefore cannot be even.  Hence
\(F\mathbin\triangle F'=\varnothing\), so \(F=F'\).  \(\square\)

Equivalently, once the residual edges are specified, parity forces every
matching edge that can occur.  Some residual subsets have no even completion,
but none has two.

### Lemma 9.1B (weighted restriction product)

Let \(q_e\ge0\) for residual edges and put \(q_e=0\) on \(M\).  Then

\[
 \begin{split}
 \sum_{F\in\mathcal C_{\rm even}(M,R)}
      \prod_{e\in F\setminus M}q_e
 &\le
 \sum_{S\subseteq R\setminus M}\prod_{e\in S}q_e\\
 &=\prod_{e\in R\setminus M}(1+q_e)
 \le\exp\left(\sum_e q_e\right).
 \end{split}
 \tag{9.15b}
\]

#### Proof

Apply Lemma 9.1A and enlarge the image of \(\rho\) to the full power set.  The
middle identity is the finite subset-product expansion, and the last inequality
uses \(1+x\le e^x\).  \(\square\)

The two finite ingredients are already represented in the Lean development by
`residualRestriction_injective` and
`finiteInjectiveFamily_product_exp_bound`.

### Completion of the large-residual branch

Equation (9.12) and Lemma 9.1B give

\[
 \mathcal A(M,j)
 \le\exp\left(\Lambda_0+\sum_e q_e\right).
 \tag{9.16}
\]

By (9.6),

\[
 \sum_e q_e
 =\frac12\sum_{a,b}\theta_{ab}^2+\Lambda_0.
 \tag{9.17}
\]

The square sum factorizes exactly:

\[
 \sum_{a,b}\theta_{ab}^2
 =\frac{e^2}{m_0^2}
   \left(\sum_a d_a^2\right)
   \left(\sum_b(d'_b)^2\right).
 \tag{9.18}
\]

Every residual degree is at most \(U\), and both degree sums equal \(m_0\).
Consequently

\[
 \sum_a d_a^2\le Um_0,
 \qquad
 \sum_b(d'_b)^2\le Um_0,
 \qquad
 \sum_{a,b}\theta_{ab}^2\le e^2U^2.
 \tag{9.18a}
\]

Combining this with (9.13) yields the uniform one-sided bound

\[
 \boxed{
 \mathcal A(M,j)
 \le
 \exp\left\{C\left(U^2+\frac{U^4}{m_0}\right)\right\}.}
 \tag{9.19}
\]

If \(m_0\ge n/N^6\), then \(U=O(N)\) and
\(U^4/m_0=O(N^{10}/n)=o(1)\).  Thus

\[
 \mathcal A(M,j)\le\exp(C'N^2)
 =\exp\{o(n/N^4)\},
 \tag{9.19a}
\]

uniformly over every feasible canonical skeleton.

This argument removes the simple-cycle decomposition, residual-only walk sum,
mixed matching-cycle encoding, the parameter \(\tau\), and the factor
\(h\tau\).  It is deliberately coarser than the bounded-cell estimate in the
separate overlap note, but it is far sharper than needed for Proposition 9.2.
No lower estimate for \(\mathcal A(M,j)\) is asserted or used.

---

## Integration checklist

When incorporating these blocks into the canonical Markdown and generated TeX:

1. preserve equations (7.8)--(7.21), then insert Lemma 7.1A and replace the
   paragraph leading to (7.25);
2. insert Proposition 8.0 and Definition 8.0A immediately after (8.3);
3. replace the current Lemma 8.3 by Lemmas 8.3A--8.3D and Proposition 8.4;
4. replace the cycle/traversal passage by Lemmas 9.1A--9.1B and the global square-sum estimate;
5. rename the two unrelated uses of `B_n`;
6. regenerate the TeX and PDFs from the canonical source;
7. rerun display-tag, citation, finite-diagnostic, and formalization-status
   checks;
8. keep the status statement “candidate solution; not externally or fully
   formally verified” until the corresponding stronger review is complete.
