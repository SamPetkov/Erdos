# Independent audit of `DENSE_FOUR_TYPE_MATCHING.md`

> **Historical-scope notice (2026-07-13).** This document preserves the
> internal 2026-07-12 verdict on the component bytes then under review. It is
> not a review of the later repaired or synchronized bytes. The authoritative
> proof is `../proofs/COMPLETE_PROOF_SELF_CONTAINED.md`; see
> `ADVERSARIAL_LEAP_AUDIT_2026-07-13.md` for the missing globalization bridge
> and its regression check, and
> `PROOF_COMPONENT_SYNCHRONIZATION_AUDIT_2026-07-13.md` for the synchronized
> component mapping. The original audit body and verdict below are retained
> unchanged.

## Verdict

**Core endpoint theorem: PASS.  Claimed completion of the whole high-cell
lemma: PASS.**

I reconstructed the endpoint incidence weight, all cancellations against
the two diagonal weights, the falling-factorial comparison, the
transportation-table summation, and all three ranges of the diagonal sum.
The central claims are correct:

\[
 W(L)\leq \sqrt{D(r)D(c)}\,\mathcal M(L)Q^L,
 \qquad
 \sum_LW(L)\leq
 e^{O(\sqrt{n\ln n})+O(\ln n)}\sum_rD(r),
\]

and the midpoint four-type profile has

\[
 \sum_rD(r)=1+o(1).
\]

The near-containment ratio and its multinomial summation are also correct.
The current version also includes the necessary large-/small-residual
middle-strip dichotomy in (5.6)--(5.8), and the imported common-part note
now explicitly extends its fixed-slack rate estimate to the (o(1))-enlarged
finite phase interval.

`DENSE_FOUR_TYPE_MATCHING.md`, (1.6), allows the actual finite mean (T) to
lie (o(1)) outside ([2/q,1+2/q]).  The imported statement in
`FOUR_SIZE_PARTIAL_RATES.md` is formulated on the exact interval, but now
states immediately after (0.5) that all estimates persist under this
(o(1))-enlargement.  This is valid: its numerical margins permit weakening
(1/5000), for example to (1/10000).  Thus the hypotheses now match
literally.

An earlier draft cited only the large-residual middle-strip estimate.  The
audited current draft has corrected this: (5.6)--(5.8) explicitly add the
small-residual bound `exp{O(n/(ln n)^5)}`.  I checked that derivation below.
The sharper display (6.1) is explicitly the endpoint-plus-near sum; the
complete high-cell corollary needs only the weaker `exp{o(n/(ln n)^4)}`
budget and therefore follows.

No reversal of concavity, missing factorial, missing unequal-margin factor,
or incorrect containment activity was found.

## 1. Claim-by-claim status

| Item | Status | Audit conclusion |
|---|---:|---|
| Exact endpoint incidence (W(L)), (1.9)--(1.10) | PASS | Slot choices, type pairings, stub choices, and the one global ((n)_J^{-1}) give exactly the displayed expression. |
| Diagonal identity (D(r)), (2.1) | PASS | It equals both the diagonal specialization of (W) and (prod_i\binom{k_i}{r_i}^2/Y_r^{\rm sgn}). |
| Falling-factorial concavity, (2.5)--(2.7) | PASS | The direction is correct and the Gamma derivative is bounded above by (ln(n+1)). |
| Local (Q_{ij}), (2.3) | PASS | Both the factorial constant and the power of two are exact. |
| Uniform (Q_{ij}\leq\eta_n^{|i-j|}/|i-j|!), (2.4) | PASS | The factor (2^{3/2}) safely uses (s\geq a-3); (eta_n=O((\ln n)^{3/2}/\sqrt n)). |
| Cauchy--multinomial sum with unequal margins, Lemma 3.1 | PASS | No assumption (r=c) is hidden; dropping opposite constraints gives the two exact multinomial expansions. |
| Vanishing diagonal range, Section 4.1 | PASS | The activity exponent, falling-factorial correction, and transition at (E=n/a^3) are consistent. |
| Fixed-positive diagonal range, Section 4.2 | PASS | The imported finite-dimensional rate proof is valid, gives (e^{-c_\delta n}), and now explicitly covers the midpoint's (o(1))-enlarged (T)-interval. |
| Near-full range and (Z_h^{\rm sgn}(M)\leq1), Section 4.3 | PASS | The unordered-partition bound, edge penalty, phase-uniform cancellation, and Vandermonde sum all have the correct direction. |
| Coverage of all diagonal vectors | PASS | The low, central, and near-full ranges cover every vector; only (D(0)=1) remains. |
| Near-containment local ratio, (5.1) | PASS | Direct cancellation gives exactly the displayed binomial, rising-factorial denominator, and binary exponent. |
| Near-containment summation, (5.3)--(5.5) | PASS | Consecutive ratios are log-convex on the stated range and are (o(1)) at both endpoints; the total multiplier is (e^{O((\ln n)^2)}). |
| Middle strip, (5.6)--(5.8) | PASS | The large-residual fixed-four-type sum is exponentially small; the small-residual branch adds only (O(n/(\ln n)^5)) to the logarithm. |
| Match to the midpoint profile | PASS | The four counts are (Theta(n/\ln n)), are uniformly positive, and the signed first moment is (e^{\Omega(K)}). No published ordinary-tame-profile hypothesis is needed. |

## 2. Independent reconstruction of (W(L)) and (D(r))

Fix a typed matrix (L=(\ell_{ij})) with row margins (r_i) and column
margins (c_j).  Selecting distinct row slots, distinct column slots, and
pairing the selected slots with type multiplicities (L) gives

\[
 \frac{\prod_i(k_i)_{r_i}\prod_j(k_j)_{c_j}}
      {\prod_{ij}\ell_{ij}!}.
\]

For a selected type-((i,j)) slot pair, prescribing
(x_{ij}=\min(u_i,u_j)) stub pairs has incidence

\[
 \frac{(u_i)_{x_{ij}}(u_j)_{x_{ij}}}{x_{ij}!},
\]

and all (J=\sum x_{ij}\ell_{ij}) prescribed pairs occur in a uniform
stub matching with probability (1/(n)_J).  Multiplication by the isolated
signed reward (g(x_{ij})) proves (1.9)--(1.10).  This is an exact incidence
weight.  The no-backtracking/canonical-skeleton restriction may subsequently
reduce it, which is harmless for the upper bound.

On the diagonal, (x_{ii}=u_i), so (B_{ii}=u_i!g(u_i)=b_i).  Therefore

\[
 W(\operatorname{diag}r)
 =\frac{\prod_i(k_i)_{r_i}^2}{\prod_i r_i!}
   \frac{\prod_i b_i^{r_i}}{(n)_{m_r}}=D(r).
\]

Independently, the signed partial first moment is

\[
 Y_r^{\rm sgn}
 =2^{\sum r_i}\frac{(n)_{m_r}}
 {\prod_i(u_i!)^{r_i}r_i!}
 2^{-\sum_i\binom{u_i}{2}r_i}.
\]

Substituting this into
(prod_i\binom{k_i}{r_i}^2/Y_r^{\rm sgn}) gives precisely the same
formula for (D(r)).  Thus there is no missing (r_i!), factor (2), or
ambient-vertex factorial.

## 3. Lemma 2.1: exact quotient and concavity direction

Dividing (W(L)) by (sqrt{D(r)D(c)}) cancels all slot falling
factorials and leaves the exact identity

\[
 \frac{W(L)}{\sqrt{D(r)D(c)}}
 =\frac{\sqrt{\prod_i r_i!c_i!}}{\prod_{ij}\ell_{ij}!}
  \frac{\sqrt{(n)_{m_r}(n)_{m_c}}}{(n)_J}
  \prod_{ij}
  \left(\frac{B_{ij}}{\sqrt{b_i b_j}}\right)^{\ell_{ij}}.
 \tag{3.1}
\]

This verifies all factorial cancellations before any inequality is used.

Let (f(x)=\ln(n)_x=\ln\Gamma(n+1)-\ln\Gamma(n-x+1)).  Then

\[
 f'(x)=\psi(n-x+1),\qquad f''(x)=-\psi'(n-x+1)<0.
\]

Writing

\[
 h=\frac12\sum_{ij}|i-j|\ell_{ij},
 \qquad \frac{m_r+m_c}{2}=J+h,
\]

concavity gives

\[
 \frac{f(m_r)+f(m_c)}2\leq f(J+h).
\]

Moreover (f') is decreasing and
(f'(x)\leq f'(0)=\psi(n+1)<\ln(n+1)).  Hence

\[
 \frac12\{f(m_r)+f(m_c)\}-f(J)
 \leq f(J+h)-f(J)\leq h\ln(n+1),
\]

which is exactly (2.7).  The direction in the note is therefore correct.
The argument remains valid when (h) is a half-integer because only the
Gamma interpolation is used.

For the local quotient, let (t=s+d).  Since the smaller slot is saturated,

\[
 B_{ij}=b_s\binom td,
 \qquad
 \frac{b_t}{b_s}=(t)_d2^{ds+\binom d2}.
\]

Consequently

\[
 \frac{B_{ij}}{\sqrt{b_i b_j}}
 =\frac{\sqrt{(t)_d}}{d!}
   2^{-(ds+\binom d2)/2},
\]

proving (2.3).  Finally, ((t)_d\leq a^d) and (s\geq a-3) imply

\[
 ds+\binom d2\geq d(a-3),
\]

so

\[
 Q_{ij}\leq \frac1{d!}
 \left(2^{3/2}\sqrt{\frac{(n+1)a}{2^a}}\right)^d.
\]

Using (2^a=\Theta(n^2/(\ln n)^2)) gives the asserted
(eta_n=O((\ln n)^{3/2}/\sqrt n)).  The constants in (Q_{ij}) all
pass.

## 4. Lemma 3.1: unequal margins and the transportation sum

For fixed (r,c), set

\[
 A_L=\frac{\prod_i r_i!}{\prod_{ij}\ell_{ij}!},\qquad
 C_L=\frac{\prod_j c_j!}{\prod_{ij}\ell_{ij}!}.
\]

The combinatorial coefficient in (2.2) is exactly
(sqrt{A_LC_L}).  Cauchy gives

\[
 \sum_{L:r,c}\sqrt{A_LC_L}Q^L
 \leq
 \left(\sum_{L:r,c}A_LQ^L\right)^{1/2}
 \left(\sum_{L:r,c}C_LQ^L\right)^{1/2}.
\]

Dropping only the column constraints in the first sum gives, row by row,

\[
 \sum_{L:\operatorname{row}L=r}A_LQ^L
 =\prod_i\left(\sum_jQ_{ij}\right)^{r_i}.
\]

Dropping only the row constraints in the second sum similarly gives the
column product.  This proves (3.5) for arbitrary (r,c); equal margins are
never assumed.  Since every row and column sum is (1+O(\eta_n)) and
(sum r_i=\sum c_i\leq K), the cost is (e^{O(\eta_nK)}).

Summing over all feasible pairs ((r,c)) gives

\[
 e^{O(\eta_nK)}\left(\sum_r\sqrt{D(r)}\right)^2
 \leq e^{O(\eta_nK)}\prod_i(k_i+1)\sum_rD(r).
\]

There are four coordinates, so the vector-count factor is (e^{O(\ln n)}),
and

\[
 \eta_nK=O\left(\frac{(\ln n)^{3/2}}{\sqrt n}
                         \frac n{\ln n}\right)
 =O(\sqrt{n\ln n}).
\]

This validates the entire Cauchy--multinomial step, including imbalance
paths.

## 5. Lemma 4.1: every diagonal range

### 5.1 Vanishing selected mass

The adjacent-size identity

\[
 \frac{\mu_{v-1}}{\mu_v}
 =\frac{v}{n-v+1}2^{v-1}
\]

is exact.  With (a=(2/q+o(1))\ln n), each downward size step multiplies
(mu) by (Theta(n/\ln n)).  Hence the (u=a) coordinate dominates

\[
 \Lambda=\sum_i\frac{k_i^2}{2\mu_{u_i}}
 =O((\ln n)^{-(2/q-1/2)})=o(1).
\]

Also

\[
 \frac{b_i}{n^{u_i}}
 =\frac{(n)_{u_i}}{n^{u_i}}\frac1{2\mu_{u_i}}
 \leq\frac1{2\mu_{u_i}},
\]

so, for (E=\sum r_i),

\[
 \sum_{\sum r_i=E}D(r)
 \leq \frac{n^{aE}}{(n)_{aE}}\frac{\Lambda^E}{E!}.
 \tag{5.1}
\]

For (E\leq n/a^3),

\[
 \ln\frac{n^{aE}}{(n)_{aE}}
 \leq\frac{(aE)^2}{n-aE}\leq\frac{2E}{a},
\]

and summing (5.1) gives (e^{e^{2/a}\Lambda}-1=o(1)).  For
(n/a^3<E\leq\delta n/(a-3)), put (t=aE/n).  Then

\[
 \ln\frac{n^{aE}}{(n)_{aE}}\leq\frac{t^2n}{1-t},
 \qquad
 \ln E!\geq E(\ln E-1),
\]

and ((\ln E-1)/a\geq q/3) uniformly.  Choosing (delta) so that
(t/(1-t)<q/6) makes each level at most (e^{-ctn}).  The smallest
(tn) in this range is (Theta(n/a^2)), so the sum over levels is still
(o(1)).  Since (m_r\geq(a-3)E), these two estimates cover all
(0<m_r\leq\delta n).

### 5.2 Fixed positive selected and residual mass

The direct rate imported from `FOUR_SIZE_PARTIAL_RATES.md` can be checked
without any prefix ordering.  For residual proportions (z_i), let
(R=\sum z_i), (Y=1-R), and (I_r=\sum iz_i).  The leading rate is

\[
 \Phi_T(z)=R\ln R+\frac q2(I_r-TR).
\]

The support endpoints alone give

\[
 I_r-TR\leq(5-T)R,
 \qquad
 I_r-TR=\sum_i(T-i)y_i\leq(T-2)Y.
\]

On the exact phase interval these imply, as in that note,
(Phi_T\leq-Y/5000) whenever (R\geq1/64).  If
(T) is allowed an (o(1)) overshoot, both right sides change only by
(o(1)R) or (o(1)Y); the fixed margins (17/1000) and (1/200) in the
two subintervals survive for all large (n).  Thus one may safely write

\[
 \Phi_T\leq-Y/10000
\]

under the literal hypothesis (1.6).

The finite factorial extraction is

\[
 \ln D(r)\leq K\alpha\Phi_T(z)
       +O\left(KY\ln\frac eY\right)+O(\ln n).
\]

For fixed positive selected and residual vertex fractions, (Y) and (R)
are bounded away from zero, (K\alpha=\Theta(n)), and the error is
(O(K)=o(n)).  Hence

\[
 D(r)\leq e^{-c_\delta n}.
\]

This confirms the central input independently of any published tame-profile
theorem.  It also covers fractional and nongreedy subprofiles.

### 5.3 Near-full selected mass

For (h=k-r), (H=\sum h_i), and (M=\sum u_ih_i), direct factorial
cancellation gives

\[
 D(k-h)=\left(\prod_i\binom{k_i}{h_i}\right)
         \frac{Z_h^{\rm sgn}(M)}{Z_k^{\rm sgn}(n)}.
 \tag{5.2}
\]

There are at most (H^M) unordered prescribed-block partitions (this is a
very loose but valid upper bound via assignments to (H) labelled boxes).
Every signed block contributes a factor (2), while its edge constraint
contributes (2^{-\binom u2}).  Since every residual block has size at
least (s=a-3),

\[
 \ln Z_h^{\rm sgn}(M)
 \leq qH+M\ln H-q\sum_i h_i\binom{u_i}{2}
 \leq qH+M\left(\ln H-\frac q2(s-1)\right).
\]

If (0<M\leq\delta n), then (H\leq M/s), and

\[
 \ln H-\frac q2(s-1)
 \leq \ln\delta+
 \left\{\ln n-\ln s-\frac q2(s-1)\right\}
 \leq\ln\delta+C.
\]

The last braces are (O(1)), uniformly in the phase, because
(qa=2\ln n-2\ln\ln n+O(1)) and (ln s=\ln\ln n+O(1)).
Moreover (qH\leq qM/s).  A fixed sufficiently small (delta) therefore
makes (ln Z_h^{\rm sgn}(M)\leq0), proving the claimed
(Z_h^{\rm sgn}(M)\leq1).

Also (H\leq M/s\leq2\delta K) for large (n).  Using the complete
signed margin and then Vandermonde gives

\[
 \sum_{M\leq\delta n}D(k-h)
 \leq e^{-c_ZK}\sum_{H\leq2\delta K}\binom KH
 \leq e^{-c_ZK+Kh_{\rm bin}(2\delta)}=e^{-\Omega(K)}.
\]

This includes (h=0), i.e. the full diagonal.  Together with the two
preceding ranges it leaves only (D(0)=1), and proves
(sum_rD(r)=1+o(1)).

## 6. Near-containment decorations

Let the two slot sizes be (m) and (m+d), and change the exposed cell
from (m) to (m-e).  Direct division of the two local incidence factors
gives

\[
 \begin{aligned}
 \frac{B(m-e)}{B(m)}
 &=\frac{\binom me d!}{(d+e)!}
   2^{\binom{m-e}{2}-\binom m2}\\
 &=\frac{\binom me}{\prod_{h=1}^e(d+h)}
   2^{-em+e(e+1)/2},
 \end{aligned}
\]

which proves (5.1).  For total deficit (Q), the one global denominator
changes by

\[
 \frac{(n)_{J_0}}{(n)_{J_0-Q}}
 =(n-J_0+Q)_Q\leq n^Q.
\]

This justifies charging (n^e) locally only after retaining the exact
joint denominator.

If (T_e=n^eR_{m,d}(e)), then

\[
 \frac{T_{e+1}}{T_e}
 =\frac{n(m-e)2^{-m+e+1}}{(e+1)(d+e+1)}.
\]

The quotient of this expression at (e+1) and at (e) is (5.4a).  On
(0\leq e\leq m/4), (0\leq d\leq3), direct cross-multiplication shows
that it is increasing.  Thus the consecutive-term ratios first decrease
and then increase, and their maximum is at an endpoint.  Those endpoint
bounds are

\[
 O((\ln n)^3/n),\qquad n^{-1/2+o(1)}.
\]

All ratios are therefore (o(1)), and the series is its first term up to a
(1+o(1)) factor:

\[
 \sum_{1\leq e<m/4}T_e=O((\ln n)^3/n).
\]

For (ell_{ij}) indistinguishable cells of one type, assigning deficits
produces exactly the multinomial factor
(ell_{ij}!/\prod_e\ell_{ij,e}!).  Hence the sum factorizes as
((1+\epsilon_n)^{\sum_{ij}\ell_{ij}}), and
(sum_{ij}\ell_{ij}\leq K).  This proves

\[
 (1+\epsilon_n)^K
 =\exp\{O(K(\ln n)^3/n)\}
 =\exp\{O((\ln n)^2)\}.
\]

### The middle-strip dichotomy

For completeness, the full high-cell lemma also permits cells outside
this near range.  Conditional on an endpoint/near skeleton with residual
stub mass (M_0\geq n/(\ln n)^6), the fixed-four-type version of
`RESIDUAL_ATTACHMENT.md`, (3.11), is

\[
 \Xi(M_0)\leq
 K^2\sum_{a/2<j\leq3a/4}
 g(j)\frac{(e a^2/M_0)^j}{j!}.
\]

Writing (j=x\log_2n), (1+o(1)\leq x\leq3/2+o(1)), the quadratic
coefficient in its base-two logarithm is
(x^2/2-x\leq-3/8+o(1)).  Thus
(Xi=2^{-\Omega((\ln n)^2)}).  The replacement of the equitable
(k,s) by (K,a) changes only lower-order (O((\ln n)\ln\ln n)) terms.

If (M_0<n/(\ln n)^6), the deterministic small-residual bound instead
gives

\[
 \ln\mathcal A\leq O(aM_0)=O(n/(\ln n)^5).
\]

Taking the worse of the two cases uniformly over the already summed
endpoint/near skeletons adds only (O(n/(\ln n)^5)) to the logarithm.
This is exactly the dichotomy now written as (5.6)--(5.8) in the audited
note, and it remains strictly inside the required (o(n/(\ln n)^4)) budget.

## 7. Match to the midpoint four-size profile

The profile in `ALPHA_MINUS_TWO_ROUTE.md` has exactly the support

\[
 \alpha-2,\ \alpha-3,\ \alpha-4,\ \alpha-5,
\]

so its relative-to-(a=\alpha-2) indices are (0,1,2,3), exactly as in
the dense note.  The limiting four-point tilt stays in a compact interval,
and every limiting mass exceeds (1/91).  Tangent integer rounding changes
each count by (O(1)), so (k_i/K\geq1/92) and
(k_i=\Theta(n/\ln n)) for all large (n).  The two integer constraints
give (sum_i u_ik_i=n).

At the midpoint, the uniform signed root separation and the envelope
derivative give

\[
 \ln Z_k^{\rm sgn}(n)=\Theta(n/\ln n)=\Theta(K),
\]

with a positive phase-uniform lower constant.  Hence (1.7) is genuinely
available.  The top-size bound (1.5) follows uniformly from the standard
cycle expansion for (mu_{\alpha-2}).

The dependency now explicitly covers the (o(1)) widening of the finite mean
interval; as checked above, the rate proof has more than enough fixed slack
to absorb it.  In particular, the current dense proof does not need
the published partial-profile conclusion for the special infinite-support
tame profile; the direct four-size common-part theorem supplies the needed
diagonal estimate.

## 8. Reproducible arithmetic checks

As supplementary diagnostics, I ran two independent finite checks using
only Python's standard library.

1. For 10,000 random choices of four consecutive sizes, slot counts, and
   feasible typed matrices, I evaluated logarithms of (W(L)), (D(r)),
   and (D(c)).  The exact quotient reconstruction (3.1) agreed to
   (2\cdot10^{-10}), and every instance satisfied the falling-factorial
   bound (2.7).
2. For 200 random small fixed-margin instances, I enumerated every feasible
   (4\times4) transportation table.  The direct sum of (W(L)) never
   exceeded the row/column multinomial right side obtained from Cauchy's
   inequality.

These computations are not used as proofs; they are checks against a
factorial, orientation, or inequality-direction transcription error.

## 9. Final conclusion

The rigorously audited endpoint-plus-near sum is

\[
 \sum_LW(L)D_{\rm near}(L)
 \leq\exp\{O(\sqrt{n\ln n})+O((\ln n)^2)\}.
\]

After applying the middle-strip dichotomy (5.6)--(5.8), the complete bare
high-cell sum is bounded by

\[
 \exp\left\{
 O(\sqrt{n\ln n})+O((\ln n)^2)
 +O\left(\frac{n}{(\ln n)^5}\right)
 \right\}
 =\exp\{o(n/(\ln n)^4)\}.
\]

The residual-attachment theorem then contributes another
(exp\{o(n/(\ln n)^4)\}).  Thus the dense four-type high-matching
obligation is closed at the amplification scale.
