# Independent full-chain audit 1 of `COMPLETE_PROOF_DRAFT.md`

**Audit date:** 2026-07-12  
**Auditor verdict:** **PASS**  
**Scope of the verdict:** the current, repaired formulation of the draft and
the component lemmas listed in its Section 8.  This is an internal
mathematical reconstruction, not external peer review or a claim about
priority.

I treated the theorem as unproved and rebuilt the chain from the exact
profile counts, the configuration-model overlap law, and bounded
differences.  In particular, I did not use the conclusions of the draft as
premises.  I found no missing overlap regime, false inequality, circular
dependency, or phase-restricted hypothesis in the current chain.

Two points were repaired while this audit was in progress:

1. The phase-uniform independence-set statement is
   `mu_{alpha+2}=n^{delta-2+o(1)}<=n^{-1+o(1)}`, not equality to
   `n^{-1+o(1)}` at every phase.  The current draft has the correct form.
2. The profile rounded at the midpoint must be the exact finite-`n`
   four-size variational optimizer.  It converges uniformly to the Gaussian
   in (2.3), but rounding the limiting optimizer itself would not justify an
   `O(log n)` error relative to the finite optimum.  The current draft and
   component notes now make the exact finite optimizer explicit.

Neither repair changes the theorem or its constant.

## 1. Obligation matrix

| Proof obligation | Verdict | Independent conclusion |
|---|---:|---|
| Phase expansion, uniformly for all `0<=delta<1` | PASS | The expansion for `mu_alpha` and the two exact adjacent ratios imply `mu_{alpha+2}=n^{delta-2+o(1)}<=n^{-1+o(1)}` uniformly. |
| Exclusion of independent sets of size `alpha+2` | PASS | Markov gives `P(alpha(G)>alpha+1)=o(1)` for every sufficiently large integer `n`. |
| Unrestricted chromatic first-moment lower root | PASS | Exact profile enumeration, the continuous maximum, and an `O(log n)` downward shift in the colour count give `P(chi<=k_chi^-)=o(1)`. |
| Root phase and derivative | PASS | At every relevant support, `n/k=alpha_0-1-2/q+o(1)` and `dL/dk=(2/q)(ln n)^2+O(ln n ln ln n)`, uniformly through the phase cycle. |
| Four-size entropy loss certificate | PASS | The dual calculation gives `D_4<ln(153/100)` uniformly on the complete mean-deficit interval. |
| Signed root separation | PASS | Dividing the signed advantage `k(q-D_4+o(1))` by the root derivative gives exactly the coefficient `q^2(q-D_4)/4`. |
| Exact finite-`n` optimizer and rounding | PASS | The four masses stay uniformly positive; tangent integer correction changes `O(1)` counts and the exact log moment by `O(log n)`. |
| Midpoint signed first-moment margin | PASS | The midpoint profile satisfies `ln E Z_k^sgn >= c_Z k` for a phase-independent `c_Z>0`. |
| Signed overlap normalization | PASS | The normalized local factor is exactly `A_zeta(r)=2^{W+c-v}=prod g(r_ab) 2^{beta(H)}`. |
| Ordered/unordered profile normalization | PASS | Labelling equal-size slots multiplies `Z` by a deterministic `prod k_i!`, which cancels from the normalized second moment; the formulas for `D(r)` use the corresponding unordered partial first moment correctly. |
| Canonical high-cell decomposition | PASS | Cells above `floor(U/2)` form a matching; the exposed incidence factor and conditional residual configuration law multiply to the original overlap probability exactly. |
| Partial diagonal: vanishing mass | PASS | The exact recurrence is dominated by a Poisson series whose total activity is `o(1)`. |
| Partial diagonal: macroscopic mass | PASS | The derived rate `Phi_T` is uniformly negative away from its two corners, including nongreedy subprofiles. |
| Partial diagonal: near-full mass | PASS | The complementary exact recurrence and the complete signed first-moment margin give exponential suppression. |
| All diagonal endpoints | PASS | Combining the preceding three ranges gives `sum_r D(r)=1+o(1)`. |
| Dense unequal-type transportation | PASS | The exact geometric-mean comparison retains `(n)_J`; Cauchy plus two multinomial expansions sums all imbalanced paths and directed cycles at cost `exp(O(sqrt(n ln n)))`. |
| Near-containment decorations | PASS | The exact local ratio and the one global denominator comparison give total cost `exp(O((ln n)^2))`. |
| Mixed four-type middle strip | PASS | For residual mass at least `n/(ln n)^6`, its joint activity is `2^{-Omega((log_2 n)^2)}`; below that cutoff, all remaining local and topological factors cost `exp(O(n/(ln n)^5))`. |
| Residual local increments | PASS | The joint factorial bound gives `Lambda=O(U^4/N_0)` and maximum weighted degree `tau=O(U^3/N_0)` without multiplying marginal cell probabilities. |
| Cycles disjoint from the high matching | PASS | Weighted-walk summation begins at length four and costs `O(n tau^4)`. |
| Cycles meeting arbitrarily many high cells | PASS | The high matching is a partial permutation of norm one; marking one high edge costs `O(h tau)`, with no hidden `2^h` or `h^r`. |
| Small residual degree | PASS | Pointwise, `beta<=|E(H_res)|<=N_0/2` and the local exponent is at most `(U-1)N_0/2`. |
| Full signed second moment | PASS | The canonical high-skeleton sum times the uniform residual supremum is `exp(o(n/(ln n)^4))`. |
| Paley--Zygmund seed | PASS | `P(Z>0)>=(E Z)^2/E Z^2=e^{-Lambda_n}`. |
| Rare-event amplification | PASS | The maximum coverable induced set is one-vertex Lipschitz; McDiarmid plus the simultaneous leftover-colouring lemma gives the asserted logarithmic gain. |
| Final constant | PASS | The midpoint leaves coefficient `q^2 gamma_4/16-o(1)`; taking half gives `c_*=q^2 gamma_4/32`. |
| Final quantifiers | PASS | Every estimate is phase-uniform and deterministic in `n`; the conclusion is all-`n` whp, not a density-one or subsequence statement. |
| Circularity | PASS | The first-moment construction precedes and supplies the only complete-moment input to the overlap estimates; no second-moment conclusion is used to construct the profile. |

## 2. Phase and unrestricted chromatic lower bound

Put `q=ln 2`, `N=ln n`, `alpha=floor(alpha_0)`, and
`delta=alpha_0-alpha`.  The exact ratio

\[
 \frac{\mu_{s+1}}{\mu_s}
 =\frac{n-s}{s+1}2^{-s}
\]

is `Theta(N/n)` at `s=alpha,alpha+1`, uniformly in the
phase.  Together with

\[
 \mu_\alpha=n^{\delta+O(\ln N/N)},
\]

this gives

\[
 \mu_{\alpha+2}=n^{\delta-2+o(1)}
 \le n^{-1+o(1)}=o(1).
\]

Thus the Markov exclusion of larger independent sets is valid even along
sequences with `delta` tending to either endpoint.

For an exact bounded profile `k_vec`, direct enumeration gives

\[
 \mathbb E X_{\mathbf k}
 =\frac{n!}{\prod_u (u!)^{k_u}k_u!}
   2^{-\sum_u k_u\binom u2}.
\]

Stirling's inequalities, with the zero-count convention, put its logarithm
below `L_kvec+O(N^2)`.  There are at most
`(n+1)^(alpha+1)=exp(O(N^2))` profiles.  Hence

\[
 \ln E_{n,k,\alpha+1}\le L_+(n,k)+O(N^2).
\]

I also re-expanded the finite Lagrange equations at the chromatic root.
For every support used in the proof, including the one-sided support after
its Gaussian tail is summed,

\[
 \frac nk=\alpha_0-1-\frac2q+o(1),\qquad
 \alpha-\frac nk=1+\frac2q-\delta+o(1),
\]

and the envelope derivative is

\[
 \frac{dL}{dk}=\frac2qN^2+O(N\ln N).
\]

These estimates are uniform over an `O(n/N^3)` window.  Moving down by
`ceil(N)` therefore decreases `L_+` by `Theta(N^3)`, which dominates the
profile-enumeration error.  On the simultaneous event that no independent
set exceeds `alpha+1`, any colouring with fewer than `k_chi^-` parts can be
refined to exactly `k_chi^-` nonempty independent parts.  This verifies the
unrestricted, rather than artificially bounded, lower threshold for `chi`.

## 3. Four-size signed first moment

For support `S`, the limiting constrained entropy is

\[
 \mathcal F_S(T)
 =\max\left[-\sum_i p_i\ln p_i-\frac q2\sum_i i^2p_i\right],
 \qquad \sum p_i=1,\quad\sum ip_i=T.
\]

The Lagrange solution is the stated discrete Gaussian.  For
`S_4={2,3,4,5}`, the tilt lies in `(2q,9q/2)` throughout
`T in [2/q,1+2/q]`.  Rechecking the four rational tail estimates gives

\[
 L(2q)<0.51,\quad H(3q)<0.02,\quad
 L(3q)<0.12,\quad H(9q/2)<0.25.
\]

Evaluating the one-sided dual function at the four-size tilt therefore
gives

\[
 0\le D_4<\ln(1.53),\qquad
 q-D_4>\gamma_4:=\ln(200/153).
\]

At the unrestricted root, the finite four-size signed logarithmic moment is
`k(q-D_4+o(1))`.  The signed derivative differs from the ordinary derivative
only by the lower-order constant `q`.  Hence

\[
 r_+-r_4^{co}
 =\left(\frac{q^2}{4}(q-D_4)+o(1)\right)\frac n{N^3}.
\]

The current construction uses the exact finite-`n` four-size maximizer at
the midpoint.  Its weights have the form
`d_{alpha-i}^{-1} exp(lambda_0+lambda_1 i)` and converge uniformly to the
four Gaussian proportions, so all four coordinates are bounded below by a
fixed positive constant.  Rounding and solving the two constraint errors
with

\[
 \Delta k_2=e_1-3e_0,\qquad
 \Delta k_3=2e_0-e_1
\]

changes only `O(1)` counts.  Because the correction is tangent to both
constraints, the exact finite first variation vanishes; Stirling contributes
only `O(N)`.  The midpoint distance from the signed root is a fixed
fraction of `n/N^3`, so the resulting exact profile has

\[
 \ln\mathbb E Z_{\mathbf k}^{sgn}\ge c_Z k
\]

for a single `c_Z>0` valid in every phase.

## 4. Exact signed overlap and normalization

Fix two labelled-slot partitions of the profile and let
`B=sum_slots binom(u,2)`.  If their overlap matrix is `r`, exactly
`W=sum_ab binom(r_ab,2)` edge variables are constrained by both
partitions.  On the graph `H` of cells of multiplicity at least two,
compatible sign pairs are constant on each component.  Thus the number of
compatible sign pairs is

\[
 2^{2k-v(H)+c(H)}.
\]

For each such pair the probability of all constraints is
`2^{-(2B-W)}`.  Dividing by the squared one-partition signed probability
`(2^k2^{-B})^2` gives

\[
 A_\zeta(r)=2^{W+c-v}
 =\left(\prod_{ab}g(r_{ab})\right)2^{\beta(H)}.
\]

This verifies that incompatible signs contribute zero and that the moment
is not obtained by an illicit factor `2^(2k)` times the ordinary moment.
The overlap matrix law

\[
 p(r)=\frac{\prod_a s_a!\prod_b t_b!}
            {n!\prod_{ab}r_{ab}!}
\]

then gives the normalized second moment exactly.  Passing between ordered
slots and unordered equal-size parts multiplies both `Z` and `E Z` by the
same deterministic factor, so the normalized formula and the partial
diagonal identities are consistent.

## 5. Canonical high cells and the residual factor

Let `U=alpha-2` and `R=floor(U/2)`.  Two cells above `R` cannot share a
row or column, so they form a canonical matching `M`.  If their exact
multiplicities sum to `J`, selecting their row stubs, column stubs, and
bijections gives

\[
 \pi(M,j)=
 \frac{\prod_i(s_{a_i})_{j_i}(t_{b_i})_{j_i}}
      {(n)_J\prod_i j_i!}.
\]

Conditional on these paired stubs, the residual matching is uniform on the
remaining degrees.  Multiplying its exact contingency-table probability by
`pi` cancels to the original `p(r)`.  The residual cap and no-backtracking
condition make the decomposition unique.

For residual total degree `N_0`, the threshold expansion gives

\[
 \lambda_{ab}\le C\left(\frac{d_ad'_b}{N_0}\right)^3,
 \qquad
 q_{ab}\le C\left(\frac{d_ad'_b}{N_0}\right)^2.
\]

Consequently

\[
 \sum\lambda_{ab}=O(U^4/N_0),\qquad
 \max_v\sum_{e\ni v}q_e=:\tau=O(U^3/N_0).
\]

The even-subgraph identity is summed before any independence relaxation.
Cycles disjoint from `M` cost `O(n tau^4)`.  For cycles meeting `M`, cut at
their matching edges.  The residual-walk kernel has row-sum norm at most
`tau`, while traversal of `M` is a partial permutation of norm one.  Marking
and orienting one matching edge therefore gives `O(h tau)`, not `2^h` or
`h^r`.  At `N_0>=n/N^6` the total logarithmic cost is `O(N^8)`.  When
`N_0<n/N^6`, the deterministic estimates

\[
 \beta(M\cup H_{res})\le |E(H_{res})|\le N_0/2,
 \qquad
 \sum_e\binom{r_e}{2}\le (U-1)N_0/2
\]

give `O(n/N^5)`.  Both are `o(n/N^4)` uniformly over every high skeleton.

## 6. Exact diagonal sum

For a common subprofile `ell`, direct cancellation gives

\[
 D(\ell)=\frac{\prod_i\binom{k_i}{\ell_i}^2}
                {Y_\ell^{sgn}},
\]

and the exact recurrence

\[
 \frac{D(\ell+e_i)}{D(\ell)}
 =\frac{(k_i-\ell_i)^2}
       {2(\ell_i+1)\mu_{u_i}(n-m)}.
\]

At the empty corner, the total initial activity is

\[
 \sum_i\frac{k_i^2}{2\mu_{u_i}(n)}
 =O(N^{-(2/q-1/2)})=o(1).
\]

The exact finite-population correction remains harmless until the selected
mass leaves the vanishing range, so the nonempty sum there is `o(1)`.

For central mass, writing the residual normalized counts as `z_i`,
`R=sum z_i`, and `I_r=sum i z_i`, I recover the leading rate

\[
 \Phi_T(z)=R\ln R+\frac q2(I_r-TR).
\]

The two support-endpoint inequalities are

\[
 \Phi_T\le R\{\ln R+q(5-T)/2\},
 \qquad
 \Phi_T\le R\ln R+q(T-2)(1-R)/2.
\]

They imply a phase-uniform strict negative rate away from `R=0,1`; no
greedy-prefix or numerical-grid premise is needed.  The lower-order entropy
term is too small to change the sign at the moving cutoff.

At the full corner, the complementary identity

\[
 D(k-h)=\left(\prod_i\binom{k_i}{h_i}\right)
          \frac{Z_h^{sgn}}{Z_k^{sgn}}
\]

is exact.  For sufficiently small residual vertex fraction,
`Z_h^sgn<=1`, while `Z_k^sgn>=e^{c_Zk}`.  Vandermonde's identity then sums
all near-full residual vectors exponentially.  These three ranges prove

\[
 \sum_rD(r)=1+o(1).
\]

## 7. Dense four-type transportation and decorations

For a typed full-containment matrix `L`, its bare weight is the exact
formula in (5.1) of the draft.  With row and column margins `r,c`, division
by `sqrt(D(r)D(c))` leaves a factorial transportation coefficient, local
ratios, and one global falling-factorial ratio.  Concavity of
`f(x)=ln(n)_x` gives in the required direction

\[
 \frac{\sqrt{(n)_{m_r}(n)_{m_c}}}{(n)_J}
 \le (n+1)^{\frac12\sum_{ij}|i-j|\ell_{ij}}.
\]

For a size difference `d`, the exact local ratio is

\[
 Q_{ij}=(n+1)^{d/2}\frac{\sqrt{(t)_d}}{d!}
        2^{-(ds+\binom d2)/2}
 \le\frac{\eta_n^d}{d!},
 \qquad
 \eta_n=O(N^{3/2}/\sqrt n).
\]

For fixed margins, Cauchy's inequality separates the row and column
multinomial coefficients.  Dropping the opposite constraints produces two
exact multinomial expansions.  Summing the margins once more gives

\[
 \sum_LW(L)
 \le \exp\{O(\eta_n k)+O(N)\}\sum_rD(r)
 =\exp\{O(\sqrt{nN})+O(N)\}.
\]

Thus imbalanced paths and off-diagonal type cycles have all been summed;
there is no pointwise diagonal-maximality assumption.

If a full containment of sizes `m,m+d` is lowered by `e`, the exact local
ratio is

\[
 \frac{\binom me}{(d+1)\cdots(d+e)}
 2^{-em+e(e+1)/2}.
\]

The global denominator is compared only once, by at most `n^e` per missing
stub.  The consecutive-ratio check makes the total near-containment
activity `O(N^3/n)` per high cell, hence `exp(O(N^2))` overall.

The updated mixed middle-strip proof also checks the regime that cannot be
imported merely from the equitable calculation.  After the near skeleton,
if residual mass `M_0>=n/N^6`, the joint prescribed-cell bound gives

\[
 \Xi_4(M_0)
 \le k^2\sum_{a/2<j\le3a/4+O(1)}
       g(j)\frac{(ea^2/M_0)^j}{j!}
 =2^{-\Omega((\log_2 n)^2)}.
\]

If `M_0<n/N^6`, summing the residual probability first and applying the
same pointwise local/cycle-rank inequalities costs `exp(O(n/N^5))`.
Therefore all actual high multiplicities, not only endpoint containments,
are covered.  The complete bare high-skeleton sum is

\[
 \exp\{O(\sqrt{nN})+O(N^2)+O(n/N^5)\}
 =\exp\{o(n/N^4)\}.
\]

Multiplying by the uniform residual-attachment supremum proves

\[
 \Lambda_n=ln\frac{\mathbb E Z^2}{(\mathbb E Z)^2}
 =o(n/N^4).
\]

## 8. Paley seed and rare-event amplification

Paley--Zygmund gives

\[
 \Pr\{\zeta(G_n)\le k_{co}\}
 \ge\Pr\{Z>0\}\ge e^{-\Lambda_n}.
\]

For completeness, I reconstructed the amplification rather than using its
statement.  Let

\[
 S_k=\max\{|W|:\zeta(G[W])\le k\}.
\]

Changing one vertex-exposure block changes `S_k` by at most one.  The seed
probability and the upper McDiarmid tail imply

\[
 n-\mathbb E S_k\le\sqrt{(n-1)\Lambda_n/2}.
\]

A lower tail with parameter `r` leaves, except with probability `e^{-r}`,
at most

\[
 O(\sqrt{n\Lambda_n}+\sqrt{nr})
\]

uncovered vertices.  Simultaneously every induced set can be ordinarily
coloured with `O(|U|/N+n^{1/3})` colours, so it is also cocolourable with
that many parts.

Set `B_n=n/N^4` and `r_n=sqrt(B_n)`.  Since
`Lambda_n=o(B_n)`, all three amplification errors satisfy

\[
 \frac{\sqrt{n\Lambda_n}}N=o(n/N^3),\qquad
 \frac{\sqrt{nr_n}}N=o(n/N^3),\qquad
 n^{1/3}=o(n/N^3).
\]

Hence `zeta<=k_co+o(n/N^3)` with high probability.

## 9. Constant, quantifiers, and dependency audit

The safe root separation is

\[
 r_+-r_4^{co}\ge\frac{q^2\gamma_4}{8}\frac n{N^3}.
\]

Taking the midpoint, and absorbing the `O(N)` chromatic-root shift and all
integer rounding, gives

\[
 k_\chi^- - k_{co}
 \ge\left(\frac{q^2\gamma_4}{16}-o(1)\right)\frac n{N^3}.
\]

The amplification error is `o(n/N^3)`.  Therefore half of the last leading
constant is available for every sufficiently large `n`:

\[
 \Pr\left\{\chi(G_n)-\zeta(G_n)
 \ge \frac{q^2}{32}\ln\frac{200}{153}
       \frac n{(\ln n)^3}\right\}\longrightarrow1.
\]

No independence between the final lower and upper events is used; a union
bound suffices.

The dependency graph is acyclic:

1. the phase expansion and exact first-moment variational problem construct
   the midpoint profile and establish its signed complete-moment margin;
2. that margin, the exact profile, and elementary independence-set counts
   prove the diagonal endpoint estimate;
3. the diagonal estimate feeds the dense transportation sum;
4. the exact signed overlap identity and configuration model prove the
   profile-independent residual-attachment estimate;
5. the dense and residual estimates combine only after both have been
   proved, yielding the second moment;
6. Paley--Zygmund and the independently proved amplification theorem are
   applied last.

In particular, the proof never invokes the published ordinary tame-profile
second moment at the signed midpoint, where its ordinary first-moment
hypothesis would fail.

## 10. Explicit verdict

**PASS.**  Under the current exact finite-optimizer formulation and the
updated mixed middle-strip split, every stated hypothesis is supplied by the
midpoint four-size profile, every overlap matrix appears in exactly one
canonical regime, and the logarithm of the normalized signed second moment
is within the `o(n/(ln n)^4)` amplification budget.  I found no substantive
gap and no false remaining lemma.  The final all-`n` high-probability lower
bound and the constant in (0.1) follow.
