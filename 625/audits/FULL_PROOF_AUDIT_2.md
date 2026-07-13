# Second independent full-chain audit of `COMPLETE_PROOF_DRAFT.md`

> **Historical-scope notice (2026-07-13).** This document preserves the
> internal 2026-07-12 verdict on the draft and component bytes then under
> review. It is not a review of the later repaired or synchronized bytes.
> The authoritative proof is now `../proofs/COMPLETE_PROOF_SELF_CONTAINED.md`;
> see `ADVERSARIAL_LEAP_AUDIT_2026-07-13.md` for the later defects and
> regression checks, and `PROOF_COMPONENT_SYNCHRONIZATION_AUDIT_2026-07-13.md`
> for the mapping from that canonical proof to the synchronized component
> notes. The original audit body and verdict below are retained unchanged.

**Audit date:** 2026-07-12  
**Verdict:** **PASS**, for the current post-repair draft, as an internally
complete proof of the stated all-`n` theorem.  I found no remaining reversed
inequality, missing factorial, uncovered overlap regime, logarithm-base error,
or probability-quantifier gap.

This is an internal reconstruction, not external peer review.  The verdict is
for the theorem and dependency files as they stand after the corrections
listed in Section 8 below.  Earlier snapshots of the main draft did not pass
literally because they misstated the uniform order of `mu_{alpha+2}` and
omitted the small-residual middle-strip term from (5.10).  Both statements are
correct in the audited version.

## 1. Audit method and verdict by obligation

I did not use another full-chain audit as a premise.  I reconstructed the
argument in the following order, deliberately different from the order in the
candidate proof:

1. exact finite-`n` signed witness and overlap law;
2. exact common-diagonal contribution and its three mass regimes;
3. the unequal-margin transportation comparison, retaining the global
   `(n)_J` denominator;
4. the canonical high-cell/residual decomposition;
5. the four-size first-moment displacement and the unrestricted chromatic
   lower bound;
6. Paley--Zygmund, rare-event amplification, and the final constant.

The resulting obligation table is:

| Proof obligation | Verdict | Reason |
|---|---:|---|
| Ordinary and signed profile first moments | PASS | Recovered directly from unordered partition counting; the signed bonus is exactly `2^k` because every class has size at least two. |
| Exact normalized signed overlap factor | PASS | `A_zeta(r)=2^{W+c-v}=prod g(r_ab) 2^{beta(H)}` follows by counting compatible sign assignments componentwise. |
| Canonical high-cell exposure | PASS | Cells above `floor(U/2)` form a matching, and the exposed incidence has the single global denominator `(n)_J`. |
| Exact diagonal common weight | PASS | `D(r)=prod binom(k_i,r_i)^2/Y_r^sgn` and both endpoint recurrences have the stated factorial orientation. |
| Common-diagonal central rate | PASS | Independent Stirling expansion gives exactly `Phi_T(z)=R ln R+(q/2)(I_r-TR)` with the sign used in the draft; the two analytic endpoint bounds make it strictly negative off the two corners. |
| Geometric-mean `(n)_J` comparison | PASS | Concavity of `ln(n)_x` gives the displayed inequality in the required direction; the local ratio and every `d!` were rederived. |
| Sum over unequal margins | PASS | Cauchy followed by two multinomial expansions gives `exp(O(sqrt(n ln n))) sum_r D(r)`. |
| Near-containment and middle strip | PASS | The exact deficiency ratio is correct.  The large-residual and small-residual middle branches together cost `o(n/(ln n)^4)`. |
| Residual local factors and cycle space | PASS | The canonical attachment theorem is uniform over the mixed four-size skeletons and introduces no `2^h` or `h^r` loss. |
| Four-size first-moment displacement | PASS | Natural-log bookkeeping gives coefficient `q^2(q-D_4)/4`; finite-`n` optimization and tangent rounding preserve the uniform margin. |
| Unrestricted chromatic lower bound | PASS | Markov excludes classes of size `alpha+2`, and the total bounded-colouring first moment is `o(1)` at `k_chi^-`. |
| Rare-event amplification | PASS | `Lambda=o(n/(ln n)^4)` produces only `o(n/(ln n)^3)` additional classes with failure probability `o(1)`. |
| All-`n` and whp quantifiers | PASS | Every phase estimate is uniform on the closed phase interval; the final intersection uses only a union bound. |
| Explicit constant | PASS | The final safe constant is `q^2 ln(200/153)/32=0.004021983962242005...`. |

## 2. Exact finite-`n` counting reconstruction

Fix class sizes `u_1,...,u_k`, all at least two, with sum `n`.  The number of
unordered partitions with size multiplicities `k_u` is

\[
 \frac{n!}{\prod_u (u!)^{k_u} k_u!}.
\]

The internal edge requirements of distinct classes use disjoint edge
coordinates.  Consequently the ordinary and signed first moments are exactly

\[
 Z_{\mathbf k}^{ord}
 =\frac{n!}{\prod_u (u!)^{k_u}k_u!}
    2^{-\sum_u k_u\binom u2},
 \qquad
 Z_{\mathbf k}^{sgn}=2^k Z_{\mathbf k}^{ord}.             \tag{2.1}
\]

The factor `2^k` is exact here.  For a set of size at least two, the events
"independent" and "clique" are disjoint, so there is no singleton certificate
multiplicity.

For two uniformly chosen ordered partitions of the same slot profile, let
`r_ab` be the overlap matrix.  Its exact configuration-model law is

\[
 p(r)=\frac{\prod_a u_a!\prod_b u_b!}
            {n!\prod_{a,b}r_{ab}!}.                       \tag{2.2}
\]

Put `w_ab=binom(r_ab,2)` and let `H` be the bipartite support of cells with
`r_ab>=2`.  If `W=sum w_ab`, and `v,c` are the numbers of nonisolated vertices
and components of `H`, compatibility forces the two signs to agree across
every support edge.  Exactly `2^c` assignments on the `v` nonisolated slots
are compatible.  Division by the `2^{2k}` sign average therefore gives

\[
 A_\zeta(r)=2^{W+c-v}.                                    \tag{2.3}
\]

Writing

\[
 g(0)=g(1)=g(2)=1,
 \qquad g(x)=2^{\binom x2-1}\quad(x\ge3),
\]

and `beta(H)=|E(H)|-|V(H)|+c(H)`, (2.3) is equivalently

\[
 A_\zeta(r)=\left(\prod_{a,b}g(r_{ab})\right)2^{\beta(H)}.
                                                                    \tag{2.4}
\]

Thus the normalized second moment is exactly

\[
 \frac{\mathbb E(Z_{\mathbf k}^{sgn})^2}
      {(\mathbb E Z_{\mathbf k}^{sgn})^2}
 =\sum_r p(r)A_\zeta(r).                                 \tag{2.5}
\]

No ordinary-colouring moment is substituted in (2.5), and incompatible sign
pairs contribute zero rather than an extra factor.

## 3. Common diagonals and the central rate

Use the original deficit indexing `u_i=alpha-i`,
`i in {2,3,4,5}` (so the largest size is `a=alpha-2`), and let `k_i` be
their exact integer counts.  For a common subprofile `r=(r_i)`, put
`m_r=sum_i u_i r_i`.  Directly
from (2.1)--(2.5), its exact normalized contribution is

\[
 D(r)=
 \frac{\prod_i(k_i)_{r_i}^2}{\prod_i r_i!}
 \frac{\prod_i [u_i!g(u_i)]^{r_i}}{(n)_{m_r}}
 =\frac{\prod_i\binom{k_i}{r_i}^2}{Y_r^{sgn}}.           \tag{3.1}
\]

This formula checks the potentially confusing factorial orientation:
there is one `r_i!` in the denominator of the first expression, not two and
not zero.  Adding one selected common block gives

\[
 \frac{D(r+e_i)}{D(r)}
 =\frac{(k_i-r_i)^2}
        {2(r_i+1)\mu_{u_i}(n-m_r)}.                       \tag{3.2}
\]

At the opposite endpoint, with `h=k-r`, `M=n-m_r`, exact cancellation gives

\[
 D(k-h)=\left\{\prod_i\binom{k_i}{h_i}\right\}
          \frac{Z_h^{sgn}(M)}{Z_k^{sgn}(n)}.              \tag{3.3}
\]

### 3.1 Independent derivation of the central sign

Write `K=sum k_i`, `p_i=k_i/K`, `y_i=r_i/K`, and let the residual normalized
profile be `z_i=p_i-y_i`.  Set

\[
 Y=\sum_i y_i,\quad R=\sum_i z_i=1-Y,
 \quad I=\sum_i i y_i,\quad I_r=\sum_i i z_i=T-I.
\]

Expanding (3.1), while retaining the global falling factorial until after
Stirling is applied, gives

\[
 \ln D(r)=n\rho\ln\rho
 +K\sum_i\{2p_i\ln p_i-2z_i\ln z_i-y_i\ln y_i-y_i+y_iD_i\}
 +O(\ln n),                                               \tag{3.4}
\]

where

\[
 \rho=\frac{n-m_r}{n},\qquad
 D_i=\ln K+\ln(u_i!)+u_i-u_i\ln n+q\binom{u_i}{2}-q.
                                                                    \tag{3.5}
\]

For consecutive deficits,

\[
 D_{i+1}-D_i
 =\ln n-\ln(\alpha-i)-q(\alpha-i)+q-1
 =-\frac{q\alpha}{2}+O(1).                               \tag{3.6}
\]

If `bar D=sum p_iD_i`, the complete signed-moment identity gives

\[
 -K^{-1}\ln Z_k^{sgn}=\sum_i p_i\ln p_i-1+\bar D+o(1).
                                                                    \tag{3.7}
\]

The midpoint profile has `Z_k^{sgn}>=exp(cK)`, so (3.7) bounds `bar D`
above by an absolute constant.  From (3.6),

\[
 D_i=\bar D+\frac{q\alpha}{2}(T-i)+O(1).                 \tag{3.8}
\]

Also

\[
 \rho=R+\frac{I-TY}{\alpha-T},
 \qquad n=K(\alpha-T).
\]

When the residual mass is bounded away from zero, substitution in (3.4)
therefore yields

\[
 \ln D(r)
 \le K\alpha\Phi_T(z)+O\!\left(KY\ln\frac eY+\ln n\right),
                                                                    \tag{3.9}
\]

with

\[
 \boxed{\Phi_T(z)=R\ln R+\frac q2(I_r-TR).}             \tag{3.10}
\]

This verifies the sign in the main proof.  In particular, the signed bonus
does not change (3.10) to `R ln R-(q/2)(I_r-TR)`.

For `2/q<=T<=1+2/q` and support `{2,3,4,5}`,

\[
 I_r-TR\le(5-T)R,
 \qquad I_r-TR=\sum_i(T-i)y_i\le(T-2)(1-R).              \tag{3.11}
\]

Hence

\[
 \Phi_T\le R\{\ln R+q(5-T)/2\},
 \qquad
 \Phi_T\le R\ln R+q(T-2)(1-R)/2.                       \tag{3.12}
\]

The first bound is uniformly negative for `1/64<=R<=0.47`; convexity of the
second gives a uniform negative multiple of `1-R` for `R>=0.47`.  Direct
evaluation gives zero at `R=0`, so the only zeros on the full domain are the
empty and full residual corners.  The finite-`n` phase shift is `o(1)` and is
absorbed by the fixed slack in these inequalities.

### 3.2 Endpoint coverage

At the empty selected corner, put

\[
 \lambda_i=\frac{k_i^2}{2\mu_{u_i}},\qquad
 \Lambda=\sum_i\lambda_i.
\]

The uniform phase estimate for `u_2=alpha-2` gives

\[
 \Lambda=O((\ln n)^{-(2/q-1/2)})=o(1).                  \tag{3.13}
\]

The exact denominator bound

\[
 D(r)\le\frac{n^{m_r}}{(n)_{m_r}}
          \prod_i\frac{\lambda_i^{r_i}}{r_i!}           \tag{3.14}
\]

and a split at `sum r_i=n/a^3` show that all nonzero subprofiles of
sufficiently small fixed vertex mass sum to `o(1)`.  For fixed positive
selected and residual mass, (3.9)--(3.12) give `exp(-Omega(n))` per vector.
At the near-full corner, (3.3), the bound `Z_h^{sgn}(M)<=1` for small `M`,
and `Z_k^{sgn}(n)>=exp(cK)` give `exp(-Omega(K))` after summing the residual
vectors.  Therefore

\[
 \boxed{\sum_rD(r)=1+o(1).}                              \tag{3.15}
\]

All three regions use exact recurrences at the singular corners; no
finite-population approximation is made there.

## 4. Geometric-mean audit of the global falling factorial

For a typed full-containment matrix `L=(ell_ij)`, let its row and column
margins be `r,c`, put `x_ij=min(u_i,u_j)`, and
`J=sum x_ij ell_ij`.  Direct slot matching gives

\[
 W(L)=
 \frac{\prod_i(k_i)_{r_i}\prod_j(k_j)_{c_j}}
      {\prod_{ij}\ell_{ij}!}\frac1{(n)_J}
 \prod_{ij}B_{ij}^{\ell_{ij}},                           \tag{4.1}
\]

where

\[
 B_{ij}=\frac{(u_i)_{x_{ij}}(u_j)_{x_{ij}}}{x_{ij}!}g(x_{ij}).
\]

Dividing (4.1) by `sqrt(D(r)D(c))` gives the exact ratio

\[
 \frac{W(L)}{\sqrt{D(r)D(c)}}
 =\frac{\sqrt{\prod_i r_i!c_i!}}{\prod_{ij}\ell_{ij}!}
   \frac{\sqrt{(n)_{m_r}(n)_{m_c}}}{(n)_J}
   \prod_{ij}\left(\frac{B_{ij}}{\sqrt{b_ib_j}}\right)^{\ell_{ij}},
                                                                    \tag{4.2}
\]

with `b_i=u_i!g(u_i)`.  This identity is the main factorial checkpoint.

Let `f(x)=ln(n)_x`.  Since

\[
 f''(x)=-\psi'(n-x+1)<0,
\]

`f` is concave.  Moreover,

\[
 \frac{m_r+m_c}{2}
 =J+\frac12\sum_{ij}|i-j|\ell_{ij}.                      \tag{4.3}
\]

Consequently

\[
 \frac{f(m_r)+f(m_c)}2\le f\!\left(\frac{m_r+m_c}{2}\right),
\]

and `f'(x)<=ln(n+1)` gives

\[
 \frac{\sqrt{(n)_{m_r}(n)_{m_c}}}{(n)_J}
 \le(n+1)^{\frac12\sum_{ij}|i-j|\ell_{ij}}.             \tag{4.4}
\]

The direction is therefore exactly the one used in the draft.  Reversing
concavity would destroy the proof; no such reversal occurs.

If the two endpoint sizes are `t=s+d`, then

\[
 B_{ij}=b_s\binom td,
 \qquad \frac{b_t}{b_s}=(t)_d2^{ds+\binom d2},
\]

so the remaining local factor is

\[
 Q_{ij}=(n+1)^{d/2}\frac{\sqrt{(t)_d}}{d!}
          2^{-\{ds+\binom d2\}/2}.                       \tag{4.5}
\]

Thus `Q_ii=1`, and, uniformly for `1<=d<=3`,

\[
 Q_{ij}\le\frac1{d!}
 \left(C\frac{(\ln n)^{3/2}}{\sqrt n}\right)^d.         \tag{4.6}
\]

This checks both the `d!` orientation and the power of `n`.  For fixed
margins, Cauchy's inequality turns the transportation factorial into the
geometric mean of a row multinomial and a column multinomial.  Dropping the
opposite constraints gives exact multinomial sums.  Hence

\[
 \sum_{L:\,row(L)=r,\,col(L)=c}W(L)
 \le\sqrt{D(r)D(c)}\exp\{C\eta_nK\},
 \quad \eta_n=O((\ln n)^{3/2}/\sqrt n).                  \tag{4.7}
\]

Finally,

\[
 \left(\sum_r\sqrt{D(r)}\right)^2
 \le\prod_i(k_i+1)\sum_rD(r),                           \tag{4.8}
\]

so (3.15) implies

\[
 \sum_LW(L)
 \le\exp\{O(\sqrt{n\ln n})+O(\ln n)\}.                \tag{4.9}
\]

As a diagnostic separate from the proof, I evaluated (4.2)--(4.6) on 2,500
random feasible finite matrices with `7<=a<=11` and small four-type margin
vectors.  No violation occurred.  The algebra above, not this numerical
check, is the proof.

## 5. Decorations, middle cells, and residual topology

If a full containment between sizes `m` and `m+d` is reduced from `m` to
`m-e`, its exact local ratio is

\[
 R_{m,d}(e)=
 \frac{\binom me}{(d+1)\cdots(d+e)}
 2^{-em+e(e+1)/2}.                                       \tag{5.1}
\]

If the total deficiency is `Q`, the global denominator ratio is

\[
 \frac{(n)_{J_0}}{(n)_{J_0-Q}}
 =(n-J_0+Q)_Q\le n^Q,                                   \tag{5.2}
\]

which confirms its orientation.  Summing `n^eR_{m,d}(e)` for `e<m/4`
costs `O((ln n)^3/n)` per endpoint cell, hence only `exp(O((ln n)^2))`
over all cells.

The remaining canonical high cells lie in the middle range
`a/2<j<=3a/4+O(1)`.  Conditional on residual mass `M_0>=n/(ln n)^6`, the
single global factorial bound gives total activity

\[
 \Xi_4(M_0)=K^2\sum_jg(j)\frac{(ea^2/M_0)^j}{j!}
 =2^{-\Omega((\log_2 n)^2)}.                              \tag{5.3}
\]

For `M_0<n/(ln n)^6`, the deterministic local-plus-cycle bound is instead

\[
 \exp\{O(aM_0)\}=\exp\{O(n/(\ln n)^5)\}.                \tag{5.4}
\]

The distinction between (5.3) and (5.4) is necessary; the current main
draft states it correctly.

After every cell above `floor(a/2)` is exposed, the remaining configuration
model is exact and capped.  The residual attachment theorem sums all
double/triple local factors and the complete even-subgraph factor uniformly.
Its logarithmic cost is `O((ln n)^8)` in the large-residual branch and
`O(n/(ln n)^5)` in the small-residual branch.  In particular it retains
cycles containing arbitrarily many high matching edges and introduces no
factor `2^h`.

Combining (4.9), (5.1)--(5.4), and the uniform residual bound gives

\[
 \Lambda_n:=\ln\frac{\mathbb E(Z_{\mathbf k}^{sgn})^2}
                         {(\mathbb EZ_{\mathbf k}^{sgn})^2}
 =o\!\left(\frac n{(\ln n)^4}\right).                   \tag{5.5}
\]

The scale comparisons used here are

\[
 \sqrt{n\ln n},\ (\ln n)^8,\ \frac n{(\ln n)^5}
 =o\!\left(\frac n{(\ln n)^4}\right).                  \tag{5.6}
\]

This exhausts the overlap matrix: high cells are canonical, near and middle
high cells are disjoint cases, and everything else belongs to the capped
residual model.

## 6. First-moment displacement and the chromatic lower bound

Now return to the threshold calculation.  Put `N=ln n`, `q=ln2`, and use
the phase `delta={alpha_0}`.  For the unrestricted support `S_+` and the
four-size support `S_4`, let

\[
 D_4(\delta)=\mathcal F_{S_+}(T(\delta))
              -\mathcal F_{S_4}(T(\delta)),
 \quad T(\delta)=1+2/q-\delta.
\]

The analytic tail certificate gives, uniformly on the closed phase
interval,

\[
 0\le D_4(\delta)<\ln(153/100),
 \qquad q-D_4(\delta)>\gamma_4:=\ln(200/153).             \tag{6.1}
\]

At the unrestricted root `r_+`, the signed four-size log first moment is

\[
 r_+\{q-D_4(\delta)+o(1)\}.                              \tag{6.2}
\]

The derivative in natural logarithms is

\[
 \frac{\partial L}{\partial k}
 =\frac2qN^2+O(N\ln N),
 \qquad
 r_+=\left(\frac q2+o(1)\right)\frac nN.                \tag{6.3}
\]

The signed root is lower, not higher, because (6.2) is positive and the
derivative is positive.  The mean-value theorem gives

\[
 r_+-r_4^{co}
 =\left(\frac{q^2}{4}\{q-D_4(\delta)\}+o(1)\right)
   \frac n{N^3}.                                         \tag{6.4}
\]

This independently checks the factor `q^2/4` and the use of natural logs.
The exact finite-`n` optimizer on the four sizes converges uniformly to the
limiting Gaussian.  Its four masses remain bounded below; tangent integer
rounding changes the log moment by only `O(N)`.  At the midpoint integer
`k_co`, therefore,

\[
 \ln\mathbb EZ_{\mathbf k}^{sgn}=\Omega(n/N)=\Omega(K),
                                                                    \tag{6.5}
\]

which is precisely the complete-moment hypothesis used in Section 3.

For the unrestricted lower bound, the exact phase expansion is

\[
 \mu_{\alpha+2}=n^{\delta-2+o(1)}
 \le n^{-1+o(1)}=o(1),                                  \tag{6.6}
\]

not uniformly an equality `n^{-1+o(1)}`.  Markov therefore excludes
independent sets of size `alpha+2`.  At

\[
 k_\chi^-=\lfloor r_+\rfloor-\lceil N\rceil,
\]

the derivative loss is `Theta(N^3)`, whereas the sum over all bounded
integer profiles and all Stirling errors costs only `O(N^2)` in the
logarithm.  Hence

\[
 \Pr\{\chi(G_n)\le k_\chi^-\}=o(1).                     \tag{6.7}
\]

Any colouring with fewer parts can be refined to exactly `k_chi^-` parts,
so this is an unrestricted chromatic statement, not merely a bounded-profile
one.

Using the deliberately safe halves in the draft, (6.1)--(6.4), the midpoint,
and integer shifts give

\[
 k_\chi^- - k_{co}
 \ge\left(\frac{q^2\gamma_4}{16}-o(1)\right)\frac n{N^3}.
                                                                    \tag{6.8}
\]

The `O(N)` chromatic shift and `O(1)` rounding shifts are uniformly
`o(n/N^3)`.

## 7. Probability transfer, error scales, and final constant

Paley--Zygmund applied to the nonnegative signed witness and (5.5) gives

\[
 \Pr\{\zeta(G_n)\le k_{co}\}
 \ge\Pr\{Z_{\mathbf k}^{sgn}>0\}\ge e^{-\Lambda_n}.     \tag{7.1}
\]

Set

\[
 B_n=\frac n{N^4},\qquad r_n=\sqrt{B_n}.
\]

The rare-event Alon--Scott theorem then yields, outside probability
`e^{-r_n}+o(1)`,

\[
 \zeta(G_n)\le k_{co}
 +O\!\left(\frac{\sqrt{n\Lambda_n}+\sqrt{nr_n}}N+n^{1/3}\right).
                                                                    \tag{7.2}
\]

Each error is `o(n/N^3)`:

\[
 \frac{\sqrt{n\Lambda_n}}N=o(n/N^3),\qquad
 \frac{\sqrt{nr_n}}N=\frac{n^{3/4}}{N^2}=o(n/N^3),
 \qquad n^{1/3}=o(n/N^3).                               \tag{7.3}
\]

Also `r_n->infinity`, so the failure probability tends to zero.  Intersecting
(6.7) and (7.2) uses a union bound only; no independence is needed.  Equations
(6.8)--(7.3) give

\[
 \chi(G_n)-\zeta(G_n)
 \ge\left(\frac{q^2\gamma_4}{16}-o(1)\right)\frac n{N^3}
\]

with high probability.  One final safe halving gives the displayed theorem
constant

\[
 \boxed{c_*=\frac{q^2}{32}\ln\frac{200}{153}
 =0.004021983962242005\ldots>0.}                         \tag{7.4}
\]

Since `n/(ln n)^3->infinity`, the fixed-`M` convergence follows immediately.

## 8. Corrections encountered and final scope

Three points were explicitly checked against finite-`n` phase and error
scales:

1. **`mu_{alpha+2}` phase exponent.**  An earlier draft wrote a uniform
   equality `n^{-1+o(1)}`.  The correct statement is (6.6).  The current main
   draft and component note use the correct form.
2. **Small-residual middle strip.**  An earlier (5.10) listed only
   `O(sqrt(n ln n))+O((ln n)^2)`.  The branch `M_0<n/(ln n)^6` safely costs
   `O(n/(ln n)^5)` in the logarithm.  The current draft includes it and
   qualifies the exponentially small middle-strip statement.
3. **Finite-`n` profile rounding.**  The current proof starts from the exact
   finite-`n` constrained four-size optimizer, then performs a tangent
   correction.  This justifies the claimed `O(ln n)` loss uniformly even at
   both phase endpoints.

With those repairs incorporated, the proof covers every sufficiently large
integer `n`; it does not discard jump-near phases, use a density-one set, or
turn numerical evidence into a proof.  The finite random check mentioned in
Section 4 was used only as a sign/factorial diagnostic.  The formal verdict is
therefore **PASS**.
