# Erdős Problem 625: proposed complete proof

**Synchronized internal-audit status (2026-07-13).**  This concise draft is
now synchronized with the repaired canonical manuscript
`COMPLETE_PROOF_SELF_CONTAINED.md` and the independent regression record
`../audits/ADVERSARIAL_LEAP_AUDIT_2026-07-13.md`.  In particular, it includes
the uniform root corridor, the raw/effective multiplier and signed-rounding
conventions, the conditioned global high-skeleton sum, the one-sided residual
attachment bound, and the deterministic amplification error sequence.  The
four 2026-07-12 full-chain reconstructions retain their historical PASS
verdicts for the earlier bytes; they are not represented as audits of this
later synchronized text.  The 2026-07-13 adversarial audit regression-checks
the repaired canonical passages, and
`../audits/PROOF_COMPONENT_SYNCHRONIZATION_AUDIT_2026-07-13.md` records their
propagation to the component notes.  This remains a candidate resolution, not
a claim of external peer review, publication, priority, or acceptance by the
mathematical community.

## Theorem

Let `G_n~G(n,1/2)`.  Put

\[
 q=\ln2,\qquad
 c_*:=\frac{q^2}{32}\ln\frac{200}{153}>0.
\]

Then

\[
 \boxed{
 \Pr\left\{\chi(G_n)-\zeta(G_n)
       \ge c_*\frac{n}{(\ln n)^3}\right\}\longrightarrow1.}
                                                                  \tag{0.1}
\]

In particular, for every fixed `M`,

\[
 \Pr\{\chi(G_n)-\zeta(G_n)\ge M\}\longrightarrow1,              \tag{0.2}
\]

which is the positive resolution of Problem 625 with the required all-`n`
convergence-in-probability quantifier.

## 1. Phase notation and the unrestricted chromatic lower location

Let

\[
 \alpha_0=2\log_2n-2\log_2\log_2n
            +2\log_2(e/2)+1,\qquad
 \alpha=\lfloor\alpha_0\rfloor,\qquad
 \delta=\alpha_0-\alpha.                                  \tag{1.1}
\]

Write `N=ln n` and `w=ln N`.

The expansion in `EXCEPTIONAL_REGIME.md` and the exact adjacent-size ratio
give, uniformly for `0<=delta<1`,

\[
 \mu_\alpha=\binom n\alpha2^{-\binom\alpha2}
 =n^{\delta+O(\ln\ln n/\ln n)},\qquad
 \mu_{\alpha+2}=n^{\delta-2+o(1)}
 \le n^{-1+o(1)}=o(1).                                    \tag{1.2}
\]

Thus Markov's inequality gives

\[
 \Pr\{\alpha(G_n)>\alpha+1\}=o(1).                       \tag{1.3}
\]

Write a class size as `u=alpha-i`.  Let `S_+={-1,0,1,...}`;
at finite `n` it is cut off where `u>=1`.  For a real class count `k`, let
`L_+(n,k)` be the continuous maximum of

\[
 L_{\mathbf k}=n\ln n-n+k-
   \sum_u k_u\ln\!\left(k_u\,2^{\binom u2}u!\right)       \tag{1.4}
\]

over profiles with `sum k_u=k`, `sum u k_u=n`, and deficits in `S_+`.
Write `d_u=2^{binom(u,2)}u!`.
The same notation `L_S(n,k)` is used for the four-size support
`S_4={2,3,4,5}`.  Put

\[
 s_0=\alpha_0-1-\frac2q.
\]

The uniform root-corridor statement needed below is the following.  For
`S in {S_+,S_4}` and every `0<=c<=q`, the equation
`L_S(n,k)+ck=0` has a unique zero `r_{S,c}` in a fixed corridor, and

\[
 \frac n{r_{S,c}}=s_0+O(w/N).                             \tag{1.5a}
\]

Moreover, for every fixed `A>0`, uniformly for `0<=c<=q` and every `k`
with `|n/k-s_0|<=Aw/N`,

\[
 \frac{\partial}{\partial k}\{L_S(n,k)+ck\}
 =\frac2qN^2+O_A(Nw).                                    \tag{1.5b}
\]

For completeness, if `s=n/k` and
`Psi_{S,c}(s)=(L_S(n,n/s)+c n/s)/(n/s)`, the exact affine-plus-curved
decomposition and scalar expansion in canonical equations (3.11)--(3.19) give
`Psi_{S,c}(s_0)=O(w)` and `Psi'_{S,c}(s)=-N+O_A(w)` throughout that corridor.
The two endpoints `s_0-Aw/N` and `s_0+Aw/N` therefore bracket zero for a sufficiently
large fixed `A`, strict monotonicity gives (1.5a), and

\[
 \frac d{dk}\{L_S+ck\}=\Psi_{S,c}(s)-s\Psi'_{S,c}(s)
\]

gives (1.5b) throughout the corridor.  Thus root localization is established
before any mean-value argument.  Set `r_+=r_{S_+,0}`.

There are at most `exp(O((ln n)^2))` integer bounded profiles, and uniform
Stirling bounds give

\[
 \ln E_{n,k,\alpha+1}\le L_+(n,k)+O((\ln n)^2),           \tag{1.6}
\]

where `E` is the expected total number of unordered `(alpha+1)`-bounded
`k`-colourings.  Hence, for

\[
 k_\chi^-:=\lfloor r_+(n)\rfloor-\lceil\ln n\rceil,       \tag{1.7}
\]

(1.5b)--(1.6) give `E_{n,k_chi^-,alpha+1}=o(1)`.  On the event
in (1.3), any colouring can be refined to exactly `k_chi^-` nonempty
independent parts without exceeding size `alpha+1`.  Consequently

\[
 \Pr\{\chi(G_n)\le k_\chi^-\}=o(1).                      \tag{1.8}
\]

All estimates above hold for every sufficiently large integer `n`; no
subsequence or fixed-distance-from-a-jump hypothesis has been used.

## 2. A four-size signed profile below the chromatic location

Set

\[
 S_4=\{2,3,4,5\},\qquad
 T(\delta)=1+\frac2q-\delta.                              \tag{2.1}
\]

For any support `S`, define

\[
 \mathcal F_S(T)=\max_{\substack{\sum p_i=1\\\sum ip_i=T}}
 \left[-\sum p_i\ln p_i-\frac q2\sum i^2p_i\right].     \tag{2.2}
\]

The optimizer is the finite or one-sided discrete Gaussian

\[
 p_i=\frac{e^{\mu i-qi^2/2}}
           {\sum_{j\in S}e^{\mu j-qj^2/2}}.              \tag{2.3}
\]

`ALPHA_MINUS_TWO_ROUTE.md`, Proposition 3.1, proves by explicit rational
tail estimates, uniformly for the whole interval in (2.1),

\[
 0\le
 D_4(\delta):=\mathcal F_{S_+}(T(\delta))
               -\mathcal F_{S_4}(T(\delta))
 <\ln\frac{153}{100}.                                     \tag{2.4}
\]

Therefore

\[
 q-D_4(\delta)>\gamma_4:=\ln\frac{200}{153}.              \tag{2.5}
\]

The finite-`n` profile functional converges uniformly to (2.2); the linear
terms cancel between supports.  Let `r_4^{co}=r_{S_4,q}`, the already-localized
real zero of the four-size **signed** first moment.  At `k=r_+`, the exact
support comparison and (2.4) give

\[
 L_{S_4}(n,r_+)+qr_+=r_+\{q-D_4(\delta)+o(1)\}.          \tag{2.5a}
\]

By (1.5a), both `r_+` and `r_4^{co}` lie in the same fixed corridor, so the
entire segment between them lies where (1.5b) is valid.  Only now applying
the mean-value theorem, together with
`r_+=(q/2+o(1))n/N`, gives

\[
 r_+-r_4^{co}
 =\left(\frac{q^2}{4}\{q-D_4(\delta)\}+o(1)\right)
    \frac{n}{(\ln n)^3}.                                  \tag{2.6}
\]

In particular, for every sufficiently large `n`,

\[
 r_+-r_4^{co}\ge
 \frac{q^2\gamma_4}{8}\frac{n}{(\ln n)^3}.               \tag{2.7}
\]

Use the midpoint integer

\[
 k_{co}:=\left\lceil\frac{r_4^{co}+r_+}{2}\right\rceil.  \tag{2.8}
\]

Let `p_i^{(n)}` be the exact finite-`n` maximizer of the four-size
functional `L_{S_4}(n,k_co)`.  In the exact decomposition
`-ln d_{alpha-i}=A_n+B_ni+h_n(i)`, distinguish the raw Lagrange multiplier
from the effective tilt:

\[
 p_i^{(n)}\ \propto\ d_{\alpha-i}^{-1}
       e^{\lambda_n^{\rm raw}i}
 \ \propto\ e^{\widehat\lambda_ni+h_n(i)},\qquad
 \widehat\lambda_n=B_n+\lambda_n^{\rm raw}.              \tag{2.8a}
\]

Uniform convergence makes `widehat lambda_n` converge to the bounded tilt
in (2.3), and all four exact proportions are uniformly bounded below.  Round
`k_co p_i^{(n)}` to preliminary integers `tilde k_i` and define the **signed**
constraint errors

\[
 e_0=\sum_i\widetilde k_i-k_{co},\qquad
 e_1=\sum_i i\widetilde k_i-(\alpha k_{co}-n).            \tag{2.8b}
\]

They are `O(1)`.  Correct the deficit-2 and deficit-3 coordinates by

\[
 \Delta k_2=e_1-3e_0,\qquad \Delta k_3=2e_0-e_1.          \tag{2.8c}
\]

The signs in (2.8b) matter: directly,
`Delta k_2+Delta k_3=-e_0` and
`2 Delta k_2+3 Delta k_3=-e_1`.  Thus both constraints cancel exactly,
only `O(1)` counts change, and positivity is preserved.  Because this
correction is tangent to both constraints and starts at the exact finite-`n`
optimizer, the first variation vanishes; the Hessian cost is `O(1/k_co)` and
the Stirling remainder is `O(ln n)`.  We obtain an exact profile

\[
 \mathbf k=(k_2,k_3,k_4,k_5),\qquad
 u_i=\alpha-i,\qquad k_i=\Theta(n/\ln n),                \tag{2.9}
\]

with

\[
 \ln\mathbb E Z_{\mathbf k}^{sgn}=\Theta(n/\ln n).       \tag{2.10}
\]

Here `Z^sgn` counts partitions with each part declared independent or a
clique.  Since every `u_i>=2`, the two declarations are disjoint and the
first moment is exactly `2^k` times the ordinary profile first moment.
Equations (1.7), (2.7), and (2.8) imply

\[
 k_\chi^- - k_{co}
 \ge\left(\frac{q^2\gamma_4}{16}-o(1)\right)
          \frac{n}{(\ln n)^3}.                            \tag{2.11}
\]

## 3. Exact signed overlap representation

For two independent uniform ordered partitions with the profile (2.9), let
`r_ab` be their overlap matrix and put

\[
 w_{ab}=\binom{r_{ab}}2.
\]

Let `H(r)` be the bipartite graph of cells with `r_ab>=2`, omitting isolated
slot vertices.  Write `W=sum w_ab`, `v=|V(H)|`, and `c` for the number of
nonempty components.  Summing the two signs on both partitions gives the
exact normalized local factor

\[
 A_\zeta(r)=2^{W+c-v}
 =\left(\prod_{ab}g(r_{ab})\right)2^{\beta(H)},            \tag{3.1}
\]

where

\[
 g(0)=g(1)=g(2)=1,\qquad
 g(x)=2^{\binom x2-1}\ (x\ge3),\qquad
 \beta(H)=|E(H)|-|V(H)|+c(H).                             \tag{3.2}
\]

Equivalently, `2^beta` is the number of even subgraphs of `H`.  If `p(r)`
is the exact configuration-model overlap law, then

\[
 \frac{\mathbb E(Z_{\mathbf k}^{sgn})^2}
      {(\mathbb EZ_{\mathbf k}^{sgn})^2}
 =\sum_r p(r)A_\zeta(r).                                  \tag{3.3}
\]

This identity includes incompatible signs as zero contributions; it does
not obtain the second moment by naively multiplying an ordinary-colouring
moment by `2^{2k}`.

## 4. Canonical large cells and residual attachments

Put `U=alpha-2` and `R=floor(U/2)`.  Every cell with multiplicity greater
than `R` belongs to a matching, since two such cells cannot share a row or
column.  Canonically expose all these high cells and their exact stub
pairs.  If their total exposed multiplicity is `J`, the unexposed stubs form
an exact uniform bipartite configuration model of total degree `n-J`.

`RESIDUAL_ATTACHMENT.md`, Theorem 2.1, proved and independently audited in
`../audits/RESIDUAL_ATTACHMENT_AUDIT.md`, sums every residual threshold
increment and the entire even-subgraph factor, including cycles joining
arbitrarily many high cells.  There is a deterministic
`b_n=o(n/N^4)` such that, uniformly over every high skeleton `(M,j)`, its
conditional residual factor satisfies the **one-sided** bound

\[
 \mathcal A(M,j)\le e^{b_n}.                              \tag{4.1}
\]

More precisely, for an absolute `C`, the upper bound is `exp(CN^8)` when
the residual degree is at least `n/N^6`, and `exp(Cn/N^5)` below that
cutoff.  The cap indicator in `mathcal A` can make this factor smaller than
one, so no lower bound and no two-sided assertion about `ln mathcal A` is
made or needed.

The proof has two regimes.  If the residual degree is at least
`n/N^6`, weighted residual row and column sums are
`O(N^3/(n-J))`; a cycle-walk expansion gives only
`O(N^8)`.  Below that degree, the deterministic inequalities
`beta<=|E(H_res)|` and
`sum binom(r_e,2)<=(U-1)(n-J)/2` give `O(n/N^5)`.
The matching acts as a partial permutation of norm one, so no factor `2^h`
or `h^r` is lost.

## 5. The dense four-type high-cell sum

For a full-containment endpoint matrix `L=(ell_ij)`, let its row and column
margins be `r,c`, put `x_ij=min(u_i,u_j)`, and
`J=sum x_ij ell_ij`.  Its exact bare weight is

\[
 W(L)=
 \frac{\prod_i(k_i)_{r_i}\prod_j(k_j)_{c_j}}
      {\prod_{ij}\ell_{ij}!}\frac1{(n)_J}
 \prod_{ij}\left[
  \frac{(u_i)_{x_{ij}}(u_j)_{x_{ij}}}{x_{ij}!}g(x_{ij})
 \right]^{\ell_{ij}}.                                    \tag{5.1}
\]

For a diagonal common vector `r`, define

\[
 D(r)=\frac{\prod_i(k_i)_{r_i}^2}{\prod_i r_i!}
       \frac{\prod_i[u_i!g(u_i)]^{r_i}}{(n)_{m_r}},\qquad
 m_r=\sum_i u_i r_i.                                      \tag{5.2}
\]

The exact geometric-mean comparison in
`DENSE_FOUR_TYPE_MATCHING.md`, Lemma 2.1, is

\[
 W(L)\le\sqrt{D(r)D(c)}
 \frac{\sqrt{\prod_i r_i!c_i!}}{\prod_{ij}\ell_{ij}!}
 \prod_{ij}Q_{ij}^{\ell_{ij}},                            \tag{5.3}
\]

where `Q_ii=1` and, uniformly for `i!=j`,

\[
 Q_{ij}\le
 \frac1{|i-j|!}
 \left(C\frac{(\ln n)^{3/2}}{\sqrt n}\right)^{|i-j|}.    \tag{5.4}
\]

The global falling factorial is retained in proving (5.3): concavity of
`ln(n)_x` bounds its ratio by `(n+1)^{sum |i-j|ell_ij/2}`, which is exactly
absorbed in (5.4).  Cauchy's inequality followed by two exact multinomial
expansions handles unequal margins and gives

\[
 \sum_LW(L)
 \le\exp\{O(\sqrt{n\ln n})+O(\ln n)\}\sum_rD(r).          \tag{5.5}
\]

`FOUR_SIZE_PARTIAL_RATES.md` proves directly, for the midpoint profile,

\[
 \sum_rD(r)=1+o(1).                                       \tag{5.6}
\]

Its central rate, with residual normalized counts `z_i`,
`R=sum z_i`, and `I_r=sum i z_i`, is

\[
 \Phi_T(z)=R\ln R+\frac q2(I_r-TR).                       \tag{5.7}
\]

The two elementary bounds

\[
 \Phi_T\le R\{\ln R+q(5-T)/2\},\qquad
 \Phi_T\le R\ln R+q(T-2)(1-R)/2                         \tag{5.8}
\]

give a uniform strict negative rate away from `R=0,1`.  Exact recurrences
at those two singular endpoints show that the nonempty vanishing-mass sum
is `o(1)`, while the near-full sum is `exp(-Omega(n/ln n))` using (2.10).
This proves (5.6) without invoking the ordinary tame-profile expectation
hypothesis.

Replacing a containment multiplicity `m` by `m-e` has exact local ratio

\[
 \frac{\binom me}{(d+1)\cdots(d+e)}
  2^{-em+e(e+1)/2}.                                      \tag{5.9}
\]

Here is the conditioned bridge from the per-cell estimate to the sum over
**all** high skeletons; it is the concise version of canonical equations
(8.25a), (8.26a), and (8.29a)--(8.29b).  For a full-containment table `L`,
temporarily distinguish its endpoint cells.  If `S(L)` is the family of all
near-containment decorations and `w(S)` its bare weight, the single global
falling-factorial comparison gives

\[
 \sum_{S\in\mathcal S(L)}w(S)
 \le W(L)\prod_{c\in L}\left(1+\rho_c\right),\qquad
 \rho_c=O(N^3/n).                                        \tag{5.9a}
\]

Distinguishing and then forgetting identical typed cells is exactly the
multinomial expansion in (5.9a), so it creates no extra multiplicity.  A
high skeleton is a matching with at most `k_co` cells, hence the product is
at most `exp(O(N^2))`.

Condition on such a near-containment skeleton and write `m_0` for its
residual stub mass, with residual row and column degrees `d_a,d'_b`.  If
`m_0>=n/N^6`, expand jointly over sets `D` of **distinct** residual cells and
their threshold demands.  Lemma 6.2 of the canonical manuscript is applied
before any constraints are dropped, giving

\[
\begin{split}
 E_{mid}(S)
 &\le\sum_D\prod_{ab\in D}g(j_{ab})
       \Pr\{r_{ab}\ge j_{ab}\ \text{for every }ab\in D\}\\
 &\le\prod_{ab}\left(1+
       \sum_{R<j\le3U/4+O(1)}
       g(j)\frac{(e d_ad'_b/m_0)^j}{j!}\right)
 \le e^{\Xi_4},\qquad
 \Xi_4=2^{-\Omega((\log_2n)^2)}.                          \tag{5.9b}
\end{split}
\]

This joint threshold expansion, rather than multiplication of marginal
probabilities, handles the residual dependence.  If `m_0<n/N^6`, summing the
residual matching probability first and using `r_e<=U` gives the conditional
bound `E_mid(S)<=exp(CUm_0)<=exp(Cn/N^5)`.  Consequently

\[
 \sum_{\text{all high skeletons}}\text{bare weight}
 \le e^{O(N^2)}\left(\sum_LW(L)\right)
      \max\{e^{\Xi_4},e^{Cn/N^5}\}.                       \tag{5.9c}
\]

Combining (5.5)--(5.6) with (5.9c) yields

\[
 \sum_{\text{all high skeletons}}\text{bare weight}
 \le\exp\left\{O(\sqrt{nN})+O(N^2)+O(n/N^5)\right\}
 =\exp\{o(n/N^4)\}.
                                                                  \tag{5.10}
\]

The exact canonical decomposition is a sum of nonnegative bare skeleton
weights multiplied by their conditional residual factors.  Multiplying the
global upper bound (5.10) by the **uniform one-sided** estimate (4.1) gives
an `exp{o(n/N^4)}` upper bound.  The normalized second moment is at least one
by variance, so its logarithm is nonnegative and

\[
 \boxed{
 \Lambda_n:=\ln\frac{\mathbb E(Z_{\mathbf k}^{sgn})^2}
                     {(\mathbb EZ_{\mathbf k}^{sgn})^2}
 =o\!\left(\frac n{(\ln n)^4}\right).}                 \tag{5.11}
\]

## 6. From the rare seed to a high-probability cocolouring

Paley--Zygmund and (5.11) give

\[
 \Pr\{Z_{\mathbf k}^{sgn}>0\}\ge e^{-\Lambda_n}.        \tag{6.1}
\]

The event on the left implies `zeta(G_n)<=k_co`.  The independently audited
rare-event Alon--Scott theorem in `ALON_CONCENTRATION_EXTENSION.md` and
`../audits/RARE_EVENT_AMPLIFICATION_AUDIT.md` supplies a deterministic
`epsilon_n=o(1)`, independent of the deterministic parameters below, such
that uniformly for every deterministic `r=r(n)>0`,

\[
 \Pr\!\left\{\zeta(G_n)>k_{co}+C\left(
   \frac{\sqrt{n\Lambda_n}+\sqrt{nr}}N+n^{1/3}+1
  \right)\right\}
 \le e^{-r}+\varepsilon_n.                              \tag{6.2}
\]

Choose

\[
 B_n=\frac n{N^4},\qquad r_n=\sqrt{B_n}.                  \tag{6.3}
\]

Then `r_n->infinity`, and (5.11) makes the deterministic sequence

\[
 a_n=C\left(
   \frac{\sqrt{n\Lambda_n}+\sqrt{nr_n}}N+n^{1/3}+1
 \right)                                                 \tag{6.4}
\]

satisfy `a_n=o(n/N^3)`.  The probability statement is now the unambiguous
uniform tail bound

\[
 \Pr\{\zeta(G_n)>k_{co}+a_n\}
 \le e^{-r_n}+\varepsilon_n\longrightarrow0.             \tag{6.5}
\]

## 7. Completion and quantifiers

Let
`E_chi={chi(G_n)>k_chi^-}` and
`E_co={zeta(G_n)<=k_co+a_n}`.  Equations (1.8) and (6.5) show that both
events have probability tending to one; a union bound is sufficient, and no
independence is asserted.  By (2.11) and `a_n=o(n/N^3)`, on their intersection

\[
 \chi(G_n)-\zeta(G_n)
 \ge\left(\frac{q^2\gamma_4}{16}-o(1)\right)
       \frac n{(\ln n)^3}.                                \tag{7.1}
\]

For all sufficiently large `n`, the right side is at least
`c_* n/(ln n)^3`, with `c_*=q^2 gamma_4/32`.  This proves (0.1).
Since `n/(ln n)^3->infinity`, (0.2) follows for every fixed `M`.

Every estimate above is uniform for `delta in [0,1)` and for the exact
integer profile after rounding.  Therefore the proof covers all
sufficiently large integers `n`, including sequences approaching either
side of every independence-number jump.  It proves a high-probability
statement, not merely an expectation bound, positive probability, density
subset, or infinite subsequence result.

## 8. Internal dependency list

The canonical authority is `COMPLETE_PROOF_SELF_CONTAINED.md`; the component
notes below support its derivations and do not supersede it.  The supporting
proofs and audit records are:

- `COMPLETE_PROOF_SELF_CONTAINED.md`: consolidated proof with the component
  derivations written out in one document;
- `EXCEPTIONAL_REGIME.md`: uniform `mu` and phase expansions;
- `ALPHA_MINUS_TWO_ROUTE.md`: analytic entropy certificate, root gap,
  unrestricted Markov lower bound, and exact integer midpoint profile;
- `X_SECOND_MOMENT.md` and `SIGNED_PROFILE_OVERLAP.md`: exact signed overlap
  factor and configuration-model identities;
- `FOUR_SIZE_PARTIAL_RATES.md`: the all-range diagonal sum (5.6);
- `DENSE_FOUR_TYPE_MATCHING.md`: unequal-margin transport and decoration
  sum;
- `RESIDUAL_ATTACHMENT.md`: all residual local and even-subgraph
  attachments;
- `../audits/RESIDUAL_ATTACHMENT_AUDIT.md`: independent reconstruction of the
  residual theorem;
- `ALON_CONCENTRATION_EXTENSION.md` and
  `../audits/RARE_EVENT_AMPLIFICATION_AUDIT.md`: rare-event-to-whp transfer;
- `../audits/FULL_PROOF_AUDIT_1.md` through
  `../audits/FULL_PROOF_AUDIT_4.md`: historical
  2026-07-12 end-to-end reconstructions with PASS verdicts for the earlier
  snapshot, not reviews of the later synchronized bytes;
- `../audits/ADVERSARIAL_LEAP_AUDIT_2026-07-13.md`: the targeted regression
  audit for the root corridor, rounding identities, high-skeleton
  globalization, one-sided residual bound, and deterministic amplification
  sequence in the repaired canonical manuscript;
- `../audits/PROOF_COMPONENT_SYNCHRONIZATION_AUDIT_2026-07-13.md`: propagation
  audit for the synchronized component notes and this concise draft.

Reproducible diagnostic scripts are in `../experiments/`; finite
experiments are not used as proof steps.
