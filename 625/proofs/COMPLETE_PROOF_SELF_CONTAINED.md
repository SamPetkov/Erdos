# A self-contained proof of a polynomial-scale gap between the chromatic and cochromatic numbers of a random graph

**Authors:** Samuil Petkov & ChatGPT 5.6

**Date:** 2026-07-12  
**Status:** self-contained manuscript assembled from, and checked against, the
component arguments in this research dossier.  This document makes no claim
of external peer review or priority.

## Abstract

For a graph `G`, let `chi(G)` be its chromatic number and let `zeta(G)` be
the least number of parts in a vertex partition in which every part induces
either an empty graph or a complete graph.  We prove that, for
`G_n~G(n,1/2)`,

\[
 \Pr\left\{\chi(G_n)-\zeta(G_n)
 \ge \frac{(\ln2)^2}{32}\ln\frac{200}{153}
       \frac{n}{(\ln n)^3}\right\}\longrightarrow1.      \tag{0.1}
\]

The construction uses classes of the four sizes
`alpha-2,...,alpha-5`, where `alpha` is the usual independence-number
phase.  Signing each class as independent or complete moves its
first-moment root down by order `n/(ln n)^3`, uniformly through the whole
phase cycle.  An exact sign-summed overlap identity reduces the second
moment to a bipartite configuration model.  We sum partial diagonals,
unequal-type dense containments, all intermediate high cells, and every
residual even-subgraph attachment with logarithmic cost
`o(n/(ln n)^4)`.  Paley--Zygmund gives a possibly rare cocolouring, and a
proved Alon--Scott-type leftover argument amplifies it to high probability
without losing the root separation.

## 1. Notation and elementary facts

All logarithms are natural unless a base is displayed.  Put

\[
 q=\ln2,\qquad N=\ln n,\qquad w=\ln N.                    \tag{1.1}
\]

For an integer `s`, let

\[
 \mu_s(v)=\binom vs2^{-\binom s2},\qquad \mu_s=\mu_s(n). \tag{1.2}
\]

We use the following standard inequalities in their stated forms.

1. For integers `m>=1`,
   \[
    \ln(m!)=m\ln m-m+\frac12\ln(2\pi m)+O(1/m).          \tag{1.3}
   \]
   In particular, uniformly for `m>=0`, with `0 ln0=0`, the last two
   terms may be replaced by `O(ln(m+1))`.
2. If a random variable `Y` is a function of `r` independent blocks and
   changing one block changes `Y` by at most one, then
   \[
    \Pr\{|Y-\mathbb EY|\ge t\}
    \le2\exp(-2t^2/r).                                    \tag{1.4}
   \]
   We will use the corresponding one-sided bounds as well.
3. If `Z>=0` and `0<EZ<infinity`, then
   \[
    \Pr\{Z>0\}\ge\frac{(\mathbb EZ)^2}{\mathbb EZ^2}.   \tag{1.5}
   \]
4. If `X~Bin(m,1/2)`, then
   \[
    \Pr\{X\le m/4\}\le e^{-m/16}.                       \tag{1.6}
   \]
   Indeed, exponential Markov with `t=ln 3` bounds the probability by
   `[3^(1/4)(2/3)]^m<=e^{-m/16}`.
5. For every nonnegative random variable `X` and `a>0`,
   `P(X>=a)<=E X/a`.

The first is Stirling's estimate, the second is McDiarmid's bounded-
differences inequality, and the third is the zero-threshold case of
Paley--Zygmund.  The fourth is the only binomial-tail estimate used below;
the fifth is Markov's inequality.

## 2. The complete independence-number phase

Define

\[
 \alpha_0=2\log_2n-2\log_2\log_2n
             +2\log_2(e/2)+1,
 \quad \alpha=\lfloor\alpha_0\rfloor,
 \quad \delta=\alpha_0-\alpha.                           \tag{2.1}
\]

Thus `0<=delta<1`.  The estimates below are uniform on this entire
interval, including sequences approaching either endpoint.

### Lemma 2.1 (phase expansion)

There is a bounded continuous function `K(delta)` such that

\[
 \ln\mu_\alpha
 =\delta N+\left(\frac2q-\frac12-\delta\right)w
   +K(\delta)+O(w^2/N).                                  \tag{2.2}
\]

In particular,

\[
 \mu_{\alpha+2}=n^{\delta-2+o(1)}
 \le n^{-1+o(1)}=o(1),                                   \tag{2.3}
\]

and, with `a=alpha-2`,

\[
 \mu_a\ge c n^2N^{2/q-5/2}                              \tag{2.4}
\]

for an absolute `c>0` and all sufficiently large `n`.

#### Proof

Write

\[
 C=1+\ln q-q,\qquad S=N-w+C,\qquad b=1-\delta.
\]

Then `alpha=2S/q+b`.  Since `alpha=O(N)`, (1.3) gives

\[
 \ln(n)_\alpha=\alpha N+
 \sum_{j=0}^{\alpha-1}\ln(1-j/n)
 =\alpha N+O(\alpha^2/n),
\]

and hence

\[
 \ln\mu_\alpha
 =\alpha\left(N-\ln\alpha+1-\frac q2(\alpha-1)\right)
  -\frac12\ln(2\pi\alpha)+O(1/N).                       \tag{2.5}
\]

Expanding `ln alpha` at `2N/q`, uniformly in `b in (0,1]`, gives

\[
 N-\ln\alpha+1-\frac q2(\alpha-1)
 =\frac{q\delta}{2}
  +\frac{w-C-bq/2}{N}+O(w^2/N^2).                        \tag{2.6}
\]

Multiplication by `alpha` proves (2.2).  For reference, the bounded
constant is

\[
\begin{split}
 K(\delta)={}&\delta C+\frac q2\delta(1-\delta)-\frac{2C}{q}
 -(1-\delta)\\
 &-\frac12\ln(2\pi)-\frac q2+\frac12\ln q.
\end{split}                                               \tag{2.7}
\]

The exact adjacent-size ratios are

\[
 \frac{\mu_{s+1}}{\mu_s}
 =\frac{n-s}{s+1}2^{-s},\qquad
 \frac{\mu_{s-1}}{\mu_s}
 =\frac{s}{n-s+1}2^{s-1}.                                \tag{2.8}
\]

At `s=alpha+O(1)`, the first is `Theta(N/n)` and the
second is `Theta(n/N)`, uniformly in `delta`.  Applying the first ratio
twice to (2.2) proves (2.3).  The minimum of the right side of (2.2) over
the phase is attained, up to a constant factor, at `delta=0`; hence
`mu_alpha>=c_1N^{2/q-1/2}`.  Applying the second ratio twice proves
(2.4).  \(\square\)

It follows at once from (2.3) and Markov's inequality that

\[
 \Pr\{\alpha(G_n)>\alpha+1\}=o(1).                       \tag{2.9}
\]

## 3. Continuous profile roots

For a class size `u`, put

\[
 d_u=2^{\binom u2}u!.
\]

Write `u=alpha-i`, so that `i` is the deficit from `alpha`.  Let

\[
 S_+=\{-1,0,1,2,\ldots\},\qquad S_4=\{2,3,4,5\}.         \tag{3.1}
\]

At finite `n`, `S_+` is cut off at `i=alpha-1`, since class sizes are
positive.  For a real class count `k`, define

\[
 L_{\mathbf k}=nN-n+k-\sum_i k_i\ln(k_id_{\alpha-i}),    \tag{3.2}
\]

and let `L_S(n,k)` be its maximum over real `k_i>=0` satisfying

\[
 \sum_{i\in S}k_i=k,\qquad
 \sum_{i\in S}(\alpha-i)k_i=n.                           \tag{3.3}
\]

Set

\[
 T=\alpha-\frac nk.                                      \tag{3.4}
\]

The following lemma supplies all root geometry needed later.

### Lemma 3.1 (root phase, derivative, and support comparison)

Let

\[
 s_0=\alpha_0-1-\frac2q,\qquad
 T_0=\alpha-s_0=1+\frac2q-\delta.                        \tag{3.5}
\]

For `S=S_+` and `S=S_4`, the relevant zero of `L_S(n,k)` has

\[
 \frac nk=s_0+O(w/N),\qquad T=T_0+O(w/N).                \tag{3.6}
\]

Uniformly when `k` is within `O(n/N^3)` of either zero,

\[
 \frac{\partial L_S}{\partial k}
 =\frac2qN^2+O(Nw).                                      \tag{3.7}
\]

For two supports `R,S`, at the same feasible `k`,

\[
 \frac{L_R(n,k)-L_S(n,k)}k
 =\mathcal F_{n,R}(T)-\mathcal F_{n,S}(T),               \tag{3.8}
\]

where, uniformly for `T=T_0+o(1)`,

\[
 \mathcal F_{n,S}(T)\longrightarrow
 \mathcal F_S(T):=\max_{\substack{\sum p_i=1\\\sum ip_i=T}}
 \left[-\sum p_i\ln p_i-\frac q2\sum i^2p_i\right].  \tag{3.9}
\]

The convergence and all error terms are uniform in `delta`.

#### Proof

Put `s=n/k` and `p_i=k_i/k`.  Dividing (3.2) by `k` gives

\[
 \frac{L_S(n,n/s)}{n/s}
 =(s-1)N-s+1+\ln s
 +\max_p\left[-\sum p_i\ln p_i-\sum p_i\ln d_{\alpha-i}\right].
                                                               \tag{3.10}
\]

There is an exact affine-plus-curved decomposition

\[
 -\ln d_{\alpha-i}=A_n+B_ni+h_n(i),                      \tag{3.11}
\]

where

\[
 A_n=-\ln d_\alpha,\qquad
 B_n=q\alpha-q/2+\ln\alpha,                              \tag{3.12}
\]

and, for `i>=0`,

\[
 h_n(i)=-\frac q2i^2+\sum_{r=0}^{i-1}\ln(1-r/\alpha).   \tag{3.13}
\]

For `i=-1`, direct subtraction gives
`h_n(-1)=-q/2+ln(alpha/(alpha+1))`.  Thus, for fixed `i`,

\[
 h_n(i)=-qi^2/2+O(i^2/\alpha),                           \tag{3.14}
\]

while (3.13) also supplies a uniform Gaussian upper tail.  Since the target
mean `T_0` stays in the compact interval

\[
 \frac2q\le T_0\le1+\frac2q,                             \tag{3.15}
\]

the Lagrange tilt in the entropy maximum is bounded.  Its optimizer is
proportional to `exp(lambda i+h_n(i))`, and (3.13) makes the omitted tail
uniformly summable.  Dominated convergence proves (3.9).  The affine terms
in (3.11) prove the exact difference identity (3.8).

Substitute (3.11) into (3.10).  If `T=alpha-s`, the scalar part at
`s=s_0` is, by Stirling,

\[
 s_0\left(N-\ln\alpha-\frac q2s_0+\frac q2\right)-N
 +T_0+1+\ln s_0+\frac q2T_0^2
 -\frac12\ln(2\pi\alpha)+O(1/N).                        \tag{3.15a}
\]

Now `q s_0/2=N-w+ln q-q` exactly, while
`ln alpha=ln s_0+T_0/s_0+O(1/N^2)` and
`ln s_0=w+q-ln q+O(w/N)`.  These relations reduce (3.15a) to
`O(w)`, uniformly in the phase.  The entropy term is `O(1)` by the
Gaussian tail just proved.  Hence

\[
 L_S(n,n/s_0)/(n/s_0)=O(w).                              \tag{3.16}
\]

Differentiating (3.10) by the envelope theorem, and using

\[
 B_n=2N-w+O(1),                                          \tag{3.17}
\]

gives

\[
 \frac{d}{ds}\left\{\frac{L_S(n,n/s)}{n/s}\right\}
 =-N+O(w)                                                \tag{3.18}
\]

in a fixed neighbourhood of `s_0`.  Equations (3.16)--(3.18) give the
unique local zero and (3.6).  Finally, if the expression in braces is
`Psi(s)`, then `L=k Psi(s)` and `ds/dk=-s/k`; at a zero,

\[
 \frac{dL}{dk}=-s\Psi'(s)=\frac2qN^2+O(Nw).              \tag{3.19}
\]

Changing `k` by `O(n/N^3)` changes `s` by only `O(1/N)`, so the same
estimate is uniform throughout the stated window.  \(\square\)

## 4. A valid unrestricted lower location for `chi`

Let `r_+(n)` be the zero in Lemma 3.1 for `S_+`, and put

\[
 k_\chi^-:=\lfloor r_+(n)\rfloor-\lceil N\rceil.         \tag{4.1}
\]

For an integer profile, direct enumeration gives

\[
 \mathbb E X_{\mathbf k}
 =\frac{n!}{\prod_i((\alpha-i)!)^{k_i}k_i!}
  2^{-\sum_i k_i\binom{\alpha-i}{2}}.                   \tag{4.2}
\]

There are at most
`(n+1)^(alpha+1)=exp(O(N^2))` bounded profiles.  Applying (1.3) to
(4.2), uniformly even when some `k_i=0`, yields

\[
 \ln E_{n,k,\alpha+1}\le L_+(n,k)+O(N^2),                \tag{4.3}
\]

where the left side is the logarithm of the expected total number of
unordered, exactly `k`-part, `(alpha+1)`-bounded colourings.  By Lemma
3.1,

\[
 L_+(n,k_\chi^-)\le-cN^3,                                \tag{4.4}
\]

so the expectation in (4.3) is `o(1)`.  On the event (2.9), any colouring
with at most `k_chi^-` nonempty parts can be refined, by splitting parts,
to exactly `k_chi^-` nonempty independent parts, all of size at most
`alpha+1`.  Therefore

\[
 \Pr\{\chi(G_n)\le k_\chi^-\}=o(1).                     \tag{4.5}
\]

This is an unrestricted chromatic lower bound; the size cap has been
removed probabilistically by (2.9).

## 5. The four-size signed first-moment advantage

The optimizer in (3.9) has the form

\[
 p_i=\frac{e^{\lambda i-qi^2/2}}
           {\sum_{j\in S}e^{\lambda j-qj^2/2}},          \tag{5.1}
\]

where `lambda` is chosen to give mean `T`.  Define

\[
 D_4(\delta)=\mathcal F_{S_+}(T_0)
              -\mathcal F_{S_4}(T_0),\qquad
 \gamma_4=\ln\frac{200}{153}.                            \tag{5.2}
\]

### Lemma 5.1 (uniform entropy certificate)

For every `0<=delta<=1`,

\[
 0\le D_4(\delta)<\ln\frac{153}{100},\qquad
 q-D_4(\delta)>\gamma_4.                                 \tag{5.3}
\]

#### Proof

Let `lambda_4` be the tilt for `S_4`.  At `lambda=2q`, shift the
index by two.  The four-size mean is no larger than

\[
 2+\frac{\sum_{j\ge0}j2^{-j^2/2}}
          {\sum_{j\ge0}2^{-j^2/2}}<2+\frac45<\frac2q.    \tag{5.4}
\]

For the first strict inequality, retain the first three terms of the
denominator, sum the numerator through `j=3`, and bound its remaining
geometric tail by `1/60`; the elementary bounds
`2/3<q<5/7` prove the second.  At `lambda=9q/2`, put
`t=2^{-1/8}`.  The four weights are proportional to

\[
 t^{25},\quad t^9,\quad t,\quad t.
\]

Their mean is greater than four because

\[
 t-t^9-2t^{25}=t(1-t^8-2t^{24})=t/4>0,                 \tag{5.5}
\]

whereas `1+2/q<4`.  Hence

\[
 2q<\lambda_4<9q/2.                                     \tag{5.6}
\]

For a tilt `lambda`, let `L(lambda)` be the total weight of deficits
`-1,0,1` divided by the weight of deficits `2,3,4,5`, and let
`H(lambda)` be the analogous ratio for deficits at least six.  The first
ratio decreases and the second increases with `lambda`.  Directly summing
the displayed finite terms and bounding the Gaussian tails gives

\[
 L(2q)<\frac{51}{100},\quad H(3q)<\frac1{50},\quad
 L(3q)<\frac3{25},\quad H(9q/2)<\frac14.                 \tag{5.7}
\]

Here are explicit checks.  At `2q`, with `b=2^{-1/2}`,

\[
 L(2q)=\frac{b+1/4+b/16}{1+b+1/4+b/16}<51/100.
\]

At `3q`, after centring at deficit three, the denominator is
`5/4+2b`; the high numerator is at most
`b/16+1/256+1/3968`, and the low numerator is
`1/256+b/16+1/4`.  The inequalities follow from
`7/10<b<71/100`.  Finally, after division by `t`, the tail above deficit
five at `9q/2` begins with `t^8,t^24,t^48`; the rest is below `1/60`,
and

\[
 3(t^8+t^{24})+4/60<2,                                  \tag{5.8}
\]

which is equivalent to `H(9q/2)<1/4`.

If `lambda_4<=3q`, monotonicity and (5.7) give `L+H<53/100`;
if `lambda_4>=3q`, they give `L+H<37/100`.  Evaluating the dual
function for `S_+` at the `S_4` tilt yields

\[
 D_4\le\ln(1+L(\lambda_4)+H(\lambda_4))<\ln(153/100).
\]

Since `S_4` is a subset of `S_+`, the loss is nonnegative.  Subtracting
from `q=ln2` completes the proof.  \(\square\)

For a fixed partition into `k` classes, assigning each class the declaration
"independent" or "complete" multiplies its first moment by `2^k`: every
declaration prescribes all internal edge bits, and all `2^k` declarations
have probability `2^{-sum binom(u,2)}`.  Let `r_4^{co}` be the zero of

\[
 L_{S_4}(n,k)+qk.                                       \tag{5.9}
\]

At `k=r_+`, Lemma 3.1 and (5.2) give

\[
 L_{S_4}(n,r_+)+qr_+
 =r_+\{q-D_4(\delta)+o(1)\}.                             \tag{5.10}
\]

Since `r_+=(q/2+o(1))n/N`, the mean-value theorem and (3.7) give

\[
 r_+-r_4^{co}
 =\left(\frac{q^2}{4}\{q-D_4(\delta)\}+o(1)\right)
   \frac n{N^3}.                                        \tag{5.11}
\]

In particular, for all sufficiently large `n`,

\[
 r_+-r_4^{co}\ge\frac{q^2\gamma_4}{8}\frac n{N^3}.     \tag{5.12}
\]

Choose the midpoint integer

\[
 k_{co}=\left\lceil\frac{r_4^{co}+r_+}{2}\right\rceil. \tag{5.13}
\]

At this exact `k`, let `p_i^{(n)}` be the exact finite-`n` maximizer of
`L_{S_4}`.  Its Lagrange equations give

\[
 p_i^{(n)}\ \propto\ d_{\alpha-i}^{-1}e^{\lambda_ni},  \tag{5.14}
\]

subject to mean `alpha-n/k_co`.  Lemma 3.1 makes these proportions
converge uniformly to (5.1).  Equation (5.6) also shows directly that the
four limiting weights differ by at most a fixed factor.  Thus

\[
 \min_{2\le i\le5}p_i^{(n)}\ge c_p>0                    \tag{5.15}
\]

uniformly in the phase.

Round `k_co p_i^(n)` to integers.  If the errors in the total-count and
total-deficit constraints are `e_0,e_1=O(1)`, add

\[
 \Delta k_2=e_1-3e_0,\qquad
 \Delta k_3=2e_0-e_1.                                   \tag{5.16}
\]

This enforces both constraints exactly, changes only `O(1)` counts, and
preserves positivity by (5.15).  Because the displacement is tangent to
both constraints and starts at the exact finite optimizer, its first
variation vanishes and its Hessian cost is `O(1/k_co)`.  Applying (1.3)
to the five factorials gives an exact integer vector

\[
 \mathbf k=(k_2,k_3,k_4,k_5),\qquad
 u_i=\alpha-i,\qquad k_i=\Theta(n/N),                    \tag{5.17}
\]

whose signed first moment is

\[
 \mathbb EZ_{\mathbf k}^{sgn}
 =2^{k_{co}}\frac{n!}{\prod_i(u_i!)^{k_i}k_i!}
   2^{-\sum_i k_i\binom{u_i}{2}},                        \tag{5.18}
\]

and

\[
 \ln\mathbb EZ_{\mathbf k}^{sgn}
 =L_{S_4}(n,k_{co})+qk_{co}+O(N)
 \ge c_Zk_{co}                                          \tag{5.19}
\]

for a phase-independent `c_Z>0`.  The last inequality follows from the
midpoint distance, (3.7), and (5.12).  Every `u_i` tends to infinity, so
the independent and complete declarations of one part are disjoint.  Thus
`Z_{\mathbf k}^{sgn}>0` implies an actual cocolouring with `k_co` parts.

Finally, (4.1), (5.12), and (5.13) give

\[
 k_\chi^- -k_{co}
 \ge\left(\frac{q^2\gamma_4}{16}-o(1)\right)
       \frac n{N^3}.                                    \tag{5.20}
\]

## 6. Exact signed second-moment representation

Temporarily label all slots within each of the four types.  This multiplies
the unordered witness by the deterministic factor `prod_i k_i!` and hence
does not change its normalized second moment.  Choose two independent
uniform ordered partitions of the profile.  If their slots are indexed by
`a` and `b`, put

\[
 r_{ab}=|V_a\cap W_b|.                                   \tag{6.1}
\]

The overlap matrix has the exact law

\[
 p(r)=\frac{\prod_a s_a!\prod_b t_b!}
            {n!\prod_{a,b}r_{ab}!},                      \tag{6.2}
\]

where here both degree lists are the multiset given by (5.17).
Equivalently, place `s_a` stubs at each row slot and `t_b` stubs at each
column slot and take a uniform perfect matching of the two `n`-stub sets.

Let `H(r)` be the simple bipartite graph whose edges are cells with
`r_ab>=2`, omitting isolated slot vertices.  Write

\[
 W=\sum_{a,b}\binom{r_{ab}}2,\qquad
 \beta(H)=|E(H)|-|V(H)|+c(H).                             \tag{6.3}
\]

### Lemma 6.1 (exact sign sum)

The normalized local factor of the pair of partitions is

\[
 A_\zeta(r)=2^{W+c(H)-|V(H)|}
 =\left(\prod_{a,b}g(r_{ab})\right)2^{\beta(H)},          \tag{6.4}
\]

where

\[
 g(0)=g(1)=g(2)=1,\qquad
 g(x)=2^{\binom x2-1}\quad(x\ge3).                       \tag{6.5}
\]

Consequently

\[
 \frac{\mathbb E(Z_{\mathbf k}^{sgn})^2}
      {(\mathbb EZ_{\mathbf k}^{sgn})^2}
 =\sum_rp(r)A_\zeta(r).                                  \tag{6.6}
\]

#### Proof

Let `B=sum_a binom(s_a,2)`, which is the number of internal edge bits
prescribed by one partition.  A row sign and a column sign are compatible
on a cell of size at least two exactly when they agree.  Therefore signs
must be constant on every component of `H`.  There are

\[
 2^{2k_{co}-|V(H)|+c(H)}
\]

compatible pairs of sign assignments, including the free signs on slots
isolated from `H`.  For each compatible pair, `W` edge bits are prescribed
twice, so the probability of all constraints is `2^{-(2B-W)}`.  Division
by the square of the one-partition signed probability
`(2^{k_co}2^{-B})^2` gives the first expression in (6.4).

For every support edge, split `binom(r,2)` as
`(binom(r,2)-1)+1`.  Since
`|E|-|V|+c=beta`, this gives the second expression.  Averaging over (6.2)
proves (6.6).  \(\square\)

The identity

\[
 2^{\beta(H)}
 =\#\{F\subseteq E(H):\deg_F(v)\text{ is even for every }v\} \tag{6.7}
\]

will be used repeatedly.  It is the elementary fact that the even
subgraphs form the binary cycle space of dimension `beta(H)`.

We also need one exact configuration-model estimate.

### Lemma 6.2 (joint prescribed-cell bound)

In a bipartite configuration model of total degree `m_0`, with row degrees
`d_a` and column degrees `d'_b`, prescribe distinct cells `D` and demands
`x_ab>=1`.  Put

\[
 x=\sum_Dx_{ab},\quad D_a=\sum_bx_{ab},\quad
 D'_b=\sum_ax_{ab}.
\]

Then

\[
 \Pr\{r_{ab}\ge x_{ab}\ \forall ab\in D\}
 \le\frac{\prod_a(d_a)_{D_a}\prod_b(d'_b)_{D'_b}}
          {(m_0)_x\prod_{ab\in D}x_{ab}!}.               \tag{6.8}
\]

In particular, with `theta_ab=e d_a d'_b/m_0`, the right side is at most

\[
 \prod_{ab\in D}\frac{\theta_{ab}^{x_{ab}}}{x_{ab}!}.  \tag{6.9}
\]

#### Proof

Choose the required row and column stubs and biject them inside each
prescribed cell.  This gives the numerator of (6.8); any fixed set of `x`
paired stubs occurs with probability `1/(m_0)_x`.  A union bound proves
(6.8).  Next use `(d)_r<=d^r` and

\[
 (m_0)_x=x!\binom{m_0}{x}\ge(m_0/e)^x,                  \tag{6.10}
\]

which proves (6.9).  Notice that (6.8) retains the single global falling
factorial before (6.9) is taken.  \(\square\)

## 7. Exact partial diagonals

For a selected common subprofile `ell=(ell_i)`, put

\[
 L=\sum_i\ell_i,\qquad
 m=\sum_i u_i\ell_i,\qquad
 M=\sum_i\binom{u_i}{2}\ell_i.                           \tag{7.1}
\]

The signed first moment of such partial partitions occupying any `m`
vertices of `[n]` is

\[
 Y_{\ell}^{sgn}
 =2^L\frac{n!}{(n-m)!\prod_i(u_i!)^{\ell_i}\ell_i!}
       2^{-M}.                                           \tag{7.2}
\]

Summing the possible matchings between selected row and column slots gives
the exact common-subprofile contribution

\[
 D(\ell)=\frac{\prod_i\binom{k_i}{\ell_i}^2}
                 {Y_\ell^{sgn}}.                         \tag{7.3}
\]

In particular, `D(0)=1` and
`D(k)=1/E Z_k^sgn`.  Adding one common block gives

\[
 \frac{D(\ell+e_i)}{D(\ell)}
 =\frac{(k_i-\ell_i)^2}
        {2(\ell_i+1)\mu_{u_i}(n-m)}.                     \tag{7.4}
\]

At the opposite endpoint, put `h=k-ell`,
`v=sum_i u_i h_i`, and let `Z_h^sgn(v)` be the signed first moment of a
complete profile `h` on `v` vertices.  Exact factorial cancellation gives

\[
 D(k-h)=\frac{B(h)}{\mathbb EZ_k^{sgn}},\qquad
 B(h)=\left(\prod_i\binom{k_i}{h_i}\right)Z_h^{sgn}(v), \tag{7.5}
\]

and

\[
 \frac{B(h+e_i)}{B(h)}
 =\frac{2(k_i-h_i)\mu_{u_i}(v+u_i)}{(h_i+1)^2}.          \tag{7.6}
\]

### Lemma 7.1 (all common subprofiles)

For the exact midpoint profile,

\[
 \sum_{0\le\ell_i\le k_i}D(\ell)=1+o(1).               \tag{7.7}
\]

#### Proof: the empty corner

Let

\[
 \eta=\frac{w}{32N},\qquad
 \lambda_i=\frac{k_i^2}{2\mu_{u_i}(n)},\qquad
 \Lambda=\sum_i\lambda_i.                               \tag{7.8}
\]

Equations (2.4), (2.8), and `k_i=Theta(n/N)` imply

\[
 \Lambda=O(N^{-(2/q-1/2)})=o(1).                        \tag{7.9}
\]

If the final selected mass is at most `eta n`, every intermediate mass
`m'` in (7.4) satisfies

\[
 \frac{\mu_{u_i}(n)}{\mu_{u_i}(n-m')}
 \le(1-2\eta)^{-u_i}\le N^{3/8}.                        \tag{7.10}
\]

Iterating (7.4), in any order, yields

\[
 D(\ell)\le\prod_i\frac{(N^{3/8}\lambda_i)^{\ell_i}}
                              {\ell_i!}.
\]

Thus

\[
 1\le\sum_{m\le\eta n}D(\ell)
 \le\exp(N^{3/8}\Lambda)=1+o(1).                       \tag{7.11}
\]

#### Proof: the central range

Write

\[
 p_i=k_i/k_{co},\quad y_i=\ell_i/k_{co},\quad
 Y=\sum_i y_i,\quad I=\sum_i i y_i,\quad
 z_i=p_i-y_i,\quad R=\sum_i z_i=1-Y,\quad
 I_r=\sum_i i z_i=T-I.                                  \tag{7.12}
\]

The residual vertex fraction is

\[
 \rho=\frac{n-m}{n}
 =R+\frac{I-TY}{\alpha-T}.                              \tag{7.13}
\]

Uniform Stirling estimates in (7.3), retaining zeros, give

\[
\begin{split}
 \ln D(\ell)={}&n\rho\ln\rho\\
 &+k_{co}\sum_i\{2p_i\ln p_i-2(p_i-y_i)\ln(p_i-y_i)
                  -y_i\ln y_i-y_i+y_iE_i\}+O(N),        \tag{7.14}
\end{split}
\]

where

\[
 E_i=\ln k_{co}+\ln(u_i!)+u_i-u_iN
       +q\binom{u_i}{2}-q.                               \tag{7.15}
\]

Exact subtraction and the definition of `alpha_0` give

\[
 E_{i+1}-E_i=N-\ln(\alpha-i)-q(\alpha-i)+q-1
            =-q\alpha/2+O(1).                            \tag{7.16}
\]

Let `bar E=sum p_iE_i`.  Applying Stirling to the complete moment
(5.18) gives

\[
 -\frac1{k_{co}}\ln\mathbb EZ_k^{sgn}
 =\sum_i p_i\ln p_i-1+\bar E+o(1).                      \tag{7.17}
\]

The positive margin (5.19) bounds `bar E` above.  Since
`sum p_i(i-T)=0`, (7.16) implies

\[
 \sum_i y_iE_i\le\frac{q\alpha}{2}(TY-I)+O(Y).          \tag{7.18}
\]

The remaining entropy expression in (7.14) is
`O(Y ln(e/Y))`, uniformly because every `p_i` is bounded below.  If
`rho>=1/32`, then `R>=1/64` for large `n`, and (7.13) gives

\[
 n\rho\ln\rho=k_{co}\alpha R\ln R+O(k_{co}Y).           \tag{7.19}
\]

Consequently

\[
 \ln D(\ell)
 \le k_{co}\alpha\Phi_T(z)
     +Ck_{co}Y\ln(e/Y)+CN,                               \tag{7.20}
\]

where

\[
 \Phi_T(z)=R\ln R+\frac q2(I_r-TR).                     \tag{7.21}
\]

This rate is uniformly negative away from its two corners.  Indeed,

\[
 I_r-TR\le(5-T)R,\qquad
 I_r-TR=\sum_i(T-i)y_i\le(T-2)(1-R),                    \tag{7.22}
\]

and hence

\[
 \Phi_T\le R\{\ln R+q(5-T)/2\},
 \quad
 \Phi_T\le R\ln R+q(T-2)(1-R)/2.                       \tag{7.23}
\]

On `R<=47/100`, the first bound is at most `-Y/5000`, using
`q<0.6932`; on `R>=47/100`, convexity of

\[
 R\ln R+(1-q/2+1/200)(1-R)
\]

between `47/100` and `1` gives the same conclusion, in fact with
`1/200` in place of `1/5000`.  Thus, whenever

\[
 m>\eta n,\qquad n-m>n/32,                               \tag{7.24}
\]

we have `Y>=eta/2`, and the leading negative term in (7.20) dominates
the entropy error.  Uniformly in this range,

\[
 D(\ell)\le e^{-c k_{co}w}.                              \tag{7.25}
\]

There are only `(k_co+1)^4` vectors, so their total is `o(1)`.

#### Proof: the full corner

It remains to take `v=n-m<=n/32`.  Uniformly for the four sizes,
`mu_{u_i}(n)<=n^{6+o(1)}` by (2.2) and (2.8), while

\[
 \mu_{u_i}(v)\le\mu_{u_i}(n)(v/n)^{u_i}\le n^{-4+o(1)}. \tag{7.26}
\]

Here `u_i=(2/q+o(1))N` and `32^{-u_i}=n^{-10+o(1)}`.  In any order of
adding residual blocks, (7.6) is therefore below one for all sufficiently
large `n`; hence `B(h)<=1`.  Equations (5.19) and (7.5) give

\[
 D(k-h)\le e^{-c_Zk_{co}}.                               \tag{7.27}
\]

Summing `(k_co+1)^4` residual vectors proves an `o(1)` contribution.
Together with (7.11) and (7.25), this proves (7.7).  \(\square\)

## 8. Canonical high cells and dense endpoint transportation

Put

\[
 U=\alpha-2,\qquad R_0=\lfloor U/2\rfloor.                \tag{8.1}
\]

In every overlap matrix, the cells of multiplicity greater than `R_0`
form a matching: two such cells in one row or column would use more than
`U` stubs.  Let this canonical matching be

\[
 M=\{a_rb_r:1\le r\le h\},\qquad
 r_{a_rb_r}=j_r>R_0,\qquad J=\sum_rj_r.                  \tag{8.2}
\]

Selecting the exact stub pairs in these cells has incidence

\[
 \pi(M,j)=
 \frac{\prod_r(s_{a_r})_{j_r}(t_{b_r})_{j_r}}
      {(n)_J\prod_rj_r!}.                                \tag{8.3}
\]

Conditional on the exposed pairs, the remaining matching is a uniform
configuration model with total degree `n-J` and the residual row and
column degrees.  It is restricted to put no further pair in a cell of
`M` and no cell above `R_0`.  Multiplication of (8.3) by the exact
residual contingency-table law cancels to (6.2).  Thus every overlap
matrix occurs exactly once.

We first sum the bare high matching, postponing all local and topological
factors in the capped residual model.  Index the four sizes as

\[
 u_i=a-i,\qquad 0\le i\le3,\qquad a=\alpha-2.             \tag{8.4}
\]

For a typed full-containment matrix `L=(ell_ij)`, put

\[
 r_i=\sum_j\ell_{ij},\quad c_j=\sum_i\ell_{ij},\quad
 x_{ij}=\min(u_i,u_j),\quad J(L)=\sum_{ij}x_{ij}\ell_{ij}. \tag{8.5}
\]

Its exact incidence, including its local signed rewards but not residual
attachments, is

\[
 W(L)=
 \frac{\prod_i(k_i)_{r_i}\prod_j(k_j)_{c_j}}
      {\prod_{ij}\ell_{ij}!}\frac1{(n)_{J(L)}}
 \prod_{ij}\left[
  \frac{(u_i)_{x_{ij}}(u_j)_{x_{ij}}}{x_{ij}!}g(x_{ij})
 \right]^{\ell_{ij}}.                                   \tag{8.6}
\]

For a margin vector `r`, define

\[
 D(r)=
 \frac{\prod_i(k_i)_{r_i}^2}{\prod_i r_i!}
 \frac{\prod_i[u_i!g(u_i)]^{r_i}}{(n)_{m_r}},\qquad
 m_r=\sum_i u_ir_i.                                     \tag{8.7}
\]

This is exactly the common-subprofile weight (7.3).

### Lemma 8.1 (geometric-mean transportation comparison)

For every feasible `L`,

\[
 W(L)\le\sqrt{D(r)D(c)}
 \frac{\sqrt{\prod_i r_i!c_i!}}{\prod_{ij}\ell_{ij}!}
 \prod_{ij}Q_{ij}^{\ell_{ij}},                          \tag{8.8}
\]

where `Q_ii=1` and, if the two sizes are `t=s+d`,
`1<=d<=3`,

\[
 Q_{ij}=(n+1)^{d/2}\frac{\sqrt{(t)_d}}{d!}
       2^{-\{ds+\binom d2\}/2}
 \le\frac{\eta_n^d}{d!},                               \tag{8.9}
\]

with

\[
 \eta_n=2^{3/2}\sqrt{\frac{(n+1)a}{2^a}}
       =O(N^{3/2}/\sqrt n)=o(1).                         \tag{8.10}
\]

#### Proof

For integer `x`, let `f(x)=ln(n)_x` and interpolate linearly between
successive integers.  Its successive slopes are `ln(n-x)`, which decrease;
therefore `f` is concave, and every slope is at most `ln(n+1)`.  Moreover,

\[
 \frac{m_r+m_c}{2}
 =J(L)+\frac12\sum_{ij}|i-j|\ell_{ij}.                  \tag{8.11}
\]

Concavity and `f'(x)<=ln(n+1)` give

\[
 \frac{\sqrt{(n)_{m_r}(n)_{m_c}}}{(n)_{J(L)}}
 \le(n+1)^{\frac12\sum_{ij}|i-j|\ell_{ij}}.            \tag{8.12}
\]

For `t=s+d`, put `b_u=u!g(u)`.  A direct calculation gives

\[
 \frac{(t)_s(s)_s}{s!}g(s)=b_s\binom td,\qquad
 \frac{b_t}{b_s}=(t)_d2^{ds+\binom d2}.                 \tag{8.13}
\]

Thus the local factor divided by `sqrt(b_sb_t)` is

\[
 \frac{\sqrt{(t)_d}}{d!}2^{-\{ds+\binom d2\}/2}.        \tag{8.14}
\]

Dividing (8.6) by `sqrt(D(r)D(c))`, then using (8.12) and
(8.14), proves (8.8)--(8.9).  Finally `t<=a`, `s>=a-3`, and

\[
 2^a=\Theta(n^2/N^2)                                    \tag{8.15}
\]

uniformly in the phase.  This proves (8.10).  \(\square\)

### Lemma 8.2 (sum of all endpoint tables)

\[
 \sum_LW(L)\le
 \exp\{O(\sqrt{nN})+O(N)\}\sum_rD(r)
 =\exp\{O(\sqrt{nN})+O(N)\}.                            \tag{8.16}
\]

#### Proof

For fixed margins, write

\[
 A_L=\frac{\prod_i r_i!}{\prod_{ij}\ell_{ij}!},\qquad
 C_L=\frac{\prod_j c_j!}{\prod_{ij}\ell_{ij}!}.        \tag{8.17}
\]

Cauchy's inequality gives

\[
 \sum_L\sqrt{A_LC_L}\,Q^L
 \le\left(\sum_LA_LQ^L\right)^{1/2}
      \left(\sum_LC_LQ^L\right)^{1/2}.                 \tag{8.18}
\]

Dropping the column constraints in the first sum and the row constraints in
the second produces two exact multinomial expansions:

\[
 \sum_LA_LQ^L\le\prod_i\left(\sum_jQ_{ij}\right)^{r_i},
 \quad
 \sum_LC_LQ^L\le\prod_j\left(\sum_iQ_{ij}\right)^{c_j}.
                                                               \tag{8.19}
\]

Every row and column sum of `Q` is at most `1+C eta_n`, and the total
margin is at most `k_co`.  Hence the fixed-margin cost is
`exp(O(eta_n k_co))`.  There are only `O(k_co^4)` margin vectors, and

\[
 \left(\sum_r\sqrt{D(r)}\right)^2
 \le O(k_{co}^4)\sum_rD(r).                              \tag{8.20}
\]

Use Lemma 7.1 and `eta_n k_co=O(sqrt(nN))` to finish.  \(\square\)

### Lemma 8.3 (all nonendpoint high multiplicities)

The full-containment sum (8.16) remains
`exp(o(n/N^4))` after all high-cell multiplicities
`R_0<j<min(u_i,u_j)` are inserted.

#### Proof

Let the smaller slot size be `m`, the larger `m+d`, with `0<=d<=3`.
Replacing the endpoint multiplicity `m` by `m-e` has exact local ratio

\[
 R_{m,d}(e)=
 \frac{\binom me}{(d+1)\cdots(d+e)}
 2^{-em+e(e+1)/2}.                                      \tag{8.21}
\]

For many decorated cells, with total deficit `Q`, the ratio of the one
global denominators is

\[
 \frac{(n)_{J_0}}{(n)_{J_0-Q}}
 =(n-J_0+Q)_Q\le n^Q.                                   \tag{8.22}
\]

For `1<=e<m/4`, the consecutive ratio of the summands
`n^eR_{m,d}(e)` is

\[
 \frac{n(m-e)2^{-m+e+1}}{(e+1)(d+e+1)}.                 \tag{8.23}
\]

The ratio of (8.23) at `e+1` to its value at `e` is

\[
 2\frac{m-e-1}{m-e}\frac{e+1}{e+2}
  \frac{d+e+1}{d+e+2},                                  \tag{8.24}
\]

which increases for `e<=m/4` and `d<=3`.  Thus (8.23) is largest at
an endpoint.  At `e=0` it is `O(N^3/n)`, by (8.15), and at
`e=floor(m/4)` it is `n^{-1/2+o(1)}`.  The series therefore decreases
geometrically and

\[
 \sum_{1\le e<m/4}n^eR_{m,d}(e)=O(N^3/n).                \tag{8.25}
\]

The multinomial choices among identical typed cells turn this into a factor

\[
 (1+O(N^3/n))^{k_{co}}=\exp(O(N^2)).                     \tag{8.26}
\]

It remains to cover the middle strip, rather than silently importing an
equitable-profile estimate.  First expose a near-containment skeleton and
let `m_0` be its residual stub mass.  If `m_0>=n/N^6`, Lemma 6.2,
before dropping the matching constraints, bounds the entire remaining
middle-cell expansion by `exp(Xi_4)`, where

\[
 \Xi_4\le k_{co}^2
 \sum_{a/2<j\le3a/4+O(1)}
  g(j)\frac{(ea^2/m_0)^j}{j!}.                           \tag{8.27}
\]

Put `L=log_2 n` and `j=xL`.  Uniformly for
`1+o(1)<=x<=3/2+o(1)`,

\[
\begin{split}
 \log_2\left[k_{co}^2g(j)\frac{(ea^2/m_0)^j}{j!}\right]
 &\le2L+\frac{j^2}{2}-j\log_2m_0+O(j\log_2a)\\
 &\le-cL^2.                                              \tag{8.28}
\end{split}
\]

Indeed, the quadratic coefficient is `x^2/2-x<=-3/8+o(1)` on
this interval.  Hence `Xi_4=2^{-Omega(L^2)}`.

If instead `m_0<n/N^6`, leave the entire residual matching unexposed.
The near skeleton is a matching, so pointwise

\[
 \beta(M\cup H_{res})\le|E(H_{res})|\le m_0/2,
 \quad
 \sum_e\binom{r_e}{2}\le(a-1)m_0/2.                    \tag{8.29}
\]

All remaining local and topological factors together are therefore at most
`exp(O(am_0))=exp(O(n/N^5))`.  In particular, this also upper-bounds the
bare middle-cell sum.  Combining (8.16), (8.26), and the two branches gives

\[
 \sum_{\text{all high skeletons}}\text{bare weight}
 \le\exp\{O(\sqrt{nN})+O(N^2)+O(n/N^5)\}
 =\exp\{o(n/N^4)\}.                                     \tag{8.30}
\]

\(\square\)

## 9. All residual local and cycle attachments

Fix an actual canonical high skeleton `(M,j)` as in (8.2), and let
`m_0=n-J` be the residual total degree.  Its residual degrees are at most
`U`.  Define

\[
 \mathcal A(M,j)=\mathbb E_{res}\left[
  \left(\prod_e g(r'_e)\right)
  2^{\beta(M\cup H_{res})}\mathbf1_{\mathcal E(M,j)}
 \right],                                                \tag{9.1}
\]

where `E(M,j)` imposes the residual cap `r'_e<=R_0` and forbids a
further pair in a cell of `M`.  By (6.4), (8.3), and the exact conditional
law, the normalized moment is exactly

\[
 \sum_{(M,j)}\pi(M,j)\left(\prod_{e\in M}g(j_e)\right)
 \mathcal A(M,j).                                       \tag{9.2}
\]

### Lemma 9.1 (uniform attachment bound)

Uniformly over every canonical high skeleton,

\[
 \ln\mathcal A(M,j)=o(n/N^4).                            \tag{9.3}
\]

More precisely, it is `O(N^8)` when `m_0>=n/N^6` and
`O(n/N^5)` otherwise.

#### Proof: large residual degree

Suppose `m_0>=n/N^6`.  Since

\[
 U=(2+o(1))\log_2n,\qquad
 \log_2m_0=\log_2n-O(\log_2N),                           \tag{9.4}
\]

we have `U<3 log_2 m_0` for all sufficiently large `n`.  For a
residual cell outside `M`, put

\[
 \theta_{ab}=\frac{e d_ad'_b}{m_0},\quad
 \Delta_x=g(x)-g(x-1),                                  \tag{9.5}
\]

and

\[
 \lambda_{ab}=\sum_{x=3}^{R_0}\Delta_x
                    \frac{\theta_{ab}^x}{x!},\qquad
 q_{ab}=\frac{\theta_{ab}^2}{2}+\lambda_{ab}.            \tag{9.6}
\]

Set both quantities to zero on `M`.  Let
`theta_*=eU^2/m_0`.  The ratio of consecutive majorants
`g(x)theta_*^x/x!` is

\[
 \frac{2^x\theta_*}{x+1},                                \tag{9.7}
\]

and increases with `x`.  Hence the sequence is log-convex.  Its decreasing
head is dominated by the `x=3` term.  Consecutive values of (9.7) grow
by the factor `2(x+1)/(x+2)>=8/5`, so only `O(1)` transition terms can
have ratio between `1/2` and `1`.  Its increasing tail is dominated by its
right endpoint, and

\[
 \log_2\left(g(R_0)\frac{\theta_*^{R_0}}{R_0!}\right)
 \le\frac{R_0^2}{2}-R_0\log_2m_0+O(R_0\log_2U)
 =-\Omega(R_0\log n),                                   \tag{9.8}
\]

using `R_0=U/2` and (9.4).  Thus, uniformly in the cell,

\[
 \lambda_{ab}\le C\theta_{ab}^3,\qquad
 q_{ab}\le C\theta_{ab}^2.                              \tag{9.9}
\]

Expand each capped local factor as

\[
 g(r'_e)=1+\sum_{x=3}^{R_0}\Delta_x
                   \mathbf1_{\{r'_e\ge x\}}.            \tag{9.10}
\]

If an edge is selected in a fixed even subgraph, use instead

\[
 \mathbf1_{\{r'_e\ge2\}}g(r'_e)
 =\mathbf1_{\{r'_e\ge2\}}
  +\sum_{x=3}^{R_0}\Delta_x\mathbf1_{\{r'_e\ge x\}}.   \tag{9.11}
\]

The terms on the right of (9.11) are alternatives, so a triple cell is not
charged twice.  Fix an even subgraph in (6.7), expand (9.10)--(9.11), and
apply Lemma 6.2 jointly to all demanded cells.  Dropping the cap only after
this nonnegative expansion gives

\[
 \mathcal A(M,j)
 \le e^{\Lambda_0}
  \sum_{F\text{ even}}\prod_{e\in F\setminus M}q_e,\qquad
 \Lambda_0=\sum_e\lambda_e.                              \tag{9.12}
\]

The degree sums give

\[
 \Lambda_0\le\frac C{m_0^3}
   \left(\sum_a d_a^3\right)\left(\sum_b(d'_b)^3\right)
 \le C\frac{U^4}{m_0},                                  \tag{9.13}
\]

and

\[
 \max_a\sum_bq_{ab}\ \vee\ \max_b\sum_aq_{ab}
 \le C\frac{U^3}{m_0}=:\tau=o(1).                       \tag{9.14}
\]

Every even graph is a union of edge-disjoint simple cycles.  Choose one
such decomposition deterministically; dropping edge-disjointness gives

\[
 \sum_{F\text{ even}}\prod_{e\in F\setminus M}q_e
 \le\exp\left\{\sum_{C\text{ simple cycle}}
                  \prod_{e\in C\setminus M}q_e\right\}. \tag{9.15}
\]

For cycles disjoint from `M`, mark a row start and drop simplicity and the
closing constraint.  The weighted row and column sums are at most `tau`,
and a bipartite cycle has length at least four.  Hence

\[
 \sum_{C:C\cap M=\varnothing}\prod_{e\in C}q_e
 \le\frac{n\tau^4}{1-\tau^2}.                            \tag{9.16}
\]

For a cycle meeting `M`, mark and orient one matching edge.  There are at
most `2h` choices.  Cutting at all matching edges leaves nonempty residual
walks.  The residual-walk kernel has row-sum norm at most

\[
 b=\sum_{\ell\ge1}\tau^\ell=\frac\tau{1-\tau},          \tag{9.17}
\]

while traversal of the matching is a partial permutation of norm one.
Thus, if the relaxed cycle uses `r` matching edges, its total remaining
weight is at most `b^r`; there is no fresh factor `h` after the first marked
edge.  Therefore

\[
 \sum_{C:C\cap M\ne\varnothing}
       \prod_{e\in C\setminus M}q_e
 \le2h\sum_{r\ge1}b^r\le Ch\tau.                        \tag{9.18}
\]

Every high cell uses more than `U/2` stubs, so `h<2n/U`.  Combining
(9.12)--(9.18),

\[
 \ln\mathcal A(M,j)
 \le C\left\{\frac{U^4}{m_0}+n\tau^4+h\tau\right\}
 =O(N^8)                                                  \tag{9.19}
\]

at the cutoff `m_0>=n/N^6`.

#### Proof: small residual degree

Suppose `m_0<n/N^6`.  Since `M` is a matching, it is a forest, and
adding a residual support edge increases cycle rank by at most one.  Hence

\[
 \beta(M\cup H_{res})\le|E(H_{res})|\le m_0/2.           \tag{9.20}
\]

Also, pointwise,

\[
 \sum_e\binom{r'_e}{2}
 \le\frac{U-1}{2}\sum_er'_e=\frac{U-1}{2}m_0.           \tag{9.21}
\]

Equations (6.5), (9.20), and (9.21) bound the integrand in (9.1) by
`2^{Um_0/2}`.  Therefore

\[
 \ln\mathcal A(M,j)=O(Um_0)=O(n/N^5).                   \tag{9.22}
\]

Both (9.19) and (9.22) are `o(n/N^4)`.  \(\square\)

### Proposition 9.2 (normalized signed second moment)

For the exact midpoint profile,

\[
 \Lambda_n:=\ln\frac{\mathbb E(Z_{\mathbf k}^{sgn})^2}
                      {(\mathbb EZ_{\mathbf k}^{sgn})^2}
 =o(n/N^4).                                               \tag{9.23}
\]

#### Proof

Equation (9.2) is an exact canonical decomposition.  Lemma 8.3 sums all
bare high skeletons by `exp(o(n/N^4))`, including the empty skeleton,
all dense endpoint tables, every near-containment decoration, and the two
middle-strip regimes.  Lemma 9.1 bounds the conditional residual factor by
the same exponential scale uniformly over every skeleton.  Multiplication
proves the upper bound in (9.23).  The normalized second moment is at least
one by variance, so its logarithm is nonnegative and (9.23) follows.
\(\square\)

## 10. Rare-event amplification

Proposition 9.2 and (1.5) give the seed

\[
 \Pr\{Z_{\mathbf k}^{sgn}>0\}\ge e^{-\Lambda_n}.        \tag{10.1}
\]

By the observation after (5.19), this implies

\[
 \Pr\{\zeta(G_n)\le k_{co}\}\ge e^{-\Lambda_n}.        \tag{10.2}
\]

We now prove the amplification needed to turn this possibly rare event into
a typical one.

### Lemma 10.1 (simultaneous leftover colouring)

There is an absolute `C` such that, with probability `1-o(1)`, every
`U subseteq[n]` satisfies

\[
 \chi(G_n[U])\le C\frac{|U|}{N}+n^{1/3}.                 \tag{10.3}
\]

#### Proof

Let `H` be the complement of `G_n`.  Put `u_0=ceil(n^{1/4})`.
For any fixed `u_0`-set, (1.6) gives probability
`exp(-Omega(u_0^2))` that its `H`-edge density is below `1/4`.
There are at most `exp(u_0N)` such sets, so a union bound shows that, with
probability `1-o(1)`, every `u_0`-set has density at least `1/4`.
By averaging over its `u_0`-subsets, the same is then true of every larger
set.

Start with any vertex set of size at least `n^{1/3}`.  While its current
size is at least `u_0`, choose a vertex of maximum `H`-degree and replace
the current set by its `H`-neighbourhood there.  Density at least `1/4`
implies that this neighbourhood has size at least one quarter of the
current size, up to an additive one.  The chosen vertices form a clique in
`H`; before the current size falls from `n^{1/3}` to `n^{1/4}`, this
constructs at least `cN` vertices for an absolute `c>0`.  They are an
independent set in `G_n`.

For an arbitrary `U`, repeatedly remove such independent sets and give each
a new colour until fewer than `n^{1/3}` vertices remain; colour the rest
singly.  This proves (10.3) simultaneously for every `U`.  \(\square\)

### Lemma 10.2 (amplification from a seed)

Suppose deterministic `k_n,Lambda_n>=0` satisfy

\[
 \Pr\{\zeta(G_n)\le k_n\}\ge e^{-\Lambda_n}.             \tag{10.4}
\]

Then for every deterministic `r>0`,

\[
\begin{split}
 \Pr\Bigg\{\zeta(G_n)>k_n+C\bigg(
 &\frac{\sqrt{n\Lambda_n}+\sqrt{nr}}N
   +n^{1/3}+1\bigg)\Bigg\}\\
 &\le e^{-r}+o(1).                                       \tag{10.5}
\end{split}
\]

#### Proof

For an induced set `W`, let `zeta(W)=zeta(G_n[W])`, and define

\[
 S_k=\max\{|W|:\zeta(W)\le k_n\}.                       \tag{10.6}
\]

Expose the random graph in `n-1` independent vertex blocks, where block
`v` contains the edges from `v` to earlier vertices.  Changing one block
changes `S_k` by at most one: after deletion of the affected vertex, every
feasible induced set loses at most one vertex and the two configurations
agree on the remainder.  Therefore (1.4) applies.

Since `S_k=n` exactly when `zeta(G_n)<=k_n`, (10.4) and the upper
one-sided bounded-differences tail imply

\[
 n-\mathbb ES_k\le\sqrt{(n-1)\Lambda_n/2}.               \tag{10.7}
\]

The lower tail with radius `sqrt((n-1)r/2)` gives, except with probability
`e^{-r}`,

\[
 n-S_k\le
 \sqrt{(n-1)\Lambda_n/2}+\sqrt{(n-1)r/2}.                \tag{10.8}
\]

Choose a maximizing set `W` and put `U=[n]\setminus W`.  Concatenating a
`k_n`-part cocolouring of `G[W]` with an ordinary colouring of `G[U]`
gives

\[
 \zeta(G_n)\le k_n+\chi(G_n[U]).                         \tag{10.9}
\]

Intersect (10.8) with the simultaneous event in Lemma 10.1 and apply
(10.3).  This proves (10.5).  \(\square\)

Apply Lemma 10.2 to (10.2).  Put

\[
 B_n=\frac n{N^4},\qquad r_n=\sqrt{B_n}.                 \tag{10.10}
\]

Then `r_n->infinity`, and Proposition 9.2 gives

\[
 \frac{\sqrt{n\Lambda_n}}N=o(n/N^3),\qquad
 \frac{\sqrt{nr_n}}N=o(n/N^3),\qquad
 n^{1/3}=o(n/N^3).                                       \tag{10.11}
\]

Consequently

\[
 \Pr\left\{\zeta(G_n)
 \le k_{co}+o(n/N^3)\right\}\longrightarrow1.          \tag{10.12}
\]

The `o(n/N^3)` in (10.12) is a deterministic sequence.

## 11. Completion of the proof

Intersect the events (4.5) and (10.12).  No independence is required; a
union bound suffices.  Equation (5.20) then gives, with high probability,

\[
 \chi(G_n)-\zeta(G_n)
 \ge\left(\frac{q^2\gamma_4}{16}-o(1)\right)
        \frac n{N^3}.                                    \tag{11.1}
\]

For every sufficiently large `n`, the right side is at least

\[
 c_*\frac n{N^3},\qquad
 c_*:=\frac{q^2\gamma_4}{32}
 =\frac{(\ln2)^2}{32}\ln\frac{200}{153}>0.              \tag{11.2}
\]

This proves (0.1).  Since `n/(ln n)^3` tends to infinity, for every fixed
`M`,

\[
 \Pr\{\chi(G_n)-\zeta(G_n)\ge M\}\longrightarrow1.      \tag{11.3}
\]

Every estimate used above is uniform for `delta in [0,1)` and for the
exact tangent-rounded finite-`n` profile.  The conclusion therefore holds
along all sufficiently large integers, including sequences approaching
either side of every independence-number jump.  It is a high-probability
statement, not a density-subset or subsequence result.  \(\blacksquare\)

## 12. Dependency and provenance note

The proof is logically ordered as follows.  The elementary phase expansion
and exact first-moment variational calculation construct the midpoint
profile and prove its complete signed first-moment margin.  That margin and
elementary independence-set estimates prove the full partial-diagonal sum.
The partial-diagonal sum feeds the dense four-type transportation estimate.
Independently, the exact sign sum and the configuration model prove the
uniform residual-attachment estimate.  These two estimates combine only
after both are established, yielding the normalized second moment.
Paley--Zygmund and the proved leftover amplification are applied last.
Thus there is no circular use of a second-moment conclusion in the profile
construction.  In particular, no ordinary-colouring second-moment theorem
is invoked at the signed midpoint, where the ordinary first moment is
exponentially small.

For provenance only, the separate dossier files from which the arguments
were consolidated are `EXCEPTIONAL_REGIME.md`,
`ALPHA_MINUS_TWO_ROUTE.md`, `FOUR_SIZE_PARTIAL_RATES.md`,
`DENSE_FOUR_TYPE_MATCHING.md`, `SIGNED_PROFILE_OVERLAP.md`,
`RESIDUAL_ATTACHMENT.md`, and `ALON_CONCENTRATION_EXTENSION.md`.
No step of the proof above depends on those cross-references.
