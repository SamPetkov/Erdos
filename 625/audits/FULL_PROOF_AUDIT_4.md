# Fourth independent full-chain audit of `COMPLETE_PROOF_DRAFT.md`

## Hard verdict

**PASS.**  I treated every conclusion in the draft as unproved and rebuilt the
argument from the exact first-moment count, the exact signed overlap law, and
the exact configuration-model exposure.  I found no counterexample, missing
overlap family, reversed factorial inequality, phase-uniformity failure, or
unproved lemma in the current version of the proof chain.

In particular, the current component files support, for every sufficiently
large integer `n`,

\[
 \Pr\!\left\{\chi(G_{n,1/2})-\zeta(G_{n,1/2})
 \ge \frac{(\ln2)^2}{32}\ln\frac{200}{153}
          \frac{n}{(\ln n)^3}\right\}\longrightarrow1.
\]

This is an internal mathematical verdict on the files in this dossier.  It is
not external peer review, bibliographic verification, or a priority claim.

Throughout this audit I write

\[
 q=\ln2,\qquad N=\ln n,\qquad
 H_n=\frac n{N^3},\qquad B_n=\frac n{N^4}.
\]

## Proof-obligation table

| Proof obligation | Verdict | Independent reconstruction |
|---|---:|---|
| Uniform independence-number phase expansion | PASS | The exact adjacent-size ratios and the full-cycle expansion give `mu_{alpha+2}=n^{delta-2+o(1)}<=n^{-1+o(1)}` uniformly for `0<=delta<1`. |
| Unrestricted chromatic lower bound | PASS | Exact profile enumeration, `exp(O(N^2))` possible bounded profiles, and an `N`-colour shift below the continuous root give an `o(1)` first moment.  The independence-number cap removes the artificial size restriction. |
| Finite-`n` four-size optimizer | PASS | The exact finite weights have a Gaussian-dominated tail; the four-point optimizer converges uniformly to the limiting discrete Gaussian and all four masses are uniformly positive. |
| Four-size entropy certificate | PASS | The two explicit omitted-tail estimates give `D_4<ln(153/100)` and hence the fixed signed advantage `q-D_4>ln(200/153)`. |
| Root phase and root displacement | PASS | The roots have the same phase mean to `o(1)` and derivative `(2/q)N^2+O(N ln N)`; the coefficient is exactly `q^2(q-D_4)/4`. |
| Integer rounding and complete signed margin | PASS | The two constraint errors are corrected in the deficit-2 and deficit-3 coordinates by an `O(1)` tangent move; the exact logarithmic moment loses only `O(N)` and remains `Omega(n/N)`. |
| Ordered/unordered normalization | PASS | Labelling equal-size slots multiplies the witness by the deterministic factor `prod_i k_i!`, which cancels from the normalized second moment. |
| Exact sign-summed overlap factor | PASS | Compatible signs are constant on each component of the multiplicity-at-least-two graph, giving exactly `A_zeta=2^{W+c-v}=prod g(r_ab) 2^beta`. |
| Canonical high-cell decomposition | PASS | Cells above `floor(U/2)` form a matching.  The exposed incidence times the exact residual law cancels to the original contingency-table probability, with the cap and no-backtracking condition ensuring uniqueness. |
| Residual local increments | PASS | The joint factorial bound gives total triple activity `O(U^4/M)` and maximum weighted residual degree `O(U^3/M)` without multiplying marginal probabilities. |
| Residual even-subgraph cycles | PASS | Cycles disjoint from the high matching start at length four; cycles through arbitrarily many high cells are controlled by a residual-walk kernel and a norm-one partial permutation, with no `2^h` or `h^r` loss. |
| Small residual degree | PASS | Pointwise, `beta<=|E(H_res)|<=M/2` and the local exponent is at most `(U-1)M/2`, yielding `O(n/N^5)` at the cutoff. |
| Vanishing diagonal mass | PASS | The exact recurrence is dominated by a Poisson series whose total activity is `o(1)`, with the global falling factorial retained. |
| Central diagonal mass | PASS | The rate `Phi_T=R ln R+q(I_r-TR)/2` is strictly negative away from both corners by two analytic endpoint inequalities, including nongreedy fractional subprofiles. |
| Near-full diagonal mass | PASS | The exact complementary recurrence and the complete signed first-moment margin give exponential suppression. |
| Dense unequal-type transport | PASS | Concavity of `ln(n)_x` is used in the correct direction.  Cauchy followed by two exact multinomial expansions sums unequal margins, imbalance paths, and directed type cycles. |
| Near-containment decorations | PASS | The exact local ratio and one global denominator comparison give a total multiplier `exp(O(N^2))`. |
| Middle high cells, large residual branch | PASS | Their joint activity is `2^{-Omega((log_2 n)^2)}` when the remaining mass is at least `n/N^6`. |
| Middle high cells, small residual branch | PASS | All remaining local and topological factors are bounded together by `exp(O(n/N^5))`; no large-residual estimate is used below its cutoff. |
| Exhaustiveness and non-overcounting | PASS | Every multiplicity is either residual, near an endpoint, or in the middle high strip.  Exactness/matching restrictions are dropped only after the canonical identity and only to create nonnegative overcounts. |
| Full normalized second moment | PASS | The bare high sum and the uniform residual-attachment supremum both have logarithm `o(B_n)`, so the normalized moment does as well. |
| Rare-event amplification | PASS | The maximum `k`-cocolourable induced-set size is one-fibre Lipschitz; McDiarmid plus a simultaneous leftover-colouring lemma converts the Paley seed to a whp bound at cost `o(H_n)`. |
| Final constant and quantifiers | PASS | The midpoint leaves coefficient `q^2 gamma_4/16-o(1)` and the proof safely takes half.  Every estimate is uniform over the whole phase, so the result is all-`n`, not subsequential. |

## 1. Exact first moment and the unrestricted chromatic lower location

For an exact unordered profile `k=(k_u)`, direct counting gives

\[
 \mathbb E X_{\mathbf k}
 =\frac{n!}{\prod_u (u!)^{k_u}k_u!}
   2^{-\sum_u k_u\binom u2}.                              \tag{1.1}
\]

Uniform Stirling inequalities put its logarithm below the continuous
functional `L_k` up to `O(N^2)` in the one-sided support.  There are at most

\[
 (n+1)^{\alpha+1}=\exp\{O(N^2)\}
\]

integer profiles with all parts at most `alpha+1`.  Thus the total expected
number of such `k`-colourings is at most

\[
 \exp\{L_+(n,k)+O(N^2)\}.                                \tag{1.2}
\]

The exact ratio

\[
 \frac{\mu_{s+1}}{\mu_s}
 =\frac{n-s}{s+1}2^{-s}                                  \tag{1.3}
\]

is `Theta(N/n)` for `s=alpha,alpha+1`.  Together with the uniform phase
expansion `mu_alpha=n^{delta+O(ln N/N)}`, this gives

\[
 \mu_{\alpha+2}=n^{\delta-2+o(1)}
 \le n^{-1+o(1)}=o(1),                                   \tag{1.4}
\]

including sequences with `delta` tending to one.  Markov therefore gives
`Pr(alpha(G)>alpha+1)=o(1)`.

At the chromatic-window root,

\[
 \frac{\partial L_S}{\partial k}
 =\frac2qN^2+O(N\ln N)                                   \tag{1.5}
\]

uniformly for every support used in the proof and throughout an
`O(n/N^3)` window.  Moving down by `ceil(N)` colours lowers `L_+` by
`Theta(N^3)`, which dominates (1.2).  On the event in (1.4), every colouring
with at most `k_chi^-` colours can be refined to exactly `k_chi^-` nonempty
independent parts without increasing a part.  This proves the genuinely
unrestricted lower bound

\[
 \Pr\{\chi(G)\le k_\chi^-\}=o(1).                         \tag{1.6}
\]

## 2. Finite-`n` four-size optimizer and root displacement

The finite-weight convergence can be checked more sharply than a
fixed-coordinate appeal.  With `d_u=2^{binom(u,2)}u!`, remove the constant
and linear terms from `-ln d_{alpha-i}`.  For `i>=0` the remaining exact
weight is

\[
 h_n(i)=-\frac q2i^2+
         \ln\frac{(\alpha)_i}{\alpha^i}
 \le-\frac q2i^2,                                        \tag{2.1}
\]

while `h_n(-1)=-q/2+ln(alpha/(alpha+1))`.  Thus the growing one-sided tail is
uniformly Gaussian-dominated, not merely convergent at each fixed deficit.
For the four fixed coordinates,

\[
 h_n(i)=-\frac q2i^2+O(1/\alpha)                         \tag{2.2}
\]

uniformly in the phase.

The exact continuous finite-`n` optimizer therefore has weights

\[
 p_i^{(n)}=
 \frac{\exp\{\mu_ni+h_n(i)\}}
      {\sum_{j\in S_4}\exp\{\mu_nj+h_n(j)\}},           \tag{2.3}
\]

and strict monotonicity of the tilted mean gives
`mu_n=mu(T)+o(1)` and `p_i^(n)=p_i(T)+o(1)` uniformly.  The limiting tilt
satisfies

\[
 2q<\mu(T)<\frac92q.                                     \tag{2.4}
\]

Consequently all four proportions exceed `1/92` for large `n`, uniformly
through the cycle.

I rechecked the four omitted-tail inequalities used in the dual estimate:

\[
 L(2q)<0.51,\quad H(3q)<0.02,\quad
 L(3q)<0.12,\quad H(9q/2)<0.25.                          \tag{2.5}
\]

Splitting at `mu=3q` makes the omitted-to-retained ratio less than `0.53`
or `0.37`, respectively.  Hence

\[
 0\le D_4(\delta)<\ln(1.53),\qquad
 q-D_4(\delta)>\gamma_4:=\ln\frac{200}{153}.             \tag{2.6}
\]

Writing `s=n/k`, the root equation gives, uniformly,

\[
 s=\alpha_0-1-\frac2q+O\!\left(\frac{\ln N}{N}\right),
 \qquad
 T=1+\frac2q-\delta+O\!\left(\frac{\ln N}{N}\right).  \tag{2.7}
\]

At the unrestricted root,

\[
 L_{S_4}(n,r_+)+qr_+
 =r_+\{q-D_4(\delta)+o(1)\}.                             \tag{2.8}
\]

Using (1.5), `r_+=(q/2+o(1))n/N`, and the mean-value theorem gives the
coefficient with no missing factor of `q` or two:

\[
 r_+-r_4^{co}
 =\left[\frac{q^2}{4}\{q-D_4(\delta)\}+o(1)\right]H_n.  \tag{2.9}
\]

The uniform margin (2.6) implies the safe finite-`n` inequality

\[
 r_+-r_4^{co}\ge\frac{q^2\gamma_4}{8}H_n                \tag{2.10}
\]

for every sufficiently large integer `n`.

At the integer midpoint, rounding `kp_i^(n)` and correcting the two
constraint errors by

\[
 \Delta k_2=e_1-3e_0,\qquad
 \Delta k_3=2e_0-e_1                                    \tag{2.11}
\]

changes only `O(1)` counts and is tangent to both constraints.  Whether one
phrases the continuous optimizer as the exact `L`-optimizer with exact `u!`
weights or as the gamma-extended exact-moment optimizer changes only the
already allowed `O(N)` Stirling error.  It does not affect (2.9), the
rounding, or the uniform complete signed margin

\[
 \ln\mathbb E Z_{\mathbf k}^{sgn}\ge c_ZK=\Omega(n/N)   \tag{2.12}
\]

for a fixed phase-independent `c_Z>0`.

## 3. Exact signed normalization

For two independent uniform ordered partitions of the same slot profile,
the overlap law is exactly

\[
 p(r)=\frac{\prod_a s_a!\prod_b t_b!}
            {n!\prod_{a,b}r_{ab}!}.                      \tag{3.1}
\]

Let `H` be the bipartite graph of cells with `r_ab>=2`, let
`W=sum_ab binom(r_ab,2)`, and omit isolated slot vertices when defining
`v=|V(H)|` and `c=c(H)`.  A pair of part signs is compatible exactly when
the signs agree along every edge of `H`.  There are

\[
 2^{2K-v+c}
\]

compatible sign pairs: two choices per nonempty component and independent
choices on all isolated slots.  The duplicated graph constraints save
exactly `W` fair bits.  Dividing by the two first moments therefore gives

\[
 A_\zeta(r)=2^{W+c-v}.                                    \tag{3.2}
\]

Since `beta=|E|-|V|+c`, this is equivalently

\[
 A_\zeta(r)=\left(\prod_{a,b}g(r_{ab})\right)2^{\beta(H)},
 \quad
 g(0)=g(1)=g(2)=1,\quad
 g(x)=2^{\binom x2-1}\ (x\ge3).                         \tag{3.3}
\]

The factor `2^beta` is exactly the number of even subgraphs of `H`.  In
particular, a double-cell forest has factor one; charging two per double cell
would be the ordinary-colouring normalization and is wrong.

Temporarily labelling slots of equal size multiplies the unordered witness
by the deterministic factor `prod_i k_i!`.  It multiplies its first moment
by the same factor and its second moment by the square, so (3.2)--(3.3) are
unchanged.  Thus

\[
 \frac{\mathbb E Z^2}{(\mathbb EZ)^2}
 =\sum_rp(r)A_\zeta(r)                                   \tag{3.4}
\]

with no ordered/unordered or sign-assignment discrepancy.

## 4. Canonical high cells and residual even subgraphs

Put `U=alpha-2` and `R=floor(U/2)`.  Two cells larger than `R` cannot share
a row or column because `2(R+1)>U`.  They therefore form a canonical
matching `M`.  If their exact multiplicities are `j_e` and
`J=sum_e j_e`, their exposed incidence is

\[
 \pi(M,\mathbf j)=
 \frac{\prod_{ab\in M}(s_a)_{j_{ab}}(t_b)_{j_{ab}}}
      {(n)_J\prod_{ab\in M}j_{ab}!}.                     \tag{4.1}
\]

For a fixed exposed stub realization, the remaining matching is the exact
uniform configuration model on the residual degrees.  If its matrix is
`r'` and `M_0=n-J`, direct cancellation gives

\[
 \pi(M,\mathbf j)
 \frac{\prod_a d_a!\prod_b d'_b!}
      {M_0!\prod_{ab}r'_{ab}!}
 =\frac{\prod_a s_a!\prod_b t_b!}
       {n!\prod_{ab}r_{ab}!}.                            \tag{4.2}
\]

The no-backtracking condition in the exposed cells and the cap `r'<=R`
make the representation canonical.  Formula (4.2) also clarifies the only
wording subtlety: exposed stub pairs are unique for each stub matching, not
for an overlap matrix; after summing stub realizations, every overlap matrix
still has exactly its probability (3.1).

In the large-residual regime, `M_0>=n/N^6`, the joint threshold expansion
gives

\[
 \Lambda_{loc}=O(U^4/M_0),\qquad
 \tau=O(U^3/M_0),                                       \tag{4.3}
\]

where `tau` bounds every weighted row and column degree.  Cycles disjoint
from `M` have total walk weight `O(n tau^4)`.  For a cycle meeting `M`, cut
at all matching edges.  The residual-walk kernel has row-sum norm at most
`tau`, while traversal of `M` is a partial permutation of norm one.  Marking
one oriented matching edge costs `2h`, but later matching edges are
determined by residual-walk endpoints.  Summing all numbers and lengths of
segments costs `O(h tau)`, not `2^h` or `h^r`.  At the cutoff all terms have
logarithm `O(N^8)=o(B_n)`.

If `M_0<n/N^6`, pointwise

\[
 \beta(M\cup H_{res})\le |E(H_{res})|\le M_0/2,
 \qquad
 \sum_e\binom{r'_e}{2}\le\frac{U-1}{2}M_0.             \tag{4.4}
\]

Thus every residual local factor and every cycle factor together cost at
most

\[
 \exp\{O(UM_0)\}=\exp\{O(n/N^5)\}=\exp\{o(B_n)\}.       \tag{4.5}
\]

This covers four-cycles with two high edges, cycles using one high edge and
a three-edge residual path, cycles through arbitrarily many high cells,
intersecting cycles, and triple cells lying on those paths.

## 5. Diagonal endpoints

For a common selected vector `ell`, with selected mass `m`, exact factorial
cancellation gives

\[
 A_{\boldsymbol\ell}
 =\frac{\prod_i\binom{k_i}{\ell_i}^2}
        {Y_{\boldsymbol\ell}^{sgn}},                      \tag{5.1}
\]

and the exact recurrence

\[
 \frac{A_{\boldsymbol\ell+e_i}}{A_{\boldsymbol\ell}}
 =\frac{(k_i-\ell_i)^2}
        {2(\ell_i+1)\mu_{u_i}(n-m)}.                     \tag{5.2}
\]

At the empty corner the total initial activity is

\[
 \sum_i\frac{k_i^2}{2\mu_{u_i}(n)}
 =O\!\left(N^{-(2/q-1/2)}\right)=o(1).                  \tag{5.3}
\]

The exact recurrence, including the finite-population factor, is dominated
by a Poisson series through selected mass `(ln N)n/(32N)`, and its nonempty
sum is `o(1)`.

For central mass, let `y_i=ell_i/K`, `z_i=p_i-y_i`,
`Y=sum y_i`, `R=1-Y`, and `I_r=sum i z_i`.  The leading rate extracted from
the exact factorials is

\[
 \Phi_T(\mathbf z)=R\ln R+\frac q2(I_r-TR).              \tag{5.4}
\]

Every fractional, nongreedy subprofile obeys both

\[
 \Phi_T\le R\left\{\ln R+\frac q2(5-T)\right\},
 \qquad
 \Phi_T\le R\ln R+\frac q2(T-2)(1-R).                  \tag{5.5}
\]

The first is uniformly negative for `R<=0.47`; the second is uniformly
negative for `R>=0.47` except at `R=1`.  The fixed rational slack survives
the actual `o(1)` enlargement of the phase interval.  The lower-order error
`O(KY ln(e/Y)+N)` is too small to change the sign at the moving cutoff.

At the full corner, write `r=k-ell`, let `v` be its vertex mass, and define
`B_r` by

\[
 A_{k-r}=\frac{B_r}{Z_k^{sgn}},\qquad
 \frac{B_{r+e_i}}{B_r}
 =\frac{2(k_i-r_i)\mu_{u_i}(v+u_i)}{(r_i+1)^2}.          \tag{5.6}
\]

For `v<=n/32`, uniformly in phase,

\[
 \mu_{u_i}(v)\le\mu_{u_i}(n)(v/n)^{u_i}
 \le n^{-4+o(1)},                                       \tag{5.7}
\]

so every ratio in (5.6) is less than one.  Hence `B_r<=1`, while
`Z_k^sgn>=exp(c_ZK)`.  The polynomial number of residual vectors remains
exponentially negligible.  The three ranges prove

\[
 \sum_rD(r)=1+o(1).                                      \tag{5.8}
\]

## 6. Dense four-type transport and the exhaustive high-cell split

For a typed full-containment matrix `L=(ell_ij)`, with margins `r,c`, put
`x_ij=min(u_i,u_j)` and `J=sum x_ij ell_ij`.  Direct slot and stub counting
gives

\[
 W(L)=
 \frac{\prod_i(k_i)_{r_i}\prod_j(k_j)_{c_j}}
      {\prod_{ij}\ell_{ij}!}\frac1{(n)_J}
 \prod_{ij}\left[
  \frac{(u_i)_{x_{ij}}(u_j)_{x_{ij}}}{x_{ij}!}g(x_{ij})
 \right]^{\ell_{ij}}.                                   \tag{6.1}
\]

For a diagonal vector,

\[
 D(r)=\frac{\prod_i(k_i)_{r_i}^2}{\prod_i r_i!}
       \frac{\prod_i[u_i!g(u_i)]^{r_i}}{(n)_{m_r}}.      \tag{6.2}
\]

Dividing (6.1) by `sqrt(D(r)D(c))` before approximating anything leaves one
global falling-factorial quotient.  If
`f(x)=ln(n)_x`, concavity gives the required direction

\[
 \frac{\sqrt{(n)_{m_r}(n)_{m_c}}}{(n)_J}
 \le(n+1)^{\frac12\sum_{ij}|i-j|\ell_{ij}}.              \tag{6.3}
\]

For a size difference `d`, exact local cancellation gives

\[
 Q_{ij}=(n+1)^{d/2}\frac{\sqrt{(t)_d}}{d!}
 2^{-\{ds+\binom d2\}/2}
 \le\frac1{d!}\left(C\frac{N^{3/2}}{\sqrt n}\right)^d. \tag{6.4}
\]

For fixed margins, Cauchy's inequality separates the row and column
multinomial coefficients.  Dropping the opposite constraints then gives two
exact multinomial expansions.  Summing all margins and using (5.8) yields

\[
 \sum_LW(L)
 \le\exp\{O(\sqrt{nN})+O(N)\}\sum_rD(r)
 =\exp\{O(\sqrt{nN})+O(N)\}.                             \tag{6.5}
\]

This sums unequal margins, imbalance paths, and all directed type cycles; it
does not assert false pointwise diagonal maximality.

If a cell between sizes `m` and `m+d` is lowered from full containment to
`m-e`, its exact local ratio is

\[
 \frac{\binom me}{(d+1)\cdots(d+e)}
 2^{-em+e(e+1)/2}.                                       \tag{6.6}
\]

Only after retaining the global denominator is its change bounded by

\[
 \frac{(n)_{J_0}}{(n)_{J_0-Q}}\le n^Q.                  \tag{6.7}
\]

The resulting sum for `1<=e<m/4` is `O(N^3/n)` per endpoint cell, hence all
near-containment decorations multiply (6.5) by only `exp(O(N^2))`.

The ranges are exhaustive.  An actual high cell has multiplicity `x>R`.
With `e=m-x`, either

- `e<m/4`, which is the endpoint/near-endpoint range just summed; or
- `e>=m/4`, equivalently `R<x<=3m/4`, up to the harmless `O(1)` changes
  among the four adjacent sizes, which is the middle high strip.

After the near skeleton is exposed, let its actual remaining stub mass be
`M_0`.  If `M_0>=n/N^6`, the joint prescribed-cell bound gives

\[
 \Xi_4(M_0)
 \le K^2\sum_{a/2<j\le3a/4+O(1)}
 g(j)\frac{(ea^2/M_0)^j}{j!}
 =2^{-\Omega((\log_2n)^2)}.                              \tag{6.8}
\]

If `M_0<n/N^6`, one does not apply (6.8).  Instead, sum the conditional
residual probability first and use the deterministic inequalities (4.4) on
everything that remains.  This includes all middle high cells, all capped
cells, and their topology, at cost `exp(O(n/N^5))`.  Thus both residual-mass
branches cover every near and middle configuration.

Consequently the entire bare canonical high-skeleton sum is bounded by

\[
 \exp\left\{O(\sqrt{nN})+O(N^2)+O(n/N^5)\right\}
 =\exp\{o(B_n)\}.                                        \tag{6.9}
\]

## 7. Second moment and rare-event amplification

Multiplying (6.9) by the uniform residual-attachment supremum from Section 4
inside the exact canonical decomposition gives

\[
 R_n:=\frac{\mathbb E Z^2}{(\mathbb EZ)^2}
 \le\exp\{o(B_n)\}.                                     \tag{7.1}
\]

Since `R_n>=1`,

\[
 \Lambda_n:=\ln R_n\ge0,\qquad \Lambda_n=o(B_n).        \tag{7.2}
\]

Paley--Zygmund gives

\[
 \Pr\{Z>0\}\ge R_n^{-1}=e^{-\Lambda_n},                \tag{7.3}
\]

and `Z>0` implies `zeta(G)<=k_co`.

For completeness, define

\[
 S_k=\max\{|W|:\zeta(G[W])\le k_{co}\}.                \tag{7.4}
\]

Expose independent oriented vertex fibres.  Changing one fibre changes only
edges incident with its endpoint, so deleting that vertex shows that `S_k`
changes by at most one.  From `Pr(S_k=n)>=e^{-Lambda_n}`, the upper
McDiarmid tail forces

\[
 n-\mathbb ES_k\le\sqrt{(n-1)\Lambda_n/2}.               \tag{7.5}
\]

A lower tail with parameter `r>0` leaves at most
`O(sqrt(n Lambda_n)+sqrt(nr))` vertices uncovered outside probability
`e^{-r}`.  On one simultaneous graph event, every induced leftover `U` can
be ordinarily coloured with

\[
 O(|U|/N+n^{1/3})                                       \tag{7.6}
\]

colours; an ordinary colouring is also a cocolouring.  No independence of
the adaptively selected leftover is needed.

Take `r_n=sqrt(B_n)`.  Then `r_n->infinity` and

\[
 \frac{\sqrt{n\Lambda_n}/N}{H_n}
 =\sqrt{\frac{\Lambda_n}{B_n}}=o(1),\qquad
 \frac{\sqrt{nr_n}/N}{H_n}=\frac N{n^{1/4}}=o(1),
 \qquad
 \frac{n^{1/3}}{H_n}=o(1).                               \tag{7.7}
\]

Therefore

\[
 \Pr\{\zeta(G)\le k_{co}+o(H_n)\}\longrightarrow1.    \tag{7.8}
\]

## 8. Adversarial counterexample search

The following were the strongest attempted failure modes.

1. **Right edge of an independence-number phase.**  Taking
   `delta=1-o(1)` does not leave an `alpha+2` independent set: (1.4) remains
   at most `n^{-1+o(1)}`.  The four-point tilt and its omitted-tail constants
   stay in fixed compact intervals.
2. **A sparse off-diagonal type cycle beats every diagonal.**  Individual
   off-diagonal matrices can indeed be larger than a chosen diagonal term.
   This is not a counterexample because (6.3)--(6.5) compare with the
   geometric mean of two endpoint diagonals and sum all transportation
   matrices jointly.
3. **The global factorial reverses near full mass.**  Direct division gives
   (6.3) in the displayed direction.  Reversing it would be fatal, but
   concavity of `ln(n)_x` proves exactly the direction used.
4. **The full diagonal escapes the central rate.**  It is deliberately not
   handled by the central approximation.  The exact complementary recurrence
   (5.6) and the `exp(Omega(K))` complete signed moment suppress it.
5. **Many high cells create an uncharged even-subgraph factor.**  A high
   matching alone is a forest.  A high edge enters an even subgraph only via
   residual paths, and the norm-one partial-permutation calculation charges
   every such cycle without a hidden `2^h` or `h^r`.
6. **Cells just above `U/2` fall between the near and residual ranges.**  They
   are precisely the middle range in (6.8).  The separate small-residual
   branch covers the case in which the activity estimate (6.8) is unavailable.
7. **Ordered slots or incompatible signs add a factorial or `2^K`.**  The
   deterministic ordering factor cancels, while incompatible signs have
   probability zero before normalization.  Equations (3.2)--(3.4) retain the
   correct factor.

As a transcription diagnostic only, I also evaluated 20,000 randomly
generated finite four-type transportation matrices.  The exact logarithmic
quotient agreed with the expression preceding (6.3) to floating-point
precision, and no instance violated the falling-factorial inequality.  This
finite check is not used as proof.

No attempted family supplies a counterexample or exposes a missing lemma.

## 9. Final constant, dependencies, and quantifiers

The safe root gap (2.10), the midpoint, the `O(N)` chromatic shift, and
integer rounding give

\[
 k_\chi^- - k_{co}
 \ge\left(\frac{q^2\gamma_4}{16}-o(1)\right)H_n.         \tag{9.1}
\]

The amplification error in (7.8) is `o(H_n)`.  Taking half the remaining
coefficient gives

\[
 c_*=
 \frac{q^2\gamma_4}{32}
 =\frac{(\ln2)^2}{32}\ln\frac{200}{153}
 =0.004021983962242005\ldots>0.                           \tag{9.2}
\]

Every input to the conclusion is uniform for `delta in [0,1)` and for the
exact tangent-rounded integer profile.  The dependency chain is acyclic:
the first moment constructs the profile and its complete signed margin; that
margin proves the diagonal bound; the diagonal bound feeds the dense
transport sum; the independent residual theorem completes the overlap sum;
and only then are Paley--Zygmund and rare-event amplification used.

Thus the proof covers every sufficiently large integer `n`, including
arbitrary sequences approaching both sides of every independence-number
jump.  Since `H_n->infinity`, it also proves the fixed-`M` formulation of
Erdős Problem 625.

