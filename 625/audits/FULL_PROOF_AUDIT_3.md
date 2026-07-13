# Third independent full-chain audit of `COMPLETE_PROOF_DRAFT.md`

> **Historical-scope notice (2026-07-13).** This document preserves the
> internal 2026-07-12 verdict on the draft and component bytes then under
> review. It is not a review of the later repaired or synchronized bytes.
> The authoritative proof is now `../proofs/COMPLETE_PROOF_SELF_CONTAINED.md`;
> see `ADVERSARIAL_LEAP_AUDIT_2026-07-13.md` for the later defects and
> regression checks, and `PROOF_COMPONENT_SYNCHRONIZATION_AUDIT_2026-07-13.md`
> for the mapping from that canonical proof to the synchronized component
> notes. The original audit body and verdict below are retained unchanged.

## Hard verdict

**PASS.**  I independently reconstructed the claimed proof, in a different
order from the draft, and found no counterexample, missing uniformity, or
uncovered overlap family.  In particular, the proof does establish, for
every sufficiently large integer `n`,

\[
 \Pr\!\left(\chi(G_{n,1/2})-\zeta(G_{n,1/2})
       \ge c_*\frac{n}{(\ln n)^3}\right)\longrightarrow1,
 \qquad
 c_*:=\frac{(\ln2)^2}{32}\ln\frac{200}{153}.
\]

Numerically,

\[
 \boxed{c_*=0.004021983962242005\ldots>0.}
\]

There are **no blocking corrections**.  Two points that would have been
blockers in an earlier presentation are explicit in the current files:

1. the integer four-size profile is obtained from the exact finite-`n`
   constrained optimizer before tangent rounding, rather than by asserting
   an `O(\ln n)` loss for a merely limiting optimizer; and
2. the middle high-cell range has separate large- and small-residual
   branches, the latter costing `exp{O(n/(ln n)^5)}` rather than being
   described as exponentially small.

The word **PASS** is mathematical, not bibliographic: it means that the
displayed theorem follows from the component arguments in this dossier.  It
does not assert journal review or external validation.

## 1. Audit contract and notation

I treated each of the following as a separate proof obligation and did not
use the conclusion of one to justify an earlier one:

1. the unrestricted independence-number cap and chromatic first-moment
   lower bound;
2. the phase-uniform variational comparison between the unrestricted and
   four-size supports;
3. the root displacement, exact integer profile, and explicit constant;
4. the exact sign-summed overlap factor;
5. a disjoint exhaustive classification of all overlap multiplicities;
6. the diagonal, off-diagonal endpoint, near-endpoint, middle, and residual
   sums, with the one global falling factorial retained;
7. the Paley--Zygmund seed exponent;
8. rare-event Alon--Scott amplification; and
9. the all-`n`, rather than subsequential, probability quantifier.

Write throughout

\[
 q=\ln2,\qquad N=\ln n,\qquad
 H_n=\frac n{N^3},\qquad B_n=\frac n{N^4}.
\]

The fractional independence-number phase is

\[
 \alpha_0=\frac2q\{N-\ln N+1+\ln q-q\}+1,
 \quad \alpha=\lfloor\alpha_0\rfloor,
 \quad \delta=\alpha_0-\alpha\in[0,1).
\]

Every `o(1)` used below is uniform in this complete phase interval.

## 2. Independence-number cap and unrestricted chromatic lower bound

The uniform expansion in `EXCEPTIONAL_REGIME.md` is

\[
 \ln\mu_\alpha
 =\delta N+\left(\frac2q-\frac12-\delta\right)\ln N
   +K(\delta)+O\!\left(\frac{(\ln N)^2}{N}\right).
 \tag{2.1}
\]

In particular, `mu_alpha=n^{delta+o(1)}` uniformly.  The exact adjacent
ratio

\[
 \frac{\mu_{t+1}}{\mu_t}
 =\frac{n-t}{t+1}2^{-t}
 \tag{2.2}
\]

is `Theta(N/n)` for `t=alpha,alpha+1`.  Therefore

\[
 \mu_{\alpha+2}
 =\mu_\alpha\,O(N^2/n^2)
 =n^{\delta-2+o(1)}\le n^{-1+o(1)}=o(1)                  \tag{2.3}
\]

even at the right endpoint of a cycle.  Markov then gives

\[
 \Pr\{\alpha(G)>\alpha+1\}=o(1).                         \tag{2.4}
\]

I also reconstructed the continuous first-moment scale rather than taking
the location formula as a premise.  Put `s=n/k` and `T=alpha-s`.  For a
deficit profile `p=(p_i)` of bounded mean, uniform Stirling expansion gives

\[
 \frac{L_S(n,k)}k
 =(s-1)\left(N-\ln s-\frac q2s\right)
   +1-\frac12\ln(2\pi s)
   +\mathcal F_S(T)+\frac q2T^2+o(1).                    \tag{2.5}
\]

For `S_+={-1,0,1,...}`, the exact finite-`n` weights are uniformly
log-concave with Gaussian tails, so (2.5) also holds for the one-sided
support.  At its zero this implies

\[
 s=\alpha_0-1-\frac2q+o(1),\qquad
 T=1+\frac2q-\delta+o(1),                                \tag{2.6}
\]

and differentiation at the constrained optimum gives

\[
 \frac{\partial L_S}{\partial k}
 =\left(\frac2q+o(1)\right)N^2.                          \tag{2.7}
\]

These estimates are insensitive to an `O(H_n)` displacement of `k`: that
changes `s` by only `O(1/N)`.

Let `r_+` be the `S_+` zero and

\[
 k_\chi^-:=\lfloor r_+\rfloor-\lceil N\rceil.
\]

There are only `exp(O(N^2))` integer profiles with all parts at most
`alpha+1`, and uniform Stirling error contributes another `O(N^2)` in the
logarithm.  Moving `N` colours below `r_+` lowers `L_+` by
`Theta(N^3)`.  Hence the expected total number of such bounded colourings
at `k_chi^-` is `o(1)`.  On (2.4), any colouring with at most `k_chi^-`
parts can be refined to exactly that many nonempty parts, still of size at
most `alpha+1`.  Thus

\[
 \Pr\{\chi(G)\le k_\chi^-\}=o(1).                        \tag{2.8}
\]

This is an unrestricted chromatic lower bound; no artificial cap remains
in the conclusion.

## 3. Phase-uniform four-size advantage and root displacement

For

\[
 S_4=\{2,3,4,5\},\qquad T(\delta)=1+2/q-\delta,
\]

define

\[
 \mathcal F_S(T)=\max_p\left\{-\sum p_i\ln p_i
                   -\frac q2\sum i^2p_i\right\}.
\]

The optimizer has weights proportional to
`exp(mu i-q i^2/2)`.  I checked the analytic certificate in
`ALPHA_MINUS_TWO_ROUTE.md` directly.  Its tilt lies between `2q` and
`9q/2`.  With `L(mu)` and `H(mu)` denoting respectively the omitted low and
high mass relative to the four retained terms, the two cases are

\[
 \begin{array}{c|c}
 \mu\le3q & L(\mu)+H(\mu)<51/100+1/50=53/100,\\
 \mu\ge3q & L(\mu)+H(\mu)<3/25+1/4=37/100.
 \end{array}
\]

Evaluating the unrestricted dual function at the four-point tilt therefore
gives, uniformly for the entire compact phase interval,

\[
 0\le D_4(\delta):=\mathcal F_{S_+}(T)-\mathcal F_{S_4}(T)
 <\ln(153/100),                                           \tag{3.1}
\]

and hence

\[
 q-D_4(\delta)>\gamma_4,qquad
 \gamma_4:=\ln(200/153)=0.26787944515560125\ldots .       \tag{3.2}
\]

The finite-`n` profile functionals converge uniformly because their second
differences are `-q+O(1/N)` on every fixed deficit window and their tilted
tails are Gaussian.  Linear terms cancel when supports with the same mean
are compared.  At `k=r_+`, therefore,

\[
 L_{S_4}(n,r_+)+q r_+
 =r_+\{q-D_4(\delta)+o(1)\}.                              \tag{3.3}
\]

Using (2.7), `r_+=(q/2+o(1))n/N`, and the mean-value theorem gives the
independently reconstructed displacement

\[
 r_+-r_4^{co}
 =\left(\frac{q^2}{4}\{q-D_4(\delta)\}+o(1)\right)H_n.   \tag{3.4}
\]

Thus for every sufficiently large `n`, not just on a subsequence,

\[
 r_+-r_4^{co}\ge \frac{q^2\gamma_4}{8}H_n.              \tag{3.5}
\]

Take

\[
 k_{co}=\left\lceil\frac{r_4^{co}+r_+}{2}\right\rceil.
\]

The exact finite-`n` four-size constrained optimizer converges uniformly to
the four-point Gaussian, whose four masses have a fixed positive lower
bound.  Rounding its four counts and correcting the two integer constraints
in the deficit-2 and deficit-3 coordinates changes `O(1)` counts.  The
correction is tangent to the exact constrained optimum, and the five
Stirling errors are only `O(ln n)`.  This supplies an exact integer profile

\[
 (k_2,k_3,k_4,k_5),\qquad k_i=\Theta(n/N),qquad
 \sum k_i=k_{co},\quad\sum(\alpha-i)k_i=n,                \tag{3.6}
\]

with

\[
 \ln\mathbb E Z_{\mathbf k}^{sgn}=\Theta(n/N)            \tag{3.7}
\]

and a phase-uniform positive lower constant.  Since every part has size at
least `alpha-5>=2` for large `n`, its independent and clique declarations
are disjoint.  Finally,

\[
 k_\chi^- -k_{co}
 \ge\left(\frac{q^2\gamma_4}{16}-o(1)\right)H_n.         \tag{3.8}
\]

The `O(N)` chromatic shift, `O(1)` midpoint rounding, and `O(ln n)` profile
error are all negligible on the `H_n` scale.

## 4. Exact signed overlap factor

Label slots temporarily; this multiplies the unordered witness by the
constant `prod_i k_i!` and therefore does not change its normalized second
moment.  For two uniform ordered partitions let `r_ab` be the intersection
matrix and let `H` be the simple bipartite graph of cells with `r_ab>=2`.
Write

\[
 W=\sum_{ab}\binom{r_{ab}}2,qquad v=|V(H)|,qquad c=c(H).
\]

The `v` nonisolated slot signs must be constant on each of the `c`
components; all isolated signs remain free.  Thus the number of compatible
sign pairs, divided by the `2^{2k}` sign pairs already present in the two
first moments, is `2^{c-v}`.  Every shared edge constraint has been counted
twice in the denominator but once jointly, giving `2^W`.  Therefore the
exact normalized factor is

\[
 A_\zeta(r)=2^{W+c-v}.                                    \tag{4.1}
\]

Writing

\[
 g(0)=g(1)=g(2)=1,\qquad
 g(x)=2^{\binom x2-1}\quad(x\ge3),
\]

and `beta(H)=|E|-|V|+c`, this is equivalently

\[
 A_\zeta(r)=\left(\prod_{ab}g(r_{ab})\right)2^{\beta(H)}, \tag{4.2}
\]

where `2^beta` is exactly the number of even subgraphs.  Consequently

\[
 \frac{\mathbb E Z^2}{(\mathbb EZ)^2}
 =\sum_r p(r)A_\zeta(r),                                 \tag{4.3}
\]

with `p(r)` the exact bipartite configuration-model law.  No incompatible
sign pair has been assigned a positive contribution.

## 5. Exhaustive overlap partition and absence of double counting

Put `a=alpha-2`, `U=a`, and `R=floor(U/2)`.  Cells of multiplicity greater
than `R` form a matching, because two such cells cannot share a slot of
degree at most `U`.  For every overlap matrix, expose exactly this canonical
matching, including its exact stub pairs.  If its multiplicities sum to
`J`, its incidence is

\[
 \pi(M,\mathbf j)
 =\frac{\prod_{ab\in M}(s_a)_{j_{ab}}(t_b)_{j_{ab}}}
        {(n)_J\prod_{ab\in M}j_{ab}!}.                   \tag{5.1}
\]

Conditional on those pairs, the remaining stubs form a uniform
configuration model of total degree `n-J`.  Multiplying (5.1) by its exact
residual law cancels to the original contingency-table probability.  The
no-backtracking and residual-cap conditions make the decomposition unique
at the overlap-matrix level; at the stub level, (5.1) sums every realization
once.  Hence this is a genuine partition before any upper bound is taken.

The multiplicity ranges are exhaustive:

1. `0,1,2,...,R` are residual.  Multiplicities `3,...,R` enter through all
   threshold increments of `g`, while double cells enter through the exact
   even-subgraph expansion.  Zero and one are neutral.
2. For a high cell between slot sizes `m` and `m+d`, `0<=d<=3`, either
   `r=m-e` with `e<m/4` (the endpoint/near-endpoint range), or
   `R<r<=3m/4` (the middle range).  Boundary equalities can be assigned to
   the middle range.  Since `m in {a-3,...,a}`, the `O(1)` endpoint changes
   in the displayed middle interval do not leave a gap.

The later endpoint and threshold expansions sometimes drop exactness or a
matching restriction.  That creates only nonnegative overcount **after**
the canonical partition and therefore cannot omit or cancel a term.

## 6. Residual cells and all cycles through high cells

For a fixed canonical high matching, `RESIDUAL_ATTACHMENT.md` expands every
local threshold and the even-subgraph count jointly.  In the large-residual
regime `n-J>=n/N^6`, the prescribed-cell factorial bound gives

\[
 \Lambda_{loc}=O(U^4/(n-J)),\qquad
 \tau=O(U^3/(n-J))                                       \tag{6.1}
\]

for the total triple increment and maximum weighted residual degree.
Cycles disjoint from the high matching cost `O(n tau^4)`.  For cycles
meeting it, cutting at matching edges produces nonempty residual walks.
The matching is a partial permutation of row-sum norm one, so after one of
its `h` edges is marked the later matching edges are determined by walk
endpoints.  The cost is `O(h tau)`, not `2^h`, `h^r`, or a product of
marginal attachment probabilities.  Since `h<2n/U`, all three terms are
`O(N^8)` at the worst cutoff.

If `n-J<n/N^6`, pointwise

\[
 \beta(M\cup H_{res})\le |E(H_{res})|\le(n-J)/2,
\]

and

\[
 \sum_e\binom{r_e}{2}\le\frac{U-1}{2}(n-J).
\]

Thus all residual local and topological factors together cost at most
`exp{O(n/N^5)}`.  Uniformly over every high skeleton,

\[
 \ln\mathcal A_{res}=o(B_n).                             \tag{6.2}
\]

This explicitly includes four-cycles using two high cells, a high cell plus
a three-edge residual path, cycles through arbitrarily many high cells,
intersecting cycles, and triple cells on those paths.

## 7. Dense endpoints, all off-diagonal flows, and the middle strip

Reindex the four sizes as `u_i=a-i`, `0<=i<=3`.  A full-containment endpoint
matrix `L=(ell_ij)` has exact bare weight

\[
 W(L)=
 \frac{\prod_i(k_i)_{r_i}\prod_j(k_j)_{c_j}}
      {\prod_{ij}\ell_{ij}!}\frac1{(n)_J}
 \prod_{ij}\left[
  \frac{(u_i)_{x_{ij}}(u_j)_{x_{ij}}}{x_{ij}!}g(x_{ij})
 \right]^{\ell_{ij}},                                    \tag{7.1}
\]

where `x_ij=min(u_i,u_j)`.  For a diagonal vector `r`, put

\[
 D(r)=\frac{\prod_i(k_i)_{r_i}^2}{\prod_i r_i!}
       \frac{\prod_i[u_i!g(u_i)]^{r_i}}{(n)_{m_r}}.       \tag{7.2}
\]

Direct division, before any approximation, gives

\[
 W(L)\le\sqrt{D(r)D(c)}
 \frac{\sqrt{\prod_i r_i!c_i!}}{\prod_{ij}\ell_{ij}!}
 \prod_{ij}Q_{ij}^{\ell_{ij}},                           \tag{7.3}
\]

with `Q_ii=1` and

\[
 Q_{ij}\le\frac1{|i-j|!}
 \left(C\frac{N^{3/2}}{\sqrt n}\right)^{|i-j|}.         \tag{7.4}
\]

The critical finite-population direction is correct: concavity of
`f(x)=ln(n)_x` gives

\[
 \frac{\sqrt{(n)_{m_r}(n)_{m_c}}}{(n)_J}
 \le(n+1)^{\frac12\sum|i-j|\ell_{ij}}.                  \tag{7.5}
\]

This factor is exactly absorbed into (7.4).  Cauchy followed by a row
multinomial sum and a column multinomial sum works for unequal margins and
yields

\[
 \sum_LW(L)
 \le e^{O(\sqrt{nN})+O(N)}\sum_rD(r).                    \tag{7.6}
\]

I separately checked the three diagonal ranges.  Exact common-block
recurrences give `o(1)` for nonempty vanishing selected mass.  The central
rate

\[
 \Phi_T(z)=R\ln R+\frac q2(I_r-TR)
\]

obeys both

\[
 \Phi_T\le R\{\ln R+q(5-T)/2\},\qquad
 \Phi_T\le R\ln R+q(T-2)(1-R)/2.                        \tag{7.7}
\]

These are uniformly strictly negative away from the empty and full
corners, including an `o(1)` enlargement of the exact phase interval.  At
the near-full corner, the complement identity divides by the complete
signed moment (3.7); exact residual recurrences or the residual first-moment
bound give `exp(-Omega(n/N))`.  Consequently

\[
 \sum_rD(r)=1+o(1).                                      \tag{7.8}
\]

For a near-containment `m-e` in sizes `m,m+d`, direct cancellation gives

\[
 \frac{\binom me}{(d+1)\cdots(d+e)}
  2^{-em+e(e+1)/2}.                                     \tag{7.9}
\]

Only after retaining the joint denominator is its change bounded by
`n^e`.  The resulting sum per endpoint cell is `O(N^3/n)`, so all
decorations multiply (7.6) by `exp(O(N^2))`.

For the complementary middle high cells, after the near-endpoint skeleton
is exposed let the remaining degree be `M_0`.  If `M_0>=n/N^6`, their full
joint activity is bounded by

\[
 \exp\!\left\{K^2\sum_{a/2<j\le3a/4+O(1)}
      g(j)\frac{(ea^2/M_0)^j}{j!}\right\}.             \tag{7.10}
\]

For `j=x log_2 n`, `x in [1+o(1),3/2+o(1)]`, the base-two logarithm of
each summand has leading coefficient

\[
 \left(\frac{x^2}{2}-x\right)(\log_2n)^2
 \le-\left(\frac38-o(1)\right)(\log_2n)^2.              \tag{7.11}
\]

If `M_0<n/N^6`, the deterministic local-plus-topological bound costs
`exp(O(aM_0))=exp(O(n/N^5))`.  Hence every high multiplicity, every typed
off-diagonal flow, all partial diagonals, all near-containments, and both
middle branches satisfy

\[
 \sum_{\text{high skeletons}}\text{bare weight}
 \le\exp\{O(\sqrt{nN})+O(N^2)+O(n/N^5)\}
 =\exp\{o(B_n)\}.                                       \tag{7.12}
\]

There is no double count in the proof identity: (7.12) is an upper sum over
the exact canonical skeletons from Section 5.  Dropping transportation or
exactness constraints occurs only inside its upper bounds.

## 8. Seed exponent

Combining (6.2), (7.12), and the exact canonical decomposition gives

\[
 R_n:=\frac{\mathbb E Z^2}{(\mathbb EZ)^2}
 \le\exp\{o(B_n)\}.                                     \tag{8.1}
\]

Since `R_n>=1` by Cauchy--Schwarz,

\[
 \Lambda_n:=\ln R_n=o(B_n),\qquad \Lambda_n\ge0.         \tag{8.2}
\]

Paley--Zygmund applied to the nonnegative integer witness gives

\[
 \Pr\{Z>0\}\ge R_n^{-1}=e^{-\Lambda_n}.                 \tag{8.3}
\]

The event `Z>0` is exactly sufficient for a cocolouring with `k_co` parts,
so

\[
 \Pr\{\zeta(G)\le k_{co}\}\ge e^{-\Lambda_n}.          \tag{8.4}
\]

This is the required rare seed.  No bounded-second-moment or
positive-constant-probability claim is being substituted for it.

## 9. Rare-event amplification and its scale

For `T=zeta`, let

\[
 S=\max\{|W|:\zeta(G[W])\le k_{co}\}.
\]

Changing one vertex exposure block changes `S` by at most one: after the
affected vertex is deleted, the two induced graphs agree.  Since
`Pr(S=n)>=e^{-Lambda_n}`, the upper McDiarmid tail forces

\[
 n-\mathbb ES\le\sqrt{(n-1)\Lambda_n/2}.                 \tag{9.1}
\]

The lower tail with radius `sqrt((n-1)r/2)` then leaves at most the sum of
these two radii uncovered outside probability `e^{-r}`.  Simultaneously,
every induced set can be ordinarily coloured using

\[
 O(|U|/N+n^{1/3})
\]

colours; appending this ordinary colouring to a cocolouring is valid.  Thus

\[
 \zeta(G)\le k_{co}
 +O\!\left(\frac{\sqrt{n\Lambda_n}+\sqrt{nr}}N+n^{1/3}\right)
\]

outside probability `e^{-r}+o(1)`.

Choose `r=sqrt(B_n)`.  Then `r->infinity`, and each normalized error tends
to zero:

\[
 \frac{\sqrt{n\Lambda_n}/N}{H_n}
 =\sqrt{\frac{\Lambda_n}{B_n}}=o(1),                    \tag{9.2}
\]

\[
 \frac{\sqrt{nr}/N}{H_n}
 =\frac{N}{n^{1/4}}=o(1),\qquad
 \frac{n^{1/3}}{H_n}=\frac{N^3}{n^{2/3}}=o(1).           \tag{9.3}
\]

Therefore

\[
 \Pr\{\zeta(G)\le k_{co}+o(H_n)\}\longrightarrow1.     \tag{9.4}
\]

## 10. Constant and all-`n` quantifier

Intersect (2.8) and (9.4); independence is neither needed nor claimed.
Using (3.8), with high probability,

\[
 \chi(G)-\zeta(G)
 \ge\left(\frac{q^2\gamma_4}{16}-o(1)\right)H_n.         \tag{10.1}
\]

Taking half of the surviving coefficient gives the advertised safe
constant

\[
 c_*=\frac{q^2\gamma_4}{32}
 =\frac{(\ln2)^2}{32}\ln\frac{200}{153}
 =0.004021983962242005\ldots .                            \tag{10.2}
\]

All ingredients used to reach (10.1) are uniform in `delta in [0,1)`:

- the `mu_alpha` expansion and the `alpha+2` cap;
- the one-sided and four-point variational limits;
- the fixed rational entropy margin `gamma_4`;
- the exact finite-`n` optimizer and four-coordinate rounding;
- the four-type endpoint estimates;
- both residual-mass branches; and
- the deterministic concentration theorem.

No hypothesis keeps `delta` a fixed distance from zero or one.  Hence the
argument applies to every sufficiently large integer `n`, including
arbitrary sequences approaching either side of every independence-number
jump.  Finally, `H_n=n/(ln n)^3->infinity`, so (10.1) implies for every
fixed `M`

\[
 \Pr\{\chi(G_n)-\zeta(G_n)\ge M\}\longrightarrow1.
\]

## 11. Adversarial failure-mode checklist

| Attempted failure mode | Audit result |
|---|---|
| An independent set of size `alpha+2` survives near a phase endpoint | Fails: its expectation is uniformly `n^{-1+o(1)}`. |
| The four-size entropy loss reaches the sign bonus `ln 2` | Fails: the analytic bound leaves the fixed margin `ln(200/153)`. |
| Limiting-profile rounding consumes the `n/N^3` gap | Fails in the current construction: rounding starts at the exact finite-`n` optimizer and costs `O(ln n)`. |
| An incompatible pair of part signs receives positive second-moment weight | Fails: compatibility is imposed componentwise and gives exactly `2^{W+c-v}`. |
| Dense off-diagonal transport is assumed pointwise below a diagonal | Fails as an objection: the proof uses a geometric mean and joint Cauchy--multinomial sum, not pointwise diagonal maximality. |
| A family of cycles through many high cells creates a `2^h` or `h^r` factor | Fails: the high matching is a partial permutation; only residual paths carry weight. |
| Cells just above `U/2` are omitted between the endpoint and bounded ranges | Fails: they are precisely the middle high range. |
| The large-residual middle estimate is used below its cutoff | Fails in the current proof: the separate deterministic `O(n/N^5)` branch covers that range. |
| The full or near-full diagonal escapes the rate inequality | Fails: exact complement recurrences and the `exp(Omega(n/N))` complete signed moment suppress it. |
| Paley--Zygmund supplies too rare a seed for the desired gap | Fails: `Lambda=o(n/N^4)` is exactly the Alon--Scott budget for `H_n=n/N^3`. |
| The result holds only on a density-one set or subsequence | Fails: every error term is phase-uniform, and the final probability limit is over all integers. |

**Final audit verdict: PASS, with no mathematical blocker found.**
