# The `(alpha-2)`-bounded signed route

**Status.**  The first-moment comparison in this note is proved uniformly
through the whole phase `delta={alpha_0} in [0,1)`.  It gives a deterministic
separation of order `n/(ln n)^3` between a valid lower first-moment location
for the unrestricted chromatic number and the signed first-moment location
of an `(alpha-2)`-bounded cocolouring.  A fixed four-size version, using only
class sizes

\[
 \alpha-2,\quad \alpha-3,\quad \alpha-4,\quad \alpha-5,       \tag{0.1}
\]

also retains a uniform signed advantage.  The latter has only four slot
types and is the cleaner overlap candidate.

This note supplies the first-moment half of the argument.  The published
tame-colouring second moment cannot be invoked at the signed threshold
because the ordinary first moment is `exp{-Theta(n/ln n)}`.  Section 8
therefore isolates the high-matching lemma that was missing when this note
was written.  That lemma is now proved in
`DENSE_FOUR_TYPE_MATCHING.md`, Corollary 6.2, and the completed chain is
assembled in `COMPLETE_PROOF_DRAFT.md`.

Throughout,

\[
 q=\ln2,\qquad N=\ln n,\qquad
 \alpha_0=\alpha+\delta,\quad \alpha=\lfloor\alpha_0\rfloor,
 \quad 0\le\delta<1.                                      \tag{0.2}
\]

All logarithms in formulas below are natural unless a base is displayed.

## 1. The finite and limiting variational problems

Write a class size as `u=alpha-i`; thus `i` is its deficit from `alpha`.
At chromatic scale the mean deficit is

\[
 T(\delta)=1+\frac2q-\delta,
 \qquad \frac2q\le T(\delta)\le1+\frac2q.                 \tag{1.1}
\]

The endpoints are

\[
 \frac2q=2.885390\ldots,
 \qquad 1+\frac2q=3.885390\ldots.                         \tag{1.2}
\]

For a set of allowed deficits `S`, define

\[
 \mathcal F_S(T)=
 \max\left\{
  -\sum_{i\in S}p_i\ln p_i-\frac q2\sum_{i\in S}i^2p_i:
  \sum p_i=1,\ \sum ip_i=T
 \right\}.                                                \tag{1.3}
\]

If

\[
 Z_S(\mu)=\sum_{i\in S}e^{\mu i-qi^2/2},                 \tag{1.4}
\]

then the unique optimizer is

\[
 p_i=\frac{e^{\mu i-qi^2/2}}{Z_S(\mu)},qquad
 \frac{Z_S'(\mu)}{Z_S(\mu)}=T,                            \tag{1.5}
\]

and

\[
 \mathcal F_S(T)=\ln Z_S(\mu)-\mu T.                     \tag{1.6}
\]

The three supports used below are

\[
 S_+=\{-1,0,1,2,\ldots\},\qquad
 S_2=\{2,3,\ldots\},\qquad
 S_4=\{2,3,4,5\}.                                         \tag{1.7}
\]

`S_+` allows class sizes at most `alpha+1`; `S_2` is
`(alpha-2)`-bounded; `S_4` is the four-type restriction (0.1).

### Exact connection with `L_0`

Recall

\[
 d_u=2^{\binom u2}u!,\qquad
 L_{\mathbf k}=n\ln n-n+k-\sum_u k_u\ln(k_ud_u).          \tag{1.8}
\]

The identity used in the tame-colourings paper is

\[
 -\ln d_{\alpha-i}=h_n(i)+C_ni+f_n,                       \tag{1.9}
\]

where, uniformly for every fixed `i`,

\[
 h_n(i)=-\frac q2i^2+o(1).                                \tag{1.10}
\]

For fixed `n,k`, the mean deficit `T_n=alpha-n/k` is fixed.
Consequently the terms `C_n E i+f_n` cancel when two supports are
compared.  If `L_S(n,k)` denotes the continuous optimum in (1.8) with
deficits restricted to `S`, then, exactly at finite `n`,

\[
 \frac{L_R(n,k)-L_S(n,k)}k
 =\mathcal F_{n,R}(T_n)-\mathcal F_{n,S}(T_n),             \tag{1.11}
\]

where `mathcal F_{n,S}` is (1.3) with `-qi^2/2` replaced by
`h_n(i)` and with the natural finite upper cutoff.  The Gaussian tail in
`h_n`, bounded tilts, and compactness of the interval (1.1) give, uniformly
in the phase,

\[
 \mathcal F_{n,R}(T_n)-\mathcal F_{n,S}(T_n)
 =\mathcal F_R(T(\delta))-\mathcal F_S(T(\delta))+o(1)     \tag{1.12}
\]

whenever `k` differs by `O(n/N^3)` from a chromatic first-moment root.
One may first center at the known `(alpha-2)` first-moment root, for which
`n/k=alpha_0-1-2/q+o(1)`, and then use the derivative estimate in Section 5
to justify this window.  Thus (1.12) does not assume the conclusion it is
used to prove.

## 2. Forbidding deficits `-1,0,1` costs less than `ln 2`

Define the limiting loss

\[
 D_2(\delta)=
 \mathcal F_{S_+}(T(\delta))-\mathcal F_{S_2}(T(\delta)).  \tag{2.1}
\]

It is nonnegative because `S_2` is a subset of `S_+`.

### Proposition 2.1 (analytic uniform margin)

For every `0<=delta<=1`,

\[
 \boxed{0\le D_2(\delta)<\ln(3/2)},\qquad
 \boxed{q-D_2(\delta)>\ln(4/3)}.                           \tag{2.2}
\]

#### Proof

Let `mu_2` be the tilt in (1.5) for `S_2`.  First we show

\[
 \mu_2>2q.                                                 \tag{2.3}
\]

At `mu=2q`, put `j=i-2`.  The `S_2` weights are proportional to
`2^{-j^2/2}`, `j>=0`.  Their mean deficit is

\[
 2+\frac{\sum_{j\ge0}j2^{-j^2/2}}
          {\sum_{j\ge0}2^{-j^2/2}}<2+\frac45.             \tag{2.4}
\]

Here is a wholly elementary bound for (2.4).  The denominator is at least
`1+2^{-1/2}+1/4`.  For the numerator, the terms with `j=1,2,3` are
`2^{-1/2},1/2,3/(16 sqrt 2)`.  Starting at `j=4`, consecutive terms have
ratio at most `1/16`, so their sum is at most `1/60`.  Substitution, even
using only `2^{-1/2}<1`, proves the ratio is less than `4/5`.
Also

\[
 \frac23<q<\frac57,                                       \tag{2.5}
\]

for example from the positive `atanh` series for `ln 2`; hence
`2+4/5<2/q`, the smallest target mean in (1.1).  Since the tilted mean is
strictly increasing in `mu`, (2.3) follows.

Use the variational representation (1.6), but evaluate the `S_+` dual
function at `mu_2`.  This gives

\[
 D_2(\delta)
 \le \ln\left(1+
 \frac{\sum_{i=-1}^1e^{\mu_2i-qi^2/2}}
      {\sum_{i\ge2}e^{\mu_2i-qi^2/2}}
 \right).                                                  \tag{2.6}
\]

The ratio in (2.6) is strictly decreasing in `mu`: the logarithmic
derivative of its numerator is a mean at most `1`, while that of its
denominator is a mean at least `2`.  It is therefore at most its value at
`2q`.  Put `a=2^{-1/2}`.  After removing a common factor, its numerator is

\[
 A=a+\frac14+\frac a{16},                                  \tag{2.7}
\]

whereas its denominator is

\[
 B=\sum_{j\ge0}2^{-j^2/2}.
\]

The first five denominator terms give

\[
 B\ge1+a+\frac14+\frac a{16}+\frac1{256}=1+A+\frac1{256}.
\]

Moreover `A<257/256`, since this is equivalent to
`272/sqrt 2<193`, whose square is
`73984<74498`.  Hence `B>2A`, the ratio in (2.6) is less than `1/2`, and
(2.2) follows.  \(\square\)

The 1001-point diagnostic in the accompanying script gives

\[
 \max_{0\le\delta\le1}D_2(\delta)
 \approx0.1668401366,qquad
 \min(q-D_2)\approx0.5263070440.                           \tag{2.8}
\]

These decimals are not used in Proposition 2.1.

## 3. A fixed four-type profile also keeps a uniform advantage

Define

\[
 D_4(\delta)=
 \mathcal F_{S_+}(T(\delta))-\mathcal F_{S_4}(T(\delta)).  \tag{3.1}
\]

The interval (1.1) lies uniformly inside `(2,5)`, so the optimizer on
`S_4` exists, is unique, and all four masses are bounded away from zero
uniformly in the phase.

### Proposition 3.1 (four-type analytic certificate)

For every `0<=delta<=1`,

\[
 \boxed{0\le D_4(\delta)<\ln(153/100)},\qquad
 \boxed{q-D_4(\delta)>\gamma_4:=\ln(200/153)}.             \tag{3.2}
\]

Numerically,

\[
 \gamma_4=0.2678794451\ldots.                              \tag{3.3}
\]

#### Proof

Let `mu_4` be the `S_4` tilt.  At `mu=2q`, its mean is no larger than the
mean in (2.4), hence is below `2/q`.  At `mu=9q/2`, write
`t=2^{-1/8}`.  The four weights are proportional to

\[
 t^{25},\quad t^9,\quad t,\quad t.                         \tag{3.4}
\]

Their mean is larger than `4`, because

\[
 t-t^9-2t^{25}=t(1-t^8-2t^{24})=t/4>0.                   \tag{3.5}
\]

By (2.5), `1+2/q<4`.  Monotonicity of the tilted mean therefore gives

\[
 2q<\mu_4<\frac92q.                                       \tag{3.6}
\]

Let

\[
 L(\mu)=\frac{\sum_{i=-1}^1e^{\mu i-qi^2/2}}
                    {\sum_{i=2}^5e^{\mu i-qi^2/2}},
 \qquad
 H(\mu)=\frac{\sum_{i\ge6}e^{\mu i-qi^2/2}}
                    {\sum_{i=2}^5e^{\mu i-qi^2/2}}.       \tag{3.7}
\]

`L` is decreasing and `H` is increasing.  Direct elementary tail bounds
give

\[
 L(2q)<\frac{51}{100},\quad H(3q)<\frac1{50},\quad
 L(3q)<\frac3{25},\quad H(9q/2)<\frac14.                  \tag{3.8}
\]

For completeness, at `2q` the low ratio is

\[
 \frac{a+1/4+a/16}{1+a+1/4+a/16}<51/100,
 \qquad a=2^{-1/2};                                       \tag{3.9}
\]

`a<71/100` is already enough.  At `3q`, after centering at `i=3`, the
denominator is `5/4+2a`; the high numerator is
`a/16+1/256+R`, with `R<1/3968`, and the low numerator is
`1/256+a/16+1/4`.  These prove the two middle inequalities in (3.8), using
`7/10<a<71/100`.

For the last inequality in (3.8), (3.4) gives

\[
 H(9q/2)=\frac{t^9+t^{25}+R'}{2t+t^9+t^{25}}.
\]

After division by `t`, `R'/t` begins with `t^48=1/64` and subsequent
ratios are at most `1/16`, so `R'/t<1/60`.  Therefore

\[
 3(t^8+t^{24})+4R'/t
 <\frac{15}{8}+\frac1{15}<2,                              \tag{3.10}
\]

which is exactly `4H(9q/2)<1`.

If `mu_4<=3q`, (3.8) yields `L+H<53/100`; if `mu_4>=3q`, it yields
`L+H<37/100`.  Evaluating the `S_+` dual function at `mu_4`, as in (2.6),
now gives

\[
 D_4(\delta)\le\ln(1+L(\mu_4)+H(\mu_4))
 <\ln(153/100).                                            \tag{3.11}
\]

Subtracting from `q=ln2` proves (3.2).  \(\square\)

The numerical diagnostic gives the much stronger, but non-rigorous-for-
the-proof, values

\[
 \max_{0\le\delta\le1}D_4(\delta)
 \approx0.1724458451,qquad
 \min(q-D_4)\approx0.5207013355.                           \tag{3.12}
\]

The minimum loss on the same grid is about `0.0902167045`, near
`delta=0.385`.  Thus no grid assertion is being disguised as the analytic
certificate (3.2).

## 4. Integer four-type profiles

Let `k` be in the chromatic window and put

\[
 D=\alpha k-n.
\]

The four counts must satisfy

\[
 k_2+k_3+k_4+k_5=k,qquad
 2k_2+3k_3+4k_4+5k_5=D.                                   \tag{4.1}
\]

Let `p_i^{(n)}` be the exact finite-`n` maximizer of `L_{S_4}(n,k)`, with
the exact factorial weights from (1.8).  By (1.12) and strict concavity,
`p_i^{(n)}` converges uniformly in the phase to the limiting optimizer
(1.5).  Since `D/k=T(delta)+o(1)` lies in a compact subinterval of `(2,5)`,
we therefore have `p_i^{(n)}>=c_*>0` for all four `i`, uniformly in the
phase.  Round each `kp_i^{(n)}` to an integer.  If the two constraint errors
are `e_0,e_1=O(1)`, correct them in the `i=2,3` coordinates using

\[
 \Delta k_2=e_1-3e_0,qquad
 \Delta k_3=2e_0-e_1.                                     \tag{4.2}
\]

This changes every count by `O(1)`, preserves nonnegativity for large `n`,
and enforces (4.1) exactly.

Because the correction is tangent to both constraints and starts at the
exact finite-`n` constrained optimizer, the first variation of `L` vanishes.
The Hessian contribution is `O(1/k)`.  Applying Stirling
to the five factorials `n!,k_2!,...,k_5!` therefore gives an integer profile
`mathbf k^(4)` with

\[
 \ln\mathbb E\bar X_{\mathbf k^{(4)}}
 =L_{S_4}(n,k)+O(\ln n).                                   \tag{4.3}
\]

Every part has size at least `alpha-5`, so there are no singleton-label
ambiguities.  For signed cocolourings,

\[
 \ln\mathbb E\bar X^{\rm co}_{\mathbf k^{(4)}}
 =L_{S_4}(n,k)+qk+O(\ln n).                                \tag{4.4}
\]

Thus the finite-support restriction has no hidden integer loss on the
`n/N` first-moment scale or the `n/N^3` threshold scale.

## 5. Translation to an explicit `n/(ln n)^3` threshold gap

Let `r_+(n)` be the real root

\[
 L_{S_+}(n,r_+)=0,                                        \tag{5.1}
\]

and let `r_S^{co}(n)` be the real signed root

\[
 L_S(n,r_S^{co})+qr_S^{co}=0,\qquad S\in\{S_2,S_4\}.      \tag{5.2}
\]

All these roots lie within `O(n/N^3)` of the ordinary `(alpha-2)` root.
The envelope calculation behind Corollary 39 of the tame-colourings paper
applies equally to any of the supports above: their deficit tilts are
bounded, and

\[
 \frac{\partial}{\partial k}L_S(n,k)
 =\frac2qN^2+O(N\ln N)                                    \tag{5.3}
\]

uniformly in that window.  For a fixed finite support this also follows
directly by differentiating (1.8): the original size tilt is
`alpha q+ln alpha+O(1)`, and substitution in the envelope derivative gives
`2N^2/q+O(N ln N)`.

At `k=r_+`, (1.11)--(1.12) give

\[
 L_S(n,r_+)+qr_+
 =r_+\{q-D_S(\delta)+o(1)\}.                               \tag{5.4}
\]

Also

\[
 r_+=\left(\frac q2+o(1)\right)\frac nN.                 \tag{5.5}
\]

The mean value theorem and (5.3)--(5.5) yield the phase-resolved formula

\[
 \boxed{
 r_+-r_S^{co}
 =\left(\frac{q^2}{4}\{q-D_S(\delta)\}+o(1)\right)
   \frac n{N^3}.}                                         \tag{5.6}
\]

In particular, Proposition 2.1 gives

\[
 r_+-r_{S_2}^{co}
 \ge\left(\frac{q^2\ln(4/3)}4-o(1)\right)\frac n{N^3},   \tag{5.7}
\]

and Proposition 3.1 gives

\[
 r_+-r_{S_4}^{co}
 \ge\left(\frac{q^2\ln(200/153)}4-o(1)\right)
       \frac n{N^3}.                                      \tag{5.8}
\]

Therefore the following fully explicit constants are valid for all
sufficiently large `n`:

\[
 \begin{array}{c|c}
 S_2 & c_2=\dfrac{q^2\ln(4/3)}8=0.0172772148\ldots\\[6pt]
 S_4 & c_4=\dfrac{q^2\ln(200/153)}8=0.0160879358\ldots
 \end{array}                                               \tag{5.9}
\]

That is, `r_+-r_S^{co}>=c_S n/(ln n)^3` for all large `n`.

## 6. Why `r_+` is a valid lower location for unrestricted `chi`

Two points are needed: exclusion of larger independent sets and the finite
first-moment error.

First,

\[
 \mu_{\alpha+2}
 =\mu_\alpha
   \prod_{j=0}^1
   \frac{n-\alpha-j}{\alpha+j+1}2^{-(\alpha+j)}
 =n^{\delta-2+o(1)}\le n^{-1+o(1)}=o(1)                   \tag{6.1}
\]

uniformly in the phase.  Here `mu_alpha=n^{delta+O(ln ln n/ln n)}` and
each displayed ratio is `Theta((ln n)/n)`.  Hence, by Markov,

\[
 \Pr\{\alpha(G_{n,1/2})>\alpha+1\}=o(1).                  \tag{6.2}
\]

Second, one does not need a delicate integer approximation for the Markov
bound.  There are at most `(n+1)^(alpha+1)=exp{O(N^2)}` bounded profiles,
and Stirling's formula gives, for each of them, an upper error `O(N^2)`
relative to its continuous `L` value.  Hence the self-contained bound

\[
 \ln E_{n,k,\alpha+1}\le L_{S_+}(n,k)+O(N^2).             \tag{6.3}
\]

Set

\[
 k_\chi^-:=\lfloor r_+\rfloor-\lceil N\rceil.             \tag{6.4}
\]

By (5.3), `L_{S_+}(n,k_chi^-)<=-Theta(N^3)`, so (6.3) gives
`E_{n,k_chi^-,alpha+1}=o(1)`.  On (6.2), any colouring with at most
`k_chi^-` colours can be refined to an exactly `k_chi^-`-colouring whose
parts all have size at most `alpha+1`.  Thus

\[
 \boxed{\Pr\{\chi(G_{n,1/2})\le k_\chi^-\}=o(1).}         \tag{6.5}
\]

This is why the comparison is with a valid **unrestricted** chromatic lower
threshold, not merely with an artificial bounded chromatic number.

The real signed root remains the correct first-moment location, but the
witness used for an overlap proof should sit well above that root.  Take the
midpoint

\[
 k_{co}:=\left\lceil\frac{r_{S_4}^{co}+r_+}{2}\right\rceil.
                                                                    \tag{6.6}
\]

By (5.3), (5.8), and (4.4), the integer profile from Section 4 now has

\[
 \ln\mathbb E\bar X^{\rm co}_{\mathbf k^{(4)}}
 =\Theta(n/N)=\Theta(k_{co}),                              \tag{6.7}
\]

not merely `Theta(N^2)`.  This high-expectation choice is important in the
near-full overlap range.  The `O(N)` shift in (6.4), the `O(1)` rounding in
(6.6), and the `O(ln n)` error in (4.4) are all `o(n/N^3)`.  Combining
(5.8), (6.4), and (6.6),

\[
 k_\chi^- - k_{co}\ge\left(\frac{c_4}{2}-o(1)\right)
                         \frac n{N^3}.                    \tag{6.8}
\]

## 7. What becomes easier at `alpha-2`

For every fixed `i>=2`,

\[
 \mu_{\alpha-i}
 =\mu_\alpha\left(\Theta(n/N)\right)^i.                  \tag{7.1}
\]

In particular,

\[
 \mu_{\alpha-2}\gg n^2/N^2                               \tag{7.2}
\]

uniformly through every phase.  If `k_i=Theta(n/N)` is the number of slots
of size `alpha-i`, the exact signed common-part activity is

\[
 \frac{k_i^2}{2\mu_{\alpha-i}}.                            \tag{7.3}
\]

For `i=2` this is `O(1/mu_alpha)=o(1)`; for `i=3,4,5` it is smaller still.
Thus the compulsory large common-cluster exponent present in the
`(alpha-1)` route disappears.

Likewise, for `i>j` the aggregate first-order activity of a containment
of an `(alpha-i)` slot in an `(alpha-j)` slot is

\[
 \frac{k_i k_j\binom{\alpha-j}{i-j}}
      {2\mu_{\alpha-i}}=o(1),                              \tag{7.4}
\]

uniformly for the four-type profile.  The factor in the binomial is only a
fixed power of `N`, while (7.1) supplies the corresponding power of `n`.
Fixed-distance near-containments have another factor
`O(N^3/n)` per displaced vertex.  The middle high-cell strip has
`exp{-Omega(N^2)}` one-cell activity.

These estimates explain why the four-type route is substantially cleaner.
They do **not**, by themselves, justify multiplying one-cell activities:
the exact joint law contains `(n)_J` rather than a product of powers of
`n`, and near-total overlaps have diagonal/partial-diagonal cancellations.

## 8. Seed probability and the subsequently closed lemma

The target needed by the rare-event Alon--Scott amplification is

\[
 \Pr\{\zeta(G_{n,1/2})\le k_{co}\}
 \ge\exp\{-o(n/N^4)\}.                                    \tag{8.1}
\]

For a nonnegative signed witness `Z`, it would suffice to prove

\[
 \ln\frac{\mathbb EZ^2}{(\mathbb EZ)^2}=o(n/N^4).          \tag{8.2}
\]

The available ingredients are:

1. The `(alpha-2)` near-optimal profile from tame Lemma 7.20 has the
   Gaussian tail and the uniform macroscopic partial-profile lower bound in
   **every** phase, because (7.2) is much stronger than its
   `mu_a>=n^1.05` hypothesis.
2. `SIGNED_PROFILE_OVERLAP.md`, Theorem 3.1, sums all bounded/intermediate
   cells and the exact even-subgraph factor.
3. `RESIDUAL_ATTACHMENT.md`, Theorem 2.1, shows that after a matching of
   high cells is exposed, every residual local and cycle attachment costs
   only `exp{o(n/N^4)}`, uniformly for mixed profiles.
4. For the four-type profile, every individual common and unequal-size
   containment activity is `o(1)` by (7.3)--(7.4), and the integer profile
   has only a `4 by 4` type structure.

What cannot be invoked is the published tame second-moment theorem itself.
At the signed root,

\[
 \ln\mathbb E\bar X_{\mathbf k}=-\Theta(n/N).             \tag{8.3}
\]

The same order holds at the midpoint witness (6.6): its signed logarithmic
first moment is `Theta(n/N)`, but subtracting the certificate bonus `qk`
still leaves an ordinary logarithmic first moment `-Theta(n/N)` (indeed the
midpoint lies halfway between ordinary exponents `-qk+o(k)` and
`-D_4(delta)k+o(k)`, with `D_4>=0`).

which violates the tame definition's fixed-power lower bound
`ln E X >> -n^(1-c)`.  The signed first moment is large, but that is not a
hypothesis of the published ordinary-colouring theorem.

The statement that remained at this stage was isolated as follows.

> **Four-type high-matching lemma.**  Let `mathbf k` be the
> integer profile on sizes `alpha-2,...,alpha-5` constructed in Section 4,
> at the midpoint choice (6.6), so that its signed first moment is at least
> `exp(cn/N)=exp(c'k)` for fixed positive constants `c,c'`.  In the canonical
> configuration-model decomposition, expose every overlap cell larger than
> half the maximum slot size.  These cells form a matching.  Sum their exact
> bare signed weights, with the joint denominator `(n)_J`, over all typed
> matchings, including common parts, unequal-size containments,
> near-containments, partial diagonals, and the full diagonal.  Then
> \[
>  \ln S_{\rm high}=o(n/N^4).                              \tag{8.4}
> \]

For the full `S_2` optimizer, the same lemma is needed with all its
Gaussian-tail types.  The existing tame partial-profile estimates are then
available.  For the four-type optimizer, a structural proof that follows
the old middle-overlap route must additionally verify its finite list of
proper prefix rates; numerically they are uniformly positive, but that
auxiliary certification is not substituted for (8.4) here.  A direct proof
of (8.4) may bypass that formulation and use the exact partial-diagonal
first-moment identity instead.

With (8.4) proved, the residual-attachment theorem multiplies it by
`exp{o(n/N^4)}`, the bounded-cell theorem contributes `1+o(1)`, and (8.2)
follows.  Paley--Zygmund gives (8.1).  The rare-event concentration theorem
then adds only

\[
 O\left(\frac{\sqrt{n\,o(n/N^4)}}N+n^{1/3}\right)
 =o(n/N^3)                                                 \tag{8.5}
\]

colours, while (6.8) leaves a positive constant multiple of `n/N^3`.
Therefore (8.4), together with the already proved pieces, completes this
all-phase route to a whp diverging gap.  The geometric-mean transport and
Cauchy--multinomial proof of (8.4) is in
`DENSE_FOUR_TYPE_MATCHING.md`; the assembled proof records the final
constant and quantifiers.

## 9. Reproducible calculation

Run

```powershell
python research\experiments\alpha_minus_two_route.py
```

The script uses only the Python standard library.  It prints the limiting
losses on a 1001-point phase grid, the omitted-mass checkpoint ratios used
in the analytic proof, and the safe constants in (5.9).  Its floating-point
output is diagnostic only; Propositions 2.1 and 3.1 use the explicit
rational/surd bounds written above.
