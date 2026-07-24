# Erdős 625: root-gap constant propagation and placement experiment

**Status.** This is a focused mathematical review note. It derives a sharper
constant from equations already stated in the canonical candidate manuscript.
It does not alter the canonical manuscript, publication PDFs, Lean sources, or
`Erdos625Statement`.

Throughout, put

\[
 q=\ln 2,\qquad N=\ln n,\qquad H_n=\frac{n}{N^3},
\]

and define the limiting four-support advantage

\[
 A(\delta)=q-D_4(\delta),\qquad
 \gamma_4=\ln\frac{200}{153}.
\]

The inputs used below are:

1. the uniform root-displacement formula from equation (5.11),
   \[
    r_+(n)-r_4^{co}(n)
    =\left(\frac{q^2}{4}A(\delta_n)+o(1)\right)H_n;
    \tag{1.1}
   \]
2. the midpoint integer from equation (5.13),
   \[
    k_{co}=\left\lceil\frac{r_4^{co}+r_+}{2}\right\rceil;
    \tag{1.2}
   \]
3. the chromatic lower integer
   \[
    k_\chi^-=\lfloor r_+\rfloor-\lceil N\rceil;
    \tag{1.3}
   \]
4. the amplification loss `a_n=o(H_n)` from equations (10.12)--(10.13).

All uses of `o(1)` in this note inherit the manuscript's asserted uniformity in
the complete phase parameter.

## 1. Exact floor-and-ceiling loss

### Lemma 1.1

For real numbers `x>y` and `L>=0`, define

\[
 K_\chi=\lfloor x\rfloor-\lceil L\rceil,
 \qquad
 K_{1/2}=\left\lceil\frac{x+y}{2}\right\rceil.
\]

Then

\[
 \boxed{
 K_\chi-K_{1/2}>
 \frac{x-y}{2}-L-3.}
 \tag{1.4}
\]

#### Proof

Use

\[
 \lfloor x\rfloor>x-1,
 \qquad
 \lceil L\rceil<L+1,
 \qquad
 \left\lceil\frac{x+y}{2}\right\rceil<\frac{x+y}{2}+1.
\]

Subtracting the last two quantities from the first gives (1.4).  The constant
three is the natural universal bound: the three independent rounding errors can
simultaneously approach one. \(\square\)

The same argument gives a placement-sensitive version. For fixed
`0<theta<1`, put

\[
 K_\theta=\left\lceil y+\theta(x-y)\right\rceil.
\]

Then

\[
 \boxed{
 K_\chi-K_\theta>
 (1-\theta)(x-y)-L-3.}
 \tag{1.5}
\]

Equation (1.5) is exact deterministic arithmetic. Whether a non-midpoint
choice preserves every later second-moment estimate is a separate question.

## 2. The midpoint retains the full phase-resolved coefficient

Apply Lemma 1.1 with

\[
 x=r_+(n),\qquad y=r_4^{co}(n),\qquad L=N.
\]

Equations (1.1)--(1.3) give

\[
 \begin{aligned}
 k_\chi^- - k_{co}
 &>\frac12\{r_+-r_4^{co}\}-N-3\\
 &=\left(
   \frac{q^2}{8}A(\delta_n)+o(1)
   \right)H_n,
 \end{aligned}
 \tag{2.1}
\]

because

\[
 \frac{N+3}{H_n}=\frac{(N+3)N^3}{n}\longrightarrow0.
 \tag{2.2}
\]

No witness or profile is changed here: `k_co` remains exactly the midpoint
integer used in the canonical manuscript. In particular, the signed
first-moment margin and every subsequent overlap estimate are the same ones
already invoked there.

## 3. Amplification does not consume the coefficient

On the intersection of the two high-probability events used in Section 11,

\[
 \chi(G_n)>k_\chi^-,
 \qquad
 \zeta(G_n)\le k_{co}+a_n,
\]

one has

\[
 \chi(G_n)-\zeta(G_n)
 > k_\chi^- - k_{co}-a_n.
 \tag{3.1}
\]

Since `a_n=o(H_n)`, equation (2.1) yields the phase-resolved conclusion

\[
 \boxed{
 \chi(G_n)-\zeta(G_n)
 \ge
 \left(
   \frac{q^2}{8}A(\delta_n)-o(1)
 \right)H_n}
 \tag{3.2}
\]

with high probability.

This is only a propagation of the manuscript's own root formula. It uses no
new second-moment or concentration estimate.

## 4. A factor-four explicit constant

The proof of Lemma 5.1 supplies a uniform strict inequality

\[
 A(\delta)>\gamma_4
 \qquad(0\le\delta\le1).
 \tag{4.1}
\]

The limiting value functions, and hence `A`, are continuous on the closed phase
interval. Equivalently, one may use the fixed strict omitted-mass bounds inside
the proof of Lemma 5.1. In either formulation there is an `eta_0>0` such that

\[
 A(\delta)\ge\gamma_4+\eta_0
 \qquad(0\le\delta\le1).
 \tag{4.2}
\]

Combining (3.2) and (4.2), and absorbing the uniform `o(1)`, gives for all
sufficiently large `n`

\[
 \boxed{
 \chi(G_n)-\zeta(G_n)
 \ge
 \frac{q^2}{8}\ln\frac{200}{153}
 \frac{n}{(\ln n)^3}}
 \tag{4.3}
\]

with high probability, conditional on the correctness and stated uniformity of
the canonical proof chain.

The currently displayed coefficient is

\[
 \frac{q^2}{32}\ln\frac{200}{153}.
\]

Thus (4.3) is a factor-four constant improvement obtained without changing the
four-size profile or any probabilistic estimate.

## 5. Numerical phase scan — diagnostic only

The accompanying standard-library script also scans the limiting variational
problem. With the unrestricted support truncated at deficits 59 and 89, the two
computations agree to displayed floating-point precision. On a 1001-point phase
grid it reports approximately

\[
 \min_{0\le\delta\le1}A(\delta)
 \approx0.520701335491,
 \]

attained at the endpoint `delta=1` on that grid. This would correspond to the
phase-uniform coefficient

\[
 \frac{q^2}{8}\min A\approx0.031271565748.
\]

This scan is evidence about available slack, not a proof and not a proposed
replacement constant.

## 6. Root-placement experiment

Equation (1.5) suggests replacing the midpoint by

\[
 k_\theta=
 \left\lceil
 r_4^{co}+\theta(r_+-r_4^{co})
 \right\rceil,
 \qquad 0<\theta<1.
 \tag{6.1}
\]

The deterministic retained gap would be

\[
 \left(
 (1-\theta)\frac{q^2}{4}A(\delta_n)+o(1)
 \right)H_n.
 \tag{6.2}
\]

At the level of the continuous first-moment objective, the distance from the
signed root is `theta` times the root separation, so every fixed `theta>0`
should retain a positive exponential first-moment margin of order `n/N`.
However, the constants in the partial-diagonal and dense-overlap estimates must
be replayed with their dependence on that margin exposed. Therefore (6.2) is an
experimental route, not a theorem claimed by this note.

A conservative next test would be `theta=1/4`, which increases the retained
root gap by a factor `3/2` relative to the midpoint while retaining one quarter
of the continuous signed-root margin.

## 7. Scope boundary

This note does not verify equation (5.11), Lemma 5.1, Proposition 9.2, or the
amplification theorem independently. It verifies the deterministic rounding and
coefficient propagation once those canonical inputs, including their uniformity,
are accepted. The exact checker is a regression test and not a substitute for
the asymptotic argument.