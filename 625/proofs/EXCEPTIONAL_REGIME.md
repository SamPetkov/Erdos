# Exceptional oscillatory regime and nearby-`n` transfer

## Scope and status

This note settles the elementary asymptotic and density calculations around
Heckel's hypothesis

\[
 n^{a+\varepsilon}\leq \mu_\alpha\leq n^{1-\varepsilon},
 \qquad
 \mu_t=\binom nt2^{-\binom t2},
\]

and audits the deterministic nearby-`n` route.  It does **not** settle Erdős
Problem 625.  The conclusions relevant to the larger investigation are:

1. Uniformly through a complete oscillation,
   \(x(n):=\log\mu_\alpha/\log n=\{\alpha _0(n)\}+o(1)\), and a uniform
   expansion through the constant term is given below.
2. For fixed \(a,\varepsilon\), the natural lower and upper densities of the
   admissible integers can be written in closed form.  For \(a=0.05\) and
   \(\varepsilon\downarrow0\), they are
   \(0.9413458545\ldots\) and \(0.9578002903\ldots\).  There is no single
   natural density.
3. Consecutive admissible blocks are separated by intervals of length
   \(\Theta(n)\).  Some exceptional integers have distance a positive linear
   fraction of `n` from every admissible integer.  Heckel's lower bound
   \(n^{1-\varepsilon}\) is sublinear, so the one-vertex Lipschitz estimate
   cannot bridge these intervals.
4. The constant \(x_0=0.0290543918664\ldots\) can be reproduced from the
   limiting optimal-profile equations in the tame-colourings paper.  What
   crosses zero there is the exponential rate of a required *partial*
   profile.  The source does not construct the replacement feasible profile
   below the transition, and neither does this note.

The elementary calculations below use no probabilistic theorem.  Statements
about tame profiles are explicitly marked as source-dependent.

> **Status box.**
>
> | Item | Status and precise meaning |
> |---|---|
> | Full-cycle expansion | **Proved here, uniformly:** (1) has an explicit \(O((\ln\ln n)^2/\ln n)\) error in \(\ln\mu_\alpha\), uniform in the phase \(\delta\in[0,1)\). |
> | Density formulas | **Proved limiting statements:** (17)--(19) are natural lower/upper densities after integer-rounding errors are shown to be `o(n)`.  They are not exact finite-`n` proportions, and in general no natural density exists. |
> | Numerical checks | `research/experiments/exceptional_cycle.py` reproduces the two density constants, transfer constants, expansion constants, and the scalar root \(x_0\) using double precision.  It performs no random-graph simulation and supplies no finite-`n` probabilistic evidence. |
> | \(x_0\) | **Source-dependent reduction, independently solved scalar equation:** the computation assumes the limiting optimal-profile formula and partial-profile exponential rate proved in the tame-colourings paper.  The script verifies the resulting root; it does not reprove those profile theorems or construct the missing feasible profile below \(x_0\). |

## 1. Uniform expansion for \(\mu_\alpha\)

All logarithms in this section are natural unless a base is displayed.  Put

\[
 q=\ln2,\qquad N=\ln n,\qquad w=\ln N,
 \qquad C=1+\ln q-q.
\]

Then

\[
 \alpha _0(n)=\frac{2}{q}(N-w+C)+1.
\]

Let

\[
 \delta=\{\alpha _0(n)\}\in[0,1),\qquad
 \alpha=\lfloor\alpha _0(n)\rfloor=\alpha _0(n)-\delta.
\]

Define

\[
 A(\delta)=\frac2q-\frac12-\delta
\]

and

\[
\begin{split}
 K(\delta)={}&\delta C+\frac q2\delta(1-\delta)-\frac{2C}{q}
 -(1-\delta)\\
 &-\frac12\ln(2\pi)-\frac q2+\frac12\ln q.
\end{split}
\]

### Lemma 1 (full-cycle expansion)

Uniformly for \(0\leq\delta<1\),

\[
 \boxed{
 \ln\mu_\alpha
 =\delta N+A(\delta)w+K(\delta)
   +O\!\left(\frac{w^2}{N}\right).
 }
 \tag{1}
\]

Equivalently,

\[
 \boxed{
 \mu_\alpha
 =e^{K(\delta)}n^\delta(\ln n)^{2/q-1/2-\delta}(1+o(1)),
 }
 \tag{2}
\]

where the relative `o(1)` is uniform over the cycle.  Consequently,

\[
 \boxed{
 x(n)=\frac{\ln\mu_\alpha}{\ln n}
 =\delta+\frac{A(\delta)\ln\ln n+K(\delta)}{\ln n}
 +O\!\left(\frac{(\ln\ln n)^2}{(\ln n)^2}\right).
 }
 \tag{3}
\]

#### Proof

Write \(b=1-\delta\) and \(S=N-w+C\).  Then

\[
 \alpha=\frac{2S}{q}+b=O(N).
\]

Uniformly for this range,

\[
 \ln\binom n\alpha
 =\alpha N-\ln\Gamma(\alpha+1)+O(\alpha^2/n),
\]

and Stirling's formula gives

\[
 \ln\Gamma(\alpha+1)
 =\alpha\ln\alpha-\alpha+\frac12\ln(2\pi\alpha)+O(1/\alpha).
\]

It follows that

\[
\begin{split}
 \ln\mu_\alpha
 & =\alpha\left(N-\ln\alpha+1-\frac q2(\alpha-1)\right)
    -\frac12\ln(2\pi\alpha)+O(1/N).                  \tag{4}
\end{split}
\]

The expression in parentheses is

\[
 \frac{q\delta}{2}
 +\frac{w-C-bq/2}{N}
 +O(w^2/N^2),                                        \tag{5}
\]

uniformly in \(b\in(0,1]\).  Multiplying (5) by
\(\alpha=2(N-w+C)/q+b\), and using

\[
 \ln\alpha=q+w-\ln q+o(1),
\]

in the final logarithm in (4), gives exactly (1).  Exponentiation gives (2),
and division by \(N\) gives (3).  All discarded bounds are uniform because
\(\delta\) ranges over a compact interval.  ∎

### Endpoint and jump checks

At the beginning of a cycle (\(\delta=0\)),

\[
 \mu_\alpha=e^{K(0)}(\ln n)^{2/q-1/2}(1+o(1)),
\]

so the minimum is polylogarithmic, not asymptotic to a nonzero constant.  Just
before the next jump (\(\delta\to1\)),

\[
 \mu_\alpha=n(\ln n)^{2/q-3/2+o(1)}e^{K(1)}.
\]

Thus \(x(n)\) starts at \(o(1)\), increases to \(1+o(1)\), and then drops by
approximately one when \(\alpha\) increases.  In particular, finite-`n`
values of `x` can lie slightly above one near the right endpoint; treating the
cycle as exactly `[0,1)` loses a polylogarithmic correction but no fixed-power
statement.

The exact ratio

\[
 \frac{\mu_{\alpha-1}}{\mu_\alpha}
 =\frac{\alpha 2^{\alpha-1}}{n-\alpha+1}
\]

has the uniform asymptotic

\[
 \boxed{
 \frac{\mu_{\alpha-1}}{\mu_\alpha}
 =\frac{e^2q}{2}\,2^{-\delta}\frac{n}{\ln n}(1+o(1)).
 }
 \tag{6}
\]

Hence \(\ln\mu_{\alpha-1}/\ln n=1+\delta+o(1)=1+x(n)+o(1)\).
This is the precise mapping between the `x` used below and the condition on
\(\mu_{\alpha-1}\) in the tame-profile lemma.

## 2. Geometry of one oscillation

The function \(\alpha _0(r)\), extended to real \(r\), is strictly increasing
for all sufficiently large `r`.  Let

\[
 B_s=\alpha _0^{-1}(s),\qquad B_j=B_s\big|_{s=j}.
\]

Thus the `j`th cycle is \([B_j,B_{j+1})\), up to integer rounding.  For bounded
real `u`, uniformly in `u`,

\[
 \boxed{
 \frac{B_{s+u}}{B_s}
 =2^{u/2}\left(1+\frac{uq}{2\ln B_s}
 +O\!\left(\frac1{(\ln B_s)^2}\right)\right).
 }
 \tag{7}
\]

Indeed, if \(h=\ln(B_{s+u}/B_s)\), then the exact difference of the two
\(\alpha _0\) values is

\[
 u=\frac2q\left(h-\ln\left(1+\frac{h}{\ln B_s}\right)\right),
\]

and solving this equation gives (7).  In particular,

\[
 \frac{B_{j+1}}{B_j}\longrightarrow R:=\sqrt2.
 \tag{8}
\]

### Exact level boundaries

Fix \(s\in(0,1)\).  Inside the `j`th cycle, \(\alpha=j\) is fixed and
\(x(n)=\ln\mu_j(n)/\ln n\) is strictly increasing for all sufficiently large
`j`.  One way to see this is to differentiate: the derivative with respect to
\(\ln n\) of \(\ln\binom nj\) is \(j+o(1)\), whereas
\(\ln\mu_j=O(\ln n)\) in the cycle, so the numerator in the quotient rule is
\(j\ln n-O(\ln n)>0\).

Let \(E_{j,s}\) be the unique real point in \([B_j,B_{j+1})\) satisfying
\(x(E_{j,s})=s\).  This definition, followed by ceilings/floors, gives exact
integer exceptional intervals; it does not hide the polylogarithmic term in
(3).  If \(N_j=\ln B_j\), \(w_j=\ln N_j\), then its phase
\(\delta_{j,s}:=\alpha _0(E_{j,s})-j\) satisfies

\[
 \boxed{
 \delta_{j,s}
 =s-\frac{A(s)w_j+K(s)}{N_j}+o(1/N_j).
 }
 \tag{9}
\]

Combining (7) and (9) gives, more explicitly,

\[
 \boxed{
 \frac{E_{j,s}}{B_j}
 =2^{s/2}\left[1+\frac q{2N_j}
 \{s-A(s)w_j-K(s)\}+o(w_j/N_j)\right].
 }
 \tag{10}
\]

The leading formula \(E_{j,s}/B_j\to2^{s/2}\) is enough for all density and
distance conclusions below.

## 3. Exact exceptional intervals

Fix

\[
 0<p<r<1,
\]

and define the admissible set

\[
 \mathcal G_{p,r}=\{n\in\mathbb N:p\le x(n)\le r\}.
\]

For the hypothesis in Heckel's theorem,

\[
 p=a+\varepsilon,\qquad r=1-\varepsilon,
 \qquad 0<\varepsilon<(1-a)/2.                    \tag{11}
\]

The exact admissible block in cycle `j` is

\[
 \mathcal G_{p,r}\cap[B_j,B_{j+1})
 = [E_{j,p},E_{j,r}]\cap\mathbb N,                \tag{12}
\]

with the obvious endpoint adjustment if a level point is itself an integer.
The two exceptional pieces in that cycle are

\[
 [B_j,E_{j,p})\cap\mathbb N,
 \qquad
 (E_{j,r},B_{j+1})\cap\mathbb N.                 \tag{13}
\]

Across a cycle boundary these join into one gap

\[
 \boxed{
 \mathcal I_j=(E_{j,r},E_{j+1,p})\cap\mathbb N.
 }
 \tag{14}
\]

Set

\[
 U=2^{p/2},\qquad V=2^{r/2},\qquad R=\sqrt2.
\]

Then (10) yields

\[
 |\mathcal I_j|=(RU-V)B_j+o(B_j)
 =\left(U-\frac VR\right)B_{j+1}+o(B_{j+1}).     \tag{15}
\]

This is a positive linear fraction of its location whenever \(p>0\) or
\(r<1\).  The exceptional intervals are therefore macroscopically wide.

## 4. Natural-density calculation

Let

\[
 D_{p,r}(X)=\frac{|\mathcal G_{p,r}\cap[1,X]|}{X}.
\]

Take a cutoff \(X=yB_j\) with \(1\le y\le R\).  The admissible part of a
completed cycle with start `B` has length \((V-U)B+o(B)\).  From (8), the sum
of the starts of all completed cycles before the current one is

\[
 \sum_{i<j}B_i=\frac{B_j}{R-1}+o(B_j).
\]

Consequently, with

\[
 H=\frac{V-U}{R-1},
\]

the complete subsequential limit profile is

\[
 D(y)=
 \begin{cases}
 H/y,&1\le y\le U,\\[2mm]
 (H+y-U)/y,&U\le y\le V,\\[2mm]
 (H+V-U)/y,&V\le y\le R.
 \end{cases}                                      \tag{16}
\]

Since \(H\le U\), the first piece decreases, the middle piece increases, and
the last piece decreases.  The minimum is attained at \(y=U\), and the
maximum at \(y=V\).  Therefore

\[
 \boxed{
 \underline d(\mathcal G_{p,r})
 =\frac{2^{(r-p)/2}-1}{\sqrt2-1},
 }
 \tag{17}
\]

and

\[
 \boxed{
 \overline d(\mathcal G_{p,r})
 =\frac{1-2^{-(r-p)/2}}{1-2^{-1/2}}.
 }
 \tag{18}
\]

Thus the two densities depend only on the phase width \(r-p\), although the
fraction within a single completed cycle, \((V-U)/(R-1)\), also depends on the
location of the phase interval.  The logarithmic density does exist and equals
\(r-p\), because \(d n/n=(q/2+o(1))d\delta\) within a cycle.

For (11), put \(h=1-a-2\varepsilon\).  Then

\[
 \underline d=\frac{2^{h/2}-1}{\sqrt2-1},
 \qquad
 \overline d=\frac{1-2^{-h/2}}{1-2^{-1/2}}.       \tag{19}
\]

For \(a=0.05\) and then \(\varepsilon\downarrow0\), these become

\[
 \underline d
 =\frac{2^{-0.05/2}-2^{-1/2}}{1-2^{-1/2}}
 =0.9413458545597445\ldots,                       \tag{20}
\]

\[
 \overline d
 =\frac{1-2^{-0.95/2}}{1-2^{-1/2}}
 =0.9578002902595889\ldots.                       \tag{21}
\]

These reproduce the two numbers in Heckel's paper.  A quantifier caveat is
essential: for each **fixed** positive \(\varepsilon\), (19), not (20)--(21),
describes that theorem's hypothesis.  The displayed 94.13--95.78 percent
figures are the limit as the fixed margin is subsequently taken to zero; they
are not the density for one theorem invocation with \(\varepsilon=\varepsilon(n)\).

## 5. Exact scale of the nearest admissible integer

For a point \(n=yB_j\) in the upper exceptional piece of the `j`th cycle,
\(V<y<R\), the two neighboring admissible endpoints are asymptotic to
\(VB_j\) and \(RUB_j\).  Hence

\[
 \frac{\operatorname{dist}(n,\mathcal G_{p,r})}{B_j}
 =\min\{y-V,RU-y\}+o(1).                           \tag{22}
\]

For a point in the lower exceptional piece of the current cycle,
\(1<y<U\), the same formula can be written as

\[
 \frac{\operatorname{dist}(n,\mathcal G_{p,r})}{B_j}
 =\min\left\{y-\frac VR,U-y\right\}+o(1),          \tag{23}
\]

where \((V/R)B_j\) is the end of the preceding admissible block.  Equations
(22)--(23) quantify the distance for every phase in the exceptional gap.

At the midpoint of (14),

\[
 \max_{n\in\mathcal I_j}\operatorname{dist}(n,\mathcal G_{p,r})
 =\frac{RU-V}{2}B_j+o(B_j),                        \tag{24}
\]

and the distance as a fraction of the midpoint itself tends to

\[
 \boxed{
 \rho_{p,r}=\frac{RU-V}{RU+V}>0.
 }
 \tag{25}
\]

If the artificial upper margin is allowed to vanish and \(p=a=0.05,r=1\),
then

\[
 U=2^{0.025}=1.0174796921026863\ldots,
\]

so the exceptional gap has asymptotic width
\(0.0174796921\ldots\,B_{j+1}\), its maximum nearest-good distance is

\[
 0.0087398460513431\ldots\,B_{j+1},
\]

and the relative distance at its midpoint is

\[
 \rho_{0.05,1}=0.0086641229505851\ldots.           \tag{26}
\]

Thus there are infinitely many exceptional integers whose distance from every
admissible integer is at least \(0.0086n\), say.

## 6. Nearby-`n` transfer: what follows and what does not

Couple all \(G_n\) as induced subgraphs of one infinite \(G(\mathbb N,1/2)\).
Adding one vertex changes each of \(\chi\) and \(\zeta\) by either zero or one:

\[
 0\le\chi(G_{n+1})-\chi(G_n)\le1,
 \qquad
 0\le\zeta(G_{n+1})-\zeta(G_n)\le1.
\]

Consequently, for \(D_n=\chi(G_n)-\zeta(G_n)\),

\[
 \boxed{|D_m-D_n|\le|m-n|.}                       \tag{27}
\]

The loss is one per vertex, not two: monotonicity of both parameters improves
the bound obtained by separately applying two absolute-value inequalities.

Suppose Heckel's theorem is invoked with a fixed margin \(\eta>0\).  At an
admissible `m` it gives, with high probability,

\[
 D_m\ge m^{1-\eta}.                                \tag{28}
\]

Combining (27)--(28) gives only

\[
 D_n\ge m^{1-\eta}-|m-n|.                          \tag{29}
\]

This proves divergence at an exceptional `n` if, for example,
\(|m-n|\le m^{1-\eta}/2\).  Thus the deterministic argument can extend a
fixed admissible block by boundary layers of order \(n^{1-\eta}\).

It cannot reach the middle of an exceptional interval.  At the midpoint in
(24), every admissible `m` has \(|m-n|\ge c n\) for a fixed `c>0`, whereas
\(m^{1-\eta}=o(n)\).  The right side of (29) is then negative.  Moreover, the
total boundary-layer width in a cycle is \(O(n^{1-\eta})\) while the
exceptional gap has width \(\Theta(n)\), so the fraction reached tends to zero.

There is an additional quantifier obstruction.  The admissible phase interval
for margin \(\eta\) begins at \(a+\eta\).  An integer with phase at or below
`a` is a positive linear distance from this block for every fixed `eta`.
Taking \(\eta=\eta(n)\to0\) is not licensed by a theorem proved only for every
fixed \(\eta>0\).  In fact, the thin boundary layers obtained from margin
\(\eta\) already lie, for large `n`, in the direct admissible interval for the
fixed smaller margin \(\eta/2\).  Nearby-`n` transfer therefore adds no new
fixed phase range to the union of the existing fixed-margin statements.

### A countermodel to the naive Lipschitz inference

The failure is not merely that (29) was estimated crudely.  Fix \(\eta>0\),
let \(\mathcal G\) be the corresponding admissible set, and define a
deterministic nonnegative sequence

\[
 f(k)=\sup_{m\in\mathcal G}
       \big(m^{1-\eta}-|k-m|\big)_+.
\]

It is 1-Lipschitz (a supremum of 1-Lipschitz cones) and satisfies
\(f(m)\ge m^{1-\eta}\) at every admissible `m`.  Nevertheless, at the midpoint
\(n_j\) of each sufficiently large exceptional gap, \(f(n_j)=0\): all
comparable admissible points are a linear distance away, and for very small or
very large `m` the distance also dominates \(m^{1-\eta}\).  Hence a
1-Lipschitz lower bound on all good integers is logically consistent with zero
at infinitely many exceptional midpoints.  Any successful nearby-`n` argument
must use probabilistic stability much stronger than deterministic vertex
Lipschitzness.

## 7. The transition \(x_0\)

This subsection depends on the optimal-profile analysis in Heckel and
Panagiotou, *Colouring random graphs: Tame colourings*
([arXiv:2306.07253](https://arxiv.org/abs/2306.07253)), especially its
reparametrisation, partial-colouring calculation, and discussion after Lemma
7.20.  The application to cochromatic number is stated in Heckel,
*The difference between the chromatic and the cochromatic number of a random
graph* ([arXiv:2409.17614](https://arxiv.org/abs/2409.17614)).

For the \((\alpha-1)\)-bounded first-moment-optimal continuous profile, put
\(i=\alpha-u\ge1\).  At limiting phase \(x\in[0,1]\), its class proportions
are

\[
 \zeta_i(x)=\exp\left(\lambda(x)+\mu(x)i-\frac q2i^2\right),\qquad i\ge1,
 \tag{30}
\]

where \(\lambda,\mu\) are the unique values satisfying

\[
 \sum_{i\ge1}\zeta_i=1,
 \qquad
 \sum_{i\ge1}i\zeta_i=T(x):=1+\frac2q-x.           \tag{31}
\]

The exponential rate for the partial profile consisting of all prescribed
maximum-size classes (the `i=1` part) is

\[
 \phi(x)=-(1-\zeta_1(x))\ln(1-\zeta_1(x))
 +\zeta_1(x)\left(\frac{qx}{2}-1\right).           \tag{32}
\]

The transition is the unique numerical root

\[
 \boxed{x_0=0.0290543918664065\ldots}              \tag{33}
\]

of \(\phi(x_0)=0\).  At the root,

\[
 \zeta_1(x_0)=0.0200042296606687\ldots,
 \qquad
 \mu(x_0)=2.667435050073759\ldots.                 \tag{34}
\]

The standard-library computation in
`research/experiments/exceptional_cycle.py` solves the mean equation (31) by
bisection, with a discrete-Gaussian tail truncated at `i=79`, and then solves
(32) by bisection.  For reference,

\[
 \phi(0)=-1.7896260\times10^{-4},\qquad
 \phi(0.04)=7.2951391\times10^{-5}.
\]

By (6), if the cochromatic application takes \(a=\alpha-1\), then

\[
 \mu_a=\mu_{\alpha-1}=n^{1+x+o(1)}.
\]

Thus the suggested replacement of \(\mu_a\ge n^{1.05}\) by
\(\mu_a\ge n^{1+x_0+\varepsilon}\) is the same, at fixed-power precision, as
requiring \(\mu_\alpha\ge n^{x_0+\varepsilon}\).

For \(x<x_0\), (32) is negative.  The cited paper proves that the expected
number of the corresponding partial unordered colourings is then
\(\exp(-\Theta(n))\), so the first-moment-optimal complete profile contains an
unrealizable subprofile and the lower-bound-on-partial-profiles condition used
in the second moment fails.  This is a **feasibility transition**.  The
continuous first-moment profile (30) itself varies continuously through
\(x_0\); calling (33) a discontinuous change of that profile would be
misleading.

What is unavailable from the cited results is a construction and second-moment
analysis of the replacement feasible profile for \(x\le x_0\).  Reproducing
the scalar root (33) does not supply that missing theorem.  It relies, in
particular, on source results identifying (30) as the relevant limiting
first-moment optimum and converting (32) into a uniform partial-colouring
expectation.

If that source-dependent modification could be completed above `x_0`, the
same density calculation with \(a=x_0\) and vanishing margin would give

\[
 \underline d=0.9657931398424675\ldots,
 \qquad
 \overline d=0.9755673071108460\ldots,              \tag{35}
\]

which explains the informal description “roughly 97 percent.”  It would still
leave positive-linear-width exceptional gaps and therefore would not, by
itself or by deterministic nearby-`n` transfer, resolve the all-`n` problem.

## 8. Audit conclusions for the mechanism registry

- **Proved here:** the uniform expansion (1)--(3), inverse-cycle expansion
  (7), exact level intervals (12)--(15), density profile (16)--(21), and
  nearest-good distances (22)--(26).
- **Transfer verdict:** deterministic nearby-`n` Lipschitz transfer reaches
  only sublinear boundary layers and no new fixed phase range.  Midpoints of
  the exceptional gaps give an explicit obstruction.
- **Source-dependent but numerically reproduced:** the scalar transition
  (33), conditional on the limiting profile and partial-profile rate from the
  tame-colourings paper.
- **Still missing:** a feasible optimal/near-optimal profile below `x_0`, or a
  probabilistic vertex-deletion stability result strong enough to replace the
  linear deterministic loss.
