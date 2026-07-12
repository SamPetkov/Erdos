# A candidate constrained profile below the exceptional transition

**Status.**  This note identifies and solves the limiting variational problem
obtained by imposing the missing largest-class feasibility constraint for
phases `0 <= x <= x0`.  A subsequent independent reconstruction in
`research/audits/CONSTRAINED_PROFILE_AUDIT.md` proved the complete-prefix
lemma stated below, using an exact residual identity and rationally certified
bounds.  It also found the decisive boundary caveat: the active largest-class
prefix itself has rate exactly zero, so the profile does not yet satisfy the
strict partial-profile hypothesis.  Lifting a slackened profile uniformly to
finite `n` and proving the signed second moment remain open.  This is a
concrete candidate phase, not a resolution of Problem #625.

Throughout, `q=ln 2`,

\[
 T(x)=1+\frac2q-x,
 \qquad 0\le x\le x_0=0.0290543918664\ldots .                 \tag{1}
\]

The index `i=alpha-u` records the deficit of a class of size `u` from
`alpha`.  The limiting vertex masses are denoted by `z_i`; hence

\[
 \sum_{i\ge1}z_i=1,
 \qquad \sum_{i\ge1}i z_i=T(x).                               \tag{2}
\]

## 1. Why only the largest-class constraint is initially active

For a partial profile with vertex masses `lambda_i`, Lemma 3.3 of the tame
colourings paper gives the leading exponential rate

\[
 \Phi_x(\lambda)
 =-(1-L)\ln(1-L)
  +\frac q2\sum_{i\ge1}\lambda_i(i-T(x)),
 \qquad L=\sum_i\lambda_i.                                   \tag{3}
\]

For fixed `L`, this expression is minimized by taking as much mass as allowed
at the smallest indices first.  Therefore the dangerous subprofiles are the
prefixes `i=1,...,s`, with at most one fractional final coordinate.  Since
(3) is concave as that final coordinate varies, checking the two endpoint
prefixes is enough at the limiting exponential scale.

For the unconstrained optimum, the tame-colourings analysis proves that every
prefix ending at `s>=2` has positive rate, uniformly over `x in [0,1]`.
The only failing prefix below `x0` is `s=1`.  If its mass is `z`, its rate is

\[
 \psi_x(z)=-(1-z)\ln(1-z)+z\left(\frac{qx}{2}-1\right).       \tag{4}
\]

For `x>0`, (4) is positive just to the right of zero and has one further root
in `(0,1)`.  Denote that root by

\[
 c(x):=\max\{z\in[0,1):\psi_x(z)=0\},
 \qquad c(0):=0.                                               \tag{5}
\]

Taylor expansion at zero gives

\[
 c(x)=q x+O(x^2).                                              \tag{6}
\]

At `x=x0`, `c(x0)=0.0200042296607...`, exactly the largest-class
mass of the unconstrained profile.  For `x<x0`, the unconstrained mass is
larger than `c(x)`, explaining its exponentially unlikely largest-class
subprofile.

## 2. The constrained KKT optimizer

At fixed `x` and fixed number of classes, the signed first moment differs
from the ordinary first moment by a factor depending only on the total number
of classes, not on their size profile.  Consequently both first moments have
the same profile optimizer.  Imposing the necessary constraint

\[
 z_1\le c(x)                                                   \tag{7}
\]

makes (7) active below `x0`.  Conditional on `z_1=c(x)`, the strict-concavity
and Lagrange-multiplier calculation for the remaining coordinates gives

\[
 z_1=c(x),\qquad
 z_i=(1-c(x))\frac{\exp(\mu i-q i^2/2)}
 {\sum_{j\ge2}\exp(\mu j-q j^2/2)},\quad i\ge2,               \tag{8}
\]

where the unique `mu=mu_c(x)` is chosen so that

\[
 \frac{\sum_{i\ge2}i\exp(\mu i-q i^2/2)}
 {\sum_{i\ge2}\exp(\mu i-q i^2/2)}
 =\frac{T(x)-c(x)}{1-c(x)}.                                   \tag{9}
\]

Existence and uniqueness in (9) follow because the left side is the mean of
a one-parameter exponential family and its derivative is its strictly
positive variance.  At `x=x0`, (8) joins the unconstrained profile
continuously.  At `x=0`, it becomes the ordinary `i>=2` optimizer, so the
phase also joins the `(alpha-2)`-bounded description at the cycle boundary.
This supplies a natural analytic interpolation through the entire previously
unmodelled interval.

## 3. Prefix-rate test

For (8), define

\[
 Z_s=\sum_{i=1}^s z_i,
 \qquad
 \Phi_s(x)=-(1-Z_s)\ln(1-Z_s)
  +\frac q2\sum_{i=1}^s z_i(i-T(x)).                          \tag{10}
\]

By construction, `Phi_1(x)=0`, and completeness gives
`lim_{s->infinity} Phi_s(x)=0`.  A standard-library calculation using a
discrete-Gaussian tail through `i=120` tested 1001 equally spaced values of
`x in [0,x0]`.  For every tested prefix with `s>=2` and
`0.001 <= Z_s <= 0.999`, it found

\[
 \Phi_s(x)\ge 0.0287835313.                                   \tag{11}
\]

No tested prefix rate was negative.  The minimum in (11) occurred at `x=x0`,
`s=2`, `Z_2=0.1218702082...`.  The script is
`research/experiments/constrained_profile.py`.

This calculation is consistent with the following exact target lemma.

> **Missing profile lemma.**  For every fixed `delta>0` there is
> `C_delta>0` such that, uniformly for `0<=x<=x0`, every prefix of (8) with
> `delta<=Z_s<=1-delta` and `s>=2` satisfies
> `Phi_s(x)>=C_delta`.

The independent audit proves this lemma for all complete prefixes `s>=2`.
Its key exact identity is

\[
 \Phi_s^{\rm capped}(x)=(1-c(x))\varphi_s^{\rm residual}(x),  \tag{11a}
\]

where the residual profile is the `i>=2` discrete-Gaussian family.  Exact
rational certificates give uniform positivity for residual prefixes 2 and 3,
and a tail-propagation lemma gives every larger prefix.  The exploratory value
in (11) is still only a grid value; the proof and its certifier are in the
audit and `research/experiments/constrained_profile_certify.py`.

## 4. Why the equality at the active cap needs slack

The exact largest-class prefix has zero limiting rate at `z_1=c(x)`, whereas
the second-moment framework needs quantitative room.  Use instead

\[
 z_1=c(x)-\rho_n                                                   \tag{12}
\]

and re-optimize the residual distribution, where `rho_n>0` tends to zero
slowly enough.  Since

\[
 \partial_z\psi_x(c(x))<0\quad(x>0),                           \tag{13}
\]

the partial rate gains order `rho_n |partial_z psi_x(c(x))|`.
Near the cycle boundary, (6) gives
`|partial_z psi_x(c(x))|=Theta(x)`.  The finite-`n` minimum phase from the
uniform expansion of `mu_alpha` is of order
`ln ln n/ln n`, rather than literally zero.  Thus it is plausible to choose
`rho_n=o(c(x))` while making the partial expectation exponentially larger
than `exp(n^0.99)`.  A proof must retain the finite-`n` error terms and integer
rounding; this note does not assert that lift.

### 4.1 The KKT price of slack

Slack cannot be selected from the partial-profile rate alone.  Let
`V_x(d)` be the optimized limiting complete-profile objective when `z_1=d`
and the residual coordinates are re-optimized subject to (2).  Write the
residual solution as

\[
 z_i=\exp(\lambda_d+\mu_di-qi^2/2),\qquad i\ge2,
\]

and extrapolate its unconstrained formula to

\[
 \widehat z_1(d)=\exp(\lambda_d+\mu_d-q/2).                  \tag{13a}
\]

The envelope theorem (or direct differentiation of the Lagrangian) gives the
exact derivative

\[
 \boxed{V_x'(d)=\ln\frac{\widehat z_1(d)}d.}                 \tag{13b}
\]

Indeed, the residual mass and first moment both decrease by one unit when
`d` increases by one unit; subtracting their two KKT multipliers from the
direct derivative `-ln d-1-q/2` yields (13b).  The certified residual bounds
`2.61<mu_d<2.68`, together with `0.10<y_2<0.12`, keep
`widehat z_1(d)` between two positive absolute constants throughout the small
phase.  Hence, as `d=c(x)->0`,

\[
 V_x'(c(x))=\ln(1/c(x))+O(1).                                \tag{13c}
\]

The functional `V_x` is the profile entropy/energy **per colour class**; its
contribution to the complete log first moment is multiplied by
`k=Theta(n/N)`, not by `n`.  At the start of a finite cycle,
`c(x)=Theta(w/N)`, so the marginal complete-objective cost of additive slack
`rho` is

\[
 \Theta\!\left(\frac nN\rho\{w+O(\ln w)\}\right).            \tag{13d}
\]

The full signed advantage is only `Theta(n/N)` in logarithmic first-moment
`Theta(n/N^3)` colour displacement needs only

\[
 \rho w=O(1);                                                \tag{13e}
\]

For example `rho=1/N` costs only `Theta(nw/N^2)=o(n/N)` in the complete
objective, while the largest-prefix gain is
`n c rho=Theta(nw/N^2)`.  This scale therefore fits comfortably inside the
signed advantage and is still exponentially substantial.  Proving it useful
requires a sharper finite-`n` partial-profile expansion than the existing
`O(nw/N)` general bound.  The two-scale obligation remains, but it is not an
incompatibility: partial feasibility and complete objective loss must be
controlled simultaneously at their correct normalizations.

## 5. What this does and does not repair

The construction addresses the *exceptional-profile* obstruction: it gives
an explicit candidate feasible profile below `x0`, instead of merely noting
that the old optimum is unrealizable.  It does not address the independent
*full-shift* obstruction.  At a reduction of order `n/log^3 n`, the ordinary
first moment of the same profile is about `exp(-Theta(n/log n))`; this violates
the existing definition of a tame ordinary-colouring profile even though the
signed/certified first moment receives the compensating `2^k` factor.

There is also a quantitative probability-scale warning near the very start of
a cycle.  Write `N=ln n` and `w=ln N`.  The uniform expansion in
`EXCEPTIONAL_REGIME.md` gives

\[
 x(n)=\left(\frac2q-\frac12+o(1)\right)\frac wN,
 \qquad c(x(n))=\Theta(w/N).                                  \tag{14}
\]

Hence the capped number of `(alpha-1)`-classes is of order

\[
 k_{\alpha-1}=\Theta(nw/N^2),                                 \tag{15}
\]

while

\[
 \mu_{\alpha-1}
 =\Theta\!\left(nN^{2/q-3/2}\right)                         \tag{16}
\]

up to an explicit cycle-end constant.  The probability exponent appearing in
the existing tame-colouring second-moment theorem is therefore

\[
 \frac{k_{\alpha-1}^2}{\mu_{\alpha-1}}
 =\Theta\!\left(
   \frac{n w^2}{N^{2/q+5/2}}
  \right)
 =\Theta\!\left(\frac{n w^2}{N^{5.38539\ldots}}\right).       \tag{17}
\]

For a conjectural gap `h=n/N^3`, ordinary vertex concentration can amplify a
positive-probability construction only when its negative logarithm is
`o(h^2/n)=o(n/N^6)`.  The exponent in (17) is larger by
`N^{0.61460...}w^2`.  Thus simply inserting the capped profile into the old
Paley--Zygmund bound would still be quantitatively too weak at the cycle
boundary.  A conditioned-density, truncated-witness, or otherwise sharper
overlap argument is needed; profile feasibility alone is not the whole proof.

Accordingly, a complete positive proof along this route still needs all of:

1. a directed-rounding proof of the missing profile lemma and a uniform
   finite-`n` construction with the slack (12);
2. a direct signed-cocolouring or two-graph overlap theorem that permits the
   small ordinary first moment at the full `n/log^3 n` displacement;
3. comparison with a uniform lower bound for the unrestricted chromatic
   number, followed by concentration amplification.

The useful new point is that the first item now has an explicit two-phase
candidate and a scalar active constraint.  The unresolved lemma is no longer
"find some profile below `x0`" but the precise finite-`n` lifting and prefix
bound stated above.
