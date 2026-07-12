# Finite slack at the exceptional cap

## Verdict

Let \(q=\ln 2\), \(N=\ln n\), \(w=\ln N\),
\(\alpha=\lfloor\alpha _0(n)\rfloor\), \(a=\alpha-1\), and, in this note,

\[
 x=\frac{\ln\mu_\alpha}{\ln n}.
\]

The limiting cap (c=c(x)) is defined by

\[
 \psi_x(c)=-(1-c)\ln(1-c)+c\left(\frac{qx}{2}-1\right)=0. \tag{1}
\]

The main finite-size conclusion is the opposite of what the coarse
(O(nw/N)) error in Lemma 3.3 might suggest:

* no positive additive slack is needed merely to make the critical
  largest-class partial first moment large;
* at the limiting cap itself that first moment has a positive entropy lift;
  at the beginning of a cycle its logarithm is

\[
 \left(q-\frac{q^2}{4}+o(1)\right)\frac{nw}{N^2}
 \left(w-\ln w+3-\ln\left(2-\frac q2\right)+o(1)\right); \tag{2}
\]

* directed integer rounding changes (2) by only (O(w)), while the usual
  complete-profile rounding costs (O(N^{3/2})) in log first moment;
* a deliberate choice (\rho=A/N), (d=c-\rho), creates an additional
  largest-prefix exponent (Theta(nw/N^2)) at the cycle start and dominates
  the true expansion and rounding remainders;
* its loss in the **complete** profile objective is only
  (Theta(nw/N^2)), because the profile entropy objective is multiplied by
  the number (k=Theta(n/N)) of classes, not by (n).  This is
  (o(kq)), where (kq) is the logarithm of the signed (2^k) advantage.

Thus (\rho=Theta(1/N)) is quantitatively compatible with the signed budget.
It does not dominate the published coarse (O(nw/N)) remainder; indeed no
admissible slack does so at the cycle start.  The exact calculation below is
therefore essential.  This closes a first-moment and rounding scale
calculation, not the signed second moment needed for Erdős Problem 625.

## 1. Exact largest-prefix expectation

Let (Y_{a,\ell}) count unordered families of (ell) pairwise disjoint
independent (a)-sets.  Put

\[
 d=\frac{a\ell}{n}.
\]

There is an exact identity

\[
 \boxed{
 \mathbb E Y_{a,\ell}
 =\frac{n!}{(n-a\ell)!(a!)^\ell\ell!}
   2^{-\ell\binom a2}.}                                    \tag{3}
\]

Equivalently, writing ((n)_r=n!/(n-r)!),

\[
 \mathbb E Y_{a,\ell}
 =\frac{\mu_a^\ell}{\ell!}
   \frac{(n)_{a\ell}}{(n)_a^\ell}.                         \tag{4}
\]

Formula (4) cleanly separates the independent-set supply, the unordered
class entropy, and the disjointness correction.

Since (a+1=\alpha), the exact ratio of consecutive independent-set means is

\[
 \ln\mu_a=xN+\ln(a+1)-\ln(n-a)+qa.                         \tag{5}
\]

Define

\[
 B_n:=\ln\mu_a-N+\ln a+1-\frac{aqx}{2}.                    \tag{6}
\]

### Proposition 1 (uniform sharp expansion)

Uniformly for (0<d\leq0.03), (a=O(N)), and
(ell=dn/a\to\infty),

\[
\begin{aligned}
 \ln\mathbb E Y_{a,\ell}
={}&n\psi_x(d)+\frac{nd}{a}\{B_n-\ln d\}
       +\frac{d(a-1)}2                                      \\
 &-\frac12\ln(1-d)-\frac12\ln(2\pi\ell)                   \\
 &+\frac{d(a-1)(2a-1)}{12n}
   -\frac1{12\ell}-\frac{d}{12n(1-d)}                      \\
 &+O\left(\frac{da^3}{n^2}+\frac1{n^2}+\frac1{\ell^3}\right).
                                                               \tag{7}
\end{aligned}
\]

The implied constant is absolute on the displayed range of (d).

#### Proof

For (m=dn=a\ell), Euler--Maclaurin applied to
(sum_{j=0}^{m-1}\ln(1-j/n)) gives

\[
 \ln(n)_m=mN+n\{- (1-d)\ln(1-d)-d\}
 -\frac12\ln(1-d)-\frac{d}{12n(1-d)}+O(n^{-2}).             \tag{8}
\]

For the short falling factorial, Taylor expansion gives

\[
 \ln(n)_a=aN-\frac{a(a-1)}{2n}
 -\frac{a(a-1)(2a-1)}{12n^2}+O(a^4/n^3).                  \tag{9}
\]

Finally,

\[
 \ln\ell!=\ell\ln\ell-\ell+\frac12\ln(2\pi\ell)
 +\frac1{12\ell}+O(\ell^{-3}).                            \tag{10}
\]

Substitution in (4), using
(ln\ell=N+\ln d-\ln a), yields (7).  In particular, the
error in (7) is a genuine small remainder, not (O(nw/N)). (square)

The script `research/experiments/finite_slack_profile.py` evaluates (3) and
(7) independently.  For (n=10^4,10^6,10^8) and (d\simeq0.01), their
absolute differences are respectively (2.3\cdot10^{-5}),
(6.8\cdot10^{-7}), and (2.6\cdot10^{-3}); the last discrepancy is mainly
the cancellation error in binary64 evaluation of the gamma-function form of
(3).

## 2. The hidden entropy lift at the cap

Let

\[
 C=1+\ln q-q,\qquad
 \delta=\{\alpha_0(n)\},\qquad D=C-\frac{q\delta}{2}.
\]

Then the identity

\[
 a=\frac2q(N-w+D)                                          \tag{11}
\]

is exact.  Combining (5)--(6) with (11) gives, uniformly for
(0\leq x\leq x_0),

\[
 \boxed{
 B_n=xw+(2-x)D+2\ln(2/q)+1
       +O\left(\frac wN+\frac an\right).}                  \tag{12}
\]

At the start of a cycle,

\[
 x=\left(\frac2q-\frac12+o(1)\right)\frac wN,qquad
 \delta=o(1),                                               \tag{13}
\]

and hence

\[
 B_n=2C+2\ln(2/q)+1+o(1)=3+o(1).                          \tag{14}
\]

The exact cancellation to (3) follows immediately from
(C=1+\ln q-q) and (ln(2/q)=q-\ln q).

Set

\[
 \gamma=2-\frac q2=1.653426409720027\ldots .               \tag{15}
\]

The root equation (1) gives (c=qx+O(x^2)), so (13) implies

\[
 c=\gamma\frac wN(1+o(1)),qquad a=\frac{2N}{q}(1+o(1)).   \tag{16}
\]

At (d=c), the (n\psi_x(d)) term in (7) vanishes, but the
unordered-class term does not.  Equations (7), (14), and (16) give

\[
\begin{aligned}
 \ln\mathbb E Y_{a,cn/a}
 &=\frac{nc}{a}\{-\ln c+3+o(1)\}                           \\
 &=\frac{q\gamma}{2}\frac{nw}{N^2}
   \{w-\ln w+3-\ln\gamma+o(1)\}.                          \tag{17}
\end{aligned}
\]

Since (q\gamma/2=q-q^2/4=0.5730339270803949\ldots), this is
exactly (2).  It tends to infinity much faster than every power of (N).

This positivity is uniform through the exceptional interval.  For fixed
positive (x), (12) contains the positive term (xw), so the cap lift is
(Theta(nw/N)).  In the intermediate range (x\to0), the sum
(xw-\ln c) tends to infinity; its smallest overall scale occurs at the
cycle boundary (13), where (17) applies.  Consequently

\[
 \inf_{\text{exceptional phases}}
 \ln\mathbb E Y_{a,\lfloor cn/a\rfloor}
 =\Omega\left(\frac{nw^2}{N^2}\right).                    \tag{18}
\]

Here is a uniform justification of the last sentence.  The full-cycle
expansion for \(\mu_\alpha\) implies
\[
 x\geq\left(\frac2q-\frac12-o(1)\right)\frac wN
\]
at every point of the cycle.  On \(0\leq x\leq x_0\), continuity of the
root equation gives \(C_1x\leq c(x)\leq C_2x\), while (12) and the bounded
range of \(D\) give \(B_n\geq xw+C_3\) for an absolute \(C_3>0\) and all
large \(n\).  If \(x\leq1/w\), then
\[
 c(B_n-\ln c)\geq C_4x\ln(1/x).
\]
The function \(x\ln(1/x)\) is increasing on this interval, so its minimum is
at the cycle-start scale and is \(\Omega(w^2/N)\).  If \(x\geq1/w\), then
\(c(B_n-\ln c)=\Omega(1/w)\), which is much larger than \(w^2/N\).
Multiplication by \(n/a=\Theta(n/N)\), and comparison with the \(O(N)\)
displayed lower-order terms in (7), proves (18).

Directed rounding gives

\[
 d_n=\frac a n\left\lfloor\frac{cn}{a}\right\rfloor,qquad
 0\leq c-d_n<\frac an.                                     \tag{19}
\]

Near the cycle start, changing (d) by (a/n) changes (7) by (O(w)).
Thus (17)--(18) survive integer rounding with overwhelming room.

## 3. The limiting cap is below the true finite first-moment cap

The positive lift is large enough to move the zero of the exact partial
first moment.  This distinction is useful:

* (c(x)) is the **limiting rate cap**, defined by (1);
* (widehat c_n(x)) is the larger local root of the exact finite equation
  (ln\mathbb E Y_{a,dn/a}=0), with integer effects suppressed.

At a fixed phase (x>0), Taylor expansion of (7) gives

\[
 \widehat c_n-c
 =\frac{c\{B_n-\ln c\}}
        {a\{-\psi_x'(c)\}}+O(w^2/N^2),qquad
 \psi_x'(c)=\ln(1-c)+\frac{qx}{2}<0.                       \tag{20}
\]

This displacement is (Theta(w/N)).

At the cycle start the displacement is comparable with (c), so (20) is
not uniform.  Put (d=tc), with (t) in a fixed compact subset of
((0,\infty)).  From (13)--(16), uniformly in such (t),

\[
 \frac{2N^2}{nw^2}\ln\mathbb E Y_{a,tcn/a}
 =t\gamma\{\gamma(1-t)+q\}+o(1).                           \tag{21}
\]

Therefore the nonzero finite root satisfies

\[
 \boxed{
 \frac{\widehat c_n}{c}\longrightarrow
 1+\frac q\gamma
 =1.4192186458890028\ldots .}                              \tag{22}
\]

Thus choosing (d=c-\rho) is conservative: even (\rho=0) stays a
positive linear fraction below the actual finite largest-prefix threshold at
the most delicate phase.

This also separates the **baseline finite-cap loss** from the **extra slack
loss**.  At the cycle start,
\[
 \widehat c_n-c=\frac{q w}{N}(1+o(1)).
\]
Since the complete-profile multiplier is
\(\Lambda(d)=w-\ln w+O(1)\) throughout this short interval and
\(k=(q/2+o(1))n/N\), using the limiting cap \(c\), instead of the finite
largest-prefix threshold \(\widehat c_n\), already sacrifices
\[
 \Delta_{\rm baseline}
 =\left(\frac{q^2}{2}+o(1)\right)\frac{nw^2}{N^2}.          \tag{22a}
\]
This is still \(o(kq)\), by a factor \(w^2/N\).  The additional loss caused
by \(c\mapsto c-A/N\), computed in (35), is smaller than (22a) by a factor
\(\Theta(1/w)\).  Of course \(\widehat c_n\) itself has first moment only of
constant order; (22a) is a threshold comparison, not a claim that one may use
that endpoint unchanged in the partial-profile theorem.

For a certified cocolouring partial profile, every (a)-set may independently
be labelled "independent" or "clique".  Since the sets are disjoint and
(a\geq2), this multiplies (3) **exactly** by (2^\ell):

\[
 \ln\mathbb E Y^{\rm signed}_{a,\ell}
 =\ln\mathbb E Y_{a,\ell}+q\ell.                           \tag{23}
\]

At the cycle start, (q\ell=\Theta(nw/N^2)), one factor (w) below the
ordinary entropy lift (17).  It further improves feasibility but does not
change the leading ratio (22).  This first-moment identity does not by itself
control signed overlaps.

## 4. How much deliberate slack is actually needed?

For (d=c-\rho), the exact power-series argument in the profile audit gives

\[
 \frac{(c-\rho)\rho}{2}
 \leq\psi_x(c-\rho)
 \leq\frac{(c-\rho)\rho}{2(1-c)}.                          \tag{24}
\]

At the cycle start, if (\rho=A/N) for fixed (A>0), then

\[
 n\psi_x(c-\rho)
 =\left(\frac{A\gamma}{2}+o(1)\right)\frac{nw}{N^2}.       \tag{25}
\]

The cap lift (17) remains positive and is larger than (25) by a factor
asymptotic to (w/A).  Both quantities dominate the (O(N^{3/2})) loss from
the standard adjacent-size integer rounding, as well as the (N^6) margin
in the partial-profile hypothesis.

There are therefore three different answers to "the smallest slack," which
should not be conflated.

1. **For the critical complete largest-class prefix:** no deliberate slack is
   needed.  The minimal directed rounding prescription is (19), whose
   effective slack lies in ([0,a/n)).
2. **Demanding that the new (n\psi) term alone beat a polylogarithmic
   target (R_n):** (24) only requires

   \[
    \rho\gg \frac{2R_n}{nc}.
   \]

   At the cycle start and (R_n=N^6), this is
   (\rho\gg 2N^7/(\gamma nw)), far below (1/N).
3. **Using only the continuum uniform-slack lemma to pay the complete
   binomial-product entropy (O(n/N)):** the natural modular scale is
   (\rho=\Theta(1/N)) (with constants depending on the fixed macroscopic
   cutoff).  The exact cap lift makes even this modular slack unnecessary in
   the only boundary layer where the limiting rate vanishes.

The following is a boundary-layer **scale audit**, not yet a complete
finite-profile theorem.  Fix the macroscopic cutoff (delta>0).
Every complete residual prefix (s\geq2) has rate (C_\delta n) by the
residual-prefix audit, while

\[
 2\sum_i\ln\binom{k_i}{\ell_i}=O(n/N).                     \tag{26}
\]

Only profiles close to the all-(a)-set endpoint can have vanishing limiting
rate.  If (r=k_a-\ell), then

\[
 2\ln\binom{k_a}{r}\leq2r\ln(ek_a/r),                     \tag{27}
\]

whereas (24), away from (d=0), supplies a linear gain
(Omega(a r)).  The possible deficit in (27) is confined to
(r\leq k_a e^{-\Omega(N)}), and its maximum is (n^{1-\Omega(1)}).
For phases where (c\geq\delta/2), the exact endpoint lift is
(Omega_\delta(nw/N)), and the same boundary-layer comparison dominates that
deficit, including the short fractional segment entering the second
coordinate.  For phases where (c<\delta/2), every macroscopic partial profile
contains at least \(\delta/2\) residual mass and is covered by the
(C_\delta n) bound.  Directed rounding perturbs these logarithms by only
(O(N^{3/2})).  These estimates show that no new asymptotic scale forces
positive (\rho).

For completeness, the required directed rounding is a direct restriction of
the construction in Lemma 7.17 of the tame-colourings paper.  First fix
\(k_a=\lfloor cn/a\rfloor\).  Re-optimize the residual real profile on
sizes at most \(a-1\), with its now-integer number of classes and vertices.
Its limiting deficit mean stays in a compact subinterval of \((3,4)\), and
the coordinates of deficits \(3\) and \(4\) both contain \(\Theta(k)\)
classes.  Run the floor-and-carry algorithm only on residual sizes, and use
these two adjacent positive coordinates for the final two linear constraints.
No carry enters size \(a\).  Exactly as in Lemma 7.17, this makes
\(O(\sqrt N)\) unit neighbor changes and costs \(O(N^{3/2})\) in log first
moment.  It therefore preserves (19) and all margins above.

What remains to turn this scale audit into a theorem is a uniform
constant-tracking argument for every fractional and non-greedy partial
profile after the residual reoptimization.  In particular, (27) by itself
does not prove the full product inequality (2.4) simultaneously for every
integer subprofile.  The exact complete largest-prefix estimate is proved;
the global macroscopic partial-profile lift is conditional on completing
that finite combinatorial audit.  Even after that, the overlap estimates and
the hypothesis (mu_a\geq n^{1+\varepsilon}) of the existing theorem remain.

## 5. Complete-profile objective loss: the KKT multiplier

The normalization is important here.  Let (p_i) be **fractions of colour
classes**, so (sum_i p_i=1) and (sum_i i p_i=T).  Vertex masses differ
from (p_i) by (1+O(1/N)).  The profile-dependent entropy/energy objective
is multiplied by the number (k=\Theta(n/N)) of classes.

For a prescribed (p_1=d), write

\[
 R_d=\frac{T-d}{1-d},qquad
 Z(\mu)=\sum_{i\geq2}e^{\mu i-qi^2/2},                     \tag{28}
\]

where (mu=mu_d) makes the residual mean (R_d).  The optimized
per-class objective is

\[
 V(d)=-d\ln d-\frac q2d-(1-d)\ln(1-d)
 +(1-d)\{\ln Z(\mu_d)-\mu_dR_d\}.                          \tag{29}
\]

Envelope differentiation gives the exact multiplier

\[
 \boxed{
 V'(d)=\ln\frac{1-d}{d}+\mu_d-\frac q2-\ln Z(\mu_d).}      \tag{30}
\]

For (x<x_0), (V'(c)>0): increasing the capped coordinate toward the
unconstrained optimum improves the complete first moment.  Put

\[
 \Lambda(x):=V'(c(x)).                                     \tag{31}
\]

Then, for (\rho=o(c)), the finite continuous profile and standard directed
integer rounding give

\[
 \ln E_{\rm comp}(c-\rho)-\ln E_{\rm comp}(c)
 =-k\left\{\Lambda(x)\rho
 +O\left(\frac{\rho^2}{c}+\frac{\rho w}{N}\right)\right\}
 +O(N^{3/2}).                                               \tag{32}
\]

The (O(\rho w/N)) term includes conversion between class fractions and
vertex masses and the finite-(n) discrete-Gaussian correction.

At (x=x_0), (Lambda(x_0)=0).  At the cycle start, let (mu_0) solve

\[
 \frac{\sum_{i\geq2}i e^{\mu_0i-qi^2/2}}
      {\sum_{i\geq2}e^{\mu_0i-qi^2/2}}
 =1+\frac2q.
\]

Numerically,

\[
 \mu_0=2.644386531109143\ldots,\quad
 Z_0=456.0382817169458\ldots,\quad
 \mu_0-\frac q2-\ln Z_0=-3.824763816295169\ldots .         \tag{33}
\]

Consequently,

\[
 \Lambda(x)
 =w-\ln w-4.327613562980954\ldots+o(1)                    \tag{34}
\]

at the cycle start.  Since (k=(q/2+o(1))n/N), setting
(\rho=A/N) in (32) costs

\[
 \boxed{
 \Delta\ln E_{\rm comp}
 =\left(\frac{qA}{2}+o(1)\right)
   \frac{n}{N^2}
   \{w-\ln w-4.3276135629\ldots\}.}                        \tag{35}
\]

The signed first-moment bonus is

\[
 kq=\left(\frac{q^2}{2}+o(1)\right)\frac nN.               \tag{36}
\]

The ratio of (35) to (36) is

\[
 \frac{A\Lambda(x)}{qN}=O(w/N)=o(1).                       \tag{37}
\]

Thus (\rho=1/N) is nowhere near exhausting the signed advantage.  The
formal full-budget balance is (\rho\asymp q/\Lambda\asymp q/w), not
(1/(Nw)).  At the cycle start this balanced value is larger than (c), so
even deleting the entire capped coordinate costs (o(kq)).  The smaller
choice (\rho=1/(Nw)) has both partial-prefix gain and complete-objective loss
of order (n/N^2); it too dominates every polylogarithmic rounding error.

Lemma 16 of the cochromatic paper gives

\[
 \frac{\partial L_0}{\partial k}=\frac{2}{q}N^2+O(Nw).      \tag{38}
\]

Therefore the number of extra colours needed to compensate the loss (32) is

\[
 \Delta k_{\rm slack}
 =\frac{q^2n\Lambda(x)\rho}{4N^3}(1+o(1)).                 \tag{39}
\]

For (\rho=A/N) at the cycle start this is

\[
 \Delta k_{\rm slack}
 =\left(\frac{q^2A}{4}+o(1)\right)\frac{nw}{N^4},          \tag{40}
\]

whereas the full signed first-moment displacement is

\[
 \Delta k_{\rm signed}
 =\left(\frac{q^3}{4}+o(1)\right)\frac n{N^3}.             \tag{41}
\]

Again their ratio is (A\Lambda/(qN)=o(1)).

## 6. The exact incompatible scales

At the cycle start,

\[
 c\asymp\frac wN,qquad
 n c\rho\asymp\frac{nw}{N}\rho.                           \tag{42}
\]

For (\rho=1/N), the true slack exponent is (nw/N^2).  It cannot dominate
the black-box error (nw/N) in Lemma 3.3.  In fact, asking
(nc\rho\gg nw/N) would require (\rho\gg1), incompatible with
(0\leq\rho<c=o(1)).  This is a genuine incompatibility **with that coarse
lemma**, not with the exact finite first moment.

Proposition 1 replaces the coarse error at the critical prefix by the explicit
positive term (17) and a remainder

\[
 O\left(\frac{da^3}{n^2}+n^{-2}+\ell^{-3}+N\right),        \tag{43}
\]

where the harmless (O(N)) also absorbs the displayed logarithmic and
integer-\(\ell\) rounding terms.  The separate \(O(N^{3/2})\) complete-profile
rounding loss is also dominated.  Both (17) and the additional gain (25)
dominate these errors.
Thus there is no first-moment scale conflict after the exact calculation.

## 7. Reproducibility and remaining obstruction

Run

```powershell
python research\experiments\finite_slack_profile.py
```

to reproduce:

* exact-vs-expanded finite expectations;
* (2C+2\ln(2/q)+1=3);
* the multiplier constants (33)--(34);
* the finite-cap ratio (1+q/\gamma);
* the signed-budget and cycle-start normalization constants.

What is proved here is the exact critical-prefix finite first-moment lift, its
rounding scale, and the complete-objective cost of deliberate slack.  It
removes the apparent critical-prefix obstruction created by Lemma 3.3's
coarse error.  A global integer audit of all macroscopic partial profiles is
still required, as explained above.  This note does **not**
prove a signed/two-graph second moment for the new complete profile, nor does
it repair the fixed-power (mu_a\geq n^{1+\varepsilon}) assumption in the
existing tame-colouring theorem.  Those remain the substantive obstacles.
