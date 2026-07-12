# Audit of the capped exceptional profile

**Verdict.**  The capped KKT profile in
`research/proofs/CONSTRAINED_EXCEPTIONAL_PROFILE.md` is the correct optimizer
of the stated *limiting, cap-constrained* variational problem, conditional on
the previously established unconstrained-profile transition at \(x_0\).  The
claim that worst partial profiles are greedy prefixes (with at most one
fractional last coordinate) is exact for the limiting rate, not merely a
heuristic.

This audit proves the note's stated **Missing profile lemma** for complete
prefixes \(s\geq2\), uniformly on \(0\leq x\leq x_0\).  The proof uses an
exact residual-profile identity and elementary certified bounds; no phase
grid is used.

There is also an important correction to the interpretation.  At the active
cap the full \(i=1\) prefix has rate exactly zero.  Hence the capped profile
does **not** satisfy a uniform positive-rate condition for *all* macroscopic
subprofiles.  For any \(0<\delta<c(x_0)\), this zero-rate prefix itself is a
counterexample at phases with \(c(x)\geq\delta\).  The slack proposed in the
original note is therefore logically necessary, and its uniform finite-\(n\)
analysis remains open.

Throughout,

\[
 q=\ln2,\qquad T(x)=1+\frac2q-x,\qquad 0\leq x\leq x_0<0.03.
\]

## 1. Re-derivation of the capped KKT profile

After affine terms fixed by the mass and mean constraints are discarded, the
limiting log-first-moment objective that produces the discrete-Gaussian
profile can be written

\[
 \mathcal J(z)=-\sum_{i\geq1}z_i\ln z_i
                  -\frac q2\sum_{i\geq1}i^2z_i,              \tag{1.1}
\]

subject to

\[
 \sum_i z_i=1,\qquad \sum_i iz_i=T(x),\qquad
 z_i\geq0.                                                     \tag{1.2}
\]

This is the limiting form of the strictly concave entropy maximization in the
optimal-profile calculation.  Add the cap \(z_1\leq c(x)\), where

\[
 \psi_x(c)=-(1-c)\ln(1-c)+c\Big(\frac{qx}{2}-1\Big)=0. \tag{1.3}
\]

For \(x>0\), \(\psi_x'(0)=qx/2>0\) and
\(\psi_x''(z)=-1/(1-z)<0\), so (1.3) has exactly one positive
root \(c(x)\), and \(\psi_x(z)\geq0\) precisely for
\(0\leq z\leq c(x)\).  At \(x=0\), the only feasible root is
\(c(0)=0\).

The previously established transition statement says that the unconstrained
optimizer has \(z_1^{\mathrm{unc}}>c(x)\) for \(x<x_0\), with equality at
\(x=x_0\).  Strict concavity then forces the cap to be active: if a
constrained optimizer below \(x_0\) had \(z_1<c(x)\), its interior KKT
equations would reproduce the unique unconstrained optimizer, a contradiction.

Conditional on \(z_1=c\), the residual mass and mean are

\[
 \sum_{i\geq2}z_i=1-c,\qquad
 \sum_{i\geq2}iz_i=T-c.                                \tag{1.4}
\]

The KKT equations for \(i\geq2\) give

\[
 z_i=(1-c)\frac{\exp(\mu i-qi^2/2)}
                  {\sum_{j\geq2}\exp(\mu j-qj^2/2)},\qquad i\geq2,  \tag{1.5}
\]

where \(\mu\) is uniquely fixed by

\[
 R:=\frac{T-c}{1-c}
 =\frac{\sum_{i\geq2}i\exp(\mu i-qi^2/2)}
        {\sum_{i\geq2}\exp(\mu i-qi^2/2)}.             \tag{1.6}
\]

Uniqueness follows because the derivative of the right-hand side with
respect to \(\mu\) is its strictly positive variance.  This re-derives
equations (8)--(9) of the candidate note.  At \(x=0\), \(c=0\) and this is
exactly the \(i\geq2\) optimizer.  At \(x=x_0\), it is the conditional
\(i\geq2\) tail of the unconstrained optimizer, so the two phases join.

## 2. The prefix reduction is an exact linear-programming fact

For a partial profile \(0\leq\lambda_i\leq z_i\), put
\(L=\sum_i\lambda_i\).  Its limiting rate is

\[
 \Phi_x(\lambda)=-(1-L)\ln(1-L)
       +\frac q2\sum_i\lambda_i(i-T).                    \tag{2.1}
\]

For fixed \(L\), the entropy term is constant and the coefficients
\(i-T\) are strictly increasing in \(i\).  If \(i<j\),
\(\lambda_i<z_i\), and \(\lambda_j>0\), shifting

\[
 \epsilon\leq\min\{z_i-\lambda_i,\lambda_j\}
\]

from coordinate \(j\) to coordinate \(i\) changes the linear term by
\(q\epsilon(i-j)/2<0\).  Repeating this exchange proves:

> **Greedy-prefix lemma.**  At every fixed total mass \(L\), the minimum
> of (2.1) over the coordinate box \(0\leq\lambda_i\leq z_i\) is
> attained by saturating \(i=1,2,\ldots\) in order, with at most one
> fractional final coordinate.

This statement is exact for the limiting functional.  Along a segment in
which the final coordinate varies, the second derivative of (2.1) with
respect to that coordinate is

\[
 -\frac1{1-L}<0.                                             \tag{2.2}
\]

Thus the rate is concave on the segment, and its minimum over the full segment
is at one of its two complete-prefix endpoints.  This justifies the prefix
reduction for nonnegativity.  It does not by itself create a *strict* bound
when an endpoint rate is zero, and it does not remove finite-\(n\) rounding
or error terms.

## 3. Exact residual identity at the feasibility cap

Write

\[
 y_i=\frac{z_i}{1-c},\quad i\geq2,\qquad
 \sum_{i\geq2}y_i=1,\qquad \sum_{i\geq2}iy_i=R.       \tag{3.1}
\]

For \(s\geq2\), define the residual prefix rate

\[
 \varphi_s(R)=
 -\Big(1-\sum_{i=2}^s y_i\Big)
  \ln\Big(1-\sum_{i=2}^s y_i\Big)
 +\frac q2\sum_{i=2}^s y_i(i-R).                       \tag{3.2}
\]

Let \(a_s=\sum_{i>s}y_i\) and let \(m_s^+\) be the conditional
mean of this residual tail.  Mean balance gives

\[
 \varphi_s=a_s\Big[-\ln a_s-\frac q2(m_s^+-R)\Big].   \tag{3.3}
\]

The full capped profile has tail mass \((1-c)a_s\), so its complete-prefix
rate is

\[
\begin{aligned}
 \Phi_s
 &=(1-c)a_s\Big[-\ln((1-c)a_s)
                    -\frac q2(m_s^+-T)\Big]\\
 &=(1-c)\varphi_s
 +(1-c)a_s\Big[-\ln(1-c)-\frac q2(R-T)\Big].   \tag{3.4}
\end{aligned}
\]

But \(R-T=c(T-1)/(1-c)\), and the cap equation is equivalent to

\[
 -(1-c)\ln(1-c)-\frac q2c(T-1)=0.                    \tag{3.5}
\]

Therefore the correction bracket in (3.4) vanishes exactly:

\[
\boxed{\Phi_s(x)=(1-c(x))\varphi_s(R(x)),\qquad s\geq2.} \tag{3.6}
\]

This identity is the main simplification missing from the candidate note.
It also holds for \(s=1\) if the residual empty-prefix rate is defined to be
zero, and then it recovers \(\Phi_1=0\).

Solving (1.3) for \(x\) and substituting into \(R=(T-c)/(1-c)\)
gives two useful exact parametrizations:

\[
 x(c)=\frac2q\Big[1+\frac{1-c}{c}\ln(1-c)\Big]
     =\frac2q\sum_{m\geq1}\frac{c^m}{m(m+1)},             \tag{3.7}
\]

\[
 R(c)=1-\frac{2\ln(1-c)}{qc}
     =1+\frac2q\sum_{m\geq0}\frac{c^m}{m+1}.            \tag{3.8}
\]

Both are interpreted by continuity at \(c=0\).  In particular, \(c\)
and \(R\) increase with \(x\).

## 4. Certified coarse bounds for the residual family

From (3.7), \(x(c)>c/q\) for \(c>0\).  Since
\(x\leq x_0<0.03\) and \(q<0.694\),

\[
 0\leq c<0.021.                                             \tag{4.1}
\]

Using \(0.693<q<0.694\) and

\[
 1\leq \frac{-\ln(1-c)}c
 \leq1+\frac{c}{2(1-c)},                               \tag{4.2}
\]

equation (3.8) yields the deliberately coarse enclosure

\[
\boxed{3.88<R<3.92.}                                      \tag{4.3}
\]

Let \(m(\mu)\) be the mean of the probability distribution

\[
 y_i(\mu)=\frac{\exp(\mu i-qi^2/2)}
                  {\sum_{j\geq2}\exp(\mu j-qj^2/2)},\qquad i\geq2. \tag{4.4}
\]

Since \(m'(\mu)=\operatorname{Var}_{\mu}(I)>0\), (4.3) and the
following exact-rational certificates imply \(2.64<\mu<2.68\):

| \(\mu\) | certified \(m(\mu)\) | certified \(y_2\) | certified \(y_3\) |
|---:|---:|---:|---:|
| 2.64 | 3.87984430150033744… | 0.10949899589834176… | 0.27125176939171513… |
| 2.68 | 3.93066424332936533… | 0.10146430485130760… | 0.26160588326821528… |

The enclosures are generated using only exact `Fraction` arithmetic, a
Taylor remainder for \(e^\mu\), an integer-square-root enclosure for
\(\sqrt2\), and an explicit geometric tail bound in
`research/experiments/constrained_profile_certify.py`.  The displayed
interval widths are smaller than the printed precision; the script's
assertions compare the rational endpoints, not the displayed decimals.

For an exponential family,

\[
 \frac{d}{d\mu}y_i=(i-R)y_i.                              \tag{4.5}
\]

Thus \(y_2\) and \(y_3\) both decrease throughout the range (4.3),
and the endpoint certificates give

\[
\boxed{0.10<y_2<0.11,\qquad0.26<y_3<0.28.}              \tag{4.6}
\]

## 5. Proof of every residual prefix inequality

### Lemma 5.1 (the first two prefixes)

Uniformly for the family (4.4) with mean in (4.3),

\[
 \varphi_2>\frac{5223}{312500}=0.0167136,\qquad
 \varphi_3>\frac{42329}{625000}=0.0677264.             \tag{5.1}
\]

#### Proof

For \(0<Y<1\), \(-\ln(1-Y)\geq Y\), so

\[
 -(1-Y)\ln(1-Y)\geq Y(1-Y).                          \tag{5.2}
\]

For \(s=2\), use \(Y=y_2\), \(q/2<0.347\), (4.3), and
(4.6):

\[
\begin{aligned}
 \varphi_2
 &\geq y_2(1-y_2)-\frac q2y_2(R-2)\\
 &>0.10(0.90)-0.347(0.11)(1.92)
   =0.0167136.
\end{aligned}                                               \tag{5.3}
\]

For \(s=3\), \(0.36<Y=y_2+y_3<0.39\), and

\[
\begin{aligned}
 \varphi_3
 &\geq Y(1-Y)
 -\frac q2\Big((R-2)y_2+(R-3)y_3\Big)\\
 &>0.36(0.64)
 -0.347\Big(1.92(0.11)+0.92(0.28)\Big)
 =0.0677264.
\end{aligned}                                               \tag{5.4}
\]

All inequalities are strict because the input enclosures are strict.
\(\square\)

The remaining prefixes follow analytically from the \(s=3\) case.  The
next lemma is the tail-propagation argument behind Lemmas 7.13--7.14 of the
tame-colourings paper, stated here on the slightly extended mean range needed
by the capped profile.

### Lemma 5.2 (tail propagation)

Let \(y_i\) have the form (4.4), with mean \(R\), and suppose
\(\mu<2.68\).  If \(\varphi_3>0\), then
\(\varphi_s>0\) for every \(s\geq4\).

#### Proof

For \(\ell\geq3\), set

\[
 S_\ell=\sum_{j\geq0}\exp\Big(\mu j-\frac q2(j^2+2j\ell)\Big),
\qquad
 S_\ell'=\sum_{j\geq0}j\exp\Big(\mu j-\frac q2(j^2+2j\ell)\Big).
                                                                    \tag{5.5}
\]

If \(y_\ell=e^{\lambda+\mu\ell-q\ell^2/2}\), direct tail summation
gives

\[
 \varphi_{\ell-1}=y_\ell E_\ell,                     \tag{5.6}
\]

where

\[
 E_\ell=\sum_{j\geq0}e^{\mu j-q(j^2+2j\ell)/2}
 \Big[B(\ell)-\lambda-\ln S_\ell+\frac q2R-\frac q2j\Big], \tag{5.7}
\]

and

\[
 B(t)=\frac q2t^2-\mu t-\frac q2t.                       \tag{5.8}
\]

Now \(B'(t)=qt-\mu-q/2\).  Since
\(\mu<2.68<4q\), \(B\) is increasing for
\(t\geq4.5\), and a direct endpoint comparison also gives
\(B(\ell)\geq B(4)\) for every integer \(\ell\geq5\).
Furthermore, \(S_\ell\) decreases with \(\ell\).  Therefore, for
\(\ell\geq5\), the bracket in (5.7) is bounded below by

\[
 C(j):=B(4)-\lambda-\ln S_4+\frac q2R-\frac q2j.       \tag{5.9}
\]

The function \(C(j)\) decreases in \(j\).  After division by
\(S_\ell\), (5.7) is bounded below by the average of \(C(j)\)
under weights proportional to
\(\exp(\mu j-qj^2/2-qj\ell)\).  Increasing \(\ell\) shifts these
weights monotonically toward smaller \(j\), so this average is at least
its value at \(\ell=4\), namely \(E_4/S_4\).  Hence

\[
 \frac{E_\ell}{S_\ell}\geq\frac{E_4}{S_4}>0,\qquad \ell\geq5,
\]

where the final inequality is equivalent by (5.6) to
\(\varphi_3>0\).  Another use of (5.6) proves
\(\varphi_{\ell-1}>0\). \(\square\)

Combining Lemmas 5.1 and 5.2 gives

\[
\boxed{\varphi_s(R(x))>0
       \quad\text{for every }0\leq x\leq x_0\text{ and every }s\geq2.} \tag{5.10}
\]

## 6. The missing prefix lemma is proved

### Theorem 6.1 (uniform macroscopic complete-prefix rate)

For every fixed \(\delta>0\), there is \(C_\delta>0\) such that,
uniformly for \(0\leq x\leq x_0\), every complete prefix of the capped
profile with \(s\geq2\) and

\[
 \delta\leq Z_s=\sum_{i=1}^s z_i\leq1-\delta
\]

satisfies

\[
\boxed{\Phi_s(x)\geq C_\delta.}                       \tag{6.1}
\]

#### Proof

The cap \(c(x)\), residual mean \(R(x)\), exponential-family
parameter \(\mu(x)\), and every fixed residual prefix rate are continuous
on the compact interval \([0,x_0]\).  The uniform bound
\(\mu(x)<2.68\) implies the uniform Gaussian-tail estimate

\[
 \sup_{0\leq x\leq x_0}\sum_{i>s}y_i(x)\longrightarrow0.
\]

If \(Z_s\leq1-\delta\), then the full tail mass
\((1-c)\sum_{i>s}y_i\) is at least \(\delta\).  Hence all prefixes
appearing in (6.1) have \(s\leq S_\delta\) for some finite integer
\(S_\delta\) independent of \(x\).  By (3.6) and (5.10), each of
the finitely many continuous functions
\((1-c(x))\varphi_s(R(x))\), \(2\leq s\leq S_\delta\), is
strictly positive on \([0,x_0]\).  The minimum over this finite family
and compact interval is a positive number \(C_\delta\). \(\square\)

This closes the exact target lemma stated in Section 3 of the candidate note,
at the limiting continuous-profile level.

## 7. What the theorem does not close: an exact counterexample

The full largest-class prefix has

\[
 \Phi_1(x)=\psi_x(c(x))=0.                              \tag{7.1}
\]

Fix any \(\delta\in(0,c(x_0))\).  Since \(c(x)\) is continuous and
increasing from zero to \(c(x_0)\), there are phases with
\(\delta\leq c(x)\leq1-\delta\).  At any such phase, take the
partial profile

\[
 \lambda_1=c(x),\qquad \lambda_i=0\quad(i\geq2).       \tag{7.2}
\]

It has macroscopic mass in \([\delta,1-\delta]\) and rate zero.
Therefore the following stronger statement is false:

\[
 \inf_{\substack{0\leq x\leq x_0,\ 0\leq\lambda\leq z(x)\\
                       \delta\leq\sum_i\lambda_i\leq1-\delta}}
 \Phi_x(\lambda)>0.                                    \tag{7.3}
\]

The greedy-prefix lemma and Theorem 6.1 show that this is the only limiting
complete-prefix equality apart from the empty and complete profiles: every
\(s\geq2\) proper prefix has positive rate, and fractional-prefix rates are
controlled by concavity between adjacent endpoint rates.  But the equality
(7.1) is enough to prevent the quantitative partial-profile hypothesis used
in the existing second-moment theorem.

Replacing \(c(x)\) by \(c(x)-\rho_n\) makes the largest-prefix rate
positive when \(x>0\).  The resulting perturbation has a useful exact form,
proved next.  It shows that no new *limiting* complete-prefix obstruction
appears, but it does not provide the finite-\(n\) quantitative slack.

### 7.1 Exact identity for every slackened cap

Fix \(0\leq d\leq c(x)\), put \(z_1=d\), and re-optimize the residual
coordinates.  Thus

\[
 R_d=\frac{T-d}{1-d},\qquad
 z_i=(1-d)y_i^{(d)},\quad
 y_i^{(d)}\propto e^{\mu_di-qi^2/2}\quad(i\geq2).             \tag{7.4}
\]

If \(a_s^{(d)}=\sum_{i>s}y_i^{(d)}\) and
\(\varphi_s(R_d)\) denotes the residual prefix rate, the same calculation as
in (3.4), without setting \(d=c\), gives

\[
\boxed{
 \Phi_s^{(d)}=(1-d)\varphi_s(R_d)
                 +a_s^{(d)}\psi_x(d),\qquad s\geq1,}         \tag{7.5}
\]

where the empty residual prefix is used when \(s=1\).  Indeed, the correction
term before multiplication by the residual tail mass is

\[
 -\ln(1-d)-\frac q2(R_d-T),
\]

and multiplication by \(1-d\) turns it exactly into

\[
 -(1-d)\ln(1-d)-\frac q2d(T-1)=\psi_x(d).                    \tag{7.6}
\]

The residual rates in (7.5) are positive throughout the entire slack range.
To see this without invoking any new numerical grid, note that
\(R_d\) increases with \(d\), while

\[
 T(x)>1+\frac2{0.694}-0.03>3.85,
 \qquad R_d\leq R_{c(x)}<3.92.                               \tag{7.7}
\]

The exact-rational certifier additionally gives

\[
 m(2.61)=3.8421016485\ldots<3.85,
 \qquad m(2.68)=3.9306642433\ldots>3.92.                    \tag{7.8}
\]

Hence \(2.61<\mu_d<2.68\), and monotonicity gives the coarse bounds

\[
 0.10<y_2^{(d)}<0.12,\qquad0.26<y_3^{(d)}<0.29.              \tag{7.9}
\]

Repeating (5.3)--(5.4) yields

\[
 \varphi_2(R_d)>0.0100512,
 \qquad \varphi_3(R_d)>0.0578716,                            \tag{7.10}
\]

and Lemma 5.2 propagates positivity to every \(s\geq4\).
Since \(\psi_x(d)>0\) for \(0<d<c(x)\), (7.5) proves that every
nontrivial proper complete prefix of a strictly slackened limiting profile
has positive rate.  The greedy-prefix and concavity argument then handles
fractional prefixes as well.

The exact size of the slack gain can also be isolated.  Write

\[
 g(z)=\sum_{m\geq2}\frac{z^{m-1}}{m(m-1)}.
\]

The power-series form of \(\psi_x\), together with the root equation at
\(c\), gives

\[
 \psi_x(d)=d\{g(c)-g(d)\}.                                   \tag{7.11}
\]

For \(0\leq z\leq c<0.021\),

\[
 \frac12\leq g'(z)=\sum_{m\geq2}\frac{z^{m-2}}m
 \leq\frac1{2(1-c)}.                                         \tag{7.12}
\]

Consequently, for additive slack \(d=c-\rho\), \(0<\rho<c\),

\[
\boxed{
 \frac{(c-\rho)\rho}{2}
 \leq\psi_x(c-\rho)
 \leq\frac{(c-\rho)\rho}{2(1-c)}.}                          \tag{7.13}
\]

For proportional slack \(d=(1-\eta)c\), \(0<\eta<1\), this reads

\[
 \frac{\eta(1-\eta)c^2}{2}
 \leq\psi_x((1-\eta)c)
 \leq\frac{\eta(1-\eta)c^2}{2(1-c)}.                        \tag{7.14}
\]

Since \(c(x)\sim qx\) as \(x\downarrow0\), (7.14) proves the endpoint
asymptotic

\[
 \psi_x((1-\eta)c(x))
 \sim\frac{q^2}{2}\eta(1-\eta)x^2.                          \tag{7.15}
\]

Likewise, if \(\rho=o(c)\), (7.13) gives

\[
 \psi_x(c-\rho)\sim\frac{c\rho}{2}
                  \sim\frac{qx\rho}{2}.                     \tag{7.16}
\]

These formulas explain both why an arbitrarily small slack is enough at a
fixed positive phase and why an additive prescription \(\rho=o(c(x))\) is
awkward as \(x\to0\).

There is a cleaner uniform prescription.  For a deterministic
\(\rho_n\downarrow0\), set

\[
 d_n(x)=(c(x)-\rho_n)_+.                                     \tag{7.17}
\]

If \(c(x)\leq\rho_n\), this simply uses the \(i\geq2\) optimizer; no
largest-class prefix exists.  If \(c(x)>\rho_n\), (7.13) supplies the
slack rate.  Combining (7.5), (7.10), the greedy-prefix lemma, and concavity
gives the following continuum statement.

> **Uniform slack-rate lemma.**  For every fixed \(\delta>0\), there is a
> constant \(K_\delta>0\), independent of \(n\), \(x\), and \(\rho_n\),
> such that every greedy partial prefix of the re-optimized profile (7.17)
> with total mass in \([\delta,1-\delta]\) has limiting rate at least
> \(K_\delta\rho_n\), for all sufficiently large \(n\) with
> \(0<\rho_n<1\).

Here is the only noncompact part of the proof.  If a largest-only partial
prefix has mass \(L\geq\delta\), then \(L\leq d_n=c-\rho_n\), and
(7.11)--(7.12) give

\[
 \psi_x(L)=L\{g(c)-g(L)\}\geq\frac{\delta\rho_n}{2}.         \tag{7.18}
\]

On the segment between the full largest-class prefix and the next prefix,
if \(d_n\geq\delta/2\), its left endpoint has rate at least
\(\delta\rho_n/4\) by (7.13); if \(d_n<\delta/2\), every mass
\(L\geq\delta\) uses a \(\delta/2\)-sized fraction of the uniformly
positive residual prefix from (7.10).  Concavity gives the same lower bound
throughout the segment.  All subsequent macroscopic segments have uniformly
positive endpoint rates by the residual prefix theorem and the uniform tail
argument from Theorem 6.1; the endpoints at total masses zero and one are
excluded by \(\delta\).  Reducing the resulting constant if necessary proves
the lemma.

This identifies a plausible finite-\(n\) slack scale.  The error in the
available general rate expansion (Lemma 3.3 of the tame-colourings paper) is

\[
 O\!\left(\frac{n\ln\ln n}{\ln n}\right),                   \tag{7.19}
\]

and the logarithm of the binomial-product term in its partial-profile
condition is at most \(O(n/\ln n)\).  Thus a choice such as

\[
 \rho_n=(\ln n)^{-1/2},\qquad
 \frac{\ln\ln n}{\ln n}=o(\rho_n),                           \tag{7.20}
\]

would make the continuum slack contribution
\(K_\delta n\rho_n\) dominate both scales, including as \(x\to0\) because
(7.17) then switches to \(d_n=0\).

This is a sufficient *rate-scale calculation*, not a finite-\(n\) profile
theorem.  What still has to be proved is that an integer profile can preserve
the truncated mass and mean, remain near enough to the required first-moment
threshold, and inherit (7.19) uniformly when \(x=x(n)\) approaches a cycle
boundary.  Moreover, the existing general second-moment theorem assumes a
fixed power margin \(\mu_a\geq n^{1+\varepsilon}\); when \(x(n)\to0\), that
hypothesis fails independently of the prefix-rate calculation.  Formulae
(7.5) and (7.13) isolate the slack bottleneck, but they do not remove these
finite-\(n\) and theorem-uniformity obligations.

## 8. Audit of `constrained_profile.py`

The original script correctly implements the intended limiting formulas and
its reported grid values are reproducible.  It is suitable as exploratory
numerics, with these precise limitations:

1. `IMAX = 120` truncates the infinite discrete Gaussian and renormalizes it
   without an explicit tail interval.  The omitted tail is astronomically
   small in this parameter range, but the script does not prove that fact.
2. One hundred bisection iterations do not create one hundred bits of
   accuracy in binary64 arithmetic; iterations after machine precision are
   inert.
3. The 1001-point phase grid cannot certify a continuum minimum.  The printed
   value \(0.0287835313\ldots\) is a grid minimum, as the script says, not
   a proof of (6.1).
4. The filter \(0.001\leq Z_s\leq0.999\) checks only the example
   \(\delta=0.001\).  It also omits fractional prefixes.  The latter omission
   is justified for nonnegativity by the exact concavity reduction, but the
   zero endpoint at \(s=1\) remains decisive for strict bounds.
5. Direct evaluation of \(\psi_x(z)\) suffers cancellation when both
   \(x\) and \(z\) are extremely small.  The parametrization (3.7) is a
   more stable way to cover that endpoint.

The companion script
`research/experiments/constrained_profile_certify.py` does not replace the
exploratory scan.  It supplies exact-rational certificates for the coarse
bounds used in Lemma 5.1 and explicitly bounds its infinite tail.  Together
with the analytic residual identity and propagation lemma, those certificates
prove Theorem 6.1 without directed interval scanning over \(x\).

## 9. Corrected status

| Item | Audited status |
|---|---|
| Capped KKT optimizer | **Correct**, conditional on the established unconstrained transition; strict concavity makes the cap active below \(x_0\). |
| Prefix-only reduction | **Exact** for the limiting rate and coordinate box, by the exchange argument; fractional last coordinates are handled by concavity. |
| Uniform prefix-rate lemma for \(s\geq2\) | **Proved here** on all \(0\leq x\leq x_0\). |
| Uniform positive rate for every macroscopic subprofile at the cap | **False**; (7.2) is an explicit zero-rate counterexample. |
| Re-optimized limiting slack profile | **Proved here:** exact identity (7.5), quantitative slack bounds (7.13)--(7.16), and the uniform \(K_\delta\rho_n\) macroscopic rate for (7.17). |
| Slackened finite-\(n\) profile | **Open**; (7.20) is a sufficient rate scale, but uniform phase, objective loss, integer rounding, and theorem-hypothesis bounds remain. |
| Signed/two-graph second moment at the full shift | **Open and independent** of this limiting prefix lemma. |
