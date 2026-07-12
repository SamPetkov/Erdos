# Exact common partial diagonals for the four-size profile

**Status.**  This note proves the exact-common, or partial-diagonal, part of
the four-type high-matching lemma in `ALPHA_MINUS_TWO_ROUTE.md`.  Under the
high signed-first-moment hypothesis used there, the sum of **all** exact
common-subprofile terms is in fact

\[
 \sum_{0\leq \boldsymbol\ell\leq\mathbf k}
 A_{\boldsymbol\ell}^{\rm common}=1+o(1).                 \tag{0.1}
\]

This is stronger than the required
`exp{o(n/(ln n)^4)}` bound.  The proof is uniform through the whole
independence-number phase.  This note itself does not bound unequal-size
containments; Section 7 states the comparison that was still needed here.
That comparison is subsequently proved in
`DENSE_FOUR_TYPE_MATCHING.md`, Lemmas 2.1--3.1.

Throughout,

\[
 q=\ln2,\qquad N=\ln n,\qquad w=\ln N,
 \qquad u_i=\alpha-i\quad (i\in S:=\{2,3,4,5\}).          \tag{0.2}
\]

Let `K` be the number of classes and let

\[
 \sum_i k_i=K,\qquad \sum_i u_i k_i=n,
 \qquad p_i=\frac{k_i}{K},\qquad
 T=\sum_i i p_i=\alpha-\frac nK.                         \tag{0.3}
\]

We assume

\[
 \frac2q\leq T\leq1+\frac2q,\qquad
 \min_i p_i\geq c_*>0,                                  \tag{0.4}
\]

and that the complete signed first moment satisfies, for some fixed
`c_0>0`,

\[
 Z_{\mathbf k}^{\rm sgn}
 =2^K\frac{n!}{\prod_i(u_i!)^{k_i}k_i!}
       2^{-\sum_i\binom{u_i}{2}k_i}
 \geq e^{c_0K}.                                          \tag{0.5}
\]

The midpoint profile in Section 6 of `ALPHA_MINUS_TWO_ROUTE.md` has (0.5),
with `K=Theta(n/N)`.  Section 1 below verifies (0.4) and the harmlessness of
integer rounding for its finite-support entropy maximizer.
All estimates are unchanged if the displayed interval for `T` is enlarged
by `o(1)`: the strict constants in Lemma 3.2 have fixed slack, and this
covers the finite-`n` shift of the exact midpoint integer profile at both
phase endpoints.

## 1. The four-type optimizer and integer rounding

At prescribed mean `T`, maximize

\[
 -\sum_{i=2}^5p_i\ln p_i-\frac q2\sum_{i=2}^5i^2p_i
 \quad\hbox{subject to}\quad
 \sum_i p_i=1,\quad\sum_i i p_i=T.                       \tag{1.1}
\]

The unique maximizer is

\[
 p_i(T)=\frac{e^{\mu(T)i-qi^2/2}}
                 {\sum_{j=2}^5e^{\mu(T)j-qj^2/2}},       \tag{1.2}
\]

where the tilted mean is `T`.  The elementary tilt certificate in
`ALPHA_MINUS_TWO_ROUTE.md`, Proposition 3.1, gives

\[
 2q<\mu(T)<\frac92q                                      \tag{1.3}
\]

uniformly on the interval (0.4).  For a fixed value of `mu` in this
interval, the logarithms base `2` of the four unnormalised weights in
(1.2) differ by at most `9/2`.  Consequently the explicit bound

\[
 \boxed{\displaystyle p_i(T)\geq
        \frac1{4\,2^{9/2}}>\frac1{91}\quad(2\leq i\leq5)} \tag{1.4}
\]

holds for every phase.  Thus all four coordinates are uniformly positive,
not merely positive separately for each fixed phase.

For completeness, an exact integer profile loses nothing on any scale used
below.  Let `p_i^{(n)}` be the exact finite-`n` maximizer of the continuous
functional `L_{S_4}(n,K)`, using the exact weights
`d_{u_i}=2^{binom(u_i,2)}u_i!` (the added signed term `qK` is constant at
fixed `K`).
Uniform convergence and strict concavity give
`p_i^{(n)}=p_i(T)+o(1)` uniformly in the phase, so (1.4), with `1/91`
replaced harmlessly by `1/92`, holds for this exact optimizer.  Round
`Kp_i^{(n)}` initially.  If the resulting errors in the two constraints are
`e_0,e_1=O(1)`, the correction

\[
 \Delta k_2=e_1-3e_0,\qquad
 \Delta k_3=2e_0-e_1                                    \tag{1.5}
\]

enforces both constraints exactly and changes every coordinate by `O(1)`.
By (1.4), all coordinates remain positive for large `n`.  The correction is
tangent to both linear constraints and starts at the exact finite-`n`
optimizer, so the first variation of the optimized profile functional
vanishes.  Stirling's formula then gives

\[
 \ln Z_{\mathbf k}^{\rm sgn}
 =\ln Z_{K\mathbf p^{(n)}}^{\rm sgn}+O(\ln n).           \tag{1.6}
\]

In particular, an `Omega(K)` margin in (0.5) survives rounding.  All the
estimates below are written for the resulting exact integer vector, so no
later appeal to a nonintegral profile is made.

## 2. Exact identities and the two endpoint recurrences

For a subprofile $\boldsymbol\ell=(\ell_i)$, put

\[
 L=\sum_i\ell_i,\qquad m=\sum_i u_i\ell_i,
 \qquad M=\sum_i\binom{u_i}{2}\ell_i.                    \tag{2.1}
\]

Its signed partial-partition first moment is

\[
 Y_{\boldsymbol\ell}^{\rm sgn}
 =2^L\frac{n!}{(n-m)!\prod_i(u_i!)^{\ell_i}\ell_i!}
       2^{-M}.                                            \tag{2.2}
\]

The exact common-subprofile contribution is

\[
 \boxed{\displaystyle
 A_{\boldsymbol\ell}
 =\frac{\prod_i\binom{k_i}{\ell_i}^{2}}
        {Y_{\boldsymbol\ell}^{\rm sgn}}.}               \tag{2.3}
\]

Here `A_0=1` and
`A_{mathbf k}=1/Z_{mathbf k}^{sgn}`.  Adding one selected common block gives
the exact recurrence

\[
 \boxed{\displaystyle
 \frac{A_{\boldsymbol\ell+\mathbf e_i}}
      {A_{\boldsymbol\ell}}
 =\frac{(k_i-\ell_i)^2}
        {2(\ell_i+1)\mu_{u_i}(n-m)},}                    \tag{2.4}
\]

where

\[
 \mu_s(v)=\binom vs2^{-\binom s2}.                       \tag{2.5}
\]

There is a second exact representation at the other endpoint.  Put
$\mathbf r=\mathbf k-\boldsymbol\ell$,
$v=\sum_i u_i r_i$, and let $Z_{\mathbf r}^{\rm sgn}(v)$ be the signed first
moment of complete partitions of $v$ vertices with profile $\mathbf r$.  Then

\[
 A_{\mathbf k-\mathbf r}
 =\frac{B_{\mathbf r}}{Z_{\mathbf k}^{\rm sgn}},\qquad
 B_{\mathbf r}:=\left(\prod_i\binom{k_i}{r_i}\right)
                    Z_{\mathbf r}^{\rm sgn}(v).          \tag{2.6}
\]

Starting with `B_0=1`, addition of a residual block gives

\[
 \boxed{\displaystyle
 \frac{B_{\mathbf r+\mathbf e_i}}{B_{\mathbf r}}
 =\frac{2(k_i-r_i)\mu_{u_i}(v+u_i)}{(r_i+1)^2}.}          \tag{2.7}
\]

Both formulas retain every factorial.  Thus the endpoint arguments below
do not replace `(n)_m` by `n^m` in a range where that replacement is false.

## 3. The finite-dimensional central rate

We next derive a direct rate bound for (2.3).  Write

\[
 y_i=\frac{\ell_i}{K},\quad Y=\sum_i y_i,\quad
 I=\sum_i i y_i,\quad R=1-Y,                             \tag{3.1}
\]

and, for the residual vector `z_i=p_i-y_i`, write

\[
 I_r=\sum_i i z_i=T-I.                                   \tag{3.2}
\]

The residual vertex fraction is

\[
 \rho=\frac{n-m}{n}
 =R+\frac{I-TY}{\alpha-T}.                               \tag{3.3}
\]

Define the limiting rate

\[
 \boxed{\displaystyle
 \Phi_T(\mathbf z)
 :=R\ln R+\frac q2(I_r-TR).}                             \tag{3.4}
\]

The convention is `0 ln 0=0`.

### Lemma 3.1 (uniform rate extraction)

There is a constant `C`, independent of the phase, such that whenever
`rho>=1/32` (and hence `R>=1/64` for large `n`),

\[
 \boxed{\displaystyle
 \ln A_{\boldsymbol\ell}
 \leq K\alpha\Phi_T(\mathbf z)
      +CKY\ln\frac eY+C\ln n.}                           \tag{3.5}
\]

#### Proof

Uniform Stirling estimates in (2.3) give

\[
 \ln A_{\boldsymbol\ell}
 =n\rho\ln\rho
  +K\sum_i\left\{
     2p_i\ln p_i-2(p_i-y_i)\ln(p_i-y_i)
     -y_i\ln y_i-y_i+y_iD_i\right\}
  +O(\ln n),                                             \tag{3.6}
\]

where

\[
 D_i=\ln K+\ln(u_i!)+u_i-u_i\ln n
          +q\binom{u_i}{2}-q.                            \tag{3.7}
\]

The error in (3.6) is uniform even when some `ell_i` or `k_i-ell_i`
vanishes, by using
`ln(t!)=t ln t-t+O(ln(t+1))` with the usual zero convention.

For `u_i=alpha-i`, exact subtraction gives

\[
 D_{i+1}-D_i
 =N-\ln(\alpha-i)-q(\alpha-i)+q-1.                       \tag{3.8}
\]

The defining expansion of `alpha` implies

\[
 D_{i+1}-D_i=-\frac{q\alpha}{2}+O(1)                    \tag{3.9}
\]

uniformly for `i=2,3,4`.  Let
$\bar D=\sum_i p_iD_i$.  Because $\sum_i p_i(i-T)=0$, (3.9) yields

\[
 D_i=\bar D+\frac{q\alpha}{2}(T-i)+O(1).                 \tag{3.10}
\]

Applying Stirling once to the complete moment gives

\[
 -\frac1K\ln Z_{\mathbf k}^{\rm sgn}
 =\sum_i p_i\ln p_i-1+\bar D+o(1).                       \tag{3.11}
\]

Hypothesis (0.5) therefore bounds $\bar D$ above by an absolute constant.
It follows that

\[
 \sum_i y_iD_i
 \leq\frac{q\alpha}{2}(TY-I)+O(Y).                       \tag{3.12}
\]

By (1.4), the remaining entropy expression in (3.6) is at most

\[
 C Y\ln\frac eY.                                         \tag{3.13}
\]

Finally, (3.3), `n=K(alpha-T)`, and the Lipschitz continuity of
`x ln x` on `[1/64,1]` give

\[
 n\rho\ln\rho=K\alpha R\ln R+O(KY).                    \tag{3.14}
\]

Substitution of (3.12)--(3.14) in (3.6) proves (3.5).
\(\square\)

### Lemma 3.2 (analytic negativity; no grid certificate)

Uniformly for
`2/q<=T<=1+2/q`, every `0<=z_i<=p_i` satisfies

\[
 \Phi_T(\mathbf z)\leq0,                                 \tag{3.15}
\]

with equality only at $\mathbf z=0$ and $\mathbf z=\mathbf p$.  More
quantitatively, whenever `R>=1/64`,

\[
 \boxed{\displaystyle
 \Phi_T(\mathbf z)\leq-\gamma Y,qquad
 \gamma=\frac1{5000}.}                                  \tag{3.16}
\]

#### Proof

Two bounds, using only the endpoints `2` and `5` of the support, suffice.
First,

\[
 I_r-TR\leq(5-T)R,                                       \tag{3.17}
\]

so

\[
 \Phi_T\leq R\left\{\ln R+\frac q2(5-T)\right\}.       \tag{3.18}
\]

Second, since $\mathbf y=\mathbf p-\mathbf z$,

\[
 I_r-TR=\sum_i(T-i)y_i\leq(T-2)(1-R),                   \tag{3.19}
\]

and hence

\[
 \Phi_T\leq R\ln R+\frac q2(T-2)(1-R).                 \tag{3.20}
\]

Put

\[
 a_*:=1-\frac q2,qquad b_*:=\frac{5q}{2}-1.             \tag{3.21}
\]

The coefficients in (3.20) and (3.18) are at most `a_*` and `b_*`,
respectively.  For `R<=47/100`, (3.18) is strictly negative because

\[
 \ln(47/100)+b_*<0.                                      \tag{3.22}
\]

For `47/100<=R<=1`, use (3.20).  The function

\[
 R\ln R+(a_*+1/200)(1-R)                                \tag{3.23}
\]

is convex, is zero at `R=1`, and is negative at `R=47/100`.
Thus (3.20) is at most `-(1-R)/200` throughout this interval.
For a completely rational certificate of the two strict endpoint checks,
use

\[
 \frac{6931}{10000}<q<\frac{6932}{10000},\qquad
 \ln(47/100)<-\frac34.                                  \tag{3.24}
\]

The first pair follows from the positive `atanh` series for `ln 2`; the
last inequality is equivalent to `e^{3/4}<100/47` and follows, for example,
by bounding the positive exponential series and its geometric tail.
At the left endpoint of (3.23), these bounds give

\[
 \frac{47}{100}\ln\frac{47}{100}
 +\left(1-\frac{6931}{20000}+\frac1{200}\right)
       \frac{53}{100}
 <-0.0035,                                                \tag{3.25}
\]

which is the claimed strict convex-endpoint margin.

More explicitly, on `1/64<=R<=47/100`,

\[
 \ln R+b_*< -\frac34+\frac52\frac{6932}{10000}-1
 =-\frac{17}{1000},
\]

and hence (3.18) is at most
`-17/64000<-1/5000<=-Y/5000`.  Thus the lower cutoff
`R>=1/64` is used explicitly in the small-`R` part of (3.16).  On the
remaining interval, the stronger `-Y/200` margin just proved implies
(3.16).  Equality in (3.15) can therefore occur only at `R=0` or `R=1`,
which are exactly $\mathbf z=0$ and $\mathbf z=\mathbf p$ because all
coordinates of `p` are positive.  \(\square\)

The rate proof is genuinely finite dimensional but does not require
checking a floating-point list of greedy prefixes.  Equations (3.17) and
(3.19) simultaneously dominate every fractional and nongreedy subprofile.

## 4. Vanishing selected mass: an exact `1+o(1)` sum

Let

\[
 \eta_n:=\frac{w}{32N}.                                  \tag{4.1}
\]

The standard independence-set expansion, uniformly over the phase, gives

\[
 \mu_\alpha(n)\geq cN^{2/q-1/2},\qquad
 \frac{\mu_{s-1}(n)}{\mu_s(n)}=\Theta(n/N)               \tag{4.2}
\]

for the four fixed sizes in question.  Since `k_i=Theta(n/N)`, it follows
that

\[
 \Lambda_n:=\sum_{i=2}^5\frac{k_i^2}{2\mu_{u_i}(n)}
 =O\left(N^{-(2/q-1/2)}\right).                           \tag{4.3}
\]

If a final subprofile has `m<=eta_n n`, then at every stage in (2.4),

\[
 \frac{\mu_{u_i}(n)}{\mu_{u_i}(n-m')}
 \leq(1-2\eta_n)^{-u_i}
 \leq e^{4\eta_n u_i}\leq N^{3/8}                       \tag{4.4}
\]

for all sufficiently large `n`.  Iterating (2.4), in any order, yields

\[
 A_{\boldsymbol\ell}
 \leq\prod_i\frac{(N^{3/8}\lambda_i)^{\ell_i}}{\ell_i!},
 \qquad \lambda_i:=\frac{k_i^2}{2\mu_{u_i}(n)}.          \tag{4.5}
\]

Therefore

\[
 \boxed{\displaystyle
 \sum_{\boldsymbol\ell:\,m\leq\eta_n n}
 A_{\boldsymbol\ell}
 \leq\exp\{N^{3/8}\Lambda_n\}=1+o(1).}                 \tag{4.6}
\]

The empty subprofile contributes exactly one, so the left side of (4.6)
is also at least one.

## 5. Mesoscopic and fixed mass: exponential suppression

Consider now

\[
 m>\eta_n n,qquad n-m>n/32.                              \tag{5.1}
\]

Then `Y>=eta_n/2` and `R>=1/64` for large `n`, because all four block
sizes differ from their mean by only `O(1)`.  Lemmas 3.1 and 3.2 give

\[
 \ln A_{\boldsymbol\ell}
 \leq-\frac{K\alpha Y}{5000}
       +CKY\ln\frac eY+C\ln n.                           \tag{5.2}
\]

Since `alpha=Theta(N)` and
`ln(e/Y)=O(w)` at the lower endpoint `Y=Theta(w/N)`, the second term in
(5.2) is `o(K alpha Y)`.  Hence, uniformly in (5.1),

\[
 A_{\boldsymbol\ell}\leq e^{-cKw}.                       \tag{5.3}
\]

There are at most `(K+1)^4` subprofiles, and consequently

\[
 \boxed{\displaystyle
 \sum_{\boldsymbol\ell\text{ satisfying }(5.1)}
 A_{\boldsymbol\ell}=o(1).}                              \tag{5.4}
\]

For a fixed positive selected and residual vertex mass, (3.16) actually
gives `e^{-Omega(n)}`.  The weaker `e^{-Omega(Kw)}` form in (5.3) is what
allows the cutoff in (5.1) to tend to zero.

## 6. Near-full selected mass: the complete moment pays

It remains to treat `v=n-m<=n/32`.  Uniformly for `i=2,3,4,5`, the exact
independence-set expansion and its adjacent-size ratio give

\[
 \mu_{u_i}(n)\leq n^{6+o(1)}.                             \tag{6.1}
\]

For every `s<=v<=n`,

\[
 \frac{\mu_s(v)}{\mu_s(n)}
 =\frac{(v)_s}{(n)_s}\leq\left(\frac vn\right)^s.        \tag{6.2}
\]

Since `u_i=(2/q+o(1))N`, equations (6.1)--(6.2) imply, whenever
`v<=n/32`,

\[
 \mu_{u_i}(v)
 \leq n^{6+o(1)}32^{-u_i}
 =n^{-4+o(1)}.                                            \tag{6.3}
\]

Choose any order for adding the residual blocks in (2.7).  Every
intermediate vertex count is at most the final count `v`, so (6.3) and
`k_i<=n` show that every ratio in (2.7) is less than one for large `n`.
Thus

\[
 B_{\mathbf r}\leq1.                                     \tag{6.4}
\]

By (2.6) and (0.5),

\[
 A_{\mathbf k-\mathbf r}\leq e^{-c_0K}.                 \tag{6.5}
\]

Summing over at most `(K+1)^4` residual vectors proves

\[
 \boxed{\displaystyle
 \sum_{\boldsymbol\ell:\,n-m\leq n/32}
 A_{\boldsymbol\ell}=o(1).}                              \tag{6.6}
\]

Combining (4.6), (5.4), and (6.6) proves (0.1).

## 7. What this does and does not prove about off-diagonal containments

The result closes every exact partial diagonal, including vanishing mass,
every fixed positive mass, near-full mass, and the full diagonal.  In the
notation of `RESIDUAL_ATTACHMENT.md`, it proves the diagonal specialization
of the dense `4 by 4` transportation sum.

It does **not** compare an unequal-size containment matrix with its diagonal
counterpart.  One sufficient remaining statement is the following.  If the
off-diagonal and near-containment decoration sum conditional on an exact
common vector $\boldsymbol\ell$ is $D_{\rm off}(\boldsymbol\ell)$ and

\[
 \sup_{\boldsymbol\ell}\ln D_{\rm off}(\boldsymbol\ell)
 =o(n/N^4),                                               \tag{7.1}
\]

with only polynomially many typed transportation matrices per vector, then
(0.1) immediately gives

\[
 \sum_{\boldsymbol\ell}
 A_{\boldsymbol\ell}D_{\rm off}(\boldsymbol\ell)
 \leq\exp\{o(n/N^4)\}.                                   \tag{7.2}
\]

More generally it is enough to construct a polynomial-to-one map from each
typed off-diagonal matrix $L$ to a common vector $\boldsymbol\ell(L)$ such
that

\[
 W(L)\leq A_{\boldsymbol\ell(L)}\exp\{o(n/N^4)\}         \tag{7.3}
\]

uniformly.  Neither (7.1) nor (7.3) is asserted here.  The one-containment
activities and all residual attachments are already small, but the dense
finite-population factor in a general `4 by 4` transportation matrix still
requires this separate comparison.

## 8. Audit checklist

1. **All quantifiers are phase-uniform.**  The only phase inputs are the
   compact interval for `T`, the four fixed sizes, and the uniform complete
   first-moment margin (0.5).
2. **No numerical prefix grid is used.**  The rate certificate is the
   analytic pair (3.18), (3.20), with the elementary rational bounds (3.24).
3. **Both singular corners use exact recurrences.**  Stirling and compactness
   are used only when the residual vertex mass is at least `n/32`; the
   vanishing and near-full corners retain all falling factorials.
4. **The full moment is used only where needed.**  It bounds $\bar D$ in the
   central rate and supplies the denominator in (6.5).  No ordinary
   first-moment lower bound is assumed.
5. **Rounding is tangent to both constraints.**  Hence it costs only
   `O(ln n)`, which is negligible relative to the `Theta(K)` margin in
   (0.5), the `Omega(Kw)` central suppression, and the target `n/N^4`.
