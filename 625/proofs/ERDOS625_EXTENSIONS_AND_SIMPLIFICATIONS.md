# Erdős Problem 625: result extensions and proof simplifications

**Status.** This note records deductions and replacement arguments obtained by
re-examining the candidate manuscript at repository `main` commit
`cda78922ea6c87bfc81f9bf693374dd045dac624`.  It separates:

- exact deductions that can be inserted after ordinary mathematical review;
- exact finite inequalities whose attached script checks by rational arithmetic;
- numerical diagnostics and architectural alternatives that still require a
  full replay of the proof chain.

Nothing here is external peer review, priority verification, or a completed
Lean proof of `Erdos625Statement`.

Throughout,

\[
 q=\ln2,\qquad N=\ln n,
\]

and `D_4(delta)` is the four-support entropy loss in equation (5.2) of the
canonical manuscript.

---

## 1. Exact simplification of the large-residual attachment bound

The cycle decomposition and cycle-to-walk estimates in equations
(9.15)--(9.18) are not needed at the precision required by Proposition 9.2.
The matching structure gives a direct weighted restriction injection.

### Lemma 1.1 (an even completion of residual edges is unique)

Let `M` be a matching in a finite graph and let `R` be any other finite edge
set.  Let

\[
 \mathcal E(M,R)
 =\{F\subseteq M\cup R:\deg_F(v)\equiv0\pmod2\ \text{for every }v\}.
\]

Then

\[
 \rho:\mathcal E(M,R)\longrightarrow\mathcal P(R\setminus M),
 \qquad
 \rho(F)=F\setminus M,
 \tag{1.1}
\]

is injective.

#### Proof

If `rho(F)=rho(F')`, then the symmetric difference `F triangle F'` is contained
in `M`.  It is also even, because the symmetric difference of two even edge
sets is even.  A nonempty subset of a matching has degree one at every incident
vertex, so it cannot be even.  Hence `F triangle F'` is empty and `F=F'`.
\(\square\)

Equivalently, after the residual edges are specified, parity forces every
matching edge that can occur; some residual subsets have no completion, but
none has two.

### Corollary 1.2 (weighted product bound)

For nonnegative residual weights `(q_e)`, extended by zero on `M`,

\[
 \sum_{F\in\mathcal E(M,R)}\prod_{e\in F\setminus M}q_e
 \le
 \sum_{S\subseteq R\setminus M}\prod_{e\in S}q_e
 =\prod_{e\in R\setminus M}(1+q_e)
 \le\exp\left(\sum_e q_e\right).
 \tag{1.2}
\]

This is the weighted form of the restriction injection already present in the
Lean development as `residualRestriction_injective`; the generic
product-to-exponential endpoint is already present as
`finiteInjectiveFamily_product_exp_bound`.

### Application to Lemma 9.1

Equation (9.12) gives

\[
 \mathcal A(M,j)
 \le e^{\Lambda_0}
 \sum_{F\in\mathcal C_{\rm even}(M,R)}
      \prod_{e\in F\setminus M}q_e.
 \tag{1.3}
\]

Therefore Corollary 1.2 gives immediately

\[
 \mathcal A(M,j)
 \le\exp\left(\Lambda_0+\sum_e q_e\right).
 \tag{1.4}
\]

Using the definitions in (9.5)--(9.6),

\[
 \sum_e q_e
 =\frac12\sum_{a,b}\theta_{ab}^2+\Lambda_0.
 \tag{1.5}
\]

The degree sums factor exactly:

\[
 \sum_{a,b}\theta_{ab}^2
 =\frac{e^2}{m_0^2}
   \left(\sum_a d_a^2\right)
   \left(\sum_b(d'_b)^2\right).
 \tag{1.6}
\]

Since every residual degree is at most `U` and both degree sums are `m_0`,

\[
 \sum_a d_a^2\le Um_0,
 \qquad
 \sum_b(d'_b)^2\le Um_0,
 \tag{1.7}
\]

so

\[
 \sum_{a,b}\theta_{ab}^2\le e^2U^2.
 \tag{1.8}
\]

Together with (9.13), this yields the stronger uniform estimate

\[
 \boxed{
 \mathcal A(M,j)
 \le\exp\left\{C\left(U^2+\frac{U^4}{m_0}\right)\right\}.}
 \tag{1.9}
\]

In the large-residual regime `m_0 >= n/N^6` and `U=O(N)`,

\[
 \mathcal A(M,j)\le\exp(CN^2),
 \tag{1.10}
\]

which is stronger than the current `exp(CN^8)` bound and still
`exp(o(n/N^4))`.

This replacement removes from the manuscript proof:

- deterministic simple-cycle decompositions;
- residual-only walk enumeration;
- mixed matching-cycle encodings;
- the row-norm parameter `tau` and the `h tau` term;
- equations (9.15)--(9.18).

Those formalized cycle and traversal modules remain independently useful, but
they are no longer logically required for the displayed second-moment bound.

---

## 2. A stronger and simpler central partial-diagonal rate

The rate estimate in Lemma 7.1 can be strengthened from `Y/5000` to `Y/100`
without changing the split point.

### Lemma 2.1

Under the hypotheses and notation of Lemma 7.1A in the review rewrite,

\[
 \boxed{\Phi_T(z)\le-\frac{1-R}{100}}
 \qquad(1/64\le R\le1).
 \tag{2.1}
\]

#### Proof

For `1/64 <= R <= 47/100`, use

\[
 \Phi_T(z)\le R\ln R+(5q/2-1)R.
 \tag{2.2}
\]

The convex function

\[
 f(R)=R\ln R+(5q/2-1)R+\frac{1-R}{100}
 \tag{2.3}
\]

satisfies

\[
 f(1/64)<-0.0436,
 \qquad
 f(47/100)<-0.0051.
 \tag{2.4}
\]

It is therefore nonpositive throughout that interval.  For
`47/100 <= R <= 1`, use

\[
 \Phi_T(z)\le R\ln R+(1-q/2)(1-R).
 \tag{2.5}
\]

The convex function

\[
 h(R)=R\ln R+(1-q/2+1/100)(1-R)
 \tag{2.6}
\]

has `h(47/100)<-0.0032` and `h(1)=0`, so it is nonpositive on the second
interval.  This proves (2.1). \(\square\)

This does not alter the final order, but it makes the domination of the entropy
and Stirling errors substantially less delicate.

---

## 3. Carry the phase-resolved root displacement to the theorem

The current proof obtains the sharp phase-dependent root displacement in
(5.11), then discards most of it through two safety halvings.  That loss is not
structural.

Define

\[
 A(\delta)=q-D_4(\delta),
 \qquad
 A_*:=\min_{0\le\delta\le1}A(\delta).
 \tag{3.1}
\]

The value functions in Section 3 are continuous, so `A` is continuous.  Lemma
5.1 gives `A(delta)>gamma_4` on the compact closed phase interval, where

\[
 \gamma_4=\ln(200/153).
 \tag{3.2}
\]

Consequently `A_*>gamma_4`.

Using (5.11) directly and the midpoint definition (5.13), rather than replacing
(5.11) by (5.12), gives

\[
 k_\chi^- - k_{co}
 =\left(\frac{q^2}{8}A(\delta)+o(1)\right)\frac{n}{N^3}.
 \tag{3.3}
\]

The amplification loss is `o(n/N^3)`, hence the proof yields the stronger
phase-resolved conclusion

\[
 \boxed{
 \chi(G_n)-\zeta(G_n)
 \ge\left(\frac{q^2}{8}A(\delta_n)-o(1)\right)
       \frac{n}{N^3}}
 \quad\text{with high probability}.
 \tag{3.4}
\]

In particular, the explicit phase-independent constant can be increased from

\[
 \frac{q^2\gamma_4}{32}
 \quad\text{to}\quad
 \frac{q^2\gamma_4}{8}.
 \tag{3.5}
\]

This is a factor-four improvement that changes no profile, overlap estimate, or
amplification argument.

---

## 4. An elementary stronger four-support entropy certificate

The current certificate uses the broad tilt interval
`2q < lambda_4 < 9q/2`.  A tighter interval gives a cleaner omitted-mass bound.

### Proposition 4.1

For every phase,

\[
 \frac{12}{5}q<\lambda_4<\frac{21}{5}q.
 \tag{4.1}
\]

Moreover, with `L(lambda)` and `H(lambda)` defined as in Lemma 5.1,

\[
 L(12q/5)<3/10,
 \qquad
 H(3q)<1/50,
 \tag{4.2}
\]

and

\[
 L(3q)<3/25,
 \qquad
 H(21q/5)<1/5.
 \tag{4.3}
\]

Hence, splitting at `lambda=3q`,

\[
 L(\lambda_4)+H(\lambda_4)<8/25.
 \tag{4.4}
\]

Therefore

\[
 D_4(\delta)<\ln(33/25),
 \qquad
 q-D_4(\delta)>\ln(50/33).
 \tag{4.5}
\]

#### Certificate

Put `x=2^(1/10)`.  The exact rational intervals

\[
 0.693147<q<0.693148,
 \qquad
 1.071773<x<1.071774
 \tag{4.6}
\]

reduce all new assertions to integer-power inequalities.  For example,
`L(12q/5)<3/10` follows from

\[
 10(1+x^{29}+x^{48})
 <3(x^{57}+x^{56}+x^{45}+x^{24}),
 \tag{4.7}
\]

using the upper endpoint for the left side and the lower endpoint for the right
side.  At `21q/5`, the high tail begins with `x^72` and every subsequent ratio
is at most `x^(-23)`, so

\[
 H(21q/5)
 \le
 \frac{x^{72}}{(1-x^{-23})(x^{64}+x^{81}+x^{88}+x^{85})}
 <\frac15.
 \tag{4.8}
\]

The attached script `experiments/entropy_certificate_upgrade.py` checks the
rational intervals and every displayed comparison using `fractions.Fraction`.
It also verifies the existing `lambda=3q` inequalities.

Combining (3.4) and (4.5) gives the explicit candidate constant

\[
 \boxed{
 c_{\rm improved}
 =\frac{(\ln2)^2}{8}\ln\frac{50}{33}
 =0.0249544559\ldots,}
 \tag{4.9}
\]

compared with the current displayed constant

\[
 \frac{(\ln2)^2}{32}\ln\frac{200}{153}
 =0.0040219839\ldots.
 \tag{4.10}
\]

Thus the two low-risk constant improvements together increase the explicit
coefficient by a factor greater than six.

---

## 5. Complement-symmetric strengthening

The cochromatic number is complement invariant:

\[
 \zeta(\overline G)=\zeta(G).
 \tag{5.1}
\]

Also `G(n,1/2)` and its complement have the same law.  Apply the main theorem to
`G_n` and to `overline G_n` and intersect the two high-probability events.
This gives, with the same admissible constant `c`,

\[
 \boxed{
 \min\{\chi(G_n),\chi(\overline G_n)\}-\zeta(G_n)
 \ge c\frac{n}{(\ln n)^3}}
 \quad\text{with high probability}.
 \tag{5.2}
\]

Thus the candidate argument places the cochromatic number below **both**
chromatic numbers by polynomial scale, not merely below the chromatic number of
one chosen orientation.

---

## 6. Fixed-density criticality away from `p=1/2`

For every deterministic graph,

\[
 \zeta(G)\le\min\{\chi(G),\chi(\overline G)\}.
 \tag{6.1}
\]

For fixed `p in (0,1)`, the standard dense-random-graph asymptotic is

\[
 \chi(G(n,p))
 =\left(\frac12\ln\frac1{1-p}+o(1)\right)\frac{n}{\ln n}.
 \tag{6.2}
\]

Applying the same formula to the complement gives

\[
 \boxed{
 \max\{\chi(G),\chi(\overline G)\}-\zeta(G)
 \ge
 \left(\frac12\left|\ln\frac{p}{1-p}\right|+o(1)\right)
 \frac{n}{\ln n}}
 \tag{6.3}
\]

with high probability for `G~G(n,p)`.

For `p>1/2`, the larger chromatic number is `chi(G)`, so (6.3) is directly a
lower bound for `chi(G)-zeta(G)`.  For `p<1/2`, it is the complementary
chromatic gap.  This identifies `p=1/2` as the unique fixed-density point where
the first-order comparison cancels and the finer `n/(ln n)^3` analysis is
needed.

---

## 7. A standard upper bound narrows the remaining scale

Let

\[
 h(G)=\max\{\alpha(G),\omega(G)\}.
\]

Every coclour class has size at most `h(G)`, so

\[
 \zeta(G)\ge n/h(G).
 \tag{7.1}
\]

The standard second-order estimates for `G(n,1/2)` give

\[
 h(G)=2\log_2n-2\log_2\log_2n+O(1)
 \tag{7.2}
\]

and

\[
 \chi(G)=
 \frac{n}{2\log_2n-2\log_2\log_2n+O(1)}
 \tag{7.3}
\]

with high probability.  The two denominators differ by only `O(1)`, hence

\[
 \boxed{\chi(G)-\zeta(G)=O\left(\frac{n}{(\ln n)^2}\right)}
 \tag{7.4}
\]

with high probability.

Combined with the candidate lower bound, this gives the current scale window

\[
 \frac{n}{(\ln n)^3}
 \ \lesssim\ 
 \chi(G)-\zeta(G)
 \ \lesssim\ 
 \frac{n}{(\ln n)^2}.
 \tag{7.5}
\]

Closing the remaining logarithmic factor would require a substantially sharper
lower bound on `zeta`, not merely another improvement to the signed first
moment.

---

## 8. An exactly certified three-size first-moment alternative

Let

\[
 S_3=\{2,3,5\},
 \qquad
 D_3(\delta)=\mathcal F_{S_+}(T_0)-\mathcal F_{S_3}(T_0).
 \tag{8.1}
\]

The three-size support has a positive uniform signed advantage that can be
proved by the same elementary omitted-mass method as Lemma 5.1.

### Proposition 8.1 (three-size entropy certificate)

For every target

\[
 \frac2q\le T\le1+\frac2q,
\]

let \(\lambda_3\) be the unique tilt for the support \(S_3\).  Then

\[
 \frac{29}{10}q<\lambda_3<\frac{21}{5}q.
 \tag{8.2}
\]

At a tilt \(\lambda\), let \(L_3(\lambda)\) be the weight of deficits
\(-1,0,1\) divided by the retained \(S_3\) weight, let
\(M_4(\lambda)\) be the deficit-4 weight divided by the retained weight, and
let \(H_3(\lambda)\) be the analogous ratio for deficits at least six.  The
following exact bounds hold:

\[
 L_3(29q/10)<\frac15,
 \qquad
 H_3(7q/2)<\frac2{25},
 \qquad
 M_4(7q/2)=\frac12,
 \tag{8.3}
\]

and

\[
 L_3(7q/2)<\frac2{25},
 \qquad
 H_3(21q/5)<\frac14,
 \qquad
 M_4(21q/5)<\frac58.
 \tag{8.4}
\]

Consequently

\[
 L_3(\lambda_3)+M_4(\lambda_3)+H_3(\lambda_3)
 <\frac{191}{200},
 \tag{8.5}
\]

and hence

\[
 \boxed{
 D_3(\delta)<\ln\frac{391}{200},
 \qquad
 q-D_3(\delta)>\ln\frac{400}{391}>0.}
 \tag{8.6}
\]

#### Proof

The mean on a finite support is strictly increasing in the tilt.  At
\(29q/10\), exact rational comparison gives a mean below \(2/q\); at
\(21q/5\), it gives a mean above \(1+2/q\).  This proves (8.2).

The low ratio \(L_3\) decreases with the tilt because every low omitted index
is below every retained index.  The high ratio \(H_3\) increases for the
opposite reason.  The ratio \(M_4\) has logarithmic derivative
\(4-\mathbb E_{S_3,\lambda}i\).  The retained mean is below four throughout
(8.2), so \(M_4\) is increasing on the relevant interval.

Put \(x=2^{1/10}\).  At \(29q/10\), after division by the deficit \(-1\)
weight, the low exponents are \(0,34,58\), while the retained exponents are
\(72,76,54\).  Thus

\[
 5(1+x^{34}+x^{58})<x^{72}+x^{76}+x^{54}
 \tag{8.7}
\]

proves the first bound in (8.3).  At \(7q/2\), the retained weights are
proportional to \(x^{50},x^{60},x^{50}\), while the deficit-4 weight is
\(x^{60}\); hence \(M_4=1/2\).  The low and high bounds at this tilt follow
from the same rational interval for \(x\) and a geometric tail beginning with
exponent \(30\).

At \(21q/5\), the retained exponents are \(64,81,85\), the deficit-4 exponent
is \(88\), and the high tail begins with exponents \(72,49,16\).  The
remainder has successive ratio at most \(x^{-43}\), giving

\[
 4\left(x^{72}+x^{49}+\frac{x^{16}}{1-x^{-43}}\right)
 <x^{64}+x^{81}+x^{85},
 \tag{8.8}
\]

and

\[
 8x^{88}<5(x^{64}+x^{81}+x^{85}).
 \tag{8.9}
\]

These are exactly the last two bounds in (8.4).

If \(\lambda_3\le7q/2\), monotonicity gives an omitted ratio below

\[
 \frac15+\frac12+\frac2{25}=\frac{39}{50}.
\]

If \(\lambda_3\ge7q/2\), it is below

\[
 \frac2{25}+\frac58+\frac14=\frac{191}{200}.
\]

Evaluating the full-support dual function at the \(S_3\) tilt proves
\(D_3\le\ln(1+191/200)\), and subtraction from \(q=\ln2\) gives (8.6).
\(\square\)

The attached exact-check script verifies every rational comparison in this
proof using `Fraction`; its separate support scan reports the stronger numerical
minimum

\[
 \min_T\{q-(\mathcal F_{S_+}(T)-\mathcal F_{S_3}(T))\}
 \approx0.0921449643.
 \tag{8.10}
\]

The certified three-size route has several structural advantages:

- it retains deficits `2` and `3`, so the unimodular correction in (5.16)
  remains unchanged;
- its minimum and maximum deficits are still `2` and `5`, so the central-rate
  proof uses the same endpoint inequalities;
- the maximum type displacement remains three;
- the dense transportation table becomes `3 by 3` rather than `4 by 4`;
- all three limiting masses are uniformly positive by compactness of the tilt
  interval.

Combining (8.6) with the direct propagation of (5.11) would give the explicit
three-size coefficient

\[
 \frac{(\ln2)^2}{8}\ln\frac{400}{391}
 =0.0013667079\ldots.
 \tag{8.11}
\]

This is now an exact first-moment alternative, not merely a numerical guess.
It is **not yet a second proof of the theorem**: the partial-diagonal,
transportation, high-skeleton, and residual estimates must be replayed with a
three-coordinate profile before the route can replace the four-size witness.

Adding deficit `1` remains unsafe for the existing empty-corner argument,
because the activity \(k_1^2/\mu_{\alpha-1}(n)\) is not uniformly `o(1)` over
the phase cycle.  Deficit `2` remains the natural largest-class cutoff for this
method.

---

## 9. Root placement can probably be optimized

The midpoint in (5.13) is convenient but not intrinsic.  For a fixed
`theta in (0,1)`, consider

\[
 k_\theta
 =\left\lceil r_4^{co}+\theta(r_+-r_4^{co})\right\rceil.
 \tag{9.1}
\]

The signed first-moment margin remains `exp(c_theta n/N)` for a fixed
`c_theta>0`, while the retained chromatic gap becomes

\[
 \left((1-\theta)\frac{q^2}{4}A(\delta)+o(1)\right)
 \frac{n}{N^3}.
 \tag{9.2}
\]

The focused component proofs state their first-moment input only as the
existence of some fixed positive `c_Z`.  This strongly suggests that every
fixed `theta>0` is admissible and that the coefficient can approach the full
root displacement as `theta` is chosen small.

This is not yet classified as a completed improvement: every use of `c_Z` must
be replayed with constants allowed to depend on `theta`.  A conservative first
test is `theta=1/4`, which increases the midpoint gap by a factor `3/2` while
leaving a substantial fixed first-moment margin.

---

## 10. Recommended integration order

1. Replace the large-residual cycle expansion by Lemma 1.1 and Corollary 1.2.
2. Strengthen the central rate to (2.1).
3. Carry equation (5.11) directly to the final theorem, producing (3.4).
4. Insert the exact entropy certificate (4.1)--(4.8) after independent review of
   the rational-check script.
5. Add the complement-symmetric corollary and fixed-density criticality remark.
6. Treat the three-size support and non-midpoint root placement as separate
   experimental branches rather than mixing them into the canonical proof.
