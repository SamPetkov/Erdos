# Erdős 625: an exact stronger four-support entropy certificate

**Status.** This is a focused replacement certificate for Lemma 5.1 of the
candidate manuscript. It keeps the same four deficits

\[
 S_4=\{2,3,4,5\}
\]

and changes no later probabilistic argument. The note does not modify the
canonical manuscript, publication PDFs, Lean sources, or `Erdos625Statement`.

Put

\[
 q=\ln2,
 \qquad
 T\in\left[\frac2q,1+\frac2q\right].
\]

For a tilt `lambda`, write

\[
 w_i(\lambda)=\exp\left(\lambda i-\frac q2i^2\right),
 \qquad
 Z_4(\lambda)=\sum_{i=2}^5w_i(\lambda).
\]

Let `lambda_4(T)` be the unique tilt for which the retained mean equals `T`.
Define

\[
 L(\lambda)=
 \frac{\sum_{i=-1}^1w_i(\lambda)}{Z_4(\lambda)},
 \qquad
 H(\lambda)=
 \frac{\sum_{i\ge6}w_i(\lambda)}{Z_4(\lambda)}.
\]

The low ratio `L` is decreasing in the tilt, while `H` is increasing.

## 1. Exact rational enclosures

Set

\[
 x=2^{1/20}.
\]

The accompanying checker proves by exact integer and rational arithmetic that

\[
 0.693147180559<q<0.693147180560,
 \tag{1.1}
\]

and

\[
 1.035264923841<x<1.035264923842.
 \tag{1.2}
\]

The logarithm enclosure follows from

\[
 \ln2=2\operatorname{arctanh}(1/3)
\]

with an explicit geometric tail. The root enclosure follows by raising the two
rational endpoints to the twentieth power.

## 2. A tighter tilt bracket

### Lemma 2.1

For every target in the full phase interval,

\[
 \boxed{
 \frac{49}{20}q<\lambda_4(T)<\frac{83}{20}q.}
 \tag{2.1}
\]

#### Proof certificate

At `lambda=(49/20)q`, after a common shift the four retained weights have
`x`-exponents

\[
 63,\ 62,\ 41,\ 0.
\]

The exact interval calculation proves

\[
 q\,
 \frac{2x^{63}+3x^{62}+4x^{41}+5}
      {x^{63}+x^{62}+x^{41}+1}<2,
\]

so the mean is below `2/q`.

At `lambda=(83/20)q`, the retained exponents are

\[
 126,\ 159,\ 172,\ 165.
\]

The checker proves

\[
 \sum_{i=2}^5\{q(i-1)-2\}w_i>0,
\]

which is equivalent to the mean being larger than `1+2/q`. Strict monotonicity
of the retained mean proves (2.1). \(\square\)

## 3. Exact omitted-weight bounds

Use the split tilt

\[
 \lambda_s=\frac{29}{10}q.
\]

The rational interval calculation proves

\[
 L\left(\frac{49}{20}q\right)<\frac{263}{1000},
 \qquad
 H\left(\frac{29}{10}q\right)<\frac3{200},
 \tag{3.1}
\]

and

\[
 L\left(\frac{29}{10}q\right)<\frac{33}{250},
 \qquad
 H\left(\frac{83}{20}q\right)<\frac{29}{200}.
 \tag{3.2}
\]

For reference, the exponent patterns used by the exact checker are:

- at `49q/20`, after division by the deficit `-1` weight, the low exponents
  are `0,59,98` and the retained exponents are `117,116,95,54`;
- at `29q/10`, the deficit-6 exponent is `-12`, and every subsequent high-tail
  ratio is at most `x^(-72)`;
- at `29q/10`, after the same low-weight normalization, the low exponents are
  `0,68,116` and the retained exponents are `144,152,140,108`;
- at `83q/20`, the high exponents begin `138,91,24,-63`, and after deficit 9
  every successive ratio is at most `x^(-107)`.

Now split according to the position of the target tilt.

If `lambda_4<=lambda_s`, monotonicity and (3.1) give

\[
 L(\lambda_4)+H(\lambda_4)
 <\frac{263}{1000}+\frac3{200}
 =\frac{139}{500}.
 \tag{3.3}
\]

If `lambda_4>=lambda_s`, equations (3.2) give

\[
 L(\lambda_4)+H(\lambda_4)
 <\frac{33}{250}+\frac{29}{200}
 =\frac{277}{1000}
 <\frac{139}{500}.
 \tag{3.4}
\]

Thus, uniformly through the full phase interval,

\[
 \boxed{L(\lambda_4)+H(\lambda_4)<\frac{139}{500}.}
 \tag{3.5}
\]

## 4. Entropy loss

Let `F_+` and `F_4` be the limiting constrained values from Section 3 of the
canonical manuscript. Evaluating the full-support dual function at the
four-support optimizer gives

\[
 \begin{aligned}
 D_4(\delta)
 &=F_+(T_0)-F_4(T_0)\\
 &\le\ln\{1+L(\lambda_4)+H(\lambda_4)\}.
 \end{aligned}
 \tag{4.1}
\]

Equation (3.5) therefore proves

\[
 \boxed{
 D_4(\delta)<\ln\frac{639}{500},
 \qquad
 q-D_4(\delta)>\ln\frac{1000}{639}.}
 \tag{4.2}
\]

This strengthens both the canonical certificate

\[
 q-D_4(\delta)>\ln\frac{200}{153}
\]

and the preliminary `ln(50/33)` certificate recorded in the broader research
notebook PR.

## 5. Consequences for displayed constants

Using only the canonical manuscript's present final safety factor, replacing
`gamma_4` by (4.2) would give

\[
 \frac{q^2}{32}\ln\frac{1000}{639}
 =0.006724102452095\ldots.
 \tag{5.1}
\]

If the independent root-gap propagation in PR #31 is accepted, the combined
coefficient becomes

\[
 \boxed{
 \frac{q^2}{8}\ln\frac{1000}{639}
 =0.026896409808379\ldots.}
 \tag{5.2}
\]

These are consequences of separate review layers. This note itself proves only
the limiting entropy certificate (4.2), conditional on the variational
comparison already used in Lemma 5.1.

## 6. Numerical diagnostic

A 2001-point phase scan of the limiting variational problem, using unrestricted
support cutoffs 59 and 89, gives identical displayed values for the two
truncations and reports

\[
 \min_\delta\{q-D_4(\delta)\}
 \approx0.520701335491228
\]

at `delta=1` on the grid. This numerical value is not part of the certificate.

## 7. Scope boundary

The exact checker verifies every displayed rational enclosure and weight
comparison. It does not independently prove the finite-to-limiting convergence
in Section 3, the signed root displacement, the second moment, amplification,
or `Erdos625Statement`.