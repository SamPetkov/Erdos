# Audit of the stronger Erdős 625 four-support entropy certificate

**Audit date:** 24 July 2026  
**Verdict:** **PASS for the stated limiting entropy certificate.**

This audit checks the elementary weight comparison only. It is not an
independent proof of the finite-`n` root displacement, normalized second moment,
or final theorem.

## 1. Claim audited

For the retained support `S_4={2,3,4,5}`, the proposed certificate is

\[
 D_4(\delta)<\ln\frac{639}{500},
 \qquad
 \ln2-D_4(\delta)>\ln\frac{1000}{639}
\]

uniformly for the complete limiting phase interval.

## 2. Independent structure check

For a fixed target mean, the retained optimizer has weights

\[
 w_i(\lambda)=\exp\left(\lambda i-\frac{\ln2}{2}i^2\right).
\]

The retained mean is strictly increasing in `lambda`. The omitted low-to-kept
ratio decreases because every low omitted index is smaller than every retained
index. The omitted high-to-kept ratio increases because every high omitted
index is larger than every retained index.

Evaluating the full-support dual function at the retained optimizer gives

\[
 D_4\le\ln(1+L+H).
\]

These are the same monotonicity and dual-evaluation facts used by the canonical
Lemma 5.1.

## 3. Exact interval checks

The checker encloses

\[
 q=\ln2
\]

using the positive series

\[
 q=2\sum_{k\ge0}\frac{(1/3)^{2k+1}}{2k+1}
\]

and an explicit geometric tail. It encloses `x=2^(1/20)` by checking the
rational twentieth powers.

Every subsequent comparison uses only `Fraction` arithmetic. In particular it
checks:

1. the retained mean at `49q/20` is below `2/q`;
2. the retained mean at `83q/20` is above `1+2/q`;
3. `L(49q/20)<263/1000`;
4. `H(29q/10)<3/200`;
5. `L(29q/10)<33/250`;
6. `H(83q/20)<29/200`.

The two monotonicity cases give respectively

\[
 \frac{263}{1000}+\frac3{200}=\frac{139}{500}
\]

and

\[
 \frac{33}{250}+\frac{29}{200}=\frac{277}{1000}
 <\frac{139}{500}.
\]

No floating-point comparison enters the proof certificate.

## 4. Tail directions checked

The potentially error-prone interval directions were checked separately.

- For positive exponents, upper numerators use the upper enclosure for `x` and
  lower denominators use the lower enclosure.
- For negative exponents, an upper bound uses the lower positive enclosure for
  `x`.
- At `29q/10`, the high tail starts with exponent `-12`; the first ratio is
  `x^(-72)` and later ratios are smaller.
- At `83q/20`, the high exponents are `138,91,24,-63,...`; after the exponent
  `-63`, the first remaining ratio is `x^(-107)` and later ratios are smaller.
- In the upper mean bracket, negative coefficients are paired with upper weight
  bounds and positive coefficients with lower weight bounds.

The displayed tail and mean inequalities therefore have the correct one-sided
directions.

## 5. Regression and optimization independence

`625/experiments/four_support_entropy_certificate.py` uses explicit exceptions,
not Python `assert`. The exact gates remain active under `python -O`.

The same script performs a separate floating-point phase scan. That scan is
labelled diagnostic and is not used to establish the rational certificate.

## 6. Consequence boundary

The audit supports replacing the limiting entropy advantage in Lemma 5.1 by

\[
 \ln2-D_4(\delta)>\ln(1000/639).
\]

To change the canonical theorem constant, a separate review must verify how
this limiting inequality is transported to the finite optimizer and combined
with the root displacement and final rounding. PR #31 addresses the latter
propagation independently.

No external peer review, priority claim, or complete formal verification is
asserted.