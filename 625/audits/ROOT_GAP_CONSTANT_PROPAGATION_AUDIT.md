# Audit of the Erdős 625 root-gap constant propagation

**Audit date:** 24 July 2026  
**Canonical base:** repository `main` at the branch point of this PR  
**Verdict:** **PASS conditional on the canonical inputs explicitly listed below.**

This is an arithmetic/asymptotic propagation audit. It is not an independent
verification of the signed second moment or of `Erdos625Statement`.

## 1. Inputs treated as hypotheses

The audit uses only the following claims from the canonical candidate
manuscript:

1. equation (5.11), uniformly in the phase,
   \[
    r_+-r_4^{co}
    =\left(\frac{q^2}{4}\{q-D_4(\delta)\}+o(1)\right)
      \frac{n}{N^3};
   \]
2. the exact midpoint definition (5.13);
3. the chromatic lower integer from (4.1);
4. the uniform strict entropy advantage in Lemma 5.1;
5. the deterministic amplification loss `a_n=o(n/N^3)` from (10.12)--(10.13);
6. the final event intersection used in Section 11.

No conclusion of this audit should be read as an independent proof of those
inputs.

## 2. Independent derivation

Let `x=r_+`, `y=r_4^{co}`, and `L=N`. The exact inequalities

\[
 \lfloor x\rfloor>x-1,
 \qquad
 \lceil L\rceil<L+1,
 \qquad
 \left\lceil\frac{x+y}{2}\right\rceil<\frac{x+y}{2}+1
\]

give

\[
 k_\chi^- - k_{co}>rac{x-y}{2}-N-3.
\]

Since

\[
 \frac{N+3}{n/N^3}=\frac{(N+3)N^3}{n}\to0,
\]

equation (5.11) implies

\[
 k_\chi^- - k_{co}
 =\left(\frac{q^2}{8}\{q-D_4(\delta_n)\}+o(1)\right)
   \frac{n}{N^3}
\]

in the one-sided form required by the proof.

Subtracting `a_n=o(n/N^3)` does not change this coefficient. Therefore the
phase-resolved final gap has coefficient

\[
 \frac{q^2}{8}\{q-D_4(\delta_n)\}.
\]

The factor `1/8` comes from the coefficient `1/4` in the root displacement and
the single midpoint factor `1/2`. There is no second asymptotic halving forced
by integer rounding or amplification.

## 3. Uniform explicit constant

Lemma 5.1 gives

\[
 q-D_4(\delta)>\gamma_4:=\ln(200/153)
\]

on the closed phase interval. The limiting value functions are continuous, so
the strict inequality has uniform positive slack. The same conclusion can be
read directly from the fixed strict omitted-weight bounds in the proof of Lemma
5.1.

Consequently the phase-resolved coefficient eventually dominates

\[
 \frac{q^2\gamma_4}{8}.
\]

The currently displayed theorem uses `q^2 gamma_4/32`; the proposed arithmetic
corollary is therefore exactly four times larger.

## 4. Exact regression checker

`625/experiments/root_gap_constant_supercheck.py` performs:

- 55,296 exact `Fraction` checks of the midpoint and general-`theta`
  floor/ceiling inequality;
- an exact decimal identity check that the propagated displayed coefficient is
  four times the current coefficient;
- a canonical equation-tag scan when run from the repository root;
- a numerical limiting-phase scan, clearly marked diagnostic;
- a finite-`n` table showing the decay of the additive rounding loss relative to
  `n/(log n)^3`.

The checker uses explicit exceptions rather than Python `assert`, so its gates
remain active under `python -O`.

## 5. Adversarial checks

### Could the rounding loss contain another factor of two?

No. The exact loss is additive, bounded by `N+3`, not multiplicative. Since
`N=o(n/N^3)`, it disappears after normalization.

### Does amplification halve the gap?

No. The amplification theorem contributes an additive deterministic loss
`a_n=o(n/N^3)`. It does not multiply the root separation by a fixed constant.

### Is pointwise strictness enough for the displayed constant?

Pointwise strictness alone on a noncompact domain would not be enough. Here the
phase interval closes at `delta=1`, the limiting value functions are continuous,
and the proof of Lemma 5.1 itself uses fixed strict numerical bounds. Hence a
uniform slack exists.

### Does this alter the witness profile?

No. The integer `k_co` is the same midpoint integer as in the canonical proof.
No Section 7--9 estimate is rerun or weakened.

## 6. Remaining boundary

The audit does not independently establish:

- the uniform `o(1)` in equation (5.11);
- continuity and exact finite-`n` approximation of the entropy loss;
- the complete normalized second moment;
- the rare-seed amplification theorem;
- external peer review or formal verification.

Within the stated dependency boundary, no additional loss reducing
`q^2 gamma_4/8` to `q^2 gamma_4/32` was found.