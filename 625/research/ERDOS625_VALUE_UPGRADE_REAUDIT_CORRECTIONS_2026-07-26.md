# Corrections to the Erdős 625 theorem-upgrade program after the full TeX re-audit

**Date:** 26 July 2026  
**Applies to:** `ERDOS625_VALUE_UPGRADE_PROGRAM_2026-07-26.md` and `ERDOS625_VALUE_UPGRADE_THEOREMS.tex` in PR #43  
**Purpose:** narrow four proposed extensions whose first formulations were stronger than the mathematics presently supports

The main phase-resolved `/8` theorem, stronger certified fixed coefficient, complement corollary, tunable amplifier tail, and balanced rare seed are unchanged. The corrections below concern only new theorem programs.

## 1. Near-root placement correction

### Earlier formulation

The initial roadmap treated

\[
 \theta_n\ln n\to\infty
\]

as though it were already a proved sufficient condition for moving the signed witness from the midpoint to

\[
 k_{\theta_n}
 =\left\lceil
 r_4^{\rm co}+\theta_n(r_+-r_4^{\rm co})
 \right\rceil.
\]

### Correct classification

This condition is a **candidate sufficient criterion**, not an established lemma. The exact deterministic placement formula is valid, but the proof must collect the dependence on the positive signed first-moment margin in Sections 7--9.

Define

\[
 M_n(\theta)
 =L_{S_4}(n,k_\theta)+(\ln2)k_\theta.
\]

The expected scale is

\[
 M_n(\theta)\asymp \theta\frac n{\ln n}.
\]

A complete theorem must prove that:

1. integer profile construction and Stirling errors are `o(M_n(theta_n))`;
2. the full-corner term `1/EZ` still beats the polynomial number of residual profiles;
3. Lemma 7.1 is uniform at the moving profile;
4. the Section VIII bare-skeleton theorem is uniform at the moving profile;
5. the q-only attachment theorem is uniform at the moving profile;
6. the amplifier adds `o(n/(ln n)^3)` classes, which is sufficient for the final coefficient.

The explicit candidate

\[
 \theta_n=(\ln n)^{-1/2}
\]

still leaves a first-moment log margin of order `n/(ln n)^(3/2)` and is therefore a strong conservative target. It should be retained as a conjectural theorem until the uniform replay is complete.

### Correct theorem label

> **Near-root placement program.** Prove uniformity of the four-support second-moment architecture for `theta_n=(ln n)^(-1/2)`. Conditional on that uniformity,
> \[
>  \chi(G_n)-\zeta(G_n)
>  \ge
>  \left[
>   \frac{(\ln2)^2}{4}A_4(\delta_n)-o(1)
>  \right]\frac n{(\ln n)^3}
> \]
> with high probability.

## 2. Balance-stability correction

### Earlier formulation

The initial roadmap proposed that every near-optimal cocoloring must use asymptotically equal numbers of clique and independent parts, based on replacing `2^k` by `binom(k,rho k)`.

### Correct classification

That calculation controls the selected **four-size signed witness family**. It does not exclude an arbitrary cocoloring with a different class-size profile. The immediate theorem target must therefore be restricted.

### Valid current targets

1. **Balanced rare seed:** already follows from the unrestricted normalized second moment up to a polynomial loss.
2. **Balanced constructed cocoloring:** a labelled-slot amplifier should preserve asymptotic balance while adding `o(H_n)` parts.
3. **Four-size witness-family stability:** among signed witnesses with the chosen four-size profile, a fixed sign imbalance loses
   \[
   k\bigl(\ln2-H(\rho)\bigr)
   \]
   in first-moment entropy and shifts the root by a positive multiple of `H_n`.

### Global theorem requires a new input

To prove that **every arbitrary near-optimal cocoloring** is balanced, one must first perform a first-moment union bound over all signed class-size profiles. This is the same all-profile lower-location problem required for a matching upper bound on `chi-zeta`.

The global balance theorem must therefore be moved under the all-signed-profile location program.

## 3. Slow-support complexity correction

### Earlier formulation

The initial program proposed an estimate of the form

\[
 \Lambda(n,m)
 \le O\!\left(K(m)\frac n{(\ln n)^4}\right)
\]

and suggested choosing `K(m_n)=o(ln n)`.

### Why this is insufficient

The target required by the amplifier is

\[
 \Lambda(n,m_n)=o\!\left(\frac n{(\ln n)^4}\right).
\]

If the bound is literally `K(m)n/(ln n)^4`, then any growing `K(m_n)` violates the target scale. The condition `K(m_n)=o(ln n)` does not repair this.

### Correct formulation

First prove a dimension-dependent bound

\[
 \Lambda(n,m)\le K(m)B_n,
\]

where the fixed-support base scale satisfies

\[
 B_n=o\!\left(\frac n{(\ln n)^4}\right).
\]

Then choose `m_n` so that

\[
 K(m_n)B_n=o\!\left(\frac n{(\ln n)^4}\right).
\]

For example, the present fixed four-size bare-skeleton exponent has the much smaller scale

\[
 B_n=
 O\!\left(n^{2/3}(\ln n)^{4/3}+\sqrt{n\ln n}\right).
\]

A polynomial or moderately exponential `K(m)` may then permit a slowly growing support, but the admissible growth must be calculated from this exact comparison.

### Support definition

Replace the ambiguous phrase “`m` consecutive sizes” by an explicit deficit support, for example

\[
 S_m=\{-1,0,1,\ldots,m\},
\]

with `m=o(alpha)`. Other asymmetric truncations may be better, but their endpoints and feasibility interval must be stated.

## 4. Cochromatic-corridor correction

### Earlier formulation

The initial roadmap wrote the prospective upper location

\[
 \zeta(G_n)\le r_4^{\rm co}(n)+o(H_n)
\]

as though it were already the output of the current constructive proof.

### Correct present upper location

The current midpoint construction gives

\[
 \zeta(G_n)
 \le
 \frac{r_4^{\rm co}(n)+r_+(n)}2+o(H_n)
\]

with high probability, conditional on closure of the normalized second moment.

### Near-root upper location

The sharper bound

\[
 \zeta(G_n)\le r_4^{\rm co}(n)+o(H_n)
\]

requires the near-root placement theorem above.

### Correct corridor program

The location project has three logically separate stages:

1. **midpoint upper location:** supplied by the current candidate proof after Section VIII closure;
2. **near-root upper location:** conditional on the shrinking-placement uniformity theorem;
3. **all-profile lower location:** a new first-moment exclusion theorem over every signed profile.

Only after stages 2 and 3 can one state a two-sided `O(H_n)` cochromatic corridor centered at the full signed root.

## 5. Revised priority order

1. close the physical-fibre and global all-deficit Section VIII theorem;
2. insert the phase-resolved `/8` theorem and stronger fixed coefficient;
3. add the complement corollary and tunable tail;
4. prove the balanced rare seed and, if concise, the labelled-slot balanced amplifier;
5. audit `theta_n=(ln n)^(-1/2)` placement quantitatively;
6. develop an all-signed-profile lower location;
7. only then promote global balance necessity and a near-root cochromatic corridor;
8. formulate the slow-support complexity bound with an actual base scale `B_n`;
9. pursue the ordinary-coloring third-order upper construction needed for the full matching upper bound.

## 6. Statements unaffected by this correction

The following remain correctly classified:

- public candidate-proof chronology beginning on 12 July 2026;
- the exact phase-resolved root displacement;
- the midpoint `/8` coefficient;
- the stronger entropy certificate `A_4>ln(1000/639)`;
- the simultaneous complement corollary;
- the tunable rare-seed completion tail;
- the generic restriction-product theorem;
- the exact signed cycle-space factor;
- the limiting coefficient `(ln 2)^3/4` as the formal full-support, near-root target;
- the matching `O(n/(ln n)^3)` upper bound as the largest separate follow-up problem.
