# Erdős 625 chromatic lower-tail closure audit

**Date:** 2026-08-06  
**Branch:** `agent/625-referee-readable-tier-one-pass`  
**Manuscript source:** `625/arxiv/SECTION4_CHROMATIC_LOWER_TAIL_V3.tex`  
**Status:** complete candidate paper interface; exact Lean declaration and independent replay still required

## Purpose

The final gap theorem uses a deterministic integer threshold `k_chi^-(n)` for which

```text
P(chi(G_n) > k_chi^-(n)) -> 1
```

and whose distance from the ordinary first-moment root is negligible on the target scale `n/(log n)^3`. The former manuscript stated this conclusion correctly but compressed the decisive uniformity, exact-class-count, and event-direction steps into a short appeal to the profile variational lemma.

The replacement Section 4 makes every one of those interfaces explicit.

## Exact deterministic threshold

The threshold is

```text
k_chi^-(n) = floor(r_+(n)) - ceil(log n).
```

Thus

```text
log n <= r_+(n)-k_chi^-(n) < log n+2.
```

In particular,

```text
|k_chi^-(n)-r_+(n)| = o(n/(log n)^3).
```

No phase-dependent rounding convention or density-one subsequence is introduced.

## Exact profile enumeration

For a profile with `k_i` classes of size `alpha-i`, the expected number of unordered proper colorings is

```text
n! / product_i(((alpha-i)!)^(k_i) k_i!)
  * 2^(-sum_i k_i binom(alpha-i,2)).
```

The manuscript now explains the symmetry factors:

- `n!` orders the vertices;
- each block factorial removes its internal ordering;
- `k_i!` removes the ordering of equal-size blocks;
- blocks of different sizes have different profile types, so there is no additional global `k!` factor.

The profile sum therefore counts each unordered partition once.

The profile-coordinate box has at most

```text
(n+1)^(alpha+1) = exp(O((log n)^2))
```

points. The two exact conservation laws only reduce this count. Applying the factorial estimate uniformly, including zero coordinates, gives

```text
log E_{n,k,alpha+1}
  <= L_+(n,k) + O((log n)^2).
```

## Uniform derivative corridor

The key missing line was the verification that the complete interval from `k_chi^-` to `r_+` remains inside the derivative corridor.

Writing `s(k)=n/k`, one has uniformly on this interval

```text
k = Theta(n/log n),
s(k) = Theta(log n),
```

and hence

```text
|s(k_chi^-)-s(r_+)|
  <= sup n/k^2 * (r_+-k_chi^-)
  = O((log n)^3/n)
  = o(log log n/log n).
```

This is much smaller than the corridor width. Therefore the phase-uniform derivative estimate applies at every intermediate point:

```text
dL_+(n,k)/dk >= c_* (log n)^2.
```

Since `L_+(n,r_+)=0`, the mean-value theorem yields

```text
L_+(n,k_chi^-) <= -c_* (log n)^3.
```

The `O((log n)^2)` profile-enumeration error is absorbed with a fixed margin, producing one deterministic sequence

```text
epsilon_n^prof = exp(-c_chi (log n)^3) -> 0.
```

## Removing the class-size cap

Let

```text
A_n = {alpha(G_n) <= alpha+1}.
```

The independence-number estimate supplies one deterministic phase-uniform sequence

```text
P(A_n^c) <= epsilon_n^cap -> 0.
```

On `A_n`, every color class has size at most `alpha+1`.

The first-moment variable counts colorings with exactly `k_chi^-` nonempty classes, whereas the event `chi(G_n)<=k_chi^-` initially gives at most that many classes. The manuscript now includes the exact refinement argument. If a proper coloring has `h<k_chi^-` classes, then some class contains at least two vertices because `k_chi^-<n`. Splitting that independent class into two nonempty subsets preserves properness and the size cap. Each split increases the number of classes by exactly one. After `k_chi^--h` steps, one obtains an exactly `k_chi^-`-class coloring.

Therefore

```text
{chi(G_n) <= k_chi^-} intersect A_n
  subseteq
{an exactly k_chi^-, (alpha+1)-bounded coloring exists}.
```

Markov's inequality gives

```text
P(chi(G_n) <= k_chi^-)
  <= epsilon_n^cap + epsilon_n^prof -> 0.
```

Equivalently,

```text
P(chi(G_n) > k_chi^-) -> 1.
```

The strict direction is the one used by the final event intersection.

## What is now closed in the manuscript

The replacement section contains a complete candidate proof of the theorem-facing chromatic lower-tail interface:

1. one deterministic integer threshold;
2. the exact unordered profile count;
3. a phase-uniform profile-enumeration error;
4. verification that the full displacement interval lies in the derivative corridor;
5. a uniform `-Theta((log n)^3)` first-moment exponent;
6. the refinement from at most to exactly `k_chi^-` classes;
7. the strict probability event;
8. the required `o(n/(log n)^3)` location precision;
9. one set of eventuality thresholds valid through the complete phase and along the full sequence.

## What remains open

This audit does not promote E625-09 to `welded`. The following acceptance steps remain:

1. freeze the exact Lean declaration using the same `r_+`, `k_chi^-`, class-size cap, and strict event direction;
2. bind the derivative corridor and all error sequences with the required uniform quantifiers;
3. independently check the manuscript proof line by line;
4. replay the declaration under the pinned Lean 4.31 toolchain with warnings fatal;
5. run the placeholder, forbidden-shortcut, and axiom gates;
6. import the result into the theorem-facing root and replay the final adapter on the same integrated commit.

Until those steps pass, E625-09 remains `needs review` and the manuscript remains fail-closed.
