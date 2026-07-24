# X07 -- Rare-seed amplification and cochromatic upper tail

Status: stage after X05 and X06.  Kind: graph-probability assembly.  The
generic theorem is independent of Sections VIII--IX; its concrete manuscript
application depends on the Section IX seed and hence on the VIII--IX branch.

## Target quantifier order

Prove that there are an absolute `C > 0` and a deterministic sequence
`epsilon : Nat -> Real` with `epsilon n -> 0`, chosen before all later
parameters, such that for every deterministic `k : Nat -> Nat` and
`Lambda r : Nat -> Real` satisfying eventually

\[
 \Lambda_n\ge0,
 \quad r_n>0,
 \quad
 \Pr\{\zeta(G_n)\le k_n\}\ge e^{-\Lambda_n},
\]

one has eventually

\[
 \Pr\!\left\{
 \zeta(G_n)> k_n+C\left(
 \frac{\sqrt{n\Lambda_n}+\sqrt{nr_n}}{\ln n}
 +n^{1/3}+1\right)\right\}
 \le e^{-r_n}+\varepsilon_n.
\]

Natural/real rounding may be exposed through a ceiling, provided an explicit
lemma relates the rounded Lean event to the displayed real threshold.

## Available inputs

The repository already contains the induced-capacity lower tail, its exact
deficit radius, a maximizing core with exact complement size, deterministic
concatenation, and the conditional event assembly.  X05 supplies the one
uniform leftover event; X06 supplies the quantitative union bound.

## Concrete application still needed

After the generic theorem is proved, instantiate

\[
 B_n=n/(\ln n)^4,
 \qquad r_n=\sqrt{B_n},
\]

and the Section IX sequences `k_co` and `Lambda_n`.  The accepted
amplification-scale module already proves the needed little-o transformations.
The missing upstream facts are the actual Section IX seed and its
`Lambda_n = o(B_n)` estimate.

## Failure modes

The failure sequence may not depend on `k`, `Lambda`, or `r`.  A pointwise
leftover event is insufficient.  Positivity and rounding conditions may only
be imposed eventually; the result must remain a full-sequence `atTop` claim.
