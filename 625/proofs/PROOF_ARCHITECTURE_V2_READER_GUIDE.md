# Erdős 625: reader-first proof architecture for Version 2

## Status and purpose

This note is an exposition layer for the corrected Version 2 proof.  It does
not replace the theorem-by-theorem audit and does not promote any conditional
statement to a proved one.  Its purpose is to make the logical spine visible
before the reader enters the phase asymptotics, physical-fibre counting, and
normalized second moment.

The candidate proof was first deposited publicly on 12 July 2026.  The later
PRs audit, simplify, strengthen, and formalize that proof.  At the time of this
note, the remaining submission-blocking theorem is the global Section VIII
attained-demand/all-deficit reindexing and its aggregate weight comparison.

## 1. The theorem in one paragraph

For `G_n ~ G(n,1/2)`, an ordinary coloring pays the probability cost of making
every class independent.  A cocoloring permits every class to be declared
either independent or complete.  At `p=1/2` the two declarations have the same
probability, so a partition into `k` classes acquires an exact sign multiplicity
`2^k`.  This extra entropy moves the signed first-moment root below the ordinary
coloring root by order `n/(log n)^3`.  A signed second-moment argument produces
a rare cocoloring at a midpoint between the two roots, and a Lipschitz
amplification argument upgrades that rare seed to high probability.  The
resulting gap is phase-sensitive because the dense-random-graph independence
threshold oscillates with `n`.

The corrected phase-resolved target is

\[
  \chi(G_n)-\zeta(G_n)
  \ge
  \left[
    \frac{(\log 2)^2}{8}
      \bigl(\log 2-D_4(\delta_n)\bigr)-\varepsilon_n
  \right]
  \frac{n}{(\log n)^3},
  \qquad \varepsilon_n\to0,
\]

with high probability.  The certified uniform entropy estimate gives

\[
  \frac{(\log2)^2}{8}\log\!\left(\frac{1000}{639}\right)
  =0.026896409808379\ldots .
\]

Both statements remain conditional on closure of the global Section VIII
bare-skeleton theorem.

## 2. Dependency graph

The proof should be read in the following order.

```text
phase expansion and profile roots
        |
        +--> ordinary first moment --> lower bound for chi(G_n)
        |
        +--> signed four-size first moment --> root displacement
                                            |
exact signed-overlap identity --------------+
        |
        +--> partial diagonals
        |
        +--> high-skeleton deficit sum (Section VIII)
        |
        +--> q-only residual attachment (Section IX)
        |
        v
normalized signed second moment
        |
        v
positive-probability signed seed
        |
        v
leftover coloring + bounded differences
        |
        v
high-probability upper bound for zeta(G_n)
        |
        v
intersection with the chi(G_n) lower bound
```

No independence is required between the final chromatic and cochromatic
events; a union bound suffices.

## 3. Phase and ordinary-coloring location

Let `alpha=alpha(n)` denote the phase integer associated with the
independence-number threshold.  The relevant class sizes are perturbations of
`alpha`, and the phase variable `delta_n` records the fractional displacement
inside one threshold window.

For an ordinary coloring profile, the first moment has a continuous root
`r_+(n)`.  The unrestricted lower-tail argument has two ingredients:

1. on the usual independence-number event, every color class has size at most
   the phase cap;
2. an arbitrary coloring with fewer than the target number of colors can be
   refined into a bounded profile with exactly the required number of
   nonempty classes.

Consequently

\[
  \chi(G_n)
  \ge r_+(n)-o\!\left(\frac{n}{(\log n)^3}\right)
\]

with high probability.

## 4. Why signed colorings improve the root

Fix a partition into `k` classes.  A sign vector specifies which classes are
required to be independent and which are required to be complete.  For
`G(n,1/2)`, each sign choice has the same edge-probability cost.  Summing over
signs gives the exact factor

\[
  2^k.
\]

The proof restricts the class sizes to four consecutive phase coordinates,
corresponding to deficits `2,3,4,5`.  Let `r_4^{co}(n)` be the root of the exact
finite signed four-size objective.  The root displacement is

\[
  r_+(n)-r_4^{\mathrm{co}}(n)
  =
  \left[
    \frac{(\log2)^2}{4}
      A_4(\delta_n)+o(1)
  \right]
  \frac{n}{(\log n)^3},
\]

where

\[
  A_4(\delta)=\log2-D_4(\delta).
\]

The current seed is placed at the midpoint

\[
  k_{\mathrm{co}}
  =
  \left\lceil
    \frac{r_4^{\mathrm{co}}+r_+}{2}
  \right\rceil,
\]

so the deterministic retained separation has leading coefficient

\[
  \frac{(\log2)^2}{8}A_4(\delta_n).
\]

Integer rounding costs only `O(1)` classes and amplification costs
`o(n/(log n)^3)`; neither creates another factor two loss.

## 5. Exact signed-overlap identity

Take two ordered signed partitions with overlap table `(r_ab)`.  After summing
over their sign declarations, the compatibility factor separates into a local
cell product and a binary cycle-space factor:

\[
  \operatorname{SignedOverlapWeight}(r)
  =
  \left(\prod_{a,b}g(r_{ab})\right)2^{\beta(H_r)}.
\]

Here `H_r` is the bipartite support graph of cells whose multiplicity is at
least two, and `beta(H_r)` is its binary cycle rank.  This identity is exact;
it is not a high-temperature approximation.

The normalized second moment is then organized by the canonical high cells of
the overlap table.  Partial diagonal configurations are handled separately.
The remaining high cells form a matching because every row and column margin
is at most the phase cap and every high cell exceeds half of that cap.

## 6. The Section VIII object dictionary

The following objects must not be conflated.

| Object | Meaning |
|---|---|
| profile block | one actual class of the ordered profile |
| block atom | the abstract type/slot label of a profile block |
| high-demand table | actual multiplicities `j_ab` in canonical high cells |
| block support `P` | the matching of block pairs where `j_ab>0` |
| full multiplicity `m_e` | `min{s_e,t_e}` for a selected block pair |
| deficit `h_e` | `m_e-j_e` |
| local partial stub matching | a size-`j_e` matching inside one selected block pair |
| full endpoint table `L` | counts of selected block pairs by their four endpoint types |
| residual attachment | the conditional contribution of non-high cells after exposure |

A partial physical matching generally has many full completions.  The proof
therefore compares aggregate finite fibres; it does not assign one canonical
full physical completion to each partial object.

## 7. Exact high-skeleton weight

For a fixed block matching `P`, endpoint sizes `(s_e,t_e)`, and actual
multiplicities `j_e`, summing all local physical partial-matching fibres gives

\[
  w(P,j)
  =
  \frac{
    \prod_{e\in P}(s_e)_{j_e}(t_e)_{j_e}
  }{
    (n)_J\prod_{e\in P}j_e!
  }
  \prod_{e\in P}g(j_e),
  \qquad
  J=\sum_{e\in P}j_e.
\]

This formula has exactly one `j_e!` denominator per selected cell and one
global falling-factorial denominator `(n)_J`.

Let

\[
  m_e=\min\{s_e,t_e\},\qquad h_e=m_e-j_e,
\]

and let `w_full(P)` denote the aggregate full-containment reference weight.
For one cell with endpoint sizes `m,m+d`, the exact local ratio is

\[
  R_{m,d}(h)
  =
  \frac{\binom mh}{(d+1)(d+2)\cdots(d+h)}
  2^{-hm+h(h+1)/2}.
\]

If `H=sum_e h_e`, then the only global denominator change is

\[
  \frac{(n)_{J+H}}{(n)_J}
  =(n-J)_H\le n^H.
\]

Therefore

\[
  \frac{w(P,m-h)}{w_{\mathrm{full}}(P)}
  \le
  \prod_{e\in P}n^{h_e}R_{m_e,d_e}(h_e).
\]

The remaining formal obligation is to prove that the attained canonical-demand
sum is reindexed by these data without omission or multiplicity.

## 8. Geometric summation of all deficits

The canonical high condition implies

\[
  2h<m.
\]

A finite integer estimate then gives

\[
  n^hR_{m,d}(h)
  \le
  \left(\frac{nm}{2^{\lfloor2m/3\rfloor}}\right)^h.
\]

For the four phase sizes define

\[
  \rho_n
  =
  \max_m\frac{nm}{2^{\lfloor2m/3\rfloor}}.
\]

The phase expansion yields

\[
  \rho_n
  =O\!\left(\frac{(\log n)^{7/3}}{n^{1/3}}\right)=o(1).
\]

For large `n`, the sum over all positive deficits in one selected cell is at
most `2 rho_n`.  Since `P` is a matching with at most `k_co` cells, the entire
deficit fibre contributes at most

\[
  (1+2\rho_n)^{k_{\mathrm{co}}}
  =
  \exp\!\left\{
    O\bigl(n^{2/3}(\log n)^{4/3}\bigr)
  \right\}.
\]

The full endpoint reference sum is transported to the partial-diagonal sum by
the exact endpoint factorial identity and square-free AM--GM estimate:

\[
  \sum_LW(L)
  \le
  \exp\{O(\sqrt{n\log n})\}\sum_rD(r).
\]

Because the partial-diagonal sum is `1+o(1)`, the desired bare-skeleton bound is

\[
  \operatorname{BareSkeletonSum}_n
  \le
  \exp\!\left\{
    O\bigl(n^{2/3}(\log n)^{4/3}\bigr)
    +O(\sqrt{n\log n})
  \right\}
  =
  \exp\!\left\{o\!\left(\frac{n}{(\log n)^4}\right)\right\}.
\]

This replaces the old near/middle split and its auxiliary middle-range
parameters.

## 9. Direct Section IX residual bound

Let `M` be the exposed high-support matching.  An even residual edge set is
uniquely determined by its restriction outside `M`: the symmetric difference
of two completions would be an even subset of a matching, hence empty.
Therefore, for nonnegative activities `q_e`,

\[
  \sum_{F\text{ even}}
    \prod_{e\in F\setminus M}q_e
  \le
  \prod_{e\notin M}(1+q_e).
\]

The local increment activity is pointwise bounded by the same `q` activity, so
both residual products are charged to one total-activity sum.  A two-regime
argument gives the literal aggregate estimate

\[
  \operatorname{AttachmentSum}_n
  \le
  \operatorname{BareSkeletonSum}_n
  \exp\!\left\{
    \eta_n\frac{n}{(\log n)^4}
  \right\},
  \qquad \eta_n\to0.
\]

No simple-cycle decomposition, residual walk kernel, or polymer surrogate is
needed in the final exposition.

## 10. From the second moment to high probability

Once Sections VIII and IX give

\[
  \frac{\mathbb E Z_n^2}{(\mathbb E Z_n)^2}
  \le
  \exp\!\left\{o\!\left(\frac{n}{(\log n)^4}\right)\right\},
\]

Paley--Zygmund supplies a positive-probability signed seed.  The proof then
uses a simultaneous leftover-coloring lemma and a one-Lipschitz cocolorable
capacity.  Bounded differences amplify the seed to a high-probability upper
bound for `zeta(G_n)` with an additive loss `o(n/(log n)^3)`.

The final theorem follows by intersecting this event with the ordinary
chromatic lower bound.

## 11. One worked two-cell example

Suppose a block support contains two selected cells with

\[
  (s_1,t_1)=(8,9),\qquad (s_2,t_2)=(7,7),
\]

and deficits

\[
  (h_1,h_2)=(1,2).
\]

Then

\[
  (m_1,m_2)=(8,7),\qquad (j_1,j_2)=(7,5),
\]

so

\[
  J=12,\qquad H=3,\qquad J+H=15.
\]

The aggregate partial weight is

\[
  \frac{(8)_7(9)_7}{7!}
  \frac{(7)_5(7)_5}{5!}
  \frac{g(7)g(5)}{(n)_{12}}.
\]

The full reference weight uses multiplicities `8` and `7` and denominator
`(n)_{15}`.  Their denominator ratio is one global factor

\[
  \frac{(n)_{15}}{(n)_{12}}=(n-12)_3\le n^3,
\]

which is distributed as `n^{h_1}n^{h_2}` in the product bound.  There is not a
separate ambient denominator attached independently to each cell.

## 12. Reader checklist

Before accepting the final manuscript, a reader should be able to locate:

1. the exact definition of the phase variable and both continuous roots;
2. the entropy calculation producing the signed root displacement;
3. the exact signed-overlap/cycle-space identity;
4. the partial-diagonal normalized sum;
5. the attained-demand to block-support/deficit reindexing;
6. the aggregate local fibre formula for `w(P,j)`;
7. the one-global-denominator comparison;
8. the all-deficit geometric product;
9. the direct q-only residual attachment theorem;
10. the seed amplification theorem and final event intersection.

If any one of Items 5--7 is merely described informally rather than proved as
an exact finite statement, the normalized second-moment theorem remains
conditional.
