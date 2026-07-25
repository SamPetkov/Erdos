# A generic restriction-product theorem behind Section IX

## 1. Finite theorem

Let `E` be a finite coordinate set, let `C` be a finite family of subsets of
`E`, and let `I subset E`. Assume that deletion of `I` is injective on `C`:

\[
  A\setminus I=B\setminus I,\quad A,B\in\mathcal C
  \quad\Longrightarrow\quad A=B.
\]

For arbitrary nonnegative activities \((q_e)_{e\in E}\),

\[
 \boxed{
 \sum_{A\in\mathcal C}\prod_{e\in A\setminus I}q_e
 \le
 \prod_{e\in E\setminus I}(1+q_e).}
 \tag{1.1}
\]

Indeed, the restrictions `A \ I` form a subfamily of the full powerset of
`E \ I`, with no repetitions. Summing over the larger powerset gives the
product on the right.

The theorem is kernel-checked in
`Erdos625/FiniteRestrictionProduct.lean`. It is independent of graph parity,
matchings, or the Erdős 625 profile.

## 2. Section IX as a corollary

Take `C` to be the even edge sets of the residual bipartite support and take
`I=M`, where `M` is the exposed matching. If two even edge sets have the same
restriction outside `M`, their symmetric difference is an even subset of a
matching. Such a subset must be empty. Therefore deletion is injective, and
(1.1) is exactly the matching-restriction product bound used in Section IX.

This factorization is logically cleaner than a cycle/polymer enumeration: all
model-specific work is confined to proving injectivity and bounding the total
activities.

## 3. Forest generalization

The matching hypothesis is stronger than necessary. Let `T` be any forest in
a finite graph. No nonempty edge subset of `T` is even: every nonempty forest
has a leaf of degree one in its nontrivial edge-induced subgraph. Hence
restriction outside `T` is injective on the graph's binary cycle space, and

\[
 \boxed{
 \sum_{F\text{ even}}
   \prod_{e\in F\setminus T}q_e
 \le
 \prod_{e\notin T}(1+q_e).}
 \tag{3.1}
\]

For a spanning forest, this is the weighted subset-product form of the usual
fact that cotree coordinates determine a binary cycle uniquely.

The forest statement is an immediate mathematical corollary of (1.1), but its
graph-theoretic injectivity proof has not yet been added to the Lean tree.

## 4. Binary-matroid form

The same statement is not intrinsically graphical. Let `C` be the cycle space
of a binary matroid on ground set `E`, and let `I` be independent. A nonzero
cycle vector cannot be supported inside `I`; consequently projection to
`E \ I` is injective on `C`. Formula (1.1) gives

\[
 \sum_{x\in C}\prod_{e\in\operatorname{supp}(x)\setminus I}q_e
 \le
 \prod_{e\in E\setminus I}(1+q_e).
 \tag{4.1}
\]

This is a useful abstract form for parity-constrained partition functions,
configuration-model second moments, and high-temperature expansions. It should
be treated as a reusable method lemma rather than claimed as a new matroid
result without a separate literature review.

## 5. Possible follow-up direction

A substantive follow-up paper would need more than (1.1) alone. The promising
program is to combine:

1. injective restriction along forests or independent matroid sets;
2. sharp activity estimates in a random combinatorial model;
3. stability or near-equality analysis for the product bound;
4. at least two applications where this removes a conventional polymer or
   cycle enumeration.

The Erdős 625 attachment problem supplies one application. Random regular
partition models and parity-constrained configuration models are natural
second targets.
