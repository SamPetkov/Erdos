# Alon--Scott concentration for cochromatic and two-graph covering numbers

**Synchronized supporting status (2026-07-13).**  The concentration and
amplification statements below are proved self-containedly.  They strengthen
the basic vertex-Azuma bounds for `zeta` and `X` by a logarithmic factor.  The
uniform deterministic-error formulation in (2.12a) is synchronized with
Lemma 10.2 of the authoritative manuscript
`COMPLETE_PROOF_SELF_CONTAINED.md`.  This note does not estimate the required
surrogate gap, so it does not by itself resolve Erdős Problem #625.

Let

\[
 X(G_1,G_2)=\min\{k:[n]\text{ can be partitioned into }k\text{ sets,
 each independent in }G_1\text{ or }G_2\}.
\]

All logarithms in asymptotic width statements are natural; changing their
base only changes constants.

## 1. A uniform leftover-colouring lemma

### Lemma 1.1

There is an absolute constant `c>0` such that, with probability `1-o(1)`,
every vertex set `U` of `G~G(n,1/2)` with `|U|>=n^(1/3)` contains an
independent set of size at least `c log n`.  On the same event, every
`U subseteq[n]` satisfies

\[
 \chi(G[U])\le C\frac{|U|}{\log n}+n^{1/3}                    \tag{1.1}
\]

for an absolute `C`.

#### Proof

Apply a Chernoff bound and a union bound to the complement graph to obtain,
with probability `1-o(1)`, that every set of at least `n^(1/4)` vertices has
complement-edge density at least `1/4`.  One direct verification starts with
sets of size `u=ceil(n^(1/4))`: the failure probability for a fixed set is
`exp(-Theta(u^2))`, whereas there are at most `exp(O(u log n))` such sets.
If a larger set had density below `1/4`, averaging its `u`-subsets would give
one of density below `1/4` as well.

Starting in any `U` of size at least `n^(1/3)`, greedily choose a vertex of
maximum complement degree and replace the current set by its complement
neighbourhood.  While at least `n^(1/4)` vertices remain, the current size
shrinks by at worst a fixed factor and each chosen vertex extends a clique in
the complement.  This supplies `c log n` chosen vertices for a fixed `c>0`,
which are an independent set in `G`.

For (1.1), repeatedly remove such independent sets from `U` and give each a
new colour until fewer than `n^(1/3)` vertices remain; colour those remaining
vertices singly.  ∎

This is the dense-graph leftover lemma in the Alon--Scott proof for ordinary
chromatic number.  Importantly, an ordinary colouring is also a cocolouring,
and an ordinary `G_1`-colouring is also an admissible two-graph partition.

## 2. A common concentration theorem

For an induced vertex set `W`, write `T(W)` for one of

\[
 \chi(G[W]),\qquad \zeta(G[W]),\qquad
 X(G_1[W],G_2[W]).                                            \tag{2.1}
\]

Each parameter is hereditary under vertex restriction, rises by at most one
when a deleted vertex is restored, and is subadditive across a vertex-set
partition by concatenating admissible partitions.  These are the only
deterministic structural properties used below.

### Theorem 2.1 (quantitative deterministic interval)

Let `lambda_n -> infinity`.  For each of the three
parameters in (2.1), there is a deterministic integer `h_T(n)` such that,
with probability `1-o(1)`,

\[
 h_T(n)\le T([n])
 \le h_T(n)+O\!\left(
       \frac{\sqrt{n\lambda_n}}{\log n}+n^{1/3}
      \right).                                                \tag{2.2}
\]

The implicit constant is absolute for `p=1/2`.  In particular, for every
function `omega(n)->infinity`, the interval can be chosen to have length

\[
 \omega(n)\frac{\sqrt n}{\log n}.                             \tag{2.3}
\]

#### Proof

Put `epsilon_n=exp(-lambda_n)` and choose the lower quantile

\[
 h_T=\min\{j:\Pr(T([n])\le j)\ge\epsilon_n\}.                 \tag{2.4}
\]

Thus `Pr(T<h_T)<epsilon_n`.

Define

\[
 S_T=\max\{|W|:T(W)\le h_T\}.                                \tag{2.5}
\]

Expose the random graph in `n-1` independent vertex blocks: block `v`
contains the edges from `v` to earlier vertices.  For `X`, put the
corresponding edge vectors from both independent graphs in the same block.
Changing one block changes `S_T` by at most one.  Indeed, after deleting the
affected vertex, every feasible induced set loses at most one vertex and is
unchanged in the other configuration.  McDiarmid's inequality therefore gives

\[
 \Pr(|S_T-\mathbb ES_T|\ge t)
 \le2\exp\!\left(-\frac{2t^2}{n-1}\right).                    \tag{2.6}
\]

Take

\[
 t_n=\sqrt{\frac{n-1}{2}(\lambda_n+1)}.                       \tag{2.7}
\]

Since `Pr(S_T=n)=Pr(T<=h_T)>=epsilon_n`, the upper-tail half of (2.6)
forces `E S_T>=n-t_n`; otherwise `Pr(S_T=n)<epsilon_n`.  The lower-tail
half then gives

\[
 \Pr(S_T<n-2t_n)\le e^{-\lambda_n-1}=o(1).                    \tag{2.8}
\]

On this event choose `W` attaining (2.5), and put `U=[n]\W`.  Concatenating
partitions gives, in all three cases,

\[
 T([n])\le h_T+\chi(G_\star[U]),                              \tag{2.9}
\]

where `G_star=G` for `chi,zeta` and `G_star=G_1` for `X`.
Lemma 1.1 and `|U|<=2t_n` make the last term

\[
 O(t_n/\log n+n^{1/3}).                                      \tag{2.10}
\]

Together with the lower-tail bound following (2.4), this proves (2.2).
Given any prescribed `omega->infinity`, choose `lambda_n->infinity` so slowly
that `sqrt(lambda_n)=o(omega(n))`; also
`n^(1/3)=o(sqrt(n)/log n)`.  This yields (2.3).  ∎

### Theorem 2.2 (rare-event amplification)

Let `T` be any of the three parameters in (2.1).  Suppose deterministic
sequences `k_n` and `Lambda_n>=0` satisfy

\[
 \Pr\{T([n])\le k_n\}\ge e^{-\Lambda_n}.                     \tag{2.11}
\]

Let `r_n->infinity` with `Lambda_n+r_n=o(n)`.  Then, with high probability,

\[
 \boxed{
 T([n])\le k_n+O\!\left(
  \frac{\sqrt{n(\Lambda_n+r_n)}}{\log n}+n^{1/3}
 \right).}                                                   \tag{2.12}
\]

#### Proof

Use (2.5) with `h_T=k_n` and put

\[
 t_n=\sqrt{\frac{n-1}{2}(\Lambda_n+r_n)}.
\]

If `E S_T<=n-t_n`, the event `S_T=n` would have probability at most
`exp[-2t_n^2/(n-1)]=exp[-Lambda_n-r_n]`, contradicting (2.11).
Thus `E S_T>=n-t_n`, and the opposite McDiarmid tail gives

\[
 \Pr\{S_T<n-2t_n\}\le e^{-\Lambda_n-r_n}=o(1).
\]

Colour the leftover as in (2.9)--(2.10).  ∎

An independent reconstruction in
`../audits/RARE_EVENT_AMPLIFICATION_AUDIT.md` gives the following slightly
sharper canonical form.  There is a deterministic `varepsilon_n=o(1)`,
independent of `k_n`, `Lambda_n`, and `r`, such that uniformly for every
deterministic choice `r=r(n)>0`, without assuming `Lambda_n+r=o(n)`,

\[
 \Pr\left\{T([n])>k_n+C\left(
   \frac{\sqrt{n\Lambda_n}+\sqrt{nr}}{\log n}+n^{1/3}+1
  \right)\right\}
 \le e^{-r}+\varepsilon_n.                                  \tag{2.12a}
\]

Indeed, (2.11) and the upper McDiarmid tail imply directly that
`n-E S_T<=sqrt((n-1)Lambda_n/2)`.  The lower tail with radius
`sqrt((n-1)r/2)` then leaves at most the sum of these two radii uncovered.
The simultaneous leftover lemma finishes the argument.  Its single failure
probability is precisely the same deterministic `varepsilon_n` for all three
parameters.  The original Theorem 2.2 is therefore valid as stated; its
`o(n)` hypothesis only ensures that the guaranteed leftover is sublinear.

For `T=zeta`, (2.11) may come from a Paley--Zygmund bound on a signed
cocolouring count.  If its normalized second moment is at most
`exp(Lambda_n)`, a cocolouring at `k_n` exists with probability at least
`exp(-Lambda_n)`, and (2.12) makes it typical after only the displayed
additive cost.  Thus a proposed deterministic separation `H_n` survives
whenever

\[
 \Lambda_n=o\!\left(\frac{H_n^2\log^2 n}{n}\right),           \tag{2.13}
\]

up to the harmless `n^(1/3)` term.  The extra `log^2 n` in (2.13), compared
with direct Azuma amplification, materially changes the exceptional-phase
second-moment budget.  If
`B_n=H_n^2 log^2(n)/n -> infinity`, choose `r_n->infinity` with
`r_n=o(B_n)`.  If `B_n` stays bounded along a subsequence, then
`Lambda_n=o(B_n)` forces the Paley--Zygmund seed probability itself to tend
to one there (after the elementary two-case split recorded in the audit).
For the intended `H_n=n/log^3 n`, `B_n=n/log^4 n -> infinity`, so the usable
budget is unconditionally `Lambda_n=o(n/log^4 n)`.

### Audit of what the theorem does not say

- The interval is deterministic but is not asserted to be centred at the
  expectation or median.
- A one-vertex Lipschitz bound alone gives a `sqrt n` scale.  The logarithmic
  gain comes from colouring the small leftover set, not from a stronger
  bounded-differences inequality.
- For `X`, no property of the second graph is needed for the leftover: using
  only independent sets of `G_1` is enough.
- The result is a marginal concentration theorem.  It does not claim that
  `chi(G_1)` and `X(G_1,G_2)` are independent.

## 3. Sharpened forum amplification

The exact coupling in `TWO_GRAPH_MODEL.md` proves

\[
 \zeta(G)\preceq_{\rm st}X(G_1,G_2).                          \tag{3.1}
\]

The logarithmically improved intervals turn a positive-probability surrogate
gap into a high-probability single-graph gap without passing through
expectations.

### Proposition 3.1

Suppose there is a fixed `p>0` and a positive sequence `a_n` such that, for
all sufficiently large `n`,

\[
 \Pr\{\chi(G_1)-X(G_1,G_2)\ge a_n\}\ge p.                    \tag{3.2}
\]

If

\[
 \frac{a_n\log n}{\sqrt n}\longrightarrow\infty,             \tag{3.3}
\]

then there is `b_n=(1-o(1))a_n` such that

\[
 \Pr\{\chi(G)-\zeta(G)\ge b_n\}\longrightarrow1.             \tag{3.4}
\]

#### Proof

Choose `omega(n)->infinity` slowly enough that

\[
 w_n:=\omega(n)\sqrt n/\log n=o(a_n).                         \tag{3.5}
\]

Apply Theorem 2.1 to obtain deterministic intervals

\[
 [h_\chi,h_\chi+w_\chi],\qquad [h_X,h_X+w_X],
 \qquad w_\chi,w_X\le w_n,                                  \tag{3.6}
\]

which contain the two marginals with probability `1-o(1)`.  Their joint
occurrence for `(G_1,G_2)` also has probability `1-o(1)`, without any
independence assertion.  Hence (3.2) intersects this joint typical event for
all large `n`.  On any outcome in the intersection,

\[
 a_n\le\chi(G_1)-X(G_1,G_2)
 \le h_\chi+w_\chi-h_X.                                      \tag{3.7}
\]

Thus the deterministic endpoints satisfy

\[
 h_\chi-(h_X+w_X)\ge a_n-w_\chi-w_X.                         \tag{3.8}
\]

For a fresh graph, `chi(G)>=h_chi` with probability `1-o(1)`.  By (3.1),

\[
 \Pr\{\zeta(G)\le h_X+w_X\}
 \ge\Pr\{X\le h_X+w_X\}=1-o(1).                             \tag{3.9}
\]

The marginal lower event for `chi(G)` and upper event for `zeta(G)` occur on
the same fresh graph with probability `1-o(1)` by a union bound; the special
coupling used to prove stochastic domination is not reused here.  Combining
(3.8)--(3.9) proves (3.4) with
`b_n=a_n-w_chi-w_X=(1-o(1))a_n`.  ∎

This strictly improves the elementary expectation-plus-Azuma sufficient
condition `a_n >> sqrt n` when the success probability in (3.2) is bounded
away from zero.  The quantifier remains essential: (3.2) only on a subsequence
still yields (3.4) only on that subsequence.

## 4. Exact bottleneck after the improvement

It is now enough to prove, uniformly for every sufficiently large `n`, a
fixed-positive-probability estimate

\[
 \chi(G_1)-X(G_1,G_2)
 \gg \frac{\sqrt n}{\log n}.                                  \tag{4.1}
\]

The predicted `n/log^3 n` surrogate gap is vastly larger than (4.1), so
concentration is not the scale-limiting obstacle.  The unresolved step is the
existence/threshold analysis for `X` through every integer-profile phase.
