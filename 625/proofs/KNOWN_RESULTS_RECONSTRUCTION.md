# Reconstruction of the known results

This note keeps probability quantifiers explicit and gives the short
reconstructions.  The line-by-line tame-colouring dependency audit, exact
version history, and source-level hypotheses are recorded in Sections 4--7
of `research/sources/RECENT_WORK_AUDIT.md`; together those two files form the
complete known-results reconstruction.

## 1. First-order asymptotics

Let `L=log_2 n` and let

\[
r=\lceil 2L\rceil.
\]

For `r>=2`, the expected number `H_r` of `r`-vertex subsets inducing either a
clique or an independent set in `G(n,1/2)` is

\[
\mathbb E H_r=2\binom nr2^{-\binom r2}.
\]

Using `binom(n,r) <= (en/r)^r`,

\[
\begin{aligned}
\log_2\mathbb E H_r
&\le 1+r\log_2(en/r)-\binom r2\\
&\le -2L\log_2L+O(L),
\end{aligned}
\]

which tends to minus infinity. Markov's inequality therefore gives

\[
\Pr\bigl(\max\{\alpha(G),\omega(G)\}\ge r\bigr)=o(1).       \tag{1.1}
\]

On the complementary event, every class in every cocolouring has fewer than
`2 log_2 n` vertices. Hence any such partition into `k` classes satisfies

\[
n<2k\log_2n,
\qquad\text{and therefore}\qquad
\zeta(G)\ge \frac{n}{2\log_2n}.                              \tag{1.2}
\]

The deterministic inequality `zeta(G)<=chi(G)` follows by allowing every
ordinary colour class as an independent cocolour class. Bollobás's dense
random-graph colouring theorem gives, for fixed `p=1/2`,

\[
\chi(G(n,1/2))\le (1+o(1))\frac n{2\log_2n}
\quad\text{with high probability}.                           \tag{1.3}
\]

Intersecting the two high-probability events in (1.1) and (1.3) yields

\[
\frac n{2\log_2n}\le\zeta(G)\le\chi(G)
\le(1+o(1))\frac n{2\log_2n}\quad\text{whp}.                \tag{1.4}
\]

Thus both parameters are asymptotic to `n/(2 log_2 n)`. The argument only
controls their ratio and says nothing at the additive scale.

Source caveat: the full original Bollobás (1988) article remains a recorded
paywall retrieval failure. The theorem is explicitly restated in the later
primary papers audited here, but the user's original-text requirement is not
yet satisfied for that dependency.

## 2. Anti-concentration implication

The following reconstructs Proposition 3 of Heckel's 2024 EJC paper, including
the numerical constants and Harris monotonicity directions.

Let

\[
D(G)=\chi(G)-\zeta(G)
\]

and suppose an integer-valued deterministic sequence `g(n)` satisfies

\[
\Pr(D(G)\le g(n))>0.999.                                    \tag{2.1}
\]

Couple `G` with its complement `bar G`. Since `bar G` has the same
`G(n,1/2)` distribution and

\[
\zeta(\bar G)=\zeta(G),                                     \tag{2.2}
\]

applying (2.1) to `bar G` gives, with probability at least `0.999`,

\[
\chi(\bar G)\le\zeta(\bar G)+g
=\zeta(G)+g\le\chi(G)+g.                                   \tag{2.3}
\]

Let `s_n` be the smallest integer `s` for which

\[
\Pr(\chi(G)\le s)\ge0.05.
\]

Define

\[
\mathcal D=\{\chi(G)\le s_n\},\qquad
\mathcal U=\{\chi(\bar G)\le s_n+g(n)\}.
\]

As events in the edge indicators of `G`, `D` is decreasing. The event `U` is
increasing: adding edges to `G` deletes edges from `bar G` and cannot increase
`chi(bar G)`. On `D`, either (2.3) fails or `U` holds, so

\[
\Pr(\mathcal U\cap\mathcal D)
\ge\Pr(\mathcal D)-0.001.                                   \tag{2.4}
\]

Harris's inequality for an increasing and a decreasing event has the
negative-correlation direction

\[
\Pr(\mathcal U\cap\mathcal D)
\le\Pr(\mathcal U)\Pr(\mathcal D).                          \tag{2.5}
\]

Since `P(D)>=0.05`, (2.4)--(2.5) imply

\[
\Pr(\mathcal U)\ge1-\frac{0.001}{0.05}=0.98.                \tag{2.6}
\]

The two chromatic numbers have the same distribution. Minimality of `s_n`
also gives `P(chi(G)<=s_n-1)<0.05`. Consequently

\[
\Pr\bigl(s_n\le\chi(G)\le s_n+g(n)\bigr)
>1-0.05-0.02=0.93>0.9.                                      \tag{2.7}
\]

Thus (2.1) creates a deterministic concentration interval of length exactly
`g(n)` containing `chi(G(n,1/2))` with probability greater than `0.9`.

The non-concentration theorem used by Heckel states that there is `c>0` such
that any sequence of intervals containing `chi(G(n,1/2))` with probability
greater than `0.9` has, along an infinite sequence `n*`, length at least

\[
c\frac{\sqrt{n^*}\log\log n^*}{(\log n^*)^3}.                \tag{2.8}
\]

Combining (2.7) and (2.8) gives the advertised lower bound on `g(n*)`.

This conclusion is only an infinite-subsequence obstruction to a uniform
high-probability upper bound. It neither produces a lower bound on the gap at
those `n*` with probability tending to one nor implies divergence for all
sufficiently large integers.

## 3. Density theorem: exact top-level statement

Set

\[
\alpha_0=2\log_2n-2\log_2\log_2n+2\log_2(e/2)+1,
\qquad \alpha=\lfloor\alpha_0\rfloor,
\]

and

\[
\mu_\alpha=\binom n\alpha2^{-\binom\alpha2}.
\]

Heckel's Theorem 1 (arXiv:2409.17614v2) is:

> Fix `epsilon>0`, and restrict to integers `n` satisfying
> `n^(0.05+epsilon) <= mu_alpha <= n^(1-epsilon)`. For
> `G~G(n,1/2)`, with high probability along that restricted sequence,
> `chi(G)-zeta(G) >= n^(1-epsilon)`.

The epsilon is fixed before `n` tends to infinity. The theorem does not
license `epsilon=epsilon(n)` and does not cover all integers. The exact
oscillatory density and exceptional-interval calculations are proved in
`EXCEPTIONAL_REGIME.md`.

The detailed reconstruction in `RECENT_WORK_AUDIT.md`, Sections 4.4 and 5,
checks the remaining proof chain as follows:

1. Heckel's Proposition 5 constructs a shifted `(alpha-1)`-bounded profile
   with a cocolouring first-moment gain and verifies the fixed tame-profile
   hypotheses only under
   `n^(0.05+epsilon)<=mu_alpha<=n^(1-epsilon)`.
2. Proposition 6 transfers the truncated ordinary-colouring overlap bounds
   to signed cocolourings by counting compatible signs.  It uses an upper
   bound `2^(2k-ell)` when two partitions share `ell` whole parts; it does
   not replace the ordinary second moment by a formal factor `2^(2k)`.
3. Tame Lemma 7.20 supplies the near-optimal profile, its Gaussian tail, and
   the macroscopic partial-profile expectation.  The latter is the clause
   requiring `mu_(alpha-1)>=n^1.05`; the fixed `epsilon` cannot be sent to
   zero with `n`.
4. Tame Lemmas 5.1--5.3 and 6.3--6.5 bound the truncated first and second
   moments in `G(n,m)`.  Lemma 3.7 compares the relevant one- and two-profile
   forbidden-edge probabilities with `G(n,1/2)` at logarithmic cost
   `exp(O((log n)^2))`.
5. Paley--Zygmund gives the positive-probability cocolouring at the shifted
   location.  Scott's/Alon's deterministic-interval argument, with a
   uniform induced-leftover colouring event, amplifies this to the theorem's
   high-probability gap on every admissible sequence.

The exact formulas, constants, imported theorem numbers, probability levels,
and model transitions for these five steps are in the cited audit.  In
particular, no part of that reconstruction upgrades the result from its
fixed-`epsilon` admissible sequences to all integers.
