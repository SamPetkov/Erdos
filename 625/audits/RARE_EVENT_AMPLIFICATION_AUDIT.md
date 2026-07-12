# Independent audit of rare-event amplification

## Verdict

The rare-event amplification theorem in
`research/proofs/ALON_CONCENTRATION_EXTENSION.md` is correct for each of

\[
 \chi(G),\qquad \zeta(G),\qquad X(G_1,G_2).
\]

The vertex-fibre product exposure is valid, the maximum-coverable-subset
variable has oscillation exactly at most one per fibre, and the leftover may
be coloured uniformly even though it is selected after both graphs have been
seen.  The constants in the displayed McDiarmid argument are conservative
but correct.  No independence between the random leftover and the graph used
to colour it is required.

There are two qualifications worth making explicit.

1. The hypothesis \(\Lambda_n+r_n=o(n)\) is not needed for the proof.  It
   merely makes the guaranteed leftover sublinear.  A slightly sharper form
   below works for arbitrary \(\Lambda_n\geq0\) and \(r_n>0\).
2. To derive an \(o(H_n)\) amplification cost from a *single* application of
   the theorem, one chooses
   \(r_n\to\infty\) with
   \(r_n=o(H_n^2\log^2n/n)\); this requires the latter scale to diverge.
   If that scale stays bounded while
   \(\Lambda_n=o(H_n^2\log^2n/n)\), then \(\Lambda_n\to0\) and the seed event
   itself already has probability \(1-o(1)\).  Thus the budget implication in
   the proof note is valid after this elementary two-case interpretation.  In
   the intended application \(H_n=n/\log^3n\), the budget is
   \(n/\log^4n\to\infty\), so no qualification is active.

## 1. Probability space and the only valid product exposure

For one graph, orient every unordered pair toward its larger endpoint and
write

\[
 B_v=(1_{\{uv\}\in E(G)}:u<v),\qquad 2\leq v\leq n.
\]

The \(n-1\) nonempty vectors \(B_2,\ldots,B_n\) are independent.  For
\(X(G_1,G_2)\), use the combined fibre

\[
 B_v=((1_{\{uv\}\in E(G_1)})_{u<v},
      (1_{\{uv\}\in E(G_2)})_{u<v}).
\]

These combined fibres are again independent.  Changing one fibre changes
only edges incident with its endpoint \(v\).  It need not change every edge
incident with \(v\); the important fact is that deleting \(v\) removes every
changed coordinate.

This orientation is essential.  Full undirected stars are not independent,
because two stars share their joining edge.  Exposing the two whole graphs as
two blocks also does not give oscillation one.  The fibre construction in the
proof note avoids both errors.

## 2. Independent reconstruction of the Lipschitz variable

Fix a deterministic integer \(k\), and let \(T(W)\) be the appropriate
parameter of the structure induced on \(W\).  Define

\[
 S_k=\max\{|W|:W\subseteq[n],\ T(W)\leq k\}.                 \tag{2.1}
\]

The premise \(\Pr(T([n])\leq k)>0\) implies \(k\geq1\) for \(n\geq1\), so
the feasible family is nonempty on every realization (in particular,
singletons and the empty set are feasible).  All three parameters are
hereditary under vertex deletion.

Consider two inputs differing in one fibre at vertex \(v\), and let \(W\)
maximize (2.1) in the first input.

* If \(v\notin W\), no coordinate of the induced input on \(W\) changed, so
  \(W\) is feasible in the second input.
* If \(v\in W\), the induced input on \(W\setminus\{v\}\) did not change,
  and heredity gives
  \(T(W\setminus\{v\})\leq T(W)\leq k\).

Thus the second maximum is at least \(|W|-1\).  Interchanging the two inputs
proves

\[
       |S_k(B_2,\ldots,B_n)-S_k(B'_2,\ldots,B'_n)|\leq1     \tag{2.2}
\]

whenever only one fibre differs.  The argument applies verbatim to \(X\)
because deletion is simultaneous in the two induced graphs.  It does not
assume that an optimal partition is unique or stable.

Consequently, with \(\mu=\mathbb E S_k\), the one-sided forms of
McDiarmid's inequality give

\[
 \Pr(S_k-\mu\geq t),\ \Pr(\mu-S_k\geq t)
 \leq \exp\!\left(-\frac{2t^2}{n-1}\right).                 \tag{2.3}
\]

There is no leading factor two in either one-sided inequality.

## 3. Exact conversion of seed mass into a large coverable set

Suppose

\[
       \Pr(T([n])\leq k)\geq e^{-\Lambda},\qquad \Lambda\geq0. \tag{3.1}
\]

There is exactly one subset of size \(n\), hence

\[
       \{S_k=n\}=\{T([n])\leq k\}.                          \tag{3.2}
\]

Since \(S_k\leq n\), put \(d=n-\mu\geq0\).  If \(d>0\), (2.3) and
(3.1)--(3.2) imply

\[
 e^{-\Lambda}
 \leq \Pr(S_k=n)
 \leq \exp\!\left(-\frac{2d^2}{n-1}\right),
\]

and therefore

\[
       n-\mu\leq a:=\sqrt{\frac{n-1}{2}\Lambda}.            \tag{3.3}
\]

For \(\Lambda=0\), (3.1) says that the event in (3.2) has probability one,
so (3.3) remains true.

For any \(r>0\), set

\[
       b:=\sqrt{\frac{n-1}{2}r}.
\]

If \(S_k<n-a-b\), then (3.3) gives \(S_k<\mu-b\).  A second use of (2.3)
therefore yields the sharper estimate

\[
       \Pr\{S_k<n-a-b\}\leq e^{-r}.                         \tag{3.4}
\]

Up to an inessential rounding by one, (3.4) says that all but
\(a+b\) vertices are coverable with \(k\) parts.

The proof note instead sets

\[
 t=\sqrt{\frac{n-1}{2}(\Lambda+r)}.
\]

If \(\mu\leq n-t\), (2.3) would make the probability in (3.2) at most
\(e^{-\Lambda-r}<e^{-\Lambda}\), a contradiction.  Hence
\(\mu>n-t\), and then

\[
       \Pr(S_k<n-2t)\leq e^{-\Lambda-r}.                    \tag{3.5}
\]

This confirms every inequality and strictness issue in the original proof.
Equation (3.4) has a smaller radius, whereas (3.5) has a smaller displayed
failure probability; both have the same asymptotic order needed here.

## 4. Independent check of the uniform leftover lemma

Let \(G\sim G(n,1/2)\), let \(H=\overline G\), and put
\(u=\lceil n^{1/4}\rceil\).  For each fixed \(u\)-set \(A\), a Chernoff
bound gives

\[
 \Pr\left(e_H(A)<\frac14\binom u2\right)
       \leq e^{-c_0u^2}                                     \tag{4.1}
\]

for an absolute \(c_0>0\).  Meanwhile
\(\binom nu\leq e^{O(u\log n)}\), and
\(u\log n=o(u^2)\).  A union bound shows that, with probability \(1-o(1)\),
every \(u\)-set has \(H\)-edge density at least \(1/4\).  Averaging the
edge count over all \(u\)-subsets extends the same conclusion to every set
of size at least \(u\).

On this simultaneous event, start with any \(A\) of size at least
\(n^{1/3}\) and greedily construct a clique in \(H[A]\).  While the current
candidate set has size at least \(u\), it has a vertex with at least
\((m-1)/4\geq m/5\) neighbours for all large \(n\).  Restricting to that
neighbourhood preserves adjacency to all previously selected vertices.
Because

\[
       \frac{n^{1/3}}{n^{1/4}}=n^{1/12},
\]

this can be iterated \(c\log n\) times for an absolute \(c>0\) (for
example, any sufficiently small \(c<1/(12\log5)\)).  The resulting
\(H\)-clique is a \(G\)-independent set.

Repeatedly removing such independent sets until fewer than \(n^{1/3}\)
vertices remain, and then using singleton colours, proves the simultaneous
bound

\[
       \chi(G[U])\leq C\frac{|U|}{\log n}+n^{1/3}+1          \tag{4.2}
\]

for every \(U\subseteq[n]\), on one event of probability \(1-o(1)\).
This is stronger than a statement for each fixed \(U\).  The simultaneity is
exactly what permits \(U\) to depend on the whole random input.

For a cocolouring, an ordinary independent colour class is admissible.  For
\(X\), an independent set of \(G_1\) is admissible regardless of \(G_2\).
Thus, for every vertex partition \([n]=W\mathbin{\dot\cup}U\),

\[
 \begin{aligned}
 \chi(G)&\leq\chi(G[W])+\chi(G[U]),\\
 \zeta(G)&\leq\zeta(G[W])+\chi(G[U]),\\
 X(G_1,G_2)&\leq X(G_1[W],G_2[W])+\chi(G_1[U]).              \tag{4.3}
 \end{aligned}
\]

No independence assertion is present in (4.2)--(4.3).  In particular, the
maximizing \(W\), and hence \(U\), may depend on both \(G_1\) and \(G_2\).

## 5. Sharpened audited theorem

The preceding calculation proves the following quantitative version, which
also confirms the asymptotic theorem under audit.

**Audited rare-event theorem.**  Let \(n\geq2\), let \(T\) be one of
\(\chi(G)\), \(\zeta(G)\), or \(X(G_1,G_2)\), and suppose

\[
       \Pr(T\leq k)\geq e^{-\Lambda}
\]

for deterministic \(k\) and \(\Lambda\geq0\).  For every deterministic
\(r>0\),

\[
 \Pr\left\{
 T>k+C\frac{\sqrt{n\Lambda}+\sqrt{nr}}{\log n}+n^{1/3}+1
 \right\}
 \leq e^{-r}+o(1),                                          \tag{5.1}
\]

where the \(o(1)\) is the failure probability of the uniform random-graph
event and \(C\) is absolute.  The statement is asymptotic in \(n\), uniformly
in deterministic \(k,\Lambda,r\); no condition
\(\Lambda+r=o(n)\) is required.

To see (5.1), take a maximizing \(W\) in (2.1).  On the event (3.4), its
leftover \(U\) has size at most \(a+b+1\).  Intersect with the simultaneous
event (4.2) and use (4.3).

If \(r_n\to\infty\), (5.1) is a high-probability statement.  Since

\[
 \sqrt{\Lambda_n}+\sqrt{r_n}
 \leq\sqrt{2(\Lambda_n+r_n)},
\]

it implies the order of the boxed bound in Theorem 2.2.  Conversely, the
original argument (3.5) proves that boxed bound directly.  The additional
hypothesis \(\Lambda_n+r_n=o(n)\) in the original theorem simply ensures
\(|U|=o(n)\); the proof and conclusion remain valid without it, although the
bound may then be coarse or trivial.

## 6. Audit of all asymptotic regimes

The proof remains valid in each potentially delicate regime.

* **\(\Lambda_n=0\).**  The seed event has probability one, so the conclusion
  is immediate; (3.3) gives \(S_k=n\) almost surely.
* **Bounded \(\Lambda_n>0\).**  Taking any \(r_n\to\infty\) gives a leftover
  of order \(\sqrt{nr_n}\), plus the smaller \(O(\sqrt n)\) seed term.
* **Diverging \(\Lambda_n=o(n)\).**  The seed contribution is
  \(O(\sqrt{n\Lambda_n})\), exactly as claimed.  It does not acquire an
  additional factor \(\sqrt{\log n}\).
* **\(\Lambda_n+r_n=o(n)\).**  Then \(a+b=o(n)\), so the maximizing coverable
  set contains \(n-o(n)\) vertices.  No stronger relation between
  \(\Lambda_n\) and \(r_n\) is used.
* **Very small leftovers.**  If
  \((\sqrt{n\Lambda_n}+\sqrt{nr_n})/\log n<n^{1/3}\), the coarse terminal
  singleton term dominates.  It was retained in the theorem, so this is not
  a gap.
* **Very large \(\Lambda_n\).**  Formula (5.1) is still true.  If its
  right-hand additive bound exceeds \(n\), it is merely non-informative.
* **Random, adaptively selected leftover.**  The event (4.2) is simultaneous
  over all subsets.  Conditioning on \(S_k\) or treating the leftover as a
  fresh random graph would be invalid, but neither operation occurs.

## 7. Exact second-moment budget implication

Let \(Z\geq0\) count admissible cocolourings with at most \(k_n\) parts.  If

\[
       \frac{\mathbb E Z^2}{(\mathbb E Z)^2}\leq e^{\Lambda_n},
\]

Paley--Zygmund at threshold zero gives

\[
       \Pr(Z>0)\geq e^{-\Lambda_n}.                         \tag{7.1}
\]

Because \(Z>0\) implies \(\zeta(G)\leq k_n\), the theorem applies.  For a
target separation \(H_n>0\), put

\[
       B_n:=\frac{H_n^2\log^2n}{n}.                         \tag{7.2}
\]

The amplified part of the additive cost, divided by \(H_n\), is

\[
 O\left(\sqrt{\frac{\Lambda_n}{B_n}}+
         \sqrt{\frac{r_n}{B_n}}\right),                    \tag{7.3}
\]

apart from \(n^{1/3}/H_n\).  Thus, whenever \(B_n\to\infty\), the precise
single-run sufficient conditions are

\[
       \Lambda_n=o(B_n),\qquad
       r_n\to\infty,\qquad r_n=o(B_n).                      \tag{7.4}
\]

For example, take \(r_n=\sqrt{B_n}\).  Also, \(B_n\to\infty\) implies

\[
 H_n\gg\frac{\sqrt n}{\log n}\gg n^{1/3},                 \tag{7.5}
\]

so the terminal \(n^{1/3}\) term is automatically \(o(H_n)\).

If \(B_n\) does not diverge, the bare condition
\(\Lambda_n=o(B_n)\) should not be justified by trying to choose a globally
diverging \(r_n=o(B_n)\), which may be impossible.  Instead use the following
complete case split.  Write \(\varepsilon_n=\Lambda_n/B_n\to0\).  Indices
with \(\varepsilon_n=0\) are immediate from (7.1); on the remaining indices
the following split is well defined.

* On indices where \(B_n<\varepsilon_n^{-1/2}\), one has
  \(\Lambda_n<\sqrt{\varepsilon_n}=o(1)\).  Equation (7.1) itself then has
  probability \(1-o(1)\), so no leftover and no amplification cost are
  needed.
* On the complementary indices,
  \(B_n\geq\varepsilon_n^{-1/2}\to\infty\).  Apply (5.1) on this subsequence
  with \(r_n=\sqrt{B_n}\); equations (7.3)--(7.5) give cost \(o(H_n)\).

Consequently the concise budget condition

\[
       \boxed{\Lambda_n=o\left(H_n^2\log^2n/n\right)}       \tag{7.6}
\]

is indeed sufficient when interpreted with this direct-event/amplification
split.  If one cites only the literal statement of Theorem 2.2, rather than
the stronger (5.1), one must additionally check its stated
\(\Lambda_n+r_n=o(n)\) hypothesis on the amplified indices.  This check is
automatic in the application presently under study:

\[
 H_n=\frac{n}{\log^3n},\qquad
 B_n=\frac{n}{\log^4n}=o(n),\qquad
 \Lambda_n=o(B_n).
\]

The gain over direct vertex-Azuma amplification is therefore genuinely the
factor \(\log^2n\) in the allowable second-moment exponent.

## 8. Failure-mode and counterexample audit

No counterexample to the theorem was found.  The following nearby statements
would be false or unsupported, and none is used in the proof.

1. A leftover lemma valid only for each deterministic \(U\) cannot be applied
   to the maximizing random leftover.  Uniformity over all \(U\) is required.
2. Treating the maximizing leftover in \(X\) as independent of \(G_1\) would
   be false.  The simultaneous \(G_1\) event removes that need.
3. Using independent-set removal in an unspecified auxiliary graph would not
   suffice for \(X\).  The proof specifically uses \(G_1\), whose independent
   sets are allowed \(X\)-parts.
4. The ordinary Lipschitz property of \(T([n])\) gives only a
   \(\sqrt{n\Lambda}\)-scale parameter bound.  The division by \(\log n\)
   comes only after converting the uncovered vertices into colour classes.
5. The relation \(\Pr(S_k=n)=\Pr(T\leq k)\), rather than merely an
   implication, is essential for locating the mean of \(S_k\).
6. A global assertion that \(r_n=o(B_n)\) can be chosen from (7.6) alone is
   false when \(B_n\) is bounded.  In that regime the seed event is already
   high probability, as explained in Section 7.
7. A numerical or fixed-subsequence second-moment estimate gives only the
   corresponding numerical or subsequence consequence.  The theorem does
   not repair a failure of the hypothesis to hold for every sufficiently
   large \(n\).

## 9. Final formal assessment

**Theorem 2.2: pass.**  The product exposure, one-fibre Lipschitz bound,
McDiarmid constants, adaptive-leftover step, and all stated
\(\Lambda_n+r_n=o(n)\) regimes are sound.

**Budget (2.13): pass with an exposition clarification.**  On diverging
budget scales it follows by choosing \(r_n\to\infty\) slowly; on bounded
budget scales the hypothesis forces the seed probability itself to tend to
one.  For \(H_n=n/\log^3n\), the usable exponent budget is exactly
\(o(n/\log^4n)\).

**Recommended canonical form.**  Use (5.1), which has failure probability
\(e^{-r_n}+o(1)\), additive cost

\[
 O\left(\frac{\sqrt{n\Lambda_n}+\sqrt{nr_n}}{\log n}
          +n^{1/3}\right),
\]

and does not require \(\Lambda_n+r_n=o(n)\).  This is a strengthening, not a
repair of a false statement.
