# Independent audit of the Alon--Scott concentration extension

## Verdict

The leftover-colouring proof extends to both the cochromatic number
\(\zeta(G)\) and the two-graph parameter \(X(G_1,G_2)\).  For each of
\(T_n=\chi(G)\), \(\zeta(G)\), and \(X(G_1,G_2)\), and for every deterministic
\(\omega_n\to\infty\), there is a deterministic interval \(I_n\) of length at
most

\[
        \omega_n\frac{\sqrt n}{\log n}
\]

such that \(\Pr(T_n\in I_n)=1-o(1)\).  Here \(G,G_1,G_2\) have law
\(G(n,1/2)\), with \(G_1,G_2\) independent in the definition of \(X\).

The claimed stochastic-domination consequence is also correct, and in fact
does not require a concentration theorem for \(\zeta\).  Concentration of
\(\chi\) and \(X\), followed by the upper-tail implication of
\(\zeta\preceq_{\rm st}X\), is enough.

This verdict was derived before reading
`research/proofs/ALON_CONCENTRATION_EXTENSION.md`.  The comparison with that
file appears near the end of this audit.

## 1. Definitions and exact scope

For a graph \(G\) on \([n]\):

* \(\chi(G)\) is the minimum number of independent parts in a vertex
  partition;
* \(\zeta(G)\) is the minimum number of parts, each of which induces either a
  clique or an independent set;
* \(X(G_1,G_2)\) is the minimum number of parts, each of which is independent
  in at least one of \(G_1,G_2\).

All three parameters are understood on induced substructures.  Logarithm
bases only change constants below.

The proof establishes a statement for every sufficiently large integer \(n\),
not merely along a subsequence.  The interval may depend on the chosen
function \(\omega_n\), but is deterministic once \(n\) and \(\omega_n\) are
fixed.

## 2. The uniform leftover property

The only random-graph input needed after the bounded-difference step is the
following simultaneous statement.

**Uniform independent-set lemma.**  There is an absolute constant \(c>0\)
such that, with probability \(1-o(1)\), every \(S\subseteq[n]\) with
\(|S|>n^{1/3}\) contains an independent set of size at least \(c\log n\).

Here is a self-contained derivation.  Put \(H=\overline G\), which again has
law \(G(n,1/2)\), and let \(u=\lceil n^{1/4}\rceil\).  For a fixed \(u\)-set
\(A\), a Chernoff bound gives

\[
 \Pr\!\left(e_H(A)<\frac14\binom u2\right)\leq \exp(-c_0u^2)
\]

for an absolute \(c_0>0\).  Since
\(\binom nu\leq\exp(O(u\log n))\) and \(u\log n=o(u^2)\), a union bound shows
that, with probability \(1-o(1)\), every \(u\)-set has edge density at least
\(1/4\).  Averaging over all \(u\)-subsets shows the same lower density bound
for every set of size at least \(u\).

On this event, greedily build a clique in \(H[S]\).  Whenever the current
candidate set has size at least \(u\), it contains a vertex of degree at least
one quarter of the remaining size minus one.  Replacing the candidate set by
that vertex's neighbours shrinks it by a factor at most five, for large \(n\).
Starting from \(|S|\geq n^{1/3}\), this can be repeated \(c\log n\) times
(for example any fixed \(c<1/(13\log 5)\) works), because
\(n^{1/3}/5^{c\log n}>n^{1/4}\).  The resulting clique of \(H\) is an
independent set of \(G\).

Crucially, this event is uniform over all \(S\).  Thus \(S\) may be selected
after seeing the graph.  On the event, for every \(U\subseteq[n]\), repeated
removal of such independent sets and then singleton-colouring the final
\(n^{1/3}\) vertices gives

\[
 \chi(G[U])\leq \frac{|U|}{c\log n}+n^{1/3}+1.       \tag{2.1}
\]

Consequently the same leftover estimate holds for the other parameters:

\[
 \zeta(G[U])\leq\chi(G[U]),\qquad
 X(G_1[U],G_2[U])\leq\chi(G_1[U]).                  \tag{2.2}
\]

For \(X\), the event used in (2.1) is simply the uniform event for \(G_1\).
It remains valid even though the eventual leftover \(U\) depends on both
\(G_1\) and \(G_2\).

## 3. The structural facts used by the martingale argument

Let \(T\) denote any of \(\chi,\zeta,X\), with the ambient graph or graph pair
suppressed.  Three deterministic properties are used:

1. **Hereditary restriction.** If \(A\subseteq B\), then
   \(T(\mathcal R[A])\leq T(\mathcal R[B])\), by restricting every part.
2. **Singleton extension.** Adding one vertex raises \(T\) by at most one,
   since a singleton is admissible for all three parameters.
3. **Disjoint-set subadditivity.** For a vertex partition \(V=W\dot\cup U\),
   \[
       T(\mathcal R)\leq T(\mathcal R[W])+T(\mathcal R[U]),    \tag{3.1}
   \]
   by concatenating the two partitions.

These facts first give the ordinary one-vertex Lipschitz statement.  If
\(\mathcal R,\mathcal R'\) differ only on edges incident with \(v\), put
\(t_0=T(\mathcal R[[n]\setminus\{v\}])\), which is the same for both
realizations.  Restriction and singleton extension put both
\(T(\mathcal R)\) and \(T(\mathcal R')\) in
\(\{t_0,t_0+1\}\).  Hence \(|T(\mathcal R)-T(\mathcal R')|\leq1\).
This alone gives only the usual \(O(\omega\sqrt n)\) whp window.

Fix an integer \(h\), and define the maximum coverable-subset variable

\[
 s_h(\mathcal R):=\max\{|W|:W\subseteq[n],\ T(\mathcal R[W])\leq h\}. \tag{3.2}
\]

If two realizations differ only on edges incident with one vertex \(v\), then

\[
        |s_h(\mathcal R)-s_h(\mathcal R')|\leq1.              \tag{3.3}
\]

Indeed, take a maximizing \(W\) for the first realization.  If \(v\notin W\),
the same \(W\) is feasible in the second.  If \(v\in W\), then
\(W\setminus\{v\}\) is feasible in the second by hereditary restriction.
This gives one direction of (3.3); symmetry gives the other.

The relevant product blocks are explicit.  Order the vertices.  For a single
graph, block \(i\) consists of all indicators of edges \(ij\) with \(j<i\).
For \(X\), block \(i\) contains those indicators in **both** graphs.  The
blocks are independent.  Altering one block changes only edges incident with
vertex \(i\), so (3.3) gives bounded-difference constant exactly one.  It is
unnecessary, and weaker by an irrelevant constant, to expose the two graphs
as \(2n\) separate blocks.

McDiarmid's inequality therefore yields, with \(n-1\) nonempty blocks,

\[
 \Pr(|s_h-\mathbb Es_h|\geq t)
 \leq 2\exp\!\left(-\frac{2t^2}{n-1}\right).                 \tag{3.4}
\]

The deletion proof of (3.3), rather than a claimed Lipschitz property of
\(T\) itself, is the point that makes the Alon--Scott proof transfer verbatim.

## 4. Quantile choice and interval endpoints

Fix a deterministic \(\omega_n\to\infty\), and write \(q_n=\omega_n\) (for
large \(n\), when \(q_n>1\)).  Define the lower quantile

\[
 h_n:=\min\{r\in\mathbb Z_{\geq0}:\Pr(T_n\leq r)>q_n^{-1}\}. \tag{4.1}
\]

Because \(T_n\) is integer-valued, minimality gives the exact lower-endpoint
bound

\[
       \Pr(T_n<h_n)=\Pr(T_n\leq h_n-1)\leq q_n^{-1}=o(1).    \tag{4.2}
\]

Let \(s=s_{h_n}\).  The events \(\{s=n\}\) and \(\{T_n\leq h_n\}\) are
identical, hence

\[
        \Pr(s=n)>q_n^{-1}.                                   \tag{4.3}
\]

Set

\[
        t_n=\sqrt{\frac{n-1}{2}\log(8q_n)}.                  \tag{4.4}
\]

The one-sided version of (3.4) is at most \((8q_n)^{-1}\) at distance
\(t_n\).  If \(\mathbb Es\leq n-t_n\), then \(\{s=n\}\) would be contained
in that upper-tail event, contradicting (4.3).  Therefore

\[
        \mathbb Es>n-t_n.                                    \tag{4.5}
\]

It follows once more from the lower tail in (3.4) that

\[
        \Pr(s<n-2t_n)\leq(8q_n)^{-1}=o(1).                   \tag{4.6}
\]

This records all strict inequalities needed in the usual endpoint argument.
Using a mass merely \(\geq q_n^{-1}\) together with a tail merely
\(\leq q_n^{-1}\) would not by itself force (4.5); the strict quantile in
(4.1) and the slack factor eight avoid that nuisance.

## 5. Completing the concentration proof

On the event in (4.6), choose a maximizing \(W\) in (3.2) and put
\(U=[n]\setminus W\).  Then \(|U|\leq2t_n\).  Intersecting with the uniform
leftover event in Section 2, equations (2.1)--(2.2) and (3.1) give

\[
 T_n\leq h_n+\frac{2t_n}{c\log n}+n^{1/3}+1.                 \tag{5.1}
\]

Together with (4.2), this puts \(T_n\), with probability \(1-o(1)\), in the
deterministic interval

\[
 \left[h_n,
 h_n+\frac{2t_n}{c\log n}+n^{1/3}+1\right].                 \tag{5.2}
\]

Its length is \(o(\omega_n\sqrt n/\log n)\), since

\[
 \frac{t_n}{\omega_n\sqrt n}
   =O\!\left(\frac{\sqrt{\log\omega_n}}{\omega_n}\right)=o(1),
 \qquad
 \frac{(n^{1/3}+1)\log n}{\omega_n\sqrt n}=o(1).             \tag{5.3}
\]

Thus (5.2) may be enlarged, for every sufficiently large \(n\), to an
interval of length \(\omega_n\sqrt n/\log n\).  This proves the target claim
for all three parameters.

The original Scott presentation takes a coarser deviation
\(t\asymp\sqrt{\omega_n n}\), after harmlessly slowing \(\omega_n\); the
choice (4.4) simply uses the available subgaussian tail more efficiently.

## 6. Positive-probability gap plus stochastic domination

Let

\[
 C_n=\chi(G_1),\qquad Y_n=X(G_1,G_2),\qquad Z_n=\zeta(G),
\]

where \(G\) is a fresh single graph when discussing marginal laws.  Assume
there is a fixed \(p_0>0\) such that, for every sufficiently large \(n\),

\[
       \Pr(C_n-Y_n\geq a_n)\geq p_0,                         \tag{6.1}
\]

and

\[
       R_n:=\frac{a_n\log n}{\sqrt n}\longrightarrow\infty. \tag{6.2}
\]

Choose any \(\rho_n\to\infty\) with \(\rho_n=o(R_n)\), for example
\(\rho_n=\sqrt{R_n}\).  Applying the concentration result with \(\rho_n\)
gives deterministic intervals

\[
 I_n^C=[L_n^C,U_n^C],\qquad I_n^Y=[L_n^Y,U_n^Y]               \tag{6.3}
\]

such that each variable lies in its interval with probability \(1-o(1)\) and

\[
 |I_n^C|+|I_n^Y|=o(a_n).                                     \tag{6.4}
\]

No independence between \(C_n\) and \(Y_n\) is asserted or needed.  By the
union bound, their joint concentration event has probability \(1-o(1)\).
Together with (6.1), for large \(n\) the intersection of that event with
\(\{C_n-Y_n\geq a_n\}\) has probability at least \(p_0-o(1)>0\).  Hence it
is nonempty, forcing the deterministic endpoint inequality

\[
        U_n^C-L_n^Y\geq a_n.                                 \tag{6.5}
\]

Subtracting the two interval lengths yields

\[
 L_n^C-U_n^Y
 \geq a_n-|I_n^C|-|I_n^Y|
 =a_n-o(a_n).                                                 \tag{6.6}
\]

Now assume the marginal stochastic domination

\[
             Z_n\preceq_{\rm st}Y_n,                         \tag{6.7}
\]

meaning \(\Pr(Z_n>x)\leq\Pr(Y_n>x)\) for every real \(x\).  Since
\(\Pr(Y_n>U_n^Y)=o(1)\), (6.7) immediately gives
\(\Pr(Z_n>U_n^Y)=o(1)\).  Also \(\Pr(C_n<L_n^C)=o(1)\).
These two marginal statements hold jointly for \((\chi(G),\zeta(G))\) on the
same graph by a union bound; no coupling supplied by stochastic domination is
needed.  With high probability,

\[
 \chi(G)-\zeta(G)
 \geq L_n^C-U_n^Y
 \geq (1-o(1))a_n.                                           \tag{6.8}
\]

This proves the claimed consequence.  Notice that concentration of \(\zeta\)
is not used in Section 6; it is a separate true statement proved in Sections
2--5.

## 7. Quantifier and failure-mode audit

The following qualifications are essential.

* The lower bound in (6.1) must hold for every sufficiently large \(n\), with
  one fixed \(p_0>0\), to obtain an all-\(n\) whp conclusion.  A subsequence
  hypothesis gives only a subsequence conclusion.
* The scale condition (6.2) is exactly what permits deterministic
  concentration intervals of width \(o(a_n)\).  Merely
  \(a_n=O(\sqrt n/\log n)\) leaves the endpoint subtraction inconclusive.
* The domination direction must be \(\zeta\preceq_{\rm st}X\).  Reversing it
  supplies no upper-tail control on \(\zeta\).
* Stochastic domination is a statement about marginal tails.  One must not
  replace \(G\) by \(G_1\) inside an arbitrary domination coupling or claim a
  pointwise inequality \(\zeta(G_1)\leq X(G_1,G_2)\).
* The leftover \(U\) is random and selected from the entire input.  A lemma for
  each fixed \(U\), even with failure probability \(o(1)\), would not suffice;
  the simultaneous lemma of Section 2 is what closes the proof.
* For \(X\), changing the block for a vertex must bundle the coordinates from
  both graphs (or else use \(2(n-1)\) blocks).  Treating all edges of each
  graph as one block would not have Lipschitz constant one.
* In the endpoint argument, positive probability is used only to prove that
  two deterministic intervals are geometrically separated.  There is no
  unjustified amplification of the dependent event
  \(\{\chi(G_1)-X(G_1,G_2)\geq a_n\}\) itself.

## 8. Comparison with the existing extension note

After Sections 1--7 were written, I read
`research/proofs/ALON_CONCENTRATION_EXTENSION.md`.  Its conclusions and proof
architecture agree with the independent reconstruction.  I found no
counterexample and no substantive gap.

The correspondence is exact:

* its Lemma 1.1 is the simultaneous leftover event proved in Section 2 above;
* its \(S_T\) is the coverable-subset variable (3.2);
* it correctly bundles the two graphs' coordinates in one vertex block for
  \(X\), so the number of blocks is \(n-1\) and the oscillation is one;
* it correctly uses ordinary \(G_1\)-colouring for the \(X\)-leftover;
* its amplification proposition uses deterministic interval separation and
  the correct direction \(\zeta\preceq_{\rm st}X\).

There are two superficially different parameterizations of the same quantile
argument.  The existing note takes
\(\epsilon_n=e^{-\lambda_n}\) and
\(t_n^2=(n-1)(\lambda_n+1)/2\).  This gives an upper-tail bound
\(e^{-\lambda_n-1}<\epsilon_n\), so its use of
\(\Pr(S_T=n)\geq\epsilon_n\) is safe even in the equality case.  The
independent derivation instead takes \(q_n=\omega_n\) and uses
\(t_n^2=(n-1)\log(8q_n)/2\).  Formally these are the same calculation with
\(\lambda_n\) of order \(\log q_n\).

The restriction \(\lambda_n=o(\log^2 n)\) in the existing Theorem 2.1 is not
needed for the bounded-difference or leftover proof.  It is harmless, since
for any prescribed \(\omega_n\to\infty\) one can choose, for example, a
divergent \(\lambda_n\leq\min\{\omega_n,\log n\}\), which satisfies
\(\sqrt{\lambda_n}=o(\omega_n)\).  Removing the restriction would simplify
the quantitative statement but would not strengthen the stated
every-\(\omega\) conclusion.

The following clarifications would make the existing note maximally
audit-proof, though none repairs an error:

1. State explicitly that interval length means "at most" the displayed
   length; the interval can always be enlarged to the requested real length.
2. Record hereditary restriction and disjoint-set subadditivity before the
   \(S_T\) argument, as in Section 3 above.
3. In the amplification proof, say explicitly that the marginal lower event
   for \(\chi(G)\) and marginal upper event for \(\zeta(G)\) are intersected
   on the same fresh graph by a union bound, not via the stochastic-domination
   coupling.
4. Note that \(\zeta\)-concentration, although true, is not needed for the
   amplification proposition.

## 9. Counterexample search summary

Several tempting variants do fail, which helps delimit the proved statement.

* If the success probability in (6.1) is \(p_n=o(1)\), the gap event may lie
  entirely in the exceptional complement of the two concentration intervals;
  no endpoint separation follows.  A toy example is a variable equal to
  \(a_n\) with probability \(p_n\) and zero otherwise, paired against zero.
* If the two deterministic window lengths are only \(O(a_n)\), (6.5) can be
  exhausted by opposite endpoints and (6.6) need not retain a
  \((1-o(1))a_n\) gap.
* A fixed-set leftover lemma cannot be substituted for the uniform lemma:
  there are exponentially many possible maximizing leftovers, and the chosen
  one depends on the exposed graph(s).
* A pointwise assertion \(\zeta(G_1)\leq X(G_1,G_2)\) is false in general (for
  example, an empty \(G_2\) makes \(X=1\) regardless of \(G_1\)).  Only the
  proved marginal stochastic domination may be used.
* Bundling all of \(G_1\) into one block and all of \(G_2\) into another does
  not have oscillation one.  The valid blocks are vertex fibres.

None of these failure modes occurs in
`research/proofs/ALON_CONCENTRATION_EXTENSION.md`.

## 10. Final audited statements

For every deterministic \(\omega_n\to\infty\), each of

\[
 \chi(G(n,1/2)),\qquad \zeta(G(n,1/2)),\qquad
 X(G_1,G_2)
\]

lies with high probability in a deterministic interval of length at most
\(\omega_n\sqrt n/\log n\).

Moreover, if a fixed \(p_0>0\) and a positive sequence \(a_n\) satisfy, for
all sufficiently large \(n\),

\[
 \Pr\bigl(\chi(G_1)-X(G_1,G_2)\geq a_n\bigr)\geq p_0,
 \qquad
 \frac{a_n\log n}{\sqrt n}\to\infty,
\]

then the stochastic domination \(\zeta\preceq_{\rm st}X\) implies

\[
 \Pr\bigl(\chi(G)-\zeta(G)\geq(1-o(1))a_n\bigr)\to1.
\]

The \(o(1)\) in the threshold is deterministic; explicitly one may take
\(a_n-w_n^\chi-w_n^X\), where the two deterministic interval widths are
chosen to have sum \(o(a_n)\).
