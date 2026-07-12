# Independent coupling audit for Erdos Problem #625

**Verdict.** All three proposed claims are correct. The concentration and
amplification formulas require \(n\ge 2\). The exact stochastic direction is

\[
\zeta(G)\preceq_{\mathrm{st}}X(G_1,G_2),
\qquad
\Pr(X\le k)\le \Pr(\zeta\le k).
\]

I derived Sections 1--5 before opening
**research/proofs/TWO_GRAPH_MODEL.md**. Section 6 gives the requested
after-the-fact comparison.

## 1. Conventions and deterministic facts

For an edge \(e\), write its fibre as

\[
(a,b)=\left(\mathbf 1_{\{e\in G_1\}},
                 \mathbf 1_{\{e\in G_2\}}\right).
\]

Thus \(00\) imposes neither possible independence obstruction at \(e\), while
\(11\) imposes both. A certified partition is a set partition whose every part
has a chosen label \(i\in\{1,2\}\) and is independent in \(G_i\). Choosing one
valid label for every part does not change the minimum.

For any vertex \(v\),

\[
\begin{aligned}
X((G_1,G_2)-v)&\le X(G_1,G_2)\le X((G_1,G_2)-v)+1,\\
\chi(G-v)&\le\chi(G)\le\chi(G-v)+1,\\
\zeta(G-v)&\le\zeta(G)\le\zeta(G-v)+1.
\end{aligned}                                                   \tag{1.1}
\]

Restriction proves the lower bounds, and adding \(v\) as a singleton proves
the upper bounds. Also,

\[
X(G_1,G_2)\le \chi(G_1),                                      \tag{1.2}
\]

because one may use only colour classes of \(G_1\).

## 2. Explicit edge-fibre coupling

### 2.1 One-fibre lemma

Fix all fibres except one edge \(e=uv\), and let \(x_{ab}\) be the resulting
value of \(X\) in state \(ab\). Then

\[
x_{00}=\min\{x_{01},x_{10}\},
\qquad
x_{11}\ge\max\{x_{01},x_{10}\}.                              \tag{2.1}
\]

Monotonicity gives \(x_{00}\le\min(x_{01},x_{10})\) and the second relation.
For the remaining inequality, take an optimal certificate in state \(00\).

- If \(u,v\) lie in different parts, the same certificate survives in both
  mixed states.
- If they lie in the same part, that part is certified in at least one graph.
  A \(G_1\)-certificate survives in state \(01\); a \(G_2\)-certificate
  survives in state \(10\).

Thus at least one mixed state still has a certificate with \(x_{00}\) parts.
This witness step, not monotonicity alone, is the key point.

### 2.2 Local coupling map

Conditional on the outside fibres, choose
\(s_0\in\{01,10\}\) with \(x_{s_0}=x_{00}\), breaking ties
deterministically, and let \(s_1\) be the other mixed state. Map

\[
00\mapsto s_0,\qquad
11\mapsto s_1,\qquad
01\mapsto01,\qquad
10\mapsto10.                                                  \tag{2.2}
\]

If the input is uniform on the four states, the output is uniform on
\(\{01,10\}\), since each output has exactly two preimages. Moreover \(X\)
never increases: the \(00\) row is equality by the choice of \(s_0\); the
mixed rows are fixed; and \(x_{s_1}\le x_{11}\) for the \(11\) row.

Although the choice of \(s_0\) is adaptive, it depends only on the outside
configuration. Hence, conditional on the outside, the output remains a fair
exactly-one state and is independent of the outside.

### 2.3 Iteration and endpoint laws

Start with independent \(G_1,G_2\sim G(n,1/2)\), so every fibre is uniform on
the four states. Process the edges in a fixed order using (2.2). Inductively,
processed fibres are mutually independent fair exactly-one fibres,
unprocessed fibres remain mutually independent fair four-state fibres, and
\(X\) is nonincreasing along every sample path.

At the endpoint, every fibre is independently \(01\) or \(10\). Therefore the
endpoint pair has the exact law

\[
(H,\overline H),\qquad H\sim G(n,1/2).                        \tag{2.3}
\]

A set independent in \(\overline H\) is a clique in \(H\), so

\[
X(H,\overline H)=\zeta(H).                                    \tag{2.4}
\]

The coupling therefore gives

\[
\boxed{\zeta(H)\le X(G_1,G_2)\quad\text{almost surely}}        \tag{2.5}
\]

with the required endpoint marginals and with \(G_1,G_2\) independent.
Equivalently,

\[
\boxed{\zeta(G(n,1/2))\preceq_{\mathrm{st}}X(G_1,G_2)},
\qquad
\Pr(X\le k)\le\Pr(\zeta\le k).                                \tag{2.6}
\]

The endpoint \(H\) is generally dependent on the input pair. Equation (2.5)
does not permit setting \(H=G_1\).

## 3. Vertex-block concentration constants

Use the \(n-1\) independent vector blocks

\[
\mathcal B_i=\{\{i,j\}:j>i\},\qquad 1\le i\le n-1.             \tag{3.1}
\]

For \(X\), each block contains the corresponding indicators from both graphs.
Changing it alters only edges incident with \(i\), so (1.1) gives the exact
general oscillation bound

\[
c_i(X)=1.                                                      \tag{3.2}
\]

McDiarmid's inequality gives, for \(n\ge2\) and \(t\ge0\),

\[
\Pr(X-\mathbb EX\ge t),\ \Pr(X-\mathbb EX\le-t)
\le \exp\left(-\frac{2t^2}{n-1}\right),                       \tag{3.3}
\]

and hence

\[
\Pr(|X-\mathbb EX|\ge t)
\le2\exp\left(-\frac{2t^2}{n-1}\right).                       \tag{3.4}
\]

For

\[
Y(G)=\chi(G)-\zeta(G),
\]

both summands have block oscillation at most one, so

\[
c_i(Y)=2.                                                      \tag{3.5}
\]

Consequently,

\[
\Pr(Y-\mathbb EY\ge t),\ \Pr(Y-\mathbb EY\le-t)
\le \exp\left(-\frac{t^2}{2(n-1)}\right),                     \tag{3.6}
\]

and

\[
\Pr(|Y-\mathbb EY|\ge t)
\le2\exp\left(-\frac{t^2}{2(n-1)}\right).                     \tag{3.7}
\]

Both constants are sharp as deterministic block oscillation bounds.

- For \(X\), on two vertices, changing the sole two-graph block from \(00\)
  to \(11\) changes \(X\) from \(1\) to \(2\).
- For \(Y\), fix edge \(23\) and change only the star at vertex \(1\).
  For \(K_2\sqcup K_1\), \((\chi,\zeta,Y)=(2,2,0)\); for \(K_3\),
  \((\chi,\zeta,Y)=(3,1,2)\). One block can therefore change \(Y\) by two.

For \(n=1\), \(X=\chi=\zeta=1\) and \(Y=0\) deterministically; formulas with
denominator \(n-1\) should be replaced by this exact statement.

## 4. Positive-probability amplification

Assume \(n\ge2\), \(a>0\), \(p\in(0,1]\), and

\[
\Pr\bigl(\chi(G_1)-X(G_1,G_2)\ge a\bigr)\ge p.                \tag{4.1}
\]

Let \(D=\chi(G_1)-X(G_1,G_2)\). By (1.2), \(D\ge0\) pointwise, so

\[
\mathbb ED\ge a\Pr(D\ge a)\ge pa.                             \tag{4.2}
\]

Stochastic domination (2.6) gives \(\mathbb E\zeta\le\mathbb EX\). Since
\(G\) and \(G_1\) have the same marginal law,

\[
\begin{aligned}
\mathbb E[\chi(G)-\zeta(G)]
&=\mathbb E\chi-\mathbb E\zeta\\
&\ge\mathbb E\chi-\mathbb EX\\
&=\mathbb E[\chi(G_1)-X]\ge pa.                               \tag{4.3}
\end{aligned}
\]

Apply (3.6) to a fresh \(G\sim G(n,1/2)\). The event \(Y<pa/2\) lies at least
\(pa/2\) below \(\mathbb EY\), whence

\[
\Pr\left(Y<\frac{pa}{2}\right)
\le\exp\left(-\frac{(pa)^2}{8(n-1)}\right).                   \tag{4.4}
\]

Equivalently,

\[
\boxed{
\Pr\left(\chi(G)-\zeta(G)\ge\frac{pa}{2}\right)
\ge1-\exp\left(-\frac{(pa)^2}{8(n-1)}\right).}                \tag{4.5}
\]

This is an expectation transfer followed by fresh-graph concentration. It
does not use independence between \(\chi(G_1)\) and \(X\), and it does not
assert a pathwise comparison between the two gap variables.

## 5. Edge cases, small \(n\), and dependence

### 5.1 Exact enumeration

Exhaustive enumeration gives the following counts. Denominators are
\(2^{\binom n2}\) for \(\zeta\) and \(2^{2\binom n2}\) for \(X\).

| \(n\) | counts for \(\zeta\) | counts for \(X\) |
|---:|---|---|
| 1 | \(\{1:1\}\) | \(\{1:1\}\) |
| 2 | \(\{1:2\}\) | \(\{1:3,2:1\}\) |
| 3 | \(\{1:2,2:6\}\) | \(\{1:15,2:48,3:1\}\) |
| 4 | \(\{1:2,2:62\}\) | \(\{1:127,2:3686,3:282,4:1\}\) |

For \(n=2\), \(\zeta=1\) surely while \(\Pr(X=2)=1/4\), decisively fixing the
stochastic direction. Every lower-tail inequality in (2.6) holds in the
displayed cases.

The gap laws are not the same. At \(n=3\), over the \(64\) ordered input pairs,

\[
\#\{\chi(G_1)-X=0,1,2\}=(51,12,1),                            \tag{5.1}
\]

whereas over the \(8\) single graphs,

\[
\#\{\chi(G)-\zeta(G)=0,2\}=(7,1).                             \tag{5.2}
\]

### 5.2 Invalid pathwise transfers

Take \(G_2\) empty and \(G_1=K_2\sqcup K_1\). Then

\[
X(G_1,G_2)=1,\qquad \zeta(G_1)=2,
\]

so \(\zeta(G_1)\le X(G_1,G_2)\) is false. Moreover,

\[
\chi(G_1)-X=1>0=\chi(G_1)-\zeta(G_1).                         \tag{5.3}
\]

This shows concretely why the coupling graph cannot be retained as \(G_1\)
inside the amplification argument.

The variables \(\chi(G_1)\) and \(X\) are also not independent. For \(n=2\),
with edge indicators \(A,B\),

\[
\chi(G_1)=1+A,\qquad X=1+AB,\qquad
\operatorname{Cov}(\chi(G_1),X)=\frac18.                     \tag{5.4}
\]

Nonnegativity of \(D\), not independence, validates (4.2).

### 5.3 The \(n=1\) endpoint

At \(n=1\), \(D=Y=0\). A premise with \(a,p>0\) is impossible, so the
amplification implication is vacuous; its exponential formula is not
literally defined because \(n-1=0\). If \(a=0\), the probability statement is
trivial but should still not be written with the zero denominator.

## 6. Comparison with TWO_GRAPH_MODEL.md

After completing Sections 1--5, I read the existing proof note. There is no
substantive discrepancy.

1. **Coupling.** The note uses good bits (certificate/absence indicators) and
   runs from exactly-one fibres to independent fibres, making \(X\)
   nondecreasing. The reconstruction above uses edge-present bits and runs the
   same local table in reverse, from independent fibres to exactly-one fibres,
   making \(X\) nonincreasing. Endpoint laws and stochastic direction agree.
2. **Concentration.** Both derivations give block oscillation \(1\) for \(X\)
   and \(2\) for \(\chi-\zeta\), hence the same exponents.
3. **Amplification.** Both use
   \[
   \mathbb E(\chi-\zeta)\ge
   \mathbb E(\chi(G_1)-X)\ge pa
   \]
   and then the lower-tail bound with \(t=pa/2\). Neither assumes independence
   of \(\chi(G_1)\) and \(X\).
4. **Finite checks.** The exact \(n=2,3,4\) distributions agree.
5. **Minor presentation caveat.** The note states its concentration theorem
   for \(n\ge2\), but its headline amplification display does not repeat that
   restriction. The formula should be read with \(n\ge2\). This has no
   asymptotic consequence.

Thus the audit finds proofs, not counterexamples, for claims (i)--(iii). The
main logical hazard is attempting to retain \(G=G_1\) inside the adaptive
coupling; the expectation step (4.3) is the correct way around that dependence
obstruction.
