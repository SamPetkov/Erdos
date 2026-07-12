# Second independent coupling audit for Erdos Problem #625

**Verdict.** For every finite `n >= 1` and every integer `k`, the proposed
inequality is true:

\[
 \boxed{\Pr\{X(G_1,G_2)\le k\}\le
        \Pr\{\zeta(G)\le k\}.}
 \tag{0.1}
\]

Equivalently,

\[
 \zeta(G(n,1/2))\preceq_{\rm st}X(G_1,G_2).
\]

The proof below is a conditional Boolean-event/four-state interpolation.  It
does not construct or follow an optimal partition and does not require an
adaptive coupling of the minimum values.  The decisive structural fact is
that a labelled partition certificate can ask for **at most one** of the two
absence bits over any edge.

There is also a valid deterministic-interval amplification.  If `chi` and
`X` lie whp in deterministic intervals of respective widths
`w_chi(n), w_X(n)`, and for some fixed `p>0`

\[
 \Pr\{\chi(G_1)-X(G_1,G_2)\ge a_n\}\ge p
 \tag{0.2}
\]

for every sufficiently large `n`, then

\[
 \Pr\{\chi(G)-\zeta(G)
       \ge a_n-w_\chi(n)-w_X(n)\}\longrightarrow1.
 \tag{0.3}
\]

In particular, if the two widths are `o(a_n)`, the whp lower bound is
`(1-o(1))a_n`.  No independence between `chi(G_1)` and `X` is asserted or
needed.

Sections 1--6 were reconstructed before opening the existing coupling notes.
Section 7 records the after-the-fact comparison.

---

## 1. Definitions and certificate convention

Let

\[
 E_n=\binom{[n]}2,
 \qquad
 A_e={\bf1}_{\{e\in G_1\}},
 \qquad
 B_e={\bf1}_{\{e\in G_2\}}.
\]

Initially the fibres `(A_e,B_e)`, `e in E_n`, are mutually independent and
uniform on

\[
 \{00,01,10,11\}.
\]

A **labelled partition certificate** is a set partition `P` of `[n]` into
nonempty parts, together with a label

\[
 \sigma(C)\in\{1,2\}
\]

for every part `C`.  It is valid when

\[
 \begin{cases}
  A_e=0&\text{for every }e\in\binom C2,
          \quad\text{if }\sigma(C)=1,\\
  B_e=0&\text{for every }e\in\binom C2,
          \quad\text{if }\sigma(C)=2.
 \end{cases}
 \tag{1.1}
\]

Thus `X <= k` exactly when some valid labelled certificate has at most `k`
parts.  Labelling causes no change to the definition of `X`: every allowed
part has at least one valid label, and choosing one such label for each part
gives a certificate.

### Singleton convention

A singleton has no internal edge, so both labels are valid.  These two labels
are duplicate witnesses for an existence event and do not change the minimum.
One may equivalently leave singleton parts unlabelled.  Empty parts are not
used; the event is formulated with an actual set partition into at most `k`
nonempty parts.

Most importantly, for a fixed edge `e=uv`:

- if `u,v` are in different certificate parts, the certificate asks for no
  bit over `e`;
- if `u,v` are in the same part, that part has size at least two and its one
  chosen label asks for exactly one of `A_e=0` or `B_e=0`.

No certificate ever asks for both conditions over the same edge.  Singleton
duplication therefore cannot invalidate the one-fibre argument below.

---

## 2. The conditional Boolean slice

Fix an integer `k`, an edge `e`, and all fibres except the fibre over `e`.
For `a,b in {0,1}`, let

\[
 f_{ab}={\bf1}_{\{X\le k\}}
\]

when `(A_e,B_e)=(a,b)` and the outside configuration is held fixed.

Discard every labelled certificate whose requirements on the frozen outside
bits already fail.  Among the remaining certificates, let

\[
 c_0={\bf1}_{\{\text{some certificate does not use }e\}},
\]

and, for `i=1,2`, let

\[
 c_i={\bf1}_{\{\text{some certificate uses }e
                   \text{ with label }i\}}.
\]

The one-bit-per-fibre property gives the exact formula

\[
 f(a,b)=
 c_0\ \vee\ \bigl(c_1\wedge[a=0]\bigr)
     \ \vee\ \bigl(c_2\wedge[b=0]\bigr).
 \tag{2.1}
\]

Consequently the Boolean slice is one of only five functions:

\[
 0,\qquad 1,\qquad [a=0],\qquad [b=0],\qquad
 [a=0]\vee[b=0].
 \tag{2.2}
\]

In particular,

\[
 f_{01}+f_{10}\ge f_{00}+f_{11}.
 \tag{2.3}
\]

Equivalently, one may record the two witness relations

\[
 f_{00}=f_{01}\vee f_{10},
 \qquad
 f_{11}\le f_{01}\wedge f_{10},
 \tag{2.4}
\]

from which (2.3) follows.  The inequality is strict precisely in the slice
where viable certificates of both edge labels exist but no viable certificate
avoids `e`.

Monotonicity by itself would not prove (2.3): the decreasing Boolean function
`[a=0] and [b=0]` has the opposite four-state inequality.  Formula (2.1),
which excludes that function, is the required certificate input.

---

## 3. Four-state interpolation and stochastic domination

Let `nu_0` be the uniform law on all four states and `nu_1` the uniform law on
the two off-diagonal states:

\[
 \nu_0(00)=\nu_0(01)=\nu_0(10)=\nu_0(11)=\frac14,
\]

\[
 \nu_1(01)=\nu_1(10)=\frac12,
 \qquad
 \nu_1(00)=\nu_1(11)=0.
\]

For every frozen outside configuration, (2.3) gives

\[
 \begin{aligned}
 \mathbb E_{\nu_1}f-\mathbb E_{\nu_0}f
 &=\frac{f_{01}+f_{10}}2
   -\frac{f_{00}+f_{01}+f_{10}+f_{11}}4\\
 &=\frac{f_{01}+f_{10}-f_{00}-f_{11}}4\ge0.
 \end{aligned}
 \tag{3.1}
\]

Enumerate the `N=binom(n,2)` edges.  Let `P_j` be the product law in which
the first `j` fibres have law `nu_1` and the remaining fibres have law `nu_0`.
Conditioning on all fibres except the `j`th and applying (3.1) shows

\[
 \mathbb P_j\{X\le k\}
 \ge \mathbb P_{j-1}\{X\le k\}.
 \tag{3.2}
\]

Telescoping over all fibres yields

\[
 \mathbb P_0\{X\le k\}
 \le \mathbb P_N\{X\le k\}.
 \tag{3.3}
\]

Under `P_0`, the two graphs are independent copies of `G(n,1/2)`, so the
left side is the desired original probability.  Under `P_N`, independently
for every edge,

\[
 B_e=1-A_e,
\]

and the `A_e` are independent fair bits.  Hence the endpoint pair is exactly

\[
 (H,\overline H),\qquad H\sim G(n,1/2).
\]

A part independent in `H` is an independent-set part of `H`, while a part
independent in `bar H` is a clique part of `H`.  Therefore, deterministically,

\[
 X(H,\overline H)=\zeta(H).
 \tag{3.4}
\]

Combining (3.3) and (3.4) proves (0.1) for every finite `n` and every integer
`k`.

### Continuous form

The same interpolation can be parametrized by

\[
 \nu_t(00)=\nu_t(11)=\frac{1-t}{4},
 \qquad
 \nu_t(01)=\nu_t(10)=\frac{1+t}{4},
 \qquad 0\le t\le1.
 \tag{3.5}
\]

Both coordinate marginals remain fair for every `t`, and for a frozen outside
configuration

\[
 \mathbb E_{\nu_t}f
 =\mathbb E_{\nu_0}f
   +\frac t4(f_{01}+f_{10}-f_{00}-f_{11})
\]

is nondecreasing.  Coordinate telescoping again proves monotonicity for the
product law.  At intermediate `t`, each graph separately still has law
`G(n,1/2)`, although the two graphs are no longer independent.  Only `t=0`
is used for the original two-independent-graph model.

---

## 4. Direction and adaptive-law audit

The direction is fixed by (3.1): moving from four equally likely fibre states
to the anti-correlated states `01,10` makes the lower-tail event `X <= k`
**more** likely.  Thus the endpoint value `zeta` is stochastically smaller:

\[
 F_X(k)\le F_\zeta(k),
 \qquad
 \zeta\preceq_{\rm st}X.
\]

This proof has no adaptive sampling step.  Every hybrid law `P_j` is declared
in advance as an explicit product law.  The optimum partition may depend on
all edge states, but after the outside fibres are frozen its entire adaptive
effect is already represented by the deterministic Boolean slice (2.1).
There is therefore no risk that choosing an optimizer biases an unprocessed
fibre.

For comparison, an adaptive pathwise value coupling can also be valid, but it
must choose its local map using **only** the outside configuration.  Conditional
on that outside, the current fibre is still uniform and independent; if the
map has two preimages for each of `01` and `10`, its output is conditionally a
fair exactly-one fibre.  An induction then preserves the hybrid product law.
A rule that inspected the current fibre when selecting between the two maps,
or selected a global optimizer without first freezing the outside, would not
have this justification.

The Boolean argument proves the distributional inequality directly.  It does
not claim the false pointwise inequality

\[
 \zeta(G_1)\le X(G_1,G_2).
\]

Indeed, taking `G_2` empty gives `X=1`, while `zeta(G_1)` can exceed one.

---

## 5. Deterministic-interval amplification

Here is the exact abstract form needed for the all-large-`n` reduction.

### Proposition 5.1

Suppose there are deterministic intervals

\[
 I_\chi=[\ell_\chi,u_\chi],
 \qquad
 I_X=[\ell_X,u_X]
 \tag{5.1}
\]

such that

\[
 \Pr\{\chi(G_1)\in I_\chi\}=1-o(1),
 \qquad
 \Pr\{X(G_1,G_2)\in I_X\}=1-o(1).
 \tag{5.2}
\]

Write

\[
 w_\chi=u_\chi-\ell_\chi,
 \qquad
 w_X=u_X-\ell_X.
\]

If for a fixed `p>0` and every sufficiently large `n`,

\[
 \Pr\{\chi(G_1)-X(G_1,G_2)\ge a_n\}\ge p,
 \tag{5.3}
\]

then

\[
 \Pr\{\chi(G)-\zeta(G)
        \ge a_n-w_\chi-w_X\}=1-o(1).
 \tag{5.4}
\]

#### Proof

The two events in (5.2) occur jointly with probability `1-o(1)` by the union
bound; no independence is required.  Since `p` is fixed, this joint typical
event intersects the event in (5.3) for every sufficiently large `n`.  On an
outcome in the intersection,

\[
 a_n\le\chi(G_1)-X(G_1,G_2)\le u_\chi-\ell_X.
\]

The endpoints are deterministic, so

\[
 u_\chi-\ell_X\ge a_n.
 \tag{5.5}
\]

Stochastic domination at the deterministic upper endpoint of `I_X` gives

\[
 \Pr\{\zeta(G)\le u_X\}
 \ge \Pr\{X(G_1,G_2)\le u_X\}=1-o(1).
 \tag{5.6}
\]

Also `Pr{chi(G) >= ell_chi}=1-o(1)`.  These two marginal events may be
intersected for the same fresh graph `G` by another union bound.  On their
intersection,

\[
 \begin{aligned}
 \chi(G)-\zeta(G)
 &\ge \ell_\chi-u_X\\
 &=(u_\chi-\ell_X)-w_\chi-w_X\\
 &\ge a_n-w_\chi-w_X,
 \end{aligned}
\]

which proves (5.4).  If an endpoint is nonintegral, replace it by the
appropriate floor or ceiling; the variables are integer-valued.  \(\square\)

### Consequence at the available concentration scale

If the deterministic whp intervals for both `chi` and `X` have width at most

\[
 w_n=\omega(n)\frac{\sqrt n}{\log n}
\]

for every prescribed slowly diverging `omega(n)`, then the condition

\[
 a_n\frac{\log n}{\sqrt n}\longrightarrow\infty
\]

allows `omega` to be chosen slowly enough that `w_n=o(a_n)`.  Proposition 5.1
then gives

\[
 \chi(G)-\zeta(G)\ge(1-o(1))a_n
 \qquad\text{whp}.
 \tag{5.7}
\]

### Variant using `chi` and `zeta` intervals

If one has deterministic whp intervals for `chi` and `zeta`, rather than for
`chi` and `X`, the same width-loss conclusion follows by a lower-tail anchor.
Indeed, on the gap event together with `chi(G_1)<=u_chi`,

\[
 X\le u_\chi-a_n
\]

with probability at least `p-o(1)`.  Domination gives the same fixed-positive
lower bound for

\[
 \Pr\{\zeta\le u_\chi-a_n\}.
\]

If the deterministic `zeta` interval is `[ell_zeta,u_zeta]` and its failure
probability is `o(1)`, this forces

\[
 \ell_\zeta\le u_\chi-a_n
\]

eventually; otherwise the displayed lower-tail probability would be `o(1)`.
It follows whp that

\[
 \chi-\zeta\ge a_n-w_\chi-w_\zeta.
\]

The `chi`/`X` version is cleaner here because domination transfers the whp
upper endpoint of `X` directly to `zeta`.

### Logical requirements

1. The success probability in (5.3) must dominate the concentration failure
   probability.  A fixed `p>0` is more than enough.  If `p=p_n->0`, one needs
   the stronger quantitative hypothesis that the interval failures are
   `o(p_n)`.
2. The interval endpoints must be deterministic.  A merely sample-dependent
   interval does not let the existence of one joint outcome force (5.5).
3. The premise must hold for every sufficiently large `n` to obtain an
   all-large-`n` conclusion.  A subsequence premise gives only a subsequence
   conclusion.
4. A useful positive lower bound requires `a_n>w_chi+w_X`; the formal bound is
   otherwise valid but vacuous.
5. Stochastic domination transfers a one-variable lower tail.  It does not
   compare `chi(G_1)-X` pathwise with `chi(G)-zeta(G)`.  The deterministic
   interval endpoints are what bridge the two gaps.

---

## 6. Edge cases and finite checks

### `n=1`

There are no edge fibres.  The unique vertex is a singleton part, so

\[
 X=\zeta=1
\]

deterministically.  Thus both lower-tail probabilities are zero for `k<=0`
and one for `k>=1`.  The interpolation has zero steps and (0.1) is equality.
A positive-gap amplification premise with `a_n>0` cannot hold at this `n`.

### `n=2`

Let `A,B` be the two edge indicators.  A one-part `X`-certificate exists iff
at least one graph omits the edge, so

\[
 X=1+AB,
 \qquad
 \Pr\{X\le1\}=\frac34.
\]

Every graph on two vertices is itself either a clique or an independent set,
so

\[
 \zeta=1,
 \qquad
 \Pr\{\zeta\le1\}=1.
\]

For `k<=0` both probabilities are zero, for `k=1` the inequality is strict,
and for `k>=2` both are one.  This is the smallest case and decisively fixes
the stochastic direction.

As a separate sanity check, exhaustive direct enumeration performed before
reading the existing audit gave the following CDFs:

| `n` | `P(X<=k)`, `k=0,...,n` | `P(zeta<=k)`, `k=0,...,n` |
|---:|---|---|
| 1 | `(0,1)` | `(0,1)` |
| 2 | `(0,3/4,1)` | `(0,1,1)` |
| 3 | `(0,15/64,63/64,1)` | `(0,1/4,1,1)` |
| 4 | `(0,127/4096,3813/4096,4095/4096,1)` | `(0,1/32,1,1,1)` |

Every listed threshold agrees with (0.1).

---

## 7. After-the-fact comparison with the existing notes

After completing the reconstruction above, I read
`research/proofs/TWO_GRAPH_MODEL.md`,
`research/audits/COUPLING_AUDIT_1.md`, and the amplification section of
`research/proofs/ALON_CONCENTRATION_EXTENSION.md`.

There is no substantive discrepancy.

1. **Boolean interpolation.**  `TWO_GRAPH_MODEL.md` contains a short
   probability-only verification in absence-bit ("good-bit") notation.  Its
   identities are the complement-bit version of (2.4), and its four-state
   difference is exactly (3.1).  The present reconstruction makes the slice
   exhaustive via the five-function classification (2.2) and tensors the
   conditional inequality through explicit hybrid product laws.
2. **Value coupling.**  The main proof in `TWO_GRAPH_MODEL.md` and the reverse
   construction in `COUPLING_AUDIT_1.md` build adaptive pathwise couplings of
   the minimum values.  Their adaptive law is preserved: the choice of local
   table depends only on the frozen outside, and each table gives the required
   conditional fibre law.  This agrees with the audit in Section 4.  The
   fixed-law Boolean interpolation is distributional and does not contradict
   the notes' statement that a fixed edgewise map is insufficient for a
   simultaneous pathwise value coupling.
3. **Singletons.**  `TWO_GRAPH_MODEL.md` explicitly notes that a singleton has
   two labels but requires no good bits.  That agrees with Section 1: duplicate
   singleton labels matter for signed certificate counts, not for the
   existence event or the minimum.
4. **Direction and finite cases.**  Both existing notes state
   `P(X<=k)<=P(zeta<=k)`.  Their exact `n<=4` counts reproduce the independently
   computed CDF table in Section 6.  In particular, the strict `n=2`, `k=1`
   inequality rules out a reversed stochastic order.
5. **Deterministic-interval transfer.**  Proposition 3.1 of
   `ALON_CONCENTRATION_EXTENSION.md` is exactly Proposition 5.1 above: intersect
   the positive-probability gap with the joint `chi`/`X` typical event to force
   deterministic endpoint separation, transfer the upper endpoint of `X` to
   `zeta`, and lose the sum of the two interval widths.  Its use of dependence
   and quantifiers is correct.
6. **Relation to the older amplification.**  `COUPLING_AUDIT_1.md` and
   `TWO_GRAPH_MODEL.md` also give an expectation-plus-bounded-differences
   transfer, which needs a surrogate gap larger than the `sqrt(n)` scale.  The
   deterministic-interval argument is sharper when intervals of width
   `omega sqrt(n)/log n` are available.  The two arguments are compatible and
   serve different quantitative regimes.

The complete coupling lemma and the deterministic-interval reduction are
therefore validated.  The remaining mathematical burden for Problem #625 is
not this transfer step, but proving the required fixed-positive-probability
surrogate separation uniformly through all sufficiently large `n`.
