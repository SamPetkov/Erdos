# Erdős Problem 625 after the 12 July candidate proof

## A theorem-level program for a stronger main paper and substantive follow-up results

**Date:** 26 July 2026  
**Repository:** `SamPetkov/Erdos`  
**Stack base:** PR #41, `agent/625-section8-decorated-reference-quotient`  
**Scope:** chronology, current proof frontier, stronger consequences of the existing architecture, and mathematically precise next-result programs

---

## 0. Status convention

This note deliberately separates four statuses.

- **Kernel-checked finite theorem:** accepted by Lean in the public repository without `sorry`, `admit`, or a project-defined axiom.
- **Conditional corollary:** follows from the candidate proof once the remaining normalized-second-moment bridge is closed.
- **New theorem target:** a precise statement with a proposed proof route, but not yet established.
- **Exploratory program:** a plausible separate-paper direction whose final theorem is not yet fixed.

No item labelled conditional or new is presented as already proved.

---

## 1. Public chronology and claim scope

### 1.1 Public timestamp of the candidate proof

The candidate proof was publicly recorded on GitHub on **12 July 2026**.
PR #1,

> `Add verification report and publication bundle for Problem 625`,

was created at `2026-07-12 19:08:31 UTC` and merged at
`2026-07-12 19:29:28 UTC`. Its public head commit was

```text
945ed733af198fe8698e14079ddc079f2bc554d7
```

and its merge commit was

```text
7d0cba893b7cdc707102380c52e22359b867eb5e.
```

The PR explicitly described the verdict as

```text
Provisional internal verification: PASS
```

and explicitly did **not** describe it as external verification, peer review,
formal verification, publication, or community acceptance.

Accordingly, the accurate chronology is:

1. candidate proof publicly deposited on 12 July 2026;
2. no official solution claim made on the Erdős Problems page while awaiting external assessment;
3. later PRs devoted to adversarial audit, simplification, formalization,
   coefficient strengthening, and new consequences.

The July 12 public record establishes a public chronology. It does not rule out
unpublished independent work by other researchers.

### 1.2 Current external status

As of 26 July 2026, the Erdős Problems page still marks Problem 625 as open and
lists no claimed complete or partial solution in its comments:

- <https://www.erdosproblems.com/625>
- <https://www.erdosproblems.com/forum/thread/625>

The closest published/public results remain:

- A. Heckel, *On a question of Erdős and Gimbel on the cochromatic number*,
  Electron. J. Combin. 31 (2024), P4.72, arXiv:2408.13839;
- A. Heckel, *The difference between the chromatic and the cochromatic number
  of a random graph*, arXiv:2409.17614, proving a positive answer for roughly
  95% of integers `n`;
- R. Steiner, *On the Difference Between the Chromatic and Cochromatic Number*,
  SIAM J. Discrete Math. 39 (2025), 2268--2274.

A targeted search through 26 July 2026 did not find an indexed paper claiming
the same full-sequence high-probability lower bound of order
`n/(log n)^3`. This is a literature-search statement, not a guarantee about
unpublished or unindexed work.

### 1.3 Recommended attribution language

Until an external expert has checked the proof, the repository and any message
to Thomas Bloom should use language of the following form:

> A candidate full-sequence proof was publicly deposited on GitHub on 12 July
> 2026. The proof has since undergone extensive computational, formal, and
> theorem-by-theorem internal auditing. External verification is still being
> sought, and no claim of community acceptance is made.

This preserves both priority chronology and mathematical caution.

---

## 2. Notation and the candidate theorem

Let

```text
q = ln 2,
N = ln n,
H_n = n/N^3.
```

For `G_n ~ G(n,1/2)`, let `chi(G_n)` be the chromatic number and
`zeta(G_n)` the cochromatic number.

The canonical candidate manuscript proves, conditional on the remaining
Section VIII--IX closure,

\[
 \Pr\!\left(
   \chi(G_n)-\zeta(G_n)
   \ge
   \frac{q^2}{32}\log\!\left(\frac{200}{153}\right)H_n
 \right)\longrightarrow1.
\]

The displayed coefficient is

\[
 c_{\mathrm{canonical}}
 =\frac{q^2}{32}\log\!\left(\frac{200}{153}\right)
 =0.004021983962242\ldots.
\]

The proof architecture is:

1. phase-resolved first moment for ordinary independent-set partitions;
2. signed four-size first moment for cocolorings;
3. exact signed overlap/cycle-space identity;
4. partial-diagonal control;
5. canonical high-skeleton endpoint and residual analysis;
6. normalized second moment and Paley--Zygmund rare seed;
7. rare-seed-to-typical-completion amplification;
8. intersection with the chromatic lower event.

---

## 3. Current proof frontier

### 3.1 Parts that are no longer the bottleneck

The public stack now contains rigorous finite or focused-CI-checked versions of:

- the phase expansion and independent-set first moment;
- the four-size signed variational problem;
- the exact signed overlap identity;
- all partial diagonals;
- the endpoint transport inequality;
- the all-high one-cell deficit estimate;
- the matching-restriction product theorem;
- the q-only literal residual attachment estimate;
- the exact reduction of the normalized second moment to the Section VIII bare
  skeleton estimate;
- the rare-seed amplifier and graph-law concentration infrastructure.

PR #41 additionally proves the exact full-endpoint reference normalization:
for each endpoint table `L`, summing over all selected block pairings and all
full-cell physical stub matchings gives exactly the manuscript weight
`fourEndpointW(L)`, with no missing or duplicated factorial.

It also proves that the map

```text
fourEndpointDecoratedBlockPairingToPhysicalFibre
```

is injective.

### 3.2 Exact remaining closure theorem

The decisive remaining proof obligation is a global Section VIII reindexing
and comparison theorem.

It has two finite subproblems.

#### Endpoint physical-fibre equivalence

Complete the reverse construction

```text
FourEndpointPhysicalFibre
  -> FourEndpointDecoratedBlockPairing
```

and prove the two round trips. The source branch already contains a candidate
reverse-data construction, but it must receive a direct focused build and a
line-by-line audit before it is counted as proved.

#### Aggregate deficit reindexing

Every attained canonical high physical skeleton must be represented by:

1. a block-level matching support `P`;
2. one full endpoint size `m_e` per selected cell;
3. one admissible deficit `h_e`, so the actual multiplicity is
   `j_e=m_e-h_e`;
4. one partial physical stub matching in each selected cell.

After summing the local physical fibres, the aggregate weight is

\[
 w(P,j)
 =
 \frac{\prod_{e\in P}(s_e)_{j_e}(t_e)_{j_e}}
      {(n)_J\prod_{e\in P}j_e!}
 \prod_{e\in P}g(j_e),
 \qquad J=\sum_{e\in P}j_e.
\]

For `d_e=|s_e-t_e|` and `h_e=m_e-j_e`, the exact local aggregate ratio is

\[
 R_{m,d}(h)
 =
 \frac{\binom mh}{(d+1)(d+2)\cdots(d+h)}
 2^{-hm+h(h+1)/2}.
\]

The single nonlocal denominator changes by

\[
 \frac{(n)_{J+H}}{(n)_J}=(n-J)_H\le n^H,
 \qquad H=\sum_e h_e.
\]

Hence

\[
 \boxed{
 \frac{w(P,m-h)}{w_{\mathrm{full}}(P)}
 \le
 \prod_{e\in P}n^{h_e}R_{m_e,d_e}(h_e).}
\]

The high-cell condition gives `2h<m`, and therefore

\[
 n^hR_{m,d}(h)
 \le
 \left(\frac{nm}{2^{\lfloor2m/3\rfloor}}\right)^h.
\]

At the four-size phase,

\[
 \rho_n
 =O\!\left(\frac{N^{7/3}}{n^{1/3}}\right)=o(1).
\]

Summing the geometric cell fibres and applying endpoint transport gives

\[
 \operatorname{BareSkeletonSum}_n
 \le
 \exp\!\left\{
   O(n^{2/3}N^{4/3})+O(\sqrt{nN})
 \right\}
 =\exp\!\left\{o\!\left(\frac n{N^4}\right)\right\}.
\]

The repaired Section IX theorem then yields

\[
 \frac{\mathbb E Z_n^2}{(\mathbb E Z_n)^2}
 \le
 \exp\!\left\{o\!\left(\frac n{N^4}\right)\right\}.
\]

This is the exact closure route. Further cycle/polymer decompositions do not
address the remaining seam.

---

## 4. Main-paper upgrades already latent in the proof

### 4.1 Phase-resolved theorem

Let

\[
 A_4(\delta)=\log 2-D_4(\delta),
\]

where `D_4` is the four-support entropy loss at phase `delta`.
The root-displacement calculation gives

\[
 r_+(n)-r_4^{\mathrm{co}}(n)
 =
 \left(\frac{q^2}{4}A_4(\delta_n)+o(1)\right)H_n.
\]

The midpoint witness is placed at

\[
 k_{1/2}(n)
 =\left\lceil
   \frac{r_4^{\mathrm{co}}(n)+r_+(n)}2
  \right\rceil.
\]

After integer rounding and amplification, both of which cost `o(H_n)`, one
retains half the root displacement:

\[
 \boxed{
 \chi(G_n)-\zeta(G_n)
 \ge
 \left(\frac{q^2}{8}A_4(\delta_n)-o(1)\right)H_n
 }
\]

with high probability, conditional on the completed normalized second moment.

This should be the main theorem. A uniform fixed constant should be stated as a
corollary.

### 4.2 Stronger certified uniform constant

The exact four-support entropy certificate proves

\[
 A_4(\delta)>\log\!\left(\frac{1000}{639}\right)
\]

uniformly in the full limiting phase interval. Therefore the midpoint theorem
supports

\[
 \boxed{
 c_*=\frac{q^2}{8}\log\!\left(\frac{1000}{639}\right)
 =0.026896409808379\ldots.}
\]

This is approximately

\[
 6.68734884596
\]

times the constant printed in the canonical candidate manuscript.

### 4.3 Complement-symmetric consequence

Since

\[
 \zeta(\overline G)=\zeta(G)
\]

and `G(n,1/2)` is complement invariant, applying the completed theorem to both
`G_n` and `\overline G_n` gives

\[
 \boxed{
 \min\{\chi(G_n),\chi(\overline G_n)\}-\zeta(G_n)
 \ge c_*H_n
 }
\]

with high probability.

This says the mixed partition beats both pure orientations simultaneously.

### 4.4 Tunable upper tail for the cochromatic location

The rare-seed amplifier gives more than one high-probability specialization.
If a `k_n`-cocoloring seed has probability at least `exp(-Lambda_n)`, then for
every deterministic `r>0`,

\[
 \Pr\!\left(
 \zeta(G_n)>k_n+C\left[
   \frac{\sqrt{n\Lambda_n}+\sqrt{nr}}{N}
   +n^{1/3}+1
 \right]\right)
 \le e^{-r}+o(1).
\]

This should be stated as a named theorem or proposition, since it is reusable
outside the single final choice of `r`.

### 4.5 Balanced-sign rare seed

Let `Z_sgn` count signed witnesses with arbitrary clique/independent labels and
let `Z_bal` restrict to exactly `floor(k/2)` clique labels. Then

\[
 \mathbb EZ_{\mathrm{bal}}
 =\frac{\binom{k}{\lfloor k/2\rfloor}}{2^k}
  \mathbb EZ_{\mathrm{sgn}},
\]

and

\[
 \binom{k}{\lfloor k/2\rfloor}\ge\frac{2^k}{k+1}.
\]

Since `Z_bal<=Z_sgn`,

\[
 \frac{\mathbb EZ_{\mathrm{bal}}^2}
      {(\mathbb EZ_{\mathrm{bal}})^2}
 \le
 (k+1)^2
 \frac{\mathbb EZ_{\mathrm{sgn}}^2}
      {(\mathbb EZ_{\mathrm{sgn}})^2}.
\]

Thus the normalized second moment supplies a balanced rare seed at the same
exponential scale, up to `O(log k)`.

The high-probability preservation of balance requires a labelled-slot
amplifier and is a separate theorem target below.

---

## 5. New theorem target I: remove the midpoint loss

### 5.1 General placement

For `0<theta<1`, define

\[
 k_\theta(n)
 =\left\lceil
 r_4^{\mathrm{co}}(n)
 +\theta\bigl(r_+(n)-r_4^{\mathrm{co}}(n)\bigr)
 \right\rceil.
\]

The deterministic distance from the chromatic root is

\[
 r_+(n)-k_\theta(n)
 =
 (1-\theta)
 \left(\frac{q^2}{4}A_4(\delta_n)+o(1)\right)H_n
 +O(1).
\]

Midpoint placement corresponds to `theta=1/2`.

### 5.2 Error-envelope criterion

Suppose all finite-root, second-moment, rounding, and amplification errors that
require a positive buffer above the signed root are bounded by

\[
 E_n=O\!\left(\frac n{N^4}\right).
\]

The signed-root buffer at placement `theta_n` is

\[
 \theta_n\bigl(r_+-r_4^{\mathrm{co}}\bigr)
 =\Theta\!\left(\theta_n\frac n{N^3}\right).
\]

It dominates `E_n` whenever

\[
 \boxed{\theta_nN\longrightarrow\infty.}
\]

A conservative explicit candidate is

\[
 \theta_n=N^{-1/2}.
\]

Then `theta_n->0`, but the seed remains a factor `sqrt N` above the
`n/N^4` error scale.

### 5.3 Target theorem

> **Near-root placement theorem.** Assume the four-support profile
> construction and Proposition 9.2 hold uniformly for placements
> `theta_n` satisfying `theta_n N -> infinity`. Then, for
> `theta_n=N^{-1/2}`,
> \[
> \chi(G_n)-\zeta(G_n)
> \ge
> \left(\frac{q^2}{4}A_4(\delta_n)-o(1)\right)H_n
> \]
> with high probability.

The certified uniform consequence would be

\[
 \boxed{
 \chi(G_n)-\zeta(G_n)
 \ge
 \frac{q^2}{4}\log\!\left(\frac{1000}{639}\right)H_n
 }
\]

with coefficient

\[
 0.053792819616758\ldots,
\]

approximately `13.3746976919` times the canonical displayed coefficient.

### 5.4 Required proof audit

The proof should expose all dependence on the signed-root buffer in:

1. integer profile feasibility;
2. finite-to-limiting entropy approximation;
3. partial-diagonal estimates;
4. canonical high-skeleton estimates;
5. the q-only residual estimate;
6. Paley--Zygmund seed probability;
7. the amplifier loss.

The critical question is not whether `theta` is fixed. It is whether every
error is uniform on a window whose width above the signed root is
`omega(n/N^4)`.

**Priority:** highest-return theorem that reuses the existing architecture.

---

## 6. New theorem target II: exact minimum of the four-support advantage

Numerical scans suggest

\[
 \min_{\delta\in[0,1]}A_4(\delta)
 \approx0.520701335491,
\]

apparently near the endpoint `delta=1`. This value is diagnostic only.

Let `F_S(T)` be the constrained entropy value for support `S`, and let
`lambda_S(T)` be its selected Lagrange multiplier. The envelope identity is

\[
 \frac{d}{dT}F_S(T)=-\lambda_S(T).
\]

For the full support and `S_4={2,3,4,5}`,

\[
 D_4(T)=F_\infty(T)-F_4(T),
\]

so

\[
 \frac{d}{dT}D_4(T)
 =\lambda_4(T)-\lambda_\infty(T).
\]

If `T=T_0(delta)`, then

\[
 A_4'(\delta)
 =T_0'(\delta)
  \bigl(\lambda_\infty(T_0(\delta))
       -\lambda_4(T_0(\delta))\bigr).
\]

A rigorous endpoint-minimum theorem can therefore be obtained by:

1. proving monotonicity of `T_0`;
2. interval-enclosing both selected tilts on a finite partition of the phase
   interval;
3. certifying the sign of `lambda_infinity-lambda_4`;
4. evaluating `A_4(1)` with rational interval bounds.

If the diagnostic minimum is certified, the midpoint coefficient becomes

\[
 0.031271565748\ldots,
\]

and the near-root coefficient becomes

\[
 0.062543131497\ldots.
\]

This would be the sharp constant for the existing four-size support, not the
sharp constant for the full cochromatic problem.

---

## 7. New theorem target III: balance is necessary near the optimum

### 7.1 Sign entropy

Suppose a signed partition has `k` nonempty classes, of which a proportion
`rho` are labelled clique classes. The number of sign assignments with this
proportion is

\[
 \binom{k}{\rho k}
 =\exp\{kH(\rho)+O(\log k)\},
\]

where

\[
 H(\rho)=-\rho\log\rho-(1-\rho)\log(1-\rho).
\]

The unrestricted sign entropy is `k log 2`. Thus an imbalance costs

\[
 k\bigl(\log 2-H(\rho)\bigr).
\]

Near `rho=1/2+x`,

\[
 \log 2-H(1/2+x)=2x^2+O(x^4).
\]

Since the local derivative of the coloring first-moment logarithm with respect
to the number of classes is of order `N^2`, an entropy loss of order
`k=Theta(n/N)` produces a root displacement of order

\[
 \frac{n/N}{N^2}=\frac n{N^3}=H_n.
\]

### 7.2 Target structural theorem

> **Balance stability theorem.** For every fixed `epsilon>0`, there exists
> `c(epsilon)>0` such that, with high probability, every cocoloring whose
> clique-class proportion lies outside
> `[1/2-epsilon,1/2+epsilon]` uses at least
> \[
> r_4^{\mathrm{co}}(n)+c(\epsilon)H_n
> \]
> nonempty classes.

A quantitative local version should give

\[
 c(\epsilon)
 =\frac{q^2}{4}\bigl(\log 2-H(1/2+\epsilon)\bigr)
 +o_\epsilon(1)
\]

up to the support loss and root normalization.

Consequently, any sequence of cocolorings with class count

\[
 r_4^{\mathrm{co}}(n)+o(H_n)
\]

must satisfy

\[
 \rho_n=\frac12+o(1).
\]

This is more conceptually valuable than merely constructing one balanced seed:
it identifies a structural feature forced by near-optimality.

### 7.3 Proof route

1. refine the first-moment sum by the number of clique labels;
2. replace the sign factor `2^k` by `binom(k,rho k)`;
3. rerun the finite-support root calculation with `log 2` replaced by
   `H(rho)`;
4. take a union bound over imbalanced `rho` values;
5. combine with the balanced existence result.

A labelled-slot amplifier can then produce, with high probability, a
near-optimal cocoloring having

\[
 \#\{\text{clique parts}\}=(1/2+o(1))k,
 \qquad
 \#\{\text{independent parts}\}=(1/2+o(1))k.
\]

---

## 8. High-upside extension: slowly growing support

### 8.1 Motivation

For a fixed finite support `S`, the signed-root advantage is

\[
 \frac{q^2}{4}\bigl(\log 2-D_S(\delta_n)\bigr)H_n.
\]

The four-size support has a strictly positive but nonzero truncation loss.
A five-size support improves the scanned minimum by only about `1.017%` while
raising the endpoint table dimension from `4x4` to `5x5`. Therefore a single
fixed extra size is not a compelling redesign.

The meaningful target is a support `S_n` whose width tends slowly to infinity.

### 8.2 Limiting coefficient

If

\[
 \sup_{\delta\in[0,1]}D_{S_n}(\delta)\longrightarrow0,
\]

then the signed-root displacement tends to

\[
 \frac{q^3}{4}H_n.
\]

Midpoint placement would retain

\[
 \frac{q^3}{8}=0.041628081498616\ldots,
\]

whereas near-root placement would retain

\[
 \boxed{
 \frac{q^3}{4}=0.083256162997232\ldots.}
\]

### 8.3 Why uniform truncation is plausible

The selected full-support deficit law has Gaussian-type tails in the existing
analytic infrastructure. A support containing all deficits up to a cutoff
`m` should therefore satisfy an omitted-mass estimate of the form

\[
 \sup_\delta D_m(\delta)
 \le C\exp(-cm^2)
\]

or another uniform tail tending to zero.

The first-moment side is therefore plausible. The principal difficulty is a
second moment uniform in the number of endpoint types.

### 8.4 Dimension-uniform second-moment program

The fixed-support proof must be reorganized so that constants depend on the
support width through an explicit complexity envelope `K(m)`.

Required ingredients:

1. endpoint transportation controlled by norms or generating functions rather
   than `m^2` unrelated cell estimates;
2. a block-matching description whose sparsity is independent of the ambient
   type-table dimension;
3. all-high deficit bounds uniform in the endpoint type;
4. q-only residual bounds with explicit polynomial or subexponential dependence
   on `m`;
5. an explicit choice `m=m_n` such that
   \[
   K(m_n)=o(N).
   \]

If `K(m)` is polynomial, `m_n=floor(log log n)` is more than sufficient. If
`K(m)` is exponential in a fixed power of `m`, a slower cutoff such as
`floor(log log log n)` may be appropriate.

### 8.5 Target theorem

> **Slow-support theorem.** There exists an explicit sequence `m_n->infinity`
> and a signed profile supported on `m_n` consecutive deficit sizes such that
> \[
> \chi(G_n)-\zeta(G_n)
> \ge
> \left(\frac{q^3}{4}-o(1)\right)H_n
> \]
> with high probability.

This would be the strongest result naturally suggested by the present signed
entropy mechanism. It is a plausible separate paper or a major Version 3,
not a prerequisite for validating the July 12 theorem.

---

## 9. Largest follow-up target: prove the matching upper bound

Heckel conjectures

\[
 \chi(G_n)-\zeta(G_n)
 \asymp\frac n{(\log n)^3}
\]

with high probability. The candidate theorem supplies the full-sequence lower
bound side.

The most important possible follow-up is

\[
 \boxed{
 \chi(G_n)-\zeta(G_n)
 =O(H_n)
 }
\]

with high probability.

### 9.1 Required location bounds

A two-sided proof can be decomposed into:

\[
 \zeta(G_n)
 \ge r_{\mathrm{signed,full}}(n)-O(H_n)
\]

and

\[
 \chi(G_n)
 \le r_+(n)+O(H_n).
\]

The first inequality is a lower bound on the cochromatic number and should come
from a first-moment union bound over **all** signed profiles, not only the
selected four-size witness family.

The second inequality requires a third-order ordinary-coloring construction.
Existing first-order or `o(n/N^2)` localization is not automatically precise
enough at the `H_n=n/N^3` scale.

### 9.2 Intermediate publishable theorem

Before the full upper bound, establish a phase-resolved corridor

\[
 r_{\mathrm{signed,full}}(n)-o(H_n)
 \le\zeta(G_n)
 \le r_4^{\mathrm{co}}(n)+o(H_n).
\]

This would be the first explicit third-order location result for the
cochromatic number itself and would isolate the remaining ordinary-coloring
input needed for the complete `Theta(H_n)` theorem.

### 9.3 Why this should be a separate project

The lower-gap proof is based on constructing one signed witness and amplifying
a rare seed. A matching upper bound requires excluding all better signed
partitions and constructing ordinary colorings to matching precision. It is a
different global optimization problem and should not delay external review of
the current proof.

---

## 10. General edge density `p != 1/2`

For `G(n,p)`, a class of size `s` is independent with probability

\[
 (1-p)^{\binom s2}
\]

and a clique with probability

\[
 p^{\binom s2}.
\]

Summing the two declarations gives the one-class reward

\[
 g_p(s)=p^{\binom s2}+(1-p)^{\binom s2}.
\]

At `p=1/2`,

\[
 g_{1/2}(s)=2^{1-\binom s2},
\]

which is the exact symmetric sign gain used in the present proof.

For `p!=1/2`, the optimal declaration depends on class size and the two-partition
overlap factor acquires an external field. The binary compatibility sum becomes
an inhomogeneous Ising-type partition function on the overlap support graph.

A separate project should determine:

1. whether a polynomial chromatic--cochromatic gap persists for every fixed
   `p in (0,1)`;
2. the optimal phase-dependent clique proportion;
3. the analogue of the finite-support entropy advantage;
4. whether `p=1/2` is merely a symmetry point or a transition point in the
   structure of optimal mixed partitions.

This direction connects naturally with generalized hereditary chromatic numbers:

- E. Scheinerman, *Generalized Chromatic Numbers of Random Graphs*, SIAM J.
  Discrete Math. 5 (1992), 74--80;
- B. Bollobás and A. Thomason, *Generalized chromatic numbers of random graphs*,
  Random Structures & Algorithms 6 (1995), 353--356.

---

## 11. Two-independent-graph model

The Erdős Problems discussion records the following model, attributed there to
Zach Hunter with Micha Christoph, Annika Heckel, and Raphael Steiner.

Let `G_1,G_2` be independent copies of `G(n,1/2)`. Define `X(G_1,G_2)` as the
minimum number of parts in a partition in which each part is independent in at
least one of the two graphs.

For a fixed partition into `k` classes and a fixed assignment of every class to
one of the two layers,

\[
 \Pr\{\text{all assigned independence constraints hold}\}
 =2^{-\sum_i\binom{|C_i|}{2}}.
\]

Summing over the `2^k` layer assignments gives **exactly the same first moment**
as the signed clique/independent witness at `p=1/2`.

The second moment is different. A class labelled clique in one witness and
independent in another creates a compatibility obstruction in the one-graph
model. In the two-layer model, constraints in different graph layers are
independent rather than contradictory. This may replace the cycle-space
compatibility factor by a simpler two-layer overlap calculation.

The forum comment reports a McDiarmid coupling under which

\[
 X(G_1,G_2)\ge\zeta(G)
\]

for a coupled `G~G(n,1/2)`. The comments are explicitly unverified. Before
using this model in a paper:

1. obtain the exact coupling proof from the people named in the discussion;
2. agree on attribution;
3. calculate the two-layer normalized second moment;
4. compare its phase constant with the one-graph signed model.

This is a credible alternative proof or follow-up paper, not an input that
should be silently folded into the current manuscript.

---

## 12. Reusable method results

### 12.1 Restriction-product theorem

If a finite family `C` of subsets of a finite ground set `E` is determined
injectively by deletion of a coordinate set `I`, then for nonnegative
activities `q_e`,

\[
 \sum_{A\in\mathcal C}\prod_{e\in A\setminus I}q_e
 \le\prod_{e\in E\setminus I}(1+q_e).
\]

For graph cycle spaces, deletion of a forest is injective. For binary matroid
cycle spaces, deletion of an independent set is injective.

The theorem is useful inside the main paper. It is too short for a standalone
paper unless combined with several applications or a stability/sharpness
theory.

### 12.2 Exact cycle-space factor

For two signed partitions, the support graph of overlap cells of size at least
two carries the exact factor

\[
 2^{W+c(H)-|V(H)|}
 =\left(\prod_e g(r_e)\right)2^{\beta(H)}.
\]

The topological correction is the binary cycle-space dimension. A `q`-template
generalization should lead to Potts/Tutte-type factors.

### 12.3 Rare-seed amplifier

The amplification argument depends only on:

1. independent block exposure;
2. a Lipschitz maximum feasible induced-subobject score;
3. a rare full-coverage seed;
4. a deterministic or high-probability leftover completion rule.

An abstract methods theorem would apply to other hereditary covering and
partition parameters. It becomes a viable standalone methods paper only after
at least one further nontrivial application is supplied.

---

## 13. Recommended publication architecture

### Main Erdős 625 paper, Version 2

Include:

1. the full-sequence candidate theorem after external verification;
2. the phase-resolved coefficient;
3. the certified uniform coefficient
   `q^2 log(1000/639)/8`;
4. the simultaneous complement corollary;
5. the tunable cochromatic upper-tail theorem;
6. the matching-restriction simplification;
7. the exact endpoint normalization and aggregate deficit proof;
8. the rare-seed amplifier as a named method proposition;
9. a precise public chronology and verification-status paragraph.

Include the balanced rare seed. Include high-probability balance only if the
labelled-slot amplifier is completed.

### Follow-up paper A: structure and sharp coefficient

Best moderate-risk package:

1. near-root placement and removal of the midpoint loss;
2. exact phase minimum for the four-support advantage;
3. existence and necessity of balanced near-optimal cocolorings.

This package would improve both the constant and the conceptual content.

### Follow-up paper B: growing support

Develop dimension-uniform endpoint and residual estimates and approach the
coefficient `q^3/4`.

### Follow-up paper C: matching upper bound

Prove the `O(n/(log n)^3)` upper bound and hence the full order conjecture.
This is the most important but highest-risk project.

### Alternative follow-up

Develop the two-independent-graph model after direct communication and explicit
attribution.

---

## 14. Concrete PR sequence

### Closure PRs

1. validate the physical-fibre reverse-data module;
2. prove decorated/physical round trips;
3. prove the aggregate high-deficit reindexing;
4. instantiate the bare-skeleton asymptotic;
5. derive Proposition 9.2 and the final event intersection on one branch.

### Value-upgrade PRs

6. integrate the phase-resolved `/8` theorem and stronger entropy certificate;
7. add complement and tunable-tail corollaries;
8. expose a uniform error envelope in the placement parameter;
9. prove the `theta_n=N^{-1/2}` near-root theorem;
10. prove the balanced-sign first-moment stability theorem;
11. certify the exact four-support phase minimum.

### Separate-paper branches

12. dimension-uniform slowly growing support;
13. all-profile first moment for the lower location of `zeta`;
14. third-order ordinary-coloring upper construction;
15. combine 13--14 into the matching upper bound.

---

## 15. Decision table

| Direction | Mathematical value | Reuses current proof | Risk | Recommended destination |
|---|---:|---:|---:|---|
| Close physical fibre and deficits | essential | very high | medium | current main paper |
| Phase-resolved `/8` theorem | high | complete | low | current main paper |
| Stronger uniform certificate | high | complete | low | current main paper |
| Complement/tail corollaries | medium | complete | low | current main paper |
| Near-root placement | very high | high | medium | first follow-up or strong V2 |
| Exact phase minimum | medium-high | high | medium | first follow-up |
| Balance necessity | high conceptual value | high | medium | first follow-up |
| Fixed five-size support | small gain | medium | medium | do not prioritize |
| Slowly growing support | very high | medium | high | separate paper |
| Matching upper bound | maximal | low-medium | very high | major separate paper |
| General `p` | high | medium | high | separate paper |
| Two-graph coupling | potentially high | partial | high/attribution-sensitive | separate collaboration |

---

## 16. Immediate recommendation

The next mathematical work should proceed in this order:

1. **Finish the current proof closure.** This is still necessary for any theorem
   upgrade to be meaningful.
2. **Promote the phase-resolved theorem and the coefficient
   `0.0268964098...` into the main paper.** These are already latent in the
   current architecture.
3. **Attack near-root placement with `theta_n=N^{-1/2}`.** This is the best
   ratio of new value to new machinery.
4. **Prove balance stability.** This gives a structural theorem, not merely a
   larger decimal constant.
5. **Choose one major follow-up:** slowly growing support for the best lower
   constant, or the matching upper bound for the full conjectured order.

Further isolated constant tweaks or fixed-support grid scans should not take
priority over these steps.
