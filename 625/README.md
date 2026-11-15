# Erdős Problem 625

This directory contains a proposed resolution of Erdős Problem 625, together
with a Lean 4 formalization of an explicit quantitative consequence that
already resolves the problem.

The [`G(12,1/2)` animation](assets/animations/) is an exactly solved finite
illustration with recorded witnesses and checksums. It is not used in the
asymptotic proof.

For $G_n\sim G(n,1/2)$, write $\chi$ for the chromatic number and $\zeta$
for the cochromatic number. All logarithms are natural. Using five consecutive
class sizes, the manuscript proves

$$
\mathbb P\!\left(
  \chi(G_n)-\zeta(G_n)
  \ge c\,\frac{n}{(\log n)^3}
\right)\longrightarrow1
$$

for every constant $c\lt c_5=\frac{(\log 2)^2}{4}\min_{[0,1]}A_5$, and
Lemma 5.4 gives $c_5\gt\frac{(\log 2)^2}{4}\log(169/100)=0.0630268508\ldots$;
in particular the bound holds with $c=0.063$. It also proves the
phase-resolved statement

$$
\mathbb P\!\left(
  \chi(G_n)-\zeta(G_n)
  \ge \left[\frac{(\log 2)^2}{4}A_5(\delta_n)-\varepsilon_n\right]
      \frac{n}{(\log n)^3}
\right)\longrightarrow1,
$$

where $A_5\gt\log(169/100)$ on $[0,1]$ and the deterministic error satisfies
$\varepsilon_n=O(\log\log n/\log n)$ uniformly in the rounding phase.
Corollary 11.2 bounds the failure probability by
$O(n^{-3/2}(\log n)^{\beta+5/2})$, where $\beta=2/\log 2+1/2$, uniformly in
the phase. This bound is summable over $n$, so under any coupling of the
graphs the gap bound holds almost surely for all sufficiently large $n$
(Corollary 11.3).

The released Lean theorem is the weaker explicit consequence

$$
\mathbb P\!\left(
  \chi(G_n)-\zeta(G_n)
  \ge \frac{(\log 2)^2}{4}\log\!\left(\frac{200}{153}\right)
      \frac{n}{(\log n)^3}
\right)\longrightarrow1.
$$

In particular, the chromatic--cochromatic gap tends to infinity with high
probability along the full sequence of integers.

## Publication files

- [`arxiv/main.tex`](arxiv/main.tex) is the main LaTeX entry point.
- [`arxiv/main.pdf`](arxiv/main.pdf) is the compiled manuscript.
- [`arxiv/references.bib`](arxiv/references.bib) and
  [`arxiv/main.bbl`](arxiv/main.bbl) contain the bibliography.
- [`arxiv/petkov-preprint.sty`](arxiv/petkov-preprint.sty) is the required
  stylesheet; keep it with the other three source files.
- [`arxiv/Erdos625_source.zip`](arxiv/Erdos625_source.zip) is the submission
  source package. See the [build instructions](arxiv/README.md#build-and-replacement).

## Formal verification

[`formalization/`](formalization/) contains the modular Lean project and the
generated one-file proof
[`Erdos625SelfContained.lean`](formalization/Erdos625SelfContained.lean).
Both sources kernel-check the displayed uniform consequence under the
repository-pinned Lean/mathlib v4.31.0 toolchain. The formal proof includes the
fixed-offset construction leading to the uniform coefficient. The
manuscript's larger constant `c_5`, which exceeds
`(log 2)^2/4 * log(169/100)`, and its phase-resolved
refinement involving `A_5(delta_n)`, including the remainder and
failure-probability bounds, are proved in the manuscript and are not claimed
as part of the Lean theorem. The cloud-replayed formal source is
commit `824e4b609466d2e26b216a76ecf103184dac2663`; see
[`formalization/README.md`](formalization/README.md) for reproduction commands,
the trust boundary, and the immutable cloud replay record at
`31bbe00c529a996bdb61b880120d71240172d18f`. Both Lean sources now also
contain three modules proving lower bounds for the five-size phase gain `A_5`
on `[0, 1]`: the manuscript's Lemma 5.3 and stronger bounds up to
`A_5(delta) > log(169/100)`. They
do not change the Lean theorem, and the extended sources have not been
replayed in the cloud.

[`verification/`](verification/) contains independent finite and symbolic
checks used to test numerical certificates and manuscript identities. They
are not substitutes for either the mathematical argument or the Lean proof.

This is a preprint and has not undergone external peer review. The repository
makes the argument and formalization available for expert scrutiny; it does not
claim an official change in the published status of the problem.
