# Erdős Problem 625

This directory contains a proposed resolution of Erdős Problem 625, together
with a Lean 4 formalization of an explicit quantitative consequence that
already resolves the problem.

The [`G(12,1/2)` animation](assets/animations/) is an exactly solved finite
illustration with recorded witnesses and checksums. It is not used in the
asymptotic proof.

For $G_n\sim G(n,1/2)$, write $\chi$ for the chromatic number and $\zeta$
for the cochromatic number. The manuscript proves the phase-resolved statement

$$
\mathbb P\!\left(
  \chi(G_n)-\zeta(G_n)
  \ge \left[\frac{(\log 2)^2}{4}A_4(\delta_n)-\varepsilon_n\right]
      \frac{n}{(\log n)^3}
\right)\longrightarrow1.
$$

All logarithms are natural. The deterministic error satisfies
$\varepsilon_n=O(\log\log n/\log n)$ uniformly in the rounding phase.
Corollary 11.2 also bounds the failure probability by
$O((\log n)^{2/\log 2+1/2}/n)$ for this remainder order and for the
fixed-coefficient consequence, with phase-independent constants and an
eventual threshold. These refinements are proved in the manuscript.

The explicit uniform consequence, which is also the released Lean theorem, is

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
fixed-offset construction leading to the uniform coefficient. The stronger
phase-resolved refinement involving `A_4(delta_n)`, including its quantified
remainder and failure-probability bound, is proved in the manuscript
and is not claimed as part of the Lean theorem. The exact formal source is
commit `824e4b609466d2e26b216a76ecf103184dac2663`; see
[`formalization/README.md`](formalization/README.md) for reproduction commands,
the trust boundary, and the immutable cloud replay record at
`31bbe00c529a996bdb61b880120d71240172d18f`. The current manuscript update
leaves the released Lean proof sources and standalone file byte-for-byte
unchanged.

[`verification/`](verification/) contains independent finite and symbolic
checks used to test numerical certificates and manuscript identities. These
checks support the audit trail; they are not substitutes for either the
mathematical argument or the Lean proof.

This is a preprint and has not undergone external peer review. The repository
makes the argument and formalization available for expert scrutiny; it does not
claim an official change in the published status of the problem.
