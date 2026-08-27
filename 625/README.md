# Erdős Problem 625

This directory contains a proposed resolution of Erdős Problem 625 and its
complete Lean 4 formalization.

For `G_n ~ G(n,1/2)`, the proved quantitative statement is

```text
P(chi(G_n) - zeta(G_n)
  >= ((log 2)^2 / 32) log(200/153) * n/(log n)^3) -> 1.
```

In particular, the chromatic--cochromatic gap tends to infinity with high
probability along the full sequence of integers.

## Publication files

- [`arxiv/main.tex`](arxiv/main.tex) is the single, self-contained manuscript
  source.
- [`arxiv/main.pdf`](arxiv/main.pdf) is the compiled manuscript.
- [`arxiv/references.bib`](arxiv/references.bib) and
  [`arxiv/main.bbl`](arxiv/main.bbl) contain the bibliography.
- [`arxiv/Erdos625_source.zip`](arxiv/Erdos625_source.zip) is the submission
  source package.

## Formal verification

[`formalization/`](formalization/) contains the modular Lean project and the
generated one-file proof [`Erdos625SelfContained.lean`](formalization/Erdos625SelfContained.lean).
Both prove the same theorem and use the repository-pinned Lean/mathlib v4.31.0
toolchain. See [`formalization/README.md`](formalization/README.md) for exact
reproduction commands, the trust boundary, and the immutable cloud replay
transcript.

[`verification/`](verification/) contains independent finite and symbolic
checks used to test numerical certificates and manuscript identities. These
checks support the audit trail; they are not substitutes for either the
mathematical argument or the Lean proof.

This is a preprint and has not undergone external peer review. The repository
makes the argument and formalization available for expert scrutiny; it does not
claim an official change in the published status of the problem.
