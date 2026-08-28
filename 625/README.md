# Erdős Problem 625

This directory contains a proposed resolution of Erdős Problem 625, together
with a Lean 4 formalization of an explicit quantitative consequence that
already resolves the problem.

For `G_n ~ G(n,1/2)`, the manuscript proves the phase-resolved statement

```text
P(chi(G_n) - zeta(G_n)
  >= [((log 2)^2 / 4) A_4(delta_n) - epsilon_n]
     * n/(log n)^3) -> 1,
```

where `epsilon_n -> 0`. Its explicit uniform consequence is

```text
P(chi(G_n) - zeta(G_n)
  >= ((log 2)^2 / 4) log(200/153) * n/(log n)^3) -> 1.
```

The companion Lean theorem certifies the conservative consequence

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
Both Lean sources prove the displayed conservative consequence and use the
repository-pinned Lean/mathlib v4.31.0 toolchain. The fixed-offset construction,
phase-resolved coefficient, and stronger uniform constant are established in
the manuscript proof and are not claimed as kernel-checked. See
[`formalization/README.md`](formalization/README.md) for exact reproduction
commands, the trust boundary, and the immutable cloud replay transcript.

[`verification/`](verification/) contains independent finite and symbolic
checks used to test numerical certificates and manuscript identities. These
checks support the audit trail; they are not substitutes for either the
mathematical argument or the Lean proof.

This is a preprint and has not undergone external peer review. The repository
makes the argument and formalization available for expert scrutiny; it does not
claim an official change in the published status of the problem.
