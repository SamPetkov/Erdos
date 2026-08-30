# Erdős Problem 625 publication package

`main.tex` is the canonical, self-contained manuscript source. It contains no
local `\input` dependencies. The bibliography is supplied both as
`references.bib` and as the generated `main.bbl` for arXiv portability.

Build from this directory with:

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error main.tex
```

The resulting `main.pdf` states a phase-resolved theorem with coefficient
`((log 2)^2 / 4) A_4(delta_n) - o(1)` and the uniform consequence with
coefficient `((log 2)^2 / 4) log(200/153)`. The companion declaration
`Erdos625.erdos625` kernel-checks this same explicit uniform consequence and
therefore resolves Erdős Problem 625. Its exact formal source revision is
`824e4b609466d2e26b216a76ecf103184dac2663`, under the pinned Lean/Mathlib
v4.31.0 toolchain, and its immutable replay and archive revision is
`31bbe00c529a996bdb61b880120d71240172d18f`. Detailed build commands,
checksums, the trust-boundary audit, and clean-environment replay evidence are
maintained in the companion formalization documentation. The phase-resolved
refinement involving `A_4(delta_n)` is established in the manuscript and is
not claimed as part of the Lean theorem.

`Erdos625_source.zip` contains the four files needed for submission:
`main.tex`, `main.bbl`, `references.bib`, and this README.
