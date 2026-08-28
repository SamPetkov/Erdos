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
`Erdos625.erdos625` kernel-checks the conservative consequence with coefficient
`((log 2)^2 / 32) log(200/153)`, which already resolves Erdős Problem 625.
The manuscript cites an exact Git revision of that software companion. Its
formal source revision is
`86c4422f9b41c4ce50e7c920dc7349a9f07f24a8`, under the pinned Lean/Mathlib
v4.31.0 toolchain. Detailed build commands, checksums, trust-boundary audit,
and clean-environment replay evidence are maintained in the companion
formalization documentation. The stronger phase-resolved and uniform
coefficients are established in the manuscript proof and are not claimed as
part of the current Lean theorem.

`Erdos625_source.zip` contains the four files needed for submission:
`main.tex`, `main.bbl`, `references.bib`, and this README.
