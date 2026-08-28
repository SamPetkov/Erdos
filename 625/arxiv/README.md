# Erdős Problem 625 publication package

`main.tex` is the canonical, self-contained manuscript source. It contains no
local `\input` dependencies. The bibliography is supplied both as
`references.bib` and as the generated `main.bbl` for arXiv portability.

Build from this directory with:

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error main.tex
```

The resulting `main.pdf` states the theorem represented by
`Erdos625.erdos625` in the companion Lean development, with coefficient
`((log 2)^2 / 32) log(200/153)`. The manuscript cites an exact Git revision of
that software companion. Its formal source revision is
`86c4422f9b41c4ce50e7c920dc7349a9f07f24a8`, under the pinned Lean/Mathlib
v4.31.0 toolchain. Detailed build commands, checksums, trust-boundary audit,
and clean-environment replay evidence are maintained in the companion
formalization documentation.

`Erdos625_source.zip` contains the four files needed for submission:
`main.tex`, `main.bbl`, `references.bib`, and this README.
