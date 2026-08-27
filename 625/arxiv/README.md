# Erdős Problem 625 publication package

`main.tex` is the canonical, self-contained manuscript source. It contains no
local `\input` dependencies. The bibliography is supplied both as
`references.bib` and as the generated `main.bbl` for arXiv portability.

Build from this directory with:

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error main.tex
```

The resulting `main.pdf` states the theorem represented by
`Erdos625.erdos625` in the public formalization at the immutable commit
`86c4422f9b41c4ce50e7c920dc7349a9f07f24a8`, with coefficient
`((log 2)^2 / 32) log(200/153)`. The deterministic standalone Lean source has
SHA-256
`0f54ac26285e5a1631ed62f0258ba0836cc3a2cd28cc35df3b2f737cfaffac30`.
On 2026-08-27 this exact file was replayed in a clean cloud environment under
the pinned Lean/Mathlib v4.31.0 toolchain with
`lake env lean -DwarningAsError=true Erdos625SelfContained.lean`; the command
exited 0, and `#print axioms Erdos625.erdos625` reported exactly `propext`,
`Classical.choice`, and `Quot.sound`.
`Erdos625_source.zip` contains the four files needed for submission:
`main.tex`, `main.bbl`, `references.bib`, and this README.
