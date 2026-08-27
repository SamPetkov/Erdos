# Erdős Problem 625 publication package

`main.tex` is the canonical, self-contained manuscript source. It contains no
local `\input` dependencies. The bibliography is supplied both as
`references.bib` and as the generated `main.bbl` for arXiv portability.

Build from this directory with:

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error main.tex
```

The resulting `main.pdf` states the exact theorem proved by
`Erdos625.erdos625` in the public formalization at
`https://github.com/SamPetkov/Erdos/tree/main/625/formalization`, with coefficient
`((log 2)^2 / 32) log(200/153)`. `Erdos625_source.zip` contains the four files
needed for submission: `main.tex`, `main.bbl`, `references.bib`, and this
README.
