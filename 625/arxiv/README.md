# Erdős Problem 625 publication package

`main.tex` is the canonical, self-contained manuscript source. It contains no
local `\input` dependencies. The bibliography is supplied both as
`references.bib` and as the generated `main.bbl` for arXiv portability.

Build from this directory with:

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error main.tex
```

## arXiv submission

Upload `Erdos625_source.zip`, select `pdflatex`, and use `main.tex` as the
top-level file. At the time of this release, TeX Live 2025 is arXiv's default;
TeX Live 2023 remains available as a fallback if the generated preview differs.
Retain `main.bbl`: arXiv uses a pre-generated bibliography when its basename
matches the top-level source.

These choices follow arXiv's current
[TeX submission guidance](https://info.arxiv.org/help/submit_tex.html).

The manuscript intentionally contains neither `\date` nor `\today`. The arXiv
identifier and submission record supply the authoritative date, whereas
`\today` would change whenever arXiv rebuilds the source. Before submitting,
inspect the arXiv-generated PDF and compilation log, with particular attention
to the three figures, the final theorem, and the bibliography. See arXiv's
[date guidance](https://info.arxiv.org/help/faq/today.html) for the reason the
source is undated.

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

`Erdos625_source.zip` contains `main.tex`, `main.bbl`, `references.bib`, and
this build guide. `main.tex` and the pre-generated `main.bbl` suffice to compile
the paper; `references.bib` is retained as bibliography source and provenance,
and the guide makes the archive self-describing.
