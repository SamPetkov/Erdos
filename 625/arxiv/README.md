# arXiv manuscript source

This directory contains the publication-layout manuscript for the candidate
resolution of Erdős Problem 625.

## Files

- `main.tex` — editable article source.
- `references.bib` — author–year bibliography.
- `main.bbl` — bibliography output included for arXiv submission portability.
- `main.pdf` — compiled 35-page preprint dated 12 July 2026.

The article lists Samuil Petkov as the author. Its ethics and reproducibility
statements disclose substantial assistance from ChatGPT 5.6, independent AI
verification, and quarantined use of Aristotle for atomic Lean proof search.
It also states that there was no external funding and that there are no
competing interests.

The introduction and technical sections identify precisely how the manuscript
builds on Heckel (2024) and Heckel (2025): contextual anti-concentration and
the conjectural scale, the one-partition signed factor, overlap-sensitive sign
bookkeeping, and the rare-seed/concentration strategy. The manuscript
rederives the finite identities it uses and distinguishes its claimed
full-phase estimates from Heckel's range-restricted theorem.

## Build

With a TeX installation providing `latexmk`, run from this directory:

```powershell
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The checked build used MiKTeX pdfTeX 1.40.29. The final log contained no
LaTeX, package, citation, reference, overfull-box, or underfull-box warnings.

## Status

This is a candidate mathematical manuscript, not a claim of peer review or
community acceptance. The accompanying [Lean development](../formalization/)
is a verified partial formalization; the exact final probabilistic theorem
remains open in Lean. Aristotle output is accepted only after local replay,
warning-as-error compilation, placeholder scanning, and an axiom audit.
