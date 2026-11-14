# Erdős 625: revised replacement manuscript

This directory contains the current manuscript and its source package, prepared on 14 November 2026 from the author's revised sources of 13 November 2026. The manuscript keeps the date of the first arXiv posting, 30 August 2026.

## Files

- [main.pdf](main.pdf): the 56-page paper.
- [main.tex](main.tex), [main.bbl](main.bbl), [references.bib](references.bib), [petkov-preprint.sty](petkov-preprint.sty): the matching editable sources.
- [Erdos625_source.zip](Erdos625_source.zip): the four source files above, ready for arXiv.
- [arxiv-abstract.txt](arxiv-abstract.txt) and [arxiv-comments.txt](arxiv-comments.txt): submission text.
- [MANIFEST.txt](MANIFEST.txt) and [SHA256SUMS](SHA256SUMS): directory inventory and digests; the digest list excludes itself.

## Changes in this revision

- **Five class sizes.** The argument uses five consecutive class sizes instead of four. The uniform coefficient becomes `(log 2)^2/4 * log(8750/6681) ≈ 0.032405`, up from `(log 2)^2/4 * log(200/153) ≈ 0.032176`. The phase-resolved form uses the five-size phase gain `A_5`, and Lemma 5.3 gives `A_5 > log(8750/6681)` on `[0, 1]`.
- **Summable failure probability.** Corollary 11.2 bounds the failure probability by `O(n^(-3/2) (log n)^(β+5/2))` with `β = 2/log 2 + 1/2`, uniformly in the phase. This is summable over `n`.
- **Almost-sure form.** Corollary 11.3 deduces that, under any coupling of the graphs, the gap bound holds almost surely for all sufficiently large `n`.
- **Exposition.** The abstract is rewritten, and the introduction, the notation section and several section openings are edited for clarity.

## Formalization boundary

The released Lean theorem is the fixed-coefficient consequence with `log(200/153)`. The Lean project also proves Lemmas 5.2 and 5.3 and two stronger lower bounds for `A_5` on `[0, 1]`, the strongest being `A_5 > log(169/100)`. These modules do not lift the released theorem to the manuscript's coefficient. The phase refinement, the remainder rate and the failure-probability bounds are written results, not Lean theorems. See the [Lean README](../formalization/README.md).

## Build

Use a TeX distribution with pdfLaTeX, BibTeX, `latexmk`, and the packages
loaded by `main.tex` and `petkov-preprint.sty`. For a minimal installation,
include `newtx`, its `kastrup` (`binhex.tex`) support, and the `tex-gyre` fonts.
Keep all four source files together and run from this directory:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The ZIP contains exactly `main.tex`, `main.bbl`, `references.bib`, and `petkov-preprint.sty` at its root. Its replacement destination is arXiv:2608.30604.
