# Publication artifacts

This directory contains publication-oriented derivatives of the canonical
Markdown proof in
[`../proofs/COMPLETE_PROOF_SELF_CONTAINED.md`](../proofs/COMPLETE_PROOF_SELF_CONTAINED.md).
The derivatives do not change the theorem, proof text, or qualification as a
candidate solution that has not been externally peer reviewed.
The Markdown, TeX title page, and embedded PDF metadata attribute the
manuscript to **Samuil Petkov & ChatGPT 5.6**.

## Files

- [`tex/COMPLETE_PROOF_SELF_CONTAINED.tex`](tex/COMPLETE_PROOF_SELF_CONTAINED.tex)
  - standalone LF-normalized TeX generated with Pandoc 3.9.0.2.
- [`tex/BUILD.md`](tex/BUILD.md) - exact generation command and helper files.
- [`pdf/COMPLETE_PROOF_SELF_CONTAINED.pdf`](pdf/COMPLETE_PROOF_SELF_CONTAINED.pdf)
  - 27-page A4 PDF compiled with Tectonic 0.16.9.
- [`../COMPLETE_PROOF_SELF_CONTAINED.pdf`](../COMPLETE_PROOF_SELF_CONTAINED.pdf)
  - byte-identical convenience copy in the top level of `625/` for immediate
    GitHub viewing.

## Integrity

```text
9EA27F617D95DAFA42991A3CAF2ACBF3A4E92CA16CA25D524D7B587954D95A83  ../proofs/COMPLETE_PROOF_SELF_CONTAINED.md
D30987F28BF20556A633D0A78A10FFA240BC4977FF53E01A31FE08D27B396A94  ../sources/ERDOS625_REFERENCES.bib
AAF38D8134015EC9AEAD6FEA4916F618C4479F6601E1EB34F68A5134B0E1B82A  tex/COMPLETE_PROOF_SELF_CONTAINED.tex
2ACD9BA34A7104976C65A007DF5132668605AFACA7407516B290545CB0634357  pdf/COMPLETE_PROOF_SELF_CONTAINED.pdf
2ACD9BA34A7104976C65A007DF5132668605AFACA7407516B290545CB0634357  ../COMPLETE_PROOF_SELF_CONTAINED.pdf
```

## PDF quality assurance

- Compile exit code: 0.
- Page count and size: 27 pages, A4, unencrypted.
- Authorship: the title page and PDF Author field both read
  `Samuil Petkov & ChatGPT 5.6`.
- Statement styling: all 12 lemma statements appear in blue breakable boxes;
  Proposition 9.2 appears in a green box; proofs remain in normal page flow.
- Compile diagnostics: no overfull boxes, missing glyphs, or fatal errors;
  one cosmetic underfull-box warning in the final provenance filename list.
- Render check: all 27 pages rendered successfully at 120 DPI.
- Visual check: three nine-page contact sheets and full-size pages 5, 19--21,
  24--27
  inspected, including the title/contents, main theorem, short and long lemma
  boxes, repaired root corridor, global high-skeleton bridge, green
  proposition box, residual attachment argument, amplification, final
  theorem, in-text citations, and reference list.
- Text check: no blank pages, Unicode replacement characters, or `??`
  markers; all 12 lemma titles, Proposition 9.2, constant `200/153`, and the
  six-reference bibliography were detected.  The five unique external
  reference links are embedded in six clickable PDF annotations.
