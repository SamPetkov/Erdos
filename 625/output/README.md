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
  - 25-page A4 PDF compiled with Tectonic 0.16.9.
- [`../COMPLETE_PROOF_SELF_CONTAINED.pdf`](../COMPLETE_PROOF_SELF_CONTAINED.pdf)
  - byte-identical convenience copy in the top level of `625/` for immediate
    GitHub viewing.

## Integrity

```text
4B9815B42F90E7F7A4044D64FB76A19AEBF4C296D6119A6AFECB73BFFB329164  ../proofs/COMPLETE_PROOF_SELF_CONTAINED.md
D30987F28BF20556A633D0A78A10FFA240BC4977FF53E01A31FE08D27B396A94  ../sources/ERDOS625_REFERENCES.bib
10B846C6B956B673AE9B7BBCF54766EC032F8AE50CD7BE20FE5CC0EE73C130D2  tex/COMPLETE_PROOF_SELF_CONTAINED.tex
5A832F3C41C8BD780743ABD28864516CCCD3DAA1904650C9C769D5CCBF7C4CFB  pdf/COMPLETE_PROOF_SELF_CONTAINED.pdf
5A832F3C41C8BD780743ABD28864516CCCD3DAA1904650C9C769D5CCBF7C4CFB  ../COMPLETE_PROOF_SELF_CONTAINED.pdf
```

## PDF quality assurance

- Compile exit code: 0.
- Page count and size: 25 pages, A4, unencrypted.
- Authorship: the title page and PDF Author field both read
  `Samuil Petkov & ChatGPT 5.6`.
- Statement styling: all 12 lemma statements appear in blue breakable boxes;
  Proposition 9.2 appears in a green box; proofs remain in normal page flow.
- Compile diagnostics: no overfull boxes, missing glyphs, or fatal errors;
  one cosmetic underfull-box warning in the final provenance filename list.
- Render check: all 25 pages rendered successfully at 144 DPI.
- Visual check: pages 1, 2, 3, 5, 8, 11, 13, 16, 20, 22, 23, and 25
  inspected, including the title/contents, main theorem, short and long lemma
  boxes, green proposition box, dense equations, display (7.12), residual
  attachment argument, in-text citations, and the final reference list.
- Text check: no blank pages, Unicode replacement characters, or `??`
  markers; all 12 lemma titles, Proposition 9.2, constant `200/153`, and the
  six-reference bibliography were detected.  All five external reference
  links are embedded as clickable PDF annotations.
