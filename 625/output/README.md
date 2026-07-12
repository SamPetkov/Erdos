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

## Integrity

```text
6C67D07E3146467386CAB0D536F86458E50DAA4A1D368BFC06058B750701B884  ../proofs/COMPLETE_PROOF_SELF_CONTAINED.md
A25F3B4ECD7F99B9FE72A64DE6D4F6116746869BF767F661268182DEABE6E357  tex/COMPLETE_PROOF_SELF_CONTAINED.tex
F418098173C8FAF27893972BA4A5932FDA3483C54560A0A5641764DD46B5A840  pdf/COMPLETE_PROOF_SELF_CONTAINED.pdf
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
  attachment argument, and final provenance note.
- Text check: no blank pages, Unicode replacement characters, or `??`
  markers; all 12 lemma titles, Proposition 9.2, constant `200/153`, and the
  final section were detected.
