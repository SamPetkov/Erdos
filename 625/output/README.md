# Publication artifacts

This directory contains publication-oriented derivatives of the canonical
Markdown proof in
[`../proofs/COMPLETE_PROOF_SELF_CONTAINED.md`](../proofs/COMPLETE_PROOF_SELF_CONTAINED.md).
The derivatives do not change the theorem, proof text, or qualification as a
candidate solution that has not been externally peer reviewed.

## Files

- [`tex/COMPLETE_PROOF_SELF_CONTAINED.tex`](tex/COMPLETE_PROOF_SELF_CONTAINED.tex)
  - standalone LF-normalized TeX generated with Pandoc 3.9.0.2.
- [`tex/BUILD.md`](tex/BUILD.md) - exact generation command and helper files.
- [`pdf/COMPLETE_PROOF_SELF_CONTAINED.pdf`](pdf/COMPLETE_PROOF_SELF_CONTAINED.pdf)
  - 25-page A4 PDF compiled with Tectonic 0.16.9.

## Integrity

```text
53B2ADCCD64133991F3DCDCAA9F8E8820F38A12C982CC5735F96568DD014A190  ../proofs/COMPLETE_PROOF_SELF_CONTAINED.md
98EB7134512D65457D742DEDBBCE18F3E970B9024F184E60F0370B847D197AAD  tex/COMPLETE_PROOF_SELF_CONTAINED.tex
8595B63DF459B57CCC56CAD0E81EB0BFBC8229BA383C47E83479EB45BFF8C557  pdf/COMPLETE_PROOF_SELF_CONTAINED.pdf
```

## PDF quality assurance

- Compile exit code: 0.
- Page count and size: 25 pages, A4, unencrypted.
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
