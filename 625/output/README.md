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
A0AAC63A6C1B470C76A389753140953E40D6A8B8CB6625DC9C6203A6477B336D  ../proofs/COMPLETE_PROOF_SELF_CONTAINED.md
F7BDC5AD95A6C20B82E952A805162B0D6E9A69D8C88BEABD3B57D07B6B69EE3D  tex/COMPLETE_PROOF_SELF_CONTAINED.tex
9CAC00FB7654E9B2E452D27C447984536651380DCC263F83443B7F943A4030EC  pdf/COMPLETE_PROOF_SELF_CONTAINED.pdf
9CAC00FB7654E9B2E452D27C447984536651380DCC263F83443B7F943A4030EC  ../COMPLETE_PROOF_SELF_CONTAINED.pdf
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
