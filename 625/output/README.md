# Publication artifacts

This directory contains publication-oriented derivatives of the canonical
Markdown proof in
[`../proofs/COMPLETE_PROOF_SELF_CONTAINED.md`](../proofs/COMPLETE_PROOF_SELF_CONTAINED.md).
The derivatives do not change the theorem, proof text, or qualification as a
candidate solution that has not been externally peer reviewed.
The Markdown, TeX title page, and embedded PDF metadata attribute the
manuscript to **Samuil Petkov**.  The project documentation records its
development in collaboration with **ChatGPT 5.6**.

## Files

- [`tex/COMPLETE_PROOF_SELF_CONTAINED.tex`](tex/COMPLETE_PROOF_SELF_CONTAINED.tex)
  - standalone LF-normalized TeX generated with Pandoc 3.9.0.2.
- [`tex/BUILD.md`](tex/BUILD.md) - exact generation command and helper files.
- [`pdf/COMPLETE_PROOF_SELF_CONTAINED.pdf`](pdf/COMPLETE_PROOF_SELF_CONTAINED.pdf)
  - 30-page A4 PDF compiled with Tectonic 0.16.9.
- [`../COMPLETE_PROOF_SELF_CONTAINED.pdf`](../COMPLETE_PROOF_SELF_CONTAINED.pdf)
  - byte-identical convenience copy in the top level of `625/` for immediate
    GitHub viewing.

## Integrity

```text
8E6B9233684303426D2CC42FC92D2F238A53D82F2BE9EB63F31560B3B2E6241B  ../proofs/COMPLETE_PROOF_SELF_CONTAINED.md
6F4847F423409AD7ED5397BDF385F69A56EE908078382812D454D34FDA4BD1D4  ../sources/ERDOS625_REFERENCES.bib
CAB0A748309B9566E7AF3CB6A99ECBE939A901FB989F9392DDFD7451751D341E  tex/COMPLETE_PROOF_SELF_CONTAINED.tex
80004AB60B1504B24708B324E4E825E1843A2DF1AC560C9C49F1C0520727039E  pdf/COMPLETE_PROOF_SELF_CONTAINED.pdf
80004AB60B1504B24708B324E4E825E1843A2DF1AC560C9C49F1C0520727039E  ../COMPLETE_PROOF_SELF_CONTAINED.pdf
```

## PDF quality assurance

- Compile exit code: 0.
- Page count and size: 30 pages, A4, unencrypted.
- Authorship: the title page and PDF Author field both read `Samuil Petkov`;
  the project documentation records collaboration with `ChatGPT 5.6`.
- Statement styling: all 12 lemma statements appear in blue breakable boxes;
  Proposition 9.2 appears in a green box; proofs remain in normal page flow.
- Compile diagnostics: no fatal errors; the publication-layout preprint has a
  separate clean warning scan recorded in `../arxiv/README.md`.
- Render check: the updated title, attribution pages, main theorem, and first
  boxed lemma rendered successfully at 120 DPI.
- Visual check: the expanded Heckel provenance is legible and does not collide
  with the page header, theorem box, equations, or section boundary.
- Text check: no blank pages, Unicode replacement characters, or `??`
  markers; all 12 lemma titles, Proposition 9.2, constant `200/153`, and the
  eleven-reference bibliography were detected, including both requested
  Heckel papers and the Aristotle technical report.
