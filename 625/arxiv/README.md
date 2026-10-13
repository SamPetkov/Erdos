# Erdős 625 revised v2 manuscript

Current sources and matching PDF after two separate rounds of GPT-6 Pro review, prepared 13 October 2026. The completed reports were independently adjudicated before accepting changes. No arXiv replacement has been submitted.

Download [main.pdf](main.pdf) (52 pages) or [Erdos625-v2-arxiv-upload.zip](Erdos625-v2-arxiv-upload.zip). The legacy archive Erdos625_source.zip contains the same package. Main text: about 36.3 pages, with supporting material and references following. Shared preprint typography and coloured links are preserved.

This round records 7 source changes:

- Retain the original attribution and give a verified theorem locator for the one-sided inequality.
- Use the verified 1998 theorem locator in the amplification proof.
- Identify the two established bounds used to obtain the global endpoint-table sum.
- Distinguish the exact finite-support tilt from its limiting Gaussian-score tilt.
- Name the fixed interval that makes the Lipschitz constant uniform.
- Specify which indicator is dropped and why the expectation can only increase.
- Remove the repeated explanation of the selected number of parts.

The principal conclusions and their exact graph/phase hypotheses are retained. The review is not a proof certification or new Lean replay; the manuscript retains its precise formal-verification scope and assistance disclosure.

The four-file ZIP contains main.tex, main.bbl, references.bib and petkov-preprint.sty at its root. Compile main.tex with pdflatex or latexmk -pdf. Separate abstract and comments metadata are provided. The exact upload sources compile without warnings or errors; the PDF has embedded fonts, bookmarks and internal/external links.

The [version submitted for this review](https://github.com/SamPetkov/Erdos/tree/60547b426132228be2fae3ce20106efd85eefaac/625/arxiv) remains in Git history.
