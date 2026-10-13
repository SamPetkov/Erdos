# Erdős 625 revised v2 manuscript

Current TeX and matching PDF, prepared 13 October 2026 after a separate GPT-6 Pro mathematical and editorial review. The review returned minor fixes; its specific release conditions were independently checked and addressed. No arXiv replacement has been submitted.

Download [main.pdf](main.pdf) (52 pages) or [Erdos625-v2-arxiv-upload.zip](Erdos625-v2-arxiv-upload.zip). The legacy archive name Erdos625_source.zip contains the same package. The main text occupies about 36.3 pages; supporting proofs, calculations and references account for the remainder. The shared preprint typography and coloured links are preserved.

Repaired two fixed-constant inequality chains: Appendix F now separates the Lipschitz constant from its absorption, and Proposition 8.8 uses the explicit multinomial endpoint factor proved below it. Clarified the completion indicator, ambient bipartite graph and capped cells, identified the finite tilt, removed repeated explanations and linked the frozen sharp-constant replay record. The main theorem, explicit coefficient, full integer sequence and uniform-phase quantifiers are retained.

This final-review pass records 11 replacements or relocations. Both abstracts are unchanged from the preceding release. Bibliography entries, style and assistance disclosures are retained. The review does not constitute a new formal verification, and the manuscript's precise Lean scope remains intact.

The upload ZIP contains main.tex, main.bbl, references.bib and petkov-preprint.sty at its root. Compile main.tex with pdflatex or latexmk -pdf. arxiv-abstract.txt and arxiv-comments.txt provide separate metadata. The exact extracted sources compile with PDFLaTeX/MiKTeX without warnings or errors; PDF fonts are embedded, with bookmarks and internal/external links.

The [version sent to the reviewer](https://github.com/SamPetkov/Erdos/tree/133836ad98d4922453eadc13fba858fb3933a04c/625/arxiv) is preserved in Git history.
