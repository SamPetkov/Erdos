# Erdős 625 revised v2 manuscript

Current reviewed v2 sources and PDF, prepared 13 October 2026, with a shorter main text. This prepares an arXiv replacement; none has been submitted.

Download [main.pdf](main.pdf) (52 pages) or [Erdos625-v2-arxiv-upload.zip](Erdos625-v2-arxiv-upload.zip). The legacy archive name Erdos625_source.zip contains the same package.

The main text occupies about 36.3 pages, down from 40.7. The long uniform-root proof, profile-rounding estimates and optional explicit amplification tail bound are in Appendices A–C. The mean-excess route used by the main theorem remains in Section 10, including its complete vertex-exposure argument. Complete mathematical arguments remain in the PDF, so the total page count stays 52.

The archive contains main.tex, main.bbl, references.bib and petkov-preprint.sty at the root. Compile main.tex using pdflatex or latexmk -pdf. arxiv-abstract.txt and arxiv-comments.txt provide separate metadata. The shared preprint sizing and coloured links are preserved.

The exact extracted upload sources compile with PDFLaTeX/MiKTeX without warnings or errors. The 26 theorem-like statements, abstracts, citations and display equations were checked against the preceding reviewed version. In 625, one repeated expectation-bound display was removed and arbitrary parameters in the shared amplification proof were renamed. WOW's bibliography entries are unchanged; their generated order follows the new citation order. These checks do not claim a new formal verification or detector score.

[Before the main-text shortening](https://github.com/SamPetkov/Erdos/tree/e00edd897214fb518e916e34e618f7aa73118cf2/625/arxiv) is preserved in Git history.
