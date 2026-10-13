# Erdős 625 revised v2 manuscript

Current reviewed v2 sources and PDF, prepared 13 October 2026. This prepares an arXiv replacement; no replacement has been submitted.

Download [main.pdf](main.pdf) (53 pages) or [Erdos625-v2-arxiv-upload.zip](Erdos625-v2-arxiv-upload.zip). The legacy archive name Erdos625_source.zip contains the same current package.

The uniform gap comes before the phase refinement. The central overlap estimate is explained in the main text, the local-ratio lemma names its numerator precisely, and the final amplification application uses the mean bound and Markov’s inequality. Matching notation is consistent.

The source archive contains main.tex, main.bbl, references.bib and petkov-preprint.sty at its root. Compile main.tex with pdflatex (or latexmk -pdf); keep the supplied bibliography. arxiv-abstract.txt and arxiv-comments.txt provide separate metadata for the replacement form. Both papers use the same preprint style with coloured links.

The exact upload sources were compiled with PDFLaTeX/MiKTeX. The final logs contain no LaTeX warnings or errors, the fonts are embedded, and package contents match the compiled inputs. These checks support reproducibility; they do not constitute a complete formal verification of the manuscripts.

[Manuscript before this review pass](https://github.com/SamPetkov/Erdos/tree/3ab76e5a5066e5ddeff132d5e9777b6965cc6ea2/625/arxiv) is preserved in Git history.
