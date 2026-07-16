# Erdős Problem 593 arXiv package

The submission source is `main.tex`; bibliography data are in
`references.bib`. The generated `main.bbl` is included for arXiv
portability.

Build with:

```text
pdflatex main.tex
biber main
pdflatex main.tex
pdflatex main.tex
```

The manuscript carries the fixed manuscript date 11 July 2026. arXiv records
submission and version dates separately.
