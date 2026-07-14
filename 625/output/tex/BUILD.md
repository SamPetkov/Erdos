# Building the TeX and PDF manuscript

The tracked TeX file is generated from
[`../../proofs/COMPLETE_PROOF_SELF_CONTAINED.md`](../../proofs/COMPLETE_PROOF_SELF_CONTAINED.md)
with Pandoc 3.9.0.2.  From the repository root, run:

```powershell
pandoc 625/proofs/COMPLETE_PROOF_SELF_CONTAINED.md `
  -f markdown+tex_math_single_backslash+raw_tex `
  -t latex -s --ascii --eol=lf `
  --lua-filter=625/output/tex/pandoc_filter.lua `
  --include-in-header=625/output/tex/header.tex `
  --metadata title="A Self-Contained Proof of a Polynomial-Scale Gap Between the Chromatic and Cochromatic Numbers of a Random Graph" `
  --metadata subtitle="Candidate all-n solution to Erdős Problem 625; not externally peer reviewed" `
  --metadata author="Samuil Petkov & ChatGPT 5.6" `
  --metadata date="12 July 2026" `
  -V documentclass=article -V fontsize=11pt -V papersize=a4 `
  -V geometry:margin=1in -V colorlinks=true -V linkcolor=blue -V urlcolor=blue `
  --toc --toc-depth=1 `
  -o 625/output/tex/COMPLETE_PROOF_SELF_CONTAINED.tex
```

The repository copy was compiled with the Codex LaTeX plugin's Tectonic
driver.  Any conventional LaTeX installation with the packages named in the
generated preamble should also compile it.  The generated PDF is stored in
[`../pdf/COMPLETE_PROOF_SELF_CONTAINED.pdf`](../pdf/COMPLETE_PROOF_SELF_CONTAINED.pdf).

The Lua filter places each lemma statement in a blue, breakable box and the
normalized-second-moment proposition in a green box.  Proofs remain in the
ordinary page flow, so long arguments stay readable and page breaks remain
natural.  The styling changes presentation only; the canonical Markdown proof
is not modified.

The canonical Markdown contains readable author--date citations and a complete
reference list.  A reusable BibTeX mirror is maintained at
[`../../sources/ERDOS625_REFERENCES.bib`](../../sources/ERDOS625_REFERENCES.bib).
The generated TeX and PDF therefore remain self-contained and do not require a
separate bibliography-processing pass.

The status wording is intentionally conservative: the manuscript presents a
candidate solution backed by internal audits and exact finite checks, not a
claim of external peer review, publication, priority, or community acceptance.
