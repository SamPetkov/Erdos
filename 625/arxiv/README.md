# Erdős 625: final v2 manuscript package

Prepared 14 October 2026 after a fresh independent GPT-6 Pro release recheck of each exact current manuscript. Both reports recommend author-managed v2 release and identify no mathematical blocker within their stated coverage. Two useful optional prose corrections per paper were independently checked and applied; the abstracts, theorem statements and displayed mathematics are unchanged by this final recheck.

The proof roadmap now places the amplification cost and completion of the deterministic gap in the sections that establish them. An unlabelled heading duplicating the adjacent proof heading has been removed.

- `main.pdf`: the current 52-page paper.
- `main.tex`: editable source.
- `Erdos625-v2-arxiv-upload.zip`: arXiv upload package; `Erdos625_source.zip` contains the same package.
- `MANIFEST.txt` and `SHA256SUMS`: current scoped inventory and digests for this directory; the ledger excludes itself.
- `arxiv-abstract.txt` and `arxiv-comments.txt`: separate submission metadata.

The upload ZIP contains exactly `main.tex`, `main.bbl`, `references.bib`, and `petkov-preprint.sty`. The exact extracted sources compiled successfully with pdfLaTeX, without warnings or errors, unresolved references/citations, box warnings or missing glyphs. All PDF fonts are embedded, and bookmarks plus coloured internal/external links are present. Both papers retain the same stylesheet.

## Formalization scope and evidence

Appendix H distinguishes the released full-sequence fixed-coefficient theorem and its tail-amplification route from the phase refinement and the complete written mean-positive-excess proof. The latter is not claimed as a separately released Lean theorem.

The author waived further Lean reruns and log retrieval on 13 October 2026. No new Lean run was performed in this recheck. The earlier fresh Procida replay's full completion remains unconfirmed after the SSH outage; its last retrieved corrected checkpoints were 67/195 WOW and 194/480 Erdős production modules, without observed failures. Archived source-identified compilation evidence remains historical. Unpublished endpoint patches, retired/vacuous modules and unimported templates are excluded from stronger coverage claims. No released Lean source or toolchain was changed in this publication, and no Lean was run on the PC in this recheck.

The fresh Pro reviews are mathematical/editorial checks with explicit coverage limits, not new kernel verification or proof certification. No new AI-detector score is claimed. No arXiv submission has been made; these packages are ready for the author's replacement submission.
