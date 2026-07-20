# arXiv preprints

This directory contains submission-oriented copies of the manuscripts for
Erdős Problems 593 and 625.

- `arxiv_593/`: self-contained TeX source, generated Markdown, and PDF.
- `arxiv_625/`: TeX source, bibliography, generated bibliography, Markdown,
  and PDF.
- `arxiv_593.pdf` and `arxiv_625.pdf`: convenient top-level copies.

Both PDFs carry the fixed manuscript date 20 July 2026. arXiv supplies separate
public submission and revision dates in its own record.

Regenerate and verify every mirror with:

```bash
python scripts/sync_arxiv_artifacts.py
```

The synchronization workflow checks authorship metadata, page size, embedded
fonts, bibliography mirrors, and byte-identical PDF copies. It does not modify
Lean source files.
