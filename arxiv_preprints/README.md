# arXiv preprints

This directory contains submission-oriented copies of the manuscripts for
Erdős Problems 593 and 625.

- `arxiv_593/`: self-contained TeX source, generated Markdown, and PDF.
- `arxiv_625/`: TeX source, bibliography, generated bibliography, Markdown,
  and PDF.
- `arxiv_593.pdf` and `arxiv_625.pdf`: convenient top-level copies.

The Problem 593 PDF carries the fixed manuscript date 21 July 2026; the Problem
625 PDF remains dated 20 July 2026. arXiv supplies separate public submission
and revision dates in its own record.

Regenerate and verify every mirror with:

```bash
python scripts/sync_arxiv_artifacts.py
python scripts/refresh_internal_proof_metadata.py
```

The synchronization workflow checks authorship metadata, page size, embedded
fonts, bibliography mirrors, current publication citations, and byte-identical
PDF copies. Markdown generation is pinned to Pandoc 3.1.3. It does not modify
Lean source files.
