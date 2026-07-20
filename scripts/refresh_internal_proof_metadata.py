#!/usr/bin/env python3
"""Refresh the sole-author internal Problem 625 proof artifact.

This script keeps the internal proof dossier aligned with the publication
manuscript without changing any Lean source.  It updates the manuscript date,
the published Steiner citation, the bibliography maintenance mirror, and the
verification scope note, then recompiles the existing A4 proof layout.
"""

from __future__ import annotations

import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PROOF_MD = ROOT / "625" / "proofs" / "COMPLETE_PROOF_SELF_CONTAINED.md"
PROOF_TEX = ROOT / "625" / "output" / "tex" / "COMPLETE_PROOF_SELF_CONTAINED.tex"
PROOF_PDF = ROOT / "625" / "output" / "pdf" / "COMPLETE_PROOF_SELF_CONTAINED.pdf"
PROOF_PDF_MIRROR = ROOT / "625" / "COMPLETE_PROOF_SELF_CONTAINED.pdf"
SOURCE_BIB = ROOT / "625" / "sources" / "ERDOS625_REFERENCES.bib"
BUILD_MD = ROOT / "625" / "output" / "tex" / "BUILD.md"
DOSSIER_README = ROOT / "625" / "README.md"
FINAL_VERIFICATION = ROOT / "625" / "FINAL_VERIFICATION.md"

SOLE_AUTHOR = "Samuil Petkov"
REVISION_DATE = "20 July 2026"

STEINER_BIB = r"""@article{steiner-2024,
  author        = {Steiner, Raphael},
  title         = {On the Difference Between the Chromatic and Cochromatic Number},
  journal       = {SIAM Journal on Discrete Mathematics},
  volume        = {39},
  number        = {4},
  pages         = {2268--2274},
  year          = {2025},
  doi           = {10.1137/24M1715180},
  url           = {https://doi.org/10.1137/24M1715180},
  eprint        = {2408.02400},
  archiveprefix = {arXiv},
  primaryclass  = {math.CO},
  note          = {Published online 17 November 2025; arXiv:2408.02400}
}
"""

STEINER_MD_OLD = """8. R. Steiner, \"On the Difference Between the Chromatic and Cochromatic
   Number,\" arXiv:2408.02400v2 [math.CO], 2024.
   <https://arxiv.org/abs/2408.02400>.
"""

STEINER_MD_NEW = """8. R. Steiner, \"On the Difference Between the Chromatic and Cochromatic
   Number,\" *SIAM Journal on Discrete Mathematics* **39**(4) (2025),
   2268--2274. <https://doi.org/10.1137/24M1715180>.
   Published online 17 November 2025; arXiv:2408.02400.
"""

STEINER_TEX_REPLACEMENT = r"""R. Steiner, ``On the Difference Between the Chromatic and Cochromatic
  Number,'' \emph{SIAM Journal on Discrete Mathematics} \textbf{39}(4)
  (2025), 2268--2274. \url{https://doi.org/10.1137/24M1715180}.
  Published online 17 November 2025; arXiv:2408.02400."""

SYNC_NOTE = """## 2026-07-20 publication synchronization

The sole-author TeX, Markdown, bibliography, and PDF publication artifacts were
regenerated on 20 July 2026.  The manuscript and PDF metadata name **Samuil
Petkov** as the sole author; AI systems remain disclosed as assistance rather
than coauthors.  The current publication artifacts are verified by the
`arXiv artifact synchronization` workflow.  Historical hashes and audit verdicts
below remain scoped to the bytes and dates explicitly stated in their original
records.

"""


def write(path: Path, text: str) -> None:
    path.write_text(text, encoding="utf-8", newline="\n")


def update_bib() -> None:
    text = SOURCE_BIB.read_text(encoding="utf-8")
    pattern = re.compile(r"@(misc|article)\{steiner-2024,.*?\n\}\n", re.DOTALL)
    text, count = pattern.subn(STEINER_BIB, text, count=1)
    if count != 1:
        raise RuntimeError("could not locate Steiner in the source bibliography")
    write(SOURCE_BIB, text)


def update_proof_markdown() -> None:
    text = PROOF_MD.read_text(encoding="utf-8")
    text = text.replace("**Date:** 12 July 2026", f"**Date:** {REVISION_DATE}")
    text = text.replace("Steiner (2024)", "Steiner (2025)")
    if STEINER_MD_OLD in text:
        text = text.replace(STEINER_MD_OLD, STEINER_MD_NEW)
    elif "10.1137/24M1715180" not in text:
        raise RuntimeError("could not refresh the Steiner reference in the proof Markdown")
    text = text.replace("Samuil Pekov", SOLE_AUTHOR).replace("Samuil Petkob", SOLE_AUTHOR)
    write(PROOF_MD, text)


def update_proof_tex() -> None:
    text = PROOF_TEX.read_text(encoding="utf-8")
    text = re.sub(r"^\\date\{.*?\}\s*$", rf"\\date{{{REVISION_DATE}}}", text, count=1, flags=re.MULTILINE)
    text = text.replace("Steiner (2024)", "Steiner (2025)")
    pattern = re.compile(
        r"R\. Steiner, ``On the Difference Between the Chromatic and Cochromatic\s+"
        r"Number,'' arXiv:2408\.02400v2 \{\[\}math\.CO\{\]\}, 2024\.\s+"
        r"\\url\{https://arxiv\.org/abs/2408\.02400\}\.",
        re.DOTALL,
    )
    text, count = pattern.subn(STEINER_TEX_REPLACEMENT, text, count=1)
    if count != 1 and "10.1137/24M1715180" not in text:
        raise RuntimeError("could not refresh the Steiner reference in the proof TeX")
    text = text.replace("Samuil Pekov", SOLE_AUTHOR).replace("Samuil Petkob", SOLE_AUTHOR)
    write(PROOF_TEX, text)


def update_build_docs() -> None:
    if BUILD_MD.exists():
        text = BUILD_MD.read_text(encoding="utf-8")
        text = text.replace('--metadata date="12 July 2026"', f'--metadata date="{REVISION_DATE}"')
        write(BUILD_MD, text)

    if DOSSIER_README.exists():
        text = DOSSIER_README.read_text(encoding="utf-8")
        text = text.replace("The publication-layout PDF is dated 12 July 2026", f"The publication-layout PDF is dated {REVISION_DATE}")
        write(DOSSIER_README, text)

    if FINAL_VERIFICATION.exists():
        text = FINAL_VERIFICATION.read_text(encoding="utf-8")
        marker = "## 2026-07-20 publication synchronization"
        if marker not in text:
            title = "# Final internal verification record\n\n"
            if not text.startswith(title):
                raise RuntimeError("unexpected final-verification header")
            text = title + SYNC_NOTE + text[len(title):]
        write(FINAL_VERIFICATION, text)


def compile_pdf() -> None:
    with tempfile.TemporaryDirectory(prefix="erdos625-internal-") as tmp:
        build = Path(tmp)
        local_tex = build / PROOF_TEX.name
        shutil.copy2(PROOF_TEX, local_tex)
        env = os.environ.copy()
        env.update(
            {
                "TZ": "UTC",
                "SOURCE_DATE_EPOCH": "1784548800",
                "FORCE_SOURCE_DATE": "1",
            }
        )
        subprocess.run(
            [
                "latexmk",
                "-pdf",
                "-interaction=nonstopmode",
                "-halt-on-error",
                "-file-line-error",
                local_tex.name,
            ],
            cwd=build,
            env=env,
            check=True,
        )
        PROOF_PDF.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(build / f"{PROOF_TEX.stem}.pdf", PROOF_PDF)
        shutil.copy2(PROOF_PDF, PROOF_PDF_MIRROR)


def validate() -> None:
    for path in [PROOF_MD, PROOF_TEX, SOURCE_BIB, BUILD_MD, DOSSIER_README]:
        if not path.exists():
            continue
        text = path.read_text(encoding="utf-8")
        if "Samuil Petkov & ChatGPT" in text or "Samuil Petkov \\& ChatGPT" in text:
            raise RuntimeError(f"obsolete coauthor metadata remains in {path.relative_to(ROOT)}")
    for path in [PROOF_MD, PROOF_TEX, SOURCE_BIB]:
        if "10.1137/24M1715180" not in path.read_text(encoding="utf-8"):
            raise RuntimeError(f"published Steiner citation missing from {path.relative_to(ROOT)}")
    if REVISION_DATE not in PROOF_MD.read_text(encoding="utf-8"):
        raise RuntimeError("internal proof Markdown date was not refreshed")
    if rf"\date{{{REVISION_DATE}}}" not in PROOF_TEX.read_text(encoding="utf-8"):
        raise RuntimeError("internal proof TeX date was not refreshed")


def main() -> None:
    update_bib()
    update_proof_markdown()
    update_proof_tex()
    update_build_docs()
    compile_pdf()
    validate()


if __name__ == "__main__":
    main()
