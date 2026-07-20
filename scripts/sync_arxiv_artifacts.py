#!/usr/bin/env python3
"""Synchronize the public Erdős 593 and 625 manuscript artifacts.

Authoritative publication sources:

* Erdős 593: ``arxiv_preprints/arxiv_593/main.tex``
* Erdős 625: ``625/arxiv/main.tex``

The script normalizes sole-author metadata, updates publication bibliography
records, regenerates Markdown and PDF outputs, and copies all public mirrors.
It never reads or modifies a ``.lean`` file.
"""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parents[1]

P593_DIR = ROOT / "arxiv_preprints" / "arxiv_593"
P593_TEX = P593_DIR / "main.tex"
P593_MD = P593_DIR / "main.md"
P593_PDF = P593_DIR / "main.pdf"

P625_DIR = ROOT / "625" / "arxiv"
P625_TEX = P625_DIR / "main.tex"
P625_MD = P625_DIR / "main.md"
P625_PDF = P625_DIR / "main.pdf"
P625_BIB = P625_DIR / "references.bib"
P625_BBL = P625_DIR / "main.bbl"

SOLE_AUTHOR = "Samuil Petkov"


def run(command: list[str], *, cwd: Path | None = None, env: dict[str, str] | None = None) -> None:
    subprocess.run(command, cwd=cwd, env=env, check=True)


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8", newline="\n")


def copy_file(source: Path, destination: Path) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, destination)


def replace_first_author_command(text: str) -> str:
    text = re.sub(
        r"^\\author(?:\[[^\]]*\])?\{.*?\}\s*$",
        rf"\\author[{SOLE_AUTHOR}]{{{SOLE_AUTHOR}}}",
        text,
        count=1,
        flags=re.MULTILINE,
    )
    return text


def normalize_593_tex(text: str) -> str:
    text = re.sub(r"^\\author\{.*?\}\s*$", rf"\\author{{{SOLE_AUTHOR}}}", text, count=1, flags=re.MULTILINE)
    text = re.sub(r"^\\address\{.*?\}\s*\n?", "", text, flags=re.MULTILINE)
    text = re.sub(r"^\\email\{.*?\}\s*\n?", "", text, flags=re.MULTILINE)
    text = text.replace("Samuil Pekov", SOLE_AUTHOR).replace("Samuil Petkob", SOLE_AUTHOR)
    text = text.replace(
        "\\newblock Accepted for publication; arXiv:2403.11223.\n",
        "\\newblock arXiv:2403.11223.\n",
    )
    required = [
        "Obligatory Triple Systems: An Alternative Proof",
        "first publicly posted complete classification",
        "no claim of informational independence",
        "complete Lean formalisation",
    ]
    missing = [needle for needle in required if needle not in text]
    if missing:
        raise RuntimeError(f"Erdős 593 canonical TeX is missing required wording: {missing}")
    forbidden = [
        "The proof here is self-contained and does not use that manuscript",
        "The proof presented here was developed without consulting Li's manuscript",
        "No statement or argument from Li's preprint is used in the proof",
        "Samuil Petkov & ChatGPT",
        "Samuil Petkov and ChatGPT",
    ]
    hits = [needle for needle in forbidden if needle in text]
    if hits:
        raise RuntimeError(f"Erdős 593 canonical TeX contains stale wording: {hits}")
    return text


def normalize_625_tex(text: str) -> str:
    text = replace_first_author_command(text)
    text = re.sub(r"pdfauthor=\{.*?\}", f"pdfauthor={{{SOLE_AUTHOR}}}", text, count=1)
    text = re.sub(r"^\\date\{.*?\}\s*$", r"\\date{20 July 2026}", text, count=1, flags=re.MULTILINE)
    text = text.replace("Samuil Pekov", SOLE_AUTHOR).replace("Samuil Petkob", SOLE_AUTHOR)
    if "A Polynomial-Scale Gap Between the Chromatic and Cochromatic Numbers of a Random Graph" not in text:
        raise RuntimeError("Erdős 625 canonical title changed unexpectedly")
    if r"\author[Samuil Petkov]{Samuil Petkov}" not in text:
        raise RuntimeError("Erdős 625 canonical author metadata is not sole-author Samuil Petkov")
    return text


def update_steiner_bibliography(text: str) -> str:
    replacement = r"""@article{steiner-2024,
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
    pattern = re.compile(r"@misc\{steiner-2024,.*?\n\}\n", re.DOTALL)
    updated, count = pattern.subn(replacement, text, count=1)
    if count != 1:
        # Remain idempotent after the first run.
        pattern = re.compile(r"@article\{steiner-2024,.*?\n\}\n", re.DOTALL)
        updated, count = pattern.subn(replacement, text, count=1)
    if count != 1:
        raise RuntimeError("could not locate the Steiner bibliography entry")
    return updated


def compile_latex(tex_path: Path, output_pdf: Path, *, bib_path: Path | None = None, output_bbl: Path | None = None, epoch: str) -> None:
    with tempfile.TemporaryDirectory(prefix=f"{tex_path.stem}-latex-") as tmp:
        build = Path(tmp)
        shutil.copy2(tex_path, build / tex_path.name)
        if bib_path is not None:
            shutil.copy2(bib_path, build / bib_path.name)
        env = os.environ.copy()
        env.update({"TZ": "UTC", "SOURCE_DATE_EPOCH": epoch, "FORCE_SOURCE_DATE": "1"})
        run(
            [
                "latexmk",
                "-pdf",
                "-interaction=nonstopmode",
                "-halt-on-error",
                "-file-line-error",
                tex_path.name,
            ],
            cwd=build,
            env=env,
        )
        copy_file(build / f"{tex_path.stem}.pdf", output_pdf)
        if output_bbl is not None:
            bbl = build / f"{tex_path.stem}.bbl"
            if not bbl.exists():
                raise RuntimeError(f"expected bibliography output was not generated: {bbl}")
            copy_file(bbl, output_bbl)


def generate_markdown(tex_path: Path, output_path: Path, *, title: str, date: str, bibliography: Path | None = None) -> None:
    with tempfile.TemporaryDirectory(prefix=f"{tex_path.stem}-pandoc-") as tmp:
        raw = Path(tmp) / "raw.md"
        command = [
            "pandoc",
            str(tex_path),
            "--from=latex",
            "--to=gfm+tex_math_dollars",
            "--wrap=none",
            "--markdown-headings=atx",
            "--output",
            str(raw),
        ]
        if bibliography is not None:
            command.extend(["--citeproc", "--bibliography", str(bibliography)])
        run(command, cwd=ROOT)
        body = raw.read_text(encoding="utf-8")

    body = body.replace("Samuil Pekov", SOLE_AUTHOR).replace("Samuil Petkob", SOLE_AUTHOR)
    body = re.sub(rf"^#?\s*{re.escape(title)}\s*\n+", "", body, count=1)
    header = f"# {title}\n\n**{SOLE_AUTHOR}**  \n{date}\n\n"
    write_text(output_path, header + body.lstrip())


def patch_authorship_docs() -> None:
    paths = [
        ROOT / "625" / "README.md",
        ROOT / "625" / "FINAL_VERIFICATION.md",
        ROOT / "625" / "output" / "README.md",
        ROOT / "625" / "output" / "tex" / "BUILD.md",
        ROOT / "625" / "formalization" / "README.md",
        ROOT / "625" / "proofs" / "COMPLETE_PROOF_SELF_CONTAINED.md",
    ]
    replacements = {
        "**Authors:** Samuil Petkov & ChatGPT 5.6": "**Author:** Samuil Petkov",
        "**Authors:** Samuil Petkov & ChatGPT-5.6": "**Author:** Samuil Petkov",
        "authored by **Samuil Petkov & ChatGPT 5.6**": "authored by **Samuil Petkov** and developed with disclosed AI assistance",
        "authored by **Samuil Petkov & ChatGPT-5.6**": "authored by **Samuil Petkov** and developed with disclosed AI assistance",
        "--metadata author=\"Samuil Petkov & ChatGPT 5.6\"": "--metadata author=\"Samuil Petkov\"",
        "displays `Samuil Petkov & ChatGPT 5.6`": "displays `Samuil Petkov`",
        "contains the same attribution": "contains the same author metadata",
    }
    for path in paths:
        if not path.exists():
            continue
        text = path.read_text(encoding="utf-8")
        for old, new in replacements.items():
            text = text.replace(old, new)
        text = text.replace("Samuil Pekov", SOLE_AUTHOR).replace("Samuil Petkob", SOLE_AUTHOR)
        write_text(path, text)

    proof_tex = ROOT / "625" / "output" / "tex" / "COMPLETE_PROOF_SELF_CONTAINED.tex"
    if proof_tex.exists():
        text = proof_tex.read_text(encoding="utf-8")
        text = re.sub(r"^\\author\{.*?\}\s*$", rf"\\author{{{SOLE_AUTHOR}}}", text, count=1, flags=re.MULTILINE)
        text = text.replace("Samuil Petkov \\& ChatGPT 5.6", SOLE_AUTHOR)
        text = text.replace("Samuil Petkov & ChatGPT 5.6", SOLE_AUTHOR)
        text = text.replace("Samuil Pekov", SOLE_AUTHOR).replace("Samuil Petkob", SOLE_AUTHOR)
        write_text(proof_tex, text)


def compile_internal_625_proof() -> None:
    tex = ROOT / "625" / "output" / "tex" / "COMPLETE_PROOF_SELF_CONTAINED.tex"
    if not tex.exists():
        return
    pdf = ROOT / "625" / "output" / "pdf" / "COMPLETE_PROOF_SELF_CONTAINED.pdf"
    compile_latex(tex, pdf, epoch="1784548800")
    copy_file(pdf, ROOT / "625" / "COMPLETE_PROOF_SELF_CONTAINED.pdf")


def make_zip(path: Path, files: list[tuple[Path, str]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(path, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for source, arcname in files:
            if source.exists():
                archive.write(source, arcname)


def sync_593() -> None:
    text = normalize_593_tex(P593_TEX.read_text(encoding="utf-8"))
    write_text(P593_TEX, text)
    compile_latex(P593_TEX, P593_PDF, epoch="1784548800")
    generate_markdown(
        P593_TEX,
        P593_MD,
        title="Obligatory Triple Systems: An Alternative Proof",
        date="20 July 2026",
    )

    tex_mirrors = [ROOT / "arxiv_preprints" / "Erdos593_revised.tex"]
    md_mirrors = [ROOT / "arxiv_preprints" / "Erdos593_revised.md"]
    pdf_mirrors = [ROOT / "arxiv_preprints" / "arxiv_593.pdf"]
    for destination in tex_mirrors:
        copy_file(P593_TEX, destination)
    for destination in md_mirrors:
        copy_file(P593_MD, destination)
    for destination in pdf_mirrors:
        copy_file(P593_PDF, destination)

    make_zip(
        ROOT / "arxiv_preprints" / "Erdos593_revised_source.zip",
        [
            (P593_TEX, "main.tex"),
            (P593_MD, "main.md"),
        ],
    )


def sync_625() -> None:
    write_text(P625_TEX, normalize_625_tex(P625_TEX.read_text(encoding="utf-8")))
    write_text(P625_BIB, update_steiner_bibliography(P625_BIB.read_text(encoding="utf-8")))
    compile_latex(P625_TEX, P625_PDF, bib_path=P625_BIB, output_bbl=P625_BBL, epoch="1784548800")
    generate_markdown(
        P625_TEX,
        P625_MD,
        title="A Polynomial-Scale Gap Between the Chromatic and Cochromatic Numbers of a Random Graph",
        date="20 July 2026",
        bibliography=P625_BIB,
    )

    mirror_dir = ROOT / "arxiv_preprints" / "arxiv_625"
    for source, destination in [
        (P625_TEX, mirror_dir / "main.tex"),
        (P625_MD, mirror_dir / "main.md"),
        (P625_PDF, mirror_dir / "main.pdf"),
        (P625_BIB, mirror_dir / "references.bib"),
        (P625_BBL, mirror_dir / "main.bbl"),
        (P625_TEX, ROOT / "arxiv_preprints" / "Erdos625_revised.tex"),
        (P625_MD, ROOT / "arxiv_preprints" / "Erdos625_revised.md"),
        (P625_PDF, ROOT / "arxiv_preprints" / "arxiv_625.pdf"),
    ]:
        copy_file(source, destination)

    make_zip(
        ROOT / "arxiv_preprints" / "Erdos625_revised_source.zip",
        [
            (P625_DIR / "README.md", "README.md"),
            (P625_TEX, "main.tex"),
            (P625_MD, "main.md"),
            (P625_BBL, "main.bbl"),
            (P625_BIB, "references.bib"),
        ],
    )


def validate() -> None:
    publication_texts = [
        P593_TEX,
        P593_MD,
        ROOT / "arxiv_preprints" / "Erdos593_revised.tex",
        ROOT / "arxiv_preprints" / "Erdos593_revised.md",
        P625_TEX,
        P625_MD,
        ROOT / "arxiv_preprints" / "Erdos625_revised.tex",
        ROOT / "arxiv_preprints" / "Erdos625_revised.md",
        ROOT / "625" / "output" / "tex" / "COMPLETE_PROOF_SELF_CONTAINED.tex",
        ROOT / "625" / "proofs" / "COMPLETE_PROOF_SELF_CONTAINED.md",
    ]
    author_forbidden = [
        "Samuil Pekov",
        "Samuil Petkob",
        "Samuil Petkov & ChatGPT 5.6",
        "Samuil Petkov \\& ChatGPT 5.6",
        "Samuil Petkov and ChatGPT 5.6",
    ]
    stale_593 = [
        "The proof here is self-contained and does not use that manuscript",
        "The proof presented here was developed without consulting Li's manuscript",
        "No statement or argument from Li's preprint is used in the proof",
    ]
    for path in publication_texts:
        if not path.exists():
            continue
        text = path.read_text(encoding="utf-8")
        hits = [needle for needle in author_forbidden if needle in text]
        if hits:
            raise RuntimeError(f"{path.relative_to(ROOT)} contains obsolete coauthor metadata: {hits}")
        if "593" in str(path):
            hits = [needle for needle in stale_593 if needle in text]
            if hits:
                raise RuntimeError(f"{path.relative_to(ROOT)} contains stale priority wording: {hits}")

    if "journal       = {SIAM Journal on Discrete Mathematics}" not in P625_BIB.read_text(encoding="utf-8"):
        raise RuntimeError("Steiner journal metadata was not refreshed")


def synchronize() -> None:
    patch_authorship_docs()
    sync_593()
    sync_625()
    compile_internal_625_proof()
    validate()


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    synchronize()
    if args.check:
        run(["git", "diff", "--exit-code", "--", "."], cwd=ROOT)
