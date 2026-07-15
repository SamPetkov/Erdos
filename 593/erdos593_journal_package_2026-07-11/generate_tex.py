#!/usr/bin/env python3
"""Generate the journal-style LaTeX manuscript from the Markdown master."""
from __future__ import annotations

import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / "erdos593_obligatory_triple_systems.md"
BODY = ROOT / ".erdos593_body.tex"
OUTPUT = ROOT / "erdos593_obligatory_triple_systems.tex"

ENV = {
    "Theorem": "theorembox",
    "Lemma": "lemmabox",
    "Proposition": "propositionbox",
    "Corollary": "corollarybox",
    "Claim": "claimbox",
    "Definition": "definitionbox",
    "Remark": "remarkbox",
}

HEADING_RE = re.compile(
    r"^\\(?P<level>section|subsection|subsubsection|paragraph)\{(?P<kind>Theorem|Lemma|Proposition|Corollary|Claim|Definition|Remark)(?P<rest>.*)\}\\label\{(?P<label>[^}]*)\}$"
)
ANY_HEADING_RE = re.compile(r"^\\(?:section|subsection|subsubsection|paragraph)\{")
PROOF_RE = re.compile(r"^\\textbf\{Proof(?: strategy| of[^}]*)?\.\}", re.IGNORECASE)


def style_latex_theorems(body: str) -> str:
    lines = body.splitlines()
    out: list[str] = []
    i = 0
    while i < len(lines):
        m = HEADING_RE.match(lines[i])
        if not m:
            out.append(lines[i])
            i += 1
            continue
        kind = m.group("kind")
        title = f"{kind}{m.group('rest')}"
        env = ENV[kind]
        out.append(r"\phantomsection")
        out.append(rf"\label{{{m.group('label')}}}")
        out.append(rf"\begin{{{env}}}{{{title}}}")
        i += 1
        closed = False
        while i < len(lines):
            line = lines[i]
            if PROOF_RE.match(line):
                out.append(rf"\end{{{env}}}")
                out.append(line)
                i += 1
                closed = True
                break
            if ANY_HEADING_RE.match(line):
                out.append(rf"\end{{{env}}}")
                closed = True
                break
            out.append(line)
            i += 1
        if not closed:
            out.append(rf"\end{{{env}}}")
    return "\n".join(out) + "\n"


def run_pandoc() -> str:
    subprocess.run(
        [
            "pandoc",
            str(SOURCE),
            "--from=markdown+tex_math_dollars",
            "--to=latex",
            "--biblatex",
            f"--bibliography={ROOT / 'references.bib'}",
            "--wrap=none",
            "-o",
            str(BODY),
        ],
        check=True,
        cwd=ROOT,
    )
    body = BODY.read_text(encoding="utf-8")
    body = style_latex_theorems(body)

    body = re.sub(
        r"\\section\{Scope, provenance, and comparison\}\\label\{scope-provenance-and-comparison\}\s*",
        "",
        body,
        count=1,
    )
    body = body.replace(r"\subsection{Abstract}\label{abstract}", r"\begin{abstract}", 1)
    body = body.replace(
        r"\subsection{How arXiv:2606.24882 helps, and how the proofs differ}\label{how-arxiv2606.24882-helps-and-how-the-proofs-differ}",
        r"\end{abstract}" "\n"
        r"\noindent\textbf{Keywords.} obligatory triple systems; uncountable chromatic number; Levi graph; Berge cycle; one-point amalgamation.\par" "\n"
        r"\noindent\textbf{2020 Mathematics Subject Classification.} Primary 05C65, 05C15; Secondary 03E05, 05D10." "\n"
        r"\tableofcontents" "\n"
        r"\clearpage" "\n"
        r"\section{Comparison with arXiv:2606.24882}\label{comparison-with-arxiv}",
        1,
    )
    body = body.replace(
        r"\subsection{Dependency audit}\label{dependency-audit}",
        r"\section{Dependency audit}\label{dependency-audit}",
        1,
    )
    body = body.replace(
        r"\section{Source ledger}\label{source-ledger}",
        r"\clearpage\appendix\section{Source ledger}\label{source-ledger}",
        1,
    )
    return body


PREAMBLE = r'''\documentclass[11pt]{article}

\usepackage[a4paper,margin=28mm,headheight=15pt]{geometry}
\usepackage{amsmath,mathtools}
\usepackage{libertinus}
\usepackage{microtype}
\usepackage{booktabs,longtable,array,tabularx}
\usepackage{enumitem}
\usepackage{xcolor}
\usepackage[most]{tcolorbox}
\usepackage{fancyhdr}
\usepackage{xurl}
\usepackage{csquotes}
\usepackage[backend=biber,style=numeric-comp,sorting=nyt,maxbibnames=99,giveninits=true,doi=true,url=true,isbn=false]{biblatex}
\addbibresource{references.bib}
\AtBeginBibliography{\small}
\setlength{\bibitemsep}{0.30\baselineskip}
\usepackage{hyperref}
\usepackage{bookmark}

\definecolor{Navy}{HTML}{234A6F}
\definecolor{NavyLight}{HTML}{EEF4FA}
\definecolor{Forest}{HTML}{2F6B45}
\definecolor{ForestLight}{HTML}{EFF8F2}
\definecolor{Plum}{HTML}{6A4A7C}
\definecolor{PlumLight}{HTML}{F6F1F8}
\definecolor{Teal}{HTML}{176B6D}
\definecolor{TealLight}{HTML}{EEF8F8}
\definecolor{Amber}{HTML}{9A5A00}
\definecolor{AmberLight}{HTML}{FFF7E8}
\definecolor{Slate}{HTML}{4B5968}
\definecolor{SlateLight}{HTML}{F2F5F7}
\definecolor{Burgundy}{HTML}{7B3341}
\definecolor{BurgundyLight}{HTML}{FBF0F2}
\definecolor{LinkBlue}{HTML}{1B5A8A}

\hypersetup{
  pdftitle={Obligatory Triple Systems and Erdos Problem 593},
  pdfauthor={Journal-style working manuscript},
  pdfsubject={A self-contained proof with comparison to arXiv:2606.24882},
  pdfkeywords={obligatory triple systems, Erdos Problem 593, Levi graph, Berge cycle},
  colorlinks=true,
  linkcolor=Navy,
  citecolor=Forest,
  urlcolor=LinkBlue
}

\setlength{\parindent}{0pt}
\setlength{\parskip}{0.52em}
\setlist[itemize]{leftmargin=2.1em,itemsep=0.22em,topsep=0.35em}
\setlist[enumerate]{leftmargin=2.2em,itemsep=0.22em,topsep=0.35em}
\setcounter{tocdepth}{2}
\setcounter{secnumdepth}{0}
\renewcommand{\arraystretch}{1.15}
\setlength{\LTpre}{0.6em}
\setlength{\LTpost}{0.6em}
\emergencystretch=3em

\pagestyle{fancy}
\fancyhf{}
\fancyhead[L]{\small\sffamily Obligatory Triple Systems}
\fancyhead[R]{\small\sffamily 11 July 2026}
\fancyfoot[C]{\small\thepage}
\renewcommand{\headrulewidth}{0.35pt}

\newcommand{\tightlist}{\setlength{\itemsep}{0pt}\setlength{\parskip}{0pt}}
\providecommand{\passthrough}[1]{#1}
\providecommand{\square}{\mdlgwhtsquare}

\tcbset{
  journalbox/.style={
    enhanced,
    breakable,
    boxrule=0.75pt,
    arc=1.2mm,
    left=2.2mm,
    right=2.2mm,
    top=1.7mm,
    bottom=1.7mm,
    before skip=0.85em,
    after skip=0.85em,
    fonttitle=\bfseries\sffamily,
    coltitle=white,
    attach boxed title to top left={xshift=2.3mm,yshift=-1.9mm},
    boxed title style={arc=0.9mm,boxrule=0pt,left=1.8mm,right=1.8mm,top=0.7mm,bottom=0.7mm},
    drop fuzzy shadow=black!10
  }
}
\newtcolorbox{theorembox}[1]{journalbox,colback=NavyLight,colframe=Navy,boxed title style={colback=Navy},title={#1}}
\newtcolorbox{lemmabox}[1]{journalbox,colback=ForestLight,colframe=Forest,boxed title style={colback=Forest},title={#1}}
\newtcolorbox{propositionbox}[1]{journalbox,colback=PlumLight,colframe=Plum,boxed title style={colback=Plum},title={#1}}
\newtcolorbox{corollarybox}[1]{journalbox,colback=TealLight,colframe=Teal,boxed title style={colback=Teal},title={#1}}
\newtcolorbox{claimbox}[1]{journalbox,colback=AmberLight,colframe=Amber,boxed title style={colback=Amber},title={#1}}
\newtcolorbox{definitionbox}[1]{journalbox,colback=SlateLight,colframe=Slate,boxed title style={colback=Slate},title={#1}}
\newtcolorbox{remarkbox}[1]{journalbox,colback=BurgundyLight,colframe=Burgundy,boxed title style={colback=Burgundy},title={#1}}

\renewenvironment{quote}
  {\begin{tcolorbox}[breakable,colback=SlateLight,colframe=Slate!65,boxrule=0.5pt,arc=1mm,left=2mm,right=2mm,top=1.2mm,bottom=1.2mm]}
  {\end{tcolorbox}}

\title{\sffamily\bfseries Obligatory Triple Systems\\[0.3em]
\Large A self-contained proof of Erd\H{o}s Problem 593}
\author{Journal-style working manuscript}
\date{11 July 2026}

\begin{document}
\maketitle
\begin{center}
\small\itshape Compared against arXiv:2606.24882v1; not a transcription of that paper.
\end{center}
\vspace{0.6em}
'''

POSTAMBLE = r'''
\nocite{*}
\printbibliography[heading=bibintoc,title={References}]
\end{document}
'''


def main() -> None:
    body = run_pandoc()
    OUTPUT.write_text(PREAMBLE + body + POSTAMBLE, encoding="utf-8")
    BODY.unlink(missing_ok=True)
    print(OUTPUT)


if __name__ == "__main__":
    main()
