#!/usr/bin/env python3
"""Generate the complete AMS Version 3 manuscript body.

The canonical TeX remains frozen while the proof is incomplete. This script
extracts the complete Sections 1--7 and 10 from that source, converts their
legacy theorem and proof markup to the ordinary AMS hierarchy, applies a small
set of line-audited prose normalizations, and inserts the replacement Sections
8, 9, and 11. The canonical Git-blob SHA is checked before line-independent
section markers are used.
"""

from __future__ import annotations

import argparse
import hashlib
import re
from pathlib import Path


EXPECTED_CANONICAL_BLOB = "c4d090b73cd5efcdb98cc30f79bb5f53c6c9bc97"

START_SECTION_1 = r"\section{Notation and elementary"
START_SECTION_8 = r"\section{Canonical high cells and dense endpoint"
START_SECTION_10 = r"\section{Rare-event amplification}"
START_SECTION_11 = r"\section{Completion of the proof}"


def git_blob_sha(raw: bytes) -> str:
    header = f"blob {len(raw)}\0".encode("ascii")
    return hashlib.sha1(header + raw).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def slice_between(text: str, start: str, end: str) -> str:
    begin = text.find(start)
    finish = text.find(end)
    require(begin >= 0, f"missing start marker: {start}")
    require(finish >= 0, f"missing end marker: {end}")
    require(begin < finish, f"reversed markers: {start!r}, {end!r}")
    return text[begin:finish]


def capitalize_theorem_title(match: re.Match[str]) -> str:
    prefix, first = match.groups()
    return prefix + first.upper()


def normalize_legacy_section(text: str) -> str:
    # Remove navigation-only commands that are redundant in the generated AMS
    # draft. Labels immediately following theorem statements are retained.
    text = re.sub(r"(?m)^\\phantomsection\s*$\n?", "", text)
    text = re.sub(
        r"(?m)^\\addcontentsline\{toc\}\{subsection\}\{[^\n]*\}\s*$\n?",
        "",
        text,
    )

    # Convert the ruled legacy boxes to the ordinary amsthm hierarchy. The
    # source labels occur immediately before the environments and remain valid.
    text = re.sub(
        r"\\begin\{lemmabox\}\{Lemma\s+[0-9.]+\s+\(([^{}]*)\)\}",
        r"\\begin{lemma}[\1]",
        text,
    )
    text = re.sub(
        r"\\begin\{propositionbox\}\{Proposition\s+[0-9.]+\s+\(([^{}]*)\)\}",
        r"\\begin{proposition}[\1]",
        text,
    )
    text = re.sub(
        r"\\begin\{resultbox\}\{Theorem\s+[0-9.]+\}",
        r"\\begin{theorem}",
        text,
    )
    text = text.replace(r"\end{lemmabox}", r"\end{lemma}")
    text = text.replace(r"\end{propositionbox}", r"\end{proposition}")
    text = text.replace(r"\end{resultbox}", r"\end{theorem}")
    text = re.sub(
        r"(\\begin\{(?:lemma|proposition|theorem|corollary)\}\[)([a-z])",
        capitalize_theorem_title,
        text,
    )

    # Convert the legacy paragraph proofs to genuine amsthm proof environments.
    # Section 7 has one proof divided into three named ranges, so it is handled
    # separately before the generic proof conversion.
    text = re.sub(
        r"\\paragraph\{Proof: the empty corner\.\}\\label\{[^}]+\}\s*",
        r"\\begin{proof}\n\\displayheading{Empty corner}\n",
        text,
    )
    text = re.sub(
        r"\\paragraph\{Proof: the central range\.\}\\label\{[^}]+\}\s*",
        r"\\displayheading{Central range}\n",
        text,
    )
    text = re.sub(
        r"\\paragraph\{Proof: the full corner\.\}\\label\{[^}]+\}\s*",
        r"\\displayheading{Full corner}\n",
        text,
    )
    text = re.sub(
        r"\\paragraph\{Proof\.\}\\label\{[^}]+\}\s*",
        r"\\begin{proof}\n",
        text,
    )
    text = text.replace(r"\(\square\)", r"\end{proof}")
    text = re.sub(r"[ \t]+\\end\{proof\}", r"\n\\end{proof}", text)

    # Normalize mathematical English and notation without changing any finite
    # identity, hypothesis, quantifier, or summation domain.
    replacements = {
        r"\ln": r"\log",
        r"\log2": r"\log 2",
        "colouring": "coloring",
        "colourings": "colorings",
        "coloured": "colored",
        "colour": "color",
        "cocolouring": "cocoloring",
        "cocolourings": "cocolorings",
        "cocolourable": "cocolorable",
        "fibre": "fiber",
        "fibres": "fibers",
        "neighbourhood": "neighborhood",
        "neighbourhoods": "neighborhoods",
        "catalogued": "cataloged",
    }
    for old, new in replacements.items():
        text = text.replace(old, new)

    text = text.replace(
        "\\section{Notation and elementary\nfacts}",
        "\\section{Phase notation and elementary estimates}",
    )
    text = text.replace(
        "\\section{The complete independence-number\nphase}",
        "\\section{The complete independence-number phase}",
    )
    text = text.replace(
        "\\section{The four-size signed first-moment\nadvantage}",
        "\\section{The four-size signed first-moment advantage}",
    )
    text = text.replace(
        "\\section{Exact signed second-moment\nrepresentation}",
        "\\section{Exact signed second-moment representation}",
    )

    prose_replacements = {
        (
            "The profile optimization has two jobs. It must locate the zero of the\n"
            "first-moment exponent, and it must compare two different supports at the\n"
            "same average class size. The affine part of the deficit weight cancels under\n"
            "the fixed-mean constraint; only the curved part distinguishes the supports.\n"
            "The following lemma packages both facts, together with the uniform derivative\n"
            "needed to convert an entropy advantage into a root displacement."
        ): (
            "The profile optimization serves two purposes: it locates the first-moment\n"
            "root and compares two supports at the same mean class size. Under the\n"
            "fixed-mean constraint the affine deficit term cancels, so only the curved\n"
            "term distinguishes the supports. The next lemma collects the root corridor,\n"
            "the uniform slope, and the support comparison used below."
        ),
        (
            "A \\emph{signed cocoloring} is a partition in which every class is\n"
            "declared either ``independent'' or ``complete''; it is realized when each\n"
            "class induces the graph specified by its declaration.  Thus the sign is a\n"
            "two-way declaration attached to a class, and the signed counts below count\n"
            "witnesses for ordinary cocolorings rather than a new graph invariant."
        ): (
            "Recall that a signed cocoloring witness is a profile partition with one\n"
            "independent-or-complete declaration on each class. It is realized when each\n"
            "class induces the declared graph. These declarations are auxiliary counting\n"
            "data, not a new graph invariant."
        ),
        (
            "There are two logically separate tasks. First, restricting the deficits to\n"
            "\\(S_4=\\{2,3,4,5\\}\\) must cost strictly less than \\(\\log 2\\) per part. Second,\n"
            "the \\(2^k\\) choices of signs must convert that strict inequality into a\n"
            "macroscopic separation of the two roots. Lemma~5.1 proves the first point;\n"
            "the derivative estimate from Lemma~3.1 then proves the second."
        ): (
            "The four-size comparison has two steps. Restricting the deficits to\n"
            "\\(S_4=\\{2,3,4,5\\}\\) must cost strictly less than \\(\\log 2\\) per part. The\n"
            "\\(2^k\\) sign choices then convert this strict entropy margin into a\n"
            "macroscopic root separation. Lemma~5.1 proves the margin, and the slope\n"
            "estimate in Lemma~3.1 converts it into displacement."
        ),
        (
            "For completeness, the first strict inequality in (5.4) has the following\n"
            "direct verification.  Put"
        ): (
            "We verify the first strict inequality in (5.4) directly. Put"
        ),
        (
            "It is proved directly for the four-size signed profile, including both\n"
            "corners and every intermediate mass, and no tame-profile theorem is invoked."
        ): (
            "We prove it directly for the four-size signed profile, uniformly at both\n"
            "corners and throughout the intermediate range; no external tame-profile\n"
            "theorem is used."
        ),
        (
            "The proof has three ranges, classified by the vertex mass occupied by the\n"
            "marked common classes."
        ): (
            "We split the common-subprofile sum according to the vertex mass occupied by\n"
            "the marked classes."
        ),
    }
    for old, new in prose_replacements.items():
        text = text.replace(old, new)

    text = re.sub(
        r"We (?:first|begin by) bracket this tilt\..*?Substituting\s+\\\(i=j\+2\\\) in the weight gives",
        lambda _: (
            "We begin by bracketing this tilt. At \\(\\lambda=2{\\log 2}\\), set\n"
            "\\(j=i-2\\), a bijection from \\(S_4\\) onto \\(\\{0,1,2,3\\}\\).\n"
            "Substituting \\(i=j+2\\) gives"
        ),
        text,
        count=1,
        flags=re.S,
    )

    text = text.replace(
        "\\gamma_4=\\log\\frac{200}{153}.                            \\tag{5.2}\n\\]",
        (
            "\\gamma_4=\\log\\frac{200}{153}.                            \\tag{5.2}\n"
            "\\]\n"
            "This coarse certificate is sufficient for the root separation.\n"
            "Section~11 sharpens it to obtain the displayed numerical constant."
        ),
    )

    rate_certificate = r"""Here is an exact endpoint certificate for this split. Put
$q=\log 2$. The expansion
\[
 q=2\sum_{m\ge0}\frac{1}{(2m+1)3^{2m+1}}
\]
gives
\[
 \frac{69}{100}<q<\frac{7}{10}.
\]
Indeed, the first two positive terms give
$2(1/3+1/81)=56/81>69/100$, while bounding every denominator in the
tail from $m=1$ below by $3$ gives
$ q<2(1/3+1/72)=25/36<7/10$.

For $x=100/47$, the same expansion with
$z=(x-1)/(x+1)=53/147$ yields
\begin{equation}
 \log\!\left(\frac{100}{47}\right)
 >2\left(z+\frac{z^3}{3}\right)
 =\frac{7169416}{9529569}.
 \label{eq:partial-diagonal-log-certificate-v3}
\end{equation}

On $1/64\le R\le47/100$, add $Y/5000=(1-R)/5000$ to the first
bound in (7.23). The resulting function is convex in $R$, and its
largest coefficient occurs at $T=2/q$. At $R=1/64$, using
$\log64=6q$ and $q>2/3$, its value is at most
\[
 \frac{-7q/2-1}{64}+\frac{63}{320000}<0.
\]
At $R=47/100$, equations above give the upper bound
\[
 -\frac{47}{100}\frac{7169416}{9529569}
 +\frac{141}{400}+\frac{53}{500000}
 =-\frac{4721156593}{4764784500000}<0.
\]
Convexity therefore gives $\Phi_T\le-Y/5000$ throughout this interval.

On $47/100\le R\le1$, use the second bound in (7.23), add $Y/200$,
and use $T\le1+2/q$. The resulting convex function has value zero at
$R=1$. At $R=47/100$, the bounds $q>69/100$ and
\eqref{eq:partial-diagonal-log-certificate-v3} give
\[
 -\frac{47}{100}\frac{7169416}{9529569}
 +\frac{53}{100}\frac{33}{50}
 =-\frac{180911419}{47647845000}<0.
\]
Hence $\Phi_T\le-Y/200$ on the second interval. The companion script
\texttt{check\_partial\_diagonal\_rate\_v3.py} verifies these rational
comparisons independently.
Thus, whenever"""
    text = re.sub(
        r"Here is the numerical check used in this split\..*?Thus, whenever",
        lambda _: rate_certificate,
        text,
        count=1,
        flags=re.S,
    )

    text = re.sub(
        r"We use the same\s+seed-to-typical strategic principle, but not that theorem as a black box:\s*"
        r"Lemma 10\.2 proves the quantitative implication needed here for an arbitrary\s*"
        r"seed exponent \\\(\\Lambda_n\\\), and Lemma 10\.1 supplies the simultaneous\s*"
        r"leftover coloring that controls the added parts\.",
        lambda _: (
            "We follow the same seed-to-typical principle, but prove the precise form\n"
            "needed here. Lemma 10.2 treats an arbitrary seed exponent\n"
            "\\(\\Lambda_n\\), and Lemma 10.1 supplies a simultaneous coloring bound\n"
            "for every leftover vertex set."
        ),
        text,
        count=1,
    )
    text = re.sub(
        r"The ordinary-coloring concentration argument motivating this amplification\s*"
        r"appears in \\citet\[Theorem~1\]\{scott-2008-2017\}\. Lemmas 10\.1 and 10\.2 prove the precise\s*"
        r"simultaneous-leftover and rare-seed forms required here\.",
        lambda _: (
            "The vertex-exposure argument is motivated by\n"
            "\\citet[Theorem~1]{scott-2008-2017}. Lemma 10.1 gives the simultaneous\n"
            "leftover bound, and Lemma 10.2 gives the arbitrary-seed amplifier used here."
        ),
        text,
        count=1,
    )
    text = text.replace(
        "We now prove the amplification needed to turn this possibly rare event\n"
        "into a typical one.",
        "We next turn this possibly rare event into a typical one.",
    )

    # Section 10 must point to the replacement normalized-second-moment
    # proposition rather than to the legacy proposition number.
    text = text.replace(
        "Proposition 9.2",
        "Proposition~\\ref{prop:normalized-second-moment-v3}",
    )
    return text


def generate(source: Path, output: Path) -> None:
    raw = source.read_bytes()
    blob = git_blob_sha(raw)
    require(
        blob == EXPECTED_CANONICAL_BLOB,
        f"canonical source drift: expected {EXPECTED_CANONICAL_BLOB}, found {blob}",
    )
    text = raw.decode("utf-8")

    sections_1_to_7 = normalize_legacy_section(
        slice_between(text, START_SECTION_1, START_SECTION_8)
    )
    section_10 = normalize_legacy_section(
        slice_between(text, START_SECTION_10, START_SECTION_11)
    )

    generated = "\n".join(
        [
            "% GENERATED FILE: do not edit directly.",
            f"% Canonical source Git blob: {blob}",
            "% Generator: 625/scripts/build_self_contained_ams_v3.py",
            "",
            sections_1_to_7.rstrip(),
            "",
            r"\input{SECTION8_SELF_CONTAINED_V3}",
            "",
            r"\input{SECTION9_SELF_CONTAINED_V3}",
            "",
            section_10.rstrip(),
            "",
            r"\input{FINAL_ASSEMBLY_SELF_CONTAINED_V3}",
            "",
        ]
    )
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(generated, encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    root = Path(__file__).resolve().parents[1]
    parser.add_argument(
        "--source",
        type=Path,
        default=root / "arxiv" / "main.tex",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=root / "arxiv" / "AMS_SELF_CONTAINED_BODY_V3.generated.tex",
    )
    args = parser.parse_args()
    generate(args.source, args.output)
    print(f"generated {args.output}")


if __name__ == "__main__":
    main()
