#!/usr/bin/env python3
"""Fail-closed structural checks for the Erdős 625 Version 3 manuscript."""

from __future__ import annotations

import re
import subprocess
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ARXIV = ROOT / "arxiv"
GENERATOR = ROOT / "scripts" / "build_phase_root_self_contained_v3.py"
CONSTANT_CHECKER = ROOT / "experiments" / "check_constant_ledger_v3.py"
PARTIAL_RATE_CHECKER = ROOT / "experiments" / "check_partial_diagonal_rate_v3.py"
GENERATED = ARXIV / "AMS_SELF_CONTAINED_BODY_V3.generated.tex"
MASTER = ARXIV / "AMS_SELF_CONTAINED_DRAFT_V3.tex"

SOURCE_FILES = [
    ARXIV / "FRONTMATTER_INTRODUCTION_SELF_CONTAINED_V3.tex",
    ARXIV / "CONVENTIONS_AND_PROOF_OBJECTS_V3.tex",
    ARXIV / "PROOF_ARCHITECTURE_SELF_CONTAINED_V3.tex",
    ARXIV / "SECTION2_PHASE_PACKAGE_V3.tex",
    ARXIV / "SECTION3_ROOT_GEOMETRY_V3.tex",
    ARXIV / "SECTION4_CHROMATIC_LOWER_TAIL_V3.tex",
    ARXIV / "SECTION5_ROOT_TRANSPORT_V3.tex",
    ARXIV / "SECTION7_EMPTY_CORNER_V3.tex",
    ARXIV / "SECTION7_CENTRAL_EXTRACTION_V3.tex",
    ARXIV / "SECTION7_FULL_CORNER_V3.tex",
    ARXIV / "SECTION8_SELF_CONTAINED_V3.tex",
    ARXIV / "SECTION9_SELF_CONTAINED_V3.tex",
    ARXIV / "SECTION9_EXPLICIT_GLOBAL_LEDGER_V3.tex",
    ARXIV / "FINAL_ASSEMBLY_SELF_CONTAINED_V3.tex",
    ARXIV / "FORMALIZATION_STATUS_APPENDIX_V3.tex",
    ARXIV / "FORMALIZATION_STATUS_ADDENDUM_2026_08_07_V3.tex",
]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def flatten(text: str) -> str:
    """Normalize TeX source whitespace without changing control sequences."""
    return re.sub(r"\s+", " ", text)


def strip_tex(text: str) -> str:
    text = re.sub(r"%.*", " ", text)
    text = re.sub(r"\\[A-Za-z@]+\*?(?:\[[^]]*\])?", " ", text)
    text = text.replace("{", " ").replace("}", " ")
    text = re.sub(r"\$[^$]*\$", " ", text)
    return re.sub(r"\s+", " ", text)


def check_balanced_environments(text: str, name: str) -> None:
    begins = Counter(re.findall(r"\\begin\{([^}]+)\}", text))
    ends = Counter(re.findall(r"\\end\{([^}]+)\}", text))
    require(
        begins == ends,
        f"{name}: unbalanced environments: {begins - ends}, {ends - begins}",
    )


def check_control_characters(text: str, name: str) -> None:
    bad = [
        (index, ord(character))
        for index, character in enumerate(text)
        if ord(character) < 32 and character not in "\n\r\t"
    ]
    require(not bad, f"{name}: hidden control characters: {bad[:8]}")


def main() -> None:
    for path in [
        MASTER,
        GENERATOR,
        CONSTANT_CHECKER,
        PARTIAL_RATE_CHECKER,
        *SOURCE_FILES,
    ]:
        require(path.is_file(), f"missing file: {path}")

    subprocess.run(["python", str(GENERATOR)], cwd=ROOT.parent, check=True)
    subprocess.run(["python", str(CONSTANT_CHECKER)], cwd=ROOT.parent, check=True)
    subprocess.run(["python", str(PARTIAL_RATE_CHECKER)], cwd=ROOT.parent, check=True)
    require(GENERATED.is_file(), "generator did not create the manuscript body")

    master = MASTER.read_text(encoding="utf-8")
    generated = GENERATED.read_text(encoding="utf-8")
    sources = {path.name: path.read_text(encoding="utf-8") for path in SOURCE_FILES}
    combined = "\n".join([master, generated, *sources.values()])

    require(r"\ErdosProofClosedfalse" in master, "publication switch is not fail-closed")
    require(r"\ErdosProofClosedtrue" not in master, "publication mode was enabled")
    front = sources["FRONTMATTER_INTRODUCTION_SELF_CONTAINED_V3.tex"]
    require("Verification status" in front, "visible verification status is missing")
    require(r"\fbox" not in front, "front matter still contains a boxed status banner")
    require(r"\begin{maintheorem}" in front, "unnumbered main theorem is missing")

    required_master_inputs = (
        "AMS_THEOREM_ENVIRONMENTS_V3",
        "FRONTMATTER_INTRODUCTION_SELF_CONTAINED_V3",
        "CONVENTIONS_AND_PROOF_OBJECTS_V3",
        "PROOF_ARCHITECTURE_SELF_CONTAINED_V3",
        "AMS_SELF_CONTAINED_BODY_V3.generated",
        "FORMALIZATION_STATUS_APPENDIX_V3",
        "FORMALIZATION_STATUS_ADDENDUM_2026_08_07_V3",
    )
    missing_inputs = [token for token in required_master_inputs if token not in master]
    require(not missing_inputs, f"master file missing inputs: {missing_inputs}")

    required_body_markers = (
        r"\section{Phase notation and elementary estimates}",
        r"\input{SECTION2_PHASE_PACKAGE_V3}",
        r"\input{SECTION3_ROOT_GEOMETRY_V3}",
        r"\input{SECTION4_CHROMATIC_LOWER_TAIL_V3}",
        r"\input{SECTION5_ROOT_TRANSPORT_V3}",
        r"\input{SECTION7_EMPTY_CORNER_V3}",
        r"\input{SECTION7_CENTRAL_EXTRACTION_V3}",
        r"\input{SECTION7_FULL_CORNER_V3}",
        r"\input{SECTION8_SELF_CONTAINED_V3}",
        r"\input{SECTION9_SELF_CONTAINED_V3}",
        r"\input{SECTION9_EXPLICIT_GLOBAL_LEDGER_V3}",
        r"\section{Rare-event amplification}",
        r"\input{FINAL_ASSEMBLY_SELF_CONTAINED_V3}",
        "Canonical source Git blob: c4d090b73cd5efcdb98cc30f79bb5f53c6c9bc97",
    )
    missing_body = [token for token in required_body_markers if token not in generated]
    require(not missing_body, f"generated body missing markers: {missing_body}")
    require(
        generated.count(r"\section{") >= 5,
        "generated body does not contain the expected numbered sections",
    )
    require(
        len(generated.splitlines()) >= 700,
        f"generated body is unexpectedly short: {len(generated.splitlines())} lines",
    )

    section2 = sources["SECTION2_PHASE_PACKAGE_V3.tex"]
    section2_flat = flatten(section2)
    for token in (
        "Uniform phase expansion and adjacent-size control",
        r"\varepsilon_n^{\mathrm{ph}}",
        r"|E_n(\delta)|\le\varepsilon_n^{\mathrm{ph}}",
        r"\varepsilon_n^{\mathrm{cap}}",
        r"2^\alpha",
        "one eventuality threshold valid for the complete phase",
    ):
        require(token in section2_flat, f"Section 2 phase package missing: {token}")
    require(
        r"\begin{equation}" not in section2,
        "Section 2 uses numbered equations with manual tags",
    )

    section3 = sources["SECTION3_ROOT_GEOMETRY_V3.tex"]
    section3_flat = flatten(section3)
    for token in (
        "Uniform root, slope, and finite-dual package",
        r"S_+^{(n)}",
        r"\varepsilon_n^{\mathrm{dual}}",
        r"\varepsilon_{n,A}^{\mathrm{slope}}",
        "No limiting replacement is used in this cancellation",
        "one eventuality threshold for the complete phase",
    ):
        require(token in section3_flat, f"Section 3 root package missing: {token}")
    require(
        r"\begin{equation}" not in section3,
        "Section 3 uses numbered equations with manual tags",
    )

    section4 = sources["SECTION4_CHROMATIC_LOWER_TAIL_V3.tex"]
    section4_flat = flatten(section4)
    for token in (
        "A uniform lower location",
        r"\Delta_n:=r_+(n)-k_\chi^-",
        r"\frac{n}{k^2}",
        r"c_*(\log n)^2",
        r"\varepsilon_n^{\mathrm{prof}}",
        r"\varepsilon_n^{\mathrm{cap}}",
        "Splitting such a class into two nonempty subsets preserves independence",
        "The direction is strict",
        r"o\!\left(\frac{n}{(\log n)^3}\right)",
        "full sequence of integers",
    ):
        require(token in section4_flat, f"Section 4 lower tail missing: {token}")
    require(
        r"\begin{equation}" not in section4,
        "Section 4 lower tail uses numbered equations with manual tags",
    )
    require(
        "By Lemma 3.1 and (1.2)" not in generated,
        "compressed chromatic lower-tail proof remains in generated source",
    )

    section5 = sources["SECTION5_ROOT_TRANSPORT_V3.tex"]
    section5_flat = flatten(section5)
    for token in (
        "finite-$n$ support loss",
        r"D_{4,n}(T)",
        r"T_+(n)=T_0",
        r"\mathcal F_S'(T)=-\lambda_S(T)",
        r"\varepsilon_n^{\mathrm{target}}",
        r"\omega_n^{\mathrm{root}}",
        "This equality is finite and contains no limiting substitution",
        "one deterministic error sequence valid across the complete phase",
        "integer sequences approaching either endpoint",
        r"r_4^{\mathrm{co}}<r_+",
        "orientation fixed",
    ):
        require(token in section5_flat, f"Section 5 root transport missing: {token}")
    require(
        r"\begin{equation}" not in section5,
        "Section 5 root transport uses a numbered equation with a manual tag",
    )
    require(
        "Lemma 3.1 and (5.2) give" not in generated,
        "compressed Section 5 target transport remains in generated source",
    )

    empty = sources["SECTION7_EMPTY_CORNER_V3.tex"]
    empty_flat = flatten(empty)
    for token in (
        "in any order",
        r"(1-2\eta)^{-u_i}",
        r"-\log(1-2\eta)\le4\eta",
        r"\frac{111}{56}",
        r"\varepsilon_n^{\mathrm{empty}}",
        "one phase-independent constant",
        "Every threshold in this estimate is independent of the phase",
    ):
        require(token in empty_flat, f"Section 7 empty corner missing: {token}")
    require(
        r"\begin{equation}" not in empty,
        "Section 7 empty corner uses numbered equations with manual tags",
    )

    central = sources["SECTION7_CENTRAL_EXTRACTION_V3.tex"]
    central_flat = flatten(central)
    for token in (
        "Uniform Stirling extraction",
        r"C_{\mathrm S}",
        r"\tag{7.14a}",
        r"\sum_i y_i\log",
        "Only the upper bound on $\\bar E$ is used here",
        r"\label{eq:partial-diagonal-combined-structural-v3}",
        r"\frac{13}{8960}",
        r"\frac1{20}",
        r"\varepsilon_n^{\mathrm{diag}}",
        r"\varepsilon_n^{\mathrm{central}}",
        "one eventuality threshold for the complete phase",
        "check_partial_diagonal_rate_v3.py",
    ):
        require(token in central_flat, f"Section 7 central extraction missing: {token}")
    require(
        len(central.splitlines()) >= 260,
        f"Section 7 central extraction is unexpectedly short: {len(central.splitlines())} lines",
    )
    require(
        r"\begin{equation}" not in central,
        "Section 7 central extraction uses numbered equations with manual tags",
    )

    full = sources["SECTION7_FULL_CORNER_V3.tex"]
    full_flat = flatten(full)
    for token in (
        r"v(a)+u_i\le v(h)",
        r"\mu_{u_i}(w)\le n^{-3}",
        r"2n^{-2}<1",
        r"\varepsilon_n^{\mathrm{full}}",
        "Disjoint three-range assembly",
        r"\eta<31/32",
        "no boundary term is counted twice",
        r"\varepsilon_n^{\mathrm{central}}",
        "one eventuality threshold for the complete phase",
    ):
        require(token in full_flat, f"Section 7 full corner missing: {token}")
    require(
        r"\begin{equation}" not in full,
        "Section 7 full corner uses numbered equations with manual tags",
    )

    section8 = sources["SECTION8_SELF_CONTAINED_V3.tex"]
    section8_flat = flatten(section8)
    for token in (
        "Completion-free aggregate weight",
        "Exact one-cell deficit ratio",
        "Aggregate deficit comparison",
        "Optional-choice product",
        "Reference grouping",
        "Reusable finite core",
        "Square-free endpoint transport",
        "Endpoint-table sum",
        "Insertion of the phase estimates",
        r"w_{\mathrm{hi}}(P,j):=w(P,j)",
        "one-sided reference measure",
        "not a deletion of common-class overlaps",
        r"\rho_{16}",
    ):
        require(token in section8_flat, f"Section 8 missing: {token}")
    require("Lean" not in section8, "Section 8 contains implementation-status prose")

    section9 = sources["SECTION9_SELF_CONTAINED_V3.tex"]
    section9_flat = flatten(section9)
    for token in (
        r"\theta_{ab}",
        r"\lambda_{ab}",
        r"q_{ab}",
        r"\Phi_F",
        r"\label{eq:zero-residual-attachment-v3}",
        "the unique empty matching",
        "no independence between cells is asserted",
        "no overlap is assigned to two skeletons",
        r"\frac{U^2}{8}",
        r"\frac{U^2}{6}",
        "factorial term only improves the upper bound",
        "Fixed even-set expansion",
        "Restriction-product bound",
        "Quadratic activity bound",
        "The intrinsic residual regime",
        "The complementary residual regime",
        "Normalized signed second moment",
    ):
        require(token in section9_flat, f"Section 9 missing: {token}")

    global_ledger = sources["SECTION9_EXPLICIT_GLOBAL_LEDGER_V3.tex"]
    global_ledger_flat = flatten(global_ledger)
    for token in (
        "Explicit global logarithmic ledger",
        r"\varepsilon_n^{\mathrm{pd}}",
        r"\Gamma_n^{\mathrm{skel}}",
        r"\varepsilon_n^{\mathrm{skel}}",
        r"\Gamma_n^{\mathrm{att}}",
        r"\varepsilon_n^{\mathrm{att}}",
        r"\Lambda_n",
        "No factor is charged in both ledgers",
    ):
        require(token in global_ledger_flat, f"global second-moment ledger missing: {token}")
    require(
        r"\begin{equation}" not in global_ledger,
        "global ledger uses numbered equations with manual tags",
    )

    final = sources["FINAL_ASSEMBLY_SELF_CONTAINED_V3.tex"]
    final_flat = flatten(final)
    for token in (
        r"\frac{(\log 2)^2}{8}A_4(\delta_n)",
        r"\log\!\left(\frac{1000}{639}\right)",
        r"\frac{2777}{10000}",
        r"\frac{20000}{12777}",
        r"\frac{12780}{12777}",
        r"\sigma_4>0",
        "there is no additional correction to the total number of classes",
        "exact rational certificates",
        "1035264923841377",
        "check\\_constant\\_ledger\\_v3.py",
        "Simultaneous complement form",
        "no further asymptotic loss is introduced",
    ):
        require(token in final_flat, f"final assembly missing: {token}")
    require("+b_n" not in final, "final assembly reintroduced a class-count correction")
    require("|b_n|" not in final, "final assembly reintroduced an untracked correction")

    appendix = sources["FORMALIZATION_STATUS_APPENDIX_V3.tex"]
    appendix_flat = flatten(appendix)
    for token in (
        "Welded",
        "Running",
        "Needs review",
        "eventually_fourEndpointThreeQuarterRho_le_one",
        "SECTION5_ROOT_TRANSPORT_V3.tex",
        "SECTION7_EMPTY_CORNER_V3.tex",
        "SECTION7_CENTRAL_EXTRACTION_V3.tex",
        "SECTION7_FULL_CORNER_V3.tex",
        "sum_partialDiagonalWeight_le_exp_sum_muCutoffActivity",
        "partialDiagonalRate_uniform_negative",
        "partialDiagonalRate_uniform_negative_fourDeficit",
        "sum_partialDiagonalWeight_fullCorner_eq",
        "complete candidate manuscript proof of E625-11A--D",
        "Publication gate",
        "Recommended theorem-facing Lean organization",
    ):
        require(token in appendix_flat, f"formalization appendix missing: {token}")

    addendum = sources["FORMALIZATION_STATUS_ADDENDUM_2026_08_07_V3.tex"]
    addendum_flat = flatten(addendum)
    for token in (
        "Theorem-facing closure addendum",
        "Deterministic error chain",
        "Exact formalization targets",
        "The arrows denote theorem dependency, not equality",
        "status of the main theorem remains fail-closed",
    ):
        require(token in addendum_flat, f"formalization addendum missing: {token}")

    forbidden = (
        "TODO",
        "TBD",
        "proof omitted",
        "details are standard",
        "The endpoint transportation estimate absorbs",
        "canonically equivalent to the dependent sum",
        "after Section~7 has removed",
        r"\exp\!left",
        r"\begin{lemmabox}",
        r"\begin{propositionbox}",
        r"\begin{resultbox}",
        r"\paragraph{Proof",
        r"\(\square\)",
        r"\log2",
        r"\ln",
    )
    offenders = [token for token in forbidden if token in combined]
    require(not offenders, f"forbidden manuscript markers: {offenders}")

    labels = re.findall(r"\\label\{([^}]+)\}", combined)
    label_counts = Counter(labels)
    duplicates = sorted(label for label, count in label_counts.items() if count > 1)
    require(not duplicates, f"duplicate labels: {duplicates}")

    for name, text in {"master": master, "generated": generated, **sources}.items():
        check_control_characters(text, name)
        check_balanced_environments(text, name)
        require(text.count("{") == text.count("}"), f"{name}: unbalanced braces")

    words = re.findall(r"[A-Za-z][A-Za-z'-]+", strip_tex(combined))
    # The generated body delegates theorem-facing passages to checked source
    # files. Measure the complete assembled source set, not only the wrapper.
    require(
        len(words) >= 6500,
        f"manuscript prose extraction is unexpectedly short: {len(words)} words",
    )

    print("ERDOS 625 SELF-CONTAINED MANUSCRIPT CHECK: PASS")
    print(f"  generated body lines: {len(generated.splitlines())}")
    print(f"  Section 2 phase source lines: {len(section2.splitlines())}")
    print(f"  Section 3 root source lines: {len(section3.splitlines())}")
    print(f"  Section 4 lower-tail source lines: {len(section4.splitlines())}")
    print(f"  Section 5 root-transport source lines: {len(section5.splitlines())}")
    print(f"  Section 7 empty source lines: {len(empty.splitlines())}")
    print(f"  Section 7 central source lines: {len(central.splitlines())}")
    print(f"  Section 7 full source lines: {len(full.splitlines())}")
    print(f"  global ledger source lines: {len(global_ledger.splitlines())}")
    print(f"  approximate prose words: {len(words)}")
    print(f"  unique semantic labels: {len(label_counts)}")
    print("  exact certificates: four-support slack and partial-diagonal scalar ledger")
    print("  publication switch: disabled")


if __name__ == "__main__":
    main()
