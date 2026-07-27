#!/usr/bin/env python3
"""Check coverage and internal consistency of the Erdős 625 literal audit.

The checker validates source SHA, exact theorem ranges, status classifications,
known source defects, and human-audit coverage. It is not a mathematical proof.
"""

from __future__ import annotations

import hashlib
import json
import re
from collections import Counter
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "625/arxiv/main.tex"
AUDIT = ROOT / "625/audits/LINE_BY_LINE_THEOREM_AUDIT_2026-07-27.md"
MANIFEST = ROOT / "625/audits/THEOREM_STATUS_MANIFEST_2026-07-27.json"

BOXED_IDS = {
    "T1",
    "L2.1",
    "L3.1",
    "L5.1",
    "L6.1",
    "L6.2",
    "L7.1",
    "L8.1",
    "L8.2",
    "L8.3",
    "L9.1",
    "P9.2",
    "L10.1",
    "L10.2",
}

EXPECTED_STATUS = {
    "T1": "RED",
    "L2.1": "GREEN",
    "L3.1": "GREEN-REWRITE",
    "L5.1": "GREEN-REWRITE",
    "L6.1": "GREEN",
    "L6.2": "GREEN",
    "L7.1": "GREEN-REWRITE",
    "L8.1": "GREEN-REWRITE",
    "L8.2": "GREEN-REWRITE",
    "L8.3": "RED",
    "L9.1": "SUPERSEDED",
    "P9.2": "RED",
    "L10.1": "GREEN",
    "L10.2": "GREEN",
}

EXPECTED_BEGIN = {
    "T1": 119,
    "L2.1": 295,
    "L3.1": 495,
    "L5.1": 860,
    "L6.1": 1354,
    "L6.2": 1445,
    "L7.1": 1651,
    "L8.1": 2053,
    "L8.2": 2151,
    "L8.3": 2233,
    "L9.1": 2550,
    "P9.2": 2832,
    "L10.1": 2903,
    "L10.2": 2968,
}

EXPECTED_PROOF_BEGIN = {
    "L2.1": 324,
    "L3.1": 563,
    "L5.1": 871,
    "L6.1": 1385,
    "L6.2": 1484,
    "L7.1": 1667,
    "L8.1": 2081,
    "L8.2": 2171,
    "L8.3": 2245,
    "L9.1": 2567,
    "P9.2": 2844,
    "L10.1": 2914,
    "L10.2": 2991,
}

ALLOWED_STATUS = {
    "GREEN",
    "GREEN-REWRITE",
    "AMBER",
    "RED",
    "TYPO/EDITORIAL",
    "SUPERSEDED",
}

REQUIRED_TAGS = {
    "0.1",
    "2.2",
    "3.7",
    "5.3",
    "5.11",
    "5.20",
    "6.4",
    "6.8",
    "7.7",
    "8.8",
    "8.16",
    "8.21",
    "8.30",
    "9.2",
    "9.3",
    "9.23",
    "10.3",
    "10.5",
    "10.13",
    "11.1",
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def boxed_token(item_id: str) -> str:
    if item_id == "T1":
        return "Theorem 1"
    if item_id == "P9.2":
        return "Proposition 9.2"
    if item_id.startswith("L"):
        return f"Lemma {item_id[1:]}"
    raise RuntimeError(f"unknown boxed id: {item_id}")


def git_blob_sha(raw: bytes) -> str:
    return hashlib.sha1(f"blob {len(raw)}\0".encode("ascii") + raw).hexdigest()


def source_range(lines: list[str], bounds: list[int]) -> str:
    require(len(bounds) == 2, f"invalid range: {bounds}")
    start, end = bounds
    require(1 <= start <= end <= len(lines), f"out-of-range source span: {bounds}")
    return "\n".join(lines[start - 1 : end])


def load_manifest() -> dict[str, Any]:
    data = json.loads(MANIFEST.read_text(encoding="utf-8"))
    require(isinstance(data.get("items"), list), "manifest items missing")
    return data


def check_manifest(manifest: dict[str, Any], raw: bytes, lines: list[str]) -> Counter[str]:
    require(manifest["source"] == "625/arxiv/main.tex", "manifest source mismatch")
    require(manifest["source_blob_sha"] == git_blob_sha(raw), "stale source blob SHA")
    items = manifest["items"]
    ids = [item["id"] for item in items]
    require(len(ids) == len(set(ids)), "duplicate manifest ids")
    by_id = {item["id"]: item for item in items}
    require(BOXED_IDS <= set(by_id), "boxed statement coverage incomplete")

    for item in items:
        item_id = item["id"]
        require(item["status"] in ALLOWED_STATUS, f"{item_id}: invalid status")
        require(isinstance(item["blocking"], bool), f"{item_id}: invalid blocking flag")
        require(item["issue"] and item["repair"], f"{item_id}: empty issue/repair")
        statement_text = source_range(lines, item["statement_lines"])
        source_range(lines, item["proof_lines"])
        if item_id in BOXED_IDS:
            require(boxed_token(item_id) in statement_text, f"{item_id}: identifier not in range")

    for item_id, expected in EXPECTED_STATUS.items():
        require(by_id[item_id]["status"] == expected, f"{item_id}: status drift")
        require(
            by_id[item_id]["statement_lines"][0] == EXPECTED_BEGIN[item_id],
            f"{item_id}: statement line drift",
        )

    for item_id, proof_begin in EXPECTED_PROOF_BEGIN.items():
        require(
            by_id[item_id]["proof_lines"][0] == proof_begin,
            f"{item_id}: proof line drift",
        )
        head = source_range(lines, [proof_begin, min(proof_begin + 3, len(lines))])
        require("Proof" in head or "\\begin{proof}" in head, f"{item_id}: proof marker absent")

    red_boxed = {item_id for item_id in BOXED_IDS if by_id[item_id]["status"] == "RED"}
    require(red_boxed == {"T1", "L8.3", "P9.2"}, f"unexpected RED set: {red_boxed}")
    require(
        manifest["single_blocking_chain"]
        == ["Lemma 8.3", "Proposition 9.2", "Theorem 1"],
        "blocking chain drift",
    )
    return Counter(item["status"] for item in items)


def check_source(text: str) -> None:
    tags = re.findall(r"\\tag\{([^}]+)\}", text)
    duplicates = [tag for tag, count in Counter(tags).items() if count > 1]
    require(not duplicates, f"duplicate equation tags: {duplicates}")
    require(REQUIRED_TAGS <= set(tags), f"missing required tags: {sorted(REQUIRED_TAGS - set(tags))}")
    require("2^\\ell_\\bullet" in text, "known Section 7 typo absent; refresh audit")
    require("2^{\\ell_\\bullet}" not in text, "source typo was fixed without refreshing audit")
    require(r"We prove that, for \(G_n\sim G(n,1/2)\)" in text, "abstract claim changed")
    require("3a/4+O(1)" in text, "imprecise Section VIII range changed")


def check_audit(audit: str, manifest: dict[str, Any]) -> None:
    markers = (
        "literal line-by-line and theorem-by-theorem audit",
        "There is one submission-blocking chain",
        "Lemma 8.3",
        "Proposition 9.2",
        "Theorem 1",
        "2^\\ell_\\bullet",
        "matching-restriction",
        "Acceptance gates before changing theorem status",
        "The current canonical TeX is nevertheless not ready to assert Theorem 1",
        "**Theorem 1:** RED",
    )
    missing = [marker for marker in markers if marker not in audit]
    require(not missing, f"audit markers missing: {missing}")

    for item in manifest["items"]:
        start, end = item["statement_lines"]
        require(
            f"{start}--{end}" in audit or f"{start}–{end}" in audit,
            f"audit range absent for {item['id']}",
        )
        if item["id"] in BOXED_IDS:
            require(boxed_token(item["id"]) in audit, f"audit identifier absent for {item['id']}")


def main() -> None:
    for path in (SOURCE, AUDIT, MANIFEST):
        require(path.is_file(), f"missing file: {path}")

    raw = SOURCE.read_bytes()
    text = raw.decode("utf-8")
    lines = text.splitlines()
    audit = AUDIT.read_text(encoding="utf-8")
    manifest = load_manifest()

    require(len(lines) >= 3100, f"canonical source unexpectedly short: {len(lines)}")
    counts = check_manifest(manifest, raw, lines)
    check_source(text)
    check_audit(audit, manifest)

    print("ERDOS 625 LINE-BY-LINE AUDIT CHECK: PASS")
    print(f"  source lines: {len(lines)}")
    print(f"  audited items: {len(manifest['items'])}")
    print(f"  statuses: {dict(sorted(counts.items()))}")
    print(f"  source blob: {git_blob_sha(raw)}")
    print("  RED boxed chain: Lemma 8.3 -> Proposition 9.2 -> Theorem 1")
    print("  scope: audit coverage/status consistency only")


if __name__ == "__main__":
    main()
