#!/usr/bin/env python3
"""Validate the literal theorem-by-theorem audit of the Erdős 625 TeX.

This checker verifies coverage, exact source ranges, status consistency, and
known source defects.  It does not prove any mathematical theorem.
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

ALLOWED_STATUSES = {
    "GREEN",
    "GREEN-REWRITE",
    "AMBER",
    "RED",
    "TYPO/EDITORIAL",
    "SUPERSEDED",
}

REQUIRED_BOXED_IDS = {
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

EXPECTED_BOXED_STATUS = {
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

EXPECTED_BEGIN_LINES = {
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

EXPECTED_PROOF_STARTS = {
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

REQUIRED_EQUATION_TAGS = {
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


def git_blob_sha(raw: bytes) -> str:
    header = f"blob {len(raw)}\0".encode("ascii")
    return hashlib.sha1(header + raw).hexdigest()


def load_manifest() -> dict[str, Any]:
    data = json.loads(MANIFEST.read_text(encoding="utf-8"))
    require(isinstance(data, dict), "manifest root must be an object")
    require(isinstance(data.get("items"), list), "manifest items must be a list")
    return data


def line_slice(lines: list[str], start: int, end: int) -> str:
    require(1 <= start <= end <= len(lines), f"invalid source range {start}-{end}")
    return "\n".join(lines[start - 1 : end])


def validate_manifest_against_source(
    manifest: dict[str, Any], source_raw: bytes, source_lines: list[str]
) -> Counter[str]:
    require(manifest.get("source") == "625/arxiv/main.tex", "manifest source mismatch")
    require(
        manifest.get("source_blob_sha") == git_blob_sha(source_raw),
        "manifest source blob SHA is stale",
    )

    items = manifest["items"]
    ids = [item.get("id") for item in items]
    require(all(isinstance(item_id, str) and item_id for item_id in ids), "invalid item id")
    require(len(ids) == len(set(ids)), "duplicate item ids in manifest")
    item_by_id = {item["id"]: item for item in items}

    require(REQUIRED_BOXED_IDS <= set(item_by_id), "boxed theorem coverage is incomplete")

    for item in items:
        item_id = item["id"]
        status = item.get("status")
        require(status in ALLOWED_STATUSES, f"{item_id}: invalid status {status!r}")
        require(isinstance(item.get("blocking"), bool), f"{item_id}: blocking must be bool")
        require(item.get("issue"), f"{item_id}: missing issue field")
        require(item.get("repair"), f"{item_id}: missing repair field")
        statement_range = item.get("statement_lines")
        proof_range = item.get("proof_lines")
        require(
            isinstance(statement_range, list) and len(statement_range) == 2,
            f"{item_id}: malformed statement range",
        )
        require(
            isinstance(proof_range, list) and len(proof_range) == 2,
            f"{item_id}: malformed proof range",
        )
        statement_text = line_slice(source_lines, *statement_range)
        line_slice(source_lines, *proof_range)
        if item_id in REQUIRED_BOXED_IDS:
            title = item["title"]
            require(title in statement_text, f"{item_id}: title absent from statement range")

    for item_id, expected_status in EXPECTED_BOXED_STATUS.items():
        require(
            item_by_id[item_id]["status"] == expected_status,
            f"{item_id}: expected {expected_status}, found {item_by_id[item_id]['status']}",
        )
        require(
            item_by_id[item_id]["statement_lines"][0] == EXPECTED_BEGIN_LINES[item_id],
            f"{item_id}: statement begin line drifted",
        )

    for item_id, proof_start in EXPECTED_PROOF_STARTS.items():
        require(
            item_by_id[item_id]["proof_lines"][0] == proof_start,
            f"{item_id}: proof begin line drifted",
        )
        proof_head = line_slice(source_lines, proof_start, min(proof_start + 3, len(source_lines)))
        require(
            "Proof" in proof_head or "\\begin{proof}" in proof_head,
            f"{item_id}: proof marker absent at recorded start",
        )

    theorem_blockers = {
        item_id
        for item_id in REQUIRED_BOXED_IDS
        if item_by_id[item_id]["status"] == "RED"
    }
    require(
        theorem_blockers == {"T1", "L8.3", "P9.2"},
        f"unexpected boxed RED set: {sorted(theorem_blockers)}",
    )
    require(
        manifest.get("single_blocking_chain") == ["Lemma 8.3", "Proposition 9.2", "Theorem 1"],
        "blocking chain changed unexpectedly",
    )

    return Counter(item["status"] for item in items)


def validate_source_invariants(source_text: str) -> None:
    tags = re.findall(r"\\tag\{([^}]+)\}", source_text)
    counts = Counter(tags)
    duplicates = sorted(tag for tag, count in counts.items() if count > 1)
    require(not duplicates, f"duplicate equation tags: {duplicates}")
    missing_tags = sorted(REQUIRED_EQUATION_TAGS - set(tags))
    require(not missing_tags, f"required equation tags missing: {missing_tags}")

    require("2^\\ell_\\bullet" in source_text, "known equation (7.2) typo no longer present")
    require(
        "2^{\\ell_\\bullet}" not in source_text,
        "canonical source was silently repaired without updating this audit",
    )
    require(
        "We prove that, for \\(G_n\\sim G(n,1/2)\\)" in source_text,
        "audit-safe abstract may have replaced the canonical claim; refresh audit",
    )
    require("3a/4+O(1)" in source_text, "imprecise Section VIII range marker disappeared")


def validate_audit_text(audit_text: str, manifest: dict[str, Any]) -> None:
    required_markers = (
        "literal line-by-line and theorem-by-theorem audit",
        "single submission-blocking chain",
        "Lemma 8.3",
        "Proposition 9.2",
        "Theorem 1",
        "2^\\ell_\\bullet",
        "three-quarter",
        "matching-restriction",
        "Acceptance gates before changing theorem status",
    )
    missing = [marker for marker in required_markers if marker not in audit_text]
    require(not missing, f"audit markdown missing markers: {missing}")

    for item in manifest["items"]:
        require(item["title"] in audit_text, f"audit markdown omits {item['title']}")
        start, end = item["statement_lines"]
        range_tokens = (f"{start}--{end}", f"{start}–{end}")
        require(
            any(token in audit_text for token in range_tokens),
            f"audit markdown omits source range for {item['id']}",
        )

    require(
        "The current canonical TeX is nevertheless not ready to assert Theorem 1" in audit_text,
        "final status boundary is missing",
    )
    require(
        "Theorem 1:** RED" in audit_text or "Theorem 1:** RED" in audit_text.replace(" ", " "),
        "final theorem RED classification is missing",
    )


def main() -> None:
    for path in (SOURCE, AUDIT, MANIFEST):
        require(path.is_file(), f"missing required file: {path}")

    source_raw = SOURCE.read_bytes()
    source_text = source_raw.decode("utf-8")
    source_lines = source_text.splitlines()
    audit_text = AUDIT.read_text(encoding="utf-8")
    manifest = load_manifest()

    require(len(source_lines) >= 3100, f"canonical TeX unexpectedly short: {len(source_lines)}")
    status_counts = validate_manifest_against_source(manifest, source_raw, source_lines)
    validate_source_invariants(source_text)
    validate_audit_text(audit_text, manifest)

    print("ERDOS 625 LINE-BY-LINE AUDIT CHECK: PASS")
    print(f"  canonical source lines: {len(source_lines)}")
    print(f"  audited items: {len(manifest['items'])}")
    print(f"  status counts: {dict(sorted(status_counts.items()))}")
    print(f"  source blob: {git_blob_sha(source_raw)}")
    print("  boxed RED chain: Lemma 8.3 -> Proposition 9.2 -> Theorem 1")
    print("  scope: coverage and status consistency; not a proof of the mathematics")


if __name__ == "__main__":
    main()
