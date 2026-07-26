#!/usr/bin/env python3
"""Validate and query the private formalization dependency DAG.

The repository keeps two related graphs:

* the exhaustive Lean import graph, reconstructed from the configured roots;
* the curated semantic graph in .agent-coordination/formalization-dag.json.

This script is deliberately standard-library only.  It never edits the DAG,
submits proof-search jobs, or changes GitHub state.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path
from typing import Any


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
DAG_PATH = REPOSITORY_ROOT / ".agent-coordination" / "formalization-dag.json"
STATUSES = {
    "needs-review",
    "frozen",
    "ready",
    "running",
    "candidate",
    "lean-validated",
    "welded",
    "blocked",
}
TERMINAL_STATUSES = {"lean-validated", "welded"}
TARGET_REQUIRED = {
    "frozen",
    "ready",
    "running",
    "candidate",
    "lean-validated",
    "welded",
}
DEPENDENCIES_REQUIRED = {
    "ready",
    "running",
    "candidate",
    "lean-validated",
    "welded",
}
APPROVAL_REQUIRED = {"ready", "running", "candidate"}
DECLARATION_RE = re.compile(
    r"(?m)^[ \t]*(?:noncomputable[ \t]+)?"
    r"(?:theorem|lemma|def|abbrev|opaque)[ \t]+{name}\b"
)
IMPORT_RE = re.compile(r"(?m)^[ \t]*import[ \t]+([A-Za-z0-9_.'-]+)[ \t]*$")
NAMESPACE_RE = re.compile(r"^namespace[ \t]+([A-Za-z0-9_.'-]+)[ \t]*$")
SECTION_RE = re.compile(
    r"^(?:(?:noncomputable|private)[ \t]+)?section(?:[ \t]+[A-Za-z0-9_.'-]+)?[ \t]*$"
)
END_RE = re.compile(r"^end(?:[ \t]+[A-Za-z0-9_.'-]+)?[ \t]*$")


class DagError(RuntimeError):
    """A deterministic DAG validation error."""


def load_dag() -> dict[str, Any]:
    if not DAG_PATH.is_file():
        raise DagError(f"missing DAG: {DAG_PATH}")
    try:
        return json.loads(DAG_PATH.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise DagError(f"invalid JSON in {DAG_PATH}: {exc}") from exc


def git_head() -> str:
    result = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=REPOSITORY_ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    return result.stdout.strip()


def git_is_ancestor(commit: str) -> bool:
    result = subprocess.run(
        ["git", "merge-base", "--is-ancestor", commit, "HEAD"],
        cwd=REPOSITORY_ROOT,
        capture_output=True,
        text=True,
    )
    return result.returncode == 0


def normalize_signature(value: str) -> str:
    return re.sub(r"\s+", " ", value).strip()


def enclosing_namespace(text: str, position: int) -> str:
    blocks: list[list[str]] = []
    for raw_line in text[:position].splitlines():
        line = raw_line.split("--", 1)[0].strip()
        namespace_match = NAMESPACE_RE.fullmatch(line)
        if namespace_match:
            blocks.append(namespace_match.group(1).split("."))
        elif SECTION_RE.fullmatch(line):
            blocks.append([])
        elif END_RE.fullmatch(line) and blocks:
            blocks.pop()
    return ".".join(part for block in blocks for part in block)


def extract_signature(target: dict[str, Any]) -> str:
    declaration = target.get("declaration")
    source = target.get("source")
    if not isinstance(declaration, str) or not declaration:
        raise DagError("target declaration must be a nonempty string")
    if not isinstance(source, str) or not source:
        raise DagError(f"{declaration}: target source must be a nonempty string")

    source_path = (REPOSITORY_ROOT / source).resolve()
    try:
        source_path.relative_to(REPOSITORY_ROOT)
    except ValueError as exc:
        raise DagError(f"{declaration}: source escapes repository: {source}") from exc
    if not source_path.is_file():
        raise DagError(f"{declaration}: missing source file: {source}")

    local_name = declaration.rsplit(".", 1)[-1]
    text = source_path.read_text(encoding="utf-8")
    pattern = re.compile(DECLARATION_RE.pattern.format(name=re.escape(local_name)))
    match = pattern.search(text)
    if match is None:
        raise DagError(f"{declaration}: declaration not found in {source}")
    namespace = enclosing_namespace(text, match.start())
    inferred_name = f"{namespace}.{local_name}" if namespace else local_name
    if inferred_name != declaration:
        raise DagError(
            f"{declaration}: source namespace resolves declaration as {inferred_name}"
        )
    body_start = text.find(":=", match.start())
    if body_start < 0:
        raise DagError(f"{declaration}: could not find ':=' after declaration")
    signature = text[match.start() : body_start].strip()
    return signature


def signature_hash(signature: str) -> str:
    normalized = normalize_signature(signature)
    return hashlib.sha256(normalized.encode("utf-8")).hexdigest()


def validate_targets(nodes: list[dict[str, Any]]) -> list[str]:
    messages: list[str] = []
    seen_declarations: dict[str, str] = {}
    for node in nodes:
        node_id = node["id"]
        status = node["status"]
        target = node.get("target")
        if status in TARGET_REQUIRED and not isinstance(target, dict):
            raise DagError(f"{node_id}: status {status!r} requires an exact target")
        if target is None:
            continue
        if not isinstance(target, dict):
            raise DagError(f"{node_id}: target must be an object or null")
        declaration = target.get("declaration")
        if declaration in seen_declarations:
            raise DagError(
                f"{node_id}: target declaration duplicates "
                f"{seen_declarations[declaration]}: {declaration}"
            )
        seen_declarations[declaration] = node_id
        signature = extract_signature(target)
        actual_hash = signature_hash(signature)
        expected_hash = target.get("signature_sha256")
        if expected_hash == "AUTO":
            if status in TARGET_REQUIRED:
                raise DagError(
                    f"{node_id}: status {status!r} cannot use an AUTO signature hash"
                )
            messages.append(f"{node_id}: signature hash pending freeze: {actual_hash}")
        elif not isinstance(expected_hash, str) or not re.fullmatch(
            r"[0-9a-f]{64}", expected_hash
        ):
            raise DagError(f"{node_id}: signature_sha256 must be 64 lowercase hex digits")
        elif expected_hash != actual_hash:
            raise DagError(
                f"{node_id}: signature drift for {target['declaration']}; "
                f"expected {expected_hash}, got {actual_hash}"
            )
    return messages


def validate_semantic_graph(dag: dict[str, Any]) -> tuple[dict[str, dict[str, Any]], list[str]]:
    nodes = dag.get("nodes")
    roots = dag.get("root_nodes")
    if not isinstance(nodes, list) or not nodes:
        raise DagError("nodes must be a nonempty array")
    if not isinstance(roots, list) or not roots:
        raise DagError("root_nodes must be a nonempty array")

    by_id: dict[str, dict[str, Any]] = {}
    for node in nodes:
        if not isinstance(node, dict):
            raise DagError("every node must be an object")
        node_id = node.get("id")
        status = node.get("status")
        if not isinstance(node_id, str) or not node_id:
            raise DagError("every node needs a nonempty id")
        if node_id in by_id:
            raise DagError(f"duplicate node id: {node_id}")
        if status not in STATUSES:
            raise DagError(f"{node_id}: invalid status {status!r}")
        dependencies = node.get("depends_on", [])
        if not isinstance(dependencies, list) or not all(
            isinstance(item, str) for item in dependencies
        ):
            raise DagError(f"{node_id}: depends_on must be an array of node ids")
        if status in TERMINAL_STATUSES and not node.get("evidence"):
            raise DagError(f"{node_id}: terminal status requires validation evidence")
        by_id[node_id] = node

    for node_id, node in by_id.items():
        for dependency in node.get("depends_on", []):
            if dependency not in by_id:
                raise DagError(f"{node_id}: unknown dependency {dependency}")
            if dependency == node_id:
                raise DagError(f"{node_id}: self dependency")
        if node["status"] in DEPENDENCIES_REQUIRED:
            unfinished = [
                dependency
                for dependency in node.get("depends_on", [])
                if by_id[dependency]["status"] not in TERMINAL_STATUSES
            ]
            if unfinished:
                raise DagError(
                    f"{node_id}: status {node['status']!r} has unfinished "
                    f"dependencies: {unfinished}"
                )
        if node["status"] in APPROVAL_REQUIRED:
            approval = node.get("approval")
            if (
                not isinstance(approval, dict)
                or approval.get("user_approved") is not True
                or not isinstance(approval.get("record"), str)
                or not approval["record"].strip()
            ):
                raise DagError(
                    f"{node_id}: status {node['status']!r} requires a recorded "
                    "user approval of the exact brief"
                )

    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(node_id: str) -> None:
        if node_id in visiting:
            raise DagError(f"semantic dependency cycle reaches {node_id}")
        if node_id in visited:
            return
        visiting.add(node_id)
        for dependency in by_id[node_id].get("depends_on", []):
            visit(dependency)
        visiting.remove(node_id)
        visited.add(node_id)

    for node_id in by_id:
        visit(node_id)

    needed: set[str] = set()

    def collect(node_id: str) -> None:
        if node_id in needed:
            return
        if node_id not in by_id:
            raise DagError(f"unknown root node: {node_id}")
        needed.add(node_id)
        for dependency in by_id[node_id].get("depends_on", []):
            collect(dependency)

    for root in roots:
        collect(root)
    orphaned = sorted(
        node_id
        for node_id, node in by_id.items()
        if node.get("scope", "core") == "core" and node_id not in needed
    )
    if orphaned:
        raise DagError(f"core nodes do not feed a root: {orphaned}")

    messages = validate_targets(nodes)
    return by_id, messages


def module_name(base: Path, source: Path) -> str:
    return ".".join(source.relative_to(base).with_suffix("").parts)


def validate_import_graph(dag: dict[str, Any]) -> list[str]:
    configurations = dag.get("lean_import_graphs")
    if not isinstance(configurations, list) or not configurations:
        raise DagError("lean_import_graphs must be a nonempty array")
    messages: list[str] = []
    reachable_sources: set[Path] = set()

    for configuration in configurations:
        directory = configuration.get("directory")
        root_files = configuration.get("root_files")
        if not isinstance(directory, str) or not isinstance(root_files, list):
            raise DagError("invalid lean_import_graphs entry")
        base = (REPOSITORY_ROOT / directory).resolve()
        if not base.is_dir():
            raise DagError(f"Lean graph directory does not exist: {directory}")

        sources = [
            source
            for source in base.rglob("*.lean")
            if not any(
                part.startswith(".") for part in source.relative_to(base).parts
            )
        ]
        modules = {module_name(base, source): source for source in sources}
        dependencies: dict[str, list[str]] = {}
        for name, source in modules.items():
            imports = IMPORT_RE.findall(source.read_text(encoding="utf-8"))
            dependencies[name] = [item for item in imports if item in modules]

        for root_file in root_files:
            root_path = (base / root_file).resolve()
            if not root_path.is_file():
                raise DagError(f"missing Lean root: {directory}/{root_file}")
            root_name = module_name(base, root_path)
            visiting: set[str] = set()
            closure: set[str] = set()

            def walk(name: str) -> None:
                if name in visiting:
                    raise DagError(f"Lean import cycle at {name}")
                if name in closure:
                    return
                visiting.add(name)
                for dependency in dependencies.get(name, []):
                    walk(dependency)
                visiting.remove(name)
                closure.add(name)

            walk(root_name)
            reachable_sources.update(modules[name].resolve() for name in closure)
            messages.append(
                f"{directory}/{root_file}: {len(closure)} internal module(s), acyclic"
            )
    welded_targets = 0
    for node in dag["nodes"]:
        target = node.get("target")
        if node["status"] != "welded" or not isinstance(target, dict):
            continue
        source = (REPOSITORY_ROOT / target["source"]).resolve()
        if source not in reachable_sources:
            raise DagError(
                f"{node['id']}: welded target is absent from every configured "
                f"Lean root: {target['source']}"
            )
        welded_targets += 1
    messages.append(f"{welded_targets} welded target source(s) reachable from Lean roots")
    return messages


def validate_candidate_streams(dag: dict[str, Any]) -> None:
    streams = dag.get("candidate_streams")
    if not isinstance(streams, list):
        raise DagError("candidate_streams must be an array")
    for stream in streams:
        if not isinstance(stream, dict):
            raise DagError("every candidate stream must be an object")
        repository = stream.get("repository")
        pull_requests = stream.get("pull_requests")
        if not isinstance(repository, str) or not repository:
            raise DagError("candidate stream repository must be a nonempty string")
        if (
            not isinstance(pull_requests, list)
            or not all(isinstance(number, int) and number > 0 for number in pull_requests)
            or len(set(pull_requests)) != len(pull_requests)
        ):
            raise DagError(f"{repository}: pull_requests must be unique positive integers")
        if stream.get("tracking") != "mutable-head":
            raise DagError(f"{repository}: candidate stream must track mutable-head")
        head_snapshot = stream.get("head_snapshot")
        expected_keys = {str(number) for number in pull_requests}
        if not isinstance(head_snapshot, dict) or set(head_snapshot) != expected_keys:
            raise DagError(
                f"{repository}: head_snapshot keys must exactly match pull_requests"
            )
        for number, sha in head_snapshot.items():
            if not isinstance(sha, str) or not re.fullmatch(r"[0-9a-f]{40}", sha):
                raise DagError(
                    f"{repository} PR {number}: head snapshot must be a full Git SHA"
                )
        if not isinstance(stream.get("snapshot_captured_at"), str):
            raise DagError(f"{repository}: snapshot_captured_at is required")
        sync_rule = str(stream.get("sync_rule", "")).lower()
        for required_word in ("modifications", "deletions", "renames"):
            if required_word not in sync_rule:
                raise DagError(
                    f"{repository}: sync_rule must cover {required_word}"
                )


def validate(dag: dict[str, Any]) -> tuple[dict[str, dict[str, Any]], list[str]]:
    if dag.get("schema_version") != 1:
        raise DagError("schema_version must be 1")
    if dag.get("private_only") is not True:
        raise DagError("private_only must be true")
    repository = dag.get("repository")
    if not isinstance(repository, str) or not repository.endswith("-private"):
        raise DagError("repository must identify a private staging repository")
    baseline = dag.get("baseline", {})
    commit = baseline.get("commit")
    if not isinstance(commit, str) or not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise DagError("baseline.commit must be a full lowercase Git SHA")
    if not git_is_ancestor(commit):
        raise DagError(f"baseline commit is not an ancestor of HEAD: {commit}")
    validate_candidate_streams(dag)
    public_policy = str(
        dag.get("automation_policy", {}).get("public_repositories", "")
    ).lower()
    if "read-only" not in public_policy or "never merge" not in public_policy:
        raise DagError(
            "automation_policy.public_repositories must be read-only and forbid merges"
        )
    by_id, semantic_messages = validate_semantic_graph(dag)
    import_messages = validate_import_graph(dag)
    return by_id, semantic_messages + import_messages


def actionable_nodes(by_id: dict[str, dict[str, Any]]) -> tuple[list[str], list[str]]:
    ready: list[str] = []
    review: list[str] = []
    for node_id, node in by_id.items():
        dependencies_done = all(
            by_id[dependency]["status"] in TERMINAL_STATUSES
            for dependency in node.get("depends_on", [])
        )
        if node["status"] == "ready" and dependencies_done:
            ready.append(node_id)
        elif node["status"] == "needs-review" and dependencies_done:
            review.append(node_id)
    return sorted(ready), sorted(review)


def render_brief(dag: dict[str, Any], node: dict[str, Any]) -> str:
    target = node.get("target")
    if not isinstance(target, dict):
        raise DagError(
            f"{node['id']} has no frozen target; review and freeze its statement first"
        )
    signature = extract_signature(target)
    scope = node.get("permitted_scope", [target["source"]])
    checks = node.get(
        "acceptance_checks",
        [
            "warning-fatal Lean replay under the pinned repository toolchain",
            "scan for sorry/admit/project axiom/unsafe/native_decide/implemented_by",
            "#print axioms with only standard Lean/Mathlib axioms",
            "independent mathematical and statement-fidelity review",
        ],
    )
    return f"""Brief ID: {node['id']}
Repository and frozen commit SHA: {dag['repository']} @ {git_head()}
Exact declaration: {target['declaration']}
Verbatim theorem signature:
```lean
{signature}
```
Mathematical purpose: {node.get('purpose', '')}
Current obstruction: {node.get('blocker') or 'NONE RECORDED'}
Permitted files and dependencies:
{chr(10).join(f'- {item}' for item in scope)}
Forbidden shortcuts: sorry, admit, project axiom, unsafe, native_decide,
implemented_by, theorem weakening, hidden assumptions, circular dependencies,
or unrelated refactoring.
Acceptance checks:
{chr(10).join(f'- {item}' for item in checks)}
Aristotle authorization: NOT APPROVED
"""


def main() -> int:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    if hasattr(sys.stderr, "reconfigure"):
        sys.stderr.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("validate")
    subparsers.add_parser("next")
    subparsers.add_parser("hashes")
    brief_parser = subparsers.add_parser("brief")
    brief_parser.add_argument("node_id")
    args = parser.parse_args()

    try:
        dag = load_dag()
        by_id, messages = validate(dag)
        if args.command == "validate":
            counts = Counter(node["status"] for node in by_id.values())
            print(
                f"OK: {dag['project']}: {len(by_id)} semantic nodes; "
                + ", ".join(f"{key}={counts[key]}" for key in sorted(counts))
            )
            for message in messages:
                print(message)
        elif args.command == "next":
            ready, review = actionable_nodes(by_id)
            if ready:
                print("READY")
                for node_id in ready:
                    print(f"- {node_id}: {by_id[node_id]['title']}")
            else:
                print("NO READY FROZEN THEOREM")
                print("STATEMENT REVIEW FRONTIER")
                for node_id in review:
                    print(f"- {node_id}: {by_id[node_id]['title']}")
        elif args.command == "hashes":
            for node_id, node in by_id.items():
                target = node.get("target")
                if isinstance(target, dict):
                    print(f"{node_id} {signature_hash(extract_signature(target))}")
        elif args.command == "brief":
            if args.node_id not in by_id:
                raise DagError(f"unknown node: {args.node_id}")
            print(render_brief(dag, by_id[args.node_id]))
        return 0
    except (DagError, subprocess.CalledProcessError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
