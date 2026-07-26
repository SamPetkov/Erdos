# Codex–Antigravity Private Review Contract

This contract applies to the entire repository. It coordinates Codex reviews
with Antigravity implementation work through the current private pull request.

## Repository boundary

- Work only in this private repository and its private pull requests.
- Never push to, open or update a pull request in, or merge into a public
  repository.
- A private pull request is mutable. A review directive may require changing,
  replacing, renaming, moving, or deleting existing files and proofs, not only
  adding new material.
- Prefer ordinary follow-up commits on the existing private PR branch. Rebase,
  history rewrite, or force-push only when the directive explicitly requests it.
- Antigravity must not merge a PR. Private merge authorization follows an
  independent Codex validation or an explicit user instruction.

## Review mailbox

Codex communicates through structured comments on the current private PR.
Before modifying a PR branch, Antigravity must:

1. identify the private PR associated with the current branch;
2. read all PR comments and locate the latest unresolved
   `CODEX-DIRECTIVE v1`;
3. acknowledge that directive with an `ANTIGRAVITY-REPORT v1` comment whose
   result is `IN_PROGRESS`;
4. implement exactly the requested bounded change;
5. post a final `ANTIGRAVITY-REPORT v1` with evidence and the new head SHA.

The latest directive supersedes an older directive only where they conflict.
If the target statement, base SHA, permitted files, or acceptance criteria are
ambiguous, report `BLOCKED` instead of guessing.

## Existing-PR correction rule

A directive is not append-only. When the defect is in existing work,
Antigravity should correct that work directly. Appropriate actions include:

- revising an existing theorem statement or proof;
- replacing an invalid reduction with a faithful one;
- removing a false claim, stale audit note, or redundant workaround;
- updating imports, build configuration, tests, and documentation;
- reorganizing or renaming existing files when needed for a focused repair;
- reverting a broken portion of the PR while retaining independently valid
  parts.

Do not preserve incorrect code merely to minimize the diff. Do preserve
unrelated user work and keep the repair focused and reviewable.

## Exact theorem brief gate

Do not submit or continue an Aristotle request unless the directive contains an
exact user-approved theorem brief with:

- repository and frozen commit SHA;
- exact declaration name and verbatim Lean signature;
- definitions and assumptions that must remain unchanged;
- permitted files and dependencies;
- the concrete Lean error or mathematical obstruction;
- forbidden shortcuts and required validation;
- an explicit statement that Aristotle submission is approved.

AXLE may be used for read-only checking or bounded proof assistance, but its
output is only a candidate until it passes the validation gates below.

## Validation gates

Before reporting `READY_FOR_CODEX_REVIEW`, Antigravity must provide:

- exact statement-fidelity confirmation;
- Lean replay against the repository-pinned toolchain;
- warning-fatal results for the changed modules;
- a scan showing no `sorry`, `admit`, project `axiom`, `unsafe`,
  `native_decide`, or `implemented_by`;
- `#print axioms` output for the changed theorem, with only standard axioms;
- mathematical semantic review, including edge cases and dependency direction;
- the commands run, their exit status, changed files, and head commit SHA.

An Aristotle or AXLE success message alone never satisfies these gates.
Infrastructure failures such as billing, runner, network, or cache failures
must be reported separately from Lean or mathematical failures.

## Review outcomes

Codex answers with `CODEX-REVIEW v1`:

- `PRIVATE-VALIDATED`: the exact private head passed independent review;
- `CHANGES-REQUIRED`: follow the attached next directive on the same PR;
- `REJECTED`: do not reuse the candidate without a new brief;
- `BLOCKED`: no further action until the stated dependency changes.

Validation applies only to the reviewed commit SHA. A later PR update must be
reviewed again.

## Formalization DAG control

Before selecting a theorem or changing proof code, validate and read
`.agent-coordination/formalization-dag.json` using
`scripts/formalization_dag.py`. Follow
`.agents/workflows/advance-formalization-dag.md`. Only a `ready` node paired
with an active user-approved exact brief may be sent to Aristotle. Public
repositories are read-only, and tracked public PRs must be refreshed as full
mutable trees rather than append-only patches.
