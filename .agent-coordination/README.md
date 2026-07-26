# Private PR Agent Mailbox

The live mailbox is the comment stream of the private pull request. These
markers make requests and reports easy for both agents to find and audit.

## Codex directive

```markdown
<!-- CODEX-DIRECTIVE v1 -->
Directive-ID: <repository>-PR<number>-<sequence>
State: ACTION_REQUIRED
Review-SHA: <full commit SHA reviewed by Codex>
Target-PR: <private PR URL>

Problem:
<exact Lean error, mathematical defect, review finding, or integration issue>

Required change:
<bounded requested outcome; this may change or remove existing PR work>

Frozen theorem target:
<exact declaration and verbatim signature, or "not a theorem request">

Permitted scope:
<files and dependencies that may change>

Allowed PR mutations:
<modify/delete/rename/add; state whether rebase or force-push is permitted>

Acceptance checks:
<exact Lean, warning, placeholder, axiom, and semantic checks>

Aristotle authorization:
<APPROVED with the exact brief, or NOT APPROVED>

Non-goals:
<work that must not be attempted>
```

## Antigravity report

```markdown
<!-- ANTIGRAVITY-REPORT v1 -->
Directive-ID: <matching directive ID>
Result: IN_PROGRESS | READY_FOR_CODEX_REVIEW | BLOCKED | NEEDS_BRIEF
Head-SHA: <full current commit SHA, or NONE>

Changes:
<modified, deleted, renamed, and added files; describe corrections to existing work>

Statement fidelity:
<comparison with the frozen target>

Validation:
<commands, exit codes, warning-fatal result, placeholder scan, and #print axioms>

Mathematical review:
<why the change proves the requested claim and any edge cases checked>

Remaining blocker:
<NONE or one concrete next obligation>
```

## Codex verdict

```markdown
<!-- CODEX-REVIEW v1 -->
Directive-ID: <matching directive ID>
Reviewed-SHA: <full commit SHA>
Verdict: PRIVATE-VALIDATED | CHANGES-REQUIRED | REJECTED | BLOCKED

Evidence:
<independent Lean replay, axiom audit, and semantic review>

Next action:
<NONE or the next bounded directive>
```

`PRIVATE-VALIDATED` applies only to the exact reviewed SHA. Any later update,
including a modification of existing proof code, invalidates that verdict until
the new head is checked.
