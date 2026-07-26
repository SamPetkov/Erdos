# Apply the latest Codex review

Use this workflow on a private PR branch after Codex has reviewed it.

1. Read `AGENTS.md` and `.agent-coordination/README.md`.
2. Confirm that the remote is this private repository and identify the current
   branch and associated PR.
3. Fetch the PR metadata, comments, reviews, and checks. Do not switch to or
   write to a public repository.
4. Locate the latest unresolved `<!-- CODEX-DIRECTIVE v1 -->` comment.
5. Check that its review SHA is an ancestor of, or exactly matches, the current
   head. If the branch has moved incompatibly, report `BLOCKED`.
6. Post an `ANTIGRAVITY-REPORT v1` acknowledgment with result `IN_PROGRESS`.
7. Inspect the complete relevant diff and dependencies. The requested repair
   may update existing files; do not assume that only new files may be added.
8. Implement the smallest faithful correction. Preserve unrelated work.
9. Run the directive's targeted Lean checks and all repository validation gates
   that are available. Distinguish runner/infrastructure failure from a Lean
   error.
10. Commit and push the repair to the same private PR branch unless the
    directive specifies a different private branch.
11. Post a final `ANTIGRAVITY-REPORT v1` using the template in
    `.agent-coordination/README.md`.
12. Stop for independent Codex review. Do not merge the private PR and do not
    create, update, or merge a public PR.

If no exact directive exists, do not invent one. Report `BLOCKED` and request a
Codex review or an exact user-approved theorem brief.
