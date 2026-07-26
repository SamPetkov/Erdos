# Advance the formalization DAG

Use this workflow only in the private repository.

1. Read `AGENTS.md`, `.agent-coordination/README.md`, and
   `.agent-coordination/FORMALIZATION_DAG.md`.
2. Run `python scripts/formalization_dag.py validate`. Stop if the graph,
   frozen signature, or Lean import closure has drifted.
3. Read the private PR mailbox. A `CODEX-DIRECTIVE v1` comment is required
   before editing. Its reviewed SHA and scope must cover the current head.
4. Run `python scripts/formalization_dag.py next`.
5. If the frontier says `STATEMENT REVIEW`, draft a precise theorem statement,
   hypothesis ledger, dependency boundary, and minimal candidate lemma. Do not
   run proof search. Return `NEEDS_BRIEF`.
6. A node may move to `frozen` only after Codex checks its declaration,
   verbatim signature, source, and SHA-256. It may move to `ready` only after
   the user explicitly approves that exact brief.
7. Aristotle may be called only when both the DAG node is `ready` and the
   active directive contains `Aristotle authorization: APPROVED` plus the
   complete exact brief. AXLE may suggest candidates but cannot approve them.
8. Put a returned proof in a bounded private branch and mark it `candidate`.
   Stop for independent review; never treat service output as proof evidence.
9. Independently replay Lean with warnings fatal, scan forbidden shortcuts,
   run `#print axioms`, compare the exact statement, and conduct mathematical
   review. Mark `lean-validated` only for the reviewed SHA.
10. Regenerate and check standalone/self-contained artifacts when imports or
    proofs change. Mark `welded` only after private integration and all gates.
11. Refresh tracked public PRs by exact current tree, including modifications,
    deletions, and renames. Public repositories are read-only in this workflow.
12. Post an `ANTIGRAVITY-REPORT v1` and stop for a `CODEX-REVIEW v1` verdict.

Never skip an unfinished dependency, silently alter a theorem, merge a public
PR, or merge a private staging PR.
