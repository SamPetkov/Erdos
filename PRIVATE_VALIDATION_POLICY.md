# Private validation and promotion policy

This repository is a quarantine and validation mirror for active Erdős 625 work.
It is not the publication repository.

## Non-negotiable rules

1. Public repositories are fetched read-only. No workflow in this repository may
   authenticate to or push to `SamPetkov/Erdos`.
2. Branches named `staging/public-*` mirror specific public PR heads. Their
   private pull requests remain draft and are not merged into private `main`.
3. A public PR is eligible for manual promotion only when:
   - `.private-staging/public-pr-<N>.json` records the current public head SHA;
   - its validation state is `success`;
   - the corresponding private commit status is green;
   - all required predecessor staging branches are also green.
4. An Aristotle archive is never accepted merely because it exists or because
   the submission process returned exit code zero. Acceptance requires:
   - explicit terminal remote completion;
   - a safely extractable returned Lean project;
   - fewer `sorry`/`admit` occurrences globally and in the named target;
   - a non-identical source tree;
   - successful `lake build` of the returned project.
5. Aristotle output is an artifact for review. It is not copied into a public
   branch automatically.
6. The hourly monitor may dispatch private validation when a public head changes
   or a private record becomes stale. It never promotes to the public repository.

## Active private stack

- public PR #34 → `staging/public-34-matching-restriction-product`
- public PR #35 → `staging/public-35-matching-restriction-envelope`
- public PR #37 → `staging/public-37-q-only-attachment-envelope`
- public PR #36 → `staging/public-36-section8-endpoint-transport-core`

The dependency chain is `#34 → #35 → #37`; PR #36 is independent.
