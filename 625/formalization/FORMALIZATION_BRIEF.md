# Confirmed Lean formalization brief

Confirmed by the user on 2026-07-13: proceed brick by brick in Lean, without
Aristotle.

## Exact question and deliverable

Translate the candidate proof of manuscript equation (0.1) into a reproducible
Lean 4/mathlib development.  The final acceptance criterion is a theorem of
`Erdos625Statement`, with every dependency kernel-checked and with no `sorry`,
`admit`, project-defined axiom, or numerical experiment standing in for an
asymptotic proof.

## Definitions and conventions

- Graphs are labelled simple graphs on `Fin n`.
- `G(n,1/2)` is mathlib's binomial random graph measure.
- `χ` is the minimum number of independent colour classes.
- `ζ` is the minimum number of vertex classes, each a clique or an independent
  set; unused palette entries are allowed, so `k` means “at most `k` parts.”
- All manuscript logarithms are natural.  The invariant gap is embedded in
  `ℝ`, so subtraction is not truncated.
- The target is convergence of event probabilities along the full sequence
  `n → ∞`; no coupling between different values of `n` is assumed.

## Scope and non-goals

The scope is an analytical formal proof of the stated probability limit.
Finite Python checks remain diagnostics only.  This work does not establish
priority, publication, external peer review, or official resolution status,
and it will not silently strengthen a one-sided estimate or replace a hard
overlap lemma by an equivalent global assertion.

## Candidate routes

1. Follow the manuscript dependency chain directly: finite identities, phase
   expansion, variational roots, chromatic lower location, signed first moment,
   exact overlap representation, partial diagonals, high-cell transportation,
   residual attachments, second moment, and amplification.
2. Reuse existing mathlib probability/graph/asymptotic APIs where their
   quantifiers match exactly.
3. Preserve an alternate finite combinatorial formulation for bottlenecks
   whose analytic statement is awkward in Lean; equivalence must be proved
   before switching formulations.

## Evidence and validation

- pin Lean and every package revision;
- build the imported root module at every milestone;
- reject `sorry` in CI and inspect `#print axioms` locally;
- prove sample-space measurability and model identities rather than relying on
  notation alone;
- audit endpoint uniformity, signs, inequality directions, rounding,
  exceptional regimes, and all quantifier dependencies;
- obtain an independent adversarial review for each published milestone.

Likely failure modes are nonuniform `O(·)` terms, circular root localization,
unproved existence/uniqueness before choice, missing endpoint cases, an
uncontrolled sum over overlap profiles, equality inferred from a one-sided
residual bound, and loss of the explicit constant during rounding or
amplification.

## Cost and checkpoints

M0 (model and target) is a modest compilation/audit milestone.  The phase and
overlap layers are a long research formalization and may require substantial
new mathlib infrastructure.  User confirmation is required after M0 and again
before any expensive broad campaign or change of mathematical route.  A
checkpoint may report a precise open lemma; it must never report the full
theorem as proved while that lemma remains open.
