# Lean formalization

This directory contains the incremental Lean 4 formalization of the proposed
resolution of Erdős Problem 625.

**Authors:** Samuil Petkov & ChatGPT 5.6

The confirmed scope, conventions, validation criteria, failure modes, and
checkpoint policy are recorded in [`FORMALIZATION_BRIEF.md`](FORMALIZATION_BRIEF.md).
The comparison with DeepMind's statement-only Problem 625 draft is recorded in
[`EXTERNAL_FORMALIZATION_AUDIT.md`](EXTERNAL_FORMALIZATION_AUDIT.md); no code
was copied and no dependency was added.

## Reproducible toolchain

- Lean: `v4.31.0`
- mathlib: `v4.31.0`
- Aristotle: optional isolated proof search on its fixed Lean `v4.28.0`
  service toolchain; no returned file is accepted without a local Lean 4.31
  port and the full repository gates.  See
  [`ARISTOTLE_WORKFLOW.md`](ARISTOTLE_WORKFLOW.md).

Build from this directory with:

```powershell
lake exe cache get
lake build --wfail
```

Do not run `lake update` for an ordinary reproduction: the tracked manifest
already fixes every dependency commit.  Use it only for an intentional,
reviewed dependency refresh.

## Integrity policy

A milestone is called complete only when its imported modules compile without
`sorry`, `admit`, project-defined axioms, or hidden generated proof objects.
Finite computations may test definitions but are never substituted for an
asymptotic proof.  `FORMALIZATION_LEDGER.md` maps the public declarations to
the authoritative manuscript and records all remaining obligations explicitly.

## Current scope

Milestone M0 formalizes the finite labelled-graph model, chromatic and
cochromatic invariants and minimum semantics, the inequality `ζ(G) ≤ χ(G)`,
induced-set cocolouring concatenation, the exact `G(n, 1/2)` probability law
and uniform singleton mass, event measurability, and the full-sequence target
proposition. The independent M0 results are in
[`M0_AUDIT_2026-07-13.md`](M0_AUDIT_2026-07-13.md).

The verified post-M0 bricks now include exact phase/floor arithmetic and
adjacent first-moment ratios; Markov, Paley--Zygmund, and binomial-tail tools;
the complete finite independent-set first moment; the endpoint-uniform phase
expansion and its genuine consequences (2.3), (2.4), and (2.9); and exact
Boolean-cube and arbitrary finite-block bounded differences.  The uniform
vertex-block product law is proved equivalent to `G(n,1/2)`, including event
and expectation transport.  The largest induced `k`-cocolourable subgraph is
defined, shown one-vertex Lipschitz, characterized at full capacity, and given
one- and two-sided graph-law tails with the `(n-1)/4` block profile.  The
capacity maximum is attained by an explicit induced core whose complement has
exact size `n-capacity`; concatenating its cocolouring with an ordinary
colouring of the complement proves the deterministic manuscript inequality
(10.9).  A generic probability lemma also converts an endpoint seed of mass
`exp(-Λ)` and a positive-proxy one-sided sub-Gaussian tail into the exact
endpoint-to-expectation cost `sqrt(2vΛ)`; its graph-specific specialization
proves `n-E[capacity]≤sqrt((n-1)Λ/2)` for `n≥2`.  The
finite-support `{2,3,4,5}` exponential family also has kernel-checked mean
inversion, a zero-safe entropy variational optimizer, and a sharp
coordinatewise score-stability theorem for the optimized value at each fixed
interior target.

The early reproduced build, source, axiom, and independent statement checks
are recorded in
[`M1A_M2_SETUP_AUDIT_2026-07-13.md`](M1A_M2_SETUP_AUDIT_2026-07-13.md).
The subsequent cross-audit of the Boolean-cube bounded-differences theorem
and the explicit phase estimates is in
[`M1B_M2_ESTIMATES_AUDIT_2026-07-13.md`](M1B_M2_ESTIMATES_AUDIT_2026-07-13.md).
The current declaration-by-declaration hashes and remaining obligations are
kept in the formalization ledger.  The combined phase, vertex-block, capacity,
and rare-seed checkpoint is reproduced in
[`M3_PHASE_BLOCK_AMPLIFICATION_AUDIT_2026-07-13.md`](M3_PHASE_BLOCK_AMPLIFICATION_AUDIT_2026-07-13.md).

The difficult profile-root, unrestricted chromatic lower-location,
signed-moment/overlap, residual-attachment, and complete amplification layers
remain open.  The project therefore does **not** claim Lemma 2.1 or
`Erdos625Statement`. The
[`formalization ledger`](FORMALIZATION_LEDGER.md) is the authoritative
declaration-by-declaration status record.

CI also performs a source gate for placeholders, explicit placeholder-axiom
terms, project `axiom`/`constant` declarations, and `unsafe`, and invokes
Lean with `--wfail`, so Lean's own warning for a proof placeholder is fatal.
The optional external `nanoda` path is disabled; no mutable proof-checker
helper is part of the milestone claim.

## License and citation

The original formalization is covered by the repository's
[CC BY 4.0 license](../../LICENSE) and [scope notice](../../LICENSE_SCOPE.md).
Please cite Samuil Petkov using the repository's
[`CITATION.cff`](../../CITATION.cff) when using this work academically.
