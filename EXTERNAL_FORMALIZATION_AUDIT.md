# External Lean formalization audit

Audit date: 2026-07-13.

## Scope

The repository
[`google-deepmind/formal-conjectures`](https://github.com/google-deepmind/formal-conjectures)
was inspected at `main` commit
`b2e608fc52d765510915a244bb69b1a2741acc3c`, together with its open draft
[Problem 625 pull request #570](https://github.com/google-deepmind/formal-conjectures/pull/570)
at commit `ae58413d143b432ae036c501e6ebe48ef68e673b` and tracking
[issue #2122](https://github.com/google-deepmind/formal-conjectures/issues/2122).
This was a comparison audit only. No code was copied and the project acquired
no dependency on `formal-conjectures`.

## Useful material

The upstream
[`Coloring.lean`](https://github.com/google-deepmind/formal-conjectures/blob/b2e608fc52d765510915a244bb69b1a2741acc3c/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Coloring.lean)
contains a compact `Cocolorable` predicate and an `ℕ∞`-valued
`cochromaticNumber`. It confirms that representing a cocolouring by a map to
`Fin k`, with every fibre either independent or complete, is a natural Lean
interface. The Erdős-problem directory also provides useful naming, docstring,
and source-link conventions.

The local development already has the stronger API required by the proof:
an explicit `CoColoring` witness with part kinds, a natural-valued minimum for
finite graphs, its exact minimum characterization, monotonicity in the palette,
and induced-set/complement concatenation. Replacing it with the upstream
definition would lose proved infrastructure and introduce an unnecessary
dependency.

## Why pull request #570 is not imported

The pull request is a statement-only draft, not a proof. Its current target is
not extensionally the manuscript theorem:

- the displayed gap is accidentally formalized as `χ G - χ G`, rather than
  `χ G - ζ G`;
- the subtraction is natural-number subtraction and is therefore truncated;
- the random-graph construction and convergence quantifiers do not provide the
  local project's measurable-event probability formulation; and
- the file contains proof placeholders, as expected for the
  `formal-conjectures` benchmark.

By contrast, `Erdos625Statement` uses mathlib's binomial-random-graph measure,
a measurable event, real-valued subtraction, and full-sequence convergence of
the event probabilities to one. The external draft therefore supplies no
proof obligation that can be discharged by reuse. It remains useful only as a
cross-check of vocabulary and repository conventions.

## Licensing note

The inspected Lean files in `formal-conjectures` carry Apache-2.0 notices.
Because no code was copied, no third-party notice is required in this project.
Any future reuse must be separately reviewed and attributed under the upstream
license.
