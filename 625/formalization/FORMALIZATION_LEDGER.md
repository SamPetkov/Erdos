# Erdős Problem 625 Lean formalization ledger

This ledger separates kernel-checked Lean results from the remaining claims in
the candidate manuscript.  Its manuscript anchor is
[`../proofs/COMPLETE_PROOF_SELF_CONTAINED.md`](../proofs/COMPLETE_PROOF_SELF_CONTAINED.md).

## Status vocabulary

- **proved**: Lean accepts the declaration without `sorry`, `admit`, or a
  project-defined axiom;
- **defined**: Lean accepts a definition of an object or proposition, but no
  proof of the mathematical claim is asserted;
- **open**: the manuscript argument has not yet been translated into Lean;
- **audit only**: numerical or prose evidence, never a substitute for proof.

## Milestone M0: model and target

| Lean declaration | Manuscript anchor | Status | Meaning |
|---|---|---:|---|
| `gapConstant`, `gapConstant_pos`, `gapScale` | (0.1), (1.1) | defined; positivity proved | Natural-log scale and exact positive constant. Small-`n` totalization is irrelevant at `atTop`. |
| `LabeledGraph n` | §1 | defined | Labelled simple graphs on `Fin n`. |
| `CoColoring`, `CoColorable` | Abstract and §1 | defined | At most `k` clique-or-independent vertex classes; empty palette classes are allowed. |
| `cochromaticNumber` | Abstract and §1 | defined | Minimum `k` admitting a cocolouring on a finite vertex type. |
| `chromaticNumberNat` | Abstract and §1 | defined | Natural-valued wrapper around mathlib's chromatic number, restricted to finite vertex types. |
| `cochromaticNumber_le_chromaticNumber` | elementary observation before (0.1) | proved | Every proper colouring is a cocolouring. |
| `CoColoring.relabel` | proof infrastructure | proved by construction | Palette renaming preserves validity. |
| `CoColoring.addEmptyColors`, `coColorable_mono` | proof infrastructure | proved by construction / proved | Unused palette entries preserve cocolourability. |
| `CoColoring.sumInduce` | §§9–11 interface | proved by construction | Cocolourings on an induced set and its complement glue with disjoint palettes. |
| `coColorable_of_induce_and_compl` | §§9–11 interface | proved | `k + ℓ` cocolours suffice after induced-set concatenation. |
| `coColorable_of_induce_and_colorable_compl` | leftover step in §§10–11 | proved | The leftover may use an ordinary colouring. |
| `coColorable_iff_cochromaticNumber_le` | definition audit | proved | Confirms that `cochromaticNumber` has the intended minimum semantics. |
| `randomGraphMeasure` | (0.1) | defined | Mathlib's binomial random graph law at edge probability `1/2`. |
| `randomGraphMeasure_singleton`, `randomGraphMeasure_singleton_uniform` | model validation | proved | Records the exact singleton formula and proves uniform mass `(1/2)^(n choose 2)`. |
| `measurableSet_gapEvent` | (0.1) | proved | The finite-space event is measurable, not merely assigned an outer measure. |
| `gapProbability_le_one` | probability sanity check | proved | The event mass is at most one. |
| `Erdos625Statement` | (0.1) | defined, **unproved** | Exact full-sequence convergence of the displayed event probability to one. |
| `erdos625Statement_iff_real` | (0.1) | proved | The `ENNReal` target is equivalent to the manuscript's real-valued probability limit. |

## Remaining proof dependency graph

The following items are open.  Names here are work-package labels, not hidden
Lean axioms or claimed theorems.

1. Exact finite probability identities and elementary inequalities used in §1.
2. Independence-number phase expansion, including endpoint-uniform errors
   (Lemma 2.1).
3. Existence, uniqueness, derivative bounds, and support comparison for the
   continuous profile roots (Lemma 3.1).  Roots will not be introduced by
   choice until existence and uniqueness are proved.
4. The unrestricted chromatic lower-location argument (§4).
5. The four-size signed first-moment calculation and uniform entropy
   certificate (Lemma 5.1).
6. Exact sign-summed second-moment and prescribed-cell bounds (Lemmas 6.1–6.2).
7. All partial-diagonal ranges, with empty, central, and full corners kept
   explicit (Lemma 7.1).
8. Canonical high cells, endpoint transportation, and all nonendpoint high
   multiplicities (Lemmas 8.1–8.3).
9. Residual local/cycle attachment bound and normalized signed second moment
   (Lemma 9.1 and Proposition 9.2).  The residual estimate must remain
   one-sided; no equality is to be inferred from an upper bound.
10. Simultaneous leftover colouring and seed amplification (Lemmas 10.1–10.2).
11. Assembly of the preceding results into `Erdos625Statement` (§11).

The central high-risk corridor is items 6–9.  A reduction that merely restates
their global overlap bound will not count as progress; each profile family,
quantifier, endpoint, and uniform error term must be explicit.

## Trust and validation policy

- Toolchain: Lean `v4.31.0`; mathlib tag `v4.31.0`, pinned transitively by
  `lake-manifest.json`.
- Aristotle and other external proof-generation services are not used.
- CI rejects placeholders/project axioms with a source gate and runs
  `lake build --wfail`, making Lean's own placeholder warning fatal.  The
  optional external `nanoda` helper path is disabled.
- Before each published milestone: run `lake build`, scan all project `.lean`
  files for `sorry`, `admit`, and project axioms, inspect `#print axioms` for
  public theorems, and obtain an independent statement/dependency audit.
- Python experiments and manuscript audits remain evidence and diagnostics;
  they are not imported as proof certificates.

## Next checkpoint

After M0 is audited and published, the next brick is the exact finite
combinatorics/probability layer supporting §1 and the phase definitions in §2.
The user checkpoint is required before beginning the phase-asymptotic campaign.
