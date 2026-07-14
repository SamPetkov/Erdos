# Sections X--XI formalization breakdown -- 2026-07-14

## Scope and status rule

This document records the accepted deterministic Lean atoms and the exact
remaining proof obligations for manuscript Sections 10 and 11.  A declaration
marked **local proved** is accepted Lean 4.31 source.  An Aristotle request is
only quarantined proof search on an isolated Lean 4.28 project; while it is
running or pending it proves nothing in this repository, and no returned
source is imported automatically.

Neither Lemma 10.1, Lemma 10.2, Section 11, nor `Erdos625Statement` is complete.

## Accepted local atoms

| Declaration | Manuscript role | Status | Exact limitation |
|---|---|---:|---|
| `exists_vertex_quarter_degree` | deterministic averaging step in Lemma 10.1 | local proved | The denominator-cleared quarter-density premise yields one vertex with `card - 1 <= 4 * degree`.  It does not prove the random simultaneous-density event or construct the full greedy colouring. |
| `quarterRecurrence_lowerBound` | recurrence (10.3a) | local proved | From `(s t - 1) / 4 <= s (t+1)` it proves `4^(-t) * s 0 - 1/3 <= s t`.  The required number of iterations and independent-set extraction are not included. |
| `chromaticLowerEvent`, `cochromaticUpperEvent` | threshold events in Section 11 | defined | These are the strict natural chromatic lower event and real cochromatic upper event with deterministic error. |
| `thresholdIntersection_subset_gapEvent` | deterministic Section 11 event inclusion | local proved | Given the exact threshold separation, the intersection is contained in `gapEvent`; the strict chromatic event contributes the necessary `+1`. |
| `explicitThresholdIntersection_subset_gapEvent` | expanded form of (11.2) | local proved | The same inclusion displays the constant explicitly.  It supplies no sequence choice, probability limit, or eventual separation theorem. |

The previously accepted amplification infrastructure also includes the induced
`k`-cocolourable capacity, its full-capacity event, one-vertex block
oscillation, graph-law tails, rare-seed expectation inversion (10.7), the
one-sided lower-tail estimate (10.8), a maximizing core with exact complement
size, and deterministic concatenation (10.9).  Those interfaces do not by
themselves prove Lemma 10.2.

## Section X dependency DAG

```text
fixed-set lower-quarter binomial tail
  -> union bound over all u0-subsets
  -> one quarter-density event for every set of size at least u0
  -> quarter-degree vertex + quarter recurrence
  -> an independent set of size c log n in every set of size at least n^(1/3)
  -> greedy colouring on every U, on the same event
  -> Lemma 10.1 (simultaneous leftover colouring)

rare cochromatic seed
  + induced-capacity concentration (10.7)--(10.8)
  + maximizing core and concatenation (10.9)
  + Lemma 10.1's one simultaneous event
  -> Lemma 10.2 with one universal C and epsilon_n
  -> seed/radius scale estimates (10.10)--(10.12)
  -> cochromatic upper tail (10.13)
```

The remaining Section X obligations, in dependency order, are:

1. Define the complement-graph quarter-density event at
   `u0 = ceil(n^(1/4))`.  Transport the exact induced-edge law to the
   lower-quarter binomial tail, count all `u0`-subsets, and prove that its
   failure probability tends to zero along the full sequence.
2. Prove by averaging that the same event gives quarter density in every
   larger vertex set.  This must be one event with an internal `∀ U`, not
   a separately chosen event or exceptional set for each `U`.
3. Combine that event with `exists_vertex_quarter_degree` and
   `quarterRecurrence_lowerBound`.  Prove that a chain starting above
   `n^(1/3)` survives for the required order-`log n` number of steps and yields
   an independent set of size at least `c * log n`, for one absolute `c > 0`.
4. Formalize the greedy deletion/colouring recursion for an arbitrary `U` and
   prove the displayed bound (10.3) simultaneously for every `U` on the one
   event.  Extract one absolute constant `C` and one deterministic failure
   sequence tending to zero.
5. Assemble Lemma 10.2 from the already proved capacity expectation and lower-
   tail bounds, the maximizing core, deterministic concatenation, and the
   simultaneous event.  The quantifiers must choose `C` and a deterministic
   `epsilon_n -> 0` before quantifying over deterministic `k_n`, `Lambda_n`,
   and `r_n`; the error sequence may not depend on any of those three choices.
   The conclusion must be uniform for every deterministic `r_n > 0`.
6. Prove the scale implications used in (10.10)--(10.12): the seed term from
   `Lambda_n = o(n/(log n)^4)`, the divergence of
   `r_n = sqrt(n/(log n)^4)`, the amplified-radius term, `n^(1/3)`, and the
   additive constant are all negligible relative to `n/(log n)^3`.
7. Define the actual deterministic error `a_n` and instantiate Lemma 10.2 to
   obtain (10.13), including `exp(-r_n) + epsilon_n -> 0` on the full sequence.

No pointwise-in-`U` probability statement can replace steps 2--4: the
capacity-attaining complement is chosen from the random graph and therefore
must be controlled by the same simultaneous event.

## Section XI dependency DAG

```text
Section 4 chromatic lower tail
  + Section 10 cochromatic upper tail
  + eventual root separation minus a_n
  -> probabilities of both threshold events tend to one
  -> probability of their intersection tends to one (no independence)
  + deterministic threshold-intersection inclusion
  -> probability of gapEvent tends to one
  -> Erdos625Statement

explicit gap-scale divergence
  + gapEvent tail
  -> every fixed-M gap tail (11.3)
```

The accepted `Section11EventAssembly.lean` module supplies only the pointwise
set inclusion in the middle of this DAG.  The remaining actual sequence/tail
instantiation is:

1. Define the manuscript sequences `kChi n`, `kCo n`, and `a n`, and connect
   their Lean definitions to the Section 4, Section 5, Section 9, and Section
   10 outputs without replacing an eventual statement by a subsequence.
2. Prove the eventual explicit threshold separation, including the strict-
   event `+1` and the little-o loss `a_n`.
3. Prove measurability and full-sequence convergence to one for the actual
   chromatic-lower and cochromatic-upper event probabilities.
4. Prove that the intersection probability tends to one by a union bound; no
   independence assumption is permitted.
5. Instantiate `explicitThresholdIntersection_subset_gapEvent`, use measure
   monotonicity, and prove the exact full-sequence target
   `Erdos625Statement`.
6. Prove divergence of the explicit positive gap scale and derive the actual
   fixed-`M` probability tail (11.3).

Every limit above is an `atTop` statement along all natural `n`.  Phase
uniformity near independence-number jumps must therefore be inherited from the
upstream full-sequence theorems, not added as a density-one or subsequence
qualification.

## Aristotle request ledger

All seven requests below are currently running or pending and quarantined.
The two accepted local Section X atoms were proved independently; their local
files remain authoritative regardless of the service result.  The other five
rows remain open repository obligations.

| Section | Isolated task | Request ID | Service/repository status |
|---|---|---|---|
| X | quarter recurrence | `6b7ec5a6-6bfc-4926-b699-bc20977f66fd` | running/pending; quarantined; local `QuarterRecurrence.lean` independently proved |
| X | quarter-density high-degree vertex | `b275f7c1-dfba-4c1c-9ead-0112c4e54020` | running/pending; quarantined; local `QuarterDensityDegree.lean` independently proved |
| X | growing amplification radius | `ff666a22-b192-489c-8c66-ef0da63a0daa` | running/pending; quarantined; no accepted local theorem yet |
| X | seed square-root scale | `288de3bd-372f-4802-8070-60c0eef7f3c2` | running/pending; quarantined; no accepted local theorem yet |
| XI | probability intersection | `cb039d44-1e81-4b0b-a0e2-481eeb8fc8a0` | running/pending; quarantined; no accepted local theorem yet |
| XI | eventual parameter threshold | `e451963a-2f93-407c-aa0e-28467d87642e` | running/pending; quarantined; no accepted local theorem yet |
| XI | explicit gap-scale divergence | `764866b6-c929-48fb-b476-ec61925d250c` | running/pending; quarantined; no accepted local theorem yet |

The service tasks are redundant candidate generation only.  A returned proof
must still be reviewed, reconstructed or ported to Lean 4.31, source-scanned,
built with warnings fatal, axiom-audited, and integrated without changing its
quantifiers before it can become accepted repository source.
