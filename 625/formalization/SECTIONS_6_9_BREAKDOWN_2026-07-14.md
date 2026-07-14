# Sections 6--9 atomic formalization breakdown — 2026-07-14

## Scope and acceptance rule

This document decomposes the signed-overlap core of the candidate manuscript
into finite statements small enough to prove and audit independently.  A row
marked **local proved** is imported by `Erdos625.lean` and has passed the local
Lean 4.31 warning-as-error gate.  An Aristotle row is only isolated proof
search on Lean 4.28: it remains **unproved in this repository** until its exact
statement is reviewed, ported or re-proved locally, built with `--wfail`,
source-scanned, axiom-audited, and connected to the next dependency without a
new hidden assumption.

No item below states or assumes `Erdos625Statement`, Lemma 9.1, Proposition
9.2, or another global conclusion under a renamed hypothesis.

## Dependency graph

```text
ordered overlap margins
  -> exact overlap-labeling count/law (6.2)
  -> prescribed-demand witness count + infeasible branch
  -> joint prescribed-cell bound (6.8) -> product bound (6.9)

partial-diagonal and full-corner recurrences
  + exact numerical Phi branch
  + phase/entropy/Stirling estimates
  -> central decay (7.25) -> Lemma 7.1

high cells form a matching
  -> exposed-extension equivalence/count
  -> exact residual conditioning and canonical skeleton (8.2)--(8.3)
  + endpoint transportation and middle-threshold expansion
  -> Lemmas 8.1--8.3

threshold expansion
  + prescribed-cell bound
  + even-cycle decomposition with recoverable canonical choice
  + closed alternating-walk and marked-traversal bounds
  -> residual attachment estimate (9.12)--(9.18)
  -> Lemma 9.1 -> Proposition 9.2
```

## Trusted local atoms

| Declaration | Anchor | Status | What remains |
|---|---|---:|---|
| `sum_table_rows_eq_sum_table_columns` | overlap margins | local proved | Instantiate it for the actual overlap table. |
| `sum_demand_le_sum_table` | before (6.8) | local proved | Combine with the exact witness enumeration. |
| `no_contingencyTable_of_infeasible_demands` | Lemma 6.2 impossible branch | local proved | The feasible prescribed-cell count and probability ratio are still open. |
| `highCells_form_matching` | assertion before (8.2) | local proved | Define the canonical skeleton and prove the residual conditional law. |
| `card_iUnion_stubAllocation` | allocation count before (6.8) | local proved | Use it in the full disjoint-allocation enumeration. |
| `card_disjoint_extension` | one-cell extension step before (6.8) | local proved | Iterate or replace it by an audited global allocation equivalence. |
| `card_stubAllocation_mul_factorials` | falling-factorial allocation factor in (6.8) | local proved | Combine row and column selections with the cell bijections. |
| `card_prescribedDemandWitness_mul_factorials` | exact numerator count in (6.8) | local proved | Connect witnesses to uniform full matchings and apply the finite union bound. |
| `card_extensions_of_exposed_equiv` | fixed-witness matching count before (6.8), and after (8.3) | local proved | Assemble each demand witness into one exposed global equivalence and transport the uniform law. |
| `card_extensions_of_embedding_pairing` | indexed fixed-pair count before (6.8) | local proved | Build the row/column embeddings carried by each demand witness. |
| `card_rowStub`, `card_columnStub`, `witnessAtomEquiv`, `witnessRowEmbedding`, `witnessColumnEmbedding`, `card_witnessRowAtom`, `card_witnessColumnAtom` | global stub and witness encoding before (6.8) | local proved | Define the cell event, prove witness coverage, and connect these embeddings to the extension count. |
| `configurationCellCount`, `prescribedCellEvent`, `ExtendsPrescribedDemandWitness`, `extendsWitness_mem_prescribedCellEvent`, `exists_extendingWitness_of_mem_prescribedCellEvent`, `card_extensionsOfPrescribedDemandWitness` | event and one-witness count before (6.8) | defined; local proved | Both directions of event/witness coverage and the exact one-witness extension count are proved. Count the finite union and transport the uniform law. |

These four declarations are in `OverlapContingencyTools.lean`, 109 lines,
SHA-256
`26D344C5420CD52D61BFEA7CD5ED197A7FF3958A0048D07DA6710A0F18EF44AE`.
Its isolated `lake build Erdos625.OverlapContingencyTools --wfail` completed
successfully (2,966 jobs).  The module is imported by the project root and
listed in `AxiomAudit.lean`; direct `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound` for all four declarations.  The subsequent
integrated `lake build Erdos625 --wfail` also passed all 8,640 jobs.

The stub-allocation declarations are in `StubAllocationTools.lean`.  Its
isolated `lake build Erdos625.StubAllocationTools --wfail` completed
successfully (2,968 jobs).  In addition to the union and one-cell extension
counts, the module now proves the full allocation identity by an explicit
equivalence with embeddings of `Σ c, Fin (demand c)` into `Fin m`.
`PrescribedDemandTools.lean` then combines the row allocations, column
allocations, and per-cell bijections; its isolated warning-as-error build passed
all 2,969 jobs.  These are exact finite numerator counts, not yet a probability
bound.

`MatchingExtensionTools.lean` gives an explicit equivalence between full
matchings extending an exposed finite pairing and arbitrary bijections of the
two complements.  Its isolated warning-as-error build passed all 2,966 jobs and
proves the exact residual factorial count, both for finset exposures and for a
family of distinct pairs indexed by an arbitrary finite type.  The remaining
work is the configuration-model bridge, not this generic extension enumeration.

`ConfigurationModelPrescribedCells.lean` now defines the global row and column
stub types, exact total-cardinality formulas, and an injective encoding of every
prescribed-demand witness as distinct paired row/column atoms.  Its isolated
warning-as-error build passed all 2,971 jobs.  It also defines the exact cell
event, proves both directions of the event/witness bridge by an explicit finite
selection construction, and proves the exact factorial count of extensions of
any one witness.  The finite union count and uniform probability remain
deliberately separate.

## Aristotle wave 3: analytic and traversal leaves

| Atomic theorem | Project | Service status | Repository status |
|---|---|---:|---:|
| `(m/e)^x ≤ m.descFactorial x` | `20508797-129c-4791-9dda-755e3fc8b1f4` | complete | quarantined; local port pending |
| mutually exclusive threshold-choice product expansion | `f3a6d8c3-0d73-43b7-8876-895a3c566db4` | complete | quarantined; local port pending |
| edge-disjoint simple-cycle decomposition of an even finite graph | `4be14041-929c-4b0d-8e3e-1930684ee103` | complete | quarantined; strip three `grind +suggestions` options and re-audit locally |
| exponential overcount for an injectively recoverable collection | `5bd6f82e-4584-42f4-a7f6-1a0f11eb4586` | complete | quarantined; injective instantiation still open |
| weighted bipartite alternating-path sum | `cca93425-d003-4472-bace-d9af3f90ed6e` | complete with an executable `exact?` residue | rejected verbatim; repair/re-proof required |
| marked partial-traversal sum with one initial cardinal factor | `d8984160-3989-4819-a1da-b060a84deee7` | complete | quarantined; encoding bridge still open |
| exact two-branch numerical `Phi` inequality | `5eb09fd9-9d04-4c28-9207-8cfa454ccff6` | complete | quarantined; local port pending |
| infeasible prescribed-demand table is empty | `5a02c85b-b717-445b-9104-73f93e248d9f` | complete | superseded by the independent local theorem above |

## Aristotle wave 4: overlap, recurrence, and conditioning leaves

All projects in this table were submitted on 14 July 2026 and remain
quarantined even if their service status later changes.

| Atomic theorem | Project | Manuscript use |
|---|---|---|
| exact row, column, and total overlap-count margins | `be92ab04-869c-42e1-8187-84298e2b3ecb` | (6.1) and feasibility for (6.2) |
| exact ordered overlap-labeling factorial identity | `7084730d-0e79-4b1d-90b1-6569e7a7be15` | exact law (6.2) |
| permutations extending a prescribed injective pairing have cardinal `(m-x)!` | `90e0b760-2285-495b-a191-a7ba2dde099c` | one factor in (6.8) |
| disjoint cell-stub allocations give a descending factorial | `438fb013-0ce0-4453-b4cc-0f3c7402c7ca` | one factor in (6.8) |
| exact partial-diagonal successive-coordinate ratio | `c078073b-1147-4c8e-af10-54ef753300ee` | recurrence (7.4) |
| exact full-corner successive-coordinate ratio | `a08db302-f1c3-40b0-a621-8a571daad30d` | recurrence (7.6) |
| high entries under row/column cap form a matching | `43262197-53d2-4b0c-8a33-f9995b14c501` | before (8.2); independently proved locally above |
| extensions of an exposed matching are equivalent to complement matchings | `ceec69e3-9595-4f33-b573-e0bc6fa2171f` | structural part after (8.3) |

The last equivalence is not yet a statement about uniform conditional
probability.  That probability pushforward remains a separate obligation.
At this checkpoint all eight service projects are complete and audited in
quarantine.  The ordered-law result required the explicit ambient parameter
`FixedFiberLabelings (V := V) t` and public finite instances that its original
input omitted; the full-corner result changed surrounding definitions to
`noncomputable`.  The original stub-allocation result carries avoidable
feasibility and instance complexity.  Cleaner split or assumption-minimal
variants are recorded below.  The one-cell extension split has now been
re-proved locally, and the full allocation factor and prescribed-demand witness
count have been reconstructed and checked locally.  The remaining rows are not
accepted merely because the service completed them.

## Aristotle wave 5: explicit missing bridges

| Atomic theorem | Project | Service status | Manuscript use |
|---|---|---:|---|
| exact full prescribed-demand witness cardinality, corrected explicit-finiteness input | `933f98ea-3a1c-4823-b9bc-9744f552acb0` | complete; independently reconstructed and local proved | `card_prescribedDemandWitness_mul_factorials` assembles the numerator in (6.8) |
| exact cardinal of extensions of an exposed finite matching | `3131b669-2e71-4a25-be04-18494413427a` | independently reconstructed and local proved | `card_extensions_of_exposed_equiv`; conditioning count after (8.3) |
| injective selected decomposition recovered by union | `44d62168-b483-4e47-be82-4069945cca3e` | complete, quarantined | instantiate injectivity in (9.15) |
| finite closed alternating-walk geometric sum | `e4a2bdac-6e02-44f3-b604-a1c4f3c3a6f3` | complete, quarantined | (9.16) |
| finite marked-traversal geometric sum | `a25ef5a5-2a2e-49b2-8576-f9369c480d95` | complete, quarantined | (9.17)--(9.18) |

The first prescribed-witness run (`2926d7c8-c040-4485-b2be-bf04b168a8a8`)
is rejected: service error recovery inserted an inadmissible missing `Fintype`
instance.  It is retained only as a diagnostic and will never be ported.

## Aristotle wave 6: cycle-decomposition induction atoms

The original full even-cycle decomposition remained in progress, so its two
substantive recursive steps were split without assuming the decomposition:

| Atomic theorem | Project | Role |
|---|---|---|
| a nonempty finite graph with all degrees even contains a simple cycle | `889d51c6-e15b-4373-8092-6e286e34c066` | choose the next cycle |
| deleting the edges of a simple cycle preserves even degree at every vertex | `64f4a284-70ef-4606-91ed-2a5b3ce1a968` | maintain the induction invariant |
| deleting a simple cycle strictly decreases the finite edge count | `4835db0f-d693-42c3-8cea-0745ccc616cf` | well-founded recursion measure |
| generic finite peeling into pairwise-disjoint pieces whose union recovers the set | `3bff812b-2d33-4d00-ac88-ab72689842da` | non-graph-specific recursive assembly |

The graph-specific instantiation and cycle-edge bookkeeping remain local proof
obligations even if all four isolated atoms return successfully.

At this checkpoint the cycle-existence, parity-after-deletion, strict-decrease,
and generic-peeling projects are complete and audited in quarantine.  The
first two contain `grind +suggestions` options that must be removed before any
local port; cycle existence also contains generated-proof generalization that
requires manual review.

## Aristotle wave 7: corrected counting splits

| Atomic theorem | Project | Service status | Role |
|---|---|---:|---|
| fixed-fiber multinomial count with explicit finite instances | `fe77b778-d5c2-4de2-86b5-d0c8907ebfdc` | queued | first factor of exact overlap law (6.2) |
| rowwise overlap multinomial count with explicit finite instances | `a6ef4342-1e6f-4be7-af19-146e7545591d` | queued | second factor of exact overlap law (6.2) |
| clean monolithic ordered-law variant | `0e193ffc-c430-4dca-bff6-ebbf3939857b` | queued | alternative assembly of (6.2) |
| assumption-minimal stub-allocation identity | `5e3d753d-bf3f-4d57-b220-31c6c5538e82` | independently reconstructed and local proved | `card_stubAllocation_mul_factorials` in `StubAllocationTools.lean` |
| assumption-minimal one-cell disjoint extension count | `e2f1d51c-208f-4176-9198-ebcabd7eacff` | independently re-proved and local proved | `card_disjoint_extension` in `StubAllocationTools.lean` |

The local stub-allocation module explicitly constructs the missing `Finite`
and `Fintype` instances for its subtype and proves the global equivalence under
Lean 4.31.  The returned service proof remains provenance only; the repository
accepts the separately reviewed local reconstruction.

## Non-atomic obligations that must not be hidden

1. Turn the overlap-labeling identity into the exact probability law (6.2)
   for the manuscript's ordered profiles and signs.
2. Use the now-proved reverse event-to-witness construction to bound the event
   by the sum of the exact one-witness extension counts, transport the uniform
   law, and apply the finite union bound to finish (6.8).  Both coverage
   directions, the one-witness count, global stub types, witness atoms and
   embeddings, witness numerator, and infeasible branch are now proved.
3. Prove the uniform central diagonal estimate (7.14)--(7.25), including the
   phase reduction and deterministic uniform error sequence.
4. Define the canonical high skeleton and prove the exact residual matching
   pushforward; a mere equivalence of complement matchings is insufficient.
5. Prove the endpoint transportation and all near/middle skeleton sums
   (8.16)--(8.29b), including the no-further-near conditioning event.
6. Choose the even-cycle decomposition canonically enough to recover the
   original even edge set, and encode its cycles as the weighted walks used by
   the analytic bounds.
7. Assemble (9.10)--(9.18) with the actual degree sums and asymptotic error
   estimates, then prove Lemma 9.1 and Proposition 9.2.

Only those assemblies, followed by the amplification layer and exact final
target, can close the proof.  Successful isolated arithmetic or enumeration
leaves do not by themselves certify a manuscript lemma.
