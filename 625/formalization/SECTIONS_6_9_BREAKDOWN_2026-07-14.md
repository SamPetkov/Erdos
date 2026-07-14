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
| `sum_orderedOverlapCount_row`, `sum_orderedOverlapCount_column`, `card_fixedFiberLabeling_mul_factorials`, `card_orderedOverlapLabeling_mul_factorials`, `orderedOverlapLabeling_probability_eq`, `fixedMarginOverlapEvent_probability_eq` | exact ordered law (6.1)–(6.2) | local proved | Connect the fixed-row ordered law to the project's unordered profile representation and then add the sign/component factors (6.3)–(6.7). |
| `sum_table_rows_eq_sum_table_columns` | overlap margins | local proved | Instantiate it for the actual overlap table. |
| `sum_demand_le_sum_table` | before (6.8) | local proved | Combine with the exact witness enumeration. |
| `no_contingencyTable_of_infeasible_demands` | Lemma 6.2 impossible branch | local proved; integrated | The feasible prescribed-cell count and probability ratio are handled by the configuration-model modules. |
| `highCells_form_matching` | assertion before (8.2) | local proved | Define the canonical skeleton and prove the residual conditional law. |
| `card_iUnion_stubAllocation` | allocation count before (6.8) | local proved | Use it in the full disjoint-allocation enumeration. |
| `card_disjoint_extension` | one-cell extension step before (6.8) | local proved | Iterate or replace it by an audited global allocation equivalence. |
| `card_stubAllocation_mul_factorials` | falling-factorial allocation factor in (6.8) | local proved | Combine row and column selections with the cell bijections. |
| `card_prescribedDemandWitness_mul_factorials` | exact numerator count in (6.8) | local proved; integrated | Consumed by `jointPrescribedCellBound`. |
| `card_extensions_of_exposed_equiv` | fixed-witness matching count before (6.8), and after (8.3) | local proved | Assemble each demand witness into one exposed global equivalence and transport the uniform law. |
| `card_extensions_of_embedding_pairing` | indexed fixed-pair count before (6.8) | local proved | Build the row/column embeddings carried by each demand witness. |
| `card_rowStub`, `card_columnStub`, `witnessAtomEquiv`, `witnessRowEmbedding`, `witnessColumnEmbedding`, `card_witnessRowAtom`, `card_witnessColumnAtom` | global stub and witness encoding before (6.8) | local proved | Define the cell event, prove witness coverage, and connect these embeddings to the extension count. |
| `configurationCellCount`, `prescribedCellEvent`, `ExtendsPrescribedDemandWitness`, `extendsWitness_mem_prescribedCellEvent`, `exists_extendingWitness_of_mem_prescribedCellEvent`, `card_configurationMatching`, `card_extensionsOfPrescribedDemandWitness`, `card_prescribedCellEvent_le_witness_mul_factorial` | event and finite union count before (6.8) | defined; local proved; integrated | Both coverage directions, the ambient `m!` count, each exact `(m-x)!` extension count, and the aggregate event-cardinality bound are consumed by the complete probability theorem. |
| `uniformConfigurationMatching_prescribedCellEvent_apply`, `uniformConfigurationMatching_prescribedCellEvent_le_witness`, `jointPrescribedCellBound` | uniform-law transport and equation (6.8) | local proved | Exact ENNReal probability ratio, witness union bound, and factorial normalization to one global `(m)_x`. |
| `pow_sub_add_one_le_descFactorial`, `factorial_pow_le_descFactorial_pow`, `real_div_exp_one_pow_le_descFactorial`, `ennreal_div_euler_pow_le_descFactorial` | effective bound (6.10) | local proved | The global lower bound `(m/e)^x ≤ (m)_x` is proved with `0<m` and `x≤m`; no asymptotic replacement is used. |
| `cellDegreePowerProduct`, `row_column_descendingProduct_le_cellDegreePowerProduct`, `configurationCellTheta`, `configurationCellTheta_pow_product`, `configurationCellWeight_product_eq_global`, `jointPrescribedCellBound_cellwise_of_totalDemand_le`, `not_mem_prescribedCellEvent_of_total_lt`, `jointPrescribedCellBound_cellwise` | product majorant (6.9) | local proved, all cases | Exact cellwise `ℝ≥0∞` product bound with `θ_ab=e d_a d'_b/m`. The feasible-total theorem proves the analytic inequality; the public theorem removes that premise by proving the prescribed event empty when total demand exceeds `m`. All finite-product inversions and denominator conditions are explicit. |
| `sum_configurationCellCount_row`, `sum_configurationCellCount_column`, `configurationCellCount_highCells_form_matching` | first concrete bridge before (8.2) | local proved | The actual configuration cell table has its exact row and column degree margins; under a common cap, its high cells form a partial matching. Canonical selection and the residual law remain open. |
| `witnessSelectedRowStubs`, `witnessSelectedColumnStubs`, `RemainingRowStub`, `RemainingColumnStub`, `extensionsOfPrescribedDemandWitnessEquivRemaining`, `card_remainingRowStub`, `card_remainingColumnStub`, `card_remainingStubs_eq` | structural complement equivalence after (8.3) | local proved | Extending a fixed exposed witness is exactly equivalent to a bijection of unused stubs, with exact remaining cardinalities. No degree-fibre identification or residual probability-law claim is included. |
| `descFactorial_endpoint_transport`, `descFactorial_endpoint_transport_succ`, `descFactorial_min_transport`, `descFactorial_min_transport_succ` | endpoint transport (8.12) | local proved | Exact total natural-number theorem with stronger loss `n^gap`; the manuscript's `(n+1)^gap` and exact `min`/`Nat.dist` forms follow. |
| `selectedBlockCount`, `selectedVertexMass`, `selectedInternalEdgeCount`, `partialSignedFirstMoment`, `partialDiagonalWeight`, `partialDiagonalWeight_zero`, `partialSignedFirstMoment_increment_mul`, `partialDiagonalWeight_increment_mul`, `partialDiagonalWeight_increment_div` | formulas (7.1)–(7.3) and recurrence (7.4) | local proved | Exact full-profile algebra on the feasible selected-mass domain, with a clearly documented total natural-subtraction extension outside it. The denominator-free recurrence assumes the vertex-mass condition; the displayed ratio additionally uses componentwise subprofile containment to prove the old marked weight positive. |
| `complementaryProfile`, `residualVertexMass`, `completeSignedFirstMoment`, `fullCornerWeight`, `selectedVertexMass_complement_le_of_fullMass`, `partialDiagonalWeight_complement_mul_complete`, `partialDiagonalWeight_complement_eq_fullCorner_div`, `fullCornerWeight_increment_mul`, `fullCornerWeight_increment_div` | endpoint factorization (7.5) and recurrence (7.6) | local proved | The full-profile mass identity and componentwise containment derive every feasibility fact explicitly. Denominator-free and quotient forms are both kernel-checked; the ratio remains valid at `h_i=k_i`, where the next weight and numerator are zero. |

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
selection construction, proves the exact factorial count of extensions of any
one witness, and embeds the whole event into the disjoint union of those
extension types.  `ConfigurationModelProbability.lean` then transports this
count through the uniform PMF and proves the exact joint prescribed-cell bound
(6.8), the effective falling-factorial bound (6.10), and the all-cases cellwise
product majorant (6.9).  Its isolated warning-as-error build passed all 3,383
jobs; a focused axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.

`PartialDiagonalWeights.lean` formalizes the exact finite statistics and
partial-diagonal recurrence through (7.4).  Its isolated warning-as-error
build passed all 1,920 jobs.  A focused audit of every public theorem reports
only `propext`, `Classical.choice`, and `Quot.sound`.  Aristotle's recurrence
output was used only as advisory provenance; the repository theorem is an
independent full-profile reconstruction checked by the local kernel.

`ConfigurationModelCellMarginals.lean` proves the exact row and column
marginals of the configuration cell table and the resulting high-cell matching
statement.  Its isolated warning-as-error build passed all 2,973 jobs; its
focused audit again reports only `propext`, `Classical.choice`, and
`Quot.sound`.

`ConfigurationModelResidualMatching.lean` exposes the deterministic
complement equivalence after a prescribed witness and proves exact selected and
remaining cardinalities.  Its isolated warning-as-error build passed all 2,972
jobs and its focused audit used only the three standard axioms.  It deliberately
does not claim the residual degree-fibre law or a conditional pushforward.

`EndpointTransportBounds.lean` proves the endpoint descending-factorial
transport with loss `n^gap`, the weaker manuscript-facing `(n+1)^gap` form,
and exact minimum/absolute-difference instantiations.  Its isolated
warning-as-error build passed all 2,967 jobs and its focused audit used only
the standard axioms.

`OrderedOverlapLaw.lean` proves the fixed-row ordered overlap margins, exact
multinomial sample-space and fixed-table counts, the cross-multiplied identity,
and the literal rational event/sample-space law (6.1)–(6.2).  Its isolated
warning-as-error build passed all 2,966 jobs and its focused audit used only
the standard axioms.  It does not yet supply the unordered-profile ordering
bridge or the sign/component factors.

`FullCornerWeights.lean` proves the complementary-profile feasibility lemmas,
the endpoint factorization (7.5), and the full-corner recurrence (7.6), each in
denominator-free and quotient form.  Its isolated warning-as-error build passed
all 1,921 jobs, and its focused audit reports only the three standard axioms.

## Aristotle wave 3: analytic and traversal leaves

| Atomic theorem | Project | Service status | Repository status |
|---|---|---:|---:|
| `(m/e)^x ≤ m.descFactorial x` | `20508797-129c-4791-9dda-755e3fc8b1f4` | complete | independently reconstructed and locally proved in `FallingFactorialBounds.lean`; service result retained as provenance only |
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

1. Connect the proved fixed-row ordered overlap law (6.1)–(6.2) to the
   project's unordered profile representation, then prove the exact
   sign/component factors (6.3)–(6.7) and assemble Lemma 6.1.
2. Prove the uniform partial-diagonal estimates (7.7)–(7.25), including the
   phase reduction and deterministic uniform error sequence.  The exact finite
   setup, endpoint factorization, and recurrences (7.1)–(7.6) are locally proved.
3. Define the canonical high skeleton and prove the exact residual matching
   pushforward; a mere equivalence of complement matchings is insufficient.
4. Prove the endpoint transportation and all near/middle skeleton sums
   (8.16)--(8.29b), including the no-further-near conditioning event.
5. Choose the even-cycle decomposition canonically enough to recover the
   original even edge set, and encode its cycles as the weighted walks used by
   the analytic bounds.
6. Assemble (9.10)--(9.18) with the actual degree sums and asymptotic error
   estimates, then prove Lemma 9.1 and Proposition 9.2.

## RVE refinement: ordered Sections 8–9 work packages

A second local replay split the remaining Sections 8–9 argument into the
following dependency-ordered packages.  These are proof obligations, not
axioms or aliases for the desired conclusion.

1. Prove the exact row and column marginals of `configurationCellCount` and
   use them to construct the canonical high-cell partial matching.
2. Expose the complement-matching equivalence after a prescribed witness;
   identify it with a residual `ConfigurationMatching`; and prove the exact
   cell-count split `full = exposed + residual`.
3. Prove uniqueness of the canonical high-demand witness.  This is needed
   because the exact incidence (8.3) includes the condition that no residual
   pair returns to a skeleton cell; the union bound behind (6.8) does not
   provide disjointness.
4. Package the preceding facts as an exact decomposition of a full matching
   into a high skeleton, its exposed witness, and a residual matching with the
   skeleton-cell and off-skeleton caps.
5. Count typed partial matchings with prescribed table `ell i j` by the
   cross-multiplied row/column descending-factorial identity.  This is the
   missing finite bridge from the skeleton type to the weight `W(L)` in (8.6).
6. Prove endpoint transportation (8.11)–(8.14), preferably by a direct
   descending-factorial inequality rather than interpolation, and combine it
   with the exact minimum/absolute-difference and local reward identities.
7. Assemble Lemma 8.2 through
   `(sum_r sqrt (D r))^2`.  A sum of one-vector `D` over margin pairs is
   ill-typed and is not an acceptable substitute.
8. Split Lemma 8.3 into the exact ratios (8.21)–(8.22), the recurrence for
   `A_e` including `e=0`, labelled near-deficit expansion, one-sided middle
   threshold expansion, uniform `Xi_4` decay, small-residual deterministic
   majorant, and final skeleton-mass assembly.  The small-residual step is an
   inequality using `g ≥ 1`, never an equality.
9. Define even bipartite edge subsets and prove the actual cycle-space count
   (6.7); this identity must not be hidden in a renamed hypothesis.
10. Port the mutually exclusive threshold-choice expansion and apply the
    all-cases theorem `jointPrescribedCellBound_cellwise` jointly to the
    combined per-cell demands before removing caps or forbidden-cell events.
11. Prove the finite degree-sum bounds behind (9.13)–(9.14), then the exact
    factorization of the sums of powers of `theta_ab`.
12. Construct the simple-cycle deletion recursion manually, prove union
    recovery, choose decompositions injectively, and only then apply the
    exponential family overcount in (9.15).
13. Build the cycle-to-closed-walk and marked-cycle-to-traversal encodings
    used in (9.16)–(9.18).  The analytic geometric bounds do not supply these
    encodings, and a marked traversal receives no fresh cardinal factor after
    its initial mark.
14. For the small residual branch, prove injectivity of restriction of an
    even subgraph of `M ∪ R` to `R` when `M` is a matching; parity then
    recovers the matching edges and gives the direct `2^|R|` bound.
15. State the final attachment estimate with one deterministic error sequence
    and one eventual threshold uniform over every feasible skeleton.  A
    skeleton-dependent error sequence or threshold has the wrong quantifiers.

The RVE replay under Lean 4.31 and warning-as-error accepted the threshold
choice expansion, recoverable-decomposition selector, injective exponential
overcount, closed-walk and marked-traversal geometric bounds, sign-exponent
bookkeeping, and component-constant sign count; each used only `propext`,
`Classical.choice`, and `Quot.sound`.  It rejected the weighted-Cauchy output
because it fails locally and retains `sorryAx`, and rejected the old cycle
decomposition because it contains forbidden `grind +suggestions`.  A capped
residual-pair theorem is mathematically reusable after removing an unused
hypothesis that currently fails warnings-fatal.  The Aristotle API key was
not present in this terminal for new submissions, so only already returned
projects were replayed and all remain quarantined until a clean local port.

Only those assemblies, followed by the amplification layer and exact final
target, can close the proof.  Successful isolated arithmetic or enumeration
leaves do not by themselves certify a manuscript lemma.
