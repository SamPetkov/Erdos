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
| `highCells_form_matching` | assertion before (8.2) | local proved | Connect this generic matching fact to the canonical cutoff-demand atoms recorded below, then construct and count the labelled skeleton witness and prove its residual conditional law. |
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
| `sum_configurationCellCount_row`, `sum_configurationCellCount_column`, `configurationCellCount_highCells_form_matching` | first concrete bridge before (8.2) | local proved | The actual configuration cell table has its exact row and column degree margins; under a common cap, its high cells form a partial matching. The canonical cutoff-demand atoms are recorded below; constructing and counting the labelled witness and proving the residual law remain open. |
| `witnessSelectedRowStubs`, `witnessSelectedColumnStubs`, `RemainingRowStub`, `RemainingColumnStub`, `extensionsOfPrescribedDemandWitnessEquivRemaining`, `card_remainingRowStub`, `card_remainingColumnStub`, `card_remainingStubs_eq` | structural complement equivalence after (8.3) | local proved | Extending a fixed exposed witness is exactly equivalent to a bijection of unused stubs, with exact remaining cardinalities. |
| `uniformOfFintype_map_equiv` | uniform finite-law transport after the residual equivalence | local proved | An equivalence maps the uniform PMF to the uniform PMF. |
| `uniform_filter_eq_uniformSubtype_map` | generic conditioning of a finite uniform law | local proved | Conditioning on a nonempty finite event is the pushforward of the subtype's uniform law. It does not identify the canonical skeleton event or transport its cap conditions. |
| `card_selectedRowStubs_in_class`, `card_selectedColumnStubs_in_class` | classwise witness-fibre counts after (8.3) | local proved | The selected stubs in each row or column class have the exact demand-sum cardinality. |
| `residualRowDegree`, `residualColumnDegree`, `card_remainingRowFiber`, `card_remainingColumnFiber`, `remainingRowStubEquivResidual`, `remainingColumnStubEquivResidual` | exact residual degree fibres after (8.3) | local proved | The unused local fibres have the exact residual degrees and class-preserving equivalences to standard residual stub dependent sums. |
| `extensionsOfWitnessEquivResidualConfiguration`, `uniform_extensionSubtype_map_residual` | fixed-witness residual matching space after (8.3) | local proved | The extension subtype is equivalent to the residual `ConfigurationMatching` space, and its uniform law pushes forward to the residual uniform law. The deterministic cutoff/support and fixed-fibre uniqueness atoms are recorded below; choosing and counting the labelled witness, proving manuscript incidence (8.3), and packaging the global canonical event remain open. |
| `card_targetFiber_eq_usedTarget_add_residual`, `remainingRowStubEquivResidual_apply_in_class`, `residualConfiguration_targetClass`, `usedRowTargetIndices_eq_witnessCell`, `configurationCellCount_eq_demand_add_residual` | exact fixed-witness residual cell-count decomposition | local proved | Row-class transport and the exact used-cell identification yield `full configurationCellCount = demand + residual configurationCellCount` for every cell of a fixed witness extension. The zero/cap consequences are recorded in the next row; the actual labelled skeleton witness and manuscript incidence (8.3) remain open. |
| `nat_add_eq_left_iff_right_eq_zero`, `nat_add_le_iff_le_sub_of_le`, `exposedCell_constraints_iff_residual`, `configurationCell_constraints_iff_residual` | exact fixed-witness zero/cap constraints | local proved | The supporting zero equivalence is cap-free. The packaged theorem assumes `hcap : demand a b <= cap` and returns `full = demand` iff residual count is zero together with `full <= cap` iff `residual <= cap - demand a b`. High-skeleton cells use the zero branch; the unshifted off-skeleton cap requires a prior proof that `demand a b = 0`. Canonical event packaging remains open. |
| `canonicalHighDemand`, `compatiblePairing_unique`, `selectedFiber_eq_fullFiber_of_zero_residual`, `canonicalHighDemand_partialMatching_and_incidence`, `supportIndexed_fullConstraints_iff_residual` | deterministic canonical-support atoms around (8.2)–(8.3) | defined; local proved | The strict `U/2` cutoff retains whole cell demands, has partial-matching support, and has exact on/off-cutoff values. Once source and target fibres are fixed their compatible pairing is unique, zero residual plus the displayed cardinal identities forces a selected fibre to be full, and the simultaneous support-indexed cap/no-return constraints translate exactly under explicit split, demand-cap, and off-support-zero hypotheses. These facts do **not** construct or count the labelled canonical witness, prove manuscript incidence (8.3), identify the global conditioned skeleton law, or prove Lemma 8.3. |
| `highCellFinset_card_mul_succ_le_total` | high-cell mass bound in Section 8 | local proved | The number of entries above `R`, multiplied by `R+1`, is at most the total table mass. This is not a canonical-skeleton construction. |
| `sum_sqrt_mul_weight_le` | weighted Cauchy step in the margin-pair sum | local proved | The finite nonnegative square-root inequality is exact. Instantiating it with the actual margin weights and assembling Lemma 8.2 remain open. |
| `descFactorial_endpoint_transport`, `descFactorial_endpoint_transport_succ`, `descFactorial_min_transport`, `descFactorial_min_transport_succ` | endpoint transport (8.12) | local proved | Exact total natural-number theorem with stronger loss `n^gap`; the manuscript's `(n+1)^gap` and exact `min`/`Nat.dist` forms follow. |
| `degreeSquareSum_le_cap_mul_total`, `degreeCubeSum_le_cap_sq_mul_total`, `sum_configurationCellTheta_sq_row`, `sum_configurationCellTheta_sq_column`, `sum_configurationCellTheta_cube`, `sum_configurationCellTheta_sq_row_le_uniform`, `sum_configurationCellTheta_sq_column_le_uniform`, `sum_configurationCellTheta_cube_le`, `sum_configurationCellTheta_cube_eq_zero_of_total_zero` | degree/theta estimates (9.13)–(9.14) | local proved | Exact finite factorizations and normalized `ℝ≥0∞` bounds, with the `m=0` branch separated explicitly. |
| `localSignRewardNat`, `prod_localSignRewardNat_eq_pow` | local sign-reward exponent | local proved | The product of the local powers of two is reduced to one exact exponent. Component signs and the global signed-moment sum remain open. |
| `BipartiteEvenMatrix`, `evenMatrix_eq_zero_of_support_rowMatching` | small-residual parity kernel | local proved | An even `ZMod 2` bipartite matrix supported on a row matching is zero. The generic restriction, incidence encoding, and actual residual-family instantiation are recorded below; cycle decomposition and attachment remain open. |
| `selectedBlockCount`, `selectedVertexMass`, `selectedInternalEdgeCount`, `partialSignedFirstMoment`, `partialDiagonalWeight`, `partialDiagonalWeight_zero`, `partialSignedFirstMoment_increment_mul`, `partialDiagonalWeight_increment_mul`, `partialDiagonalWeight_increment_div` | formulas (7.1)–(7.3) and recurrence (7.4) | local proved | Exact full-profile algebra on the feasible selected-mass domain, with a clearly documented total natural-subtraction extension outside it. The denominator-free recurrence assumes the vertex-mass condition; the displayed ratio additionally uses componentwise subprofile containment to prove the old marked weight positive. |
| `complementaryProfile`, `residualVertexMass`, `completeSignedFirstMoment`, `fullCornerWeight`, `selectedVertexMass_complement_le_of_fullMass`, `partialDiagonalWeight_complement_mul_complete`, `partialDiagonalWeight_complement_eq_fullCorner_div`, `fullCornerWeight_increment_mul`, `fullCornerWeight_increment_div` | endpoint factorization (7.5) and recurrence (7.6) | local proved | The full-profile mass identity and componentwise containment derive every feasibility fact explicitly. Denominator-free and quotient forms are both kernel-checked; the ratio remains valid at `h_i=k_i`, where the next weight and numerator are zero. |
| `two_mul_card_selectedCells_le_total`, `card_selectedCells_le_half_total` | generic selected-cell cardinality | local proved | If each selected cell has mass at least two, the number of selected cells is at most the total mass divided by two. This is only a cardinality estimate. |
| `configurationResidualSupportRelation`, `configurationResidualSupportFinset`, `sum_configurationCellCount_all`, `card_configurationResidualSupportFinset_le_half_stubMass`, `card_configurationResidualSupportFinset_le_half_rowStubCard` | actual configuration-table residual support | local proved | The number of cells containing at least two matched stub pairs is at most the total row-stub count divided by two. No cycle-space or attachment claim is asserted. |
| `bipartiteEdgeRow`, `bipartiteEdgeColumn`, `bipartiteEdgeMatrix`, `bipartiteEdgeMatrix_injective`, `sum_bipartiteEdgeMatrix_row`, `sum_bipartiteEdgeMatrix_column`, `BipartiteEvenEdgeSet`, `bipartiteEdgeMatrix_even_iff` | finite bipartite incidence encoding | local proved | A finite edge set is encoded injectively by its zero-one `ZMod 2` matrix, whose row/column parity is equivalent to even row/column fibres. The actual residual-family instantiation is recorded below; this encoding alone proves no cycle decomposition or attachment estimate. |
| `evenMatrix_eq_of_eq_on_residual`, `residualRestriction_injective`, `card_evenMatrixSupportedOn_le_pow_card_residualCell` | generic small-residual restriction count | local proved | Even matrices supported on a row matching plus a residual relation are determined by their residual-cell values and number at most `2 ^ |R|`. The actual residual even-edge family is instantiated below; the exact finite binary cycle-space identity is proved separately below, while a recoverable simple-cycle decomposition and the attachment argument remain open. |
| `ActualResidualEvenEdgeFamily`, `card_actualResidualEvenEdgeFamily_le_pow_support` | actual residual even-edge support/count bridge in Section 9 | defined; local proved | The family is literally the finite even edge sets supported on the row matching `M` together with cells whose supplied multiplicity is at least two. Under the displayed row-matching hypothesis its cardinal is at most `2 ^ Nat.card (ResidualCell (fun a b => 2 <= cellCount a b))`. This proves neither a cycle decomposition nor the traversal, attachment, or Lemma 9.1 estimates. |
| `twice_sum_choose_two_le_cap_mass` | division-free form of (9.21) | local proved | If every residual multiplicity is at most `U` and the total residual mass is `m₀`, then `2 * sum_e (r e).choose 2 <= (U - 1) * m₀`. This finite arithmetic bound does not by itself prove the cycle-rank bound (9.20), the integrand estimate (9.22), or Lemma 9.1. |
| `cycleRank_matching_union_le_card_residual` | forest-plus-residual-edge part of (9.20) | local proved | A genuine bipartite matching is acyclic, and adjoining an arbitrary residual relation gives cyclomatic number at most the number of residual cells.  This does not prove the cycle-space identity/decomposition, traversal estimates, integrand estimate (9.22), or Lemma 9.1. |
| `cycleRank_matching_union_configurationResidualSupport_le_card`, `cycleRank_matching_union_configurationResidualSupport_le_half_stubMass`, `cycleRank_matching_union_configurationResidualSupport_le_half_m₀` | literal configuration-support chain in (9.20) | local proved | The generic residual relation is identified with the actual multiplicity-at-least-two cell support, giving `cycleRank ≤ |support| ≤ m₀ / 2` once the residual row-stub mass is named `m₀`.  The canonical-skeleton instantiation, concrete cycle-to-walk and weight/kernel transfer (including eventual `tau < 1`), and attachment estimates remain open; the abstract row-norm/geometric traversal kernel is proved below. |
| `finrank_graphCycleSpace_eq_cycleRank`, `natCard_evenEdgeSubset_eq_two_pow_cycleRank` | exact finite binary cycle-space count (6.7) | local proved | The `ZMod 2` incidence kernel is explicitly equivalent to literal finite even edge subsets and has cardinality `2 ^ cycleRank`.  A recoverable edge-disjoint simple-cycle decomposition and weighted cycle-to-walk encoding remain open. |
| `finiteKernelWalkMass_le_pow`, `bipartiteCellKernel_walkMass_le_pow`, `sum_marked_range_finiteKernelWalkMass_even_add_four_le_geometric`, `sum_marked_range_finiteKernelWalkMass_succ_le_geometric` | analytic traversal kernel for (9.16)–(9.18) | local proved | Row norm propagates along finite walks, marked starts cost one cardinality factor, and the positive/even geometric tails are exact in `ENNReal`.  Eventual `tau < 1`, the concrete q-kernel transfer, and cycle-to-walk injections remain open. |

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

`ConfigurationThetaMoments.lean` proves the capped degree moments, exact theta
factorizations, normalized row/column square and global cube bounds in
(9.13)–(9.14), and the zero-total branch.  Its independent warning-as-error
rebuild passed all 3,384 jobs; no asymptotic estimate is hidden in the module.

`FullCornerWeights.lean` proves the complementary-profile feasibility lemmas,
the endpoint factorization (7.5), and the full-corner recurrence (7.6), each in
denominator-free and quotient form.  Its isolated warning-as-error build passed
all 1,921 jobs, and its focused audit reports only the three standard axioms.

Six additional Aristotle-derived leaf modules were manually reviewed and
replayed under Lean 4.31 rather than imported from the service.  The combined
warning-as-error build passed all 3,233 jobs:

- `UniformEquivTransport.lean` proves only uniform-PMF transport along a finite
  equivalence, not the conditioning statement needed for the residual law;
- `ResidualFiberCounts.lean` proves the selected row- and column-stub counts
  class by class, but not residual degree identification or probability;
- `HighCellMass.lean` proves the total-mass bound on the number of high cells;
- `WeightedCauchyTools.lean` proves the finite analytic inequality needed by a
  later Section 8 margin-sum reduction;
- `LocalSignReward.lean` proves only the local exponent arithmetic; and
- `EvenMatchingKernel.lean` proves the parity kernel for matching-supported
  even matrices, not the full small-residual injection or enumeration.

All six are atomic leaves.  In particular, they do not close the canonical
residual conditional law, the full Section 8 skeleton estimates, the Section 9
attachment estimate, or either global signed-moment assembly.

Later accepted Lean 4.31 modules extend these leaves without closing those
assemblies: `UniformConditionalLaw.lean` proves generic finite-uniform
conditioning; `ResidualDegreeMatching.lean` gives exact residual degrees,
class-preserving stub equivalences, and the fixed-extension residual uniform
pushforward; `ConfigurationResidualCellCounts.lean` proves the supporting
class-transport and used-cell lemmas and the exact per-cell identity
`full = demand + transported residual`;
`ConfigurationResidualCellConstraints.lean` proves the exact zero/cap
equivalences with its explicit `hcap` boundary; `ResidualSupportMass.lean` and
`ConfigurationResidualSupport.lean` prove that the number of multiplicity-at-
least-two cells is at most the relevant total count divided by two;
`BipartiteEdgeMatrix.lean` gives
the injective incidence encoding and parity equivalence; and
`EvenMatchingRestriction.lean` proves the generic restriction injection and
`2 ^ |R|` count.  `Section8CanonicalSkeleton.lean` additionally defines the
canonical cutoff demand and proves its partial-matching support and exact
on/off-cutoff values, uniqueness of an ambient-compatible pairing once its
fibres are fixed, fullness of a selected fibre under zero residual and the
displayed cardinal hypotheses, and a generic support-indexed full/residual
constraint equivalence.  `Section9ActualResidualFamily.lean` instantiates the
literal multiplicity-at-least-two residual family and proves its direct
`2 ^ |R|` count, while `Section9ChooseTwoMass.lean` proves the division-free
finite inequality (9.21).  These accepted atoms still do not construct or
count the labelled canonical witness, prove manuscript incidence (8.3),
identify the global conditioned skeleton law, choose and recover a cycle
decomposition, establish the attachment estimate, or prove Lemma 8.3 or
Lemma 9.1.

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

## Aristotle wave 8: locally replayed residual and analytic leaves

| Atomic theorem | Project | Accepted Lean 4.31 module | Limitation |
|---|---|---|---|
| weighted finite Cauchy--Schwarz | `e2c8d889-b584-4930-b702-50bfe4e96f06` | `WeightedCauchyTools.lean` | analytic inequality only; no margin-table assembly |
| uniform PMF transport along an equivalence | `eb6e68c9-7cdc-48d7-b924-d297bd94b079` | `UniformEquivTransport.lean` | does not identify the original conditional law |
| classwise selected row-stub count | `474273da-73c4-41e6-81d2-5693016a684c` | `ResidualFiberCounts.lean` | deterministic row fibre only |
| classwise selected column-stub count | `9cb8b5ce-fef9-428a-a63e-bd4ed805b95f` | `ResidualFiberCounts.lean` | deterministic column fibre only |
| high-cell cardinality versus total mass | `4f3f0236-34ec-4263-b548-e95defbc8385` | `HighCellMass.lean` | no canonical selection or probability statement |
| local sign-reward exponent identity | `acb79d29-444c-4ef8-8cf4-c943c504c370` | `LocalSignReward.lean` | no component-sign or global sum |
| matching-support parity kernel | `5316a33d-76e4-4d2d-8f74-8dfa3ecf8575` | `EvenMatchingKernel.lean` | no residual restriction map or enumeration |

The raw Lean 4.28 service results remain quarantined.  The six repository
modules are reviewed Lean 4.31 ports or reconstructions and passed the local
combined `--wfail` replay; their declarations are included in the central
axiom-audit source.  Acceptance of these leaves does not transfer trust to any
other service result or discharge a non-atomic obligation below.

## Aristotle wave 9: redundant residual atoms

Both isolated service requests completed successfully and are quarantined.
Each service project reports a successful build on its service toolchain and
only the standard axioms.  They carry no repository authority: the
corresponding local Lean 4.31 modules were independently reconstructed,
reviewed, and accepted, and no returned service source was imported.

| Atomic theorem | Service request | Service status | Local authority |
|---|---|---:|---|
| finite target-fibre split used by the residual cell-count decomposition | `826239cf-a40e-40b7-bab7-c08352b8ea2d` | completed; quarantined | `ConfigurationResidualCellCounts.lean` |
| number of configuration-table cells of multiplicity at least two is at most total row-stub count divided by two | `d8760a0e-fed8-4f78-9509-158b8f1151f6` | completed; quarantined | `ConfigurationResidualSupport.lean` |

The first service request concerns only an auxiliary fibre split.  Independently
of that completed request, the accepted local module proves the stronger
per-cell theorem `configurationCellCount_eq_demand_add_residual`.

Aristotle is used here only for redundant candidate generation on isolated
atoms.  A completed service result does not supersede the reviewed local
statement, proof, Lean 4.31 build, source scan, or axiom audit.

## Aristotle wave 10: completed constraint and incidence checks

These isolated service requests completed with successful builds and only the
standard Lean/Mathlib axioms; their request workspaces remain quarantined.  The
corresponding Lean 4.31 modules were independently proved, reviewed, and
accepted locally; no service output has been imported and the local proofs are
authoritative.

| Atomic theorem | Service request | Service status | Local authority |
|---|---|---:|---|
| fixed-witness zero/cap equivalence | `d813a2ec-52b7-4c47-bb42-6c01ed4b9d10` | completed; quarantined | `ConfigurationResidualCellConstraints.lean` |
| bipartite incidence encoding and parity equivalence | `09654357-ad7a-47d3-8ca7-addb8bb28668` | completed; quarantined | `BipartiteEdgeMatrix.lean` |

## Aristotle wave 11: canonical-support and residual-family atoms

The six atomic local results in the first six rows below are accepted Lean 4.31
proofs and are authoritative independently of the service.  Five corresponding
service requests completed, while the pairing request completed with errors;
all returned workspaces remain quarantined and no service source was imported.
The full-Lemma requests and their follow-ups are recorded only as search
provenance.  A service completion, cancellation, or diagnostic counterexample
is not a repository proof and does not close the non-atomic obligation.

| Atomic theorem or work package | Service request | Current service status | Repository status / local authority |
|---|---|---:|---|
| compatible pairing uniqueness after both fibres are fixed | `6701da9c-54b3-43a5-9b07-66df6d73605b` | `COMPLETE_WITH_ERRORS` | independently proved and accepted in `Section8CanonicalSkeleton.lean`; service workspace quarantined |
| selected fibre is full under zero residual and the displayed cardinal hypotheses | `bf257c53-f0e0-4f70-961e-b2908919b25c` | `COMPLETE` | independently proved and accepted in `Section8CanonicalSkeleton.lean`; service workspace quarantined |
| canonical cutoff support is a partial matching with exact on/off-cutoff values | `8cea8264-7636-488c-8948-90d1b66100d4` | `COMPLETE` | independently proved and accepted in `Section8CanonicalSkeleton.lean`; service workspace quarantined |
| support-indexed full/residual cap and no-return translation | `d4dff887-097c-4f54-bf04-e27b74128903` | `COMPLETE` | independently proved and accepted in `Section8CanonicalSkeleton.lean`; service workspace quarantined |
| actual residual even-edge family and direct `2 ^ |R|` bound | `701408de-fc95-4dbf-b3f5-e264575082e9` | `COMPLETE` | independently proved and accepted in `Section9ActualResidualFamily.lean`; service workspace quarantined |
| division-free choose-two mass inequality (9.21) | `7111f397-3732-45f7-bc95-bb99b96b5f8b` | `COMPLETE` | independently proved and accepted in `Section9ChooseTwoMass.lean`; service workspace quarantined |
| cycle-rank bound for a row matching plus residual support | `5ac53fc2-d9fd-4574-ba02-5bae99c26efa` | `COMPLETE` | exact returned source remains quarantined because it fails Lean 4.31 replay and recovery introduces `sorryAx`; an independent local reconstruction in `Section9CycleRankResidual.lean` is warning-fatally proved and accepted with the unchanged theorem statement |
| exact full Lemma 8.3 | `ae343c06-0ad1-40a3-aa0b-0a909b6f30f9` | `COMPLETE_WITH_ERRORS` | rejected: the returned target calls a renamed helper containing one live `sorry`, and `#print axioms` reports `sorryAx`; Lemma 8.3 remains open |
| exact full Lemma 9.1 | `fe0c45b5-e074-4f9d-bd91-af93f2fed768` | `COMPLETE_WITH_ERRORS` | rejected: besides the live `sorry` and resulting `sorryAx`, the helper `sum_fourpow_le` is false because it drops the essential residual cap/no-return event; Lemma 9.1 remains open |
| `sum_fourpow_le` subset-expansion follow-up | `857e6b3d-02cd-4400-bbd9-5bda925b3556` | `CANCELED` | no proof result; does not prove Lemma 9.1 |
| `sum_fourpow_le` sequential-exposure follow-up | `5ee75c79-dee3-46d1-9a9c-15edd7c2900b` | `COMPLETE` | completed with a valid counterexample to the requested helper rather than a proof; does not prove Lemma 9.1 |
| faithful fixed-`F` cap/no-return demand expansion (9.10)--(9.12) | `fe520e24-b80f-406e-b4d0-3a842fca287e` | `RUNNING` | exact locally type-checked request; no repository proof until a returned proof passes all local gates |
| recoverable weighted even-subgraph polymer bound (9.15) | `25a033db-451f-4203-9593-fcb8b1f562d9` | `RUNNING` | decomposition must be constructed in the proof; no decomposition hypothesis or repository result |
| matching-cycle weighted walk enumeration (9.17)--(9.18) | `d433e6aa-0ba2-44e0-9519-3b1f897eb3e4` | `RUNNING` | cycle cutting/encoding must be constructed in the proof; no aggregate-bound hypothesis or repository result |
| deterministic small-residual integrand bound (9.20)--(9.22) | `29f7b05b-f22f-4266-bc04-795aa0cb709e` | `RUNNING` | exact locally type-checked request; no repository proof yet |
| finite analytic endpoint estimate (9.7)--(9.9) | `0be16581-1f1d-4781-a58c-2cb46e4d1bcf` | `RUNNING` | absolute constant is existential; no unjustified small numerical constant and no repository proof yet |

## Non-atomic obligations that must not be hidden

1. Connect the proved fixed-row ordered overlap law (6.1)–(6.2) to the
   project's unordered profile representation, then prove the exact
   sign/component factors (6.3)–(6.7) and assemble Lemma 6.1.
2. Prove the uniform partial-diagonal estimates (7.7)–(7.25), including the
   phase reduction and deterministic uniform error sequence.  The exact finite
   setup, endpoint factorization, and recurrences (7.1)–(7.6) are locally proved.
3. Connect the proved deterministic canonical-support atoms to an actual
   labelled high-skeleton witness and its global conditioned event.  The
   cutoff demand has partial-matching support and exact on/off-cutoff values;
   pairing uniqueness once both fibres are fixed, selected-fibre fullness
   under zero residual, and the generic support-indexed cap/no-return
   translation are also proved.  What remains is to construct and count the
   labelled witness, prove manuscript incidence (8.3), and identify the global
   conditioned skeleton law.  The generic support theorem does not supply
   those steps by itself.
4. Prove the endpoint transportation and all near/middle skeleton sums
   (8.16)--(8.29b), including the no-further-near conditioning event.
5. The manuscript's actual residual even-edge family, its support/count bridge,
   and the exact binary cycle-space cardinality are proved.  Choose an
   edge-disjoint simple-cycle decomposition canonically enough to recover the
   original edge set and encode its cycles as the weighted walks used by the
   analytic bounds.
6. The division-free choose-two mass inequality (9.21) is proved.  Assemble
   (9.10)--(9.22), including the still-open canonical-skeleton instantiation,
   recoverable cycle decomposition, concrete cycle-to-walk encodings, and
   weight/kernel transfer; the abstract traversal/geometric kernel is proved,
   with the actual degree sums and asymptotic error estimates.  The rejected
   raw `sum_fourpow_le` shortcut cannot replace the cap/no-return event: the
   faithful event-restricted attachment argument in both residual-mass regimes
   remains open.  Complete that argument, then prove Lemma 9.1 and
   Proposition 9.2.

## RVE refinement: ordered Sections 8–9 work packages

A second local replay split the remaining Sections 8–9 argument into the
following dependency-ordered packages.  These are proof obligations, not
axioms or aliases for the desired conclusion.

1. **Deterministic cutoff/support atom completed locally:** the canonical high
   demand is defined, its support is a partial matching, and its on- and
   off-cutoff values are exact.  Use it with the proved row/column marginals
   and high-cell mass bound to construct, count, and expose the actual labelled
   canonical high-skeleton witness.
2. **Fixed-witness decomposition completed locally:** the complement is
   identified class-preservingly with a residual `ConfigurationMatching`
   having the exact
   residual degrees.  Finite-uniform conditioning, the fixed-extension uniform
   pushforward, and the exact per-cell identity
   `full configurationCellCount = demand + residual configurationCellCount`
   are proved.  The zero and cap conditions are also translated exactly under
   `hcap : demand <= cap`; the cap becomes `cap - demand`.  The generic
   support-indexed theorem additionally packages the unshifted residual cap
   and residual-zero condition when the explicit split, demand-cap, and
   off-support-zero hypotheses are supplied.  The remaining work is to connect
   these facts to the actual labelled skeleton event and manuscript incidence
   (8.3); the deterministic atoms do not identify that event by themselves.
3. **Fixed-fibre uniqueness atoms completed locally:** an ambient-compatible
   pairing is unique after both fibres are fixed, and zero residual plus the
   displayed subset/cardinality hypotheses forces a selected fibre to be the
   full fibre.  Prove uniqueness of the entire labelled canonical high-demand
   witness and exact manuscript incidence (8.3), including that no residual
   pair returns to a skeleton cell; the union bound behind (6.8) does not
   provide disjointness.
4. Package the preceding facts as an exact decomposition of a full matching
   into a high skeleton, its exposed witness, and a residual matching with the
   skeleton-cell and off-skeleton caps.
5. Count typed partial matchings with prescribed table `ell i j` by the
   cross-multiplied row/column descending-factorial identity.  This is the
   missing finite bridge from the skeleton type to the weight `W(L)` in (8.6).
6. Combine the proved endpoint transportation, exact
   minimum/absolute-difference identities, and local reward exponent with the
   actual skeleton weights in (8.11)–(8.14).
7. Assemble Lemma 8.2 through the proved weighted Cauchy leaf and
   `(sum_r sqrt (D r))^2`.  A sum of one-vector `D` over margin pairs is
   ill-typed and is not an acceptable substitute.
8. Split Lemma 8.3 into the exact ratios (8.21)–(8.22), the recurrence for
   `A_e` including `e=0`, labelled near-deficit expansion, one-sided middle
   threshold expansion, uniform `Xi_4` decay, small-residual deterministic
   majorant, and final skeleton-mass assembly.  The small-residual step is an
   inequality using `g ≥ 1`, never an equality.
9. **Actual residual-family support/count bridge completed locally:** the
   literal even-edge family supported on `M` together with cells of
   multiplicity at least two is defined and has the direct `2^|R|` bound under
   the row-matching hypothesis; the exact binary cycle-space count (6.7) is
   also proved.  Construct a recoverable cycle decomposition; it may not be
   hidden in a renamed hypothesis.
10. Port the mutually exclusive threshold-choice expansion and apply the
    all-cases theorem `jointPrescribedCellBound_cellwise` jointly to the
    combined per-cell demands before removing caps or forbidden-cell events.
11. **Completed locally:** finite degree-sum bounds, exact theta
    factorizations, normalized square/cube estimates (9.13)–(9.14), and the
    zero-total branch.
12. Construct the simple-cycle deletion recursion manually, prove union
    recovery, choose decompositions injectively, and only then apply the
    exponential family overcount in (9.15).
13. Build the cycle-to-closed-walk and marked-cycle-to-traversal encodings
    used in (9.16)–(9.18).  The analytic geometric bounds do not supply these
    encodings, and a marked traversal receives no fresh cardinal factor after
    its initial mark.
14. **Generic and actual restriction leaves completed locally:** finite
    bipartite edge sets have an injective incidence-matrix encoding with exact
    parity equivalence; restriction of supported even matrices to a residual
    relation is injective; and the literal actual residual family satisfies
    the required `M`-plus-`R` support and direct `2^|R|` count.  The number of
    actual configuration cells of multiplicity at least two is at most the
    total row-stub count divided by two.  These cardinality bounds do not prove
    the cycle decomposition, traversal estimates, or attachment bound.
15. **Completed locally:** the division-free choose-two estimate
    `2 * sum_e (r e).choose 2 <= (U - 1) * m₀` under the displayed cap and
    total-mass hypotheses, which is the finite arithmetic content of (9.21).
    The full finite cycle-rank chain in (9.20), including the literal residual-
    support and `m₀ / 2` forms, is now proved.  The exact binary cycle-space
    cardinality and abstract traversal/geometric kernel are also proved.  The
    canonical-skeleton instantiation, recoverable cycle decomposition,
    cycle-to-walk encodings, and integrand/attachment assembly remain open.
16. State the final attachment estimate with one deterministic error sequence
    and one eventual threshold uniform over every feasible skeleton.  A
    skeleton-dependent error sequence or threshold has the wrong quantifiers.

The earlier RVE replay under Lean 4.31 and warning-as-error accepted the
threshold-choice expansion, recoverable-decomposition selector, injective
exponential overcount, closed-walk and marked-traversal geometric bounds,
sign-exponent bookkeeping, and component-constant sign count.  Its original
weighted-Cauchy artifact remains rejected because it retained `sorryAx`; the
separate corrected wave-8 theorem was manually reviewed and accepted in
`WeightedCauchyTools.lean`.  The old cycle decomposition remains rejected
because it contains forbidden `grind +suggestions`.  A capped residual-pair
theorem is mathematically reusable after removing an unused hypothesis that
currently fails warnings-fatal.  Raw external outputs stay quarantined unless
and until an exact local port passes every repository gate.

Only those assemblies, followed by the amplification layer and exact final
target, can close the proof.  Successful isolated arithmetic or enumeration
leaves do not by themselves certify a manuscript lemma.
