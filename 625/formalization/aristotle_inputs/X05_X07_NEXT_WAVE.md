# X05/X07 next-wave decomposition

Date: 2026-07-15.  Environment for every isolated package: Lean 4.28.0 and
Mathlib commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

This ledger records theorem interfaces only.  It contains no Lean proof
placeholder and does not claim that an Aristotle response has passed local
replay.

Local declaration validation: **PASS**.  Each of the eight source-only
packages below was elaborated with Lean 4.28.0 against the pinned Mathlib
commit.  Each contains exactly one intentional target `sorry`, no `axiom`,
`admit`, `unsafe`, or `implemented_by`, and no local `.lake` dependency cache.

## X05: simultaneous leftover-colouring tail

The faithful target event is

```text
leftoverLinearEvent C n =
  {G | forall U : Finset (Fin n),
    (chromaticNumberNat (G.induce U) : Real) <=
      C * U.card / log n + n^(1/3)}.
```

The universal quantifier is inside the event in every downstream package.

### X05a -- finite-union probability transport

Package: `.aristotle/pending-next/x05a_exact_event_union_bound`

Declaration: `exactSizeUniversalEvent_compl_probability_le`.

For a property `P S omega` indexed by the exact `u`-subsets of `Fin n`, if
each failure event has real probability at most `delta`, then the complement
of the one universal event has real probability at most
`Nat.choose n u * delta`.  No independence hypothesis appears.  Instantiating
`P` with complement quarter-density is the X01-to-common-event transport.

### X05b -- X02/X03/X04 event bridge

Package: `.aristotle/pending-next/x05b_density_chain_event_bridge`

Declaration:
`exactQuarterDensityEvent_subset_uniformIndependentSetEvent`.

Inputs are exactly the X02 density-lift interface, the X03 quarter-chain
interface, and X04's common survival inequalities at `start`.  The conclusion
is one event asserting that every vertex set of size at least `start` contains
an independent set of size at least `block`.  The only new proof obligation is
transporting survival from `start` to a larger `S.card` and assembling the
two prior deterministic results.

### X05c -- uniform numerical greedy cost

Package: `.aristotle/pending-next/x05c_greedy_numeric_bound`

Declaration:
`greedyColorCost_eventually_le_linear_log_plus_cubeRoot`.

From X04's exact eventual lower bound

```text
log n / (26 * log 4) <= quarterSteps n,
```

this target exhibits an absolute `C > 0` and proves, uniformly for every
`u <= n`, that the piecewise natural greedy cost is at most
`C*u/log n + n^(1/3)`.  The piecewise definition is essential: below
`quarterStart n` it uses `u`, eliminating the otherwise spurious `+1` from a
ceiling.

### X05d -- deterministic universal leftover event

Package: `.aristotle/pending-next/x05d_uniform_independent_to_leftover`

Declaration:
`uniformIndependentSetEvent_subset_leftoverLinearEvent`.

The accepted `simultaneous_induced_chromatic_bound` is exposed through its
exact functional interface.  Together with X05c's uniform numerical bound it
maps the one uniform independent-set event into the faithful
`leftoverLinearEvent`.

### X05e -- full universal-event probability assembly

Package: `.aristotle/pending-next/x05e_full_universal_leftover_tail`

Declaration:
`exists_leftoverLinearEvent_probability_tendsto_one`.

Given one measurable good event, its deterministic eventual inclusion in
`leftoverLinearEvent C n`, and a deterministic real failure bound tending to
zero, this target proves

```text
exists C0 : Real, 0 < C0 and
  Tendsto (fun n => randomGraphMeasure n (leftoverLinearEvent C0 n))
    atTop (nhds 1).
```

The pinned Lean 4.28 Mathlib predates `SimpleGraph.binomialRandom`, so the
isolated package represents the exact `p=1/2` law as `uniformOn Set.univ`, as
does X01.  This is mathematically identical to the repository's current
binomial-random-graph wrapper.  This is the final X05 assembly, not a
fixed-`U` substitute.

## X07: rare-seed amplification and cochromatic upper tail

Define the exact accepted capacity radius

```text
sqrt (((n-1) * Lambda) / 2) + sqrt (((n-1) * r) / 2)
```

and the displayed amplification error

```text
C * ((sqrt (n*Lambda) + sqrt (n*r)) / log n + n^(1/3) + 1).
```

### X07a -- deterministic capacity/leftover inclusion

Package:
`.aristotle/pending-next/x07a_capacity_leftover_threshold_inclusion`

Declaration:
`capacitySuccess_inter_leftover_subset_amplifiedUpper`.

The abstract `capacity` and `zeta` arguments are intended to be instantiated
by the accepted repository definitions `cochromaticInducedCapacity G k` and
`cochromaticNumber G`.  The witness hypothesis is exactly
`exists_capacity_witness_with_compl_bound`: it supplies an attaining core,
the exact complement cardinality, and deterministic concatenation.  The
target proves the actual displayed threshold inclusion; it assumes no
cochromatic upper-tail statement.

### X07b -- one-index quantitative amplification

Package: `.aristotle/pending-next/x07b_quantitative_amplification`

Declaration: `cochromaticAmplified_failureProbability_le`.

From the accepted capacity-success complement bound `exp(-r)`, X05's
leftover-event complement bound `epsilon`, and the exact deterministic
capacity witness, this target proves that the displayed cochromatic upper-tail
failure has real probability at most `exp(-r) + epsilon`.  There is no
independence hypothesis.

### X07c -- full-sequence quantifier assembly

Package:
`.aristotle/pending-next/x07c_full_sequence_quantifier_assembly`

Declaration: `cochromaticAmplified_fullSequence_upperTail`.

The theorem fixes `C`, `epsilon`, the universal leftover estimate, the
capacity statistic, its witness bridge, and the accepted capacity-tail
interface before quantifying over arbitrary deterministic sequences
`k`, `Lambda`, and `r`.  Its conclusion is the eventual bound

```text
Pr{zeta(G_n) > k_n +
  C*((sqrt(n*Lambda_n)+sqrt(n*r_n))/log n + n^(1/3)+1)}
  <= exp(-r_n) + epsilon_n.
```

This is a generic Section X theorem only; it is not the final Erdős 625
statement.

## Concrete X07 instantiation

No separate concrete package was created.  The repository does not yet
define `kCoConcrete` or `LambdaConcrete`, and
`XI02_CONCRETE_FINAL_INSTANTIATION.md` correctly records that their Section IX
seed bound and `LambdaConcrete = o(n/(log n)^4)` estimate are upstream open
obligations.  Creating a concrete target now would hide those missing facts
behind assumptions or restate an equivalently hard final theorem.

## Adapter packages for X01 and X05e

Three additional source-only packages were declaration-checked with Lean
4.28.0 against the same pinned Mathlib commit.  Each contains exactly one
intentional target `sorry`, no `axiom`, `admit`, `unsafe`, or
`implemented_by`, and no local `.lake` cache.

### X01a -- quarter-density failure to the X01 tail event

Package:
`.aristotle/pending-next/x01a_quarter_density_failure_adapter`

Declaration:
`not_quarterDenseOn_complement_implies_lowerQuarter`.

For a labelled graph `G` and vertex set `S`, failure of
`QuarterDenseOn Gᶜ S` implies both the explicit natural-number floor bound

```text
inducedComplementEdgeCount S G <= Nat.choose S.card 2 / 4
```

and the real inequality defining X01's fixed-set lower-quarter event.  Thus
the conversion does not hide the strict natural-number inequality or the
rounding performed by `Nat` division.

### X01b -- exact quadratic exponent comparison

Package: `.aristotle/pending-next/x01b_choose_two_quadratic_bound`

Declaration: `square_div_sixtyFour_le_choose_two_div_sixteen`.

In the exact numeric type used by the exponential tail, it proves under the
minimal hypothesis `2 <= u` that

```text
(u : Real)^2 / 64 <= (Nat.choose u 2 : Real) / 16.
```

This is the deterministic inequality needed to replace the X01 exponent by
the quadratic exponent used by the union-bound decay.

### X05f -- generic-measure universal-event assembly

Package: `.aristotle/pending-next/x05f_generic_measure_universal_tail`

Declaration:
`exists_leftoverLinearEvent_probability_tendsto_one_generic`.

This is X05e with an arbitrary family
`mu : forall n, Measure (LabeledGraph n)` and explicit probability-measure
witnesses `forall n, IsProbabilityMeasure (mu n)`.  Its conclusion uses
`mu n` directly, so the repository can instantiate it with
`randomGraphMeasure` without first asserting an equality with a separate
uniform graph law.  The faithful event is unchanged: `leftoverLinearEvent`
still contains the universal quantifier over every induced vertex set `U`
inside the event.
