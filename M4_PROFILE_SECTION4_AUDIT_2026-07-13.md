# M4 profile and Section 4 foundation audit — 2026-07-13

## Verdict

**PASS for the pinned declarations below.**  This milestone closes the exact
finite first-moment formula (4.2), including its unordered-partition
enumeration, and the finite profile aggregation needed before (4.3).  It also
closes the compact-uniform four-support optimizer infrastructure and the exact
capacity lower-tail step (10.8).

This is not a certification of (4.3)–(4.5), Lemma 3.1, or
`Erdos625Statement`.  Those obligations remain explicit below.

## Pinned source

| Module | Lines | SHA-256 |
|---|---:|---|
| `CochromaticCapacityLowerTail.lean` | 171 | `1252116F7474370EFE40B5538B5AFE9A75DC0ECE1DE2468BA974D6E23F4DF9FE` |
| `ProfileValueUniformS4.lean` | 54 | `F714518B663A0CCA1BE9820348B5D1CD04CA2B903CE2DE0FBD5C64B8EAD6C3B7` |
| `ProfileOptimizerContinuityS4.lean` | 174 | `CDA02F1B2195E9C0B32C527C36FAC82BFEC5CF3B47590BE93CD6DA00648A21E7` |
| `ProfileOptimizerUniformS4.lean` | 242 | `313CBC9DB688823A93EC7113AC2828796420974F6F27FF7E91A768F201638E22` |
| `ColoringProfileFirstMoment.lean` | 545 | `8B969A16CE6F84FD2729DC526E90B4F07534DFFB6456C0202CDC4278AD8338DD` |
| `ColoringProfileAggregation.lean` | 143 | `E57957D3FE2ECF29F69486954D4FE92D938F71705A43FEC5C24C769A385DBC66` |
| `ColoringProfileEnumeration.lean` | 701 | `1A87F6B63A16F51468CEBF2C34C87B4B319CAA0D0B1C6F9F588FB1CBDF2D5D2A` |
| `ColoringProfileEnumerationInverse.lean` | 265 | `2ABD6A2F8587ECDC4A380EA155AE8C9E75E48B967506DF12930B3A1FA9372032` |
| `ColoringProfileEnumerationInjective.lean` | 316 | `6222DA1EE4944DE830C83B3E6A3AFB2A02866B2422975B4269F5BA9D44E504A3` |

The two documentation-only edits in `ColoringProfileFirstMoment.lean` and
`ColoringProfileAggregation.lean` explain that the isolated enumeration
proposition is proved downstream.  The final hashes above, not the earlier
pre-synchronization hashes, are the accepted pins.

## What is kernel-checked

### Exact capacity lower tail

`randomGraph_cochromaticInducedCapacity_lowerTail` negates the vertex-block
MGF with the correct direction.  Combining it with the already formalized
rare-seed expectation gap gives
`randomGraph_cochromaticInducedCapacity_failureProbability_le` and its strict
event spelling with failure probability `exp (-r)`.  The center is the actual
`G(n,1/2)` expectation, the proxy is `(n-1)/4`, and no two-sided factor is
introduced.

### Compact-uniform four-support optimizer

The target-independent value estimate is promoted to one-index uniformity.
Joint score/target continuity proves moving-target convergence of the mean,
unique tilt, and all four optimizer coordinates.  Heine–Cantor then gives
uniform tilt and optimizer convergence on every compact subset of `(2,5)`,
and compact positivity gives one eventual positive lower bound for all four
coordinates.  Empty compact sets are handled rather than silently excluded.

### Exact finite first moment and enumeration

The finite profile layer uses unordered nonempty `Finpartition` blocks.  It
proves the exact internal-edge count, the probability that a fixed partition
is proper, and the expectation as actual partition cardinality times the
energy factor.

The enumeration chain constructs canonical `(size,label,position)` slots and
factorial decorations.  It proves the decoration count, reconstructs a
profile partition and both decoration coordinates from every slot
equivalence, proves the forward and inverse coordinate laws, and independently
recovers the kernel partition and decoration for injectivity.  The total map
is proved injective and surjective and packaged as
`totalProfileDecorationEquiv`; it is not merely a cardinality equation or an
assumed bijection.

Consequently `profileEnumerationStatement` and the public
`profileColoringExpectation_eq_formula` require only the necessary hypothesis
`ColoringProfile.vertexMass k = n`.  This is the exact mass-constrained form
of (4.2).

The mass guard is mathematically necessary: under mass mismatch the profile-
partition type is empty while the arithmetic Bell coefficient need not be
zero.  Independent compiled edge-case tests covered `b=0`, the zero profile at
`n=0` (enumeration and expectation equal to one), and explicit failure of raw
enumeration for the zero profile at `n=1`.  The unconditional decorated-total
equivalence remains correct under mismatch because both sides are empty.

### Finite aggregation

`boundedColoringProfiles` finitizes all mass-`n`, exactly-`parts`, size-at-most-
`b` profiles inside a coordinate box.  Every admissible coordinate is at most
`n`, the box has exactly `(n+1)^b` elements, and the filtered family has at
most that cardinality.  `boundedProfileColoringExpectation_eq_sum` is the
exact finite sum interchange over the already defined per-profile
expectations.

## Reproduced gates

- Final integrated `lake build --wfail`: **PASS**, 3,709/3,709 jobs.
- Final project inventory: **32 Lean files, 8,413 physical lines**; every
  accepted module is imported by `Erdos625.lean`.
- Recursive source gate for `sorry`, `admit`, `sorryAx`, line-leading project
  `axiom`/`constant`/`unsafe`, `native_decide`, and
  `set_option autoImplicit true`: **PASS**.
- Integrated `Erdos625/AxiomAudit.lean`: **PASS**.  Representative new
  declarations, including the total equivalence, enumeration theorem, and
  public (4.2) formula, use only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Independent frozen-pin audit of all three enumeration modules: **PASS**.
  Direct strict compilation, per-module warning-as-error builds, source scan,
  axiom prints, inverse/injectivity review, and boundary tests all passed with
  unchanged hashes.
- `git diff --check`: **PASS**.
- Dependency audit: **PASS** for Lean 4.31.0, mathlib v4.31.0, all nine locked
  transitive package revisions, import resolution, and root coverage.  No
  external/generated proof input was found.  Conservative transitively
  redundant imports are permitted and are not presented as import-minimal.

The standard run is a locked, cache-assisted build.  Exact control-file and
transitive pins, the distinction from a source-only dependency rebuild, and
reproduction commands are recorded in
[`DEPENDENCY_REPRODUCIBILITY.md`](DEPENDENCY_REPRODUCIBILITY.md).

## Exact remaining Section 4 obligations

1. **Equation (4.3): uniform logarithmic first-moment bound.**  Define the
   finite real log-weight corresponding to the exact ENNReal formula; prove
   zero-safe factorial/log identities and uniform Stirling bounds even when
   some profile coordinates vanish; connect the constrained discrete maximum
   to `L_+(n,k)`; and absorb the at-most `(n+1)^b` profile multiplicity into
   the stated `O(N^2)` error.
2. **Equation (4.4): continuous `S_+` root and rounding decrement.**  Formalize
   the relevant part of Lemma 3.1 for the finite cutoff of `S_+`, including
   existence/uniqueness and the derivative corridor, then transfer from the
   real root to `floor r_+(n) - ceil N` with all domain and positivity guards.
3. **Equation (4.5): deterministic refinement and event inclusion.**  Prove
   that a proper colouring with at most `k` nonempty parts can, when `k≤n`, be
   refined to exactly `k` nonempty independent parts without increasing the
   maximum part size.  Combine it with the independence-number event (2.9),
   positivity of the bounded-profile count, Markov's inequality, and the
   limit from (4.3)–(4.4).

Only after these and all later manuscript dependencies are closed may the
project prove `Erdos625Statement` or unfreeze the private arXiv package.
