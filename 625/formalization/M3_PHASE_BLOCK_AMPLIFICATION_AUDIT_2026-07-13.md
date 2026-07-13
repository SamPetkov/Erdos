# M3 phase, vertex-block, and amplification-interface audit

**Date:** 2026-07-13

**Toolchain:** Lean and mathlib `v4.31.0`

**Verdict:** PASS for the declarations listed below; this is not a proof of
`Erdos625Statement`.

## Scope

This milestone closes three previously explicit infrastructure gaps:

1. the full-sequence consequences (2.3), (2.4), and (2.9) of the audited phase
   expansion;
2. the exact variable-size vertex-block representation of `G(n,1/2)`, including
   event and expectation transport and finite-block bounded differences;
3. the induced-cocolourability capacity, its endpoint event, concentration,
   maximizing core, deterministic leftover inequality (10.9), generic
   rare-seed inversion, and graph-specific expectation bound (10.7).

It also records the finite four-support mean inversion, zero-safe entropy
optimizer, and fixed-target value stability used as infrastructure for
Lemma 3.1.  The continuous profile roots,
overlap estimates, residual attachment, simultaneous leftover-colouring event,
lower-tail step (10.8), and final theorem remain open.

## Pinned accepted source

| Module | Physical lines | SHA-256 |
|---|---:|---|
| `BlockBoundedDifferences.lean` | 471 | `057F7D3AF61EAD4A05EB2DF9CFF6C8519EBAC199D99BAC42D21A30F049FE1E1A` |
| `PhaseAsymptotic.lean` | 559 | `01B8AC33271BB06CCFC5279C457F883270D4BCB236713DFAEFBCC8815B5A9043` |
| `PhaseConsequences.lean` | 496 | `94BB58809EBE84BA1CA1E5442BBDC3D134E7F9239B692F0A13013351F722D075` |
| `VertexBlockGraph.lean` | 266 | `A2696B53A61B75C29FEC9617DFE5998753820E409130734C17363B138EF5C83F` |
| `VertexBlockExpectation.lean` | 34 | `F46035106F96110D20C357417D76482D2B3C4D3CD343329D7E516F7DBB6D34B5` |
| `InducedCochromaticCapacity.lean` | 359 | `566B5856322EFB3A78C7F0F87045960728C19E5EFA4CABBE09C84F058D621CF0` |
| `CochromaticAmplification.lean` | 93 | `17732D8062DA47E07DA8A509008F0B3319096285ECFDC150091CF1469F086B3F` |
| `RareSeedInversion.lean` | 133 | `0C96BD24777698D2EF7AEEB3D712E4CFEEFAC8016FA8E9D32B75DD0BB63C967F` |
| `CochromaticSeedGap.lean` | 102 | `66D847C2DF2BFF38826D67E071B3CA1EDA052528508D734AB50276EBD3EBCB7D` |
| `ProfileEntropyS4.lean` | 397 | `1B55E8BAC87D5BAFEF2D46BB479B0D7828740FD0FA64A6360EA375C10A236B62` |
| `ProfileOptimizerS4.lean` | 197 | `23300A989FD1EC236402EB02535DE775DA1290D42F9639EEB08DBF5AC930F3CE` |
| `ProfileValueStabilityS4.lean` | 126 | `A6487FECE04718D81D2685E13071F598B27AEB1F0C143812009E93664F6F9803` |

## Reproduced gates

- `lake build --wfail`: **PASS**, 3,694 jobs.
- Recursive Lean source gate for `sorry`, `admit`, `sorryAx`, project
  `axiom`/`constant` declarations, and `unsafe`: **PASS**.
- Tracked representative `#print axioms` audit: **PASS**.  Public results use
  only `propext`, `Classical.choice`, and `Quot.sound`; the explicit
  `CoColoring.pullback` theorem uses no axioms.
- `git diff --check`: **PASS**.

The combined build also detected and corrected an integration-only namespace
mistake: `ProfileOptimizerS4.lean` extends
`Erdos625.ProfileEntropyS4`, so the root axiom audit and ledger now use the
actual declaration namespace.  No theorem statement or proof changed.

## Independent semantic review

Separate read-only reviews checked the phase consequences, finite-block MGF
induction, vertex-block equivalence and pushforward law, exact expectation
transport, four-support optimizer, capacity deletion oscillation, endpoint
event, chosen `(n-1)/4` variance profile, one- and two-sided graph tails,
maximizing-core complement construction, rare-seed exponential inversion, and
the graph-specific `(10.7)` substitution.  Each review reproduced warning-as-
error compilation, source and axiom gates, and the pinned hash.

The four-support value-stability review additionally checked both
cross-evaluation inequality directions, zero-coordinate compatibility,
coordinatewise sup bounds, and the fixed-`T` quantifier on the convergence
corollary.  It does not promote that corollary to compact-uniform convergence
in `T`.

The zero-proxy cases `n=0,1` are deliberately not passed through the positive-
variance rare-seed inversion.  The concentration statements themselves remain
valid there under Lean's totalized division, but are vacuous; a separate
degeneracy argument would be required if those finite cases were ever needed.

## Aristotle boundary

Two isolated Lean 4.28 Aristotle tasks were used only as proof-search
cross-checks.  One returned inverse proofs that were not imported; the second
identified the explicit `Finset.Nonempty.image` elaboration needed for the
finite maximum.  All accepted graph, probability, and asymptotic proofs were
ported or authored and checked locally on Lean 4.31.  Returned archives remain
ignored and quarantined, and both temporary API keys were revoked.  Full
details and CLI reproduction commands are in `ARISTOTLE_WORKFLOW.md`.

## Status after M3

This milestone materially advances Lemma 10.2 but does not complete it: (10.7)
and (10.9) are formalized, while the lower-tail assembly (10.8), the uniform
leftover-colouring Lemma 10.1, and their final intersection remain open.  The
private arXiv package therefore remains frozen under the full-proof-first gate.
