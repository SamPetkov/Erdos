# Lean post-M0 audit: M1a and M2 setup — 2026-07-13

## Verdict

**PASS for the imported post-M0 closure.** The exact finite first-moment,
phase-arithmetic, elementary-probability, and phase-setup bricks listed below
are kernel checked. This verdict does **not** assert the independent-block
bounded-differences bridge, the quantitative phase expansion of Lemma 2.1, or
`Erdos625Statement`.

## Audited scope

The four new audited source files and their SHA-256 identifiers are:

| File | SHA-256 |
|---|---|
| `Erdos625/Phase.lean` | `24308AD8C0EDB01861632C7EB6A6FA964A095A2763CCF6BEBE244E7EC6519B35` |
| `Erdos625/ProbabilityTools.lean` | `8C400D9B1ED0776E76B742FD55A67A89E21ADFC599005BBCB8DCFE9CAE047016` |
| `Erdos625/IndependentSets.lean` | `0FF96D0DD09BF781A85542F05A1E7FB55680C701989D2BEDA725637FB3379735` |
| `Erdos625/PhaseExpansion.lean` | `00C2C2A2456652FEC95A39DC70EA4D33F6A0880B5BCE178822A4E3D8546D64B5` |

`BoundedDifferences.lean` and `PhaseEstimates.lean` were active, unimported
work in progress and are expressly outside this verdict.

## Reproduced checks

`lake build --wfail` completed successfully with exactly **3,138 jobs**. The
imported closure comprises the root plus `Foundation`, `GraphModel`, `Phase`,
`PhaseExpansion`, `ProbabilityTools`, `Target`, `IndependentSets`, and
`AxiomAudit`.

A strict scan of that closure found no `sorry`, `admit`, explicit placeholder
axiom, project `axiom` or `constant`, or `unsafe` declaration. The 24 tracked
`#print axioms` checks all reported exactly:

```text
[propext, Classical.choice, Quot.sound]
```

`git diff --check` also passed. During the audit, the CI source gate was found
not to mention explicit placeholder-axiom terms or `constant` declarations.
The workflow was hardened to reject those forms as well as `unsafe`, and the
strengthened local scan passed.

## Independent statement audits

- `Phase.lean`: exact floor semantics, `0 ≤ δ < 1`, and both adjacent
  first-moment ratios passed an endpoint and denominator audit.
- `ProbabilityTools.lean`: Markov, zero-threshold Paley–Zygmund, the
  conditional sub-Gaussian tail, and the exact `Bin(m,1/2)` lower-quarter
  bound passed a constant and totalization audit. The McDiarmid declaration
  still assumes the centered MGF and is not the independent-coordinate
  theorem.
- `IndependentSets.lean`: fixed-set probability, exact expectation, positivity
  semantics, measurability, and shifted Markov events passed checks including
  `s=0` and `s>n`.
- `PhaseExpansion.lean`: exact constants, guarded phase normal forms,
  continuity/boundedness of `K`, and eventual index ranges passed. It makes
  no claim of equations (2.5), (2.6), or (2.2).

## Remaining blockers

The next checkpoint requires two genuine proofs: coordinate oscillation on an
independent Boolean cube must imply the centered sub-Gaussian MGF, and the
falling-factorial, Robbins/Stirling, and Taylor bounds must be assembled into
the quantified endpoint-uniform phase expansion. Until both are imported and
audited, neither Lemma 2.1 nor the final theorem is claimed.
