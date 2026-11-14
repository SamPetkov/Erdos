# Lean 4 formalization of Erdős Problem 625

This directory contains a complete Lean 4 formalization of the explicit
uniform quantitative consequence below. That consequence resolves Erdős
Problem 625. The manuscript in `../arxiv/main.tex` additionally proves the
sharper uniform coefficient `(log 2)^2 / 4 * log(8750/6681)` and a
phase-resolved refinement involving `A_5(delta_n)`; neither is claimed as part
of the current Lean theorem.

The exact top-level result is

```lean
theorem Erdos625.erdos625 : Erdos625.Erdos625Statement
```

where `Erdos625Statement` says that, for `G(n,1/2)`, the probability of

```text
chromaticNumber - cochromaticNumber
  >= ((log 2)^2 / 4 * log (200 / 153)) * n / (log n)^3
```

tends to one along the full sequence of natural numbers.

## Reproduce the modular proof

The project pins Lean and mathlib at version `v4.31.0`. From this directory:

```text
lake exe cache get
lake build --wfail
```

The final declaration is in `Erdos625/Section15FinalInstantiation.lean`.
`Erdos625.lean` is the project root and imports the complete proof closure.

## Reproduce the one-file proof

`Erdos625SelfContained.lean` concatenates the complete transitive local import
closure of the release root into one Lean source file. It retains only external
Mathlib imports; "one-file" therefore means one project source file, not a
copy of Mathlib or a toolchain-free artifact.

Check that it is current:

```text
python scripts/generate_self_contained.py --check
```

Compile it independently:

```text
lake env lean -DwarningAsError=true Erdos625SelfContained.lean
```

The checked source contains 483 local source modules, 86 external imports,
and 91,243 lines. Its normalized-LF SHA-256 (the value printed by the
generator on every platform) is
`bbbfd1867af9996e2aa058defc5bbc020319a5967e5e8b86e693c60f01ee3368`.

## Five-size phase gain

The release root also imports three modules on the five-size phase gain

```text
A_5(delta) = log 2 - F_{S_+}(T_delta) + F_{S_5}(T_delta),
S_+ = {i in Z : i >= -1},  S_5 = {2,...,6},  T_delta = 1 + 2/log 2 - delta,
F_S(T) = inf over real lambda of
         log sum_{i in S} exp(lambda*i - (log 2/2)*i^2) - lambda*T,
```

from the manuscript in `../arxiv/main.tex`. For every `delta` in `[0, 1]`:

| Module | Main theorem | Statement |
|---|---|---|
| `Erdos625/FiveSizeEntropyGap.lean` | `entropy_gap` | the manuscript's Lemma 5.3, including `A_5(delta) > log(8750/6681)` |
| `Erdos625/FiveSizePhaseGainSharp.lean` | `log_2605_div_1651_lt_phaseGain5` | `A_5(delta) > log(2605/1651)` |
| `Erdos625/FiveSizePhaseGainCertificate.lean` | `log_169_div_100_lt_phaseGain5` | `A_5(delta) > log(169/100)` |

The second and third bounds are stronger than the manuscript's. These modules
are part of both the modular build and the one-file proof. They do not change
`Erdos625Statement` or the proof of `Erdos625.erdos625`, whose coefficient is
still `(log 2)^2 / 4 * log(200/153)`.

The project directory also retains four superseded midpoint-route modules for
historical comparison:

- `Erdos625/Section12CanonicalBareSkeletonAsymptotic.lean`;
- `Erdos625/Section12ConcreteSignedFirstMoment.lean`;
- `Erdos625/Section12PartialDiagonalAssembly.lean`;
- `Erdos625/Section13GlobalMidpointSeed.lean`.

They are not imported by `Erdos625.lean`, are not members of the 483-module
release closure, and are not needed for `Erdos625.erdos625`.

## Trust boundary

The proof sources contain no `sorry`, `admit`, project-defined axiom,
`unsafe`, `native_decide`, or `implemented_by`. The final theorem's axiom
audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Public cloud replay evidence

The exact standalone file at source commit
`824e4b609466d2e26b216a76ecf103184dac2663` was independently replayed in a
clean Aristotle cloud workspace. The raw download, primary-command stdout,
stderr, and exit-code records, supplementary check output, source and
toolchain revisions, file checksums, and axiom audit are preserved at
immutable public commit
`31bbe00c529a996bdb61b880120d71240172d18f` in
[`replay/aristotle-03e8124e-c359-4219-8b37-442060dae209`](https://github.com/SamPetkov/Erdos/tree/31bbe00c529a996bdb61b880120d71240172d18f/625/formalization/replay/aristotle-03e8124e-c359-4219-8b37-442060dae209).
The current one-file proof differs from that replayed file only by the three
five-size phase-gain modules and the root module's added imports and
documentation; the current file itself has not been replayed in the cloud.
The replay records are not kept on the main branch; they remain available at
that commit.
