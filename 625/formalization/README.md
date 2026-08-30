# Lean 4 formalization of Erdős Problem 625

This directory contains a complete Lean 4 formalization of the explicit
uniform quantitative consequence below. That consequence resolves Erdős
Problem 625. The manuscript in `../arxiv/main.tex` additionally proves the
phase-resolved refinement involving `A_4(delta_n)`; that refinement is not
claimed as part of the current Lean theorem.

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
closure into one Lean source file. It retains only external Mathlib imports.

Check that it is current:

```text
python scripts/generate_self_contained.py --check
```

Compile it independently:

```text
lake env lean -DwarningAsError=true Erdos625SelfContained.lean
```

The checked source contains 480 local source modules, 86 external imports,
and 89,528 lines. Its normalized-LF SHA-256 (the value printed by the
generator on every platform) is
`53060b9563330f20a5f2133ffdf8f56e5a41eae6d0f772487193d9c54133e837`.

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
