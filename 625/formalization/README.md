# Lean 4 formalization of Erdős Problem 625

This directory contains the complete Lean 4 formalization of the theorem
stated in `../arxiv/main.tex`.

The exact top-level result is

```lean
theorem Erdos625.erdos625 : Erdos625.Erdos625Statement
```

where `Erdos625Statement` says that, for `G(n,1/2)`, the probability of

```text
chromaticNumber - cochromaticNumber
  >= ((log 2)^2 / 32 * log (200 / 153)) * n / (log n)^3
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

The checked source contains 475 local source modules, 86 external imports,
and 88,563 lines. Its normalized-LF SHA-256 (the value printed by the
generator on every platform) is
`0f54ac26285e5a1631ed62f0258ba0836cc3a2cd28cc35df3b2f737cfaffac30`.

## Trust boundary

The proof sources contain no `sorry`, `admit`, project-defined axiom,
`unsafe`, `native_decide`, or `implemented_by`. The final theorem's axiom
audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Public cloud replay evidence

The exact standalone file at source commit
`86c4422f9b41c4ce50e7c920dc7349a9f07f24a8` was independently replayed in a
clean Aristotle cloud workspace. The complete merged stdout/stderr, exit code,
source and toolchain revisions, file checksums, and audit report are preserved
at immutable public commit `1eb0aeba305327d383496b912a1e6e1a8fa71947` in
[`replay/aristotle-76792321-4b5f-4367-8885-d1470db80091`](https://github.com/SamPetkov/Erdos/tree/1eb0aeba305327d383496b912a1e6e1a8fa71947/625/formalization/replay/aristotle-76792321-4b5f-4367-8885-d1470db80091).
