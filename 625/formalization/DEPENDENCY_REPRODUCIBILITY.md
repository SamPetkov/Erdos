# Lean dependency and reproducibility record

**Audit date:** 2026-07-13

This record fixes what “self-contained” means for the formalization.  Every
project theorem is elaborated from the tracked project source and checked by
Lean's kernel.  Project modules name the project or mathlib modules they use
with ordinary Lean `import` declarations; the root module imports every
accepted project layer.  No external service response, generated project
proof object, or private theorem file is an input.  The standard reproduction
below may use mathlib's content-addressed compiled cache as an acceleration;
that cache is tied to the locked dependency revisions and is not a project
proof source.

The repository does not copy the Lean standard library or mathlib source.
Instead, it gives Lake a reproducible, content-addressed dependency closure.
This is the standard auditable notion of a self-contained Lean project: the
repository plus the pinned public toolchain and lockfile suffice to reconstruct
and kernel-check every imported result.

## Direct toolchain and library pins

| Input | Pin | SHA-256 of tracked control file |
|---|---|---|
| Lean toolchain | `leanprover/lean4:v4.31.0` | `EFAC0B94923B2D8B6840CD35BE9177AD0FC5AB2332F4F4311C98712CEE92FDEE` (`lean-toolchain`) |
| mathlib | tag `v4.31.0`; commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` | `618799B4648A3FED6F033E9C5A4239FBFFC4A769452E26362F5A2E5087CF02EB` (`lakefile.toml`) |
| complete Lake closure | tracked `lake-manifest.json` | `2D44C1423A5B32897C583A81237CCCE01D4A8AB48D6A1D4AC85F7FC47C17E3D9` |

The manifest resolves mathlib's transitive packages to these commits:

| Package | Commit |
|---|---|
| `mathlib` | `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` |
| `plausible` | `63045536fe95024e6c18fc7b48e03f506701c5bc` |
| `LeanSearchClient` | `c5d5b8fe6e5158def25cd28eb94e4141ad97c843` |
| `importGraph` | `5c7542ed018c78194f1e2b903eaf6a792b74c03d` |
| `proofwidgets` | `24b0d9dc081c5423f8eec7e866c441e5184f29d9` |
| `aesop` | `e3cb2f741431ce31bf73549fb52316a57368b06f` |
| `Qq` | `f46324995fca5f0483b742e4eb4daec7f4ee50d2` |
| `batteries` | `fa08db58b30eb033edcdab331bba000827f9f785` |
| `Cli` | `92564e5770e4d09f2d86dfbf8ada1e9c715b384c` |

These are build dependencies, not additional mathematical assumptions.  A
representative `#print axioms` closure is compiled in
`Erdos625/AxiomAudit.lean`; accepted project theorems use only the standard
logical principles reported there (`propext`, `Classical.choice`, and
`Quot.sound`, with some constructive declarations using fewer).

## Reproduction

From `625/formalization`, the standard cache-assisted replay is:

```powershell
lake exe cache get
lake build --wfail
```

An ordinary reproduction must not run `lake update`: that would intentionally
change the lockfile rather than replay it.  To force local compilation rather
than downloading new compiled caches, use `lake build --no-cache --rehash
--wfail` after removing existing Lake build-output directories; this is a much
more expensive source-only dependency replay and is not what the recorded
cache-assisted milestone run claims.  GitHub Actions checks the same tracked
project source on Ubuntu, rejects proof placeholders and project-defined
`axiom`, `constant`, or `unsafe` declarations, and runs the warning-as-error
build.  The milestone audit records pin the project source hashes and the
result of the corresponding locked, cache-assisted dependency-closure build.

## Import discipline

- Every source file declares ordinary project/mathlib imports and does not rely
  on editor state or a previous interactive session.  Some files retain
  conservative direct imports that are transitively redundant; import
  minimality is not part of the soundness or reproducibility claim.
- `Erdos625.lean` is the accepted-project root and imports every accepted
  formalization layer.
- `Erdos625/AxiomAudit.lean` imports those layers independently and prints the
  kernel dependency closure of representative public theorems.
- Experimental Aristotle files remain ignored and quarantined.  Any useful
  idea must be restated in tracked Lean 4.31 source and pass the same local
  build and audit before it can enter the root.
- Python checks, manuscript calculations, and numerical experiments are
  validation evidence only; no Lean theorem depends on them.
