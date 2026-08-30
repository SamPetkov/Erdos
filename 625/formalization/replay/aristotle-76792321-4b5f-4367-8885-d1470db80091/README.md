# Historical cloud replay: Erdős 625

This directory preserves the independently downloadable output of an earlier
Aristotle cloud replay. It checks the superseded source commit
`86c4422f9b41c4ce50e7c920dc7349a9f07f24a8` and is retained only as historical
provenance. The sharp release and its current standalone file are replayed in
`../aristotle-03e8124e-c359-4219-8b37-442060dae209/`.

## Run identity

- Provider: Aristotle by Harmonic
- Request/project ID: `76792321-4b5f-4367-8885-d1470db80091`
- Completed task ID: `0ab123aa-eb27-4cd2-b28c-e3cddec699f0`
- Request URL: <https://aristotle.harmonic.fun/dashboard/requests/76792321-4b5f-4367-8885-d1470db80091>
- Audit date: 27 August 2026
- Audited repository: <https://github.com/SamPetkov/Erdos.git>
- Audited commit: `86c4422f9b41c4ce50e7c920dc7349a9f07f24a8`
- Working directory: `625/formalization`

## Exact source and toolchain

- File: `Erdos625SelfContained.lean`
- SHA-256: `0f54ac26285e5a1631ed62f0258ba0836cc3a2cd28cc35df3b2f737cfaffac30`
- Closure check: 475 source modules, 86 external imports, 88,563 lines
- Lean pin: `leanprover/lean4:v4.31.0`
- Lean version: `Lean (version 4.31.0, x86_64-unknown-linux-gnu, commit 68218e876d2a38b1985b8590fff244a83c321783, Release)`
- Mathlib pin: `v4.31.0`
- Mathlib revision: `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`

The deterministic closure check was:

```text
python3 scripts/generate_self_contained.py --check
checked Erdos625SelfContained.lean: 475 source modules, 86 external imports, 88563 lines, sha256=0f54ac26285e5a1631ed62f0258ba0836cc3a2cd28cc35df3b2f737cfaffac30
[exit 0]
```

## Kernel command and result

The exact command, run from `625/formalization`, was:

```text
lake env lean -DwarningAsError=true Erdos625SelfContained.lean
```

The exit code was `0`. The complete command output is preserved in
`erdos625_selfcontained_compile.log`. The cloud command redirected stderr into
stdout (`> /tmp/compile.log 2>&1`), so that file is the complete merged stdout
and stderr stream rather than a filtered excerpt.

The target theorem was audited twice. Both occurrences report exactly:

```text
'Erdos625.erdos625' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The transcript contains no position-tagged error or warning, no `sorryAx`, and
no axiom outside `propext`, `Classical.choice`, and `Quot.sound`. The 21
position-less `ring_nf` suggestions are informational messages and did not fail
the command under `-DwarningAsError=true`.

## Preserved files and checksums

| File | Purpose | SHA-256 |
| --- | --- | --- |
| `AUDIT_REPORT.md` | Human-readable provenance and diagnostic audit | `634ffd26177ccdd60ac9d62b3215d5b31bd5ef2b353f9b2957b7263faa756f24` |
| `erdos625_selfcontained_compile.log` | Complete merged stdout and stderr | `91449fb3c229454c77659d1498dc65af5feb40a2b1e817ff97b4e5e01dad0122` |
| `lake_cache_get.log` | Complete pinned dependency-cache transcript | `3fb0b82411b6bae733bf567cee70c81728bcebf3f25c9fb68131ea983f607b07` |
| `exit-code.txt` | Exit status of the exact Lean command | `9a271f2a916b0b6ee6cecb2426f0b3206ef074578be55d9bc94f6f3fe3ab86aa` |

The Aristotle project archive was downloaded through the official authenticated
CLI. The three cloud-generated audit files above are included byte-for-byte;
their checksums match the downloaded archive.
