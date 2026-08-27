# Reproducibility audit — Erdős Problem 625 self-contained formalization

**Verdict: PASS.** Every requested check matched exactly. The pinned file compiles
under Lean 4.31.0 with exit code 0 and `Erdos625.erdos625` depends on exactly
`propext`, `Classical.choice`, `Quot.sound`.

No file of the audited repository was edited; nothing was committed to it.

## 0. Note on the resumed session

The previously reported background state (`/tmp/lake_deps.log`, an in-flight cache
process, the clone itself) was **not** present when this session began: the machine
had been reset to a bare scaffold, with no log file, no checkout, and no Lean/Mathlib
artifacts. There was therefore no saved cache process to inspect. The audit was
re-run end to end from the pinned commit; `/tmp/lake_deps.log` in this report is the
log of the *new* dependency fetch, preserved here as `lake_cache_get.log`.
Process waiting was done by matching executable names (`pgrep -x`), never a
command-line pattern, so no self-match occurred.

## 1. Source provenance

| Item | Value |
| --- | --- |
| Repository | `https://github.com/SamPetkov/Erdos.git` |
| Commit (as requested, verified) | `86c4422f9b41c4ce50e7c920dc7349a9f07f24a8` |
| Commit date | 2026-08-27 15:14:00 +0300 |
| Working directory | `625/formalization` |

## 2. Integrity checks — all match

| Check | Expected | Observed | Result |
| --- | --- | --- | --- |
| SHA-256 of `Erdos625SelfContained.lean` | `0f54ac26285e5a1631ed62f0258ba0836cc3a2cd28cc35df3b2f737cfaffac30` | identical | MATCH |
| Local source modules | 475 | 475 | MATCH |
| External imports | 86 | 86 | MATCH |
| Logical lines | 88,563 | 88,563 | MATCH |
| Hash reported by generator | as above | identical | MATCH |

`wc -l Erdos625SelfContained.lean` independently reports `88563`.

Verbatim generator output:

```
$ python3 scripts/generate_self_contained.py --check
checked Erdos625SelfContained.lean: 475 source modules, 86 external imports, 88563 lines, sha256=0f54ac26285e5a1631ed62f0258ba0836cc3a2cd28cc35df3b2f737cfaffac30
[exit 0]
```

No byte or metric differed, so the audit proceeded to compilation.

## 3. Environment

| Item | Value |
| --- | --- |
| Toolchain pin (`625/formalization/lean-toolchain`) | `leanprover/lean4:v4.31.0` |
| `lake env lean --version` | `Lean (version 4.31.0, x86_64-unknown-linux-gnu, commit 68218e876d2a38b1985b8590fff244a83c321783, Release)` |
| Mathlib requirement (`lakefile.toml`) | `https://github.com/leanprover-community/mathlib4.git`, rev `v4.31.0` |
| Mathlib revision (`lake-manifest.json`) | `fabf563a7c95…` (inputRev `v4.31.0`) |
| Other pinned packages | plausible, LeanSearchClient, importGraph, proofwidgets, aesop, Qq, batteries, Cli — all at manifest revisions |
| Cache | `lake exe cache get`: 8542 files downloaded and decompressed from the official Mathlib cache; no local rebuild of Mathlib |
| Host | Linux x86_64, 8 cores, 64 GB RAM |

## 4. Compilation

Exact command, run from `625/formalization`:

```
lake env lean -DwarningAsError=true Erdos625SelfContained.lean
```

| Item | Value |
| --- | --- |
| **Exit code** | **0** |
| Wall-clock | ≈ 9 min 20 s (single `lean` invocation; peak RSS several GB) |
| Diagnostics with a `file:line:col:` position | **0** (no `error:`, no `warning:`) |
| `sorry` / `sorryAx` in output | none |
| `sorry`, `native_decide`, `@[implemented_by]` in the source file | none |
| `axiom` declarations in the source file | 0 |

Because `-DwarningAsError=true` was in force, exit code 0 establishes that Lean
emitted **no errors and no warnings**.

### Complete diagnostic summary

The full 200,829-byte output is preserved verbatim as
`erdos625_selfcontained_compile.log`. It consists of exactly two kinds of content
and nothing else:

1. **21 identical informational suggestion blocks** (84 lines total), emitted
   without a source position and at *information* severity — they did not fail the
   build under `warningAsError`:

   ```
   Try this:
     [apply] ring_nf

     The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.

     Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
   ```

2. **1664 `#print axioms` results.** Their distribution:

   | Axiom set reported | Count |
   | --- | --- |
   | `propext, Classical.choice, Quot.sound` | 1604 |
   | `propext, Quot.sound` | 55 |
   | `propext` | 4 |
   | `Quot.sound` | 1 |
   | `does not depend on any axioms` | 4 |

   Every axiom set observed anywhere in the file is a subset of
   `{propext, Classical.choice, Quot.sound}`. No `sorryAx` and no
   repository-declared axiom appears in any of the 1664 outputs.

## 5. Axiom check for the main theorem

The file declares the target at line 87490 as `theorem erdos625 : Erdos625Statement`
and audits it twice — `#print axioms erdos625` at line 87501 and
`#print axioms Erdos625.erdos625` at line 88530. Both produce the same line
(log lines 1365 and 2965):

```
'Erdos625.erdos625' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**This contains exactly `propext`, `Classical.choice`, and `Quot.sound` — the three
standard Lean axioms, and nothing else.** No `sorryAx`, no custom axiom, no
`Lean.ofReduceBool`/`Lean.trustCompiler`.

## 6. Files in this directory

- `AUDIT_REPORT.md` — this report.
- `erdos625_selfcontained_compile.log` — complete stdout+stderr of the audited command.
- `lake_cache_get.log` — complete log of the pinned dependency/cache fetch.
