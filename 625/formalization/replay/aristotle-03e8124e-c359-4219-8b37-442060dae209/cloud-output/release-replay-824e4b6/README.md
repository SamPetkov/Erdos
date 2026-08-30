# Release replay `824e4b6` — raw artifacts

Independent replay of the pinned Erdős 625 Lean sources. **No supplied source
file was created, edited, repaired, or deleted by this replay**; every artifact
here is new and confined to this directory.

Read `AUDIT_REPORT.md` for the full findings.

## Outcome in one table

| # | Command | Exit |
| --- | --- | --- |
| 00 | `lake exe cache get` | 0 |
| 01 | `lake build --wfail` | 0 |
| 02 | `lake env lean -DwarningAsError=true Erdos625/Section12ConcreteSignedFirstMoment.lean` | 0 |
| 03 | `lake env lean -DwarningAsError=true Erdos625/Section12PartialDiagonalAssembly.lean` | **1** (missing `.olean` for its import; module is outside the default-target closure) |
| 04 | `lake env lean -DwarningAsError=true Erdos625/Section15FinalInstantiation.lean` | 0 |
| 05 | `lake env lean -DwarningAsError=true Erdos625.lean` | 0 |
| 06 | `lake env lean -DwarningAsError=true Erdos625/AxiomAudit.lean` | 0 |
| 07 | `lake env lean -DwarningAsError=true Erdos625SelfContained.lean` | 0 |

`Erdos625.erdos625` depends on axioms: `[propext, Classical.choice, Quot.sound]`.

## Reproduce

From the repository root, with Lean/Lake from `lean-toolchain`:

```
replay/release-replay-824e4b6/run_replay.sh
```

The driver writes `logs/<tag>.stdout.log`, `logs/<tag>.stderr.log`, and
`logs/<tag>.exit-code.txt` for each command, plus `summary.tsv` and
`timeline.txt`. It never touches a source file.

## Integrity of these logs

`SHA256SUMS-logs.txt` seals every preserved log. Verify with:

```
cd replay/release-replay-824e4b6 && sha256sum -c SHA256SUMS-logs.txt
```

The log files are additionally stored with read-only permissions.
