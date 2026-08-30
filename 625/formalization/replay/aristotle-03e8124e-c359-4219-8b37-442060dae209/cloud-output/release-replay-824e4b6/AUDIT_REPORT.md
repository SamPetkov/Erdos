# Independent release replay — Erdős 625 Lean formalization

**Verdict: PASS with one reproducible command failure that is an invocation-order
artifact, not a source defect.**

Six of the seven requested commands returned exit code 0 with no `error:` and no
`warning:` diagnostics under `-DwarningAsError=true`. The one failure,
`lake env lean -DwarningAsError=true Erdos625/Section12PartialDiagonalAssembly.lean`
(exit 1), is caused by a missing `.olean` for an imported module that
`lake build --wfail` never compiles, because that module is outside the import
closure of the default target. It is reported here as it occurred; no source file
was repaired, rewritten, or modified.

All integrity metrics for `Erdos625SelfContained.lean` matched exactly, the
constant `Foundation.gapConstant` is the exact one-quarter constant, the final
theorem is instantiated through the fixed-offset seed/root chain, and the printed
axiom closure of `Erdos625.erdos625` is exactly `propext`, `Classical.choice`,
`Quot.sound`.

No supplied source file was edited. Everything written by this replay lives under
`replay/release-replay-824e4b6/`.

---

## 1. Provenance

| Item | Value |
| --- | --- |
| Requested source commit | `824e4b6` |
| Commit present in the supplied working copy | `f6f4ad4f257b8e4329502b27d8bc806becf513ef` ("Initial commit", 2026-08-30) |
| Tracked files hashed | 499 (`SHA256SUMS-all-tracked.txt`) |

**Caveat, stated plainly:** the working copy delivered for this replay carries a
single squashed commit; the requested commit id `824e4b6` is not an ancestor and
cannot be verified from git history here. Provenance was therefore established by
content hash instead, and the content hash of the pinned artifact matches the
value supplied in the request (see §2). Every tracked file's SHA-256 is recorded
in `SHA256SUMS-all-tracked.txt` so the tree can be matched byte-for-byte against
the release commit elsewhere.

Selected hashes:

| File | SHA-256 |
| --- | --- |
| `Erdos625SelfContained.lean` | `53060b9563330f20a5f2133ffdf8f56e5a41eae6d0f772487193d9c54133e837` |
| `Erdos625.lean` | `a6e6630a9ab38386abb2d202fb39f01b79d0b9e36346aaec6d2b609305c90ba7` |
| `Erdos625/Foundation.lean` | `15ee3831ea8a4ca2d487379ea94f8929a0d7ceefb89aed45c4f3fa60f77d0a00` |
| `Erdos625/Section15FinalInstantiation.lean` | `74dc1249a29236501ccafc056f515491d572c35384a5d295f07f67023a93ca43` |
| `Erdos625/AxiomAudit.lean` | `6d5093828ffc03129d32373d259267e0e94c9396795fa66dc219e9b8fef62041` |
| `lakefile.toml` | `618799b4648a3fed6f033e9c5a4239fbffc4a769452e26362f5a2e5087cf02eb` |
| `lake-manifest.json` | `2d44c1423a5b32897c583a81237ccce01d4a8ab48d6a1d4ac85f7fc47c17e3d9` |
| `lean-toolchain` | `efac0b94923b2d8b6840cd35be9177ad0fc5ab2332f4f4311c98712cee92fdee` |

## 2. Integrity checks on `Erdos625SelfContained.lean` — all match

| Check | Expected (request) | Observed | Result |
| --- | --- | --- | --- |
| SHA-256 | `53060b95…33e837` | `53060b9563330f20a5f2133ffdf8f56e5a41eae6d0f772487193d9c54133e837` | MATCH |
| Lines | 89,528 | 89,528 (`wc -l`) | MATCH |
| Merged local modules | 480 | 480 (`BEGIN SOURCE MODULE:` markers, and generator `--check`) | MATCH |
| External imports | 86 | 86 (`^import ` lines, all distinct, all Mathlib) | MATCH |

Verbatim generator output (`logs/08_generator_check.*`, exit 0):

```
$ python3 scripts/generate_self_contained.py --check
checked Erdos625SelfContained.lean: 480 source modules, 86 external imports, 89528 lines, sha256=53060b9563330f20a5f2133ffdf8f56e5a41eae6d0f772487193d9c54133e837
```

The generator was run in `--check` mode only; `git status` confirmed it wrote
nothing.

Static scan (`static_scan.txt`): zero occurrences of `sorry`, `native_decide`, or
`implemented_by` in `Erdos625SelfContained.lean`, in `Erdos625.lean`, or anywhere
under `Erdos625/`; zero `axiom` declarations. (The token `axiom` occurs only
inside comments and `#print axioms` commands; `admit` occurs only inside the
English words "admits"/"admitting".)

**Documentation drift (informational, not a defect in the proof).** Two shipped
documents are stale relative to the pinned sources and were left untouched:

- `SELF_CONTAINED_BUILD.md` records 475 modules, 88,563 lines and hash
  `0f54ac26…ffac30`; the pinned file has 480 modules, 89,528 lines and hash
  `53060b95…33e837`.
- `README.md` displays the gap coefficient as `(log 2)^2 / 32 * log (200/153)`;
  the pinned `Erdos625.gapConstant` is `(log 2)^2 / 4 * log (200/153)` (§5).

## 3. Environment (recorded in `environment.txt`)

| Item | Value |
| --- | --- |
| OS / host | Linux x86_64 (gVisor sandbox), 8 cores, 64 GiB RAM |
| Toolchain pin | `leanprover/lean4:v4.31.0` |
| `lean --version` | Lean 4.31.0, x86_64-unknown-linux-gnu, commit `68218e876d2a38b1985b8590fff244a83c321783`, Release |
| `lake --version` | Lake 5.0.0-src+68218e8 (Lean 4.31.0) |
| `elan --version` | elan 4.2.3 |
| Mathlib requirement | `https://github.com/leanprover-community/mathlib4.git`, rev `v4.31.0` |
| Mathlib revision (manifest) | `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` |
| Other pinned deps | plausible `63045536…`, LeanSearchClient `c5d5b8fe…`, importGraph `5c7542ed…`, proofwidgets `24b0d9dc…`, aesop `e3cb2f74…`, Qq `f4632499…`, batteries `fa08db58…`, Cli `92564e57…` |
| Dependency cache | `lake exe cache get`, exit 0, 39 s (`logs/00_cache_get.*`) |

## 4. Command results

Each command's stdout, stderr, and exit code are preserved separately under
`logs/`. Machine-readable summary: `summary.tsv`; wall-clock timeline:
`timeline.txt`.

| # | Command | Exit | Duration | `error:` | `warning:` |
| --- | --- | --- | --- | --- | --- |
| 00 | `lake exe cache get` | **0** | 39 s | 0 | 0 |
| 01 | `lake build --wfail` | **0** | 1589 s | 0 | 0 |
| 02 | `lake env lean -DwarningAsError=true Erdos625/Section12ConcreteSignedFirstMoment.lean` | **0** | 31 s | 0 | 0 |
| 03 | `lake env lean -DwarningAsError=true Erdos625/Section12PartialDiagonalAssembly.lean` | **1** | 3 s | 1 | 0 |
| 04 | `lake env lean -DwarningAsError=true Erdos625/Section15FinalInstantiation.lean` | **0** | 16 s | 0 | 0 |
| 05 | `lake env lean -DwarningAsError=true Erdos625.lean` | **0** | 17 s | 0 | 0 |
| 06 | `lake env lean -DwarningAsError=true Erdos625/AxiomAudit.lean` | **0** | 17 s | 0 | 0 |
| 07 | `lake env lean -DwarningAsError=true Erdos625SelfContained.lean` | **0** | 845 s | 0 | 0 |

`lake build --wfail` completed with exit 0, so no Lean warning was emitted
anywhere in the default-target build; the 3,472 stdout lines are `info:`
diagnostics (axiom reports and 19 `Try this:` suggestions from tactic
`ring`/`ring_nf` fallbacks, which are informational and do not affect exit codes
under `-DwarningAsError=true`).

### 4.1 The one failure, reported unrepaired

Command 03 stdout, in full:

```
Erdos625/Section12PartialDiagonalAssembly.lean:1:0: error: object file
'/workspace/request-project/.lake/build/lib/lean/Erdos625/Section12ConcreteSignedFirstMoment.olean'
of module Erdos625.Section12ConcreteSignedFirstMoment does not exist
```

Diagnosis (no source change made):

- `Erdos625/Section12PartialDiagonalAssembly.lean` begins with
  `import Erdos625.Section12ConcreteSignedFirstMoment`.
- The Lake default target is the library root `Erdos625`, so `lake build --wfail`
  compiles exactly the transitive import closure of `Erdos625.lean` — 480
  modules. Four modules under `Erdos625/` are outside that closure and therefore
  never receive an `.olean`: `Section12ConcreteSignedFirstMoment`,
  `Section12PartialDiagonalAssembly`, `Section12CanonicalBareSkeletonAsymptotic`,
  and `Section13GlobalMidpointSeed` (the superseded "midpoint" chain).
- Command 02 elaborates `Section12ConcreteSignedFirstMoment.lean` but
  `lake env lean` does not emit an `.olean`, so command 03 still finds none.

Two supplementary runs (clearly marked as *not* part of the requested seven, and
requiring no source edit) characterise the failure:

| Log | Command | Exit |
| --- | --- | --- |
| `logs/09_supplementary_lake_build_module.*` | `lake build Erdos625.Section12PartialDiagonalAssembly` | 0 |
| `logs/10_supplementary_Section12PartialDiagonalAssembly_rerun.*` | requested command 03, re-run after the dependency `.olean` exists | 0 |

So the module itself compiles cleanly under `-DwarningAsError=true`; the failure
is purely that the requested command sequence does not produce the `.olean` its
import needs. This module is *not* in the dependency closure of the final
theorem.

## 5. `Foundation.gapConstant` is the exact one-quarter constant

`Erdos625/Foundation.lean`:

```lean
noncomputable def gapConstant : ℝ :=
  (Real.log 2) ^ 2 / 4 * Real.log (200 / 153 : ℝ)
```

Kernel-level confirmation against the built library
(`logs/11_supplementary_gapconstant_check.*`, exit 0 under
`-DwarningAsError=true`), where both `example`s were accepted:

```lean
example : Erdos625.gapConstant = (Real.log 2) ^ 2 / 4 * Real.log (200 / 153 : ℝ) := rfl
example : 4 * Erdos625.gapConstant = (Real.log 2) ^ 2 * Real.log (200 / 153 : ℝ) := by
  unfold Erdos625.gapConstant; ring
```

```
def Erdos625.gapConstant : ℝ :=
Real.log 2 ^ 2 / 4 * Real.log (200 / 153)
```

The denominator is exactly `4` — the one-quarter constant — with no rounding,
no auxiliary slack factor, and no `32`. Related printed definitions
(`logs/12`, `logs/13`):

```
def Erdos625.q : ℝ := Real.log 2
def Erdos625.gapScale : ℕ → ℝ := fun n => Erdos625.gapConstant * ↑n / Real.log ↑n ^ 3
def Erdos625.baseScale : ℕ → ℝ := fun n => ↑n / Real.log ↑n ^ 3
def Erdos625.gapEvent : (n : ℕ) → Set (Erdos625.LabeledGraph n) :=
  fun n => {G | Erdos625.gapScale n ≤ ↑(Erdos625.chromaticNumberNat G) - ↑(Erdos625.cochromaticNumber G)}
def Erdos625.gapProbability : ℕ → ENNReal := fun n => (Erdos625.randomGraphMeasure n) (Erdos625.gapEvent n)
def Erdos625.Erdos625Statement : Prop := Filter.Tendsto Erdos625.gapProbability Filter.atTop (nhds 1)
def Erdos625.randomGraphMeasure : (n : ℕ) → MeasureTheory.Measure (Erdos625.LabeledGraph n) :=
  fun n => SimpleGraph.binomialRandom (Fin n) Erdos625.halfProbability
```

So the theorem asserts that for `G(n,1/2)` the probability of
`χ − z ≥ ((log 2)^2 / 4 · log(200/153)) · n / (log n)^3` tends to 1 along all of `ℕ`.

## 6. The final theorem uses the fixed-offset seed/root chain

`Erdos625/Section15FinalInstantiation.lean` (verbatim proof body):

```lean
theorem erdos625 : Erdos625Statement := by
  obtain ⟨Lambda, hLambdaNonneg, hLambdaSmall, hSeed⟩ :=
    exists_phaseCochromaticFixedOffset_real_seed
  refine erdos625Statement_of_uniform_seed_and_root
    phaseChromaticLowerIndex phaseCochromaticFixedOffsetIndex
    Lambda fixedOffsetRoundingBudget
    hLambdaNonneg hLambdaSmall hSeed
    randomGraphMeasure_chromaticNumberAtMost_phaseChromaticLowerIndex_tendsto_zero
    fixedOffset_rounding_budget_spec.1 ?_
  obtain ⟨c, hc, hgap⟩ :=
    exists_eventually_concrete_phase_fixedOffset_root_gap
  refine ⟨c, ?_, hgap⟩
  simpa only [gapConstant, q] using hc
```

Every quantitative input is a *fixed-offset* declaration:

- seed: `exists_phaseCochromaticFixedOffset_real_seed`, supplying
  `exp (−Λ n) ≤ ℙ[CoColorable G (phaseCochromaticFixedOffsetIndex n)]` eventually,
  with `Λ = o(amplificationBase)`;
- cochromatic index: `phaseCochromaticFixedOffsetIndex`;
- rounding budget: `fixedOffsetRoundingBudget`, with `fixedOffset_rounding_budget_spec`;
- root corridor: `exists_eventually_concrete_phase_fixedOffset_root_gap`, giving
  `c > q^2/4 · log(200/153) = gapConstant` and eventually
  `(c − fixedOffsetRoundingBudget n) · baseScale n ≤ phaseChromaticLowerIndex n − phaseCochromaticFixedOffsetIndex n`;
- chromatic tail: `randomGraphMeasure_chromaticNumberAtMost_phaseChromaticLowerIndex_tendsto_zero`;
- combining lemma: `erdos625Statement_of_uniform_seed_and_root`.

No hypothesis is left open (`Erdos625Statement` is closed, with no parameters),
and the superseded midpoint chain (`Section13GlobalMidpointSeed`,
`Section12PartialDiagonalAssembly`, `Section12ConcreteSignedFirstMoment`,
`Section12CanonicalBareSkeletonAsymptotic`) is not imported by `Erdos625.lean`,
so it lies outside the dependency closure of `erdos625` — independently
corroborated by §4.1, where those four modules had no `.olean` after the full
default-target build.

Full signatures of the chain declarations are preserved in
`logs/12_supplementary_statement_check.stdout.log`.

## 7. Axiom closure

Automated scan of every `depends on axioms: [...]` block in all preserved logs
(`axiom_scan.txt`, multi-line blocks reassembled):

| Log | axiom reports | distinct axioms | disallowed |
| --- | --- | --- | --- |
| `01_lake_build_wfail` | 1682 | `propext`, `Classical.choice`, `Quot.sound` | none |
| `02_Section12ConcreteSignedFirstMoment` | 2 | same | none |
| `04_Section15FinalInstantiation` | 1 | same | none |
| `06_AxiomAudit` | 1003 | same | none |
| `07_Erdos625SelfContained` | 1682 | same | none |

No `sorryAx`, no `Lean.ofReduceBool`, no `Lean.trustCompiler`, no project axiom
appears anywhere. `Erdos625/AxiomAudit.lean` issues 1005 `#print axioms` commands,
the last being `#print axioms Erdos625.erdos625`.

The final theorem, printed identically in the modular build, in the standalone
`Section15FinalInstantiation` run, in the axiom audit, and in the one-file
self-contained run:

```
'Erdos625.erdos625' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This is **exactly** `propext`, `Classical.choice`, `Quot.sound`.

## 8. Files preserved in this directory

```
AUDIT_REPORT.md                  this report
README.md                        directory index and reproduction instructions
SHA256SUMS-all-tracked.txt       SHA-256 of all 499 tracked files, pre-run
SHA256SUMS-logs.txt              SHA-256 of every preserved log (immutability seal)
environment.txt                  toolchain, versions, manifest, host
run_replay.sh                    the exact driver used
summary.tsv                      command / exit code / duration
timeline.txt                     UTC begin/end stamps
static_scan.txt                  sorry / axiom / native_decide scan
axiom_scan.txt                   parsed axiom closure scan over all logs
GapConstantCheck.lean            supplementary kernel check of gapConstant
StatementCheck.lean, QCheck.lean supplementary printouts of the statement chain
logs/NN_*.stdout.log             raw stdout, one file per command
logs/NN_*.stderr.log             raw stderr, one file per command
logs/NN_*.exit-code.txt          raw exit code, one file per command
```

Logs `00`–`07` are the seven requested commands plus the cache fetch, in the
requested order. Logs `08`–`13` are supplementary checks, explicitly labelled as
such. All log files are stored read-only and sealed by `SHA256SUMS-logs.txt`.
