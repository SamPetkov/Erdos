# Optional Aristotle workflow

Aristotle is an optional proof-search assistant for this formalization. Its output
is never accepted on the strength of the service response alone. Every returned
Lean file must pass the same local source, build, and axiom gates as handwritten
code before it can be imported.

## Local installation

The signed-in official installation documentation was read on 2026-07-13. It
recommends `uv tool install aristotlelib`; `pip install aristotlelib` is also an
officially supported route. The Windows workstation was checked with the
official PyPI package `aristotlelib` version 2.1.0. The executable is installed
under the current Python 3.14 user installation, and that installation's
`Scripts` directory has been added to the Windows user `PATH`. A newly opened
terminal should report:

```powershell
aristotle --version
```

Expected output:

```text
aristotlelib 2.1.0
```

## Authentication without leaking the key

Create an API key from the official dashboard at
<https://aristotle.harmonic.fun/dashboard>. Do not paste the key into a Lean
file, this repository, a command-line `--api-key` argument, or a chat message.
For a single PowerShell session, read it without putting the value in shell
history:

```powershell
$secureKey = Read-Host 'Aristotle API key' -AsSecureString
$keyPointer = [Runtime.InteropServices.Marshal]::SecureStringToBSTR($secureKey)
try {
  $env:ARISTOTLE_API_KEY =
    [Runtime.InteropServices.Marshal]::PtrToStringBSTR($keyPointer)
} finally {
  [Runtime.InteropServices.Marshal]::ZeroFreeBSTR($keyPointer)
}
aristotle list --limit 1
```

The environment variable lasts only for that terminal session. Local `.env`
files and `.aristotle/` results are ignored by Git as an additional safeguard.

## Toolchain compatibility

The official service currently runs:

```text
Lean:    leanprover/lean4:v4.28.0
Mathlib: 8f9d9cff6bd728b17a24e163c9402775d9e6a365
```

The accepted Erdős-625 project is deliberately on Lean/Mathlib `v4.31.0`.
Changing the accepted project backward merely for the service would weaken the
reproducible local baseline. Instead, difficult obligations are copied into a
minimal ignored `.aristotle/` project pinned to the service versions. Any proof
returned there is ported back to `v4.31.0` and rechecked locally.

## Audited use on this project

Submit one isolated proof obligation at a time from a reviewed, minimal project
copy. A submission transmits that project copy and the prompt to Harmonic, so it
must be intentional. A typical invocation is:

```powershell
aristotle submit `
  'Prove the named Lean theorem without changing its statement. Do not use sorry, admit, new axioms, unsafe declarations, native_decide, or theorem-strengthening assumptions. Return the smallest checked patch.' `
  --project-dir C:\path\to\reviewed-minimal-project `
  --wait `
  --destination .aristotle\result.zip
```

Returned code is quarantined under `.aristotle/` and then reviewed against a
pinned hash. Acceptance requires all of the following:

1. The target theorem and all quantifiers are unchanged.
2. No forbidden proof placeholders, project axioms, or unsafe escape hatches.
3. Direct compilation with `-DwarningAsError=true`.
4. `lake build --wfail` for the full project.
5. Representative `#print axioms` output no stronger than the standard
   Mathlib baseline already recorded for this repository.
6. Independent semantic review of the mathematical argument and its dependency
   boundary.

Aristotle may accelerate local obligations, but the final acceptance authority
remains the Lean kernel plus the repository's explicit audits.

### First isolated run (2026-07-13)

Project `e6ad9e3b-6c9a-4a36-a714-eeb515713209`, task
`a9fa45d2-5a1e-4982-8170-46444b591980`, contained only the three missing
inverse/equivalence proofs for the vertex-block encoding. Aristotle returned
proofs of `blocksToGraph_adj_lower`, `graphToBlocks_blocksToGraph`, and
`blocksToGraph_graphToBlocks`, and its fixed-version build reported only
`propext`, `Classical.choice`, and `Quot.sound` in `#print axioms`.

The returned archive is quarantined in the ignored `.aristotle/` directory. It
was not copied into the accepted source: its compact `aesop`/`grind` proof of
the final inverse did not finish within a 184-second direct Lean 4.31 replay.
The accepted module instead retains the more explicit local proofs, which
compile under Lean 4.31 with warnings treated as errors. The Aristotle result
therefore supplies an independent proof-search cross-check, not an accepted
dependency. The temporary one-run API key was revoked immediately after the
archive was downloaded, and its value was cleared from process memory.

The service documentation also describes a generated `negate_state` helper that
contains `admit` internally when reporting a counterexample. That output is
useful diagnostically but is never admissible here: the repository gate scans
the returned source and rejects the helper or any theorem depending on it.

### Second isolated run (2026-07-13)

Project `b6f44db1-21cc-4722-9d59-dc84a2be7719`, task
`0baa5e00-77a4-4076-bf4e-81d425ef7e75`, tested the finite maximum argument
behind the largest induced cocolourable subgraph.  In an abstract finite-set
model, Aristotle proved the two intended obligations: every feasible set has
cardinality at most the capacity, and the capacity can change by at most one
after deleting a single element.  The service-side Lean 4.28 build passed and
reported only the standard `propext`, `Classical.choice`, and `Quot.sound`
axioms.

The result was downloaded entirely through the CLI to the local archive
`C:\Users\petko\aristotle-capacity-result.tar.gz` and extracted only inside the
ignored `.aristotle/` quarantine.  Review identified one useful portability
detail: the nonemptiness proof for the image defining the maximum must use
`Finset.Nonempty.image` explicitly under Lean 4.31, rather than ambiguous dot
notation.  That elaboration fix was ported into the accepted definition; the
graph-specific deletion, event, variance, measure-transport, and concentration
proofs were written and checked locally.  The temporary run key was revoked
after download and cleared from process memory.

Completed results can be inspected without the website:

```powershell
aristotle list --limit 10
aristotle tasks b6f44db1-21cc-4722-9d59-dc84a2be7719 --limit 10
aristotle download b6f44db1-21cc-4722-9d59-dc84a2be7719 `
  --destination aristotle-capacity-result.tar.gz
```

The dashboard is needed for API-key creation and revocation, but not for local
status inspection or result download.

### Sections VIII--XI waves (2026-07-14--15)

Later isolated waves supplied redundant candidates for deterministic atoms in
Sections 8--11.  Accepted local Lean 4.31 reconstructions, not service output,
are authoritative; request identifiers and per-theorem status are recorded in
`SECTIONS_6_9_BREAKDOWN_2026-07-14.md` and
`SECTIONS_10_11_BREAKDOWN_2026-07-14.md`.

The exact full Lemma 9.1 project
`fe0c45b5-e074-4f9d-bd91-af93f2fed768` ended
`COMPLETE_WITH_ERRORS`.  One live `sorry` remains in `sum_fourpow_le`, and a
subsequent semantic audit showed that this raw configuration-matching
collision exponential-moment bound is false as stated: it discards the
residual cap/no-return event whose restriction is essential.  The returned
final theorem therefore depends on both `sorryAx` and a false helper and is
rejected; its archive is retained only in the ignored quarantine.

The subset-expansion follow-up
`857e6b3d-02cd-4400-bbd9-5bda925b3556` was canceled.  The
sequential-exposure follow-up
`5ee75c79-dee3-46d1-9a9c-15edd7c2900b` completed with a valid counterexample
to `sum_fourpow_le`, rather than a proof of the requested target.  Neither
follow-up proves Lemma 9.1.  A faithful proof retaining the cap/no-return event
and treating the manuscript's two residual-mass regimes remains open.

### Status reconciliation (2026-07-15)

This reconciliation supersedes older submission-time labels below; it does
not change any module-count, hash, or full-build metric.

- Work package D was already independently accepted.
- For work packages G, H, I, J, K, L, M, N, O, P, and Q, the exact returned
  theorem statements were independently audited, ported into tracked source,
  and replayed successfully in local Lean 4.31 warning-fatal builds.  This is
  acceptance of those atomic statements only.  The exact-scope/caveat columns
  in the wave tables remain controlling; in particular these leaves do not by
  themselves prove full Lemma 8.3, full Lemma 9.1, or complete Sections
  VIII--XI.
- Work package F's clean bounded continuation
  `a1b4fe23-5553-48b7-88db-20d2f75b0ef0` is accepted as the independently
  reviewed `Section8CanonicalLabelledWitness.lean`.  Its 198-line source has
  SHA-256
  `4F1FCAEE9EF845C16C05B9223D95C3FB135DCD0E840030F9A35DFDE4D0557E5F`,
  passed a warning-fatal Lean 4.31 build in about 304 seconds (about 286
  seconds for the module), passed aggregate integration, and reports only
  `propext`, `Classical.choice`, and `Quot.sound`.  The accepted theorem is
  only deterministic `∃!` identification for one fixed matching, not the
  probability of the global canonical event.
- The original A and B returns remain rejected by the repository's resource
  and source-policy gates.  Their bounded continuations are independently
  accepted: A `819e5c2f-ba0e-4b85-acc4-68018958acc2` in
  `Section9CappedFixedFExpansion.lean`, and B
  `aa66bdd6-3c5b-4259-b35b-15ff3c66acb7` in
  `Section9CyclePolymerBound.lean`.
- C `d433e6aa-0ba2-44e0-9519-3b1f897eb3e4` ended
  `COMPLETE_WITH_ERRORS` with the original target `sorry` still present and is
  rejected.  E `0be16581-1f1d-4781-a58c-2cb46e4d1bcf` is accepted in
  `Section9FiniteAnalyticEndpoint.lean` after strict local replay.

### Faithful Section IX wave (2026-07-15)

The false unrestricted collision-moment helper was not resubmitted.  Instead,
five independent service projects were prepared from the manuscript-faithful
dependency chain.  Every request skeleton was compiled locally with the
service's Lean 4.28.0/Mathlib revision and contained exactly one intentional
target `sorry` and no project axioms or unsafe escape hatches.  The source-only
payloads deliberately excluded the local 1.6 GB dependency cache.

| Work package | Service project | Status at submission |
|---|---|---:|
| fixed-`F` cap/no-return prescribed-demand expansion behind (9.10)--(9.12) | `fe520e24-b80f-406e-b4d0-3a842fca287e` | original rejected; bounded continuation `819e5c2f-ba0e-4b85-acc4-68018958acc2` passed strict Lean 4.28 and is accepted in `Section9CappedFixedFExpansion.lean` |
| recoverable even-subgraph decomposition and weighted polymer bound (9.15) | `25a033db-451f-4203-9593-fcb8b1f562d9` | original rejected; bounded continuation `aa66bdd6-3c5b-4259-b35b-15ff3c66acb7` passed strict Lean 4.28 and is accepted in `Section9CyclePolymerBound.lean` |
| matching-cycle cutting and one-time-mark weighted walk bound (9.17)--(9.18) | `d433e6aa-0ba2-44e0-9519-3b1f897eb3e4` | `COMPLETE_WITH_ERRORS`; rejected because the original target `sorry` remains |
| deterministic small-residual integrand bound from (9.20)--(9.22) | `29f7b05b-f22f-4266-bc04-795aa0cb709e` | `COMPLETE`; audited and ported |
| finite absolute-constant endpoint estimate for `lambda` and `q` in (9.7)--(9.9) | `0be16581-1f1d-4781-a58c-2cb46e4d1bcf` | `COMPLETE`; strict Lean 4.28 replay and accepted Lean 4.31 port `Section9FiniteAnalyticEndpoint.lean` |

The first request imports the literal locally proved joint prescribed-cell
bound rather than assuming an abstract probability inequality.  The cycle
requests require their decomposition and cycle-to-walk constructions inside
the target proofs; they do not hide those constructions in hypotheses.  The
analytic request quantifies an absolute constant instead of asserting a false
small finite constant.  A service completion will remain quarantined until the
returned statement, source, warning-fatal Lean 4.31 replay, axiom output, and
mathematical dependency boundary all pass local review.

The original polymer proof preserved the proposition but inserted both
`set_option maxHeartbeats 0` and `grind +suggestions`, so that source remains
quarantined.  Its bounded continuation passed strict Lean 4.28 after only the
unused-binder rename `hM` to `_hM`; the accepted Lean 4.31 port
`Section9CyclePolymerBound.lean` passed warning-fatally in 122.856 seconds with
the standard `propext`, `Classical.choice`, and `Quot.sound` axiom trio.  It is
a real-valued finite even-edge polymer bound and constructs a recoverable
edge-disjoint minimal-even decomposition.  It does not instantiate the actual
residual family or provide the `ENNReal` weight/kernel and cycle-to-walk bridge.

The bounded fixed-`F` continuation kept the theorem statement unchanged and
passed strict Lean 4.28 in about 67 seconds.  Its accepted Lean 4.31 port
`Section9CappedFixedFExpansion.lean` passed warning-fatally in 48.5 seconds,
with a clean trust scan and the same standard axiom trio.  The endpoint result
likewise passed strict Lean 4.28; its accepted Lean 4.31 port
`Section9FiniteAnalyticEndpoint.lean` passed warning-fatally in about 47
seconds with the standard trio.  It proves only the finite real analytic
endpoint bridge under its exact hypotheses, not the upstream random event.

The returned matching-cycle request C retains its original target `sorry` and
is rejected.  The separate local replacement
`Section9MatchingTraversalBridge.lean` is accepted after a 34.4-second
warning-fatal Lean 4.31 build (about 27 seconds for the module), clean trust
scan, an axiom audit reporting only `propext`, `Classical.choice`, and
`Quot.sound`, and aggregate integration.  Its stated scope is
only the relaxed finite matching-operator/geometric bridge; it does not
construct the positive residual kernel from `q` or an injective,
weight-preserving cycle-to-walk code.

The returned small-residual theorem preserved the exact statement, passed two
semantic audits and a warning-fatal Lean 4.28 replay, and was ported to the
accepted Lean 4.31 module `Section9SmallResidualDeterministic.lean`; its axiom
output is the standard trio.

### Second faithful wave (2026-07-15)

Twelve more isolated requests were checked under the service's exact
Lean/Mathlib revision and submitted as source-only payloads.  Each payload had
exactly one target `sorry`, no other placeholder or trust escape, and no local
cache, manifest, or binary artifact.  Two Section VIII targets are explicitly
intermediate identities: the labelled incidence is not yet the complete
configuration-model probability identity (8.3), and the distinguishable-cell
product expansion is not yet the unlabelled typed-skeleton bridge.

| Package | Service project | Status at submission |
|---|---|---:|
| canonical labelled high-demand witness uniqueness | `3a103aa6-bb8f-4ee4-840d-6a307fa13a1e` | original completed with suggestion-enabled automation; clean continuation `a1b4fe23-5553-48b7-88db-20d2f75b0ef0` audited and accepted as `Section8CanonicalLabelledWitness.lean` after warning-fatal Lean 4.31 replay and aggregate integration; exact scope is deterministic `∃!` for one fixed matching |
| normalized labelled-witness incidence algebra | `2521afcb-76cd-4887-b4d3-8d5dd2525bac` | `COMPLETE`; exact statement audited, ported, and warning-fatally accepted in Lean 4.31 |
| exact canonical cutoff-event identification | `3752e0d3-ded9-40a9-b921-13b86511dda7` | `COMPLETE`; exact statement audited, ported, and warning-fatally accepted in Lean 4.31 |
| distinguishable near-skeleton product expansion | `3bf1699a-829c-4a08-96db-46ec367e2f8e` | `COMPLETE`; exact statement audited, ported, and warning-fatally accepted in Lean 4.31 |
| capped local-reward telescoping (9.10)--(9.11) | `a59bc485-46ae-470d-bb47-8cc5112493ab` | `COMPLETE`; exact statement audited, ported, and warning-fatally accepted in Lean 4.31 |
| injective finite-family product/exponential bound | `76396761-3a66-4129-bbaf-ddea479a0ada` | `COMPLETE`; exact statement audited, ported, and warning-fatally accepted in Lean 4.31 |
| eventual traversal parameter `tau < 1/3` | `b19e923c-6617-463f-bfd3-d8dc4cf9ff54` | `COMPLETE`; exact statement audited, ported, and warning-fatally accepted in Lean 4.31 |
| uniform two-regime attachment error | `f1f67e1a-3aa0-4da4-931d-b6530804ed2f` | `COMPLETE`; exact statement audited, ported, and warning-fatally accepted in Lean 4.31 |
| quarter-cutoff union-bound decay | `e569e37b-3486-4909-b5dd-3ebbbbe64049` | `COMPLETE`; exact statement audited, ported, and warning-fatally accepted in Lean 4.31 |
| simultaneous deterministic greedy colouring | `78638bbc-5941-4275-9ea3-b0022cc640dc` | `COMPLETE`; exact statement audited, ported, and warning-fatally accepted in Lean 4.31 |
| amplification-error little-o assembly | `3fcd655d-a5cd-42b8-bcb0-85767126b3a7` | `COMPLETE`; exact statement audited, ported, and warning-fatally accepted in Lean 4.31 |
| moving-threshold to fixed-threshold tail | `20da6297-c83e-4800-8724-cc2551a31409` | `COMPLETE`; exact statement audited, ported, and warning-fatally accepted in Lean 4.31 |

The request IDs are provenance and scheduling records, not proof certificates.
Every completion remains quarantined until statement identity, trust scan,
warning-fatal v4.28 and v4.31 replay, axiom output, and semantic scope all pass.

### Endpoint, edge-law, and decomposition queue (2026-07-15)

Four later service completions have passed the repository gates at strictly
atomic scope:

| Isolated target | Service project | Accepted local authority | Limitation |
|---|---|---|---|
| endpoint-resolved positive-kernel row bound | `955531da-fb82-490e-a884-bdeaaa6984e9` | `Section9EndpointKernel.lean` | endpoint resolution and inherited geometric row norm only |
| explicit path/chain kernel summands | `cf3a9bd2-3191-4b6d-aeb1-f5973430458e` | `Section9ExplicitPathTerms.lean` | pointwise summand bounds only; no cycle encoding |
| degree-cap `q` row/column norm | `75de0fb8-61f2-4628-96e1-015df6a58424` | `Section9QDegreeBound.lean` | abstract norm estimate; concrete manuscript instantiation remains open |
| exact binomial edge-count singleton law | `f3ca6d6a-200a-42bc-810e-9799b721f7e7` | `Section10BinomialEdgeCount.lean` | finite graph law only; fixed-induced-set transport and universal event remain open |

The edge-law return changed the Mathlib revision; acceptance followed only
after replay and a compatibility repair on the repository's Lean 4.31
revision.  The two elementary seams in
`Section10CapacityLeftoverQuantitative.lean` and
`Section11ChromaticLowerTailBridge.lean` were proved locally and have no
service-completion provenance.

The source-only staging queue also contains finer Section VIII canonical-event
packages, the remaining Section IX covering-cycle and mixed-cycle encoder
packages, and the Section X sequence from fixed-subset quarter tails through
universal leftover colouring and amplification.  Each payload is kept small,
pinned to the service's Lean 4.28 environment, and contains one intentional
target hole; full targets may be submitted in parallel with decomposed leaves
when slots permit.  A failure is split into smaller faithful statements, while
a completion is downloaded, statement-audited, replayed, source-scanned,
axiom-audited, and scope-checked before integration.  Thus staged, queued, or
running packages are proposals, not accepted theorems, and they do not prove
Lemma 9.1, Proposition 9.2, Lemma 10.1, Lemma 10.2, or the final theorem.
