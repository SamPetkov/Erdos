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
