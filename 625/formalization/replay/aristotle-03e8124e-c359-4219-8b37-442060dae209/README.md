# Aristotle replay of the sharp Erdős 625 formalization

This directory preserves the independent clean-environment replay of the exact
Lean source committed at
`824e4b609466d2e26b216a76ecf103184dac2663`.

## Provenance

- Aristotle project: `03e8124e-c359-4219-8b37-442060dae209`
- Aristotle task: `158be658-ab0c-4c17-8934-803da696dc86`
- Request URL:
  <https://aristotle.harmonic.fun/dashboard/requests/03e8124e-c359-4219-8b37-442060dae209>
- Replay interval: 2026-08-30 18:27:25--19:13:38 UTC
- Raw download SHA-256:
  `7f51ff2ba8891be9c1866e7dd9a64a39ddd7db5a3b46fbe5005a736bcfa4cf3a`
- Standalone SHA-256:
  `53060b9563330f20a5f2133ffdf8f56e5a41eae6d0f772487193d9c54133e837`
- Standalone closure: 480 local modules, 86 external imports, 89,528 lines
- Toolchain: Lean 4.31.0; Mathlib revision
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`

Aristotle receives a squashed upload rather than the repository's Git history.
The requested source commit is therefore identified by its content: after the
download, all 485 Lean files in the cloud copy were compared with commit
`824e4b609466d2e26b216a76ecf103184dac2663` and matched byte-for-byte.

## Result

The exact submitted Lean sources pass the release checks:

- `lake build --wfail`: exit 0 (9,038 jobs in the default-target, final-import-
  closure replay; the release transcript records 1,589 seconds);
- deterministic standalone generator check: exit 0;
- final-instantiation module, project root, and axiom audit under
  `-DwarningAsError=true`: exit 0;
- `Erdos625SelfContained.lean` under `-DwarningAsError=true`: exit 0
  after 845 seconds;
- `Erdos625.erdos625` uses exactly `propext`, `Classical.choice`, and
  `Quot.sound`;
- the formal constant is
  `((log 2)^2 / 4) * log(200/153)`, and the final theorem uses the
  fixed-offset seed/root chain.

One requested direct compilation of the superseded, out-of-closure module
`Section12PartialDiagonalAssembly.lean` initially exited 1 because its imported
dependency had no `.olean`: the default Lake target does not build that retired
chain, and running `lean` on its predecessor does not emit an object file.
Building the named Lake target and rerunning the identical warnings-as-errors
command both exited 0. This invocation-order artifact is preserved in full in
the logs; it is not a source or theorem failure.

## Artifact caveat

No Lean source was changed by the replay. Aristotle did, however, prepend a
nine-line attribution notice to its returned copy of the root `README.md` and
added `ARISTOTLE_SUMMARY.md`; its returned archive also omits the repository's
root `.gitignore`. Consequently, the cloud summary's blanket claim that no
supplied file was edited is too broad. The raw archive is retained unchanged
for provenance, while the public source identity is established by the byte
comparison of all Lean files and the standalone checksum above. The returned
logs are hash-sealed, but their archive modes are `0644`; “read-only” in the
verbatim cloud text is therefore not a filesystem-permission claim.

## Contents

- `aristotle-result.tar.gz`: the byte-identical Aristotle download;
- `cloud-output/ARISTOTLE_SUMMARY.md`: the verbatim cloud summary;
- `cloud-output/release-replay-824e4b6/`: the verbatim audit report, exact
  driver, environment record, command timelines, available stdout, stderr, and
  exit-code records, static scans, the primary-log axiom scan, and cloud
  checksum seals;
- `SHA256SUMS`: local checksums of every preserved verbatim artifact.

The raw logs are evidence, not an additional trust boundary: the formal claims
rest on the Lean kernel and the exact source identified above.
