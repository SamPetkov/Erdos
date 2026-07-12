# Additional provisional verification

This directory preserves the user-supplied follow-up review of the proposed
Problem 625 proof and its separately written finite checker.

## Status

The report's exact verdict is:

> **Provisional internal verification: PASS.**

It reports no blocking mathematical error and independently reconstructs the
main proof chain.  It also identifies Lemmas 3.1, 7.1, 8.3, and 9.1 as the
highest-priority targets for future formalization.

This is an additional internal review, not peer review, journal refereeing,
community acceptance, or machine verification.  The supplied files do not
embed a reviewer identity, professional credential, affiliation, signature,
tool/model identifier, commit ID, or license, so the repository does not
describe the report as external or professional verification.

## Files and provenance

- [`erdos625_verification_report.md`](erdos625_verification_report.md) - the
  complete report as supplied, SHA-256
  `E0107A1FEB47F8D2CD2F742E509FDC1C5B3BE4C60811AF09FF927E1712B3185E`.
- [`erdos625_independent_checks.py`](erdos625_independent_checks.py) - the
  independent checker as supplied, SHA-256
  `FB45DFEC62CED7BC8AADAD42865DA989572DCDC2FECC5AEB41B5A21B454E1310`.
- [`INDEPENDENT_CHECK_RESULTS.txt`](INDEPENDENT_CHECK_RESULTS.txt) - output
  reproduced locally on 2026-07-12.

The report reviewed manuscript SHA-256
`53B2ADCCD64133991F3DCDCAA9F8E8820F38A12C982CC5735F96568DD014A190`,
which was byte-for-byte identical to the canonical manuscript at the time of
review.  The current `../proofs/COMPLETE_PROOF_SELF_CONTAINED.md` differs only
by a subsequently added author line; the reviewed theorem and proof text are
unchanged.

The report refers to an earlier archive with SHA-256
`037F9A32A1C0D32C996BFD64222F65D121AC14871EFAB92826DD16DEF810C783`
and correctly notes that its source-ledger paths were flattened.  The current
repository and rebuilt ZIP use a top-level `625/` directory with
`625/sources/`, so that packaging defect is already fixed.

Paths and `sandbox:/mnt/data` links embedded in the supplied report refer to
the review environment and reviewed archive root; they are preserved as
received and are not repository links.

## Reproduce the finite checks

From the repository root:

```powershell
python 625/verification/erdos625_independent_checks.py
```

The checker uses only the Python standard library and was independently
replayed under Python 3.14.3 with exit code 0 in approximately 4.7 seconds.
Use Python 3.9 or newer.  Do **not** run it with `python -O`, `python -OO`, or
`PYTHONOPTIMIZE`, because seven assertions implement the checks and Python's
optimization flags disable them.

The checks are finite diagnostics.  Four groups use exact integer or
`Fraction` arithmetic; the Lemma 8.1 transport group uses floating-point
square roots with tolerance `1e-11`.  They verify identities and small
instances but do not constitute formal verification and do not prove the
asymptotic theorem.
