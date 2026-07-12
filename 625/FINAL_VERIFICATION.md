# Final internal verification record

Initial record: 2026-07-12.  Adversarial proof-audit update: 2026-07-13.

## Mathematical audit gates

- `audits/FULL_PROOF_AUDIT_1.md`: PASS.
- `audits/FULL_PROOF_AUDIT_2.md`: PASS.
- `audits/FULL_PROOF_AUDIT_3.md`: PASS.
- `audits/FULL_PROOF_AUDIT_4.md`: PASS.

Each audit independently reconstructed the complete proof chain.  The fourth
audit was started without the surrounding research conversation and included
a separate finite-`n` optimizer/diagonal sub-audit.  These are internal
checks, not external peer review.

## 2026-07-13 adversarial leap audit and repairs

The fresh independent review recorded in
`audits/ADVERSARIAL_LEAP_AUDIT_2026-07-13.md` did not accept the earlier PASS
verdicts as evidence.  It found three substantive written-proof defects:

1. Lemma 3.1 localized its derivative near ordinary roots, while Section 5
   used that estimate to localize the signed root, creating a circular step.
2. Lemma 8.3 did not display the conditioning/product identity that promotes
   its per-cell and conditional estimates to the sum of every high skeleton.
3. Lemma 9.1 claimed a two-sided logarithmic asymptotic although its proof and
   downstream use require only a one-sided upper bound.

The canonical manuscript now contains a uniform root-corridor lemma and
optimizer convergence, the explicit global high-skeleton expansion
(8.25a)--(8.29b), and the correct one-sided residual statement.  It also makes
the partial-diagonal domains, integer-rounding signs, greedy leftover
recurrence, growing deterministic amplification parameter, and final error
sequence explicit.  Three independent route-specific regression reviews
returned PASS on the patched passages.  No repair changes the theorem,
constant, four class sizes, or full-sequence probability quantifier.

## Additional user-supplied verification

The report in `verification/erdos625_verification_report.md` gives the exact
verdict **Provisional internal verification: PASS** and reports no blocking
mathematical error.  The supplied manuscript copy had SHA-256
`53B2ADCCD64133991F3DCDCAA9F8E8820F38A12C982CC5735F96568DD014A190`,
byte-for-byte identical to the canonical proof at the time of review.  That
report applies to the manuscript version identified by its hash.  The current
canonical manuscript is newer: in addition to the author and citation
material, it contains the 2026-07-13 mathematical repairs listed above.  The
supplied report is preserved as provenance and supplementary internal
evidence, not represented as a review of the current bytes.

The supplied report's statement that the theorem answers Problem #625
positively is recorded as conditional on the correctness of this candidate
argument; it is not an externally established resolution.

The separately written standard-library checker was replayed under Python
3.14.3 with exit code 0; all five groups passed.  Four groups use exact
integer or rational arithmetic, while the Lemma 8.1 transport group uses
floating-point square roots with tolerance `1e-11`.  Its seven assertions
must be run without Python optimization.  These are finite diagnostics, not
a proof of the asymptotic theorem or machine verification.

No reviewer identity, credential, affiliation, signature, tool/model, commit
ID, or license is embedded in the supplied files.  Accordingly, the report is
recorded as additional user-supplied internal review, not external or
professional verification.

## Reproducibility checks

The following commands completed successfully.  From the repository root,
run:

```powershell
python 625/experiments/alpha_minus_two_route.py
python 625/experiments/dense_transport_scan.py
python 625/experiments/exact_chi_zeta.py --self-test --exhaustive-n 5
$py = rg --files 625/experiments -g '*.py'
foreach ($f in $py) { python -m py_compile $f }
```

The exact solver reported:

```text
SELF-TEST PASS: 1099 labelled graphs (all n=1..5) plus n=0
```

All seven experiment scripts compiled.  The two asymptotic diagnostic scripts
completed without assertion or arithmetic failure.  Finite computations are
diagnostic only and are not used as proof.

For the self-contained proof, concise proof, five main component proofs, and
four full audits, a structural scan found balanced display delimiters and no
duplicate equation tags.  The self-contained manuscript specifically has
187 opening and 187 closing display delimiters and 176 unique tags; scans for
tabs, mojibake, and the known malformed-TeX patterns were clean.

## Publication artifact checks

Pandoc 3.9.0.2 generated the LF-normalized standalone TeX manuscript from the
canonical Markdown source.  Its presentation filter places all 12 lemma
statements in blue breakable boxes and Proposition 9.2 in a green box while
leaving proofs in normal page flow.  Tectonic 0.16.9 compiled it successfully
to a 27-page A4 PDF.  The final compile had no overfull boxes, missing glyphs,
or fatal errors; one underfull-box warning remains in the final provenance
filename list and is cosmetic.

All 27 pages were rendered to PNG at 120 DPI.  Three nine-page contact sheets
and full-size pages 5, 19--21, and 24--27 were visually inspected, covering
the title and contents, abstract and main bound, short and long lemma boxes,
the repaired root corridor, global high-skeleton bridge, green proposition
box, residual attachments, amplification, final theorem, in-text citations,
and the reference list.  The rebuilt title page
displays `Samuil Petkov & ChatGPT 5.6`, and the embedded PDF Author field
contains the same attribution.
Text extraction found no blank page, replacement
character, or `??` marker and confirmed every lemma title, Proposition 9.2,
the main constant, all six references, five unique external reference links
in six PDF annotations, and the final section.

## Final SHA-256 identifiers

Paths below are relative to the `625/` directory.

```text
9EA27F617D95DAFA42991A3CAF2ACBF3A4E92CA16CA25D524D7B587954D95A83  proofs/COMPLETE_PROOF_SELF_CONTAINED.md
42A39BC3A7D922B74EC3501EF233F93711F9C2769FE602EDA70E145220B923D3  proofs/COMPLETE_PROOF_DRAFT.md
CC17BE8A3196258FF6BFAC6FAD154EF7FA3D7EC7CE32CB29C4384C0397028213  audits/FULL_PROOF_AUDIT_1.md
2B9D96CBB560FD0674978B3111E1DF22A511412CEC42FDDDF2BE099F4E31125E  audits/FULL_PROOF_AUDIT_2.md
F7724290612866BD6D6A2105C95202C6C943C4CA93574708F980AFB0D087AE6E  audits/FULL_PROOF_AUDIT_3.md
110549CEDC8056BB7DE57D43789CA81D3FD48BCF9D45ADD697141117166E632E  audits/FULL_PROOF_AUDIT_4.md
CA110DE66D62F2CABC1D84E08594D343FB3BD9C8DA844D1D6BFA68B626FBB8E8  audits/ADVERSARIAL_LEAP_AUDIT_2026-07-13.md
088C2E4C9B45F5BC806842C68CCF94A9CAE477C876ABCB7B74A65B79F1B77C2A  sources/SOURCE_LEDGER.md
D30987F28BF20556A633D0A78A10FFA240BC4977FF53E01A31FE08D27B396A94  sources/ERDOS625_REFERENCES.bib
E9E56C7559D8774BE83281854EC5DCEAA9D8961D3DB5BB7E8EE01B2C5ED1A2D2  experiments/alpha_minus_two_route.py
85C25A975D7F4EEBF7B262126358B9058A171043AA2F26DA369ED9C9D86EB0F9  experiments/dense_transport_scan.py
DF90D14FE86A8FF3B1B8E2165EB7FB554811CD58D86D9F2CC3C6C7573AA1E0C0  experiments/exact_chi_zeta.py
E0107A1FEB47F8D2CD2F742E509FDC1C5B3BE4C60811AF09FF927E1712B3185E  verification/erdos625_verification_report.md
FB45DFEC62CED7BC8AADAD42865DA989572DCDC2FECC5AEB41B5A21B454E1310  verification/erdos625_independent_checks.py
AAF38D8134015EC9AEAD6FEA4916F618C4479F6601E1EB34F68A5134B0E1B82A  output/tex/COMPLETE_PROOF_SELF_CONTAINED.tex
2ACD9BA34A7104976C65A007DF5132668605AFACA7407516B290545CB0634357  output/pdf/COMPLETE_PROOF_SELF_CONTAINED.pdf
2ACD9BA34A7104976C65A007DF5132668605AFACA7407516B290545CB0634357  COMPLETE_PROOF_SELF_CONTAINED.pdf
F5A3CE99990EE68DC3E91456BD0755990ECFD9C992547EEB346DF6EBF9632AAB  assets/erdos625-preview.png
```
