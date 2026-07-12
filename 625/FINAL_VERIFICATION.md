# Final internal verification record

Date: 2026-07-12.

## Mathematical audit gates

- `audits/FULL_PROOF_AUDIT_1.md`: PASS.
- `audits/FULL_PROOF_AUDIT_2.md`: PASS.
- `audits/FULL_PROOF_AUDIT_3.md`: PASS.
- `audits/FULL_PROOF_AUDIT_4.md`: PASS.

Each audit independently reconstructed the complete proof chain.  The fourth
audit was started without the surrounding research conversation and included
a separate finite-`n` optimizer/diagonal sub-audit.  These are internal
checks, not external peer review.

## Additional user-supplied verification

The report in `verification/erdos625_verification_report.md` gives the exact
verdict **Provisional internal verification: PASS** and reports no blocking
mathematical error.  The supplied manuscript copy had SHA-256
`53B2ADCCD64133991F3DCDCAA9F8E8820F38A12C982CC5735F96568DD014A190`,
byte-for-byte identical to the canonical proof at the time of review.  The
current canonical manuscript differs from that reviewed copy only by the
subsequent author line `Samuil Petkov & ChatGPT 5.6` and non-mathematical
citation, bibliography, and provenance material; its theorem and proof text
are unchanged.

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
176 opening and 176 closing display delimiters and 166 unique tags; scans for
tabs, mojibake, and the known malformed-TeX patterns were clean.

## Publication artifact checks

Pandoc 3.9.0.2 generated the LF-normalized standalone TeX manuscript from the
canonical Markdown source.  Its presentation filter places all 12 lemma
statements in blue breakable boxes and Proposition 9.2 in a green box while
leaving proofs in normal page flow.  Tectonic 0.16.9 compiled it successfully
to a 25-page A4 PDF.  The final compile had no overfull boxes, missing glyphs,
or fatal errors; one underfull-box warning remains in the final provenance
filename list and is cosmetic.

All 25 pages were rendered to PNG.  Pages 1, 2, 3, 5, 8, 11, 13, 16, 20, 22,
23, and 25 were visually inspected, covering the title and contents, abstract
and main bound, short and long lemma boxes, green proposition box, dense
equations, the repaired two-line display (7.12), residual attachments, the
in-text citations, and the final reference list.  The rebuilt title page
displays `Samuil Petkov & ChatGPT 5.6`, and the embedded PDF Author field
contains the same attribution.
Text extraction found no blank page, replacement
character, or `??` marker and confirmed every lemma title, Proposition 9.2,
the main constant, all six references, five external reference links, and the
final section.

## Final SHA-256 identifiers

Paths below are relative to the `625/` directory.

```text
4B9815B42F90E7F7A4044D64FB76A19AEBF4C296D6119A6AFECB73BFFB329164  proofs/COMPLETE_PROOF_SELF_CONTAINED.md
42A39BC3A7D922B74EC3501EF233F93711F9C2769FE602EDA70E145220B923D3  proofs/COMPLETE_PROOF_DRAFT.md
CC17BE8A3196258FF6BFAC6FAD154EF7FA3D7EC7CE32CB29C4384C0397028213  audits/FULL_PROOF_AUDIT_1.md
2B9D96CBB560FD0674978B3111E1DF22A511412CEC42FDDDF2BE099F4E31125E  audits/FULL_PROOF_AUDIT_2.md
F7724290612866BD6D6A2105C95202C6C943C4CA93574708F980AFB0D087AE6E  audits/FULL_PROOF_AUDIT_3.md
110549CEDC8056BB7DE57D43789CA81D3FD48BCF9D45ADD697141117166E632E  audits/FULL_PROOF_AUDIT_4.md
088C2E4C9B45F5BC806842C68CCF94A9CAE477C876ABCB7B74A65B79F1B77C2A  sources/SOURCE_LEDGER.md
D30987F28BF20556A633D0A78A10FFA240BC4977FF53E01A31FE08D27B396A94  sources/ERDOS625_REFERENCES.bib
E9E56C7559D8774BE83281854EC5DCEAA9D8961D3DB5BB7E8EE01B2C5ED1A2D2  experiments/alpha_minus_two_route.py
85C25A975D7F4EEBF7B262126358B9058A171043AA2F26DA369ED9C9D86EB0F9  experiments/dense_transport_scan.py
DF90D14FE86A8FF3B1B8E2165EB7FB554811CD58D86D9F2CC3C6C7573AA1E0C0  experiments/exact_chi_zeta.py
E0107A1FEB47F8D2CD2F742E509FDC1C5B3BE4C60811AF09FF927E1712B3185E  verification/erdos625_verification_report.md
FB45DFEC62CED7BC8AADAD42865DA989572DCDC2FECC5AEB41B5A21B454E1310  verification/erdos625_independent_checks.py
10B846C6B956B673AE9B7BBCF54766EC032F8AE50CD7BE20FE5CC0EE73C130D2  output/tex/COMPLETE_PROOF_SELF_CONTAINED.tex
5A832F3C41C8BD780743ABD28864516CCCD3DAA1904650C9C769D5CCBF7C4CFB  output/pdf/COMPLETE_PROOF_SELF_CONTAINED.pdf
5A832F3C41C8BD780743ABD28864516CCCD3DAA1904650C9C769D5CCBF7C4CFB  COMPLETE_PROOF_SELF_CONTAINED.pdf
F5A3CE99990EE68DC3E91456BD0755990ECFD9C992547EEB346DF6EBF9632AAB  assets/erdos625-preview.png
```
