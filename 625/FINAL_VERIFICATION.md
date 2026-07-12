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
subsequent author line `Samuil Petkov & ChatGPT 5.6` and a non-mathematical
provenance sentence recording the completed historical-source audit; its
theorem and proof text are unchanged.

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
equations, the repaired two-line display (7.12), residual attachments, and the
final provenance note.  The rebuilt title page displays `Samuil Petkov &
ChatGPT 5.6`, and the embedded PDF Author field contains the same attribution.
Text extraction found no blank page, replacement
character, or `??` marker and confirmed every lemma title, Proposition 9.2,
the main constant, and the final section.

## Final SHA-256 identifiers

Paths below are relative to the `625/` directory.

```text
A0AAC63A6C1B470C76A389753140953E40D6A8B8CB6625DC9C6203A6477B336D  proofs/COMPLETE_PROOF_SELF_CONTAINED.md
42A39BC3A7D922B74EC3501EF233F93711F9C2769FE602EDA70E145220B923D3  proofs/COMPLETE_PROOF_DRAFT.md
CC17BE8A3196258FF6BFAC6FAD154EF7FA3D7EC7CE32CB29C4384C0397028213  audits/FULL_PROOF_AUDIT_1.md
2B9D96CBB560FD0674978B3111E1DF22A511412CEC42FDDDF2BE099F4E31125E  audits/FULL_PROOF_AUDIT_2.md
F7724290612866BD6D6A2105C95202C6C943C4CA93574708F980AFB0D087AE6E  audits/FULL_PROOF_AUDIT_3.md
110549CEDC8056BB7DE57D43789CA81D3FD48BCF9D45ADD697141117166E632E  audits/FULL_PROOF_AUDIT_4.md
088C2E4C9B45F5BC806842C68CCF94A9CAE477C876ABCB7B74A65B79F1B77C2A  sources/SOURCE_LEDGER.md
E9E56C7559D8774BE83281854EC5DCEAA9D8961D3DB5BB7E8EE01B2C5ED1A2D2  experiments/alpha_minus_two_route.py
85C25A975D7F4EEBF7B262126358B9058A171043AA2F26DA369ED9C9D86EB0F9  experiments/dense_transport_scan.py
DF90D14FE86A8FF3B1B8E2165EB7FB554811CD58D86D9F2CC3C6C7573AA1E0C0  experiments/exact_chi_zeta.py
E0107A1FEB47F8D2CD2F742E509FDC1C5B3BE4C60811AF09FF927E1712B3185E  verification/erdos625_verification_report.md
FB45DFEC62CED7BC8AADAD42865DA989572DCDC2FECC5AEB41B5A21B454E1310  verification/erdos625_independent_checks.py
F7BDC5AD95A6C20B82E952A805162B0D6E9A69D8C88BEABD3B57D07B6B69EE3D  output/tex/COMPLETE_PROOF_SELF_CONTAINED.tex
9CAC00FB7654E9B2E452D27C447984536651380DCC263F83443B7F943A4030EC  output/pdf/COMPLETE_PROOF_SELF_CONTAINED.pdf
9CAC00FB7654E9B2E452D27C447984536651380DCC263F83443B7F943A4030EC  COMPLETE_PROOF_SELF_CONTAINED.pdf
F5A3CE99990EE68DC3E91456BD0755990ECFD9C992547EEB346DF6EBF9632AAB  assets/erdos625-preview.png
```

## Historical-source completion

On 2026-07-12 the user supplied the four originals previously unavailable
through public or institutional retrieval: Erdős--Gimbel (1993), Gimbel
(2016), Bollobás (1988), and Janson--Łuczak--Ruciński (2000).  All four were
checked directly; the book scan, which has no usable text layer, was inspected
through rendered pages.  Filenames, SHA-256 identifiers, exact pages, theorem
statements, and quantifiers are recorded in
`sources/HISTORICAL_SOURCE_AUDIT.md` and `sources/SOURCE_LEDGER.md`.

The originals confirm the historical problem statement, its
a.a.s./with-high-probability formulation, and the standard dense-random-graph
chromatic asymptotic.  They do not alter the candidate theorem, its explicit
constant, or any proof step.
The copyrighted source PDFs remain local and are intentionally excluded from
the repository and release archives.  This clears the requested source-access
condition; it does not constitute external peer review, publication, priority
verification, or community acceptance.
