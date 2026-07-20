# Final internal verification record

## 2026-07-20 publication synchronization

The sole-author TeX, Markdown, bibliography, and PDF publication artifacts were
regenerated on 20 July 2026.  The manuscript and PDF metadata name **Samuil
Petkov** as the sole author; AI systems remain disclosed as assistance rather
than coauthors.  The current publication artifacts are verified by the
`arXiv artifact synchronization` workflow.  Historical hashes and audit verdicts
below remain scoped to the bytes and dates explicitly stated in their original
records.

Initial record: 2026-07-12.  Adversarial proof-audit update: 2026-07-13.
Publication and Lean-checkpoint refresh: 2026-07-14.

## Mathematical audit gates

- `audits/FULL_PROOF_AUDIT_1.md`: PASS on the 2026-07-12 reviewed bytes.
- `audits/FULL_PROOF_AUDIT_2.md`: PASS on the 2026-07-12 reviewed bytes.
- `audits/FULL_PROOF_AUDIT_3.md`: PASS on the 2026-07-12 reviewed bytes.
- `audits/FULL_PROOF_AUDIT_4.md`: PASS on the 2026-07-12 reviewed bytes.

Each audit independently reconstructed the complete proof chain.  The fourth
audit was started without the surrounding research conversation and included
a separate finite-`n` optimizer/diagonal sub-audit.  These historical verdicts
are not represented as reviews of the later 2026-07-13 repaired or
synchronized bytes; each file now carries an explicit top notice.  These are
internal checks, not external peer review.

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

## 2026-07-13 proof-component synchronization

After the adversarial repairs, the concise draft and the focused first-moment,
dense-overlap, residual-attachment, and amplification notes were synchronized
to the authoritative self-contained manuscript.  The propagation check in
`audits/PROOF_COMPONENT_SYNCHRONIZATION_AUDIT_2026-07-13.md` maps the uniform
root corridor, finite optimizer and tangent rounding, conditioned global
high-skeleton sum, one-sided residual estimate, and deterministic
amplification/final events to both the canonical locations and supporting
notes.  Its scope verdict is PASS for document propagation and traceability;
it is not an additional mathematical proof verdict.

The bodies and verdicts of the six relevant 2026-07-12 audits were preserved.
Top notices were added to delimit the older byte scope and point to the
adversarial and synchronization records.  The user-supplied verification files
were not edited and remain limited by their existing provenance statements.

This synchronization did not change the canonical manuscript, generated TeX,
or either PDF copy.  Their SHA-256 identifiers remain, respectively,
`9EA27F617D95DAFA42991A3CAF2ACBF3A4E92CA16CA25D524D7B587954D95A83`,
`AAF38D8134015EC9AEAD6FEA4916F618C4479F6601E1EB34F68A5134B0E1B82A`,
and `2ACD9BA34A7104976C65A007DF5132668605AFACA7407516B290545CB0634357`
for both PDF locations.

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

All eight experiment scripts compiled.  The two asymptotic diagnostic scripts
completed without assertion or arithmetic failure.  Finite computations are
diagnostic only and are not used as proof.

For the self-contained proof, concise proof, five main component proofs, and
four full audits, a structural scan found balanced display delimiters and no
duplicate equation tags.  The self-contained manuscript specifically has
187 opening and 187 closing display delimiters and 176 unique tags; scans for
tabs, mojibake, and the known malformed-TeX patterns were clean.

## 2026-07-13 publication artifact checks

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
displays `Samuil Petkov`, and the embedded PDF Author field
contains the same author metadata.
Text extraction found no blank page, replacement
character, or `??` marker and confirmed every lemma title, Proposition 9.2,
the main constant, all six references, five unique external reference links
in six PDF annotations, and the final section.

## 2026-07-14 publication artifact refresh

The canonical Markdown was regenerated as the boxed TeX manuscript and a
30-page A4 PDF.  Its top-level and `output/pdf/` copies are byte-identical
(SHA-256 `80004AB60B1504B24708B324E4E825E1843A2DF1AC560C9C49F1C0520727039E`).
Targeted 120-DPI rendering checked the revised title, attribution, theorem,
boxed-lemma, Heckel-provenance, and bibliography pages.  Text extraction found
no blank page, Unicode replacement character, or unresolved `??` marker and
confirmed all twelve lemma titles, Proposition 9.2, the explicit constant, the
eleven-reference bibliography, both Heckel papers, and the Aristotle report.

The separate sole-author publication-layout preprint compiles to 35 letter-size
pages.  Its top-level and `arxiv/main.pdf` copies are byte-identical (SHA-256
`626E04CFB1862CCE4E429D2BDA6026FA874E4EF5026B9816135B75F89C861C15`).
All 35 pages were rendered, reviewed in contact sheets, and spot-checked at
full size; no clipping, overlap, blank-page, unresolved-reference, citation,
or box-layout defect was found.  The editable TeX, author--year bibliography,
portable `.bbl`, build notes, and compiled PDF are synchronized in `arxiv/`.

## Supplementary animation artifact checks

The supplementary exact-example animation is generated by
`experiments/render_erdos625_animation.py`. Before rendering, the script
imports the repository's exact graph solver and checks the deterministic
selected instance modeled on `G(12,1/2)` (SplitMix64 seed 78), its 40-edge
graph digest, the exact
values `alpha=5`, `omega=6`, `chi=6`, and `zeta=3`, all displayed partition
classes, and the three lower-bound obstruction certificates. The resulting
gap is exactly `chi-zeta=3`. This is a finite explanatory example and is not
used as statistical evidence or as evidence for the asymptotic theorem. The
seed was deliberately selected to make the two exact partitions visually
instructive; no claim of representativeness is made. The validation gates use
explicit exceptions rather than optimization-sensitive Python assertions; the
validation-only check also passed under `python -O`.

The final H.264 MP4 is 1280 by 720 pixels, 24 frames/s, and 20.00 seconds. The
retained GIF preview is 960 by 540 pixels, 10 frames/s, 200 frames, and loops;
the repository README now links only the MP4.
Representative frames from all storyboard phases and a final full-resolution
frame were visually inspected after the last render. Titles, graph labels,
certificate highlights, color classes, clique/independent outlines, equations,
and the finite-example disclaimer were legible and unclipped. The JSON sidecar
records the edge list, exact witnesses, render settings, output hashes,
generator-script and exact-solver hashes, dependency versions, and font
basenames without machine-specific paths.

## Final SHA-256 identifiers

Paths below are relative to the `625/` directory.

```text
8E6B9233684303426D2CC42FC92D2F238A53D82F2BE9EB63F31560B3B2E6241B  proofs/COMPLETE_PROOF_SELF_CONTAINED.md
5094D58F685EF7ED7B9DE1CEC37202F48B8F70A0A2B18667B8957B232F955A2D  proofs/COMPLETE_PROOF_DRAFT.md
CA97B605FAE2FB4A0D0ABF9F8894EB5DBEB26455E21C312F5C37EF860A2E93C7  proofs/ALPHA_MINUS_TWO_ROUTE.md
C0AD9373F857D06A1EC9656AF2AEE725F087AD81D631E1A91258FE0F2430E950  proofs/DENSE_FOUR_TYPE_MATCHING.md
CE578B2B066A4545D0F1573300A218D8345B35D68F60316F9C32A3C8E99C5194  proofs/RESIDUAL_ATTACHMENT.md
4A91E9C5F01C980004817B821ED960EDAD43BBB6D3887A0C208A2B65AAD7A565  proofs/ALON_CONCENTRATION_EXTENSION.md
32E0BC482C41E7F357A441888E957E5222E60484F0EDDD206E14FCA0BF396D3F  audits/FULL_PROOF_AUDIT_1.md
1D4CC063455E6BBE0E06E8A8927FE35947BC325C19CBED6AA72BE188AC6F8802  audits/FULL_PROOF_AUDIT_2.md
0F2A2BC1E6C25835F53E6FF5676625E724D8DF485C01A8AABE91DA4DE2155341  audits/FULL_PROOF_AUDIT_3.md
A3977A50B4BB2C395596DAFC4B08FC256811BADF7D3D424959B8192282C9322B  audits/FULL_PROOF_AUDIT_4.md
7DC59CD69903A7125E1B5B7FBF7234D86004607499B5763557156A4BEFB56AEF  audits/DENSE_FOUR_TYPE_MATCHING_AUDIT.md
71CE7E3EE4794EB927BFF204C5B22FEA911F39FC20220068FBB1AD59E32121DC  audits/RESIDUAL_ATTACHMENT_AUDIT.md
CA110DE66D62F2CABC1D84E08594D343FB3BD9C8DA844D1D6BFA68B626FBB8E8  audits/ADVERSARIAL_LEAP_AUDIT_2026-07-13.md
0ABF100570C7CCF88592E9045E6C1EA1134393BB44C54EF5C68F300D7BB02D9B  audits/PROOF_COMPONENT_SYNCHRONIZATION_AUDIT_2026-07-13.md
088C2E4C9B45F5BC806842C68CCF94A9CAE477C876ABCB7B74A65B79F1B77C2A  sources/SOURCE_LEDGER.md
6F4847F423409AD7ED5397BDF385F69A56EE908078382812D454D34FDA4BD1D4  sources/ERDOS625_REFERENCES.bib
E9E56C7559D8774BE83281854EC5DCEAA9D8961D3DB5BB7E8EE01B2C5ED1A2D2  experiments/alpha_minus_two_route.py
85C25A975D7F4EEBF7B262126358B9058A171043AA2F26DA369ED9C9D86EB0F9  experiments/dense_transport_scan.py
DF90D14FE86A8FF3B1B8E2165EB7FB554811CD58D86D9F2CC3C6C7573AA1E0C0  experiments/exact_chi_zeta.py
E0107A1FEB47F8D2CD2F742E509FDC1C5B3BE4C60811AF09FF927E1712B3185E  verification/erdos625_verification_report.md
FB45DFEC62CED7BC8AADAD42865DA989572DCDC2FECC5AEB41B5A21B454E1310  verification/erdos625_independent_checks.py
CAB0A748309B9566E7AF3CB6A99ECBE939A901FB989F9392DDFD7451751D341E  output/tex/COMPLETE_PROOF_SELF_CONTAINED.tex
80004AB60B1504B24708B324E4E825E1843A2DF1AC560C9C49F1C0520727039E  output/pdf/COMPLETE_PROOF_SELF_CONTAINED.pdf
80004AB60B1504B24708B324E4E825E1843A2DF1AC560C9C49F1C0520727039E  COMPLETE_PROOF_SELF_CONTAINED.pdf
F5A3CE99990EE68DC3E91456BD0755990ECFD9C992547EEB346DF6EBF9632AAB  assets/erdos625-preview.png
0AB6B0293C37D20FBC70AD296C2795F67B3AC4ADB0110180A0AF2D2CE45E342F  experiments/render_erdos625_animation.py
32F713BA14257593FDCD931A38C46A189BB516D701B08C72F0AA9384F9079D40  assets/animations/erdos625-coloring-example.gif
68DE745E2B735756B5DF3BF3F2ADAE08A973742767E935F2E6FF744DA0A5CD96  assets/animations/erdos625-coloring-example.mp4
068C6201E59222187DE491C4C1B25312C2B54C30302EE3D32F6E361486EA6759  assets/animations/erdos625-coloring-example.json
```

The current complete archive is deliberately not hashed inside this record,
because this file is itself an archive member.  Its aggregate SHA-256 is kept
in `releases/SHA256SUMS.txt`, which is intentionally excluded from the ZIP.
