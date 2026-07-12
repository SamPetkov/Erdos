# Final verification record

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

## Final SHA-256 identifiers

Paths below are relative to the `625/` directory.

```text
53B2ADCCD64133991F3DCDCAA9F8E8820F38A12C982CC5735F96568DD014A190  proofs/COMPLETE_PROOF_SELF_CONTAINED.md
42A39BC3A7D922B74EC3501EF233F93711F9C2769FE602EDA70E145220B923D3  proofs/COMPLETE_PROOF_DRAFT.md
CC17BE8A3196258FF6BFAC6FAD154EF7FA3D7EC7CE32CB29C4384C0397028213  audits/FULL_PROOF_AUDIT_1.md
2B9D96CBB560FD0674978B3111E1DF22A511412CEC42FDDDF2BE099F4E31125E  audits/FULL_PROOF_AUDIT_2.md
F7724290612866BD6D6A2105C95202C6C943C4CA93574708F980AFB0D087AE6E  audits/FULL_PROOF_AUDIT_3.md
110549CEDC8056BB7DE57D43789CA81D3FD48BCF9D45ADD697141117166E632E  audits/FULL_PROOF_AUDIT_4.md
6B7D2ACD66C4E51FF9C4608A081E4662CAC28445BEA98435DAB990FCF1FD0F55  sources/SOURCE_LEDGER.md
E9E56C7559D8774BE83281854EC5DCEAA9D8961D3DB5BB7E8EE01B2C5ED1A2D2  experiments/alpha_minus_two_route.py
85C25A975D7F4EEBF7B262126358B9058A171043AA2F26DA369ED9C9D86EB0F9  experiments/dense_transport_scan.py
DF90D14FE86A8FF3B1B8E2165EB7FB554811CD58D86D9F2CC3C6C7573AA1E0C0  experiments/exact_chi_zeta.py
```

## Source-access limitation

The source ledger records four mandatory historical originals that could not
be legally acquired through the available public or institutional routes:
Erdős--Gimbel (1993), Gimbel (2016), Bollobás (1988), and
Janson--Łuczak--Ruciński (2000).  They are not represented as directly read.
All recent arXiv versions and accessible originals were acquired and audited;
the forward-citation search date and negative-search limitations are recorded
in `sources/SOURCE_LEDGER.md` and `sources/RECENT_WORK_AUDIT.md`.
