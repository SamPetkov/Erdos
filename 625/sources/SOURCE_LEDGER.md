# Source ledger

Literature-search date: 2026-07-11. Original-source audit updated:
2026-07-12. Entries are marked `verified-original` only after the original
HTML/PDF/text has been acquired and checked directly. Full theorem wording,
version diffs, and source-level warnings are in `RECENT_WORK_AUDIT.md`;
historical acquisition and inspection details are in
`HISTORICAL_SOURCE_AUDIT.md`.

| ID | Source | Type/status | Original acquired | Exact statement extracted | Quantifier/range audit | Model/profile assumptions | Forward-citation status | Notes |
|---|---|---|---|---|---|---|---|---|
| 1 | Erdős Problems #625 record | Web/primary record | Direct HTML read 2026-07-11 | Full record transcribed in historical audit | Open status is site-owner belief; target is all large `n` whp | `G(n,1/2)`, `chi`, `zeta` | N/A | Verified-original web record |
| 2 | Site LaTeX source/bibliography | Web/primary record | Direct HTML read | Full statement and bibliography checked | Summaries distinguish subsequence, ~95%, and conjecture | Same problem | N/A | Verified-original web record |
| 3 | Complete forum thread #625 | Web/discussion | All three comments read | Two-graph proposal reconstructed separately | 2025-09-15 claims are unreviewed; uniform all-large-`n` is essential | Surrogate `X(G1,G2)` | N/A | Exact coupling is proved in `TWO_GRAPH_MODEL.md` |
| 4 | CDC prompt architecture | PDF/method reference | Original PDF acquired/read | N/A | N/A | N/A | N/A | Workflow only; local PDF/extraction retained |
| 5 | Heckel, arXiv:2408.13839 | v2 preprint + EJC 31(4), P4.72 | All arXiv versions/source and EJC PDF read | Thm. 1, Prop. 3 reconstructed | `0.999` upper-gap hypothesis gives only an unbounded-subsequence bound | `G(n,1/2)`, unrestricted gap | Citation audit complete | Verified-original; exact constants audited |
| 6 | Steiner, arXiv:2408.02400 | v2 preprint; SIAM JDM 39(4), 2025 | All arXiv versions/source read; final publisher PDF access-blocked | v2 Thm. 1.7 reconstructed | Fixed `eps`; infinitely many `n`; probability `c_eps>0`, not whp | `G(n,1/2)`, unrestricted gap | Final metadata/references checked | Random theorem absent from v1; journal limitation recorded |
| 7 | Heckel, arXiv:2409.17614 | v2 preprint (2025-02-19) | All versions/PDF/source read | Thm. 1 and Props. 5–6 reconstructed | Fixed `eps`; whp on every admissible sequence, not all `n` | `(alpha-1)`-bounded tame profile; `mu_alpha` window | No post-Feb-2025 citing work located; coverage caveats explicit | v2 corrected lower hypothesis to `n^(0.05+eps)` |
| 8 | Heckel–Panagiotou, arXiv:2306.07253 | v3 preprint | All versions/PDF/source read | Thms. 1.1, 1.2, 2.5; Lem. 7.20/imports audited | Clause-specific fixed-power and partial-profile hypotheses recorded | Mainly `G(n,m)` then transfer; tame bounded profiles | Dependency audit complete | Source typos flagged |
| 9 | Heckel–Riordan, arXiv:2103.14014 | v3; JLMS 108(5), 2023 | All versions/PDF/source read | Thms. 5 and 8 reconstructed | Strongest consequences are subsequence statements | Deterministic intervals for `chi` | Dependency into Heckel verified | DOI 10.1112/jlms.12794 |
| 10 | Heckel, arXiv:1906.11808 | v2; JAMS 34, 2021 | All versions/PDF/source read | Thm. 3 reconstructed | Rules out narrow all-`n` intervals via infinite witness subsequence | `chi(G(n,1/2))` | Superseded quantitatively by HR | DOI 10.1090/jams/957 |
| 11 | Scott, arXiv:0806.0178 | v2 explanatory note | Both versions/PDF/source read | Thm. 1 and leftover proof reconstructed | Each prescribed `omega(n)->infinity`; whp all `n` | `chi(G(n,p))`, fixed `p` | N/A | Argument extended/reproved for `zeta` and `X` |
| 12 | Surya–Warnke, arXiv:2201.00906 | v2; EJC 31, P1.44 | Both versions/PDF/source read | Thms. 1, 3, 4 audited | whp throughout stated `p` ranges | Ordinary `chi`, not `zeta` | N/A | At `p=1/2`, width `omega sqrt(n)/log n` |
| 13 | Erdős–Gimbel (1993) | Ann. Discrete Math. 55, 261–264 | User-supplied original PDF read in full 2026-07-12 | Definition, random-graph bounds, and explicit open difference question checked on p. 263 | Full `n->infinity` sequence; the source's “a.s.” terminology is read as a.a.s., not a subsequence claim | `G(n,1/2)`; historical cochromatic source | N/A | Verified-original; DOI and PDF hash recorded in historical audit |
| 14 | Gimbel (2016) | Springer chapter, 95–108 | User-supplied original PDF read in full 2026-07-12 | Section 7.4 and Problem 2 checked on p. 100 | Full `n->infinity` sequence; the source asks `chi(R_n)-z(R_n)->infinity` “almost surely” | `R_n=G(n,1/2)`; historical survey | N/A | Verified-original; ratio statement and $100/$1000 prize note checked |
| 15 | Bollobás (1988) | Combinatorica 8, 49–55 | User-supplied original PDF read in full 2026-07-12 | Theorem 4 checked on p. 52 | Fixed `0<p<1`; almost every `G(n,p)`; first-order `chi` asymptotic | Ordinary `chi`; `d=1/(1-p)`; no cochromatic-gap theorem | N/A | Verified-original; exact denominator and PDF hash recorded |
| 16 | Bollobás–Erdős (1976) | Math. Proc. Camb. Phil. Soc. 80, 419–427 | Original Rényi author scan read/rendered | First-order and sharper clique statements checked | Infinite-graph coupling wording recorded | Clique number/complement independence | N/A | Verified-original; local scan retained |
| 17 | Frieze (1990) | Discrete Math. 81, 171–175 | Original CMU author scan read/rendered | Displayed theorem checked visually | `d=np`, fixed epsilon, `d_epsilon<=d=o(n)`; not constant `p=1/2` | Independence number | N/A | Verified-original; local scan retained |
| 18 | Janson–Łuczak–Ruciński (2000) | Wiley book | User-supplied original scan visually checked 2026-07-12 | Contents, §7.4, Lemma 7.13, Theorem 7.14, and Remark 7.15 checked on pp. 190–192 | Fixed `0<p<1`; a.a.s. (probability tending to one); sharper constant-`p` denominator recorded | Ordinary dense random-graph `chi`; no cochromatic-gap theorem | N/A | Verified-original by rendered-page inspection; scan has no usable text layer |

The four user-supplied copyrighted PDFs are identified by filename and SHA-256
in `HISTORICAL_SOURCE_AUDIT.md`; they are intentionally excluded from the
public repository and release archives.
