# Work log

## 2026-07-11

- User confirmed the research brief.
- Initialized source ledger and mechanism registry.
- Began primary-source retrieval and first four-agent research wave.
- Proved an explicit adaptive product-space coupling `zeta <=st X`, exact
  concentration/amplification lemmas, and fixed-profile first moments for the
  two-graph model; see `proofs/TWO_GRAPH_MODEL.md`.
- Derived uniform oscillatory asymptotics, exact limiting density formulas,
  linear exceptional-gap widths, and a rigorous obstruction to deterministic
  nearby-`n` transfer; see `proofs/EXCEPTIONAL_REGIME.md`.
- Acquired original PDFs for Bollobás--Erdős (1976), Frieze (1990), all recent
  arXiv sources, and the CDC prompt. Historical paywall failures are recorded
  explicitly in `sources/HISTORICAL_SOURCE_AUDIT.md`.
- Completed the all-version recent-literature and forward-citation audit;
  recorded exact theorem quantifiers, dependency edges, publication metadata,
  and source-level typos in `sources/RECENT_WORK_AUDIT.md`.
- Derived the exact assigned two-graph overlap moment, its bipartite-Ising and
  even-subgraph representations, the termwise sandwich between signed
  cocolouring and ordinary colouring, and the exact `G(n,m)^2` replacement;
  isolated both the raw density-fluctuation obstruction and the remaining
  conditioned overlap sum in `proofs/X_SECOND_MOMENT.md`.
- Constructed the cap-constrained exceptional-profile phase below `x0`. An
  independent audit proved the complete-prefix lemma by an exact residual
  identity and rational certificates, and identified the active largest-class
  zero-rate prefix as the precise reason finite-`n` slack is still needed.
- Extended the Alon--Scott leftover-colouring concentration theorem to both
  `zeta` and `X`, improving their deterministic whp interval width to
  `omega sqrt(n)/log n`. Combined this with stochastic domination to sharpen
  the forum route: a fixed-positive-probability surrogate gap above that scale
  transfers to a whp original gap without using expectations.
- Built a standard-library exact `chi/zeta` solver, exhaustively validated it
  through all labelled graphs of order six and independent-oracle fixtures,
  and retained complement-audited exact samples through order 28.
- First independent coupling audit found no substantive error; further
  coupling and concentration reconstructions are in progress.
- Two further independent reconstructions confirmed the adaptive coupling,
  including the value-level and Boolean-slice formulations; no coupling
  defect was found.
- Proved a rare-event form of the Alon--Scott amplification argument: an
  event of probability at least `exp(-Lambda)` for `chi`, `zeta`, or `X`
  becomes a whp upper bound after an additive
  `O(sqrt(n(Lambda+r))/log n+n^(1/3))` cost.  This changes the admissible
  second-moment exponent for a target `n/log^3 n` gap from `n/log^6 n` to
  `n/log^4 n`; an independent reconstruction is underway.
- Derived and checked an exact finite-size expansion for the critical
  largest-class prefix of the capped exceptional profile.  The limiting cap
  has a positive `Theta(n loglog(n)^2/log(n)^2)` entropy lift even at the
  cycle start, and its integer rounding and optional slack cost fit inside
  the signed first-moment budget.  The all-partial-profile boundary layer is
  still not fully certified.
- Proved the exact signed overlap factor for arbitrary profiles and a uniform
  `1+O(log^4(n)/n)` contribution for every overlap cell up to half the class
  size.  Exact common top classes force an exponent
  `Theta(n loglog(n)^2/log(n)^5.385...)`, which is too large for direct
  Azuma but is `o(n/log^4 n)` and therefore compatible with rare-event
  amplification.
- For equitable signed profiles, proved endpoint control, exact partial-
  diagonal identities, and near-copy suppression.  The remaining overlap
  obligation is a residual-attachment expansion after exposing the matching
  of cells larger than half a class; a dedicated proof attempt is underway.
- An independent audit confirmed the rare-event amplification theorem and
  sharpened it to failure `exp(-r)+o(1)` with additive cost
  `O((sqrt(n Lambda)+sqrt(n r))/log n+n^(1/3))`, without the original
  sublinearity hypothesis.  The `o(n/log^4 n)` moment budget for an
  `n/log^3 n` gap is therefore independently certified.
- Proved the residual-attachment expansion after canonically exposing every
  cell above half a class: all local increments and all even-subgraph cycles
  cost `exp(o(n/log^4 n))` uniformly, with no `2^h` loss.  Combined with
  exact partial-diagonal estimates this closes the equitable raw signed
  moment at the required scale; an independent audit is underway.
- Identified a cleaner all-phase candidate using only the four class sizes
  `alpha-2,...,alpha-5`.  Its signed first-moment entropy appears to beat the
  unrestricted ordinary first-moment optimum by a uniform constant per
  class, while `mu_(alpha-2)>=n^(2-o(1))` makes the complete high one-polymer
  activity `o(1)`.  The remaining overlap term is now the explicit dense
  off-diagonal `4x4` containment transportation sum; its factorial weight is
  recorded and a focused proof attempt is active.

## 2026-07-12

- Replaced the numerical four-size observation by an analytic all-phase
  certificate: the entropy loss is below `ln(153/100)`, leaving the uniform
  signed margin `gamma_4=ln(200/153)`.
- Proved the exact common-part recurrence and the full diagonal sum
  `sum_r D(r)=1+o(1)`, including vanishing, macroscopic, and near-full mass.
- Proved the dense `4x4` geometric-mean transportation comparison.  Cauchy
  and two multinomial expansions sum all unequal-margin paths and type
  cycles at cost `exp(O(sqrt(n log n)))`; exact near-containments and both
  middle-strip residual regimes remain inside the `o(n/log^4 n)` budget.
- Combined dense high skeletons with the independently audited residual
  attachment theorem to obtain
  `ln(EZ^2/(EZ)^2)=o(n/log^4 n)` for the exact tangent-rounded midpoint
  profile.
- Paley--Zygmund and the independently audited rare-event Alon--Scott theorem
  then give the proposed all-`n` result
  `chi-zeta >= ((ln2)^2 ln(200/153)/32)n/(ln n)^3` with high probability.
- Four independent end-to-end reconstructions returned PASS.  During those
  audits, the phase-uniform statement for `mu_(alpha+2)`, the small-residual
  middle-strip term, and the exact finite-`n` optimizer wording were repaired;
  none of the repairs changed the theorem or constant.
- Consolidated the component chain into the 12-section self-contained
  manuscript `proofs/COMPLETE_PROOF_SELF_CONTAINED.md`, including proofs of
  the simultaneous leftover-colouring and rare-event amplification lemmas.
  Final delimiter/tag, malformed-TeX, code, and exact-solver checks are logged
  in `FINAL_VERIFICATION.md`.
- The result remains labelled a proposed resolution pending external expert
  review, publication, and priority verification.  The four previously
  unavailable historical originals were later supplied by the user, read on
  2026-07-12, and recorded with hashes in the source ledger; they confirmed
  the historical framing and required no change to the theorem or constant.
- Added the user-supplied follow-up report with its exact verdict,
  **Provisional internal verification: PASS**, plus its unchanged checker,
  reproduced output, hashes, provenance, and limitations.  Independent replay
  returned all five PASS groups; this remains internal finite diagnostic
  evidence, not peer review or formal verification.
- Generated an LF-normalized standalone TeX manuscript and compiled a 25-page
  A4 PDF.  All 12 lemma statements are set in blue breakable boxes,
  Proposition 9.2 is set in green, and proofs stay in normal page flow.  The
  final build has no overfull boxes or missing glyphs, all pages rendered, and
  representative title, theorem-box, dense-equation, residual, and provenance
  pages passed visual inspection.
- Added the supplied schematic preview to the repository landing pages with
  an explicit statement that it is explanatory and not proof evidence.
- Rebuilt the complete release ZIP to include the proof chain, audits,
  verification assets, TeX, PDF, preview, source ledger, and reproducibility
  files.

## 2026-07-13

- Reopened the proof under an adversarial, route-split review rather than
  relying on the four earlier PASS verdicts.  The review found a circular
  signed-root localization in the written use of Lemma 3.1, an unstated
  conditioning/globalization bridge in Lemma 8.3, and an overstrong two-sided
  formulation of Lemma 9.1.
- Strengthened Lemma 3.1 to a uniform root-corridor theorem for
  `L_S+ck`, made the finite optimizer convergence explicit, and defined the
  tangent-rounding errors and effective multiplier.  This removes the root-
  localization circularity without changing the root gap or constant.
- Added the exact endpoint-decoration product, joint middle-cell threshold
  expansion, small-residual expectation, and global conditioned sum in
  (8.25a)--(8.29b).  The patched proof now displays the multiplicities and
  conditioning needed to pass from local estimates to all high skeletons.
- Replaced the residual attachment claim by the one-sided uniform upper bound
  actually proved and used.  Also made the central-rate domain, log-convex
  near-containment check, leftover recurrence, growing deterministic
  amplification parameter, and final deterministic error sequence explicit.
- Three independent regression reviews returned PASS on the repaired routes.
  The severity-ranked findings, repairs, diagnostics, and remaining external/
  formal verification boundary are recorded in
  `audits/ADVERSARIAL_LEAP_AUDIT_2026-07-13.md`.
- Replayed the five-group independent finite checker successfully, regenerated
  the color-boxed TeX, and compiled a 27-page A4 PDF.  All pages rendered; the
  repaired root, high-skeleton, residual, amplification, theorem, and reference
  pages passed full-size visual inspection.
- Added a deterministic 20-second README animation of one exactly solved
  `G(12,1/2)` graph (SplitMix64 seed 78). The renderer reuses the exact solver,
  validates `chi=6`, `zeta=3`, both displayed partitions, and explicit
  lower-bound obstruction certificates before producing the GIF and MP4. The
  selected seed is a finite explanatory artifact, not statistical evidence or
  evidence for the asymptotic theorem.
- Embedded the optimized GIF in both GitHub landing pages, linked it to the HD
  MP4, and recorded the full edge list, witnesses, render settings, hashes,
  dimensions, sizes, and finite-example limitation in a JSON sidecar and asset
  README. Representative animation phases passed visual inspection.
- Synchronized the concise draft and focused first-moment, dense-overlap,
  residual-attachment, and amplification notes to the canonical 2026-07-13
  repairs.  The canonical manuscript remains the sole authoritative proof;
  the component files are now explicitly indexed as supporting derivations.
- Added a proof-component traceability matrix and placed scope notices on the
  six 2026-07-12 audit records whose PASS verdicts concern earlier bytes.  The
  notices preserve those audit bodies and verdicts without representing them
  as reviews of the later repaired or synchronized files.
- This propagation pass did not change the canonical Markdown, generated TeX,
  or either PDF copy.  Their SHA-256 identifiers remain `9EA27F...D95A83`,
  `AAF38D...1B82A`, and `2ACD9B...4357`, respectively.  The user-supplied
  verification report and checker were also left untouched.
- Two fresh read-only regression passes independently checked the synchronized
  root/rounding/amplification chain and the dense-overlap/residual chain.  Both
  returned PASS after minor notation and path cleanups; no new mathematical
  claim, constant, or full-sequence quantifier was introduced.
- Refreshed the component/audit hash ledger, added repository-wide LF rules for
  dossier text and scripts, and rebuilt the current 65-file complete archive.
  Its aggregate checksum is kept outside the archive in
  `releases/SHA256SUMS.txt`.
- Began the confirmed brick-by-brick Lean 4 formalization without Aristotle.
  Milestone M0 pins Lean/mathlib, formalizes finite labelled graphs, chromatic
  and cochromatic invariants, exact minimum semantics, `ζ≤χ`, induced-set and
  leftover gluing, the exact `G(n,1/2)` law, uniform singleton mass, event
  measurability, and the full-sequence target proposition.  `lake build
  --wfail` succeeds with no placeholder or project axiom; independent graph,
  probability, and reproducibility reviews returned PASS.  The target remains
  explicitly unproved, and the remaining dependency graph is recorded in
  `formalization/FORMALIZATION_LEDGER.md`.
- Extended the imported Lean closure with exact phase/floor identities,
  adjacent first-moment ratios, Markov and zero-threshold Paley–Zygmund,
  an exact binomial lower-quarter tail, the complete independent-set
  expectation/event calculation, and the non-asymptotic phase setup. A
  warning-free 3,138-job build, strict source scan, and 24 representative
  axiom checks passed; independent statement audits found no blocking issue.
  The bounded-differences coordinate bridge and the quantitative phase
  expansion remain explicitly open, and the arXiv package remains paused.
- Hardened the Lean CI source gate after an independent integration audit
  noticed that its earlier expression did not reject explicit placeholder
  axioms or `constant` declarations. The strengthened gate also rejects
  `unsafe`; the current source passes it.
- Proved the centered bounded-differences MGF directly on every finite uniform
  Boolean cube by recursive two-point averaging, identified that average with
  the actual uniform-PMF integral, and derived exact one-/two-sided tails with
  variance proxy `Σcᵢ²/4`. A cross-audit passed constants, centering,
  degenerate cases, source, compilation, and axiom checks. The manuscript's
  larger vertex blocks still require a separate product-space theorem and
  graph-statistic oscillation proof.
- Added explicit finite Taylor, descending-factorial, and sharp two-sided
  Robbins remainder estimates. A separate cross-audit passed every stated
  theorem. The endpoint-uniform algebraic assembly (2.5), (2.6), and (2.2)
  remains open rather than being inferred from these ingredients.
