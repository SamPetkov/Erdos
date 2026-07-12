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
  review, publication, and priority verification.  Historical-source access
  failures remain explicitly disclosed in the source ledger.
- Added the user-supplied follow-up report with its exact verdict,
  **Provisional internal verification: PASS**, plus its unchanged checker,
  reproduced output, hashes, provenance, and limitations.  Independent replay
  returned all five PASS groups; this remains internal finite diagnostic
  evidence, not peer review or formal verification.
- Generated a standalone TeX manuscript and compiled a 25-page A4 PDF.  The
  final build has no overfull boxes or missing glyphs, all pages rendered, and
  representative title, theorem, dense-equation, residual, and provenance
  pages passed visual inspection.
- Added the supplied schematic preview to the repository landing pages with
  an explicit statement that it is explanatory and not proof evidence.
- Rebuilt the complete release ZIP to include the proof chain, audits,
  verification assets, TeX, PDF, preview, source ledger, and reproducibility
  files.
