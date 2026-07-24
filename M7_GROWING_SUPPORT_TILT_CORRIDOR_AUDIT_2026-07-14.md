# M7 growing-support tilt and corridor audit — 2026-07-14

## Verdict

**PASS for the pinned declarations and source bytes below.** This milestone
closes the bounded-tilt growing-support partition and moment estimates, the
limiting deficit-Gaussian law through second order, its strict mean inversion,
pointwise and compact-uniform moment convergence, compact selected-tilt
convergence, and the generic inverse/root/rounding tools used by Section 4.

This is not a certification of manuscript Lemma 3.1, the phase-specific
`L_+` center and slope estimates, the final chromatic probability limit, any
of the signed-overlap and residual arguments in Sections 6–9, or
`Erdos625Statement`. Those obligations remain explicit below.

## Pinned source

| Module | Lines | SHA-256 |
|---|---:|---|
| `GaussianTailTools.lean` | 93 | `760FBC526C01BA42D37885509710F288EA26351E6C22EC1ACE51F096A6D9F4A3` |
| `GeometricMomentTools.lean` | 83 | `0E911845F72F9C5A96494F0281F45E43DA8951A339437F1D53AD85DB108EBA19` |
| `GaussianMomentTailTools.lean` | 72 | `5336EBED3AA295E514FB6603A90E3C125754A6C14621B53EEE79C2058C6134` |
| `GeometricSecondMomentTools.lean` | 146 | `3AEFF988953B08E299AADE9D2E2B509B77E1B96EB243E90A3190FBB1B1918FD3` |
| `GaussianSecondMomentTailTools.lean` | 77 | `FF720FA70E33948EE6968FB1A9492B262F2FA996BCF5E1298A85EF34750A1C9A` |
| `SeriesConvergenceTools.lean` | 46 | `96B3769A270A86CBA5492351FE933E7F843C658CAD340E7B61E3839D23AF0E2C` |
| `UniformSeriesConvergenceTools.lean` | 201 | `1684840090EE0BA95EC5A0240E3645C3B88D0CD323B6DB53FE3245261BA3243F` |
| `TiltedGaussianSummability.lean` | 77 | `AA392F6785A9C7A30B958F8FAA879C2A5EDC5053D2D0E87CEFA0A848374BBEA9` |
| `ExtendedGaussianProfile.lean` | 211 | `C0943C6E2D41AA613DD7FA5C70D26D018279DF4760EA3901AB20CD46E5B76B2E` |
| `ExtendedGaussianEndpoints.lean` | 467 | `64DDD44D8F8A1746DC4E6F465A977F0F2D4BE8372521B24C05AA202CB577F493` |
| `ExtendedGaussianCalculus.lean` | 372 | `52D085FEF4D8DA9007DCB3876A6683DF4B0C48CFDDF156ADD731939C4E3E9EF3` |
| `ColoringProfileDeficitPartitionBounds.lean` | 485 | `16AFCB8F30C91E1811E337DF69CBCC38248DF5F9DC11289EEB5FB45B435758F7` |
| `ColoringProfileDeficitPointwiseConvergence.lean` | 172 | `46AE9D6414631FB9B3B546BA00F33B5B63BE089AC57DFB18FE7403D56552EE30` |
| `ColoringProfileDeficitConvergence.lean` | 69 | `F054354659D476060977DC8C1D5BCDCF473B2CAEA33784A72450B9F189BF766C` |
| `ColoringProfileDeficitMomentConvergence.lean` | 276 | `D4D662C59D913A3638168F22F4D3B49434A65D7887C3F893D2A511D45BAC1323` |
| `ColoringProfileDeficitUniformMomentConvergence.lean` | 410 | `F93776ED50981343B5D65B6F6275643C68372CE50E59ED46F5D13C1DA2DBE288` |
| `ColoringProfileDeficitUniformMeanConvergence.lean` | 108 | `55667A552734FF9152870C50B96F299B6B6707D2D6E28E27DCC67674073E9C13` |
| `ColoringProfileDeficitTilt.lean` | 200 | `3216017316F7FB8E28C37E4703B3A80E10CE764BC9CED97E6E3B355E6DAD9988` |
| `ColoringProfileDeficitVariance.lean` | 469 | `323FAEF6BE874981708ED6A5EF7B477AB2FAC927BC6E119B4F04F956A6AD6CA4` |
| `ExtendedGaussianTilt.lean` | 247 | `D966E90B3F65B06DCCD550E93CCC41A1CE4BAE2CF0EA54AB92AE6FF0544E30E8` |
| `ColoringProfileDeficitTiltConvergence.lean` | 126 | `551D1407AD6C06664303F8B3158991446960CD3D9E30C26B0F586985517441A1` |
| `InverseConvergenceTools.lean` | 79 | `834B0936BC05E77E50A0932FBB0B1F6636E67D8B72E7120D31A0ACA3A8011B71` |
| `MeanInversionTools.lean` | 76 | `21D0BE1949EE65583BAE33EC4528F569D9C579C856A58F2532D9EF61C07D50C9` |
| `VarianceStabilityTools.lean` | 102 | `C92C56624027DA830E255F8E3695838EF151090E59CA4CD0175097E9C8C0E759` |
| `ProfileAsymptoticTools.lean` | 132 | `6BA710D29717906925411DCB63A7D400B29FAC94FF7F4A87DF5749098F1A953E` |
| `ProfileCorridorTools.lean` | 162 | `56494155EA53BA7CF333B96B7AB72DE8D7139EAF750FA07D619D19A832F8B417` |

Toolchain: Lean `v4.31.0`; mathlib release `v4.31.0`, pinned by
`lake-manifest.json`.

## What is kernel-checked

### Uniform moments and the limiting deficit law

Exact reversal of the finite support isolates the exceptional deficit `-1`
atom. Explicit Gaussian/geometric tails control the partition, absolute first
moment, and second moment uniformly in the support whenever `|λ|≤M`; the
zero-deficit atom gives a uniform denominator lower bound.

The limiting law on `{-1,0,1,…}` has summable moments through order two. Its
partition and first numerator are differentiable term by term, its mean has
derivative equal to its raw variance, and a countable Cauchy–Schwarz argument
makes that variance strictly positive. The mean tends to `-1` and `+∞` at the
two tilt endpoints, so every target above `-1` has one unique limiting tilt.

### Growing-support and selected-inverse convergence

Fixed-coordinate convergence plus one summable Gaussian majorant is promoted
to convergence of the entire growing-support partition, first numerator,
second numerator, and normalized mean. The convergence is both pointwise and
uniform on every bounded tilt interval.

For each compact target interval above `-1`, the finite selected tilts are
eventually trapped by one common bound and converge uniformly to the limiting
selected tilt. Finite variances converge uniformly to the positive limiting
variance. A compact positive variance floor and derivative integration supply
an explicit lower-separation modulus, so the inverse-convergence theorem does
not assume the desired inverse conclusion.

### Generic phase-corridor interfaces

The milestone proves reusable theorems for a unique decreasing root, a
quantitative root corridor from a center error and negative derivative bound,
integrated decrement estimates, endpoint tilt trapping, and the exact effect
of flooring a real root and subtracting a ceiling. It also proves the exact
product-chain derivative needed for a part-count objective.

These generic theorems do not identify the manuscript's phase objective or
prove its center and slope hypotheses. Those concrete substitutions remain
open and cannot be discharged by invoking the generic interface itself.

## Reproduced gates

- Integrated `lake build Erdos625 --wfail`: **PASS**; Lake reported
  `Build completed successfully (8639 jobs)`.
- Isolated warning-as-error builds of the selected limiting tilt, compact
  selected-tilt convergence, and root-corridor modules: **PASS**.
- Project inventory at the pinned Lean bytes: **81 Lean files, 17,049 physical
  lines**; every accepted module is imported by `Erdos625.lean`.
- Recursive source gate for `sorry`, `admit`, `sorryAx`, line-leading project
  `axiom`/`constant`/`unsafe`, `native_decide`, and `run_tac`: **PASS**.
- Integrated `Erdos625/AxiomAudit.lean`: **PASS**. Every representative new
  declaration reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Independent statement and edge-case audits of the growing-support moment,
  compact-inverse, variance-stability, and corridor modules: **PASS, no
  blockers**.
- `git diff --check`: **PASS**.

## Exact remaining obligations

1. Identify the finite attained optimum with the phase-dependent scalar
   objective, prove its center estimate and phase-uniform derivative bounds,
   instantiate the root corridor, justify the integer decrement, and make the
   chromatic probability bound tend to zero.
2. Formalize the four-size signed first moment and its uniform entropy
   comparison.
3. Formalize the ordered overlap margins, contingency-table probability, and
   the complete central/near/middle second-moment partition in Sections 6–8.
4. Formalize the residual threshold expansion, even-cycle decomposition,
   weighted traversal bounds, and marked partial-profile recurrence in
   Section 9.
5. Assemble the rare-seed and bounded-differences amplification with those
   results, then prove `Erdos625Statement` itself.

Only after all five items and the final source/axiom/dependency audit pass may
the repository describe the exact theorem as fully machine-verified.
