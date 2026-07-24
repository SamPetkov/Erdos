# M5 finite Section 4 and dual audit — 2026-07-13

## Verdict

**PASS for the pinned declarations below.**  This milestone closes the finite
Stirling, logarithmic-weight, profile-extraction, event-containment, Markov,
Gibbs-dual, and local dual-calculus layers needed for (4.3)–(4.5).  It also
proves a phase-cap squeeze theorem that reduces the remaining chromatic
probability limit to one explicit dual main-term limit.

This is not a certification of the continuous `L_+` comparison, the
target-matching tilt, the root/slope/rounding estimate, Lemma 3.1, or
`Erdos625Statement`.  Those obligations remain explicit below.

## Pinned source

| Module | Lines | SHA-256 |
|---|---:|---|
| `ColoringPartitionBridge.lean` | 120 | `C8B1EB88B8F605698C7D2CD8E77578853541F59D48681A9A23F3ECEC7989B8E8` |
| `ColoringProfileAggregationBounds.lean` | 52 | `DFF1334E276A56E376F44DFEA88C70578E9EF8F241161B0AD1538FE87FBE9C4D` |
| `ColoringProfileChromaticBridge.lean` | 56 | `F64D75491EBF0772C4D698489B450BB9C05D74F15B6A924B6CF314528E45E76F` |
| `ColoringProfileCountPositivity.lean` | 61 | `230D85582C3290E3F372146E26BCA83DAC5963874D3813BD56CF4BBE4456E1CE` |
| `ColoringProfileDiscreteObjective.lean` | 118 | `B5AB6CFF9BAFD40D0D4297D88360309B1B5AA3FD23A5EBC489A2EB436F3C2DAD` |
| `ColoringProfileDualAsymptotic.lean` | 73 | `DEDABE1D7738925636F2573FC64341D0FD160CC41D31577F19394E82105A7CC5` |
| `ColoringProfileDualBound.lean` | 235 | `6CACD8AF39F605665DBD110F7FE1F569B3591361350B0C2E83FD0A3814D9F904` |
| `ColoringProfileDualDifferentiation.lean` | 252 | `DD0E7AB8F4BC9CBCF4514AE3068448CB52E467DB4790FA71035F0C9F4AE58A79` |
| `ColoringProfileDualProbability.lean` | 50 | `837C9859DD9A83A48429D51F5E0646A73234130FBBFE60F837BEDF9480D3F960` |
| `ColoringProfileExtraction.lean` | 135 | `717E1C16F3D1A67E624133BE7DB5B95C99AFBFEDE62FBCBF7037C750364B6164` |
| `ColoringProfileFactorialBounds.lean` | 171 | `4F4EBAFFE80660A48846A61158CDC69700D33A8BFE3392AC43A0D653946CCC2D` |
| `ColoringProfileFirstMomentBound.lean` | 34 | `193938EDC9B79C764C10610DC7BFF9DE1C13F1C5703D1B186828C039ABAFA554` |
| `ColoringProfileLogBounds.lean` | 78 | `867D9AABC0E64468F8777E4577293CA57B59A6EB104EFEA667756B99CDD5893D` |
| `ColoringProfileLogWeight.lean` | 156 | `40ADB6A4FC77DEB48A7168C705EDA9C57B06887F71753F164FE977E94AE470E9` |
| `ColoringProfileProbability.lean` | 135 | `7FE70B6C0FA0CA4AEA05717E74F4A23E4364A3B27E03656466E87CD60E4DF508` |
| `ColoringProfileRealObjective.lean` | 160 | `EA5748697882132D60C95F2DE7EFCA817BE4E32133AF1A5A55F977F9D4AF23EC` |
| `ColoringProfileVariationalEnvelope.lean` | 87 | `CFDBC3B865CEB47AB932E1E1F25BB6274E85FF51DEA73DD4E07C5951B596F456` |
| `FinpartitionRefinement.lean` | 227 | `E97B1D96D371163030945DD5C3F54ED2E376B16520A075FD37F7A0E27893B3A6` |

## What is kernel-checked

### Finite logarithmic profile bound

The development proves explicit zero-safe logarithmic factorial estimates,
identifies the exact logarithm of each positive ENNReal profile expectation,
and transfers the bound back through `exp`.  Summing over the actual finite
profile box gives the rigorous `(n+1)^b` multiplicity.  The resulting finite
exponent is algebraically equal to the manuscript's expanded discrete
objective, including zero coordinates and the empty profile.

Natural profiles embed into an explicit real feasible space with exactly
preserved part-count, vertex-mass, and objective constraints.  A generic
variational envelope packages any valid real upper bound without assuming
that the manuscript's concrete `L_+` bound has already been proved.

### Exact coloring-to-profile reduction

A proper coloring is converted to its nonempty kernel partition and refined
to exactly `k` nonempty parts whenever `k≤n`.  Properness and the part-size
cap survive refinement.  The refined partition is extracted into a bounded
profile whose coloring count is positive.  Consequently the event `χ≤k` is
contained in the union of a positive bounded-profile-count event and the
event `α>b`, with zero endpoints treated explicitly rather than excluded.

Finite-space threshold-one Markov and a union bound then prove

`P(χ≤k) ≤ E[bounded profile count] + P(α>b)`.

Using the already proved independence-number estimate gives the sharp shifted
error `μ(n,b+1)`.  An audit caught an earlier coarse `μ(n,b)` draft before it
was accepted; the pinned theorem uses `b+1`, and hence gives
`phaseNat n + 2` at the phase cap.

### Concrete dual and its calculus

A finite, zero-safe Gibbs relative-entropy argument proves that every feasible
real profile is bounded by every value of an explicit one-parameter
log-partition dual.  This transfers to the finite aggregate and then to the
chromatic probability bound as

`ofReal((n+1)^b) · ofReal(exp(dual(t)+error_n)) + ofReal(μ(n,b+1))`.

The partition-function derivative, logarithmic derivative, dual derivative,
mean derivative, and variance identities are proved directly.  In particular,
the dual derivative is `parts·mean−n`, its derivative is `parts·variance`, and
it is strictly increasing for positive `parts` when `b≥2`.  The cutoff is
sharp: the independent audit compiled the `b=1` edge case and obtained zero
variance.

### Conditional asymptotic assembly

At `b=phaseNat n+1`, the final theorem combines the explicit finite dual bound
with the already proved full-sequence limit
`μ(n,phaseNat n+2) → 0`.  If the displayed dual main term tends to zero and
the natural part-count side conditions hold eventually, then
`P(χ≤parts n) → 0`.  This is a squeeze theorem, not an assumption that the
dual main term vanishes.

## Reproduced gates

- Final integrated `lake build --wfail`: **PASS**, 3,728/3,728 jobs.
- Final project inventory at the pinned Lean bytes: **50 Lean files, 10,715
  physical lines**; every accepted module is imported by `Erdos625.lean`.
- Recursive source gate for `sorry`, `admit`, `sorryAx`, line-leading project
  `axiom`/`constant`/`unsafe`, `native_decide`, `run_tac`, and
  `set_option autoImplicit true`: **PASS**.
- Integrated `Erdos625/AxiomAudit.lean`: **PASS**.  Representative new
  declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
- Independent frozen-pin audit of the dual differentiation, probability, and
  asymptotic modules: **PASS**.  Three direct warning-as-error compiles, a
  combined 3,085-job build, source/import/diff gates, nineteen public theorem
  axiom checks, sign review, and explicit boundary instantiations all passed.
- Independent reviews of the discrete objective, probability reduction, real
  embedding, variational envelope, refinement, extraction, and chromatic
  bridge: **PASS** after the sharp shifted-tail correction described above.
- `git diff --check`: **PASS**.

## Exact remaining Section 4 obligations

1. Prove the endpoint limits of the finite-support dual mean and existence and
   uniqueness of the target-matching tilt in the relevant phase corridor.
2. Identify the concrete dual optimum with the manuscript's `L_+` quantity,
   including the deficit-coordinate reindexing and uniform support comparison.
3. Prove the `L_+` root/slope estimate and transfer it through the manuscript's
   integer rounding, with all eventual positivity and cutoff conditions.
4. Verify that this parameter choice makes the explicit dual main term in the
   phase-cap squeeze tend to zero.

Only after these and all later signed-moment, overlap, residual, and
amplification obligations are closed may the project prove
`Erdos625Statement` or unfreeze the private arXiv package.
