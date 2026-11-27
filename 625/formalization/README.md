# Lean 4 formalization of Erdős Problem 625

This directory contains a complete Lean 4 formalization of the explicit
uniform quantitative consequence below. That consequence resolves Erdős
Problem 625. The companion 15-page manuscript (`../manuscript/main.tex`, titled
*The Asymptotic Difference Between the Chromatic and Cochromatic Numbers of a Random Graph*
and prepared as `arXiv:2608.30604v3`; earlier one-sided version at `arXiv:2608.30604v2`)
determines the exact asymptotic difference along the **full** integer sequence
(`lim_{n -> infty} ((log_2 n)^3 / n) (χ(G_n) - ζ(G_n)) = 1/4`, equivalently
`((log n)^3 / n) (χ(G_n) - ζ(G_n)) -> (log 2)^3 / 4`, almost surely under every
joint coupling of `(G_n)_{n >= 2}`, in `L^p` for every `1 <= p < infty`, in
running-supremum sub-Gaussian Orlicz `psi_2`-norm (`S_n := sup_{m >= n} |Y_m - 1/4|`,
`||S_n||_{psi_2} <= 4 (log_2 n)^3 sqrt(log n / n) + sup_{m >= n} |E[Y_m] - 1/4| / sqrt(log 2) -> 0`
with `lim_{n -> infty} E[e^{M S_n^2}] = 1` for every `M >= 0` and `lim_{n -> infty} E[S_n^p] = 0`
for every `1 <= p < infty` under every joint coupling of `(G_m)_{m >= 2}`, alongside
`||sup_{m >= n} |Y_m - E[Y_m]|||_{psi_2} <= 4 (log_2 n)^3 sqrt(log n / n)` for `n >= e^{12}` and
single-`n` `||Y_n - 1/4||_{psi_2} <= sqrt(8/3) (log_2 n)^3 / sqrt(n) + |E[Y_n] - 1/4| / sqrt(log 2) -> 0`
with `lim_{n -> infty} E[e^{M (Y_n - 1/4)^2}] = 1`), and
locally uniformly in cumulant- and moment-generating functions
`log E[e^{t Y_n}] -> t/4` and `E[e^{t Y_n}] -> e^{t/4}` on `[-T, T]` (`T >= 0`), with
`E[χ(G_n) - ζ(G_n)] = (1/4 + o(1)) n / (log_2 n)^3`, `Var(χ(G_n) - ζ(G_n)) <= n - 1`,
`0 <= log E[e^{lambda Y_n}] - lambda E[Y_n] <= lambda^2 (log_2 n)^6 / (2 n)`,
`P(|Y_n - E[Y_n]| >= u) <= 2 exp(-u^2 n / (2 (log_2 n)^6))`, Gaussian-threshold
square-exponential (`psi_2`) moment bounds
`E[exp(theta (Delta(G_n) - E[Delta(G_n)])^2 / (n - 1))] <= (1 - 2 theta)^{-1/2}` and
`E[exp(theta n (Y_n - E[Y_n])^2 / (log_2 n)^6)] <= (1 - 2 theta)^{-1/2}` (`theta ∈ [0, 1/2)`),
Gaussian-constant Orlicz `psi_2`-norm bounds
`||Delta(G_n) - E[Delta(G_n)]||_{psi_2} <= sqrt((8/3)(n - 1))` and
`||Y_n - E[Y_n]||_{psi_2} <= sqrt(8/3) (log_2 n)^3 / sqrt(n)`
(with `||X||_{psi_2} := inf { s > 0 : E[e^{X^2 / s^2}] <= 2 }`, `||c||_{psi_2} = |c| / sqrt(log 2)`,
and `||X + Y||_{psi_2} <= ||X||_{psi_2} + ||Y||_{psi_2}`),
central `L^p` bounds `E[|Delta(G_n) - E[Delta(G_n)]|^p] <= 2 ((p / e)(n - 1))^{p/2}` and
`E[|Y_n - E[Y_n]|^p] <= 2 (p (log_2 n)^6 / (e n))^{p/2}` (`1 <= p < infty`),
non-asymptotic coupling-uniform fluctuation bounds
`P(exists m >= n : |Delta(G_m) - E[Delta(G_m)]| >= sqrt(2(1 + eta)(m - 1) log m)) <= 2 (1/eta + 1/n) n^{-eta}`
(`n >= 2`, `eta > 0`, hence `limsup_{n -> infty} |Delta(G_n) - E[Delta(G_n)]| / sqrt(2 n log n) <= 1` almost surely), and
sub-Gaussian single-`n` and coupling-uniform tail-union bounds
`P(|Y_n - 1/4| > varepsilon), P(exists m >= n : |Y_m - 1/4| > varepsilon) <= 2 exp(-vartheta^2 varepsilon^2 n / (2 (log_2 n)^6))`
eventually for every fixed `varepsilon > 0`, `vartheta ∈ (0, 1)`, and joint coupling of `(G_n)_{n >= 2}`),
together with an explicit `O(log log n / log n)`-rate full-sequence two-sided
refinement `[0.080, 0.086] · n / (log n)^3` (almost surely and in expectation, with
moving-corridor exit tail `<= 2 exp(-n (log log n)^2 / (2 (log n)^8))` eventually and
fixed-corridor single-`n` and coupling-uniform tail-union bounds
`P(((log n)^3 / n) Delta(G_n) ∉ [c', C']), P(exists m >= n : ((log m)^3 / m) Delta(G_m) ∉ [c', C']) <= 2 exp(-vartheta^2 eta_0^2 n / (2 (log n)^6))`
eventually for every `c' < c_7`, `C' > C_7`, `eta_0 = min(c_7 - c', C' - C_7)`,
`vartheta ∈ (0, 1)`, and joint coupling of `(G_m)_{m >= 2}`) via
the shifted seven-size phase gain `A_7(delta_tilde_n) > log(391/200)`, unconditional
`(k + 2d)` / `(k + 4d)` class splitting, elementary Stirling-free factorial
reductions `(1.1)`, and a self-contained `G(n, 1/2)` second-moment proof; the
exact scope of `Erdos625` and the auxiliary library `Erdos625HP` is recorded below.

The exact top-level result is

```lean
theorem Erdos625.erdos625 : Erdos625.Erdos625Statement
```

where `Erdos625Statement` says that, for `G(n,1/2)`, the probability of

```text
chromaticNumber - cochromaticNumber
  >= ((log 2)^2 / 4 * log (200 / 153)) * n / (log n)^3
```

tends to one along the full sequence of natural numbers.

## Reproduce the modular proof

The project pins Lean and mathlib at version `v4.31.0`. From this directory:

```text
lake exe cache get
lake build --wfail
```

The final declaration is in `Erdos625/Section15FinalInstantiation.lean`.
`Erdos625.lean` is the project root and imports the complete proof closure.

## Reproduce the one-file proof

`Erdos625SelfContained.lean` concatenates the complete transitive local import
closure of the release root into one Lean source file. It retains only external
Mathlib imports; "one-file" therefore means one project source file, not a
copy of Mathlib or a toolchain-free artifact.

Check that it is current:

```text
python scripts/generate_self_contained.py --check
```

Compile it independently:

```text
lake env lean -DwarningAsError=true Erdos625SelfContained.lean
```

The checked source contains 483 local source modules, 86 external imports,
and 91,243 lines. Its normalized-LF SHA-256 (the value printed by the
generator on every platform) is
`bbbfd1867af9996e2aa058defc5bbc020319a5967e5e8b86e693c60f01ee3368`.

## Five-size phase gain

The release root also imports three modules on the five-size phase gain

```text
A_5(delta) = log 2 - F_{S_+}(T_delta) + F_{S_5}(T_delta),
S_+ = {i in Z : i >= -1},  S_5 = {2,...,6},  T_delta = 1 + 2/log 2 - delta,
F_S(T) = inf over real lambda of
         log sum_{i in S} exp(lambda*i - (log 2/2)*i^2) - lambda*T,
```

from the earlier five-size version (`arXiv:2608.30604v2`; superseded by `A_7` in `../manuscript/main.tex`). For every `delta` in
`[0, 1]`:

| Module | Main theorem | Statement |
|---|---|---|
| `Erdos625/FiveSizeEntropyGap.lean` | `entropy_gap` | `A_5(delta) > log(8750/6681)` (`arXiv:2608.30604v2`, Lemma 5.3) |
| `Erdos625/FiveSizePhaseGainSharp.lean` | `log_2605_div_1651_lt_phaseGain5` | `A_5(delta) > log(2605/1651)` |
| `Erdos625/FiveSizePhaseGainCertificate.lean` | `log_169_div_100_lt_phaseGain5` | `A_5(delta) > log(169/100)` (`arXiv:2608.30604v2`, Lemma 5.4) |

The third bound gives the `[0.063, 0.104]` five-size certificate (superseded in the
15-page v3 manuscript by the shifted seven-size certificate `A_7(delta_tilde) > log(391/200)`
in `Erdos625HP/ShiftedSevenSizeCertificate.lean`). These
modules are part of both the modular build and the one-file proof. They do not change
`Erdos625Statement` or the proof of `Erdos625.erdos625`, whose coefficient is
still `(log 2)^2 / 4 * log(200/153)`.

The project directory also retains four superseded midpoint-route modules for
historical comparison:

- `Erdos625/Section12CanonicalBareSkeletonAsymptotic.lean`;
- `Erdos625/Section12ConcreteSignedFirstMoment.lean`;
- `Erdos625/Section12PartialDiagonalAssembly.lean`;
- `Erdos625/Section13GlobalMidpointSeed.lean`.

They are not imported by `Erdos625.lean`, are not members of the 483-module
release closure, and are not needed for `Erdos625.erdos625`.

## Trust boundary

The proof sources contain no `sorry`, `admit`, project-defined axiom,
`unsafe`, `native_decide`, or `implemented_by`. The final theorem's axiom
audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Public cloud replay evidence

The exact standalone file at source commit
`824e4b609466d2e26b216a76ecf103184dac2663` was independently replayed in a
clean Aristotle cloud workspace. The raw download, primary-command stdout,
stderr, and exit-code records, supplementary check output, source and
toolchain revisions, file checksums, and axiom audit are preserved at
immutable public commit
`31bbe00c529a996bdb61b880120d71240172d18f` in
[`replay/aristotle-03e8124e-c359-4219-8b37-442060dae209`](https://github.com/SamPetkov/Erdos/tree/31bbe00c529a996bdb61b880120d71240172d18f/625/formalization/replay/aristotle-03e8124e-c359-4219-8b37-442060dae209).
The current one-file proof differs from that replayed file only by the three
five-size phase-gain modules and the root module's added imports and
documentation; the current file itself has not been replayed in the cloud.
The replay records are not kept on the main branch; they remain available at
that commit.

## Auxiliary library `Erdos625HP` (v3 exact-constant & phase-refinement manuscript)

`Erdos625HP.lean` (together with `Erdos625/HPRouteMarkBound.lean`,
`Erdos625/HPRouteFullCornerDecay.lean`, and the 26 modules in `Erdos625HP/`)
extends the development for the 15-page v3 manuscript without modifying any
existing `Erdos625` proof module or `Erdos625.erdos625`:

### Proved unconditionally (zero external hypotheses)

| Module | Main declarations | Mathematical content |
|---|---|---|
| `Erdos625HP/UnconditionalSecondMomentAndMainTheorem.lean` | `erdos625_mainTheorem_unconditional`, `erdos625_phaseRefinement_unconditional`, `eventually_prop73_and_cor81_upperTails_regimeU`, `eventually_prop73_and_cor81_upperTails_regimeC`, `eventually_lemma72_overlapSum_le`, `eventually_similarRange_pairSum_le` | **Complete zero-hypothesis (`0`-binder) unconditional closures** of both **Main Theorem `(i)–(iv)`** (`erdos625_mainTheorem_unconditional`, including coupling-uniform running-supremum Orlicz `psi_2`, square-exponential moment, and `L^p` bounds) and **Phase Refinement** (`erdos625_phaseRefinement_unconditional`, with `A_7(delta_tilde) ∈ (log(391/200), log 2]`, `(0.080, 0.086)` bounds, moving-corridor `(log n)^8` and coupling-uniform fixed-corridor `(log n)^6` sub-Gaussian exit tails, expectation sandwich, and arbitrary-coupling almost-sure bounds); unconditional `G(n, 1/2)` Lemma 7.2 (`lem:hp-transfer`) fixed-`nu` relevant-pair overlap sum `<= exp(C_ov (log n)^5) E[X̄_k]^2 F_1^ch(nu)` and `<= exp(C_ov (log n)^5) E[Z_k^mk]^2 W(nu)` (`n - m_nu >= n^{1 - c_0}`, `1 <= M`, `c_0 ∈ (0, 1/2)`), unconditional Proposition 7.3 similar-range relevant-pair sum (`n - m_nu < n^{1 - c_0}`), and unconditional Proposition 7.3 Paley–Zygmund rare-seed lower bounds (`>= exp(-C_sm n^{1 - c_0} / log n)`) + Corollary 8.1 quasi-exponential upper tails (`<= exp(-2 n / (log n)^{10})` at `k_co = ceil(r_co) + 16`, `k_ch = ceil(r_ch) + ceil(log n)`, `a_n = 2 n / (log n)^5`) in both `Regime U` (`7 <= M`, `m <= 1`, `delta_- ∈ (x_0, 1 + delta_*]`) and `Regime C` (`8 <= M`, `p1Bar ∈ (0, 1/40]`, `delta_- ∈ (0, delta_*]`, `gamma > 0`) |
| `Erdos625HP/SelectedProfilesAndMaximalPsi2.lean` | `coupling_orliczPsi2_sup_normalizedGap_center_le`, `tendsto_lp_zero_of_orliczPsi2_tendsto_zero`, `coupling_orliczPsi2_and_moments_sup_normalizedGap_sub_quarter`, `existsUnique_windowFiniteGibbsTilt_and_optimizer_bounds_lemma32_ii`, `eventually_window_and_capped_phaseObjective_deriv_and_diff_lemma31`, `eventually_selectedProfiles_prop53_regimeU`, `eventually_selectedProfiles_prop53_regimeC`, `eventually_selectedProfiles_lemma61_and_commonClass_sums_regimeU`, `eventually_selectedProfiles_lemma61_and_commonClass_sums_regimeC` | Main Theorem `(i),(iv)` & Corollary 8.1 coupling-uniform running-supremum Orlicz `psi_2`-norm bound `||sup_{m >= n} |Y_m - E[Y_m]|||_{psi_2} <= 4 (log_2 n)^3 sqrt(log n / n)` (`n >= e^{12}`), general `||Z_n||_{psi_2} -> 0 => E[|Z_n|^p] -> 0` (`1 <= p < infty`), and `1/4`-centered running-supremum `S_n := sup_{m >= n} |Y_m - 1/4|` bounds `||S_n||_{psi_2} <= 4 (log_2 n)^3 sqrt(log n / n) + sup_{m >= n} |E[Y_m] - 1/4| / sqrt(log 2) -> 0`, `E[exp(M S_n^2)] -> 1` (`M >= 0`), and `E[S_n^p] -> 0` (`1 <= p < infty`) under every `G(m, 1/2)` coupling; Section 3 Lemma 3.2(ii) finite-`n` Gibbs tilt `exists!` & `O_M(1/alpha)` optimizer/probability convergence and Lemma 3.1 window/capped `(3.7)` derivative & value-difference bounds; complete unconditional Proposition 5.3(i)–(ii) selected integer profiles `(k_co_vec, k_ch_vec)` (`k_co = ceil(r_co) + 16`, `k_ch = ceil(r_ch) + ceil(log n)`, `log E[Z_k^mk] >= c_Z (log n)^2`, `log E[X̄_{k^ch}] >= c_Z (log n)^3`), unconditional Lemma 6.1(i)–(ii), and Proposition 7.3 scrambled & middle common-class subprofile sums in both `Regime U` (`7 <= M`, `m <= 1`) and `Regime C` (`8 <= M`, `p1Bar ∈ (0, 1/40]`) |
| `Erdos625HP/UnconditionalOneSixteenth.lean` | `erdos625_one_sixteenth`, `erdos625_fourSize_phaseResolved`, `erdos625_lt_min_fourSize` | Full-sequence bound `P(χ(G_n) - ζ(G_n) >= (1/16) n / (log n)^3) -> 1` (`1/16 = 0.0625`), phase-resolved four-size bound with `A_4(delta_n)`, and every `c < ((log 2)^2 / 4) min A_4` |
| `Erdos625HP/InfiniteDualsLowerTailsAndCompleteRegularity.lean` | `orliczPsi2_const_and_add_le`, `orliczPsi2_normalizedGap_sub_quarter_le`, `coupling_tailUnion_chromaticSubCochromatic_sqrt_log_le`, `ae_limsup_chromaticSubCochromatic_and_normalizedGap_le_one`, `abs_infiniteFiniteEntropy_sub_dualValue_le`, `abs_cappedInfiniteFiniteEntropy_sub_cappedDualValue_le`, `exists_pos_eventually_existsUnique_infinitePhaseObjective_zero_logLogCorridor`, `exists_pos_eventually_existsUnique_cappedInfinitePhaseObjective_zero_logLogCorridor`, `eventually_allSupport_corridorRoot_separation_and_prop53_iii`, `eventually_randomGraph_lowerTails_prop41_i`, `eventually_randomGraph_lowerTails_prop41_ii`, `eventually_randomGraph_lowerTails_prop41_iii`, `eventually_condProb_badZComposed_tendsto_zero`, `eventually_lemma71_complete_regularity` | Main Theorem `(i),(iv)` & Corollary 8.1 exact Orlicz `psi_2` constant formula `||c||_{psi_2} = |c| / sqrt(log 2)` and triangle inequality `||X + Y||_{psi_2} <= ||X||_{psi_2} + ||Y||_{psi_2}` on probability spaces (`Integrable`-qualified for general `X, Y`), non-asymptotic `1/4`-centered bound `||Y_n - 1/4||_{psi_2} <= ||Y_n - E[Y_n]||_{psi_2} + |E[Y_n] - 1/4| / sqrt(log 2) <= sqrt(8/3) (log_2 n)^3 / sqrt(n) + |E[Y_n] - 1/4| / sqrt(log 2)` (`n >= 2`), non-asymptotic coupling-uniform fluctuation tail-union bound `P(exists m >= n : |Delta(G_m) - E[Delta(G_m)]| >= sqrt(2(1 + eta)(m - 1) log m)) <= 2 (1/eta + 1/n) n^{-eta}` (`n >= 2`, `eta > 0`), and arbitrary-coupling almost-sure fluctuation envelope `limsup_{n -> infty} |Delta(G_n) - E[Delta(G_n)]| / sqrt(2 n log n) <= 1` and `limsup_{n -> infty} (sqrt(n) / ((log_2 n)^3 sqrt(2 log n))) |Y_n - E[Y_n]| <= 1`; Section 3 Lemma 3.2(i),(iv) `O(1/alpha)` infinite-support finite-to-limiting dual bounds `|F_{n,S_{>= m}}(T) - F_{S_{>= m}}(T)| <= C_dual / alpha` on `[9/4, 9/2]` (`m <= 2`) and `|F_{n,S_{>= 1}}^{=vartheta}(T) - F_{S_{>= 1}}^{=vartheta}(T)| <= (1 - vartheta) C_dual / alpha <= C_dual / alpha` on `K_cap` (`vartheta ∈ [0, 1/20]`), plus Lemma 3.1 strict monotonicity, `exists!` corridor roots, and `(3.6)` `O(log log n / log n)` location for `L_{S_{>= m}}(n, ·) + tau ·` (`m <= 2`) and `L_{S_{>= 1}}^{=vartheta}(n, ·) + tau ·` (`delta_n ∈ [0, delta_*]`, `vartheta ∈ [0, 1/20]`); Section 5.2 `(5.19)` mixed infinite-vs-window (`m_1 <= 2`, `m_2 <= 1`, `7 <= M_2 <= M`), capped-infinite-vs-capped-window, and infinite-vs-capped-window (`8 <= M_2 <= M`, `delta_n ∈ [0, delta_*]`) `O_M(n log log n / (log n)^4)` corridor-root separations, and unconditional Proposition 5.3(iii) `(5.20)` threshold separations (`m <= 1`, `7 <= M' <= M`) with `(m_n, 7)` root ordering `r_{>= m_n}^co < r_co < r_{>= m_n} < r_ch` and `O(log log n / log n)` envelope; Section 4 complete unconditional Proposition 4.1(i)–(iii) `G(n, 1/2)` lower tails (`<= 3 exp(-2 n / (log n)^{10})` eventually); Section 7 `B_pi` bad `z`-composed event `P(A_P ∩ B_P^c) <= varepsilon P(A_P)` (`max_{D ∈ P} |D| <= alpha`) and complete unconditional Lemma 7.1 first- and second-moment regularity assembly (`U_sizes = [alpha - (M + 1), alpha]`, `varepsilon ∈ (0, 1)`) |
| `Erdos625HP/FiniteDualsCorridorRootsAndRegularity.lean` | `orliczPsi2_chromaticSubCochromatic_le`, `orliczPsi2_normalizedGap_le`, `strictMonoOn_div_log_pow_six`, `finiteDeficitResidualScore_bounds`, `abs_windowFiniteEntropy_sub_dualValue_le`, `abs_cappedWindowFiniteEntropy_sub_cappedDualValue_le`, `exists_pos_eventually_existsUnique_windowPhaseObjective_zero_logLogCorridor`, `exists_pos_eventually_existsUnique_cappedWindowPhaseObjective_zero_logLogCorridor`, `eventually_unrestrictedPhaseObjective_deriv_logLogRate`, `eventually_window_and_capped_corridorRoot_separation_logLogRate`, `randomGraphMeasure_partitionColoring_and_marked_inter_crossEvent_eq`, `condProb_heavyCrossPairEvent_le_and_eventually_inv_n`, `eventually_condProb_badTwoClassSplit_tendsto_zero`, `eventually_condProb_manyNearParts_tendsto_zero`, `sq_regularPartitionSum_le_relevantPairs_and_integral_le` | Main Theorem `(i)` & Corollary 8.1 exact Gaussian-constant Orlicz `psi_2`-norm bounds `||Delta(G_n) - E[Delta(G_n)]||_{psi_2} <= sqrt((8/3)(n - 1))` and `||Y_n - E[Y_n]||_{psi_2} <= sqrt(8/3) (log_2 n)^3 / sqrt(n)` (`n >= 2`, from `theta = 3/8`) and `[e^6, infty)` strict monotonicity of `x / (log x)^6` & `x / (log_2 x)^6`; Section 3 finite falling-factorial score bounds `log (alpha)_{(i)} - i log alpha ∈ [-i^2 / alpha, 0]` (`2 i <= alpha`), Lemma 3.2(i),(iv) `O_M(1/alpha)` finite-to-limiting dual bounds `|F_{n,S_{m,M}}(T) - F_{S_{m,M}}(T)| <= (m + M)^2 / alpha` on `(2, 5)` (`m <= 1`, `M >= 7`) and `|F_{n,S_{0,M}}^{=vartheta}(T) - F_{S_{0,M}}^{=vartheta}(T)| <= (1 - vartheta) M^2 / alpha <= M^2 / alpha` on `K_cap` (`M >= 8`, `vartheta ∈ [0, 1/20]`), Lemma 3.1 general-`M` `S_{m,M}` (`m <= 1`, `M >= 7`) and capped `S_{0,M}` (`M >= 8`, `delta_n ∈ [0, delta_*]`, `vartheta ∈ [0, 1/20]`) strict monotonicity, `exists!` corridor roots, `(3.6)` `O(log log n / log n)` location, and `(3.7)` unrestricted derivative `|partial_k(L_{S_+}(n, k) + tau k) - (2 / log 2)(log n)^2| <= K_slope (log n)(log log n)`, plus Section 5.2 `(5.19)` general-`M` unconstrained & capped root separation `((log 2)^2 / 4)(tau_2 - tau_1 + F_2 - F_1) n / (log n)^3 + O_M(n log log n / (log n)^4)`; Section 7 Lemma 7.1 `G(n, 1/2)` cross-edge conditioning & mark-invariance, `E_pi` heavy cross-pair `<= C(|P|, 2) 2^{2 a} 2^{-m_prod} P(A_P)` & `<= (1/n) P(A_P)` (`m_prod = ceil(7 log_2 n)`), `C_pi^c` bad two-class split `<= varepsilon P(A_P)`, `D_pi^c` many-near-parts `<= varepsilon P(A_P)` (`c_D > 0`), and regular-partition square reductions `(Z^{ch})^2 <= sum_{Pi_rel(floor(c_full)_+)} 1_{A_pi ∩ A_{pi'}}` & `Z^2 <= sum_{Pi_rel(floor(2 c_half)_+)} 1_{A_pi^co ∩ A_{pi'}^co}` |
| `Erdos625HP/PhaseCoverAndSecondMomentAssembly.lean` | `exp_quad_eq_gaussian_integral`, `blockUniform_sqExpMoment_le_of_const_oscillation`, `sqExpMoment_chromaticSubCochromatic_le`, `sqExpMoment_normalizedGap_le`, `dualValue_Sge1_eq_at_sge1Tilt`, `cappedDualValue_Sge1_concave_strictMono_and_eq_dualValue`, `continuousOn_and_tendstoUniformlyOn_cappedDualValue_Sge1_zero`, `exists_finite_phase_cover_dual_budget`, `relevantPair_part_trichotomy_and_overlap_gap`, `crossEdge_binom_pow_le`, `finset_sum_prod_pow_div_factorial_le_exp_and_tsum_eq`, `eventually_overlapKernel_le_exp_polylog5`, `eventually_similarRange_geom_ratio_le_half` | Main Theorem `(i)` & Corollary 8.1 exact Gaussian Laplace identity and Gaussian-threshold `(1 - 2 theta)^{-1/2}` square-exponential (`psi_2`) moment bounds (`theta ∈ [0, 1/2)`) across `r >= 1` uniform blocks and for `Delta(G_n)` and `Y_n` (`n >= 2`); Lemma 3.2(i),(iv) exact `S_{>= 1}` dual value at `lambda_{S_{>= 1}}(T)` (`T > 1`), concavity on `[0, 1)` & strict monotonicity on `[0, p_{S_{>= 1}, T}(1)]` & optimizer identity `F_{S_{>= 1}}^{=p_{S_{>= 1}, T}(1)}(T) = F_{S_{>= 1}}(T)` (`T > 2`), and joint continuity & uniform boundary limit `F_{S_{>= 1}}^{=vartheta} -> F_{S_{>= 2}}` as `vartheta -> 0+` on `K_cap`; Section 9 constructive `(J + 3)`-interval phase cover `[0, 1) = I_0 ∪ (⋃_j I_j) ∪ I_tr ∪ I_main` with all Proposition 4.1(iii), Regime U/C, and `< 2 eta / 3` dual-gap budgets verified unconditionally; Section 7 `Pi_rel` part trichotomy (`Identical`, `Scrambled`, `<= 2 B` `Exceptional`), overlap spectral gap `¬(2 M + 4 < |D ∩ D'| < u_- - 1)` & `s_2 <= (4 M + 6) t + 2 a B`, unconditional Lemma 7.1 cross-edge majorant (`3 <= z <= n`), Lemma 7.2 Poisson series identity & `exp(C_ov (log n)^5)` overlap-kernel bound, and Proposition 7.3 similar-range geometric ratio `<= 1/2` eventually (`z >= phaseNat n - (3 M + 4)`) |
| `Erdos625HP/CommonClassMiddleAndSecondMoment.lean` | `exists_vertexDeletion_chromaticSubCochromatic_eq_two`, `rpow_le_mul_exp_of_pos`, `centralMoment_chromaticSubCochromatic_le`, `centralMoment_normalizedGap_le`, `cgf_normalizedGap_bounds`, `log_unmarkedDiagonalWeight_le`, `log_unmarkedDiagonalWeight_self_ge`, `partialDiagonalWeight_and_unmarked_scrambled_le`, `sum_scrambled_partial_and_unmarkedDiagonalWeight_le_exp` | Corollary 8.1 sharpness witness (`K_4` vs `K_3 ⊔ K_1`, achieving `|(χ(G) - ζ(G)) - (χ(H) - ζ(H))| = 2`), non-asymptotic central `L^p` bounds `E[|Delta(G_n) - E[Delta(G_n)]|^p] <= 2 ((p / e)(n - 1))^{p/2}` and `E[|Y_n - E[Y_n]|^p] <= 2 (p (log_2 n)^6 / (e n))^{p/2}` (`n >= 2`, `1 <= p < infty`), and CGF sandwich `0 <= log E[e^{lambda Y_n}] - lambda E[Y_n] <= lambda^2 (log_2 n)^6 / (2 n)`; Appendix C finite non-Stirling bounds on `log F_1^ch(nu)` and `log F_1^ch(k)`; Proposition 7.3 scrambled-range pointwise and subprofile-sum bounds `sum_{nu in S} W(nu) <= sum_{nu in S} F_1^ch(nu) <= exp(2 (sum_i k_i)^2 / mu_a)` |
| `Erdos625HP/SubgaussianConcentrationAndMarkProbability.lean` | `blockMean_sq_center_le`, `blockUniform_variance_mgf_and_tails_of_const_oscillation`, `randomGraph_variance_mgf_and_tails_of_const_vertexDeletionOscillation`, `variance_cochromatic_and_chromatic_le`, `chromaticSubCochromatic_hasVertexDeletionOscillation`, `variance_chromaticSubCochromatic_le`, `variance_normalizedGap_le`, `mgf_chromaticSubCochromatic_center_le`, `randomGraph_abs_chromaticSubCochromatic_sub_mean_ge_le`, `mgf_normalizedGap_bounds`, `randomGraph_abs_normalizedGap_sub_mean_ge_le`, `randomGraphMeasure_partitionMarkedEvent_eq`, `randomGraphMeasure_partitionCocoloringEvent_eq_two_pow_mul`, `randomGraphMeasure_partitionCocoloringEvent_inter_le_two_pow_sub_common`, `randomGraphMeasure_partitionCocoloringEvent_inter_le_two_pow_sub_inter`, `scrambledPart_heavyOverlap_card_and_vertex_sum_le`, `summable_subgaussianGapTail`, `summable_phaseRefinementSubgaussianTail` | Section 1 `(1.2)` conditional Popoviciu variance `Var(Y) <= c^2 r / 4`, Hoeffding MGF `<= exp(c^2 r lambda^2 / 8)`, and one-/two-sided `exp(-2 t^2 / (c^2 r))` tails across `r >= 1` uniform product blocks and `n - 1` active `G(n, 1/2)` vertex-star blocks (`Var(ζ(G_n)), Var(χ(G_n)) <= (n - 1) / 4`); Corollary 8.1 oscillation-`2` bounds for `Delta(G_n) = χ(G_n) - ζ(G_n)` and `Y_n`: `Var(Delta(G_n)) <= n - 1`, `Var(Y_n) <= (log_2 n)^6 / n`, `E[exp(lambda(Delta - E[Delta]))] <= exp((n - 1) lambda^2 / 2)`, `P(|Delta - E[Delta]| >= t) <= 2 exp(-t^2 / (2(n - 1)))`, `exp(lambda E[Y_n]) <= E[exp(lambda Y_n)] <= exp(lambda E[Y_n]) exp(lambda^2 (log_2 n)^6 / (2 n))`, and `P(|Y_n - E[Y_n]| >= u) <= 2 exp(-u^2 n / (2 (log_2 n)^6))` (`n >= 2`); Section 7 `(7.1)` exact `G(n, 1/2)` mark-measure identity `P(A_P^co) = 2^{|P|} P(A_P)` (`min_{B in P} |B| >= 2`) and compatible-pair mark bounds `P(A_P^co ∩ A_Q^co) <= 2^{|P| + |Q| - |P ∩ Q|} P(A_P ∩ A_Q)`; Lemma 7.2 scrambled-part heavy-overlap bounds (`|B| <= 2(alpha - u) + 2 <= 2 M + 4` and `sum_{|B| >= 2} |B| <= 2(u - z) <= 4 M + 6`); `Summable` of `exp(-c n / (log_2 n)^6)` (`c > 0`) and `exp(-n (log log n)^2 / (2 (log n)^8))` |
| `Erdos625HP/UnconditionalSplittingAndQuasiExpTail.lean` | `splitCost_eq_natCeil_sub_one_and_le_two_mul_div`, `exists_finpartition_unconditional_split_large_parts`, `exists_unconditional_bounded_coloring_partition_of_maxDisjointIndepGe_le`, `exists_unconditional_bounded_cocoloring_partition_of_maxDisjointIndepGe_le`, `randomGraph_chromaticNumberAtMost_le_of_unconditional_splitting`, `randomGraph_cochromaticNumberAtMost_le_of_unconditional_splitting`, `roundedWindowProfile_conservation_and_error`, `universalAllowance_isLittleO`, `quasiExpTail_isBigO_polylogTail`, `summable_quasiExpTail`, `randomGraph_packingPair_gt_universalShift_le` | Unconditional Lemma 1.1 splitting arithmetic `ceil(m / (u - 1)) - 1 <= 2 floor(m / u)` (`u >= 2`, `m >= 1`), `(k + 2d)`-coloring and `(k + 4d)`-cocoloring bounded-size refinements (eliminating `alpha(G), omega(G) <= 2(u - 1)`), and finite Proposition 4.1(i) lower-tail reductions; Proposition 5.3 two-coordinate `{3, 4}` integer profile rounding (`sum_i k_i = k`, `sum_i (alpha - i) k_i = n`, and `|k_i - k p_i| <= (m + M + 4) * M + 1`); universal allowance `2 n / (log n)^5 = o(n log log n / (log n)^4)`, `exp(-2 n / (log n)^{10}) = O(n^{-3/2} (log n)^{beta + 5/2})`, `Summable` of `exp(-2 n / (log n)^{10})`, and `G(n, 1/2)` two-sided packing union tail `P({D_u(G_n) > mu_u + n / (log n)^5} ∪ {D_u(G_n^c) > mu_u + n / (log n)^5}) <= 2 exp(-2 n / (log n)^{10})` |
| `Erdos625HP/ShiftedSevenSizeCertificate.lean` | `partitionFn_shiftSupportOne`, `dualValue_shiftSupportOne`, `log_391_div_200_lt_phaseGain7`, `continuousOn_phaseGain7`, `phaseGain7_nonconstant`, `lowerPhaseCoeff7_gt_0080`, `upperPhaseCoeff7_lt_0086`, `tendstoUniformlyOn_dualValue_S0M_Sge1`, `continuousOn_phiInf`, `strictAntiOn_phiInf`, `existsUnique_criticalPhase_x0`, `criticalPhaseX0_bounds_and_sign` | Lemma 3.2(iii) Gaussian shift equivariance & uniform support limit `F_{S_{0,M}} -> F_{S_{>= 1}}`; Lemma 5.1 six-cell rational certificate `A_7(delta_tilde) > log(391/200)`, continuity & strict nonconstancy `A_7(1 + delta_*) < 0.672 < 0.689 < A_7(delta_*)`, `0.080 < c_7` and `C_7 < 0.086`; Lemma 5.2(i) continuity & strict decrease of `phi_infty` on `[0, 1 + delta_*]` and unique critical phase `x_0 ∈ (0.0290, 0.0291)` |
| `Erdos625HP/CappedAndGeneralRateCertificate.lean` | `existsUnique_capThresholdTheta_pos`, `capThresholdTheta_lt_one_div_40`, `capThresholdTheta_x0_eq_p1Inf`, `capThresholdTheta_lt_p1Inf_of_lt_x0`, `phiInfAux_capThresholdTheta_add_target`, `strictMonoOn_capThresholdTheta`, `continuousOn_capThresholdTheta`, `existsUnique_s0mTilt`, `gibbsProbS0M_one_lt_p1Inf`, `commonClass_rate_bound_S0M`, `convexOn_mul_log_add_quad`, `capped_rate_bound_of_tail_rate`, `commonClass_capped_rate_bound_S0M`, `tendstoUniformlyOn_cappedDualValue_S0M_Sge1` | Lemma 5.2(i) realizability cap `theta(delta)` (`capThresholdTheta`, extended by `0` outside `[0, x_0]`), continuity, strict monotonicity, `< 1/40`, `< p_{1,infty}` on `[0, x_0)`, and exact shift identity `g(theta(delta_1)) + (log 2 / 2)(T_{delta_2} - 1) = (log 2 / 2)(delta_1 - delta_2)` on `(0, x_0]`; Lemma 5.2(ii) unconstrained (`M >= 7`) and capped (`M >= 8`) common-class rate bounds `<= -2 c_* R (1 - R)`; Lemma 3.2(iv) joint compact-uniform convergence of `cappedDualValue` (`[0, 1/20] × K_cap`, extended by `0` outside its domain) as `M -> infty` |
| `Erdos625HP/SelfContainedSecondMomentCore.lean` | `capThresholdTheta_biLipschitz_bounds`, `profileFree_commonClass_entropy_term_le`, `two_rpow_neg_half_alphaZero_sub_one`, `crossEdge_sum_sq_le`, `two_mul_crossEdge_sum_ge`, `card_zeroOneMatrices_mul_factorials_le`, `factorial_le_residual_mul_prod_choose`, `transmuted_factorial_ratio_le`, `scrambledRange_commonClass_sum_le`, `disjoint_scrambled_extra_pairs_ge` | Lemma 5.2(i) sharp linear bounds `(40/41)(log 2) delta <= theta(delta) <= (log 2) delta` on `[0, x_0]`; Appendix C profile-free entropy bound `2 p log p - 2(p - y) log(p - y) - y log y - y <= y log(e / y)`; Section 7 `G(n, 1/2)` second-moment core: exact center identity `2^{-(alpha_0 - 1)/2} = (2 log_2 n) / (e n)`, `z`-composed cross-edge bounds, `0`–`1` matrix stub-pairing bound `<= r_1! / (prod_i sigma_i! prod_j tau_j!)`, peeling & transmuted factorial-ratio bounds, scrambled box-sum bound `<= exp(2 k^2 / mu_a)`, and disjoint similar-range extra-edge lower bound `>= s * z.choose 2` |
| `Erdos625HP/PairMomentAndPhaseAsymptotics.lean` | `integral_independentSetCount_mul_sub_one_le`, `randomGraph_independentSetCount_ge_two_le`, `randomGraph_lowerTailExceptional_le`, `exists_uniform_phaseExpansion_and_adjacent_bounds`, `lowerTailExceptionalBound_phaseNat_add_two_isBigO`, `summable_polylog_three_halves`, `summable_lowerTailExceptionalBound_phaseNat_add_two`, `gibbsProb_shiftSupportOne`, `gibbsMean_shiftSupportOne`, `unique_gibbsMean_shiftSupportOne_and_prob_eq`, `dualValue_diff_shiftSupportOne`, `eventually_mu_vertexCap_le_rpow_neg_five_halves`, `concentrationAllowance_isLittleO`, `phaseGain7_le_log_two` | Retained `v6` pair-moment bound `E[X_u(X_u - 1)] <= mu_u^2 exp(J_u) + mu_u(exp(K_u) - 1)` (`1 <= u < n`), Markov pair tail, and four-event exceptional union bound `<= E_u`; Lemma 2.1 all six uniform phase expansions across `delta_n ∈ [0, 1)` (including phase-retaining `n^{1+delta_n}` and `n^{2+delta_n}` lower bounds on `mu_{alpha-1}, mu_{alpha-2}`), `E_{alpha+2}(n) = O(n^{-3/2} (log n)^{beta + 5/2})`, and `Summable` of `n^{-3/2}(log n)^gamma` and `E_{alpha+2}`; Lemma 3.2(iii) Gibbs probability & mean shift equivariance (`p_{S+1, lambda}(i+1) = p_{S, lambda - log 2}(i)`, `M_{S+1}(lambda) = M_S(lambda - log 2) + 1`, and mean-matched `p_{S+1, T+1}(i+1) = p_{S, T}(i)` at unique `lambda_S(T)`); Appendix C asymptotic vertex-cap bound `mu_w(s) <= n^{-5/2}` (`w <= 2^{-(M+5)} n`); `a_n = 2 n^{1 - c_0/3} = o(n log log n / (log n)^4)` and `A_7(td) <= log 2` |
| `Erdos625HP/BoundedLowerTailsAndMomentCore.lean` | `pow_mul_exp_neg_le_factorial`, `factorial_le_exp_mul_succ_mul_pow_mul_exp_neg`, `factorial_div_le_one_sub_rpow_mul_exp_neg`, `chromaticNumberNat_le_card`, `profileColoringExpectation_toReal_le_exp_mul_succ_mul_exp`, `log_partialDiagonalWeight_le`, `log_partialDiagonalWeight_self_ge`, `randomGraph_maxDisjointHomogeneousEq_ge_le_entropy`, `eventually_randomGraph_homogeneousPacking_alpha_tail`, `eventually_randomGraph_homogeneousPacking_alpha_sub_one_tail` | Elementary Stirling-free factorial inequalities `(1.1)` (`m^m e^{-m} <= m! <= e(m+1) m^m e^{-m}` and `n! / ((n-s)! n^s) <= (1 - s/n)^{-(n-s+1)} e^{-s}`); `χ(G) <= |V|` (paired with `cochromaticNumber_le_chromaticNumber`); Section 4 finite first-moment bound `E[X̄_k] <= e(n+1) exp(L_k)`; Appendix C finite non-Stirling bounds on `log W(nu)` and `log W(k)`; finite homogeneous-packing entropy bound and unconditional Proposition 4.1(ii)–(iii) `G(n, 1/2)` packing tails `P(H_alpha(G_n) >= ceil(8 n ell / L^2)) <= exp(-200 n ell^2 / L^2)` and `P(H_{alpha-1}(G_n) >= ceil(thetaBar n / (alpha - 1))) <= exp(-thetaBar gamma n)` |
| `Erdos625HP/HomogeneousPackingAndBorelCantelli.lean` | `coloring_card_filter_eq_le_maxDisjointHomogeneousEq`, `cocoloring_card_filter_eq_le_maxDisjointHomogeneousEq`, `randomGraph_maxDisjointHomogeneousEq_ge_le_factorial`, `randomGraph_maxDisjointHomogeneousEq_ge_le`, `ae_eventually_notMem_of_summable_measureReal`, `aemeasurable_of_map_eq_randomGraphMeasure` | Lemma 1.2 homogeneous exact-size packing `H_u(G)` (`maxDisjointHomogeneousEq`, via `IsHomogeneousSet` and `IsDisjointHomogeneousFamilyEq`), size-`u` class-count bounds for colorings and cocolorings, exact factorial & exponential `G(n, 1/2)` tail bounds `(2 mu_u)^m / m! * exp(-(u^2 / n) * m.choose 2)`, first Borel–Cantelli lemma for summable `measureReal` event sequences, and `AEMeasurable` marginal transfer |
| `Erdos625HP/DisjointLargeSetOscillation.lean` | `maxDisjointIndepGe_le_independentSetCount`, `integral_maxDisjointIndepGe_le_mu`, `maxDisjointIndepGe_hasVertexDeletionOscillation`, `randomGraph_maxDisjointIndepGe_gt_mu_add_le_exp`, `exists_bounded_coloring_partition_of_maxDisjointIndepGe_le`, `exists_bounded_cocoloring_partition_of_maxDisjointIndepGe_le` | Lemma 1.1 disjoint large-set packings `D_u(G) <= X_u(G)`, `E[D_u] <= mu_u`, unit vertex-deletion oscillation, McDiarmid upper tail `<= exp(-2 t^2 / (n - 1))`, and bounded-size `(k + d)`-coloring and `(k + 2d)`-cocoloring class splitting |
| `Erdos625HP/FourSizeSharpCertificate.lean` | `log_4207_div_2500_lt_phaseGain4`, `continuousOn_phaseGain5`, `phaseGain5_one_lt_phaseGain5_zero` | Rational certificate `A_4(delta) > log(4207/2500)` on `[0, 1]`, continuity of `A_5` and `A_4` on `[0, 1]`, and strict nonconstancy `A_5(1) < A_5(0)` |
| `Erdos625HP/PhaseConstants.lean` | `lowerPhaseCoeff_gt_0063`, `upperPhaseCoeff_lt_0104`, `lowerPhaseCoeff_add_upperPhaseCoeff` | Uniform five-size bounds `0.063 < c_5` and `C_5 < 0.104`, plus `c_5 + C_5 = (log 2)^3 / 2` |
| `Erdos625HP/ConcreteCochromaticLowerBound.lean` | `randomGraphMeasure_phaseCochromaticLowerIndex_lt_cochromaticNumber_tendsto_one`, `tendsto_unrestricted_sub_cocoloringRoot_div_baseScale` | Section 4 full-sequence unrestricted lower bound `P(ζ(G_n) > k_ζ^-(n)) -> 1` and root separation `(r_+ - r_+^co) / (n / (log n)^3) -> (log 2)^3 / 4` |
| `Erdos625HP/ConcreteTwoSidedInstantiation.lean` | `exists_pos_eventually_existsUnique_fiveSizePhaseObjective_zero_logLogCorridor`, `exists_concrete_fiveSize_twoSided_location_error` | Eventual strict monotonicity, existence, and uniqueness (`∃!`) of the five-size corridor roots `r_5^co(n), r_5(n)`, concrete thresholds `k_co, k_ch` and allowances `a_n, b_n`, and both two-sided threshold separations `(A)` |
| `Erdos625HP/CochromaticLowerTail.lean` | `randomGraphMeasure_cochromaticNumberAtMost_le_two_pow_mul_box_add_two_mu` | Finite cochromatic first-moment reduction (including singletons and complementation) |
| `Erdos625/HPRouteMarkBound.lean`, `Erdos625/HPRouteFullCornerDecay.lean`, `Erdos625HP/FullCornerSharp.lean`, `Erdos625HP/FiveSizeRateBound.lean`, `Erdos625HP/Amplification.lean` | `natCard_compatiblePairSignAssignments_le_two_pow_sub_common`, `fiveSizeRate_le_neg_div_10000`, `cochromaticNumber_hasVertexDeletionOscillation`, `chromaticNumberNat_hasVertexDeletionOscillation` | Compatible-mark bound `2^(|A|+|B|-ℓ)`, marked and unmarked full-corner recurrences, five-size rate bound (`R log R + (log 2 / 2) J <= -(1 - R) / 10000`), and unit vertex-deletion oscillation of `ζ` and `χ` |

### Proved as implications from stated hypotheses

| Module | Main declarations | Stated hypotheses -> conclusion |
|---|---|---|
| `Erdos625HP/FullCornerSharp.lean` | `fullCornerWeight_le_pow_of_sharp_mu_cap`, `unmarkedFullCornerWeight_le_pow_of_sharp_mu_cap` | Per-step ratio cap `<= rho` -> `B(h), B^ch(h) <= rho^(sum_i h_i)` |
| `Erdos625HP/ConcreteTwoSidedInstantiation.lean` | `hp_cochromatic_upperTail_of_secondMoment_seed`, `hp_chromatic_upperTail_of_secondMoment_seed`, `concrete_twoSided_phase_and_uniform_gap_of_hp_seeds` | The `G(n, 1/2)` rare-seed probability lower bounds (obtained in the manuscript from Proposition 7.3 via Paley–Zygmund) -> Corollary 8.1 amplification upper tails and the five-size `[0.063, 0.104]` two-sided theorem |
| `Erdos625HP/ShiftedSevenSizeCertificate.lean` | `shifted_twoSided_phase_and_0080_0086_gap_tendsto_one`, `sharp_constant_quarter_along_subsequence_of_window_thresholds` | Shifted seven-size / `M`-window threshold inputs `(A)`, `(B)`, `(C)` -> Section 9 convergence-in-probability assembly of the phase-resolved `A_7(delta_tilde_n)` & `[0.080, 0.086]` Phase Refinement and subsequence `1/4` limit |
| `Erdos625HP/CappedAndGeneralRateCertificate.lean` | `fullSequence_sharpGapConstant_of_finite_phase_cover` | Section 9 finite phase cover of `[0, 1)` + localized per-piece threshold separations and tail bounds -> full-sequence deviation probability bound `P(|((log_2 n)^3 / n)(χ(G_n) - ζ(G_n)) - 1/4| > varepsilon) <= C_varepsilon E(n)` along all integers |
| `Erdos625HP/HomogeneousPackingAndBorelCantelli.lean` | `ae_eventually_mem_of_summable_compl`, `ae_eventually_twoSidedGap_of_summable_compl`, `ae_tendsto_normalizedGap_of_summable_failures` | Summable single-`n` failure probabilities at rational/reciprocal tolerances -> almost-sure eventual two-sided gap bounds and almost-sure convergence `((log_2 n)^3 / n)(χ(G_n) - ζ(G_n)) -> c` under every joint coupling of `(G_n)` with marginals `G(n, 1/2)` |
| `Erdos625HP/BoundedLowerTailsAndMomentCore.lean` | `tendsto_integral_abs_sub_rpow_normalizedGap_of_polylog_tail`, `tendsto_expected_normalizedGap_of_polylog_tail` | Single-`n` deviation tail `O_varepsilon(n^{-3/2} (log n)^{beta + 5/2})` (`beta = 2 / log 2 + 1 / 2`) -> `L^p` convergence `E[|((log_2 n)^3 / n)(χ(G_n) - ζ(G_n)) - 1/4|^p] -> 0` for every `1 <= p < infty` and expectation limit `((log_2 n)^3 / n) E[χ(G_n) - ζ(G_n)] -> 1/4` |
| `Erdos625HP/PairMomentAndPhaseAsymptotics.lean` | `eventually_partialDiagonalWeight_subprofile_le_exp_neg_half`, `eventually_unmarkedDiagonalWeight_subprofile_le_exp_neg_half`, `regime_cochromatic_and_chromatic_upperTail_of_secondMoment_seed`, `phaseRefinement_expectation_and_ae_of_polylog_tail` | Proposition 5.3(ii) profile mass (`sum_i u_i k_i = n`) and first-moment lower bounds (`E[Z_k^mk] >= exp(c_Z (log n)^2)`, `E[X̄_{k^ch}] >= exp(c_Z (log n)^3)`) -> Lemma 6.1(ii) asymptotic decay `W(nu), F_1^ch(nu) <= exp(-(n - m_nu)/2)` when `n - m_nu <= 2^{-(M+5)} n`; retained polynomial-tail Corollary 8.1 and Phase Refinement assemblies (`v6`) |
| `Erdos625HP/UnconditionalSplittingAndQuasiExpTail.lean` | `regime_cochromatic_and_chromatic_upperTail_quasiExp_of_secondMoment_seed`, `tendsto_mgf_normalizedGap_of_quasiExp_tail`, `mainTheorem_ae_lp_expectation_and_mgf_of_quasiExp_tail`, `phaseRefinement_expectation_and_ae_of_quasiExp_tail` | General-regime Paley–Zygmund + Proposition 7.3 rare-seed lower bounds `>= exp(-C_sm n^{1 - c_0} / log n)` (`c_0 = min(delta_- / 2, 1/60)`) -> Corollary 8.1 quasi-exponential upper tails `P(ζ(G_n) > k_co + 2 n / (log n)^5), P(χ(G_n) > k_ch + 2 n / (log n)^5) <= exp(-2 n / (log n)^{10})`; single-`n` quasi-exponential deviation tail `O_varepsilon(exp(-2 n / (log n)^{10}))` -> MGF convergence `E[e^{t Y_n}] -> e^{t/4}` for all `t ∈ R` and full Main Theorem assembly (almost-sure convergence under every coupling, `L^p` convergence for `1 <= p < infty`, expectation `(1/4 + o(1)) n / (log_2 n)^3`, and MGF convergence); shifted seven-size `O(exp(-2 n / (log n)^{10}))` exit tail -> `O(log log n / log n)`-rate Phase Refinement two-sided expectation sandwich `((log n)^3 / n) E[χ(G_n) - ζ(G_n)] ∈ I_n` and `[0.080, 0.086] · n / (log n)^3` bounds in expectation and almost surely under every `G(n, 1/2)` coupling |
| `Erdos625HP/SubgaussianConcentrationAndMarkProbability.lean` | `subgaussian_tail_and_mgf_of_tendsto_expected_normalizedGap`, `mainTheorem_subgaussian_tail_ae_lp_expectation_and_mgf`, `phaseRefinement_subgaussian_tail_expectation_and_ae` | Expectation convergence `E[Y_n] -> 1/4` (or the `O_varepsilon(exp(-2 n / (log n)^{10}))` finite-phase-cover bound) -> Corollary 8.1 oscillation-`2` sub-Gaussian bootstrap `P(|Y_n - 1/4| > varepsilon) <= 2 exp(-vartheta^2 varepsilon^2 n / (2 (log_2 n)^6))` eventually (`varepsilon > 0`, `vartheta ∈ (0, 1)`), 1-line CGF squeeze `E[e^{t Y_n}] -> e^{t/4}`, and complete Main Theorem assembly (`Var(χ(G_n) - ζ(G_n)) <= n - 1`, non-asymptotic mean tail, sub-Gaussian `1/4` tail, arbitrary-coupling a.s., `L^p`, expectation, and MGF convergence); shifted seven-size `O(exp(-2 n / (log n)^{10}))` exit tail -> widened `varepsilon_n := tilde_varepsilon_n + (1 + log log n) / log n = O(log log n / log n)` Phase Refinement assembly with sub-Gaussian exit tail `<= 2 exp(-n (log log n)^2 / (2 (log n)^8))` eventually, expectation sandwich, and `[0.080, 0.086] · n / (log n)^3` bounds in expectation and almost surely |
| `Erdos625HP/CommonClassMiddleAndSecondMoment.lean` | `tendstoUniformlyOn_cgf_and_mgf_normalizedGap`, `eventually_commonClass_subprofile_le_regimeU`, `eventually_commonClass_subprofile_le_regimeC`, `eventually_middleRange_commonClass_sum_small_regimeU`, `eventually_middleRange_commonClass_sum_small_regimeC`, `mainTheorem_v9_complete` | Expectation convergence `E[Y_n] -> 1/4` -> compact-uniform CGF and MGF convergence `log E[e^{t Y_n}] -> t/4` and `E[e^{t Y_n}] -> e^{t/4}` on `[-T, T]`; Proposition 5.3 profile mass (`sum_j u_j k_j = n`), coordinate ratios (`|k_j / K - p^*_{j+1}| <= C_p log log n / log n`), and `1 <= E[Z_k^mk]` / `1 <= E[X̄_k]` -> complete asymptotic Lemma 6.1(i) (`W(nu), F_1^ch(nu) <= exp(-c_W m_nu) <= exp(-c_W n / (log n)^3)` for `m_nu >= n / (log n)^3` and `n - m_nu > 2^{-(M+5)} n`) and Proposition 7.3 `exp(C_ov (log n)^5)`-weighted middle-range subprofile sums `< varepsilon` in both `Regime U` (`M >= 7`) and `Regime C` (`M >= 8`); v9 Main Theorem `(i)–(iv)` synthesis |
| `Erdos625HP/PhaseCoverAndSecondMomentAssembly.lean` | `eventually_threeRange_secondMoment_and_paleyZygmund`, `phaseRefinement_v10_complete`, `mainTheorem_v10_complete` | Proposition 7.3 three-range decomposition (`W_scr <= exp(n^{1 - c_0} / log n)` and `exp(C_ov (log n)^5) W_mid <= 1` weighted by `2 exp(C_ov (log n)^5)`, plus `similar` (`z >= phaseNat n - (3 M + 4)`) weighted by `2^{n^{1 - c_0} / (phaseNat n - (M + 1))} exp(C_sim (log n)^5)` and extra-edge `2^{-s z.choose 2}`) -> `exists C_sm > 0` (`C_sm = 4` in proof) with `E[Z^2] <= exp(C_sm n^{1 - c_0} / log n) (E Z)^2` and Paley–Zygmund lower bound `P(Z > 0) >= exp(-C_sm n^{1 - c_0} / log n)`; shifted seven-size `O(exp(-2 n / (log n)^{10}))` exit tail -> complete v10 Phase Refinement (`0.080 < c_7`, `C_7 < 0.086`, moving-corridor `<= 2 exp(-n (log log n)^2 / (2 (log n)^8))` exit tail, expectation sandwich, and fixed-corridor `P(((log n)^3 / n) Delta(G_n) ∉ [c', C']) <= 2 exp(-vartheta^2 eta_0^2 n / (2 (log n)^6))` tail + expectation + arbitrary-coupling a.s. for all `c' < c_7`, `C' > C_7`, `vartheta ∈ (0, 1)`); finite-phase-cover `O_varepsilon(exp(-2 n / (log n)^{10}))` bound -> complete v10 Main Theorem `(i)–(iv)` synthesis including `(1 - 2 theta)^{-1/2}` square-exponential moments |
| `Erdos625HP/FiniteDualsCorridorRootsAndRegularity.lean` | `eventually_coupling_tailUnion_of_subgaussian_marginals`, `phaseRefinement_v11_complete`, `mainTheorem_v11_complete` | Marginal sub-Gaussian tails `P(G_m ∈ Bad_m) <= 2 exp(-vartheta_1^2 a m / (2 (log m)^6))` (`a > 0`, `∀ vartheta_1 ∈ (0, 1)`) -> single coupling-uniform threshold `N` (prior to `∀ Ω ℙ G`) giving `P(exists m >= n : G_m ∈ Bad_m) <= 2 exp(-vartheta^2 a n / (2 (log n)^6))` for all `n >= N` under every joint coupling of `(G_m)_{m >= 2}` (`vartheta ∈ (0, 1)`); shifted seven-size `O(exp(-2 n / (log n)^{10}))` exit tail -> complete v11 Phase Refinement upgrading v10 under every joint coupling `(Ω, ℙ, G)` with eventual `P(exists m >= n : ((log m)^3 / m) Delta(G_m) ∉ [c', C']) <= 2 exp(-vartheta^2 eta_0^2 n / (2 (log n)^6))` and almost-sure bounds; finite-phase-cover `O_varepsilon(exp(-2 n / (log n)^{10}))` bound -> complete v11 Main Theorem `(i)–(iv)` synthesis upgrading v10 with `(i)` `sqrt(8/3)` Orlicz `psi_2`-norm bounds and `(iii)` eventual `P(exists m >= n : |Y_m - 1/4| > varepsilon) <= 2 exp(-vartheta^2 varepsilon^2 n / (2 (log_2 n)^6))` + almost-sure convergence under every joint coupling `(Ω, ℙ, G)` |
| `Erdos625HP/InfiniteDualsLowerTailsAndCompleteRegularity.lean` | `tendsto_sqExpMoment_one_of_orliczPsi2_tendsto_zero`, `phaseRefinement_v12_complete`, `mainTheorem_v12_complete` | Orlicz `psi_2`-norm convergence `||Z_n||_{psi_2} -> 0` (with eventual nonemptiness of `{s > 0 : Integrable ... ∧ E[exp(Z_n^2 / s^2)] <= 2}`) -> eventual integrability and `E[exp(M Z_n^2)] -> 1` for every `M >= 0`; shifted seven-size `(m_n, 7)` Corollary 8.1 upper-tail input `P({ζ(G_n) > k_co + 2 n / (log n)^5} ∪ {χ(G_n) > k_ch + 2 n / (log n)^5}) <= C_up exp(-2 n / (log n)^{10})` (discharging lower-tail and root-separation obligations internally via unconditional Proposition 4.1(i) and Proposition 5.3(iii)) -> complete v12 Phase Refinement with coupling-independent `∃ N : ℕ` placed outside `∀ {Ω} ℙ G` for `P(exists m >= n : ((log m)^3 / m) Delta(G_m) ∉ [c', C']) <= 2 exp(-vartheta^2 eta_0^2 n / (2 (log n)^6))` (`c' < c_7`, `C' > C_7`, `vartheta ∈ (0, 1)`); finite-phase-cover `O_varepsilon(exp(-2 n / (log n)^{10}))` deviation bound -> complete v12 Main Theorem `(i)–(iv)` synthesis upgrading v11 with `(i)` non-asymptotic `2 (1/eta + 1/n) n^{-eta}` tail-union and almost-sure `sqrt(2 n log n)` fluctuation bounds, `(iii)` coupling-independent `∃ N : ℕ` placed outside `∀ {Ω} ℙ G`, and `(iv)` `||Y_n - 1/4||_{psi_2} <= sqrt(8/3) (log_2 n)^3 / sqrt(n) + |E[Y_n] - 1/4| / sqrt(log 2) -> 0` and `E[exp(M (Y_n - 1/4)^2)] -> 1` (`M >= 0`) |

All conditional bridge theorems in the table above are retained intact, and
every profile, first-moment, common-class, second-moment, and upper-tail
hypothesis in Sections 5–9 is discharged unconditionally in
`Erdos625HP/SelectedProfilesAndMaximalPsi2.lean` and
`Erdos625HP/UnconditionalSecondMomentAndMainTheorem.lean`, culminating in the
zero-hypothesis (`0`-binder) top-level theorems
`Erdos625HP.erdos625_phaseRefinement_unconditional` and
`Erdos625HP.erdos625_mainTheorem_unconditional`.

### Reproduce `Erdos625HP` and its one-file proof `Erdos625HPSelfContained.lean`

```text
lake exe cache get
lake build --wfail Erdos625 Erdos625HP
python scripts/generate_hp_self_contained.py --check
lake env lean -DwarningAsError=true Erdos625HPSelfContained.lean
```

`Erdos625HPSelfContained.lean` contains 512 local source modules (485 under
`Erdos625`, comprising the 483 release modules plus the 2 `HPRoute*` modules,
and 27 under `Erdos625HP`: the 26 modules in `Erdos625HP/` plus root
`Erdos625HP.lean`), 89 external Lean/Mathlib imports (`Lean.LibrarySuggestions.Basic`
plus 88 `Mathlib` modules), and 148,633 lines (`7,256,871` bytes), with
normalized-LF SHA-256
`1db40bfe653ca42ef3d91640ed0eb748433e8958dc61276586af99aaa7a3e2ad`.
`Erdos625HP/AxiomAudit.lean` prints the axiom closure of 251 selected primary
declarations (249 in `Erdos625HP` and the two `Erdos625/HPRoute*` declarations);
every audited declaration depends solely on `propext`, `Classical.choice`, and
`Quot.sound` (verified from scratch locally with external-only `LEAN_PATH` — zero
project `.olean` directories — in `STANDALONE_512_CLEAN_LEANPATH.log`,
`STANDALONE_EXIT=0` in `1217.7s` with `0` warnings/errors; the earlier `510`-module
`procida` SLURM `Job 69570` wiped-`.lake/build` transcript
`PROCIDA_STANDALONE_69570.log` is also retained; note that `../lean-build.log` is
a historical pre-fix scratch log from 18 November 2026).
