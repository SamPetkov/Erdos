import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Group.Integral
import Erdos625HP.CommonClassMiddleAndSecondMoment

/-!
# v10 Square-exponential moments, capped-dual boundary limit, `(J + 3)` phase cover, and Section 7 assembly

This module formalizes the v10 upgrades across the Main Theorem, Phase Refinement, Lemma 3.2,
Section 7, Corollary 8.1, and Section 9 using only the standard Lean kernel foundations
(`propext`, `Classical.choice`, `Quot.sound`):

1. **Main Theorem `(i)` & Corollary 8.1 — Gaussian-threshold `(1 - 2θ)^(-1/2)` square-exponential
   (`ψ₂`) moment bounds (`θ ∈ [0, 1/2)`):**
   - `exp_quad_eq_gaussian_integral`: exact Laplace-Gaussian identity
     `exp(θ z² / σ²) = (√(2π))⁻¹ ∫_ℝ exp(s (√(2θ)/σ) z - s²/2) ds`.
   - `blockUniform_sqExpMoment_le_of_const_oscillation`: for oscillation `≤ c` across `r ≥ 1`
     independent uniform blocks and `θ ∈ [0, 1/2)`,
     `E[exp(4 θ (Y - E[Y])² / (c² r))] ≤ (1 - 2θ)^(-1/2)`.
   - `sqExpMoment_chromaticSubCochromatic_le` and `sqExpMoment_normalizedGap_le`:
     `E[exp(θ (Δ(G_n) - E[Δ(G_n)])² / (n - 1))] ≤ (1 - 2θ)^(-1/2)` and
     `E[exp(θ n (Y_n - E[Y_n])² / (log₂ n)⁶)] ≤ (1 - 2θ)^(-1/2)` for all `n ≥ 2` and `θ ∈ [0, 1/2)`.

2. **Lemma 3.2(i),(iv) — Exact `S_{≥ 1}` dual formula, concavity & strict monotonicity of
   `ϑ ↦ 𝓕_{S_{≥ 1}}^{=ϑ}(T)`, optimizer identity, and uniform `ϑ ↓ 0` boundary limit:**
   - `dualValue_Sge1_eq_at_sge1Tilt`: for every `T > 1`,
     `𝓕_{S_{≥ 1}}(T) = log Z_{S_{≥ 1}}(λ_{S_{≥ 1}}(T)) - λ_{S_{≥ 1}}(T) T`.
   - `cappedDualValue_Sge1_concave_strictMono_and_eq_dualValue`: for every `T > 2`,
     `ϑ ↦ 𝓕_{S_{≥ 1}}^{=ϑ}(T)` is concave on `[0, 1)`, strictly increasing on `[0, p_{S_{≥ 1}, T}(1)]`,
     and satisfies `𝓕_{S_{≥ 1}}^{=p_{S_{≥ 1}, T}(1)}(T) = 𝓕_{S_{≥ 1}}(T)`.
   - `continuousOn_and_tendstoUniformlyOn_cappedDualValue_Sge1_zero`: joint continuity on
     `[0, 1/20] × K_cap` and uniform convergence `sup_{T ∈ K_cap} |𝓕_{S_{≥ 1}}^{=ϑ}(T) - 𝓕_{S_{≥ 2}}(T)| → 0`
     as `ϑ ↓ 0`.

3. **Section 9 — Complete unconditional `(J + 3)`-interval phase cover & dual-budget theorem:**
   - `exists_finite_phase_cover_dual_budget`: constructively produces for every `ε > 0`
     (`η = (log 2)³ ε`) the transition interval `I_tr = [x₀ - δ₀, x₀ + δ₀]`, main arc
     `I_main = [x₀ + δ₀, 1)`, near-zero interval `I₀ = [0, a₁]`, and capped mesh `I₁, …, I_{N_mesh}`
     covering `[0, 1)` with all Proposition 4.1(iii) / Regime U / Regime C cap margins and `< 2η/3`
     dual-gap bounds verified unconditionally.

4. **Section 7 — `Π_rel` part trichotomy, cross-edge majorant, Poisson kernel, and three-range
   second-moment assembly:**
   - `relevantPair_part_trichotomy_and_overlap_gap`: classifies parts of `(P, P') ∈ Π_rel` into
     `Identical`, `Scrambled`, and `Exceptional` (`≤ 2B`), proves the overlap spectral gap
     (`¬(2M + 4 < |D ∩ D'| < u_- - 1)`), and proves `s₂ ≤ (4M + 6) t + 2 a B`.
   - `crossEdge_binom_pow_le`: unconditional Lemma 7.1 display for all `3 ≤ z ≤ n`.
   - `finset_sum_prod_pow_div_factorial_le_exp_and_tsum_eq` and
     `eventually_overlapKernel_le_exp_polylog5`: Lemma 7.2 Poisson identity and `exp(O_M((log n)⁵))`
     overlap-kernel bound.
   - `eventually_similarRange_geom_ratio_le_half` and
     `eventually_threeRange_secondMoment_and_paleyZygmund`: Proposition 7.3 similar-range quadratic
     decay (`≤ 1/2` eventually) and complete three-range (`scrambled` + `middle` + `similar`)
     second-moment assembly + Paley–Zygmund bridge.

5. **Section 9 — Sharpened v10 Phase Refinement (fixed-corridor `(log n)⁶` tail) & `mainTheorem_v10_complete`.**
-/

namespace Erdos625HP

open Erdos625 Erdos625.FiveSizeEntropyGap FiveSizePhaseGainSharp FiveSizePhaseGainCertificate
open Filter Asymptotics MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal

noncomputable section

set_option autoImplicit false

/-!
## 1. Gaussian-threshold `(1 - 2θ)^(-1/2)` square-exponential (`ψ₂`) moment bounds
-/

private theorem integrable_exp_linear_sub_half_sq (m : ℝ) :
    Integrable (fun s : ℝ ↦ Real.exp (s * m - s ^ 2 / 2)) := by
  have hbase : Integrable (fun u : ℝ ↦ Real.exp (-(1 / 2 : ℝ) * u ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
  have hshift : Integrable (fun s : ℝ ↦ Real.exp (-(1 / 2 : ℝ) * (s - m) ^ 2)) :=
    hbase.comp_sub_right m
  have hmul : Integrable (fun s : ℝ ↦
      Real.exp (m ^ 2 / 2) * Real.exp (-(1 / 2 : ℝ) * (s - m) ^ 2)) :=
    hshift.const_mul (Real.exp (m ^ 2 / 2))
  refine hmul.congr (Filter.Eventually.of_forall fun s ↦ ?_)
  dsimp only
  rw [← Real.exp_add]
  congr 1
  ring

/-- **Exact Gaussian Laplace-transform identity (`Corollary 8.1` proof):**
for every `σ > 0`, `θ ≥ 0`, and `z ∈ ℝ`,
`exp(θ z² / σ²) = (√(2π))⁻¹ ∫_{s ∈ ℝ} exp(s (√(2θ)/σ) z - s²/2) ds`. -/
theorem exp_quad_eq_gaussian_integral {σ θ : ℝ} (hσ : 0 < σ) (hθ : 0 ≤ θ) (z : ℝ) :
    Real.exp (θ * z ^ 2 / σ ^ 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        ∫ s : ℝ, Real.exp (s * (Real.sqrt (2 * θ) / σ * z) - s ^ 2 / 2) := by
  set m : ℝ := Real.sqrt (2 * θ) / σ * z
  have hm_sq : m ^ 2 / 2 = θ * z ^ 2 / σ ^ 2 := by
    dsimp [m]
    rw [mul_pow, div_pow, Real.sq_sqrt (by linarith : 0 ≤ 2 * θ)]
    field_simp [hσ.ne']
  have hrew :
      (fun s : ℝ ↦ Real.exp (s * m - s ^ 2 / 2)) =
        fun s : ℝ ↦ Real.exp (θ * z ^ 2 / σ ^ 2) * Real.exp (-(1 / 2 : ℝ) * (s - m) ^ 2) := by
    funext s
    rw [← hm_sq, ← Real.exp_add]
    congr 1
    ring
  rw [hrew, integral_const_mul,
    MeasureTheory.integral_sub_right_eq_self (fun u : ℝ ↦ Real.exp (-(1 / 2 : ℝ) * u ^ 2)) m,
    integral_gaussian (1 / 2 : ℝ)]
  have hpi : Real.pi / (1 / 2 : ℝ) = 2 * Real.pi := by ring
  rw [hpi]
  have hsqrt_ne : Real.sqrt (2 * Real.pi) ≠ 0 :=
    (Real.sqrt_pos.mpr (mul_pos two_pos Real.pi_pos)).ne'
  field_simp [hsqrt_ne]

/-- Finite-space Fubini + Gaussian-integral helper converting a sub-Gaussian MGF bound
`E[exp(λ X)] ≤ exp(σ² λ² / 2)` (`∀ λ ∈ ℝ`) into the sharp Gaussian square-exponential bound
`E[exp(θ X² / σ²)] ≤ (1 - 2θ)^(-1/2)` for every `θ ∈ [0, 1/2)`. -/
private theorem fintype_sqExpMoment_le_of_subgaussian_mgf
    {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (ℙ : Measure Ω) [IsFiniteMeasure ℙ]
    {X : Ω → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hmgf : ∀ lam : ℝ, (∫ ω : Ω, Real.exp (lam * X ω) ∂ℙ) ≤ Real.exp (σ ^ 2 * lam ^ 2 / 2))
    {θ : ℝ} (hθ : θ ∈ Set.Ico (0 : ℝ) (1 / 2)) :
    (∫ ω : Ω, Real.exp (θ * (X ω) ^ 2 / σ ^ 2) ∂ℙ) ≤ (1 - 2 * θ) ^ (-(1 / 2 : ℝ)) := by
  have h1m2θ_pos : 0 < 1 - 2 * θ := by linarith [hθ.2]
  have hsqrt2pi_pos : 0 < Real.sqrt (2 * Real.pi) :=
    Real.sqrt_pos.mpr (mul_pos two_pos Real.pi_pos)
  set c : ℝ := Real.sqrt (2 * θ) / σ
  have hc_sq : σ ^ 2 * c ^ 2 / 2 = θ := by
    dsimp [c]
    rw [div_pow, Real.sq_sqrt (by linarith [hθ.1] : 0 ≤ 2 * θ)]
    field_simp [hσ.ne']
  have hlhs :
      (∫ ω : Ω, Real.exp (θ * (X ω) ^ 2 / σ ^ 2) ∂ℙ) =
        (Real.sqrt (2 * Real.pi))⁻¹ *
          ∫ s : ℝ, ∑ ω : Ω, ℙ.real {ω} * Real.exp (s * (c * X ω) - s ^ 2 / 2) := by
    rw [integral_fintype Integrable.of_finite]
    simp_rw [smul_eq_mul, exp_quad_eq_gaussian_integral hσ hθ.1]
    have hpull :
        (∑ ω : Ω, ℙ.real {ω} *
            ((Real.sqrt (2 * Real.pi))⁻¹ *
              ∫ s : ℝ, Real.exp (s * (c * X ω) - s ^ 2 / 2))) =
          (Real.sqrt (2 * Real.pi))⁻¹ *
            ∑ ω : Ω, ∫ s : ℝ, ℙ.real {ω} * Real.exp (s * (c * X ω) - s ^ 2 / 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ω _ ↦ ?_
      rw [integral_const_mul]
      ring
    rw [hpull]
    congr 1
    exact (integral_finsetSum Finset.univ fun ω _ ↦
      (integrable_exp_linear_sub_half_sq (c * X ω)).const_mul (ℙ.real {ω})).symm
  have hpt : ∀ s : ℝ,
      (∑ ω : Ω, ℙ.real {ω} * Real.exp (s * (c * X ω) - s ^ 2 / 2)) ≤
        Real.exp (-((1 - 2 * θ) / 2) * s ^ 2) := by
    intro s
    have hsplit :
        (∑ ω : Ω, ℙ.real {ω} * Real.exp (s * (c * X ω) - s ^ 2 / 2)) =
          Real.exp (-s ^ 2 / 2) * ∑ ω : Ω, ℙ.real {ω} * Real.exp ((s * c) * X ω) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ω _ ↦ ?_
      rw [show s * (c * X ω) - s ^ 2 / 2 = -s ^ 2 / 2 + (s * c) * X ω by ring, Real.exp_add]
      ring
    have hfin_int :
        (∑ ω : Ω, ℙ.real {ω} * Real.exp ((s * c) * X ω)) =
          ∫ ω : Ω, Real.exp ((s * c) * X ω) ∂ℙ := by
      rw [integral_fintype Integrable.of_finite]
      simp_rw [smul_eq_mul]
    rw [hsplit, hfin_int]
    have hm := mul_le_mul_of_nonneg_left (hmgf (s * c)) (Real.exp_pos (-s ^ 2 / 2)).le
    refine hm.trans (le_of_eq ?_)
    rw [← Real.exp_add]
    congr 1
    have h1 : σ ^ 2 * (s * c) ^ 2 / 2 = θ * s ^ 2 := by
      calc σ ^ 2 * (s * c) ^ 2 / 2 = (σ ^ 2 * c ^ 2 / 2) * s ^ 2 := by ring
        _ = θ * s ^ 2 := by rw [hc_sq]
    rw [h1]
    ring
  have hint_lhs :
      Integrable (fun s : ℝ ↦ ∑ ω : Ω, ℙ.real {ω} * Real.exp (s * (c * X ω) - s ^ 2 / 2)) :=
    integrable_finsetSum Finset.univ fun ω _ ↦
      (integrable_exp_linear_sub_half_sq (c * X ω)).const_mul (ℙ.real {ω})
  have hint_rhs : Integrable (fun s : ℝ ↦ Real.exp (-((1 - 2 * θ) / 2) * s ^ 2)) :=
    integrable_exp_neg_mul_sq (half_pos h1m2θ_pos)
  have hint_le := integral_mono hint_lhs hint_rhs hpt
  have hrhs_val :
      (Real.sqrt (2 * Real.pi))⁻¹ * ∫ s : ℝ, Real.exp (-((1 - 2 * θ) / 2) * s ^ 2) =
        (1 - 2 * θ) ^ (-(1 / 2 : ℝ)) := by
    rw [integral_gaussian ((1 - 2 * θ) / 2)]
    have hdiv_eq : Real.pi / ((1 - 2 * θ) / 2) = (2 * Real.pi) / (1 - 2 * θ) := by
      field_simp [h1m2θ_pos.ne']
    rw [hdiv_eq, Real.sqrt_div (mul_pos two_pos Real.pi_pos).le]
    have h1 : (Real.sqrt (2 * Real.pi))⁻¹ *
        (Real.sqrt (2 * Real.pi) / Real.sqrt (1 - 2 * θ)) = (Real.sqrt (1 - 2 * θ))⁻¹ := by
      field_simp [hsqrt2pi_pos.ne']
    rw [h1, Real.sqrt_eq_rpow, ← Real.rpow_neg h1m2θ_pos.le]
  rw [hlhs]
  exact (mul_le_mul_of_nonneg_left hint_le (inv_nonneg.mpr hsqrt2pi_pos.le)).trans
    (le_of_eq hrhs_val)

/-- **Section 1, eq. `(1.2)` Gaussian-threshold square-exponential moment bound:**
for any real-valued function `Y` of oscillation `≤ c` (`c > 0`) across `r ≥ 1` independent
uniform blocks and any `θ ∈ [0, 1/2)`,
`E[exp(4 θ (Y - E[Y])² / (c² r))] ≤ (1 - 2θ)^(-1/2)`. -/
theorem blockUniform_sqExpMoment_le_of_const_oscillation
    {r : ℕ} (hr : 1 ≤ r)
    {Omega : Fin r → Type*} [∀ i, Fintype (Omega i)] [∀ i, Nonempty (Omega i)]
    {Y : (∀ i, Omega i) → ℝ} {c : ℝ≥0} (hc : 0 < c)
    (hY : HasBlockOscillation Y (fun _ ↦ c))
    {θ : ℝ} (hθ : θ ∈ Set.Ico (0 : ℝ) (1 / 2)) :
    blockExpectation Omega
        (fun x ↦ Real.exp (4 * θ * (Y x - blockExpectation Omega Y) ^ 2 /
          ((c : ℝ) ^ 2 * (r : ℝ)))) ≤
      (1 - 2 * θ) ^ (-(1 / 2 : ℝ)) := by
  letI : MeasurableSpace (∀ i, Omega i) := ⊤
  letI : IsProbabilityMeasure (blockUniformMeasure Omega) :=
    PMF.toMeasure.isProbabilityMeasure (blockUniformPMF Omega)
  have hc_pos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  set σ : ℝ := (c : ℝ) * Real.sqrt (r : ℝ) / 2
  have hσ_pos : 0 < σ := by
    dsimp [σ]
    exact div_pos (mul_pos hc_pos (Real.sqrt_pos.mpr hr_pos)) two_pos
  have hσ_sq : σ ^ 2 = (c : ℝ) ^ 2 * (r : ℝ) / 4 := by
    dsimp [σ]
    rw [div_pow, mul_pow, Real.sq_sqrt hr_pos.le]
    ring
  obtain ⟨-, hmgf, -⟩ := blockUniform_variance_mgf_and_tails_of_const_oscillation hr hc hY
  have hmgf' : ∀ lam : ℝ,
      (∫ x : ∀ i, Omega i, Real.exp (lam * (Y x - blockExpectation Omega Y))
        ∂blockUniformMeasure Omega) ≤ Real.exp (σ ^ 2 * lam ^ 2 / 2) := by
    intro lam
    have hb := hmgf lam
    have heq : (c : ℝ) ^ 2 * (r : ℝ) * lam ^ 2 / 8 = σ ^ 2 * lam ^ 2 / 2 := by
      rw [hσ_sq]; ring
    simpa [blockExpectation, heq] using hb
  have hres := fintype_sqExpMoment_le_of_subgaussian_mgf
    (blockUniformMeasure Omega) hσ_pos hmgf' hθ
  have hfun :
      (fun x : ∀ i, Omega i ↦
        Real.exp (4 * θ * (Y x - blockExpectation Omega Y) ^ 2 / ((c : ℝ) ^ 2 * (r : ℝ)))) =
      (fun x : ∀ i, Omega i ↦
        Real.exp (θ * (Y x - blockExpectation Omega Y) ^ 2 / σ ^ 2)) := by
    funext x
    congr 1
    rw [hσ_sq]
    field_simp [hc_pos.ne', hr_pos.ne']
  change ∫ x : ∀ i, Omega i,
      Real.exp (4 * θ * (Y x - blockExpectation Omega Y) ^ 2 / ((c : ℝ) ^ 2 * (r : ℝ)))
      ∂blockUniformMeasure Omega ≤ (1 - 2 * θ) ^ (-(1 / 2 : ℝ))
  rwa [hfun]

/-- **Main Theorem `(i)` & Corollary 8.1 square-exponential (`ψ₂`) moment bound for `Δ(G_n)`:**
for all `n ≥ 2` and `θ ∈ [0, 1/2)`,
`E[exp(θ (Δ(G_n) - E[Δ(G_n)])² / (n - 1))] ≤ (1 - 2θ)^(-1/2)`. -/
theorem sqExpMoment_chromaticSubCochromatic_le
    {n : ℕ} (hn : 2 ≤ n) {θ : ℝ} (hθ : θ ∈ Set.Ico (0 : ℝ) (1 / 2)) :
    (∫ G : LabeledGraph n,
        Real.exp (θ * (((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) -
          ∫ H : LabeledGraph n,
            ((chromaticNumberNat H : ℝ) - (cochromaticNumber H : ℝ))
            ∂randomGraphMeasure n) ^ 2 / ((n - 1 : ℕ) : ℝ))
        ∂randomGraphMeasure n) ≤
      (1 - 2 * θ) ^ (-(1 / 2 : ℝ)) := by
  have hn1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n - 1 by omega)
  set σ : ℝ := Real.sqrt ((n - 1 : ℕ) : ℝ)
  have hσ_pos : 0 < σ := Real.sqrt_pos.mpr hn1_pos
  have hσ_sq : σ ^ 2 = ((n - 1 : ℕ) : ℝ) := Real.sq_sqrt hn1_pos.le
  have hmgf : ∀ lam : ℝ,
      (∫ G : LabeledGraph n,
        Real.exp (lam * (((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) -
          ∫ H : LabeledGraph n,
            ((chromaticNumberNat H : ℝ) - (cochromaticNumber H : ℝ))
            ∂randomGraphMeasure n))
        ∂randomGraphMeasure n) ≤ Real.exp (σ ^ 2 * lam ^ 2 / 2) := by
    intro lam
    rw [hσ_sq]
    exact mgf_chromaticSubCochromatic_center_le n lam
  have hres := fintype_sqExpMoment_le_of_subgaussian_mgf
    (randomGraphMeasure n) hσ_pos hmgf hθ
  simpa only [hσ_sq] using hres

/-- **Main Theorem `(i)` & Corollary 8.1 square-exponential (`ψ₂`) moment bound for `Y_n`:**
for all `n ≥ 2` and `θ ∈ [0, 1/2)`,
`E[exp(θ n (Y_n - E[Y_n])² / (log₂ n)⁶)] ≤ (1 - 2θ)^(-1/2)`. -/
theorem sqExpMoment_normalizedGap_le
    {n : ℕ} (hn : 2 ≤ n) {θ : ℝ} (hθ : θ ∈ Set.Ico (0 : ℝ) (1 / 2)) :
    let Y : LabeledGraph n → ℝ := fun G ↦
      (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
        ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
    (∫ G : LabeledGraph n,
        Real.exp (θ * (n : ℝ) * (Y G - ∫ H : LabeledGraph n, Y H ∂randomGraphMeasure n) ^ 2 /
          (Real.logb 2 (n : ℝ)) ^ 6)
        ∂randomGraphMeasure n) ≤
      (1 - 2 * θ) ^ (-(1 / 2 : ℝ)) := by
  intro Y
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hn_pos : (0 : ℝ) < (n : ℝ) := lt_trans zero_lt_one hn1
  have hn1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n - 1 by omega)
  have hn1_le : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
  have hlb_pos : 0 < Real.logb 2 (n : ℝ) := Real.logb_pos one_lt_two hn1
  set D : LabeledGraph n → ℝ := fun G ↦ (chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)
  set meanD : ℝ := ∫ H : LabeledGraph n, D H ∂randomGraphMeasure n
  have hmeanY : (∫ H : LabeledGraph n, Y H ∂randomGraphMeasure n) =
      ((Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ)) * meanD :=
    integral_const_mul _ D
  have hpt : ∀ G : LabeledGraph n,
      Real.exp (θ * (n : ℝ) * (Y G - ∫ H : LabeledGraph n, Y H ∂randomGraphMeasure n) ^ 2 /
          (Real.logb 2 (n : ℝ)) ^ 6) ≤
        Real.exp (θ * (D G - meanD) ^ 2 / ((n - 1 : ℕ) : ℝ)) := by
    intro G
    apply Real.exp_le_exp.mpr
    have hdiff : Y G - ∫ H, Y H ∂randomGraphMeasure n =
        ((Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ)) * (D G - meanD) := by
      rw [hmeanY]; dsimp [Y, D]; ring
    have hlhs_eq :
        θ * (n : ℝ) * (Y G - ∫ H, Y H ∂randomGraphMeasure n) ^ 2 /
            (Real.logb 2 (n : ℝ)) ^ 6 =
          θ * (D G - meanD) ^ 2 / (n : ℝ) := by
      rw [hdiff]
      field_simp [hn_pos.ne', hlb_pos.ne']
    rw [hlhs_eq]
    exact div_le_div_of_nonneg_left (mul_nonneg hθ.1 (sq_nonneg _)) hn1_pos hn1_le
  exact (integral_mono Integrable.of_finite Integrable.of_finite hpt).trans
    (sqExpMoment_chromaticSubCochromatic_le hn hθ)

/-!
## 2. Exact `S_{≥ 1}` dual formula, concavity/monotonicity of `ϑ ↦ 𝓕_{S_{≥ 1}}^{=ϑ}(T)`, and `ϑ ↓ 0` limit
-/

private theorem splus_dual_obj_min_at_tilt {t : ℝ} (ht : -1 < t) (l : ℝ) :
    Real.log (extendedGaussianPartition q (extendedGaussianTilt q t)) -
        extendedGaussianTilt q t * t ≤
      Real.log (extendedGaussianPartition q l) - l * t := by
  set μ : ℝ := extendedGaussianTilt q t
  let φ : ℝ → ℝ := fun x ↦ Real.log (extendedGaussianPartition q x) - x * t
  have hderiv : ∀ x : ℝ, HasDerivAt φ (extendedGaussianMean q x - t) x := by
    intro x
    have hZ := hasDerivAt_extendedGaussianPartition q x q_pos
    have hlog := hZ.log (extendedGaussianPartition_ne_zero q_pos)
    have hlin : HasDerivAt (fun y : ℝ ↦ y * t) t x := by
      simpa using (hasDerivAt_id x).mul_const t
    exact (hlog.sub hlin).congr_deriv rfl
  have hmean_μ : extendedGaussianMean q μ = t :=
    extendedGaussianMean_extendedGaussianTilt q_pos ht
  change φ μ ≤ φ l
  rcases le_total μ l with hle | hge
  · have hmono : MonotoneOn φ (Set.Icc μ l) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc μ l)
      · exact fun x _ ↦ (hderiv x).continuousAt.continuousWithinAt
      · exact fun x _ ↦ (hderiv x).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        rw [(hderiv x).deriv, ← hmean_μ]
        linarith [strictMono_extendedGaussianMean q q_pos hx.1]
    exact hmono (left_mem_Icc.mpr hle) (right_mem_Icc.mpr hle) hle
  · have hanti : AntitoneOn φ (Set.Icc l μ) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc l μ)
      · exact fun x _ ↦ (hderiv x).continuousAt.continuousWithinAt
      · exact fun x _ ↦ (hderiv x).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        rw [(hderiv x).deriv, ← hmean_μ]
        linarith [strictMono_extendedGaussianMean q q_pos hx.2]
    exact hanti (left_mem_Icc.mpr hge) (right_mem_Icc.mpr hge) hge

private theorem sge1_dual_obj_min_at_tilt {T : ℝ} (hT : 1 < T) (l : ℝ) :
    Real.log (partitionFn Sge1 (sge1Tilt T)) - sge1Tilt T * T ≤
      Real.log (partitionFn Sge1 l) - l * T := by
  have ht : -1 < T - 2 := by linarith
  have hrew : ∀ x : ℝ,
      Real.log (partitionFn Sge1 x) - x * T =
        (Real.log (extendedGaussianPartition q (x - 2 * q)) - (x - 2 * q) * (T - 2)) -
          2 * q * (T - 1) := by
    intro x
    rw [partitionFn_Sge1_eq_shift_extendedGaussian x,
      Real.log_mul (Real.exp_pos _).ne' (extendedGaussianPartition_ne_zero q_pos), Real.log_exp]
    ring
  rw [hrew (sge1Tilt T), hrew l]
  have hl0 : sge1Tilt T - 2 * q = extendedGaussianTilt q (T - 2) := by
    unfold sge1Tilt; ring
  rw [hl0]
  linarith [splus_dual_obj_min_at_tilt ht (l - 2 * q)]

private theorem bddBelow_dual_Sge1 {T : ℝ} (hT : 1 < T) :
    BddBelow (Set.range fun l : ℝ ↦ Real.log (partitionFn Sge1 l) - l * T) :=
  ⟨Real.log (partitionFn Sge1 (sge1Tilt T)) - sge1Tilt T * T, by
    rintro _ ⟨l, rfl⟩
    exact sge1_dual_obj_min_at_tilt hT l⟩

/-- **Exact `S_{≥ 1}` Legendre-dual formula (`Lemma 3.2(i)`, eq. `(3.8)`):**
for every `T > 1`, the infimum defining `𝓕_{S_{≥ 1}}(T)` is attained at `λ_{S_{≥ 1}}(T)`:
`𝓕_{S_{≥ 1}}(T) = log Z_{S_{≥ 1}}(λ_{S_{≥ 1}}(T)) - λ_{S_{≥ 1}}(T) T`. -/
theorem dualValue_Sge1_eq_at_sge1Tilt {T : ℝ} (hT : 1 < T) :
    dualValue Sge1 T = Real.log (partitionFn Sge1 (sge1Tilt T)) - sge1Tilt T * T := by
  unfold dualValue
  exact le_antisymm (ciInf_le (bddBelow_dual_Sge1 hT) (sge1Tilt T))
    (le_ciInf fun l ↦ sge1_dual_obj_min_at_tilt hT l)

private theorem partitionFn_Sge1_pos (l : ℝ) : 0 < partitionFn Sge1 l := by
  rw [partitionFn_Sge1_eq_shift_extendedGaussian]
  exact mul_pos (Real.exp_pos _) (extendedGaussianPartition_pos q_pos)

private theorem partitionFn_Sge1_recurrence (l : ℝ) :
    partitionFn Sge1 l =
      Real.exp (l - Real.log 2 / 2) * (1 + partitionFn Sge1 (l - Real.log 2)) := by
  have hsum_all := summable_gaussWeight l
  have hs1 : Summable (({1} : Set ℤ).indicator (gaussWeight l)) := hsum_all.indicator {1}
  have hs2 : Summable ((Sge1 \ {1}).indicator (gaussWeight l)) := hsum_all.indicator (Sge1 \ {1})
  have hpt : ∀ i : ℤ, Sge1.indicator (gaussWeight l) i =
      ({1} : Set ℤ).indicator (gaussWeight l) i + (Sge1 \ {1}).indicator (gaussWeight l) i := by
    intro i
    by_cases hi1 : i = 1
    · subst hi1
      have h1_mem : (1 : ℤ) ∈ Sge1 := by simp [Sge1]
      simp [h1_mem]
    · by_cases hiS : i ∈ Sge1
      · have hdiff : i ∈ Sge1 \ {1} := ⟨hiS, hi1⟩
        simp [hiS, hi1, hdiff]
      · have hndiff : i ∉ Sge1 \ {1} := fun h ↦ hiS h.1
        simp [hiS, hi1, hndiff]
  have hts1 : (∑' x : ℤ, ({1} : Set ℤ).indicator (gaussWeight l) x) = gaussWeight l 1 := by
    rw [(hasSum_single (1 : ℤ)
      (fun b hb ↦ Set.indicator_of_notMem (Set.mem_singleton_iff.not.mpr hb) _)).tsum_eq,
      Set.indicator_of_mem (Set.mem_singleton (1 : ℤ)) _]
  have hsplit : partitionFn Sge1 l = gaussWeight l 1 + partitionFn (Sge1 \ {1}) l := by
    unfold partitionFn
    rw [tsum_subtype Sge1 (gaussWeight l), tsum_subtype (Sge1 \ {1}) (gaussWeight l)]
    simp_rw [hpt]
    rw [(hs1.hasSum.add hs2.hasSum).tsum_eq, hts1]
  have hdiff_eq : Sge1 \ {1} = shiftSupportOne Sge1 := by
    ext j
    simp only [shiftSupportOne, Sge1, Set.mem_setOf_eq, Set.mem_sdiff, Set.mem_singleton_iff]
    omega
  have hw1 : gaussWeight l 1 = Real.exp (l - Real.log 2 / 2) := by
    unfold gaussWeight; push_cast; congr 1; ring
  rw [hsplit, hdiff_eq, partitionFn_shiftSupportOne Sge1 l, hw1]
  ring

private theorem sge1Tilt_reduced_eq_sub_log_two {T : ℝ} (hT : 2 < T) :
    let p₁ : ℝ := gibbsProb Sge1 (sge1Tilt T) 1
    p₁ ∈ Set.Ioo (0 : ℝ) 1 ∧
      sge1Tilt ((T - 1) / (1 - p₁)) = sge1Tilt T - Real.log 2 := by
  intro p₁
  set lam : ℝ := sge1Tilt T
  have hZ_pos : 0 < partitionFn Sge1 lam := partitionFn_Sge1_pos lam
  have hZ_shift_pos : 0 < partitionFn Sge1 (lam - Real.log 2) :=
    partitionFn_Sge1_pos (lam - Real.log 2)
  have hrec := partitionFn_Sge1_recurrence lam
  have hw1 : gaussWeight lam 1 = Real.exp (lam - Real.log 2 / 2) := by
    unfold gaussWeight; push_cast; congr 1; ring
  have hp₁_formula : p₁ = 1 / (1 + partitionFn Sge1 (lam - Real.log 2)) := by
    dsimp [p₁]
    unfold gibbsProb
    rw [hw1, hrec]
    field_simp [(Real.exp_pos _).ne', (by linarith : 1 + partitionFn Sge1 (lam - Real.log 2) ≠ 0)]
  have hp₁_mem : p₁ ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [hp₁_formula]
    exact ⟨div_pos one_pos (by linarith), (div_lt_one (by linarith)).mpr (by linarith)⟩
  refine ⟨hp₁_mem, ?_⟩
  have h1mp₁_pos : 0 < 1 - p₁ := sub_pos.mpr hp₁_mem.2
  have hderiv_Z : ∀ l : ℝ,
      HasDerivAt (partitionFn Sge1)
        ((2 + extendedGaussianMean q (l - 2 * q)) * partitionFn Sge1 l) l := by
    intro l
    have hd_exp : HasDerivAt (fun x : ℝ ↦ Real.exp (2 * x - 2 * q))
        (2 * Real.exp (2 * l - 2 * q)) l := by
      have hlin : HasDerivAt (fun x : ℝ ↦ 2 * x - 2 * q) 2 l :=
        (((hasDerivAt_id l).const_mul (2 : ℝ)).sub (hasDerivAt_const l (2 * q))).congr_deriv (by ring)
      exact hlin.exp.congr_deriv (mul_comm _ _)
    have hsub : HasDerivAt (fun x : ℝ ↦ x - 2 * q) 1 l :=
      ((hasDerivAt_id l).sub (hasDerivAt_const l (2 * q))).congr_deriv (by ring)
    have hd_ext0 : HasDerivAt ((extendedGaussianPartition q) ∘ (fun x : ℝ ↦ x - 2 * q))
        (extendedGaussianFirstNumerator q (l - 2 * q) * 1) l :=
      HasDerivAt.comp l (hasDerivAt_extendedGaussianPartition q (l - 2 * q) q_pos) hsub
    have hd_ext : HasDerivAt (fun x : ℝ ↦ extendedGaussianPartition q (x - 2 * q))
        (extendedGaussianFirstNumerator q (l - 2 * q)) l :=
      hd_ext0.congr_deriv (mul_one _)
    have hmul : HasDerivAt (partitionFn Sge1)
        (2 * Real.exp (2 * l - 2 * q) * extendedGaussianPartition q (l - 2 * q) +
          Real.exp (2 * l - 2 * q) * extendedGaussianFirstNumerator q (l - 2 * q)) l :=
      (hd_exp.mul hd_ext).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun x ↦ partitionFn_Sge1_eq_shift_extendedGaussian x)
    refine hmul.congr_deriv ?_
    rw [partitionFn_Sge1_eq_shift_extendedGaussian l]
    unfold extendedGaussianMean
    have hZp_ne := extendedGaussianPartition_ne_zero (lambda := l - 2 * q) q_pos
    field_simp [hZp_ne]
  have hd_lhs := hderiv_Z lam
  have hd_rhs :
      HasDerivAt (fun l : ℝ ↦ Real.exp (l - Real.log 2 / 2) * (1 + partitionFn Sge1 (l - Real.log 2)))
        (Real.exp (lam - Real.log 2 / 2) * (1 + partitionFn Sge1 (lam - Real.log 2)) +
          Real.exp (lam - Real.log 2 / 2) *
            ((2 + extendedGaussianMean q (lam - Real.log 2 - 2 * q)) *
              partitionFn Sge1 (lam - Real.log 2))) lam := by
    have hlin1 : HasDerivAt (fun l : ℝ ↦ l - Real.log 2 / 2) 1 lam :=
      ((hasDerivAt_id lam).sub (hasDerivAt_const lam (Real.log 2 / 2))).congr_deriv (by ring)
    have hd1 : HasDerivAt (fun l : ℝ ↦ Real.exp (l - Real.log 2 / 2))
        (Real.exp (lam - Real.log 2 / 2)) lam :=
      hlin1.exp.congr_deriv (mul_one _)
    have hsh : HasDerivAt (fun l : ℝ ↦ l - Real.log 2) 1 lam :=
      ((hasDerivAt_id lam).sub (hasDerivAt_const lam (Real.log 2))).congr_deriv (by ring)
    have hcomp0 : HasDerivAt ((partitionFn Sge1) ∘ (fun l : ℝ ↦ l - Real.log 2))
        (((2 + extendedGaussianMean q (lam - Real.log 2 - 2 * q)) *
          partitionFn Sge1 (lam - Real.log 2)) * 1) lam :=
      HasDerivAt.comp lam (hderiv_Z (lam - Real.log 2)) hsh
    have hcomp : HasDerivAt (fun l : ℝ ↦ partitionFn Sge1 (l - Real.log 2))
        ((2 + extendedGaussianMean q (lam - Real.log 2 - 2 * q)) *
          partitionFn Sge1 (lam - Real.log 2)) lam :=
      hcomp0.congr_deriv (mul_one _)
    have hd2 : HasDerivAt (fun l : ℝ ↦ 1 + partitionFn Sge1 (l - Real.log 2))
        ((2 + extendedGaussianMean q (lam - Real.log 2 - 2 * q)) *
          partitionFn Sge1 (lam - Real.log 2)) lam :=
      ((hasDerivAt_const lam (1 : ℝ)).add hcomp).congr_deriv (zero_add _)
    exact (hd1.mul hd2).congr_deriv (by ring)
  rw [← funext partitionFn_Sge1_recurrence] at hd_rhs
  have heq_deriv := hd_lhs.unique hd_rhs
  have hmean_lam : 2 + extendedGaussianMean q (lam - 2 * q) = T := by
    have hl : lam - 2 * q = extendedGaussianTilt q (T - 2) := by
      dsimp [lam]; unfold sge1Tilt; ring
    rw [hl, extendedGaussianMean_extendedGaussianTilt q_pos (by linarith : -1 < T - 2)]
    ring
  rw [hmean_lam, ← hrec] at heq_deriv
  have h1mp₁_Z :
      Real.exp (lam - Real.log 2 / 2) * partitionFn Sge1 (lam - Real.log 2) =
        (1 - p₁) * partitionFn Sge1 lam := by
    dsimp [p₁]; unfold gibbsProb
    rw [hw1, sub_mul, div_mul_cancel₀ _ hZ_pos.ne', hrec]
    ring
  have hbalance :
      T * partitionFn Sge1 lam =
        partitionFn Sge1 lam +
          (1 - p₁) * partitionFn Sge1 lam *
            (2 + extendedGaussianMean q (lam - Real.log 2 - 2 * q)) := by
    calc T * partitionFn Sge1 lam
        = partitionFn Sge1 lam +
            Real.exp (lam - Real.log 2 / 2) *
              ((2 + extendedGaussianMean q (lam - Real.log 2 - 2 * q)) *
                partitionFn Sge1 (lam - Real.log 2)) := heq_deriv
      _ = partitionFn Sge1 lam +
            (Real.exp (lam - Real.log 2 / 2) * partitionFn Sge1 (lam - Real.log 2)) *
              (2 + extendedGaussianMean q (lam - Real.log 2 - 2 * q)) := by ring
      _ = _ := by rw [h1mp₁_Z]
  have hdivZ : T - 1 = (1 - p₁) * (2 + extendedGaussianMean q (lam - Real.log 2 - 2 * q)) := by
    have hmulZ : (T - 1) * partitionFn Sge1 lam =
        ((1 - p₁) * (2 + extendedGaussianMean q (lam - Real.log 2 - 2 * q))) *
          partitionFn Sge1 lam := by linarith
    exact mul_right_cancel₀ hZ_pos.ne' hmulZ
  have hmean_red :
      extendedGaussianMean q (lam - Real.log 2 - 2 * q) = (T - 1) / (1 - p₁) - 2 := by
    rw [eq_sub_iff_add_eq, eq_div_iff h1mp₁_pos.ne']
    linarith
  have htarget_gt : -1 < (T - 1) / (1 - p₁) - 2 := by
    have h1 : 1 < (T - 1) / (1 - p₁) := by
      rw [lt_div_iff₀ h1mp₁_pos]
      linarith [hp₁_mem.1]
    linarith
  have htilt_eq := eq_extendedGaussianTilt_of_extendedGaussianMean_eq q_pos htarget_gt hmean_red
  unfold sge1Tilt
  rw [← htilt_eq]
  dsimp [lam]
  unfold sge1Tilt
  ring

private theorem cappedDualValue_Sge1_eq_formula {T θ : ℝ}
    (hT : 2 < T) (hθ : θ ∈ Set.Ico (0 : ℝ) 1) :
    cappedDualValue Sge1 θ T =
      binEntropy θ - Real.log 2 * (T - 1 / 2) +
        (1 - θ) * dualValue Sge1 ((T - 1) / (1 - θ)) := by
  have h1mθ_pos : 0 < 1 - θ := sub_pos.mpr hθ.2
  have hTred_gt1 : 1 < (T - 1) / (1 - θ) := by
    rw [lt_div_iff₀ h1mθ_pos]
    linarith [hθ.1]
  have hdiff_eq : Sge1 \ {1} = shiftSupportOne Sge1 := by
    ext j
    simp only [shiftSupportOne, Sge1, Set.mem_setOf_eq, Set.mem_sdiff, Set.mem_singleton_iff]
    omega
  have harg : (T - θ) / (1 - θ) = (T - 1) / (1 - θ) + 1 := by
    field_simp [h1mθ_pos.ne']; ring
  have hsh := dualValue_shiftSupportOne (S := Sge1) ⟨1, by simp [Sge1]⟩
    (bddBelow_dual_Sge1 hTred_gt1)
  unfold cappedDualValue
  rw [hdiff_eq, harg, hsh]
  field_simp [h1mθ_pos.ne']
  ring

private theorem concaveOn_binEntropy_Icc : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) binEntropy := by
  have h1 : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun x : ℝ ↦ -(x * Real.log x)) :=
    (Real.convexOn_mul_log.subset (fun x hx ↦ hx.1) (convex_Icc 0 1)).neg
  have h2 : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun x : ℝ ↦ -((1 - x) * Real.log (1 - x))) := by
    refine ⟨convex_Icc 0 1, fun x hx y hy a b ha hb hab ↦ ?_⟩
    have hx' : 1 - x ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hy' : 1 - y ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have hlin : 1 - (a * x + b * y) = a * (1 - x) + b * (1 - y) := by
      calc 1 - (a * x + b * y) = (a + b) - (a * x + b * y) := by rw [hab]
        _ = a * (1 - x) + b * (1 - y) := by ring
    dsimp only
    simp only [smul_eq_mul]
    rw [hlin]
    simpa only [smul_eq_mul] using h1.2 hx' hy' ha hb hab
  have hsum := h1.add h2
  refine hsum.congr fun x _ ↦ ?_
  simp only [Pi.add_apply, binEntropy]
  ring

/-- **Lemma 3.2(iv) concavity, strict monotonicity, and optimizer identity for `𝓕_{S_{≥ 1}}^{=ϑ}(T)`:**
for every `T > 2`, with `p₁ = p_{S_{≥ 1}, T}(1) = gibbsProb Sge1 (sge1Tilt T) 1 ∈ (0, 1)`:
1. `ϑ ↦ 𝓕_{S_{≥ 1}}^{=ϑ}(T)` is concave on `[0, 1)`;
2. `ϑ ↦ 𝓕_{S_{≥ 1}}^{=ϑ}(T)` is strictly increasing on `[0, p₁]` (hence on `[0, min(p₁, 1/20)]`);
3. `𝓕_{S_{≥ 1}}^{=p₁}(T) = 𝓕_{S_{≥ 1}}(T)` and `𝓕_{S_{≥ 1}}^{=ϑ}(T) ≤ 𝓕_{S_{≥ 1}}(T)` on `[0, 1)`. -/
theorem cappedDualValue_Sge1_concave_strictMono_and_eq_dualValue {T : ℝ} (hT : 2 < T) :
    let p₁ : ℝ := gibbsProb Sge1 (sge1Tilt T) 1
    ConcaveOn ℝ (Set.Ico (0 : ℝ) 1) (fun θ ↦ cappedDualValue Sge1 θ T) ∧
      StrictMonoOn (fun θ ↦ cappedDualValue Sge1 θ T) (Set.Icc 0 p₁) ∧
      cappedDualValue Sge1 p₁ T = dualValue Sge1 T ∧
      ∀ θ ∈ Set.Ico (0 : ℝ) 1, cappedDualValue Sge1 θ T ≤ dualValue Sge1 T := by
  intro p₁
  obtain ⟨hp₁_mem, htilt_red⟩ := sge1Tilt_reduced_eq_sub_log_two hT
  set lam : ℝ := sge1Tilt T
  have hZ_pos : 0 < partitionFn Sge1 lam := partitionFn_Sge1_pos lam
  have hZ_shift_pos : 0 < partitionFn Sge1 (lam - Real.log 2) :=
    partitionFn_Sge1_pos (lam - Real.log 2)
  have hw1 : gaussWeight lam 1 = Real.exp (lam - Real.log 2 / 2) := by
    unfold gaussWeight; push_cast; congr 1; ring
  have hlog_p₁ : Real.log p₁ = lam - Real.log 2 / 2 - Real.log (partitionFn Sge1 lam) := by
    dsimp [p₁]; unfold gibbsProb
    rw [Real.log_div (gaussWeight_pos lam 1).ne' hZ_pos.ne', hw1, Real.log_exp]
  have hlog_1mp₁ :
      Real.log (1 - p₁) =
        lam - Real.log 2 / 2 + Real.log (partitionFn Sge1 (lam - Real.log 2)) -
          Real.log (partitionFn Sge1 lam) := by
    have h1mp₁_eq :
        1 - p₁ = Real.exp (lam - Real.log 2 / 2) * partitionFn Sge1 (lam - Real.log 2) /
          partitionFn Sge1 lam := by
      dsimp [p₁]; unfold gibbsProb
      rw [one_sub_div hZ_pos.ne', hw1, partitionFn_Sge1_recurrence lam]
      ring
    rw [h1mp₁_eq, Real.log_div (mul_pos (Real.exp_pos _) hZ_shift_pos).ne' hZ_pos.ne',
      Real.log_mul (Real.exp_pos _).ne' hZ_shift_pos.ne', Real.log_exp]
  have hconc : ConcaveOn ℝ (Set.Ico (0 : ℝ) 1) (fun θ ↦ cappedDualValue Sge1 θ T) := by
    refine ⟨convex_Ico 0 1, fun x hx y hy a b ha hb hab ↦ ?_⟩
    have hz : a * x + b * y ∈ Set.Ico (0 : ℝ) 1 := by
      rcases eq_or_lt_of_le ha with rfl | ha_pos
      · simp only [zero_add] at hab; subst hab; simpa using hy
      · exact ⟨by nlinarith [hx.1, hy.1], by nlinarith [hx.2, hy.2, hab]⟩
    dsimp only
    rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      cappedDualValue_Sge1_eq_formula hT hx,
      cappedDualValue_Sge1_eq_formula hT hy,
      cappedDualValue_Sge1_eq_formula hT hz]
    have h1mx : 0 < 1 - x := sub_pos.mpr hx.2
    have h1my : 0 < 1 - y := sub_pos.mpr hy.2
    have h1mz : 0 < 1 - (a * x + b * y) := sub_pos.mpr hz.2
    have hTz_gt1 : 1 < (T - 1) / (1 - (a * x + b * y)) := by
      rw [lt_div_iff₀ h1mz]; linarith [hz.1]
    have hTx_gt1 : 1 < (T - 1) / (1 - x) := by rw [lt_div_iff₀ h1mx]; linarith [hx.1]
    have hTy_gt1 : 1 < (T - 1) / (1 - y) := by rw [lt_div_iff₀ h1my]; linarith [hy.1]
    set μz : ℝ := sge1Tilt ((T - 1) / (1 - (a * x + b * y)))
    have hdz := dualValue_Sge1_eq_at_sge1Tilt hTz_gt1
    have hdx : dualValue Sge1 ((T - 1) / (1 - x)) ≤
        Real.log (partitionFn Sge1 μz) - μz * ((T - 1) / (1 - x)) :=
      ciInf_le (bddBelow_dual_Sge1 hTx_gt1) μz
    have hdy : dualValue Sge1 ((T - 1) / (1 - y)) ≤
        Real.log (partitionFn Sge1 μz) - μz * ((T - 1) / (1 - y)) :=
      ciInf_le (bddBelow_dual_Sge1 hTy_gt1) μz
    have hmx : (1 - x) * dualValue Sge1 ((T - 1) / (1 - x)) ≤
        (1 - x) * Real.log (partitionFn Sge1 μz) - μz * (T - 1) := by
      have hm := mul_le_mul_of_nonneg_left hdx h1mx.le
      have hc : (1 - x) * (μz * ((T - 1) / (1 - x))) = μz * (T - 1) := by
        field_simp [h1mx.ne']
      linarith
    have hmy : (1 - y) * dualValue Sge1 ((T - 1) / (1 - y)) ≤
        (1 - y) * Real.log (partitionFn Sge1 μz) - μz * (T - 1) := by
      have hm := mul_le_mul_of_nonneg_left hdy h1my.le
      have hc : (1 - y) * (μz * ((T - 1) / (1 - y))) = μz * (T - 1) := by
        field_simp [h1my.ne']
      linarith
    have hmz : (1 - (a * x + b * y)) * dualValue Sge1 ((T - 1) / (1 - (a * x + b * y))) =
        (1 - (a * x + b * y)) * Real.log (partitionFn Sge1 μz) - μz * (T - 1) := by
      rw [hdz]
      dsimp [μz]
      field_simp [h1mz.ne']
    have hbin := concaveOn_binEntropy_Icc.2 ⟨hx.1, hx.2.le⟩ ⟨hy.1, hy.2.le⟩ ha hb hab
    simp only [smul_eq_mul] at hbin
    have hcomb1 := mul_le_mul_of_nonneg_left hmx ha
    have hcomb2 := mul_le_mul_of_nonneg_left hmy hb
    have hlin_id :
        a * ((1 - x) * Real.log (partitionFn Sge1 μz) - μz * (T - 1)) +
          b * ((1 - y) * Real.log (partitionFn Sge1 μz) - μz * (T - 1)) =
        (1 - (a * x + b * y)) * Real.log (partitionFn Sge1 μz) - μz * (T - 1) := by
      calc a * ((1 - x) * Real.log (partitionFn Sge1 μz) - μz * (T - 1)) +
            b * ((1 - y) * Real.log (partitionFn Sge1 μz) - μz * (T - 1))
          = ((a + b) - (a * x + b * y)) * Real.log (partitionFn Sge1 μz) -
              (a + b) * (μz * (T - 1)) := by ring
        _ = (1 - (a * x + b * y)) * Real.log (partitionFn Sge1 μz) - μz * (T - 1) := by
            rw [hab]; ring
    have hconst_id :
        a * (Real.log 2 * (T - 1 / 2)) + b * (Real.log 2 * (T - 1 / 2)) =
          Real.log 2 * (T - 1 / 2) := by
      calc a * (Real.log 2 * (T - 1 / 2)) + b * (Real.log 2 * (T - 1 / 2))
          = (a + b) * (Real.log 2 * (T - 1 / 2)) := by ring
        _ = Real.log 2 * (T - 1 / 2) := by rw [hab, one_mul]
    linarith [hbin, hcomb1, hcomb2, hlin_id, hmz, hconst_id]
  have heq_p₁ : cappedDualValue Sge1 p₁ T = dualValue Sge1 T := by
    have hp₁_ico : p₁ ∈ Set.Ico (0 : ℝ) 1 := ⟨hp₁_mem.1.le, hp₁_mem.2⟩
    have h1mp₁_pos : 0 < 1 - p₁ := sub_pos.mpr hp₁_mem.2
    have hTp₁_gt1 : 1 < (T - 1) / (1 - p₁) := by
      rw [lt_div_iff₀ h1mp₁_pos]; linarith [hp₁_mem.1]
    rw [cappedDualValue_Sge1_eq_formula hT hp₁_ico,
      dualValue_Sge1_eq_at_sge1Tilt hTp₁_gt1,
      dualValue_Sge1_eq_at_sge1Tilt (by linarith : 1 < T)]
    dsimp [p₁] at htilt_red ⊢
    change binEntropy p₁ - Real.log 2 * (T - 1 / 2) +
        (1 - p₁) * (Real.log (partitionFn Sge1 (sge1Tilt ((T - 1) / (1 - p₁)))) -
          sge1Tilt ((T - 1) / (1 - p₁)) * ((T - 1) / (1 - p₁))) =
      Real.log (partitionFn Sge1 lam) - lam * T
    rw [htilt_red]
    unfold binEntropy
    rw [hlog_p₁, hlog_1mp₁]
    field_simp [h1mp₁_pos.ne']
    ring
  have hkl_bound : ∀ θ ∈ Set.Ico (0 : ℝ) 1,
      cappedDualValue Sge1 θ T ≤ dualValue Sge1 T ∧
        (θ ≠ p₁ → cappedDualValue Sge1 θ T < dualValue Sge1 T) := by
    intro θ hθ
    have h1mθ_pos : 0 < 1 - θ := sub_pos.mpr hθ.2
    have hTθ_gt1 : 1 < (T - 1) / (1 - θ) := by rw [lt_div_iff₀ h1mθ_pos]; linarith [hθ.1]
    have htest : dualValue Sge1 ((T - 1) / (1 - θ)) ≤
        Real.log (partitionFn Sge1 (lam - Real.log 2)) -
          (lam - Real.log 2) * ((T - 1) / (1 - θ)) :=
      ciInf_le (bddBelow_dual_Sge1 hTθ_gt1) (lam - Real.log 2)
    have hmul := mul_le_mul_of_nonneg_left htest h1mθ_pos.le
    have htest_id :
        binEntropy θ - Real.log 2 * (T - 1 / 2) +
            (1 - θ) * (Real.log (partitionFn Sge1 (lam - Real.log 2)) -
              (lam - Real.log 2) * ((T - 1) / (1 - θ))) =
          (Real.log (partitionFn Sge1 lam) - lam * T) +
            (binEntropy θ + θ * Real.log p₁ + (1 - θ) * Real.log (1 - p₁)) := by
      rw [hlog_p₁, hlog_1mp₁]
      field_simp [h1mθ_pos.ne']
      ring
    have hstep1 :
        cappedDualValue Sge1 θ T ≤
          dualValue Sge1 T +
            (binEntropy θ + θ * Real.log p₁ + (1 - θ) * Real.log (1 - p₁)) := by
      rw [cappedDualValue_Sge1_eq_formula hT hθ,
        dualValue_Sge1_eq_at_sge1Tilt (by linarith : 1 < T)]
      change binEntropy θ - Real.log 2 * (T - 1 / 2) +
          (1 - θ) * dualValue Sge1 ((T - 1) / (1 - θ)) ≤
        (Real.log (partitionFn Sge1 lam) - lam * T) + _
      linarith [hmul, htest_id]
    rcases eq_or_lt_of_le hθ.1 with rfl | hθ_pos
    · have hkl0 : binEntropy 0 + 0 * Real.log p₁ + (1 - 0) * Real.log (1 - p₁) < 0 := by
        unfold binEntropy
        simp only [neg_zero, zero_mul, sub_zero, Real.log_one, one_mul]
        dsimp only [p₁, lam]
        linarith [Real.log_neg (sub_pos.mpr hp₁_mem.2) (by linarith [hp₁_mem.1])]
      exact ⟨by linarith, fun _ ↦ by linarith⟩
    · by_cases hne : θ = p₁
      · subst hne
        exact ⟨heq_p₁.le, fun h ↦ absurd rfl h⟩
      · have hkl_neg : binEntropy θ + θ * Real.log p₁ + (1 - θ) * Real.log (1 - p₁) < 0 := by
          unfold binEntropy
          have hr1_pos : 0 < p₁ / θ := div_pos hp₁_mem.1 hθ_pos
          have hr2_pos : 0 < (1 - p₁) / (1 - θ) := div_pos (sub_pos.mpr hp₁_mem.2) h1mθ_pos
          have hr1_ne1 : p₁ / θ ≠ 1 := by
            intro h1
            exact hne ((div_eq_one_iff_eq hθ_pos.ne').mp h1).symm
          have hr2_ne1 : (1 - p₁) / (1 - θ) ≠ 1 := by
            intro h2
            have := (div_eq_one_iff_eq h1mθ_pos.ne').mp h2
            exact hne (by linarith)
          have hl1 := mul_lt_mul_of_pos_left (Real.log_lt_sub_one_of_pos hr1_pos hr1_ne1) hθ_pos
          have hl2 := mul_lt_mul_of_pos_left (Real.log_lt_sub_one_of_pos hr2_pos hr2_ne1) h1mθ_pos
          rw [Real.log_div hp₁_mem.1.ne' hθ_pos.ne'] at hl1
          rw [Real.log_div (sub_pos.mpr hp₁_mem.2).ne' h1mθ_pos.ne'] at hl2
          have hc1 : θ * (p₁ / θ - 1) = p₁ - θ := by field_simp [hθ_pos.ne']
          have hc2 : (1 - θ) * ((1 - p₁) / (1 - θ) - 1) = θ - p₁ := by
            field_simp [h1mθ_pos.ne']; ring
          dsimp only [p₁, lam] at hl1 hl2 hc1 hc2 ⊢
          linarith
        exact ⟨by linarith, fun _ ↦ by linarith⟩
  have hmono : StrictMonoOn (fun θ ↦ cappedDualValue Sge1 θ T) (Set.Icc 0 p₁) := by
    intro θ₁ hθ₁ θ₂ hθ₂ hlt
    have hθ₁_ico : θ₁ ∈ Set.Ico (0 : ℝ) 1 := ⟨hθ₁.1, lt_of_le_of_lt hθ₁.2 hp₁_mem.2⟩
    have hp₁_ico : p₁ ∈ Set.Ico (0 : ℝ) 1 := ⟨hp₁_mem.1.le, hp₁_mem.2⟩
    have hp₁_sub_pos : 0 < p₁ - θ₁ := by linarith [hlt, hθ₂.2]
    set α : ℝ := (θ₂ - θ₁) / (p₁ - θ₁)
    have hα_pos : 0 < α := div_pos (sub_pos.mpr hlt) hp₁_sub_pos
    have hα_le1 : α ≤ 1 := (div_le_one hp₁_sub_pos).mpr (by linarith [hθ₂.2])
    have h1mα_nn : 0 ≤ 1 - α := sub_nonneg.mpr hα_le1
    have hcomb : (1 - α) * θ₁ + α * p₁ = θ₂ := by
      dsimp [α]
      field_simp [hp₁_sub_pos.ne']
      ring
    have hc_ineq := hconc.2 hθ₁_ico hp₁_ico h1mα_nn hα_pos.le (by ring)
    simp only [smul_eq_mul] at hc_ineq
    rw [hcomb, heq_p₁] at hc_ineq
    have hstrict₁ : cappedDualValue Sge1 θ₁ T < dualValue Sge1 T :=
      (hkl_bound θ₁ hθ₁_ico).2 (by linarith [hlt, hθ₂.2])
    have hm_strict : α * cappedDualValue Sge1 θ₁ T < α * dualValue Sge1 T :=
      mul_lt_mul_of_pos_left hstrict₁ hα_pos
    linarith
  exact ⟨hconc, hmono, heq_p₁, fun θ hθ ↦ (hkl_bound θ hθ).1⟩

/-- **Lemma 3.2(iv) joint continuity and uniform `ϑ ↓ 0` boundary limit on `K_cap`:**
1. `(ϑ, T) ↦ 𝓕_{S_{≥ 1}}^{=ϑ}(T)` is jointly continuous on `[0, 1/20] × K_cap`;
2. `sup_{T ∈ K_cap} |𝓕_{S_{≥ 1}}^{=ϑ}(T) - 𝓕_{S_{≥ 2}}(T)| → 0` as `ϑ → 0` within `[0, 1/20]`. -/
theorem continuousOn_and_tendstoUniformlyOn_cappedDualValue_Sge1_zero :
    ContinuousOn (fun p : ℝ × ℝ ↦ cappedDualValue Sge1 p.1 p.2)
        (Set.Icc (0 : ℝ) (1 / 20) ×ˢ KcapInterval) ∧
      TendstoUniformlyOn (fun θ T ↦ cappedDualValue Sge1 θ T)
        (dualValue (Sge1 \ {1})) (nhdsWithin 0 (Set.Icc (0 : ℝ) (1 / 20))) KcapInterval := by
  obtain ⟨h2lo, h2hi⟩ := two_div_log_two_bounds
  have hTred_mem : ∀ θ ∈ Set.Icc (0 : ℝ) (1 / 20), ∀ T ∈ KcapInterval,
      T > 2 ∧ (T - 1) / (1 - θ) ∈ Set.Icc (9 / 4 : ℝ) (17 / 4) := by
    intro θ hθ T hT
    have h1mθ_pos : 0 < 1 - θ := by linarith [hθ.2]
    refine ⟨by linarith [hT.1, h2lo], ?_, ?_⟩
    · rw [le_div_iff₀ h1mθ_pos]; nlinarith [hθ.1, hθ.2, hT.1, h2lo]
    · rw [div_le_iff₀ h1mθ_pos]; nlinarith [hθ.1, hθ.2, hT.2, h2hi]
  have hcont_dual : ContinuousOn (dualValue Sge1) (Set.Icc (9 / 4 : ℝ) (17 / 4)) := by
    rw [Metric.continuousOn_iff]
    intro x hx eps heps
    set L : ℝ := 8 * dualLipschitzSpan + 1
    have hL_pos : 0 < L := by linarith [dualLipschitzSpan_nonneg]
    refine ⟨eps / L, div_pos heps hL_pos, fun y hy hdist ↦ ?_⟩
    rw [Real.dist_eq] at hdist ⊢
    have hlip := abs_dualValue_sub_le_of_mem_Icc S4_subset_Sge1 Sge1_subset_Splus hy hx
    have hmul : 8 * dualLipschitzSpan * |y - x| ≤ L * |y - x| := by
      dsimp [L]; nlinarith [abs_nonneg (y - x)]
    have hLyx : L * |y - x| < eps := by
      have := (lt_div_iff₀ hL_pos).mp hdist
      linarith
    exact lt_of_le_of_lt (hlip.trans hmul) hLyx
  have hcont_bin : ContinuousOn binEntropy (Set.Icc (0 : ℝ) (1 / 20)) := by
    unfold binEntropy
    have hc1 : Continuous (fun θ : ℝ ↦ -θ * Real.log θ) := by
      simpa [neg_mul] using Real.continuous_mul_log.neg
    have hc2 : ContinuousOn (fun θ : ℝ ↦ (1 - θ) * Real.log (1 - θ)) (Set.Icc 0 (1 / 20)) := by
      intro θ hθ
      have hne : 1 - θ ≠ 0 := by linarith [hθ.2]
      exact ((continuousAt_const.sub continuousAt_id).mul
        ((continuousAt_const.sub continuousAt_id).log hne)).continuousWithinAt
    exact hc1.continuousOn.sub hc2
  have hjoint : ContinuousOn (fun p : ℝ × ℝ ↦ cappedDualValue Sge1 p.1 p.2)
      (Set.Icc (0 : ℝ) (1 / 20) ×ˢ KcapInterval) := by
    have hform_eq : Set.EqOn (fun p : ℝ × ℝ ↦ cappedDualValue Sge1 p.1 p.2)
        (fun p : ℝ × ℝ ↦ binEntropy p.1 - Real.log 2 * (p.2 - 1 / 2) +
          (1 - p.1) * dualValue Sge1 ((p.2 - 1) / (1 - p.1)))
        (Set.Icc (0 : ℝ) (1 / 20) ×ˢ KcapInterval) := by
      rintro ⟨θ, T⟩ ⟨hθ, hT⟩
      exact cappedDualValue_Sge1_eq_formula (hTred_mem θ hθ T hT).1 ⟨hθ.1, by linarith [hθ.2]⟩
    refine ContinuousOn.congr ?_ hform_eq
    have hc_fst : ContinuousOn (fun p : ℝ × ℝ ↦ binEntropy p.1)
        (Set.Icc (0 : ℝ) (1 / 20) ×ˢ KcapInterval) :=
      hcont_bin.comp continuous_fst.continuousOn (fun _ hp ↦ hp.1)
    have hc_lin : ContinuousOn (fun p : ℝ × ℝ ↦ Real.log 2 * (p.2 - 1 / 2))
        (Set.Icc (0 : ℝ) (1 / 20) ×ˢ KcapInterval) :=
      (continuous_const.mul (continuous_snd.sub continuous_const)).continuousOn
    have hc_arg : ContinuousOn (fun p : ℝ × ℝ ↦ (p.2 - 1) / (1 - p.1))
        (Set.Icc (0 : ℝ) (1 / 20) ×ˢ KcapInterval) :=
      (continuous_snd.sub continuous_const).continuousOn.div
        (continuous_const.sub continuous_fst).continuousOn
        (fun _ hp ↦ by linarith [hp.1.2])
    have hc_comp : ContinuousOn (fun p : ℝ × ℝ ↦ dualValue Sge1 ((p.2 - 1) / (1 - p.1)))
        (Set.Icc (0 : ℝ) (1 / 20) ×ˢ KcapInterval) :=
      hcont_dual.comp hc_arg (fun p hp ↦ (hTred_mem p.1 hp.1 p.2 hp.2).2)
    exact (hc_fst.sub hc_lin).add
      ((continuous_const.sub continuous_fst).continuousOn.mul hc_comp)
  refine ⟨hjoint, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  have h3_mem : (3 : ℝ) ∈ Set.Icc (9 / 4 : ℝ) (17 / 4) := by norm_num
  set M_d : ℝ := |dualValue Sge1 3| + 16 * dualLipschitzSpan + 32 * dualLipschitzSpan + 1
  have hM_d_pos : 0 < M_d := by
    dsimp [M_d]; linarith [abs_nonneg (dualValue Sge1 3), dualLipschitzSpan_nonneg]
  have hbin0 : ContinuousWithinAt binEntropy (Set.Icc (0 : ℝ) (1 / 20)) 0 :=
    hcont_bin 0 ⟨le_rfl, by norm_num⟩
  have hbin_ev : ∀ᶠ θ : ℝ in nhdsWithin 0 (Set.Icc (0 : ℝ) (1 / 20)),
      |binEntropy θ| < eps / 2 := by
    have h0 : binEntropy 0 = 0 := by unfold binEntropy; simp
    have htend : Tendsto binEntropy (nhdsWithin 0 (Set.Icc (0 : ℝ) (1 / 20))) (nhds 0) := by
      have ht := hbin0.tendsto
      rwa [h0] at ht
    filter_upwards [htend.eventually (Metric.ball_mem_nhds 0 (half_pos heps))] with θ hθ
    simpa [Real.dist_eq] using hθ
  have hθ_small : ∀ᶠ θ : ℝ in nhdsWithin 0 (Set.Icc (0 : ℝ) (1 / 20)),
      θ ∈ Set.Icc (0 : ℝ) (1 / 20) ∧ θ < (eps / 2) / M_d := by
    have hmem : Set.Icc (0 : ℝ) (1 / 20) ∈ nhdsWithin 0 (Set.Icc (0 : ℝ) (1 / 20)) :=
      self_mem_nhdsWithin
    have hlt : Set.Iio ((eps / 2) / M_d) ∈ nhdsWithin 0 (Set.Icc (0 : ℝ) (1 / 20)) :=
      nhdsWithin_le_nhds (Iio_mem_nhds (div_pos (half_pos heps) hM_d_pos))
    exact Filter.inter_mem hmem hlt
  filter_upwards [hbin_ev, hθ_small] with θ hbin_lt ⟨hθ_icc, hθ_lt⟩ T hT
  rw [Real.dist_eq, ← cappedDualValue_zero Sge1 T]
  have hT_gt2 := (hTred_mem θ hθ_icc T hT).1
  have hTred_icc := (hTred_mem θ hθ_icc T hT).2
  have hT0_icc : T - 1 ∈ Set.Icc (9 / 4 : ℝ) (17 / 4) := by
    simpa using (hTred_mem 0 ⟨le_rfl, by norm_num⟩ T hT).2
  rw [cappedDualValue_Sge1_eq_formula hT_gt2 ⟨hθ_icc.1, by linarith [hθ_icc.2]⟩,
    cappedDualValue_Sge1_eq_formula hT_gt2 ⟨le_rfl, zero_lt_one⟩]
  have hdiff_id :
      (binEntropy 0 - Real.log 2 * (T - 1 / 2) + (1 - 0) * dualValue Sge1 ((T - 1) / (1 - 0))) -
        (binEntropy θ - Real.log 2 * (T - 1 / 2) +
          (1 - θ) * dualValue Sge1 ((T - 1) / (1 - θ))) =
      -binEntropy θ + θ * dualValue Sge1 (T - 1) +
        (1 - θ) * (dualValue Sge1 (T - 1) - dualValue Sge1 ((T - 1) / (1 - θ))) := by
    have hb0 : binEntropy 0 = 0 := by unfold binEntropy; simp
    rw [hb0]; simp only [sub_zero, div_one, one_mul]; ring
  rw [hdiff_id]
  have hd_bound : |dualValue Sge1 (T - 1)| ≤ |dualValue Sge1 3| + 16 * dualLipschitzSpan := by
    have hl := abs_dualValue_sub_le_of_mem_Icc S4_subset_Sge1 Sge1_subset_Splus hT0_icc h3_mem
    have hdist3 : |(T - 1) - 3| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith [hT0_icc.1, hT0_icc.2]
    have htri : |dualValue Sge1 (T - 1)| ≤
        |dualValue Sge1 (T - 1) - dualValue Sge1 3| + |dualValue Sge1 3| :=
      (congrArg abs (by ring : dualValue Sge1 (T - 1) =
        (dualValue Sge1 (T - 1) - dualValue Sge1 3) + dualValue Sge1 3)).trans_le (abs_add_le _ _)
    have hm := mul_le_mul_of_nonneg_left hdist3
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) dualLipschitzSpan_nonneg)
    linarith
  have h1mθ_pos : 0 < 1 - θ := by linarith [hθ_icc.2]
  have hlip_term :
      (1 - θ) * |dualValue Sge1 (T - 1) - dualValue Sge1 ((T - 1) / (1 - θ))| ≤
        32 * dualLipschitzSpan * θ := by
    have hl := abs_dualValue_sub_le_of_mem_Icc S4_subset_Sge1 Sge1_subset_Splus hT0_icc hTred_icc
    have hm := mul_le_mul_of_nonneg_left hl h1mθ_pos.le
    have hgap : (1 - θ) * |(T - 1) - (T - 1) / (1 - θ)| = θ * (T - 1) := by
      have halg : (T - 1) - (T - 1) / (1 - θ) = -(θ * (T - 1)) / (1 - θ) := by
        field_simp [h1mθ_pos.ne']; ring
      have hT1_pos : 0 ≤ T - 1 := by linarith [hT0_icc.1]
      rw [halg, abs_div, abs_neg, abs_of_nonneg (mul_nonneg hθ_icc.1 hT1_pos),
        abs_of_pos h1mθ_pos, mul_div_cancel₀ _ h1mθ_pos.ne']
    have hT1_le4 : T - 1 ≤ 4 := by
      have : 1 + 2 / Real.log 2 + 1 / 20 - 1 ≤ 4 := by linarith [h2hi]
      linarith [hT.2]
    calc (1 - θ) * |dualValue Sge1 (T - 1) - dualValue Sge1 ((T - 1) / (1 - θ))|
        ≤ (1 - θ) * (8 * dualLipschitzSpan * |(T - 1) - (T - 1) / (1 - θ)|) := hm
      _ = 8 * dualLipschitzSpan * ((1 - θ) * |(T - 1) - (T - 1) / (1 - θ)|) := by ring
      _ = 8 * dualLipschitzSpan * (θ * (T - 1)) := by rw [hgap]
      _ ≤ 8 * dualLipschitzSpan * (θ * 4) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hT1_le4 hθ_icc.1)
            (mul_nonneg (by norm_num) dualLipschitzSpan_nonneg)
      _ = 32 * dualLipschitzSpan * θ := by ring
  have htri_all :
      |-binEntropy θ + θ * dualValue Sge1 (T - 1) +
          (1 - θ) * (dualValue Sge1 (T - 1) - dualValue Sge1 ((T - 1) / (1 - θ)))| ≤
        |binEntropy θ| + M_d * θ := by
    have h1 := abs_add_le (-binEntropy θ + θ * dualValue Sge1 (T - 1))
      ((1 - θ) * (dualValue Sge1 (T - 1) - dualValue Sge1 ((T - 1) / (1 - θ))))
    have h2 := abs_add_le (-binEntropy θ) (θ * dualValue Sge1 (T - 1))
    rw [abs_neg, abs_mul, abs_of_nonneg hθ_icc.1] at h2
    rw [abs_mul, abs_of_pos h1mθ_pos] at h1
    have hm1 : θ * |dualValue Sge1 (T - 1)| ≤
        θ * (|dualValue Sge1 3| + 16 * dualLipschitzSpan) :=
      mul_le_mul_of_nonneg_left hd_bound hθ_icc.1
    have hMd_expand : M_d * θ =
        θ * (|dualValue Sge1 3| + 16 * dualLipschitzSpan) + 32 * dualLipschitzSpan * θ + θ := by
      dsimp [M_d]; ring
    linarith [hθ_icc.1]
  have hMθ_lt : M_d * θ < eps / 2 := by
    rwa [lt_div_iff₀ hM_d_pos, mul_comm] at hθ_lt
  linarith

/-!
## 3. Complete unconditional Section 9 `(J + 3)`-interval phase cover & dual-budget theorem
-/

private theorem continuousOn_p1Inf_and_strictMono :
    ContinuousOn p1Inf (Set.Icc (0 : ℝ) (1 + deltaStar)) ∧
      StrictMonoOn p1Inf (Set.Icc (0 : ℝ) (1 + deltaStar)) := by
  obtain ⟨h2lo, _⟩ := two_div_log_two_bounds
  have hT_gt2 : ∀ d ∈ Set.Icc (0 : ℝ) (1 + deltaStar), 2 < phaseTarget d := by
    intro d hd
    unfold phaseTarget deltaStar at *
    linarith [hd.2, h2lo]
  have hcont_tilt : ContinuousOn (extendedGaussianTilt q) (Set.Ioi (-1 : ℝ)) := by
    rw [Metric.continuousOn_iff]
    intro t0 ht0 eps heps
    set mu0 := extendedGaussianTilt q t0
    have hm0 : extendedGaussianMean q mu0 = t0 :=
      extendedGaussianMean_extendedGaussianTilt q_pos ht0
    have hsm := strictMono_extendedGaussianMean q q_pos
    set tlo := extendedGaussianMean q (mu0 - eps)
    set thi := extendedGaussianMean q (mu0 + eps)
    have hlo : tlo < t0 := by rw [← hm0]; exact hsm (by linarith)
    have hhi : t0 < thi := by rw [← hm0]; exact hsm (by linarith)
    refine ⟨min (t0 - tlo) (thi - t0), lt_min (by linarith) (by linarith), fun t ht hdist ↦ ?_⟩
    rw [Real.dist_eq] at hdist ⊢
    have hmt : extendedGaussianMean q (extendedGaussianTilt q t) = t :=
      extendedGaussianMean_extendedGaussianTilt q_pos ht
    have hd1 : |t - t0| < t0 - tlo := lt_of_lt_of_le hdist (min_le_left _ _)
    have hd2 : |t - t0| < thi - t0 := lt_of_lt_of_le hdist (min_le_right _ _)
    have ht_gt : tlo < t := by linarith [(abs_lt.mp hd1).1]
    have ht_lt : t < thi := by linarith [(abs_lt.mp hd2).2]
    have hmu_gt : mu0 - eps < extendedGaussianTilt q t := by
      apply hsm.lt_iff_lt.mp; rw [hmt]; exact ht_gt
    have hmu_lt : extendedGaussianTilt q t < mu0 + eps := by
      apply hsm.lt_iff_lt.mp; rw [hmt]; exact ht_lt
    rw [abs_lt]
    exact ⟨by linarith, by linarith⟩
  have hcont_p1At : Continuous p1AtTilt := by
    unfold p1AtTilt extendedGaussianExceptionalAtom
    have hc_num : Continuous (fun μ : ℝ ↦ Real.exp (-μ - q / 2)) :=
      Real.continuous_exp.comp (continuous_id.neg.sub continuous_const)
    have hc_den : Continuous (extendedGaussianPartition q) :=
      continuous_iff_continuousAt.mpr fun μ ↦
        (hasDerivAt_extendedGaussianPartition q μ q_pos).continuousAt
    exact hc_num.div hc_den fun _ ↦ extendedGaussianPartition_ne_zero q_pos
  have harg_mem : ∀ d ∈ Set.Icc (0 : ℝ) (1 + deltaStar),
      phaseTarget d - 2 ∈ Set.Ioi (-1 : ℝ) := by
    intro d hd
    have := hT_gt2 d hd
    exact Set.mem_Ioi.mpr (by linarith)
  refine ⟨?_, ?_⟩
  · have hfn : p1Inf = fun d ↦ p1AtTilt (extendedGaussianTilt q (phaseTarget d - 2)) :=
      funext p1Inf_eq_p1AtTilt
    rw [hfn]
    have hc_arg : Continuous (fun d : ℝ ↦ phaseTarget d - 2) := by
      unfold phaseTarget; exact (continuous_const.sub continuous_id).sub continuous_const
    exact hcont_p1At.continuousOn.comp
      (hcont_tilt.comp hc_arg.continuousOn harg_mem) (fun _ _ ↦ Set.mem_univ _)
  · intro d₁ hd₁ d₂ hd₂ hlt
    rw [p1Inf_eq_p1AtTilt, p1Inf_eq_p1AtTilt]
    apply strictAnti_p1AtTilt
    have hT_lt : phaseTarget d₂ - 2 < phaseTarget d₁ - 2 := by
      unfold phaseTarget; linarith
    have hm1 := extendedGaussianMean_extendedGaussianTilt q_pos
      (by linarith [hT_gt2 d₁ hd₁] : -1 < phaseTarget d₁ - 2)
    have hm2 := extendedGaussianMean_extendedGaussianTilt q_pos
      (by linarith [hT_gt2 d₂ hd₂] : -1 < phaseTarget d₂ - 2)
    exact (strictMono_extendedGaussianMean q q_pos).lt_iff_lt.mp (by linarith)

private theorem phaseTarget_mem_Kcap {d : ℝ} (hd : d ∈ Set.Icc (0 : ℝ) deltaStar) :
    phaseTarget d ∈ KcapInterval := by
  unfold phaseTarget KcapInterval deltaStar at *
  exact ⟨by linarith only [hd.2], by linarith only [hd.1]⟩

private theorem phaseTarget_mem_114_4 {d : ℝ} (hd : d ∈ Set.Icc (0 : ℝ) 1) :
    phaseTarget d ∈ Set.Icc (11 / 4 : ℝ) 4 := by
  obtain ⟨h2lo, h2hi⟩ := two_div_log_two_bounds
  unfold phaseTarget
  exact ⟨by linarith only [hd.2, h2lo], by linarith only [hd.1, h2hi]⟩

private theorem phaseTarget_sub_one_mem_114_4 {d : ℝ} (hd : d ∈ Set.Icc (0 : ℝ) deltaStar) :
    phaseTarget d - 1 ∈ Set.Icc (11 / 4 : ℝ) 4 := by
  obtain ⟨h2lo, h2hi⟩ := two_div_log_two_bounds
  unfold phaseTarget deltaStar at *
  exact ⟨by linarith only [hd.2, h2lo], by linarith only [hd.1, h2hi]⟩

private theorem continuousOn_dualValue_phaseTarget :
    ContinuousOn (fun d : ℝ ↦ dualValue Sge1 (phaseTarget d)) (Set.Icc (0 : ℝ) deltaStar) := by
  rw [Metric.continuousOn_iff]
  intro x hx r hr
  set L : ℝ := 8 * dualLipschitzSpan + 1
  have hL_pos : 0 < L := by dsimp [L]; linarith only [dualLipschitzSpan_nonneg]
  refine ⟨r / L, div_pos hr hL_pos, fun y hy hdist ↦ ?_⟩
  rw [Real.dist_eq] at hdist ⊢
  have hxI : phaseTarget x ∈ Set.Icc (9 / 4 : ℝ) (17 / 4) := by
    have h1 := phaseTarget_mem_114_4 ⟨hx.1, by unfold deltaStar at hx; linarith only [hx.2]⟩
    exact ⟨by linarith only [h1.1], by linarith only [h1.2]⟩
  have hyI : phaseTarget y ∈ Set.Icc (9 / 4 : ℝ) (17 / 4) := by
    have h1 := phaseTarget_mem_114_4 ⟨hy.1, by unfold deltaStar at hy; linarith only [hy.2]⟩
    exact ⟨by linarith only [h1.1], by linarith only [h1.2]⟩
  have hlip := abs_dualValue_sub_le_of_mem_Icc S4_subset_Sge1 Sge1_subset_Splus hyI hxI
  have ht_diff : |phaseTarget y - phaseTarget x| = |y - x| := by
    unfold phaseTarget
    rw [show (1 + 2 / Real.log 2 - y) - (1 + 2 / Real.log 2 - x) = -(y - x) by ring, abs_neg]
  rw [ht_diff] at hlip
  have hmul : 8 * dualLipschitzSpan * |y - x| ≤ L * |y - x| :=
    mul_le_mul_of_nonneg_right (by dsimp [L]; linarith only []) (abs_nonneg _)
  have hLyx : L * |y - x| < r := by
    have h1 := (lt_div_iff₀ hL_pos).mp hdist
    linarith only [h1]
  exact lt_of_le_of_lt (hlip.trans hmul) hLyx

private theorem phaseCover_transition_step {eps : ℝ} (heps : 0 < eps) :
    let eta : ℝ := (Real.log 2) ^ 3 * eps
    ∃ (δ₀ : ℝ) (M_tr : ℕ),
      δ₀ ∈ Set.Ioo (0 : ℝ) (1 / 1000) ∧
      8 ≤ M_tr ∧
      let p_tr : ℝ := capThresholdTheta (criticalPhaseX0 - 2 * δ₀)
      p_tr ∈ Set.Ioc (0 : ℝ) (1 / 40) ∧
      ∀ δ ∈ Set.Icc (criticalPhaseX0 - δ₀) (criticalPhaseX0 + δ₀),
        δ ∈ Set.Icc (0 : ℝ) deltaStar ∧
        phiInfAux p_tr + Real.log 2 / 2 * (phaseTarget δ - 1) ≤ -(Real.log 2 / 2 * δ₀) ∧
        0 ≤ dualValue Sge1 (phaseTarget δ) -
            cappedDualValue (S0M M_tr) p_tr (phaseTarget δ) ∧
        (Real.log 2) ^ 2 / 4 *
            (dualValue Sge1 (phaseTarget δ) -
              cappedDualValue (S0M M_tr) p_tr (phaseTarget δ)) < 2 * eta / 3 := by
  intro eta
  have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hq24_pos : 0 < (Real.log 2) ^ 2 / 4 := by positivity
  have heta_pos : 0 < eta := mul_pos (pow_pos hq_pos 3) heps
  set b_step : ℝ := (eta / 3) / ((Real.log 2) ^ 2 / 4)
  have hb_step_pos : 0 < b_step := div_pos (by linarith only [heta_pos]) hq24_pos
  have hb_step_eq : (Real.log 2) ^ 2 / 4 * b_step = eta / 3 := by
    dsimp [b_step]; exact mul_div_cancel₀ _ hq24_pos.ne'
  have hb_step_mul : ∀ x : ℝ, x < b_step → (Real.log 2) ^ 2 / 4 * x < eta / 3 := by
    intro x hx
    have hm := mul_lt_mul_of_pos_left hx hq24_pos
    linarith only [hm, hb_step_eq]
  obtain ⟨⟨hx0_lo, hx0_hi⟩, -, -, -⟩ := criticalPhaseX0_bounds_and_sign
  obtain ⟨h2lo, _⟩ := two_div_log_two_bounds
  obtain ⟨hcont_cap, _⟩ := continuousOn_and_tendstoUniformlyOn_cappedDualValue_Sge1_zero
  have hx0_dstar : criticalPhaseX0 ∈ Set.Icc (0 : ℝ) deltaStar := by
    unfold deltaStar; exact ⟨by linarith only [hx0_lo], by linarith only [hx0_hi]⟩
  have hx0_icc : criticalPhaseX0 ∈ Set.Icc (0 : ℝ) criticalPhaseX0 :=
    ⟨by linarith only [hx0_lo], le_rfl⟩
  have hval_x0 :
      dualValue Sge1 (phaseTarget criticalPhaseX0) -
        cappedDualValue Sge1 (capThresholdTheta criticalPhaseX0) (phaseTarget criticalPhaseX0) = 0 := by
    have hTx0_gt2 : 2 < phaseTarget criticalPhaseX0 := by
      unfold phaseTarget; linarith only [h2lo, hx0_hi]
    obtain ⟨-, -, heq_opt, -⟩ := cappedDualValue_Sge1_concave_strictMono_and_eq_dualValue hTx0_gt2
    rw [capThresholdTheta_x0_eq_p1Inf]
    have hp_def : p1Inf criticalPhaseX0 =
        gibbsProb Sge1 (sge1Tilt (phaseTarget criticalPhaseX0)) 1 := rfl
    rw [hp_def, heq_opt, sub_self]
  obtain ⟨hx0_th0, hx0_th40⟩ := capThresholdTheta_lt_one_div_40 hx0_icc
  obtain ⟨r_d1, hr_d1_pos, hr_d1⟩ :=
    Metric.continuousOn_iff.mp continuousOn_dualValue_phaseTarget criticalPhaseX0 hx0_dstar
      (b_step / 2) (half_pos hb_step_pos)
  have hx0_pair_mem :
      (capThresholdTheta criticalPhaseX0, phaseTarget criticalPhaseX0) ∈
        Set.Icc (0 : ℝ) (1 / 20) ×ˢ KcapInterval :=
    ⟨⟨hx0_th0, by linarith only [hx0_th40]⟩, phaseTarget_mem_Kcap hx0_dstar⟩
  obtain ⟨r_c1, hr_c1_pos, hr_c1⟩ :=
    Metric.continuousOn_iff.mp hcont_cap
      (capThresholdTheta criticalPhaseX0, phaseTarget criticalPhaseX0) hx0_pair_mem
      (b_step / 2) (half_pos hb_step_pos)
  obtain ⟨r_th1, hr_th1_pos, hr_th1⟩ :=
    Metric.continuousOn_iff.mp continuousOn_capThresholdTheta criticalPhaseX0 hx0_icc
      (r_c1 / 2) (half_pos hr_c1_pos)
  obtain ⟨r_tr, hr_tr_def⟩ : ∃ x : ℝ, x = min r_d1 (min (r_c1 / 2) r_th1) := ⟨_, rfl⟩
  have hr_tr_pos : 0 < r_tr := by
    rw [hr_tr_def]
    exact lt_min hr_d1_pos (lt_min (half_pos hr_c1_pos) hr_th1_pos)
  have hr_tr_d1 : r_tr ≤ r_d1 := by rw [hr_tr_def]; exact min_le_left _ _
  have hr_tr_c1 : r_tr ≤ r_c1 / 2 := by
    rw [hr_tr_def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hr_tr_th1 : r_tr ≤ r_th1 := by
    rw [hr_tr_def]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨δ₀, hδ₀_def⟩ : ∃ x : ℝ, x = min (1 / 2000) (r_tr / 4) := ⟨_, rfl⟩
  have hδ₀_pos : 0 < δ₀ := by
    rw [hδ₀_def]; exact lt_min (by norm_num) (by linarith only [hr_tr_pos])
  have hδ₀_lt : δ₀ < 1 / 1000 := by
    rw [hδ₀_def]; exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hδ₀_r : δ₀ ≤ r_tr / 4 := by rw [hδ₀_def]; exact min_le_right _ _
  obtain ⟨M_tr, hM_tr8, hM_tr_conv⟩ := tendstoUniformlyOn_cappedDualValue_S0M_Sge1 b_step hb_step_pos
  refine ⟨δ₀, M_tr, ⟨hδ₀_pos, hδ₀_lt⟩, hM_tr8, ?_⟩
  dsimp only
  obtain ⟨p_tr, hp_tr_def⟩ :
      ∃ x : ℝ, x = capThresholdTheta (criticalPhaseX0 - 2 * δ₀) := ⟨_, rfl⟩
  rw [← hp_tr_def]
  have hu_tr : criticalPhaseX0 - 2 * δ₀ ∈ Set.Ioc (0 : ℝ) criticalPhaseX0 :=
    ⟨by linarith only [hx0_lo, hδ₀_lt], by linarith only [hδ₀_pos]⟩
  obtain ⟨⟨hptr_lo, _⟩, -, -⟩ := capThresholdTheta_pos_spec hu_tr
  obtain ⟨-, hptr_hi⟩ := capThresholdTheta_lt_one_div_40 ⟨hu_tr.1.le, hu_tr.2⟩
  rw [← hp_tr_def] at hptr_lo hptr_hi
  have hptr_pos : 0 < p_tr := lt_trans (mul_pos (half_pos hq_pos) hu_tr.1) hptr_lo
  refine ⟨⟨hptr_pos, hptr_hi.le⟩, fun δ hδ ↦ ?_⟩
  have hδ_ds : δ ∈ Set.Icc (0 : ℝ) deltaStar := by
    unfold deltaStar
    exact ⟨by linarith only [hδ.1, hx0_lo, hδ₀_lt], by linarith only [hδ.2, hx0_hi, hδ₀_lt]⟩
  have hcap_margin :
      phiInfAux p_tr + Real.log 2 / 2 * (phaseTarget δ - 1) ≤ -(Real.log 2 / 2 * δ₀) := by
    rw [hp_tr_def, phiInfAux_capThresholdTheta_add_target hu_tr δ, ← mul_neg]
    exact mul_le_mul_of_nonneg_left (by linarith only [hδ.1]) (half_pos hq_pos).le
  have hTδ_gt2 : 2 < phaseTarget δ := by
    unfold phaseTarget; unfold deltaStar at hδ_ds; linarith only [hδ_ds.2, h2lo]
  obtain ⟨-, -, -, hle_dual⟩ := cappedDualValue_Sge1_concave_strictMono_and_eq_dualValue hTδ_gt2
  have hptr_ico : p_tr ∈ Set.Ico (0 : ℝ) 1 := ⟨hptr_pos.le, by linarith only [hptr_hi]⟩
  have hptr_icc20 : p_tr ∈ Set.Icc (0 : ℝ) (1 / 20) := ⟨hptr_pos.le, by linarith only [hptr_hi]⟩
  have hd1 : |δ - criticalPhaseX0| ≤ δ₀ :=
    abs_le.mpr ⟨by linarith only [hδ.1], by linarith only [hδ.2]⟩
  have hd1_lt : dist δ criticalPhaseX0 < r_d1 := by
    rw [Real.dist_eq]; linarith only [hd1, hδ₀_r, hr_tr_d1, hr_tr_pos]
  have hdual_near := hr_d1 δ hδ_ds hd1_lt
  rw [Real.dist_eq] at hdual_near
  have hth_lt : dist (criticalPhaseX0 - 2 * δ₀) criticalPhaseX0 < r_th1 := by
    rw [Real.dist_eq, show (criticalPhaseX0 - 2 * δ₀) - criticalPhaseX0 = -(2 * δ₀) by ring,
      abs_neg, abs_of_pos (by linarith only [hδ₀_pos])]
    linarith only [hδ₀_r, hr_tr_th1, hr_tr_pos]
  have hptr_near := hr_th1 (criticalPhaseX0 - 2 * δ₀) ⟨hu_tr.1.le, hu_tr.2⟩ hth_lt
  rw [← hp_tr_def] at hptr_near
  have hT_dist : dist (phaseTarget δ) (phaseTarget criticalPhaseX0) < r_c1 / 2 := by
    rw [Real.dist_eq]
    have ht_eq : |phaseTarget δ - phaseTarget criticalPhaseX0| = |δ - criticalPhaseX0| := by
      unfold phaseTarget
      rw [show (1 + 2 / Real.log 2 - δ) - (1 + 2 / Real.log 2 - criticalPhaseX0) =
        -(δ - criticalPhaseX0) by ring, abs_neg]
    rw [ht_eq]; linarith only [hd1, hδ₀_r, hr_tr_c1, hr_tr_pos]
  have hpair_lt :
      dist (p_tr, phaseTarget δ)
        (capThresholdTheta criticalPhaseX0, phaseTarget criticalPhaseX0) < r_c1 := by
    rw [Prod.dist_eq]
    exact max_lt (lt_trans hptr_near (by linarith only [hr_c1_pos]))
      (lt_trans hT_dist (by linarith only [hr_c1_pos]))
  have hmem_pair : (p_tr, phaseTarget δ) ∈ Set.Icc (0 : ℝ) (1 / 20) ×ˢ KcapInterval :=
    ⟨hptr_icc20, phaseTarget_mem_Kcap hδ_ds⟩
  have hcap_near := hr_c1 (p_tr, phaseTarget δ) hmem_pair hpair_lt
  rw [Real.dist_eq] at hcap_near
  have htr_near :
      dualValue Sge1 (phaseTarget δ) - cappedDualValue Sge1 p_tr (phaseTarget δ) < b_step := by
    have hid :
        dualValue Sge1 (phaseTarget δ) - cappedDualValue Sge1 p_tr (phaseTarget δ) =
          (dualValue Sge1 (phaseTarget δ) - dualValue Sge1 (phaseTarget criticalPhaseX0)) -
            (cappedDualValue Sge1 p_tr (phaseTarget δ) -
              cappedDualValue Sge1 (capThresholdTheta criticalPhaseX0)
                (phaseTarget criticalPhaseX0)) +
            (dualValue Sge1 (phaseTarget criticalPhaseX0) -
              cappedDualValue Sge1 (capThresholdTheta criticalPhaseX0)
                (phaseTarget criticalPhaseX0)) := by ring
    have h_a : dualValue Sge1 (phaseTarget δ) - dualValue Sge1 (phaseTarget criticalPhaseX0) <
        b_step / 2 := lt_of_le_of_lt (le_abs_self _) hdual_near
    have h_b : -(cappedDualValue Sge1 p_tr (phaseTarget δ) -
        cappedDualValue Sge1 (capThresholdTheta criticalPhaseX0)
          (phaseTarget criticalPhaseX0)) < b_step / 2 :=
      lt_of_le_of_lt (neg_le_abs _) hcap_near
    linarith only [hid, h_a, h_b, hval_x0]
  have h1_nn : 0 ≤ dualValue Sge1 (phaseTarget δ) - cappedDualValue Sge1 p_tr (phaseTarget δ) :=
    sub_nonneg.mpr (hle_dual p_tr hptr_ico)
  obtain ⟨h2_nn, h2_lt⟩ := hM_tr_conv M_tr le_rfl p_tr hptr_icc20
    (phaseTarget δ) (phaseTarget_mem_Kcap hδ_ds)
  exact ⟨hδ_ds, hcap_margin, by linarith only [h1_nn, h2_nn], by
    have hm1 := hb_step_mul _ htr_near
    have hm2 := hb_step_mul _ h2_lt
    linarith only [hm1, hm2]⟩

private theorem phaseCover_main_step {eps δ₀ : ℝ} (heps : 0 < eps)
    (hδ₀ : δ₀ ∈ Set.Ioo (0 : ℝ) (1 / 1000)) :
    let eta : ℝ := (Real.log 2) ^ 3 * eps
    ∃ M_main : ℕ, 7 ≤ M_main ∧
      ∀ δ ∈ Set.Ico (criticalPhaseX0 + δ₀) 1,
        0 ≤ dualValue Sge1 (phaseTarget δ) - dualValue (S0M M_main) (phaseTarget δ) ∧
          (Real.log 2) ^ 2 / 4 *
              (dualValue Sge1 (phaseTarget δ) - dualValue (S0M M_main) (phaseTarget δ)) <
            2 * eta / 3 := by
  intro eta
  have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hq24_pos : 0 < (Real.log 2) ^ 2 / 4 := by positivity
  have heta_pos : 0 < eta := mul_pos (pow_pos hq_pos 3) heps
  set b_step : ℝ := (eta / 3) / ((Real.log 2) ^ 2 / 4)
  have hb_step_pos : 0 < b_step := div_pos (by linarith only [heta_pos]) hq24_pos
  have hb_step_eq : (Real.log 2) ^ 2 / 4 * b_step = eta / 3 := by
    dsimp [b_step]; exact mul_div_cancel₀ _ hq24_pos.ne'
  obtain ⟨⟨hx0_lo, _⟩, -, -, -⟩ := criticalPhaseX0_bounds_and_sign
  obtain ⟨M_main, hM_main7, hM_main_conv⟩ :=
    tendstoUniformlyOn_dualValue_S0M_Sge1 (2 * b_step) (by linarith only [hb_step_pos])
  refine ⟨M_main, hM_main7, fun δ hδ ↦ ?_⟩
  have hT_icc := phaseTarget_mem_114_4 ⟨by linarith only [hδ.1, hx0_lo, hδ₀.1], hδ.2.le⟩
  obtain ⟨hnn, hlt⟩ := hM_main_conv M_main le_rfl (phaseTarget δ) hT_icc
  refine ⟨hnn, ?_⟩
  have hm := mul_lt_mul_of_pos_left hlt hq24_pos
  linarith only [hm, hb_step_eq]

private theorem phaseCover_nearZero_step {eps δ₀ : ℝ} (heps : 0 < eps)
    (hδ₀ : δ₀ ∈ Set.Ioo (0 : ℝ) (1 / 1000)) :
    let eta : ℝ := (Real.log 2) ^ 3 * eps
    ∃ (a₁ : ℝ) (M₀ : ℕ),
      a₁ ∈ Set.Ioo (0 : ℝ) ((criticalPhaseX0 - δ₀) / 3) ∧
      7 ≤ M₀ ∧
      let θBar₀ : ℝ := capThresholdTheta (2 * a₁)
      θBar₀ ∈ Set.Ioc (0 : ℝ) (1 / 20) ∧
      ∀ δ ∈ Set.Icc (0 : ℝ) a₁,
        θBar₀ ≤ p1Inf δ ∧
        Real.log 2 / 2 * a₁ ≤ phiInfAux θBar₀ + Real.log 2 / 2 * (phaseTarget δ - 1) ∧
        (Real.log 2) ^ 2 / 4 *
            |(cappedDualValue Sge1 θBar₀ (phaseTarget δ) -
              dualValue (shiftSupportOne (S0M M₀)) (phaseTarget δ))| < 2 * eta / 3 := by
  intro eta
  have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hq24_pos : 0 < (Real.log 2) ^ 2 / 4 := by positivity
  have heta_pos : 0 < eta := mul_pos (pow_pos hq_pos 3) heps
  set b_step : ℝ := (eta / 3) / ((Real.log 2) ^ 2 / 4)
  have hb_step_pos : 0 < b_step := div_pos (by linarith only [heta_pos]) hq24_pos
  have hb_step_eq : (Real.log 2) ^ 2 / 4 * b_step = eta / 3 := by
    dsimp [b_step]; exact mul_div_cancel₀ _ hq24_pos.ne'
  obtain ⟨⟨hx0_lo, hx0_hi⟩, -, -, -⟩ := criticalPhaseX0_bounds_and_sign
  obtain ⟨_, hlim_cap0⟩ := continuousOn_and_tendstoUniformlyOn_cappedDualValue_Sge1_zero
  obtain ⟨_, hmono_p1⟩ := continuousOn_p1Inf_and_strictMono
  have hp1_0_pos : 0 < p1Inf 0 := by
    rw [p1Inf_eq_p1AtTilt]; exact (p1AtTilt_mem_Ioo _).1
  obtain ⟨r_cap0, hr_cap0_pos, hr_cap0_sub⟩ :=
    Metric.mem_nhdsWithin_iff.mp (Metric.tendstoUniformlyOn_iff.mp hlim_cap0 b_step hb_step_pos)
  have hr_cap0 : ∀ θ : ℝ, θ ∈ Metric.ball (0 : ℝ) r_cap0 ∩ Set.Icc 0 (1 / 20) →
      ∀ T ∈ KcapInterval, dist (dualValue (Sge1 \ {1}) T) (cappedDualValue Sge1 θ T) < b_step :=
    fun θ hθ ↦ hr_cap0_sub hθ
  obtain ⟨θ_max₀, hθ_max₀_def⟩ :
      ∃ x : ℝ, x = min (p1Inf 0 / 2) (min (r_cap0 / 2) (1 / 40)) := ⟨_, rfl⟩
  have hθ_max₀_pos : 0 < θ_max₀ := by
    rw [hθ_max₀_def]
    exact lt_min (half_pos hp1_0_pos) (lt_min (half_pos hr_cap0_pos) (by norm_num))
  have hθ_max₀_p1 : θ_max₀ ≤ p1Inf 0 / 2 := by rw [hθ_max₀_def]; exact min_le_left _ _
  have hθ_max₀_r0 : θ_max₀ ≤ r_cap0 / 2 := by
    rw [hθ_max₀_def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hθ_max₀_40 : θ_max₀ ≤ 1 / 40 := by
    rw [hθ_max₀_def]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨a₁, ha₁_def⟩ :
      ∃ x : ℝ, x = min ((criticalPhaseX0 - δ₀) / 4) (θ_max₀ / (2 * Real.log 2)) := ⟨_, rfl⟩
  have ha₁_pos : 0 < a₁ := by
    rw [ha₁_def]
    exact lt_min (by linarith only [hx0_lo, hδ₀.2])
      (div_pos hθ_max₀_pos (mul_pos two_pos hq_pos))
  have ha₁_lt : a₁ < (criticalPhaseX0 - δ₀) / 3 := by
    have h1 : a₁ ≤ (criticalPhaseX0 - δ₀) / 4 := by rw [ha₁_def]; exact min_le_left _ _
    linarith only [h1, hx0_lo, hδ₀.2]
  have ha₁_th : a₁ ≤ θ_max₀ / (2 * Real.log 2) := by rw [ha₁_def]; exact min_le_right _ _
  obtain ⟨M₀, hM₀7, hM₀_conv⟩ := tendstoUniformlyOn_dualValue_S0M_Sge1 b_step hb_step_pos
  refine ⟨a₁, M₀, ⟨ha₁_pos, ha₁_lt⟩, hM₀7, ?_⟩
  dsimp only
  obtain ⟨θBar₀, hθBar₀_def⟩ : ∃ x : ℝ, x = capThresholdTheta (2 * a₁) := ⟨_, rfl⟩
  rw [← hθBar₀_def]
  have h2a₁_ioc : 2 * a₁ ∈ Set.Ioc (0 : ℝ) criticalPhaseX0 :=
    ⟨by linarith only [ha₁_pos], by linarith only [ha₁_lt, hx0_lo, hδ₀.1, hδ₀.2]⟩
  obtain ⟨⟨hθ₀_lo, hθ₀_hi⟩, -, -⟩ := capThresholdTheta_pos_spec h2a₁_ioc
  rw [← hθBar₀_def] at hθ₀_lo hθ₀_hi
  have h2a₁_bound : Real.log 2 * (2 * a₁) ≤ θ_max₀ := by
    have hm := mul_le_mul_of_nonneg_left ha₁_th (mul_nonneg two_pos.le hq_pos.le)
    have hc : (2 * Real.log 2) * (θ_max₀ / (2 * Real.log 2)) = θ_max₀ :=
      mul_div_cancel₀ _ (mul_pos two_pos hq_pos).ne'
    linarith only [hm, hc]
  have hθ₀_lt_max : θBar₀ < θ_max₀ := lt_of_lt_of_le hθ₀_hi h2a₁_bound
  have hθ₀_pos : 0 < θBar₀ := lt_trans (mul_pos (half_pos hq_pos) h2a₁_ioc.1) hθ₀_lo
  have hθ₀_lt20 : θBar₀ < 1 / 20 := by linarith only [hθ₀_lt_max, hθ_max₀_40]
  refine ⟨⟨hθ₀_pos, hθ₀_lt20.le⟩, fun δ hδ ↦ ?_⟩
  have hδ_ds : δ ∈ Set.Icc (0 : ℝ) deltaStar := by
    unfold deltaStar
    exact ⟨hδ.1, by linarith only [hδ.2, ha₁_lt, hx0_hi, hδ₀.1]⟩
  have hp1_mono : p1Inf 0 ≤ p1Inf δ := by
    rcases eq_or_lt_of_le hδ.1 with rfl | hd_pos
    · exact le_rfl
    · exact (hmono_p1 ⟨le_rfl, by unfold deltaStar; norm_num⟩
        ⟨hδ.1, le_trans hδ_ds.2 (le_add_of_nonneg_left zero_le_one)⟩ hd_pos).le
  have hθ₀_le_p1 : θBar₀ ≤ p1Inf δ := by
    linarith only [hθ₀_lt_max, hθ_max₀_p1, hp1_0_pos, hp1_mono]
  have hmargin₀ : Real.log 2 / 2 * a₁ ≤ phiInfAux θBar₀ + Real.log 2 / 2 * (phaseTarget δ - 1) := by
    rw [hθBar₀_def, phiInfAux_capThresholdTheta_add_target h2a₁_ioc δ]
    exact mul_le_mul_of_nonneg_left (by linarith only [hδ.2]) (half_pos hq_pos).le
  have hθ₀_ball : θBar₀ ∈ Metric.ball (0 : ℝ) r_cap0 ∩ Set.Icc 0 (1 / 20) := by
    refine ⟨?_, ⟨hθ₀_pos.le, hθ₀_lt20.le⟩⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hθ₀_pos]
    linarith only [hθ₀_lt_max, hθ_max₀_r0, hr_cap0_pos]
  have hcap0_lt := hr_cap0 θBar₀ hθ₀_ball (phaseTarget δ) (phaseTarget_mem_Kcap hδ_ds)
  rw [Real.dist_eq] at hcap0_lt
  have hTm1_icc := phaseTarget_sub_one_mem_114_4 hδ_ds
  have hTm1_25 : phaseTarget δ - 1 ∈ Set.Ioo (2 : ℝ) 5 :=
    ⟨by linarith only [hTm1_icc.1], by linarith only [hTm1_icc.2]⟩
  have hm4 := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hTm1_25)
  have hS4_sub : S4 ⊆ S0M M₀ := by
    intro i hi
    simp only [S4, Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    simp only [S0M, Set.mem_setOf_eq]
    have : (7 : ℤ) ≤ (M₀ : ℤ) := by exact_mod_cast hM₀7
    omega
  have hdiff_sge1 : Sge1 \ {1} = shiftSupportOne Sge1 := by
    ext j; simp only [shiftSupportOne, Sge1, Set.mem_setOf_eq, Set.mem_sdiff,
      Set.mem_singleton_iff]; omega
  have hsh_eq := dualValue_diff_shiftSupportOne (R := Sge1) (S := S0M M₀)
    ⟨1, by simp [Sge1]⟩ ⟨1, by simp [S0M]; omega⟩
    (bddBelow_dual S4_subset_Sge1 hm4) (bddBelow_dual hS4_sub hm4)
  rw [sub_add_cancel] at hsh_eq
  obtain ⟨h0_nn, h0_lt⟩ := hM₀_conv M₀ le_rfl (phaseTarget δ - 1) hTm1_icc
  have htail_abs :
      |dualValue (Sge1 \ {1}) (phaseTarget δ) -
          dualValue (shiftSupportOne (S0M M₀)) (phaseTarget δ)| < b_step := by
    rw [hdiff_sge1, hsh_eq, abs_of_nonneg h0_nn]
    exact h0_lt
  have htri :
      |cappedDualValue Sge1 θBar₀ (phaseTarget δ) -
          dualValue (shiftSupportOne (S0M M₀)) (phaseTarget δ)| < 2 * b_step := by
    have hid :
        cappedDualValue Sge1 θBar₀ (phaseTarget δ) -
            dualValue (shiftSupportOne (S0M M₀)) (phaseTarget δ) =
          -(dualValue (Sge1 \ {1}) (phaseTarget δ) - cappedDualValue Sge1 θBar₀ (phaseTarget δ)) +
            (dualValue (Sge1 \ {1}) (phaseTarget δ) -
              dualValue (shiftSupportOne (S0M M₀)) (phaseTarget δ)) := by ring
    rw [hid]
    have ha := abs_add_le
      (-(dualValue (Sge1 \ {1}) (phaseTarget δ) - cappedDualValue Sge1 θBar₀ (phaseTarget δ)))
      (dualValue (Sge1 \ {1}) (phaseTarget δ) - dualValue (shiftSupportOne (S0M M₀)) (phaseTarget δ))
    rw [abs_neg] at ha
    linarith only [ha, hcap0_lt, htail_abs]
  refine ⟨hθ₀_le_p1, hmargin₀, ?_⟩
  have hm := mul_lt_mul_of_pos_left htri hq24_pos
  linarith only [hm, hb_step_eq]

private theorem phaseCover_mesh_step {eps δ₀ a₁ : ℝ} (heps : 0 < eps)
    (hδ₀ : δ₀ ∈ Set.Ioo (0 : ℝ) (1 / 1000))
    (ha₁ : a₁ ∈ Set.Ioo (0 : ℝ) ((criticalPhaseX0 - δ₀) / 3)) :
    let eta : ℝ := (Real.log 2) ^ 3 * eps
    ∃ (N_mesh M_cap : ℕ),
      1 ≤ N_mesh ∧ 8 ≤ M_cap ∧
      let h : ℝ := (criticalPhaseX0 - δ₀ - a₁) / (N_mesh : ℝ)
      (h ∈ Set.Ioo (0 : ℝ) (min (a₁ / 2) (δ₀ / 2)) ∧
        ∀ j : Fin N_mesh,
          let a_lo : ℝ := a₁ + (j.1 : ℝ) * h
          let a_hi : ℝ := a₁ + ((j.1 + 1 : ℕ) : ℝ) * h
          let θBar_j : ℝ := capThresholdTheta (a_hi + h)
          let θUnder_j : ℝ := capThresholdTheta (a_lo - h)
          θBar_j ∈ Set.Ioc (0 : ℝ) (1 / 20) ∧
          θUnder_j ∈ Set.Ioc (0 : ℝ) (1 / 40) ∧
          ∀ δ ∈ Set.Icc a_lo a_hi,
            δ ∈ Set.Icc a₁ deltaStar ∧
            θBar_j ≤ p1Inf δ ∧
            Real.log 2 / 2 * h ≤ phiInfAux θBar_j + Real.log 2 / 2 * (phaseTarget δ - 1) ∧
            phiInfAux θUnder_j + Real.log 2 / 2 * (phaseTarget δ - 1) ≤
              -(Real.log 2 / 2 * h) ∧
            0 ≤ cappedDualValue Sge1 θBar_j (phaseTarget δ) -
                cappedDualValue (S0M M_cap) θUnder_j (phaseTarget δ) ∧
            (Real.log 2) ^ 2 / 4 *
                (cappedDualValue Sge1 θBar_j (phaseTarget δ) -
                  cappedDualValue (S0M M_cap) θUnder_j (phaseTarget δ)) < 2 * eta / 3) ∧
      (∀ δ ∈ Set.Ico (0 : ℝ) 1,
        δ ∈ Set.Icc 0 a₁ ∨
          (∃ j : Fin N_mesh,
            δ ∈ Set.Icc (a₁ + (j.1 : ℝ) * h) (a₁ + ((j.1 + 1 : ℕ) : ℝ) * h)) ∨
          δ ∈ Set.Icc (criticalPhaseX0 - δ₀) (criticalPhaseX0 + δ₀) ∨
          δ ∈ Set.Ico (criticalPhaseX0 + δ₀) 1) := by
  intro eta
  have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hq24_pos : 0 < (Real.log 2) ^ 2 / 4 := by positivity
  have heta_pos : 0 < eta := mul_pos (pow_pos hq_pos 3) heps
  set b_step : ℝ := (eta / 3) / ((Real.log 2) ^ 2 / 4)
  have hb_step_pos : 0 < b_step := div_pos (by linarith only [heta_pos]) hq24_pos
  have hb_step_eq : (Real.log 2) ^ 2 / 4 * b_step = eta / 3 := by
    dsimp [b_step]; exact mul_div_cancel₀ _ hq24_pos.ne'
  have hb_step_mul : ∀ x : ℝ, x < b_step → (Real.log 2) ^ 2 / 4 * x < eta / 3 := by
    intro x hx
    have hm := mul_lt_mul_of_pos_left hx hq24_pos
    linarith only [hm, hb_step_eq]
  obtain ⟨⟨hx0_lo, hx0_hi⟩, -, -, -⟩ := criticalPhaseX0_bounds_and_sign
  obtain ⟨h2lo, _⟩ := two_div_log_two_bounds
  obtain ⟨hcont_cap, _⟩ := continuousOn_and_tendstoUniformlyOn_cappedDualValue_Sge1_zero
  obtain ⟨hcont_p1, _⟩ := continuousOn_p1Inf_and_strictMono
  have ha₁_lt_x0d : a₁ < criticalPhaseX0 - δ₀ := by
    linarith only [ha₁.1, ha₁.2, hx0_lo, hδ₀.2]
  have hgap_cont : ContinuousOn (fun d : ℝ ↦ p1Inf d - capThresholdTheta d)
      (Set.Icc a₁ (criticalPhaseX0 - δ₀)) :=
    (hcont_p1.mono (fun d hd ↦ ⟨by linarith only [hd.1, ha₁.1],
      by unfold deltaStar; linarith only [hd.2, hx0_hi, hδ₀.1]⟩)).sub
      (continuousOn_capThresholdTheta.mono (fun d hd ↦
        ⟨by linarith only [hd.1, ha₁.1], by linarith only [hd.2, hδ₀.1]⟩))
  obtain ⟨d_min, hd_min_mem, hd_min_is⟩ :=
    (isCompact_Icc.image_of_continuousOn hgap_cont).exists_isLeast
      (Set.Nonempty.image _ (nonempty_Icc.mpr ha₁_lt_x0d.le))
  rcases hd_min_mem with ⟨d₀, hd₀_mem, hd₀_eq⟩
  have hm_gap_pos : 0 < p1Inf d₀ - capThresholdTheta d₀ :=
    sub_pos.mpr (capThresholdTheta_lt_p1Inf_of_lt_x0
      ⟨by linarith only [hd₀_mem.1, ha₁.1], by linarith only [hd₀_mem.2, hδ₀.1]⟩)
  have hu_cap := (isCompact_Icc.prod (isCompact_Icc : IsCompact KcapInterval)).uniformContinuousOn_of_continuous
    hcont_cap
  obtain ⟨r_ucap, hr_ucap_pos, hr_ucap⟩ := Metric.uniformContinuousOn_iff.mp hu_cap b_step hb_step_pos
  have hu_th := isCompact_Icc.uniformContinuousOn_of_continuous continuousOn_capThresholdTheta
  obtain ⟨r_uth, hr_uth_pos, hr_uth⟩ :=
    Metric.uniformContinuousOn_iff.mp hu_th (min (p1Inf d₀ - capThresholdTheta d₀) (r_ucap / 2))
      (lt_min hm_gap_pos (half_pos hr_ucap_pos))
  obtain ⟨h_bound, hh_bound_def⟩ :
      ∃ x : ℝ, x = min (min (a₁ / 2) (δ₀ / 2)) (min (r_uth / 4) (r_ucap / 4)) := ⟨_, rfl⟩
  have hh_bound_pos : 0 < h_bound := by
    rw [hh_bound_def]
    exact lt_min (lt_min (half_pos ha₁.1) (half_pos hδ₀.1))
      (lt_min (by linarith only [hr_uth_pos]) (by linarith only [hr_ucap_pos]))
  have hh_b_min : h_bound ≤ min (a₁ / 2) (δ₀ / 2) := by rw [hh_bound_def]; exact min_le_left _ _
  have hh_b_uth : h_bound ≤ r_uth / 4 := by
    rw [hh_bound_def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  obtain ⟨N_mesh, hN_mesh_def⟩ :
      ∃ N : ℕ, N = Nat.floor ((criticalPhaseX0 - δ₀ - a₁) / h_bound) + 1 := ⟨_, rfl⟩
  have hN_mesh_ge1 : 1 ≤ N_mesh := by rw [hN_mesh_def]; exact Nat.succ_le_succ (Nat.zero_le _)
  have hN_mesh_pos : (0 : ℝ) < (N_mesh : ℝ) := by exact_mod_cast hN_mesh_ge1
  obtain ⟨h, hh_def⟩ : ∃ x : ℝ, x = (criticalPhaseX0 - δ₀ - a₁) / (N_mesh : ℝ) := ⟨_, rfl⟩
  have hh_pos : 0 < h := by
    rw [hh_def]; exact div_pos (by linarith only [ha₁_lt_x0d]) hN_mesh_pos
  have hh_mul : (N_mesh : ℝ) * h = criticalPhaseX0 - δ₀ - a₁ := by
    rw [hh_def]; exact mul_div_cancel₀ _ hN_mesh_pos.ne'
  have hh_lt_bound : h < h_bound := by
    rw [hh_def, div_lt_iff₀ hN_mesh_pos, hN_mesh_def]
    have hfl := Nat.lt_floor_add_one ((criticalPhaseX0 - δ₀ - a₁) / h_bound)
    have hm := (div_lt_iff₀ hh_bound_pos).mp hfl
    push_cast
    linarith only [hm, hh_bound_pos]
  obtain ⟨M_cap, hM_cap8, hM_cap_conv⟩ := tendstoUniformlyOn_cappedDualValue_S0M_Sge1 b_step hb_step_pos
  refine ⟨N_mesh, M_cap, hN_mesh_ge1, hM_cap8, ?_⟩
  dsimp only
  rw [← hh_def]
  refine ⟨?_, ?_⟩
  · have hh_lt_min : h < min (a₁ / 2) (δ₀ / 2) := lt_of_lt_of_le hh_lt_bound hh_b_min
    refine ⟨⟨hh_pos, hh_lt_min⟩, fun j ↦ ?_⟩
    obtain ⟨a_lo, ha_lo_def⟩ : ∃ x : ℝ, x = a₁ + (j.1 : ℝ) * h := ⟨_, rfl⟩
    obtain ⟨a_hi, ha_hi_def⟩ : ∃ x : ℝ, x = a₁ + ((j.1 + 1 : ℕ) : ℝ) * h := ⟨_, rfl⟩
    rw [← ha_lo_def, ← ha_hi_def]
    have hj_le : ((j.1 + 1 : ℕ) : ℝ) ≤ (N_mesh : ℝ) := by exact_mod_cast j.2
    have ha_hi_le : a_hi ≤ criticalPhaseX0 - δ₀ := by
      have hm := mul_le_mul_of_nonneg_right hj_le hh_pos.le
      linarith only [ha_hi_def, hm, hh_mul]
    have ha_lo_ge : a₁ ≤ a_lo := by
      rw [ha_lo_def]; exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hh_pos.le)
    have ha_hi_sub : a_hi - a_lo = h := by rw [ha_hi_def, ha_lo_def]; push_cast; ring
    have hhi_ioc : a_hi + h ∈ Set.Ioc (0 : ℝ) criticalPhaseX0 := by
      have hh_d : h < δ₀ / 2 := lt_of_lt_of_le hh_lt_min (min_le_right _ _)
      exact ⟨by linarith only [ha₁.1, ha_lo_ge, ha_hi_sub, hh_pos],
        by linarith only [ha_hi_le, hh_d, hδ₀.1]⟩
    have hlo_ioc : a_lo - h ∈ Set.Ioc (0 : ℝ) criticalPhaseX0 := by
      have hh_a : h < a₁ / 2 := lt_of_lt_of_le hh_lt_min (min_le_left _ _)
      exact ⟨by linarith only [ha_lo_ge, hh_a, ha₁.1],
        by linarith only [ha_hi_le, ha_hi_sub, hh_pos, hδ₀.1]⟩
    obtain ⟨θBar_j, hθBar_j_def⟩ : ∃ x : ℝ, x = capThresholdTheta (a_hi + h) := ⟨_, rfl⟩
    obtain ⟨θUnder_j, hθUnder_j_def⟩ : ∃ x : ℝ, x = capThresholdTheta (a_lo - h) := ⟨_, rfl⟩
    rw [← hθBar_j_def, ← hθUnder_j_def]
    obtain ⟨⟨hb_lo, _⟩, -, -⟩ := capThresholdTheta_pos_spec hhi_ioc
    obtain ⟨-, hb_hi⟩ := capThresholdTheta_lt_one_div_40 ⟨hhi_ioc.1.le, hhi_ioc.2⟩
    obtain ⟨⟨hu_lo, _⟩, -, -⟩ := capThresholdTheta_pos_spec hlo_ioc
    obtain ⟨-, hu_hi⟩ := capThresholdTheta_lt_one_div_40 ⟨hlo_ioc.1.le, hlo_ioc.2⟩
    rw [← hθBar_j_def] at hb_lo hb_hi
    rw [← hθUnder_j_def] at hu_lo hu_hi
    have hbar_pos : 0 < θBar_j := lt_trans (mul_pos (half_pos hq_pos) hhi_ioc.1) hb_lo
    have hunder_pos : 0 < θUnder_j := lt_trans (mul_pos (half_pos hq_pos) hlo_ioc.1) hu_lo
    refine ⟨⟨hbar_pos, by linarith only [hb_hi]⟩, ⟨hunder_pos, hu_hi.le⟩, fun δ hδ ↦ ?_⟩
    have hδ_mesh : δ ∈ Set.Icc a₁ (criticalPhaseX0 - δ₀) :=
      ⟨le_trans ha_lo_ge hδ.1, le_trans hδ.2 ha_hi_le⟩
    have hδ_ds : δ ∈ Set.Icc a₁ deltaStar :=
      ⟨hδ_mesh.1, by unfold deltaStar; linarith only [hδ_mesh.2, hx0_hi, hδ₀.1]⟩
    have hδ_0ds : δ ∈ Set.Icc (0 : ℝ) deltaStar :=
      ⟨by linarith only [hδ_ds.1, ha₁.1], hδ_ds.2⟩
    have hdist_bar : dist (a_hi + h) δ < r_uth := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith only [hδ.2, hh_pos])]
      have hdiff_le : (a_hi + h) - δ ≤ 2 * h := by linarith only [hδ.1, ha_hi_sub]
      have hh_r : h < r_uth / 4 := lt_of_lt_of_le hh_lt_bound hh_b_uth
      linarith only [hdiff_le, hh_r, hr_uth_pos]
    have hth_diff := hr_uth (a_hi + h) ⟨hhi_ioc.1.le, hhi_ioc.2⟩ δ
      ⟨by linarith only [hδ_mesh.1, ha₁.1], by linarith only [hδ_mesh.2, hδ₀.1]⟩ hdist_bar
    rw [Real.dist_eq, ← hθBar_j_def] at hth_diff
    have hgap_at_δ : p1Inf d₀ - capThresholdTheta d₀ ≤ p1Inf δ - capThresholdTheta δ :=
      hd₀_eq.trans_le (hd_min_is ⟨δ, hδ_mesh, rfl⟩)
    have hθBar_le_p1 : θBar_j ≤ p1Inf δ := by
      have h1 : θBar_j - capThresholdTheta δ <
          min (p1Inf d₀ - capThresholdTheta d₀) (r_ucap / 2) :=
        lt_of_le_of_lt (le_abs_self _) hth_diff
      have h2 : min (p1Inf d₀ - capThresholdTheta d₀) (r_ucap / 2) ≤
          p1Inf d₀ - capThresholdTheta d₀ := min_le_left _ _
      linarith only [h1, h2, hgap_at_δ]
    have hmargin_bar : Real.log 2 / 2 * h ≤
        phiInfAux θBar_j + Real.log 2 / 2 * (phaseTarget δ - 1) := by
      rw [hθBar_j_def, phiInfAux_capThresholdTheta_add_target hhi_ioc δ]
      exact mul_le_mul_of_nonneg_left (by linarith only [hδ.2]) (half_pos hq_pos).le
    have hmargin_under :
        phiInfAux θUnder_j + Real.log 2 / 2 * (phaseTarget δ - 1) ≤ -(Real.log 2 / 2 * h) := by
      rw [hθUnder_j_def, phiInfAux_capThresholdTheta_add_target hlo_ioc δ, ← mul_neg]
      exact mul_le_mul_of_nonneg_left (by linarith only [hδ.1]) (half_pos hq_pos).le
    have hunder_lt_bar : θUnder_j < θBar_j := by
      rw [hθUnder_j_def, hθBar_j_def]
      exact strictMonoOn_capThresholdTheta ⟨hlo_ioc.1.le, hlo_ioc.2⟩ ⟨hhi_ioc.1.le, hhi_ioc.2⟩
        (by linarith only [ha_hi_sub, hh_pos])
    have hTδ_gt2 : 2 < phaseTarget δ := by
      unfold phaseTarget; unfold deltaStar at hδ_0ds; linarith only [hδ_0ds.2, h2lo]
    obtain ⟨-, hmono_cap_δ, -, -⟩ := cappedDualValue_Sge1_concave_strictMono_and_eq_dualValue hTδ_gt2
    have hcap_ge :
        0 ≤ cappedDualValue Sge1 θBar_j (phaseTarget δ) -
            cappedDualValue Sge1 θUnder_j (phaseTarget δ) := by
      have hp_def : p1Inf δ = gibbsProb Sge1 (sge1Tilt (phaseTarget δ)) 1 := rfl
      have hbar_le_opt : θBar_j ≤ gibbsProb Sge1 (sge1Tilt (phaseTarget δ)) 1 := by
        rwa [← hp_def]
      have hm := hmono_cap_δ ⟨hunder_pos.le, le_trans hunder_lt_bar.le hbar_le_opt⟩
        ⟨hbar_pos.le, hbar_le_opt⟩ hunder_lt_bar
      linarith only [hm]
    have hdist_th3 : dist (a_hi + h) (a_lo - h) < r_uth := by
      rw [Real.dist_eq, show (a_hi + h) - (a_lo - h) = 3 * h by linarith only [ha_hi_sub],
        abs_of_pos (by positivity)]
      have hh_r : h < r_uth / 4 := lt_of_lt_of_le hh_lt_bound hh_b_uth
      linarith only [hh_r, hr_uth_pos]
    have hth3_diff := hr_uth (a_hi + h) ⟨hhi_ioc.1.le, hhi_ioc.2⟩ (a_lo - h)
      ⟨hlo_ioc.1.le, hlo_ioc.2⟩ hdist_th3
    rw [← hθBar_j_def, ← hθUnder_j_def] at hth3_diff
    have hpair_dist :
        dist (θBar_j, phaseTarget δ) (θUnder_j, phaseTarget δ) < r_ucap := by
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
      have hle_half : min (p1Inf d₀ - capThresholdTheta d₀) (r_ucap / 2) ≤ r_ucap / 2 :=
        min_le_right _ _
      exact lt_of_lt_of_le hth3_diff (le_trans hle_half (by linarith only [hr_ucap_pos]))
    have hbar_icc20 : θBar_j ∈ Set.Icc (0 : ℝ) (1 / 20) := ⟨hbar_pos.le, by linarith only [hb_hi]⟩
    have hunder_icc20 : θUnder_j ∈ Set.Icc (0 : ℝ) (1 / 20) :=
      ⟨hunder_pos.le, by linarith only [hu_hi]⟩
    have hmem_bar : (θBar_j, phaseTarget δ) ∈ Set.Icc (0 : ℝ) (1 / 20) ×ˢ KcapInterval :=
      ⟨hbar_icc20, phaseTarget_mem_Kcap hδ_0ds⟩
    have hmem_under : (θUnder_j, phaseTarget δ) ∈ Set.Icc (0 : ℝ) (1 / 20) ×ˢ KcapInterval :=
      ⟨hunder_icc20, phaseTarget_mem_Kcap hδ_0ds⟩
    have hcap_diff_lt := hr_ucap (θBar_j, phaseTarget δ) hmem_bar
      (θUnder_j, phaseTarget δ) hmem_under hpair_dist
    rw [Real.dist_eq, abs_of_nonneg hcap_ge] at hcap_diff_lt
    obtain ⟨hmcap_nn, hmcap_lt⟩ :=
      hM_cap_conv M_cap le_rfl θUnder_j hunder_icc20 (phaseTarget δ) (phaseTarget_mem_Kcap hδ_0ds)
    exact ⟨hδ_ds, hθBar_le_p1, hmargin_bar, hmargin_under,
      by linarith only [hcap_ge, hmcap_nn], by
      have hm1 := hb_step_mul _ hcap_diff_lt
      have hm2 := hb_step_mul _ hmcap_lt
      linarith only [hm1, hm2]⟩
  · intro δ hδ
    by_cases h1 : δ ≤ a₁
    · exact Or.inl ⟨hδ.1, h1⟩
    · replace h1 : a₁ < δ := lt_of_not_ge h1
      by_cases h2 : δ ≤ criticalPhaseX0 - δ₀
      · right; left
        by_cases htop : δ = criticalPhaseX0 - δ₀
        · refine ⟨⟨N_mesh - 1, Nat.sub_lt hN_mesh_ge1 zero_lt_one⟩, ?_, ?_⟩
          · rw [htop]
            have hcast : ((N_mesh - 1 : ℕ) : ℝ) = (N_mesh : ℝ) - 1 := by
              rw [Nat.cast_sub hN_mesh_ge1, Nat.cast_one]
            dsimp only
            rw [hcast]
            linarith only [hh_mul, hh_pos]
          · rw [htop]
            dsimp only
            rw [Nat.sub_add_cancel hN_mesh_ge1]
            linarith only [hh_mul]
        · have hlt_top : δ < criticalPhaseX0 - δ₀ := lt_of_le_of_ne h2 htop
          set idx : ℕ := Nat.floor ((δ - a₁) / h)
          have hq_nn : 0 ≤ (δ - a₁) / h := div_nonneg (by linarith only [h1]) hh_pos.le
          have hq_lt : (δ - a₁) / h < (N_mesh : ℝ) := by
            rw [hh_def, div_div_eq_mul_div, div_lt_iff₀ (by linarith only [ha₁_lt_x0d]),
              mul_comm (N_mesh : ℝ)]
            exact mul_lt_mul_of_pos_right
              (by linarith only [hlt_top] : δ - a₁ < criticalPhaseX0 - δ₀ - a₁) hN_mesh_pos
          have hidx_lt : idx < N_mesh := (Nat.floor_lt hq_nn).mpr hq_lt
          refine ⟨⟨idx, hidx_lt⟩, ?_, ?_⟩
          · have hfl := Nat.floor_le hq_nn
            have hm := (le_div_iff₀ hh_pos).mp hfl
            dsimp only
            linarith only [hm]
          · have hfl := (Nat.lt_floor_add_one ((δ - a₁) / h)).le
            have hm := (div_le_iff₀ hh_pos).mp hfl
            dsimp only
            push_cast
            linarith only [hm]
      · replace h2 : criticalPhaseX0 - δ₀ < δ := lt_of_not_ge h2
        by_cases h3 : δ ≤ criticalPhaseX0 + δ₀
        · exact Or.inr (Or.inr (Or.inl ⟨h2.le, h3⟩))
        · replace h3 : criticalPhaseX0 + δ₀ < δ := lt_of_not_ge h3
          exact Or.inr (Or.inr (Or.inr ⟨h3.le, hδ.2⟩))

/-- **Section 9 complete unconditional `(J + 3)`-interval phase cover & dual-budget theorem:**
for every `ε > 0` (`η := (log 2)³ ε`), constructively produces:
1. **Transition interval `I_tr = [x₀ - δ₀, x₀ + δ₀]`** (`δ₀ ∈ (0, 1/1000)`), `p_tr = θ(x₀ - 2δ₀)`,
   and `M_tr ≥ 8` with Regime C cap margin `≤ -(log 2 / 2) δ₀` and dual gap `< 2η/3`;
2. **Main arc `I_main = [x₀ + δ₀, 1)`** and `M_main ≥ 7` with dual gap `< 2η/3`;
3. **Near-zero interval `I₀ = [0, a₁]`** (`a₁ ∈ (0, (x₀ - δ₀)/3)`), `θ̄₀ = θ(2 a₁)`, and `M₀ ≥ 7`
   with `θ̄₀ ≤ p_{1,∞}(δ)`, Proposition 4.1(iii) margin `≥ (log 2 / 2) a₁`, and dual gap `< 2η/3`;
4. **Capped mesh `I_j = [a₁ + j h, a₁ + (j + 1) h]` (`j : Fin N_mesh`) on `[a₁, x₀ - δ₀]`** with
   `h ∈ (0, min(a₁/2, δ₀/2))`, `θ̄_j = θ(a_{j+1} + h) ≤ p_{1,∞}(δ)`, `θ̲_j = θ(a_j - h)`, and a
   uniform `M_cap ≥ 8` satisfying all Proposition 4.1(iii), Regime C, and `< 2η/3` dual-gap bounds;
5. **Full cover of `[0, 1)`** by `I₀`, `(I_j)_{j : Fin N_mesh}`, `I_tr`, and `I_main`. -/
theorem exists_finite_phase_cover_dual_budget {eps : ℝ} (heps : 0 < eps) :
    let eta : ℝ := (Real.log 2) ^ 3 * eps
    ∃ (δ₀ : ℝ) (M_tr M_main : ℕ) (a₁ : ℝ) (M₀ N_mesh M_cap : ℕ),
      δ₀ ∈ Set.Ioo (0 : ℝ) (1 / 1000) ∧
      8 ≤ M_tr ∧ 7 ≤ M_main ∧
      a₁ ∈ Set.Ioo (0 : ℝ) ((criticalPhaseX0 - δ₀) / 3) ∧
      7 ≤ M₀ ∧ 1 ≤ N_mesh ∧ 8 ≤ M_cap ∧
      let p_tr : ℝ := capThresholdTheta (criticalPhaseX0 - 2 * δ₀)
      let θBar₀ : ℝ := capThresholdTheta (2 * a₁)
      let h : ℝ := (criticalPhaseX0 - δ₀ - a₁) / (N_mesh : ℝ)
      (p_tr ∈ Set.Ioc (0 : ℝ) (1 / 40) ∧
        ∀ δ ∈ Set.Icc (criticalPhaseX0 - δ₀) (criticalPhaseX0 + δ₀),
          δ ∈ Set.Icc (0 : ℝ) deltaStar ∧
          phiInfAux p_tr + Real.log 2 / 2 * (phaseTarget δ - 1) ≤ -(Real.log 2 / 2 * δ₀) ∧
          0 ≤ dualValue Sge1 (phaseTarget δ) -
              cappedDualValue (S0M M_tr) p_tr (phaseTarget δ) ∧
          (Real.log 2) ^ 2 / 4 *
              (dualValue Sge1 (phaseTarget δ) -
                cappedDualValue (S0M M_tr) p_tr (phaseTarget δ)) < 2 * eta / 3) ∧
      (∀ δ ∈ Set.Ico (criticalPhaseX0 + δ₀) 1,
        0 ≤ dualValue Sge1 (phaseTarget δ) - dualValue (S0M M_main) (phaseTarget δ) ∧
          (Real.log 2) ^ 2 / 4 *
              (dualValue Sge1 (phaseTarget δ) - dualValue (S0M M_main) (phaseTarget δ)) <
            2 * eta / 3) ∧
      (θBar₀ ∈ Set.Ioc (0 : ℝ) (1 / 20) ∧
        ∀ δ ∈ Set.Icc (0 : ℝ) a₁,
          θBar₀ ≤ p1Inf δ ∧
          Real.log 2 / 2 * a₁ ≤ phiInfAux θBar₀ + Real.log 2 / 2 * (phaseTarget δ - 1) ∧
          (Real.log 2) ^ 2 / 4 *
              |(cappedDualValue Sge1 θBar₀ (phaseTarget δ) -
                dualValue (shiftSupportOne (S0M M₀)) (phaseTarget δ))| < 2 * eta / 3) ∧
      (h ∈ Set.Ioo (0 : ℝ) (min (a₁ / 2) (δ₀ / 2)) ∧
        ∀ j : Fin N_mesh,
          let a_lo : ℝ := a₁ + (j.1 : ℝ) * h
          let a_hi : ℝ := a₁ + ((j.1 + 1 : ℕ) : ℝ) * h
          let θBar_j : ℝ := capThresholdTheta (a_hi + h)
          let θUnder_j : ℝ := capThresholdTheta (a_lo - h)
          θBar_j ∈ Set.Ioc (0 : ℝ) (1 / 20) ∧
          θUnder_j ∈ Set.Ioc (0 : ℝ) (1 / 40) ∧
          ∀ δ ∈ Set.Icc a_lo a_hi,
            δ ∈ Set.Icc a₁ deltaStar ∧
            θBar_j ≤ p1Inf δ ∧
            Real.log 2 / 2 * h ≤ phiInfAux θBar_j + Real.log 2 / 2 * (phaseTarget δ - 1) ∧
            phiInfAux θUnder_j + Real.log 2 / 2 * (phaseTarget δ - 1) ≤
              -(Real.log 2 / 2 * h) ∧
            0 ≤ cappedDualValue Sge1 θBar_j (phaseTarget δ) -
                cappedDualValue (S0M M_cap) θUnder_j (phaseTarget δ) ∧
            (Real.log 2) ^ 2 / 4 *
                (cappedDualValue Sge1 θBar_j (phaseTarget δ) -
                  cappedDualValue (S0M M_cap) θUnder_j (phaseTarget δ)) < 2 * eta / 3) ∧
      (∀ δ ∈ Set.Ico (0 : ℝ) 1,
        δ ∈ Set.Icc 0 a₁ ∨
          (∃ j : Fin N_mesh,
            δ ∈ Set.Icc (a₁ + (j.1 : ℝ) * h) (a₁ + ((j.1 + 1 : ℕ) : ℝ) * h)) ∨
          δ ∈ Set.Icc (criticalPhaseX0 - δ₀) (criticalPhaseX0 + δ₀) ∨
          δ ∈ Set.Ico (criticalPhaseX0 + δ₀) 1) := by
  intro eta
  obtain ⟨δ₀, M_tr, hδ₀_mem, hM_tr8, h_tr⟩ := phaseCover_transition_step heps
  obtain ⟨M_main, hM_main7, h_main⟩ := phaseCover_main_step heps hδ₀_mem
  obtain ⟨a₁, M₀, ha₁_mem, hM₀7, h_zero⟩ := phaseCover_nearZero_step heps hδ₀_mem
  obtain ⟨N_mesh, M_cap, hN1, hM_cap8, h_mesh, h_cov⟩ :=
    phaseCover_mesh_step heps hδ₀_mem ha₁_mem
  exact ⟨δ₀, M_tr, M_main, a₁, M₀, N_mesh, M_cap,
    hδ₀_mem, hM_tr8, hM_main7, ha₁_mem, hM₀7, hN1, hM_cap8,
    h_tr, h_main, h_zero, h_mesh, h_cov⟩

/-!
## 4. Section 7 `Π_rel` trichotomy, cross-edge majorant, Poisson kernel, and three-range assembly
-/

private def inducedOverlapPartition {V : Type*} [DecidableEq V] {W : Finset V}
    (Q : Finpartition W) (D : Finset V) (hDW : D ⊆ W) : Finpartition D where
  parts := (Q.parts.filter fun E ↦ (D ∩ E).Nonempty).image fun E ↦ D ∩ E
  supIndep := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    intro A hA B hB hne
    rcases Finset.mem_image.mp (Finset.mem_coe.mp hA) with ⟨E₁, hE₁, rfl⟩
    rcases Finset.mem_image.mp (Finset.mem_coe.mp hB) with ⟨E₂, hE₂, rfl⟩
    have hE₁_ne : E₁ ≠ E₂ := fun h ↦ hne (by rw [h])
    exact (Q.disjoint (Finset.mem_filter.mp hE₁).1 (Finset.mem_filter.mp hE₂).1 hE₁_ne).mono
      Finset.inter_subset_right Finset.inter_subset_right
  sup_parts := by
    ext v
    simp only [Finset.sup_eq_biUnion, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨_, ⟨E, _, rfl⟩, hv⟩
      exact (Finset.mem_inter.mp hv).1
    · intro hvD
      have hvW : v ∈ W := hDW hvD
      rw [← Q.sup_parts, Finset.sup_eq_biUnion, Finset.mem_biUnion] at hvW
      rcases hvW with ⟨E, hEQ, hvE⟩
      exact ⟨D ∩ E, ⟨E, ⟨hEQ, ⟨v, Finset.mem_inter.mpr ⟨hvD, hvE⟩⟩⟩, rfl⟩,
        Finset.mem_inter.mpr ⟨hvD, hvE⟩⟩
  bot_notMem := by
    simp only [Finset.bot_eq_empty, Finset.mem_image, Finset.mem_filter]
    rintro ⟨E, ⟨_, hne⟩, heq⟩
    exact hne.ne_empty heq

private theorem card_inducedOverlapPartition {V : Type*} [DecidableEq V] {W : Finset V}
    (Q : Finpartition W) (D : Finset V) (hDW : D ⊆ W) :
    (inducedOverlapPartition Q D hDW).parts.card =
      (Q.parts.filter fun E ↦ (D ∩ E).Nonempty).card := by
  unfold inducedOverlapPartition
  dsimp only
  apply Finset.card_image_of_injOn
  intro E₁ hE₁ E₂ hE₂ heq
  dsimp only at heq
  obtain ⟨v, hv⟩ := (Finset.mem_filter.mp hE₁).2
  have hv₁ : v ∈ E₁ := (Finset.mem_inter.mp hv).2
  have hv' : v ∈ D ∩ E₂ := heq ▸ hv
  have hv₂ : v ∈ E₂ := (Finset.mem_inter.mp hv').2
  by_contra hne
  exact Finset.disjoint_left.mp
    (Q.disjoint (Finset.mem_filter.mp hE₁).1 (Finset.mem_filter.mp hE₂).1 hne) hv₁ hv₂

/-- **Section 7 `Π_rel` part trichotomy, overlap spectral gap, and `s₂` bound (`main.tex` lines 966–974 & 1078–1086):**
for any relevant pair `(P, P')` of partitions of `W` with part sizes in `[u_-, a]`
(`1 ≤ M`, `3M + 5 ≤ u_-`, `a ≤ u_- + M - 1`, `a ≤ α`, `α - u_- ≤ M + 1`) and condition-`(c)`
cap `B`:
1. `P.parts` splits disjointly into `Identical` (`P.parts ∩ P'.parts`), `Scrambled`
   (`D ∈ P.parts \ P'.parts` with `|D| ≤ z(D, P') + 2(α - |D|) + 1`), and `Exceptional`;
2. `Exceptional.card ≤ 2 * B`, and every `D ∈ Exceptional` has at most one `D' ∈ P'.parts`
   with `2 ≤ |D ∩ D'|`, which satisfies `u_- - 1 ≤ |D ∩ D'|`;
3. **Overlap spectral gap:** for every `D ∈ P.parts \ P'.parts` and `D' ∈ P'.parts`, no overlap
   block `D ∩ D'` has cardinality strictly between `2M + 4` and `u_- - 1`;
4. **Heavy-overlap vertex bound:** the total vertex count in `≥ 2`-overlap blocks across all
   non-identical parts `D ∈ P.parts \ P'.parts` is at most
   `(4 * M + 6) * (P.parts \ P'.parts).card + 2 * a * B`. -/
theorem relevantPair_part_trichotomy_and_overlap_gap
    {V : Type*} [DecidableEq V] {W : Finset V}
    (P P' : Finpartition W)
    {u_minus a α M B : ℕ}
    (_hM : 1 ≤ M)
    (hu_min : 3 * M + 5 ≤ u_minus)
    (ha_hi : a ≤ u_minus + M - 1)
    (ha_le_α : a ≤ α)
    (hα_u : α - u_minus ≤ M + 1)
    (hP_sizes : ∀ D ∈ P.parts, u_minus ≤ D.card ∧ D.card ≤ a)
    (hP'_sizes : ∀ D' ∈ P'.parts, u_minus ≤ D'.card ∧ D'.card ≤ a)
    (hRel_a :
      (∀ D ∈ P.parts,
        (P'.parts.filter fun E ↦ (D ∩ E).Nonempty).card ≤ 2 ∨
          D.card ≤ (P'.parts.filter fun E ↦ (D ∩ E).Nonempty).card + 2 * (α - D.card) + 1) ∧
      (∀ D' ∈ P'.parts,
        (P.parts.filter fun E ↦ (D' ∩ E).Nonempty).card ≤ 2 ∨
          D'.card ≤ (P.parts.filter fun E ↦ (D' ∩ E).Nonempty).card + 2 * (α - D'.card) + 1))
    (hRel_b :
      (∀ D ∈ P.parts, (P'.parts.filter fun E ↦ (D ∩ E).Nonempty).card = 2 →
        ∃ D' ∈ P'.parts, (D ∩ D').card = D.card - 1) ∧
      (∀ D' ∈ P'.parts, (P.parts.filter fun E ↦ (D' ∩ E).Nonempty).card = 2 →
        ∃ D ∈ P.parts, (D' ∩ D).card = D'.card - 1))
    (hRel_c :
      (P.parts.filter fun D ↦
        (P'.parts.filter fun E ↦ (D ∩ E).Nonempty).card = 2 ∧
          ∃ D' ∈ P'.parts, D'.card - 1 ≤ (D ∩ D').card).card ≤ B ∧
      (P'.parts.filter fun D' ↦
        (P.parts.filter fun E ↦ (D' ∩ E).Nonempty).card = 2 ∧
          ∃ D ∈ P.parts, D.card - 1 ≤ (D' ∩ D).card).card ≤ B) :
    let zP' : Finset V → ℕ := fun D ↦ (P'.parts.filter fun E ↦ (D ∩ E).Nonempty).card
    let Identical : Finset (Finset V) := P.parts ∩ P'.parts
    let Scrambled : Finset (Finset V) :=
      (P.parts \ P'.parts).filter fun D ↦ D.card ≤ zP' D + 2 * (α - D.card) + 1
    let Exceptional : Finset (Finset V) :=
      (P.parts \ P'.parts).filter fun D ↦ ¬ (D.card ≤ zP' D + 2 * (α - D.card) + 1)
    (P.parts = Identical ∪ Scrambled ∪ Exceptional ∧
      Disjoint Identical Scrambled ∧ Disjoint Identical Exceptional ∧
      Disjoint Scrambled Exceptional) ∧
    (Exceptional.card ≤ 2 * B ∧
      ∀ D ∈ Exceptional,
        (P'.parts.filter fun D' ↦ 2 ≤ (D ∩ D').card).card ≤ 1 ∧
        ∀ D' ∈ P'.parts, 2 ≤ (D ∩ D').card → u_minus - 1 ≤ (D ∩ D').card) ∧
    (∀ D ∈ P.parts \ P'.parts, ∀ D' ∈ P'.parts,
      ¬ (2 * M + 4 < (D ∩ D').card ∧ (D ∩ D').card < u_minus - 1)) ∧
    (∑ D ∈ P.parts \ P'.parts, ∑ D' ∈ P'.parts.filter (fun D' ↦ 2 ≤ (D ∩ D').card),
        (D ∩ D').card ≤
      (4 * M + 6) * (P.parts \ P'.parts).card + 2 * a * B) := by
  intro zP' Identical Scrambled Exceptional
  have hpart_sub : ∀ {Q : Finpartition W} {D : Finset V}, D ∈ Q.parts → D ⊆ W := by
    intro Q D hD v hv
    rw [← Q.sup_parts, Finset.sup_eq_biUnion, Finset.mem_biUnion]
    exact ⟨D, hD, hv⟩
  have hpart_union : Scrambled ∪ Exceptional = P.parts \ P'.parts :=
    Finset.filter_union_filter_not_eq _ (P.parts \ P'.parts)
  have hdecomp : P.parts = Identical ∪ Scrambled ∪ Exceptional := by
    rw [Finset.union_assoc, hpart_union]
    ext D
    simp only [Identical, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hdisj_IS : Disjoint Identical Scrambled := by
    rw [Finset.disjoint_left]
    intro D hI hS
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hS).1).2 (Finset.mem_inter.mp hI).2
  have hdisj_IE : Disjoint Identical Exceptional := by
    rw [Finset.disjoint_left]
    intro D hI hE
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hE).1).2 (Finset.mem_inter.mp hI).2
  have hdisj_SE : Disjoint Scrambled Exceptional := Finset.disjoint_filter_filter_not _ _ _
  have hzP_le_one_add_sdiff : ∀ {D D' : Finset V}, D ∈ P.parts → D' ⊆ W →
      (D' ∩ D).Nonempty →
      (P.parts.filter fun E ↦ (D' ∩ E).Nonempty).card ≤ 1 + (D' \ D).card := by
    intro D D' hDP _hD'W hne
    have hmemD : D ∈ P.parts.filter fun E ↦ (D' ∩ E).Nonempty :=
      Finset.mem_filter.mpr ⟨hDP, hne⟩
    set rest := (P.parts.filter fun E ↦ (D' ∩ E).Nonempty).erase D
    have hcard_er : (P.parts.filter fun E ↦ (D' ∩ E).Nonempty).card = 1 + rest.card := by
      have her : rest.card + 1 = (P.parts.filter fun E ↦ (D' ∩ E).Nonempty).card :=
        Finset.card_erase_add_one hmemD
      omega
    rw [hcard_er]
    have hsub_sdiff : ∀ E ∈ rest, (D' ∩ E).Nonempty ∧ D' ∩ E ⊆ D' \ D := by
      intro E hE
      have hneE := (Finset.mem_erase.mp hE).1
      have hEP := (Finset.mem_filter.mp (Finset.mem_erase.mp hE).2).1
      have hnon := (Finset.mem_filter.mp (Finset.mem_erase.mp hE).2).2
      refine ⟨hnon, fun v hv ↦ ?_⟩
      obtain ⟨hvD', hvE⟩ := Finset.mem_inter.mp hv
      exact Finset.mem_sdiff.mpr ⟨hvD',
        fun hvD ↦ Finset.disjoint_left.mp (P.disjoint hEP hDP hneE) hvE hvD⟩
    let pick : {E // E ∈ rest} → {v // v ∈ D' \ D} := fun E ↦
      ⟨(hsub_sdiff E.1 E.2).1.choose,
        (hsub_sdiff E.1 E.2).2 (hsub_sdiff E.1 E.2).1.choose_spec⟩
    have hinj : Function.Injective pick := by
      intro E₁ E₂ heq
      have hv1 := (Finset.mem_inter.mp (hsub_sdiff E₁.1 E₁.2).1.choose_spec).2
      have hv2 := (Finset.mem_inter.mp (hsub_sdiff E₂.1 E₂.2).1.choose_spec).2
      have hval : (pick E₁).1 = (pick E₂).1 := congrArg Subtype.val heq
      change (hsub_sdiff E₁.1 E₁.2).1.choose = (hsub_sdiff E₂.1 E₂.2).1.choose at hval
      rw [hval] at hv1
      by_contra hne_sub
      have hne_val : E₁.1 ≠ E₂.1 := fun h ↦ hne_sub (Subtype.ext h)
      exact Finset.disjoint_left.mp
        (P.disjoint (Finset.mem_filter.mp (Finset.mem_erase.mp E₁.2).2).1
          (Finset.mem_filter.mp (Finset.mem_erase.mp E₂.2).2).1 hne_val) hv1 hv2
    have hle := Fintype.card_le_of_injective pick hinj
    simp only [Fintype.card_coe] at hle
    exact Nat.add_le_add_left hle 1
  let Exc1 := Exceptional.filter fun D ↦ zP' D = 1
  let Exc2 := Exceptional.filter fun D ↦ zP' D = 2
  have hExc_split : Exceptional = Exc1 ∪ Exc2 ∧ Disjoint Exc1 Exc2 := by
    refine ⟨?_, ?_⟩
    · ext D
      simp only [Exc1, Exc2, Finset.mem_union, Finset.mem_filter]
      refine ⟨fun hE ↦ ?_, fun h ↦ h.elim And.left And.left⟩
      have hDP : D ∈ P.parts := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hE).1).1
      have hnot_scr := (Finset.mem_filter.mp hE).2
      have hz_le2 : zP' D ≤ 2 := (hRel_a.1 D hDP).resolve_right hnot_scr
      have hDW := hpart_sub hDP
      have hz_pos : 1 ≤ zP' D := by
        have hsum := (inducedOverlapPartition P' D hDW).sum_card_parts
        have hc := card_inducedOverlapPartition P' D hDW
        have hD_ge := (hP_sizes D hDP).1
        by_contra hz0
        have heq0 : (inducedOverlapPartition P' D hDW).parts = ∅ :=
          Finset.card_eq_zero.mp (by dsimp [zP'] at hz0; omega)
        rw [heq0] at hsum
        simp only [Finset.sum_empty] at hsum
        omega
      rcases (show zP' D = 1 ∨ zP' D = 2 by omega) with h1 | h2
      · exact Or.inl ⟨hE, h1⟩
      · exact Or.inr ⟨hE, h2⟩
    · rw [Finset.disjoint_left]
      intro D h1 h2
      have e1 := (Finset.mem_filter.mp h1).2
      have e2 := (Finset.mem_filter.mp h2).2
      omega
  have hExc1_props :
      Exc1.card ≤ B ∧
      ∀ D ∈ Exc1,
        (P'.parts.filter fun D' ↦ 2 ≤ (D ∩ D').card).card ≤ 1 ∧
        ∀ D' ∈ P'.parts, 2 ≤ (D ∩ D').card → u_minus - 1 ≤ (D ∩ D').card := by
    let ExcP' := P'.parts.filter fun D' ↦
      (P.parts.filter fun E ↦ (D' ∩ E).Nonempty).card = 2 ∧
        ∃ E ∈ P.parts, E.card - 1 ≤ (D' ∩ E).card
    have hD_info : ∀ D ∈ Exc1, ∃ D' ∈ ExcP', D ⊆ D' ∧
        P'.parts.filter (fun E ↦ (D ∩ E).Nonempty) = {D'} := by
      intro D hD1
      have hDE := (Finset.mem_filter.mp hD1).1
      have hz1 : zP' D = 1 := (Finset.mem_filter.mp hD1).2
      have hDP : D ∈ P.parts := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hDE).1).1
      have hDnP' : D ∉ P'.parts := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hDE).1).2
      obtain ⟨D', hD'_sing⟩ := Finset.card_eq_one.mp hz1
      have hD'_mem_f : D' ∈ P'.parts.filter (fun E ↦ (D ∩ E).Nonempty) := by
        rw [hD'_sing]; exact Finset.mem_singleton_self D'
      have hD'P' : D' ∈ P'.parts := (Finset.mem_filter.mp hD'_mem_f).1
      have hsub_DD' : D ⊆ D' := by
        intro v hvD
        have hvW : v ∈ W := hpart_sub hDP hvD
        rw [← P'.sup_parts, Finset.sup_eq_biUnion, Finset.mem_biUnion] at hvW
        rcases hvW with ⟨E, hEP', hvE⟩
        have hEf : E ∈ P'.parts.filter (fun E ↦ (D ∩ E).Nonempty) :=
          Finset.mem_filter.mpr ⟨hEP', ⟨v, Finset.mem_inter.mpr ⟨hvD, hvE⟩⟩⟩
        rw [hD'_sing, Finset.mem_singleton] at hEf
        rwa [← hEf]
      have hne_DD' : D ≠ D' := fun h ↦ hDnP' (h ▸ hD'P')
      have hsdiff_ne : (D' \ D).Nonempty := by
        by_contra hem
        rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hem
        exact hne_DD' (Finset.Subset.antisymm hsub_DD' hem)
      obtain ⟨w, hw⟩ := hsdiff_ne
      obtain ⟨hwD', hwnD⟩ := Finset.mem_sdiff.mp hw
      have hwW : w ∈ W := hpart_sub hD'P' hwD'
      rw [← P.sup_parts, Finset.sup_eq_biUnion, Finset.mem_biUnion] at hwW
      rcases hwW with ⟨E₂, hE₂P, hwE₂⟩
      have hE₂_ne : E₂ ≠ D := fun h ↦ hwnD (h ▸ hwE₂)
      have hD_pos : 0 < D.card := by have := (hP_sizes D hDP).1; omega
      have hzD'_ge2 : 2 ≤ (P.parts.filter fun E ↦ (D' ∩ E).Nonempty).card := by
        have hpair_sub : ({D, E₂} : Finset (Finset V)) ⊆
            P.parts.filter fun E ↦ (D' ∩ E).Nonempty := by
          intro X hX
          simp only [Finset.mem_insert, Finset.mem_singleton] at hX
          rcases hX with hXD | hXE₂
          · subst hXD
            obtain ⟨u₀, hu₀⟩ := Finset.card_pos.mp hD_pos
            exact Finset.mem_filter.mpr ⟨hDP, ⟨u₀, Finset.mem_inter.mpr ⟨hsub_DD' hu₀, hu₀⟩⟩⟩
          · subst hXE₂
            exact Finset.mem_filter.mpr ⟨hE₂P, ⟨w, Finset.mem_inter.mpr ⟨hwD', hwE₂⟩⟩⟩
        have hc2 := Finset.card_le_card hpair_sub
        rwa [Finset.card_pair hE₂_ne.symm] at hc2
      have hd_ne : (D' ∩ D).Nonempty := by
        obtain ⟨u₀, hu₀⟩ := Finset.card_pos.mp hD_pos
        exact ⟨u₀, Finset.mem_inter.mpr ⟨hsub_DD' hu₀, hu₀⟩⟩
      have hzD'_le : (P.parts.filter fun E ↦ (D' ∩ E).Nonempty).card ≤ M := by
        have h1 := hzP_le_one_add_sdiff hDP (hpart_sub hD'P') hd_ne
        have hsd_card : (D' \ D).card = D'.card - D.card := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub_DD']
        have hD_b := hP_sizes D hDP
        have hD'_b := hP'_sizes D' hD'P'
        omega
      have hzD'_not_scr :
          ¬ (D'.card ≤ (P.parts.filter fun E ↦ (D' ∩ E).Nonempty).card +
              2 * (α - D'.card) + 1) := by
        have hD'_b := hP'_sizes D' hD'P'
        have hdef' : α - D'.card ≤ M + 1 := by omega
        omega
      have hzD'_eq2 : (P.parts.filter fun E ↦ (D' ∩ E).Nonempty).card = 2 := by
        have := (hRel_a.2 D' hD'P').resolve_right hzD'_not_scr
        omega
      have hD_inter : (D' ∩ D).card = D.card :=
        congrArg Finset.card (Finset.inter_eq_right.mpr hsub_DD')
      refine ⟨D', Finset.mem_filter.mpr ⟨hD'P', hzD'_eq2, ⟨D, hDP, by omega⟩⟩, hsub_DD', hD'_sing⟩
    let phi : {D // D ∈ Exc1} → {D' // D' ∈ ExcP'} := fun D ↦
      ⟨(hD_info D.1 D.2).choose, (hD_info D.1 D.2).choose_spec.1⟩
    have hphi_inj : Function.Injective phi := by
      intro D₁ D₂ heq
      by_contra hne
      have hne_val : D₁.1 ≠ D₂.1 := fun h ↦ hne (Subtype.ext h)
      have hD₁P : D₁.1 ∈ P.parts :=
        (Finset.mem_sdiff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp D₁.2).1).1).1
      have hD₂P : D₂.1 ∈ P.parts :=
        (Finset.mem_sdiff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp D₂.2).1).1).1
      have hsub1 : D₁.1 ⊆ (phi D₁).1 := (hD_info D₁.1 D₁.2).choose_spec.2.1
      have hsub2 : D₂.1 ⊆ (phi D₁).1 := by
        have : (phi D₂).1 = (phi D₁).1 := congrArg Subtype.val heq.symm
        rw [← this]
        exact (hD_info D₂.1 D₂.2).choose_spec.2.1
      have hdisj : Disjoint D₁.1 D₂.1 := P.disjoint hD₁P hD₂P hne_val
      have hun_sub : D₁.1 ∪ D₂.1 ⊆ (phi D₁).1 := Finset.union_subset hsub1 hsub2
      have hcard_u := Finset.card_le_card hun_sub
      rw [Finset.card_union_of_disjoint hdisj] at hcard_u
      have hD'P' : (phi D₁).1 ∈ P'.parts := (Finset.mem_filter.mp (phi D₁).2).1
      have hb1 := (hP_sizes D₁.1 hD₁P).1
      have hb2 := (hP_sizes D₂.1 hD₂P).1
      have hb' := (hP'_sizes (phi D₁).1 hD'P').2
      omega
    have hc_le : Exc1.card ≤ ExcP'.card := by
      have := Fintype.card_le_of_injective phi hphi_inj
      simpa [Fintype.card_coe] using this
    refine ⟨hc_le.trans hRel_c.2, fun D hD1 ↦ ?_⟩
    obtain ⟨D'₀, _, hsub₀, hsing₀⟩ := hD_info D hD1
    have hDP : D ∈ P.parts :=
      (Finset.mem_sdiff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hD1).1).1).1
    have hfilt_sub : (P'.parts.filter fun D' ↦ 2 ≤ (D ∩ D').card) ⊆ {D'₀} := by
      intro D' hD'
      obtain ⟨hD'P', h2⟩ := Finset.mem_filter.mp hD'
      have hne : (D ∩ D').Nonempty := Finset.card_pos.mp (by omega)
      have hmem : D' ∈ P'.parts.filter (fun E ↦ (D ∩ E).Nonempty) :=
        Finset.mem_filter.mpr ⟨hD'P', hne⟩
      rwa [hsing₀] at hmem
    refine ⟨(Finset.card_le_card hfilt_sub).trans (by simp), fun D' hD'P' h2 ↦ ?_⟩
    have hmem_s := hfilt_sub (Finset.mem_filter.mpr ⟨hD'P', h2⟩)
    rw [Finset.mem_singleton] at hmem_s
    subst hmem_s
    rw [Finset.inter_eq_left.mpr hsub₀]
    have hb := (hP_sizes D hDP).1
    omega
  have hExc2_props :
      Exc2.card ≤ B ∧
      ∀ D ∈ Exc2,
        (P'.parts.filter fun D' ↦ 2 ≤ (D ∩ D').card).card ≤ 1 ∧
        ∀ D' ∈ P'.parts, 2 ≤ (D ∩ D').card → u_minus - 1 ≤ (D ∩ D').card := by
    let ExcP := P.parts.filter fun D ↦
      (P'.parts.filter fun E ↦ (D ∩ E).Nonempty).card = 2 ∧
        ∃ D' ∈ P'.parts, D'.card - 1 ≤ (D ∩ D').card
    have hsub_ExcP : Exc2 ⊆ ExcP ∧
        ∀ D ∈ Exc2, ∃ D'₀ ∈ P'.parts, (D ∩ D'₀).card = D.card - 1 ∧
          (P'.parts.filter fun D' ↦ 2 ≤ (D ∩ D').card) ⊆ {D'₀} := by
      have hall : ∀ D ∈ Exc2, D ∈ ExcP ∧
          ∃ D'₀ ∈ P'.parts, (D ∩ D'₀).card = D.card - 1 ∧
            (P'.parts.filter fun D' ↦ 2 ≤ (D ∩ D').card) ⊆ {D'₀} := by
        intro D hD2
        have hDE := (Finset.mem_filter.mp hD2).1
        have hz2 : zP' D = 2 := (Finset.mem_filter.mp hD2).2
        have hDP : D ∈ P.parts := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hDE).1).1
        obtain ⟨D'₀, hD'₀P', hcard_dm1⟩ := hRel_b.1 D hDP hz2
        have hD_b := hP_sizes D hDP
        have hD'₀_b := hP'_sizes D'₀ hD'₀P'
        have hne_0 : (D'₀ ∩ D).Nonempty := by
          have hpos_inter : 0 < (D'₀ ∩ D).card := by rw [Finset.inter_comm]; omega
          exact Finset.card_pos.mp hpos_inter
        have hzD'₀_le : (P.parts.filter fun E ↦ (D'₀ ∩ E).Nonempty).card ≤ 1 + M := by
          have h1 := hzP_le_one_add_sdiff hDP (hpart_sub hD'₀P') hne_0
          have hsd : (D'₀ \ D).card = D'₀.card - (D ∩ D'₀).card := Finset.card_sdiff
          omega
        have hzD'₀_not_scr :
            ¬ (D'₀.card ≤ (P.parts.filter fun E ↦ (D'₀ ∩ E).Nonempty).card +
                2 * (α - D'₀.card) + 1) := by
          have hdef' : α - D'₀.card ≤ M + 1 := by omega
          omega
        have hzD'₀_le2 : (P.parts.filter fun E ↦ (D'₀ ∩ E).Nonempty).card ≤ 2 :=
          (hRel_a.2 D'₀ hD'₀P').resolve_right hzD'₀_not_scr
        have hzD'₀_ge1 : 1 ≤ (P.parts.filter fun E ↦ (D'₀ ∩ E).Nonempty).card :=
          Finset.card_pos.mpr ⟨D, Finset.mem_filter.mpr ⟨hDP, hne_0⟩⟩
        have hD'₀_m1_le : D'₀.card - 1 ≤ (D ∩ D'₀).card := by
          rcases (show (P.parts.filter fun E ↦ (D'₀ ∩ E).Nonempty).card = 1 ∨
              (P.parts.filter fun E ↦ (D'₀ ∩ E).Nonempty).card = 2 by omega) with h1 | h2
          · obtain ⟨E₀, hsing⟩ := Finset.card_eq_one.mp h1
            have hD_in : D ∈ P.parts.filter fun E ↦ (D'₀ ∩ E).Nonempty :=
              Finset.mem_filter.mpr ⟨hDP, hne_0⟩
            rw [hsing, Finset.mem_singleton] at hD_in
            subst hD_in
            have hsub' : D'₀ ⊆ D := by
              intro v hv
              have hvW : v ∈ W := hpart_sub hD'₀P' hv
              rw [← P.sup_parts, Finset.sup_eq_biUnion, Finset.mem_biUnion] at hvW
              rcases hvW with ⟨E, hEP, hvE⟩
              have hEf : E ∈ P.parts.filter fun E ↦ (D'₀ ∩ E).Nonempty :=
                Finset.mem_filter.mpr ⟨hEP, ⟨v, Finset.mem_inter.mpr ⟨hv, hvE⟩⟩⟩
              rw [hsing, Finset.mem_singleton] at hEf
              rwa [← hEf]
            rw [Finset.inter_eq_right.mpr hsub']
            omega
          · obtain ⟨E₀, hE₀P, hE₀_card⟩ := hRel_b.2 D'₀ hD'₀P' h2
            by_cases hED : E₀ = D
            · subst hED
              rw [Finset.inter_comm] at hE₀_card
              omega
            · exfalso
              have hdisj_in : Disjoint (D'₀ ∩ D) (D'₀ ∩ E₀) :=
                (P.disjoint hDP hE₀P (Ne.symm hED)).mono
                  Finset.inter_subset_right Finset.inter_subset_right
              have hun_in : (D'₀ ∩ D) ∪ (D'₀ ∩ E₀) ⊆ D'₀ :=
                Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
              have hcu := Finset.card_le_card hun_in
              rw [Finset.card_union_of_disjoint hdisj_in, Finset.inter_comm D'₀ D,
                hcard_dm1, hE₀_card] at hcu
              omega
        have hfilt_sub : (P'.parts.filter fun D' ↦ 2 ≤ (D ∩ D').card) ⊆ {D'₀} := by
          intro D' hD'
          obtain ⟨hD'P', h2⟩ := Finset.mem_filter.mp hD'
          rw [Finset.mem_singleton]
          by_contra hne'
          have hdisj_in : Disjoint (D ∩ D'₀) (D ∩ D') :=
            (P'.disjoint hD'₀P' hD'P' (Ne.symm hne')).mono
              Finset.inter_subset_right Finset.inter_subset_right
          have hun_in : (D ∩ D'₀) ∪ (D ∩ D') ⊆ D :=
            Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
          have hcu := Finset.card_le_card hun_in
          rw [Finset.card_union_of_disjoint hdisj_in, hcard_dm1] at hcu
          omega
        exact ⟨Finset.mem_filter.mpr ⟨hDP, hz2, ⟨D'₀, hD'₀P', hD'₀_m1_le⟩⟩,
          ⟨D'₀, hD'₀P', hcard_dm1, hfilt_sub⟩⟩
      exact ⟨fun D hD ↦ (hall D hD).1, fun D hD ↦ (hall D hD).2⟩
    refine ⟨(Finset.card_le_card hsub_ExcP.1).trans hRel_c.1, fun D hD2 ↦ ?_⟩
    obtain ⟨D'₀, _, hcard_dm1, hfilt_sub⟩ := hsub_ExcP.2 D hD2
    have hDP : D ∈ P.parts :=
      (Finset.mem_sdiff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hD2).1).1).1
    refine ⟨(Finset.card_le_card hfilt_sub).trans (by simp), fun D' hD'P' h2 ↦ ?_⟩
    have hmem_s := hfilt_sub (Finset.mem_filter.mpr ⟨hD'P', h2⟩)
    rw [Finset.mem_singleton] at hmem_s
    subst hmem_s
    rw [hcard_dm1]
    have hb := (hP_sizes D hDP).1
    omega
  have hExc_all :
      Exceptional.card ≤ 2 * B ∧
      ∀ D ∈ Exceptional,
        (P'.parts.filter fun D' ↦ 2 ≤ (D ∩ D').card).card ≤ 1 ∧
        ∀ D' ∈ P'.parts, 2 ≤ (D ∩ D').card → u_minus - 1 ≤ (D ∩ D').card := by
    refine ⟨?_, fun D hD ↦ ?_⟩
    · rw [hExc_split.1, Finset.card_union_of_disjoint hExc_split.2]
      have h1 := hExc1_props.1
      have h2 := hExc2_props.1
      omega
    · rw [hExc_split.1, Finset.mem_union] at hD
      exact hD.elim (hExc1_props.2 D) (hExc2_props.2 D)
  have hScr_bounds : ∀ D ∈ Scrambled,
      (∀ D' ∈ P'.parts, (D ∩ D').card ≤ 2 * M + 4) ∧
        (∑ D' ∈ P'.parts.filter (fun D' ↦ 2 ≤ (D ∩ D').card), (D ∩ D').card) ≤ 4 * M + 6 := by
    intro D hDS
    have hDP : D ∈ P.parts := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hDS).1).1
    have hscr_ineq := (Finset.mem_filter.mp hDS).2
    have hDW := hpart_sub hDP
    have hD_b := hP_sizes D hDP
    let Q_ind := inducedOverlapPartition P' D hDW
    have hQ_card : Q_ind.parts.card = zP' D := card_inducedOverlapPartition P' D hDW
    have hscr_Q : D.card ≤ Q_ind.parts.card + 2 * (α - D.card) + 1 := by
      rwa [hQ_card]
    have hdef_D : α - D.card ≤ M + 1 := by omega
    obtain ⟨hb_max, _, hb_sum⟩ := scrambledPart_heavyOverlap_card_and_vertex_sum_le (M := M) Q_ind
      rfl (le_trans hD_b.2 ha_le_α) hdef_D hscr_Q
    refine ⟨fun D' hD'P' ↦ ?_, ?_⟩
    · by_cases hne : (D ∩ D').Nonempty
      · have hmemQ : D ∩ D' ∈ Q_ind.parts := by
          dsimp [Q_ind]; unfold inducedOverlapPartition; dsimp only
          exact Finset.mem_image.mpr ⟨D', Finset.mem_filter.mpr ⟨hD'P', hne⟩, rfl⟩
        exact (hb_max _ hmemQ).2
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        rw [hne, Finset.card_empty]; omega
    · have hbij_sum :
          (∑ D' ∈ P'.parts.filter (fun D' ↦ 2 ≤ (D ∩ D').card), (D ∩ D').card) =
            (Q_ind.parts.filter (fun B ↦ 2 ≤ B.card)).sum Finset.card := by
        refine Finset.sum_bij (fun D' _ ↦ D ∩ D') ?_ ?_ ?_ (fun _ _ ↦ rfl)
        · intro D' hD'
          obtain ⟨hD'P', h2⟩ := Finset.mem_filter.mp hD'
          have hc_pos : 0 < (D ∩ D').card := by omega
          refine Finset.mem_filter.mpr ⟨?_, h2⟩
          dsimp [Q_ind]; unfold inducedOverlapPartition; dsimp only
          exact Finset.mem_image.mpr ⟨D',
            Finset.mem_filter.mpr ⟨hD'P', Finset.card_pos.mp hc_pos⟩, rfl⟩
        · intro E₁ hE₁ E₂ hE₂ heq
          obtain ⟨hE₁P', h2₁⟩ := Finset.mem_filter.mp hE₁
          obtain ⟨hE₂P', _⟩ := Finset.mem_filter.mp hE₂
          have hc_pos₁ : 0 < (D ∩ E₁).card := by omega
          obtain ⟨v, hv⟩ := Finset.card_pos.mp hc_pos₁
          have hv₁ : v ∈ E₁ := (Finset.mem_inter.mp hv).2
          have hv₂ : v ∈ E₂ := (Finset.mem_inter.mp (heq ▸ hv)).2
          by_contra hne
          exact Finset.disjoint_left.mp (P'.disjoint hE₁P' hE₂P' hne) hv₁ hv₂
        · intro B hB
          obtain ⟨hBQ, h2⟩ := Finset.mem_filter.mp hB
          dsimp [Q_ind] at hBQ; unfold inducedOverlapPartition at hBQ; dsimp only at hBQ
          rcases Finset.mem_image.mp hBQ with ⟨D', hD'f, rfl⟩
          exact ⟨D', Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hD'f).1, h2⟩, rfl⟩
      rw [hbij_sum]
      exact hb_sum
  refine ⟨⟨hdecomp, hdisj_IS, hdisj_IE, hdisj_SE⟩, hExc_all, ?_, ?_⟩
  · intro D hDsdiff D' hD'P' ⟨hgt, hlt⟩
    rw [← hpart_union, Finset.mem_union] at hDsdiff
    rcases hDsdiff with hDS | hDE
    · have hle := (hScr_bounds D hDS).1 D' hD'P'
      omega
    · have hge := (hExc_all.2 D hDE).2 D' hD'P' (by omega)
      omega
  · have hsplit_sum :
        (∑ D ∈ P.parts \ P'.parts, ∑ D' ∈ P'.parts.filter (fun D' ↦ 2 ≤ (D ∩ D').card),
            (D ∩ D').card) =
          (∑ D ∈ Scrambled, ∑ D' ∈ P'.parts.filter (fun D' ↦ 2 ≤ (D ∩ D').card), (D ∩ D').card) +
          (∑ D ∈ Exceptional, ∑ D' ∈ P'.parts.filter (fun D' ↦ 2 ≤ (D ∩ D').card), (D ∩ D').card) := by
      rw [← hpart_union, Finset.sum_union hdisj_SE]
    have hsum_scr :
        (∑ D ∈ Scrambled, ∑ D' ∈ P'.parts.filter (fun D' ↦ 2 ≤ (D ∩ D').card), (D ∩ D').card) ≤
          (4 * M + 6) * (P.parts \ P'.parts).card := by
      calc ∑ D ∈ Scrambled, ∑ D' ∈ P'.parts.filter (fun D' ↦ 2 ≤ (D ∩ D').card), (D ∩ D').card
          ≤ ∑ _D ∈ Scrambled, (4 * M + 6) := Finset.sum_le_sum fun D hD ↦ (hScr_bounds D hD).2
        _ = Scrambled.card * (4 * M + 6) := by simp
        _ ≤ (P.parts \ P'.parts).card * (4 * M + 6) :=
            Nat.mul_le_mul_right _ (Finset.card_le_card (Finset.filter_subset _ _))
        _ = (4 * M + 6) * (P.parts \ P'.parts).card := Nat.mul_comm _ _
    have hsum_exc :
        (∑ D ∈ Exceptional, ∑ D' ∈ P'.parts.filter (fun D' ↦ 2 ≤ (D ∩ D').card), (D ∩ D').card) ≤
          2 * a * B := by
      have h_each : ∀ D ∈ Exceptional,
          (∑ D' ∈ P'.parts.filter (fun D' ↦ 2 ≤ (D ∩ D').card), (D ∩ D').card) ≤ a := by
        intro D hDE
        have hDP : D ∈ P.parts := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hDE).1).1
        have hle1 := (hExc_all.2 D hDE).1
        rcases (show (P'.parts.filter fun D' ↦ 2 ≤ (D ∩ D').card).card = 0 ∨
            (P'.parts.filter fun D' ↦ 2 ≤ (D ∩ D').card).card = 1 by omega) with h0 | h1
        · rw [Finset.card_eq_zero.mp h0, Finset.sum_empty]; exact Nat.zero_le a
        · obtain ⟨D'₀, hsing⟩ := Finset.card_eq_one.mp h1
          rw [hsing, Finset.sum_singleton]
          exact (Finset.card_le_card Finset.inter_subset_left).trans (hP_sizes D hDP).2
      calc ∑ D ∈ Exceptional, ∑ D' ∈ P'.parts.filter (fun D' ↦ 2 ≤ (D ∩ D').card), (D ∩ D').card
          ≤ ∑ _D ∈ Exceptional, a := Finset.sum_le_sum h_each
        _ = Exceptional.card * a := by simp
        _ ≤ (2 * B) * a := Nat.mul_le_mul_right a hExc_all.1
        _ = 2 * a * B := by ring
    rw [hsplit_sum]
    exact Nat.add_le_add hsum_scr hsum_exc

/-- **Unconditional Lemma 7.1 cross-edge majorant (`main.tex` lines 1002–1005):**
for all integers `3 ≤ z ≤ n` and any `u : ℕ`, setting
`d := (u : ℝ) - 2 * ((phaseNat n : ℝ) - (u : ℝ)) - (z : ℝ)` (so `z = u - 2(α - u) - d`),
`binom(n, z) * 2 ^ (-(z - 1)(u - z/2)) ≤ n * ((2 log₂ n / z) * 2 ^ (-(α - u + d)/2)) ^ (z - 1)`. -/
theorem crossEdge_binom_pow_le {n z : ℕ} (hz3 : 3 ≤ z) (hzn : z ≤ n) (u : ℕ) :
    let d : ℝ := (u : ℝ) - 2 * ((phaseNat n : ℝ) - (u : ℝ)) - (z : ℝ)
    (n.choose z : ℝ) * (2 : ℝ) ^ (-(((z : ℝ) - 1) * ((u : ℝ) - (z : ℝ) / 2))) ≤
      (n : ℝ) *
        (2 * logBaseTwo (n : ℝ) / (z : ℝ) *
          (2 : ℝ) ^ (-(((phaseNat n : ℝ) - (u : ℝ) + d) / 2))) ^ (z - 1) := by
  intro d
  have hn1 : 1 < n := by omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hz_pos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (show 0 < z by omega)
  have hexp_lt_z : Real.exp 1 < (z : ℝ) :=
    lt_of_lt_of_le (lt_trans Real.exp_one_lt_d9 (by norm_num : (2.7182818286 : ℝ) < 3))
      (by exact_mod_cast hz3)
  have hbinom : (n.choose z : ℝ) ≤ (n : ℝ) * (Real.exp 1 * (n : ℝ) / (z : ℝ)) ^ (z - 1) := by
    have hdesc_nat : z.factorial * n.choose z ≤ n ^ z := by
      rw [← Nat.descFactorial_eq_factorial_mul_choose]
      exact Nat.descFactorial_le_pow n z
    have hdesc_R : (z.factorial : ℝ) * (n.choose z : ℝ) ≤ (n : ℝ) ^ z := by
      exact_mod_cast hdesc_nat
    have hfac_lb := pow_mul_exp_neg_le_factorial z
    have hfac_pos : (0 : ℝ) < (z.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos z
    have h1 : (n.choose z : ℝ) ≤ (n : ℝ) ^ z / ((z : ℝ) ^ z * Real.exp (-(z : ℝ))) := by
      have hc : (n.choose z : ℝ) ≤ (n : ℝ) ^ z / (z.factorial : ℝ) :=
        (le_div_iff₀' hfac_pos).mpr hdesc_R
      exact hc.trans (div_le_div_of_nonneg_left (pow_nonneg hn_pos.le z)
        (mul_pos (pow_pos hz_pos z) (Real.exp_pos _)) hfac_lb)
    have hpow_id : (n : ℝ) ^ z / ((z : ℝ) ^ z * Real.exp (-(z : ℝ))) =
        (Real.exp 1 / (z : ℝ)) * (n : ℝ) * (Real.exp 1 * (n : ℝ) / (z : ℝ)) ^ (z - 1) := by
      have hexp_z : Real.exp (-(z : ℝ)) = (Real.exp 1 ^ z)⁻¹ := by
        rw [← Real.exp_nat_mul, mul_one, Real.exp_neg]
      have hz1_le : 1 ≤ z := by omega
      have hnz : (n : ℝ) ^ z = (n : ℝ) * (n : ℝ) ^ (z - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hz1_le]
      have hzz : (z : ℝ) ^ z = (z : ℝ) * (z : ℝ) ^ (z - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hz1_le]
      have hez : (Real.exp 1) ^ z = Real.exp 1 * (Real.exp 1) ^ (z - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hz1_le]
      rw [hexp_z, hnz, hzz, hez, div_pow, mul_pow]
      field_simp [hz_pos.ne', (Real.exp_pos 1).ne']
    have he_div_le1 : Real.exp 1 / (z : ℝ) ≤ 1 := (div_le_one hz_pos).mpr hexp_lt_z.le
    calc (n.choose z : ℝ)
        ≤ (Real.exp 1 / (z : ℝ)) * (n : ℝ) * (Real.exp 1 * (n : ℝ) / (z : ℝ)) ^ (z - 1) :=
          h1.trans (le_of_eq hpow_id)
      _ ≤ 1 * (n : ℝ) * (Real.exp 1 * (n : ℝ) / (z : ℝ)) ^ (z - 1) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right he_div_le1 hn_pos.le) (by positivity)
      _ = (n : ℝ) * (Real.exp 1 * (n : ℝ) / (z : ℝ)) ^ (z - 1) := by ring
  have halpha_lt : alphaZero n - 1 < (phaseNat n : ℝ) := by
    have h1 : alphaZero n < (phaseInt n : ℝ) + 1 := alphaZero_lt_phaseInt_add_one n
    have h2_int : phaseInt n ≤ (phaseNat n : ℤ) := by unfold phaseNat; omega
    have h2 : (phaseInt n : ℝ) ≤ (phaseNat n : ℝ) := by exact_mod_cast h2_int
    linarith
  have hexp_ineq :
      -(((z : ℝ) - 1) * ((u : ℝ) - (z : ℝ) / 2)) ≤
        ((z - 1 : ℕ) : ℝ) *
          (-(alphaZero n - 1) / 2 + -(((phaseNat n : ℝ) - (u : ℝ) + d) / 2)) := by
    have hzm1_cast : ((z - 1 : ℕ) : ℝ) = (z : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ z), Nat.cast_one]
    rw [hzm1_cast]
    have hzm1_pos : (0 : ℝ) < (z : ℝ) - 1 := by
      have : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz3
      linarith
    have halg : (u : ℝ) - (z : ℝ) / 2 =
        (phaseNat n : ℝ) / 2 + ((phaseNat n : ℝ) - (u : ℝ) + d) / 2 := by
      dsimp [d]; ring
    rw [halg]
    have hinner :
        -((phaseNat n : ℝ) / 2 + ((phaseNat n : ℝ) - (u : ℝ) + d) / 2) ≤
          -(alphaZero n - 1) / 2 + -(((phaseNat n : ℝ) - (u : ℝ) + d) / 2) := by linarith
    rw [← mul_neg]
    exact mul_le_mul_of_nonneg_left hinner hzm1_pos.le
  have hrpow_le :
      (2 : ℝ) ^ (-(((z : ℝ) - 1) * ((u : ℝ) - (z : ℝ) / 2))) ≤
        ((2 : ℝ) ^ (-(alphaZero n - 1) / 2) *
          (2 : ℝ) ^ (-(((phaseNat n : ℝ) - (u : ℝ) + d) / 2))) ^ (z - 1) := by
    calc (2 : ℝ) ^ (-(((z : ℝ) - 1) * ((u : ℝ) - (z : ℝ) / 2)))
        ≤ (2 : ℝ) ^ (((z - 1 : ℕ) : ℝ) *
            (-(alphaZero n - 1) / 2 + -(((phaseNat n : ℝ) - (u : ℝ) + d) / 2))) :=
          Real.rpow_le_rpow_of_exponent_le one_le_two hexp_ineq
      _ = ((2 : ℝ) ^ (-(alphaZero n - 1) / 2 + -(((phaseNat n : ℝ) - (u : ℝ) + d) / 2))) ^
            (z - 1) := by
          rw [mul_comm, Real.rpow_mul two_pos.le, Real.rpow_natCast]
      _ = ((2 : ℝ) ^ (-(alphaZero n - 1) / 2) *
            (2 : ℝ) ^ (-(((phaseNat n : ℝ) - (u : ℝ) + d) / 2))) ^ (z - 1) := by
          rw [Real.rpow_add two_pos]
  rw [two_rpow_neg_half_alphaZero_sub_one hn1] at hrpow_le
  calc (n.choose z : ℝ) * (2 : ℝ) ^ (-(((z : ℝ) - 1) * ((u : ℝ) - (z : ℝ) / 2)))
      ≤ ((n : ℝ) * (Real.exp 1 * (n : ℝ) / (z : ℝ)) ^ (z - 1)) *
          ((2 * logBaseTwo (n : ℝ)) / (Real.exp 1 * (n : ℝ)) *
            (2 : ℝ) ^ (-(((phaseNat n : ℝ) - (u : ℝ) + d) / 2))) ^ (z - 1) :=
        mul_le_mul hbinom hrpow_le (by positivity) (by positivity)
    _ = (n : ℝ) *
          ((Real.exp 1 * (n : ℝ) / (z : ℝ)) *
            ((2 * logBaseTwo (n : ℝ)) / (Real.exp 1 * (n : ℝ)) *
              (2 : ℝ) ^ (-(((phaseNat n : ℝ) - (u : ℝ) + d) / 2)))) ^ (z - 1) := by
        rw [mul_assoc, ← mul_pow]
    _ = (n : ℝ) *
          (2 * logBaseTwo (n : ℝ) / (z : ℝ) *
            (2 : ℝ) ^ (-(((phaseNat n : ℝ) - (u : ℝ) + d) / 2))) ^ (z - 1) := by
        congr 2
        field_simp [hz_pos.ne', hn_pos.ne', (Real.exp_pos 1).ne']

/-- **Lemma 7.2 Poisson overlap-kernel identity & finite-set majorant:**
for any finite index type `ι` and nonnegative kernel `T : ι → ℝ`:
1. over every finite set `S : Finset (ι → ℕ)` of multi-indices,
   `∑ r ∈ S, ∏ i : ι, (T i)^(r i) / (r i)! ≤ exp(∑ i : ι, T i)`;
2. the full countable series over all `r : ι → ℕ` converges to `exp(∑ i : ι, T i)`. -/
theorem finset_sum_prod_pow_div_factorial_le_exp_and_tsum_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → ℝ) (hT : ∀ i : ι, 0 ≤ T i) :
    (∀ S : Finset (ι → ℕ),
      (∑ r ∈ S, ∏ i : ι, (T i) ^ (r i) / ((r i).factorial : ℝ)) ≤
        Real.exp (∑ i : ι, T i)) ∧
    HasSum (fun r : ι → ℕ ↦ ∏ i : ι, (T i) ^ (r i) / ((r i).factorial : ℝ))
      (Real.exp (∑ i : ι, T i)) := by
  let term : (ι → ℕ) → ℝ := fun r ↦ ∏ i : ι, (T i) ^ (r i) / ((r i).factorial : ℝ)
  have hterm_nn : ∀ r : ι → ℕ, 0 ≤ term r := fun r ↦
    Finset.prod_nonneg fun i _ ↦ div_nonneg (pow_nonneg (hT i) _) (Nat.cast_nonneg _)
  let cube : ℕ → Finset (ι → ℕ) := fun N ↦
    Fintype.piFinset fun _ : ι ↦ Finset.range (N + 1)
  have hcube_eq : ∀ N : ℕ,
      ∑ r ∈ cube N, term r =
        ∏ i : ι, ∑ k ∈ Finset.range (N + 1), (T i) ^ k / (k.factorial : ℝ) := by
    intro N
    simpa [cube, term, Fintype.piFinset_univ] using
      (Finset.prod_univ_sum (fun _ : ι ↦ Finset.range (N + 1))
        fun (i : ι) (k : ℕ) ↦ (T i) ^ k / (k.factorial : ℝ)).symm
  have hcube_le : ∀ N : ℕ, ∑ r ∈ cube N, term r ≤ Real.exp (∑ i : ι, T i) := by
    intro N
    rw [hcube_eq N, Real.exp_sum]
    refine Finset.prod_le_prod (fun i _ ↦ ?_) (fun i _ ↦ Real.sum_le_exp_of_nonneg (hT i) (N + 1))
    exact Finset.sum_nonneg fun k _ ↦ div_nonneg (pow_nonneg (hT i) k) (Nat.cast_nonneg _)
  have hfin_le : ∀ S : Finset (ι → ℕ), ∑ r ∈ S, term r ≤ Real.exp (∑ i : ι, T i) := by
    intro S
    let N : ℕ := S.sup fun r ↦ Finset.univ.sup r
    have hsub : S ⊆ cube N := by
      intro r hr
      simp only [cube, Fintype.mem_piFinset, Finset.mem_range]
      intro i
      have h1 : r i ≤ Finset.univ.sup r := Finset.le_sup (Finset.mem_univ i)
      have h2 : Finset.univ.sup r ≤ N := Finset.le_sup hr
      omega
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun r _ _ ↦ hterm_nn r).trans (hcube_le N)
  refine ⟨hfin_le, ?_⟩
  have hconv_coord : ∀ i : ι,
      Tendsto (fun N : ℕ ↦ ∑ k ∈ Finset.range (N + 1), (T i) ^ k / (k.factorial : ℝ))
        atTop (nhds (Real.exp (T i))) := by
    intro i
    have hexp_hs : HasSum (fun k : ℕ ↦ (T i) ^ k / (k.factorial : ℝ)) (Real.exp (T i)) := by
      rw [Real.exp_eq_exp_ℝ]
      exact NormedSpace.expSeries_div_hasSum_exp (T i)
    exact hexp_hs.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hconv_cube :
      Tendsto (fun N : ℕ ↦ ∑ r ∈ cube N, term r) atTop (nhds (Real.exp (∑ i : ι, T i))) := by
    simp_rw [hcube_eq, Real.exp_sum]
    exact tendsto_finsetProd Finset.univ fun i _ ↦ hconv_coord i
  change Tendsto (fun s : Finset (ι → ℕ) ↦ ∑ b ∈ s, term b)
    atTop (nhds (Real.exp (∑ i : ι, T i)))
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp hconv_cube eps heps
  refine ⟨cube N₀, fun S hS ↦ ?_⟩
  have hlo : ∑ r ∈ cube N₀, term r ≤ ∑ r ∈ S, term r :=
    Finset.sum_le_sum_of_subset_of_nonneg hS fun r _ _ ↦ hterm_nn r
  have hhi : ∑ r ∈ S, term r ≤ Real.exp (∑ i : ι, T i) := hfin_le S
  have hc0 := hN₀ N₀ le_rfl
  rw [Real.dist_eq] at hc0 ⊢
  rw [abs_of_nonpos (by linarith [hcube_le N₀])] at hc0
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- **Lemma 7.2 asymptotic `exp(O_M((log n)⁵))` overlap-kernel bound (`main.tex` lines 1084–1093):**
for every `M : ℕ` and `c₀ ∈ (0, 1)`, there exists `C_ov > 0` such that eventually for all `n`,
uniformly over `n_tr, t : ℕ` with `n^(1 - c₀) ≤ n_tr ≤ n` and `t * (phaseNat n - (M + 1)) ≤ n_tr`,
the product of the small-`x` (`2 ≤ x ≤ 2M + 4`) Poisson overlap factor and the large-`x`
(`≤ 2 ⌊(log n)³⌋` exceptional blocks of size `≤ phaseNat n`) factor is bounded by
`exp(C_ov * (log n)⁵)`. -/
theorem eventually_overlapKernel_le_exp_polylog5 (M : ℕ)
    {c₀ : ℝ} (hc₀ : c₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C_ov : ℝ, 0 < C_ov ∧ ∀ᶠ n : ℕ in atTop,
      ∀ n_tr t : ℕ,
        (n : ℝ) ^ (1 - c₀) ≤ (n_tr : ℝ) →
        n_tr ≤ n →
        t * (phaseNat n - (M + 1)) ≤ n_tr →
        Real.exp
            (∑ x ∈ Finset.Icc 2 (2 * M + 4),
              Real.exp (x : ℝ) *
                ((t : ℝ) * (phaseNat n : ℝ) ^ x / (x.factorial : ℝ)) ^ 2 /
                ((n_tr.choose x : ℝ) * (2 : ℝ) ^ (-(x.choose 2 : ℝ)))) *
          (((2 * (Real.log (n : ℝ)) ^ 3 + 1) ^ ((M + 1) ^ 3)) *
            (max 1 ((t : ℝ) ^ 2 * (phaseNat n : ℝ) ^ (2 * phaseNat n) *
              Real.exp (phaseNat n : ℝ) * (2 : ℝ) ^ ((phaseNat n).choose 2 : ℝ))) ^
              (2 * Nat.floor ((Real.log (n : ℝ)) ^ 3))) ≤
          Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) := by
  set X_max : ℕ := 2 * M + 4
  set C_small_term : ℝ :=
    4 * Real.exp (X_max : ℝ) * (2 : ℝ) ^ (X_max.choose 2) * (4 : ℝ) ^ (2 * X_max) *
      (2 : ℝ) ^ X_max * (X_max : ℝ) ^ X_max
  set C_small : ℝ := ((X_max + 1 : ℕ) : ℝ) * C_small_term
  have hC_small_pos : 0 < C_small := by dsimp [C_small, C_small_term]; positivity
  refine ⟨C_small + 80, by linarith, ?_⟩
  have h1mc₀_pos : 0 < 1 - c₀ := sub_pos.mpr hc₀.2
  have ho_log : (fun y : ℝ ↦ (Real.log y) ^ ((2 * X_max : ℕ) : ℝ)) =o[atTop]
      (fun y : ℝ ↦ y ^ (1 - c₀)) :=
    isLittleO_log_rpow_rpow_atTop _ h1mc₀_pos
  have hb_log := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Asymptotics.isLittleO_iff.mp ho_log one_pos)
  have hb_ntr_min : ∀ᶠ n : ℕ in atTop, (2 * X_max : ℝ) ≤ (n : ℝ) ^ (1 - c₀) := by
    have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (1 - c₀)) atTop atTop :=
      (tendsto_rpow_atTop h1mc₀_pos).comp tendsto_natCast_atTop_atTop
    exact ht.eventually_ge_atTop (2 * X_max : ℝ)
  have hL_large : ∀ᶠ n : ℕ in atTop,
      max (2 * ((M + 1 : ℕ) : ℝ) + 4) (Real.exp 4) ≤ logOrder n ∧
      ((M + 1 : ℕ) : ℝ) ^ 3 * Real.log (3 * (Real.log (n : ℝ)) ^ 3) ≤ (Real.log (n : ℝ)) ^ 5 := by
    have h1 := tendsto_logOrder_atTop.eventually
      (eventually_ge_atTop (max (2 * ((M + 1 : ℕ) : ℝ) + 4) (Real.exp 4)))
    have h2 : ∀ᶠ n : ℕ in atTop,
        ((M + 1 : ℕ) : ℝ) ^ 3 * Real.log (3 * (Real.log (n : ℝ)) ^ 3) ≤ (Real.log (n : ℝ)) ^ 5 := by
      filter_upwards [tendsto_logOrder_atTop.eventually
        (eventually_ge_atTop (max 3 (((M + 1 : ℕ) : ℝ) ^ 3 + 4)))] with n hLm
      set L := logOrder n
      have hL3 : 3 ≤ L := le_trans (le_max_left _ _) hLm
      have hLM : ((M + 1 : ℕ) : ℝ) ^ 3 + 4 ≤ L := le_trans (le_max_right _ _) hLm
      have h3L3 : 3 * L ^ 3 ≤ L ^ 4 := by
        calc 3 * L ^ 3 ≤ L * L ^ 3 :=
              mul_le_mul_of_nonneg_right hL3 (pow_nonneg (by linarith) 3)
          _ = L ^ 4 := (pow_succ' L 3).symm
      have hlog_le : Real.log (3 * L ^ 3) ≤ 4 * L := by
        have hl1 : Real.log (3 * L ^ 3) ≤ Real.log (L ^ 4) :=
          Real.log_le_log (by linarith [pow_pos (by linarith : 0 < L) 3]) h3L3
        rw [Real.log_pow] at hl1
        have hl2 : Real.log L ≤ L :=
          le_trans (Real.log_le_sub_one_of_pos (by linarith)) (by linarith)
        push_cast at hl1
        linarith
      have hM3_le : ((M + 1 : ℕ) : ℝ) ^ 3 ≤ L := by
        have hnn : (0 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) ^ 3 := by positivity
        linarith
      have h4L_le : 4 * L ≤ L ^ 2 := by
        have h4 : (4 : ℝ) ≤ L := by
          have hnn : (0 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) ^ 3 := by positivity
          linarith
        calc 4 * L ≤ L * L := mul_le_mul_of_nonneg_right h4 (by linarith)
          _ = L ^ 2 := (sq L).symm
      have hL3_le_L5 : L ^ 3 ≤ L ^ 5 := pow_le_pow_right₀ (by linarith) (by omega)
      have hprod_le : ((M + 1 : ℕ) : ℝ) ^ 3 * Real.log (3 * L ^ 3) ≤ L ^ 5 := by
        calc ((M + 1 : ℕ) : ℝ) ^ 3 * Real.log (3 * L ^ 3)
            ≤ L * (4 * L) :=
              mul_le_mul hM3_le hlog_le
                (Real.log_nonneg (by linarith [one_le_pow₀ (by linarith : (1 : ℝ) ≤ L) (n := 3)]))
                (by linarith)
          _ ≤ L * L ^ 2 := mul_le_mul_of_nonneg_left h4L_le (by linarith)
          _ = L ^ 3 := (pow_succ' L 2).symm
          _ ≤ L ^ 5 := hL3_le_L5
      simpa only [L, logOrder] using hprod_le
    exact h1.and h2
  filter_upwards [eventually_gt_atTop 3,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
    hb_log, hb_ntr_min, hL_large] with n hn3 hPh hlog_n hntr_min ⟨hLm, hpoly5⟩
    n_tr t hntr_lo hntr_hi ht_le
  set L : ℝ := Real.log (n : ℝ)
  unfold logOrder at hLm hPh
  have hL_ge_m : 2 * ((M + 1 : ℕ) : ℝ) + 4 ≤ L := le_trans (le_max_left _ _) hLm
  have hL_ge_e4 : Real.exp 4 ≤ L := le_trans (le_max_right _ _) hLm
  have hL_pos : 0 < L := lt_of_lt_of_le (Real.exp_pos 4) hL_ge_e4
  have hL_ge4 : 4 < L := by
    have := Real.log_le_log (Real.exp_pos 4) hL_ge_e4
    rw [Real.log_exp] at this
    have he4 : (4 : ℝ) < Real.exp 4 := by
      have := Real.add_one_lt_exp (by norm_num : (4 : ℝ) ≠ 0); linarith
    linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have ha_ge_L : L ≤ (phaseNat n : ℝ) := hPh.1
  have ha_le_4L : (phaseNat n : ℝ) ≤ 4 * L := hPh.2
  have hu_min_ge : L / 2 ≤ ((phaseNat n - (M + 1) : ℕ) : ℝ) := by
    have hle_nat : M + 1 ≤ phaseNat n := by
      have : ((M + 1 : ℕ) : ℝ) ≤ (phaseNat n : ℝ) := by linarith
      exact_mod_cast this
    rw [Nat.cast_sub hle_nat]
    linarith
  have ht_div_ntr : (t : ℝ) ≤ 2 * (n_tr : ℝ) / L := by
    rw [le_div_iff₀ hL_pos]
    have htR : (t : ℝ) * ((phaseNat n - (M + 1) : ℕ) : ℝ) ≤ (n_tr : ℝ) := by
      exact_mod_cast ht_le
    have hm := mul_le_mul_of_nonneg_left hu_min_ge (Nat.cast_nonneg t)
    linarith
  have hntr_ge_2X : 2 * X_max ≤ n_tr := by
    have : (2 * X_max : ℝ) ≤ (n_tr : ℝ) := le_trans hntr_min hntr_lo
    exact_mod_cast this
  have hL_pow_le_ntr : L ^ (2 * X_max) ≤ (n_tr : ℝ) := by
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hL_pos _),
      abs_of_pos (Real.rpow_pos_of_pos hn_pos _), Real.rpow_natCast] at hlog_n
    exact le_trans hlog_n hntr_lo
  -- 1. Small-`x` sum bound `≤ C_small * L^2 ≤ C_small * L^5`
  have hsmall_each : ∀ x ∈ Finset.Icc 2 X_max,
      Real.exp (x : ℝ) * ((t : ℝ) * (phaseNat n : ℝ) ^ x / (x.factorial : ℝ)) ^ 2 /
          ((n_tr.choose x : ℝ) * (2 : ℝ) ^ (-(x.choose 2 : ℝ))) ≤
        C_small_term * L ^ 2 := by
    intro x hx
    obtain ⟨hx2, hx_max⟩ := Finset.mem_Icc.mp hx
    have hchoose_lb : ((n_tr : ℝ) / (2 * (x : ℝ))) ^ x ≤ (n_tr.choose x : ℝ) := by
      have h2x_le : 2 * x ≤ n_tr := by omega
      have hdesc_lb : (n_tr - x) ^ x ≤ n_tr.descFactorial x :=
        (Nat.pow_le_pow_left (by omega : n_tr - x ≤ n_tr + 1 - x) x).trans
          (Nat.pow_sub_le_descFactorial n_tr x)
      have hfac_ub : x.factorial ≤ x ^ x := Nat.factorial_le_pow x
      have hnat_mul : (n_tr - x) ^ x ≤ x ^ x * n_tr.choose x := by
        calc (n_tr - x) ^ x ≤ n_tr.descFactorial x := hdesc_lb
          _ = x.factorial * n_tr.choose x := Nat.descFactorial_eq_factorial_mul_choose n_tr x
          _ ≤ x ^ x * n_tr.choose x := Nat.mul_le_mul_right _ hfac_ub
      have hR_mul : (((n_tr - x : ℕ) : ℝ)) ^ x ≤ (x : ℝ) ^ x * (n_tr.choose x : ℝ) := by
        exact_mod_cast hnat_mul
      have hsub_ge : (n_tr : ℝ) / 2 ≤ ((n_tr - x : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega : x ≤ n_tr)]
        have : (2 : ℝ) * (x : ℝ) ≤ (n_tr : ℝ) := by exact_mod_cast h2x_le
        linarith
      have hpow_half : ((n_tr : ℝ) / 2) ^ x ≤ (((n_tr - x : ℕ) : ℝ)) ^ x :=
        pow_le_pow_left₀ (by positivity) hsub_ge x
      have hx_pos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (show 0 < x by omega)
      rw [div_pow, mul_pow, div_le_iff₀ (mul_pos (pow_pos two_pos x) (pow_pos hx_pos x))]
      calc (n_tr : ℝ) ^ x = ((n_tr : ℝ) / 2) ^ x * (2 : ℝ) ^ x := by
            rw [div_pow, div_mul_cancel₀ _ (pow_pos two_pos x).ne']
        _ ≤ ((x : ℝ) ^ x * (n_tr.choose x : ℝ)) * (2 : ℝ) ^ x :=
            mul_le_mul_of_nonneg_right (hpow_half.trans hR_mul) (by positivity)
        _ = (n_tr.choose x : ℝ) * ((2 : ℝ) ^ x * (x : ℝ) ^ x) := by ring
    have hntr_pos : (0 : ℝ) < (n_tr : ℝ) := by exact_mod_cast (show 0 < n_tr by omega)
    have hfac_ge1 : (1 : ℝ) ≤ (x.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos x
    have hnum_le :
        ((t : ℝ) * (phaseNat n : ℝ) ^ x / (x.factorial : ℝ)) ^ 2 ≤
          4 * (4 : ℝ) ^ (2 * x) * (n_tr : ℝ) ^ 2 * L ^ (2 * x - 2) := by
      have h1 : (t : ℝ) * (phaseNat n : ℝ) ^ x / (x.factorial : ℝ) ≤
          (2 * (n_tr : ℝ) / L) * (4 * L) ^ x := by
        calc (t : ℝ) * (phaseNat n : ℝ) ^ x / (x.factorial : ℝ)
            ≤ (t : ℝ) * (phaseNat n : ℝ) ^ x / 1 :=
              div_le_div_of_nonneg_left (by positivity) one_pos hfac_ge1
          _ = (t : ℝ) * (phaseNat n : ℝ) ^ x := div_one _
          _ ≤ (2 * (n_tr : ℝ) / L) * (4 * L) ^ x :=
              mul_le_mul ht_div_ntr (pow_le_pow_left₀ (by positivity) ha_le_4L x)
                (by positivity) (by positivity)
      have hsq := pow_le_pow_left₀ (by positivity) h1 2
      refine hsq.trans (le_of_eq ?_)
      have hLpow : (L ^ x) ^ 2 = L ^ (2 * x - 2) * L ^ 2 := by
        rw [← pow_mul, mul_comm x 2, ← pow_add, Nat.sub_add_cancel (by omega : 2 ≤ 2 * x)]
      have h4pow : ((4 : ℝ) ^ x) ^ 2 = (4 : ℝ) ^ (2 * x) := by
        rw [← pow_mul, mul_comm x 2]
      rw [mul_pow, div_pow, mul_pow (4 : ℝ) L x, mul_pow ((4 : ℝ) ^ x) (L ^ x) 2, h4pow, hLpow]
      field_simp [hL_pos.ne']
      ring
    have hratio_L2 :
        (n_tr : ℝ) ^ 2 * L ^ (2 * x - 2) ≤ (n_tr : ℝ) ^ x * L ^ 2 := by
      rcases eq_or_lt_of_le hx2 with rfl | hx_gt2
      · simp
      · have hpow_split : L ^ (2 * x - 2) = L ^ (2 * x - 4) * L ^ 2 := by
          rw [← pow_add]; congr 1; omega
        have hn_split : (n_tr : ℝ) ^ x = (n_tr : ℝ) ^ 2 * (n_tr : ℝ) ^ (x - 2) := by
          rw [← pow_add]; congr 1; omega
        have hL_sub : L ^ (2 * x - 4) ≤ L ^ (2 * X_max) :=
          pow_le_pow_right₀ (by linarith) (by omega)
        have hntr_pow : (n_tr : ℝ) ≤ (n_tr : ℝ) ^ (x - 2) :=
          le_self_pow₀ (by exact_mod_cast (show 1 ≤ n_tr by omega)) (by omega)
        have hm : L ^ (2 * x - 4) ≤ (n_tr : ℝ) ^ (x - 2) :=
          hL_sub.trans (hL_pow_le_ntr.trans hntr_pow)
        rw [hpow_split, hn_split]
        calc (n_tr : ℝ) ^ 2 * (L ^ (2 * x - 4) * L ^ 2)
            = ((n_tr : ℝ) ^ 2 * L ^ (2 * x - 4)) * L ^ 2 := by ring
          _ ≤ ((n_tr : ℝ) ^ 2 * (n_tr : ℝ) ^ (x - 2)) * L ^ 2 :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hm (sq_nonneg _)) (sq_nonneg _)
          _ = (n_tr : ℝ) ^ 2 * (n_tr : ℝ) ^ (x - 2) * L ^ 2 := by ring
    have hexp_x : Real.exp (x : ℝ) ≤ Real.exp (X_max : ℝ) :=
      Real.exp_le_exp.mpr (by exact_mod_cast hx_max)
    have h2choose : ((2 : ℝ) ^ (-(x.choose 2 : ℝ)))⁻¹ ≤ (2 : ℝ) ^ (X_max.choose 2) := by
      rw [Real.rpow_neg two_pos.le, inv_inv, Real.rpow_natCast]
      exact pow_le_pow_right₀ one_le_two (Nat.choose_le_choose 2 hx_max)
    have hden_pos : 0 < (n_tr.choose x : ℝ) * (2 : ℝ) ^ (-(x.choose 2 : ℝ)) :=
      mul_pos (lt_of_lt_of_le (by positivity) hchoose_lb) (Real.rpow_pos_of_pos two_pos _)
    calc Real.exp (x : ℝ) * ((t : ℝ) * (phaseNat n : ℝ) ^ x / (x.factorial : ℝ)) ^ 2 /
            ((n_tr.choose x : ℝ) * (2 : ℝ) ^ (-(x.choose 2 : ℝ)))
        = Real.exp (x : ℝ) * (((2 : ℝ) ^ (-(x.choose 2 : ℝ)))⁻¹) *
            (((t : ℝ) * (phaseNat n : ℝ) ^ x / (x.factorial : ℝ)) ^ 2 / (n_tr.choose x : ℝ)) := by
          field_simp [hden_pos.ne']
      _ ≤ Real.exp (X_max : ℝ) * (2 : ℝ) ^ (X_max.choose 2) *
            ((4 * (4 : ℝ) ^ (2 * x) * (n_tr : ℝ) ^ 2 * L ^ (2 * x - 2)) /
              (((n_tr : ℝ) / (2 * (x : ℝ))) ^ x)) := by
          refine mul_le_mul (mul_le_mul hexp_x h2choose (by positivity) (by positivity)) ?_
            (by positivity) (by positivity)
          exact div_le_div₀ (by positivity) hnum_le (by positivity) hchoose_lb
      _ ≤ Real.exp (X_max : ℝ) * (2 : ℝ) ^ (X_max.choose 2) *
            (4 * (4 : ℝ) ^ (2 * x) * (2 * (x : ℝ)) ^ x * L ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_pow, div_div_eq_mul_div, div_le_iff₀ (pow_pos hntr_pos x)]
          calc 4 * (4 : ℝ) ^ (2 * x) * (n_tr : ℝ) ^ 2 * L ^ (2 * x - 2) * (2 * (x : ℝ)) ^ x
              = 4 * (4 : ℝ) ^ (2 * x) * (2 * (x : ℝ)) ^ x *
                  ((n_tr : ℝ) ^ 2 * L ^ (2 * x - 2)) := by ring
            _ ≤ 4 * (4 : ℝ) ^ (2 * x) * (2 * (x : ℝ)) ^ x * ((n_tr : ℝ) ^ x * L ^ 2) :=
                mul_le_mul_of_nonneg_left hratio_L2 (by positivity)
            _ = 4 * (4 : ℝ) ^ (2 * x) * (2 * (x : ℝ)) ^ x * L ^ 2 * (n_tr : ℝ) ^ x := by ring
      _ ≤ C_small_term * L ^ 2 := by
          dsimp [C_small_term]
          have h4_le : (4 : ℝ) ^ (2 * x) ≤ (4 : ℝ) ^ (2 * X_max) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          have h2x_pow : (2 * (x : ℝ)) ^ x ≤ (2 : ℝ) ^ X_max * (X_max : ℝ) ^ X_max := by
            rw [mul_pow]
            have h2p : (2 : ℝ) ^ x ≤ (2 : ℝ) ^ X_max := pow_le_pow_right₀ one_le_two hx_max
            have hxp : (x : ℝ) ^ x ≤ (X_max : ℝ) ^ X_max := by
              calc (x : ℝ) ^ x ≤ (X_max : ℝ) ^ x :=
                    pow_le_pow_left₀ (by positivity) (by exact_mod_cast hx_max) x
                _ ≤ (X_max : ℝ) ^ X_max :=
                    pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ X_max by dsimp [X_max]; omega))
                      hx_max
            exact mul_le_mul h2p hxp (by positivity) (by positivity)
          have hprod := mul_le_mul h4_le h2x_pow (by positivity) (by positivity)
          have hmul_front := mul_le_mul_of_nonneg_left hprod
            (show 0 ≤ 4 * Real.exp (X_max : ℝ) * (2 : ℝ) ^ (X_max.choose 2) by positivity)
          have hmul_L := mul_le_mul_of_nonneg_right hmul_front (sq_nonneg L)
          linarith [show 4 * Real.exp (X_max : ℝ) * (2 : ℝ) ^ (X_max.choose 2) *
              ((4 : ℝ) ^ (2 * x) * (2 * (x : ℝ)) ^ x) * L ^ 2 =
            Real.exp (X_max : ℝ) * (2 : ℝ) ^ (X_max.choose 2) *
              (4 * (4 : ℝ) ^ (2 * x) * (2 * (x : ℝ)) ^ x * L ^ 2) by ring,
            show 4 * Real.exp (X_max : ℝ) * (2 : ℝ) ^ (X_max.choose 2) *
              ((4 : ℝ) ^ (2 * X_max) * ((2 : ℝ) ^ X_max * (X_max : ℝ) ^ X_max)) * L ^ 2 =
            4 * Real.exp (X_max : ℝ) * (2 : ℝ) ^ (X_max.choose 2) * (4 : ℝ) ^ (2 * X_max) *
              (2 : ℝ) ^ X_max * (X_max : ℝ) ^ X_max * L ^ 2 by ring]
  have hsmall_sum :
      (∑ x ∈ Finset.Icc 2 X_max,
        Real.exp (x : ℝ) * ((t : ℝ) * (phaseNat n : ℝ) ^ x / (x.factorial : ℝ)) ^ 2 /
          ((n_tr.choose x : ℝ) * (2 : ℝ) ^ (-(x.choose 2 : ℝ)))) ≤ C_small * L ^ 5 := by
    have hcard : ((Finset.Icc 2 X_max).card : ℝ) ≤ ((X_max + 1 : ℕ) : ℝ) := by
      rw [Nat.card_Icc]; exact_mod_cast (show X_max + 1 - 2 ≤ X_max + 1 by omega)
    have hL2_le_L5 : L ^ 2 ≤ L ^ 5 := pow_le_pow_right₀ (by linarith) (by omega)
    calc ∑ x ∈ Finset.Icc 2 X_max, _
        ≤ ∑ _x ∈ Finset.Icc 2 X_max, C_small_term * L ^ 2 := Finset.sum_le_sum hsmall_each
      _ = ((Finset.Icc 2 X_max).card : ℝ) * (C_small_term * L ^ 2) := by simp
      _ ≤ ((X_max + 1 : ℕ) : ℝ) * (C_small_term * L ^ 2) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = C_small * L ^ 2 := by dsimp [C_small]; ring
      _ ≤ C_small * L ^ 5 := mul_le_mul_of_nonneg_left hL2_le_L5 hC_small_pos.le
  -- 2. Large-`x` combinatorial factor `(2 L^3 + 1)^((M + 1)^3) ≤ exp(L^5)`
  have hlarge_comb :
      (2 * L ^ 3 + 1) ^ ((M + 1) ^ 3) ≤ Real.exp (L ^ 5) := by
    have h1_le_L3 : 1 ≤ L ^ 3 := one_le_pow₀ (by linarith)
    have h2L3 : 2 * L ^ 3 + 1 ≤ 3 * L ^ 3 := by linarith
    have hp1 : (2 * L ^ 3 + 1) ^ ((M + 1) ^ 3) ≤ (3 * L ^ 3) ^ ((M + 1) ^ 3) :=
      pow_le_pow_left₀ (by positivity) h2L3 _
    have hexp_eq : (3 * L ^ 3) ^ ((M + 1) ^ 3) =
        Real.exp (((M + 1 : ℕ) : ℝ) ^ 3 * Real.log (3 * L ^ 3)) := by
      rw [← Real.exp_log (by positivity : 0 < (3 * L ^ 3) ^ ((M + 1) ^ 3)), Real.log_pow]
      push_cast; rfl
    exact hp1.trans (hexp_eq.le.trans (Real.exp_le_exp.mpr hpoly5))
  -- 3. Large-`x` weight factor `(max 1 (...))^(2 ⌊L^3⌋) ≤ exp(72 * L^5)`
  have hlarge_wt :
      (max 1 ((t : ℝ) ^ 2 * (phaseNat n : ℝ) ^ (2 * phaseNat n) *
        Real.exp (phaseNat n : ℝ) * (2 : ℝ) ^ ((phaseNat n).choose 2 : ℝ))) ^
          (2 * Nat.floor (L ^ 3)) ≤
        Real.exp (72 * L ^ 5) := by
    have ht_le_n : (t : ℝ) ≤ (n : ℝ) := by
      have ht_ntr : t ≤ n_tr := by
        have hpos_u : 1 ≤ phaseNat n - (M + 1) := by
          have : (1 : ℝ) ≤ ((phaseNat n - (M + 1) : ℕ) : ℝ) := by linarith
          exact_mod_cast this
        calc t = t * 1 := (Nat.mul_one t).symm
          _ ≤ t * (phaseNat n - (M + 1)) := Nat.mul_le_mul_left t hpos_u
          _ ≤ n_tr := ht_le
      exact_mod_cast (ht_ntr.trans hntr_hi)
    have ht2_le : (t : ℝ) ^ 2 ≤ Real.exp (2 * L) := by
      have hn_exp : (n : ℝ) ^ 2 = Real.exp (2 * L) := by
        calc (n : ℝ) ^ 2 = (Real.exp L) ^ 2 := by dsimp [L]; rw [Real.exp_log hn_pos]
          _ = Real.exp (2 * L) := by rw [← Real.exp_nat_mul]; push_cast; ring
      rw [← hn_exp]
      exact pow_le_pow_left₀ (Nat.cast_nonneg t) ht_le_n 2
    have ha_le_L2 : (phaseNat n : ℝ) ≤ L ^ 2 := by
      have h4L : 4 * L ≤ L ^ 2 := by
        calc 4 * L ≤ L * L := mul_le_mul_of_nonneg_right hL_ge4.le hL_pos.le
          _ = L ^ 2 := (sq L).symm
      exact ha_le_4L.trans h4L
    have ha_pow_le : (phaseNat n : ℝ) ^ (2 * phaseNat n) ≤ Real.exp (16 * L ^ 2) := by
      have hL_le_exp : L ≤ Real.exp L :=
        le_trans (by linarith : L ≤ L + 1) (Real.add_one_le_exp L)
      have ha_le_exp2L : (phaseNat n : ℝ) ≤ Real.exp (2 * L) := by
        calc (phaseNat n : ℝ) ≤ L ^ 2 := ha_le_L2
          _ ≤ (Real.exp L) ^ 2 := pow_le_pow_left₀ hL_pos.le hL_le_exp 2
          _ = Real.exp (2 * L) := by rw [← Real.exp_nat_mul]; push_cast; ring
      have hexp_prod : (2 * (phaseNat n : ℝ)) * (2 * L) ≤ 16 * L ^ 2 := by
        calc (2 * (phaseNat n : ℝ)) * (2 * L)
            = (phaseNat n : ℝ) * (4 * L) := by ring
          _ ≤ (4 * L) * (4 * L) := mul_le_mul_of_nonneg_right ha_le_4L (by positivity)
          _ = 16 * L ^ 2 := by ring
      calc (phaseNat n : ℝ) ^ (2 * phaseNat n)
          ≤ (Real.exp (2 * L)) ^ (2 * phaseNat n) :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) ha_le_exp2L _
        _ = Real.exp ((2 * (phaseNat n : ℝ)) * (2 * L)) := by
            rw [← Real.exp_nat_mul]; push_cast; ring
        _ ≤ Real.exp (16 * L ^ 2) := Real.exp_le_exp.mpr hexp_prod
    have hexp_a_le : Real.exp (phaseNat n : ℝ) ≤ Real.exp (L ^ 2) :=
      Real.exp_le_exp.mpr ha_le_L2
    have h2ch_le : (2 : ℝ) ^ ((phaseNat n).choose 2 : ℝ) ≤ Real.exp (16 * L ^ 2) := by
      have hch_le_sq : ((phaseNat n).choose 2 : ℝ) ≤ 16 * L ^ 2 := by
        have hnat : 2 * (phaseNat n).choose 2 ≤ (phaseNat n) ^ 2 := by
          rw [Nat.choose_two_right,
            Nat.mul_div_cancel' (Nat.even_mul_pred_self (phaseNat n)).two_dvd, pow_two]
          exact Nat.mul_le_mul_left _ (Nat.sub_le _ 1)
        have hR : (2 : ℝ) * ((phaseNat n).choose 2 : ℝ) ≤ (phaseNat n : ℝ) ^ 2 := by
          exact_mod_cast hnat
        have ha_sq : (phaseNat n : ℝ) ^ 2 ≤ 16 * L ^ 2 := by
          calc (phaseNat n : ℝ) ^ 2 ≤ (4 * L) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) ha_le_4L 2
            _ = 16 * L ^ 2 := by ring
        have hch_nn : (0 : ℝ) ≤ ((phaseNat n).choose 2 : ℝ) := Nat.cast_nonneg _
        linarith
      rw [Real.rpow_def_of_pos two_pos]
      apply Real.exp_le_exp.mpr
      have hq_le1 : Real.log 2 ≤ 1 := le_trans Real.log_two_lt_d9.le (by norm_num)
      calc Real.log 2 * ((phaseNat n).choose 2 : ℝ)
          ≤ 1 * (16 * L ^ 2) := mul_le_mul hq_le1 hch_le_sq (Nat.cast_nonneg _) zero_le_one
        _ = 16 * L ^ 2 := one_mul _
    have hmax_le :
        max 1 ((t : ℝ) ^ 2 * (phaseNat n : ℝ) ^ (2 * phaseNat n) *
          Real.exp (phaseNat n : ℝ) * (2 : ℝ) ^ ((phaseNat n).choose 2 : ℝ)) ≤
          Real.exp (36 * L ^ 2) := by
      apply max_le
      · exact Real.one_le_exp (by positivity)
      · have h2L_le_L2 : 2 * L ≤ L ^ 2 := by
          calc 2 * L ≤ L * L := mul_le_mul_of_nonneg_right (by linarith) hL_pos.le
            _ = L ^ 2 := (sq L).symm
        calc (t : ℝ) ^ 2 * (phaseNat n : ℝ) ^ (2 * phaseNat n) *
                Real.exp (phaseNat n : ℝ) * (2 : ℝ) ^ ((phaseNat n).choose 2 : ℝ)
            ≤ Real.exp (2 * L) * Real.exp (16 * L ^ 2) * Real.exp (L ^ 2) * Real.exp (16 * L ^ 2) := by
              refine mul_le_mul (mul_le_mul (mul_le_mul ht2_le ha_pow_le (by positivity) (by positivity))
                hexp_a_le (by positivity) (by positivity)) h2ch_le (by positivity) (by positivity)
          _ = Real.exp (2 * L + 16 * L ^ 2 + L ^ 2 + 16 * L ^ 2) := by
              simp only [← Real.exp_add]
          _ ≤ Real.exp (36 * L ^ 2) := Real.exp_le_exp.mpr (by linarith [sq_nonneg L])
    have hfl_le : ((2 * Nat.floor (L ^ 3) : ℕ) : ℝ) ≤ 2 * L ^ 3 := by
      push_cast; linarith [Nat.floor_le (pow_nonneg hL_pos.le 3)]
    have hfl_mul : ((2 * Nat.floor (L ^ 3) : ℕ) : ℝ) * (36 * L ^ 2) ≤ 72 * L ^ 5 := by
      calc ((2 * Nat.floor (L ^ 3) : ℕ) : ℝ) * (36 * L ^ 2)
          ≤ (2 * L ^ 3) * (36 * L ^ 2) := mul_le_mul_of_nonneg_right hfl_le (by positivity)
        _ = 72 * L ^ 5 := by ring
    calc (max 1 _) ^ (2 * Nat.floor (L ^ 3))
        ≤ (Real.exp (36 * L ^ 2)) ^ (2 * Nat.floor (L ^ 3)) :=
          pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) hmax_le _
      _ = Real.exp (((2 * Nat.floor (L ^ 3) : ℕ) : ℝ) * (36 * L ^ 2)) :=
          (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (72 * L ^ 5) := Real.exp_le_exp.mpr hfl_mul
  -- Combine all three factors
  calc Real.exp (∑ x ∈ Finset.Icc 2 X_max, _) *
          (((2 * L ^ 3 + 1) ^ ((M + 1) ^ 3)) * (max 1 _) ^ (2 * Nat.floor (L ^ 3)))
      ≤ Real.exp (C_small * L ^ 5) * (Real.exp (L ^ 5) * Real.exp (72 * L ^ 5)) := by
        refine mul_le_mul (Real.exp_le_exp.mpr hsmall_sum)
          (mul_le_mul hlarge_comb hlarge_wt (by positivity) (by positivity))
          (by positivity) (by positivity)
    _ = Real.exp ((C_small + 73) * L ^ 5) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp ((C_small + 80) * L ^ 5) :=
        Real.exp_le_exp.mpr (by linarith [pow_pos hL_pos 5])

/-- **Proposition 7.3 similar-range quadratic decay (`main.tex` lines 1128–1129):**
for every `M : ℕ` and `c₀ ∈ (0, 1/4)`, eventually for all `n` and all `k ≤ n`,
`a ≤ phaseNat n`, and `z ≥ phaseNat n - (3M + 4)`,
`k * n^((1 - c₀) a) * 2^(-binom(z, 2)) ≤ 1 / 2` (so `∑_{s=0}^k (...)^s ≤ 2`). -/
theorem eventually_similarRange_geom_ratio_le_half (M : ℕ)
    {c₀ : ℝ} (hc₀ : c₀ ∈ Set.Ioo (0 : ℝ) (1 / 4)) :
    ∀ᶠ n : ℕ in atTop,
      ∀ k a z : ℕ,
        k ≤ n →
        a ≤ phaseNat n →
        phaseNat n - (3 * M + 4) ≤ z →
        (k : ℝ) * (n : ℝ) ^ ((1 - c₀) * (a : ℝ)) * (2 : ℝ) ^ (-(z.choose 2 : ℝ)) ≤ 1 / 2 := by
  set ε : ℝ := c₀ / 8
  have hε_pos : 0 < ε := by dsimp [ε]; linarith [hc₀.1]
  -- `phaseNat n / logBaseTwo n = (phaseNat n * q) / logOrder n → 2`
  have hlim := tendsto_phaseNat_add_mul_q_div_logOrder_two 0
  have hhi_ev : ∀ᶠ n : ℕ in atTop,
      (((phaseNat n + 0 : ℕ) : ℝ) * q) / logOrder n < 2 + ε :=
    (tendsto_order.1 hlim).2 (2 + ε) (by linarith)
  have hlo_ev : ∀ᶠ n : ℕ in atTop,
      2 - ε / 2 < (((phaseNat n + 0 : ℕ) : ℝ) * q) / logOrder n :=
    (tendsto_order.1 hlim).1 (2 - ε / 2) (by linarith)
  have hB_large : ∀ᶠ n : ℕ in atTop,
      max 4 (max ((2 * ((3 * M + 5 : ℕ) : ℝ)) / ε) (4 / c₀)) ≤ logBaseTwo (n : ℝ) := by
    have ht : Tendsto (fun n : ℕ ↦ logBaseTwo (n : ℝ)) atTop atTop := by
      unfold logBaseTwo
      exact tendsto_logOrder_atTop.atTop_div_const q_pos
    exact ht.eventually_ge_atTop _
  filter_upwards [eventually_gt_atTop 2, hhi_ev, hlo_ev, hB_large] with
    n hn2 hhi hlo hBm k a z hkn ha_le hz_ge
  set B : ℝ := logBaseTwo (n : ℝ)
  have hB4 : 4 ≤ B := le_trans (le_max_left _ _) hBm
  have hB_m : (2 * ((3 * M + 5 : ℕ) : ℝ)) / ε ≤ B :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hBm)
  have hB_c : 4 / c₀ ≤ B :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hBm)
  have hB_pos : 0 < B := by linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hL_pos : 0 < logOrder n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  -- Rewrite `(((phaseNat n + 0) * q) / logOrder n) = (phaseNat n : ℝ) / B`
  have hph_div_B : (((phaseNat n + 0 : ℕ) : ℝ) * q) / logOrder n = (phaseNat n : ℝ) / B := by
    rw [Nat.add_zero]
    dsimp [B]
    unfold logBaseTwo logOrder
    field_simp [q_pos.ne', hL_pos.ne']
  rw [hph_div_B, div_lt_iff₀ hB_pos] at hhi
  rw [hph_div_B, lt_div_iff₀ hB_pos] at hlo
  -- Upper bound on `a` and lower bound on `z - 1`
  have ha_ub : (a : ℝ) ≤ (2 + ε) * B :=
    le_trans (by exact_mod_cast ha_le) hhi.le
  have h3M5_le_epsB : ((3 * M + 5 : ℕ) : ℝ) ≤ (ε / 2) * B := by
    have hm := (div_le_iff₀ hε_pos).mp hB_m
    linarith
  have hz1_lb : (2 - ε) * B ≤ (z : ℝ) - 1 := by
    have hph_ge : 3 * M + 5 ≤ phaseNat n := by
      have h1 : ((3 * M + 5 : ℕ) : ℝ) ≤ (phaseNat n : ℝ) := by
        have : ε < 1 := by dsimp [ε]; linarith [hc₀.2]
        nlinarith [hlo, h3M5_le_epsB, hB4]
      exact_mod_cast h1
    have hz_ge1 : 1 ≤ z := by omega
    have hz_R : (phaseNat n : ℝ) - ((3 * M + 4 : ℕ) : ℝ) ≤ (z : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).mpr hz_ge
      rw [Nat.cast_sub (by omega : 3 * M + 4 ≤ phaseNat n)] at this
      exact this
    push_cast at h3M5_le_epsB hz_R
    linarith
  have hchoose_lb : (2 - c₀ / 4) * B ^ 2 ≤ (z.choose 2 : ℝ) := by
    have hz1 : 1 ≤ z := by
      have : (0 : ℝ) < (z : ℝ) - 1 := by
        have : ε < 1 := by dsimp [ε]; linarith [hc₀.2]
        nlinarith
      have : (1 : ℝ) < (z : ℝ) := by linarith
      exact_mod_cast this.le
    have hch_eq : (z.choose 2 : ℝ) = (z : ℝ) * ((z : ℝ) - 1) / 2 := by
      rw [Nat.choose_two_right, Nat.cast_div (Nat.even_mul_pred_self z).two_dvd (by norm_num)]
      push_cast [Nat.cast_sub hz1]
      ring
    rw [hch_eq]
    have hzm1_nn : 0 ≤ (2 - ε) * B := by
      have : ε < 1 := by dsimp [ε]; linarith [hc₀.2]
      nlinarith
    have hsq_le : ((2 - ε) * B) ^ 2 ≤ (z : ℝ) * ((z : ℝ) - 1) := by
      calc ((2 - ε) * B) ^ 2 ≤ ((z : ℝ) - 1) * ((z : ℝ) - 1) := by
            nlinarith [hz1_lb, hzm1_nn]
        _ ≤ (z : ℝ) * ((z : ℝ) - 1) :=
            mul_le_mul_of_nonneg_right (by linarith) (le_trans hzm1_nn hz1_lb)
    have hcoeff : 2 - c₀ / 4 ≤ (2 - ε) ^ 2 / 2 := by
      dsimp [ε]; nlinarith [sq_nonneg c₀]
    nlinarith [sq_nonneg B]
  -- Express `n = 2^B`
  have hn_eq_2B : (n : ℝ) = (2 : ℝ) ^ B := by
    dsimp [B]
    unfold logBaseTwo
    rw [Real.rpow_def_of_pos two_pos]
    have hcancel : Real.log 2 * (Real.log (n : ℝ) / q) = Real.log (n : ℝ) := by
      unfold q; exact mul_div_cancel₀ _ (Real.log_pos one_lt_two).ne'
    rw [hcancel, Real.exp_log hn_pos]
  by_cases hk0 : k = 0
  · subst hk0; simp
  · have hk_le_2B : (k : ℝ) ≤ (2 : ℝ) ^ B := by
      rw [← hn_eq_2B]; exact_mod_cast hkn
    have hna_le : (n : ℝ) ^ ((1 - c₀) * (a : ℝ)) ≤
        (2 : ℝ) ^ ((1 - c₀) * (2 + ε) * B ^ 2) := by
      rw [hn_eq_2B, ← Real.rpow_mul two_pos.le]
      apply Real.rpow_le_rpow_of_exponent_le one_le_two
      have h1mc₀_nn : 0 ≤ 1 - c₀ := by linarith [hc₀.2]
      calc B * ((1 - c₀) * (a : ℝ))
          = (1 - c₀) * B * (a : ℝ) := by ring
        _ ≤ (1 - c₀) * B * ((2 + ε) * B) :=
            mul_le_mul_of_nonneg_left ha_ub (mul_nonneg h1mc₀_nn hB_pos.le)
        _ = (1 - c₀) * (2 + ε) * B ^ 2 := by ring
    have hz_pow_le : (2 : ℝ) ^ (-(z.choose 2 : ℝ)) ≤ (2 : ℝ) ^ (-((2 - c₀ / 4) * B ^ 2)) :=
      Real.rpow_le_rpow_of_exponent_le one_le_two (neg_le_neg hchoose_lb)
    have htot_exp : B + (1 - c₀) * (2 + ε) * B ^ 2 + -((2 - c₀ / 4) * B ^ 2) ≤ -1 := by
      have hcB : 4 ≤ c₀ * B := by rwa [div_le_iff₀ hc₀.1, mul_comm] at hB_c
      have hexp_alg :
          B + (1 - c₀) * (2 + ε) * B ^ 2 + -((2 - c₀ / 4) * B ^ 2) =
            B - (13 / 8) * (c₀ * B) * B - (c₀ ^ 2 / 8) * B ^ 2 := by
        dsimp [ε]; ring
      rw [hexp_alg]
      have hnn_c2 : 0 ≤ (c₀ ^ 2 / 8) * B ^ 2 := by positivity
      have hmB : 4 * B ≤ (c₀ * B) * B := mul_le_mul_of_nonneg_right hcB hB_pos.le
      linarith
    calc (k : ℝ) * (n : ℝ) ^ ((1 - c₀) * (a : ℝ)) * (2 : ℝ) ^ (-(z.choose 2 : ℝ))
        ≤ (2 : ℝ) ^ B * (2 : ℝ) ^ ((1 - c₀) * (2 + ε) * B ^ 2) *
            (2 : ℝ) ^ (-((2 - c₀ / 4) * B ^ 2)) := by
          refine mul_le_mul (mul_le_mul hk_le_2B hna_le (by positivity) (by positivity))
            hz_pow_le (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (B + (1 - c₀) * (2 + ε) * B ^ 2 + -((2 - c₀ / 4) * B ^ 2)) := by
          rw [← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
      _ ≤ (2 : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le one_le_two htot_exp
      _ = 1 / 2 := by norm_num

/-- **Proposition 7.3 complete three-range second-moment assembly & Paley–Zygmund bridge:**
combining the scrambled (`m_ν < n / (log n)³`), middle (`n / (log n)³ ≤ m_ν` and
`n^(1 - c₀) ≤ n - m_ν`), and similar (`n - m_ν < n^(1 - c₀)`) ranges with Lemma 7.2's
`exp(C_ov (log n)⁵)` kernel factor yields `E[Z²] ≤ exp(C_sm n^(1 - c₀) / log n) E[Z]²`,
and Paley–Zygmund yields `P(Z > 0) ≥ exp(-C_sm n^(1 - c₀) / log n)`. -/
theorem eventually_threeRange_secondMoment_and_paleyZygmund
    (M : ℕ) {c₀ : ℝ} (hc₀ : c₀ ∈ Set.Ioo (0 : ℝ) (1 / 4))
    (C_ov C_sim : ℝ) :
    ∃ C_sm : ℝ, 0 < C_sm ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (Z : LabeledGraph n → ℝ) (W_scr W_mid : ℝ) (k a z : ℕ),
        (∀ G, 0 ≤ Z G) →
        0 < (∫ G : LabeledGraph n, Z G ∂randomGraphMeasure n) →
        k ≤ n → a ≤ phaseNat n → phaseNat n - (3 * M + 4) ≤ z →
        W_scr ≤ Real.exp ((n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ)) →
        Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) * W_mid ≤ 1 →
        (∫ G : LabeledGraph n, (Z G) ^ 2 ∂randomGraphMeasure n) ≤
          (∫ G : LabeledGraph n, Z G ∂randomGraphMeasure n) ^ 2 *
            (2 * (Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) * W_scr +
                Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) * W_mid) +
              (2 : ℝ) ^ ((n : ℝ) ^ (1 - c₀) / ((phaseNat n - (M + 1) : ℕ) : ℝ)) *
                Real.exp (C_sim * (Real.log (n : ℝ)) ^ 5) *
                ∑ s ∈ Finset.range (k + 1),
                  ((k : ℝ) * (n : ℝ) ^ ((1 - c₀) * (a : ℝ)) *
                    (2 : ℝ) ^ (-(z.choose 2 : ℝ))) ^ s) →
        (∫ G : LabeledGraph n, (Z G) ^ 2 ∂randomGraphMeasure n) ≤
            Real.exp (C_sm * (n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ)) *
              (∫ G : LabeledGraph n, Z G ∂randomGraphMeasure n) ^ 2 ∧
          Real.exp (-C_sm * (n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ)) ≤
            (randomGraphMeasure n).real {G : LabeledGraph n | 0 < Z G} := by
  refine ⟨4, by norm_num, ?_⟩
  -- `(log n)^6 = o(n^(1 - c₀))`, so `(|C_ov| + |C_sim| + 4) * (log n)^5 ≤ n^(1 - c₀) / log n`
  have h1mc₀_pos : 0 < 1 - c₀ := by linarith [hc₀.2]
  have ho6 : (fun x : ℝ ↦ (Real.log x) ^ ((6 : ℕ) : ℝ)) =o[atTop] (fun x : ℝ ↦ x ^ (1 - c₀)) :=
    isLittleO_log_rpow_rpow_atTop ((6 : ℕ) : ℝ) h1mc₀_pos
  set c_eps : ℝ := 1 / (|C_ov| + |C_sim| + 4)
  have hc_eps_pos : 0 < c_eps := by dsimp [c_eps]; positivity
  have hb6 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Asymptotics.isLittleO_iff.mp ho6 hc_eps_pos)
  have hL_big : ∀ᶠ n : ℕ in atTop,
      2 * ((M + 1 : ℕ) : ℝ) + 4 ≤ logOrder n :=
    tendsto_logOrder_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_gt_atTop 3,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
    eventually_similarRange_geom_ratio_le_half M hc₀, hb6, hL_big] with
    n hn3 hPh hsim_half hb6_n hLn Z W_scr W_mid k a z hZ_nn hEZ_pos
    hkn ha_le hz_ge hW_scr hW_mid hEZ2_le
  set L : ℝ := Real.log (n : ℝ)
  unfold logOrder at hLn hPh
  have hL_ge4 : 4 ≤ L := by
    have : (0 : ℝ) ≤ 2 * ((M + 1 : ℕ) : ℝ) := by positivity
    linarith
  have hL_pos : 0 < L := by linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  -- Polylog bound `(|C_ov| + |C_sim| + 4) * L^5 ≤ n^(1 - c₀) / L`
  have hpoly_le : (|C_ov| + |C_sim| + 4) * L ^ 5 ≤ (n : ℝ) ^ (1 - c₀) / L := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hL_pos _),
      abs_of_pos (Real.rpow_pos_of_pos hn_pos _), Real.rpow_natCast] at hb6_n
    rw [le_div_iff₀ hL_pos]
    have hm := mul_le_mul_of_nonneg_left hb6_n
      (show (0 : ℝ) ≤ |C_ov| + |C_sim| + 4 by positivity)
    have hc : (|C_ov| + |C_sim| + 4) * (c_eps * (n : ℝ) ^ (1 - c₀)) = (n : ℝ) ^ (1 - c₀) := by
      dsimp [c_eps]; field_simp [(show (0 : ℝ) < |C_ov| + |C_sim| + 4 by positivity).ne']
    calc (|C_ov| + |C_sim| + 4) * L ^ 5 * L
        = (|C_ov| + |C_sim| + 4) * L ^ 6 := by ring
      _ ≤ (n : ℝ) ^ (1 - c₀) := by linarith
  -- Bound geometric sum in similar range by `2`
  have hgeom_sum_le2 :
      (∑ s ∈ Finset.range (k + 1),
        ((k : ℝ) * (n : ℝ) ^ ((1 - c₀) * (a : ℝ)) * (2 : ℝ) ^ (-(z.choose 2 : ℝ))) ^ s) ≤ 2 := by
    set r_q : ℝ := (k : ℝ) * (n : ℝ) ^ ((1 - c₀) * (a : ℝ)) * (2 : ℝ) ^ (-(z.choose 2 : ℝ))
    have hr_nn : 0 ≤ r_q := by dsimp [r_q]; positivity
    have hr_half : r_q ≤ 1 / 2 := hsim_half k a z hkn ha_le hz_ge
    calc ∑ s ∈ Finset.range (k + 1), r_q ^ s
        ≤ ∑ s ∈ Finset.range (k + 1), (1 / 2 : ℝ) ^ s :=
          Finset.sum_le_sum fun s _ ↦ pow_le_pow_left₀ hr_nn hr_half s
      _ = ((1 / 2 : ℝ) ^ (k + 1) - 1) / ((1 / 2 : ℝ) - 1) :=
          geom_sum_eq (by norm_num) (k + 1)
      _ = 2 - 2 * (1 / 2 : ℝ) ^ (k + 1) := by ring
      _ ≤ 2 := by linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (k + 1)]
  -- Bound `2 ^ (n^(1 - c₀) / (phaseNat n - (M + 1))) ≤ exp(2 * n^(1 - c₀) / L)`
  have h2pow_mark :
      (2 : ℝ) ^ ((n : ℝ) ^ (1 - c₀) / ((phaseNat n - (M + 1) : ℕ) : ℝ)) ≤
        Real.exp (2 * (n : ℝ) ^ (1 - c₀) / L) := by
    have hu_ge : L / 2 ≤ ((phaseNat n - (M + 1) : ℕ) : ℝ) := by
      have hle_nat : M + 1 ≤ phaseNat n := by
        have : ((M + 1 : ℕ) : ℝ) ≤ (phaseNat n : ℝ) := by linarith [hPh.1]
        exact_mod_cast this
      rw [Nat.cast_sub hle_nat]
      linarith [hPh.1]
    rw [Real.rpow_def_of_pos two_pos]
    apply Real.exp_le_exp.mpr
    have hdiv_le : (n : ℝ) ^ (1 - c₀) / ((phaseNat n - (M + 1) : ℕ) : ℝ) ≤
        2 * (n : ℝ) ^ (1 - c₀) / L := by
      have h1 : (n : ℝ) ^ (1 - c₀) / ((phaseNat n - (M + 1) : ℕ) : ℝ) ≤
          (n : ℝ) ^ (1 - c₀) / (L / 2) :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hn_pos.le _) (half_pos hL_pos) hu_ge
      exact h1.trans_eq (by ring)
    have hq_le1 : Real.log 2 ≤ 1 := le_trans Real.log_two_lt_d9.le (by norm_num)
    calc Real.log 2 * ((n : ℝ) ^ (1 - c₀) / ((phaseNat n - (M + 1) : ℕ) : ℝ))
        ≤ 1 * (2 * (n : ℝ) ^ (1 - c₀) / L) :=
          mul_le_mul hq_le1 hdiv_le (by positivity) zero_le_one
      _ = 2 * (n : ℝ) ^ (1 - c₀) / L := one_mul _
  -- Bound the total bracket by `exp(4 * n^(1 - c₀) / L)`
  set X_main : ℝ := (n : ℝ) ^ (1 - c₀) / L
  have hX_pos : 0 < X_main := div_pos (Real.rpow_pos_of_pos hn_pos _) hL_pos
  have hL5_ge1 : 1 ≤ L ^ 5 := one_le_pow₀ (by linarith)
  have hCov_le : C_ov * L ^ 5 + 2 ≤ X_main := by
    have h1 : C_ov * L ^ 5 ≤ |C_ov| * L ^ 5 :=
      mul_le_mul_of_nonneg_right (le_abs_self C_ov) (by positivity)
    have h2 : 0 ≤ |C_sim| * L ^ 5 := by positivity
    linarith [hpoly_le]
  have hCsim_le : C_sim * L ^ 5 + 2 ≤ X_main := by
    have h1 : C_sim * L ^ 5 ≤ |C_sim| * L ^ 5 :=
      mul_le_mul_of_nonneg_right (le_abs_self C_sim) (by positivity)
    have h2 : 0 ≤ |C_ov| * L ^ 5 := by positivity
    linarith [hpoly_le]
  have h4_le_exp2 : (4 : ℝ) ≤ Real.exp 2 := by
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) he1 2
      _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
  have hX1 : 4 ≤ X_main := by
    have h1 : 0 ≤ (|C_ov| + |C_sim|) * L ^ 5 := by positivity
    linarith [hpoly_le]
  have hterm1 :
      2 * (Real.exp (C_ov * L ^ 5) * W_scr + Real.exp (C_ov * L ^ 5) * W_mid) ≤
        (1 / 2 : ℝ) * Real.exp (4 * X_main) := by
    have hscr_le : Real.exp (C_ov * L ^ 5) * W_scr ≤ Real.exp (2 * X_main - 2) := by
      calc Real.exp (C_ov * L ^ 5) * W_scr
          ≤ Real.exp (C_ov * L ^ 5) * Real.exp X_main :=
            mul_le_mul_of_nonneg_left hW_scr (Real.exp_pos _).le
        _ = Real.exp (C_ov * L ^ 5 + X_main) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (2 * X_main - 2) := Real.exp_le_exp.mpr (by linarith)
    have hmid_le : Real.exp (C_ov * L ^ 5) * W_mid ≤ Real.exp (2 * X_main - 2) :=
      hW_mid.trans (Real.one_le_exp (by linarith))
    calc 2 * (Real.exp (C_ov * L ^ 5) * W_scr + Real.exp (C_ov * L ^ 5) * W_mid)
        ≤ 4 * Real.exp (2 * X_main - 2) := by linarith
      _ ≤ Real.exp 2 * Real.exp (2 * X_main - 2) :=
          mul_le_mul_of_nonneg_right h4_le_exp2 (Real.exp_pos _).le
      _ = Real.exp (2 * X_main) := by rw [← Real.exp_add]; congr 1; ring
      _ = 1 * Real.exp (2 * X_main) := (one_mul _).symm
      _ ≤ ((1 / 2 : ℝ) * Real.exp (2 * X_main)) * Real.exp (2 * X_main) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          have h2_le : (2 : ℝ) ≤ Real.exp (2 * X_main) :=
            le_trans (by linarith) (Real.add_one_le_exp (2 * X_main))
          linarith
      _ = (1 / 2 : ℝ) * Real.exp (4 * X_main) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hterm2 :
      (2 : ℝ) ^ ((n : ℝ) ^ (1 - c₀) / ((phaseNat n - (M + 1) : ℕ) : ℝ)) *
          Real.exp (C_sim * L ^ 5) *
          (∑ s ∈ Finset.range (k + 1),
            ((k : ℝ) * (n : ℝ) ^ ((1 - c₀) * (a : ℝ)) * (2 : ℝ) ^ (-(z.choose 2 : ℝ))) ^ s) ≤
        (1 / 2 : ℝ) * Real.exp (4 * X_main) := by
    have h2pow_mark' :
        (2 : ℝ) ^ ((n : ℝ) ^ (1 - c₀) / ((phaseNat n - (M + 1) : ℕ) : ℝ)) ≤
          Real.exp (2 * X_main) := by
      dsimp [X_main]; rwa [← mul_div_assoc]
    have hsum_nn : 0 ≤ ∑ s ∈ Finset.range (k + 1),
        ((k : ℝ) * (n : ℝ) ^ ((1 - c₀) * (a : ℝ)) * (2 : ℝ) ^ (-(z.choose 2 : ℝ))) ^ s :=
      Finset.sum_nonneg fun s _ ↦ by positivity
    calc _ ≤ Real.exp (2 * X_main) * Real.exp (C_sim * L ^ 5) * 2 := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right h2pow_mark' (Real.exp_pos _).le)
              hgeom_sum_le2 hsum_nn (by positivity)
      _ = (1 / 2 : ℝ) * (4 * Real.exp (2 * X_main + C_sim * L ^ 5)) := by
          rw [← Real.exp_add]; ring
      _ ≤ (1 / 2 : ℝ) * (Real.exp 2 * Real.exp (2 * X_main + C_sim * L ^ 5)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right h4_le_exp2 (Real.exp_pos _).le) (by norm_num)
      _ = (1 / 2 : ℝ) * Real.exp (2 * X_main + (C_sim * L ^ 5 + 2)) := by
          rw [← Real.exp_add]; congr 2; ring
      _ ≤ (1 / 2 : ℝ) * Real.exp (4 * X_main) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
          linarith [hX_pos, hCsim_le]
  have hsecond_bound :
      (∫ G : LabeledGraph n, (Z G) ^ 2 ∂randomGraphMeasure n) ≤
        Real.exp (4 * (n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ)) *
          (∫ G : LabeledGraph n, Z G ∂randomGraphMeasure n) ^ 2 := by
    have hbr :
        2 * (Real.exp (C_ov * L ^ 5) * W_scr + Real.exp (C_ov * L ^ 5) * W_mid) +
          (2 : ℝ) ^ ((n : ℝ) ^ (1 - c₀) / ((phaseNat n - (M + 1) : ℕ) : ℝ)) *
            Real.exp (C_sim * L ^ 5) *
            ∑ s ∈ Finset.range (k + 1),
              ((k : ℝ) * (n : ℝ) ^ ((1 - c₀) * (a : ℝ)) * (2 : ℝ) ^ (-(z.choose 2 : ℝ))) ^ s ≤
        Real.exp (4 * X_main) := by linarith
    calc (∫ G : LabeledGraph n, (Z G) ^ 2 ∂randomGraphMeasure n)
        ≤ (∫ G : LabeledGraph n, Z G ∂randomGraphMeasure n) ^ 2 * Real.exp (4 * X_main) :=
          hEZ2_le.trans (mul_le_mul_of_nonneg_left hbr (sq_nonneg _))
      _ = Real.exp (4 * (n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ)) *
            (∫ G : LabeledGraph n, Z G ∂randomGraphMeasure n) ^ 2 := by
          dsimp [X_main, L]; rw [mul_comm, mul_div_assoc]
  refine ⟨hsecond_bound, ?_⟩
  -- Paley–Zygmund via finite Cauchy–Schwarz on `S_pos := Finset.univ.filter (0 < Z ·)`
  classical
  let S_pos : Finset (LabeledGraph n) := Finset.univ.filter fun G ↦ 0 < Z G
  have hEZ_eq :
      (∫ G : LabeledGraph n, Z G ∂randomGraphMeasure n) =
        ∑ G ∈ S_pos, (randomGraphMeasure n).real {G} * Z G := by
    rw [integral_fintype Integrable.of_finite]
    simp_rw [smul_eq_mul]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun G : LabeledGraph n ↦ 0 < Z G)]
    have hz0 : ∑ G ∈ Finset.univ.filter (fun G : LabeledGraph n ↦ ¬ 0 < Z G),
        (randomGraphMeasure n).real {G} * Z G = 0 := by
      apply Finset.sum_eq_zero
      intro G hG
      have hle0 : Z G ≤ 0 := not_lt.mp (Finset.mem_filter.mp hG).2
      have heq0 : Z G = 0 := le_antisymm hle0 (hZ_nn G)
      rw [heq0, mul_zero]
    dsimp [S_pos]; linarith
  have hcs :
      (∫ G : LabeledGraph n, Z G ∂randomGraphMeasure n) ^ 2 ≤
        (randomGraphMeasure n).real {G : LabeledGraph n | 0 < Z G} *
          (∫ G : LabeledGraph n, (Z G) ^ 2 ∂randomGraphMeasure n) := by
    rw [hEZ_eq]
    have hsplit_term : ∀ G ∈ S_pos,
        (randomGraphMeasure n).real {G} * Z G =
          Real.sqrt ((randomGraphMeasure n).real {G}) *
            (Real.sqrt ((randomGraphMeasure n).real {G}) * Z G) := by
      intro G _
      rw [← mul_assoc, Real.mul_self_sqrt measureReal_nonneg]
    rw [Finset.sum_congr rfl hsplit_term]
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq S_pos
      (fun G ↦ Real.sqrt ((randomGraphMeasure n).real {G}))
      (fun G ↦ Real.sqrt ((randomGraphMeasure n).real {G}) * Z G)
    have hsq1 : ∑ G ∈ S_pos, (Real.sqrt ((randomGraphMeasure n).real {G})) ^ 2 =
        (randomGraphMeasure n).real {G : LabeledGraph n | 0 < Z G} := by
      have hs : ∑ G ∈ S_pos, (Real.sqrt ((randomGraphMeasure n).real {G})) ^ 2 =
          ∑ G ∈ S_pos, (randomGraphMeasure n).real {G} :=
        Finset.sum_congr rfl fun G _ ↦ Real.sq_sqrt measureReal_nonneg
      rw [hs]
      have hset : ({G : LabeledGraph n | 0 < Z G} : Set (LabeledGraph n)) = ↑S_pos := by
        ext G; simp [S_pos]
      rw [hset]
      have hind :
          (randomGraphMeasure n).real (↑S_pos : Set (LabeledGraph n)) =
            ∫ G : LabeledGraph n, (S_pos : Set (LabeledGraph n)).indicator (fun _ ↦ (1 : ℝ)) G
              ∂randomGraphMeasure n := by
        rw [integral_indicator_const _ (Set.toFinite _).measurableSet, smul_eq_mul, mul_one]
      rw [hind, integral_fintype Integrable.of_finite]
      simp_rw [smul_eq_mul]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun G ↦ G ∈ S_pos)]
      have h_in : ∑ x ∈ Finset.univ.filter (fun G ↦ G ∈ S_pos),
          (randomGraphMeasure n).real {x} *
            (S_pos : Set (LabeledGraph n)).indicator (fun _ ↦ (1 : ℝ)) x =
          ∑ x ∈ S_pos, (randomGraphMeasure n).real {x} := by
        have hf_eq : Finset.univ.filter (fun G ↦ G ∈ S_pos) = S_pos := by
          ext G; simp
        rw [hf_eq]
        exact Finset.sum_congr rfl fun G hG ↦ by
          rw [Set.indicator_of_mem (Finset.mem_coe.mpr hG), mul_one]
      have h_out : ∑ x ∈ Finset.univ.filter (fun G ↦ G ∉ S_pos),
          (randomGraphMeasure n).real {x} *
            (S_pos : Set (LabeledGraph n)).indicator (fun _ ↦ (1 : ℝ)) x = 0 := by
        apply Finset.sum_eq_zero
        intro G hG
        have hnG : G ∉ (S_pos : Set (LabeledGraph n)) :=
          Finset.mem_coe.not.mpr (Finset.mem_filter.mp hG).2
        rw [Set.indicator_of_notMem hnG, mul_zero]
      linarith
    have hsq2 : ∑ G ∈ S_pos, (Real.sqrt ((randomGraphMeasure n).real {G}) * Z G) ^ 2 ≤
        ∫ G : LabeledGraph n, (Z G) ^ 2 ∂randomGraphMeasure n := by
      rw [integral_fintype Integrable.of_finite]
      simp_rw [smul_eq_mul]
      have hs : ∑ G ∈ S_pos, (Real.sqrt ((randomGraphMeasure n).real {G}) * Z G) ^ 2 =
          ∑ G ∈ S_pos, (randomGraphMeasure n).real {G} * (Z G) ^ 2 :=
        Finset.sum_congr rfl fun G _ ↦ by
          rw [mul_pow, Real.sq_sqrt measureReal_nonneg]
      rw [hs]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S_pos)
        fun G _ _ ↦ mul_nonneg measureReal_nonneg (sq_nonneg _)
    calc _ ≤ (∑ G ∈ S_pos, (Real.sqrt ((randomGraphMeasure n).real {G})) ^ 2) *
            (∑ G ∈ S_pos, (Real.sqrt ((randomGraphMeasure n).real {G}) * Z G) ^ 2) := h1
      _ ≤ (randomGraphMeasure n).real {G : LabeledGraph n | 0 < Z G} *
            (∫ G : LabeledGraph n, (Z G) ^ 2 ∂randomGraphMeasure n) := by
          rw [hsq1]
          exact mul_le_mul_of_nonneg_left hsq2 measureReal_nonneg
  have hprob_mul :
      (∫ G : LabeledGraph n, Z G ∂randomGraphMeasure n) ^ 2 ≤
        (randomGraphMeasure n).real {G : LabeledGraph n | 0 < Z G} *
          (Real.exp (4 * (n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ)) *
            (∫ G : LabeledGraph n, Z G ∂randomGraphMeasure n) ^ 2) :=
    hcs.trans (mul_le_mul_of_nonneg_left hsecond_bound measureReal_nonneg)
  have hEZ2_pos : 0 < (∫ G : LabeledGraph n, Z G ∂randomGraphMeasure n) ^ 2 :=
    sq_pos_of_pos hEZ_pos
  have hcancel :
      1 ≤ Real.exp (4 * (n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ)) *
        (randomGraphMeasure n).real {G : LabeledGraph n | 0 < Z G} := by
    have hmul_eq :
        1 * (∫ G : LabeledGraph n, Z G ∂randomGraphMeasure n) ^ 2 ≤
          (Real.exp (4 * (n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ)) *
            (randomGraphMeasure n).real {G : LabeledGraph n | 0 < Z G}) *
            (∫ G : LabeledGraph n, Z G ∂randomGraphMeasure n) ^ 2 := by
      linarith
    exact le_of_mul_le_mul_right hmul_eq hEZ2_pos
  have hexp_neg :
      Real.exp (-4 * (n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ)) =
        (Real.exp (4 * (n : ℝ) ^ (1 - c₀) / Real.log (n : ℝ)))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [hexp_neg]
  exact (inv_le_iff_one_le_mul₀' (Real.exp_pos _)).mpr hcancel

/-!
## 5. Sharpened v10 Phase Refinement (fixed-corridor `(log n)⁶` tail) & `mainTheorem_v10_complete`
-/

/-- **Complete v10 Phase Refinement (unconditional `c₇, C₇` bounds + moving-corridor `(log n)⁸`
tail + fixed-corridor `2 exp(-ϑ² η₀² n / (2 (log n)⁶))` sub-Gaussian tail + a.s.):**
with `c₇ := (log 2)² / 4 · inf_{[δ_*, 1 + δ_*]} A₇` and `C₇ := (log 2)³ / 2 - c₇`:
1. unconditionally `0.080 < (log 2)² / 4 · log(391/200) < c₇` and
   `C₇ < (log 2)² / 4 · log(800/391) < 0.086`;
2. under the `O(quasiExpTail)` exit bound for `tildeEps = O(log log n / log n)`, `ε_n` satisfies
   `0 ≤ ε_n ≤ C₁ log log n / log n`, `P(W_n ∉ I_n) ≤ 2 exp(-n (log log n)² / (2 (log n)⁸))`
   eventually, and `E[W_n] ∈ I_n` eventually;
3. for every `c' < c₇`, `C' > C₇`, and `ϑ ∈ (0, 1)`, with `η₀ := min(c₇ - c', C' - C₇) > 0`,
   eventually `P(W_n ∉ [c', C']) ≤ 2 exp(-ϑ² η₀² n / (2 (log n)⁶))`, so
   `c' n / (log n)³ ≤ χ(G_n) - ζ(G_n) ≤ C' n / (log n)³` eventually in expectation and almost
   surely under every coupling of `(G_n)`. -/
theorem phaseRefinement_v10_complete
    (tildeEps : ℕ → ℝ)
    (htilde_nn : ∀ n, 0 ≤ tildeEps n)
    (htilde_O : tildeEps =O[atTop]
      (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)))
    (htail : (fun n : ℕ ↦ (randomGraphMeasure n).real
        (twoSidedGapEvent
          (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - tildeEps n)
          (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + tildeEps n) n)ᶜ)
      =O[atTop] quasiExpTail) :
    let c₇ : ℝ := (Real.log 2) ^ 2 / 4 * sInf (phaseGain7 '' Set.Icc deltaStar (1 + deltaStar))
    let C₇ : ℝ := (Real.log 2) ^ 3 / 2 - c₇
    let eps : ℕ → ℝ := fun n ↦
      if 3 ≤ n then tildeEps n + (1 + Real.log (Real.log (n : ℝ))) / Real.log (n : ℝ) else 0
    ((80 / 1000 : ℝ) < (Real.log 2) ^ 2 / 4 * Real.log (391 / 200) ∧
      (Real.log 2) ^ 2 / 4 * Real.log (391 / 200) < c₇ ∧
      C₇ < (Real.log 2) ^ 2 / 4 * Real.log (800 / 391) ∧
      (Real.log 2) ^ 2 / 4 * Real.log (800 / 391) < (86 / 1000 : ℝ)) ∧
    (∃ C₁ : ℝ, 0 < C₁ ∧ (∀ n, 0 ≤ eps n) ∧
      ∀ n ≥ 3, eps n ≤ C₁ * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) ∧
    (∀ᶠ n : ℕ in atTop,
      (randomGraphMeasure n).real
          (twoSidedGapEvent
            (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - eps n)
            (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + eps n) n)ᶜ ≤
        2 * Real.exp (-(n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2 /
          (2 * (Real.log (n : ℝ)) ^ 8))) ∧
    (∀ᶠ n : ℕ in atTop,
      lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - eps n ≤
          (Real.log (n : ℝ)) ^ 3 / (n : ℝ) *
            (∫ G : LabeledGraph n,
              ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
              ∂randomGraphMeasure n) ∧
        (Real.log (n : ℝ)) ^ 3 / (n : ℝ) *
            (∫ G : LabeledGraph n,
              ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
              ∂randomGraphMeasure n) ≤
          upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + eps n) ∧
    (∀ {c' C' ϑ : ℝ}, c' < c₇ → C₇ < C' → ϑ ∈ Set.Ioo (0 : ℝ) 1 →
      let η₀ : ℝ := min (c₇ - c') (C' - C₇)
      (∀ᶠ n : ℕ in atTop,
        (randomGraphMeasure n).real (twoSidedGapEvent c' C' n)ᶜ ≤
          2 * Real.exp (-ϑ ^ 2 * η₀ ^ 2 * (n : ℝ) / (2 * (Real.log (n : ℝ)) ^ 6))) ∧
      (∀ᶠ n : ℕ in atTop,
        c' * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3) ≤
            (∫ G : LabeledGraph n,
              ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
              ∂randomGraphMeasure n) ∧
          (∫ G : LabeledGraph n,
              ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
              ∂randomGraphMeasure n) ≤
            C' * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3)) ∧
      (∀ {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
        (G : ∀ n : ℕ, Ω → LabeledGraph n),
        (∀ n : ℕ, Measure.map (G n) ℙ = randomGraphMeasure n) →
        ∀ᵐ ω ∂ℙ, ∀ᶠ n : ℕ in atTop,
          c' * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3) ≤
              (chromaticNumberNat (G n ω) : ℝ) - (cochromaticNumber (G n ω) : ℝ) ∧
            (chromaticNumberNat (G n ω) : ℝ) - (cochromaticNumber (G n ω) : ℝ) ≤
              C' * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3))) := by
  intro c₇ C₇ eps
  have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hq24_pos : 0 < (Real.log 2) ^ 2 / 4 := by positivity
  -- 1. Unconditional bounds on `c₇` and `C₇`
  have hd_le : deltaStar ≤ 1 + deltaStar := by unfold deltaStar; norm_num
  have hsub_wide : Set.Icc deltaStar (1 + deltaStar) ⊆ Set.Icc (0 : ℝ) (207 / 200) := by
    intro d hd
    unfold deltaStar at hd
    exact ⟨by linarith [hd.1], by linarith [hd.2]⟩
  obtain ⟨y_min, hy_isLeast⟩ :=
    (isCompact_Icc.image_of_continuousOn (continuousOn_phaseGain7.mono hsub_wide)).exists_isLeast
      (Set.Nonempty.image _ (nonempty_Icc.mpr hd_le))
  rcases hy_isLeast.1 with ⟨d_min, hd_min, hd_eq⟩
  have hsInf_eq : sInf (phaseGain7 '' Set.Icc deltaStar (1 + deltaStar)) = phaseGain7 d_min :=
    hy_isLeast.csInf_eq.trans hd_eq.symm
  have hA7_gt : Real.log (391 / 200) < phaseGain7 d_min :=
    log_391_div_200_lt_phaseGain7 d_min (hsub_wide hd_min)
  have hc₇_gt_cert : (Real.log 2) ^ 2 / 4 * Real.log (391 / 200) < c₇ := by
    dsimp [c₇]; rw [hsInf_eq]
    exact mul_lt_mul_of_pos_left hA7_gt hq24_pos
  -- Numerical bounds `0.080 < (log 2)² / 4 · log(391/200)` and `(log 2)² / 4 · log(800/391) < 0.086`
  have hlog391_gt : (268155713 / 400000000 : ℝ) < Real.log (391 / 200) := log_391_div_200_gt
  have h080_lt : (80 / 1000 : ℝ) < (Real.log 2) ^ 2 / 4 * Real.log (391 / 200) := by
    have hq_lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hq_sq : (0.6931471803 : ℝ) ^ 2 / 4 < (Real.log 2) ^ 2 / 4 := by nlinarith
    have hm := mul_lt_mul'' hq_sq hlog391_gt (by norm_num) (by norm_num)
    exact lt_trans (by norm_num) hm
  have hlog_id :
      (Real.log 2) ^ 3 / 2 - (Real.log 2) ^ 2 / 4 * Real.log (391 / 200) =
        (Real.log 2) ^ 2 / 4 * Real.log (800 / 391) := by
    have h2log2 : 2 * Real.log 2 = Real.log 4 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
    have hsub_log : 2 * Real.log 2 - Real.log (391 / 200) = Real.log (800 / 391) := by
      rw [h2log2, ← Real.log_div (by norm_num) (by norm_num)]; norm_num
    calc (Real.log 2) ^ 3 / 2 - (Real.log 2) ^ 2 / 4 * Real.log (391 / 200)
        = (Real.log 2) ^ 2 / 4 * (2 * Real.log 2 - Real.log (391 / 200)) := by ring
      _ = (Real.log 2) ^ 2 / 4 * Real.log (800 / 391) := by rw [hsub_log]
  have hC₇_lt_cert : C₇ < (Real.log 2) ^ 2 / 4 * Real.log (800 / 391) := by
    dsimp [C₇]; linarith [hc₇_gt_cert, hlog_id]
  have h086_gt : (Real.log 2) ^ 2 / 4 * Real.log (800 / 391) < (86 / 1000 : ℝ) := by
    rw [← hlog_id, show (Real.log 2) ^ 3 / 2 - (Real.log 2) ^ 2 / 4 * Real.log (391 / 200) =
      (Real.log 2) ^ 2 / 4 * (2 * Real.log 2 - Real.log (391 / 200)) by ring]
    have hq_hi : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
    have hspan : 2 * Real.log 2 - Real.log (391 / 200) <
        2 * 0.6931471808 - 268155713 / 400000000 := by linarith
    have hq_sq : (Real.log 2) ^ 2 / 4 < (0.6931471808 : ℝ) ^ 2 / 4 := by nlinarith
    have hpos_span : 0 ≤ 2 * Real.log 2 - Real.log (391 / 200) := by
      have : Real.log (391 / 200) < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
      have h4 : 2 * Real.log 2 = Real.log 4 := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
      linarith
    have hm := mul_lt_mul'' hq_sq hspan hq24_pos.le hpos_span
    exact lt_trans hm (by norm_num)
  -- Pointwise bounds `c₇ ≤ lowerPhaseCoeff7(δ̃_n)` and `upperPhaseCoeff7(δ̃_n) ≤ C₇`
  have hshift_mem : ∀ n : ℕ, shiftedPhase (phaseDelta n) ∈ Set.Icc deltaStar (1 + deltaStar) :=
    fun n ↦ shiftedPhase_mem_Icc_deltaStar (phaseDelta_mem_Ico n)
  have hcoeff_bounds : ∀ n : ℕ,
      c₇ ≤ lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) ∧
        upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) ≤ C₇ := by
    intro n
    have hle_A7 : phaseGain7 d_min ≤ phaseGain7 (shiftedPhase (phaseDelta n)) :=
      hd_eq.trans_le (hy_isLeast.2 ⟨shiftedPhase (phaseDelta n), hshift_mem n, rfl⟩)
    have hlo : c₇ ≤ lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) := by
      dsimp [c₇]; rw [hsInf_eq]; unfold lowerPhaseCoeff7
      exact mul_le_mul_of_nonneg_left hle_A7 hq24_pos.le
    have hsum : lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) +
        upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) = (Real.log 2) ^ 3 / 2 := by
      unfold lowerPhaseCoeff7 upperPhaseCoeff7; ring
    exact ⟨hlo, by dsimp [C₇]; linarith⟩
  -- Apply `phaseRefinement_subgaussian_tail_expectation_and_ae`
  obtain ⟨h1_eps, h2_mov, h3_exp, -⟩ :=
    phaseRefinement_subgaussian_tail_expectation_and_ae.{0} tildeEps htilde_nn htilde_O htail
  refine ⟨⟨h080_lt, hc₇_gt_cert, hC₇_lt_cert, h086_gt⟩, h1_eps, h2_mov, h3_exp, ?_⟩
  -- 4. Fixed-corridor `(log n)⁶` sub-Gaussian tail + expectation + arbitrary-coupling a.s.
  intro c' C' ϑ hc' hC' hϑ η₀
  have hϑ_pos : 0 < ϑ := hϑ.1
  have hη₀_pos : 0 < η₀ := lt_min (by linarith) (by linarith)
  have hgap_pos : 0 < (1 - ϑ) * η₀ := mul_pos (by linarith [hϑ.2]) hη₀_pos
  -- `eps n → 0` since `eps n ≤ C₁ * log(log n) / log n`
  obtain ⟨C₁, hC₁_pos, heps_nn, heps_ub⟩ := h1_eps
  have heps_zero : Tendsto eps atTop (nhds 0) := by
    have hll_div : Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))
        atTop (nhds 0) :=
      logLogOrder_isLittleO_logOrder.tendsto_div_nhds_zero
    have hdom : Tendsto (fun n : ℕ ↦ C₁ * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))
        atTop (nhds 0) := by
      simpa [mul_div_assoc] using hll_div.const_mul C₁
    exact squeeze_zero' (Filter.Eventually.of_forall heps_nn)
      (by filter_upwards [eventually_ge_atTop 3] with n hn3; exact heps_ub n hn3) hdom
  have heps_small : ∀ᶠ n : ℕ in atTop, eps n ≤ (1 - ϑ) * η₀ := by
    filter_upwards [heps_zero.eventually (Iio_mem_nhds hgap_pos)] with n hn
    exact hn.le
  have htail_fixed :
      ∀ᶠ n : ℕ in atTop,
        (randomGraphMeasure n).real (twoSidedGapEvent c' C' n)ᶜ ≤
          2 * Real.exp (-ϑ ^ 2 * η₀ ^ 2 * (n : ℝ) / (2 * (Real.log (n : ℝ)) ^ 6)) := by
    filter_upwards [eventually_ge_atTop 3, h3_exp, heps_small] with n hn3 ⟨hmean_lo, hmean_hi⟩ heps_n
    have hn2 : 2 ≤ n := by omega
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hn1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
    have hn1_le : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
    set L : ℝ := Real.log (n : ℝ)
    have hL_pos : 0 < L := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    set D : LabeledGraph n → ℝ := fun G ↦ (chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)
    set meanD : ℝ := ∫ G : LabeledGraph n, D G ∂randomGraphMeasure n
    set t : ℝ := ϑ * η₀ * ((n : ℝ) / L ^ 3)
    have ht_nn : 0 ≤ t := by dsimp [t]; positivity
    obtain ⟨hc7_le, hC7_ge⟩ := hcoeff_bounds n
    have hη₀_c : η₀ ≤ c₇ - c' := min_le_left _ _
    have hη₀_C : η₀ ≤ C' - C₇ := min_le_right _ _
    have hmeanW_lo : c' + ϑ * η₀ ≤ L ^ 3 / (n : ℝ) * meanD := by
      dsimp [L, meanD, D] at hmean_lo ⊢
      linarith
    have hmeanW_hi : L ^ 3 / (n : ℝ) * meanD ≤ C' - ϑ * η₀ := by
      dsimp [L, meanD, D] at hmean_hi ⊢
      linarith
    have hsub : (twoSidedGapEvent c' C' n)ᶜ ⊆ {G : LabeledGraph n | t ≤ |D G - meanD|} := by
      intro G hGnot
      rw [Set.mem_setOf_eq]
      by_contra hlt_not
      obtain ⟨hd_lo, hd_hi⟩ := abs_lt.mp (not_le.mp hlt_not)
      apply hGnot
      unfold twoSidedGapEvent
      rw [Set.mem_setOf_eq]
      have hscale_pos : 0 < (n : ℝ) / L ^ 3 := by positivity
      have hm_lo := mul_le_mul_of_nonneg_right hmeanW_lo hscale_pos.le
      have hm_hi := mul_le_mul_of_nonneg_right hmeanW_hi hscale_pos.le
      have hcancel : L ^ 3 / (n : ℝ) * meanD * ((n : ℝ) / L ^ 3) = meanD := by
        field_simp [hn_pos.ne', hL_pos.ne']
      rw [hcancel, add_mul] at hm_lo
      rw [hcancel, sub_mul] at hm_hi
      dsimp [t, D, L] at hd_lo hd_hi hm_lo hm_hi ⊢
      exact ⟨by linarith, by linarith⟩
    have hconc := randomGraph_abs_chromaticSubCochromatic_sub_mean_ge_le hn2 ht_nn
    have hexp_le :
        Real.exp (-t ^ 2 / (2 * ((n - 1 : ℕ) : ℝ))) ≤
          Real.exp (-ϑ ^ 2 * η₀ ^ 2 * (n : ℝ) / (2 * L ^ 6)) := by
      apply Real.exp_le_exp.mpr
      have hden : t ^ 2 / (2 * (n : ℝ)) ≤ t ^ 2 / (2 * ((n - 1 : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
      have hid : t ^ 2 / (2 * (n : ℝ)) = ϑ ^ 2 * η₀ ^ 2 * (n : ℝ) / (2 * L ^ 6) := by
        dsimp [t]; field_simp [hn_pos.ne', hL_pos.ne']
      calc -t ^ 2 / (2 * ((n - 1 : ℕ) : ℝ))
          = -(t ^ 2 / (2 * ((n - 1 : ℕ) : ℝ))) := by ring
        _ ≤ -(t ^ 2 / (2 * (n : ℝ))) := neg_le_neg hden
        _ = -(ϑ ^ 2 * η₀ ^ 2 * (n : ℝ) / (2 * L ^ 6)) := by rw [hid]
        _ = -ϑ ^ 2 * η₀ ^ 2 * (n : ℝ) / (2 * L ^ 6) := by ring
    exact (measureReal_mono hsub).trans (hconc.trans (by linarith))
  have hexp_fixed :
      ∀ᶠ n : ℕ in atTop,
        c' * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3) ≤
            (∫ G : LabeledGraph n,
              ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
              ∂randomGraphMeasure n) ∧
          (∫ G : LabeledGraph n,
              ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
              ∂randomGraphMeasure n) ≤
            C' * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3) := by
    filter_upwards [eventually_ge_atTop 3, h3_exp, heps_small] with n hn3 ⟨hmean_lo, hmean_hi⟩ heps_n
    obtain ⟨hc7_le, hC7_ge⟩ := hcoeff_bounds n
    have hη₀_c : η₀ ≤ c₇ - c' := min_le_left _ _
    have hη₀_C : η₀ ≤ C' - C₇ := min_le_right _ _
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hL_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hscale_pos : 0 < (n : ℝ) / (Real.log (n : ℝ)) ^ 3 := by positivity
    have hϑη_nn : 0 ≤ ϑ * η₀ := mul_nonneg hϑ.1.le hη₀_pos.le
    have hw_lo : c' ≤ (Real.log (n : ℝ)) ^ 3 / (n : ℝ) *
        (∫ G : LabeledGraph n,
          ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) ∂randomGraphMeasure n) := by
      linarith
    have hw_hi : (Real.log (n : ℝ)) ^ 3 / (n : ℝ) *
        (∫ G : LabeledGraph n,
          ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) ∂randomGraphMeasure n) ≤ C' := by
      linarith
    have hm1 := mul_le_mul_of_nonneg_right hw_lo hscale_pos.le
    have hm2 := mul_le_mul_of_nonneg_right hw_hi hscale_pos.le
    have hcanc :
        (Real.log (n : ℝ)) ^ 3 / (n : ℝ) *
          (∫ G : LabeledGraph n,
            ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) ∂randomGraphMeasure n) *
          ((n : ℝ) / (Real.log (n : ℝ)) ^ 3) =
        ∫ G : LabeledGraph n,
          ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) ∂randomGraphMeasure n := by
      field_simp [hn_pos.ne', hL_pos.ne']
    exact ⟨by linarith, by linarith⟩
  -- Summability of `(randomGraphMeasure n).real (twoSidedGapEvent c' C' n)ᶜ` via `summable_subgaussianGapTail`
  have hsum_compl :
      Summable (fun n : ℕ ↦ (randomGraphMeasure n).real (twoSidedGapEvent c' C' n)ᶜ) := by
    set c_sg : ℝ := ϑ ^ 2 * η₀ ^ 2 / (2 * (Real.log 2) ^ 6)
    have hc_sg_pos : 0 < c_sg := by dsimp [c_sg]; positivity
    have hdom_sum :
        Summable (fun n : ℕ ↦ 2 * Real.exp (-c_sg * (n : ℝ) / (Real.logb 2 (n : ℝ)) ^ 6)) :=
      (summable_subgaussianGapTail hc_sg_pos).mul_left 2
    have hrew_dom : ∀ m : ℕ, 2 ≤ m →
        2 * Real.exp (-ϑ ^ 2 * η₀ ^ 2 * (m : ℝ) / (2 * (Real.log (m : ℝ)) ^ 6)) =
          2 * Real.exp (-c_sg * (m : ℝ) / (Real.logb 2 (m : ℝ)) ^ 6) := by
      intro m hm2
      have hL_pos : 0 < Real.log (m : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < m by omega))
      congr 2
      dsimp [c_sg]
      rw [Real.logb, div_pow]
      field_simp [hL_pos.ne', hq_pos.ne']
    obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (htail_fixed.and (eventually_ge_atTop 2))
    have hshift :
        Summable (fun k : ℕ ↦
          (randomGraphMeasure (k + N₀)).real (twoSidedGapEvent c' C' (k + N₀))ᶜ) := by
      refine Summable.of_nonneg_of_le (fun _ ↦ measureReal_nonneg) (fun k ↦ ?_)
        (hdom_sum.comp_injective (add_left_injective N₀))
      obtain ⟨ht_k, hn2_k⟩ := hN₀ (k + N₀) (Nat.le_add_left N₀ k)
      exact ht_k.trans_eq (hrew_dom (k + N₀) hn2_k)
    exact (summable_nat_add_iff N₀).mp hshift
  refine ⟨htail_fixed, hexp_fixed, fun ℙ _ G hMarg ↦ ?_⟩
  exact ae_eventually_twoSidedGap_of_summable_compl ℙ G hMarg hsum_compl

/-- **Complete v10 Main Theorem `(i)–(iv)` synthesis:**
from the finite-phase-cover `O_ε(exp(-2 n / (log n)^10))` bound, simultaneously establishes:
- `(i)` for all `n ≥ 2`, `u ≥ 0`, `λ ∈ ℝ`, `θ ∈ [0, 1/2)`, and `1 ≤ p < ∞`:
  * `Var(Δ(G_n)) ≤ n - 1`,
  * `0 ≤ log E[exp(λ Y_n)] - λ E[Y_n] ≤ λ² (log₂ n)⁶ / (2 n)`,
  * `P(|Y_n - E[Y_n]| ≥ u) ≤ 2 exp(-u² n / (2 (log₂ n)⁶))`,
  * `E[exp(θ (Δ(G_n) - E[Δ(G_n)])² / (n - 1))] ≤ (1 - 2θ)^(-1/2)` and
    `E[exp(θ n (Y_n - E[Y_n])² / (log₂ n)⁶)] ≤ (1 - 2θ)^(-1/2)`,
  * `E[|Δ(G_n) - E[Δ(G_n)]|^p] ≤ 2 ((p / e)(n - 1))^(p / 2)` and
    `E[|Y_n - E[Y_n]|^p] ≤ 2 (p (log₂ n)⁶ / (e n))^(p / 2)`;
- `(ii)` for each `ε > 0` and `ϑ ∈ (0, 1)`, eventually
  `P(|Y_n - 1/4| > ε) ≤ 2 exp(-ϑ² ε² n / (2 (log₂ n)⁶))`;
- `(iii)` under every joint coupling with `G(n, 1/2)` marginals, almost surely
  `Y_n → 1 / 4` and `((log n)³ / n) Δ(G_n) → (log 2)³ / 4`;
- `(iv)` `E[|Y_n - 1/4|^p] → 0` (`1 ≤ p < ∞`), `E[Y_n] → 1 / 4`, and for all `T ≥ 0`,
  `log E[exp(t Y_n)] → t / 4` and `E[exp(t Y_n)] → exp(t / 4)` uniformly on `[-T, T]`. -/
theorem mainTheorem_v10_complete
    (htail : ∀ eps : ℝ, 0 < eps →
      (fun n : ℕ ↦ (randomGraphMeasure n).real
        {G : LabeledGraph n |
          eps < |(Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
            ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) - 1 / 4|})
        =O[atTop] quasiExpTail) :
    let D : ∀ n : ℕ, LabeledGraph n → ℝ := fun _ G ↦
      (chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)
    let Y : ∀ n : ℕ, LabeledGraph n → ℝ := fun n G ↦
      (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) * D n G
    ((∀ n : ℕ,
        (∫ G : LabeledGraph n, (D n G - ∫ H, D n H ∂randomGraphMeasure n) ^ 2
          ∂randomGraphMeasure n) ≤ ((n - 1 : ℕ) : ℝ)) ∧
      (∀ {n : ℕ}, 2 ≤ n → ∀ lam : ℝ,
        0 ≤ Real.log (∫ G : LabeledGraph n, Real.exp (lam * Y n G) ∂randomGraphMeasure n) -
            lam * (∫ H : LabeledGraph n, Y n H ∂randomGraphMeasure n) ∧
          Real.log (∫ G : LabeledGraph n, Real.exp (lam * Y n G) ∂randomGraphMeasure n) -
            lam * (∫ H : LabeledGraph n, Y n H ∂randomGraphMeasure n) ≤
          lam ^ 2 * (Real.logb 2 (n : ℝ)) ^ 6 / (2 * (n : ℝ))) ∧
      (∀ {n : ℕ}, 2 ≤ n → ∀ {u : ℝ}, 0 ≤ u →
        (randomGraphMeasure n).real
            {G : LabeledGraph n | u ≤ |Y n G - ∫ H, Y n H ∂randomGraphMeasure n|} ≤
          2 * Real.exp (-u ^ 2 * (n : ℝ) / (2 * (Real.logb 2 (n : ℝ)) ^ 6))) ∧
      (∀ {n : ℕ}, 2 ≤ n → ∀ {θ : ℝ}, θ ∈ Set.Ico (0 : ℝ) (1 / 2) →
        (∫ G : LabeledGraph n,
            Real.exp (θ * (D n G - ∫ H, D n H ∂randomGraphMeasure n) ^ 2 / ((n - 1 : ℕ) : ℝ))
            ∂randomGraphMeasure n) ≤ (1 - 2 * θ) ^ (-(1 / 2 : ℝ)) ∧
        (∫ G : LabeledGraph n,
            Real.exp (θ * (n : ℝ) * (Y n G - ∫ H, Y n H ∂randomGraphMeasure n) ^ 2 /
              (Real.logb 2 (n : ℝ)) ^ 6)
            ∂randomGraphMeasure n) ≤ (1 - 2 * θ) ^ (-(1 / 2 : ℝ))) ∧
      (∀ {n : ℕ}, 2 ≤ n → ∀ {p : ℝ}, 1 ≤ p →
        (∫ G : LabeledGraph n, |D n G - ∫ H, D n H ∂randomGraphMeasure n| ^ p
          ∂randomGraphMeasure n) ≤
          2 * (p / Real.exp 1 * ((n - 1 : ℕ) : ℝ)) ^ (p / 2) ∧
        (∫ G : LabeledGraph n, |Y n G - ∫ H, Y n H ∂randomGraphMeasure n| ^ p
          ∂randomGraphMeasure n) ≤
          2 * (p * (Real.logb 2 (n : ℝ)) ^ 6 / (Real.exp 1 * (n : ℝ))) ^ (p / 2))) ∧
    (∀ {eps theta : ℝ}, 0 < eps → theta ∈ Ioo 0 1 →
      ∀ᶠ n : ℕ in atTop,
        (randomGraphMeasure n).real {G : LabeledGraph n | eps < |Y n G - 1 / 4|} ≤
          2 * Real.exp (-theta ^ 2 * eps ^ 2 * (n : ℝ) / (2 * (Real.logb 2 (n : ℝ)) ^ 6))) ∧
    (∀ {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
      (G : ∀ n : ℕ, Ω → LabeledGraph n),
      (∀ n : ℕ, Measure.map (G n) ℙ = randomGraphMeasure n) →
      ∀ᵐ ω ∂ℙ,
        Tendsto (fun n : ℕ ↦ (Real.log n) ^ 3 / (n : ℝ) * D n (G n ω))
          atTop (nhds sharpGapConstant) ∧
        Tendsto (fun n : ℕ ↦ Y n (G n ω)) atTop (nhds (1 / 4 : ℝ))) ∧
    ((∀ {p : ℝ}, 1 ≤ p →
        Tendsto (fun n : ℕ ↦ ∫ G : LabeledGraph n, |Y n G - 1 / 4| ^ p ∂randomGraphMeasure n)
          atTop (nhds 0)) ∧
      Tendsto (fun n : ℕ ↦
        (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
          ∫ G : LabeledGraph n, D n G ∂randomGraphMeasure n)
        atTop (nhds (1 / 4 : ℝ)) ∧
      (∀ {T : ℝ}, 0 ≤ T →
        TendstoUniformlyOn
          (fun n t ↦ Real.log (∫ G : LabeledGraph n, Real.exp (t * Y n G) ∂randomGraphMeasure n))
          (fun t ↦ t / 4) atTop (Set.Icc (-T) T) ∧
        TendstoUniformlyOn
          (fun n t ↦ ∫ G : LabeledGraph n, Real.exp (t * Y n G) ∂randomGraphMeasure n)
          (fun t ↦ Real.exp (t / 4)) atTop (Set.Icc (-T) T))) := by
  intro D Y
  obtain ⟨⟨hvar, hcgf, hmean_tail, hlp_central⟩, hsubg, hae, hconv⟩ :=
    mainTheorem_v9_complete htail
  exact ⟨⟨hvar, hcgf, hmean_tail,
    fun {_} hn {_} hθ ↦ ⟨sqExpMoment_chromaticSubCochromatic_le hn hθ,
      sqExpMoment_normalizedGap_le hn hθ⟩,
    hlp_central⟩, hsubg, hae, hconv⟩

end

end Erdos625HP
