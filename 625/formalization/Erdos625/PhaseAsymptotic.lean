import Erdos625.PhaseEstimates
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.Choose.Cast

/-!
# Endpoint-uniform phase asymptotics

This module assembles the finite falling-factorial and Robbins estimates into
the phase expansion of Lemma 2.1.  The first two sections keep explicit
finite remainders; the final section packages the resulting bounds on the
full sequence `n → ∞`.
-/

namespace Erdos625

open Filter Asymptotics Finset

/-- The main expression in (2.5), before its `O(1 / N)` remainder. -/
noncomputable def phaseStirlingMain (n s : ℕ) : ℝ :=
  (s : ℝ) *
      (logOrder n - Real.log (s : ℝ) + 1 - q / 2 * ((s : ℝ) - 1)) -
    (1 / 2 : ℝ) * Real.log (2 * Real.pi * s)

/-- Explicit finite form of (2.5).  The three terms on the right are,
respectively, the falling-factorial Taylor error, its linear correction, and
Robbins' factorial remainder. -/
theorem log_mu_sub_phaseStirlingMain_abs_le {n s : ℕ}
    (hs : 0 < s) (hn : 0 < n) (hTwo : 2 * s ≤ n) :
    |Real.log (mu n s) - phaseStirlingMain n s| ≤
      2 * (s : ℝ) ^ 3 / (n : ℝ) ^ 2 +
        (s.choose 2 : ℝ) / n + 1 / (12 * (s : ℝ)) := by
  have hsn : s ≤ n := by omega
  have hsReal : (0 : ℝ) < s := by exact_mod_cast hs
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hFactorial :
      Real.log (s.factorial : ℝ) =
        (s : ℝ) * Real.log (s : ℝ) - s +
          Real.log (s : ℝ) / 2 + Real.log (2 * Real.pi) / 2 +
            stirlingLogRemainder s := by
    simp only [stirlingLogRemainder]
    ring
  have hLogProduct :
      Real.log (2 * Real.pi * (s : ℝ)) =
        Real.log (2 * Real.pi) + Real.log (s : ℝ) := by
    rw [Real.log_mul (by positivity : (2 * Real.pi : ℝ) ≠ 0) hsReal.ne']
  have hChoose : (s.choose 2 : ℝ) = (s : ℝ) * ((s : ℝ) - 1) / 2 := by
    simpa using (Nat.cast_choose_two ℝ s :
      (s.choose 2 : ℝ) = (s : ℝ) * ((s : ℝ) - 1) / 2)
  let fallError : ℝ :=
    Real.log (n.descFactorial s : ℝ) -
      (s : ℝ) * Real.log (n : ℝ) + (s.choose 2 : ℝ) / n
  have hExact :
      Real.log (mu n s) - phaseStirlingMain n s =
        fallError - (s.choose 2 : ℝ) / n - stirlingLogRemainder s := by
    rw [log_mu_eq hsn, log_choose_eq_log_descFactorial_sub hsn, hFactorial]
    simp only [phaseStirlingMain, logOrder, fallError]
    rw [hLogProduct, hChoose]
    ring
  have hFall : |fallError| ≤ 2 * (s : ℝ) ^ 3 / (n : ℝ) ^ 2 := by
    simpa only [fallError] using log_descFactorial_linear_error_le hn hTwo
  have hChooseNonneg : 0 ≤ (s.choose 2 : ℝ) / n := by positivity
  have hRNonneg : 0 ≤ stirlingLogRemainder s := stirlingLogRemainder_nonneg hs
  rw [hExact]
  calc
    |fallError - (s.choose 2 : ℝ) / n - stirlingLogRemainder s| ≤
        |fallError| + |(s.choose 2 : ℝ) / n| + |stirlingLogRemainder s| := by
      calc
        |fallError - (s.choose 2 : ℝ) / n - stirlingLogRemainder s| =
            |fallError + (-(s.choose 2 : ℝ) / n) +
              (-stirlingLogRemainder s)| := congrArg abs (by ring)
        _ ≤ |fallError + (-(s.choose 2 : ℝ) / n)| +
              |-stirlingLogRemainder s| := abs_add_le _ _
        _ ≤ (|fallError| + |-(s.choose 2 : ℝ) / n|) +
              |-stirlingLogRemainder s| := by
            gcongr
            exact abs_add_le _ _
        _ = |fallError| + |(s.choose 2 : ℝ) / n| +
              |stirlingLogRemainder s| := by
            rw [show -(s.choose 2 : ℝ) / (n : ℝ) =
              -((s.choose 2 : ℝ) / n) by ring, abs_neg, abs_neg]
    _ = |fallError| + (s.choose 2 : ℝ) / n + stirlingLogRemainder s := by
      rw [abs_of_nonneg hChooseNonneg, abs_of_nonneg hRNonneg]
    _ ≤ 2 * (s : ℝ) ^ 3 / (n : ℝ) ^ 2 +
          (s.choose 2 : ℝ) / n + 1 / (12 * (s : ℝ)) := by
      gcongr
      exact stirlingLogRemainder_le hs

/-! ## The endpoint-uniform logarithmic expansion -/

/-- The bracket on the left-hand side of (2.6). -/
noncomputable def phaseBracket (n : ℕ) : ℝ :=
  logOrder n - Real.log (phaseNat n : ℝ) + 1 -
    q / 2 * ((phaseNat n : ℝ) - 1)

/-- The two displayed terms on the right-hand side of (2.6). -/
noncomputable def phaseBracketMain (n : ℕ) : ℝ :=
  q * phaseDelta n / 2 +
    (logLogOrder n - phaseC - phaseB n * q / 2) / logOrder n

/-- The relative perturbation in
`phaseNat = (2 N / q) * (1 + phaseRelativeShift)`. -/
noncomputable def phaseShiftNumerator (n : ℕ) : ℝ :=
  -logLogOrder n + phaseC + phaseB n * q / 2

noncomputable def phaseRelativeShift (n : ℕ) : ℝ :=
  phaseShiftNumerator n / logOrder n

/-- Exact factorization of the phase size around `2N/q`. -/
theorem phaseNat_cast_eq_base_mul_one_add_shift {n : ℕ}
    (hn : PhaseDomain n) (hN : 0 < logOrder n) :
    (phaseNat n : ℝ) =
      (2 * logOrder n / q) * (1 + phaseRelativeShift n) := by
  rw [phaseNat_cast_eq_two_phaseS_div_q_add_phaseB hn]
  simp only [phaseS, phaseRelativeShift, phaseShiftNumerator]
  field_simp [q_ne_zero, hN.ne']
  ring

private theorem log_phase_base {n : ℕ} (hN : 0 < logOrder n) :
    Real.log (2 * logOrder n / q) =
      q + logLogOrder n - Real.log q := by
  rw [Real.log_div (mul_ne_zero (by norm_num) hN.ne') q_ne_zero,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hN.ne']
  simp only [q, logLogOrder]

/-- Explicit, finite form of (2.6).  Its only smallness hypothesis is the
quantified Taylor domain for the displayed relative shift. -/
theorem phaseBracket_sub_main_abs_le {n : ℕ}
    (hn : PhaseDomain n) (hN : 0 < logOrder n)
    (hShift : |phaseRelativeShift n| ≤ 1 / 2) :
    |phaseBracket n - phaseBracketMain n| ≤
      2 * phaseRelativeShift n ^ 2 := by
  have hOneShift : 0 < 1 + phaseRelativeShift n := by
    have := (abs_le.mp hShift).1
    linarith
  have hBase : 0 < 2 * logOrder n / q := div_pos (mul_pos (by norm_num) hN) q_pos
  have hLogPhase :
      Real.log (phaseNat n : ℝ) =
        q + logLogOrder n - Real.log q +
          Real.log (1 + phaseRelativeShift n) := by
    rw [phaseNat_cast_eq_base_mul_one_add_shift hn hN,
      Real.log_mul hBase.ne' hOneShift.ne', log_phase_base hN]
  have hExact :
      phaseBracket n - phaseBracketMain n =
        -Real.log (1 + phaseRelativeShift n) + phaseRelativeShift n := by
    simp only [phaseBracket, phaseBracketMain]
    rw [hLogPhase, phaseNat_cast_eq_two_phaseS_div_q_add_phaseB hn]
    simp only [phaseRelativeShift, phaseShiftNumerator, phaseS, phaseC, phaseB]
    field_simp [hN.ne', q_ne_zero]
    ring
  have hTaylor := abs_neg_log_one_sub_sub_le
    (x := -phaseRelativeShift n) (by simpa using hShift)
  rw [hExact]
  simpa [sub_eq_add_neg] using hTaylor

/-- The relative shift tends to zero on the full sequence, so its Taylor
domain is eventually automatic. -/
theorem phaseRelativeShift_tendsto_zero :
    Tendsto phaseRelativeShift atTop (nhds 0) := by
  have hConst :
      (fun _n : ℕ ↦ phaseC) =o[atTop] logOrder := by
    simpa only [Function.comp_def, id_eq] using
      (isLittleO_const_id_atTop phaseC).comp_tendsto tendsto_logOrder_atTop
  have hB :
      (fun n : ℕ ↦ phaseB n * q / 2) =o[atTop] logOrder := by
    have h := phaseB_isLittleO_logOrder.const_mul_left (q / 2)
    exact h.congr_left fun n => by ring
  have hNumerator : phaseShiftNumerator =o[atTop] logOrder := by
    have h := logLogOrder_isLittleO_logOrder.neg_left.add hConst |>.add hB
    exact h.congr_left fun n => by simp [phaseShiftNumerator]
  change Tendsto (fun n => phaseShiftNumerator n / logOrder n) atTop (nhds 0)
  exact hNumerator.tendsto_div_nhds_zero

theorem eventually_phaseRelativeShift_abs_le_half :
    ∀ᶠ n : ℕ in atTop, |phaseRelativeShift n| ≤ 1 / 2 := by
  have hIoo : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ∈ nhds (0 : ℝ) :=
    Ioo_mem_nhds (by norm_num) (by norm_num)
  filter_upwards [phaseRelativeShift_tendsto_zero.eventually hIoo] with n hn
  exact (abs_le.mpr ⟨hn.1.le, hn.2.le⟩)

private theorem phaseB_isLittleO_logLogOrder :
    phaseB =o[atTop] logLogOrder := by
  have hBounded : phaseB =O[atTop] (fun _n : ℕ ↦ (1 : ℝ)) := by
    apply IsBigO.of_bound 1
    filter_upwards with n
    rw [Real.norm_eq_abs, abs_of_pos (phaseB_pos n), norm_one, one_mul]
    exact phaseB_le_one n
  have hOne : (fun _n : ℕ ↦ (1 : ℝ)) =o[atTop] logLogOrder := by
    simpa only [Function.comp_def, id_eq] using
      (isLittleO_const_id_atTop (1 : ℝ)).comp_tendsto tendsto_logLogOrder_atTop
  exact hBounded.trans_isLittleO hOne

private theorem phaseShiftNumerator_isBigO_logLogOrder :
    phaseShiftNumerator =O[atTop] logLogOrder := by
  have hConst : (fun _n : ℕ ↦ phaseC) =o[atTop] logLogOrder := by
    simpa only [Function.comp_def, id_eq] using
      (isLittleO_const_id_atTop phaseC).comp_tendsto tendsto_logLogOrder_atTop
  have hB : (fun n : ℕ ↦ phaseB n * q / 2) =o[atTop] logLogOrder := by
    have h := phaseB_isLittleO_logLogOrder.const_mul_left (q / 2)
    exact h.congr_left fun n => by ring
  have h := (Asymptotics.isBigO_refl logLogOrder atTop).neg_left.add hConst.isBigO |>.add hB.isBigO
  exact h.congr_left fun n => by simp [phaseShiftNumerator]

private theorem phaseRelativeShift_isBigO_logLog_div_log :
    phaseRelativeShift =O[atTop]
      (fun n : ℕ ↦ logLogOrder n / logOrder n) := by
  have hInv := Asymptotics.isBigO_refl (fun n : ℕ ↦ (logOrder n)⁻¹) atTop
  have h := phaseShiftNumerator_isBigO_logLogOrder.mul hInv
  exact h.congr_left (fun n => by simp [phaseRelativeShift, div_eq_mul_inv])
    |>.congr_right (fun n => by simp [div_eq_mul_inv])

/-- Filter form of (2.6), with the exact residual and the advertised
endpoint-uniform scale. -/
theorem phaseBracket_sub_main_isBigO :
    (fun n : ℕ ↦ phaseBracket n - phaseBracketMain n) =O[atTop]
      (fun n : ℕ ↦ logLogOrder n ^ 2 / logOrder n ^ 2) := by
  have hFinite : ∀ᶠ n : ℕ in atTop,
      |phaseBracket n - phaseBracketMain n| ≤ 2 * phaseRelativeShift n ^ 2 := by
    filter_upwards [eventually_phaseDomain,
      eventually_gt_atTop (1 : ℕ), eventually_phaseRelativeShift_abs_le_half] with n hn hnOne hShift
    have hN : 0 < logOrder n := Real.log_pos (by exact_mod_cast hnOne)
    exact phaseBracket_sub_main_abs_le hn hN hShift
  have hToShift :
      (fun n : ℕ ↦ phaseBracket n - phaseBracketMain n) =O[atTop]
        (fun n : ℕ ↦ phaseRelativeShift n ^ 2) := by
    apply IsBigO.of_bound 2
    filter_upwards [hFinite] with n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (phaseRelativeShift n))]
    exact hn
  have hShiftSq := phaseRelativeShift_isBigO_logLog_div_log.pow 2
  have hShiftSq' :
      (fun n : ℕ ↦ phaseRelativeShift n ^ 2) =O[atTop]
        (fun n : ℕ ↦ logLogOrder n ^ 2 / logOrder n ^ 2) :=
    hShiftSq.congr_right fun n => by simp [div_pow]
  exact hToShift.trans hShiftSq'

/-! ## Filter form of (2.5) -/

noncomputable def phaseStirlingResidual (n : ℕ) : ℝ :=
  Real.log (mu n (phaseNat n)) - phaseStirlingMain n (phaseNat n)

noncomputable def phaseFallingBound (n : ℕ) : ℝ :=
  2 * (phaseNat n : ℝ) ^ 3 / (n : ℝ) ^ 2

noncomputable def phaseChooseCorrection (n : ℕ) : ℝ :=
  (phaseNat n).choose 2 / (n : ℝ)

noncomputable def phaseRobbinsBound (n : ℕ) : ℝ :=
  1 / (12 * (phaseNat n : ℝ))

private theorem logOrder_pow_isLittleO_natCast (k : ℕ) :
    (fun n : ℕ ↦ logOrder n ^ k) =o[atTop] (fun n : ℕ ↦ (n : ℝ)) := by
  simpa only [logOrder, Function.comp_def, id_eq] using
    (Real.isLittleO_pow_log_id_atTop (n := k)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))

private theorem eventually_logOrder_pos :
    ∀ᶠ n : ℕ in atTop, 0 < logOrder n := by
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  exact Real.log_pos (by exact_mod_cast hn)

private theorem phaseFallingBound_isBigO_inv_logOrder :
    phaseFallingBound =O[atTop] (fun n : ℕ ↦ (logOrder n)⁻¹) := by
  have hPhaseCube := phaseNat_isTheta_logOrder.1.pow 3
  have hLogSqNat := (logOrder_pow_isLittleO_natCast 2).isBigO
  have hZero : ∀ᶠ n : ℕ in atTop,
      logOrder n ^ 2 = 0 → (n : ℝ) = 0 := by
    filter_upwards [eventually_logOrder_pos] with n hN hzero
    exact (pow_ne_zero 2 hN.ne' hzero).elim
  have hInv := hLogSqNat.inv_rev hZero |>.pow 2
  have hProduct := hPhaseCube.mul hInv |>.const_mul_left 2
  apply hProduct.congr'
  · filter_upwards with n
    simp only [phaseFallingBound, div_eq_mul_inv]
    ring
  · filter_upwards [eventually_logOrder_pos] with n hN
    field_simp [hN.ne']

private theorem phaseChooseCast_isBigO_phaseNat_sq :
    (fun n : ℕ ↦ ((phaseNat n).choose 2 : ℝ)) =O[atTop]
      (fun n : ℕ ↦ (phaseNat n : ℝ) ^ 2) := by
  apply IsBigO.of_bound 1
  filter_upwards with n
  have hsNonneg : (0 : ℝ) ≤ phaseNat n := Nat.cast_nonneg _
  have hChooseNonneg : (0 : ℝ) ≤ ((phaseNat n).choose 2 : ℝ) := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hChooseNonneg,
    abs_of_nonneg (sq_nonneg _), one_mul, Nat.cast_choose_two ℝ]
  nlinarith [sq_nonneg ((phaseNat n : ℝ) - 1)]

private theorem phaseChooseCorrection_isBigO_inv_logOrder :
    phaseChooseCorrection =O[atTop] (fun n : ℕ ↦ (logOrder n)⁻¹) := by
  have hChooseLogSq := phaseChooseCast_isBigO_phaseNat_sq.trans
    (phaseNat_isTheta_logOrder.1.pow 2)
  have hLogCubeNat := (logOrder_pow_isLittleO_natCast 3).isBigO
  have hZero : ∀ᶠ n : ℕ in atTop,
      logOrder n ^ 3 = 0 → (n : ℝ) = 0 := by
    filter_upwards [eventually_logOrder_pos] with n hN hzero
    exact (pow_ne_zero 3 hN.ne' hzero).elim
  have hInv := hLogCubeNat.inv_rev hZero
  have hProduct := hChooseLogSq.mul hInv
  apply hProduct.congr'
  · filter_upwards with n
    simp [phaseChooseCorrection, div_eq_mul_inv]
  · filter_upwards [eventually_logOrder_pos] with n hN
    field_simp [hN.ne']

private theorem phaseRobbinsBound_isBigO_inv_logOrder :
    phaseRobbinsBound =O[atTop] (fun n : ℕ ↦ (logOrder n)⁻¹) := by
  have hZero : ∀ᶠ n : ℕ in atTop,
      logOrder n = 0 → (phaseNat n : ℝ) = 0 := by
    filter_upwards [eventually_logOrder_pos] with n hN hzero
    exact (hN.ne' hzero).elim
  have hInv := phaseNat_isTheta_logOrder.2.inv_rev hZero
  have hScaled := hInv.const_mul_left (1 / 12 : ℝ)
  exact hScaled.congr_left fun n => by simp [phaseRobbinsBound, div_eq_mul_inv]; ring

/-- Equation (2.5) on the full sequence: its exact residual is
`O(1 / log n)`. -/
theorem phaseStirlingResidual_isBigO_inv_logOrder :
    phaseStirlingResidual =O[atTop] (fun n : ℕ ↦ (logOrder n)⁻¹) := by
  have hFinite : ∀ᶠ n : ℕ in atTop,
      |phaseStirlingResidual n| ≤
        phaseFallingBound n + phaseChooseCorrection n + phaseRobbinsBound n := by
    filter_upwards [eventually_two_le_phaseNat, eventually_gt_atTop (1 : ℕ),
      eventually_two_mul_phaseNat_le] with n hs hn hTwo
    have hnPos : 0 < n := by omega
    simpa only [phaseStirlingResidual, phaseFallingBound, phaseChooseCorrection,
      phaseRobbinsBound] using
      log_mu_sub_phaseStirlingMain_abs_le (show 0 < phaseNat n by omega) hnPos hTwo
  have hResidualToBounds : phaseStirlingResidual =O[atTop]
      (fun n : ℕ ↦ phaseFallingBound n + phaseChooseCorrection n + phaseRobbinsBound n) := by
    apply IsBigO.of_bound 1
    filter_upwards [hFinite] with n hn
    have hFallNonneg : 0 ≤ phaseFallingBound n := by simp [phaseFallingBound]; positivity
    have hChooseNonneg : 0 ≤ phaseChooseCorrection n := by
      simp [phaseChooseCorrection]
      positivity
    have hRobbinsNonneg : 0 ≤ phaseRobbinsBound n := by simp [phaseRobbinsBound]
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (add_nonneg hFallNonneg hChooseNonneg) hRobbinsNonneg), one_mul]
    exact hn
  have hBounds := phaseFallingBound_isBigO_inv_logOrder.add
    phaseChooseCorrection_isBigO_inv_logOrder |>.add
      phaseRobbinsBound_isBigO_inv_logOrder
  exact hResidualToBounds.trans hBounds

/-! ## Assembly of (2.2) -/

/-- The displayed main term in (2.2). -/
noncomputable def phaseExpansionMain (n : ℕ) : ℝ :=
  phaseDelta n * (logOrder n - logLogOrder n) +
    (2 / q - 1 / 2) * logLogOrder n + phaseK (phaseDelta n)

/-- The purely algebraic remainder left after substituting the main part of
(2.6) into the main part of (2.5). -/
noncomputable def phaseAlgebraRemainder (n : ℕ) : ℝ :=
  -(2 / q) * (-logLogOrder n + phaseC) * phaseShiftNumerator n / logOrder n -
    phaseB n * phaseShiftNumerator n / logOrder n -
      (1 / 2 : ℝ) * Real.log (1 + phaseRelativeShift n)

private theorem log_phaseNat_eq_base_add_log_shift {n : ℕ}
    (hn : PhaseDomain n) (hN : 0 < logOrder n)
    (hShift : |phaseRelativeShift n| ≤ 1 / 2) :
    Real.log (phaseNat n : ℝ) =
      q + logLogOrder n - Real.log q +
        Real.log (1 + phaseRelativeShift n) := by
  have hOneShift : 0 < 1 + phaseRelativeShift n := by
    have := (abs_le.mp hShift).1
    linarith
  have hBase : 0 < 2 * logOrder n / q := div_pos (mul_pos (by norm_num) hN) q_pos
  rw [phaseNat_cast_eq_base_mul_one_add_shift hn hN,
    Real.log_mul hBase.ne' hOneShift.ne', log_phase_base hN]

/-- Exact endpoint algebra behind the constant `phaseK`. -/
theorem phaseMain_algebra_identity {n : ℕ}
    (hn : PhaseDomain n) (hN : 0 < logOrder n)
    (hShift : |phaseRelativeShift n| ≤ 1 / 2) :
    (phaseNat n : ℝ) * phaseBracketMain n -
        (1 / 2 : ℝ) * Real.log (2 * Real.pi * phaseNat n) -
          phaseExpansionMain n = phaseAlgebraRemainder n := by
  have hOneShift : 0 < 1 + phaseRelativeShift n := by
    have := (abs_le.mp hShift).1
    linarith
  have hBase : 0 < 2 * logOrder n / q := div_pos (mul_pos (by norm_num) hN) q_pos
  have hsPos : (0 : ℝ) < phaseNat n := by
    rw [phaseNat_cast_eq_base_mul_one_add_shift hn hN]
    positivity
  have hLogNat := log_phaseNat_eq_base_add_log_shift hn hN hShift
  have hLogProduct :
      Real.log (2 * Real.pi * (phaseNat n : ℝ)) =
        Real.log (2 * Real.pi) + Real.log (phaseNat n : ℝ) := by
    rw [Real.log_mul (by positivity : (2 * Real.pi : ℝ) ≠ 0) hsPos.ne']
  rw [hLogProduct, hLogNat, phaseNat_cast_eq_two_phaseS_div_q_add_phaseB hn]
  simp only [phaseBracketMain, phaseExpansionMain, phaseAlgebraRemainder,
    phaseRelativeShift, phaseShiftNumerator, phaseS, phaseK, phaseC, phaseB]
  field_simp [hN.ne', q_ne_zero]
  ring

private theorem abs_log_one_add_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |Real.log (1 + x)| ≤ 2 * |x| := by
  have hTaylor := abs_neg_log_one_sub_sub_le (x := -x) (by simpa using hx)
  have hTriangle :
      |Real.log (1 + x)| ≤ |-Real.log (1 + x) + x| + |x| := by
    calc
      |Real.log (1 + x)| = |-(-Real.log (1 + x) + x) + x| := by
        congr 1
        ring
      _ ≤ |-Real.log (1 + x) + x| + |x| := by
        simpa only [abs_neg] using
          (abs_add_le (-(-Real.log (1 + x) + x)) x)
  calc
    |Real.log (1 + x)| ≤ |-Real.log (1 + x) + x| + |x| := hTriangle
    _ ≤ 2 * x ^ 2 + |x| := by
      gcongr
      simpa [sub_eq_add_neg] using hTaylor
    _ ≤ 2 * |x| := by
      have hxNonneg : 0 ≤ |x| := abs_nonneg x
      have hxSq : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      rw [hxSq]
      nlinarith

private theorem neg_logLog_add_phaseC_isBigO_logLogOrder :
    (fun n : ℕ ↦ -logLogOrder n + phaseC) =O[atTop] logLogOrder := by
  have hConst : (fun _n : ℕ ↦ phaseC) =o[atTop] logLogOrder := by
    simpa only [Function.comp_def, id_eq] using
      (isLittleO_const_id_atTop phaseC).comp_tendsto tendsto_logLogOrder_atTop
  exact (Asymptotics.isBigO_refl logLogOrder atTop).neg_left.add hConst.isBigO

private theorem algebraQuadraticTerm_isBigO :
    (fun n : ℕ ↦
      -(2 / q) * (-logLogOrder n + phaseC) * phaseShiftNumerator n / logOrder n)
      =O[atTop] (fun n : ℕ ↦ logLogOrder n ^ 2 / logOrder n) := by
  have hInv := Asymptotics.isBigO_refl (fun n : ℕ ↦ (logOrder n)⁻¹) atTop
  have h := neg_logLog_add_phaseC_isBigO_logLogOrder.mul
    phaseShiftNumerator_isBigO_logLogOrder |>.mul hInv |>.const_mul_left (-(2 / q))
  apply h.congr'
  · filter_upwards with n
    simp only [div_eq_mul_inv]
    ring
  · filter_upwards with n
    rw [div_eq_mul_inv, pow_two]

private theorem algebraBoundedTerm_isBigO :
    (fun n : ℕ ↦ -phaseB n * phaseShiftNumerator n / logOrder n)
      =O[atTop] (fun n : ℕ ↦ logLogOrder n ^ 2 / logOrder n) := by
  have hInv := Asymptotics.isBigO_refl (fun n : ℕ ↦ (logOrder n)⁻¹) atTop
  have h := phaseB_isLittleO_logLogOrder.isBigO.mul
    phaseShiftNumerator_isBigO_logLogOrder |>.mul hInv |>.neg_left
  apply h.congr'
  · filter_upwards with n
    simp [div_eq_mul_inv]
  · filter_upwards with n
    rw [div_eq_mul_inv, pow_two]

private theorem logLog_div_log_isBigO_sq_div_log :
    (fun n : ℕ ↦ logLogOrder n / logOrder n) =O[atTop]
      (fun n : ℕ ↦ logLogOrder n ^ 2 / logOrder n) := by
  have hOne : (fun _n : ℕ ↦ (1 : ℝ)) =O[atTop] logLogOrder := by
    apply IsBigO.of_bound 1
    have hEventually : ∀ᶠ n : ℕ in atTop, 1 ≤ logLogOrder n :=
      tendsto_logLogOrder_atTop.eventually (eventually_ge_atTop (1 : ℝ))
    filter_upwards [hEventually] with n hn
    rw [norm_one, Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one hn), one_mul]
    exact hn
  have h := hOne.mul
    (Asymptotics.isBigO_refl (fun n : ℕ ↦ logLogOrder n / logOrder n) atTop)
  apply h.congr'
  · filter_upwards with n
    simp
  · filter_upwards with n
    simp [div_eq_mul_inv]
    ring

private theorem algebraLogTerm_isBigO :
    (fun n : ℕ ↦ -(1 / 2 : ℝ) * Real.log (1 + phaseRelativeShift n))
      =O[atTop] (fun n : ℕ ↦ logLogOrder n ^ 2 / logOrder n) := by
  have hLogShift :
      (fun n : ℕ ↦ Real.log (1 + phaseRelativeShift n)) =O[atTop]
        phaseRelativeShift := by
    apply IsBigO.of_bound 2
    filter_upwards [eventually_phaseRelativeShift_abs_le_half] with n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, two_mul]
    exact (abs_log_one_add_le hn).trans_eq (two_mul _)
  exact (hLogShift.trans phaseRelativeShift_isBigO_logLog_div_log |>.trans
    logLog_div_log_isBigO_sq_div_log).const_mul_left (-(1 / 2 : ℝ))

private theorem phaseAlgebraRemainder_isBigO :
    phaseAlgebraRemainder =O[atTop]
      (fun n : ℕ ↦ logLogOrder n ^ 2 / logOrder n) := by
  have h := algebraQuadraticTerm_isBigO.add algebraBoundedTerm_isBigO |>.add
    algebraLogTerm_isBigO
  exact h.congr_left fun n => by simp [phaseAlgebraRemainder]; ring

noncomputable def phaseExpansionResidual (n : ℕ) : ℝ :=
  Real.log (mu n (phaseNat n)) - phaseExpansionMain n

private theorem inv_logOrder_isBigO_sq_logLog_div_logOrder :
    (fun n : ℕ ↦ (logOrder n)⁻¹) =O[atTop]
      (fun n : ℕ ↦ logLogOrder n ^ 2 / logOrder n) := by
  have hOne : (fun _n : ℕ ↦ (1 : ℝ)) =O[atTop]
      (fun n : ℕ ↦ logLogOrder n ^ 2) := by
    apply IsBigO.of_bound 1
    have hEventually : ∀ᶠ n : ℕ in atTop, 1 ≤ logLogOrder n :=
      tendsto_logLogOrder_atTop.eventually (eventually_ge_atTop (1 : ℝ))
    filter_upwards [hEventually] with n hn
    rw [norm_one, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), one_mul]
    nlinarith
  have h := hOne.mul
    (Asymptotics.isBigO_refl (fun n : ℕ ↦ (logOrder n)⁻¹) atTop)
  apply h.congr'
  · filter_upwards with n
    simp
  · filter_upwards with n
    simp [div_eq_mul_inv]

private theorem phaseTimesBracketResidual_isBigO :
    (fun n : ℕ ↦ (phaseNat n : ℝ) *
      (phaseBracket n - phaseBracketMain n)) =O[atTop]
        (fun n : ℕ ↦ logLogOrder n ^ 2 / logOrder n) := by
  have h := phaseNat_isTheta_logOrder.1.mul phaseBracket_sub_main_isBigO
  apply h.congr' Filter.EventuallyEq.rfl
  filter_upwards [eventually_logOrder_pos] with n hN
  field_simp [hN.ne']

/-- Lemma 2.1 / equation (2.2) on the full sequence, uniformly through the
floor phase: the exact residual is `O(w²/N)`. -/
theorem phaseExpansionResidual_isBigO :
    phaseExpansionResidual =O[atTop]
      (fun n : ℕ ↦ logLogOrder n ^ 2 / logOrder n) := by
  have hDecomposition : ∀ᶠ n : ℕ in atTop,
      phaseExpansionResidual n =
        phaseStirlingResidual n +
          (phaseNat n : ℝ) * (phaseBracket n - phaseBracketMain n) +
            phaseAlgebraRemainder n := by
    filter_upwards [eventually_phaseDomain, eventually_logOrder_pos,
      eventually_phaseRelativeShift_abs_le_half] with n hn hN hShift
    have hAlg := phaseMain_algebra_identity hn hN hShift
    calc
      phaseExpansionResidual n =
          phaseStirlingResidual n +
            (phaseNat n : ℝ) * (phaseBracket n - phaseBracketMain n) +
              ((phaseNat n : ℝ) * phaseBracketMain n -
                (1 / 2 : ℝ) * Real.log (2 * Real.pi * phaseNat n) -
                  phaseExpansionMain n) := by
            simp only [phaseExpansionResidual, phaseStirlingResidual,
              phaseStirlingMain, phaseBracket]
            ring
      _ = phaseStirlingResidual n +
            (phaseNat n : ℝ) * (phaseBracket n - phaseBracketMain n) +
              phaseAlgebraRemainder n := by rw [hAlg]
  have hStirling := phaseStirlingResidual_isBigO_inv_logOrder.trans
    inv_logOrder_isBigO_sq_logLog_div_logOrder
  have hSum := hStirling.add phaseTimesBracketResidual_isBigO |>.add
    phaseAlgebraRemainder_isBigO
  apply hSum.congr'
  · exact Filter.EventuallyEq.symm hDecomposition
  · exact Filter.EventuallyEq.rfl

end Erdos625
