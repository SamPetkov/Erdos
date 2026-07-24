import Erdos625.PhaseRootScalarBound
import Erdos625.PhaseRootAlgebraicCoreBound
import Erdos625.PhaseRootExpansionResidualBound
import Erdos625.PhaseRootScalarResidualRemainderBound
import Erdos625.PhaseRootStirlingResidualBound
import Mathlib.Tactic

namespace Erdos625

open Filter Asymptotics

noncomputable section

set_option autoImplicit false

/-! ### Auxiliary asymptotic facts

We establish that `phaseRootScalarTerm` has an exact leading term
`(2 / q - 1 / 2) * logLogOrder` with a little-o remainder.  The upper Θ-bound
`phaseRootScalarTerm =O logLogOrder` is already available as
`phaseRootScalarTerm_isBigO_logLogOrder`; the content here is the matching lower
bound, which follows once the nonzero leading coefficient is identified.
-/

/-- The leading coefficient `2 / q - 1 / 2` is positive (`q = log 2 < 2`). -/
private theorem cLead_pos : 0 < 2 / q - 1 / 2 := by
  have hqUpper : q < 2 := Real.log_two_lt_d9.trans (by norm_num)
  have h : (1 : ℝ) < 2 / q := by
    rw [lt_div_iff₀ q_pos]; linarith
  linarith

/-- A constant is little-o of `logLogOrder` because the latter tends to `+∞`. -/
private theorem one_isLittleO_logLogOrder :
    (fun _n : ℕ ↦ (1 : ℝ)) =o[atTop] logLogOrder := by
  rw [Asymptotics.isLittleO_const_left]
  refine Or.inr ?_
  have h : Tendsto (fun n : ℕ ↦ |logLogOrder n|) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ le_abs_self _) tendsto_logLogOrder_atTop
  simpa [Real.norm_eq_abs, Function.comp_def] using h

/-- `logLogOrder ^ 2 / logOrder` is little-o of `logLogOrder`, since the ratio
`logLogOrder / logOrder` tends to `0`. -/
private theorem logLogOrderSq_div_logOrder_isLittleO :
    (fun n : ℕ ↦ logLogOrder n ^ 2 / logOrder n) =o[atTop] logLogOrder := by
  have hratio : (fun n : ℕ ↦ logLogOrder n / logOrder n) =o[atTop]
      (fun _n : ℕ ↦ (1 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).mpr
      logLogOrder_isLittleO_logOrder.tendsto_div_nhds_zero
  have h := (Asymptotics.isBigO_refl logLogOrder atTop).mul_isLittleO hratio
  refine h.congr' ?_ ?_
  · filter_upwards with n; ring
  · filter_upwards with n; ring

private theorem phaseExpansionResidual_isLittleO_logLogOrder :
    phaseExpansionResidual =o[atTop] logLogOrder :=
  phaseExpansionResidual_isBigO.trans_isLittleO logLogOrderSq_div_logOrder_isLittleO

private theorem phaseStirlingResidual_isLittleO_logLogOrder :
    phaseStirlingResidual =o[atTop] logLogOrder := by
  refine phaseStirlingResidual_isBigO_inv_logOrder.trans_isLittleO ?_
  refine ((Asymptotics.isLittleO_one_iff ℝ).mpr ?_).trans one_isLittleO_logLogOrder
  exact tendsto_inv_atTop_zero.comp tendsto_logOrder_atTop

private theorem stirlingLogRemainder_phaseNat_isLittleO_logLogOrder :
    (fun n : ℕ ↦ stirlingLogRemainder (phaseNat n)) =o[atTop] logLogOrder := by
  have hBig : (fun n : ℕ ↦ stirlingLogRemainder (phaseNat n)) =O[atTop]
      (fun _n : ℕ ↦ (1 : ℝ)) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_two_le_phaseNat] with n hn
    have hpos : 0 < phaseNat n := by omega
    have hnonneg := stirlingLogRemainder_nonneg hpos
    have hle := stirlingLogRemainder_le hpos
    have hphase : (2 : ℝ) ≤ phaseNat n := by exact_mod_cast hn
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, norm_one, mul_one]
    have : 1 / (12 * (phaseNat n : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    linarith
  exact hBig.trans_isLittleO one_isLittleO_logLogOrder

private theorem residualSum_isLittleO_logLogOrder :
    (fun n : ℕ ↦
        phaseExpansionResidual n - phaseStirlingResidual n -
          stirlingLogRemainder (phaseNat n))
      =o[atTop] logLogOrder :=
  (phaseExpansionResidual_isLittleO_logLogOrder.sub
      phaseStirlingResidual_isLittleO_logLogOrder).sub
    stirlingLogRemainder_phaseNat_isLittleO_logLogOrder

/-- `log 4 ≤ 2`. -/
private theorem log_four_le_two : Real.log 4 ≤ 2 := by
  calc
    Real.log 4 ≤ Real.log (Real.exp 2) :=
      Real.log_le_log (by norm_num)
        (by rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
            nlinarith [Real.exp_one_gt_two])
    _ = 2 := Real.log_exp 2

/-- `log (phaseNat n) - logLogOrder n` is bounded, since
`logOrder n ≤ phaseNat n ≤ 4 logOrder n`. -/
private theorem log_phaseNat_sub_logLogOrder_isBigO_one :
    (fun n : ℕ ↦ Real.log (phaseNat n : ℝ) - logLogOrder n)
      =O[atTop] (fun _n : ℕ ↦ (1 : ℝ)) := by
  apply IsBigO.of_bound 2
  filter_upwards [eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
    tendsto_logOrder_atTop.eventually_gt_atTop (1 : ℝ)] with n hp hN
  have hlogpos : 0 < logOrder n := lt_trans one_pos hN
  have hphasepos : 0 < (phaseNat n : ℝ) := lt_of_lt_of_le hlogpos hp.1
  have hlow : logLogOrder n ≤ Real.log (phaseNat n : ℝ) := by
    have := Real.log_le_log hlogpos hp.1
    simpa [logLogOrder] using this
  have hhigh : Real.log (phaseNat n : ℝ) ≤ logLogOrder n + Real.log 4 := by
    have h1 := Real.log_le_log hphasepos hp.2
    rw [Real.log_mul (by norm_num) hlogpos.ne'] at h1
    simp only [logLogOrder]; linarith
  rw [Real.norm_eq_abs, norm_one, mul_one, abs_le]
  exact ⟨by linarith, by linarith [log_four_le_two]⟩

/-- `(logOrder n - log (phaseRootCenter n)) - logLogOrder n` is bounded.  Here
`logOrder n - log (phaseRootCenter n) = log (phaseRootS0 n)`, and
`phaseRootS0 n` is comparable to `logOrder n`. -/
private theorem logOrder_sub_logCenter_sub_logLogOrder_isBigO_one :
    (fun n : ℕ ↦
        (logOrder n - Real.log (phaseRootCenter n)) - logLogOrder n)
      =O[atTop] (fun _n : ℕ ↦ (1 : ℝ)) := by
  apply IsBigO.of_bound 2
  filter_upwards [eventually_phaseRoot_domain_pos_and_target_corridor,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
    tendsto_logOrder_atTop.eventually_gt_atTop (10 : ℝ),
    eventually_gt_atTop (0 : ℕ)] with n hdom hp hN hnpos
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hnpos.ne'
  have hs0pos : 0 < phaseRootS0 n := hdom.2.1
  have hs0ne : phaseRootS0 n ≠ 0 := hs0pos.ne'
  have hlogpos : 0 < logOrder n := lt_trans (by norm_num) hN
  have hcenter : Real.log (phaseRootCenter n) =
      Real.log (n : ℝ) - Real.log (phaseRootS0 n) := by
    rw [phaseRootCenter, Real.log_div hn0 hs0ne]
  have hkey : (logOrder n - Real.log (phaseRootCenter n)) - logLogOrder n =
      Real.log (phaseRootS0 n) - logLogOrder n := by
    rw [hcenter, logOrder]; ring
  rw [hkey]
  -- Bounds on `phaseRootS0 n`.
  have hqU : q < 2 := Real.log_two_lt_d9.trans (by norm_num)
  have hqL : (1 / 2 : ℝ) < q :=
    (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
  have h2qU : 2 / q < 4 := by rw [div_lt_iff₀ q_pos]; linarith
  have h2qL : (1 : ℝ) < 2 / q := by rw [lt_div_iff₀ q_pos]; linarith
  have hs0eq : phaseRootS0 n = (phaseNat n : ℝ) + phaseDelta n - 1 - 2 / q := by
    rw [phaseRootS0, alphaZero_eq_phaseNat_add_delta hdom.1]
  have hs0U : phaseRootS0 n ≤ 4 * logOrder n := by
    rw [hs0eq]; nlinarith [hp.2, phaseDelta_lt_one n, h2qL]
  have hs0L : logOrder n / 2 ≤ phaseRootS0 n := by
    rw [hs0eq]; nlinarith [hp.1, phaseDelta_nonneg n, h2qU, hN]
  have hup : Real.log (phaseRootS0 n) ≤ logLogOrder n + Real.log 4 := by
    have := Real.log_le_log hs0pos hs0U
    rw [Real.log_mul (by norm_num) hlogpos.ne'] at this
    simp only [logLogOrder]; linarith
  have hlow : logLogOrder n - Real.log 2 ≤ Real.log (phaseRootS0 n) := by
    have hpos2 : 0 < logOrder n / 2 := by linarith
    have := Real.log_le_log hpos2 hs0L
    rw [Real.log_div hlogpos.ne' (by norm_num)] at this
    simp only [logLogOrder]; linarith
  have hlog2 : Real.log 2 ≤ 2 := by
    have := Real.log_two_lt_d9; linarith
  rw [Real.norm_eq_abs, norm_one, mul_one, abs_le]
  exact ⟨by linarith, by linarith [log_four_le_two]⟩

/-- The exact expansion of `phaseRootAlgebraicNoLog n - logOrder n`.
(Extracted verbatim from the proof of
`phaseRootAlgebraicNoLog_sub_logOrder_isBigO`.) -/
private theorem phaseRootAlgebraicNoLog_sub_logOrder_eq :
    ∀ᶠ n : ℕ in atTop,
      phaseRootAlgebraicNoLog n - logOrder n =
        (1 + 2 / q - phaseDelta n) * Real.log (phaseNat n : ℝ) +
        (phaseDelta n - 5 / 2) * logLogOrder n +
        phaseK (phaseDelta n) +
        (1 + 2 / q - phaseDelta n) *
          (2 * phaseC + q / 2 - q * phaseDelta n) -
        (2 * phaseC / q + phaseB n) - phaseDelta n + 2 + 2 / q := by
  filter_upwards [eventually_phaseDomain] with n hn
  have hpre : phaseRootAlgebraicNoLog n - logOrder n =
      (1 + 2 / q - phaseDelta n) * Real.log (phaseNat n : ℝ) +
      phaseK (phaseDelta n) + (2 / q - 1 / 2) * logLogOrder n +
      (1 + 2 / q - phaseDelta n) *
        (q * (phaseNat n : ℝ) - q / 2 - logOrder n) +
      phaseDelta n * (logOrder n - logLogOrder n) -
      ((phaseNat n : ℝ) + phaseDelta n - 1 - 2 / q) + 1 - logOrder n := by
    unfold phaseRootAlgebraicNoLog
    rw [show phaseRootDeficitTarget n = 1 + 2 / q - phaseDelta n by
      exact phaseRoot_target_identity hn]
    rw [show phaseRootS0 n =
        (phaseNat n : ℝ) + phaseDelta n - 1 - 2 / q by
      unfold phaseRootS0
      rw [alphaZero_eq_phaseNat_add_delta hn]]
    unfold phaseExpansionMain profileDeficitAffineB
    ring
  rw [hpre]
  have hp : (phaseNat n : ℝ) * q =
      2 * logOrder n - 2 * logLogOrder n + 2 * phaseC + q * phaseB n := by
    rw [phaseNat_cast_eq_two_phaseS_div_q_add_phaseB hn]
    unfold phaseS
    field_simp [q_ne_zero]
  rw [show phaseB n = 1 - phaseDelta n from rfl] at hp ⊢
  field_simp [q_ne_zero] at hp ⊢
  linear_combination (2 * q - 2 * q * phaseDelta n + 2) * hp

/-- The bounded remainder of the algebraic-core expansion.
(Extracted verbatim from the proof of
`phaseRootAlgebraicNoLog_sub_logOrder_isBigO`.) -/
private theorem algebraicCore_remainder_isBigO_one :
    (fun n : ℕ ↦
        phaseK (phaseDelta n) +
        (1 + 2 / q - phaseDelta n) *
          (2 * phaseC + q / 2 - q * phaseDelta n) -
        (2 * phaseC / q + phaseB n) - phaseDelta n + 2 + 2 / q)
      =O[atTop] (fun _n : ℕ ↦ (1 : ℝ)) := by
  have hDelta : (fun n : ℕ ↦ phaseDelta n) =O[atTop] (fun _n : ℕ ↦ (1 : ℝ)) := by
    apply IsBigO.of_bound 1
    filter_upwards with n
    rw [Real.norm_eq_abs, abs_of_nonneg (phaseDelta_nonneg n), norm_one, one_mul]
    exact (phaseDelta_lt_one n).le
  have hB : phaseB =O[atTop] (fun _n : ℕ ↦ (1 : ℝ)) := by
    apply IsBigO.of_bound 1
    filter_upwards with n
    rw [Real.norm_eq_abs, abs_of_nonneg (phaseB_pos n).le, norm_one, one_mul]
    exact phaseB_le_one n
  have hK : (fun n : ℕ ↦ phaseK (phaseDelta n)) =O[atTop]
      (fun _n : ℕ ↦ (1 : ℝ)) := by
    obtain ⟨M, hM⟩ := exists_phaseK_abs_bound
    apply IsBigO.of_bound M
    filter_upwards with n
    rw [Real.norm_eq_abs, norm_one, mul_one]
    exact hM _ ⟨phaseDelta_nonneg n, (phaseDelta_lt_one n).le⟩
  have hCoeff : (fun n : ℕ ↦ 1 + 2 / q - phaseDelta n) =O[atTop]
      (fun _n : ℕ ↦ (1 : ℝ)) := by
    simpa using ((Asymptotics.isBigO_refl (fun _n : ℕ ↦ (1 : ℝ)) atTop).const_mul_left
      (1 + 2 / q)).sub hDelta
  have hInner : (fun n : ℕ ↦ 2 * phaseC + q / 2 - q * phaseDelta n) =O[atTop]
      (fun _n : ℕ ↦ (1 : ℝ)) := by
    simpa using ((Asymptotics.isBigO_refl (fun _n : ℕ ↦ (1 : ℝ)) atTop).const_mul_left
      (2 * phaseC + q / 2)).sub (hDelta.const_mul_left q)
  have hConst (c : ℝ) : (fun _n : ℕ ↦ c) =O[atTop] (fun _n : ℕ ↦ (1 : ℝ)) := by
    simpa using (Asymptotics.isBigO_refl (fun _n : ℕ ↦ (1 : ℝ)) atTop).const_mul_left c
  have hProduct : (fun n : ℕ ↦ (1 + 2 / q - phaseDelta n) *
      (2 * phaseC + q / 2 - q * phaseDelta n)) =O[atTop]
      (fun _n : ℕ ↦ (1 : ℝ)) := by
    simpa using hCoeff.mul hInner
  have h := hK.add hProduct |>.sub ((hConst (2 * phaseC / q)).add hB)
    |>.sub hDelta |>.add (hConst 2) |>.add (hConst (2 / q))
  simpa only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply] using h

/-- The algebraic core, once the leading `(2 / q - 1 / 2) * logLogOrder` term is
removed, is bounded (`O(1)`).  This is where the delta-independent leading
coefficient is pinned down. -/
private theorem algebraicCore_sub_lead_isBigO_one :
    (fun n : ℕ ↦
        phaseRootAlgebraicCore n - (2 / q - 1 / 2) * logLogOrder n)
      =O[atTop] (fun _n : ℕ ↦ (1 : ℝ)) := by
  have hident : ∀ᶠ n : ℕ in atTop,
      phaseRootAlgebraicCore n - (2 / q - 1 / 2) * logLogOrder n =
        (1 + 2 / q - phaseDelta n) * (Real.log (phaseNat n : ℝ) - logLogOrder n)
        + ((logOrder n - Real.log (phaseRootCenter n)) - logLogOrder n)
        + (phaseK (phaseDelta n) +
            (1 + 2 / q - phaseDelta n) *
              (2 * phaseC + q / 2 - q * phaseDelta n) -
            (2 * phaseC / q + phaseB n) - phaseDelta n + 2 + 2 / q) := by
    filter_upwards [phaseRootAlgebraicNoLog_sub_logOrder_eq] with n hn
    rw [phaseRootAlgebraicCore_eq n, hn]
    ring
  have hCoeff : (fun n : ℕ ↦ 1 + 2 / q - phaseDelta n) =O[atTop]
      (fun _n : ℕ ↦ (1 : ℝ)) := by
    have hDelta : (fun n : ℕ ↦ phaseDelta n) =O[atTop] (fun _n : ℕ ↦ (1 : ℝ)) := by
      apply IsBigO.of_bound 1
      filter_upwards with n
      rw [Real.norm_eq_abs, abs_of_nonneg (phaseDelta_nonneg n), norm_one, one_mul]
      exact (phaseDelta_lt_one n).le
    simpa using ((Asymptotics.isBigO_refl (fun _n : ℕ ↦ (1 : ℝ)) atTop).const_mul_left
      (1 + 2 / q)).sub hDelta
  have hT1 : (fun n : ℕ ↦
      (1 + 2 / q - phaseDelta n) * (Real.log (phaseNat n : ℝ) - logLogOrder n))
      =O[atTop] (fun _n : ℕ ↦ (1 : ℝ)) := by
    simpa using hCoeff.mul log_phaseNat_sub_logLogOrder_isBigO_one
  have hSum :=
    (hT1.add logOrder_sub_logCenter_sub_logLogOrder_isBigO_one).add
      algebraicCore_remainder_isBigO_one
  refine hSum.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hident] with n hn
  simpa using hn.symm

/-- `phaseRootScalarTerm` minus its exact leading term is little-o of
`logLogOrder`. -/
private theorem phaseRootScalarTerm_sub_lead_isLittleO :
    (fun n : ℕ ↦
        phaseRootScalarTerm n - (2 / q - 1 / 2) * logLogOrder n)
      =o[atTop] logLogOrder := by
  have hSplit : ∀ᶠ n : ℕ in atTop,
      phaseRootScalarTerm n - (2 / q - 1 / 2) * logLogOrder n =
        (phaseRootAlgebraicCore n - (2 / q - 1 / 2) * logLogOrder n)
        + (phaseExpansionResidual n - phaseStirlingResidual n -
            stirlingLogRemainder (phaseNat n)) := by
    filter_upwards [eventually_phaseRoot_domain_pos_and_target_corridor,
      eventually_two_le_phaseNat] with n hdom hphase
    have hcore := phaseRootScalarTerm_eq_core hdom.1 hdom.2.1 (by omega)
    rw [hcore]; ring
  have h1 :=
    algebraicCore_sub_lead_isBigO_one.trans_isLittleO one_isLittleO_logLogOrder
  have h2 := residualSum_isLittleO_logLogOrder
  refine (h1.add h2).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hSplit] with n hn
  simpa using hn.symm

/-- The matching lower Θ-bound: `logLogOrder =O phaseRootScalarTerm`. -/
private theorem logLogOrder_isBigO_phaseRootScalarTerm :
    logLogOrder =O[atTop] phaseRootScalarTerm := by
  have hc : 0 < 2 / q - 1 / 2 := cLead_pos
  have hb := phaseRootScalarTerm_sub_lead_isLittleO.bound
    (by linarith : (0 : ℝ) < (2 / q - 1 / 2) / 2)
  apply IsBigO.of_bound (2 / (2 / q - 1 / 2))
  filter_upwards [hb, tendsto_logLogOrder_atTop.eventually_ge_atTop (0 : ℝ)]
    with n hbn hgn
  have hnormg : ‖logLogOrder n‖ = logLogOrder n := by
    rw [Real.norm_eq_abs, abs_of_nonneg hgn]
  rw [hnormg] at hbn
  rw [Real.norm_eq_abs, abs_le] at hbn
  have hSpos : 0 ≤ phaseRootScalarTerm n := by
    nlinarith [hbn.1, hgn, hc, mul_nonneg hc.le hgn]
  have hnormS : ‖phaseRootScalarTerm n‖ = phaseRootScalarTerm n := by
    rw [Real.norm_eq_abs, abs_of_nonneg hSpos]
  rw [hnormg, hnormS]
  rw [show (2 / (2 / q - 1 / 2)) * phaseRootScalarTerm n =
      2 * phaseRootScalarTerm n / (2 / q - 1 / 2) by ring]
  rw [le_div_iff₀ hc]
  nlinarith [hbn.1, hgn]

/--
The scalar term at the present reference center has the exact logarithmic-logarithmic
scale.  Establishing this determines whether the current center can support the
claimed root-displacement scale.
-/
theorem phaseRootScalarTerm_isTheta_logLogOrder :
    phaseRootScalarTerm =Θ[atTop] logLogOrder :=
  ⟨phaseRootScalarTerm_isBigO_logLogOrder, logLogOrder_isBigO_phaseRootScalarTerm⟩

end

end Erdos625
