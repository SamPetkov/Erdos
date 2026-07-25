import Erdos625.Section9ProfileAttachmentMatchingEnvelope
import Erdos625.Section9PhaseTwoPowerCorridor
import Erdos625.Section9ResidualRegimeScaleAdapters
import Erdos625.Section9ERealENNRealExpTransport

/-!
# Section IX: direct matching-restriction profile log scale

This module specializes the direct attained-profile attachment envelope to the
large-residual midpoint scale.  The new finite exponent

`kappaLambda * U^4 / m + kappaQ * U^2`

is uniformly `O((log n)^2)` when `U <= phaseNat n` and
`m >= n / (log n)^6`.  No type-cardinality, matching-cardinality, or traversal
parameter remains.

The theorem is still pointwise in an attained canonical skeleton.  It does not
sum the Section VIII skeleton weights or prove the final random-graph event.
-/

namespace Erdos625

open Filter
open scoped ENNReal Topology

noncomputable section

set_option autoImplicit false

/-- Exact real arithmetic for the direct matching-restriction exponent. -/
theorem matchingRestrictionEnvelope_bound
    (n L U m kappaLambda kappaQ C_U : ℝ)
    (hn : 0 < n)
    (hL : 0 < L)
    (hU0 : 0 ≤ U)
    (hm0 : 0 < m)
    (hkappaLambda0 : 0 ≤ kappaLambda)
    (hkappaQ0 : 0 ≤ kappaQ)
    (_hCU0 : 0 ≤ C_U)
    (hm : n / L ^ 6 ≤ m)
    (hU : U ≤ C_U * L)
    (hL8 : L ^ 8 ≤ n) :
    kappaLambda * U ^ 4 / m + kappaQ * U ^ 2 ≤
      (kappaLambda * C_U ^ 4 + kappaQ * C_U ^ 2) * L ^ 2 := by
  have hn_le_mL6 : n ≤ m * L ^ 6 := by
    rwa [div_le_iff₀ (pow_pos hL 6)] at hm
  have h1m_le_L6n : 1 / m ≤ L ^ 6 / n := by
    rw [div_le_div_iff₀ hm0 hn]
    simpa [mul_comm] using hn_le_mL6
  have hU4 : U ^ 4 ≤ (C_U * L) ^ 4 :=
    pow_le_pow_left₀ hU0 hU 4
  have hL10_div_n_le_L2 : L ^ 10 / n ≤ L ^ 2 := by
    rw [div_le_iff₀ hn]
    calc
      L ^ 10 = L ^ 2 * L ^ 8 := by ring
      _ ≤ L ^ 2 * n :=
        mul_le_mul_of_nonneg_left hL8 (by positivity)
  have hterm1Base : U ^ 4 / m ≤ C_U ^ 4 * L ^ 2 := by
    calc
      U ^ 4 / m = U ^ 4 * (1 / m) := by ring
      _ ≤ (C_U * L) ^ 4 * (L ^ 6 / n) :=
        mul_le_mul hU4 h1m_le_L6n (by positivity) (by positivity)
      _ = C_U ^ 4 * (L ^ 10 / n) := by ring
      _ ≤ C_U ^ 4 * L ^ 2 :=
        mul_le_mul_of_nonneg_left hL10_div_n_le_L2 (by positivity)
  have hterm1 : kappaLambda * U ^ 4 / m ≤
      kappaLambda * C_U ^ 4 * L ^ 2 := by
    calc
      kappaLambda * U ^ 4 / m = kappaLambda * (U ^ 4 / m) := by ring
      _ ≤ kappaLambda * (C_U ^ 4 * L ^ 2) :=
        mul_le_mul_of_nonneg_left hterm1Base hkappaLambda0
      _ = kappaLambda * C_U ^ 4 * L ^ 2 := by ring
  have hU2 : U ^ 2 ≤ (C_U * L) ^ 2 :=
    pow_le_pow_left₀ hU0 hU 2
  have hterm2 : kappaQ * U ^ 2 ≤
      kappaQ * C_U ^ 2 * L ^ 2 := by
    calc
      kappaQ * U ^ 2 ≤ kappaQ * (C_U * L) ^ 2 :=
        mul_le_mul_of_nonneg_left hU2 hkappaQ0
      _ = kappaQ * C_U ^ 2 * L ^ 2 := by ring
  calc
    kappaLambda * U ^ 4 / m + kappaQ * U ^ 2 ≤
        kappaLambda * C_U ^ 4 * L ^ 2 +
          kappaQ * C_U ^ 2 * L ^ 2 := add_le_add hterm1 hterm2
    _ = (kappaLambda * C_U ^ 4 + kappaQ * C_U ^ 2) * L ^ 2 := by
      ring

/-- Eventually `(log n)^8 <= n`, in the exact form used by the direct
large-residual envelope. -/
theorem eventually_log_pow_eight_le_nat :
    ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ^ 8 ≤ (n : ℝ) := by
  have hlim : Tendsto
      (fun n : ℕ => Real.log (n : ℝ) ^ 8 / (n : ℝ)) atTop (nhds 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (gt_mem_nhds zero_lt_one),
    eventually_gt_atTop 0] with n hn hn0
  rw [div_lt_one (by positivity)] at hn
  linarith

/-- The finite direct exponent is finite whenever its constants are finite and
its residual mass is positive. -/
theorem matchingRestrictionEnvelope_ne_top
    (kappaLambda kappaQ : ENNReal) (U m : ℕ)
    (hkappaLambdaTop : kappaLambda ≠ ∞)
    (hkappaQTop : kappaQ ≠ ∞)
    (hm : 0 < m) :
    (kappaLambda * (U : ENNReal) ^ 4 / (m : ENNReal) +
      kappaQ * (U : ENNReal) ^ 2) ≠ ∞ := by
  have hUTop : (U : ENNReal) ≠ ∞ := ENNReal.natCast_ne_top U
  have hm0 : (m : ENNReal) ≠ 0 := by
    exact_mod_cast hm.ne'
  have hlambdaTop :
      kappaLambda * (U : ENNReal) ^ 4 / (m : ENNReal) ≠ ∞ :=
    ENNReal.div_ne_top
      (ENNReal.mul_ne_top hkappaLambdaTop (ENNReal.pow_ne_top hUTop)) hm0
  have hqTop : kappaQ * (U : ENNReal) ^ 2 ≠ ∞ :=
    ENNReal.mul_ne_top hkappaQTop (ENNReal.pow_ne_top hUTop)
  exact ENNReal.add_ne_top.mpr ⟨hlambdaTop, hqTop⟩

/-- The attained-profile direct matching-restriction attachment is uniformly
`exp(O((log n)^2))` in the large-residual regime. -/
theorem eventually_profileHighSkeletonAttachment_le_matching_logScale :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ {b : ℕ} {k : ColoringProfile b}
          (row0 : OrderedProfilePartition n k) (U : ℕ),
          U ≤ phaseNat n →
          (∀ a : ProfileBlockIndex k, profileBlockMargin k a ≤ U) →
          ∀ demand : ProfileCanonicalHighSkeleton k U,
            (n : ℝ) / Real.log (n : ℝ) ^ 6 ≤
              (canonicalDemandResidualTotal (profileBlockMargin k)
                (profileBlockMargin k) U demand : ℝ) →
            profileHighSkeletonAttachment row0 U demand ≤
              ENNReal.ofReal
                (Real.exp (C * Real.log (n : ℝ) ^ 2)) := by
  obtain ⟨kappaLambda, kappaQ, hkLpos, hkLtop, hkQpos, hkQtop, hfinite⟩ :=
    exists_absolute_profileHighSkeletonAttachment_le_matchingEnvelope
  let C : ℝ := kappaLambda.toReal * 4 ^ 4 + kappaQ.toReal * 4 ^ 2
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards
    [eventually_phaseControlled_two_pow_le_cube,
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
      eventually_log_pow_eight_le_nat,
      eventually_gt_atTop (1 : ℕ)] with n hpow hphase hlog8 hn
  intro b k row0 U hU hcap demand hm
  let m := canonicalDemandResidualTotal (profileBlockMargin k)
    (profileBlockMargin k) U demand
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hmpos : 0 < m := by
    have : 0 < (m : ℝ) := lt_of_lt_of_le
      (div_pos (by positivity) (pow_pos hlog 6)) hm
    exact_mod_cast this
  have hbase := hfinite row0 U m hcap demand rfl hmpos
    (hpow U m hU hmpos hm)
  let exponent : ENNReal :=
    kappaLambda * (U : ENNReal) ^ 4 / (m : ENNReal) +
      kappaQ * (U : ENNReal) ^ 2
  have hexponent : exponent ≠ ∞ := by
    exact matchingRestrictionEnvelope_ne_top
      kappaLambda kappaQ U m hkLtop hkQtop hmpos
  have hbaseReal :
      profileHighSkeletonAttachment row0 U demand ≤
        ENNReal.ofReal (Real.exp exponent.toReal) := by
    apply ennreal_le_of_coe_le_ereal_exp_toReal _ _ hexponent
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr hbase
  apply hbaseReal.trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hUreal : (U : ℝ) ≤ 4 * Real.log (n : ℝ) :=
    (Nat.cast_le.mpr hU).trans hphase.2
  have henv := matchingRestrictionEnvelope_bound
    (n : ℝ) (Real.log (n : ℝ)) (U : ℝ) (m : ℝ)
    kappaLambda.toReal kappaQ.toReal 4
    (by positivity) hlog (Nat.cast_nonneg U) (by exact_mod_cast hmpos)
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg (by norm_num)
    hm hUreal hlog8
  have hparts := ENNReal.add_ne_top.mp hexponent
  rw [ENNReal.toReal_add hparts.1 hparts.2]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_pow, ENNReal.toReal_natCast]
  change
    kappaLambda.toReal * (U : ℝ) ^ 4 / (m : ℝ) +
      kappaQ.toReal * (U : ℝ) ^ 2 ≤
        C * Real.log (n : ℝ) ^ 2
  simpa [C] using henv

#print axioms matchingRestrictionEnvelope_bound
#print axioms eventually_log_pow_eight_le_nat
#print axioms matchingRestrictionEnvelope_ne_top
#print axioms eventually_profileHighSkeletonAttachment_le_matching_logScale

end

end Erdos625
