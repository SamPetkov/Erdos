import Erdos625.Section9ProfileAttachmentLargeResidualExp
import Erdos625.Section9PhaseENNRealTauCorridor
import Erdos625.Section9PhaseTwoPowerCorridor
import Erdos625.Section9ResidualRegimeScaleAdapters
import Erdos625.ProfileBlockCardinalityBound
import Erdos625.Section9PositiveSupportMassBound

namespace Erdos625

open Filter
open scoped ENNReal Topology

noncomputable section

set_option autoImplicit false

theorem eventually_profileHighSkeletonAttachment_le_largeResidual_logScale :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ {b : ℕ} {k : ColoringProfile b}
          (row₀ : OrderedProfilePartition n k) (U : ℕ),
          U ≤ phaseNat n →
          (∀ a : ProfileBlockIndex k, profileBlockMargin k a ≤ U) →
          ∀ demand : ProfileCanonicalHighSkeleton k U,
            (n : ℝ) / Real.log (n : ℝ) ^ 6 ≤
              (canonicalDemandResidualTotal (profileBlockMargin k)
                (profileBlockMargin k) U demand : ℝ) →
            profileHighSkeletonAttachment row₀ U demand ≤
              ENNReal.ofReal
                (Real.exp (C * Real.log (n : ℝ) ^ 8)) := by
  obtain ⟨kappaLambda, kappaQ, hkLpos, hkLtop, hkQpos, hkQtop, hfinite⟩ :=
    exists_absolute_profileHighSkeletonAttachment_le_largeResidualExp
  let C : ℝ :=
    kappaLambda.toReal * 4 ^ 4 +
      2 * kappaQ.toReal ^ 4 * 4 ^ 12 +
      12 * kappaQ.toReal * 4 ^ 2
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards
    [eventually_phaseControlled_ennreal_tau_lt_one_third kappaQ hkQtop,
      eventually_phaseControlled_two_pow_le_cube,
      eventually_largeResidualEnvelope_logScale
        kappaLambda.toReal kappaQ.toReal 4 ENNReal.toReal_nonneg
          ENNReal.toReal_nonneg (by norm_num),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
      eventually_gt_atTop (1 : ℕ)] with n htau hpow henvelope hphase hn
  intro b k row₀ U hU hcap demand hm
  let m := canonicalDemandResidualTotal (profileBlockMargin k)
    (profileBlockMargin k) U demand
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hmpos : 0 < m := by
    have : 0 < (m : ℝ) := lt_of_lt_of_le
      (div_pos (by positivity) (pow_pos hlog 6)) hm
    exact_mod_cast this
  have hbase := hfinite row₀ U m hcap demand rfl hmpos
    (hpow U m hU hmpos hm) (htau U m hU hmpos hm)
  apply hbase.trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hcard : (Fintype.card (ProfileBlockIndex k) : ℝ) ≤ n := by
    exact_mod_cast
      card_profileBlockIndex_le_vertex_count_of_orderedProfilePartition row₀
  have hsupportNat : (positiveDemandSupport demand.1).card * U ≤ 2 * n := by
    calc
      (positiveDemandSupport demand.1).card * U ≤
          2 * totalDemand demand.1 :=
        positiveDemandSupport_card_mul_cap_le_two_total demand.1 U
          (canonicalDemandImage_high _ _ U demand)
      _ ≤ 2 * n := by
        have hd := profileHighSkeleton_totalDemand_le k U demand
        rw [sum_profileBlockMargin_eq_vertexMass, row₀.vertexMass_eq] at hd
        omega
  have hsupport :
      ((positiveDemandSupport demand.1).card : ℝ) * U ≤ 2 * n := by
    exact_mod_cast hsupportNat
  have hUreal : (U : ℝ) ≤ 4 * Real.log (n : ℝ) :=
    (Nat.cast_le.mpr hU).trans hphase.2
  have henv := henvelope (U : ℝ) (m : ℝ)
    (Fintype.card (ProfileBlockIndex k) : ℝ)
    ((positiveDemandSupport demand.1).card : ℝ)
    (by positivity) (by exact_mod_cast hmpos) (by positivity) (by positivity)
    hm hUreal hcard hsupport
  have htop := residualLargeEnvelope_ne_top kappaLambda kappaQ
    (Fintype.card (ProfileBlockIndex k))
    (positiveDemandSupport demand.1).card U m hkLtop hkQtop hmpos
  have houter := ENNReal.add_ne_top.mp htop
  have hinner := ENNReal.add_ne_top.mp houter.1
  rw [ENNReal.toReal_add houter.1 houter.2,
    ENNReal.toReal_add hinner.1 hinner.2]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, ENNReal.toReal_ofNat, Nat.cast_mul]
  change
    kappaLambda.toReal * (U : ℝ) ^ 4 / (m : ℝ) +
        2 * (Fintype.card (ProfileBlockIndex k) : ℝ) *
          (kappaQ.toReal * (U : ℝ) ^ 3 / (m : ℝ)) ^ 4 +
        6 * ((positiveDemandSupport demand.1).card : ℝ) *
          (kappaQ.toReal * (U : ℝ) ^ 3 / (m : ℝ)) ≤
      C * Real.log (n : ℝ) ^ 8
  simpa [C] using henv

end

end Erdos625
