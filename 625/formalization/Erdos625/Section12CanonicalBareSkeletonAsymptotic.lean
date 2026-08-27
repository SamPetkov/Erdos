import Erdos625.Section8RealizedTableDeficitSum
import Erdos625.Section8FusedWeightedEndpointRowSum
import Erdos625.Section8FusedRowAsymptotic
import Erdos625.Section8CanonicalThreeQuarterRhoSmallness
import Erdos625.Section8FourDeficitProfileCover
import Erdos625.Section9CanonicalPolymerAggregation
import Erdos625.Section10AmplificationScales
import Erdos625.Section12PartialDiagonalAssembly
import Mathlib.Tactic

/-!
# Section VIII: canonical midpoint bare-skeleton asymptotics

This module combines the finite realized-table reduction, endpoint transport,
the fused-row estimate, and the canonical partial-diagonal asymptotic.  The
result is the bare-skeleton estimate consumed by the Section IX attachment
argument, with a concrete nonnegative error tending to zero at the
`amplificationBase` scale.
-/

namespace Erdos625

open Filter Set
open scoped BigOperators ENNReal Topology

noncomputable section

set_option autoImplicit false

private theorem fourEndpointMultiplicity_fourDeficitEmbedding
    (alpha : Nat) (hAlpha : 5 < alpha) (m : Fin 4 → Nat) :
    fourEndpointMultiplicity alpha hAlpha
        (fourDeficitEmbedding alpha hAlpha m) = m := by
  funext i
  exact (fourDeficitEmbedding_eval_and_off_image alpha hAlpha m).1 i

private theorem fourEndpointSize_eq_midpointPartialDiagonalSize
    (alpha : Nat) (hAlpha : 5 < alpha) :
    (fun i : Fin 4 ↦ fourEndpointSize alpha hAlpha i) =
      midpointPartialDiagonalSize alpha := by
  funext i
  exact fourDeficitCoordinate_val_add_one_eq alpha hAlpha i

private theorem fourEndpointMarginMass_midpoint
    (alpha : Nat) (hAlpha : 5 < alpha) (r : Fin 4 → Nat) :
    fourEndpointMarginMass alpha hAlpha r =
      selectedVertexMass (midpointPartialDiagonalSize alpha) r := by
  unfold fourEndpointMarginMass selectedVertexMass
  apply Finset.sum_congr rfl
  intro i _
  rw [congrFun
    (fourEndpointSize_eq_midpointPartialDiagonalSize alpha hAlpha) i]

private theorem midpointEmbedding_vertexMass
    (n alpha K : Nat) (hAlpha : 5 < alpha)
    (hadm : MidpointRoundingAdmissible n alpha K) :
    ColoringProfile.vertexMass
        (fourDeficitEmbedding alpha hAlpha
          (midpointMultiplicity n alpha K)) = n := by
  rw [(fourDeficitEmbedding_profile_invariants alpha hAlpha
    (midpointMultiplicity n alpha K)).2.1]
  exact midpointMultiplicity_vertexMass n alpha K hadm

private theorem midpointIndex_le_vertexCount
    (n alpha K : Nat) (hadm : MidpointRoundingAdmissible n alpha K) :
    K ≤ n := by
  have hsizeOne : ∀ i : Fin 4,
      1 ≤ midpointPartialDiagonalSize alpha i := by
    intro i
    have hAlpha := hadm.1
    fin_cases i <;>
      simp [midpointPartialDiagonalSize, fourDeficit] <;> omega
  calc
    K = ∑ i : Fin 4, midpointMultiplicity n alpha K i :=
      (midpointMultiplicity_count_deficit_intDisplacement n alpha K hadm).1.symm
    _ ≤ ∑ i : Fin 4,
        midpointPartialDiagonalSize alpha i *
          midpointMultiplicity n alpha K i := by
      apply Finset.sum_le_sum
      intro i _
      simpa using Nat.mul_le_mul_right
        (midpointMultiplicity n alpha K i) (hsizeOne i)
    _ = n := midpointMultiplicity_vertexMass n alpha K hadm

private theorem eventually_endpointCellBase_le_half :
    ∀ᶠ n : Nat in atTop,
      ∀ hAlpha : 5 < phaseNat n,
        ∀ i j : Fin 4,
          threeQuarterHighCellBase n
              (fourEndpointOverlapSize (phaseNat n) hAlpha i j) ≤
            (1 / 2 : ENNReal) := by
  have hreal :
      Tendsto (fun x : Real => Real.log x / x ^ (1 / 4 : Real))
        atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop
      (r := (1 / 4 : Real)) (by norm_num)).tendsto_div_nhds_zero
  have hnat :
      Tendsto (fun n : Nat => logOrder n / (n : Real) ^ (1 / 4 : Real))
        atTop (nhds 0) := by
    simpa only [Function.comp_apply, Function.comp_def, logOrder] using
      hreal.comp tendsto_natCast_atTop_atTop
  have hscaled :
      Tendsto (fun n : Nat =>
        (4 * Real.exp (19 / 6 : Real)) *
          (logOrder n / (n : Real) ^ (1 / 4 : Real))) atTop (nhds 0) := by
    simpa using hnat.const_mul (4 * Real.exp (19 / 6 : Real))
  have hdecay : ∀ᶠ n : Nat in atTop,
      4 * Real.exp (19 / 6 : Real) * logOrder n /
          (n : Real) ^ (1 / 4 : Real) ≤ 1 / 2 := by
    filter_upwards
      [hscaled.eventually_lt_const (by norm_num : (0 : Real) < 1 / 2)] with
        n hn
    calc
      4 * Real.exp (19 / 6 : Real) * logOrder n /
            (n : Real) ^ (1 / 4 : Real) =
          (4 * Real.exp (19 / 6 : Real)) *
            (logOrder n / (n : Real) ^ (1 / 4 : Real)) := by ring
      _ ≤ 1 / 2 := hn.le
  filter_upwards
    [eventually_five_fourths_log_sub_le_q_mul_endpointBudget,
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
      hdecay, eventually_gt_atTop (1 : Nat)] with
      n hbudget hphase hdecayN hn
  intro hAlpha i j
  have hnPos : (0 : Real) < n := by positivity
  let m := fourEndpointOverlapSize (phaseNat n) hAlpha i j
  let b : Nat := (3 * m - 1) / 4
  have hb := hbudget hAlpha i j
  change (5 / 4 : Real) * logOrder n - 19 / 6 ≤ q * (b : Real) at hb
  have hexp := Real.exp_le_exp.mpr hb
  have hpow :
      (n : Real) ^ (5 / 4 : Real) / Real.exp (19 / 6 : Real) ≤
        (2 : Real) ^ b := by
    rw [Real.exp_sub] at hexp
    rw [show Real.exp ((5 / 4 : Real) * logOrder n) =
        (n : Real) ^ (5 / 4 : Real) by
      rw [Real.rpow_def_of_pos hnPos, logOrder]
      congr 1
      ring] at hexp
    rw [show Real.exp (q * (b : Real)) = (2 : Real) ^ b by
      rw [show q * (b : Real) = (b : Real) * q by ring,
        Real.exp_nat_mul, q, Real.exp_log (by norm_num : (0 : Real) < 2)]] at hexp
    exact hexp
  have hm : (m : Real) ≤ 4 * logOrder n := by
    exact (Nat.cast_le.mpr (fourEndpointOverlapSize_le_alpha
      (phaseNat n) hAlpha i j)).trans hphase.2
  have hdenPos : (0 : Real) < (2 : Real) ^ b := by positivity
  have hbase :
      (n : Real) * (m : Real) / (2 : Real) ^ b ≤
        Real.exp (19 / 6 : Real) * (m : Real) /
          (n : Real) ^ (1 / 4 : Real) := by
    have hnRpowPos : 0 < (n : Real) ^ (1 / 4 : Real) := by positivity
    rw [div_le_div_iff₀ hdenPos hnRpowPos]
    calc
      (n : Real) * (m : Real) * (n : Real) ^ (1 / 4 : Real) =
          ((n : Real) ^ (5 / 4 : Real) / Real.exp (19 / 6 : Real)) *
            (m : Real) * Real.exp (19 / 6 : Real) := by
        rw [show (5 / 4 : Real) = 1 + 1 / 4 by ring,
          Real.rpow_add hnPos, Real.rpow_one]
        field_simp [Real.exp_ne_zero]
      _ ≤ (2 : Real) ^ b * (m : Real) * Real.exp (19 / 6 : Real) := by
        gcongr
      _ = Real.exp (19 / 6 : Real) * (m : Real) * (2 : Real) ^ b := by ring
  have hterm :
      (threeQuarterCellBase n
        (fourEndpointOverlapSize (phaseNat n) hAlpha i j)).toReal ≤
          4 * Real.exp (19 / 6 : Real) * logOrder n /
            (n : Real) ^ (1 / 4 : Real) := by
    rw [threeQuarterCellBase, ENNReal.toReal_div, ENNReal.toReal_mul,
      ENNReal.toReal_natCast, ENNReal.toReal_natCast, ENNReal.toReal_pow,
      ENNReal.toReal_ofNat]
    exact hbase.trans (by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [mul_le_mul_of_nonneg_left hm
        (Real.exp_pos (19 / 6 : Real)).le])
  have hcellTop :
      threeQuarterCellBase n
          (fourEndpointOverlapSize (phaseNat n) hAlpha i j) ≠ ⊤ := by
    rw [threeQuarterCellBase]
    apply ENNReal.div_ne_top
    · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top n)
        (ENNReal.natCast_ne_top
          (fourEndpointOverlapSize (phaseNat n) hAlpha i j))
    · exact pow_ne_zero _ (by norm_num : (2 : ENNReal) ≠ 0)
  apply (ENNReal.toReal_le_toReal hcellTop (by norm_num)).mp
  norm_num
  exact hterm.trans hdecayN

private theorem canonicalBareSkeletonSum_le_fusedRowMax_mul_D
    (n alpha : Nat) (hAlpha : 5 < alpha) (hHigh : 8 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (hn : Finset.univ.sum (profileBlockMargin k) = n)
    (hsmall : ∀ i j : Fin 4,
      threeQuarterHighCellBase n
          (fourEndpointOverlapSize alpha hAlpha i j) ≤ (1 / 2 : ENNReal)) :
    canonicalBareSkeletonSum k (fourEndpointLargestSize alpha hAlpha) ≤
      (fourEndpointFusedRowMax n alpha hAlpha) ^
          (∑ i : Fin 4, fourEndpointMultiplicity alpha hAlpha k i) *
        ∑ r ∈ partialSubprofileBox
            (fourEndpointMultiplicity alpha hAlpha k),
          fourEndpointD n alpha hAlpha k r := by
  change
    (∑ demand : ProfileCanonicalHighSkeleton k
        (fourEndpointLargestSize alpha hAlpha),
      profileHighSkeletonWeight k
        (fourEndpointLargestSize alpha hAlpha) demand) ≤ _
  calc
    (∑ demand : ProfileCanonicalHighSkeleton k
        (fourEndpointLargestSize alpha hAlpha),
      profileHighSkeletonWeight k
        (fourEndpointLargestSize alpha hAlpha) demand) ≤
        ∑ L : ↥(fourEndpointRealizedFullTables alpha hAlpha k),
          fourEndpointW n alpha hAlpha k L.1 *
            ∏ i : Fin 4, ∏ j : Fin 4,
              (fourEndpointThreeQuarterDeficitFactor n alpha hAlpha i j) ^
                L.1.toFun i j := by
      simpa only [hn, fourEndpointThreeQuarterDeficitFactor] using
        sum_profileHighSkeletonWeight_le_realizedTableThreeQuarterProduct
          alpha hAlpha hHigh k hcover slotIndex (by
            simpa only [hn] using hsmall)
    _ ≤ (fourEndpointFusedRowMax n alpha hAlpha) ^
          (∑ i : Fin 4, fourEndpointMultiplicity alpha hAlpha k i) *
        ∑ r ∈ partialSubprofileBox
            (fourEndpointMultiplicity alpha hAlpha k),
          fourEndpointD n alpha hAlpha k r :=
      sum_fourEndpointRealized_W_mul_threeQuarterProduct_le_fusedRowMax
        n alpha hAlpha k

private theorem fourEndpointD_midpoint_eq_ofReal_partialDiagonalWeight
    (n alpha K : Nat) (hAlpha : 5 < alpha) (hHigh : 8 < alpha)
    (hadm : MidpointRoundingAdmissible n alpha K)
    (r : Fin 4 → Nat)
    (hr : r ∈ partialSubprofileBox (midpointMultiplicity n alpha K)) :
    fourEndpointD n alpha hAlpha
        (fourDeficitEmbedding alpha hAlpha
          (midpointMultiplicity n alpha K)) r =
      ENNReal.ofReal
        (partialDiagonalWeight n (midpointPartialDiagonalSize alpha)
          (midpointMultiplicity n alpha K) r) := by
  have hrle : IsPartialSubprofile (midpointMultiplicity n alpha K) r := by
    simpa only [mem_partialSubprofileBox] using hr
  have hmass :
      selectedVertexMass (midpointPartialDiagonalSize alpha) r ≤ n := by
    calc
      selectedVertexMass (midpointPartialDiagonalSize alpha) r ≤
          selectedVertexMass (midpointPartialDiagonalSize alpha)
            (midpointMultiplicity n alpha K) := by
        unfold selectedVertexMass
        apply Finset.sum_le_sum
        intro i _
        exact Nat.mul_le_mul_left _ (hrle i)
      _ = n := midpointMultiplicity_vertexMass n alpha K hadm
  have hsizeThree : ∀ i : Fin 4,
      3 ≤ midpointPartialDiagonalSize alpha i := by
    intro i
    fin_cases i <;>
      simp [midpointPartialDiagonalSize, fourDeficit] <;> omega
  let u : Fin 4 → Nat := midpointPartialDiagonalSize alpha
  let k : Fin 4 → Nat := midpointMultiplicity n alpha K
  let m : Nat := selectedVertexMass u r
  let L : Nat := selectedBlockCount r
  let M : Nat := selectedInternalEdgeCount u r
  let F : Nat := ∏ i : Fin 4, (r i).factorial
  let U : Nat := ∏ i : Fin 4, (u i).factorial ^ r i
  let C : Nat := ∏ i : Fin 4, (k i).choose (r i)
  let G : Nat := ∏ i : Fin 4,
    ((u i).factorial * localSignRewardNat (u i)) ^ r i
  have huThree : ∀ i : Fin 4, 3 ≤ u i := by
    simpa only [u] using hsizeThree
  have hone : ∀ i : Fin 4, 1 ≤ (u i).choose 2 := by
    intro i
    have hh := Nat.choose_le_choose 2 (huThree i)
    norm_num at hh
    omega
  have hchoose (i : Fin 4) :
      (k i).descFactorial (r i) = (r i).factorial * (k i).choose (r i) :=
    Nat.descFactorial_eq_factorial_mul_choose (k i) (r i)
  have hselection :
      (∏ i : Fin 4, (k i).descFactorial (r i)) = F * C := by
    simp_rw [hchoose]
    exact Finset.prod_mul_distrib
  have hmarking : partialMarkingCount k r = C ^ 2 := by
    unfold partialMarkingCount C
    exact Finset.prod_pow Finset.univ 2 (fun i => (k i).choose (r i))
  have hprofile : partialProfileFactorialProduct u r = U * F := by
    unfold partialProfileFactorialProduct U F
    exact Finset.prod_mul_distrib
  have hG : G = U * 2 ^ (M - L) := by
    have hterm (i : Fin 4) :
        ((u i).choose 2 - 1) * r i =
          (u i).choose 2 * r i - r i := by
      rw [Nat.sub_mul, one_mul]
    have hsum :
        (∑ i : Fin 4, ((u i).choose 2 - 1) * r i) = M - L := by
      simp_rw [hterm]
      rw [Finset.sum_tsub_distrib]
      · rfl
      · intro i _
        simpa only [one_mul] using Nat.mul_le_mul_right (r i) (hone i)
    unfold G U
    simp_rw [localSignRewardNat, if_pos (huThree _), mul_pow, ← pow_mul]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum]
  have hfactorial : (n - m).factorial * n.descFactorial m = n.factorial := by
    exact Nat.factorial_mul_descFactorial hmass
  have hcross :
      (F * C) ^ 2 * G * 2 ^ L * n.factorial =
        C ^ 2 * (n - m).factorial * (U * F) * 2 ^ M * F *
          n.descFactorial m := by
    rw [hG]
    have hML : M - L + L = M := by
      apply Nat.sub_add_cancel
      unfold M L selectedInternalEdgeCount selectedBlockCount
      apply Finset.sum_le_sum
      intro i _
      simpa only [one_mul] using Nat.mul_le_mul_right (r i) (hone i)
    have hpow : 2 ^ (M - L) * 2 ^ L = 2 ^ M := by
      rw [← pow_add, hML]
    calc
      (F * C) ^ 2 * (U * 2 ^ (M - L)) * 2 ^ L * n.factorial =
          (F * C) ^ 2 * U * (2 ^ (M - L) * 2 ^ L) * n.factorial := by
        ring
      _ = (F * C) ^ 2 * U * 2 ^ M * n.factorial := by rw [hpow]
      _ = C ^ 2 * (n - m).factorial * (U * F) * 2 ^ M * F *
          n.descFactorial m := by
        rw [← hfactorial]
        ring
  have hdiagCast :
      fourEndpointDiagonalLocalProduct alpha hAlpha r = (G : ENNReal) := by
    unfold fourEndpointDiagonalLocalProduct fourEndpointDiagonalLocalFactor G
    simp_rw [congrFun
      (fourEndpointSize_eq_midpointPartialDiagonalSize alpha hAlpha)]
    push_cast
    rfl
  have hFne : F ≠ 0 := by
    unfold F
    positivity
  have hdescNe : n.descFactorial m ≠ 0 := by
    simp only [ne_eq, Nat.descFactorial_eq_zero_iff_lt]
    exact not_lt_of_ge (by simpa only [m, u] using hmass)
  have hDtop :
      fourEndpointD n alpha hAlpha
          (fourDeficitEmbedding alpha hAlpha k) r ≠ ⊤ := by
    unfold fourEndpointD fourEndpointMarginSelectionProduct
      fourEndpointMarginFactorialProduct
    rw [fourEndpointMultiplicity_fourDeficitEmbedding,
      fourEndpointMarginMass_midpoint, hdiagCast]
    apply ENNReal.mul_ne_top
    · exact ENNReal.div_ne_top
        (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))
        (by exact_mod_cast hFne)
    · exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
        (by exact_mod_cast hdescNe)
  rw [← ENNReal.toReal_eq_toReal_iff' hDtop (by finiteness)]
  unfold fourEndpointD fourEndpointMarginSelectionProduct
    fourEndpointMarginFactorialProduct
  rw [fourEndpointMultiplicity_fourDeficitEmbedding,
    fourEndpointMarginMass_midpoint, hdiagCast]
  unfold partialDiagonalWeight partialSignedFirstMoment
  change
    (((((∏ i : Fin 4, (k i).descFactorial (r i) : Nat) : ENNReal) ^ 2 /
          (F : ENNReal)) *
        (((G : Nat) : ENNReal) / (n.descFactorial m : ENNReal))).toReal) = _
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.toReal_natCast]
  rw [hselection, hmarking, hprofile]
  rw [ENNReal.toReal_ofReal (by positivity)]
  have hFneReal : (F : Real) ≠ 0 := by exact_mod_cast hFne
  have hdescNeReal : (n.descFactorial m : Real) ≠ 0 := by
    exact_mod_cast hdescNe
  field_simp [hFneReal, hdescNeReal]
  norm_cast
  simp only [m, u]
  rw [hcross]
  ring

private theorem eventually_sum_fourEndpointD_midpoint_le_two :
    ∀ᶠ n : Nat in atTop,
      ∀ hAlpha : 5 < phaseNat n,
        ∑ r ∈ partialSubprofileBox
            (midpointMultiplicity n (phaseNat n)
              (phaseCochromaticMidpointIndex n)),
          fourEndpointD n (phaseNat n) hAlpha
            (fourDeficitEmbedding (phaseNat n) hAlpha
              (midpointMultiplicity n (phaseNat n)
                (phaseCochromaticMidpointIndex n))) r ≤
            ENNReal.ofReal 2 := by
  have hsum :=
    tendsto_sum_midpointPartialDiagonalWeight.eventually_lt_const
      (by norm_num : (1 : Real) < 2)
  filter_upwards
    [hsum, eventually_eight_lt_phaseNat,
      eventually_phaseCochromaticMidpointIndex_rounding_admissible] with
      n hsumN hHigh hadm
  intro hAlpha
  calc
    ∑ r ∈ partialSubprofileBox
          (midpointMultiplicity n (phaseNat n)
            (phaseCochromaticMidpointIndex n)),
        fourEndpointD n (phaseNat n) hAlpha
          (fourDeficitEmbedding (phaseNat n) hAlpha
            (midpointMultiplicity n (phaseNat n)
              (phaseCochromaticMidpointIndex n))) r =
        ∑ r ∈ partialSubprofileBox
          (midpointMultiplicity n (phaseNat n)
            (phaseCochromaticMidpointIndex n)),
        ENNReal.ofReal
          (partialDiagonalWeight n
            (midpointPartialDiagonalSize (phaseNat n))
            (midpointMultiplicity n (phaseNat n)
              (phaseCochromaticMidpointIndex n)) r) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact fourEndpointD_midpoint_eq_ofReal_partialDiagonalWeight
        n (phaseNat n) (phaseCochromaticMidpointIndex n) hAlpha hHigh
          hadm r hr
    _ = ENNReal.ofReal
        (∑ r ∈ partialSubprofileBox
          (midpointMultiplicity n (phaseNat n)
            (phaseCochromaticMidpointIndex n)),
          partialDiagonalWeight n
            (midpointPartialDiagonalSize (phaseNat n))
            (midpointMultiplicity n (phaseNat n)
              (phaseCochromaticMidpointIndex n)) r) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro r hr
      exact (partialDiagonalWeight_pos n
        (midpointPartialDiagonalSize (phaseNat n))
        (midpointMultiplicity n (phaseNat n)
          (phaseCochromaticMidpointIndex n)) r
        (mem_partialSubprofileBox.mp hr)).le
    _ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hsumN.le

private theorem fourEndpointFusedRowMax_pow_midpoint_le_exp
    (n : Nat) (C : Real) (hC : 0 < C) (hn : 1 < n)
    (hAlpha : 5 < phaseNat n)
    (hadm : MidpointRoundingAdmissible n (phaseNat n)
      (phaseCochromaticMidpointIndex n))
    (hrow : fourEndpointFusedRowMax n (phaseNat n) hAlpha ≤
      ENNReal.ofReal
        (1 + C * logOrder n ^ (5 / 2 : Real) / Real.sqrt n)) :
    fourEndpointFusedRowMax n (phaseNat n) hAlpha ^
        phaseCochromaticMidpointIndex n ≤
      ENNReal.ofReal
        (Real.exp
          ((n : Real) *
            (C * logOrder n ^ (5 / 2 : Real) / Real.sqrt n))) := by
  let eps : Real := C * logOrder n ^ (5 / 2 : Real) / Real.sqrt n
  have hlog : 0 < logOrder n := by
    exact Real.log_pos (by exact_mod_cast hn)
  have heps : 0 ≤ eps := by
    dsimp [eps]
    positivity
  have hKle : phaseCochromaticMidpointIndex n ≤ n :=
    midpointIndex_le_vertexCount n (phaseNat n)
      (phaseCochromaticMidpointIndex n) hadm
  have hexp :
      (1 + eps) ^ phaseCochromaticMidpointIndex n ≤
        Real.exp ((n : Real) * eps) := by
    calc
      (1 + eps) ^ phaseCochromaticMidpointIndex n ≤
          Real.exp
            ((phaseCochromaticMidpointIndex n : Real) * eps) := by
        rw [Real.exp_nat_mul]
        exact pow_le_pow_left₀ (by positivity)
          (by linarith [Real.add_one_le_exp eps]) _
      _ ≤ Real.exp ((n : Real) * eps) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hKle) heps
  calc
    fourEndpointFusedRowMax n (phaseNat n) hAlpha ^
          phaseCochromaticMidpointIndex n ≤
        (ENNReal.ofReal (1 + eps)) ^
          phaseCochromaticMidpointIndex n := by
      apply pow_le_pow_left'
      simpa only [eps] using hrow
    _ = ENNReal.ofReal
        ((1 + eps) ^ phaseCochromaticMidpointIndex n) := by
      rw [ENNReal.ofReal_pow (by positivity)]
    _ ≤ ENNReal.ofReal (Real.exp ((n : Real) * eps)) :=
      ENNReal.ofReal_le_ofReal hexp
    _ = ENNReal.ofReal
        (Real.exp
          ((n : Real) *
            (C * logOrder n ^ (5 / 2 : Real) / Real.sqrt n))) := by
      rfl

private noncomputable def canonicalBareSkeletonError
    (C : Real) (n : Nat) : Real :=
  Real.log 2 * logOrder n ^ 4 / (n : Real) +
    C * logOrder n ^ (13 / 2 : Real) / Real.sqrt n

private theorem tendsto_canonicalBareSkeletonError_zero (C : Real) :
    Tendsto (canonicalBareSkeletonError C) atTop (nhds 0) := by
  have hFirstReal :
      Tendsto (fun x : Real => Real.log x ^ 4 / x) atTop (nhds 0) := by
    simpa using
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 4 one_ne_zero
  have hFirstNat :
      Tendsto (fun n : Nat => logOrder n ^ 4 / (n : Real))
        atTop (nhds 0) := by
    simpa only [Function.comp_apply, Function.comp_def, logOrder] using
      hFirstReal.comp tendsto_natCast_atTop_atTop
  have hSecondReal :
      Tendsto
        (fun x : Real =>
          Real.log x ^ (13 / 2 : Real) / x ^ (1 / 2 : Real))
        atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop
      (13 / 2 : Real) (by norm_num : (0 : Real) < 1 / 2)).tendsto_div_nhds_zero
  have hSecondNat :
      Tendsto
        (fun n : Nat =>
          logOrder n ^ (13 / 2 : Real) / Real.sqrt n)
        atTop (nhds 0) := by
    simpa only [Function.comp_apply, Function.comp_def, logOrder,
      Real.sqrt_eq_rpow] using
      hSecondReal.comp tendsto_natCast_atTop_atTop
  unfold canonicalBareSkeletonError
  simpa only [mul_div_assoc, mul_zero, add_zero] using
    (hFirstNat.const_mul (Real.log 2)).add (hSecondNat.const_mul C)

private theorem eventually_canonicalBareSkeletonError_nonneg (C : Real)
    (hC : 0 < C) :
    ∀ᶠ n : Nat in atTop, 0 ≤ canonicalBareSkeletonError C n := by
  filter_upwards [eventually_gt_atTop (1 : Nat)] with n hn
  have hlog : 0 < logOrder n := Real.log_pos (by exact_mod_cast hn)
  unfold canonicalBareSkeletonError
  positivity

private theorem eventually_canonicalBareSkeletonError_mul_amplificationBase
    (C : Real) :
    ∀ᶠ n : Nat in atTop,
      canonicalBareSkeletonError C n * amplificationBase n =
        Real.log 2 +
          (n : Real) *
            (C * logOrder n ^ (5 / 2 : Real) / Real.sqrt n) := by
  filter_upwards [eventually_gt_atTop (1 : Nat)] with n hn
  have hnPos : (0 : Real) < n := by positivity
  have hlog : 0 < logOrder n := Real.log_pos (by exact_mod_cast hn)
  have hpow :
      logOrder n ^ (13 / 2 : Real) =
        logOrder n ^ (5 / 2 : Real) * logOrder n ^ 4 := by
    rw [show (13 / 2 : Real) = 5 / 2 + 4 by ring,
      Real.rpow_add hlog]
    norm_num [Real.rpow_natCast]
  unfold canonicalBareSkeletonError amplificationBase
  change
    (Real.log 2 * logOrder n ^ 4 / (n : Real) +
        C * logOrder n ^ (13 / 2 : Real) / Real.sqrt n) *
      ((n : Real) / logOrder n ^ 4) = _
  rw [hpow]
  field_simp [hlog.ne', (Real.sqrt_pos.mpr hnPos).ne']

/-- The canonical midpoint bare-skeleton sum is subexponential on the
`amplificationBase` scale, with a concrete eventually nonnegative error
coefficient tending to zero. -/
theorem exists_phaseMidpointCanonicalBareSkeleton_error :
    ∃ epsilon : Nat → Real,
      Tendsto epsilon atTop (nhds 0) ∧
      (∀ᶠ n : Nat in atTop, 0 ≤ epsilon n) ∧
      ∀ᶠ n : Nat in atTop,
        ∀ hAlpha : 5 < phaseNat n,
          canonicalBareSkeletonSum
              (fourDeficitEmbedding (phaseNat n) hAlpha
                (midpointMultiplicity n (phaseNat n)
                  (phaseCochromaticMidpointIndex n)))
              (fourEndpointLargestSize (phaseNat n) hAlpha) ≤
            ENNReal.ofReal
              (Real.exp (epsilon n * amplificationBase n)) := by
  obtain ⟨C, hC, hrow⟩ :=
    eventually_fourEndpointFusedRowMax_le_one_add_logOrder_rpow_five_halves_div_sqrt
  refine ⟨canonicalBareSkeletonError C,
    tendsto_canonicalBareSkeletonError_zero C,
    eventually_canonicalBareSkeletonError_nonneg C hC, ?_⟩
  filter_upwards
    [hrow, eventually_sum_fourEndpointD_midpoint_le_two,
      eventually_endpointCellBase_le_half,
      eventually_phaseCochromaticMidpointIndex_rounding_admissible,
      eventually_eight_lt_phaseNat, eventually_gt_atTop (1 : Nat),
      eventually_canonicalBareSkeletonError_mul_amplificationBase C] with
      n hrowN hsumN hsmallN hadm hHigh hn herror
  intro hAlpha
  let k : ColoringProfile (phaseNat n + 1) :=
    fourDeficitEmbedding (phaseNat n) hAlpha
      (midpointMultiplicity n (phaseNat n)
        (phaseCochromaticMidpointIndex n))
  have hcover : IsFourEndpointProfileCover (phaseNat n) hAlpha k := by
    exact fourDeficitEmbedding_isFourEndpointProfileCover
      (phaseNat n) hAlpha
        (midpointMultiplicity n (phaseNat n)
          (phaseCochromaticMidpointIndex n))
  let slotIndex : FourEndpointSlotIndexing (phaseNat n) hAlpha k :=
    canonicalFourEndpointSlotIndexing (phaseNat n) hAlpha k
  have hmass : Finset.univ.sum (profileBlockMargin k) = n := by
    rw [sum_profileBlockMargin_eq_vertexMass]
    exact midpointEmbedding_vertexMass n (phaseNat n)
      (phaseCochromaticMidpointIndex n) hAlpha hadm
  have hskeleton := canonicalBareSkeletonSum_le_fusedRowMax_mul_D
    n (phaseNat n) hAlpha hHigh k hcover slotIndex hmass (hsmallN hAlpha)
  have hcount :=
    (midpointMultiplicity_count_deficit_intDisplacement n (phaseNat n)
      (phaseCochromaticMidpointIndex n) hadm).1
  have hskeleton' :
      canonicalBareSkeletonSum k
          (fourEndpointLargestSize (phaseNat n) hAlpha) ≤
        fourEndpointFusedRowMax n (phaseNat n) hAlpha ^
            phaseCochromaticMidpointIndex n *
          ∑ r ∈ partialSubprofileBox
              (midpointMultiplicity n (phaseNat n)
                (phaseCochromaticMidpointIndex n)),
            fourEndpointD n (phaseNat n) hAlpha k r := by
    simpa only [k, fourEndpointMultiplicity_fourDeficitEmbedding,
      hcount] using hskeleton
  have hrowPow := fourEndpointFusedRowMax_pow_midpoint_le_exp
    n C hC hn hAlpha hadm (hrowN hAlpha)
  have hsumK :
      ∑ r ∈ partialSubprofileBox
            (midpointMultiplicity n (phaseNat n)
              (phaseCochromaticMidpointIndex n)),
          fourEndpointD n (phaseNat n) hAlpha k r ≤ ENNReal.ofReal 2 := by
    simpa only [k] using hsumN hAlpha
  calc
    canonicalBareSkeletonSum
          (fourDeficitEmbedding (phaseNat n) hAlpha
            (midpointMultiplicity n (phaseNat n)
              (phaseCochromaticMidpointIndex n)))
          (fourEndpointLargestSize (phaseNat n) hAlpha) ≤
        ENNReal.ofReal
            (Real.exp
              ((n : Real) *
                (C * logOrder n ^ (5 / 2 : Real) / Real.sqrt n))) *
          ENNReal.ofReal 2 := by
      exact hskeleton'.trans
        (mul_le_mul hrowPow hsumK (by positivity) (by positivity))
    _ = ENNReal.ofReal
        (Real.exp
            ((n : Real) *
              (C * logOrder n ^ (5 / 2 : Real) / Real.sqrt n)) * 2) := by
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    _ = ENNReal.ofReal
        (Real.exp
            ((n : Real) *
              (C * logOrder n ^ (5 / 2 : Real) / Real.sqrt n)) *
          Real.exp (Real.log 2)) := by
      rw [Real.exp_log (by norm_num : (0 : Real) < 2)]
    _ = ENNReal.ofReal
        (Real.exp
          (Real.log 2 +
            (n : Real) *
              (C * logOrder n ^ (5 / 2 : Real) / Real.sqrt n))) := by
      rw [← Real.exp_add]
      congr 2
      ring
    _ = ENNReal.ofReal
        (Real.exp
          (canonicalBareSkeletonError C n * amplificationBase n)) := by
      rw [herror]

#print axioms exists_phaseMidpointCanonicalBareSkeleton_error

end

end Erdos625
