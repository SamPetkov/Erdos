import Erdos625.Section9ProfileAttachmentQOnly
import Erdos625.Section9ProfileAttachmentSmallResidualLogScale
import Erdos625.Section9PhaseTwoPowerCorridor
import Erdos625.Section9ActualAttachmentAggregation
import Erdos625.Section10AmplificationScales
import Mathlib.Tactic

/-!
# Section IX: q-only two-regime attachment assembly

The direct matching-restriction route gives an `exp(O((log n)^2))` attachment
bound whenever its intrinsic finite hypothesis `2^U <= m^3` holds.  The
existing phase corridor shows that this hypothesis holds throughout the old
large-residual range.  Its complement is therefore covered by the literal
small-residual estimate.

This file combines those two profile-level estimates with the exact bare-times-
attachment aggregation.  It does not estimate the Section VIII bare skeleton
sum or prove the final random-graph statement.
-/

namespace Erdos625

open Filter
open scoped ENNReal Topology

noncomputable section

set_option autoImplicit false

/-- A `log^2` large branch and an `n/log^5` small branch yield one deterministic
error sequence at the amplification scale `n/log^4`.  The two branches may have
different nonnegative constants. -/
theorem exists_uniform_qOnly_twoRegime_error
    (S : ℕ → Type*)
    (attachment : ∀ n, S n → ℝ)
    (m₀ : ∀ n, S n → ℕ)
    (Cq Cs : ℝ) (hCq : 0 ≤ Cq) (hCs : 0 ≤ Cs)
    (hlarge : ∀ᶠ n : ℕ in atTop,
      ∀ s : S n,
        (n : ℝ) / Real.log (n : ℝ) ^ 6 ≤ (m₀ n s : ℝ) →
        attachment n s ≤ Real.exp (Cq * Real.log (n : ℝ) ^ 2))
    (hsmall : ∀ᶠ n : ℕ in atTop,
      ∀ s : S n,
        (m₀ n s : ℝ) < (n : ℝ) / Real.log (n : ℝ) ^ 6 →
        attachment n s ≤
          Real.exp (Cs * (n : ℝ) / Real.log (n : ℝ) ^ 5)) :
    ∃ εAtt : ℕ → ℝ,
      Tendsto εAtt atTop (nhds 0) ∧
        ∀ᶠ n : ℕ in atTop,
          0 ≤ εAtt n ∧
            ∀ s : S n,
              attachment n s ≤
                Real.exp
                  (εAtt n * (n : ℝ) / Real.log (n : ℝ) ^ 4) := by
  refine ⟨fun n =>
    Cq * (Real.log (n : ℝ) ^ 6 / (n : ℝ)) +
      Cs / Real.log (n : ℝ), ?_, ?_⟩
  · have h_log_div_n :
        Tendsto
          (fun n : ℕ => Real.log (n : ℝ) ^ 6 / (n : ℝ))
          atTop (nhds 0) := by
      suffices h_log :
          Tendsto (fun y : ℝ => y ^ 6 / Real.exp y) atTop (nhds 0) by
        have hcomp := h_log.comp
          (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
        exact hcomp.congr' (by
          filter_upwards [Filter.eventually_gt_atTop 0] with n hn
          simp +decide [Real.exp_log (Nat.cast_pos.mpr hn)])
      simpa only [Real.exp_neg, div_eq_mul_inv] using
        Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 6
    have h_inv_log :
        Tendsto (fun n : ℕ => 1 / Real.log (n : ℝ)) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    simpa only [div_eq_mul_inv] using
      (tendsto_const_nhds.mul h_log_div_n).add
        (tendsto_const_nhds.mul h_inv_log)
  · obtain ⟨a₁, ha₁⟩ := hlarge
    obtain ⟨a₂, ha₂⟩ := hsmall
    use Nat.max (Nat.max a₁ a₂) 3
    intro n hn
    have ha₁n : a₁ ≤ n := by omega
    have ha₂n : a₂ ≤ n := by omega
    have hn3 : 3 ≤ n := by omega
    have hnpos : 0 < (n : ℝ) := by positivity
    have hlog : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 3) hn3))
    have hscale :
        (Cq * (Real.log (n : ℝ) ^ 6 / (n : ℝ)) +
            Cs / Real.log (n : ℝ)) *
              (n : ℝ) / Real.log (n : ℝ) ^ 4 =
          Cq * Real.log (n : ℝ) ^ 2 +
            Cs * (n : ℝ) / Real.log (n : ℝ) ^ 5 := by
      field_simp [ne_of_gt hnpos, ne_of_gt hlog]
      ring
    refine ⟨?_, ?_⟩
    · exact add_nonneg
        (mul_nonneg hCq
          (div_nonneg (pow_nonneg (Real.log_natCast_nonneg _) _)
            (Nat.cast_nonneg _)))
        (div_nonneg hCs (Real.log_natCast_nonneg _))
    · intro s
      by_cases hmass :
          (m₀ n s : ℝ) < (n : ℝ) / Real.log (n : ℝ) ^ 6
      · refine (ha₂ n ha₂n s hmass).trans (Real.exp_le_exp.mpr ?_)
        rw [hscale]
        exact le_add_of_nonneg_left
          (mul_nonneg hCq (sq_nonneg (Real.log (n : ℝ))))
      · refine (ha₁ n ha₁n s (le_of_not_gt hmass)).trans
          (Real.exp_le_exp.mpr ?_)
        rw [hscale]
        exact le_add_of_nonneg_right
          (div_nonneg
            (mul_nonneg hCs (Nat.cast_nonneg n))
            (pow_nonneg hlog.le 5))

/-- The q-only large branch and the literal small branch combine into the exact
midpoint canonical attachment sum with a vanishing amplification-scale error. -/
theorem exists_midpointCanonicalAttachment_qOnly_twoRegime_error
    (b U : Nat → Nat)
    (k : (n : Nat) → ColoringProfile (b n))
    (row0 : (n : Nat) → OrderedProfilePartition n (k n))
    (hU : ∀ᶠ n : Nat in atTop, U n ≤ phaseNat n)
    (hcap : ∀ᶠ n : Nat in atTop,
      ∀ a : ProfileBlockIndex (k n), profileBlockMargin (k n) a ≤ U n) :
    ∃ epsilon : Nat → Real,
      Tendsto epsilon atTop (nhds 0) ∧
      (∀ᶠ n in atTop, 0 ≤ epsilon n) ∧
      ∀ᶠ n in atTop,
        midpointCanonicalAttachmentSum (row0 n) (U n) ≤
          canonicalBareSkeletonSum (k n) (U n) *
            ENNReal.ofReal
              (Real.exp (epsilon n * amplificationBase n)) := by
  obtain ⟨Cq, hCq, hq⟩ :=
    eventually_profileHighSkeletonAttachment_le_qOnly_logScale
  obtain ⟨Cs, hCs, hs⟩ :=
    eventually_profileHighSkeletonAttachment_le_smallResidual_logScale
  have hlarge : ∀ᶠ n : Nat in atTop,
      ∀ demand : ProfileCanonicalHighSkeleton (k n) (U n),
        (n : Real) / Real.log (n : Real) ^ 6 ≤
            (canonicalDemandResidualTotal
              (profileBlockMargin (k n)) (profileBlockMargin (k n))
              (U n) demand : Real) →
        (profileHighSkeletonAttachment (row0 n) (U n) demand).toReal ≤
          Real.exp (Cq * Real.log (n : Real) ^ 2) := by
    filter_upwards
      [hq, hU, hcap, eventually_phaseControlled_two_pow_le_cube,
        eventually_gt_atTop (1 : Nat)] with n hqn hUn hcapn hcorr hn
    intro demand hmass
    let m := canonicalDemandResidualTotal
      (profileBlockMargin (k n)) (profileBlockMargin (k n)) (U n) demand
    have hlog : 0 < Real.log (n : Real) :=
      Real.log_pos (by exact_mod_cast hn)
    have hmpos : 0 < m := by
      have hmreal : 0 < (m : Real) :=
        lt_of_lt_of_le
          (div_pos (by positivity) (pow_pos hlog 6)) hmass
      exact_mod_cast hmreal
    have hpow : 2 ^ U n ≤ m ^ 3 := hcorr (U n) m hUn hmpos hmass
    have hbound := hqn (row0 n) (U n) hUn hcapn demand hpow
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq (by
      rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)])
  have hsmall : ∀ᶠ n : Nat in atTop,
      ∀ demand : ProfileCanonicalHighSkeleton (k n) (U n),
        (canonicalDemandResidualTotal
          (profileBlockMargin (k n)) (profileBlockMargin (k n))
          (U n) demand : Real) <
            (n : Real) / Real.log (n : Real) ^ 6 →
        (profileHighSkeletonAttachment (row0 n) (U n) demand).toReal ≤
          Real.exp (Cs * (n : Real) / Real.log (n : Real) ^ 5) := by
    filter_upwards [hs, hU, hcap] with n hsn hUn hcapn
    intro demand hmass
    have hbound := hsn (row0 n) (U n) hUn hcapn demand hmass
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq (by
      rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)])
  obtain ⟨epsilon, hepsilon, hevent⟩ :=
    exists_uniform_qOnly_twoRegime_error
      (fun n => ProfileCanonicalHighSkeleton (k n) (U n))
      (fun n demand =>
        (profileHighSkeletonAttachment (row0 n) (U n) demand).toReal)
      (fun n demand =>
        canonicalDemandResidualTotal
          (profileBlockMargin (k n)) (profileBlockMargin (k n))
          (U n) demand)
      Cq Cs hCq hCs hlarge hsmall
  refine ⟨epsilon, hepsilon, hevent.mono fun _ hn => hn.1, ?_⟩
  filter_upwards
    [hevent, hq, hs, hU, hcap, eventually_phaseControlled_two_pow_le_cube,
      eventually_gt_atTop (1 : Nat)] with n hn hqn hsn hUn hcapn hcorr hnlarge
  apply midpointCanonicalAttachmentSum_le_bare_mul
  intro demand
  have hfinite :
      profileHighSkeletonAttachment (row0 n) (U n) demand ≠ ⊤ := by
    by_cases hmass :
        (canonicalDemandResidualTotal
          (profileBlockMargin (k n)) (profileBlockMargin (k n))
          (U n) demand : Real) <
            (n : Real) / Real.log (n : Real) ^ 6
    · have hbound := hsn (row0 n) (U n) hUn hcapn demand hmass
      intro htop
      rw [htop] at hbound
      exact ENNReal.ofReal_ne_top (top_le_iff.mp hbound)
    · let m := canonicalDemandResidualTotal
        (profileBlockMargin (k n)) (profileBlockMargin (k n)) (U n) demand
      have hlog : 0 < Real.log (n : Real) :=
        Real.log_pos (by exact_mod_cast hnlarge)
      have hmpos : 0 < m := by
        have hmreal : 0 < (m : Real) :=
          lt_of_lt_of_le
            (div_pos (by positivity) (pow_pos hlog 6))
            (le_of_not_gt hmass)
        exact_mod_cast hmreal
      have hpow : 2 ^ U n ≤ m ^ 3 :=
        hcorr (U n) m hUn hmpos (le_of_not_gt hmass)
      have hbound := hqn (row0 n) (U n) hUn hcapn demand hpow
      intro htop
      rw [htop] at hbound
      exact ENNReal.ofReal_ne_top (top_le_iff.mp hbound)
  rw [← ENNReal.ofReal_toReal hfinite]
  apply ENNReal.ofReal_le_ofReal
  simpa only [amplificationBase, mul_div_assoc] using hn.2 demand

#print axioms exists_uniform_qOnly_twoRegime_error
#print axioms exists_midpointCanonicalAttachment_qOnly_twoRegime_error

end

end Erdos625
