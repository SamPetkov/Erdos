import Erdos625.MidpointProfileRoundingIntDisplacement
import Erdos625.MuVertexScaling
import Erdos625.FullCornerFixedDeficitMoment
import Erdos625.FullCornerVertexRatioAsymptotic
import Mathlib.Tactic

/-!
# Uniform midpoint full-corner `mu` activity

This module isolates the analytic activity estimate consumed by the finite
full-corner aggregate.  It deliberately proves no partial-diagonal sum
estimate, no eventual full-corner smallness, and no empty or central range.
-/

namespace Erdos625

open Filter
open scoped BigOperators Topology

noncomputable section

set_option autoImplicit false

/-- Uniformly over every admissible midpoint rounding, the sum of the four
canonical full-corner `mu` activities tends to zero. -/
theorem eventually_sum_midpointPartialDiagonal_fullCorner_mu_activity_le
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∀ᶠ n : Nat in atTop,
      ∀ K : Nat,
        MidpointRoundingAdmissible n (phaseNat n) K →
          (∑ i : Fin 4,
            2 * (midpointMultiplicity n (phaseNat n) K i : Real) *
              mu (n / 32 + midpointPartialDiagonalSize (phaseNat n) i)
                 (midpointPartialDiagonalSize (phaseNat n) i)) ≤ epsilon := by
  have hFixed :
      ∀ᶠ n : Nat in atTop, ∀ i : Fin 4,
        Real.log (mu n (phaseNat n - fourDeficit i)) / logOrder n -
            (phaseDelta n + (fourDeficit i : Real)) <
          (1 / 4 : Real) := by
    have h0 :
        ∀ᶠ n : Nat in atTop,
          Real.log (mu n (phaseNat n - fourDeficit (0 : Fin 4))) / logOrder n -
              (phaseDelta n + (fourDeficit (0 : Fin 4) : Real)) <
            (1 / 4 : Real) :=
      (log_mu_phaseNat_sub_fourDeficit_div_logOrder_sub_phaseDelta_add_tendsto_zero
          (0 : Fin 4)).eventually_lt_const
        (by norm_num : (0 : Real) < 1 / 4)
    have h1 :
        ∀ᶠ n : Nat in atTop,
          Real.log (mu n (phaseNat n - fourDeficit (1 : Fin 4))) / logOrder n -
              (phaseDelta n + (fourDeficit (1 : Fin 4) : Real)) <
            (1 / 4 : Real) :=
      (log_mu_phaseNat_sub_fourDeficit_div_logOrder_sub_phaseDelta_add_tendsto_zero
          (1 : Fin 4)).eventually_lt_const
        (by norm_num : (0 : Real) < 1 / 4)
    have h2 :
        ∀ᶠ n : Nat in atTop,
          Real.log (mu n (phaseNat n - fourDeficit (2 : Fin 4))) / logOrder n -
              (phaseDelta n + (fourDeficit (2 : Fin 4) : Real)) <
            (1 / 4 : Real) :=
      (log_mu_phaseNat_sub_fourDeficit_div_logOrder_sub_phaseDelta_add_tendsto_zero
          (2 : Fin 4)).eventually_lt_const
        (by norm_num : (0 : Real) < 1 / 4)
    have h3 :
        ∀ᶠ n : Nat in atTop,
          Real.log (mu n (phaseNat n - fourDeficit (3 : Fin 4))) / logOrder n -
              (phaseDelta n + (fourDeficit (3 : Fin 4) : Real)) <
            (1 / 4 : Real) :=
      (log_mu_phaseNat_sub_fourDeficit_div_logOrder_sub_phaseDelta_add_tendsto_zero
          (3 : Fin 4)).eventually_lt_const
        (by norm_num : (0 : Real) < 1 / 4)
    filter_upwards [h0, h1, h2, h3] with n hn0 hn1 hn2 hn3
    intro i
    fin_cases i <;> assumption

  have hVertex :
      ∀ᶠ n : Nat in atTop, ∀ i : Fin 4,
        ((midpointPartialDiagonalSize (phaseNat n) i : Real) *
            Real.log
              (((n / 32 + midpointPartialDiagonalSize (phaseNat n) i : Nat) : Real) /
                (n : Real))) /
            logOrder n <
          (-19 / 2 : Real) := by
    have h0 :
        ∀ᶠ n : Nat in atTop,
          ((midpointPartialDiagonalSize (phaseNat n) (0 : Fin 4) : Real) *
              Real.log
                (((n / 32 +
                    midpointPartialDiagonalSize (phaseNat n) (0 : Fin 4) : Nat) :
                      Real) /
                  (n : Real))) /
              logOrder n <
            (-19 / 2 : Real) :=
      (midpointFullCornerVertexRatio_logExponent_tendsto_neg_ten
          (0 : Fin 4)).eventually_lt_const
        (by norm_num : (-10 : Real) < (-19 / 2 : Real))
    have h1 :
        ∀ᶠ n : Nat in atTop,
          ((midpointPartialDiagonalSize (phaseNat n) (1 : Fin 4) : Real) *
              Real.log
                (((n / 32 +
                    midpointPartialDiagonalSize (phaseNat n) (1 : Fin 4) : Nat) :
                      Real) /
                  (n : Real))) /
              logOrder n <
            (-19 / 2 : Real) :=
      (midpointFullCornerVertexRatio_logExponent_tendsto_neg_ten
          (1 : Fin 4)).eventually_lt_const
        (by norm_num : (-10 : Real) < (-19 / 2 : Real))
    have h2 :
        ∀ᶠ n : Nat in atTop,
          ((midpointPartialDiagonalSize (phaseNat n) (2 : Fin 4) : Real) *
              Real.log
                (((n / 32 +
                    midpointPartialDiagonalSize (phaseNat n) (2 : Fin 4) : Nat) :
                      Real) /
                  (n : Real))) /
              logOrder n <
            (-19 / 2 : Real) :=
      (midpointFullCornerVertexRatio_logExponent_tendsto_neg_ten
          (2 : Fin 4)).eventually_lt_const
        (by norm_num : (-10 : Real) < (-19 / 2 : Real))
    have h3 :
        ∀ᶠ n : Nat in atTop,
          ((midpointPartialDiagonalSize (phaseNat n) (3 : Fin 4) : Real) *
              Real.log
                (((n / 32 +
                    midpointPartialDiagonalSize (phaseNat n) (3 : Fin 4) : Nat) :
                      Real) /
                  (n : Real))) /
              logOrder n <
            (-19 / 2 : Real) :=
      (midpointFullCornerVertexRatio_logExponent_tendsto_neg_ten
          (3 : Fin 4)).eventually_lt_const
        (by norm_num : (-10 : Real) < (-19 / 2 : Real))
    filter_upwards [h0, h1, h2, h3] with n hn0 hn1 hn2 hn3
    intro i
    fin_cases i <;> assumption

  have hEpsilon :
      ∀ᶠ n : Nat in atTop, (8 : Real) / (n : Real) < epsilon :=
    (tendsto_const_div_atTop_nhds_zero_nat (8 : Real)).eventually_lt_const
      hepsilon

  filter_upwards
    [hFixed, hVertex, eventually_two_mul_phaseNat_le, hEpsilon]
      with n hFixedN hVertexN hTwo hEpsilonN
  intro K hround

  have hcd :=
    midpointMultiplicity_count_deficit_intDisplacement
      n (phaseNat n) K hround
  have hcount := hcd.1
  have hmom := hcd.2.1
  have hAlpha : 5 < phaseNat n := hround.1
  have hnK : n ≤ phaseNat n * K := hround.2.2.1

  have hDeficitLeFive :
      ∀ i : Fin 4, fourDeficit i ≤ 5 := by
    intro i
    have hi := i.isLt
    simp only [fourDeficit]
    omega

  have hDeficitLe :
      ∀ i : Fin 4, fourDeficit i ≤ phaseNat n := by
    intro i
    exact (hDeficitLeFive i).trans hAlpha.le

  have hsplit :
      (∑ i : Fin 4,
          midpointPartialDiagonalSize (phaseNat n) i *
            midpointMultiplicity n (phaseNat n) K i) +
        (∑ i : Fin 4,
          tangentDeficitNat i *
            midpointMultiplicity n (phaseNat n) K i) =
          phaseNat n * K := by
    have hstep :
        (∑ i : Fin 4,
            midpointPartialDiagonalSize (phaseNat n) i *
              midpointMultiplicity n (phaseNat n) K i) +
          (∑ i : Fin 4,
            tangentDeficitNat i *
              midpointMultiplicity n (phaseNat n) K i) =
            ∑ i : Fin 4,
              phaseNat n *
                midpointMultiplicity n (phaseNat n) K i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have ht : tangentDeficitNat i = fourDeficit i := rfl
      simp only [midpointPartialDiagonalSize, ht, ← Nat.add_mul]
      rw [Nat.sub_add_cancel (hDeficitLe i)]
    rw [hstep, ← Finset.mul_sum, hcount]

  have hmass :
      selectedVertexMass
          (midpointPartialDiagonalSize (phaseNat n))
          (midpointMultiplicity n (phaseNat n) K) = n := by
    rw [midpointDeficit] at hmom
    unfold selectedVertexMass
    obtain ⟨P, hP⟩ :
        ∃ P, phaseNat n * K = P := ⟨_, rfl⟩
    rw [hP] at hsplit hmom hnK
    omega

  have hSizePos :
      ∀ i : Fin 4,
        0 < midpointPartialDiagonalSize (phaseNat n) i := by
    intro i
    have hd5 := hDeficitLeFive i
    simp only [midpointPartialDiagonalSize]
    omega

  have hKle : K ≤ n := by
    calc
      K = ∑ i : Fin 4,
          midpointMultiplicity n (phaseNat n) K i := hcount.symm
      _ ≤ ∑ i : Fin 4,
          midpointPartialDiagonalSize (phaseNat n) i *
            midpointMultiplicity n (phaseNat n) K i :=
        Finset.sum_le_sum fun i _ =>
          Nat.le_mul_of_pos_left _ (hSizePos i)
      _ = n := hmass

  have hCoordLe :
      ∀ i : Fin 4,
        midpointMultiplicity n (phaseNat n) K i ≤ n := by
    intro i
    have hle :
        midpointMultiplicity n (phaseNat n) K i ≤
          ∑ j : Fin 4,
            midpointMultiplicity n (phaseNat n) K j :=
      Finset.single_le_sum
        (f := fun j : Fin 4 =>
          midpointMultiplicity n (phaseNat n) K j)
        (fun j _ => Nat.zero_le _)
        (Finset.mem_univ i)
    rw [hcount] at hle
    exact hle.trans hKle

  have hnPos : 0 < n := by
    omega
  have hnOne : 1 < n := by
    omega
  have hnRPos : (0 : Real) < (n : Real) := by
    exact_mod_cast hnPos
  have hLogPos : 0 < logOrder n := by
    rw [logOrder]
    exact Real.log_pos (by exact_mod_cast hnOne)

  have hActivity :
      ∀ i : Fin 4,
        2 * (midpointMultiplicity n (phaseNat n) K i : Real) *
            mu (n / 32 + midpointPartialDiagonalSize (phaseNat n) i)
              (midpointPartialDiagonalSize (phaseNat n) i) ≤
          2 / (n : Real) ^ 2 := by
    intro i
    let s : Nat := midpointPartialDiagonalSize (phaseNat n) i
    let v : Nat := n / 32 + s

    have hd5 : fourDeficit i ≤ 5 := hDeficitLeFive i
    have hsPos : 0 < s := by
      simpa only [s] using hSizePos i
    have hsPhase : s ≤ phaseNat n := by
      change phaseNat n - fourDeficit i ≤ phaseNat n
      exact Nat.sub_le _ _
    have hsv : s ≤ v := by
      dsimp [v]
      omega
    have hvPos : 0 < v :=
      lt_of_lt_of_le hsPos hsv

    have hsTwo : 2 * s ≤ n := by
      omega
    have hQuotTwo : 2 * (n / 32) ≤ n := by
      calc
        2 * (n / 32) ≤ (n / 32) * 32 := by omega
        _ ≤ n := Nat.div_mul_le_self n 32
    have hvn : v ≤ n := by
      dsimp [v]
      omega
    have hsn : s ≤ n :=
      hsv.trans hvn

    have hScale :
        mu v s ≤
          mu n s * ((v : Real) / (n : Real)) ^ s :=
      mu_le_mu_mul_vertex_ratio_pow
        (n := n) (v := v) (s := s) hnPos hsv hvn

    have hFix :
        Real.log (mu n s) / logOrder n -
            (phaseDelta n + (fourDeficit i : Real)) <
          (1 / 4 : Real) := by
      simpa only [s, midpointPartialDiagonalSize] using hFixedN i

    have hVert :
        ((s : Real) *
            Real.log ((v : Real) / (n : Real))) /
            logOrder n <
          (-19 / 2 : Real) := by
      simpa only [s, v] using hVertexN i

    have hdR : (fourDeficit i : Real) ≤ 5 := by
      exact_mod_cast hd5
    have hDelta0 : 0 ≤ phaseDelta n :=
      phaseDelta_nonneg n
    have hDelta1 : phaseDelta n < 1 :=
      phaseDelta_lt_one n

    have hNorm :
        Real.log (mu n s) / logOrder n +
            ((s : Real) *
              Real.log ((v : Real) / (n : Real))) /
              logOrder n ≤
          (-3 : Real) := by
      linarith [hFix, hVert, hdR, hDelta0, hDelta1]

    have hNorm' :
        (Real.log (mu n s) +
            (s : Real) *
              Real.log ((v : Real) / (n : Real))) /
            logOrder n ≤
          (-3 : Real) := by
      rw [add_div]
      exact hNorm

    have hLogSum :
        Real.log (mu n s) +
            (s : Real) *
              Real.log ((v : Real) / (n : Real)) ≤
          (-3 : Real) * logOrder n :=
      (div_le_iff₀ hLogPos).mp hNorm'

    have hMuPos : 0 < mu n s :=
      mu_pos hsn
    have hvRPos : (0 : Real) < (v : Real) := by
      exact_mod_cast hvPos
    have hRatioPos : 0 < (v : Real) / (n : Real) :=
      div_pos hvRPos hnRPos
    have hPowPos :
        0 < ((v : Real) / (n : Real)) ^ s :=
      pow_pos hRatioPos s
    have hProdPos :
        0 <
          mu n s * ((v : Real) / (n : Real)) ^ s :=
      mul_pos hMuPos hPowPos

    have hLogProd :
        Real.log
            (mu n s * ((v : Real) / (n : Real)) ^ s) ≤
          (-3 : Real) * logOrder n := by
      rw [Real.log_mul hMuPos.ne' hPowPos.ne', Real.log_pow]
      exact hLogSum

    have hExp :
        Real.exp ((-3 : Real) * logOrder n) =
          ((n : Real) ^ 3)⁻¹ := by
      rw [logOrder]
      have hpowlog :
          (-3 : Real) * Real.log (n : Real) =
            -Real.log ((n : Real) ^ 3) := by
        rw [Real.log_pow]
        ring
      rw [hpowlog, Real.exp_neg,
        Real.exp_log (pow_pos hnRPos 3)]

    have hDecay :
        mu n s * ((v : Real) / (n : Real)) ^ s ≤
          ((n : Real) ^ 3)⁻¹ := by
      calc
        mu n s * ((v : Real) / (n : Real)) ^ s
            ≤ Real.exp ((-3 : Real) * logOrder n) :=
          (Real.log_le_iff_le_exp hProdPos).mp hLogProd
        _ = ((n : Real) ^ 3)⁻¹ := hExp

    have hMuV :
        mu v s ≤ ((n : Real) ^ 3)⁻¹ :=
      hScale.trans hDecay

    have hmR :
        (midpointMultiplicity n (phaseNat n) K i : Real) ≤
          (n : Real) := by
      exact_mod_cast hCoordLe i
    have hTwom :
        2 * (midpointMultiplicity n (phaseNat n) K i : Real) ≤
          2 * (n : Real) :=
      mul_le_mul_of_nonneg_left hmR (by norm_num)
    have hFirst :
        2 * (midpointMultiplicity n (phaseNat n) K i : Real) *
            mu v s ≤
          2 * (n : Real) * mu v s :=
      mul_le_mul_of_nonneg_right hTwom (mu_nonneg v s)
    have hSecond :
        2 * (n : Real) * mu v s ≤
          2 * (n : Real) * ((n : Real) ^ 3)⁻¹ :=
      mul_le_mul_of_nonneg_left hMuV (by positivity)
    have hInv :
        2 * (n : Real) * ((n : Real) ^ 3)⁻¹ =
          2 / (n : Real) ^ 2 := by
      field_simp [hnRPos.ne']
    have hAct :
        2 * (midpointMultiplicity n (phaseNat n) K i : Real) *
            mu v s ≤
          2 / (n : Real) ^ 2 := by
      calc
        2 * (midpointMultiplicity n (phaseNat n) K i : Real) *
              mu v s
            ≤ 2 * (n : Real) * mu v s := hFirst
        _ ≤ 2 * (n : Real) * ((n : Real) ^ 3)⁻¹ := hSecond
        _ = 2 / (n : Real) ^ 2 := hInv
    simpa only [s, v] using hAct

  calc
    (∑ i : Fin 4,
      2 * (midpointMultiplicity n (phaseNat n) K i : Real) *
        mu (n / 32 + midpointPartialDiagonalSize (phaseNat n) i)
          (midpointPartialDiagonalSize (phaseNat n) i))
      ≤ ∑ _i : Fin 4, 2 / (n : Real) ^ 2 :=
        Finset.sum_le_sum fun i _ => hActivity i
    _ = 8 / (n : Real) ^ 2 := by
      rw [Fin.sum_univ_four]
      ring
    _ ≤ 8 / (n : Real) := by
      rw [div_le_div_iff₀ (pow_pos hnRPos 2) hnRPos]
      have hnROne : (1 : Real) ≤ (n : Real) := by
        exact_mod_cast (show 1 ≤ n by omega)
      have hmul :
          0 ≤ (n : Real) * ((n : Real) - 1) :=
        mul_nonneg hnRPos.le (sub_nonneg.mpr hnROne)
      nlinarith
    _ ≤ epsilon := le_of_lt hEpsilonN

end

end Erdos625
