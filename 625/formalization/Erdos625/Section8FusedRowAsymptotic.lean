import Erdos625.Section8FusedWeightedEndpointRowSum
import Erdos625.Section8CanonicalThreeQuarterRhoSmallness
import Mathlib.Tactic

namespace Erdos625

open Filter
open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-!
# Section VIII: phase asymptotic for the fused four-endpoint row maximum

This module proves the phase asymptotic for the fused row maximum. It keeps
the remaining partial-diagonal estimate and the final bare-skeleton corollary
out of the statement.
-/

private lemma e625k_q_lower : (0.693 : ℝ) ≤ q :=
  le_of_lt ((by norm_num : (0.693 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9)

private lemma e625k_q_upper : q ≤ (0.694 : ℝ) :=
  le_of_lt (Real.log_two_lt_d9.trans (by norm_num))

private lemma e625k_inv_q_upper : 1 / q ≤ (1.4434 : ℝ) := by
  rw [div_le_iff₀ q_pos]
  nlinarith [e625k_q_lower]

private lemma e625k_log_q_lower : 1 - 1 / q ≤ Real.log q := by
  have h := Real.log_le_sub_one_of_pos (x := 1 / q) (one_div_pos.mpr q_pos)
  rw [Real.log_div one_ne_zero q_ne_zero, Real.log_one] at h
  linarith

private lemma e625k_q_mul_alphaZero (n : ℕ) (hn : 1 < n) :
    q * alphaZero n =
      2 * Real.log n - 2 * Real.log (logOrder n) + 2 * Real.log q + 2 - q := by
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have h2 : Real.log (Real.log (n : ℝ) / q) = Real.log (logOrder n) - Real.log q := by
    rw [Real.log_div (ne_of_gt hlogpos) q_ne_zero]
    rfl
  have h3 : Real.log (Real.exp 1 / 2) = 1 - q := by
    rw [Real.log_div (Real.exp_ne_zero 1) (by norm_num), Real.log_exp]
    rfl
  have hexp : alphaZero n =
      2 * (Real.log (n : ℝ) / q) -
        2 * ((Real.log (logOrder n) - Real.log q) / q) +
        2 * ((1 - q) / q) + 1 := by
    unfold alphaZero logBaseTwo
    rw [h2, h3]
  rw [hexp]
  field_simp [q_ne_zero]
  ring

private lemma e625k_q_mul_phase_lower (n : ℕ) (hn : PhaseDomain n) :
    2 * Real.log n - 2 * Real.log (logOrder n) - 1 ≤ q * (phaseNat n : ℝ) := by
  have hfloor : alphaZero n - 1 ≤ (phaseInt n : ℝ) :=
    le_of_lt (Int.sub_one_lt_floor (alphaZero n))
  have hcast : alphaZero n - 1 ≤ (phaseNat n : ℝ) := by
    rw [phaseNat_cast_real hn]; exact hfloor
  have hmul : q * (alphaZero n - 1) ≤ q * (phaseNat n : ℝ) :=
    mul_le_mul_of_nonneg_left hcast q_pos.le
  have hid := e625k_q_mul_alphaZero n hn.1
  have hlq := e625k_log_q_lower
  have hiq := e625k_inv_q_upper
  have hqu := e625k_q_upper
  nlinarith [hmul, hid, hlq, hiq, hqu]

private lemma e625k_q_mul_overlap_lower (n : ℕ) (hn : PhaseDomain n)
    (hAlpha : 5 < phaseNat n) (i j : Fin 4) :
    2 * Real.log n - 2 * Real.log (logOrder n) - 5 ≤
      q * ((fourEndpointOverlapSize (phaseNat n) hAlpha i j : ℕ) : ℝ) := by
  have hm := alpha_sub_five_le_fourEndpointOverlapSize (phaseNat n) hAlpha i j
  have hcast : (phaseNat n : ℝ) - 5 ≤
      ((fourEndpointOverlapSize (phaseNat n) hAlpha i j : ℕ) : ℝ) := by
    have h1 : ((phaseNat n - 5 : ℕ) : ℝ) ≤
        ((fourEndpointOverlapSize (phaseNat n) hAlpha i j : ℕ) : ℝ) :=
      Nat.cast_le.mpr hm
    rw [Nat.cast_sub (by omega : 5 ≤ phaseNat n)] at h1
    push_cast at h1
    linarith
  have hmul := mul_le_mul_of_nonneg_left hcast q_pos.le
  have hphase := e625k_q_mul_phase_lower n hn
  have hqu := e625k_q_upper
  nlinarith [hmul, hphase, hqu]

private lemma e625k_q_mul_budget_lower (n : ℕ) (hn : PhaseDomain n)
    (hAlpha : 5 < phaseNat n) (hseven : 7 ≤ phaseNat n) (i j : Fin 4) :
    (3 / 2 : ℝ) * Real.log n - (3 / 2 : ℝ) * Real.log (logOrder n) - 5 ≤
      q * (((3 * fourEndpointOverlapSize (phaseNat n) hAlpha i j - 1) / 4 : ℕ) : ℝ) := by
  have hnat := three_mul_alpha_sub_nineteen_le_four_mul_endpointBudget (phaseNat n) hAlpha i j
  have h19 : 19 ≤ 3 * phaseNat n := by omega
  have hcast : 3 * (phaseNat n : ℝ) - 19 ≤
      4 * (((3 * fourEndpointOverlapSize (phaseNat n) hAlpha i j - 1) / 4 : ℕ) : ℝ) := by
    have h1 : ((3 * phaseNat n - 19 : ℕ) : ℝ) ≤
        ((4 * ((3 * fourEndpointOverlapSize (phaseNat n) hAlpha i j - 1) / 4) : ℕ) : ℝ) :=
      Nat.cast_le.mpr hnat
    rw [Nat.cast_sub h19] at h1
    push_cast at h1
    linarith
  have hmul := mul_le_mul_of_nonneg_left hcast q_pos.le
  have hphase := e625k_q_mul_phase_lower n hn
  have hqu := e625k_q_upper
  nlinarith [hmul, hphase, hqu]

private lemma e625k_two_pow_eq_exp (b : ℕ) : (2 : ℝ) ^ b = Real.exp (q * (b : ℝ)) := by
  rw [← Real.rpow_natCast (2 : ℝ) b, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
  rfl

private lemma e625k_two_rpow_eq_exp (x : ℝ) : (2 : ℝ) ^ x = Real.exp (q * x) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
  rfl

private lemma e625k_two_pow_budget_lower (n : ℕ) (hn : PhaseDomain n)
    (hAlpha : 5 < phaseNat n) (hseven : 7 ≤ phaseNat n) (hLpos : 0 < logOrder n)
    (i j : Fin 4) :
    (n : ℝ) ^ (3 / 2 : ℝ) / (Real.exp 5 * logOrder n ^ (3 / 2 : ℝ)) ≤
      (2 : ℝ) ^ (((3 * fourEndpointOverlapSize (phaseNat n) hAlpha i j - 1) / 4 : ℕ)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (1 : ℕ) < n := hn.1
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this.le
  have hbudget := e625k_q_mul_budget_lower n hn hAlpha hseven i j
  rw [e625k_two_pow_eq_exp]
  have hrewrite : (n : ℝ) ^ (3 / 2 : ℝ) / (Real.exp 5 * logOrder n ^ (3 / 2 : ℝ)) =
      Real.exp ((3 / 2 : ℝ) * Real.log n - (3 / 2 : ℝ) * Real.log (logOrder n) - 5) := by
    rw [Real.exp_sub, Real.exp_sub, Real.rpow_def_of_pos hnpos,
      Real.rpow_def_of_pos hLpos]
    rw [show Real.log (logOrder n) * (3 / 2 : ℝ) = (3 / 2 : ℝ) * Real.log (logOrder n) by ring,
      show Real.log (n : ℝ) * (3 / 2 : ℝ) = (3 / 2 : ℝ) * Real.log (n : ℝ) by ring]
    field_simp
  rw [hrewrite]
  exact Real.exp_le_exp.mpr hbudget

private lemma e625k_two_rpow_neg_overlap_upper (n : ℕ) (hn : PhaseDomain n)
    (hAlpha : 5 < phaseNat n) (hLpos : 0 < logOrder n) (i j : Fin 4) :
    (2 : ℝ) ^ (-(fourEndpointOverlapSize (phaseNat n) hAlpha i j : ℝ)) ≤
      Real.exp 5 * logOrder n ^ 2 / (n : ℝ) ^ 2 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (1 : ℕ) < n := hn.1
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this.le
  have hoverlap := e625k_q_mul_overlap_lower n hn hAlpha i j
  rw [e625k_two_rpow_eq_exp]
  have hrewrite : Real.exp 5 * logOrder n ^ 2 / (n : ℝ) ^ 2 =
      Real.exp (-(2 * Real.log n - 2 * Real.log (logOrder n) - 5)) := by
    have h1 : Real.exp (2 * Real.log (n : ℝ)) = (n : ℝ) ^ 2 := by
      rw [show (2 : ℝ) * Real.log (n : ℝ) = Real.log (n : ℝ) + Real.log (n : ℝ) by ring,
        Real.exp_add, Real.exp_log hnpos]
      ring
    have h2 : Real.exp (2 * Real.log (logOrder n)) = logOrder n ^ 2 := by
      rw [show (2 : ℝ) * Real.log (logOrder n) = Real.log (logOrder n) + Real.log (logOrder n) by
          ring, Real.exp_add, Real.exp_log hLpos]
      ring
    rw [show -(2 * Real.log (n : ℝ) - 2 * Real.log (logOrder n) - 5) =
        5 + 2 * Real.log (logOrder n) - 2 * Real.log (n : ℝ) by ring,
      Real.exp_sub, Real.exp_add, h1, h2]
  rw [hrewrite]
  apply Real.exp_le_exp.mpr
  have hqm : q * (fourEndpointOverlapSize (phaseNat n) hAlpha i j : ℝ) ≥
      2 * Real.log n - 2 * Real.log (logOrder n) - 5 := hoverlap
  linarith

private lemma e625k_div_bound (N M B L : ℝ) (hN : 0 < N) (hL : 0 < L) (hB : 0 < B)
    (hMb : M ≤ 4 * L)
    (hBl : N ^ (3 / 2 : ℝ) / (Real.exp 5 * L ^ (3 / 2 : ℝ)) ≤ B) :
    N * M / B ≤ 4 * Real.exp 5 * (L ^ (5 / 2 : ℝ) / Real.sqrt N) := by
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hu : (0 : ℝ) < L ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hL _
  have hN32 : N ^ (3 / 2 : ℝ) = N * Real.sqrt N := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hN, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  have hL52 : L ^ (5 / 2 : ℝ) = L * L ^ (3 / 2 : ℝ) := by
    rw [show (5 / 2 : ℝ) = 1 + 3 / 2 by norm_num, Real.rpow_add hL, Real.rpow_one]
  rw [div_le_iff₀ hB]
  have hkey : 4 * Real.exp 5 * (L ^ (5 / 2 : ℝ) / Real.sqrt N) *
      (N * Real.sqrt N / (Real.exp 5 * L ^ (3 / 2 : ℝ))) = 4 * L * N := by
    rw [hL52]
    field_simp
  have hstep : N * M ≤ 4 * Real.exp 5 * (L ^ (5 / 2 : ℝ) / Real.sqrt N) *
      (N * Real.sqrt N / (Real.exp 5 * L ^ (3 / 2 : ℝ))) := by
    rw [hkey]
    nlinarith [hN.le, hMb]
  refine hstep.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← hN32]
  exact hBl

private lemma e625k_base_toReal_le (n : ℕ) (hn : PhaseDomain n) (hAlpha : 5 < phaseNat n)
    (hseven : 7 ≤ phaseNat n) (hLpos : 0 < logOrder n)
    (hphase : (phaseNat n : ℝ) ≤ 4 * logOrder n) (i j : Fin 4) :
    (threeQuarterHighCellBase n
        (fourEndpointOverlapSize (phaseNat n) hAlpha i j)).toReal ≤
      4 * Real.exp 5 * (logOrder n ^ (5 / 2 : ℝ) / Real.sqrt n) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (1 : ℕ) < n := hn.1
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this.le
  have htoReal : (threeQuarterHighCellBase n
      (fourEndpointOverlapSize (phaseNat n) hAlpha i j)).toReal =
      (n : ℝ) * ((fourEndpointOverlapSize (phaseNat n) hAlpha i j : ℕ) : ℝ) /
        (2 : ℝ) ^ (((3 * fourEndpointOverlapSize (phaseNat n) hAlpha i j - 1) / 4 : ℕ)) := by
    rw [threeQuarterHighCellBase, ENNReal.toReal_div, ENNReal.toReal_mul,
      ENNReal.toReal_natCast, ENNReal.toReal_natCast, ENNReal.toReal_pow,
      ENNReal.toReal_ofNat]
  rw [htoReal]
  apply e625k_div_bound _ _ _ _ hnpos hLpos (by positivity)
  · exact le_trans (Nat.cast_le.mpr
      (fourEndpointOverlapSize_le_alpha (phaseNat n) hAlpha i j)) hphase
  · exact e625k_two_pow_budget_lower n hn hAlpha hseven hLpos i j


private lemma e625k_size_eq (alpha : Nat) (hAlpha : 5 < alpha) (i : Fin 4) :
    fourEndpointSize alpha hAlpha i = alpha - 2 - i.val := by
  unfold fourEndpointSize fourEndpointCoordinate fourDeficitCoordinate
  simp [fourDeficit]
  omega

private lemma e625k_upper_le_alpha (alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4) :
    fourEndpointUpperSize alpha hAlpha i j ≤ alpha := by
  have h := e625k_size_eq alpha hAlpha
  fin_cases i <;> fin_cases j <;>
    simp [fourEndpointUpperSize, h] <;> omega

private lemma e625k_one_le_upper (alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4) :
    1 ≤ fourEndpointUpperSize alpha hAlpha i j := by
  have h := e625k_size_eq alpha hAlpha
  fin_cases i <;> fin_cases j <;>
    simp [fourEndpointUpperSize, h] <;> omega

private lemma e625k_lower_eq_overlap (alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4) :
    fourEndpointLowerSize alpha hAlpha i j = fourEndpointOverlapSize alpha hAlpha i j := rfl

private lemma e625k_one_le_dist {i j : Fin 4} (hij : i ≠ j) :
    1 ≤ fourEndpointDistance i j := by
  rcases Nat.eq_zero_or_pos (fourEndpointDistance i j) with h | h
  · exact absurd (Fin.ext (Nat.eq_of_dist_eq_zero h)) hij
  · exact h

private lemma e625k_Q_le_rpow (n alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4) :
    fourEndpointQ n alpha hAlpha i j ≤
      (((n : ℝ) + 1) * ((fourEndpointUpperSize alpha hAlpha i j : ℕ) : ℝ) *
        (2 : ℝ) ^ (-((fourEndpointOverlapSize alpha hAlpha i j : ℕ) : ℝ)))
          ^ ((fourEndpointDistance i j : ℝ) / 2) := by
  set d := fourEndpointDistance i j with hd
  set U := fourEndpointUpperSize alpha hAlpha i j with hU
  set m := fourEndpointOverlapSize alpha hAlpha i j with hm
  have hUnn : (0 : ℝ) ≤ (U : ℝ) := Nat.cast_nonneg U
  have hApos : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hTwo : (0 : ℝ) ≤ (2 : ℝ) ^ (-(m : ℝ)) := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hsplit : (((n : ℝ) + 1) * (U : ℝ) * (2 : ℝ) ^ (-(m : ℝ))) ^ ((d : ℝ) / 2) =
      ((n : ℝ) + 1) ^ ((d : ℝ) / 2) * (U : ℝ) ^ ((d : ℝ) / 2) *
        ((2 : ℝ) ^ (-(m : ℝ))) ^ ((d : ℝ) / 2) := by
    rw [Real.mul_rpow (by positivity) hTwo, Real.mul_rpow hApos hUnn]
  have hB : Real.sqrt ((U.descFactorial d : ℕ) : ℝ) ≤ (U : ℝ) ^ ((d : ℝ) / 2) := by
    have h1 : ((U.descFactorial d : ℕ) : ℝ) ≤ (U : ℝ) ^ (d : ℕ) := by
      exact_mod_cast Nat.descFactorial_le_pow U d
    calc Real.sqrt ((U.descFactorial d : ℕ) : ℝ) ≤ Real.sqrt ((U : ℝ) ^ (d : ℕ)) :=
          Real.sqrt_le_sqrt h1
      _ = (U : ℝ) ^ ((d : ℝ) / 2) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (U : ℝ) d, ← Real.rpow_mul hUnn]
          ring_nf
  have hC : (2 : ℝ) ^ (-((d * m + d.choose 2 : ℕ) : ℝ) / 2) ≤
      ((2 : ℝ) ^ (-(m : ℝ))) ^ ((d : ℝ) / 2) := by
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
    push_cast
    have hch : (0 : ℝ) ≤ ((d.choose 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith [hch]
  have hAeq : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hfact : (1 : ℝ) ≤ ((d.factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero d)
  unfold fourEndpointQ
  rw [e625k_lower_eq_overlap alpha hAlpha i j, ← hm, hAeq, hsplit]
  have hApow : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ ((d : ℝ) / 2) :=
    Real.rpow_nonneg hApos _
  have hCpos : (0 : ℝ) ≤ (2 : ℝ) ^ (-((d * m + d.choose 2 : ℕ) : ℝ) / 2) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  calc ((n : ℝ) + 1) ^ ((d : ℝ) / 2) * Real.sqrt ((U.descFactorial d : ℕ) : ℝ) /
        ((d.factorial : ℕ) : ℝ) * (2 : ℝ) ^ (-((d * m + d.choose 2 : ℕ) : ℝ) / 2)
      ≤ ((n : ℝ) + 1) ^ ((d : ℝ) / 2) * Real.sqrt ((U.descFactorial d : ℕ) : ℝ) *
        (2 : ℝ) ^ (-((d * m + d.choose 2 : ℕ) : ℝ) / 2) := by
        apply mul_le_mul_of_nonneg_right _ hCpos
        rw [div_le_iff₀ (by linarith : (0:ℝ) < ((d.factorial : ℕ) : ℝ))]
        have hAS : (0:ℝ) ≤ ((n : ℝ) + 1) ^ ((d : ℝ) / 2) *
            Real.sqrt ((U.descFactorial d : ℕ) : ℝ) :=
          mul_nonneg hApow (Real.sqrt_nonneg _)
        nlinarith [mul_le_mul_of_nonneg_left hfact hAS]
    _ ≤ ((n : ℝ) + 1) ^ ((d : ℝ) / 2) * (U : ℝ) ^ ((d : ℝ) / 2) *
        ((2 : ℝ) ^ (-(m : ℝ))) ^ ((d : ℝ) / 2) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hB hApow) hC hCpos
        positivity


private lemma e625k_eight_le_exp_three : (8 : ℝ) ≤ Real.exp 3 := by
  have h : Real.exp 3 = Real.exp 1 * (Real.exp 1 * Real.exp 1) := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  nlinarith [Real.exp_one_gt_d9, Real.exp_pos 1, h]

private lemma e625k_X_le (n : ℕ) (hn : PhaseDomain n) (hAlpha : 5 < phaseNat n)
    (hL4 : Real.exp 4 ≤ logOrder n) (hphase : (phaseNat n : ℝ) ≤ 4 * logOrder n)
    (i j : Fin 4) :
    ((n : ℝ) + 1) * ((fourEndpointUpperSize (phaseNat n) hAlpha i j : ℕ) : ℝ) *
        (2 : ℝ) ^ (-((fourEndpointOverlapSize (phaseNat n) hAlpha i j : ℕ) : ℝ)) ≤
      logOrder n ^ 5 / (n : ℝ) := by
  have hLpos : 0 < logOrder n := lt_of_lt_of_le (Real.exp_pos 4) hL4
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1.le
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have h1 : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
  have h2 : ((fourEndpointUpperSize (phaseNat n) hAlpha i j : ℕ) : ℝ) ≤ 4 * logOrder n :=
    le_trans (Nat.cast_le.mpr (e625k_upper_le_alpha (phaseNat n) hAlpha i j)) hphase
  have h3 : (2 : ℝ) ^ (-((fourEndpointOverlapSize (phaseNat n) hAlpha i j : ℕ) : ℝ)) ≤
      Real.exp 5 * logOrder n ^ 2 / (n : ℝ) ^ 2 :=
    e625k_two_rpow_neg_overlap_upper n hn hAlpha hLpos i j
  have hE : 8 * Real.exp 5 ≤ logOrder n ^ 2 := by
    have h8 : Real.exp 4 * Real.exp 4 = Real.exp 5 * Real.exp 3 := by
      rw [← Real.exp_add, ← Real.exp_add]; norm_num
    nlinarith [e625k_eight_le_exp_three, Real.exp_pos 5, Real.exp_pos 4,
      mul_self_le_mul_self (Real.exp_pos 4).le hL4]
  calc ((n : ℝ) + 1) * ((fourEndpointUpperSize (phaseNat n) hAlpha i j : ℕ) : ℝ) *
        (2 : ℝ) ^ (-((fourEndpointOverlapSize (phaseNat n) hAlpha i j : ℕ) : ℝ))
      ≤ (2 * (n : ℝ)) * (4 * logOrder n) * (Real.exp 5 * logOrder n ^ 2 / (n : ℝ) ^ 2) := by
        gcongr
    _ = 8 * Real.exp 5 * logOrder n ^ 3 / (n : ℝ) := by
        field_simp
        ring
    _ ≤ logOrder n ^ 2 * logOrder n ^ 3 / (n : ℝ) := by
        gcongr
    _ = logOrder n ^ 5 / (n : ℝ) := by ring

private lemma e625k_Q_off_le (n : ℕ) (hn : PhaseDomain n) (hAlpha : 5 < phaseNat n)
    (hL4 : Real.exp 4 ≤ logOrder n) (hphase : (phaseNat n : ℝ) ≤ 4 * logOrder n)
    (hLn : logOrder n ^ 5 ≤ (n : ℝ)) {i j : Fin 4} (hij : i ≠ j) :
    fourEndpointQ n (phaseNat n) hAlpha i j ≤
      logOrder n ^ (5 / 2 : ℝ) / Real.sqrt n := by
  have hLpos : 0 < logOrder n := lt_of_lt_of_le (Real.exp_pos 4) hL4
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1.le
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hUpos : (0 : ℝ) < ((fourEndpointUpperSize (phaseNat n) hAlpha i j : ℕ) : ℝ) := by
    have := e625k_one_le_upper (phaseNat n) hAlpha i j
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  set X := ((n : ℝ) + 1) * ((fourEndpointUpperSize (phaseNat n) hAlpha i j : ℕ) : ℝ) *
    (2 : ℝ) ^ (-((fourEndpointOverlapSize (phaseNat n) hAlpha i j : ℕ) : ℝ)) with hX
  have hXpos : 0 < X := by
    rw [hX]
    have : (0 : ℝ) < (2 : ℝ) ^ (-((fourEndpointOverlapSize (phaseNat n) hAlpha i j : ℕ) : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    positivity
  have hXle : X ≤ logOrder n ^ 5 / (n : ℝ) := e625k_X_le n hn hAlpha hL4 hphase i j
  have hY1 : logOrder n ^ 5 / (n : ℝ) ≤ 1 := (div_le_one hnpos).mpr hLn
  have hX1 : X ≤ 1 := hXle.trans hY1
  have hd : 1 ≤ fourEndpointDistance i j := e625k_one_le_dist hij
  have hdR : (1 : ℝ) / 2 ≤ ((fourEndpointDistance i j : ℕ) : ℝ) / 2 := by
    have : (1 : ℝ) ≤ ((fourEndpointDistance i j : ℕ) : ℝ) := by exact_mod_cast hd
    linarith
  have hstep1 : X ^ (((fourEndpointDistance i j : ℕ) : ℝ) / 2) ≤ X ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hXpos hX1 hdR
  have hstep2 : X ^ ((1 : ℝ) / 2) ≤ (logOrder n ^ 5 / (n : ℝ)) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow hXpos.le hXle (by norm_num)
  have hval : (logOrder n ^ 5 / (n : ℝ)) ^ ((1 : ℝ) / 2) =
      logOrder n ^ (5 / 2 : ℝ) / Real.sqrt n := by
    rw [Real.div_rpow (by positivity) (le_of_lt hnpos)]
    congr 1
    · rw [← Real.rpow_natCast (logOrder n) 5, ← Real.rpow_mul hLpos.le]
      norm_num
    · rw [Real.sqrt_eq_rpow]
  calc fourEndpointQ n (phaseNat n) hAlpha i j
      ≤ X ^ (((fourEndpointDistance i j : ℕ) : ℝ) / 2) :=
        e625k_Q_le_rpow n (phaseNat n) hAlpha i j
    _ ≤ X ^ ((1 : ℝ) / 2) := hstep1
    _ ≤ (logOrder n ^ 5 / (n : ℝ)) ^ ((1 : ℝ) / 2) := hstep2
    _ = logOrder n ^ (5 / 2 : ℝ) / Real.sqrt n := hval


private lemma e625k_eventually_logOrder_pow_five_le :
    ∀ᶠ n : ℕ in atTop, logOrder n ^ 5 ≤ (n : ℝ) := by
  have hb := (isLittleO_log_rpow_atTop (r := (1 / 5 : ℝ)) (by norm_num)).bound
    (by norm_num : (0 : ℝ) < 1)
  have hnat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hb
  filter_upwards [hnat, eventually_gt_atTop 1] with n hn hn1
  have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1.le
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1'
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog, one_mul,
    abs_of_nonneg (Real.rpow_nonneg hnpos.le _)] at hn
  calc logOrder n ^ 5 ≤ ((n : ℝ) ^ (1 / 5 : ℝ)) ^ 5 := by
        exact pow_le_pow_left₀ hlog hn 5
    _ = (n : ℝ) := by
        rw [← Real.rpow_natCast ((n : ℝ) ^ (1 / 5 : ℝ)) 5, ← Real.rpow_mul hnpos.le]
        norm_num

private lemma e625k_Q_diag_one (n alpha : Nat) (hAlpha : 5 < alpha) (i : Fin 4) :
    fourEndpointQ n alpha hAlpha i i = 1 := by
  have hd : fourEndpointDistance i i = 0 := by simp [fourEndpointDistance, Nat.dist_self]
  unfold fourEndpointQ
  rw [hd]
  norm_num

private lemma e625k_one_add_two_ofReal (t : ℝ) (ht : 0 ≤ t) :
    (1 : ENNReal) + 2 * ENNReal.ofReal t = ENNReal.ofReal (1 + 2 * t) := by
  rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]

private lemma e625k_sum_four_le (f : Fin 4 → ENNReal) (i : Fin 4) (u v : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hdiag : f i ≤ ENNReal.ofReal u)
    (hoff : ∀ j : Fin 4, j ≠ i → f j ≤ ENNReal.ofReal v) :
    ∑ j : Fin 4, f j ≤ ENNReal.ofReal (u + 3 * v) := by
  have hpt : ∀ j : Fin 4, f j ≤ (if j = i then ENNReal.ofReal u else ENNReal.ofReal v) := by
    intro j
    by_cases h : j = i
    · subst h; simpa using hdiag
    · simpa [h] using hoff j h
  refine (Finset.sum_le_sum fun j _ => hpt j).trans ?_
  have hsum : (∑ j : Fin 4, (if j = i then ENNReal.ofReal u else ENNReal.ofReal v))
      = ENNReal.ofReal u + 3 * ENNReal.ofReal v := by
    fin_cases i <;> simp [Fin.sum_univ_four] <;> ring
  have hval : ENNReal.ofReal (u + 3 * v) = ENNReal.ofReal u + 3 * ENNReal.ofReal v := by
    rw [ENNReal.ofReal_add hu (by positivity),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_ofNat]
  rw [hsum, hval]

private lemma e625k_seven_le_exp_four : (7 : ℝ) ≤ Real.exp 4 := by
  have h := Real.add_one_le_exp (2 : ℝ)
  have h2 : Real.exp 4 = Real.exp 2 * Real.exp 2 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos 2]

/-- Along the canonical phase, the auxiliary fused endpoint row maximum differs
from one by at most the manuscript scale
`O ((log n)^(5/2) / sqrt n)`.  The proof argument for the phase lower bound is
kept explicit and quantified uniformly. -/
theorem eventually_fourEndpointFusedRowMax_le_one_add_logOrder_rpow_five_halves_div_sqrt :
    ∃ C : Real, 0 < C ∧
      ∀ᶠ n : Nat in atTop,
        ∀ hAlpha : 5 < phaseNat n,
          fourEndpointFusedRowMax n (phaseNat n) hAlpha ≤
            ENNReal.ofReal
              (1 + C * logOrder n ^ (5 / 2 : Real) / Real.sqrt n) := by
  refine ⟨32 * Real.exp 5 + 3, by positivity, ?_⟩
  filter_upwards [eventually_phaseDomain,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
    tendsto_logOrder_atTop.eventually_ge_atTop (Real.exp 4),
    e625k_eventually_logOrder_pow_five_le] with n hdom hphase hL4 hLn
  intro hAlpha
  have hLpos : 0 < logOrder n := lt_of_lt_of_le (Real.exp_pos 4) hL4
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdom.1.le
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = logOrder n ^ (5 / 2 : ℝ) / Real.sqrt n := ⟨_, rfl⟩
  have hgoalEq : (1 : ℝ) + (32 * Real.exp 5 + 3) * logOrder n ^ (5 / 2 : ℝ) / Real.sqrt n
      = 1 + (32 * Real.exp 5 + 3) * s := by rw [hs]; ring
  rw [hgoalEq]
  have hspos : 0 < s := by
    rw [hs]
    exact div_pos (Real.rpow_pos_of_pos hLpos _) hsqrt
  have hs1 : s ≤ 1 := by
    have hid : logOrder n ^ (5 / 2 : ℝ) = Real.sqrt (logOrder n ^ 5) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (logOrder n) 5, ← Real.rpow_mul hLpos.le]
      norm_num
    rw [hs, hid, div_le_one hsqrt]
    exact Real.sqrt_le_sqrt hLn
  have hseven : 7 ≤ phaseNat n := by
    have h7 : (7 : ℝ) ≤ (phaseNat n : ℝ) :=
      le_trans (le_trans e625k_seven_le_exp_four hL4) hphase.1
    exact_mod_cast h7
  have hbaseTop : ∀ i j : Fin 4,
      threeQuarterHighCellBase n
        (fourEndpointOverlapSize (phaseNat n) hAlpha i j) ≠ ⊤ := by
    intro i j
    rw [threeQuarterHighCellBase]
    exact ENNReal.div_ne_top
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) (ENNReal.natCast_ne_top _))
      (pow_ne_zero _ (by norm_num : (2 : ENNReal) ≠ 0))
  have hfac : ∀ i j : Fin 4,
      fourEndpointThreeQuarterDeficitFactor n (phaseNat n) hAlpha i j ≤
        ENNReal.ofReal (1 + 8 * Real.exp 5 * s) := by
    intro i j
    have hb := e625k_base_toReal_le n hdom hAlpha hseven hLpos hphase.2 i j
    have hnn : (0 : ℝ) ≤ (threeQuarterHighCellBase n
        (fourEndpointOverlapSize (phaseNat n) hAlpha i j)).toReal := ENNReal.toReal_nonneg
    have hrw : threeQuarterHighCellBase n
        (fourEndpointOverlapSize (phaseNat n) hAlpha i j) =
        ENNReal.ofReal (threeQuarterHighCellBase n
          (fourEndpointOverlapSize (phaseNat n) hAlpha i j)).toReal :=
      (ENNReal.ofReal_toReal (hbaseTop i j)).symm
    rw [fourEndpointThreeQuarterDeficitFactor, hrw, e625k_one_add_two_ofReal _ hnn]
    apply ENNReal.ofReal_le_ofReal
    rw [← hs] at hb
    linarith
  apply Finset.sup_le
  intro i _
  have hrow : fourEndpointFusedRowSum n (phaseNat n) hAlpha i ≤
      ENNReal.ofReal ((1 + 8 * Real.exp 5 * s) + 3 * ((1 + 8 * Real.exp 5 * s) * s)) := by
    rw [fourEndpointFusedRowSum]
    apply e625k_sum_four_le _ i _ _ (by positivity) (by positivity)
    · rw [fourEndpointFusedKernel, e625k_Q_diag_one, ENNReal.ofReal_one, mul_one]
      exact hfac i i
    · intro j hj
      rw [fourEndpointFusedKernel]
      have hQ : fourEndpointQ n (phaseNat n) hAlpha i j ≤ s := by
        rw [hs]
        exact e625k_Q_off_le n hdom hAlpha hL4 hphase.2 hLn (Ne.symm hj)
      calc fourEndpointThreeQuarterDeficitFactor n (phaseNat n) hAlpha i j *
            ENNReal.ofReal (fourEndpointQ n (phaseNat n) hAlpha i j)
          ≤ ENNReal.ofReal (1 + 8 * Real.exp 5 * s) * ENNReal.ofReal s :=
            mul_le_mul' (hfac i j) (ENNReal.ofReal_le_ofReal hQ)
        _ = ENNReal.ofReal ((1 + 8 * Real.exp 5 * s) * s) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
  refine hrow.trans (ENNReal.ofReal_le_ofReal ?_)
  have hexp : (0 : ℝ) < Real.exp 5 := Real.exp_pos 5
  have hsq : s * s ≤ s := by nlinarith
  nlinarith [hspos, hs1, hexp, hsq]

end

end Erdos625
