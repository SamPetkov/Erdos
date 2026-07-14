import Erdos625.Section11EventAssembly
import Erdos625.PhaseExpansion

/-!
# Section 11: asymptotic and probability assembly

This module contains the three generic closing lemmas used after the
manuscript's substantive chromatic and cochromatic estimates have been proved.
They preserve full-sequence `atTop` quantifiers and the explicit constant.

No theorem below supplies the Section 5 root separation or the Section 10
cochromatic tail: those remain hypotheses to be instantiated by the preceding
formalization layers.
-/

namespace Erdos625

open Filter MeasureTheory Set Asymptotics

/-- If each of two measurable events has probability tending to one along the
full sequence, then their intersection has probability tending to one.  The
sample type may depend on `n`; no independence hypothesis appears. -/
theorem tendsto_measure_inter_one
    {Omega : ℕ → Type*}
    [∀ n, MeasurableSpace (Omega n)]
    (mu : ∀ n, Measure (Omega n))
    [∀ n, IsProbabilityMeasure (mu n)]
    (A B : ∀ n, Set (Omega n))
    (hAmeas : ∀ n, MeasurableSet (A n))
    (hBmeas : ∀ n, MeasurableSet (B n))
    (hA : Tendsto (fun n ↦ mu n (A n)) atTop (nhds 1))
    (hB : Tendsto (fun n ↦ mu n (B n)) atTop (nhds 1)) :
    Tendsto (fun n ↦ mu n (A n ∩ B n)) atTop (nhds 1) := by
  have hAReal :
      Tendsto (fun n ↦ (mu n (A n)).toReal) atTop (nhds (1 : ℝ)) := by
    simpa using
      (ENNReal.tendsto_toReal_iff
        (fun n ↦ measure_ne_top (mu n) (A n)) ENNReal.one_ne_top).mpr hA
  have hBReal :
      Tendsto (fun n ↦ (mu n (B n)).toReal) atTop (nhds (1 : ℝ)) := by
    simpa using
      (ENNReal.tendsto_toReal_iff
        (fun n ↦ measure_ne_top (mu n) (B n)) ENNReal.one_ne_top).mpr hB
  have hLower : ∀ n,
      (mu n (A n)).toReal + (mu n (B n)).toReal - 1 ≤
        (mu n (A n ∩ B n)).toReal := by
    intro n
    have hIdentity := measure_union_add_inter (μ := mu n) (A n) (hBmeas n)
    have hIdentityReal := congrArg ENNReal.toReal hIdentity
    rw [ENNReal.toReal_add (measure_ne_top (mu n) (A n ∪ B n))
          (measure_ne_top (mu n) (A n ∩ B n)),
        ENNReal.toReal_add (measure_ne_top (mu n) (A n))
          (measure_ne_top (mu n) (B n))] at hIdentityReal
    have hUnion : mu n (A n ∪ B n) ≤ 1 := by
      calc
        mu n (A n ∪ B n) ≤
            mu n (A n ∪ B n) + mu n (A n ∪ B n)ᶜ :=
          self_le_add_right _ _
        _ = mu n Set.univ :=
          measure_add_measure_compl ((hAmeas n).union (hBmeas n))
        _ = 1 := measure_univ
    have hUnionReal : (mu n (A n ∪ B n)).toReal ≤ 1 := by
      simpa using
        (ENNReal.toReal_le_toReal (measure_ne_top (mu n) (A n ∪ B n))
          ENNReal.one_ne_top).mpr hUnion
    linarith
  have hUpper : ∀ n, (mu n (A n ∩ B n)).toReal ≤ 1 := by
    intro n
    have hMeasure : mu n (A n ∩ B n) ≤ 1 := by
      calc
        mu n (A n ∩ B n) ≤ mu n Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    simpa using
      (ENNReal.toReal_le_toReal (measure_ne_top (mu n) (A n ∩ B n))
        ENNReal.one_ne_top).mpr hMeasure
  have hLowerTendsto :
      Tendsto
        (fun n ↦ (mu n (A n)).toReal + (mu n (B n)).toReal - 1)
        atTop (nhds (1 : ℝ)) := by
    convert (hAReal.add hBReal).sub_const 1 using 1
    norm_num
  have hInterReal :
      Tendsto (fun n ↦ (mu n (A n ∩ B n)).toReal)
        atTop (nhds (1 : ℝ)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hLowerTendsto
      tendsto_const_nhds (Filter.Eventually.of_forall hLower)
      (Filter.Eventually.of_forall hUpper)
  exact
    (ENNReal.tendsto_toReal_iff
      (fun n ↦ measure_ne_top (mu n) (A n ∩ B n)) ENNReal.one_ne_top).mp
      (by simpa using hInterReal)

/-- The manuscript's unscaled `n / (ln n)^3` factor. -/
noncomputable def baseScale (n : ℕ) : ℝ :=
  (n : ℝ) / (Real.log (n : ℝ)) ^ 3

/-- Section 5's root separation, together with Section 10's little-o
cochromatic amplification loss, eventually dominates the exact factor-two
reduced constant of (11.2).  The `+1` retains the strict integer chromatic
event used in Section 11. -/
theorem eventually_explicit_gap_threshold
    (kChi kCo : ℕ → ℕ) (a rho : ℕ → ℝ)
    (hrho : Tendsto rho atTop (nhds 0))
    (ha : a =o[atTop] baseScale)
    (hroot : ∀ᶠ n in atTop,
      (((Real.log 2) ^ 2 / 16 * Real.log (200 / 153 : ℝ)) - rho n) *
          baseScale n ≤
        (kChi n : ℝ) - (kCo n : ℝ)) :
    ∀ᶠ n in atTop,
      ((Real.log 2) ^ 2 / 32 * Real.log (200 / 153 : ℝ)) *
          baseScale n ≤
        ((kChi n + 1 : ℕ) : ℝ) - ((kCo n : ℝ) + a n) := by
  let c : ℝ :=
    (Real.log 2) ^ 2 / 32 * Real.log (200 / 153 : ℝ)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hLeading :
      (Real.log 2) ^ 2 / 16 * Real.log (200 / 153 : ℝ) = 2 * c := by
    dsimp [c]
    ring
  have hRho : ∀ᶠ n in atTop, |rho n| < c / 4 := by
    have hIoo : Set.Ioo (-(c / 4)) (c / 4) ∈ nhds (0 : ℝ) :=
      Ioo_mem_nhds (neg_lt_zero.mpr (div_pos hc (by norm_num)))
        (div_pos hc (by norm_num))
    filter_upwards [hrho.eventually hIoo] with n hn
    exact abs_lt.mpr hn
  have hASmall : ∀ᶠ n in atTop,
      ‖a n‖ ≤ (c / 4) * ‖baseScale n‖ :=
    ha.bound (by positivity)
  have hBasePos : ∀ᶠ n in atTop, 0 < baseScale n := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    have hnReal : (1 : ℝ) < n := by exact_mod_cast hn
    simp only [baseScale]
    exact div_pos (Nat.cast_pos.mpr (by omega))
      (pow_pos (Real.log_pos hnReal) 3)
  filter_upwards [hroot, hRho, hASmall, hBasePos] with n hRoot hRhoN hAN hBase
  rw [hLeading] at hRoot
  have hRhoUpper : rho n ≤ c / 4 :=
    (le_abs_self (rho n)).trans hRhoN.le
  have hRhoMul : rho n * baseScale n ≤ (c / 4) * baseScale n :=
    mul_le_mul_of_nonneg_right hRhoUpper hBase.le
  have hAUpper : a n ≤ (c / 4) * baseScale n := by
    calc
      a n ≤ |a n| := le_abs_self _
      _ = ‖a n‖ := (Real.norm_eq_abs _).symm
      _ ≤ (c / 4) * ‖baseScale n‖ := hAN
      _ = (c / 4) * baseScale n := by
        rw [Real.norm_eq_abs, abs_of_pos hBase]
  change c * baseScale n ≤
    ((kChi n + 1 : ℕ) : ℝ) - ((kCo n : ℝ) + a n)
  norm_num only [Nat.cast_add, Nat.cast_one]
  nlinarith

/-- The exact lower-bound scale in (11.2) tends to infinity along all natural
numbers, which is the deterministic implication used for (11.3). -/
theorem tendsto_explicit_gap_scale_atTop :
    Tendsto
      (fun n : ℕ ↦
        ((Real.log 2) ^ 2 / 32 * Real.log (200 / 153 : ℝ)) * (n : ℝ) /
          (Real.log (n : ℝ)) ^ 3)
      atTop atTop := by
  have hLimit :
      Tendsto (fun n : ℕ ↦ (n : ℝ) / (Real.log n) ^ 3)
        atTop atTop := by
    suffices hLog :
        Tendsto (fun u : ℝ ↦ Real.exp u / u ^ 3) atTop atTop by
      have h := hLog.comp
        (Real.tendsto_log_atTop.comp
          (tendsto_natCast_atTop_atTop :
            Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop))
      exact h.congr' (by
        filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
        simp only [Function.comp_apply]
        rw [Real.exp_log (Nat.cast_pos.mpr hn)])
    exact Real.tendsto_exp_div_pow_atTop 3
  simpa only [mul_div_assoc] using
    hLimit.const_mul_atTop (by positivity :
      0 < (Real.log 2) ^ 2 / 32 * Real.log (200 / 153 : ℝ))

end Erdos625
