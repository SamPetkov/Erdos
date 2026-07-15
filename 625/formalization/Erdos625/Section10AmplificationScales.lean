import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Asymptotic scales in rare-event amplification

This file isolates the deterministic asymptotic transformations in manuscript
Section 10.  The functions are exactly those in (10.10)--(10.12); no
probabilistic seed or leftover-colouring assertion is introduced here.
-/

open Filter
open scoped Topology

namespace Erdos625

/-- The deterministic scale `B_n = n / (log n)^4` from (10.10). -/
noncomputable def amplificationBase (n : ℕ) : ℝ :=
  (n : ℝ) / (Real.log (n : ℝ)) ^ 4

/-- The deterministic, genuinely growing choice `r_n = sqrt B_n`. -/
noncomputable def amplificationRadius (n : ℕ) : ℝ :=
  Real.sqrt (amplificationBase n)

/-- The unscaled target gap `n / (log n)^3`. -/
noncomputable def gapBase (n : ℕ) : ℝ :=
  (n : ℝ) / (Real.log (n : ℝ)) ^ 3

/-- The complete deterministic amplification loss from (10.12). -/
noncomputable def amplificationError
    (C : ℝ) (Lambda : ℕ → ℝ) (n : ℕ) : ℝ :=
  C *
    (Real.sqrt ((n : ℝ) * Lambda n) / Real.log (n : ℝ) +
      Real.sqrt ((n : ℝ) * amplificationRadius n) /
        Real.log (n : ℝ) +
      (n : ℝ) ^ (1 / 3 : ℝ) + 1)

/-- The deterministic radius used in the manuscript tends to infinity. -/
theorem amplificationRadius_tendsto_atTop :
    Tendsto amplificationRadius atTop atTop := by
  have hRatioZero :
      Tendsto (fun x : ℝ ↦ Real.log x ^ 4 / x) atTop (𝓝 0) := by
    simpa using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 4 one_ne_zero)
  have hRatioPos :
      ∀ᶠ x : ℝ in atTop, 0 < Real.log x ^ 4 / x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (pow_pos (Real.log_pos hx) 4) (by linarith)
  have hRatioWithin :
      Tendsto (fun x : ℝ ↦ Real.log x ^ 4 / x) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hRatioZero, hRatioPos⟩
  have hBaseReal :
      Tendsto (fun x : ℝ ↦ x / Real.log x ^ 4) atTop atTop := by
    have hInv := hRatioWithin.inv_tendsto_nhdsGT_zero
    change Tendsto
      (fun x : ℝ ↦ (Real.log x ^ 4 / x)⁻¹) atTop atTop at hInv
    simpa only [inv_div] using hInv
  have hBaseNat : Tendsto amplificationBase atTop atTop := by
    have hComp :=
      hBaseReal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    change Tendsto
      (fun n : ℕ ↦ (n : ℝ) / Real.log (n : ℝ) ^ 4) atTop atTop at hComp
    change Tendsto
      (fun n : ℕ ↦ (n : ℝ) / Real.log (n : ℝ) ^ 4) atTop atTop
    exact hComp
  exact Real.tendsto_sqrt_atTop.comp hBaseNat

/-- The first implication in (10.11): a nonnegative seed exponent
`Λ_n = o(n / (log n)^4)` contributes only `o(n / (log n)^3)` after the
square-root amplification transform. -/
theorem sqrt_seedTerm_isLittleO
    (Lambda : ℕ → ℝ)
    (hLambdaNonneg : ∀ᶠ n in atTop, 0 ≤ Lambda n)
    (hLambda :
      (fun n : ℕ ↦ Lambda n) =o[atTop]
        (fun n : ℕ ↦ (n : ℝ) / (Real.log (n : ℝ)) ^ 4)) :
    (fun n : ℕ ↦
        Real.sqrt ((n : ℝ) * Lambda n) / Real.log (n : ℝ)) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ) / (Real.log (n : ℝ)) ^ 3) := by
  refine Asymptotics.IsLittleO.of_bound fun c hc ↦ ?_
  have hLambdaBound := hLambda.bound (sq_pos_of_pos hc)
  have hNatLarge : ∀ᶠ n : ℕ in atTop, (1 : ℝ) < (n : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_gt_atTop (1 : ℝ))
  filter_upwards [hLambdaNonneg, hLambdaBound, hNatLarge] with
      n hnLambda hnBound hnLarge
  have hnPos : 0 < (n : ℝ) := by linarith
  have hlogPos : 0 < Real.log (n : ℝ) := Real.log_pos hnLarge
  have hbasePos :
      0 < (n : ℝ) / Real.log (n : ℝ) ^ 4 :=
    div_pos hnPos (pow_pos hlogPos 4)
  rw [Real.norm_eq_abs, abs_of_nonneg hnLambda,
    Real.norm_eq_abs, abs_of_pos hbasePos] at hnBound
  have hProductBound :
      (n : ℝ) * Lambda n ≤
        (c * (n : ℝ) / Real.log (n : ℝ) ^ 2) ^ 2 := by
    calc
      (n : ℝ) * Lambda n ≤
          (n : ℝ) *
            (c ^ 2 * ((n : ℝ) / Real.log (n : ℝ) ^ 4)) :=
        mul_le_mul_of_nonneg_left hnBound hnPos.le
      _ = (c * (n : ℝ) / Real.log (n : ℝ) ^ 2) ^ 2 := by
        field_simp [ne_of_gt hlogPos]
  have hSqrtBound :
      Real.sqrt ((n : ℝ) * Lambda n) ≤
        c * (n : ℝ) / Real.log (n : ℝ) ^ 2 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, hProductBound⟩
  have hDivBound :
      Real.sqrt ((n : ℝ) * Lambda n) / Real.log (n : ℝ) ≤
        c * ((n : ℝ) / Real.log (n : ℝ) ^ 3) := by
    have h := (div_le_div_iff_of_pos_right hlogPos).mpr hSqrtBound
    calc
      Real.sqrt ((n : ℝ) * Lambda n) / Real.log (n : ℝ) ≤
          (c * (n : ℝ) / Real.log (n : ℝ) ^ 2) /
            Real.log (n : ℝ) := h
      _ = c * ((n : ℝ) / Real.log (n : ℝ) ^ 3) := by
        field_simp [ne_of_gt hlogPos]
  rw [Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) hlogPos.le),
    Real.norm_eq_abs,
    abs_of_pos (div_pos hnPos (pow_pos hlogPos 3))]
  exact hDivBound

/-- The second implication in (10.11), for the exact growing deterministic
radius chosen in (10.10). -/
theorem sqrt_radiusTerm_isLittleO :
    (fun n : ℕ =>
        Real.sqrt ((n : ℝ) * amplificationRadius n) /
          Real.log (n : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ) / (Real.log (n : ℝ)) ^ 3) := by
  suffices h_simp :
      Tendsto (fun n : ℕ => Real.log n / (n : ℝ) ^ (1 / 4 : ℝ))
        atTop (nhds 0) by
    rw [Asymptotics.isLittleO_iff_tendsto']
    · refine h_simp.congr' ?_
      filter_upwards [eventually_gt_atTop 1] with n hn
      unfold amplificationRadius amplificationBase
      norm_num [Real.sqrt_eq_rpow,
        ← Real.rpow_mul (Nat.cast_nonneg _),
        ← Real.rpow_neg (Nat.cast_nonneg _)]
      ring_nf
      rw [Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul (by positivity)]
      ring_nf
      rw [Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
      ring_nf
      field_simp
      norm_num [sq, mul_assoc,
        ← Real.rpow_add (by positivity : 0 < (n : ℝ))]
    · filter_upwards [eventually_gt_atTop 1] with n hn h
      exact absurd h <| ne_of_gt <|
        div_pos (Nat.cast_pos.mpr <| pos_of_gt hn) <|
          pow_pos (Real.log_pos <| Nat.one_lt_cast.mpr hn) _
  have hreal :
      Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 4 : ℝ))
        atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop
      (r := (1 / 4 : ℝ)) (by norm_num)).tendsto_div_nhds_zero
  exact hreal.comp tendsto_natCast_atTop_atTop

/-- The real cube-root contribution in (10.11), using real exponentiation. -/
theorem realCubeRoot_isLittleO :
    (fun n : ℕ => (n : ℝ) ^ (1 / 3 : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ) / (Real.log (n : ℝ)) ^ 3) := by
  have h_log :
      (fun x : ℝ => (Real.log x) ^ 3) =o[atTop]
        (fun x : ℝ => x ^ (2 / 3 : ℝ)) := by
    convert isLittleO_log_rpow_rpow_atTop
      (3 : ℝ) (by norm_num : (0 : ℝ) < 2 / 3) using 1
    norm_cast
  rw [Asymptotics.isLittleO_iff_tendsto'] at * <;> norm_num at *
  · convert h_log.comp tendsto_natCast_atTop_atTop using 2
    norm_num
    ring_nf
    rw [show (2 / 3 : ℝ) = 1 - 1 / 3 by norm_num, Real.rpow_sub'] <;>
      norm_num
    ring
  · exact ⟨1, fun x hx hx' => absurd hx' <| by positivity⟩
  · exact ⟨2, by rintro n hn (rfl | rfl | hn) <;> norm_cast at hn⟩

/-- The constant contribution in (10.12) is negligible on the gap scale. -/
theorem one_isLittleO_gapScale :
    (fun _n : ℕ => (1 : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ) / (Real.log (n : ℝ)) ^ 3) := by
  have hreal :
      Tendsto (fun x : ℝ => x / (Real.log x) ^ 3) atTop atTop := by
    have h0 :
        Tendsto (fun x : ℝ => (Real.log x) ^ 3 / x) atTop (nhds 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 3 one_ne_zero
    have h1 :
        Tendsto (fun x : ℝ => (Real.log x) ^ 3 / x) atTop
          (nhdsWithin 0 (Set.Ioi 0)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h0 ?_
      filter_upwards [eventually_gt_atTop 1] with x hx
      have hlog : 0 < Real.log x := Real.log_pos hx
      rw [Set.mem_Ioi]
      positivity
    have h2 := h1.inv_tendsto_nhdsGT_zero
    refine h2.congr ?_
    intro x
    simp [inv_div]
  rw [Asymptotics.isLittleO_const_left]
  right
  have hnat :
      Tendsto (fun n : ℕ => (n : ℝ) / (Real.log (n : ℝ)) ^ 3)
        atTop atTop :=
    hreal.comp tendsto_natCast_atTop_atTop
  refine Tendsto.congr (fun n => ?_) (tendsto_norm_atTop_atTop.comp hnat)
  simp [Function.comp]

/-- A nonnegative seed exponent `Lambda_n = o(n/(log n)^4)` makes the full
deterministic amplification loss negligible on the target gap scale. -/
theorem amplificationError_isLittleO_gapBase
    (C : ℝ) (Lambda : ℕ → ℝ)
    (hLambdaNonneg : ∀ᶠ n in atTop, 0 ≤ Lambda n)
    (hLambda : Lambda =o[atTop] amplificationBase) :
    amplificationError C Lambda =o[atTop] gapBase := by
  change (fun n : ℕ ↦ Lambda n) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ) / Real.log (n : ℝ) ^ 4) at hLambda
  have hSeed :
      (fun n : ℕ ↦
        Real.sqrt ((n : ℝ) * Lambda n) / Real.log (n : ℝ)) =o[atTop]
        gapBase := by
    change (fun n : ℕ ↦
        Real.sqrt ((n : ℝ) * Lambda n) / Real.log (n : ℝ)) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ) / Real.log (n : ℝ) ^ 3)
    exact sqrt_seedTerm_isLittleO Lambda hLambdaNonneg hLambda
  have hRadius :
      (fun n : ℕ ↦
        Real.sqrt ((n : ℝ) * amplificationRadius n) /
          Real.log (n : ℝ)) =o[atTop]
        gapBase := by
    change (fun n : ℕ ↦
        Real.sqrt ((n : ℝ) * amplificationRadius n) /
          Real.log (n : ℝ)) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ) / Real.log (n : ℝ) ^ 3)
    exact sqrt_radiusTerm_isLittleO
  have hCubeRoot :
      (fun n : ℕ ↦ (n : ℝ) ^ (1 / 3 : ℝ)) =o[atTop] gapBase := by
    change (fun n : ℕ ↦ (n : ℝ) ^ (1 / 3 : ℝ)) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ) / Real.log (n : ℝ) ^ 3)
    exact realCubeRoot_isLittleO
  have hOne :
      (fun _n : ℕ ↦ (1 : ℝ)) =o[atTop] gapBase := by
    change (fun _n : ℕ ↦ (1 : ℝ)) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ) / Real.log (n : ℝ) ^ 3)
    exact one_isLittleO_gapScale
  have hSum :
      (fun n : ℕ ↦
        Real.sqrt ((n : ℝ) * Lambda n) / Real.log (n : ℝ) +
          Real.sqrt ((n : ℝ) * amplificationRadius n) /
            Real.log (n : ℝ) +
          (n : ℝ) ^ (1 / 3 : ℝ) + 1) =o[atTop]
        gapBase :=
    ((hSeed.add hRadius).add hCubeRoot).add hOne
  change (fun n : ℕ ↦ C *
      (Real.sqrt ((n : ℝ) * Lambda n) / Real.log (n : ℝ) +
        Real.sqrt ((n : ℝ) * amplificationRadius n) /
          Real.log (n : ℝ) +
        (n : ℝ) ^ (1 / 3 : ℝ) + 1)) =o[atTop] gapBase
  exact hSum.const_mul_left C

#print axioms amplificationRadius_tendsto_atTop
#print axioms sqrt_seedTerm_isLittleO
#print axioms sqrt_radiusTerm_isLittleO
#print axioms realCubeRoot_isLittleO
#print axioms one_isLittleO_gapScale
#print axioms amplificationError_isLittleO_gapBase

end Erdos625
