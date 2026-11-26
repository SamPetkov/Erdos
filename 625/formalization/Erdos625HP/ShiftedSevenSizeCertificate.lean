import Erdos625HP.FourSizeSharpCertificate
import Erdos625HP.TwoSidedAssembly
import Erdos625.ExtendedGaussianTilt

/-!
# Shifted seven-size `[0.080, 0.086]` certificate, critical phase `x₀`, and sharp `1/4` assembly

This module kernel-checks the analytic and assembly backbone of the upgraded
two-sided `[0.080, 0.086]` Main Theorem and `(log 2)³ / 4` (`1/4` in `log₂ n`)
Sharp Asymptotic Theorem:

1. **Gaussian shift equivariance (`Lemma 3.2(iii)`, eq. `(3.13)`):**
   * `partitionFn_shiftSupportOne` and `dualValue_shiftSupportOne`: shifting any
     support `S ⊆ ℤ` by `+1` shifts `𝓕_{S+1}(T + 1) = 𝓕_S(T) - (log 2)(T + 1/2)`.
   * `dualValue_Sge1_sub_S17_eq_phaseGain7_add_one`: comparing `S_{1,7} = {2..8}`
     against `S_{≥ 1}` at `T_δ` equals `A₇(1 + δ)`.
2. **Six-cell rational certificate for `A₇`, continuity, nonconstancy, and `[0.080, 0.086]`
   (`Lemma 5.1`, `Phase Refinement`, and `Main Theorem` constants):**
   * `log_391_div_200_lt_phaseGain7`: `log (391 / 200) < A₇(td)` for every
     `td ∈ [0, 207 / 200]`.
   * `continuousOn_phaseGain7` and `phaseGain7_nonconstant`: `A₇` is continuous on
     `[0, 207 / 200]` and strictly nonconstant (`A₇(207/200) < 0.672 < 0.689 < A₇(7/200)`).
   * `lowerPhaseCoeff7_gt_0080` and `upperPhaseCoeff7_lt_0086`: uniformly across
     all `n : ℕ`, the shifted phase `td_n = δ_n + 1_{δ_n < 7/200}` satisfies
     `0.080 < lowerPhaseCoeff7 td_n` and `upperPhaseCoeff7 td_n < 0.086`.
3. **Uniform support-limit convergence (`Lemma 3.2(iii)`):**
   * `tendstoUniformlyOn_dualValue_S0M_Sge1`: as `M → ∞`, `𝓕_{S_{0,M}} → 𝓕_{S_{≥ 1}}`
     uniformly on `[11/4, 4]` (covering `[T_1, T_0]`), with an explicit exponential tail bound.
4. **Critical phase `x₀ ∈ (0.0290, 0.0291)` (`Lemma 5.2(i)`):**
   * `continuousOn_phiInf`, `strictAntiOn_phiInf`, `phiInf_0290_pos`,
     `phiInf_0291_neg`, and `existsUnique_criticalPhase_x0`: `φ_∞` in `(0.1)` is
     continuous and strictly decreasing on `[0, 207 / 200]` with a unique zero
     `x₀`, certified to satisfy `0.0290 < x₀ < 0.0291`.
5. **Conditional assembly of `[0.080, 0.086]` and `(log 2)³ / 4` (`Section 9`):**
   * `shifted_twoSided_phase_and_0080_0086_gap_tendsto_one` and
   * `sharp_constant_quarter_along_subsequence_of_window_thresholds`.
-/

namespace Erdos625HP

open Erdos625 FiveSizeEntropyGap FiveSizePhaseGainSharp FiveSizePhaseGainCertificate
open Filter MeasureTheory Set
open scoped BigOperators Topology

set_option autoImplicit false

noncomputable section

/-! ## 1. Supports, shifted phase, and Gaussian shift equivariance -/

/-- Support `S_{≥ 0} = {i ∈ ℤ : 0 ≤ i}`. -/
def Sge0 : Set ℤ := {i : ℤ | 0 ≤ i}

/-- Support `S_{≥ 1} = {i ∈ ℤ : 1 ≤ i}`. -/
def Sge1 : Set ℤ := {i : ℤ | 1 ≤ i}

/-- Seven-size unshifted support `S_{0,7} = {1, 2, 3, 4, 5, 6, 7}`. -/
def S07 : Set ℤ := {1, 2, 3, 4, 5, 6, 7}

/-- Seven-size shifted support `S_{1,7} = {2, 3, 4, 5, 6, 7, 8}`. -/
def S17 : Set ℤ := {2, 3, 4, 5, 6, 7, 8}

/-- Finite `M`-size support `S_{0,M} = {1, …, M}`. -/
def S0M (M : ℕ) : Set ℤ := {i : ℤ | 1 ≤ i ∧ i ≤ (M : ℤ)}

/-- `S_{0,7}` as a `Finset ℤ`. -/
def F07 : Finset ℤ := {1, 2, 3, 4, 5, 6, 7}

/-- `{0, …, 7}` as a `Finset ℤ` (used for the upper nonconstancy bound). -/
def F07WithZero : Finset ℤ := {0, 1, 2, 3, 4, 5, 6, 7}

/-- `{1, …, 9}` as a `Finset ℤ` (used for the critical-phase bracket on `x₀`). -/
def F09 : Finset ℤ := {1, 2, 3, 4, 5, 6, 7, 8, 9}

/-- Boundary cutoff `δ_* = 7 / 200 = 0.035`. -/
def deltaStar : ℝ := 7 / 200

/-- Boundary shift `m_n = 1_{δ < 7/200} ∈ {0, 1}`. -/
def boundaryShift (delta : ℝ) : ℕ := by
  classical
  exact if delta < deltaStar then 1 else 0

/-- Shifted phase `δ̃ = δ + 1_{δ < 7/200}`. -/
def shiftedPhase (delta : ℝ) : ℝ :=
  delta + (boundaryShift delta : ℝ)

theorem shiftedPhase_mem_Icc_deltaStar {delta : ℝ} (hd : delta ∈ Set.Ico (0 : ℝ) 1) :
    shiftedPhase delta ∈ Set.Icc deltaStar (1 + deltaStar) := by
  unfold shiftedPhase boundaryShift deltaStar
  by_cases h : delta < 7 / 200
  · simp only [h, ↓reduceIte, Nat.cast_one]
    exact ⟨by linarith [hd.1], by linarith⟩
  · simp only [h, ↓reduceIte, Nat.cast_zero, add_zero]
    exact ⟨by linarith, by linarith [hd.2]⟩

theorem shiftedPhase_mem_Icc_wide {delta : ℝ} (hd : delta ∈ Set.Ico (0 : ℝ) 1) :
    shiftedPhase delta ∈ Set.Icc (0 : ℝ) (207 / 200) := by
  have h := shiftedPhase_mem_Icc_deltaStar hd
  unfold deltaStar at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- Seven-size phase gain `A₇(δ̃) = log 2 - 𝓕_{S_{≥ 0}}(T_{δ̃}) + 𝓕_{S_{0,7}}(T_{δ̃})`. -/
def phaseGain7 (td : ℝ) : ℝ :=
  Real.log 2 - dualValue Sge0 (phaseTarget td) + dualValue S07 (phaseTarget td)

/-- Shifted seven-size lower phase coefficient `(log 2)² / 4 · A₇(δ̃)`. -/
def lowerPhaseCoeff7 (td : ℝ) : ℝ :=
  (Real.log 2) ^ 2 / 4 * phaseGain7 td

/-- Shifted seven-size upper phase coefficient `(log 2)² / 4 · (2 log 2 - A₇(δ̃))`. -/
def upperPhaseCoeff7 (td : ℝ) : ℝ :=
  (Real.log 2) ^ 2 / 4 * (2 * Real.log 2 - phaseGain7 td)

/-- Exact natural-log asymptotic constant `(log 2)³ / 4` (`= 1/4` in `log₂ n`). -/
def sharpGapConstant : ℝ :=
  (Real.log 2) ^ 3 / 4

theorem sharpGapConstant_div_log_two_cube :
    sharpGapConstant / (Real.log 2) ^ 3 = 1 / 4 := by
  have hq : (Real.log 2) ^ 3 ≠ 0 := pow_ne_zero 3 (Real.log_pos one_lt_two).ne'
  unfold sharpGapConstant
  field_simp [hq]

theorem lowerPhaseCoeff7_add_upperPhaseCoeff7 (td : ℝ) :
    lowerPhaseCoeff7 td + upperPhaseCoeff7 td = (Real.log 2) ^ 3 / 2 := by
  unfold lowerPhaseCoeff7 upperPhaseCoeff7
  ring

/-- Unit upward translation `S + 1 = {j ∈ ℤ : j - 1 ∈ S}`. -/
def shiftSupportOne (S : Set ℤ) : Set ℤ := {j : ℤ | j - 1 ∈ S}

theorem shiftSupportOne_Splus : shiftSupportOne Splus = Sge0 := by
  ext j; simp only [shiftSupportOne, Splus, Sge0, Set.mem_setOf_eq]; omega

theorem shiftSupportOne_Sge0 : shiftSupportOne Sge0 = Sge1 := by
  ext j; simp only [shiftSupportOne, Sge0, Sge1, Set.mem_setOf_eq]; omega

theorem shiftSupportOne_S07 : shiftSupportOne S07 = S17 := by
  ext j
  simp only [shiftSupportOne, S07, S17, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  omega

theorem gaussWeight_add_one (lambda : ℝ) (i : ℤ) :
    gaussWeight lambda (i + 1) =
      Real.exp (lambda - Real.log 2 / 2) * gaussWeight (lambda - Real.log 2) i := by
  unfold gaussWeight
  rw [← Real.exp_add]
  push_cast
  congr 1
  ring

/-- **Gaussian partition shift identity (`Lemma 3.2(iii)`):**
`Z_{S+1}(λ) = exp(λ - (log 2)/2) · Z_S(λ - log 2)`. -/
theorem partitionFn_shiftSupportOne (S : Set ℤ) (lambda : ℝ) :
    partitionFn (shiftSupportOne S) lambda =
      Real.exp (lambda - Real.log 2 / 2) * partitionFn S (lambda - Real.log 2) := by
  unfold partitionFn
  let e : shiftSupportOne S ≃ S :=
    { toFun := fun j ↦ ⟨j.1 - 1, j.2⟩
      invFun := fun i ↦ ⟨i.1 + 1, by simp [shiftSupportOne]⟩
      left_inv := fun j ↦ Subtype.ext (by dsimp only; omega)
      right_inv := fun i ↦ Subtype.ext (by dsimp only; omega) }
  rw [← e.symm.tsum_eq]
  have hterm : ∀ i : S,
      gaussWeight lambda (e.symm i).1 =
        Real.exp (lambda - Real.log 2 / 2) * gaussWeight (lambda - Real.log 2) i.1 :=
    fun i ↦ gaussWeight_add_one lambda i.1
  simp_rw [hterm]
  exact tsum_mul_left

private theorem partitionFn_pos_of_nonempty {S : Set ℤ} (hS : S.Nonempty) (lambda : ℝ) :
    0 < partitionFn S lambda := by
  obtain ⟨x, hx⟩ := hS
  have hsum := hasSum_partitionFn S lambda
  exact lt_of_lt_of_le (gaussWeight_pos lambda x)
    (hsum.summable.le_tsum (⟨x, hx⟩ : S) (fun j _ ↦ (gaussWeight_pos lambda j.1).le))

/-- **Gaussian dual shift equivariance (`eq:shift-equivariance`, `(3.13)`):**
`𝓕_{S+1}(T + 1) = 𝓕_S(T) - (log 2)(T + 1/2)`. -/
theorem dualValue_shiftSupportOne {S : Set ℤ} (hS : S.Nonempty) {T : ℝ}
    (hbdd : BddBelow (Set.range fun mu : ℝ ↦ Real.log (partitionFn S mu) - mu * T)) :
    dualValue (shiftSupportOne S) (T + 1) =
      dualValue S T - Real.log 2 * (T + 1 / 2) := by
  have hobj : ∀ l : ℝ,
      Real.log (partitionFn (shiftSupportOne S) l) - l * (T + 1) =
        (Real.log (partitionFn S (l - Real.log 2)) - (l - Real.log 2) * T) -
          Real.log 2 * (T + 1 / 2) := by
    intro l
    have hpos := partitionFn_pos_of_nonempty hS (l - Real.log 2)
    rw [partitionFn_shiftSupportOne S l,
      Real.log_mul (Real.exp_pos _).ne' hpos.ne', Real.log_exp]
    ring
  have hbdd' : BddBelow (Set.range fun l : ℝ ↦
      Real.log (partitionFn (shiftSupportOne S) l) - l * (T + 1)) := by
    obtain ⟨B, hB⟩ := hbdd
    refine ⟨B - Real.log 2 * (T + 1 / 2), ?_⟩
    rintro _ ⟨l, rfl⟩
    dsimp only
    rw [hobj l]
    have := hB ⟨l - Real.log 2, rfl⟩
    linarith
  apply le_antisymm
  · suffices dualValue (shiftSupportOne S) (T + 1) + Real.log 2 * (T + 1 / 2) ≤
        dualValue S T by linarith
    refine le_ciInf fun mu ↦ ?_
    show dualValue (shiftSupportOne S) (T + 1) + Real.log 2 * (T + 1 / 2) ≤
      Real.log (partitionFn S mu) - mu * T
    have h1 : dualValue (shiftSupportOne S) (T + 1) ≤
        Real.log (partitionFn (shiftSupportOne S) (mu + Real.log 2)) -
          (mu + Real.log 2) * (T + 1) :=
      ciInf_le hbdd' (mu + Real.log 2)
    have h2 := hobj (mu + Real.log 2)
    rw [add_sub_cancel_right] at h2
    linarith
  · refine le_ciInf fun l ↦ ?_
    show _ ≤ Real.log (partitionFn (shiftSupportOne S) l) - l * (T + 1)
    rw [hobj l]
    have h1 : dualValue S T ≤
        Real.log (partitionFn S (l - Real.log 2)) - (l - Real.log 2) * T :=
      ciInf_le hbdd (l - Real.log 2)
    linarith

theorem S4_subset_S07 : S4 ⊆ S07 := by
  intro i hi
  simp only [S4, S07, Set.mem_insert_iff, Set.mem_singleton_iff] at hi ⊢
  omega

theorem S07_subset_Sge0 : S07 ⊆ Sge0 := by
  intro i hi
  simp only [S07, Sge0, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hi ⊢
  omega

theorem Sge0_subset_Splus : Sge0 ⊆ Splus := by
  intro i hi
  simp only [Sge0, Splus, Set.mem_setOf_eq] at hi ⊢
  omega

theorem S4_subset_Sge0 : S4 ⊆ Sge0 := S4_subset_S07.trans S07_subset_Sge0

theorem S4_subset_Sge1 : S4 ⊆ Sge1 := by
  intro i hi
  simp only [S4, Sge1, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hi ⊢
  omega

theorem Sge1_subset_Sge0 : Sge1 ⊆ Sge0 := by
  intro i hi; simp only [Sge1, Sge0, Set.mem_setOf_eq] at hi ⊢; omega

theorem Sge1_subset_Splus : Sge1 ⊆ Splus := Sge1_subset_Sge0.trans Sge0_subset_Splus

/-- **Shift-equivariance bridge on `[0, 7/200]`:** comparing `S_{1,7} = {2..8}` against
`S_{≥ 1}` at `T_δ` equals `A₇(1 + δ)`. -/
theorem dualValue_Sge1_sub_S17_eq_phaseGain7_add_one {delta : ℝ}
    (hdelta : delta ∈ Set.Icc (0 : ℝ) (7 / 200)) :
    Real.log 2 - dualValue Sge1 (phaseTarget delta) +
        dualValue S17 (phaseTarget delta) =
      phaseGain7 (1 + delta) := by
  obtain ⟨hA, hB⟩ := two_div_log_two_bounds
  have hT : phaseTarget (1 + delta) ∈ Set.Ioo (2 : ℝ) 5 := by
    unfold phaseTarget
    exact ⟨by linarith [hdelta.2], by linarith [hdelta.1]⟩
  have hm := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT)
  have hTeq : phaseTarget delta = phaseTarget (1 + delta) + 1 := by
    unfold phaseTarget; ring
  have h1 := dualValue_shiftSupportOne (S := Sge0) ⟨0, by simp [Sge0]⟩
    (bddBelow_dual S4_subset_Sge0 hm)
  have h2 := dualValue_shiftSupportOne (S := S07) ⟨1, by simp [S07]⟩
    (bddBelow_dual S4_subset_S07 hm)
  rw [shiftSupportOne_Sge0, ← hTeq] at h1
  rw [shiftSupportOne_S07, ← hTeq] at h2
  unfold phaseGain7
  linarith

/-! ## 2. Six-cell rational certificate `A₇(δ̃) > log (391 / 200)` and `[0.080, 0.086]` -/

theorem coe_F07 : (F07 : Set ℤ) = S07 := by
  ext i; simp [F07, S07]

theorem F07_nonempty : F07.Nonempty := ⟨1, by simp [F07]⟩

theorem sum_F07 (f : ℤ → ℝ) :
    ∑ i ∈ F07, f i = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 := by
  have h : F07 = insert 1 (insert 2 (insert 3 (insert 4 (insert 5 (insert 6 {7}))))) := rfl
  rw [h,
    Finset.sum_insert (by simp), Finset.sum_insert (by simp),
    Finset.sum_insert (by simp), Finset.sum_insert (by simp),
    Finset.sum_insert (by simp), Finset.sum_insert (by simp),
    Finset.sum_singleton]
  ring

/-- `P₇(y) = Z_{S_{0,7}}(yTilt y)`. -/
def sevenPartY (y : ℝ) : ℝ :=
  y + y ^ 2 / 2 + y ^ 3 / 8 + y ^ 4 / 64 + y ^ 5 / 1024 +
    y ^ 6 / 32768 + y ^ 7 / 2097152

/-- `Q₇(y) = ∑_{i=1}^7 i · w_i(yTilt y)`. -/
def sevenFirstY (y : ℝ) : ℝ :=
  y + 2 * (y ^ 2 / 2) + 3 * (y ^ 3 / 8) + 4 * (y ^ 4 / 64) +
    5 * (y ^ 5 / 1024) + 6 * (y ^ 6 / 32768) + 7 * (y ^ 7 / 2097152)

/-- Seven-size mean `M₇(y) = Q₇(y) / P₇(y)`. -/
def sevenMeanY (y : ℝ) : ℝ :=
  sevenFirstY y / sevenPartY y

/-- Explicit upper bound `U₀(z) = 1 + P₇(z) + (8/7) z⁸ 2⁻²⁸ ≥ Z_{S_{≥ 0}}(yTilt z)` for `z ≤ 16`. -/
def sge0BoundY (z : ℝ) : ℝ :=
  1 + sevenPartY z + 8 / 7 * (z ^ 8 / 268435456)

theorem sevenPartY_pos {y : ℝ} (hy : 0 < y) : 0 < sevenPartY y := by
  unfold sevenPartY; positivity

theorem sge0BoundY_pos {z : ℝ} (hz : 0 < z) : 0 < sge0BoundY z := by
  have := sevenPartY_pos hz
  unfold sge0BoundY; positivity

theorem sum_F07_yTilt (y : ℝ) (hy : 0 < y) :
    ∑ i ∈ F07, gaussWeight (yTilt y) i = sevenPartY y := by
  obtain ⟨-, -, h1, h2, h3, h4, h5, h6, h7⟩ := weights_yTilt y hy
  unfold sevenPartY
  rw [sum_F07, h1, h2, h3, h4, h5, h6, h7]

theorem partitionFn_S07 (lambda : ℝ) :
    partitionFn S07 lambda = ∑ i ∈ F07, gaussWeight lambda i := by
  rw [← coe_F07, partitionFn_coe_finset]

theorem seven_mean_condition_yTilt (y : ℝ) (hy : 0 < y) :
    ∑ i ∈ F07, ((i : ℝ) - sevenMeanY y) * gaussWeight (yTilt y) i = 0 := by
  obtain ⟨-, -, h1, h2, h3, h4, h5, h6, h7⟩ := weights_yTilt y hy
  have hP := sevenPartY_pos hy
  have hmul : sevenMeanY y * sevenPartY y = sevenFirstY y := by
    unfold sevenMeanY
    rw [div_mul_eq_mul_div, mul_div_assoc, div_self hP.ne', mul_one]
  unfold sevenPartY sevenFirstY at hmul
  rw [sum_F07, h1, h2, h3, h4, h5, h6, h7]
  push_cast
  linear_combination -hmul

theorem seven_dual_lower (y : ℝ) (hy : 0 < y) (lambda : ℝ) :
    Real.log (sevenPartY y) - yTilt y * sevenMeanY y ≤
      Real.log (partitionFn S07 lambda) - lambda * sevenMeanY y := by
  have htan := tangent_finset F07 (sevenMeanY y) (yTilt y) lambda
  rw [seven_mean_condition_yTilt y hy, mul_zero, add_zero, sum_F07_yTilt y hy] at htan
  have hP := sevenPartY_pos hy
  have hZ7 := sum_gaussWeight_pos F07 F07_nonempty lambda
  rw [partitionFn_S07, log_sub_mul_eq hP, log_sub_mul_eq hZ7]
  exact Real.log_le_log (mul_pos hP (Real.exp_pos _)) htan

theorem seven_dual_interp {ya yb T : ℝ} (hya : 0 < ya) (hyb : 0 < yb)
    (hTa : sevenMeanY ya ≤ T) (hTb : T ≤ sevenMeanY yb)
    (hab : sevenMeanY ya < sevenMeanY yb) :
    (sevenMeanY yb - T) * (Real.log (sevenPartY ya) - yTilt ya * sevenMeanY ya) +
        (T - sevenMeanY ya) * (Real.log (sevenPartY yb) - yTilt yb * sevenMeanY yb) ≤
      dualValue S07 T * (sevenMeanY yb - sevenMeanY ya) := by
  have hD : 0 < sevenMeanY yb - sevenMeanY ya := by linarith
  have hα : 0 ≤ sevenMeanY yb - T := by linarith
  have hβ : 0 ≤ T - sevenMeanY ya := by linarith
  refine (div_le_iff₀ hD).mp (le_ciInf fun l ↦ ?_)
  show _ ≤ Real.log (partitionFn S07 l) - l * T
  rw [div_le_iff₀ hD]
  have e1 := mul_le_mul_of_nonneg_left (seven_dual_lower ya hya l) hα
  have e2 := mul_le_mul_of_nonneg_left (seven_dual_lower yb hyb l) hβ
  linarith

theorem partitionFn_Sge0_eq_tsum_natTerm (lambda : ℝ) :
    partitionFn Sge0 lambda = ∑' d : ℕ, extendedGaussianNaturalTerm q lambda d := by
  unfold partitionFn
  let e : ℕ ≃ Sge0 :=
    { toFun := fun d ↦ ⟨(d : ℤ), Int.natCast_nonneg d⟩
      invFun := fun i ↦ i.1.toNat
      left_inv := fun d ↦ Int.toNat_natCast d
      right_inv := fun i ↦ Subtype.ext (Int.toNat_of_nonneg i.2) }
  rw [← e.tsum_eq]
  refine tsum_congr fun d ↦ ?_
  exact (natTerm_eq lambda d).symm

private theorem tsum_natTerm_le_from_eight (lambda : ℝ) (hl : lambda ≤ 9 * q / 2) :
    ∑' d : ℕ, extendedGaussianNaturalTerm q lambda d ≤
      (∑ d ∈ Finset.range 8, extendedGaussianNaturalTerm q lambda d) +
        8 / 7 * extendedGaussianNaturalTerm q lambda 8 := by
  have hs : Summable (extendedGaussianNaturalTerm q lambda) :=
    summable_extendedGaussianNaturalTerm q_pos
  have hgeom : ∀ n : ℕ, extendedGaussianNaturalTerm q lambda (n + 8) ≤
      (1 / 8 : ℝ) ^ n * extendedGaussianNaturalTerm q lambda 8 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [(by omega : n + 1 + 8 = n + 8 + 1)]
      calc extendedGaussianNaturalTerm q lambda (n + 8 + 1)
          ≤ 1 / 8 * extendedGaussianNaturalTerm q lambda (n + 8) :=
            natTerm_succ_le lambda hl (n + 8) (by omega)
        _ ≤ 1 / 8 * ((1 / 8 : ℝ) ^ n * extendedGaussianNaturalTerm q lambda 8) :=
            mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (1 / 8 : ℝ) ^ (n + 1) * extendedGaussianNaturalTerm q lambda 8 := by ring
  have hgs : Summable (fun n : ℕ ↦ (1 / 8 : ℝ) ^ n * extendedGaussianNaturalTerm q lambda 8) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
  have htail : ∑' n : ℕ, extendedGaussianNaturalTerm q lambda (n + 8) ≤
      8 / 7 * extendedGaussianNaturalTerm q lambda 8 := by
    calc ∑' n : ℕ, extendedGaussianNaturalTerm q lambda (n + 8)
        ≤ ∑' n : ℕ, (1 / 8 : ℝ) ^ n * extendedGaussianNaturalTerm q lambda 8 :=
          Summable.tsum_le_tsum hgeom ((summable_nat_add_iff 8).mpr hs) hgs
      _ = 8 / 7 * extendedGaussianNaturalTerm q lambda 8 := by
          rw [tsum_mul_right,
            tsum_geometric_of_lt_one (r := (1 / 8 : ℝ)) (by norm_num) (by norm_num)]
          norm_num
  rw [← hs.sum_add_tsum_nat_add 8]
  linarith

theorem partitionFn_Sge0_le_sge0BoundY {z : ℝ} (hz : 0 < z) (hz16 : z ≤ 16) :
    partitionFn Sge0 (yTilt z) ≤ sge0BoundY z := by
  rw [partitionFn_Sge0_eq_tsum_natTerm]
  have h := tsum_natTerm_le_from_eight (yTilt z) (yTilt_le_nine_q_half hz hz16)
  obtain ⟨-, h0, h1, h2, h3, h4, h5, h6, h7⟩ := weights_yTilt z hz
  have h8 : gaussWeight (yTilt z) 8 = z ^ 8 / 268435456 := by
    rw [gaussWeight_yTilt z hz 8 8 28 (by norm_num) (by norm_num)]
    norm_num
  have hfin :
      (∑ d ∈ Finset.range 8, extendedGaussianNaturalTerm q (yTilt z) d) +
          8 / 7 * extendedGaussianNaturalTerm q (yTilt z) 8 =
        sge0BoundY z := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, natTerm_eq]
    push_cast
    rw [h0, h1, h2, h3, h4, h5, h6, h7, h8]
    unfold sge0BoundY sevenPartY
    ring
  linarith

theorem sevenPhaseGain_cell_T {ya yb z K T : ℝ} (hya : 0 < ya) (hyb : 0 < yb) (hz : 0 < z)
    (hz16 : z ≤ 16) (hK : 0 < K) (hab : sevenMeanY ya < sevenMeanY yb)
    (hVa : 0 < Real.log (2 * sevenPartY ya / (K * sge0BoundY z)) +
      sevenMeanY ya * Real.log (z / ya))
    (hVb : 0 < Real.log (2 * sevenPartY yb / (K * sge0BoundY z)) +
      sevenMeanY yb * Real.log (z / yb))
    (hT25 : T ∈ Set.Ioo (2 : ℝ) 5) (hTa : sevenMeanY ya ≤ T) (hTb : T ≤ sevenMeanY yb) :
    Real.log K < Real.log 2 - dualValue Sge0 T + dualValue S07 T := by
  have hmean4 := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT25)
  have hU := sge0BoundY_pos hz
  have hPa := sevenPartY_pos hya
  have hPb := sevenPartY_pos hyb
  have hsge0 : dualValue Sge0 T ≤ Real.log (sge0BoundY z) - yTilt z * T := by
    have h1 := dualValue_le_at S4_subset_Sge0 hmean4 (yTilt z)
    have hpos := partitionFn_pos_of_nonempty (S := Sge0) ⟨0, by simp [Sge0]⟩ (yTilt z)
    have h2 := Real.log_le_log hpos (partitionFn_Sge0_le_sge0BoundY hz hz16)
    linarith
  have h7 := seven_dual_interp hya hyb hTa hTb hab
  have eρa : Real.log (2 * sevenPartY ya / (K * sge0BoundY z)) =
      Real.log 2 + Real.log (sevenPartY ya) - Real.log K - Real.log (sge0BoundY z) := by
    rw [Real.log_div (mul_pos two_pos hPa).ne' (mul_pos hK hU).ne',
      Real.log_mul two_ne_zero hPa.ne', Real.log_mul hK.ne' hU.ne']
    ring
  have eρb : Real.log (2 * sevenPartY yb / (K * sge0BoundY z)) =
      Real.log 2 + Real.log (sevenPartY yb) - Real.log K - Real.log (sge0BoundY z) := by
    rw [Real.log_div (mul_pos two_pos hPb).ne' (mul_pos hK hU).ne',
      Real.log_mul two_ne_zero hPb.ne', Real.log_mul hK.ne' hU.ne']
    ring
  have era : Real.log (z / ya) = yTilt z - yTilt ya := by
    unfold yTilt; rw [Real.log_div hz.ne' hya.ne']; ring
  have erb : Real.log (z / yb) = yTilt z - yTilt yb := by
    unfold yTilt; rw [Real.log_div hz.ne' hyb.ne']; ring
  rw [eρa, era] at hVa
  rw [eρb, erb] at hVb
  have hD : 0 < sevenMeanY yb - sevenMeanY ya := by linarith
  have hα : 0 ≤ sevenMeanY yb - T := by linarith
  have hβ : 0 ≤ T - sevenMeanY ya := by linarith
  have hpos : 0 < (sevenMeanY yb - T) *
        (Real.log 2 + Real.log (sevenPartY ya) - Real.log K - Real.log (sge0BoundY z) +
          sevenMeanY ya * (yTilt z - yTilt ya)) +
      (T - sevenMeanY ya) *
        (Real.log 2 + Real.log (sevenPartY yb) - Real.log K - Real.log (sge0BoundY z) +
          sevenMeanY yb * (yTilt z - yTilt yb)) := by
    rcases eq_or_lt_of_le hα with h0 | h0
    · rw [← h0, zero_mul, zero_add]
      exact mul_pos (by linarith) hVb
    · exact add_pos_of_pos_of_nonneg (mul_pos h0 hVa) (mul_nonneg hβ hVb.le)
  have e := mul_le_mul_of_nonneg_left hsge0 hD.le
  have key : (sevenMeanY yb - sevenMeanY ya) * Real.log K <
      (sevenMeanY yb - sevenMeanY ya) * (Real.log 2 - dualValue Sge0 T + dualValue S07 T) := by
    linarith
  exact lt_of_mul_lt_mul_left key hD.le

private theorem endpoint7_1a :
    0 < Real.log (2 * sevenPartY (121 / 25) / (391 / 200 * sge0BoundY (129 / 25))) +
      sevenMeanY (121 / 25) * Real.log ((129 / 25) / (121 / 25)) := by
  have hρ := log_ge_of_artanh
    (m := 2 * sevenPartY (121 / 25) / (391 / 200 * sge0BoundY (129 / 25)))
    (u := 500489 / 2000000) (L := 5113472553 / 10000000000) (by norm_num) log_half_ge
    (by norm_num) (by norm_num) (by unfold sge0BoundY sevenPartY; norm_num) 6
    (by norm_num [Finset.sum_range_succ])
  have hr := log_ge_of_artanh (m := (129 / 25) / (121 / 25)) (u := 4 / 125)
    (L := 640218587 / 10000000000) (by norm_num) log_one_ge
    (by norm_num) (by norm_num) (by norm_num) 6 (by norm_num [Finset.sum_range_succ])
  exact endpoint_of_bounds hρ hr (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
    (t := 2850281 / 1000000) (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
    (by norm_num)

private theorem endpoint7_1b :
    0 < Real.log (2 * sevenPartY (11 / 2) / (391 / 200 * sge0BoundY (129 / 25))) +
      sevenMeanY (11 / 2) * Real.log ((129 / 25) / (11 / 2)) := by
  have hρ := log_ge_of_artanh
    (m := 2 * sevenPartY (11 / 2) / (391 / 200 * sge0BoundY (129 / 25)))
    (u := 961677 / 10000000) (L := 482329081 / 2500000000) (by norm_num) log_one_ge
    (by norm_num) (by norm_num) (by unfold sge0BoundY sevenPartY; norm_num) 6
    (by norm_num [Finset.sum_range_succ])
  have hr := log_ge_of_artanh (m := (129 / 25) / (11 / 2)) (u := 380847 / 1250000)
    (L := 6293355839 / 10000000000) (by norm_num) log_half_ge
    (by norm_num) (by norm_num) (by norm_num) 6 (by norm_num [Finset.sum_range_succ])
  exact endpoint_of_bounds hρ hr (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
    (t := 9417 / 3125) (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
    (by norm_num)

private theorem endpoint7_2a :
    0 < Real.log (2 * sevenPartY (11 / 2) / (391 / 200 * sge0BoundY (149 / 25))) +
      sevenMeanY (11 / 2) * Real.log ((149 / 25) / (11 / 2)) := by
  have hρ := log_ge_of_artanh
    (m := 2 * sevenPartY (11 / 2) / (391 / 200 * sge0BoundY (149 / 25)))
    (u := 2245773 / 10000000) (L := 913885403 / 2000000000) (by norm_num) log_half_ge
    (by norm_num) (by norm_num) (by unfold sge0BoundY sevenPartY; norm_num) 6
    (by norm_num [Finset.sum_range_succ])
  have hr := log_ge_of_artanh (m := (149 / 25) / (11 / 2)) (u := 100349 / 2500000)
    (L := 401611783 / 5000000000) (by norm_num) log_one_ge
    (by norm_num) (by norm_num) (by norm_num) 6 (by norm_num [Finset.sum_range_succ])
  exact endpoint_of_bounds hρ hr (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
    (t := 3013439 / 1000000) (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
    (by norm_num)

private theorem endpoint7_2b :
    0 < Real.log (2 * sevenPartY (129 / 20) / (391 / 200 * sge0BoundY (149 / 25))) +
      sevenMeanY (129 / 20) * Real.log ((149 / 25) / (129 / 20)) := by
  have hρ := log_ge_of_artanh
    (m := 2 * sevenPartY (129 / 20) / (391 / 200 * sge0BoundY (149 / 25)))
    (u := 1295623 / 10000000) (L := 2605893029 / 10000000000) (by norm_num) log_one_ge
    (by norm_num) (by norm_num) (by unfold sge0BoundY sevenPartY; norm_num) 6
    (by norm_num [Finset.sum_range_succ])
  have hr := log_ge_of_artanh (m := (149 / 25) / (129 / 20)) (u := 2977681 / 10000000)
    (L := 6141375063 / 10000000000) (by norm_num) log_half_ge
    (by norm_num) (by norm_num) (by norm_num) 6 (by norm_num [Finset.sum_range_succ])
  exact endpoint_of_bounds hρ hr (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
    (t := 3223649 / 1000000) (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
    (by norm_num)

private theorem endpoint7_3a :
    0 < Real.log (2 * sevenPartY (129 / 20) / (391 / 200 * sge0BoundY (703 / 100))) +
      sevenMeanY (129 / 20) * Real.log ((703 / 100) / (129 / 20)) := by
  have hρ := log_ge_of_artanh
    (m := 2 * sevenPartY (129 / 20) / (391 / 200 * sge0BoundY (703 / 100)))
    (u := 1048523 / 5000000) (L := 2128623383 / 5000000000) (by norm_num) log_half_ge
    (by norm_num) (by norm_num) (by unfold sge0BoundY sevenPartY; norm_num) 6
    (by norm_num [Finset.sum_range_succ])
  have hr := log_ge_of_artanh (m := (703 / 100) / (129 / 20)) (u := 430267 / 10000000)
    (L := 275541 / 3200000) (by norm_num) log_one_ge
    (by norm_num) (by norm_num) (by norm_num) 6 (by norm_num [Finset.sum_range_succ])
  exact endpoint_of_bounds hρ hr (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
    (t := 100739 / 31250) (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
    (by norm_num)

private theorem endpoint7_3b :
    0 < Real.log (2 * sevenPartY (153 / 20) / (391 / 200 * sge0BoundY (703 / 100))) +
      sevenMeanY (153 / 20) * Real.log ((703 / 100) / (153 / 20)) := by
  have hρ := log_ge_of_artanh
    (m := 2 * sevenPartY (153 / 20) / (391 / 200 * sge0BoundY (703 / 100)))
    (u := 37501 / 250000) (L := 9446533 / 31250000) (by norm_num) log_one_ge
    (by norm_num) (by norm_num) (by unfold sge0BoundY sevenPartY; norm_num) 6
    (by norm_num [Finset.sum_range_succ])
  have hr := log_ge_of_artanh (m := (703 / 100) / (153 / 20)) (u := 738139 / 2500000)
    (L := 6086281237 / 10000000000) (by norm_num) log_half_ge
    (by norm_num) (by norm_num) (by norm_num) 6 (by norm_num [Finset.sum_range_succ])
  exact endpoint_of_bounds hρ hr (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
    (t := 3455203 / 1000000) (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
    (by norm_num)

private theorem endpoint7_4a :
    0 < Real.log (2 * sevenPartY (153 / 20) / (391 / 200 * sge0BoundY (823 / 100))) +
      sevenMeanY (153 / 20) * Real.log ((823 / 100) / (153 / 20)) := by
  have hρ := log_ge_of_artanh
    (m := 2 * sevenPartY (153 / 20) / (391 / 200 * sge0BoundY (823 / 100)))
    (u := 2236629 / 10000000) (L := 455017183 / 1000000000) (by norm_num) log_half_ge
    (by norm_num) (by norm_num) (by unfold sge0BoundY sevenPartY; norm_num) 6
    (by norm_num [Finset.sum_range_succ])
  have hr := log_ge_of_artanh (m := (823 / 100) / (153 / 20)) (u := 365239 / 10000000)
    (L := 365401539 / 5000000000) (by norm_num) log_one_ge
    (by norm_num) (by norm_num) (by norm_num) 6 (by norm_num [Finset.sum_range_succ])
  exact endpoint_of_bounds hρ hr (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
    (t := 1727601 / 500000) (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
    (by norm_num)

private theorem endpoint7_4b :
    0 < Real.log (2 * sevenPartY (177 / 20) / (391 / 200 * sge0BoundY (823 / 100))) +
      sevenMeanY (177 / 20) * Real.log ((823 / 100) / (177 / 20)) := by
  have hρ := log_ge_of_artanh
    (m := 2 * sevenPartY (177 / 20) / (391 / 200 * sge0BoundY (823 / 100)))
    (u := 695401 / 5000000) (L := 279975021 / 1000000000) (by norm_num) log_one_ge
    (by norm_num) (by norm_num) (by unfold sge0BoundY sevenPartY; norm_num) 6
    (by norm_num [Finset.sum_range_succ])
  have hr := log_ge_of_artanh (m := (823 / 100) / (177 / 20)) (u := 751679 / 2500000)
    (L := 6205155521 / 10000000000) (by norm_num) log_half_ge
    (by norm_num) (by norm_num) (by norm_num) 6 (by norm_num [Finset.sum_range_succ])
  exact endpoint_of_bounds hρ hr (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
    (t := 731321 / 200000) (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
    (by norm_num)

private theorem endpoint7_5a :
    0 < Real.log (2 * sevenPartY (177 / 20) / (391 / 200 * sge0BoundY (231 / 25))) +
      sevenMeanY (177 / 20) * Real.log ((231 / 25) / (177 / 20)) := by
  have hρ := log_ge_of_artanh
    (m := 2 * sevenPartY (177 / 20) / (391 / 200 * sge0BoundY (231 / 25)))
    (u := 67467 / 250000) (L := 5534428907 / 10000000000) (by norm_num) log_half_ge
    (by norm_num) (by norm_num) (by unfold sge0BoundY sevenPartY; norm_num) 6
    (by norm_num [Finset.sum_range_succ])
  have hr := log_ge_of_artanh (m := (231 / 25) / (177 / 20)) (u := 53897 / 2500000)
    (L := 431242819 / 10000000000) (by norm_num) log_one_ge
    (by norm_num) (by norm_num) (by norm_num) 6 (by norm_num [Finset.sum_range_succ])
  exact endpoint_of_bounds hρ hr (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
    (t := 914151 / 250000) (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
    (by norm_num)

private theorem endpoint7_5b :
    0 < Real.log (2 * sevenPartY (193 / 20) / (391 / 200 * sge0BoundY (231 / 25))) +
      sevenMeanY (193 / 20) * Real.log ((231 / 25) / (193 / 20)) := by
  have hρ := log_ge_of_artanh
    (m := 2 * sevenPartY (193 / 20) / (391 / 200 * sge0BoundY (231 / 25)))
    (u := 907279 / 10000000) (L := 1819561611 / 10000000000) (by norm_num) log_one_ge
    (by norm_num) (by norm_num) (by unfold sge0BoundY sevenPartY; norm_num) 6
    (by norm_num [Finset.sum_range_succ])
  have hr := log_ge_of_artanh (m := (231 / 25) / (193 / 20)) (u := 3138997 / 10000000)
    (L := 649730989 / 1000000000) (by norm_num) log_half_ge
    (by norm_num) (by norm_num) (by norm_num) 6 (by norm_num [Finset.sum_range_succ])
  exact endpoint_of_bounds hρ hr (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
    (t := 3777253 / 1000000) (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
    (by norm_num)

private theorem endpoint7_6a :
    0 < Real.log (2 * sevenPartY (193 / 20) / (391 / 200 * sge0BoundY (251 / 25))) +
      sevenMeanY (193 / 20) * Real.log ((251 / 25) / (193 / 20)) := by
  have hρ := log_ge_of_artanh
    (m := 2 * sevenPartY (193 / 20) / (391 / 200 * sge0BoundY (251 / 25)))
    (u := 2739089 / 10000000) (L := 2810849147 / 5000000000) (by norm_num) log_half_ge
    (by norm_num) (by norm_num) (by unfold sge0BoundY sevenPartY; norm_num) 6
    (by norm_num [Finset.sum_range_succ])
  have hr := log_ge_of_artanh (m := (251 / 25) / (193 / 20)) (u := 19807 / 1000000)
    (L := 49523977 / 1250000000) (by norm_num) log_one_ge
    (by norm_num) (by norm_num) (by norm_num) 6 (by norm_num [Finset.sum_range_succ])
  exact endpoint_of_bounds hρ hr (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
    (t := 944313 / 250000) (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
    (by norm_num)

private theorem endpoint7_6b :
    0 < Real.log (2 * sevenPartY (209 / 20) / (391 / 200 * sge0BoundY (251 / 25))) +
      sevenMeanY (209 / 20) * Real.log ((251 / 25) / (209 / 20)) := by
  have hρ := log_ge_of_artanh
    (m := 2 * sevenPartY (209 / 20) / (391 / 200 * sge0BoundY (251 / 25)))
    (u := 108659 / 1250000) (L := 174294297 / 1000000000) (by norm_num) log_one_ge
    (by norm_num) (by norm_num) (by unfold sge0BoundY sevenPartY; norm_num) 6
    (by norm_num [Finset.sum_range_succ])
  have hr := log_ge_of_artanh (m := (251 / 25) / (209 / 20)) (u := 1577137 / 5000000)
    (L := 6531221573 / 10000000000) (by norm_num) log_half_ge
    (by norm_num) (by norm_num) (by norm_num) 6 (by norm_num [Finset.sum_range_succ])
  exact endpoint_of_bounds hρ hr (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
    (t := 3888693 / 1000000) (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
    (by norm_num)

private theorem sevenMean_breakpoints :
    sevenMeanY (121 / 25) < 288537 / 100000 - 7 / 200 ∧
      sevenMeanY (121 / 25) < sevenMeanY (11 / 2) ∧
      sevenMeanY (11 / 2) < sevenMeanY (129 / 20) ∧
      sevenMeanY (129 / 20) < sevenMeanY (153 / 20) ∧
      sevenMeanY (153 / 20) < sevenMeanY (177 / 20) ∧
      sevenMeanY (177 / 20) < sevenMeanY (193 / 20) ∧
      sevenMeanY (193 / 20) < sevenMeanY (209 / 20) ∧
      (38854 / 10000 : ℝ) < sevenMeanY (209 / 20) := by
  unfold sevenMeanY sevenFirstY sevenPartY
  norm_num

/-- **Six-cell uniform certificate (`Lemma 5.1`):**
`A₇(td) > log (391 / 200)` for every `td ∈ [0, 207 / 200]`. -/
theorem log_391_div_200_lt_phaseGain7 (td : ℝ)
    (htd : td ∈ Set.Icc (0 : ℝ) (207 / 200)) :
    Real.log (391 / 200) < phaseGain7 td := by
  obtain ⟨hA, hB⟩ := two_div_log_two_bounds
  obtain ⟨c0, c01, c12, c23, c34, c45, c56, c6⟩ := sevenMean_breakpoints
  obtain ⟨h0, h1⟩ := htd
  have hT25 : phaseTarget td ∈ Set.Ioo (2 : ℝ) 5 := by
    unfold phaseTarget
    exact ⟨by linarith, by linarith⟩
  have hlo : sevenMeanY (121 / 25) ≤ phaseTarget td := by
    unfold phaseTarget; linarith
  have hhi : phaseTarget td ≤ sevenMeanY (209 / 20) := by
    unfold phaseTarget; linarith
  unfold phaseGain7
  rcases le_total (phaseTarget td) (sevenMeanY (11 / 2)) with h_1 | h_1
  · exact sevenPhaseGain_cell_T (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) c01 endpoint7_1a endpoint7_1b hT25 hlo h_1
  rcases le_total (phaseTarget td) (sevenMeanY (129 / 20)) with h_2 | h_2
  · exact sevenPhaseGain_cell_T (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) c12 endpoint7_2a endpoint7_2b hT25 h_1 h_2
  rcases le_total (phaseTarget td) (sevenMeanY (153 / 20)) with h_3 | h_3
  · exact sevenPhaseGain_cell_T (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) c23 endpoint7_3a endpoint7_3b hT25 h_2 h_3
  rcases le_total (phaseTarget td) (sevenMeanY (177 / 20)) with h_4 | h_4
  · exact sevenPhaseGain_cell_T (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) c34 endpoint7_4a endpoint7_4b hT25 h_3 h_4
  rcases le_total (phaseTarget td) (sevenMeanY (193 / 20)) with h_5 | h_5
  · exact sevenPhaseGain_cell_T (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) c45 endpoint7_5a endpoint7_5b hT25 h_4 h_5
  · exact sevenPhaseGain_cell_T (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) c56 endpoint7_6a endpoint7_6b hT25 h_5 hhi

private theorem phaseTarget_mapsTo_Icc_wide :
    Set.MapsTo phaseTarget (Set.Icc (0 : ℝ) (207 / 200)) (Set.Icc (9 / 4 : ℝ) (17 / 4)) := by
  intro td htd
  obtain ⟨hA, hB⟩ := two_div_log_two_bounds
  unfold phaseTarget
  exact ⟨by linarith [htd.2], by linarith [htd.1]⟩

/-- **Continuity of `A₇` on `[0, 207 / 200]` (`Lemma 5.1`).** -/
theorem continuousOn_phaseGain7 :
    ContinuousOn phaseGain7 (Set.Icc (0 : ℝ) (207 / 200)) := by
  have hT : ContinuousOn phaseTarget (Set.Icc (0 : ℝ) (207 / 200)) := by
    unfold phaseTarget
    exact continuousOn_const.sub continuousOn_id
  have hSge0 := (continuousOn_dualValue_Icc S4_subset_Sge0 Sge0_subset_Splus).comp
    hT phaseTarget_mapsTo_Icc_wide
  have hS07 := (continuousOn_dualValue_Icc S4_subset_S07 (S07_subset_Sge0.trans Sge0_subset_Splus)).comp
    hT phaseTarget_mapsTo_Icc_wide
  exact (continuousOn_const.sub hSge0).add hS07

/-! ### Nonconstancy of `A₇` (`A₇(1 + δ_*) < 0.672 < 0.689 < A₇(δ_*)`) -/

private def s07WithZeroPartY (y : ℝ) : ℝ := 1 + sevenPartY y
private def s07WithZeroMeanY (y : ℝ) : ℝ := sevenFirstY y / s07WithZeroPartY y

private theorem s07WithZeroPartY_pos {y : ℝ} (hy : 0 < y) : 0 < s07WithZeroPartY y := by
  have := sevenPartY_pos hy
  unfold s07WithZeroPartY; positivity

private theorem sum_F07WithZero (f : ℤ → ℝ) :
    ∑ i ∈ F07WithZero, f i = f 0 + ∑ i ∈ F07, f i := by
  have h : F07WithZero = insert 0 F07 := rfl
  rw [h, Finset.sum_insert (by simp [F07])]

private theorem sum_F07WithZero_yTilt (y : ℝ) (hy : 0 < y) :
    ∑ i ∈ F07WithZero, gaussWeight (yTilt y) i = s07WithZeroPartY y := by
  obtain ⟨-, h0, -, -, -, -, -, -, -⟩ := weights_yTilt y hy
  rw [sum_F07WithZero, h0, sum_F07_yTilt y hy]
  rfl

private theorem s07WithZero_mean_condition_yTilt (y : ℝ) (hy : 0 < y) :
    ∑ i ∈ F07WithZero, ((i : ℝ) - s07WithZeroMeanY y) * gaussWeight (yTilt y) i = 0 := by
  obtain ⟨-, h0, h1, h2, h3, h4, h5, h6, h7⟩ := weights_yTilt y hy
  have hP := s07WithZeroPartY_pos hy
  have hmul : s07WithZeroMeanY y * s07WithZeroPartY y = sevenFirstY y := by
    unfold s07WithZeroMeanY
    rw [div_mul_eq_mul_div, mul_div_assoc, div_self hP.ne', mul_one]
  unfold s07WithZeroPartY sevenPartY sevenFirstY at hmul
  rw [sum_F07WithZero, sum_F07, h0, h1, h2, h3, h4, h5, h6, h7]
  push_cast
  linear_combination -hmul

private theorem F07WithZero_subset_Sge0 : (F07WithZero : Set ℤ) ⊆ Sge0 := by
  intro i hi
  simp only [F07WithZero, Sge0, Finset.coe_insert, Finset.coe_singleton,
    Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hi ⊢
  omega

private theorem sge0_dual_lower_eight (y : ℝ) (hy : 0 < y) (lambda : ℝ) :
    Real.log (s07WithZeroPartY y) - yTilt y * s07WithZeroMeanY y ≤
      Real.log (partitionFn Sge0 lambda) - lambda * s07WithZeroMeanY y := by
  have htan := tangent_finset F07WithZero (s07WithZeroMeanY y) (yTilt y) lambda
  rw [s07WithZero_mean_condition_yTilt y hy, mul_zero, add_zero,
    sum_F07WithZero_yTilt y hy] at htan
  have hP := s07WithZeroPartY_pos hy
  have hne : F07WithZero.Nonempty := ⟨0, by simp [F07WithZero]⟩
  have hZ := sum_gaussWeight_pos F07WithZero hne lambda
  have h1 : Real.log (s07WithZeroPartY y) - yTilt y * s07WithZeroMeanY y ≤
      Real.log (∑ i ∈ F07WithZero, gaussWeight lambda i) - lambda * s07WithZeroMeanY y := by
    rw [log_sub_mul_eq hP, log_sub_mul_eq hZ]
    exact Real.log_le_log (mul_pos hP (Real.exp_pos _)) htan
  have h2 : ∑ i ∈ F07WithZero, gaussWeight lambda i ≤ partitionFn Sge0 lambda := by
    rw [← partitionFn_coe_finset F07WithZero lambda]
    exact partitionFn_mono F07WithZero_subset_Sge0 lambda
  linarith [Real.log_le_log hZ h2]

theorem phaseGain7_deltaStar_gt_0689 : (689 / 1000 : ℝ) < phaseGain7 deltaStar := by
  obtain ⟨hA, hB⟩ := two_div_log_two_bounds
  have hT25 : phaseTarget deltaStar ∈ Set.Ioo (2 : ℝ) 5 := by
    unfold phaseTarget deltaStar
    exact ⟨by linarith, by linarith⟩
  have hbr : sevenMeanY 10 < 1 + 288537 / 100000 - 7 / 200 ∧
      sevenMeanY 10 < sevenMeanY (103 / 10) ∧
      (38854 / 10000 - 7 / 200 : ℝ) < sevenMeanY (103 / 10) := by
    unfold sevenMeanY sevenFirstY sevenPartY; norm_num
  have hVa : 0 < Real.log (2 * sevenPartY 10 / (249 / 125 * sge0BoundY (203 / 20))) +
      sevenMeanY 10 * Real.log ((203 / 20) / 10) := by
    have hρ := log_ge_of_artanh
      (m := 2 * sevenPartY 10 / (249 / 125 * sge0BoundY (203 / 20)))
      (u := 3081851 / 10000000) (L := 1274155127 / 2000000000) (by norm_num) log_half_ge
      (by norm_num) (by norm_num) (by unfold sge0BoundY sevenPartY; norm_num) 6
      (by norm_num [Finset.sum_range_succ])
    have hr := log_ge_of_artanh (m := (203 / 20) / 10) (u := 74441 / 10000000)
      (L := 595539 / 40000000) (by norm_num) log_one_ge
      (by norm_num) (by norm_num) (by norm_num) 6 (by norm_num [Finset.sum_range_succ])
    exact endpoint_of_bounds hρ hr (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
      (t := 3827067 / 1000000) (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
      (by norm_num)
  have hVb : 0 < Real.log (2 * sevenPartY (103 / 10) / (249 / 125 * sge0BoundY (203 / 20))) +
      sevenMeanY (103 / 10) * Real.log ((203 / 20) / (103 / 10)) := by
    have hρ := log_ge_of_artanh
      (m := 2 * sevenPartY (103 / 10) / (249 / 125 * sge0BoundY (203 / 20)))
      (u := 288247 / 10000000) (L := 288326871 / 5000000000) (by norm_num) log_one_ge
      (by norm_num) (by norm_num) (by unfold sge0BoundY sevenPartY; norm_num) 6
      (by norm_num [Finset.sum_range_succ])
    have hr := log_ge_of_artanh (m := (203 / 20) / (103 / 10)) (u := 3267973 / 10000000)
      (L := 106011987 / 156250000) (by norm_num) log_half_ge
      (by norm_num) (by norm_num) (by norm_num) 6 (by norm_num [Finset.sum_range_succ])
    exact endpoint_of_bounds hρ hr (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
      (t := 3868443 / 1000000) (by unfold sevenMeanY sevenFirstY sevenPartY; norm_num)
      (by norm_num)
  have h249 : (689 / 1000 : ℝ) < Real.log (249 / 125) := by
    have h := log_ge_of_artanh (m := 249 / 125) (c := 1) (u := 828877 / 2500000)
      (lc := 0) (L := 1722847637 / 2500000000) (by norm_num) log_one_ge
      (by norm_num) (by norm_num) (by norm_num) 6 (by norm_num [Finset.sum_range_succ])
    linarith
  refine lt_trans h249 ?_
  unfold phaseGain7
  refine sevenPhaseGain_cell_T (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hbr.2.1 hVa hVb hT25 ?_ ?_
  · unfold phaseTarget deltaStar; linarith [hbr.1]
  · unfold phaseTarget deltaStar; linarith [hbr.2.2]

theorem phaseGain7_one_add_deltaStar_lt_0672 :
    phaseGain7 (1 + deltaStar) < 672 / 1000 := by
  obtain ⟨hA, hB⟩ := two_div_log_two_bounds
  set T₁ : ℝ := phaseTarget (1 + deltaStar)
  have hT₁25 : T₁ ∈ Set.Ioo (2 : ℝ) 5 := by
    unfold T₁ phaseTarget deltaStar
    exact ⟨by linarith, by linarith⟩
  have hm4 := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT₁25)
  have hT₁lo : 288537 / 100000 - 7 / 200 < T₁ := by
    unfold T₁ phaseTarget deltaStar; linarith
  have hT₁hi : T₁ < 28854 / 10000 - 7 / 200 := by
    unfold T₁ phaseTarget deltaStar; linarith
  have hbr : s07WithZeroMeanY (101 / 20) < 288537 / 100000 - 7 / 200 ∧
      s07WithZeroMeanY (101 / 20) < s07WithZeroMeanY (51 / 10) ∧
      (28854 / 10000 - 7 / 200 : ℝ) < s07WithZeroMeanY (51 / 10) := by
    unfold s07WithZeroMeanY sevenFirstY s07WithZeroPartY sevenPartY
    norm_num
  have h7up : dualValue S07 T₁ ≤
      Real.log (sevenPartY (121 / 25)) - yTilt (121 / 25) * T₁ := by
    have h := dualValue_le_at S4_subset_S07 hm4 (yTilt (121 / 25))
    rwa [partitionFn_S07, sum_F07_yTilt (121 / 25) (by norm_num)] at h
  have hsge0_interp :
      (s07WithZeroMeanY (51 / 10) - T₁) *
          (Real.log (s07WithZeroPartY (101 / 20)) -
            yTilt (101 / 20) * s07WithZeroMeanY (101 / 20)) +
        (T₁ - s07WithZeroMeanY (101 / 20)) *
          (Real.log (s07WithZeroPartY (51 / 10)) -
            yTilt (51 / 10) * s07WithZeroMeanY (51 / 10)) ≤
        dualValue Sge0 T₁ * (s07WithZeroMeanY (51 / 10) - s07WithZeroMeanY (101 / 20)) := by
    have hD : 0 < s07WithZeroMeanY (51 / 10) - s07WithZeroMeanY (101 / 20) := by
      linarith [hbr.2.1]
    have hα : 0 ≤ s07WithZeroMeanY (51 / 10) - T₁ := by linarith [hbr.2.2]
    have hβ : 0 ≤ T₁ - s07WithZeroMeanY (101 / 20) := by linarith [hbr.1]
    refine (div_le_iff₀ hD).mp (le_ciInf fun l ↦ ?_)
    show _ ≤ Real.log (partitionFn Sge0 l) - l * T₁
    rw [div_le_iff₀ hD]
    have e1 := mul_le_mul_of_nonneg_left (sge0_dual_lower_eight (101 / 20) (by norm_num) l) hα
    have e2 := mul_le_mul_of_nonneg_left (sge0_dual_lower_eight (51 / 10) (by norm_num) l) hβ
    linarith
  have hVa : 0 < Real.log (979 / 500 * s07WithZeroPartY (101 / 20) / (2 * sevenPartY (121 / 25))) +
      s07WithZeroMeanY (101 / 20) * Real.log ((121 / 25) / (101 / 20)) := by
    have hρ := log_ge_of_artanh
      (m := 979 / 500 * s07WithZeroPartY (101 / 20) / (2 * sevenPartY (121 / 25)))
      (u := 60761 / 1000000) (L := 1216718811 / 10000000000) (by norm_num) log_one_ge
      (by norm_num) (by norm_num) (by unfold s07WithZeroPartY sevenPartY; norm_num) 6
      (by norm_num [Finset.sum_range_succ])
    have hr := log_ge_of_artanh (m := (121 / 25) / (101 / 20)) (u := 628649 / 2000000)
      (L := 3253367957 / 5000000000) (by norm_num) log_half_ge
      (by norm_num) (by norm_num) (by norm_num) 6 (by norm_num [Finset.sum_range_succ])
    exact endpoint_of_bounds hρ hr
      (by unfold s07WithZeroMeanY sevenFirstY s07WithZeroPartY sevenPartY; norm_num)
      (t := 568879 / 200000)
      (by unfold s07WithZeroMeanY sevenFirstY s07WithZeroPartY sevenPartY; norm_num)
      (by norm_num)
  have hVb : 0 < Real.log (979 / 500 * s07WithZeroPartY (51 / 10) / (2 * sevenPartY (121 / 25))) +
      s07WithZeroMeanY (51 / 10) * Real.log ((121 / 25) / (51 / 10)) := by
    have hρ := log_ge_of_artanh
      (m := 979 / 500 * s07WithZeroPartY (51 / 10) / (2 * sevenPartY (121 / 25)))
      (u := 29897 / 400000) (L := 748821499 / 5000000000) (by norm_num) log_one_ge
      (by norm_num) (by norm_num) (by unfold s07WithZeroPartY sevenPartY; norm_num) 6
      (by norm_num [Finset.sum_range_succ])
    have hr := log_ge_of_artanh (m := (121 / 25) / (51 / 10)) (u := 1549391 / 5000000)
      (L := 3204106451 / 5000000000) (by norm_num) log_half_ge
      (by norm_num) (by norm_num) (by norm_num) 6 (by norm_num [Finset.sum_range_succ])
    exact endpoint_of_bounds hρ hr
      (by unfold s07WithZeroMeanY sevenFirstY s07WithZeroPartY sevenPartY; norm_num)
      (t := 714579 / 250000)
      (by unfold s07WithZeroMeanY sevenFirstY s07WithZeroPartY sevenPartY; norm_num)
      (by norm_num)
  have hP7 := sevenPartY_pos (y := 121 / 25) (by norm_num)
  have hPa := s07WithZeroPartY_pos (y := 101 / 20) (by norm_num)
  have hPb := s07WithZeroPartY_pos (y := 51 / 10) (by norm_num)
  have eρa : Real.log (979 / 500 * s07WithZeroPartY (101 / 20) / (2 * sevenPartY (121 / 25))) =
      Real.log (979 / 500) + Real.log (s07WithZeroPartY (101 / 20)) -
        Real.log 2 - Real.log (sevenPartY (121 / 25)) := by
    rw [Real.log_div (mul_pos (by norm_num) hPa).ne' (mul_pos two_pos hP7).ne',
      Real.log_mul (by norm_num) hPa.ne', Real.log_mul two_ne_zero hP7.ne']
    ring
  have eρb : Real.log (979 / 500 * s07WithZeroPartY (51 / 10) / (2 * sevenPartY (121 / 25))) =
      Real.log (979 / 500) + Real.log (s07WithZeroPartY (51 / 10)) -
        Real.log 2 - Real.log (sevenPartY (121 / 25)) := by
    rw [Real.log_div (mul_pos (by norm_num) hPb).ne' (mul_pos two_pos hP7).ne',
      Real.log_mul (by norm_num) hPb.ne', Real.log_mul two_ne_zero hP7.ne']
    ring
  have era : Real.log ((121 / 25) / (101 / 20)) = yTilt (121 / 25) - yTilt (101 / 20) := by
    unfold yTilt; rw [Real.log_div (by norm_num) (by norm_num)]; ring
  have erb : Real.log ((121 / 25) / (51 / 10)) = yTilt (121 / 25) - yTilt (51 / 10) := by
    unfold yTilt; rw [Real.log_div (by norm_num) (by norm_num)]; ring
  rw [eρa, era] at hVa
  rw [eρb, erb] at hVb
  have hD : 0 < s07WithZeroMeanY (51 / 10) - s07WithZeroMeanY (101 / 20) := by
    linarith [hbr.2.1]
  have hα : 0 < s07WithZeroMeanY (51 / 10) - T₁ := by linarith [hbr.2.2]
  have hβ : 0 < T₁ - s07WithZeroMeanY (101 / 20) := by linarith [hbr.1]
  have hpos := add_pos (mul_pos hα hVa) (mul_pos hβ hVb)
  have e7 := mul_le_mul_of_nonneg_left h7up hD.le
  have hlt979 : phaseGain7 (1 + deltaStar) < Real.log (979 / 500) := by
    unfold phaseGain7
    change Real.log 2 - dualValue Sge0 T₁ + dualValue S07 T₁ < Real.log (979 / 500)
    have key : (s07WithZeroMeanY (51 / 10) - s07WithZeroMeanY (101 / 20)) *
          (Real.log 2 - dualValue Sge0 T₁ + dualValue S07 T₁) <
        (s07WithZeroMeanY (51 / 10) - s07WithZeroMeanY (101 / 20)) * Real.log (979 / 500) := by
      linarith
    exact lt_of_mul_lt_mul_left key hD.le
  have h979 : Real.log (979 / 500 : ℝ) < 672 / 1000 := by
    have hinv : Real.log (500 / 979 : ℝ) = -Real.log (979 / 500) := by
      rw [show (500 / 979 : ℝ) = ((979 / 500 : ℝ))⁻¹ by norm_num, Real.log_inv]
    have h := log_ge_of_artanh (m := 500 / 979) (c := 1 / 2) (u := 53057 / 5000000)
      (lc := -(0.6931471808 : ℝ)) (L := 106117983 / 5000000000)
      (by norm_num) log_half_ge (by norm_num) (by norm_num) (by norm_num) 6
      (by norm_num [Finset.sum_range_succ])
    linarith
  exact lt_trans hlt979 h979

/-- **Strict nonconstancy of `A₇` (`Lemma 5.1`):**
`A₇(1 + δ_*) < 0.672 < 0.689 < A₇(δ_*)`. -/
theorem phaseGain7_nonconstant :
    phaseGain7 (1 + deltaStar) < 672 / 1000 ∧
      (689 / 1000 : ℝ) < phaseGain7 deltaStar ∧
      phaseGain7 (1 + deltaStar) < phaseGain7 deltaStar :=
  ⟨phaseGain7_one_add_deltaStar_lt_0672, phaseGain7_deltaStar_gt_0689,
    by linarith [phaseGain7_one_add_deltaStar_lt_0672, phaseGain7_deltaStar_gt_0689]⟩

/-! ### Uniform `[0.080, 0.086]` numerical bounds (`c₇ > 0.080` and `C₇ < 0.086`) -/

theorem log_391_div_200_gt : (268155713 / 400000000 : ℝ) < Real.log (391 / 200) := by
  have hlt : Real.log ((1 + (323181 / 1000000 : ℝ)) /
      (1 - (323181 / 1000000 : ℝ))) < Real.log (391 / 200) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have hp := artanh_partial_le (u := (323181 / 1000000 : ℝ)) (by norm_num) (by norm_num) 5
  have hL : (268155713 / 400000000 : ℝ) ≤
      ∑ j ∈ Finset.range 5, 2 * (1 / (2 * (j : ℝ) + 1)) * (323181 / 1000000 : ℝ) ^ (2 * j + 1) := by
    norm_num [Finset.sum_range_succ]
  linarith

/-- **`0.080 < (log 2)² / 4 · A₇(td)` uniformly on `[0, 207 / 200]`.** -/
theorem lowerPhaseCoeff7_gt_0080 (td : ℝ) (htd : td ∈ Set.Icc (0 : ℝ) (207 / 200)) :
    (80 / 1000 : ℝ) < lowerPhaseCoeff7 td := by
  have hA : (268155713 / 400000000 : ℝ) < phaseGain7 td :=
    lt_trans log_391_div_200_gt (log_391_div_200_lt_phaseGain7 td htd)
  have hqlo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hqsq : (0.6931471803 : ℝ) ^ 2 < (Real.log 2) ^ 2 := by nlinarith
  unfold lowerPhaseCoeff7
  nlinarith

/-- **`(log 2)² / 4 · (2 log 2 - A₇(td)) < 0.086` uniformly on `[0, 207 / 200]`.** -/
theorem upperPhaseCoeff7_lt_0086 (td : ℝ) (htd : td ∈ Set.Icc (0 : ℝ) (207 / 200)) :
    upperPhaseCoeff7 td < (86 / 1000 : ℝ) := by
  have hA : (268155713 / 400000000 : ℝ) < phaseGain7 td :=
    lt_trans log_391_div_200_gt (log_391_div_200_lt_phaseGain7 td htd)
  have hqhi : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have hqpos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hqsq : (Real.log 2) ^ 2 < (0.6931471808 : ℝ) ^ 2 := by nlinarith
  have hspan : 2 * Real.log 2 - phaseGain7 td <
      2 * 0.6931471808 - 268155713 / 400000000 := by linarith
  unfold upperPhaseCoeff7
  by_cases hnonneg : 0 ≤ 2 * Real.log 2 - phaseGain7 td
  · have hmul :
        (Real.log 2) ^ 2 / 4 * (2 * Real.log 2 - phaseGain7 td) ≤
          (0.6931471808 : ℝ) ^ 2 / 4 * (2 * 0.6931471808 - 268155713 / 400000000) :=
      mul_le_mul (by linarith) hspan.le hnonneg (by norm_num)
    linarith
  · have hneg_span : 2 * Real.log 2 - phaseGain7 td < 0 := not_le.mp hnonneg
    have hneg : (Real.log 2) ^ 2 / 4 * (2 * Real.log 2 - phaseGain7 td) < 0 :=
      mul_neg_of_pos_of_neg (by positivity) hneg_span
    linarith

/-! ## 3. Uniform support-limit convergence `𝓕_{S_{0,M}} → 𝓕_{S_{≥ 1}}` (`Lemma 3.2(iii)`) -/

theorem S07_subset_S0M {M : ℕ} (hM : 7 ≤ M) : S07 ⊆ S0M M := by
  intro i hi
  simp only [S07, S0M, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hi ⊢
  omega

theorem S0M_subset_Sge1 (M : ℕ) : S0M M ⊆ Sge1 := by
  intro i hi
  simp only [S0M, Sge1, Set.mem_setOf_eq] at hi ⊢
  exact hi.1

theorem partitionFn_Sge1_eq_tsum (lambda : ℝ) :
    partitionFn Sge1 lambda = ∑' k : ℕ, gaussWeight lambda ((k : ℤ) + 1) := by
  unfold partitionFn
  let e : ℕ ≃ Sge1 :=
    { toFun := fun k ↦ ⟨(k : ℤ) + 1, by change (1 : ℤ) ≤ (k : ℤ) + 1; omega⟩
      invFun := fun i ↦ (i.1 - 1).toNat
      left_inv := fun k ↦ by dsimp only; omega
      right_inv := fun i ↦ Subtype.ext (by
        dsimp only
        have hi : (1 : ℤ) ≤ i.1 := i.2
        omega) }
  exact (e.tsum_eq (fun i : Sge1 ↦ gaussWeight lambda i.1)).symm

theorem partitionFn_S0M_eq_sum_range (M : ℕ) (lambda : ℝ) :
    partitionFn (S0M M) lambda =
      ∑ k ∈ Finset.range M, gaussWeight lambda ((k : ℤ) + 1) := by
  let F : Finset ℤ := (Finset.range M).map
    ⟨fun k : ℕ ↦ (k : ℤ) + 1, fun a b h ↦ by dsimp only at h; omega⟩
  have hcoe : (F : Set ℤ) = S0M M := by
    ext i
    simp only [F, S0M, Finset.mem_coe, Finset.mem_map, Finset.mem_range,
      Function.Embedding.coeFn_mk, Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, hk, rfl⟩; omega
    · rintro ⟨h1, hM⟩
      refine ⟨(i - 1).toNat, ?_, ?_⟩ <;> omega
  rw [← hcoe, partitionFn_coe_finset, Finset.sum_map]
  rfl

private theorem gaussWeight_succ_le_half_on_box {lambda : ℝ} (hl : lambda ≤ 8)
    {m : ℕ} (hm : 13 ≤ m) :
    gaussWeight lambda ((m : ℤ) + 2) ≤ 1 / 2 * gaussWeight lambda ((m : ℤ) + 1) := by
  have hqlo : (2 / 3 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hstep : gaussWeight lambda ((m : ℤ) + 2) =
      Real.exp (lambda - Real.log 2 / 2 * (2 * (m : ℝ) + 3)) *
        gaussWeight lambda ((m : ℤ) + 1) := by
    unfold gaussWeight
    rw [← Real.exp_add]
    push_cast
    congr 1
    ring
  have hmR : (13 : ℝ) ≤ m := by exact_mod_cast hm
  have hexp_le : lambda - Real.log 2 / 2 * (2 * (m : ℝ) + 3) ≤ -Real.log 2 := by
    nlinarith
  have hhalf : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log two_pos]; norm_num
  rw [hstep]
  refine mul_le_mul_of_nonneg_right ?_ (gaussWeight_pos _ _).le
  rw [← hhalf]
  exact Real.exp_le_exp.mpr hexp_le

private theorem partitionFn_Sge1_sub_S0M_le {M : ℕ} (hM : 13 ≤ M)
    {lambda : ℝ} (hl : lambda ≤ 8) :
    partitionFn Sge1 lambda - partitionFn (S0M M) lambda ≤
      2 * gaussWeight 8 ((M : ℤ) + 1) := by
  have hs : Summable (fun k : ℕ ↦ gaussWeight lambda ((k : ℤ) + 1)) := by
    refine ((summable_gaussWeight lambda).comp_injective
      (fun a b (h : (a : ℤ) + 1 = (b : ℤ) + 1) ↦ by omega))
  rw [partitionFn_Sge1_eq_tsum, partitionFn_S0M_eq_sum_range,
    ← hs.sum_add_tsum_nat_add M, add_sub_cancel_left]
  have hgeom : ∀ n : ℕ, gaussWeight lambda (((n + M : ℕ) : ℤ) + 1) ≤
      (1 / 2 : ℝ) ^ n * gaussWeight lambda ((M : ℤ) + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hcast : (((n + 1 + M : ℕ) : ℤ) + 1) = (((n + M : ℕ) : ℤ) + 2) := by
        push_cast; ring
      rw [hcast]
      calc gaussWeight lambda (((n + M : ℕ) : ℤ) + 2)
          ≤ 1 / 2 * gaussWeight lambda (((n + M : ℕ) : ℤ) + 1) :=
            gaussWeight_succ_le_half_on_box hl (by omega)
        _ ≤ 1 / 2 * ((1 / 2 : ℝ) ^ n * gaussWeight lambda ((M : ℤ) + 1)) :=
            mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (1 / 2 : ℝ) ^ (n + 1) * gaussWeight lambda ((M : ℤ) + 1) := by ring
  have hgs : Summable (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n * gaussWeight lambda ((M : ℤ) + 1)) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
  have htail : ∑' n : ℕ, gaussWeight lambda (((n + M : ℕ) : ℤ) + 1) ≤
      2 * gaussWeight lambda ((M : ℤ) + 1) := by
    calc ∑' n : ℕ, gaussWeight lambda (((n + M : ℕ) : ℤ) + 1)
        ≤ ∑' n : ℕ, (1 / 2 : ℝ) ^ n * gaussWeight lambda ((M : ℤ) + 1) :=
          Summable.tsum_le_tsum hgeom ((summable_nat_add_iff M).mpr hs) hgs
      _ = 2 * gaussWeight lambda ((M : ℤ) + 1) := by
          rw [tsum_mul_right,
            tsum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)]
          norm_num
  have hmono : gaussWeight lambda ((M : ℤ) + 1) ≤ gaussWeight 8 ((M : ℤ) + 1) := by
    unfold gaussWeight
    apply Real.exp_le_exp.mpr
    apply sub_le_sub_right
    have hMpos : (0 : ℝ) ≤ ((M : ℤ) + 1 : ℤ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ (M : ℤ) + 1)
    exact mul_le_mul_of_nonneg_right hl (by simpa using hMpos)
  linarith

/-- **Quantitative uniform support-limit bound (`Lemma 3.2(iii)`):**
for `M ≥ 13` and `T ∈ [11/4, 4]`,
`0 ≤ 𝓕_{S_{≥ 1}}(T) - 𝓕_{S_{0,M}}(T) ≤ 2 · w_{M+1}(8) / w_1(-4)`. -/
theorem dualValue_Sge1_sub_S0M_le {M : ℕ} (hM : 13 ≤ M)
    {T : ℝ} (hT : T ∈ Set.Icc (11 / 4 : ℝ) 4) :
    0 ≤ dualValue Sge1 T - dualValue (S0M M) T ∧
      dualValue Sge1 T - dualValue (S0M M) T ≤
        2 * gaussWeight 8 ((M : ℤ) + 1) / gaussWeight (-4) 1 := by
  have hT25 : T ∈ Set.Ioo (2 : ℝ) 5 := ⟨by linarith [hT.1], by linarith [hT.2]⟩
  have hm := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT25)
  have hS4M : S4 ⊆ S0M M := S4_subset_S07.trans (S07_subset_S0M (by omega))
  have hnonneg : 0 ≤ dualValue Sge1 T - dualValue (S0M M) T :=
    sub_nonneg.mpr (dualValue_mono hS4M (S0M_subset_Sge1 M) hm)
  refine ⟨hnonneg, ?_⟩
  set err : ℝ := 2 * gaussWeight 8 ((M : ℤ) + 1) / gaussWeight (-4) 1
  have herr_pos : 0 < err := by
    dsimp [err]
    exact div_pos (mul_pos two_pos (gaussWeight_pos _ _)) (gaussWeight_pos _ _)
  suffices dualValue Sge1 T - err ≤ dualValue (S0M M) T by linarith
  refine le_ciInf fun l ↦ ?_
  show dualValue Sge1 T - err ≤ Real.log (partitionFn (S0M M) l) - l * T
  have hZ0 : dualValue Sge1 T ≤ Real.log (partitionFn Sge1 0) := by
    simpa using dualValue_le_at S4_subset_Sge1 hm 0
  have hZ0_lt : Real.log (partitionFn Sge1 0) < 2 := by
    have hle0 : partitionFn Sge1 0 ≤ partitionFn Sge0 (yTilt 1) := by
      have h0le : (0 : ℝ) ≤ yTilt 1 := by
        unfold yTilt; rw [Real.log_one, add_zero]; exact (div_pos (Real.log_pos one_lt_two) two_pos).le
      calc partitionFn Sge1 0
          ≤ ∑' k : ℕ, gaussWeight (yTilt 1) ((k : ℤ) + 1) := by
            rw [partitionFn_Sge1_eq_tsum]
            refine Summable.tsum_le_tsum (fun k ↦ ?_)
              ((summable_gaussWeight 0).comp_injective (fun a b (h : (a : ℤ) + 1 = (b : ℤ) + 1) ↦ by omega))
              ((summable_gaussWeight (yTilt 1)).comp_injective (fun a b (h : (a : ℤ) + 1 = (b : ℤ) + 1) ↦ by omega))
            unfold gaussWeight
            apply Real.exp_le_exp.mpr
            apply sub_le_sub_right
            have hk : (0 : ℝ) ≤ ((k : ℤ) + 1 : ℤ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ (k : ℤ) + 1)
            exact mul_le_mul_of_nonneg_right h0le (by simpa using hk)
        _ = partitionFn Sge1 (yTilt 1) := (partitionFn_Sge1_eq_tsum (yTilt 1)).symm
        _ ≤ partitionFn Sge0 (yTilt 1) := partitionFn_mono Sge1_subset_Sge0 _
    have hb1 := partitionFn_Sge0_le_sge0BoundY (z := 1) one_pos (by norm_num)
    have hsge1_pos := partitionFn_pos_of_nonempty (S := Sge1) ⟨1, by simp [Sge1]⟩ 0
    have hbound_val : sge0BoundY 1 < Real.exp 2 := by
      unfold sge0BoundY sevenPartY
      have hexp2' : (4 : ℝ) < Real.exp 2 := by
        have h1 := Real.add_one_lt_exp (x := (1 : ℝ)) one_ne_zero
        have h2 : (4 : ℝ) < (Real.exp 1) ^ 2 := by nlinarith
        rwa [show (Real.exp 1) ^ 2 = Real.exp 2 by rw [← Real.exp_nat_mul]; norm_num] at h2
      linarith
    have hlt := Real.log_lt_log hsge1_pos (lt_of_le_of_lt (hle0.trans hb1) hbound_val)
    rwa [Real.log_exp] at hlt
  have h1mem : (1 : ℤ) ∈ S0M M := by simp [S0M]; omega
  have h7mem : (7 : ℤ) ∈ S0M M := by simp [S0M]; omega
  have hZM_ge_1 : gaussWeight l 1 ≤ partitionFn (S0M M) l :=
    (hasSum_partitionFn (S0M M) l).summable.le_tsum ⟨1, h1mem⟩
      (fun j _ ↦ (gaussWeight_pos l j.1).le)
  have hZM_ge_7 : gaussWeight l 7 ≤ partitionFn (S0M M) l :=
    (hasSum_partitionFn (S0M M) l).summable.le_tsum ⟨7, h7mem⟩
      (fun j _ ↦ (gaussWeight_pos l j.1).le)
  have hqhi : Real.log 2 < (7 / 10 : ℝ) := lt_trans Real.log_two_lt_d9 (by norm_num)
  rcases lt_or_ge l (-4) with hl_lo | hl_lo
  · have hlog1 : l - Real.log 2 / 2 ≤ Real.log (partitionFn (S0M M) l) := by
      have := Real.log_le_log (gaussWeight_pos l 1) hZM_ge_1
      unfold gaussWeight at this
      rw [Real.log_exp] at this
      push_cast at this
      linarith
    have : (6 : ℝ) < (l - Real.log 2 / 2) - l * T := by
      nlinarith [hT.1]
    linarith
  rcases lt_or_ge 8 l with hl_hi | hl_hi
  · have hlog7 : 7 * l - Real.log 2 / 2 * 49 ≤ Real.log (partitionFn (S0M M) l) := by
      have := Real.log_le_log (gaussWeight_pos l 7) hZM_ge_7
      unfold gaussWeight at this
      rw [Real.log_exp] at this
      push_cast at this
      linarith
    have : (6 : ℝ) < (7 * l - Real.log 2 / 2 * 49) - l * T := by
      nlinarith [hT.2]
    linarith
  · have hZge1_at_l := dualValue_le_at S4_subset_Sge1 hm l
    have hZM_pos := partitionFn_pos_of_nonempty ⟨1, h1mem⟩ l
    have hZM_lb : gaussWeight (-4) 1 ≤ partitionFn (S0M M) l := by
      refine le_trans ?_ hZM_ge_1
      unfold gaussWeight
      apply Real.exp_le_exp.mpr
      push_cast
      linarith
    have hdiff := partitionFn_Sge1_sub_S0M_le hM hl_hi
    have hZge1_le : partitionFn Sge1 l ≤ partitionFn (S0M M) l * (1 + err) := by
      have h1 : 2 * gaussWeight 8 ((M : ℤ) + 1) ≤ partitionFn (S0M M) l * err := by
        dsimp [err]
        rw [mul_div_assoc', le_div_iff₀ (gaussWeight_pos (-4) 1)]
        nlinarith [hZM_lb, gaussWeight_pos 8 ((M : ℤ) + 1)]
      linarith
    have hlog_step : Real.log (partitionFn Sge1 l) ≤ Real.log (partitionFn (S0M M) l) + err := by
      have h1 := Real.log_le_log (partitionFn_pos_of_nonempty (S := Sge1) ⟨1, by simp [Sge1]⟩ l) hZge1_le
      rw [Real.log_mul hZM_pos.ne' (by linarith [herr_pos])] at h1
      have hlog1p : Real.log (1 + err) ≤ err := by
        have := Real.log_le_sub_one_of_pos (x := 1 + err) (by linarith [herr_pos])
        linarith
      linarith
    linarith

/-- **Uniform support-limit convergence `𝓕_{S_{0,M}} → 𝓕_{S_{≥ 1}}` on `[11/4, 4]`
(`Lemma 3.2(iii)`).** -/
theorem tendstoUniformlyOn_dualValue_S0M_Sge1 :
    ∀ eps : ℝ, 0 < eps → ∃ M₀ : ℕ, 7 ≤ M₀ ∧
      ∀ M ≥ M₀, ∀ T ∈ Set.Icc (11 / 4 : ℝ) 4,
        0 ≤ dualValue Sge1 T - dualValue (S0M M) T ∧
          dualValue Sge1 T - dualValue (S0M M) T < eps := by
  intro eps heps
  have hs : Summable (fun M : ℕ ↦ gaussWeight 8 ((M : ℤ) + 1)) :=
    (summable_gaussWeight 8).comp_injective (fun a b (h : (a : ℤ) + 1 = (b : ℤ) + 1) ↦ by omega)
  have htend : Tendsto (fun M : ℕ ↦ 2 * gaussWeight 8 ((M : ℤ) + 1) / gaussWeight (-4) 1)
      atTop (nhds 0) := by
    simpa using ((hs.tendsto_atTop_zero.const_mul 2).div_const (gaussWeight (-4) 1))
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp htend) eps heps
  refine ⟨max 13 N, le_trans (by norm_num) (le_max_left 13 N), fun M hM T hT ↦ ?_⟩
  obtain ⟨h0, hle⟩ := dualValue_Sge1_sub_S0M_le (le_trans (le_max_left 13 N) hM) hT
  have hlt := hN M (le_trans (le_max_right 13 N) hM)
  have hdpos : 0 < 2 * gaussWeight 8 ((M : ℤ) + 1) / gaussWeight (-4) 1 :=
    div_pos (mul_pos two_pos (gaussWeight_pos _ _)) (gaussWeight_pos _ _)
  rw [Real.dist_eq, sub_zero, abs_of_pos hdpos] at hlt
  exact ⟨h0, lt_of_le_of_lt hle hlt⟩

/-! ## 4. Critical phase `x₀ ∈ (0.0290, 0.0291)` (`Lemma 5.2(i)`) -/

/-- Unique tilt `λ_{S_{≥ 1}}(T)` on `S_{≥ 1}` via the `+2` shift of `S₊`. -/
def sge1Tilt (T : ℝ) : ℝ :=
  extendedGaussianTilt q (T - 2) + 2 * q

/-- Probability `p_{1,∞}(δ)` assigned to deficit `1` by the Gibbs law on `S_{≥ 1}`
with mean `T_δ` (equation `(0.1)` of the manuscript). -/
def p1Inf (delta : ℝ) : ℝ :=
  gaussWeight (sge1Tilt (phaseTarget delta)) 1 /
    partitionFn Sge1 (sge1Tilt (phaseTarget delta))

/-- Auxiliary function `g(p) = (1 - p) log(1 - p) / p` on `(0, 1)`. -/
def phiInfAux (p : ℝ) : ℝ :=
  (1 - p) * Real.log (1 - p) / p

/-- The exact threshold function `φ_∞(δ)` of equation `(0.1)` in the manuscript. -/
def phiInf (delta : ℝ) : ℝ :=
  phiInfAux (p1Inf delta) + Real.log 2 / 2 * (phaseTarget delta - 1)

theorem partitionFn_Sge1_eq_shift_extendedGaussian (lambda : ℝ) :
    partitionFn Sge1 lambda =
      Real.exp (2 * lambda - 2 * q) * extendedGaussianPartition q (lambda - 2 * q) := by
  have h1 := partitionFn_shiftSupportOne Sge0 lambda
  have h2 := partitionFn_shiftSupportOne Splus (lambda - Real.log 2)
  rw [shiftSupportOne_Sge0] at h1
  rw [shiftSupportOne_Splus] at h2
  rw [h1, h2, partitionFn_Splus]
  unfold q
  rw [← mul_assoc, ← Real.exp_add]
  congr 2 <;> ring

/-- `p₁` as an explicit function of the `S₊`-shifted tilt `μ = λ - 2q`. -/
def p1AtTilt (mu : ℝ) : ℝ :=
  extendedGaussianExceptionalAtom q mu / extendedGaussianPartition q mu

theorem p1Inf_eq_p1AtTilt (delta : ℝ) :
    p1Inf delta = p1AtTilt (extendedGaussianTilt q (phaseTarget delta - 2)) := by
  unfold p1Inf p1AtTilt sge1Tilt
  set mu := extendedGaussianTilt q (phaseTarget delta - 2)
  have hZ := partitionFn_Sge1_eq_shift_extendedGaussian (mu + 2 * q)
  rw [add_sub_cancel_right] at hZ
  have hw1 : gaussWeight (mu + 2 * q) 1 =
      Real.exp (2 * (mu + 2 * q) - 2 * q) * extendedGaussianExceptionalAtom q mu := by
    unfold gaussWeight extendedGaussianExceptionalAtom q
    rw [← Real.exp_add]
    push_cast
    congr 1
    ring
  rw [hw1, hZ, mul_div_mul_left _ _ (Real.exp_pos _).ne']

theorem p1AtTilt_mem_Ioo (mu : ℝ) : p1AtTilt mu ∈ Set.Ioo (0 : ℝ) 1 := by
  unfold p1AtTilt
  have he := extendedGaussianExceptionalAtom_pos q mu
  have hm : 0 < ∑' d : ℕ, extendedGaussianNaturalTerm q mu d :=
    lt_of_lt_of_le zero_lt_one (one_le_tsum_extendedGaussianNaturalTerm q_pos)
  have hZ : 0 < extendedGaussianPartition q mu := by
    unfold extendedGaussianPartition; linarith
  refine ⟨div_pos he hZ, (div_lt_one hZ).mpr ?_⟩
  unfold extendedGaussianPartition
  linarith

theorem strictAnti_p1AtTilt : StrictAnti p1AtTilt := by
  intro mu1 mu2 hlt
  unfold p1AtTilt
  set e1 := extendedGaussianExceptionalAtom q mu1
  set e2 := extendedGaussianExceptionalAtom q mu2
  set m1 := ∑' d : ℕ, extendedGaussianNaturalTerm q mu1 d
  set m2 := ∑' d : ℕ, extendedGaussianNaturalTerm q mu2 d
  have he1 : 0 < e1 := extendedGaussianExceptionalAtom_pos q mu1
  have he2 : 0 < e2 := extendedGaussianExceptionalAtom_pos q mu2
  have hm1 : 0 < m1 :=
    lt_of_lt_of_le zero_lt_one (one_le_tsum_extendedGaussianNaturalTerm q_pos)
  have hm2 : 0 < m2 :=
    lt_of_lt_of_le zero_lt_one (one_le_tsum_extendedGaussianNaturalTerm q_pos)
  have he_lt : e2 < e1 := by
    dsimp [e1, e2]; unfold extendedGaussianExceptionalAtom
    exact Real.exp_lt_exp.mpr (by linarith)
  have hm_le : m1 ≤ m2 := by
    dsimp [m1, m2]
    refine Summable.tsum_le_tsum (fun d ↦ ?_)
      (summable_extendedGaussianNaturalTerm q_pos)
      (summable_extendedGaussianNaturalTerm q_pos)
    unfold extendedGaussianNaturalTerm
    apply Real.exp_le_exp.mpr
    have hd : (0 : ℝ) ≤ d := by positivity
    nlinarith
  have hZ1 : 0 < extendedGaussianPartition q mu1 := by
    unfold extendedGaussianPartition; dsimp [e1, m1] at *; linarith
  have hZ2 : 0 < extendedGaussianPartition q mu2 := by
    unfold extendedGaussianPartition; dsimp [e2, m2] at *; linarith
  rw [div_lt_div_iff₀ hZ2 hZ1]
  change e2 * (e1 + m1) < e1 * (e2 + m2)
  nlinarith

/-- Pointwise inequality `-p - log(1 - p) < p² / (2(1 - p))` for `p ∈ (0, 1)`,
proved via `d/dp [p²/(2(1-p)) + p + log(1-p)] = p² / (2(1-p)²) > 0`. -/
private theorem neg_sub_log_one_sub_lt {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    -p - Real.log (1 - p) < p ^ 2 / (2 * (1 - p)) := by
  let f : ℝ → ℝ := fun x ↦ x ^ 2 / (2 * (1 - x)) + x + Real.log (1 - x)
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt f (x ^ 2 / (2 * (1 - x) ^ 2)) x := by
    intro x hx
    have h1x : 1 - x ≠ 0 := by linarith [hx.2]
    have h2x : 2 * (1 - x) ≠ 0 := by linarith [hx.2]
    have hd_num : HasDerivAt (fun t : ℝ ↦ t ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x)
    have hd_1mx : HasDerivAt (fun t : ℝ ↦ 1 - t) (-1) x :=
      ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).congr_deriv (by ring)
    have hd_den : HasDerivAt (fun t : ℝ ↦ 2 * (1 - t)) (-2) x :=
      (hd_1mx.const_mul 2).congr_deriv (by ring)
    have hd_q := hd_num.div hd_den h2x
    have hd_l := hd_1mx.log h1x
    have hd_all := (hd_q.add (hasDerivAt_id x)).add hd_l
    refine hd_all.congr_deriv ?_
    field_simp [h1x]
    ring
  have hcont : ContinuousOn f (Set.Icc 0 p) := by
    intro x hx
    have h1x : 1 - x ≠ 0 := by linarith [hx.2, hp1]
    have h2x : 2 * (1 - x) ≠ 0 := by linarith [hx.2, hp1]
    exact (((continuousAt_id.pow 2).div
      (continuousAt_const.mul (continuousAt_const.sub continuousAt_id)) h2x).add
      continuousAt_id |>.add
      ((continuousAt_const.sub continuousAt_id).log h1x)).continuousWithinAt
  have hmono : StrictMonoOn f (Set.Icc 0 p) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 p) hcont
    intro x hx
    rw [interior_Icc] at hx
    have hx01 : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx.1, lt_trans hx.2 hp1⟩
    rw [(hderiv x hx01).deriv]
    exact div_pos (sq_pos_of_pos hx01.1) (mul_pos two_pos (sq_pos_of_pos (sub_pos.mpr hx01.2)))
  have hf0 : f 0 = 0 := by simp [f]
  have hpos : 0 < f p := by
    rw [← hf0]
    exact hmono ⟨le_rfl, hp0.le⟩ ⟨hp0.le, le_rfl⟩ hp0
  dsimp [f] at hpos
  linarith

theorem strictMonoOn_phiInfAux : StrictMonoOn phiInfAux (Set.Ioo (0 : ℝ) 1) := by
  have hderiv : ∀ p ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt phiInfAux ((-p - Real.log (1 - p)) / p ^ 2) p := by
    intro p hp
    have hp0 : p ≠ 0 := hp.1.ne'
    have h1p : 1 - p ≠ 0 := by linarith [hp.2]
    have hd_1mp : HasDerivAt (fun t : ℝ ↦ 1 - t) (-1) p :=
      ((hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p)).congr_deriv (by ring)
    have hd_num : HasDerivAt (fun t : ℝ ↦ (1 - t) * Real.log (1 - t))
        ((-1) * Real.log (1 - p) + (1 - p) * ((-1) / (1 - p))) p :=
      hd_1mp.mul (hd_1mp.log h1p)
    have hd_id : HasDerivAt (fun t : ℝ ↦ t) 1 p := hasDerivAt_id p
    have hd_q := hd_num.div hd_id hp0
    refine hd_q.congr_deriv ?_
    field_simp [hp0, h1p]
    ring
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 1)
  · intro p hp
    exact (hderiv p hp).continuousAt.continuousWithinAt
  · intro p hp
    rw [isOpen_Ioo.interior_eq] at hp
    rw [(hderiv p hp).deriv]
    have h1p_pos : 0 < 1 - p := by linarith [hp.2]
    have hlog : Real.log (1 - p) < -p := by
      have := Real.log_lt_sub_one_of_pos h1p_pos (by linarith [hp.1])
      linarith
    have hnum : 0 < -p - Real.log (1 - p) := by linarith
    exact div_pos hnum (sq_pos_of_pos hp.1)

/-- **Key Cauchy–Schwarz variance bound (`Appendix B.2, Part (i)`):**
`Var(μ) ≥ (p₁(μ) / (1 - p₁(μ))) · (mean(μ) + 1)²`. -/
private theorem extendedGaussianRawVariance_ge_p1_mul_sq (mu : ℝ) :
    p1AtTilt mu / (1 - p1AtTilt mu) * (extendedGaussianMean q mu + 1) ^ 2 ≤
      extendedGaussianRawVariance q mu := by
  set e := extendedGaussianExceptionalAtom q mu
  set m := ∑' d : ℕ, extendedGaussianNaturalTerm q mu d
  set M1 := ∑' d : ℕ, (d : ℝ) * extendedGaussianNaturalTerm q mu d
  set M2 := ∑' d : ℕ, ((d : ℝ) ^ 2) * extendedGaussianNaturalTerm q mu d
  have he : 0 < e := extendedGaussianExceptionalAtom_pos q mu
  have hm : 0 < m :=
    lt_of_lt_of_le zero_lt_one (one_le_tsum_extendedGaussianNaturalTerm q_pos)
  have hcs : M1 ^ 2 ≤ M2 * m := extendedGaussianNatural_cauchySchwarz q mu q_pos
  have hp_ratio : p1AtTilt mu / (1 - p1AtTilt mu) = e / m := by
    unfold p1AtTilt
    change (e / (e + m)) / (1 - e / (e + m)) = e / m
    have hem : e + m ≠ 0 := by linarith
    field_simp [hem, hm.ne']
    ring
  have hmean1 : extendedGaussianMean q mu + 1 = (m + M1) / (e + m) := by
    unfold extendedGaussianMean extendedGaussianFirstNumerator extendedGaussianPartition
    change (-e + M1) / (e + m) + 1 = (m + M1) / (e + m)
    have hem : e + m ≠ 0 := by linarith
    field_simp [hem]
    ring
  have hvar : extendedGaussianRawVariance q mu =
      ((e + M2) * (e + m) - (-e + M1) ^ 2) / (e + m) ^ 2 := by
    unfold extendedGaussianRawVariance extendedGaussianMean
      extendedGaussianSecondNumerator extendedGaussianFirstNumerator
      extendedGaussianPartition
    change (e + M2) / (e + m) - ((-e + M1) / (e + m)) ^ 2 = _
    have hem : e + m ≠ 0 := by linarith
    field_simp [hem]
  rw [hp_ratio, hmean1, hvar, div_pow, mul_div_assoc']
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [div_mul_eq_mul_div, div_le_iff₀ hm]
  nlinarith [mul_le_mul_of_nonneg_left hcs (by linarith : 0 ≤ e + m)]

/-- Tilt-parametrized form of `φ_∞`: `φ̃(μ) = g(p₁(μ)) + (q/2)(mean(μ) + 1)`. -/
private def phiTilt (mu : ℝ) : ℝ :=
  phiInfAux (p1AtTilt mu) + q / 2 * (extendedGaussianMean q mu + 1)

private theorem hasDerivAt_p1AtTilt (mu : ℝ) :
    HasDerivAt p1AtTilt (-p1AtTilt mu * (extendedGaussianMean q mu + 1)) mu := by
  have he : HasDerivAt (extendedGaussianExceptionalAtom q)
      (-extendedGaussianExceptionalAtom q mu) mu := by
    unfold extendedGaussianExceptionalAtom
    simpa only [Pi.neg_apply, id_eq, mul_neg, mul_one] using
      (((hasDerivAt_id mu).neg.sub_const (q / 2)).exp)
  have hZ := hasDerivAt_extendedGaussianPartition q mu q_pos
  have hZpos := extendedGaussianPartition_pos q_pos (lambda := mu)
  have hq := he.div hZ hZpos.ne'
  refine hq.congr_deriv ?_
  unfold p1AtTilt extendedGaussianMean
  field_simp [hZpos.ne']
  ring

private theorem strictMonoOn_phiTilt :
    StrictMonoOn phiTilt (Set.Ioi (extendedGaussianTilt q (-1 + 1 / q))) := by
  set mu0 := extendedGaussianTilt q (-1 + 1 / q)
  have ht0 : -1 < -1 + 1 / q := by linarith [div_pos one_pos q_pos]
  have hmean0 : extendedGaussianMean q mu0 = -1 + 1 / q :=
    extendedGaussianMean_extendedGaussianTilt q_pos ht0
  have hderiv : ∀ mu ∈ Set.Ioi mu0,
      ∃ d : ℝ, 0 < d ∧ HasDerivAt phiTilt d mu := by
    intro mu hmu
    have hmean_gt : -1 + 1 / q < extendedGaussianMean q mu := by
      rw [← hmean0]
      exact strictMono_extendedGaussianMean q q_pos hmu
    set p := p1AtTilt mu
    obtain ⟨hp0, hp1⟩ := p1AtTilt_mem_Ioo mu
    have hd_g : HasDerivAt phiInfAux ((-p - Real.log (1 - p)) / p ^ 2) p := by
      have hp0' : p ≠ 0 := hp0.ne'
      have h1p : 1 - p ≠ 0 := by linarith
      have hd_1mp : HasDerivAt (fun t : ℝ ↦ 1 - t) (-1) p :=
        ((hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p)).congr_deriv (by ring)
      have hd_num : HasDerivAt (fun t : ℝ ↦ (1 - t) * Real.log (1 - t))
          ((-1) * Real.log (1 - p) + (1 - p) * ((-1) / (1 - p))) p :=
        hd_1mp.mul (hd_1mp.log h1p)
      have hd_id : HasDerivAt (fun t : ℝ ↦ t) 1 p := hasDerivAt_id p
      exact (hd_num.div hd_id hp0').congr_deriv (by field_simp [hp0', h1p]; ring)
    have hd_p := hasDerivAt_p1AtTilt mu
    have hd_comp := hd_g.comp mu hd_p
    have hd_m := ((hasDerivAt_extendedGaussianMean q mu q_pos).add_const 1).const_mul (q / 2)
    have hd_sum := hd_comp.add hd_m
    refine ⟨_, ?_, hd_sum⟩
    set S := extendedGaussianMean q mu + 1
    have hS_gt : 1 / q < S := by dsimp [S]; linarith
    have hS_pos : 0 < S := lt_trans (div_pos one_pos q_pos) hS_gt
    have hg_lt := neg_sub_log_one_sub_lt hp0 hp1
    have hvar_ge := extendedGaussianRawVariance_ge_p1_mul_sq mu
    have hterm1 : ((-p - Real.log (1 - p)) / p ^ 2) * (-p * S) >
        -(p / (2 * (1 - p)) * S) := by
      have h1 : ((-p - Real.log (1 - p)) / p ^ 2) * (p * S) <
          (p ^ 2 / (2 * (1 - p)) / p ^ 2) * (p * S) := by
        apply mul_lt_mul_of_pos_right _ (mul_pos hp0 hS_pos)
        exact div_lt_div_of_pos_right hg_lt (sq_pos_of_pos hp0)
      have h2 : (p ^ 2 / (2 * (1 - p)) / p ^ 2) * (p * S) = p / (2 * (1 - p)) * S := by
        have hp_ne : p ≠ 0 := hp0.ne'
        have h1p_ne : 1 - p ≠ 0 := by linarith
        field_simp [hp_ne, h1p_ne]
      linarith
    have hterm2 : q / 2 * (p / (1 - p) * S ^ 2) ≤ q / 2 * extendedGaussianRawVariance q mu :=
      mul_le_mul_of_nonneg_left hvar_ge (div_nonneg q_pos.le zero_le_two)
    have hqS : 1 < q * S := by
      have := (div_lt_iff₀ q_pos).mp hS_gt
      linarith
    have hgap : 0 < q / 2 * (p / (1 - p) * S ^ 2) - p / (2 * (1 - p)) * S := by
      have hpos_fac : 0 < p * S / (2 * (1 - p)) :=
        div_pos (mul_pos hp0 hS_pos) (by linarith)
      have hid : q / 2 * (p / (1 - p) * S ^ 2) - p / (2 * (1 - p)) * S =
          (p * S / (2 * (1 - p))) * (q * S - 1) := by
        have h1p_ne : 1 - p ≠ 0 := by linarith
        field_simp [h1p_ne]
      rw [hid]
      exact mul_pos hpos_fac (by linarith)
    linarith
  have hcont_phi : ContinuousOn phiTilt (Set.Ioi mu0) := by
    intro mu hmu
    obtain ⟨_, _, hd⟩ := hderiv mu hmu
    exact hd.continuousAt.continuousWithinAt
  apply strictMonoOn_of_deriv_pos (convex_Ioi mu0) hcont_phi
  intro mu hmu
  rw [isOpen_Ioi.interior_eq] at hmu
  obtain ⟨d, hd_pos, hd⟩ := hderiv mu hmu
  rwa [hd.deriv]

private theorem continuousOn_extendedGaussianTilt_Ioi :
    ContinuousOn (extendedGaussianTilt q) (Set.Ioi (-1 : ℝ)) := by
  rw [Metric.continuousOn_iff]
  intro t0 ht0 eps heps
  set mu0 := extendedGaussianTilt q t0
  have hm0 : extendedGaussianMean q mu0 = t0 :=
    extendedGaussianMean_extendedGaussianTilt q_pos ht0
  have hsm := strictMono_extendedGaussianMean q q_pos
  set tlo := extendedGaussianMean q (mu0 - eps)
  set thi := extendedGaussianMean q (mu0 + eps)
  have hlo : tlo < t0 := by rw [← hm0]; exact hsm (by linarith)
  have hhi : t0 < thi := by rw [← hm0]; exact hsm (by linarith)
  refine ⟨min (t0 - tlo) (thi - t0), lt_min (by linarith) (by linarith), fun t ht hdist ↦ ?_⟩
  rw [Real.dist_eq] at hdist ⊢
  have hmt : extendedGaussianMean q (extendedGaussianTilt q t) = t :=
    extendedGaussianMean_extendedGaussianTilt q_pos ht
  have hd1 : |t - t0| < t0 - tlo := lt_of_lt_of_le hdist (min_le_left _ _)
  have hd2 : |t - t0| < thi - t0 := lt_of_lt_of_le hdist (min_le_right _ _)
  have ht_gt : tlo < t := by linarith [(abs_lt.mp hd1).1]
  have ht_lt : t < thi := by linarith [(abs_lt.mp hd2).2]
  have hmu_gt : mu0 - eps < extendedGaussianTilt q t := by
    apply hsm.lt_iff_lt.mp; rw [hmt]; exact ht_gt
  have hmu_lt : extendedGaussianTilt q t < mu0 + eps := by
    apply hsm.lt_iff_lt.mp; rw [hmt]; exact ht_lt
  rw [abs_lt]
  exact ⟨by linarith, by linarith⟩

private theorem phiInf_eq_phiTilt_comp {delta : ℝ} (hd : delta ≤ 207 / 200) :
    phiInf delta = phiTilt (extendedGaussianTilt q (phaseTarget delta - 2)) := by
  obtain ⟨hA, _⟩ := two_div_log_two_bounds
  have ht : -1 < phaseTarget delta - 2 := by
    unfold phaseTarget; linarith
  unfold phiInf phiTilt
  rw [p1Inf_eq_p1AtTilt, extendedGaussianMean_extendedGaussianTilt q_pos ht]
  unfold q
  ring

/-- **Continuity of `φ_∞` on `[0, 207 / 200]` (`Lemma 5.2(i)`).** -/
theorem continuousOn_phiInf :
    ContinuousOn phiInf (Set.Icc (0 : ℝ) (207 / 200)) := by
  obtain ⟨hA, _⟩ := two_div_log_two_bounds
  have hlin : ContinuousOn (fun d : ℝ ↦ phaseTarget d - 2) (Set.Icc 0 (207 / 200)) := by
    unfold phaseTarget
    exact (continuousOn_const.sub continuousOn_id).sub continuousOn_const
  have hmaps : Set.MapsTo (fun d : ℝ ↦ phaseTarget d - 2)
      (Set.Icc 0 (207 / 200)) (Set.Ioi (-1 : ℝ)) := by
    intro d hd; unfold phaseTarget; change -1 < 1 + 2 / Real.log 2 - d - 2; linarith [hd.2]
  have htilt_cont : ContinuousOn (fun d : ℝ ↦ extendedGaussianTilt q (phaseTarget d - 2))
      (Set.Icc 0 (207 / 200)) :=
    continuousOn_extendedGaussianTilt_Ioi.comp hlin hmaps
  have hphiTilt_cont : Continuous phiTilt := by
    have hp_cont : Continuous p1AtTilt :=
      continuous_iff_continuousAt.mpr fun mu ↦ (hasDerivAt_p1AtTilt mu).continuousAt
    have hg_cont : Continuous (fun mu ↦ phiInfAux (p1AtTilt mu)) := by
      rw [continuous_iff_continuousAt]
      intro mu
      obtain ⟨hp0, hp1⟩ := p1AtTilt_mem_Ioo mu
      have hg_at : ContinuousAt phiInfAux (p1AtTilt mu) := by
        unfold phiInfAux
        exact (((continuousAt_const.sub continuousAt_id).mul
          ((continuousAt_const.sub continuousAt_id).log (sub_pos.mpr hp1).ne')).div
          continuousAt_id hp0.ne')
      exact hg_at.comp hp_cont.continuousAt
    exact hg_cont.add (continuous_const.mul ((continuous_extendedGaussianMean q q_pos).add continuous_const))
  refine (hphiTilt_cont.comp_continuousOn htilt_cont).congr ?_
  intro d hd
  exact phiInf_eq_phiTilt_comp hd.2

/-- **Strict decrease of `φ_∞` on `[0, 207 / 200]` (`Lemma 5.2(i)`).** -/
theorem strictAntiOn_phiInf :
    StrictAntiOn phiInf (Set.Icc (0 : ℝ) (207 / 200)) := by
  obtain ⟨hA, _⟩ := two_div_log_two_bounds
  have hqhi : q < (7 / 10 : ℝ) := lt_trans Real.log_two_lt_d9 (by norm_num)
  have h1q : 1 / q < 3 / 2 := by
    rw [div_lt_iff₀ q_pos]
    have : (2 / 3 : ℝ) < q := lt_trans (by norm_num) Real.log_two_gt_d9
    linarith
  intro d1 hd1 d2 hd2 hlt
  rw [phiInf_eq_phiTilt_comp hd1.2, phiInf_eq_phiTilt_comp hd2.2]
  set mu1 := extendedGaussianTilt q (phaseTarget d1 - 2)
  set mu2 := extendedGaussianTilt q (phaseTarget d2 - 2)
  have ht1 : -1 + 1 / q < phaseTarget d1 - 2 := by
    unfold phaseTarget; linarith [hd1.2]
  have ht2 : -1 + 1 / q < phaseTarget d2 - 2 := by
    unfold phaseTarget; linarith [hd2.2]
  have ht0 : -1 < -1 + 1 / q := by linarith [div_pos one_pos q_pos]
  have hsm := strictMono_extendedGaussianMean q q_pos
  have hmu2_mem : mu2 ∈ Set.Ioi (extendedGaussianTilt q (-1 + 1 / q)) := by
    apply hsm.lt_iff_lt.mp
    rw [extendedGaussianMean_extendedGaussianTilt q_pos ht0,
      extendedGaussianMean_extendedGaussianTilt q_pos (lt_trans ht0 ht2)]
    exact ht2
  have hmu1_mem : mu1 ∈ Set.Ioi (extendedGaussianTilt q (-1 + 1 / q)) := by
    apply hsm.lt_iff_lt.mp
    rw [extendedGaussianMean_extendedGaussianTilt q_pos ht0,
      extendedGaussianMean_extendedGaussianTilt q_pos (lt_trans ht0 ht1)]
    exact ht1
  have hmu_lt : mu2 < mu1 := by
    apply hsm.lt_iff_lt.mp
    rw [extendedGaussianMean_extendedGaussianTilt q_pos (lt_trans ht0 ht2),
      extendedGaussianMean_extendedGaussianTilt q_pos (lt_trans ht0 ht1)]
    unfold phaseTarget
    linarith
  exact strictMonoOn_phiTilt hmu2_mem hmu1_mem hmu_lt

/-! ### Exact rational bracket `0.0290 < x₀ < 0.0291` -/

private def ninePartY (y : ℝ) : ℝ :=
  sevenPartY y + y ^ 8 / 268435456 + y ^ 9 / 68719476736

private def nineFirstY (y : ℝ) : ℝ :=
  sevenFirstY y + 8 * (y ^ 8 / 268435456) + 9 * (y ^ 9 / 68719476736)

private def nineMeanY (y : ℝ) : ℝ := nineFirstY y / ninePartY y

private def sge1Bound9Y (y : ℝ) : ℝ :=
  ninePartY y + 8 / 7 * (y ^ 10 / 35184372088832)

private def sge1MeanUb9Y (y : ℝ) : ℝ :=
  (nineFirstY y + 80 / 7 * (y ^ 10 / 35184372088832)) / ninePartY y

private theorem two_div_log_two_bounds_d8 :
    (288539008 / 100000000 : ℝ) < 2 / Real.log 2 ∧
      2 / Real.log 2 < 288539009 / 100000000 := by
  have hq0 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hqlo := Real.log_two_gt_d9
  have hqhi := Real.log_two_lt_d9
  constructor
  · rw [lt_div_iff₀ hq0]; linarith
  · rw [div_lt_iff₀ hq0]; linarith

private theorem shifted_weights_nine {y : ℝ} (hy : 0 < y) :
    let mu := yTilt y - 2 * q
    let S := y ^ 2 / 2
    S * extendedGaussianExceptionalAtom q mu = y ∧
      S * extendedGaussianNaturalTerm q mu 0 = y ^ 2 / 2 ∧
      S * extendedGaussianNaturalTerm q mu 1 = y ^ 3 / 8 ∧
      S * extendedGaussianNaturalTerm q mu 2 = y ^ 4 / 64 ∧
      S * extendedGaussianNaturalTerm q mu 3 = y ^ 5 / 1024 ∧
      S * extendedGaussianNaturalTerm q mu 4 = y ^ 6 / 32768 ∧
      S * extendedGaussianNaturalTerm q mu 5 = y ^ 7 / 2097152 ∧
      S * extendedGaussianNaturalTerm q mu 6 = y ^ 8 / 268435456 ∧
      S * extendedGaussianNaturalTerm q mu 7 = y ^ 9 / 68719476736 ∧
      S * extendedGaussianNaturalTerm q mu 8 = y ^ 10 / 35184372088832 := by
  intro mu S
  have hS : S = Real.exp (2 * yTilt y - 2 * q) := by
    dsimp [S]
    unfold yTilt q
    have h1 : 2 * (Real.log 2 / 2 + Real.log y) - 2 * Real.log 2 =
        2 * Real.log y - Real.log 2 := by ring
    rw [h1, Real.exp_sub, show (2 : ℝ) * Real.log y = ((2 : ℕ) : ℝ) * Real.log y by norm_num,
      Real.exp_nat_mul, Real.exp_log hy, Real.exp_log two_pos]
  have hterm (d : ℕ) :
      S * extendedGaussianNaturalTerm q mu d = gaussWeight (yTilt y) ((d : ℤ) + 2) := by
    rw [hS]
    unfold extendedGaussianNaturalTerm gaussWeight
    dsimp [mu]
    unfold q
    rw [← Real.exp_add]
    push_cast
    congr 1
    ring
  have hexc : S * extendedGaussianExceptionalAtom q mu = gaussWeight (yTilt y) 1 := by
    rw [hS]
    unfold extendedGaussianExceptionalAtom gaussWeight
    dsimp [mu]
    unfold q
    rw [← Real.exp_add]
    push_cast
    congr 1
    ring
  obtain ⟨-, -, w1, w2, w3, w4, w5, w6, w7⟩ := weights_yTilt y hy
  have w8 : gaussWeight (yTilt y) 8 = y ^ 8 / 268435456 := by
    rw [gaussWeight_yTilt y hy 8 8 28 (by norm_num) (by norm_num)]; norm_num
  have w9 : gaussWeight (yTilt y) 9 = y ^ 9 / 68719476736 := by
    rw [gaussWeight_yTilt y hy 9 9 36 (by norm_num) (by norm_num)]; norm_num
  have w10 : gaussWeight (yTilt y) 10 = y ^ 10 / 35184372088832 := by
    rw [gaussWeight_yTilt y hy 10 10 45 (by norm_num) (by norm_num)]; norm_num
  refine ⟨by rw [hexc, w1], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using (hterm 0).trans w2
  · simpa using (hterm 1).trans w3
  · simpa using (hterm 2).trans w4
  · simpa using (hterm 3).trans w5
  · simpa using (hterm 4).trans w6
  · simpa using (hterm 5).trans w7
  · simpa using (hterm 6).trans w8
  · simpa using (hterm 7).trans w9
  · simpa using (hterm 8).trans w10

private theorem sge1_bounds_at_yTilt {y : ℝ} (hy : 0 < y) (hy16 : y ≤ 16) :
    let mu := yTilt y - 2 * q
    let S := y ^ 2 / 2
    ninePartY y ≤ S * extendedGaussianPartition q mu ∧
      S * extendedGaussianPartition q mu ≤ sge1Bound9Y y ∧
      nineMeanY y ≤ extendedGaussianMean q mu + 2 ∧
      extendedGaussianMean q mu + 2 ≤ sge1MeanUb9Y y := by
  intro mu S
  have hSpos : 0 < S := by dsimp [S]; positivity
  have hmu_le : mu ≤ 9 * q / 2 := by
    dsimp [mu]
    linarith [yTilt_le_nine_q_half hy hy16, q_pos]
  obtain ⟨he, h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := shifted_weights_nine hy
  have hs0 : Summable (extendedGaussianNaturalTerm q mu) :=
    summable_extendedGaussianNaturalTerm q_pos
  have hs1 : Summable (fun d : ℕ ↦ (d : ℝ) * extendedGaussianNaturalTerm q mu d) :=
    summable_extendedGaussianFirstMoment q_pos
  have hpart_split :
      S * extendedGaussianPartition q mu =
        ninePartY y + S * ∑' n : ℕ, extendedGaussianNaturalTerm q mu (n + 8) := by
    unfold extendedGaussianPartition
    rw [← hs0.sum_add_tsum_nat_add 8, mul_add, mul_add, Finset.mul_sum]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    dsimp [S, mu] at he h0 h1 h2 h3 h4 h5 h6 h7 ⊢
    rw [he, h0, h1, h2, h3, h4, h5, h6, h7]
    unfold ninePartY sevenPartY
    ring
  have htail0_nonneg : 0 ≤ ∑' n : ℕ, extendedGaussianNaturalTerm q mu (n + 8) :=
    tsum_nonneg fun n ↦ (extendedGaussianNaturalTerm_pos q mu _).le
  have hgeom0 : ∀ n : ℕ, extendedGaussianNaturalTerm q mu (n + 8) ≤
      (1 / 8 : ℝ) ^ n * extendedGaussianNaturalTerm q mu 8 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [(by omega : n + 1 + 8 = n + 8 + 1)]
      calc extendedGaussianNaturalTerm q mu (n + 8 + 1)
          ≤ 1 / 8 * extendedGaussianNaturalTerm q mu (n + 8) :=
            natTerm_succ_le mu hmu_le (n + 8) (by omega)
        _ ≤ 1 / 8 * ((1 / 8 : ℝ) ^ n * extendedGaussianNaturalTerm q mu 8) :=
            mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (1 / 8 : ℝ) ^ (n + 1) * extendedGaussianNaturalTerm q mu 8 := by ring
  have htail0_ub : ∑' n : ℕ, extendedGaussianNaturalTerm q mu (n + 8) ≤
      8 / 7 * extendedGaussianNaturalTerm q mu 8 := by
    calc ∑' n : ℕ, extendedGaussianNaturalTerm q mu (n + 8)
        ≤ ∑' n : ℕ, (1 / 8 : ℝ) ^ n * extendedGaussianNaturalTerm q mu 8 :=
          Summable.tsum_le_tsum hgeom0 ((summable_nat_add_iff 8).mpr hs0)
            ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _)
      _ = 8 / 7 * extendedGaussianNaturalTerm q mu 8 := by
          rw [tsum_mul_right,
            tsum_geometric_of_lt_one (r := (1 / 8 : ℝ)) (by norm_num) (by norm_num)]
          norm_num
  have hP_lo : ninePartY y ≤ S * extendedGaussianPartition q mu := by
    rw [hpart_split]
    linarith [mul_nonneg hSpos.le htail0_nonneg]
  have hP_hi : S * extendedGaussianPartition q mu ≤ sge1Bound9Y y := by
    rw [hpart_split]
    have hmul := mul_le_mul_of_nonneg_left htail0_ub hSpos.le
    dsimp [S, mu] at h8 hmul ⊢
    unfold sge1Bound9Y
    linarith
  -- First moment split (`(N₁ + 2 Z) * S = nineFirstY y + S * ∑' n, (n + 10) * term (n + 8)`)
  have hfirst_split :
      S * (extendedGaussianFirstNumerator q mu + 2 * extendedGaussianPartition q mu) =
        nineFirstY y +
          S * (∑' n : ℕ, ((n + 8 : ℕ) : ℝ) * extendedGaussianNaturalTerm q mu (n + 8) +
            2 * ∑' n : ℕ, extendedGaussianNaturalTerm q mu (n + 8)) := by
    unfold extendedGaussianFirstNumerator extendedGaussianPartition
    rw [← hs1.sum_add_tsum_nat_add 8, ← hs0.sum_add_tsum_nat_add 8]
    have hfin1 :
        S * (-extendedGaussianExceptionalAtom q mu +
            ∑ d ∈ Finset.range 8, (d : ℝ) * extendedGaussianNaturalTerm q mu d +
            2 * (extendedGaussianExceptionalAtom q mu +
              ∑ d ∈ Finset.range 8, extendedGaussianNaturalTerm q mu d)) =
          nineFirstY y := by
      have hexpnd :
          S * (-extendedGaussianExceptionalAtom q mu +
              ∑ d ∈ Finset.range 8, (d : ℝ) * extendedGaussianNaturalTerm q mu d +
              2 * (extendedGaussianExceptionalAtom q mu +
                ∑ d ∈ Finset.range 8, extendedGaussianNaturalTerm q mu d)) =
            S * extendedGaussianExceptionalAtom q mu +
              (∑ d ∈ Finset.range 8, (d : ℝ) * (S * extendedGaussianNaturalTerm q mu d)) +
              2 * (∑ d ∈ Finset.range 8, (S * extendedGaussianNaturalTerm q mu d)) := by
        have h1 : S * ∑ d ∈ Finset.range 8, (d : ℝ) * extendedGaussianNaturalTerm q mu d =
            ∑ d ∈ Finset.range 8, (d : ℝ) * (S * extendedGaussianNaturalTerm q mu d) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun d _ ↦ by ring
        have h2 : S * ∑ d ∈ Finset.range 8, extendedGaussianNaturalTerm q mu d =
            ∑ d ∈ Finset.range 8, S * extendedGaussianNaturalTerm q mu d :=
          Finset.mul_sum _ _ _
        calc S * (-extendedGaussianExceptionalAtom q mu +
                ∑ d ∈ Finset.range 8, (d : ℝ) * extendedGaussianNaturalTerm q mu d +
                2 * (extendedGaussianExceptionalAtom q mu +
                  ∑ d ∈ Finset.range 8, extendedGaussianNaturalTerm q mu d))
            = S * extendedGaussianExceptionalAtom q mu +
                S * ∑ d ∈ Finset.range 8, (d : ℝ) * extendedGaussianNaturalTerm q mu d +
                2 * (S * ∑ d ∈ Finset.range 8, extendedGaussianNaturalTerm q mu d) := by ring
          _ = S * extendedGaussianExceptionalAtom q mu +
                (∑ d ∈ Finset.range 8, (d : ℝ) * (S * extendedGaussianNaturalTerm q mu d)) +
                2 * (∑ d ∈ Finset.range 8, (S * extendedGaussianNaturalTerm q mu d)) := by
              rw [h1, h2]
      rw [hexpnd]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      dsimp [S, mu] at he h0 h1 h2 h3 h4 h5 h6 h7 ⊢
      rw [he, h0, h1, h2, h3, h4, h5, h6, h7]
      push_cast
      unfold nineFirstY sevenFirstY
      ring
    linarith
  -- Step ratio for `(d + 2) * term d` for `d ≥ 8`:
  -- `yTilt y ≤ q/2 + log 16 = 9q/2`, so `mu = yTilt y - 2q ≤ 5q/2`!
  -- Thus `term (d + 1) / term d = exp(mu - q/2 * (2d + 1)) ≤ exp(5q/2 - 17q/2) = exp(-6q) = 1/64`!
  -- Hence `((d + 1 + 2) * term (d + 1)) ≤ (11/10) * (1/64) * ((d + 2) * term d) ≤ (1/8) * ((d + 2) * term d)`!
  have hmu_le5 : mu ≤ 5 * q / 2 := by
    dsimp [mu]
    linarith [yTilt_le_nine_q_half hy hy16]
  have hexp_neg_six_q : Real.exp (-(6 * q)) = 1 / 64 := by
    rw [Real.exp_neg, show (6 : ℝ) * q = ((6 : ℕ) : ℝ) * Real.log 2 by unfold q; norm_num,
      Real.exp_nat_mul, Real.exp_log two_pos]
    norm_num
  have hstep10 : ∀ d : ℕ, 8 ≤ d →
      ((d + 1 + 2 : ℕ) : ℝ) * extendedGaussianNaturalTerm q mu (d + 1) ≤
        1 / 8 * (((d + 2 : ℕ) : ℝ) * extendedGaussianNaturalTerm q mu d) := by
    intro d hd
    have hterm_eq : extendedGaussianNaturalTerm q mu (d + 1) =
        Real.exp (mu - q / 2 * (2 * (d : ℝ) + 1)) * extendedGaussianNaturalTerm q mu d := by
      unfold extendedGaussianNaturalTerm
      rw [← Real.exp_add]; push_cast; congr 1; ring
    have hdR : (8 : ℝ) ≤ d := by exact_mod_cast hd
    have hexp_le : mu - q / 2 * (2 * (d : ℝ) + 1) ≤ -(6 * q) := by
      nlinarith [mul_le_mul_of_nonneg_left hdR q_pos.le]
    have h64 : Real.exp (mu - q / 2 * (2 * (d : ℝ) + 1)) ≤ 1 / 64 := by
      rw [← hexp_neg_six_q]; exact Real.exp_le_exp.mpr hexp_le
    have hrat : ((d + 1 + 2 : ℕ) : ℝ) * (1 / 64) ≤ 1 / 8 * ((d + 2 : ℕ) : ℝ) := by
      push_cast; linarith
    rw [hterm_eq]
    calc ((d + 1 + 2 : ℕ) : ℝ) *
            (Real.exp (mu - q / 2 * (2 * (d : ℝ) + 1)) * extendedGaussianNaturalTerm q mu d)
        ≤ ((d + 1 + 2 : ℕ) : ℝ) * (1 / 64 * extendedGaussianNaturalTerm q mu d) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right h64 (extendedGaussianNaturalTerm_pos q mu d).le)
            (by positivity)
      _ = (((d + 1 + 2 : ℕ) : ℝ) * (1 / 64)) * extendedGaussianNaturalTerm q mu d := by ring
      _ ≤ (1 / 8 * ((d + 2 : ℕ) : ℝ)) * extendedGaussianNaturalTerm q mu d :=
          mul_le_mul_of_nonneg_right hrat (extendedGaussianNaturalTerm_pos q mu d).le
      _ = 1 / 8 * (((d + 2 : ℕ) : ℝ) * extendedGaussianNaturalTerm q mu d) := by ring
  have hs_comb : Summable (fun n : ℕ ↦
      ((n + 8 + 2 : ℕ) : ℝ) * extendedGaussianNaturalTerm q mu (n + 8)) := by
    have h1 := (summable_nat_add_iff 8).mpr hs1
    have h2 := ((summable_nat_add_iff 8).mpr hs0).mul_left 2
    refine (h1.add h2).congr fun n ↦ ?_
    push_cast; ring
  have htsum_comb_eq :
      ∑' n : ℕ, ((n + 8 : ℕ) : ℝ) * extendedGaussianNaturalTerm q mu (n + 8) +
        2 * ∑' n : ℕ, extendedGaussianNaturalTerm q mu (n + 8) =
      ∑' n : ℕ, ((n + 8 + 2 : ℕ) : ℝ) * extendedGaussianNaturalTerm q mu (n + 8) := by
    rw [← tsum_mul_left, ← ((summable_nat_add_iff 8).mpr hs1).tsum_add
      (((summable_nat_add_iff 8).mpr hs0).mul_left 2)]
    refine tsum_congr fun n ↦ ?_
    push_cast; ring
  have hgeom10 : ∀ n : ℕ,
      ((n + 8 + 2 : ℕ) : ℝ) * extendedGaussianNaturalTerm q mu (n + 8) ≤
        (1 / 8 : ℝ) ^ n * (10 * extendedGaussianNaturalTerm q mu 8) := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      have h1 : n + 1 + 8 = (n + 8) + 1 := by omega
      rw [h1]
      calc (((n + 8) + 1 + 2 : ℕ) : ℝ) * extendedGaussianNaturalTerm q mu ((n + 8) + 1)
          ≤ 1 / 8 * (((n + 8 + 2 : ℕ) : ℝ) * extendedGaussianNaturalTerm q mu (n + 8)) :=
            hstep10 (n + 8) (by omega)
        _ ≤ 1 / 8 * ((1 / 8 : ℝ) ^ n * (10 * extendedGaussianNaturalTerm q mu 8)) :=
            mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (1 / 8 : ℝ) ^ (n + 1) * (10 * extendedGaussianNaturalTerm q mu 8) := by ring
  have htail10_ub :
      ∑' n : ℕ, ((n + 8 + 2 : ℕ) : ℝ) * extendedGaussianNaturalTerm q mu (n + 8) ≤
        80 / 7 * extendedGaussianNaturalTerm q mu 8 := by
    calc ∑' n : ℕ, ((n + 8 + 2 : ℕ) : ℝ) * extendedGaussianNaturalTerm q mu (n + 8)
        ≤ ∑' n : ℕ, (1 / 8 : ℝ) ^ n * (10 * extendedGaussianNaturalTerm q mu 8) :=
          Summable.tsum_le_tsum hgeom10 hs_comb
            ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _)
      _ = 80 / 7 * extendedGaussianNaturalTerm q mu 8 := by
          rw [tsum_mul_right,
            tsum_geometric_of_lt_one (r := (1 / 8 : ℝ)) (by norm_num) (by norm_num)]
          ring
  have hM9_lt_10 : nineMeanY y < 10 := by
    have hP9pos : 0 < ninePartY y := by
      have := sevenPartY_pos hy; unfold ninePartY; positivity
    unfold nineMeanY
    rw [div_lt_iff₀ hP9pos]
    have := sevenPartY_pos hy
    unfold nineFirstY sevenFirstY ninePartY sevenPartY
    nlinarith [pow_pos hy 2, pow_pos hy 3, pow_pos hy 4, pow_pos hy 5,
      pow_pos hy 6, pow_pos hy 7, pow_pos hy 8, pow_pos hy 9]
  have htail_dom :
      nineMeanY y * ∑' n : ℕ, extendedGaussianNaturalTerm q mu (n + 8) ≤
        ∑' n : ℕ, ((n + 8 + 2 : ℕ) : ℝ) * extendedGaussianNaturalTerm q mu (n + 8) := by
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun n ↦ ?_)
      (((summable_nat_add_iff 8).mpr hs0).mul_left _) hs_comb
    have h10 : nineMeanY y ≤ ((n + 8 + 2 : ℕ) : ℝ) := by
      have : (10 : ℝ) ≤ ((n + 8 + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 10 ≤ n + 8 + 2)
      linarith
    exact mul_le_mul_of_nonneg_right h10 (extendedGaussianNaturalTerm_pos q mu _).le
  have hZpos := extendedGaussianPartition_pos q_pos (lambda := mu)
  have hP9pos : 0 < ninePartY y := by
    have := sevenPartY_pos hy; unfold ninePartY; positivity
  have hmean2_eq :
      extendedGaussianMean q mu + 2 =
        (S * (extendedGaussianFirstNumerator q mu + 2 * extendedGaussianPartition q mu)) /
          (S * extendedGaussianPartition q mu) := by
    unfold extendedGaussianMean
    field_simp [hSpos.ne', hZpos.ne']
  refine ⟨hP_lo, hP_hi, ?_, ?_⟩
  · rw [hmean2_eq, le_div_iff₀ (mul_pos hSpos hZpos), hpart_split, hfirst_split, htsum_comb_eq]
    have h9eq : nineMeanY y * ninePartY y = nineFirstY y :=
      div_mul_cancel₀ _ hP9pos.ne'
    have hmul_dom := mul_le_mul_of_nonneg_left htail_dom hSpos.le
    linarith
  · rw [hmean2_eq, div_le_iff₀ (mul_pos hSpos hZpos), hfirst_split, htsum_comb_eq]
    unfold sge1MeanUb9Y
    have hnum_ub :
        nineFirstY y + S * ∑' n : ℕ, ((n + 8 + 2 : ℕ) : ℝ) * extendedGaussianNaturalTerm q mu (n + 8) ≤
          nineFirstY y + 80 / 7 * (y ^ 10 / 35184372088832) := by
      have hmul := mul_le_mul_of_nonneg_left htail10_ub hSpos.le
      dsimp [S, mu] at h8 hmul ⊢
      linarith
    have hpos_ub : 0 ≤ nineFirstY y + 80 / 7 * (y ^ 10 / 35184372088832) := by
      have := sevenPartY_pos hy
      unfold nineFirstY sevenFirstY; positivity
    calc nineFirstY y + S * ∑' n : ℕ, ((n + 8 + 2 : ℕ) : ℝ) * extendedGaussianNaturalTerm q mu (n + 8)
        ≤ nineFirstY y + 80 / 7 * (y ^ 10 / 35184372088832) := hnum_ub
      _ = ((nineFirstY y + 80 / 7 * (y ^ 10 / 35184372088832)) / ninePartY y) * ninePartY y := by
          rw [div_mul_cancel₀ _ hP9pos.ne']
      _ ≤ ((nineFirstY y + 80 / 7 * (y ^ 10 / 35184372088832)) / ninePartY y) *
            (S * extendedGaussianPartition q mu) :=
          mul_le_mul_of_nonneg_left hP_lo (div_nonneg hpos_ub hP9pos.le)

/-- **`φ_∞(0.0290) > 0` (`Lemma 5.2(i)`).** -/
theorem phiInf_0290_pos : 0 < phiInf (290 / 10000) := by
  obtain ⟨h2lo, h2hi⟩ := two_div_log_two_bounds_d8
  set y : ℝ := 10187 / 1000
  have hy : 0 < y := by dsimp [y]; norm_num
  have hy16 : y ≤ 16 := by dsimp [y]; norm_num
  obtain ⟨_, hPub, hMlb, _⟩ := sge1_bounds_at_yTilt hy hy16
  have hMgt : phaseTarget (290 / 10000) < nineMeanY y := by
    have : 1 + (288539009 / 100000000 : ℝ) - 290 / 10000 < nineMeanY y := by
      dsimp [y]; unfold nineMeanY nineFirstY sevenFirstY ninePartY sevenPartY; norm_num
    unfold phaseTarget
    linarith
  have ht0 : -1 < phaseTarget (290 / 10000) - 2 := by unfold phaseTarget; linarith
  have htilt_lt : extendedGaussianTilt q (phaseTarget (290 / 10000) - 2) < yTilt y - 2 * q := by
    apply (strictMono_extendedGaussianMean q q_pos).lt_iff_lt.mp
    rw [extendedGaussianMean_extendedGaussianTilt q_pos ht0]
    linarith
  set plo : ℝ := y / sge1Bound9Y y
  have hplo_mem : plo ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp [plo, y]; unfold sge1Bound9Y ninePartY sevenPartY; constructor <;> norm_num
  have hp_gt : plo < p1Inf (290 / 10000) := by
    rw [p1Inf_eq_p1AtTilt]
    have h1 := strictAnti_p1AtTilt htilt_lt
    have h2 : plo ≤ p1AtTilt (yTilt y - 2 * q) := by
      unfold p1AtTilt
      obtain ⟨he, -, -, -, -, -, -, -, -, -⟩ := shifted_weights_nine hy
      have hZpos := extendedGaussianPartition_pos q_pos (lambda := yTilt y - 2 * q)
      have hUpos : 0 < sge1Bound9Y y := by
        dsimp [y]; unfold sge1Bound9Y ninePartY sevenPartY; norm_num
      dsimp [plo]
      rw [le_div_iff₀ hZpos, div_mul_eq_mul_div, div_le_iff₀ hUpos]
      calc y * extendedGaussianPartition q (yTilt y - 2 * q)
          = (y ^ 2 / 2 * extendedGaussianExceptionalAtom q (yTilt y - 2 * q)) *
              extendedGaussianPartition q (yTilt y - 2 * q) :=
              congrArg (· * extendedGaussianPartition q (yTilt y - 2 * q)) he.symm
        _ = extendedGaussianExceptionalAtom q (yTilt y - 2 * q) *
              (y ^ 2 / 2 * extendedGaussianPartition q (yTilt y - 2 * q)) := by ring
        _ ≤ extendedGaussianExceptionalAtom q (yTilt y - 2 * q) * sge1Bound9Y y :=
              mul_le_mul_of_nonneg_left hPub (extendedGaussianExceptionalAtom_pos q _).le
    exact lt_of_le_of_lt h2 h1
  have hp_mem : p1Inf (290 / 10000) ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [p1Inf_eq_p1AtTilt]; exact p1AtTilt_mem_Ioo _
  have hg_gt : phiInfAux plo < phiInfAux (p1Inf (290 / 10000)) :=
    strictMonoOn_phiInfAux hplo_mem hp_mem hp_gt
  have hlog_lb : -(0.6931471808 : ℝ) + 33647738031 / 50000000000 ≤ Real.log (1 - plo) := by
    exact log_ge_of_artanh (m := 1 - plo) (c := 1 / 2) (u := 32432893 / 100000000)
      (lc := -(0.6931471808 : ℝ)) (L := 33647738031 / 50000000000)
      (by norm_num) log_half_ge (by norm_num) (by norm_num)
      (by dsimp [plo, y]; unfold sge1Bound9Y ninePartY sevenPartY; norm_num) 7
      (by norm_num [Finset.sum_range_succ])
  have hfac_pos : 0 < (1 - plo) / plo := div_pos (by linarith [hplo_mem.2]) hplo_mem.1
  have hg_lb : (1 - plo) / plo * (-(0.6931471808 : ℝ) + 33647738031 / 50000000000) ≤
      phiInfAux plo := by
    unfold phiInfAux
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_left hlog_lb hfac_pos.le
  have hlin_id : Real.log 2 / 2 * (phaseTarget (290 / 10000) - 1) =
      1 - Real.log 2 / 2 * (290 / 10000) := by
    have hq_ne : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    unfold phaseTarget
    field_simp [hq_ne]
    ring
  have hqhi := Real.log_two_lt_d9
  have hnum_pos :
      0 < (1 - plo) / plo * (-(0.6931471808 : ℝ) + 33647738031 / 50000000000) +
        (1 - (0.6931471808 : ℝ) / 2 * (290 / 10000)) := by
    dsimp [plo, y]; unfold sge1Bound9Y ninePartY sevenPartY; norm_num
  unfold phiInf
  rw [hlin_id]
  linarith

/-- **`φ_∞(0.0291) < 0` (`Lemma 5.2(i)`).** -/
theorem phiInf_0291_neg : phiInf (291 / 10000) < 0 := by
  obtain ⟨h2lo, _⟩ := two_div_log_two_bounds_d8
  set y : ℝ := 10184 / 1000
  have hy : 0 < y := by dsimp [y]; norm_num
  have hy16 : y ≤ 16 := by dsimp [y]; norm_num
  obtain ⟨hPlb, _, _, hMub⟩ := sge1_bounds_at_yTilt hy hy16
  have hMlt : sge1MeanUb9Y y < phaseTarget (291 / 10000) := by
    have : sge1MeanUb9Y y < 1 + (288539008 / 100000000 : ℝ) - 291 / 10000 := by
      dsimp [y]; unfold sge1MeanUb9Y nineFirstY sevenFirstY ninePartY sevenPartY; norm_num
    unfold phaseTarget
    linarith
  have ht0 : -1 < phaseTarget (291 / 10000) - 2 := by unfold phaseTarget; linarith
  have htilt_gt : yTilt y - 2 * q < extendedGaussianTilt q (phaseTarget (291 / 10000) - 2) := by
    apply (strictMono_extendedGaussianMean q q_pos).lt_iff_lt.mp
    rw [extendedGaussianMean_extendedGaussianTilt q_pos ht0]
    have h1 : extendedGaussianMean q (yTilt y - 2 * q) + 2 < phaseTarget (291 / 10000) :=
      lt_of_le_of_lt hMub hMlt
    linarith
  set phi_p : ℝ := y / ninePartY y
  have hphi_mem : phi_p ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp [phi_p, y]; unfold ninePartY sevenPartY; constructor <;> norm_num
  have hp_lt : p1Inf (291 / 10000) < phi_p := by
    rw [p1Inf_eq_p1AtTilt]
    have h1 := strictAnti_p1AtTilt htilt_gt
    have h2 : p1AtTilt (yTilt y - 2 * q) ≤ phi_p := by
      unfold p1AtTilt
      obtain ⟨he, -, -, -, -, -, -, -, -, -⟩ := shifted_weights_nine hy
      have hZpos := extendedGaussianPartition_pos q_pos (lambda := yTilt y - 2 * q)
      have hP9pos : 0 < ninePartY y := by
        dsimp [y]; unfold ninePartY sevenPartY; norm_num
      dsimp [phi_p]
      rw [div_le_iff₀ hZpos, div_mul_eq_mul_div, le_div_iff₀ hP9pos]
      calc extendedGaussianExceptionalAtom q (yTilt y - 2 * q) * ninePartY y
          ≤ extendedGaussianExceptionalAtom q (yTilt y - 2 * q) *
              (y ^ 2 / 2 * extendedGaussianPartition q (yTilt y - 2 * q)) :=
              mul_le_mul_of_nonneg_left hPlb (extendedGaussianExceptionalAtom_pos q _).le
        _ = (y ^ 2 / 2 * extendedGaussianExceptionalAtom q (yTilt y - 2 * q)) *
              extendedGaussianPartition q (yTilt y - 2 * q) := by ring
        _ = y * extendedGaussianPartition q (yTilt y - 2 * q) := by rw [he]
    exact lt_of_lt_of_le h1 h2
  have hp_mem : p1Inf (291 / 10000) ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [p1Inf_eq_p1AtTilt]; exact p1AtTilt_mem_Ioo _
  have hg_lt : phiInfAux (p1Inf (291 / 10000)) < phiInfAux phi_p :=
    strictMonoOn_phiInfAux hp_mem hphi_mem hp_lt
  have hlog_inv_lb : (2020956781 / 100000000000 : ℝ) ≤ Real.log (1 / (1 - phi_p)) := by
    have h := log_ge_of_artanh (m := 1 / (1 - phi_p)) (c := 1) (u := 252611 / 25000000)
      (lc := 0) (L := 2020956781 / 100000000000) (by norm_num) log_one_ge
      (by norm_num) (by norm_num)
      (by dsimp [phi_p, y]; unfold ninePartY sevenPartY; norm_num) 6
      (by norm_num [Finset.sum_range_succ])
    linarith
  have hlog_ub : Real.log (1 - phi_p) ≤ -(2020956781 / 100000000000 : ℝ) := by
    rw [one_div, Real.log_inv] at hlog_inv_lb
    linarith
  have hfac_pos : 0 < (1 - phi_p) / phi_p := div_pos (by linarith [hphi_mem.2]) hphi_mem.1
  have hg_ub : phiInfAux phi_p ≤ (1 - phi_p) / phi_p * (-(2020956781 / 100000000000 : ℝ)) := by
    unfold phiInfAux
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_left hlog_ub hfac_pos.le
  have hlin_id : Real.log 2 / 2 * (phaseTarget (291 / 10000) - 1) =
      1 - Real.log 2 / 2 * (291 / 10000) := by
    have hq_ne : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    unfold phaseTarget
    field_simp [hq_ne]
    ring
  have hqlo := Real.log_two_gt_d9
  have hnum_neg :
      (1 - phi_p) / phi_p * (-(2020956781 / 100000000000 : ℝ)) +
        (1 - (0.6931471803 : ℝ) / 2 * (291 / 10000)) < 0 := by
    dsimp [phi_p, y]; unfold ninePartY sevenPartY; norm_num
  unfold phiInf
  rw [hlin_id]
  linarith

/-- **Existence, uniqueness, and `(0.0290, 0.0291)` bracket of the critical phase `x₀`
(`Lemma 5.2(i)` and `Sharp Asymptotic Theorem`).** -/
theorem existsUnique_criticalPhase_x0 :
    ∃! x0 : ℝ, x0 ∈ Set.Icc (0 : ℝ) (207 / 200) ∧ phiInf x0 = 0 := by
  have hsub : Set.Icc (290 / 10000 : ℝ) (291 / 10000) ⊆ Set.Icc 0 (207 / 200) := by
    intro x hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hcont_sub : ContinuousOn phiInf (Set.Icc (290 / 10000 : ℝ) (291 / 10000)) :=
    continuousOn_phiInf.mono hsub
  have h0_mem : (0 : ℝ) ∈ Set.Icc (phiInf (291 / 10000)) (phiInf (290 / 10000)) :=
    ⟨phiInf_0291_neg.le, phiInf_0290_pos.le⟩
  obtain ⟨x0, hx0_sub, hx0_zero⟩ :=
    intermediate_value_Icc' (by norm_num : (290 / 10000 : ℝ) ≤ 291 / 10000) hcont_sub h0_mem
  refine ⟨x0, ⟨hsub hx0_sub, hx0_zero⟩, ?_⟩
  rintro y ⟨hy_mem, hy_zero⟩
  rcases lt_trichotomy y x0 with hlt | rfl | hgt
  · have := strictAntiOn_phiInf hy_mem (hsub hx0_sub) hlt
    linarith
  · rfl
  · have := strictAntiOn_phiInf (hsub hx0_sub) hy_mem hgt
    linarith

/-- The unique critical phase `x₀` satisfying `φ_∞(x₀) = 0` on `[0, 207 / 200]`. -/
def criticalPhaseX0 : ℝ :=
  existsUnique_criticalPhase_x0.choose

theorem criticalPhaseX0_bounds_and_sign :
    criticalPhaseX0 ∈ Set.Ioo (290 / 10000 : ℝ) (291 / 10000) ∧
      phiInf criticalPhaseX0 = 0 ∧
      (∀ d ∈ Set.Ico (0 : ℝ) criticalPhaseX0, 0 < phiInf d) ∧
      (∀ d ∈ Set.Ioc criticalPhaseX0 (207 / 200), phiInf d < 0) := by
  obtain ⟨⟨hx0_mem, hx0_zero⟩, _⟩ := existsUnique_criticalPhase_x0.choose_spec
  change criticalPhaseX0 ∈ Set.Icc (0 : ℝ) (207 / 200) at hx0_mem
  change phiInf criticalPhaseX0 = 0 at hx0_zero
  have hx0_gt : (290 / 10000 : ℝ) < criticalPhaseX0 := by
    by_contra hle
    rcases eq_or_lt_of_le (not_lt.mp hle) with heq | hlt
    · rw [heq] at hx0_zero
      linarith [phiInf_0290_pos]
    · have := strictAntiOn_phiInf hx0_mem ⟨by norm_num, by norm_num⟩ hlt
      linarith [phiInf_0290_pos]
  have hx0_lt : criticalPhaseX0 < 291 / 10000 := by
    by_contra hge
    rcases eq_or_lt_of_le (not_lt.mp hge) with heq | hgt
    · rw [← heq] at hx0_zero
      linarith [phiInf_0291_neg]
    · have := strictAntiOn_phiInf ⟨by norm_num, by norm_num⟩ hx0_mem hgt
      linarith [phiInf_0291_neg]
  refine ⟨⟨hx0_gt, hx0_lt⟩, hx0_zero, ?_, ?_⟩
  · intro d hd
    have hd_mem : d ∈ Set.Icc (0 : ℝ) (207 / 200) := ⟨hd.1, le_trans hd.2.le hx0_mem.2⟩
    have := strictAntiOn_phiInf hd_mem hx0_mem hd.2
    linarith
  · intro d hd
    have hd_mem : d ∈ Set.Icc (0 : ℝ) (207 / 200) := ⟨le_trans hx0_mem.1 hd.1.le, hd.2⟩
    have := strictAntiOn_phiInf hx0_mem hd_mem hd.1
    linarith

/-! ## 5. Conditional assembly of `[0.080, 0.086]` and `(log 2)³ / 4` (`Section 9`) -/

/-- **Conditional assembly of the Phase Refinement and `[0.080, 0.086]` Main Theorem:**
given the four shifted seven-size threshold conditions `(A)`, `(B)`, `(C)` at
`shiftedPhase (phaseDelta n)`, both the phase-resolved two-sided bound and the
uniform `[0.080, 0.086]` two-sided bound hold with probability tending to `1`. -/
theorem shifted_twoSided_phase_and_0080_0086_gap_tendsto_one
    (kZetaMinus kCo kChiMinus kCh : ℕ → ℕ)
    (a b eps : ℕ → ℝ)
    (heps_zero : Tendsto eps atTop (nhds 0))
    (hLoc : ∀ᶠ n in atTop,
      (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - eps n) *
          ((n : ℝ) / (Real.log n) ^ 3) ≤
        (kChiMinus n : ℝ) - (kCo n : ℝ) - a n ∧
      (kCh n : ℝ) + b n - (kZetaMinus n : ℝ) ≤
        (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + eps n) *
          ((n : ℝ) / (Real.log n) ^ 3))
    (hChiLow : Tendsto (fun n ↦ randomGraphMeasure n
        {G | kChiMinus n < chromaticNumberNat G}) atTop (nhds 1))
    (hZetaUp : Tendsto (fun n ↦ randomGraphMeasure n
        {G | (cochromaticNumber G : ℝ) ≤ (kCo n : ℝ) + a n}) atTop (nhds 1))
    (hZetaLow : Tendsto (fun n ↦ randomGraphMeasure n
        {G | kZetaMinus n < cochromaticNumber G}) atTop (nhds 1))
    (hChiUp : Tendsto (fun n ↦ randomGraphMeasure n
        {G | (chromaticNumberNat G : ℝ) ≤ (kCh n : ℝ) + b n}) atTop (nhds 1)) :
    Tendsto (fun n ↦ randomGraphMeasure n
        (twoSidedGapEvent
          (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - eps n)
          (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + eps n) n)) atTop (nhds 1) ∧
    Tendsto (fun n ↦ randomGraphMeasure n
        (twoSidedGapEvent (80 / 1000) (86 / 1000) n)) atTop (nhds 1) := by
  have hFour := tendsto_measure_inter_four_one randomGraphMeasure
    (fun n ↦ {G | kChiMinus n < chromaticNumberNat G})
    (fun n ↦ {G | (cochromaticNumber G : ℝ) ≤ (kCo n : ℝ) + a n})
    (fun n ↦ {G | kZetaMinus n < cochromaticNumber G})
    (fun n ↦ {G | (chromaticNumberNat G : ℝ) ≤ (kCh n : ℝ) + b n})
    (fun _ ↦ (Set.toFinite _).measurableSet)
    (fun _ ↦ (Set.toFinite _).measurableSet)
    (fun _ ↦ (Set.toFinite _).measurableSet)
    (fun _ ↦ (Set.toFinite _).measurableSet)
    hChiLow hZetaUp hZetaLow hChiUp
  have hPhase :
      Tendsto (fun n ↦ randomGraphMeasure n
        (twoSidedGapEvent
          (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - eps n)
          (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + eps n) n)) atTop (nhds 1) := by
    apply tendsto_measure_one_of_eventually_subset randomGraphMeasure _ _ hFour
    filter_upwards [hLoc] with n hLn G ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    simp only [Set.mem_setOf_eq] at h1 h2 h3 h4
    have hChiLowR : (kChiMinus n : ℝ) < (chromaticNumberNat G : ℝ) := by exact_mod_cast h1
    have hZetaLowR : (kZetaMinus n : ℝ) < (cochromaticNumber G : ℝ) := by exact_mod_cast h3
    unfold twoSidedGapEvent
    rw [Set.mem_setOf_eq]
    constructor <;> linarith [hLn.1, hLn.2]
  refine ⟨hPhase, ?_⟩
  have hMargin : ∀ n,
      (805 / 10000 : ℝ) < lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) ∧
        upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) < (8599 / 100000 : ℝ) := by
    intro n
    have htd := shiftedPhase_mem_Icc_wide (phaseDelta_mem_Ico n)
    have hA : (268155713 / 400000000 : ℝ) < phaseGain7 (shiftedPhase (phaseDelta n)) :=
      lt_trans log_391_div_200_gt (log_391_div_200_lt_phaseGain7 _ htd)
    have hqlo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hqhi : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
    have hqsq_lo : (0.6931471803 : ℝ) ^ 2 < (Real.log 2) ^ 2 := by nlinarith
    have hqsq_hi : (Real.log 2) ^ 2 < (0.6931471808 : ℝ) ^ 2 := by nlinarith
    constructor
    · unfold lowerPhaseCoeff7; nlinarith
    · unfold upperPhaseCoeff7
      have hspan : 2 * Real.log 2 - phaseGain7 (shiftedPhase (phaseDelta n)) <
          2 * 0.6931471808 - 268155713 / 400000000 := by linarith
      have hnum :
          (0.6931471808 : ℝ) ^ 2 / 4 * (2 * 0.6931471808 - 268155713 / 400000000) <
            8599 / 100000 := by norm_num
      by_cases hnn : 0 ≤ 2 * Real.log 2 - phaseGain7 (shiftedPhase (phaseDelta n))
      · have hmul :
            (Real.log 2) ^ 2 / 4 * (2 * Real.log 2 - phaseGain7 (shiftedPhase (phaseDelta n))) ≤
              (0.6931471808 : ℝ) ^ 2 / 4 * (2 * 0.6931471808 - 268155713 / 400000000) :=
          mul_le_mul (by linarith) hspan.le hnn (by norm_num)
        linarith
      · have hneg : (Real.log 2) ^ 2 / 4 *
            (2 * Real.log 2 - phaseGain7 (shiftedPhase (phaseDelta n))) < 0 :=
          mul_neg_of_pos_of_neg (by positivity) (not_le.mp hnn)
        linarith
  have heps_small : ∀ᶠ n in atTop, eps n < 1 / 100000 :=
    (tendsto_order.1 heps_zero).2 (1 / 100000) (by norm_num)
  apply tendsto_measure_one_of_eventually_subset randomGraphMeasure _ _ hPhase
  filter_upwards [eventually_ge_atTop 2, heps_small] with n hn heps_hi G ⟨hG_lo, hG_hi⟩
  have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hscale_nonneg : 0 ≤ (n : ℝ) / (Real.log n) ^ 3 := by positivity
  obtain ⟨hMlo, hMhi⟩ := hMargin n
  have hlo_c : (80 / 1000 : ℝ) ≤ lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - eps n := by
    linarith
  have hhi_c : upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + eps n ≤ (86 / 1000 : ℝ) := by
    linarith
  exact ⟨le_trans (mul_le_mul_of_nonneg_right hlo_c hscale_nonneg) hG_lo,
    le_trans hG_hi (mul_le_mul_of_nonneg_right hhi_c hscale_nonneg)⟩

/-- **Conditional assembly of the `(log 2)³ / 4` Sharp Asymptotic Theorem (`Section 9`):**
along any index set `Nset : Set ℕ` (representing `𝓝_ε`) on which, for every
window size `M ≥ 7`, the `S_{0,M}` vs `S_{≥ 1}` threshold bounds hold with
high probability, our unconditional uniform convergence `𝓕_{S_{0,M}} → 𝓕_{S_{≥ 1}}`
forces `(log n)³ / n · (χ(G_n) - ζ(G_n)) ∈ [sharpGapConstant - η, sharpGapConstant + η]`
with probability tending to `1` along `atTop ⊓ 𝓟 Nset` for every `η > 0`. -/
theorem sharp_constant_quarter_along_subsequence_of_window_thresholds
    (Nset : Set ℕ)
    (kZetaMinus kChiMinus : ℕ → ℕ)
    (kCo kCh : ℕ → ℕ → ℕ)
    (a b eps : ℕ → ℕ → ℝ)
    (heps_zero : ∀ M ≥ 7, Tendsto (eps M) (atTop ⊓ 𝓟 Nset) (nhds 0))
    (hLoc : ∀ M ≥ 7, ∀ᶠ n in atTop ⊓ 𝓟 Nset,
      ((Real.log 2) ^ 2 / 4 *
          (Real.log 2 - (dualValue Sge1 (phaseTarget (phaseDelta n)) -
            dualValue (S0M M) (phaseTarget (phaseDelta n)))) - eps M n) *
          ((n : ℝ) / (Real.log n) ^ 3) ≤
        (kChiMinus n : ℝ) - (kCo M n : ℝ) - a M n ∧
      (kCh M n : ℝ) + b M n - (kZetaMinus n : ℝ) ≤
        ((Real.log 2) ^ 2 / 4 *
          (Real.log 2 + (dualValue Sge1 (phaseTarget (phaseDelta n)) -
            dualValue (S0M M) (phaseTarget (phaseDelta n)))) + eps M n) *
          ((n : ℝ) / (Real.log n) ^ 3))
    (hChiLow : Tendsto (fun n ↦ randomGraphMeasure n
        {G | kChiMinus n < chromaticNumberNat G}) (atTop ⊓ 𝓟 Nset) (nhds 1))
    (hZetaLow : Tendsto (fun n ↦ randomGraphMeasure n
        {G | kZetaMinus n < cochromaticNumber G}) (atTop ⊓ 𝓟 Nset) (nhds 1))
    (hZetaUp : ∀ M ≥ 7, Tendsto (fun n ↦ randomGraphMeasure n
        {G | (cochromaticNumber G : ℝ) ≤ (kCo M n : ℝ) + a M n})
        (atTop ⊓ 𝓟 Nset) (nhds 1))
    (hChiUp : ∀ M ≥ 7, Tendsto (fun n ↦ randomGraphMeasure n
        {G | (chromaticNumberNat G : ℝ) ≤ (kCh M n : ℝ) + b M n})
        (atTop ⊓ 𝓟 Nset) (nhds 1))
    {eta : ℝ} (heta : 0 < eta) :
    Tendsto (fun n ↦ randomGraphMeasure n
        (twoSidedGapEvent (sharpGapConstant - eta) (sharpGapConstant + eta) n))
      (atTop ⊓ 𝓟 Nset) (nhds 1) := by
  have hqfac_pos : 0 < (Real.log 2) ^ 2 / 4 := by
    have := Real.log_pos one_lt_two; positivity
  obtain ⟨M, hM7, hMconv⟩ := tendstoUniformlyOn_dualValue_S0M_Sge1
    ((eta / 2) / ((Real.log 2) ^ 2 / 4)) (div_pos (half_pos heta) hqfac_pos)
  have hGapM : ∀ n,
      (Real.log 2) ^ 2 / 4 *
        (dualValue Sge1 (phaseTarget (phaseDelta n)) -
          dualValue (S0M M) (phaseTarget (phaseDelta n))) < eta / 2 := by
    intro n
    obtain ⟨hA, hB⟩ := two_div_log_two_bounds
    obtain ⟨hd0, hd1⟩ := phaseDelta_mem_Ico n
    have hT_mem : phaseTarget (phaseDelta n) ∈ Set.Icc (11 / 4 : ℝ) 4 := by
      unfold phaseTarget; exact ⟨by linarith, by linarith⟩
    have hlt := (hMconv M le_rfl _ hT_mem).2
    have hmul := mul_lt_mul_of_pos_left hlt hqfac_pos
    rwa [mul_div_cancel₀ _ hqfac_pos.ne'] at hmul
  have heps_small : ∀ᶠ n in atTop ⊓ 𝓟 Nset, |eps M n| < eta / 2 := by
    simpa [Real.dist_eq] using
      (Metric.tendsto_nhds.mp (heps_zero M hM7)) (eta / 2) (half_pos heta)
  -- Combine the four high-probability events along `L := atTop ⊓ 𝓟 Nset` via `.real`
  set L : Filter ℕ := atTop ⊓ 𝓟 Nset
  have hComplZero : ∀ {E : ∀ n : ℕ, Set (LabeledGraph n)},
      Tendsto (fun n ↦ randomGraphMeasure n (E n)) L (nhds 1) →
      Tendsto (fun n ↦ (randomGraphMeasure n).real (E n)ᶜ) L (nhds 0) := by
    intro E hE
    have hR : Tendsto (fun n ↦ (randomGraphMeasure n).real (E n)) L (nhds 1) := by
      simpa only [Function.comp_def, Measure.real, ENNReal.toReal_one] using
        (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp hE
    have hsub : Tendsto (fun n ↦ (1 : ℝ) - (randomGraphMeasure n).real (E n)) L (nhds 0) := by
      simpa only [sub_self] using (tendsto_const_nhds (x := (1 : ℝ))).sub hR
    refine hsub.congr' (Eventually.of_forall fun n ↦ ?_)
    dsimp only
    rw [probReal_compl_eq_one_sub (Set.toFinite _).measurableSet]
  have hBad1 := hComplZero hChiLow
  have hBad2 := hComplZero (hZetaUp M hM7)
  have hBad3 := hComplZero hZetaLow
  have hBad4 := hComplZero (hChiUp M hM7)
  have hBadSum : Tendsto (fun n ↦
      (randomGraphMeasure n).real {G | kChiMinus n < chromaticNumberNat G}ᶜ +
      (randomGraphMeasure n).real {G | (cochromaticNumber G : ℝ) ≤ (kCo M n : ℝ) + a M n}ᶜ +
      (randomGraphMeasure n).real {G | kZetaMinus n < cochromaticNumber G}ᶜ +
      (randomGraphMeasure n).real {G | (chromaticNumberNat G : ℝ) ≤ (kCh M n : ℝ) + b M n}ᶜ)
      L (nhds 0) := by
    simpa using (((hBad1.add hBad2).add hBad3).add hBad4)
  have hge2 : ∀ᶠ n in L, 2 ≤ n :=
    (eventually_ge_atTop 2).filter_mono inf_le_left
  have hTargetCompl : Tendsto (fun n ↦
      (randomGraphMeasure n).real
        (twoSidedGapEvent (sharpGapConstant - eta) (sharpGapConstant + eta) n)ᶜ)
      L (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds (x := (0 : ℝ))) hBadSum
      (Eventually.of_forall fun _ ↦ measureReal_nonneg) ?_
    filter_upwards [hge2, hLoc M hM7, heps_small] with n hn hLn hepsG
    have hsub_compl :
        (twoSidedGapEvent (sharpGapConstant - eta) (sharpGapConstant + eta) n)ᶜ ⊆
          ({G | kChiMinus n < chromaticNumberNat G}ᶜ ∪
            {G | (cochromaticNumber G : ℝ) ≤ (kCo M n : ℝ) + a M n}ᶜ) ∪
          ({G | kZetaMinus n < cochromaticNumber G}ᶜ ∪
            {G | (chromaticNumberNat G : ℝ) ≤ (kCh M n : ℝ) + b M n}ᶜ) := by
      intro G hGnot
      by_contra hAll
      simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_setOf_eq, not_or, not_not] at hAll
      obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hAll
      apply hGnot
      have hChiLowR : (kChiMinus n : ℝ) < (chromaticNumberNat G : ℝ) := by exact_mod_cast h1
      have hZetaLowR : (kZetaMinus n : ℝ) < (cochromaticNumber G : ℝ) := by exact_mod_cast h3
      have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
      have hscale_nonneg : 0 ≤ (n : ℝ) / (Real.log n) ^ 3 := by positivity
      have hgm := hGapM n
      obtain ⟨he1, he2⟩ := abs_lt.mp hepsG
      have hlo_c : sharpGapConstant - eta ≤
          (Real.log 2) ^ 2 / 4 *
            (Real.log 2 - (dualValue Sge1 (phaseTarget (phaseDelta n)) -
              dualValue (S0M M) (phaseTarget (phaseDelta n)))) - eps M n := by
        have hring : (Real.log 2) ^ 2 / 4 *
            (Real.log 2 - (dualValue Sge1 (phaseTarget (phaseDelta n)) -
              dualValue (S0M M) (phaseTarget (phaseDelta n)))) =
            sharpGapConstant - (Real.log 2) ^ 2 / 4 *
              (dualValue Sge1 (phaseTarget (phaseDelta n)) -
                dualValue (S0M M) (phaseTarget (phaseDelta n))) := by
          unfold sharpGapConstant; ring
        linarith
      have hhi_c :
          (Real.log 2) ^ 2 / 4 *
            (Real.log 2 + (dualValue Sge1 (phaseTarget (phaseDelta n)) -
              dualValue (S0M M) (phaseTarget (phaseDelta n)))) + eps M n ≤
            sharpGapConstant + eta := by
        have hring : (Real.log 2) ^ 2 / 4 *
            (Real.log 2 + (dualValue Sge1 (phaseTarget (phaseDelta n)) -
              dualValue (S0M M) (phaseTarget (phaseDelta n)))) =
            sharpGapConstant + (Real.log 2) ^ 2 / 4 *
              (dualValue Sge1 (phaseTarget (phaseDelta n)) -
                dualValue (S0M M) (phaseTarget (phaseDelta n))) := by
          unfold sharpGapConstant; ring
        linarith
      unfold twoSidedGapEvent
      rw [Set.mem_setOf_eq]
      exact ⟨le_trans (mul_le_mul_of_nonneg_right hlo_c hscale_nonneg) (by linarith [hLn.1]),
        le_trans (by linarith [hLn.2]) (mul_le_mul_of_nonneg_right hhi_c hscale_nonneg)⟩
    calc (randomGraphMeasure n).real
            (twoSidedGapEvent (sharpGapConstant - eta) (sharpGapConstant + eta) n)ᶜ
        ≤ (randomGraphMeasure n).real _ := measureReal_mono hsub_compl
      _ ≤ (randomGraphMeasure n).real (_ ∪ _) + (randomGraphMeasure n).real (_ ∪ _) :=
          measureReal_union_le _ _
      _ ≤ ((randomGraphMeasure n).real _ + (randomGraphMeasure n).real _) +
            ((randomGraphMeasure n).real _ + (randomGraphMeasure n).real _) :=
          add_le_add (measureReal_union_le _ _) (measureReal_union_le _ _)
      _ = _ := by rw [← add_assoc]
  have hTargetReal : Tendsto (fun n ↦
      (randomGraphMeasure n).real
        (twoSidedGapEvent (sharpGapConstant - eta) (sharpGapConstant + eta) n))
      L (nhds 1) := by
    have hsub : Tendsto (fun n ↦
        (1 : ℝ) - (randomGraphMeasure n).real
          (twoSidedGapEvent (sharpGapConstant - eta) (sharpGapConstant + eta) n)ᶜ)
        L (nhds 1) := by
      simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hTargetCompl
    refine hsub.congr' (Eventually.of_forall fun n ↦ ?_)
    dsimp only
    rw [probReal_compl_eq_one_sub (Set.toFinite _).measurableSet]
    ring
  have hOfReal : Tendsto (fun n ↦
      ENNReal.ofReal ((randomGraphMeasure n).real
        (twoSidedGapEvent (sharpGapConstant - eta) (sharpGapConstant + eta) n)))
      L (nhds 1) := by
    simpa only [Function.comp_def, ENNReal.ofReal_one] using ENNReal.tendsto_ofReal hTargetReal
  refine hOfReal.congr' (Eventually.of_forall fun n ↦ ?_)
  dsimp only [Measure.real]
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

end

end Erdos625HP
