import Erdos625HP.ConcreteTwoSidedInstantiation
import Erdos625HP.PhaseCoverAndSecondMomentAssembly

/-!
# v11 Orlicz `ψ₂`-norm bounds, coupling tail-union rates, general-`M` finite duals & corridor roots, and Section 7 regularity

This module formalizes the v11 upgrades across the Main Theorem, Phase Refinement, Section 3,
Section 5.2, Section 7 (Lemma 7.1), Corollary 8.1, and Section 9 using only the standard Lean
kernel foundations (`propext`, `Classical.choice`, `Quot.sound`), with `0` public `def`s and
`18` public `theorem`s (`15` unconditional + `3` conditional):

1. **Main Theorem `(i)` & Corollary 8.1 — Exact Gaussian `√(8/3)` Orlicz `ψ₂`-norm bounds &
   tail-scale monotonicity (`3` unconditional theorems):**
   - `orliczPsi2_chromaticSubCochromatic_le`
   - `orliczPsi2_normalizedGap_le`
   - `strictMonoOn_div_log_pow_six`

2. **Section 3 & Section 5.2 — General-`M` finite-window & capped dual errors, corridor roots
   (`∃!`), slope `(3.7)`, and general root separation `(5.19)` (`7` unconditional theorems):**
   - `finiteDeficitResidualScore_bounds`
   - `abs_windowFiniteEntropy_sub_dualValue_le`
   - `abs_cappedWindowFiniteEntropy_sub_cappedDualValue_le`
   - `exists_pos_eventually_existsUnique_windowPhaseObjective_zero_logLogCorridor`
   - `exists_pos_eventually_existsUnique_cappedWindowPhaseObjective_zero_logLogCorridor`
   - `eventually_unrestrictedPhaseObjective_deriv_logLogRate`
   - `eventually_window_and_capped_corridorRoot_separation_logLogRate`

3. **Section 7 `Lemma 7.1` — `G(n, 1/2)` cross-edge conditioning, `E_π / C_π / D_π` regularity,
   and `Π_rel` second-moment reduction (`5` unconditional theorems):**
   - `randomGraphMeasure_partitionColoring_and_marked_inter_crossEvent_eq`
   - `condProb_heavyCrossPairEvent_le_and_eventually_inv_n`
   - `eventually_condProb_badTwoClassSplit_tendsto_zero`
   - `eventually_condProb_manyNearParts_tendsto_zero`
   - `sq_regularPartitionSum_le_relevantPairs_and_integral_le`

4. **Section 9 — Coupling-uniform `∃ m ≥ n` sub-Gaussian tail-union rates & complete v11 syntheses
   (`3` conditional theorems):**
   - `eventually_coupling_tailUnion_of_subgaussian_marginals`
   - `phaseRefinement_v11_complete`
   - `mainTheorem_v11_complete`
-/

namespace Erdos625HP

open Erdos625 Erdos625.FiveSizeEntropyGap FiveSizePhaseGainSharp FiveSizePhaseGainCertificate
open Filter Asymptotics MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal

noncomputable section

set_option autoImplicit false

/-!
## 1. Gaussian `√(8/3)` Orlicz `ψ₂`-norm bounds and `(x / (log x)⁶)` monotonicity
-/

private theorem three_eighths_psi2_threshold_eq_two :
    ((1 : ℝ) - 2 * (3 / 8 : ℝ)) ^ (-(1 / 2 : ℝ)) = 2 := by
  have h1 : (1 : ℝ) - 2 * (3 / 8 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) := by norm_num
  rw [h1, ← Real.rpow_mul two_pos.le]
  norm_num

/-- **Main Theorem `(i)` & Corollary 8.1 Orlicz `ψ₂`-norm bound for `Δ(G_n) - E[Δ(G_n)]`:**
for every `n ≥ 2`, the Orlicz `ψ₂`-admissible set
`{s > 0 : E[exp((Δ(G_n) - E[Δ(G_n)])² / s²)] ≤ 2}` is nonempty, bounded below, and has infimum
`‖Δ(G_n) - E[Δ(G_n)]‖_{ψ₂} ≤ √(8/3 · (n - 1))`. -/
theorem orliczPsi2_chromaticSubCochromatic_le {n : ℕ} (hn : 2 ≤ n) :
    let D : LabeledGraph n → ℝ := fun G ↦
      (chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)
    let μ : ℝ := ∫ H : LabeledGraph n, D H ∂randomGraphMeasure n
    let S : Set ℝ := {s : ℝ | 0 < s ∧
      (∫ G : LabeledGraph n, Real.exp ((D G - μ) ^ 2 / s ^ 2) ∂randomGraphMeasure n) ≤ 2}
    S.Nonempty ∧ BddBelow S ∧ sInf S ≤ Real.sqrt (8 / 3 * ((n - 1 : ℕ) : ℝ)) := by
  intro D μ S
  have hn1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n - 1 by omega)
  set s₀ : ℝ := Real.sqrt (8 / 3 * ((n - 1 : ℕ) : ℝ))
  have hs₀_pos : 0 < s₀ := Real.sqrt_pos.mpr (by positivity)
  have hs₀_sq : s₀ ^ 2 = 8 / 3 * ((n - 1 : ℕ) : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hs₀_mem : s₀ ∈ S := by
    refine ⟨hs₀_pos, ?_⟩
    have hsq_exp := sqExpMoment_chromaticSubCochromatic_le hn
      (show (3 / 8 : ℝ) ∈ Set.Ico (0 : ℝ) (1 / 2) by constructor <;> norm_num)
    rw [three_eighths_psi2_threshold_eq_two] at hsq_exp
    have hcongr :
        (fun G : LabeledGraph n ↦ Real.exp ((D G - μ) ^ 2 / s₀ ^ 2)) =
          fun G : LabeledGraph n ↦
            Real.exp ((3 / 8 : ℝ) * (D G - μ) ^ 2 / ((n - 1 : ℕ) : ℝ)) := by
      funext G
      congr 1
      rw [hs₀_sq]
      field_simp [hn1_pos.ne']
    simpa only [D, μ, hcongr] using hsq_exp
  have hbdd : BddBelow S := ⟨0, fun s hs ↦ hs.1.le⟩
  exact ⟨⟨s₀, hs₀_mem⟩, hbdd, csInf_le hbdd hs₀_mem⟩

/-- **Main Theorem `(i)` & Corollary 8.1 Orlicz `ψ₂`-norm bound for `Y_n - E[Y_n]`:**
for every `n ≥ 2`, the Orlicz `ψ₂`-admissible set
`{s > 0 : E[exp((Y_n - E[Y_n])² / s²)] ≤ 2}` is nonempty, bounded below, and has infimum
`‖Y_n - E[Y_n]‖_{ψ₂} ≤ √(8/3) · (log₂ n)³ / √n`. -/
theorem orliczPsi2_normalizedGap_le {n : ℕ} (hn : 2 ≤ n) :
    let Y : LabeledGraph n → ℝ := fun G ↦
      (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
        ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
    let μ : ℝ := ∫ H : LabeledGraph n, Y H ∂randomGraphMeasure n
    let S : Set ℝ := {s : ℝ | 0 < s ∧
      (∫ G : LabeledGraph n, Real.exp ((Y G - μ) ^ 2 / s ^ 2) ∂randomGraphMeasure n) ≤ 2}
    S.Nonempty ∧ BddBelow S ∧
      sInf S ≤ Real.sqrt (8 / 3) * (Real.logb 2 (n : ℝ)) ^ 3 / Real.sqrt (n : ℝ) := by
  intro Y μ S
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hn_pos : (0 : ℝ) < (n : ℝ) := lt_trans zero_lt_one hn1
  have hlb_pos : 0 < Real.logb 2 (n : ℝ) := Real.logb_pos one_lt_two hn1
  set s₀ : ℝ := Real.sqrt (8 / 3) * (Real.logb 2 (n : ℝ)) ^ 3 / Real.sqrt (n : ℝ)
  have hs₀_pos : 0 < s₀ := by
    dsimp [s₀]
    exact div_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num)) (pow_pos hlb_pos 3))
      (Real.sqrt_pos.mpr hn_pos)
  have hs₀_sq : s₀ ^ 2 = (8 / 3 : ℝ) * (Real.logb 2 (n : ℝ)) ^ 6 / (n : ℝ) := by
    dsimp [s₀]
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8 / 3),
      Real.sq_sqrt hn_pos.le]
    ring
  have hs₀_mem : s₀ ∈ S := by
    refine ⟨hs₀_pos, ?_⟩
    have hsq_exp := sqExpMoment_normalizedGap_le hn
      (show (3 / 8 : ℝ) ∈ Set.Ico (0 : ℝ) (1 / 2) by constructor <;> norm_num)
    dsimp only at hsq_exp
    rw [three_eighths_psi2_threshold_eq_two] at hsq_exp
    have hcongr :
        (fun G : LabeledGraph n ↦ Real.exp ((Y G - μ) ^ 2 / s₀ ^ 2)) =
          fun G : LabeledGraph n ↦
            Real.exp ((3 / 8 : ℝ) * (n : ℝ) * (Y G - μ) ^ 2 /
              (Real.logb 2 (n : ℝ)) ^ 6) := by
      funext G
      congr 1
      rw [hs₀_sq]
      field_simp [hn_pos.ne', hlb_pos.ne']
    simpa only [Y, μ, hcongr] using hsq_exp
  have hbdd : BddBelow S := ⟨0, fun s hs ↦ hs.1.le⟩
  exact ⟨⟨s₀, hs₀_mem⟩, hbdd, csInf_le hbdd hs₀_mem⟩

/-- **Section 9 sub-Gaussian tail-scale monotonicity (`main.tex` lines 1220–1221, 1284–1285):**
both `x ↦ x / (log x)⁶` and `x ↦ x / (log₂ x)⁶` are strictly increasing on `[e⁶, ∞)`. -/
theorem strictMonoOn_div_log_pow_six :
    StrictMonoOn (fun x : ℝ ↦ x / (Real.log x) ^ 6) (Set.Ici (Real.exp 6)) ∧
      StrictMonoOn (fun x : ℝ ↦ x / (Real.logb 2 x) ^ 6) (Set.Ici (Real.exp 6)) := by
  have hexp6_gt1 : 1 < Real.exp 6 := Real.one_lt_exp_iff.mpr (by norm_num)
  have hcont : ContinuousOn (fun x : ℝ ↦ x / (Real.log x) ^ 6) (Set.Ici (Real.exp 6)) := by
    refine continuousOn_id.div ?_ ?_
    · refine ContinuousOn.pow ?_ 6
      exact Real.continuousOn_log.mono fun x hx ↦
        (lt_trans zero_lt_one (lt_of_lt_of_le hexp6_gt1 hx)).ne'
    · intro x hx
      have hlog_ge6 : (6 : ℝ) ≤ Real.log x := by
        have := Real.log_le_log (Real.exp_pos 6) hx
        rwa [Real.log_exp] at this
      exact pow_ne_zero 6 (by linarith)
  have hsm_nat : StrictMonoOn (fun x : ℝ ↦ x / (Real.log x) ^ 6) (Set.Ici (Real.exp 6)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici (Real.exp 6)) hcont
    intro x hx
    rw [interior_Ici] at hx
    have hx_pos : 0 < x := lt_trans (Real.exp_pos 6) hx
    have hlog_gt6 : 6 < Real.log x := by
      have := Real.log_lt_log (Real.exp_pos 6) hx
      rwa [Real.log_exp] at this
    have hlog_pos : 0 < Real.log x := by linarith
    have hd_den := (Real.hasDerivAt_log hx_pos.ne').pow 6
    have hd_quo : HasDerivAt (fun y : ℝ ↦ y / (Real.log y) ^ 6)
        ((1 * (Real.log x) ^ 6 - x * ((6 : ℕ) * (Real.log x) ^ (6 - 1) * x⁻¹)) /
          ((Real.log x) ^ 6) ^ 2) x :=
      (hasDerivAt_id x).div hd_den (pow_pos hlog_pos 6).ne'
    rw [hd_quo.deriv]
    have hnum : 1 * (Real.log x) ^ 6 - x * ((6 : ℕ) * (Real.log x) ^ (6 - 1) * x⁻¹) =
        (Real.log x - 6) * (Real.log x) ^ 5 := by
      push_cast
      field_simp [hx_pos.ne']
    rw [hnum]
    exact div_pos (mul_pos (by linarith) (pow_pos hlog_pos 5)) (by positivity)
  refine ⟨hsm_nat, ?_⟩
  intro x hx y hy hxy
  have hq6_pos : 0 < (Real.log 2) ^ 6 := pow_pos (Real.log_pos one_lt_two) 6
  have hrew : ∀ z : ℝ, z / (Real.logb 2 z) ^ 6 = (Real.log 2) ^ 6 * (z / (Real.log z) ^ 6) := by
    intro z
    rw [Real.logb, div_pow, div_div_eq_mul_div]
    ring
  dsimp only
  rw [hrew x, hrew y]
  exact mul_lt_mul_of_pos_left (hsm_nat hx hy hxy) hq6_pos

/-!
## 2. General-`M` finite-window & capped dual errors, corridor roots (`∃!`), `(3.7)`, and `(5.19)`
-/

private theorem two_mul_sum_range_cast_le_sq (i : ℕ) :
    2 * (∑ r ∈ Finset.range i, (r : ℝ)) ≤ (i : ℝ) ^ 2 := by
  induction i with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    linarith [show ((k : ℝ) + 1) ^ 2 = (k : ℝ) ^ 2 + 2 * (k : ℝ) + 1 by ring]

/-- **Section 3, eq. `(3.1)` & Appendix A.2 residual score bounds (`main.tex` lines 474, 1389–1391):**
for all integers `0 ≤ i < α`:
1. `log (α)_i - i log α = ∑_{r=0}^{i-1} log(1 - r / α)`,
2. `∑_{r=0}^{i-1} log(1 - r / α) ≤ 0` (so `h_n(i) ≤ -(log 2 / 2) i²`),
3. if `2 i ≤ α`, then `-i² / α ≤ ∑_{r=0}^{i-1} log(1 - r / α)` (so `0 ≤ -h_n(i) - (log 2 / 2) i² ≤ i² / α`). -/
theorem finiteDeficitResidualScore_bounds {alpha i : ℕ} (hi : i < alpha) :
    Real.log (alpha.descFactorial i : ℝ) - (i : ℝ) * Real.log (alpha : ℝ) =
        (∑ r ∈ Finset.range i, Real.log (1 - (r : ℝ) / (alpha : ℝ))) ∧
      (∑ r ∈ Finset.range i, Real.log (1 - (r : ℝ) / (alpha : ℝ))) ≤ 0 ∧
      (2 * i ≤ alpha →
        -(i : ℝ) ^ 2 / (alpha : ℝ) ≤
          ∑ r ∈ Finset.range i, Real.log (1 - (r : ℝ) / (alpha : ℝ))) := by
  have ha_pos : (0 : ℝ) < (alpha : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hi)
  have hprod_eq : (alpha.descFactorial i : ℝ) =
      ∏ r ∈ Finset.range i, ((alpha : ℝ) * (1 - (r : ℝ) / (alpha : ℝ))) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    refine Finset.prod_congr rfl fun r hr ↦ ?_
    have hlt : r < alpha := lt_trans (Finset.mem_range.mp hr) hi
    rw [Nat.cast_sub hlt.le]
    field_simp [ha_pos.ne']
  have hterm_pos : ∀ r ∈ Finset.range i,
      0 < (alpha : ℝ) * (1 - (r : ℝ) / (alpha : ℝ)) := by
    intro r hr
    have hlt : (r : ℝ) < (alpha : ℝ) := by
      exact_mod_cast lt_trans (Finset.mem_range.mp hr) hi
    have h1 : 0 < 1 - (r : ℝ) / (alpha : ℝ) := by
      rw [sub_pos, div_lt_one ha_pos]; exact hlt
    exact mul_pos ha_pos h1
  have hid :
      Real.log (alpha.descFactorial i : ℝ) - (i : ℝ) * Real.log (alpha : ℝ) =
        ∑ r ∈ Finset.range i, Real.log (1 - (r : ℝ) / (alpha : ℝ)) := by
    rw [hprod_eq, Real.log_prod fun r hr ↦ (hterm_pos r hr).ne']
    have hsplit : ∀ r ∈ Finset.range i,
        Real.log ((alpha : ℝ) * (1 - (r : ℝ) / (alpha : ℝ))) =
          Real.log (alpha : ℝ) + Real.log (1 - (r : ℝ) / (alpha : ℝ)) := by
      intro r hr
      have hlt : (r : ℝ) < (alpha : ℝ) := by
        exact_mod_cast lt_trans (Finset.mem_range.mp hr) hi
      have h1 : 0 < 1 - (r : ℝ) / (alpha : ℝ) := by
        rw [sub_pos, div_lt_one ha_pos]; exact hlt
      exact Real.log_mul ha_pos.ne' h1.ne'
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    ring
  have hnonpos : (∑ r ∈ Finset.range i, Real.log (1 - (r : ℝ) / (alpha : ℝ))) ≤ 0 := by
    refine Finset.sum_nonpos fun r hr ↦ ?_
    have hlt : (r : ℝ) < (alpha : ℝ) := by
      exact_mod_cast lt_trans (Finset.mem_range.mp hr) hi
    apply Real.log_nonpos
    · linarith [(div_lt_one ha_pos).mpr hlt]
    · exact sub_le_self 1 (by positivity)
  refine ⟨hid, hnonpos, fun h2i ↦ ?_⟩
  have hterm_lo : ∀ r ∈ Finset.range i,
      -2 * (r : ℝ) / (alpha : ℝ) ≤ Real.log (1 - (r : ℝ) / (alpha : ℝ)) := by
    intro r hr
    set x : ℝ := (r : ℝ) / (alpha : ℝ)
    have hx_nn : 0 ≤ x := by dsimp [x]; positivity
    have hx_lt_half : x < 1 / 2 := by
      dsimp [x]
      rw [div_lt_iff₀ ha_pos]
      have hr_lt : r < i := Finset.mem_range.mp hr
      have : 2 * (r : ℝ) < (alpha : ℝ) := by exact_mod_cast (by omega : 2 * r < alpha)
      linarith
    have h1mx_pos0 : 0 < 1 - x := by linarith
    have hquot_le : x / (1 - x) ≤ 2 * x := by
      rw [div_le_iff₀ h1mx_pos0]
      nlinarith
    have hexp_inv : 1 / (1 - x) ≤ Real.exp (2 * x) := by
      have hid1 : 1 / (1 - x) = x / (1 - x) + 1 := by
        field_simp [h1mx_pos0.ne']; ring
      rw [hid1]
      exact (Real.add_one_le_exp (x / (1 - x))).trans (Real.exp_le_exp.mpr hquot_le)
    have hexp_neg : Real.exp (-2 * x) ≤ 1 - x := by
      have hm := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp_inv h1mx_pos0.le) (Real.exp_pos (-2 * x)).le
      have hl : (1 - x) * (1 / (1 - x)) * Real.exp (-2 * x) = Real.exp (-2 * x) := by
        field_simp [h1mx_pos0.ne']
      have hr_eq : (1 - x) * Real.exp (2 * x) * Real.exp (-2 * x) = 1 - x := by
        rw [mul_assoc, ← Real.exp_add]
        simp
      rwa [hl, hr_eq] at hm
    have hlog := Real.log_le_log (Real.exp_pos (-2 * x)) hexp_neg
    rw [Real.log_exp] at hlog
    have hlog' : -2 * x ≤ Real.log (1 - x) := hlog
    dsimp [x] at hlog'
    linarith [show -2 * ((r : ℝ) / (alpha : ℝ)) = -2 * (r : ℝ) / (alpha : ℝ) by ring]
  calc -(i : ℝ) ^ 2 / (alpha : ℝ)
      ≤ -(2 * ∑ r ∈ Finset.range i, (r : ℝ)) / (alpha : ℝ) := by
        exact div_le_div_of_nonneg_right (neg_le_neg (two_mul_sum_range_cast_le_sq i)) ha_pos.le
    _ = ∑ r ∈ Finset.range i, (-2 * (r : ℝ) / (alpha : ℝ)) := by
        rw [show -(2 * ∑ r ∈ Finset.range i, (r : ℝ)) / (alpha : ℝ) =
            (-2 / (alpha : ℝ)) * ∑ r ∈ Finset.range i, (r : ℝ) by ring, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ ↦ by ring
    _ ≤ ∑ r ∈ Finset.range i, Real.log (1 - (r : ℝ) / (alpha : ℝ)) :=
        Finset.sum_le_sum hterm_lo

private def windowSupportSet (m M : ℕ) : Set ℤ :=
  {j : ℤ | ((m + 1 : ℕ) : ℤ) ≤ j ∧ j ≤ ((m + M : ℕ) : ℤ)}

private def windowFiniteScore (alpha i : ℕ) : ℝ :=
  Real.log (alpha.descFactorial i : ℝ) - (i : ℝ) * Real.log (alpha : ℝ) -
    Real.log 2 / 2 * (i : ℝ) ^ 2

private def windowFinitePartition (alpha m M : ℕ) (l : ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc (m + 1) (m + M), Real.exp (l * (i : ℝ) + windowFiniteScore alpha i)

private def windowFiniteEntropy (alpha m M : ℕ) (T : ℝ) : ℝ :=
  ⨅ l : ℝ, (Real.log (windowFinitePartition alpha m M l) - l * T)

private def cappedWindowFiniteEntropy (alpha M : ℕ) (theta T : ℝ) : ℝ :=
  binEntropy theta - Real.log 2 / 2 * theta +
    (1 - theta) * windowFiniteEntropy alpha 1 (M - 1) ((T - theta) / (1 - theta))

private def windowPhaseObjective (m M n : ℕ) (tau s : ℝ) : ℝ :=
  (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + s - s * Real.log s +
    s * (profileDeficitAffineA (phaseNat n) +
      profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s +
      windowFiniteEntropy (phaseNat n) m M (fourSizeTarget n (phaseNat n) s) + tau)

private def cappedWindowPhaseObjective (M n : ℕ) (theta tau s : ℝ) : ℝ :=
  (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + s - s * Real.log s +
    s * (profileDeficitAffineA (phaseNat n) +
      profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s +
      cappedWindowFiniteEntropy (phaseNat n) M theta (fourSizeTarget n (phaseNat n) s) + tau)

private theorem windowFinitePartition_pos (alpha m M : ℕ) (hM : 1 ≤ M) (l : ℝ) :
    0 < windowFinitePartition alpha m M l := by
  unfold windowFinitePartition
  exact Finset.sum_pos (fun _ _ ↦ Real.exp_pos _)
    ⟨m + 1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩

private theorem sum_windowGaussian_eq_partitionFn (m M : ℕ) (l : ℝ) :
    (∑ i ∈ Finset.Icc (m + 1) (m + M),
        Real.exp (l * (i : ℝ) - Real.log 2 / 2 * (i : ℝ) ^ 2)) =
      partitionFn (windowSupportSet m M) l := by
  unfold partitionFn
  let e : {i : ℕ // i ∈ Finset.Icc (m + 1) (m + M)} ≃ windowSupportSet m M :=
    { toFun := fun x ↦ ⟨(x.1 : ℤ), by
        obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp x.2
        exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩⟩
      invFun := fun y ↦ ⟨y.1.toNat, by
        obtain ⟨h1, h2⟩ := y.2
        rw [Finset.mem_Icc]
        omega⟩
      left_inv := fun x ↦ Subtype.ext (Int.toNat_natCast _)
      right_inv := fun y ↦ Subtype.ext (Int.toNat_of_nonneg (by
        obtain ⟨h1, _⟩ := y.2; omega)) }
  letI : Fintype (windowSupportSet m M) := Fintype.ofEquiv _ e
  rw [← e.tsum_eq, tsum_fintype]
  rw [← Finset.sum_coe_sort (Finset.Icc (m + 1) (m + M))]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  unfold gaussWeight
  simp only [e, Equiv.coe_fn_mk, Int.cast_natCast]

private theorem s4_subset_windowSupportSet {m M : ℕ} (hm : m ≤ 1) (hM : 7 ≤ M) :
    S4 ⊆ windowSupportSet m M := by
  intro j hj
  simp only [S4, Set.mem_insert_iff, Set.mem_singleton_iff] at hj
  simp only [windowSupportSet, Set.mem_setOf_eq]
  rcases hj with rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩

private theorem windowSupportSet_subset_Splus (m M : ℕ) :
    windowSupportSet m M ⊆ Splus := by
  intro j hj
  simp only [windowSupportSet, Splus, Set.mem_setOf_eq] at hj ⊢
  omega

private theorem log_windowFinitePartition_bounds
    {alpha m M : ℕ} (hM : 1 ≤ M) (halpha : 2 * (m + M) ≤ alpha) (l : ℝ) :
    let err : ℝ := ((m + M : ℕ) : ℝ) ^ 2 / (alpha : ℝ)
    Real.log (partitionFn (windowSupportSet m M) l) - err ≤
        Real.log (windowFinitePartition alpha m M l) ∧
      Real.log (windowFinitePartition alpha m M l) ≤
        Real.log (partitionFn (windowSupportSet m M) l) := by
  intro err
  have ha_pos : (0 : ℝ) < (alpha : ℝ) := by exact_mod_cast (show 0 < alpha by omega)
  have hZpos : 0 < partitionFn (windowSupportSet m M) l := by
    rw [← sum_windowGaussian_eq_partitionFn m M l]
    exact Finset.sum_pos (fun _ _ ↦ Real.exp_pos _)
      ⟨m + 1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  have hWpos := windowFinitePartition_pos alpha m M hM l
  have hterm : ∀ i ∈ Finset.Icc (m + 1) (m + M),
      -err ≤ Real.log (alpha.descFactorial i : ℝ) - (i : ℝ) * Real.log (alpha : ℝ) ∧
        Real.log (alpha.descFactorial i : ℝ) - (i : ℝ) * Real.log (alpha : ℝ) ≤ 0 := by
    intro i hi
    obtain ⟨_, hi_hi⟩ := Finset.mem_Icc.mp hi
    have hi_lt : i < alpha := by omega
    have h2i : 2 * i ≤ alpha := by omega
    obtain ⟨hid, hle0, hge⟩ := finiteDeficitResidualScore_bounds hi_lt
    rw [hid]
    refine ⟨?_, hle0⟩
    have hsq : (i : ℝ) ^ 2 ≤ ((m + M : ℕ) : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg i) (by exact_mod_cast hi_hi) 2
    have hdiv : -(err) ≤ -(i : ℝ) ^ 2 / (alpha : ℝ) := by
      dsimp [err]
      have h1 := div_le_div_of_nonneg_right hsq ha_pos.le
      rw [neg_div]
      exact neg_le_neg h1
    exact hdiv.trans (hge h2i)
  have hlo : Real.exp (-err) * partitionFn (windowSupportSet m M) l ≤
      windowFinitePartition alpha m M l := by
    rw [← sum_windowGaussian_eq_partitionFn m M l, Finset.mul_sum]
    unfold windowFinitePartition windowFiniteScore
    refine Finset.sum_le_sum fun i hi ↦ ?_
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [(hterm i hi).1])
  have hhi : windowFinitePartition alpha m M l ≤ partitionFn (windowSupportSet m M) l := by
    rw [← sum_windowGaussian_eq_partitionFn m M l]
    unfold windowFinitePartition windowFiniteScore
    refine Finset.sum_le_sum fun i hi ↦ ?_
    exact Real.exp_le_exp.mpr (by linarith [(hterm i hi).2])
  refine ⟨?_, Real.log_le_log hWpos hhi⟩
  have h1 := Real.log_le_log (mul_pos (Real.exp_pos _) hZpos) hlo
  rw [Real.log_mul (Real.exp_pos _).ne' hZpos.ne', Real.log_exp] at h1
  linarith

private theorem bddBelow_windowFiniteDual
    {alpha m M : ℕ} (hm : m ≤ 1) (hM : 7 ≤ M) (halpha : 2 * (m + M) ≤ alpha)
    {T : ℝ} (hT : T ∈ Set.Ioo (2 : ℝ) 5) :
    BddBelow (Set.range fun l : ℝ ↦ Real.log (windowFinitePartition alpha m M l) - l * T) := by
  have hm4 := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT)
  obtain ⟨B, hB⟩ := bddBelow_dual (s4_subset_windowSupportSet hm hM) hm4
  refine ⟨B - ((m + M : ℕ) : ℝ) ^ 2 / (alpha : ℝ), ?_⟩
  rintro _ ⟨l, rfl⟩
  have h1 : B ≤ Real.log (partitionFn (windowSupportSet m M) l) - l * T := hB ⟨l, rfl⟩
  have h2 := (log_windowFinitePartition_bounds (by omega : 1 ≤ M) halpha l).1
  linarith

/-- **Lemma 3.2(i), eq. `(3.10)` uniform `O_M(1/α)` finite-window dual error:**
for all `m ≤ 1`, `M ≥ 7`, `2(m + M) ≤ α`, and `T ∈ (2, 5)` (covering `K_*`),
`𝓕_{S_{m,M}}(T) - (m + M)² / α ≤ 𝓕_{n, S_{m,M}}(T) ≤ 𝓕_{S_{m,M}}(T)` and
`|𝓕_{n, S_{m,M}}(T) - 𝓕_{S_{m,M}}(T)| ≤ (m + M)² / α`. -/
theorem abs_windowFiniteEntropy_sub_dualValue_le
    {alpha m M : ℕ} (hm : m ≤ 1) (hM : 7 ≤ M) (halpha : 2 * (m + M) ≤ alpha)
    {T : ℝ} (hT : T ∈ Set.Ioo (2 : ℝ) 5) :
    let S_win : Set ℤ := {j : ℤ | ((m + 1 : ℕ) : ℤ) ≤ j ∧ j ≤ ((m + M : ℕ) : ℤ)}
    let F_fin : ℝ := ⨅ l : ℝ,
      (Real.log (∑ i ∈ Finset.Icc (m + 1) (m + M),
          Real.exp (l * (i : ℝ) +
            (Real.log (alpha.descFactorial i : ℝ) - (i : ℝ) * Real.log (alpha : ℝ) -
              Real.log 2 / 2 * (i : ℝ) ^ 2))) - l * T)
    (dualValue S_win T - ((m + M : ℕ) : ℝ) ^ 2 / (alpha : ℝ) ≤ F_fin ∧
        F_fin ≤ dualValue S_win T) ∧
      |F_fin - dualValue S_win T| ≤ ((m + M : ℕ) : ℝ) ^ 2 / (alpha : ℝ) := by
  intro S_win F_fin
  change (dualValue (windowSupportSet m M) T - ((m + M : ℕ) : ℝ) ^ 2 / (alpha : ℝ) ≤
      windowFiniteEntropy alpha m M T ∧
    windowFiniteEntropy alpha m M T ≤ dualValue (windowSupportSet m M) T) ∧
    |windowFiniteEntropy alpha m M T - dualValue (windowSupportSet m M) T| ≤
      ((m + M : ℕ) : ℝ) ^ 2 / (alpha : ℝ)
  have hm4 := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT)
  have hbdd_fin := bddBelow_windowFiniteDual hm hM halpha hT
  have hbdd_lim := bddBelow_dual (s4_subset_windowSupportSet hm hM) hm4
  have hlo : dualValue (windowSupportSet m M) T - ((m + M : ℕ) : ℝ) ^ 2 / (alpha : ℝ) ≤
      windowFiniteEntropy alpha m M T := by
    refine le_ciInf fun l ↦ ?_
    have h1 : dualValue (windowSupportSet m M) T ≤
        Real.log (partitionFn (windowSupportSet m M) l) - l * T := ciInf_le hbdd_lim l
    have h2 := (log_windowFinitePartition_bounds (by omega : 1 ≤ M) halpha l).1
    linarith
  have hhi : windowFiniteEntropy alpha m M T ≤ dualValue (windowSupportSet m M) T := by
    refine le_ciInf fun l ↦ ?_
    have h1 : windowFiniteEntropy alpha m M T ≤
        Real.log (windowFinitePartition alpha m M l) - l * T := ciInf_le hbdd_fin l
    have h2 := (log_windowFinitePartition_bounds (by omega : 1 ≤ M) halpha l).2
    linarith
  refine ⟨⟨hlo, hhi⟩, abs_le.mpr ⟨by linarith, ?_⟩⟩
  have herr_nn : 0 ≤ ((m + M : ℕ) : ℝ) ^ 2 / (alpha : ℝ) := by positivity
  linarith

private theorem windowFiniteEntropy_bounds
    {alpha m M : ℕ} (hm : m ≤ 1) (hM : 7 ≤ M) (halpha : 2 * (m + M) ≤ alpha)
    {T : ℝ} (hT : T ∈ Set.Ioo (2 : ℝ) 5) :
    (dualValue (windowSupportSet m M) T - ((m + M : ℕ) : ℝ) ^ 2 / (alpha : ℝ) ≤
        windowFiniteEntropy alpha m M T ∧
      windowFiniteEntropy alpha m M T ≤ dualValue (windowSupportSet m M) T) ∧
    |windowFiniteEntropy alpha m M T - dualValue (windowSupportSet m M) T| ≤
      ((m + M : ℕ) : ℝ) ^ 2 / (alpha : ℝ) :=
  abs_windowFiniteEntropy_sub_dualValue_le hm hM halpha hT

private theorem reducedTarget_mem_Icc_and_Ioo
    {theta T : ℝ} (htheta : theta ∈ Set.Icc (0 : ℝ) (1 / 20)) (hT : T ∈ KcapInterval) :
    (T - theta) / (1 - theta) ∈ Set.Icc (11 / 4 : ℝ) (9 / 2) ∧
      (T - theta) / (1 - theta) ∈ Set.Ioo (2 : ℝ) 5 := by
  obtain ⟨h2lo, h2hi⟩ := two_div_log_two_bounds
  obtain ⟨hT_lo, hT_hi⟩ := hT
  have h1m_pos : 0 < 1 - theta := by linarith [htheta.2]
  have hicc : (T - theta) / (1 - theta) ∈ Set.Icc (11 / 4 : ℝ) (9 / 2) := by
    constructor
    · rw [le_div_iff₀ h1m_pos]; nlinarith [htheta.1, htheta.2, hT_lo, h2lo]
    · rw [div_le_iff₀ h1m_pos]; nlinarith [htheta.1, htheta.2, hT_hi, h2hi]
  exact ⟨hicc, ⟨by linarith [hicc.1], by linarith [hicc.2]⟩⟩

private theorem s0m_diff_one_eq_windowSupportSet {M : ℕ} (hM : 2 ≤ M) :
    S0M M \ {1} = windowSupportSet 1 (M - 1) := by
  ext j
  simp only [S0M, windowSupportSet, Set.mem_sdiff, Set.mem_setOf_eq, Set.mem_singleton_iff]
  have : ((1 + (M - 1) : ℕ) : ℤ) = (M : ℤ) := by exact_mod_cast (show 1 + (M - 1) = M by omega)
  omega

/-- **Lemma 3.2(iv) uniform `O_M(1/α)` capped finite-window dual error:**
for all `M ≥ 8`, `2 M ≤ α`, `ϑ ∈ [0, 1/20]`, and `T ∈ K_cap`,
`|𝓕_{n, S_{0,M}}^{=ϑ}(T) - 𝓕_{S_{0,M}}^{=ϑ}(T)| ≤ (1 - ϑ) M² / α ≤ M² / α`. -/
theorem abs_cappedWindowFiniteEntropy_sub_cappedDualValue_le
    {alpha M : ℕ} (hM : 8 ≤ M) (halpha : 2 * M ≤ alpha)
    {theta T : ℝ} (htheta : theta ∈ Set.Icc (0 : ℝ) (1 / 20)) (hT : T ∈ KcapInterval) :
    let u : ℝ := (T - theta) / (1 - theta)
    let F_tail : ℝ := ⨅ l : ℝ,
      (Real.log (∑ i ∈ Finset.Icc 2 M,
          Real.exp (l * (i : ℝ) +
            (Real.log (alpha.descFactorial i : ℝ) - (i : ℝ) * Real.log (alpha : ℝ) -
              Real.log 2 / 2 * (i : ℝ) ^ 2))) - l * u)
    let F_cap_fin : ℝ := binEntropy theta - Real.log 2 / 2 * theta + (1 - theta) * F_tail
    |F_cap_fin - cappedDualValue (S0M M) theta T| ≤ (1 - theta) * (M : ℝ) ^ 2 / (alpha : ℝ) ∧
      |F_cap_fin - cappedDualValue (S0M M) theta T| ≤ (M : ℝ) ^ 2 / (alpha : ℝ) := by
  intro u F_tail F_cap_fin
  have h1m_nn : 0 ≤ 1 - theta := by linarith [htheta.2]
  have h1m_le1 : 1 - theta ≤ 1 := by linarith [htheta.1]
  have hM_eq : 1 + (M - 1) = M := by omega
  have hu_ioo := (reducedTarget_mem_Icc_and_Ioo htheta hT).2
  have hwin := (windowFiniteEntropy_bounds (alpha := alpha) (m := 1) (M := M - 1)
    le_rfl (by omega) (by omega) hu_ioo).2
  have htail_eq : F_tail = windowFiniteEntropy alpha 1 (M - 1) u := by
    unfold F_tail windowFiniteEntropy windowFinitePartition windowFiniteScore
    simp only [hM_eq]
  have hcap_diff : F_cap_fin - cappedDualValue (S0M M) theta T =
      (1 - theta) * (windowFiniteEntropy alpha 1 (M - 1) u -
        dualValue (windowSupportSet 1 (M - 1)) u) := by
    unfold F_cap_fin cappedDualValue
    rw [htail_eq, s0m_diff_one_eq_windowSupportSet (by omega : 2 ≤ M)]
    ring
  rw [hcap_diff, abs_mul, abs_of_nonneg h1m_nn]
  have h1 : (1 - theta) * |windowFiniteEntropy alpha 1 (M - 1) u -
      dualValue (windowSupportSet 1 (M - 1)) u| ≤
      (1 - theta) * ((M : ℝ) ^ 2 / (alpha : ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ h1m_nn
    simpa only [hM_eq] using hwin
  have h1' : (1 - theta) * ((M : ℝ) ^ 2 / (alpha : ℝ)) =
      (1 - theta) * (M : ℝ) ^ 2 / (alpha : ℝ) := by ring
  rw [h1'] at h1
  refine ⟨h1, h1.trans ?_⟩
  have hnn : 0 ≤ (M : ℝ) ^ 2 / (alpha : ℝ) := by positivity
  calc (1 - theta) * (M : ℝ) ^ 2 / (alpha : ℝ)
      = (1 - theta) * ((M : ℝ) ^ 2 / (alpha : ℝ)) := by ring
    _ ≤ 1 * ((M : ℝ) ^ 2 / (alpha : ℝ)) := mul_le_mul_of_nonneg_right h1m_le1 hnn
    _ = (M : ℝ) ^ 2 / (alpha : ℝ) := one_mul _

private theorem cappedWindowFiniteEntropy_bounds
    {alpha M : ℕ} (hM : 8 ≤ M) (halpha : 2 * M ≤ alpha)
    {theta T : ℝ} (htheta : theta ∈ Set.Icc (0 : ℝ) (1 / 20)) (hT : T ∈ KcapInterval) :
    |cappedWindowFiniteEntropy alpha M theta T - cappedDualValue (S0M M) theta T| ≤
      (M : ℝ) ^ 2 / (alpha : ℝ) := by
  have hM_eq : 1 + (M - 1) = M := by omega
  have hraw := (abs_cappedWindowFiniteEntropy_sub_cappedDualValue_le hM halpha htheta hT).2
  have hcap_eq : cappedWindowFiniteEntropy alpha M theta T =
      binEntropy theta - Real.log 2 / 2 * theta +
        (1 - theta) * (⨅ l : ℝ,
          (Real.log (∑ i ∈ Finset.Icc 2 M,
              Real.exp (l * (i : ℝ) +
                (Real.log (alpha.descFactorial i : ℝ) -
                  (i : ℝ) * Real.log (alpha : ℝ) -
                  Real.log 2 / 2 * (i : ℝ) ^ 2))) -
            l * ((T - theta) / (1 - theta)))) := by
    unfold cappedWindowFiniteEntropy windowFiniteEntropy windowFinitePartition windowFiniteScore
    simp only [hM_eq]
  rw [hcap_eq]
  exact hraw

private theorem lipschitz_of_concave_on_padded_Icc
    {f : ℝ → ℝ} {a_lo a_hi r_pad B_lo U_hi : ℝ}
    (hr : 0 < r_pad)
    (hconc : ∀ {u v a b : ℝ},
      u ∈ Set.Icc (a_lo - r_pad) (a_hi + r_pad) →
      v ∈ Set.Icc (a_lo - r_pad) (a_hi + r_pad) →
      0 ≤ a → 0 ≤ b → a + b = 1 →
      a * f u + b * f v ≤ f (a * u + b * v))
    (hbdd : ∀ t ∈ Set.Icc (a_lo - r_pad) (a_hi + r_pad), B_lo ≤ f t ∧ f t ≤ U_hi)
    {x y : ℝ} (hx : x ∈ Set.Icc a_lo a_hi) (hy : y ∈ Set.Icc a_lo a_hi) :
    |f y - f x| ≤ ((U_hi - B_lo) / r_pad) * |y - x| := by
  set Mspan : ℝ := U_hi - B_lo
  have step : ∀ {u v : ℝ}, u ∈ Set.Icc a_lo a_hi → v ∈ Set.Icc a_lo a_hi → u ≤ v →
      f v - f u ≤ (Mspan / r_pad) * (v - u) ∧
      f u - f v ≤ (Mspan / r_pad) * (v - u) := by
    intro u v hu hv huv
    have hu_pad : u ∈ Set.Icc (a_lo - r_pad) (a_hi + r_pad) :=
      ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hv_pad : v ∈ Set.Icc (a_lo - r_pad) (a_hi + r_pad) :=
      ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hul_pad : u - r_pad ∈ Set.Icc (a_lo - r_pad) (a_hi + r_pad) :=
      ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hvr_pad : v + r_pad ∈ Set.Icc (a_lo - r_pad) (a_hi + r_pad) :=
      ⟨by linarith [hv.1], by linarith [hv.2]⟩
    set D : ℝ := r_pad + (v - u)
    have hDpos : 0 < D := by dsimp [D]; linarith
    have ha : 0 ≤ r_pad / D := div_nonneg hr.le hDpos.le
    have hb : 0 ≤ (v - u) / D := div_nonneg (by linarith) hDpos.le
    have hsum : r_pad / D + (v - u) / D = 1 := by rw [← add_div, div_self hDpos.ne']
    constructor
    · have hcomb : r_pad / D * v + (v - u) / D * (u - r_pad) = u := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hDpos.ne']
        dsimp [D]; ring
      have hc := hconc hv_pad hul_pad ha hb hsum
      rw [hcomb] at hc
      have hmul : r_pad * f v + (v - u) * f (u - r_pad) ≤ D * f u := by
        have hd : (r_pad * f v + (v - u) * f (u - r_pad)) / D ≤ f u := by
          rwa [add_div, mul_div_right_comm, mul_div_right_comm]
        exact (div_le_iff₀' hDpos).mp hd
      dsimp [D] at hmul
      have hsp : f u - f (u - r_pad) ≤ Mspan := by
        dsimp [Mspan]; linarith [(hbdd u hu_pad).2, (hbdd (u - r_pad) hul_pad).1]
      have hpr := mul_le_mul_of_nonneg_left hsp (by linarith : 0 ≤ v - u)
      have hdiv_le : f v - f u ≤ Mspan * (v - u) / r_pad := by
        rw [le_div_iff₀ hr]; linarith
      simpa [div_mul_eq_mul_div] using hdiv_le
    · have hcomb : r_pad / D * u + (v - u) / D * (v + r_pad) = v := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hDpos.ne']
        dsimp [D]; ring
      have hc := hconc hu_pad hvr_pad ha hb hsum
      rw [hcomb] at hc
      have hmul : r_pad * f u + (v - u) * f (v + r_pad) ≤ D * f v := by
        have hd : (r_pad * f u + (v - u) * f (v + r_pad)) / D ≤ f v := by
          rwa [add_div, mul_div_right_comm, mul_div_right_comm]
        exact (div_le_iff₀' hDpos).mp hd
      dsimp [D] at hmul
      have hsp : f v - f (v + r_pad) ≤ Mspan := by
        dsimp [Mspan]; linarith [(hbdd v hv_pad).2, (hbdd (v + r_pad) hvr_pad).1]
      have hpr := mul_le_mul_of_nonneg_left hsp (by linarith : 0 ≤ v - u)
      have hdiv_le : f u - f v ≤ Mspan * (v - u) / r_pad := by
        rw [le_div_iff₀ hr]; linarith
      simpa [div_mul_eq_mul_div] using hdiv_le
  rcases le_total y x with hyx | hxy
  · obtain ⟨h1, h2⟩ := step hy hx hyx
    rw [abs_sub_comm y x, abs_of_nonneg (sub_nonneg.mpr hyx), abs_le]
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨h1, h2⟩ := step hx hy hxy
    rw [abs_of_nonneg (sub_nonneg.mpr hxy), abs_le]
    exact ⟨by linarith, by linarith⟩

private theorem dualValue_window_bounds_on_padded
    {m M : ℕ} (hm : m ≤ 1) (hM : 7 ≤ M)
    (T : ℝ) (hT : T ∈ Set.Icc (17 / 8 : ℝ) (37 / 8)) :
    min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8)) ≤
        dualValue (windowSupportSet m M) T ∧
      dualValue (windowSupportSet m M) T ≤ Real.log (partitionFn Splus 0) := by
  have hL25 : (17 / 8 : ℝ) ∈ Set.Ioo (2 : ℝ) 5 := by norm_num
  have hR25 : (37 / 8 : ℝ) ∈ Set.Ioo (2 : ℝ) 5 := by norm_num
  have hT25 : T ∈ Set.Ioo (2 : ℝ) 5 := ⟨by linarith [hT.1], by linarith [hT.2]⟩
  have hmL := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hL25)
  have hmR := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hR25)
  have hmT := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT25)
  set wL : ℝ := (37 / 8 - T) / (20 / 8)
  set wR : ℝ := (T - 17 / 8) / (20 / 8)
  have hwL_nn : 0 ≤ wL := div_nonneg (by linarith [hT.2]) (by norm_num)
  have hwR_nn : 0 ≤ wR := div_nonneg (by linarith [hT.1]) (by norm_num)
  have hw_sum : wL + wR = 1 := by dsimp [wL, wR]; ring
  have hw_pt : wL * (17 / 8 : ℝ) + wR * (37 / 8 : ℝ) = T := by dsimp [wL, wR]; ring
  have hS4_conc : wL * dualValue S4 (17 / 8) + wR * dualValue S4 (37 / 8) ≤ dualValue S4 T := by
    have hbL := bddBelow_dual subset_rfl hmL
    have hbR := bddBelow_dual subset_rfl hmR
    refine le_ciInf fun l ↦ ?_
    have e1 := mul_le_mul_of_nonneg_left (ciInf_le hbL l) hwL_nn
    have e2 := mul_le_mul_of_nonneg_left (ciInf_le hbR l) hwR_nn
    calc wL * dualValue S4 (17 / 8) + wR * dualValue S4 (37 / 8)
        ≤ wL * (Real.log (partitionFn S4 l) - l * (17 / 8)) +
            wR * (Real.log (partitionFn S4 l) - l * (37 / 8)) := add_le_add e1 e2
      _ = (wL + wR) * Real.log (partitionFn S4 l) -
            l * (wL * (17 / 8) + wR * (37 / 8)) := by ring
      _ = Real.log (partitionFn S4 l) - l * T := by rw [hw_sum, hw_pt, one_mul]
  set m0 := min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))
  have hm0_le_S4 : m0 ≤ dualValue S4 T := by
    have e1 := mul_le_mul_of_nonneg_left
      (min_le_left (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))) hwL_nn
    have e2 := mul_le_mul_of_nonneg_left
      (min_le_right (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))) hwR_nn
    have : m0 = (wL + wR) * m0 := by rw [hw_sum, one_mul]
    linarith
  have hmono := dualValue_mono subset_rfl (s4_subset_windowSupportSet hm hM) hmT
  have h0 := dualValue_le_at (s4_subset_windowSupportSet hm hM) hmT 0
  have hpos : 0 < partitionFn (windowSupportSet m M) 0 := by
    rw [← sum_windowGaussian_eq_partitionFn m M 0]
    exact Finset.sum_pos (fun _ _ ↦ Real.exp_pos _)
      ⟨m + 1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  have hhi : dualValue (windowSupportSet m M) T ≤ Real.log (partitionFn Splus 0) := by
    linarith [Real.log_le_log hpos (partitionFn_mono (windowSupportSet_subset_Splus m M) 0)]
  exact ⟨hm0_le_S4.trans hmono, hhi⟩

private def universalDualLip : ℝ :=
  8 * (Real.log (partitionFn Splus 0) - min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8)))

private theorem universalDualLip_nonneg : 0 ≤ universalDualLip := by
  have hb := dualValue_window_bounds_on_padded (m := 0) (M := 7) (by omega) le_rfl
    3 (by norm_num)
  unfold universalDualLip
  linarith [hb.1, hb.2]

private theorem abs_dualValue_window_sub_le
    {m M : ℕ} (hm : m ≤ 1) (hM : 7 ≤ M)
    {T₁ T₂ : ℝ} (hT₁ : T₁ ∈ Set.Icc (9 / 4 : ℝ) (9 / 2))
    (hT₂ : T₂ ∈ Set.Icc (9 / 4 : ℝ) (9 / 2)) :
    |dualValue (windowSupportSet m M) T₁ - dualValue (windowSupportSet m M) T₂| ≤
      universalDualLip * |T₁ - T₂| := by
  have hconc : ∀ {u v a b : ℝ},
      u ∈ Set.Icc ((9 / 4 : ℝ) - 1 / 8) ((9 / 2 : ℝ) + 1 / 8) →
      v ∈ Set.Icc ((9 / 4 : ℝ) - 1 / 8) ((9 / 2 : ℝ) + 1 / 8) →
      0 ≤ a → 0 ≤ b → a + b = 1 →
      a * dualValue (windowSupportSet m M) u + b * dualValue (windowSupportSet m M) v ≤
        dualValue (windowSupportSet m M) (a * u + b * v) := by
    intro u v a b hu hv ha hb hsum
    have hu25 : u ∈ Set.Ioo (2 : ℝ) 5 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hv25 : v ∈ Set.Ioo (2 : ℝ) 5 := ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hmu := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hu25)
    have hmv := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hv25)
    have hbu := bddBelow_dual (s4_subset_windowSupportSet hm hM) hmu
    have hbv := bddBelow_dual (s4_subset_windowSupportSet hm hM) hmv
    refine le_ciInf fun l ↦ ?_
    have e1 := mul_le_mul_of_nonneg_left (ciInf_le hbu l) ha
    have e2 := mul_le_mul_of_nonneg_left (ciInf_le hbv l) hb
    calc a * dualValue (windowSupportSet m M) u + b * dualValue (windowSupportSet m M) v
        ≤ a * (Real.log (partitionFn (windowSupportSet m M) l) - l * u) +
            b * (Real.log (partitionFn (windowSupportSet m M) l) - l * v) := add_le_add e1 e2
      _ = (a + b) * Real.log (partitionFn (windowSupportSet m M) l) -
            l * (a * u + b * v) := by ring
      _ = Real.log (partitionFn (windowSupportSet m M) l) - l * (a * u + b * v) := by
            rw [hsum, one_mul]
  have hbdd : ∀ t ∈ Set.Icc ((9 / 4 : ℝ) - 1 / 8) ((9 / 2 : ℝ) + 1 / 8),
      min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8)) ≤
        dualValue (windowSupportSet m M) t ∧
      dualValue (windowSupportSet m M) t ≤ Real.log (partitionFn Splus 0) := by
    intro t ht
    exact dualValue_window_bounds_on_padded hm hM t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hlip := lipschitz_of_concave_on_padded_Icc (r_pad := 1 / 8) (by norm_num)
    hconc hbdd hT₂ hT₁
  have hconst : (Real.log (partitionFn Splus 0) -
      min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))) / (1 / 8 : ℝ) =
      universalDualLip := by
    unfold universalDualLip; ring
  rwa [hconst] at hlip

private theorem abs_cappedDualValue_S0M_sub_le
    {M : ℕ} (hM : 8 ≤ M) {theta T₁ T₂ : ℝ}
    (htheta : theta ∈ Set.Icc (0 : ℝ) (1 / 20))
    (hT₁ : T₁ ∈ KcapInterval) (hT₂ : T₂ ∈ KcapInterval) :
    |cappedDualValue (S0M M) theta T₁ - cappedDualValue (S0M M) theta T₂| ≤
      universalDualLip * |T₁ - T₂| := by
  have h1m_pos : 0 < 1 - theta := by linarith [htheta.2]
  have hu₁ := (reducedTarget_mem_Icc_and_Ioo htheta hT₁).1
  have hu₂ := (reducedTarget_mem_Icc_and_Ioo htheta hT₂).1
  have hu₁_wide : (T₁ - theta) / (1 - theta) ∈ Set.Icc (9 / 4 : ℝ) (9 / 2) :=
    ⟨by linarith [hu₁.1], hu₁.2⟩
  have hu₂_wide : (T₂ - theta) / (1 - theta) ∈ Set.Icc (9 / 4 : ℝ) (9 / 2) :=
    ⟨by linarith [hu₂.1], hu₂.2⟩
  have hdiff : cappedDualValue (S0M M) theta T₁ - cappedDualValue (S0M M) theta T₂ =
      (1 - theta) *
        (dualValue (windowSupportSet 1 (M - 1)) ((T₁ - theta) / (1 - theta)) -
          dualValue (windowSupportSet 1 (M - 1)) ((T₂ - theta) / (1 - theta))) := by
    unfold cappedDualValue
    rw [s0m_diff_one_eq_windowSupportSet (by omega : 2 ≤ M)]
    ring
  rw [hdiff, abs_mul, abs_of_pos h1m_pos]
  have hwin := abs_dualValue_window_sub_le (m := 1) (M := M - 1) le_rfl (by omega)
    hu₁_wide hu₂_wide
  have hsub_u : (T₁ - theta) / (1 - theta) - (T₂ - theta) / (1 - theta) =
      (T₁ - T₂) / (1 - theta) := by ring
  rw [hsub_u, abs_div, abs_of_pos h1m_pos] at hwin
  calc (1 - theta) *
        |dualValue (windowSupportSet 1 (M - 1)) ((T₁ - theta) / (1 - theta)) -
          dualValue (windowSupportSet 1 (M - 1)) ((T₂ - theta) / (1 - theta))|
      ≤ (1 - theta) * (universalDualLip * (|T₁ - T₂| / (1 - theta))) :=
        mul_le_mul_of_nonneg_left hwin h1m_pos.le
    _ = universalDualLip * |T₁ - T₂| := by field_simp [h1m_pos.ne']

private theorem continuousOn_windowFiniteEntropy_Icc
    {alpha m M : ℕ} (hm : m ≤ 1) (hM : 7 ≤ M) (halpha : 2 * (m + M) ≤ alpha) :
    ContinuousOn (windowFiniteEntropy alpha m M) (Set.Icc (9 / 4 : ℝ) (9 / 2)) := by
  have hconc : ∀ {u v a b : ℝ},
      u ∈ Set.Icc ((9 / 4 : ℝ) - 1 / 8) ((9 / 2 : ℝ) + 1 / 8) →
      v ∈ Set.Icc ((9 / 4 : ℝ) - 1 / 8) ((9 / 2 : ℝ) + 1 / 8) →
      0 ≤ a → 0 ≤ b → a + b = 1 →
      a * windowFiniteEntropy alpha m M u + b * windowFiniteEntropy alpha m M v ≤
        windowFiniteEntropy alpha m M (a * u + b * v) := by
    intro u v a b hu hv ha hb hsum
    have hu25 : u ∈ Set.Ioo (2 : ℝ) 5 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hv25 : v ∈ Set.Ioo (2 : ℝ) 5 := ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hbu := bddBelow_windowFiniteDual hm hM halpha hu25
    have hbv := bddBelow_windowFiniteDual hm hM halpha hv25
    refine le_ciInf fun l ↦ ?_
    have e1 := mul_le_mul_of_nonneg_left (ciInf_le hbu l) ha
    have e2 := mul_le_mul_of_nonneg_left (ciInf_le hbv l) hb
    calc a * windowFiniteEntropy alpha m M u + b * windowFiniteEntropy alpha m M v
        ≤ a * (Real.log (windowFinitePartition alpha m M l) - l * u) +
            b * (Real.log (windowFinitePartition alpha m M l) - l * v) := add_le_add e1 e2
      _ = (a + b) * Real.log (windowFinitePartition alpha m M l) -
            l * (a * u + b * v) := by ring
      _ = Real.log (windowFinitePartition alpha m M l) - l * (a * u + b * v) := by
            rw [hsum, one_mul]
  set B_lo : ℝ := min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8)) -
    ((m + M : ℕ) : ℝ) ^ 2 / (alpha : ℝ)
  set U_hi : ℝ := Real.log (partitionFn Splus 0)
  have hbdd : ∀ t ∈ Set.Icc ((9 / 4 : ℝ) - 1 / 8) ((9 / 2 : ℝ) + 1 / 8),
      B_lo ≤ windowFiniteEntropy alpha m M t ∧ windowFiniteEntropy alpha m M t ≤ U_hi := by
    intro t ht
    have ht_icc : t ∈ Set.Icc (17 / 8 : ℝ) (37 / 8) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have ht_ioo : t ∈ Set.Ioo (2 : ℝ) 5 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hd := dualValue_window_bounds_on_padded hm hM t ht_icc
    have hw := (windowFiniteEntropy_bounds hm hM halpha ht_ioo).1
    dsimp [B_lo, U_hi]
    exact ⟨by linarith [hd.1, hw.1], hw.2.trans hd.2⟩
  set K : ℝ := (U_hi - B_lo) / (1 / 8 : ℝ) + 1
  have hKpos : 0 < K := by
    have hb3 := hbdd 3 (by norm_num)
    have : 0 ≤ U_hi - B_lo := by linarith [hb3.1, hb3.2]
    dsimp [K]; positivity
  rw [Metric.continuousOn_iff]
  intro x hx eps heps
  refine ⟨eps / K, div_pos heps hKpos, fun y hy hdist ↦ ?_⟩
  rw [Real.dist_eq] at hdist ⊢
  have hlip := lipschitz_of_concave_on_padded_Icc (r_pad := 1 / 8) (by norm_num) hconc hbdd hx hy
  have h1 : ((U_hi - B_lo) / (1 / 8 : ℝ)) * |y - x| ≤ K * |y - x| := by
    dsimp [K]; linarith [abs_nonneg (y - x)]
  have h2 : K * |y - x| < K * (eps / K) := mul_lt_mul_of_pos_left hdist hKpos
  rw [mul_div_cancel₀ _ hKpos.ne'] at h2
  linarith

private theorem abs_tilt_of_windowFiniteDual_le
    {alpha m M : ℕ} (hm : m ≤ 1) (hM : 7 ≤ M) (halpha : 2 * (m + M) ≤ alpha)
    {T l U : ℝ} (hT : T ∈ Set.Icc (9 / 4 : ℝ) (9 / 2))
    (hl : Real.log (windowFinitePartition alpha m M l) - l * T ≤ U) :
    let B_score : ℝ := 2 * ((m + M : ℕ) : ℝ) ^ 2 + 1
    let M_tilt : ℝ := max 0 (max (4 * (U + B_score)) (U + B_score))
    |l| ≤ M_tilt ∧
      -M_tilt * ((alpha : ℝ) + 2) - B_score ≤
        Real.log (windowFinitePartition alpha m M l) - l * (alpha : ℝ) := by
  intro B_score M_tilt
  have ha_ge1 : (1 : ℝ) ≤ (alpha : ℝ) := by exact_mod_cast (show 1 ≤ alpha by omega)
  have hq_le1 : Real.log 2 ≤ 1 := le_trans Real.log_two_lt_d9.le (by norm_num)
  have hscore_lo : ∀ i ∈ Finset.Icc (m + 1) (m + M), -B_score ≤ windowFiniteScore alpha i := by
    intro i hi
    obtain ⟨_, hi_hi⟩ := Finset.mem_Icc.mp hi
    have hi_lt : i < alpha := by omega
    have h2i : 2 * i ≤ alpha := by omega
    obtain ⟨hid, _, hge⟩ := finiteDeficitResidualScore_bounds hi_lt
    unfold windowFiniteScore
    rw [hid]
    have hsq : (i : ℝ) ^ 2 ≤ ((m + M : ℕ) : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg i) (by exact_mod_cast hi_hi) 2
    have h1 : -(i : ℝ) ^ 2 ≤ -(i : ℝ) ^ 2 / (alpha : ℝ) := by
      have hd : (i : ℝ) ^ 2 / (alpha : ℝ) ≤ (i : ℝ) ^ 2 / 1 :=
        div_le_div_of_nonneg_left (sq_nonneg _) zero_lt_one ha_ge1
      rw [div_one] at hd
      rw [neg_div]
      linarith
    have hge' := h1.trans (hge h2i)
    have hq_i : Real.log 2 / 2 * (i : ℝ) ^ 2 ≤ ((m + M : ℕ) : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (i : ℝ), Real.log_pos one_lt_two]
    dsimp [B_score]
    linarith
  have hterm_le : ∀ i ∈ Finset.Icc (m + 1) (m + M),
      l * (i : ℝ) - B_score ≤ Real.log (windowFinitePartition alpha m M l) := by
    intro i hi
    have hsub : Real.exp (l * (i : ℝ) + windowFiniteScore alpha i) ≤
        windowFinitePartition alpha m M l := by
      unfold windowFinitePartition
      exact Finset.single_le_sum (f := fun j : ℕ ↦ Real.exp (l * (j : ℝ) + windowFiniteScore alpha j)) (fun _ _ ↦ (Real.exp_pos _).le) hi
    have hlog := Real.log_le_log (Real.exp_pos _) hsub
    rw [Real.log_exp] at hlog
    linarith [hscore_lo i hi]
  have hmin_mem : m + 1 ∈ Finset.Icc (m + 1) (m + M) := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hmax_mem : m + M ∈ Finset.Icc (m + 1) (m + M) := Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
  have hm1_le2 : ((m + 1 : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (show m + 1 ≤ 2 by omega)
  have hmM_ge7 : (7 : ℝ) ≤ ((m + M : ℕ) : ℝ) := by exact_mod_cast (show 7 ≤ m + M by omega)
  have hM1 : 4 * (U + B_score) ≤ M_tilt := (le_max_left _ _).trans (le_max_right 0 _)
  have hM2 : U + B_score ≤ M_tilt := (le_max_right _ _).trans (le_max_right 0 _)
  have habs : |l| ≤ M_tilt := by
    rcases le_total l 0 with hl0 | hl0
    · rw [abs_of_nonpos hl0]
      have ht := hterm_le (m + 1) hmin_mem
      have hgap : (1 / 4 : ℝ) ≤ T - ((m + 1 : ℕ) : ℝ) := by linarith [hT.1]
      have hm : (-l) * (1 / 4 : ℝ) ≤ (-l) * (T - ((m + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hgap (by linarith)
      have hsum : (-l) * (T - ((m + 1 : ℕ) : ℝ)) ≤ U + B_score := by linarith
      linarith
    · rw [abs_of_nonneg hl0]
      have ht := hterm_le (m + M) hmax_mem
      have hgap : (1 : ℝ) ≤ ((m + M : ℕ) : ℝ) - T := by linarith [hT.2]
      have hm : l * 1 ≤ l * (((m + M : ℕ) : ℝ) - T) :=
        mul_le_mul_of_nonneg_left hgap hl0
      have hsum : l * (((m + M : ℕ) : ℝ) - T) ≤ U + B_score := by linarith
      linarith
  refine ⟨habs, ?_⟩
  have ht := hterm_le (m + 1) hmin_mem
  have hdiff_abs : |((m + 1 : ℕ) : ℝ) - (alpha : ℝ)| ≤ (alpha : ℝ) + 2 := by
    rw [abs_le]
    have : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    exact ⟨by linarith, by linarith⟩
  have hprod_abs : |l * (((m + 1 : ℕ) : ℝ) - (alpha : ℝ))| ≤ M_tilt * ((alpha : ℝ) + 2) := by
    rw [abs_mul]
    exact mul_le_mul habs hdiff_abs (abs_nonneg _) (le_max_left 0 _)
  have hlo_prod : -(M_tilt * ((alpha : ℝ) + 2)) ≤ l * (((m + 1 : ℕ) : ℝ) - (alpha : ℝ)) :=
    (abs_le.mp hprod_abs).1
  linarith

private theorem binEntropy_bounds_Icc {theta : ℝ} (htheta : theta ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ binEntropy theta ∧ binEntropy theta ≤ 1 := by
  unfold binEntropy
  rcases eq_or_lt_of_le htheta.1 with rfl | hpos
  · simp
  · rcases eq_or_lt_of_le htheta.2 with rfl | hlt1
    · simp
    · have h1m_pos : 0 < 1 - theta := sub_pos.mpr hlt1
      have hlog_th : Real.log theta ≤ 0 := Real.log_nonpos hpos.le hlt1.le
      have hlog_1m : Real.log (1 - theta) ≤ 0 := Real.log_nonpos h1m_pos.le (by linarith)
      have hnn : 0 ≤ -theta * Real.log theta - (1 - theta) * Real.log (1 - theta) := by
        nlinarith
      have hinv1 : -theta * Real.log theta ≤ 1 - theta := by
        have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
        rw [Real.log_inv] at h
        have hm := mul_le_mul_of_nonneg_left h hpos.le
        have hc : theta * (theta⁻¹ - 1) = 1 - theta := by field_simp [hpos.ne']
        linarith
      have hinv2 : -(1 - theta) * Real.log (1 - theta) ≤ theta := by
        have h := Real.log_le_sub_one_of_pos (inv_pos.mpr h1m_pos)
        rw [Real.log_inv] at h
        have hm := mul_le_mul_of_nonneg_left h h1m_pos.le
        have hc : (1 - theta) * ((1 - theta)⁻¹ - 1) = theta := by field_simp [h1m_pos.ne']; ring
        linarith
      exact ⟨hnn, by linarith⟩

private theorem hasDerivAt_branchObjective_v11 (c m : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun x : ℝ ↦ c + x - x * Real.log x + m * x) (-Real.log s + m) s := by
  have hTotal := (((hasDerivAt_const s c).add (hasDerivAt_id s)).sub
    ((hasDerivAt_id s).mul (Real.hasDerivAt_log hs.ne'))).add
    ((hasDerivAt_id s).const_mul m)
  have hObj := hTotal.congr_of_eventuallyEq
    (f₁ := fun x : ℝ ↦ c + x - x * Real.log x + m * x)
    (Filter.Eventually.of_forall fun x ↦ by
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id_eq])
  apply hObj.congr_deriv
  dsimp only [id_eq]
  rw [mul_inv_cancel₀ hs.ne']
  ring

private theorem eventually_corridor_inv_target_logLogRate (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      PhaseDomain n ∧
      (∀ s ∈ Set.Icc
          (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n),
        phaseRootCenter n / 2 ≤ s ∧ s ≤ 2 * phaseRootCenter n ∧
        |(n : ℝ) / s - phaseRootS0 n| ≤ 2 * C * logLogOrder n / logOrder n ∧
        |fourSizeTarget n (phaseNat n) s - phaseTarget (phaseDelta n)| ≤
          2 * C * logLogOrder n / logOrder n) := by
  have hLLC : ∀ᶠ n : ℕ in atTop,
      ‖logLogOrder n‖ ≤ (1 / (64 * (1 + C))) * ‖logOrder n‖ :=
    logLogOrder_isLittleO_logOrder.bound (by positivity)
  have hLogPos : ∀ᶠ n : ℕ in atTop, 1 ≤ logOrder n :=
    tendsto_logOrder_atTop.eventually_ge_atTop 1
  have hLLPos : ∀ᶠ n : ℕ in atTop, 0 ≤ logLogOrder n :=
    (tendsto_logLogOrder_atTop.eventually_gt_atTop 0).mono fun _ h ↦ h.le
  filter_upwards [hLLC, hLogPos, hLLPos,
    eventually_phaseRoot_domain_pos_and_target_corridor,
    eventually_five_lt_phaseNat,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with
    n hllc hL1 hllnn hcenterDom hfive hphase
  obtain ⟨hdom, hs0Pos, _⟩ := hcenterDom
  refine ⟨hdom, fun s hs ↦ ?_⟩
  set c : ℝ := phaseRootCenter n
  set a : ℝ := (phaseNat n : ℝ)
  set s0 : ℝ := phaseRootS0 n
  have hnPos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_trans Nat.zero_lt_one hdom.1)
  have hcPos : 0 < c := div_pos hnPos hs0Pos
  have haSix : (6 : ℝ) ≤ a := by
    change (6 : ℝ) ≤ (phaseNat n : ℝ); exact_mod_cast (Nat.succ_le_of_lt hfive)
  have haPos : 0 < a := by linarith
  have haSqPos : 0 < a ^ 2 := sq_pos_of_pos haPos
  have hLPos : 0 < logOrder n := lt_of_lt_of_le zero_lt_one hL1
  rw [Real.norm_eq_abs, abs_of_nonneg hllnn, Real.norm_eq_abs, abs_of_pos hLPos] at hllc
  have hDeltaHalf : C * logLogOrder n * phaseRootGapRadius n ≤ c / 2 := by
    have h1 : C * logLogOrder n ≤ (1 + C) * logLogOrder n :=
      mul_le_mul_of_nonneg_right (by linarith) hllnn
    have h2 : (1 + C) * logLogOrder n ≤ logOrder n / 64 := by
      have hm := mul_le_mul_of_nonneg_left hllc (by linarith : (0 : ℝ) ≤ 1 + C)
      have hs' : (1 + C) * (1 / (64 * (1 + C)) * logOrder n) = logOrder n / 64 := by field_simp
      linarith
    have h3 : C * logLogOrder n ≤ a / 64 := h1.trans (h2.trans (by linarith [hphase.1]))
    have hfrac : C * logLogOrder n / a ^ 2 ≤ 1 / 2 := by
      rw [div_le_iff₀ haSqPos]
      have haa2 : a ≤ a ^ 2 := by nlinarith
      linarith
    have hrew : C * logLogOrder n * phaseRootGapRadius n = c * (C * logLogOrder n / a ^ 2) := by
      dsimp [c, a]; unfold phaseRootGapRadius; ring
    rw [hrew]
    exact (mul_le_mul_of_nonneg_left hfrac hcPos.le).trans_eq (by ring)
  have hs_lo : c / 2 ≤ s := by linarith [hs.1, hDeltaHalf]
  have hs_hi : s ≤ 2 * c := by linarith [hs.2, hDeltaHalf, hcPos]
  have hs_pos : 0 < s := by linarith [hs_lo, hcPos]
  have hs0_le_a : s0 ≤ a := by
    dsimp [s0, a]
    rw [phaseRootS0, alphaZero_eq_phaseNat_add_delta hdom]
    have h2q : (1 : ℝ) < 2 / q := by
      rw [lt_div_iff₀ q_pos]; unfold q; linarith [Real.log_two_lt_d9]
    linarith [phaseDelta_lt_one n]
  have hnc : (n : ℝ) = c * s0 := by
    dsimp [c, s0]; unfold phaseRootCenter; exact (div_mul_cancel₀ _ hs0Pos.ne').symm
  have hdiff_s0 : (n : ℝ) / s - s0 = s0 * (c - s) / s := by
    rw [hnc]; field_simp [hs_pos.ne']
  have habs_cs : |c - s| ≤ C * logLogOrder n * (c / a ^ 2) := by
    rw [abs_sub_comm, abs_le]
    have hgap : phaseRootGapRadius n = c / a ^ 2 := rfl
    rw [hgap] at hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hbound_s0 : |(n : ℝ) / s - s0| ≤ 2 * C * logLogOrder n / logOrder n := by
    rw [hdiff_s0, abs_div, abs_mul, abs_of_pos hs0Pos, abs_of_pos hs_pos]
    calc s0 * |c - s| / s
        ≤ s0 * (C * logLogOrder n * (c / a ^ 2)) / (c / 2) := by
          exact div_le_div₀ (by positivity)
            (mul_le_mul_of_nonneg_left habs_cs hs0Pos.le) (half_pos hcPos) hs_lo
      _ = 2 * C * logLogOrder n * (s0 / a) / a := by
          field_simp [hcPos.ne', haPos.ne']
      _ ≤ 2 * C * logLogOrder n * 1 / a := by
          apply div_le_div_of_nonneg_right _ haPos.le
          exact mul_le_mul_of_nonneg_left ((div_le_one haPos).mpr hs0_le_a) (by positivity)
      _ = 2 * C * logLogOrder n / a := by ring
      _ ≤ 2 * C * logLogOrder n / logOrder n :=
          div_le_div_of_nonneg_left (by positivity) hLPos hphase.1
  have htarget_eq : fourSizeTarget n (phaseNat n) s - phaseTarget (phaseDelta n) =
      s0 - (n : ℝ) / s := by
    dsimp [s0]
    unfold fourSizeTarget phaseTarget phaseRootS0 q
    rw [alphaZero_eq_phaseNat_add_delta hdom]
    ring
  refine ⟨hs_lo, hs_hi, hbound_s0, ?_⟩
  rw [htarget_eq, abs_sub_comm]
  exact hbound_s0

private theorem eventually_windowPhaseObjective_strictMonoOn_logLogCorridor
    {M : ℕ} (hM : 7 ≤ M) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      ∀ m : ℕ, m ≤ 1 →
        ∀ tau ∈ Set.Icc (0 : ℝ) (Real.log 2),
          StrictMonoOn (windowPhaseObjective m M n tau)
            (Set.Icc (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
                     (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n)) := by
  obtain ⟨K, hKnn, hKlog⟩ := eventually_corridor_abs_log_linear C hC
  set Uent : ℝ := |Real.log (partitionFn Splus 0)| + 1
  set B_sc : ℝ := 2 * ((1 + M : ℕ) : ℝ) ^ 2 + 1
  set Ml : ℝ := max 0 (max (4 * (Uent + B_sc)) (Uent + B_sc))
  have hMlnn : 0 ≤ Ml := le_max_left 0 _
  let C0 : ℝ := Real.log 2 + 5 + 2 * Ml + B_sc
  let C1 : ℝ := K + Ml
  have hC0pos : 0 < C0 := by have := Real.log_pos one_lt_two; dsimp [C0, B_sc]; positivity
  have hC1nn : 0 ≤ C1 := add_nonneg hKnn hMlnn
  have hphaseM : ∀ᶠ n : ℕ in atTop, 2 * (1 + M) ≤ phaseNat n := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop ((2 * (1 + M) : ℕ) : ℝ),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact_mod_cast hn.trans hph.1
  have hphaseBig : ∀ᶠ n : ℕ in atTop, 4 * (C0 + C1) / q + 1 ≤ (phaseNat n : ℝ) := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop (4 * (C0 + C1) / q + 1),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact hn.trans hph.1
  filter_upwards [hKlog, hphaseM, hphaseBig,
    eventually_phaseRootLogLogCorridor_fourSize_domain C hC,
    eventually_phaseRootLogLogCorridor_fourSize_target_mem_Icc C hC,
    eventually_five_lt_phaseNat] with
    n hLogN hMle hBig hDom hTarget hfive m hm tau htau s₁ hs₁ s₂ hs₂ hlt
  set a : ℝ := (phaseNat n : ℝ)
  have haSix : (6 : ℝ) ≤ a := by
    change (6 : ℝ) ≤ (phaseNat n : ℝ); exact_mod_cast (Nat.succ_le_of_lt hfive)
  have haPos : 0 < a := by linarith
  have haSqPos : 0 < a ^ 2 := sq_pos_of_pos haPos
  have halpha_mM : 2 * (m + M) ≤ phaseNat n := by omega
  have hs₁pos : 0 < s₁ := (hDom s₁ hs₁).1
  have hs₂pos : 0 < s₂ := (hDom s₂ hs₂).1
  set T₁ : ℝ := fourSizeTarget n (phaseNat n) s₁
  set T₂ : ℝ := fourSizeTarget n (phaseNat n) s₂
  have hTK₁ : T₁ ∈ Set.Icc (9 / 4 : ℝ) (17 / 4) := hTarget s₁ hs₁
  have hTK₂ : T₂ ∈ Set.Icc (9 / 4 : ℝ) (17 / 4) := hTarget s₂ hs₂
  have hT₁25 : T₁ ∈ Set.Ioo (2 : ℝ) 5 := ⟨by linarith [hTK₁.1], by linarith [hTK₁.2]⟩
  have hT₂25 : T₂ ∈ Set.Ioo (2 : ℝ) 5 := ⟨by linarith [hTK₂.1], by linarith [hTK₂.2]⟩
  have hent₂ : windowFiniteEntropy (phaseNat n) m M T₂ ≤ Uent - 1 := by
    have hw := (windowFiniteEntropy_bounds hm hM halpha_mM hT₂25).1.2
    have hd := (dualValue_window_bounds_on_padded hm hM T₂
      ⟨by linarith [hTK₂.1], by linarith [hTK₂.2]⟩).2
    dsimp [Uent]
    linarith [le_abs_self (Real.log (partitionFn Splus 0))]
  set δ : ℝ := min 1 ((q / 8 * a ^ 2) * (s₂ - s₁) / s₂)
  have hδpos : 0 < δ := lt_min zero_lt_one
    (div_pos (mul_pos (mul_pos (div_pos q_pos (by norm_num)) haSqPos) (sub_pos.mpr hlt)) hs₂pos)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hs₂δ : s₂ * δ ≤ (q / 8 * a ^ 2) * (s₂ - s₁) := by
    have h := mul_le_mul_of_nonneg_left (min_le_right 1 ((q / 8 * a ^ 2) * (s₂ - s₁) / s₂)) hs₂pos.le
    rwa [mul_div_cancel₀ _ hs₂pos.ne'] at h
  obtain ⟨l, hlLt⟩ := exists_lt_of_ciInf_lt
    (lt_add_of_pos_right (windowFiniteEntropy (phaseNat n) m M T₂) hδpos)
  have hlU : Real.log (windowFinitePartition (phaseNat n) m M l) - l * T₂ ≤ Uent := by linarith
  have hTK₂_wide : T₂ ∈ Set.Icc (9 / 4 : ℝ) (9 / 2) := ⟨hTK₂.1, by linarith [hTK₂.2]⟩
  have hLinLo_raw := (abs_tilt_of_windowFiniteDual_le hm hM halpha_mM hTK₂_wide hlU).2
  have hBsc_le : 2 * ((m + M : ℕ) : ℝ) ^ 2 + 1 ≤ B_sc := by
    dsimp [B_sc]
    have : ((m + M : ℕ) : ℝ) ^ 2 ≤ ((1 + M : ℕ) : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (show m + M ≤ 1 + M by omega)) 2
    linarith
  have hMl_le : max 0 (max (4 * (Uent + (2 * ((m + M : ℕ) : ℝ) ^ 2 + 1)))
      (Uent + (2 * ((m + M : ℕ) : ℝ) ^ 2 + 1))) ≤ Ml := by
    dsimp [Ml]
    exact max_le_max le_rfl (max_le_max (by linarith) (by linarith))
  have hLinLo : -Ml * (a + 2) - B_sc ≤
      Real.log (windowFinitePartition (phaseNat n) m M l) - l * a := by
    have hm_a : max 0 (max (4 * (Uent + (2 * ((m + M : ℕ) : ℝ) ^ 2 + 1)))
        (Uent + (2 * ((m + M : ℕ) : ℝ) ^ 2 + 1))) * (a + 2) ≤ Ml * (a + 2) :=
      mul_le_mul_of_nonneg_right hMl_le (by linarith)
    dsimp [a] at hm_a ⊢
    linarith
  set m_slope : ℝ := profileDeficitAffineA (phaseNat n) + profileDeficitAffineB (phaseNat n) * a +
    tau + Real.log (windowFinitePartition (phaseNat n) m M l) - l * a
  set c_const : ℝ := (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) +
    (l - profileDeficitAffineB (phaseNat n)) * (n : ℝ)
  set g : ℝ → ℝ := fun x ↦ c_const + x - x * Real.log x + m_slope * x
  have g_eq : ∀ {x : ℝ}, x ≠ 0 →
      g x = (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + x - x * Real.log x +
        x * (profileDeficitAffineA (phaseNat n) +
          profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) x +
          (Real.log (windowFinitePartition (phaseNat n) m M l) -
            l * fourSizeTarget n (phaseNat n) x) + tau) := by
    intro x hx
    have hnx : x * ((n : ℝ) / x) = (n : ℝ) := mul_div_cancel₀ _ hx
    dsimp [g, c_const, m_slope, a]
    unfold fourSizeTarget
    calc (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + (l - profileDeficitAffineB (phaseNat n)) * (n : ℝ) +
          x - x * Real.log x +
          (profileDeficitAffineA (phaseNat n) + profileDeficitAffineB (phaseNat n) * (phaseNat n : ℝ) +
            tau + Real.log (windowFinitePartition (phaseNat n) m M l) - l * (phaseNat n : ℝ)) * x
        = (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + (l - profileDeficitAffineB (phaseNat n)) * (x * ((n : ℝ) / x)) +
            x - x * Real.log x +
            (profileDeficitAffineA (phaseNat n) + profileDeficitAffineB (phaseNat n) * (phaseNat n : ℝ) +
              tau + Real.log (windowFinitePartition (phaseNat n) m M l) - l * (phaseNat n : ℝ)) * x := by
          rw [hnx]
      _ = _ := by ring
  have hAt1 : windowPhaseObjective m M n tau s₁ ≤ g s₁ := by
    rw [g_eq hs₁pos.ne']; unfold windowPhaseObjective
    have hle1 : windowFiniteEntropy (phaseNat n) m M T₁ ≤
        Real.log (windowFinitePartition (phaseNat n) m M l) - l * T₁ :=
      ciInf_le (bddBelow_windowFiniteDual hm hM halpha_mM hT₁25) l
    have hm1 := mul_le_mul_of_nonneg_left hle1 hs₁pos.le
    dsimp [T₁] at hm1; linarith
  have hAt2 : g s₂ - s₂ * δ < windowPhaseObjective m M n tau s₂ := by
    rw [g_eq hs₂pos.ne']; unfold windowPhaseObjective
    have hm2 := mul_lt_mul_of_pos_left hlLt hs₂pos
    dsimp [T₂] at hm2; linarith
  have hAff : q / 2 * a ^ 2 - 4 ≤
      profileDeficitAffineA (phaseNat n) + profileDeficitAffineB (phaseNat n) * a := by
    have hcore := (abs_le.mp (abs_profileDeficitAffineCore_sub_quadratic_le (phaseNat n) (by omega))).1
    have hfac : factorialLogErrorBound (phaseNat n) ≤ a + 4 := by
      have h := Real.log_le_sub_one_of_pos (x := ((phaseNat n + 1 : ℕ) : ℝ)) (by positivity)
      have hEq : factorialLogErrorBound (phaseNat n) = Real.log ((phaseNat n + 1 : ℕ) : ℝ) + 4 := rfl
      rw [hEq]; push_cast at h ⊢; linarith
    dsimp [a] at hfac ⊢; linarith
  have hRemLe : C0 + C1 * a ≤ q / 4 * a ^ 2 := by
    have h1 : 4 * (C0 + C1) ≤ a * q := (div_le_iff₀ q_pos).mp (by linarith [hBig])
    have h2 : C0 + C1 * a ≤ (C0 + C1) * a := by
      have hc0a : C0 ≤ C0 * a := by
        calc C0 = C0 * 1 := (mul_one C0).symm
          _ ≤ C0 * a := mul_le_mul_of_nonneg_left (by linarith) hC0pos.le
      linarith
    have h3 : 4 * (C0 + C1) * a ≤ (a * q) * a :=
      mul_le_mul_of_nonneg_right h1 haPos.le
    linarith [show 4 * ((C0 + C1) * a) = 4 * (C0 + C1) * a by ring,
      show (a * q) * a = 4 * (q / 4 * a ^ 2) by ring]
  have hSubIcc : Set.Icc s₁ s₂ ⊆ Set.Icc
      (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
      (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n) :=
    fun x hx ↦ ⟨hs₁.1.trans hx.1, hx.2.trans hs₂.2⟩
  have hHasDerivG : ∀ x ∈ Set.Icc s₁ s₂, HasDerivAt g (-Real.log x + m_slope) x :=
    fun x hx ↦ hasDerivAt_branchObjective_v11 c_const m_slope (lt_of_lt_of_le hs₁pos hx.1)
  have hContG : ContinuousOn g (Set.Icc s₁ s₂) :=
    fun x hx ↦ (hHasDerivG x hx).continuousAt.continuousWithinAt
  have hDiffG : DifferentiableOn ℝ g (Set.Ioo s₁ s₂) :=
    fun x hx ↦ (hHasDerivG x (Ioo_subset_Icc_self hx)).differentiableAt.differentiableWithinAt
  have hSlopeG : ∀ x ∈ Set.Ioo s₁ s₂, q / 4 * a ^ 2 ≤ deriv g x := by
    intro x hx
    have hxIcc := Ioo_subset_Icc_self hx
    rw [(hHasDerivG x hxIcc).deriv]
    have hlogx := (abs_le.mp (hLogN x (hSubIcc hxIcc))).2
    have hql2 : q = Real.log 2 := rfl
    dsimp [m_slope, C0, C1] at hRemLe ⊢
    linarith [htau.1, hql2]
  have hIncG := derivative_lower_bound_mul_sub_le_sub hlt.le hContG hDiffG hSlopeG
  have hPosGain : 0 < (q / 8 * a ^ 2) * (s₂ - s₁) :=
    mul_pos (mul_pos (div_pos q_pos (by norm_num)) haSqPos) (sub_pos.mpr hlt)
  linarith

/-- **Lemma 3.1 general-`M` finite-window corridor roots (`∃!`) and `(3.6)` location:**
for every `M ≥ 7`, there exist `C > 0` and `A_* > 0` such that eventually (uniformly over
`m ∈ {0, 1}` and `τ ∈ [0, log 2]`):
1. `𝓛_{S_{m,M}}(n, ·) + τ ·` is strictly increasing on `[c_n - C Δ_n, c_n + C Δ_n]`,
2. `𝓛_{S_{m,M}}(n, r) + τ r = 0` has a unique solution `r` in `(c_n - C Δ_n, c_n + C Δ_n)`,
3. that root satisfies `|n / r - s₀| ≤ A_* log log n / log n` and
   `|(α - n / r) - T_{δ_n}| ≤ A_* log log n / log n` (`(3.6)`). -/
theorem exists_pos_eventually_existsUnique_windowPhaseObjective_zero_logLogCorridor
    {M : ℕ} (hM : 7 ≤ M) :
    ∃ C A_star : ℝ, 0 < C ∧ 0 < A_star ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ m : ℕ, m ≤ 1 →
          ∀ tau ∈ Set.Icc (0 : ℝ) (Real.log 2),
            let F_fin : ℝ → ℝ := fun T ↦ ⨅ l : ℝ,
              (Real.log (∑ i ∈ Finset.Icc (m + 1) (m + M),
                  Real.exp (l * (i : ℝ) +
                    (Real.log ((phaseNat n).descFactorial i : ℝ) -
                      (i : ℝ) * Real.log (phaseNat n : ℝ) -
                      Real.log 2 / 2 * (i : ℝ) ^ 2))) - l * T)
            let obj : ℝ → ℝ := fun s ↦
              (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + s - s * Real.log s +
                s * (profileDeficitAffineA (phaseNat n) +
                  profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s +
                  F_fin (fourSizeTarget n (phaseNat n) s) + tau)
            StrictMonoOn obj
                (Set.Icc (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
                         (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n)) ∧
              (∃! r : ℝ,
                r ∈ Set.Ioo (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
                            (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n) ∧
                  obj r = 0) ∧
              (∀ r ∈ Set.Ioo (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
                             (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n),
                obj r = 0 →
                  |(n : ℝ) / r - phaseRootS0 n| ≤ A_star * logLogOrder n / logOrder n ∧
                    |fourSizeTarget n (phaseNat n) r - phaseTarget (phaseDelta n)| ≤
                      A_star * logLogOrder n / logOrder n) := by
  obtain ⟨B, hBpos, hB⟩ :=
    unrestrictedPhaseObjective_center_div_isBigO_logLogOrder.exists_pos
  obtain ⟨Mtilt, hMtiltnn, huniformTilt⟩ :=
    exists_eventually_forall_mem_Icc_abs_profileDeficitTilt_le
      (by norm_num : (-1 : ℝ) < 9 / 4) (by norm_num : (9 / 4 : ℝ) ≤ 17 / 4)
  obtain ⟨Ntilt, hNtilt⟩ := eventually_atTop.1 huniformTilt
  let C : ℝ := 16 * (B + 2) / q
  have hCpos : 0 < C := div_pos (mul_pos (by norm_num) (by linarith)) q_pos
  refine ⟨C, 2 * C, hCpos, by positivity, ?_⟩
  let Gbound : ℝ := Real.log 2 + 5 * Mtilt + 2 * |Real.log (partitionFn Splus 0)| +
    |min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))| + ((1 + M : ℕ) : ℝ) ^ 2 + 2
  have hLLBig : ∀ᶠ n : ℕ in atTop, max 1 (2 * Gbound + 1) ≤ logLogOrder n :=
    tendsto_logLogOrder_atTop.eventually_ge_atTop _
  have hphaseN : ∀ᶠ n : ℕ in atTop, max Ntilt (2 * (1 + M)) ≤ phaseNat n := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop ((max Ntilt (2 * (1 + M)) : ℕ) : ℝ),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact_mod_cast hn.trans hph.1
  filter_upwards [hB.bound, hLLBig, hphaseN,
    eventually_windowPhaseObjective_strictMonoOn_logLogCorridor hM C hCpos.le,
    eventually_corridor_inv_target_logLogRate C hCpos.le,
    eventually_phaseRootLogLogCorridor_fourSize_domain C hCpos.le,
    eventually_phaseRootLogLogCorridor_fourSize_target_mem_Icc C hCpos.le,
    eventually_unrestrictedPhaseObjective_deriv_logLogCorridor_lower C hCpos.le,
    eventually_phaseRoot_domain_pos_and_target_corridor,
    eventually_five_lt_phaseNat] with
    n hcenterBound hLL hphN hStrict hInvRate hdomain htarget hderiv hcenterDom hfive m hm tau htau
  intro F_fin obj
  have hobj_eq : obj = windowPhaseObjective m M n tau := rfl
  rw [hobj_eq]
  clear hobj_eq obj F_fin
  set s0 : ℝ := phaseRootCenter n
  set a : ℝ := (phaseNat n : ℝ)
  set Delta : ℝ := C * logLogOrder n * phaseRootGapRadius n
  have hLL1 : 1 ≤ logLogOrder n := (le_max_left _ _).trans hLL
  have hLLG : 2 * Gbound + 1 ≤ logLogOrder n := (le_max_right _ _).trans hLL
  have hLLPos : 0 < logLogOrder n := lt_of_lt_of_le zero_lt_one hLL1
  have hs0Pos : 0 < s0 :=
    div_pos (by exact_mod_cast (lt_trans Nat.zero_lt_one hcenterDom.1.1)) hcenterDom.2.1
  have haPos : 0 < a := Nat.cast_pos.mpr (lt_trans (by omega : 0 < 5) hfive)
  have haSqPos : 0 < a ^ 2 := sq_pos_of_pos haPos
  have hDeltaPos : 0 < Delta := mul_pos (mul_pos hCpos hLLPos) (div_pos hs0Pos haSqPos)
  have halpha_mM : 2 * (m + M) ≤ phaseNat n := by
    have := (le_max_right Ntilt (2 * (1 + M))).trans hphN; omega
  have hCont : ContinuousOn (windowPhaseObjective m M n tau) (Set.Icc (s0 - Delta) (s0 + Delta)) := by
    have hPosOn : ∀ s ∈ Set.Icc (s0 - Delta) (s0 + Delta), s ≠ 0 := by
      intro s hs
      linarith [(hInvRate.2 s hs).1, hs0Pos]
    have hTargetCont : ContinuousOn (fourSizeTarget n (phaseNat n))
        (Set.Icc (s0 - Delta) (s0 + Delta)) := by
      unfold fourSizeTarget
      exact continuousOn_const.sub (continuousOn_const.div continuousOn_id hPosOn)
    have hMaps : MapsTo (fourSizeTarget n (phaseNat n))
        (Set.Icc (s0 - Delta) (s0 + Delta)) (Set.Icc (9 / 4 : ℝ) (9 / 2)) := by
      intro s hs
      have ht := htarget s (by simpa [s0, Delta] using hs)
      exact ⟨ht.1, by linarith [ht.2]⟩
    have hEntCont := (continuousOn_windowFiniteEntropy_Icc hm hM halpha_mM).comp hTargetCont hMaps
    unfold windowPhaseObjective
    exact (((continuousOn_const.add continuousOn_id).sub
      (continuousOn_id.mul (continuousOn_id.log hPosOn))).add
      (continuousOn_id.mul (((continuousOn_const.add
        (continuousOn_const.mul hTargetCont)).add hEntCont).add continuousOn_const)))
  have hShiftBound : ∀ s ∈ Set.Icc (s0 - Delta) (s0 + Delta),
      |s * (tau - finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) s) +
          windowFiniteEntropy (phaseNat n) m M (fourSizeTarget n (phaseNat n) s))| ≤
        logLogOrder n * s0 := by
    intro s hs
    have hsPos : 0 < s := by linarith [(hInvRate.2 s hs).1, hs0Pos]
    have hsLe2 : s ≤ 2 * s0 := (hInvRate.2 s hs).2.1
    set T : ℝ := fourSizeTarget n (phaseNat n) s
    have hTK : T ∈ Set.Icc (9 / 4 : ℝ) (17 / 4) := htarget s (by simpa [s0, Delta] using hs)
    have hT25 : T ∈ Set.Ioo (2 : ℝ) 5 := ⟨by linarith [hTK.1], by linarith [hTK.2]⟩
    have hUnrestHi : finiteUnrestrictedDeficitEntropy (phaseNat n) T ≤
        |Real.log (partitionFn Splus 0)| := by
      have h1 := (finiteProfileDeficitEntropy_le_extendedGaussianEntropyValue
        (phaseNat n) hfive hT25).trans (extendedGaussianEntropyValue_le_dualValue_Splus hT25)
      have hm4 := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT25)
      have h2 := dualValue_le_at S4_subset_Splus hm4 0
      unfold finiteUnrestrictedDeficitEntropy
      linarith [le_abs_self (Real.log (partitionFn Splus 0))]
    have hUnrestLo : -(5 * Mtilt) ≤ finiteUnrestrictedDeficitEntropy (phaseNat n) T := by
      obtain ⟨_, htiltB⟩ := hNtilt (phaseNat n) ((le_max_left _ _).trans hphN) T hTK
      have hp1 := one_le_profileDeficitPartition (phaseNat n) (by omega)
        (profileDeficitTilt (phaseNat n) T)
      have hlognn := Real.log_nonneg hp1
      have hmul : |profileDeficitTilt (phaseNat n) T * T| ≤ 5 * Mtilt := by
        rw [abs_mul, abs_of_pos (by linarith [hTK.1] : 0 < T)]
        have := mul_le_mul htiltB (show T ≤ 5 by linarith [hTK.2]) (by linarith [hTK.1]) hMtiltnn
        linarith
      unfold finiteUnrestrictedDeficitEntropy
      linarith [(abs_le.mp hmul).2]
    have hw_err := (windowFiniteEntropy_bounds hm hM halpha_mM hT25).1
    have hd_bds := dualValue_window_bounds_on_padded hm hM T
      ⟨by linarith [hTK.1], by linarith [hTK.2]⟩
    have herr_le : ((m + M : ℕ) : ℝ) ^ 2 / a ≤ ((1 + M : ℕ) : ℝ) ^ 2 := by
      have hsq : ((m + M : ℕ) : ℝ) ^ 2 ≤ ((1 + M : ℕ) : ℝ) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (show m + M ≤ 1 + M by omega)) 2
      have ha1 : 1 ≤ a := by dsimp [a]; exact_mod_cast (show 1 ≤ phaseNat n by omega)
      calc ((m + M : ℕ) : ℝ) ^ 2 / a ≤ ((m + M : ℕ) : ℝ) ^ 2 / 1 :=
            div_le_div_of_nonneg_left (sq_nonneg _) zero_lt_one ha1
        _ ≤ ((1 + M : ℕ) : ℝ) ^ 2 := by linarith
    have hInnerAbs :
        |tau - finiteUnrestrictedDeficitEntropy (phaseNat n) T +
          windowFiniteEntropy (phaseNat n) m M T| ≤ Gbound := by
      rw [abs_le]
      dsimp [Gbound]
      dsimp [a] at herr_le
      exact ⟨by linarith [htau.1, hUnrestHi, hw_err.1, hd_bds.1, herr_le, hMtiltnn,
          Real.log_pos one_lt_two,
          abs_nonneg (Real.log (partitionFn Splus 0)),
          neg_abs_le (min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8)))],
        by linarith [htau.2, hUnrestLo, hw_err.2, hd_bds.2,
          le_abs_self (Real.log (partitionFn Splus 0)),
          abs_nonneg (Real.log (partitionFn Splus 0)),
          abs_nonneg (min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))),
          sq_nonneg ((1 + M : ℕ) : ℝ)]⟩
    rw [abs_mul, abs_of_pos hsPos]
    calc s * |tau - finiteUnrestrictedDeficitEntropy (phaseNat n) T +
            windowFiniteEntropy (phaseNat n) m M T|
        ≤ (2 * s0) * Gbound :=
          mul_le_mul hsLe2 hInnerAbs (abs_nonneg _) (mul_pos two_pos hs0Pos).le
      _ ≤ logLogOrder n * s0 := by
          have := mul_le_mul_of_nonneg_right hLLG hs0Pos.le
          linarith
  have hDiffId : ∀ {s : ℝ}, s ≠ 0 →
      windowPhaseObjective m M n tau s =
        unrestrictedPhaseObjective n s +
          s * (tau - finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) s) +
            windowFiniteEntropy (phaseNat n) m M (fourSizeTarget n (phaseNat n) s)) := by
    intro s hsNe
    have hu := unrestrictedPhaseObjective_div_eq_deficitCentered n hsNe
    have huMul : unrestrictedPhaseObjective n s =
        s * ((n : ℝ) * Real.log (n : ℝ) / s - (n : ℝ) / s + 1 - Real.log s +
          (profileDeficitAffineA (phaseNat n) +
            profileDeficitAffineB (phaseNat n) * profileDeficitTarget (phaseNat n) (n : ℝ) s +
            finiteUnrestrictedDeficitEntropy (phaseNat n)
              (profileDeficitTarget (phaseNat n) (n : ℝ) s))) := by
      rw [div_eq_iff hsNe] at hu
      unfold finiteUnrestrictedDeficitEntropy
      linarith
    rw [huMul]
    unfold windowPhaseObjective fourSizeTarget profileDeficitTarget
    field_simp [hsNe]
    ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hLLPos] at hcenterBound
  have hCenterAbs : |unrestrictedPhaseObjective n s0| ≤ B * logLogOrder n * s0 := by
    have hm_c := mul_le_mul_of_nonneg_right hcenterBound hs0Pos.le
    rwa [abs_div, abs_of_pos hs0Pos, div_mul_cancel₀ _ hs0Pos.ne'] at hm_c
  have ha_ge6 : (6 : ℝ) ≤ (phaseNat n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hfive)
  have hKeyU : ∀ x ∈ Set.Icc (s0 - Delta) (s0 + Delta),
      HasDerivAt (unrestrictedPhaseObjective n)
        (Real.log (profileDualPartition (phaseNat n + 1)
            (profileDualTilt (phaseNat n + 1) ((n : ℝ) / x))) - Real.log x) x := by
    intro x hx
    obtain ⟨hxpos, htar⟩ := hdomain x (by simpa [s0, Delta] using hx)
    rw [fourSizeTarget, Set.mem_Ioo] at htar
    exact hasDerivAt_profileDualOptimalValue_parts (by omega) hxpos (by
      rw [Set.mem_Ioo, show (((phaseNat n + 1 : ℕ) : ℝ)) = (phaseNat n : ℝ) + 1 by push_cast; ring]
      exact ⟨by linarith [htar.2, ha_ge6], by linarith [htar.1]⟩)
  have hContU : ContinuousOn (unrestrictedPhaseObjective n) (Set.Icc (s0 - Delta) (s0 + Delta)) :=
    fun x hx ↦ (hKeyU x hx).continuousAt.continuousWithinAt
  have hDiffU : DifferentiableOn ℝ (unrestrictedPhaseObjective n)
      (Set.Ioo (s0 - Delta) (s0 + Delta)) :=
    fun x hx ↦ (hKeyU x (Ioo_subset_Icc_self hx)).differentiableAt.differentiableWithinAt
  have hDerivLo : ∀ x ∈ Set.Ioo (s0 - Delta) (s0 + Delta),
      q / 8 * a ^ 2 ≤ deriv (unrestrictedPhaseObjective n) x :=
    fun x hx ↦ hderiv x (Ioo_subset_Icc_self (by simpa [s0, Delta] using hx))
  have hProdSlope : (q / 8 * a ^ 2) * Delta = 2 * (B + 2) * logLogOrder n * s0 := by
    dsimp [Delta, C, s0, a]; unfold phaseRootGapRadius
    field_simp [q_ne_zero, haPos.ne']; ring
  have hLeftInc := derivative_lower_bound_mul_sub_le_sub
    (show s0 - Delta ≤ s0 by linarith)
    (hContU.mono fun x hx ↦ ⟨hx.1, hx.2.trans (by linarith)⟩)
    (hDiffU.mono fun x hx ↦ ⟨hx.1, lt_of_lt_of_le hx.2 (by linarith)⟩)
    (fun x hx ↦ hDerivLo x ⟨hx.1, lt_of_lt_of_le hx.2 (by linarith)⟩)
  have hRightInc := derivative_lower_bound_mul_sub_le_sub
    (show s0 ≤ s0 + Delta by linarith)
    (hContU.mono fun x hx ↦ ⟨(by linarith : s0 - Delta ≤ s0).trans hx.1, hx.2⟩)
    (hDiffU.mono fun x hx ↦ ⟨lt_of_le_of_lt (by linarith) hx.1, hx.2⟩)
    (fun x hx ↦ hDerivLo x ⟨lt_of_le_of_lt (by linarith) hx.1, hx.2⟩)
  rw [show s0 - (s0 - Delta) = Delta by ring, hProdSlope] at hLeftInc
  rw [show s0 + Delta - s0 = Delta by ring, hProdSlope] at hRightInc
  have hexp_slope :
      2 * (B + 2) * logLogOrder n * s0 =
        2 * (B * logLogOrder n * s0) + 4 * (logLogOrder n * s0) := by ring
  have hB_pos_ll : 0 < B * logLogOrder n * s0 := mul_pos (mul_pos hBpos hLLPos) hs0Pos
  have hNegLeft : windowPhaseObjective m M n tau (s0 - Delta) < 0 := by
    have hsL_mem : s0 - Delta ∈ Set.Icc (s0 - Delta) (s0 + Delta) := ⟨le_rfl, by linarith⟩
    have hsL_pos : 0 < s0 - Delta := by linarith [(hInvRate.2 _ hsL_mem).1, hs0Pos]
    rw [hDiffId hsL_pos.ne']
    have hsh := (abs_le.mp (hShiftBound (s0 - Delta) hsL_mem)).2
    have hc_hi := (abs_le.mp hCenterAbs).2
    have hpos_ll : 0 < logLogOrder n * s0 := mul_pos hLLPos hs0Pos
    linarith
  have hPosRight : 0 < windowPhaseObjective m M n tau (s0 + Delta) := by
    have hsR_mem : s0 + Delta ∈ Set.Icc (s0 - Delta) (s0 + Delta) := ⟨by linarith, le_rfl⟩
    have hsR_pos : 0 < s0 + Delta := by linarith
    rw [hDiffId hsR_pos.ne']
    have hsh := (abs_le.mp (hShiftBound (s0 + Delta) hsR_mem)).1
    have hc_lo := (abs_le.mp hCenterAbs).1
    have hpos_ll : 0 < logLogOrder n * s0 := mul_pos hLLPos hs0Pos
    linarith
  have hStrict_n := hStrict m hm tau htau
  refine ⟨hStrict_n, ?_, ?_⟩
  · have hivt : (0 : ℝ) ∈ windowPhaseObjective m M n tau '' Set.Icc (s0 - Delta) (s0 + Delta) :=
      intermediate_value_Icc (by linarith) hCont ⟨hNegLeft.le, hPosRight.le⟩
    rcases hivt with ⟨r, hr_icc, hr_zero⟩
    have hr_gt : s0 - Delta < r := lt_of_le_of_ne hr_icc.1 fun heq ↦ by
      rw [← heq] at hr_zero; linarith
    have hr_lt : r < s0 + Delta := lt_of_le_of_ne hr_icc.2 fun heq ↦ by
      rw [heq] at hr_zero; linarith
    refine ⟨r, ⟨⟨hr_gt, hr_lt⟩, hr_zero⟩, fun y ⟨hy_ioo, hy_zero⟩ ↦ ?_⟩
    exact hStrict_n.injOn (Ioo_subset_Icc_self hy_ioo) hr_icc (hy_zero.trans hr_zero.symm)
  · intro r hr_ioo _
    have hi := hInvRate.2 r (Ioo_subset_Icc_self hr_ioo)
    exact ⟨hi.2.2.1, hi.2.2.2⟩

private theorem eventually_cappedWindow_target_mem_KcapInterval (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      phaseDelta n ∈ Set.Icc (0 : ℝ) deltaStar →
        ∀ s ∈ Set.Icc
            (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
            (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n),
          fourSizeTarget n (phaseNat n) s ∈ KcapInterval := by
  have hsmall : ∀ᶠ n : ℕ in atTop, 2 * C * logLogOrder n / logOrder n ≤ 1 / 20 := by
    have h1 : ∀ᶠ n : ℕ in atTop,
        ‖logLogOrder n‖ ≤ (1 / (40 * (C + 1))) * ‖logOrder n‖ :=
      logLogOrder_isLittleO_logOrder.bound (by positivity)
    have hL1 : ∀ᶠ n : ℕ in atTop, 1 ≤ logOrder n := tendsto_logOrder_atTop.eventually_ge_atTop 1
    have hll0 : ∀ᶠ n : ℕ in atTop, 0 ≤ logLogOrder n :=
      (tendsto_logLogOrder_atTop.eventually_gt_atTop 0).mono fun _ h ↦ h.le
    filter_upwards [h1, hL1, hll0] with n hn hL hll
    have hLpos : 0 < logOrder n := lt_of_lt_of_le zero_lt_one hL
    rw [Real.norm_eq_abs, abs_of_nonneg hll, Real.norm_eq_abs, abs_of_pos hLpos] at hn
    rw [div_le_iff₀ hLpos]
    have hm := mul_le_mul_of_nonneg_left hn (show (0 : ℝ) ≤ 2 * (C + 1) by positivity)
    have hs : 2 * (C + 1) * (1 / (40 * (C + 1)) * logOrder n) = 1 / 20 * logOrder n := by
      field_simp; ring
    have hc : 2 * C * logLogOrder n ≤ 2 * (C + 1) * logLogOrder n :=
      mul_le_mul_of_nonneg_right (by linarith) hll
    linarith
  filter_upwards [hsmall, eventually_corridor_inv_target_logLogRate C hC] with
    n hsm hInv hd s hs
  have htar := (hInv.2 s hs).2.2.2
  rw [abs_le] at htar
  unfold phaseTarget at htar
  unfold KcapInterval
  unfold deltaStar at hd
  exact ⟨by linarith [htar.1, hd.2, hsm], by linarith [htar.2, hd.1, hsm]⟩

private theorem eventually_cappedWindowPhaseObjective_strictMonoOn_logLogCorridor
    {M : ℕ} (hM : 8 ≤ M) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      phaseDelta n ∈ Set.Icc (0 : ℝ) deltaStar →
        ∀ theta ∈ Set.Icc (0 : ℝ) (1 / 20),
          ∀ tau ∈ Set.Icc (0 : ℝ) (Real.log 2),
            StrictMonoOn (cappedWindowPhaseObjective M n theta tau)
              (Set.Icc (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
                       (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n)) := by
  obtain ⟨K, hKnn, hKlog⟩ := eventually_corridor_abs_log_linear C hC
  set Uent : ℝ := |Real.log (partitionFn Splus 0)| + 2
  set B_sc : ℝ := 2 * (M : ℝ) ^ 2 + 1
  set Ml : ℝ := max 0 (max (4 * (Uent + B_sc)) (Uent + B_sc))
  have hMlnn : 0 ≤ Ml := le_max_left 0 _
  let C0 : ℝ := 2 * Real.log 2 + 5 + 2 * Ml + B_sc
  let C1 : ℝ := K + 2 * Ml
  have hC0pos : 0 < C0 := by have := Real.log_pos one_lt_two; dsimp [C0, B_sc]; positivity
  have hC1nn : 0 ≤ C1 := by positivity
  have hphaseM : ∀ᶠ n : ℕ in atTop, 2 * M ≤ phaseNat n := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop ((2 * M : ℕ) : ℝ),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact_mod_cast hn.trans hph.1
  have hphaseBig : ∀ᶠ n : ℕ in atTop, 4 * (C0 + C1) / q + 1 ≤ (phaseNat n : ℝ) := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop (4 * (C0 + C1) / q + 1),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact hn.trans hph.1
  filter_upwards [hKlog, hphaseM, hphaseBig,
    eventually_phaseRootLogLogCorridor_fourSize_domain C hC,
    eventually_cappedWindow_target_mem_KcapInterval C hC,
    eventually_five_lt_phaseNat] with
    n hLogN hMle hBig hDom hKcap hfive hd theta htheta tau htau s₁ hs₁ s₂ hs₂ hlt
  set a : ℝ := (phaseNat n : ℝ)
  have haSix : (6 : ℝ) ≤ a := by
    change (6 : ℝ) ≤ (phaseNat n : ℝ); exact_mod_cast (Nat.succ_le_of_lt hfive)
  have haPos : 0 < a := by linarith
  have haSqPos : 0 < a ^ 2 := sq_pos_of_pos haPos
  have hM_eq : 1 + (M - 1) = M := by omega
  have halpha_cap : 2 * (1 + (M - 1)) ≤ phaseNat n := by omega
  have hs₁pos : 0 < s₁ := (hDom s₁ hs₁).1
  have hs₂pos : 0 < s₂ := (hDom s₂ hs₂).1
  have h1m_pos : 0 < 1 - theta := by linarith [htheta.2]
  have h1m_le1 : 1 - theta ≤ 1 := by linarith [htheta.1]
  set T₁ : ℝ := fourSizeTarget n (phaseNat n) s₁
  set T₂ : ℝ := fourSizeTarget n (phaseNat n) s₂
  have hTK₁ : T₁ ∈ KcapInterval := hKcap hd s₁ hs₁
  have hTK₂ : T₂ ∈ KcapInterval := hKcap hd s₂ hs₂
  set u₁ : ℝ := (T₁ - theta) / (1 - theta)
  set u₂ : ℝ := (T₂ - theta) / (1 - theta)
  obtain ⟨hu₁_icc, hu₁_ioo⟩ := reducedTarget_mem_Icc_and_Ioo htheta hTK₁
  obtain ⟨hu₂_icc, hu₂_ioo⟩ := reducedTarget_mem_Icc_and_Ioo htheta hTK₂
  have hent₂ : windowFiniteEntropy (phaseNat n) 1 (M - 1) u₂ ≤ Uent - 2 := by
    have hw := (windowFiniteEntropy_bounds (m := 1) (M := M - 1)
      le_rfl (by omega) halpha_cap hu₂_ioo).1.2
    have hd_u := (dualValue_window_bounds_on_padded (m := 1) (M := M - 1)
      le_rfl (by omega) u₂ ⟨by linarith [hu₂_icc.1], by linarith [hu₂_icc.2]⟩).2
    dsimp [Uent]
    linarith [le_abs_self (Real.log (partitionFn Splus 0))]
  set δ : ℝ := min 1 ((q / 8 * a ^ 2) * (s₂ - s₁) / s₂)
  have hδpos : 0 < δ := lt_min zero_lt_one
    (div_pos (mul_pos (mul_pos (div_pos q_pos (by norm_num)) haSqPos) (sub_pos.mpr hlt)) hs₂pos)
  have hδ_div_le : δ / (1 - theta) ≤ 2 := by
    have hδ1 : δ ≤ 1 := min_le_left _ _
    rw [div_le_iff₀ h1m_pos]; linarith [htheta.2]
  have hs₂δ : s₂ * δ ≤ (q / 8 * a ^ 2) * (s₂ - s₁) := by
    have h := mul_le_mul_of_nonneg_left (min_le_right 1 ((q / 8 * a ^ 2) * (s₂ - s₁) / s₂)) hs₂pos.le
    rwa [mul_div_cancel₀ _ hs₂pos.ne'] at h
  obtain ⟨l, hlLt⟩ := exists_lt_of_ciInf_lt
    (lt_add_of_pos_right (windowFiniteEntropy (phaseNat n) 1 (M - 1) u₂) (div_pos hδpos h1m_pos))
  have hlU : Real.log (windowFinitePartition (phaseNat n) 1 (M - 1) l) - l * u₂ ≤ Uent := by
    linarith
  have hu₂_wide : u₂ ∈ Set.Icc (9 / 4 : ℝ) (9 / 2) := ⟨by linarith [hu₂_icc.1], hu₂_icc.2⟩
  obtain ⟨hl_abs, hLinLo_raw⟩ := abs_tilt_of_windowFiniteDual_le (m := 1) (M := M - 1)
    le_rfl (by omega) halpha_cap hu₂_wide hlU
  simp only [hM_eq] at hl_abs hLinLo_raw
  set m_slope : ℝ := profileDeficitAffineA (phaseNat n) + profileDeficitAffineB (phaseNat n) * a +
    tau + binEntropy theta - Real.log 2 / 2 * theta +
    (1 - theta) * Real.log (windowFinitePartition (phaseNat n) 1 (M - 1) l) - l * (a - theta)
  set c_const : ℝ := (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) +
    (l - profileDeficitAffineB (phaseNat n)) * (n : ℝ)
  set g : ℝ → ℝ := fun x ↦ c_const + x - x * Real.log x + m_slope * x
  have g_eq : ∀ {x : ℝ}, x ≠ 0 →
      g x = (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + x - x * Real.log x +
        x * (profileDeficitAffineA (phaseNat n) +
          profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) x +
          (binEntropy theta - Real.log 2 / 2 * theta +
            (1 - theta) *
              (Real.log (windowFinitePartition (phaseNat n) 1 (M - 1) l) -
                l * ((fourSizeTarget n (phaseNat n) x - theta) / (1 - theta)))) + tau) := by
    intro x hx
    dsimp [g, c_const, m_slope, a]
    unfold fourSizeTarget
    field_simp [hx, h1m_pos.ne']
    ring
  have hAt1 : cappedWindowPhaseObjective M n theta tau s₁ ≤ g s₁ := by
    rw [g_eq hs₁pos.ne']; unfold cappedWindowPhaseObjective cappedWindowFiniteEntropy
    have hle1 : windowFiniteEntropy (phaseNat n) 1 (M - 1) u₁ ≤
        Real.log (windowFinitePartition (phaseNat n) 1 (M - 1) l) - l * u₁ :=
      ciInf_le (bddBelow_windowFiniteDual le_rfl (by omega) halpha_cap hu₁_ioo) l
    have hm1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle1 h1m_pos.le) hs₁pos.le
    dsimp [u₁, T₁] at hm1; linarith
  have hAt2 : g s₂ - s₂ * δ < cappedWindowPhaseObjective M n theta tau s₂ := by
    rw [g_eq hs₂pos.ne']; unfold cappedWindowPhaseObjective cappedWindowFiniteEntropy
    have hm_th := mul_lt_mul_of_pos_left hlLt h1m_pos
    rw [mul_add, mul_div_cancel₀ _ h1m_pos.ne'] at hm_th
    have hm2 := mul_lt_mul_of_pos_left hm_th hs₂pos
    dsimp [u₂, T₂] at hm2; linarith
  have hAff : q / 2 * a ^ 2 - 4 ≤
      profileDeficitAffineA (phaseNat n) + profileDeficitAffineB (phaseNat n) * a := by
    have hcore := (abs_le.mp (abs_profileDeficitAffineCore_sub_quadratic_le (phaseNat n) (by omega))).1
    have hfac : factorialLogErrorBound (phaseNat n) ≤ a + 4 := by
      have h := Real.log_le_sub_one_of_pos (x := ((phaseNat n + 1 : ℕ) : ℝ)) (by positivity)
      have hEq : factorialLogErrorBound (phaseNat n) = Real.log ((phaseNat n + 1 : ℕ) : ℝ) + 4 := rfl
      rw [hEq]; push_cast at h ⊢; linarith
    dsimp [a] at hfac ⊢; linarith
  have hRemLe : C0 + C1 * a ≤ q / 4 * a ^ 2 := by
    have h1 : 4 * (C0 + C1) ≤ a * q := (div_le_iff₀ q_pos).mp (by linarith [hBig])
    have h2 : C0 + C1 * a ≤ (C0 + C1) * a := by
      have hc0a : C0 ≤ C0 * a := by
        calc C0 = C0 * 1 := (mul_one C0).symm
          _ ≤ C0 * a := mul_le_mul_of_nonneg_left (by linarith) hC0pos.le
      linarith
    have h3 : 4 * (C0 + C1) * a ≤ (a * q) * a :=
      mul_le_mul_of_nonneg_right h1 haPos.le
    linarith [show 4 * ((C0 + C1) * a) = 4 * (C0 + C1) * a by ring,
      show (a * q) * a = 4 * (q / 4 * a ^ 2) by ring]
  have hbin_nn : 0 ≤ binEntropy theta :=
    (binEntropy_bounds_Icc ⟨htheta.1, by linarith [htheta.2]⟩).1
  have hcap_lin_lo :
      -2 * Ml * a - 2 * Ml - B_sc ≤
        (1 - theta) * Real.log (windowFinitePartition (phaseNat n) 1 (M - 1) l) -
          l * (a - theta) := by
    have hid : (1 - theta) * Real.log (windowFinitePartition (phaseNat n) 1 (M - 1) l) -
        l * (a - theta) =
        (1 - theta) * (Real.log (windowFinitePartition (phaseNat n) 1 (M - 1) l) - l * a) -
          theta * l * (a - 1) := by ring
    rw [hid]
    have hm1 :
        (1 - theta) * (-Ml * (a + 2) - B_sc) ≤
          (1 - theta) * (Real.log (windowFinitePartition (phaseNat n) 1 (M - 1) l) - l * a) :=
      mul_le_mul_of_nonneg_left hLinLo_raw h1m_pos.le
    have hlo1 : -(Ml * (a + 2) + B_sc) ≤
        (1 - theta) * (-Ml * (a + 2) - B_sc) := by
      have hnn : 0 ≤ Ml * (a + 2) + B_sc := by dsimp [B_sc, Ml]; positivity
      have hm_le := mul_le_mul_of_nonneg_right h1m_le1 hnn
      linarith
    have hl_th : |theta * l * (a - 1)| ≤ Ml * a := by
      rw [abs_mul, abs_mul, abs_of_nonneg htheta.1, abs_of_pos (by linarith : 0 < a - 1)]
      calc theta * |l| * (a - 1)
          ≤ (1 * Ml) * a := by
            refine mul_le_mul (mul_le_mul (by linarith [htheta.2]) hl_abs (abs_nonneg _) zero_le_one)
              (by linarith) (by linarith) (mul_nonneg zero_le_one hMlnn)
        _ = Ml * a := by ring
    have hexp_lo1 : -(Ml * (a + 2) + B_sc) - Ml * a = -2 * Ml * a - 2 * Ml - B_sc := by ring
    linarith [(abs_le.mp hl_th).2, hexp_lo1]
  have hSubIcc : Set.Icc s₁ s₂ ⊆ Set.Icc
      (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
      (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n) :=
    fun x hx ↦ ⟨hs₁.1.trans hx.1, hx.2.trans hs₂.2⟩
  have hHasDerivG : ∀ x ∈ Set.Icc s₁ s₂, HasDerivAt g (-Real.log x + m_slope) x :=
    fun x hx ↦ hasDerivAt_branchObjective_v11 c_const m_slope (lt_of_lt_of_le hs₁pos hx.1)
  have hContG : ContinuousOn g (Set.Icc s₁ s₂) :=
    fun x hx ↦ (hHasDerivG x hx).continuousAt.continuousWithinAt
  have hDiffG : DifferentiableOn ℝ g (Set.Ioo s₁ s₂) :=
    fun x hx ↦ (hHasDerivG x (Ioo_subset_Icc_self hx)).differentiableAt.differentiableWithinAt
  have hSlopeG : ∀ x ∈ Set.Ioo s₁ s₂, q / 4 * a ^ 2 ≤ deriv g x := by
    intro x hx
    have hxIcc := Ioo_subset_Icc_self hx
    rw [(hHasDerivG x hxIcc).deriv]
    have hlogx : Real.log x ≤ Real.log 2 + K * a := (abs_le.mp (hLogN x (hSubIcc hxIcc))).2
    have hq_th : Real.log 2 / 2 * theta ≤ Real.log 2 := by
      have := mul_le_mul_of_nonneg_left htheta.2 (div_pos (Real.log_pos one_lt_two) two_pos).le
      linarith [Real.log_pos one_lt_two]
    have hm_def : m_slope =
        (profileDeficitAffineA (phaseNat n) + profileDeficitAffineB (phaseNat n) * a) +
          tau + binEntropy theta - Real.log 2 / 2 * theta +
          ((1 - theta) * Real.log (windowFinitePartition (phaseNat n) 1 (M - 1) l) -
            l * (a - theta)) := by
      dsimp [m_slope]; ring
    have hC_comb : C0 + C1 * a =
        2 * Real.log 2 + 5 + 2 * Ml + B_sc + K * a + 2 * Ml * a := by
      dsimp [C0, C1]; ring
    rw [hm_def]
    linarith [htau.1, hAff, hRemLe, hbin_nn, hcap_lin_lo, hlogx, hq_th, hC_comb]
  have hIncG := derivative_lower_bound_mul_sub_le_sub hlt.le hContG hDiffG hSlopeG
  have hPosGain : 0 < (q / 8 * a ^ 2) * (s₂ - s₁) :=
    mul_pos (mul_pos (div_pos q_pos (by norm_num)) haSqPos) (sub_pos.mpr hlt)
  linarith

/-- **Lemma 3.1 general-`M` capped finite-window corridor roots (`∃!`) and `(3.6)` location:**
for every `M ≥ 8`, there exist `C > 0` and `A_* > 0` such that eventually whenever
`δ_n ∈ [0, δ_*]`, uniformly over `ϑ ∈ [0, 1/20]` and `τ ∈ [0, log 2]`:
1. `𝓛_{S_{0,M}}^{=ϑ}(n, ·) + τ ·` is strictly increasing on `[c_n - C Δ_n, c_n + C Δ_n]`,
2. `𝓛_{S_{0,M}}^{=ϑ}(n, r) + τ r = 0` has a unique solution `r` in `(c_n - C Δ_n, c_n + C Δ_n)`,
3. that root satisfies `|n / r - s₀| ≤ A_* log log n / log n` and
   `|(α - n / r) - T_{δ_n}| ≤ A_* log log n / log n` (`(3.6)`). -/
theorem exists_pos_eventually_existsUnique_cappedWindowPhaseObjective_zero_logLogCorridor
    {M : ℕ} (hM : 8 ≤ M) :
    ∃ C A_star : ℝ, 0 < C ∧ 0 < A_star ∧
      ∀ᶠ n : ℕ in atTop,
        phaseDelta n ∈ Set.Icc (0 : ℝ) deltaStar →
          ∀ theta ∈ Set.Icc (0 : ℝ) (1 / 20),
            ∀ tau ∈ Set.Icc (0 : ℝ) (Real.log 2),
              let F_cap_fin : ℝ → ℝ := fun T ↦
                binEntropy theta - Real.log 2 / 2 * theta +
                  (1 - theta) * (⨅ l : ℝ,
                    (Real.log (∑ i ∈ Finset.Icc 2 M,
                        Real.exp (l * (i : ℝ) +
                          (Real.log ((phaseNat n).descFactorial i : ℝ) -
                            (i : ℝ) * Real.log (phaseNat n : ℝ) -
                            Real.log 2 / 2 * (i : ℝ) ^ 2))) -
                      l * ((T - theta) / (1 - theta))))
              let obj : ℝ → ℝ := fun s ↦
                (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + s - s * Real.log s +
                  s * (profileDeficitAffineA (phaseNat n) +
                    profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s +
                    F_cap_fin (fourSizeTarget n (phaseNat n) s) + tau)
              StrictMonoOn obj
                  (Set.Icc (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
                           (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n)) ∧
                (∃! r : ℝ,
                  r ∈ Set.Ioo (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
                              (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n) ∧
                    obj r = 0) ∧
                (∀ r ∈ Set.Ioo (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
                               (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n),
                  obj r = 0 →
                    |(n : ℝ) / r - phaseRootS0 n| ≤ A_star * logLogOrder n / logOrder n ∧
                      |fourSizeTarget n (phaseNat n) r - phaseTarget (phaseDelta n)| ≤
                        A_star * logLogOrder n / logOrder n) := by
  obtain ⟨B, hBpos, hB⟩ :=
    unrestrictedPhaseObjective_center_div_isBigO_logLogOrder.exists_pos
  obtain ⟨Mtilt, hMtiltnn, huniformTilt⟩ :=
    exists_eventually_forall_mem_Icc_abs_profileDeficitTilt_le
      (by norm_num : (-1 : ℝ) < 9 / 4) (by norm_num : (9 / 4 : ℝ) ≤ 17 / 4)
  obtain ⟨Ntilt, hNtilt⟩ := eventually_atTop.1 huniformTilt
  let C : ℝ := 16 * (B + 2) / q
  have hCpos : 0 < C := div_pos (mul_pos (by norm_num) (by linarith)) q_pos
  refine ⟨C, 2 * C, hCpos, by positivity, ?_⟩
  let Gbound : ℝ := 2 * Real.log 2 + 5 * Mtilt + 2 * |Real.log (partitionFn Splus 0)| +
    |min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))| + (M : ℝ) ^ 2 + 3
  have hLLBig : ∀ᶠ n : ℕ in atTop, max 1 (2 * Gbound + 1) ≤ logLogOrder n :=
    tendsto_logLogOrder_atTop.eventually_ge_atTop _
  have hphaseN : ∀ᶠ n : ℕ in atTop, max Ntilt (2 * M) ≤ phaseNat n := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop ((max Ntilt (2 * M) : ℕ) : ℝ),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact_mod_cast hn.trans hph.1
  filter_upwards [hB.bound, hLLBig, hphaseN,
    eventually_cappedWindowPhaseObjective_strictMonoOn_logLogCorridor hM C hCpos.le,
    eventually_corridor_inv_target_logLogRate C hCpos.le,
    eventually_phaseRootLogLogCorridor_fourSize_domain C hCpos.le,
    eventually_phaseRootLogLogCorridor_fourSize_target_mem_Icc C hCpos.le,
    eventually_cappedWindow_target_mem_KcapInterval C hCpos.le,
    eventually_unrestrictedPhaseObjective_deriv_logLogCorridor_lower C hCpos.le,
    eventually_phaseRoot_domain_pos_and_target_corridor,
    eventually_five_lt_phaseNat] with
    n hcenterBound hLL hphN hStrict hInvRate hdomain htarget hKcap hderiv hcenterDom hfive
    hd theta htheta tau htau
  intro F_cap_fin obj
  have hM_eq : 1 + (M - 1) = M := by omega
  have hpw : ∀ s : ℝ, obj s = cappedWindowPhaseObjective M n theta tau s := by
    intro s
    unfold obj cappedWindowPhaseObjective cappedWindowFiniteEntropy F_cap_fin
      windowFiniteEntropy windowFinitePartition windowFiniteScore
    simp only [hM_eq]
  set s0 : ℝ := phaseRootCenter n
  set a : ℝ := (phaseNat n : ℝ)
  set Delta : ℝ := C * logLogOrder n * phaseRootGapRadius n
  have hLL1 : 1 ≤ logLogOrder n := (le_max_left _ _).trans hLL
  have hLLG : 2 * Gbound + 1 ≤ logLogOrder n := (le_max_right _ _).trans hLL
  have hLLPos : 0 < logLogOrder n := lt_of_lt_of_le zero_lt_one hLL1
  have hs0Pos : 0 < s0 :=
    div_pos (by exact_mod_cast (lt_trans Nat.zero_lt_one hcenterDom.1.1)) hcenterDom.2.1
  have haPos : 0 < a := Nat.cast_pos.mpr (lt_trans (by omega : 0 < 5) hfive)
  have haSqPos : 0 < a ^ 2 := sq_pos_of_pos haPos
  have hDeltaPos : 0 < Delta := mul_pos (mul_pos hCpos hLLPos) (div_pos hs0Pos haSqPos)
  have halpha_cap : 2 * (1 + (M - 1)) ≤ phaseNat n := by
    have := (le_max_right Ntilt (2 * M)).trans hphN; omega
  have h1m_pos : 0 < 1 - theta := by linarith [htheta.2]
  have h1m_le1 : 1 - theta ≤ 1 := by linarith [htheta.1]
  have hCont : ContinuousOn (cappedWindowPhaseObjective M n theta tau)
      (Set.Icc (s0 - Delta) (s0 + Delta)) := by
    have hPosOn : ∀ s ∈ Set.Icc (s0 - Delta) (s0 + Delta), s ≠ 0 := by
      intro s hs
      linarith [(hInvRate.2 s hs).1, hs0Pos]
    have hTargetCont : ContinuousOn (fourSizeTarget n (phaseNat n))
        (Set.Icc (s0 - Delta) (s0 + Delta)) := by
      unfold fourSizeTarget
      exact continuousOn_const.sub (continuousOn_const.div continuousOn_id hPosOn)
    have hRedCont : ContinuousOn
        (fun s ↦ (fourSizeTarget n (phaseNat n) s - theta) / (1 - theta))
        (Set.Icc (s0 - Delta) (s0 + Delta)) :=
      (hTargetCont.sub continuousOn_const).div_const (1 - theta)
    have hMaps : MapsTo (fun s ↦ (fourSizeTarget n (phaseNat n) s - theta) / (1 - theta))
        (Set.Icc (s0 - Delta) (s0 + Delta)) (Set.Icc (9 / 4 : ℝ) (9 / 2)) := by
      intro s hs
      have hu := (reducedTarget_mem_Icc_and_Ioo htheta (hKcap hd s hs)).1
      exact ⟨by linarith [hu.1], hu.2⟩
    have hEntCont := (continuousOn_windowFiniteEntropy_Icc (m := 1) (M := M - 1)
      le_rfl (by omega) halpha_cap).comp hRedCont hMaps
    unfold cappedWindowPhaseObjective cappedWindowFiniteEntropy
    exact (((continuousOn_const.add continuousOn_id).sub
      (continuousOn_id.mul (continuousOn_id.log hPosOn))).add
      (continuousOn_id.mul (((continuousOn_const.add
        (continuousOn_const.mul hTargetCont)).add
          (continuousOn_const.add (continuousOn_const.mul hEntCont))).add continuousOn_const)))
  have hShiftBound : ∀ s ∈ Set.Icc (s0 - Delta) (s0 + Delta),
      |s * (tau - finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) s) +
          cappedWindowFiniteEntropy (phaseNat n) M theta (fourSizeTarget n (phaseNat n) s))| ≤
        logLogOrder n * s0 := by
    intro s hs
    have hsPos : 0 < s := by linarith [(hInvRate.2 s hs).1, hs0Pos]
    have hsLe2 : s ≤ 2 * s0 := (hInvRate.2 s hs).2.1
    set T : ℝ := fourSizeTarget n (phaseNat n) s
    have hTK : T ∈ Set.Icc (9 / 4 : ℝ) (17 / 4) := htarget s (by simpa [s0, Delta] using hs)
    have hT25 : T ∈ Set.Ioo (2 : ℝ) 5 := ⟨by linarith [hTK.1], by linarith [hTK.2]⟩
    have hTKcap : T ∈ KcapInterval := hKcap hd s hs
    set u : ℝ := (T - theta) / (1 - theta)
    obtain ⟨hu_icc, hu_ioo⟩ := reducedTarget_mem_Icc_and_Ioo htheta hTKcap
    have hUnrestHi : finiteUnrestrictedDeficitEntropy (phaseNat n) T ≤
        |Real.log (partitionFn Splus 0)| := by
      have h1 := (finiteProfileDeficitEntropy_le_extendedGaussianEntropyValue
        (phaseNat n) hfive hT25).trans (extendedGaussianEntropyValue_le_dualValue_Splus hT25)
      have hm4 := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT25)
      have h2 := dualValue_le_at S4_subset_Splus hm4 0
      unfold finiteUnrestrictedDeficitEntropy
      linarith [le_abs_self (Real.log (partitionFn Splus 0))]
    have hUnrestLo : -(5 * Mtilt) ≤ finiteUnrestrictedDeficitEntropy (phaseNat n) T := by
      obtain ⟨_, htiltB⟩ := hNtilt (phaseNat n) ((le_max_left _ _).trans hphN) T hTK
      have hp1 := one_le_profileDeficitPartition (phaseNat n) (by omega)
        (profileDeficitTilt (phaseNat n) T)
      have hlognn := Real.log_nonneg hp1
      have hmul : |profileDeficitTilt (phaseNat n) T * T| ≤ 5 * Mtilt := by
        rw [abs_mul, abs_of_pos (by linarith [hTK.1] : 0 < T)]
        have := mul_le_mul htiltB (show T ≤ 5 by linarith [hTK.2]) (by linarith [hTK.1]) hMtiltnn
        linarith
      unfold finiteUnrestrictedDeficitEntropy
      linarith [(abs_le.mp hmul).2]
    have hw_err := (windowFiniteEntropy_bounds (m := 1) (M := M - 1)
      le_rfl (by omega) halpha_cap hu_ioo).1
    have hd_bds := dualValue_window_bounds_on_padded (m := 1) (M := M - 1)
      le_rfl (by omega) u ⟨by linarith [hu_icc.1], by linarith [hu_icc.2]⟩
    have herr_le : ((1 + (M - 1) : ℕ) : ℝ) ^ 2 / a ≤ (M : ℝ) ^ 2 := by
      simp only [hM_eq]
      have ha1 : 1 ≤ a := by dsimp [a]; exact_mod_cast (show 1 ≤ phaseNat n by omega)
      calc (M : ℝ) ^ 2 / a ≤ (M : ℝ) ^ 2 / 1 :=
            div_le_div_of_nonneg_left (sq_nonneg _) zero_lt_one ha1
        _ = (M : ℝ) ^ 2 := div_one _
    have hbin_bds := binEntropy_bounds_Icc ⟨htheta.1, by linarith [htheta.2]⟩
    have htail_abs :
        |(1 - theta) * windowFiniteEntropy (phaseNat n) 1 (M - 1) u| ≤
          |Real.log (partitionFn Splus 0)| +
            |min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))| + (M : ℝ) ^ 2 := by
      rw [abs_mul, abs_of_pos h1m_pos]
      have hw_abs : |windowFiniteEntropy (phaseNat n) 1 (M - 1) u| ≤
          |Real.log (partitionFn Splus 0)| +
            |min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))| + (M : ℝ) ^ 2 := by
        rw [abs_le]
        dsimp [a] at herr_le
        exact ⟨by linarith [hw_err.1, hd_bds.1, herr_le,
            neg_abs_le (min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))),
            abs_nonneg (Real.log (partitionFn Splus 0))],
          by linarith [hw_err.2, hd_bds.2,
            le_abs_self (Real.log (partitionFn Splus 0)),
            abs_nonneg (min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))),
            sq_nonneg (M : ℝ)]⟩
      exact (mul_le_mul_of_nonneg_right h1m_le1 (abs_nonneg _)).trans (by simpa using hw_abs)
    have hInnerAbs :
        |tau - finiteUnrestrictedDeficitEntropy (phaseNat n) T +
          cappedWindowFiniteEntropy (phaseNat n) M theta T| ≤ Gbound := by
      unfold cappedWindowFiniteEntropy
      rw [abs_le]
      dsimp [Gbound, u] at htail_abs ⊢
      have hq_th : Real.log 2 / 2 * theta ≤ Real.log 2 := by
        have := mul_le_mul_of_nonneg_left htheta.2 (div_pos (Real.log_pos one_lt_two) two_pos).le
        linarith [Real.log_pos one_lt_two]
      have hq_th_nn : 0 ≤ Real.log 2 / 2 * theta :=
        mul_nonneg (div_nonneg (Real.log_pos one_lt_two).le zero_le_two) htheta.1
      exact ⟨by linarith [htau.1, hUnrestHi, hbin_bds.1, (abs_le.mp htail_abs).1, hq_th,
          hMtiltnn, Real.log_pos one_lt_two,
          abs_nonneg (Real.log (partitionFn Splus 0)),
          abs_nonneg (min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))),
          sq_nonneg (M : ℝ)],
        by linarith [htau.2, hUnrestLo, hbin_bds.2, (abs_le.mp htail_abs).2, hq_th_nn,
          Real.log_pos one_lt_two,
          abs_nonneg (Real.log (partitionFn Splus 0)),
          abs_nonneg (min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))),
          sq_nonneg (M : ℝ)]⟩
    rw [abs_mul, abs_of_pos hsPos]
    calc s * |tau - finiteUnrestrictedDeficitEntropy (phaseNat n) T +
            cappedWindowFiniteEntropy (phaseNat n) M theta T|
        ≤ (2 * s0) * Gbound :=
          mul_le_mul hsLe2 hInnerAbs (abs_nonneg _) (mul_pos two_pos hs0Pos).le
      _ ≤ logLogOrder n * s0 := by
          have := mul_le_mul_of_nonneg_right hLLG hs0Pos.le
          linarith
  have hDiffId : ∀ {s : ℝ}, s ≠ 0 →
      cappedWindowPhaseObjective M n theta tau s =
        unrestrictedPhaseObjective n s +
          s * (tau - finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) s) +
            cappedWindowFiniteEntropy (phaseNat n) M theta (fourSizeTarget n (phaseNat n) s)) := by
    intro s hsNe
    have hu := unrestrictedPhaseObjective_div_eq_deficitCentered n hsNe
    have huMul : unrestrictedPhaseObjective n s =
        s * ((n : ℝ) * Real.log (n : ℝ) / s - (n : ℝ) / s + 1 - Real.log s +
          (profileDeficitAffineA (phaseNat n) +
            profileDeficitAffineB (phaseNat n) * profileDeficitTarget (phaseNat n) (n : ℝ) s +
            finiteUnrestrictedDeficitEntropy (phaseNat n)
              (profileDeficitTarget (phaseNat n) (n : ℝ) s))) := by
      rw [div_eq_iff hsNe] at hu
      unfold finiteUnrestrictedDeficitEntropy
      linarith
    rw [huMul]
    unfold cappedWindowPhaseObjective fourSizeTarget profileDeficitTarget
    field_simp [hsNe]
    ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hLLPos] at hcenterBound
  have hCenterAbs : |unrestrictedPhaseObjective n s0| ≤ B * logLogOrder n * s0 := by
    have hm_c := mul_le_mul_of_nonneg_right hcenterBound hs0Pos.le
    rwa [abs_div, abs_of_pos hs0Pos, div_mul_cancel₀ _ hs0Pos.ne'] at hm_c
  have ha_ge6 : (6 : ℝ) ≤ (phaseNat n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hfive)
  have hKeyU : ∀ x ∈ Set.Icc (s0 - Delta) (s0 + Delta),
      HasDerivAt (unrestrictedPhaseObjective n)
        (Real.log (profileDualPartition (phaseNat n + 1)
            (profileDualTilt (phaseNat n + 1) ((n : ℝ) / x))) - Real.log x) x := by
    intro x hx
    obtain ⟨hxpos, htar⟩ := hdomain x (by simpa [s0, Delta] using hx)
    rw [fourSizeTarget, Set.mem_Ioo] at htar
    exact hasDerivAt_profileDualOptimalValue_parts (by omega) hxpos (by
      rw [Set.mem_Ioo, show (((phaseNat n + 1 : ℕ) : ℝ)) = (phaseNat n : ℝ) + 1 by push_cast; ring]
      exact ⟨by linarith [htar.2, ha_ge6], by linarith [htar.1]⟩)
  have hContU : ContinuousOn (unrestrictedPhaseObjective n) (Set.Icc (s0 - Delta) (s0 + Delta)) :=
    fun x hx ↦ (hKeyU x hx).continuousAt.continuousWithinAt
  have hDiffU : DifferentiableOn ℝ (unrestrictedPhaseObjective n)
      (Set.Ioo (s0 - Delta) (s0 + Delta)) :=
    fun x hx ↦ (hKeyU x (Ioo_subset_Icc_self hx)).differentiableAt.differentiableWithinAt
  have hDerivLo : ∀ x ∈ Set.Ioo (s0 - Delta) (s0 + Delta),
      q / 8 * a ^ 2 ≤ deriv (unrestrictedPhaseObjective n) x :=
    fun x hx ↦ hderiv x (Ioo_subset_Icc_self (by simpa [s0, Delta] using hx))
  have hProdSlope : (q / 8 * a ^ 2) * Delta = 2 * (B + 2) * logLogOrder n * s0 := by
    dsimp [Delta, C, s0, a]; unfold phaseRootGapRadius
    field_simp [q_ne_zero, haPos.ne']; ring
  have hLeftInc := derivative_lower_bound_mul_sub_le_sub
    (show s0 - Delta ≤ s0 by linarith)
    (hContU.mono fun x hx ↦ ⟨hx.1, hx.2.trans (by linarith)⟩)
    (hDiffU.mono fun x hx ↦ ⟨hx.1, lt_of_lt_of_le hx.2 (by linarith)⟩)
    (fun x hx ↦ hDerivLo x ⟨hx.1, lt_of_lt_of_le hx.2 (by linarith)⟩)
  have hRightInc := derivative_lower_bound_mul_sub_le_sub
    (show s0 ≤ s0 + Delta by linarith)
    (hContU.mono fun x hx ↦ ⟨(by linarith : s0 - Delta ≤ s0).trans hx.1, hx.2⟩)
    (hDiffU.mono fun x hx ↦ ⟨lt_of_le_of_lt (by linarith) hx.1, hx.2⟩)
    (fun x hx ↦ hDerivLo x ⟨lt_of_le_of_lt (by linarith) hx.1, hx.2⟩)
  rw [show s0 - (s0 - Delta) = Delta by ring, hProdSlope] at hLeftInc
  rw [show s0 + Delta - s0 = Delta by ring, hProdSlope] at hRightInc
  have hexp_slope :
      2 * (B + 2) * logLogOrder n * s0 =
        2 * (B * logLogOrder n * s0) + 4 * (logLogOrder n * s0) := by ring
  have hB_pos_ll : 0 < B * logLogOrder n * s0 := mul_pos (mul_pos hBpos hLLPos) hs0Pos
  have hNegLeft : cappedWindowPhaseObjective M n theta tau (s0 - Delta) < 0 := by
    have hsL_mem : s0 - Delta ∈ Set.Icc (s0 - Delta) (s0 + Delta) := ⟨le_rfl, by linarith⟩
    have hsL_pos : 0 < s0 - Delta := by linarith [(hInvRate.2 _ hsL_mem).1, hs0Pos]
    rw [hDiffId hsL_pos.ne']
    have hsh := (abs_le.mp (hShiftBound (s0 - Delta) hsL_mem)).2
    have hc_hi := (abs_le.mp hCenterAbs).2
    have hpos_ll : 0 < logLogOrder n * s0 := mul_pos hLLPos hs0Pos
    linarith
  have hPosRight : 0 < cappedWindowPhaseObjective M n theta tau (s0 + Delta) := by
    have hsR_mem : s0 + Delta ∈ Set.Icc (s0 - Delta) (s0 + Delta) := ⟨by linarith, le_rfl⟩
    have hsR_pos : 0 < s0 + Delta := by linarith
    rw [hDiffId hsR_pos.ne']
    have hsh := (abs_le.mp (hShiftBound (s0 + Delta) hsR_mem)).1
    have hc_lo := (abs_le.mp hCenterAbs).1
    have hpos_ll : 0 < logLogOrder n * s0 := mul_pos hLLPos hs0Pos
    linarith
  have hStrict_n := hStrict hd theta htheta tau htau
  refine ⟨fun s₁ hs₁ s₂ hs₂ hlt ↦ ?_, ?_, ?_⟩
  · rw [hpw s₁, hpw s₂]
    exact hStrict_n hs₁ hs₂ hlt
  · have hivt : (0 : ℝ) ∈ cappedWindowPhaseObjective M n theta tau '' Set.Icc (s0 - Delta) (s0 + Delta) :=
      intermediate_value_Icc (by linarith) hCont ⟨hNegLeft.le, hPosRight.le⟩
    rcases hivt with ⟨r, hr_icc, hr_zero⟩
    have hr_gt : s0 - Delta < r := lt_of_le_of_ne hr_icc.1 fun heq ↦ by
      rw [← heq] at hr_zero; linarith
    have hr_lt : r < s0 + Delta := lt_of_le_of_ne hr_icc.2 fun heq ↦ by
      rw [heq] at hr_zero; linarith
    refine ⟨r, ⟨⟨hr_gt, hr_lt⟩, (hpw r).trans hr_zero⟩, fun y ⟨hy_ioo, hy_zero⟩ ↦ ?_⟩
    have hy_c : cappedWindowPhaseObjective M n theta tau y = 0 := (hpw y).symm.trans hy_zero
    exact hStrict_n.injOn (Ioo_subset_Icc_self hy_ioo) hr_icc (hy_c.trans hr_zero.symm)
  · intro r hr_ioo _
    have hi := hInvRate.2 r (Ioo_subset_Icc_self hr_ioo)
    exact ⟨hi.2.2.1, hi.2.2.2⟩

/-- **Lemma 3.1, eq. `(3.7)` explicit `O((log n)(log log n))` unrestricted slope rate:**
for every `A ≥ 0`, there exists `K_slope > 0` such that eventually across the entire log-log
corridor `[c_n - A Δ_n, c_n + A Δ_n]` and all `τ ∈ [0, log 2]`,
`|∂_k (𝓛_{S_+}(n, k) + τ k) - (2 / log 2)(log n)²| ≤ K_slope (log n)(log log n)`. -/
theorem eventually_unrestrictedPhaseObjective_deriv_logLogRate
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ K_slope : ℝ, 0 < K_slope ∧ ∀ᶠ n : ℕ in atTop,
      ∀ tau ∈ Set.Icc (0 : ℝ) (Real.log 2),
        ∀ s ∈ Set.Icc
            (phaseRootCenter n - A * logLogOrder n * phaseRootGapRadius n)
            (phaseRootCenter n + A * logLogOrder n * phaseRootGapRadius n),
          |deriv (fun k : ℝ ↦ unrestrictedPhaseObjective n k + tau * k) s -
              (2 / Real.log 2) * (Real.log (n : ℝ)) ^ 2| ≤
            K_slope * Real.log (n : ℝ) * Real.log (Real.log (n : ℝ)) := by
  obtain ⟨K_log, hK_log_nn, hLogCorr⟩ := eventually_corridor_abs_log_linear A hA
  obtain ⟨Mtilt, hMtilt_nn, huniformTilt⟩ :=
    exists_eventually_forall_mem_Icc_abs_profileDeficitTilt_le
      (by norm_num : (-1 : ℝ) < 9 / 4) (by norm_num : (9 / 4 : ℝ) ≤ 17 / 4)
  obtain ⟨Ntilt, hNtilt⟩ := eventually_atTop.1 huniformTilt
  set CL : ℝ := Real.exp Mtilt + Real.exp (Mtilt ^ 2 / q) * (1 / (1 - Real.exp (-q / 4)))
  set K_rem : ℝ := 4 * (2 + Mtilt + K_log) + CL + 2 * Real.log 2 + 10
  set K_slope : ℝ := 21 / q + K_rem + 1
  have hCL_pos : 0 < CL := by
    have h1 : 0 < 1 - Real.exp (-q / 4) := by
      have : Real.exp (-q / 4) < 1 := Real.exp_lt_one_iff.mpr (by linarith [q_pos])
      linarith
    dsimp [CL]; positivity
  have hK_slope_pos : 0 < K_slope := by
    have := q_pos; have := Real.log_pos one_lt_two; dsimp [K_slope, K_rem]; positivity
  refine ⟨K_slope, hK_slope_pos, ?_⟩
  have hphaseN : ∀ᶠ n : ℕ in atTop, Ntilt ≤ phaseNat n := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop (Ntilt : ℝ),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact_mod_cast hn.trans hph.1
  have hW_big : ∀ᶠ n : ℕ in atTop,
      max 1 (|2 * phaseC| + q + 2) ≤ logLogOrder n :=
    tendsto_logLogOrder_atTop.eventually_ge_atTop _
  have hW_le_L : ∀ᶠ n : ℕ in atTop, ‖logLogOrder n‖ ≤ 1 * ‖logOrder n‖ :=
    logLogOrder_isLittleO_logOrder.bound zero_lt_one
  have hL_big : ∀ᶠ n : ℕ in atTop, 4 ≤ logOrder n :=
    tendsto_logOrder_atTop.eventually_ge_atTop 4
  filter_upwards [hLogCorr, hphaseN, hW_big, hW_le_L, hL_big,
    eventually_phaseRootLogLogCorridor_fourSize_domain A hA,
    eventually_phaseRootLogLogCorridor_fourSize_target_mem_Icc A hA,
    eventually_phaseRoot_domain_pos_and_target_corridor,
    eventually_five_lt_phaseNat,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with
    n hLogN hphN hWn hWL hLn hdomain htarget hcenterDom hfive hphase tau htau s hs
  set a : ℝ := (phaseNat n : ℝ)
  set L : ℝ := logOrder n
  set w : ℝ := logLogOrder n
  have hw1 : 1 ≤ w := (le_max_left _ _).trans hWn
  have hw_c : |2 * phaseC| + q + 2 ≤ w := (le_max_right _ _).trans hWn
  have hL_pos : 0 < L := by linarith
  have hw_pos : 0 < w := by linarith
  rw [Real.norm_eq_abs, abs_of_pos hw_pos, Real.norm_eq_abs, abs_of_pos hL_pos, one_mul] at hWL
  have hTK : profileDeficitTarget (phaseNat n) (n : ℝ) s ∈ Set.Icc (9 / 4 : ℝ) (17 / 4) :=
    htarget s hs
  obtain ⟨hTopen, htiltB⟩ := hNtilt (phaseNat n) hphN _ hTK
  have ha_ge6 : (6 : ℝ) ≤ (phaseNat n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hfive)
  obtain ⟨hspos, htar_four⟩ := hdomain s hs
  rw [fourSizeTarget, Set.mem_Ioo] at htar_four
  have hdiffAt : DifferentiableAt ℝ (unrestrictedPhaseObjective n) s :=
    (hasDerivAt_profileDualOptimalValue_parts (by omega) hspos (by
      rw [Set.mem_Ioo, show (((phaseNat n + 1 : ℕ) : ℝ)) = (phaseNat n : ℝ) + 1 by push_cast; ring]
      exact ⟨by linarith [htar_four.2, ha_ge6], by linarith [htar_four.1]⟩)).differentiableAt
  have hderiv_add : deriv (fun k : ℝ ↦ unrestrictedPhaseObjective n k + tau * k) s =
      deriv (unrestrictedPhaseObjective n) s + tau := by
    have hd_tau : HasDerivAt (fun k : ℝ ↦ tau * k) tau s := by
      simpa using (hasDerivAt_id s).const_mul tau
    exact (hdiffAt.hasDerivAt.add hd_tau).deriv
  rw [hderiv_add]
  have hmain := abs_unrestrictedPhaseObjective_deriv_sub_deficitMain_le (n := n) (k := s) hTopen
  have hphaseExact : a * q = 2 * L - 2 * w + 2 * phaseC + q * phaseB n := by
    dsimp [a, L, w]
    rw [phaseNat_cast_eq_two_phaseS_div_q_add_phaseB hcenterDom.1]
    unfold phaseS
    field_simp [q_ne_zero]
  have haq_diff : |a * q - 2 * L| ≤ 3 * w := by
    have hb_pos : 0 ≤ q * phaseB n := mul_nonneg q_pos.le (phaseB_pos n).le
    have hb_hi : q * phaseB n ≤ q := by
      calc q * phaseB n ≤ q * 1 := mul_le_mul_of_nonneg_left (phaseB_le_one n) q_pos.le
        _ = q := mul_one q
    have hc_abs := abs_le.mp (le_rfl : |2 * phaseC| ≤ |2 * phaseC|)
    rw [show a * q - 2 * L = -2 * w + 2 * phaseC + q * phaseB n by linarith, abs_le]
    exact ⟨by linarith [hc_abs.1], by linarith [hc_abs.2]⟩
  have hquad_diff : |q / 2 * a ^ 2 - 2 / q * L ^ 2| ≤ (21 / q) * L * w := by
    have hid_q : q / 2 * a ^ 2 - 2 / q * L ^ 2 =
        ((a * q - 2 * L) * (a * q + 2 * L)) / (2 * q) := by
      field_simp [q_ne_zero]; ring
    have haq_sum : |a * q + 2 * L| ≤ 7 * L := by
      have h1 : |a * q + 2 * L| ≤ |a * q - 2 * L| + 4 * L := by
        have := abs_add_le (a * q - 2 * L) (4 * L)
        rw [abs_of_pos (by positivity : 0 < 4 * L)] at this
        simpa [show (a * q - 2 * L) + 4 * L = a * q + 2 * L by ring] using this
      linarith
    rw [hid_q, abs_div, abs_mul, abs_of_pos (mul_pos two_pos q_pos)]
    calc |a * q - 2 * L| * |a * q + 2 * L| / (2 * q)
        ≤ (3 * w) * (7 * L) / (2 * q) := by
          apply div_le_div_of_nonneg_right _ (mul_pos two_pos q_pos).le
          exact mul_le_mul haq_diff haq_sum (abs_nonneg _) (by positivity)
      _ ≤ (21 / q) * L * w := by
          have : (0 : ℝ) ≤ L * w / q := div_nonneg (mul_nonneg hL_pos.le hw_pos.le) q_pos.le
          linarith [show (3 * w) * (7 * L) / (2 * q) = (21 / 2) * (L * w / q) by ring,
            show (21 / q) * L * w = 21 * (L * w / q) by ring]
  have hpartLower := one_le_profileDeficitPartition (phaseNat n) (by omega)
    (profileDeficitTilt (phaseNat n) (profileDeficitTarget (phaseNat n) (n : ℝ) s))
  have hpartUpper := profileDeficitPartition_le_gaussianEnvelope (phaseNat n) (by omega) htiltB
  have hlogPart : |Real.log (profileDeficitPartition (phaseNat n)
      (profileDeficitTilt (phaseNat n) (profileDeficitTarget (phaseNat n) (n : ℝ) s)))| ≤ CL := by
    rw [abs_of_nonneg (Real.log_nonneg hpartLower)]
    exact (Real.log_le_sub_one_of_pos (profileDeficitPartition_pos _ _)).trans (by dsimp [CL]; linarith)
  have ha_le4L : a ≤ 4 * L := hphase.2
  have ha_nn : 0 ≤ a := Nat.cast_nonneg _
  have htilt_a : |profileDeficitTilt (phaseNat n)
      (profileDeficitTarget (phaseNat n) (n : ℝ) s) * a| ≤ 4 * Mtilt * L := by
    rw [abs_mul, abs_of_nonneg ha_nn]
    calc |profileDeficitTilt (phaseNat n) (profileDeficitTarget (phaseNat n) (n : ℝ) s)| * a
        ≤ Mtilt * (4 * L) := mul_le_mul htiltB ha_le4L ha_nn hMtilt_nn
      _ = 4 * Mtilt * L := by ring
  have hlogs : |Real.log s| ≤ Real.log 2 + 4 * K_log * L := by
    have hl := hLogN s hs
    have hql2 : q = Real.log 2 := rfl
    calc |Real.log s| ≤ q + K_log * a := hl
      _ ≤ Real.log 2 + K_log * (4 * L) := by
          rw [hql2]; linarith [mul_le_mul_of_nonneg_left ha_le4L hK_log_nn]
      _ = Real.log 2 + 4 * K_log * L := by ring
  have hfac : factorialLogErrorBound (phaseNat n) ≤ 4 * L + 4 := by
    have h := Real.log_le_sub_one_of_pos (x := ((phaseNat n + 1 : ℕ) : ℝ)) (by positivity)
    have hEq : factorialLogErrorBound (phaseNat n) = Real.log ((phaseNat n + 1 : ℕ) : ℝ) + 4 := rfl
    rw [hEq]; push_cast at h ⊢; linarith
  have htau_abs : |tau| ≤ Real.log 2 := abs_le.mpr ⟨by linarith [htau.1, Real.log_pos one_lt_two], htau.2⟩
  have hLw_ge_L : L ≤ L * w := le_mul_of_one_le_right hL_pos.le hw1
  have hql2 : q = Real.log 2 := rfl
  set D_val : ℝ := deriv (unrestrictedPhaseObjective n) s
  set T_lin : ℝ := a - profileDeficitTilt (phaseNat n)
      (profileDeficitTarget (phaseNat n) (n : ℝ) s) * a +
    Real.log (profileDeficitPartition (phaseNat n)
      (profileDeficitTilt (phaseNat n) (profileDeficitTarget (phaseNat n) (n : ℝ) s))) -
    Real.log s
  have hm_bds := abs_le.mp hmain
  have ht_bds := abs_le.mp htilt_a
  have hp_bds := abs_le.mp hlogPart
  have hls_bds := abs_le.mp hlogs
  have htau_bds := abs_le.mp htau_abs
  have hT_lin_abs : |T_lin + tau + (D_val - (q / 2 * a ^ 2 + T_lin))| ≤ K_rem * (L * w) := by
    have hL1 : 1 ≤ L := by linarith [hLn]
    have hCL_L : CL ≤ CL * L := le_mul_of_one_le_right hCL_pos.le hL1
    have hlog2_L : Real.log 2 ≤ Real.log 2 * L :=
      le_mul_of_one_le_right (Real.log_pos one_lt_two).le hL1
    have hsum_le : |T_lin + tau + (D_val - (q / 2 * a ^ 2 + T_lin))| ≤ K_rem * L := by
      have hK_expand : K_rem * L =
          8 * L + 4 * Mtilt * L + 4 * K_log * L + CL * L + 2 * (Real.log 2 * L) + 10 * L := by
        dsimp [K_rem]; ring
      rw [hK_expand, abs_le]
      dsimp [T_lin] at hm_bds ⊢
      exact ⟨by linarith [hm_bds.1, ht_bds.2, hp_bds.1, hls_bds.2, htau_bds.1, hfac, ha_nn,
          ha_le4L, hCL_L, hlog2_L, hL1],
        by linarith [hm_bds.2, ht_bds.1, hp_bds.2, hls_bds.1, htau_bds.2, hfac, ha_nn,
          ha_le4L, hCL_L, hlog2_L, hL1]⟩
    have hK_rem_nn : 0 ≤ K_rem := by
      have := Real.log_pos one_lt_two; dsimp [K_rem]; positivity
    exact hsum_le.trans (mul_le_mul_of_nonneg_left hLw_ge_L hK_rem_nn)
  have hdecomp : D_val + tau - (2 / Real.log 2) * (Real.log (n : ℝ)) ^ 2 =
      (q / 2 * a ^ 2 - 2 / q * L ^ 2) + (T_lin + tau + (D_val - (q / 2 * a ^ 2 + T_lin))) := by
    dsimp [L]; unfold logOrder; rw [← hql2]; ring
  have hfinal : |D_val + tau - (2 / Real.log 2) * (Real.log (n : ℝ)) ^ 2| ≤
      K_slope * L * w := by
    have hLw_nn : 0 ≤ L * w := mul_nonneg hL_pos.le hw_pos.le
    rw [hdecomp]
    calc |(q / 2 * a ^ 2 - 2 / q * L ^ 2) + (T_lin + tau + (D_val - (q / 2 * a ^ 2 + T_lin)))|
        ≤ |q / 2 * a ^ 2 - 2 / q * L ^ 2| + |T_lin + tau + (D_val - (q / 2 * a ^ 2 + T_lin))| :=
          abs_add_le _ _
      _ ≤ (21 / q) * L * w + K_rem * (L * w) := add_le_add hquad_diff hT_lin_abs
      _ ≤ K_slope * L * w := by
          have hid : K_slope * L * w = (21 / q) * L * w + K_rem * (L * w) + L * w := by
            dsimp [K_slope]; ring
          linarith
  simpa only [L, w, logOrder, logLogOrder] using hfinal

private theorem finiteUnrestrictedDeficitEntropy_le_at_tilt
    {alpha : ℕ} (halpha : 0 < alpha) {T : ℝ}
    (hT : T ∈ Set.Ioo (-1 : ℝ) ((alpha : ℝ) - 1)) (l : ℝ) :
    finiteUnrestrictedDeficitEntropy alpha T ≤
      Real.log (profileDeficitPartition alpha l) - l * T := by
  set lam : ℝ := profileDeficitTilt alpha T
  set Z_lam : ℝ := profileDeficitPartition alpha lam
  set Z_l : ℝ := profileDeficitPartition alpha l
  have hZ_lam_pos : 0 < Z_lam := profileDeficitPartition_pos alpha lam
  have hZ_l_pos : 0 < Z_l := profileDeficitPartition_pos alpha l
  set w : Fin (alpha + 1) → ℝ := profileDeficitWeight alpha lam
  set qw : Fin (alpha + 1) → ℝ := profileDeficitWeight alpha l
  have hw_pos : ∀ i, 0 < w i := profileDeficitWeight_pos alpha lam
  have hqw_pos : ∀ i, 0 < qw i := profileDeficitWeight_pos alpha l
  have hkl_term : ∀ i : Fin (alpha + 1),
      w i * ((l - lam) * profileDeficit alpha i - Real.log Z_l + Real.log Z_lam) ≤ qw i - w i := by
    intro i
    have hlog_le := Real.log_le_sub_one_of_pos (div_pos (hqw_pos i) (hw_pos i))
    have hm := mul_le_mul_of_nonneg_left hlog_le (hw_pos i).le
    have hrhs : w i * (qw i / w i - 1) = qw i - w i := by
      field_simp [(hw_pos i).ne']
    have hlhs : Real.log (qw i / w i) =
        (l - lam) * profileDeficit alpha i - Real.log Z_l + Real.log Z_lam := by
      rw [Real.log_div (hqw_pos i).ne' (hw_pos i).ne']
      dsimp [qw, w, Z_l, Z_lam]
      unfold profileDeficitWeight
      rw [Real.log_div (profileDeficitUnnormalized_pos alpha l i).ne' hZ_l_pos.ne',
        Real.log_div (profileDeficitUnnormalized_pos alpha lam i).ne' hZ_lam_pos.ne']
      unfold profileDeficitUnnormalized
      rw [Real.log_exp, Real.log_exp]
      ring
    rwa [hlhs, hrhs] at hm
  have hsum_le := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hkl_term i
  have hrhs_zero : (∑ i : Fin (alpha + 1), (qw i - w i)) = 0 := by
    rw [Finset.sum_sub_distrib, sum_profileDeficitWeight, sum_profileDeficitWeight, sub_self]
  have hlhs_eval :
      (∑ i : Fin (alpha + 1),
        w i * ((l - lam) * profileDeficit alpha i - Real.log Z_l + Real.log Z_lam)) =
        (l - lam) * T - Real.log Z_l + Real.log Z_lam := by
    have hrew : ∀ i : Fin (alpha + 1),
        w i * ((l - lam) * profileDeficit alpha i - Real.log Z_l + Real.log Z_lam) =
          (l - lam) * (w i * profileDeficit alpha i) +
            (Real.log Z_lam - Real.log Z_l) * w i := fun _ ↦ by ring
    rw [Finset.sum_congr rfl fun i _ ↦ hrew i, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum]
    have hmean : (∑ i : Fin (alpha + 1), w i * profileDeficit alpha i) = T :=
      profileDeficitMean_profileDeficitTilt halpha hT
    have hmass : (∑ i : Fin (alpha + 1), w i) = 1 := sum_profileDeficitWeight alpha lam
    rw [hmean, hmass]
    ring
  unfold finiteUnrestrictedDeficitEntropy
  dsimp [Z_lam, lam, Z_l] at hlhs_eval hsum_le
  linarith

private theorem abs_finiteUnrestrictedDeficitEntropy_sub_le
    {alpha : ℕ} (halpha : 0 < alpha) {T₁ T₂ M_tilt : ℝ}
    (hT₁ : T₁ ∈ Set.Ioo (-1 : ℝ) ((alpha : ℝ) - 1))
    (hT₂ : T₂ ∈ Set.Ioo (-1 : ℝ) ((alpha : ℝ) - 1))
    (hM₁ : |profileDeficitTilt alpha T₁| ≤ M_tilt)
    (hM₂ : |profileDeficitTilt alpha T₂| ≤ M_tilt) :
    |finiteUnrestrictedDeficitEntropy alpha T₁ -
        finiteUnrestrictedDeficitEntropy alpha T₂| ≤ M_tilt * |T₁ - T₂| := by
  have h12 : finiteUnrestrictedDeficitEntropy alpha T₁ -
      finiteUnrestrictedDeficitEntropy alpha T₂ ≤ M_tilt * |T₁ - T₂| := by
    have hle := finiteUnrestrictedDeficitEntropy_le_at_tilt halpha hT₁
      (profileDeficitTilt alpha T₂)
    unfold finiteUnrestrictedDeficitEntropy at hle ⊢
    have hprod : profileDeficitTilt alpha T₂ * (T₂ - T₁) ≤ M_tilt * |T₁ - T₂| := by
      calc profileDeficitTilt alpha T₂ * (T₂ - T₁)
          ≤ |profileDeficitTilt alpha T₂ * (T₂ - T₁)| := le_abs_self _
        _ = |profileDeficitTilt alpha T₂| * |T₁ - T₂| := by rw [abs_mul, abs_sub_comm]
        _ ≤ M_tilt * |T₁ - T₂| := mul_le_mul_of_nonneg_right hM₂ (abs_nonneg _)
    linarith
  have h21 : finiteUnrestrictedDeficitEntropy alpha T₂ -
      finiteUnrestrictedDeficitEntropy alpha T₁ ≤ M_tilt * |T₁ - T₂| := by
    have hle := finiteUnrestrictedDeficitEntropy_le_at_tilt halpha hT₂
      (profileDeficitTilt alpha T₁)
    unfold finiteUnrestrictedDeficitEntropy at hle ⊢
    have hprod : profileDeficitTilt alpha T₁ * (T₁ - T₂) ≤ M_tilt * |T₁ - T₂| := by
      calc profileDeficitTilt alpha T₁ * (T₁ - T₂)
          ≤ |profileDeficitTilt alpha T₁ * (T₁ - T₂)| := le_abs_self _
        _ = |profileDeficitTilt alpha T₁| * |T₁ - T₂| := abs_mul _ _
        _ ≤ M_tilt * |T₁ - T₂| := mul_le_mul_of_nonneg_right hM₁ (abs_nonneg _)
    linarith
  exact abs_le.mpr ⟨by linarith, h12⟩

private theorem eventually_phaseRootCenter_sub_main_logLogRate :
    ∀ᶠ n : ℕ in atTop,
      phaseRootCenter n ≤ (n : ℝ) / logOrder n ∧
      |phaseRootCenter n - (Real.log 2 / 2) * ((n : ℝ) / logOrder n)| ≤
        4 * (n : ℝ) * logLogOrder n / (logOrder n) ^ 2 := by
  have hW_big : ∀ᶠ n : ℕ in atTop,
      max 1 (|2 * phaseC| + 4) ≤ logLogOrder n :=
    tendsto_logLogOrder_atTop.eventually_ge_atTop _
  have hWL_small : ∀ᶠ n : ℕ in atTop,
      ‖logLogOrder n‖ ≤ (1 / 6) * ‖logOrder n‖ :=
    logLogOrder_isLittleO_logOrder.bound (by norm_num)
  have hL_big : ∀ᶠ n : ℕ in atTop, 4 ≤ logOrder n :=
    tendsto_logOrder_atTop.eventually_ge_atTop 4
  filter_upwards [hW_big, hWL_small, hL_big,
    eventually_phaseRoot_domain_pos_and_target_corridor] with
    n hWn hWL hLn hcenterDom
  obtain ⟨hdom, hs0Pos, _⟩ := hcenterDom
  set L : ℝ := logOrder n
  set w : ℝ := logLogOrder n
  set s0 : ℝ := phaseRootS0 n
  have hL_pos : 0 < L := by linarith
  have hw_pos : 0 < w := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hWn)
  have hw_c : |2 * phaseC| + 4 ≤ w := (le_max_right _ _).trans hWn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_trans Nat.zero_lt_one hdom.1)
  rw [Real.norm_eq_abs, abs_of_pos hw_pos, Real.norm_eq_abs, abs_of_pos hL_pos] at hWL
  have hqs0 : q * s0 - 2 * L =
      -2 * w + 2 * phaseC + q * (phaseB n + phaseDelta n - 1) - 2 := by
    have hph : (phaseNat n : ℝ) * q = 2 * L - 2 * w + 2 * phaseC + q * phaseB n := by
      dsimp [L, w]
      rw [phaseNat_cast_eq_two_phaseS_div_q_add_phaseB hdom]
      unfold phaseS
      field_simp [q_ne_zero]
    dsimp [s0]
    rw [phaseRootS0, alphaZero_eq_phaseNat_add_delta hdom]
    field_simp [q_ne_zero]
    linarith
  have hqs0_abs : |q * s0 - 2 * L| ≤ 3 * w := by
    have hb_lo : -1 ≤ phaseB n + phaseDelta n - 1 := by
      linarith [phaseB_pos n, phaseDelta_nonneg n]
    have hb_hi : phaseB n + phaseDelta n - 1 ≤ 1 := by
      linarith [phaseB_le_one n, phaseDelta_lt_one n]
    have hqb_lo : -2 ≤ q * (phaseB n + phaseDelta n - 1) := by
      have := mul_le_mul_of_nonneg_left hb_lo q_pos.le
      unfold q at this ⊢
      linarith [Real.log_two_lt_d9]
    have hqb_hi : q * (phaseB n + phaseDelta n - 1) ≤ 2 := by
      have := mul_le_mul_of_nonneg_left hb_hi q_pos.le
      unfold q at this ⊢
      linarith [Real.log_two_lt_d9]
    have hc_bds := abs_le.mp (le_rfl : |2 * phaseC| ≤ |2 * phaseC|)
    rw [hqs0, abs_le]
    exact ⟨by linarith [hc_bds.1], by linarith [hc_bds.2]⟩
  have hqs0_lo : L ≤ q * s0 := by
    have h1 := (abs_le.mp hqs0_abs).1
    linarith
  have hs0_ge_L : L ≤ s0 := by
    have hq_le1 : q ≤ 1 := le_trans Real.log_two_lt_d9.le (by norm_num)
    have : q * s0 ≤ 1 * s0 := mul_le_mul_of_nonneg_right hq_le1 hs0Pos.le
    linarith
  have hc_le : phaseRootCenter n ≤ (n : ℝ) / L :=
    div_le_div_of_nonneg_left hn_pos.le hL_pos hs0_ge_L
  refine ⟨hc_le, ?_⟩
  have hdiff_c : phaseRootCenter n - (q / 2) * ((n : ℝ) / L) =
      (n : ℝ) * (2 * L - q * s0) / (2 * L * s0) := by
    change (n : ℝ) / s0 - (q / 2) * ((n : ℝ) / L) = _
    field_simp [hs0Pos.ne', hL_pos.ne']
  have hql2 : q = Real.log 2 := rfl
  rw [← hql2, hdiff_c, abs_div, abs_mul, abs_of_pos hn_pos,
    abs_of_pos (by positivity : 0 < 2 * L * s0), abs_sub_comm]
  calc (n : ℝ) * |q * s0 - 2 * L| / (2 * L * s0)
      ≤ (n : ℝ) * (3 * w) / (2 * L * (L / q)) := by
        have hLq_pos : 0 < 2 * L * (L / q) := mul_pos (mul_pos two_pos hL_pos) (div_pos hL_pos q_pos)
        refine div_le_div₀ (by positivity)
          (mul_le_mul_of_nonneg_left hqs0_abs hn_pos.le) hLq_pos ?_
        have hs0_ge_Lq : L / q ≤ s0 := (div_le_iff₀ q_pos).mpr (by rwa [mul_comm])
        exact mul_le_mul_of_nonneg_left hs0_ge_Lq (by positivity)
    _ = (3 * q / 2) * ((n : ℝ) * w / L ^ 2) := by
        field_simp [q_pos.ne', hL_pos.ne']
    _ ≤ 4 * ((n : ℝ) * w / L ^ 2) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        unfold q
        linarith [Real.log_two_lt_d9]
    _ = 4 * (n : ℝ) * w / L ^ 2 := by ring

private theorem corridor_root_separation_master
    {n : ℕ} {C K_slope M_tilt r₁ r₂ G₁ G₂ F₁_lim F₂_lim tau₁ tau₂ K_E B_H : ℝ}
    (hC : 0 ≤ C) (hM_tilt : 0 ≤ M_tilt) (_hK_E : 0 ≤ K_E)
    (hL_ge4 : 4 ≤ logOrder n) (hw_ge1 : 1 ≤ logLogOrder n)
    (hn_pos : 0 < (n : ℝ)) (hs0_pos : 0 < phaseRootS0 n) (hfive : 5 < phaseNat n)
    (hL_le_a : logOrder n ≤ (phaseNat n : ℝ))
    (hc_le : phaseRootCenter n ≤ (n : ℝ) / logOrder n)
    (hc_approx : |phaseRootCenter n - (Real.log 2 / 2) * ((n : ℝ) / logOrder n)| ≤
      4 * (n : ℝ) * logLogOrder n / (logOrder n) ^ 2)
    (hcorr_inv : ∀ s ∈ Set.Icc
        (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
        (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n),
      phaseRootCenter n / 2 ≤ s ∧ s ≤ 2 * phaseRootCenter n ∧
        |fourSizeTarget n (phaseNat n) s - phaseTarget (phaseDelta n)| ≤
          2 * C * logLogOrder n / logOrder n)
    (hdomain : ∀ s ∈ Set.Icc
        (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
        (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n),
      0 < s ∧ fourSizeTarget n (phaseNat n) s ∈ Set.Ioo (2 : ℝ) 5)
    (htilt_corr : ∀ s ∈ Set.Icc
        (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
        (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n),
      fourSizeTarget n (phaseNat n) s ∈ Set.Ioo (-1 : ℝ) ((phaseNat n : ℝ) - 1) ∧
        |profileDeficitTilt (phaseNat n) (fourSizeTarget n (phaseNat n) s)| ≤ M_tilt)
    (hslope : ∀ s ∈ Set.Icc
        (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
        (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n),
      |deriv (unrestrictedPhaseObjective n) s - (2 / Real.log 2) * (logOrder n) ^ 2| ≤
        K_slope * logOrder n * logLogOrder n)
    (hr₁ : r₁ ∈ Set.Icc
        (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
        (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n))
    (hr₂ : r₂ ∈ Set.Icc
        (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
        (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n))
    (heq₁ : unrestrictedPhaseObjective n r₁ =
      r₁ * (finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) r₁) -
        G₁ - tau₁))
    (heq₂ : unrestrictedPhaseObjective n r₂ =
      r₂ * (finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) r₂) -
        G₂ - tau₂))
    (hG₁_err : |G₁ - F₁_lim| ≤ K_E * logLogOrder n / logOrder n)
    (hG₂_err : |G₂ - F₂_lim| ≤ K_E * logLogOrder n / logOrder n)
    (hH₂_abs : |finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) r₂) -
        G₂ - tau₂| ≤ B_H)
    (hΔ_abs : |tau₂ - tau₁ + F₂_lim - F₁_lim| ≤ B_H)
    (hS_lower : (K_slope + B_H) * logOrder n * logLogOrder n ≤
      (1 / Real.log 2) * (logOrder n) ^ 2) :
    |(r₁ - r₂) - (Real.log 2) ^ 2 / 4 * (tau₂ - tau₁ + F₂_lim - F₁_lim) *
        ((n : ℝ) / (logOrder n) ^ 3)| ≤
      ((4 + C) * B_H + 4 * (K_E + 2 * C * M_tilt) + (K_slope + B_H) * B_H) *
        (n : ℝ) * logLogOrder n / (logOrder n) ^ 4 := by
  set L : ℝ := logOrder n
  set w : ℝ := logLogOrder n
  set c : ℝ := phaseRootCenter n
  set a : ℝ := (phaseNat n : ℝ)
  have hL_pos : 0 < L := by linarith
  have hw_pos : 0 < w := by linarith
  have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hq_le1 : Real.log 2 ≤ 1 := le_trans Real.log_two_lt_d9.le (by norm_num)
  have hc_pos : 0 < c := div_pos hn_pos hs0_pos
  have ha_ge6 : (6 : ℝ) ≤ a := by dsimp [a]; exact_mod_cast (Nat.succ_le_of_lt hfive)
  have ha_pos : 0 < a := by linarith
  have hB_H_nn : 0 ≤ B_H := (abs_nonneg _).trans hH₂_abs
  have hKeyU : ∀ x ∈ Set.Icc
      (c - C * w * phaseRootGapRadius n) (c + C * w * phaseRootGapRadius n),
      HasDerivAt (unrestrictedPhaseObjective n)
        (Real.log (profileDualPartition (phaseNat n + 1)
            (profileDualTilt (phaseNat n + 1) ((n : ℝ) / x))) - Real.log x) x := by
    intro x hx
    obtain ⟨hxpos, htar⟩ := hdomain x hx
    rw [fourSizeTarget, Set.mem_Ioo] at htar
    have ha6' : (6 : ℝ) ≤ (phaseNat n : ℝ) := ha_ge6
    exact hasDerivAt_profileDualOptimalValue_parts (by omega) hxpos (by
      rw [Set.mem_Ioo, show (((phaseNat n + 1 : ℕ) : ℝ)) = (phaseNat n : ℝ) + 1 by push_cast; ring]
      exact ⟨by linarith [htar.2, ha6'], by linarith [htar.1]⟩)
  have hmvt : ∃ ξ ∈ Set.Icc
      (c - C * w * phaseRootGapRadius n) (c + C * w * phaseRootGapRadius n),
      unrestrictedPhaseObjective n r₁ - unrestrictedPhaseObjective n r₂ =
        deriv (unrestrictedPhaseObjective n) ξ * (r₁ - r₂) := by
    rcases lt_trichotomy r₁ r₂ with hlt | rfl | hgt
    · have hsub : Set.Icc r₁ r₂ ⊆ Set.Icc
          (c - C * w * phaseRootGapRadius n) (c + C * w * phaseRootGapRadius n) :=
        fun x hx ↦ ⟨hr₁.1.trans hx.1, hx.2.trans hr₂.2⟩
      obtain ⟨ξ, hξ_ioo, hξ_eq⟩ := exists_deriv_eq_slope (unrestrictedPhaseObjective n) hlt
        (fun x hx ↦ (hKeyU x (hsub hx)).continuousAt.continuousWithinAt)
        (fun x hx ↦ (hKeyU x (hsub (Ioo_subset_Icc_self hx))).differentiableAt.differentiableWithinAt)
      refine ⟨ξ, hsub (Ioo_subset_Icc_self hξ_ioo), ?_⟩
      have hne : r₂ - r₁ ≠ 0 := sub_ne_zero.mpr hlt.ne'
      rw [hξ_eq]; field_simp [hne]; ring
    · exact ⟨r₁, hr₁, by simp⟩
    · have hsub : Set.Icc r₂ r₁ ⊆ Set.Icc
          (c - C * w * phaseRootGapRadius n) (c + C * w * phaseRootGapRadius n) :=
        fun x hx ↦ ⟨hr₂.1.trans hx.1, hx.2.trans hr₁.2⟩
      obtain ⟨ξ, hξ_ioo, hξ_eq⟩ := exists_deriv_eq_slope (unrestrictedPhaseObjective n) hgt
        (fun x hx ↦ (hKeyU x (hsub hx)).continuousAt.continuousWithinAt)
        (fun x hx ↦ (hKeyU x (hsub (Ioo_subset_Icc_self hx))).differentiableAt.differentiableWithinAt)
      refine ⟨ξ, hsub (Ioo_subset_Icc_self hξ_ioo), ?_⟩
      have hne : r₁ - r₂ ≠ 0 := sub_ne_zero.mpr hgt.ne'
      rw [hξ_eq]; field_simp [hne]
  rcases hmvt with ⟨ξ, hξ_mem, hξ_mvt⟩
  set T₁ : ℝ := fourSizeTarget n (phaseNat n) r₁
  set T₂ : ℝ := fourSizeTarget n (phaseNat n) r₂
  set H₁ : ℝ := finiteUnrestrictedDeficitEntropy (phaseNat n) T₁ - G₁ - tau₁
  set H₂ : ℝ := finiteUnrestrictedDeficitEntropy (phaseNat n) T₂ - G₂ - tau₂
  set S_ξ : ℝ := deriv (unrestrictedPhaseObjective n) ξ
  set S' : ℝ := S_ξ - H₂
  set S₀ : ℝ := (2 / Real.log 2) * L ^ 2
  set r₀ : ℝ := (Real.log 2 / 2) * ((n : ℝ) / L)
  set Δ_main : ℝ := tau₂ - tau₁ + F₂_lim - F₁_lim
  have hlin_eq : S' * (r₁ - r₂) = r₁ * (H₁ - H₂) := by
    dsimp [S', S_ξ, H₁, H₂]
    linarith [hξ_mvt, heq₁, heq₂]
  have hS'_err : |S' - S₀| ≤ (K_slope + B_H) * L * w := by
    have hs1 := hslope ξ hξ_mem
    have h1 : |S' - S₀| ≤ |S_ξ - S₀| + |H₂| := by
      have := abs_sub (S_ξ - S₀) H₂
      simpa [S', sub_right_comm] using this
    have hLw_ge1 : 1 ≤ L * w := by nlinarith
    have hB_le : |H₂| ≤ B_H * (L * w) :=
      hH₂_abs.trans (le_mul_of_one_le_right hB_H_nn hLw_ge1)
    dsimp [S₀, L, w] at hs1 ⊢
    linarith
  have hS'_lo : (1 / Real.log 2) * L ^ 2 ≤ S' := by
    have hl := (abs_le.mp hS'_err).1
    have hsub_S : S₀ - (1 / Real.log 2) * L ^ 2 = (1 / Real.log 2) * L ^ 2 := by
      dsimp [S₀]; ring
    have hs_l : (K_slope + B_H) * L * w ≤ (1 / Real.log 2) * L ^ 2 := hS_lower
    linarith
  have hS'_pos : 0 < S' := lt_of_lt_of_le (by positivity) hS'_lo
  have hr₁_pos : 0 < r₁ := (hdomain r₁ hr₁).1
  have hr₁_le : r₁ ≤ 2 * ((n : ℝ) / L) := by
    calc r₁ ≤ 2 * c := (hcorr_inv r₁ hr₁).2.1
      _ ≤ 2 * ((n : ℝ) / L) := mul_le_mul_of_nonneg_left hc_le zero_le_two
  have hr₁_c_abs : |r₁ - c| ≤ C * (n : ℝ) * w / L ^ 2 := by
    have habs_rc : |r₁ - c| ≤ C * w * (c / a ^ 2) := by
      rw [abs_le]
      have hgap : phaseRootGapRadius n = c / a ^ 2 := rfl
      have hr₁' : c - C * w * (c / a ^ 2) ≤ r₁ ∧ r₁ ≤ c + C * w * (c / a ^ 2) := by
        simpa only [c, w, hgap, Set.mem_Icc] using hr₁
      exact ⟨by linarith [hr₁'.1], by linarith [hr₁'.2]⟩
    have ha_sq_ge : L ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hL_pos.le hL_le_a 2
    have hca_le : c / a ^ 2 ≤ ((n : ℝ) / L) / L ^ 2 := by
      calc c / a ^ 2 ≤ c / L ^ 2 := div_le_div_of_nonneg_left hc_pos.le (sq_pos_of_pos hL_pos) ha_sq_ge
        _ ≤ ((n : ℝ) / L) / L ^ 2 := div_le_div_of_nonneg_right hc_le (sq_nonneg _)
    calc |r₁ - c| ≤ C * w * (((n : ℝ) / L) / L ^ 2) :=
          habs_rc.trans (mul_le_mul_of_nonneg_left hca_le (by positivity))
      _ ≤ C * w * ((n : ℝ) / L ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hL1 : 1 ≤ L := by linarith
          calc ((n : ℝ) / L) / L ^ 2 = (n : ℝ) / (L ^ 2 * L) := by ring
            _ ≤ (n : ℝ) / (L ^ 2 * 1) :=
                div_le_div_of_nonneg_left hn_pos.le (by positivity)
                  (mul_le_mul_of_nonneg_left hL1 (sq_nonneg _))
            _ = (n : ℝ) / L ^ 2 := by ring
      _ = C * (n : ℝ) * w / L ^ 2 := by ring
  have hr₁_r₀ : |r₁ - r₀| ≤ (4 + C) * (n : ℝ) * w / L ^ 2 := by
    calc |r₁ - r₀| = |(r₁ - c) + (c - r₀)| := by ring_nf
      _ ≤ |r₁ - c| + |c - r₀| := abs_add_le _ _
      _ ≤ C * (n : ℝ) * w / L ^ 2 + 4 * (n : ℝ) * w / L ^ 2 :=
          add_le_add hr₁_c_abs hc_approx
      _ = (4 + C) * (n : ℝ) * w / L ^ 2 := by ring
  have hT_diff : |T₁ - T₂| ≤ 4 * C * w / L := by
    have ht1 := (hcorr_inv r₁ hr₁).2.2
    have ht2 := (hcorr_inv r₂ hr₂).2.2
    calc |T₁ - T₂| = |(T₁ - phaseTarget (phaseDelta n)) - (T₂ - phaseTarget (phaseDelta n))| := by
          ring_nf
      _ ≤ |T₁ - phaseTarget (phaseDelta n)| + |T₂ - phaseTarget (phaseDelta n)| := abs_sub _ _
      _ ≤ 2 * C * w / L + 2 * C * w / L := add_le_add ht1 ht2
      _ = 4 * C * w / L := by ring
  have halpha_pos : 0 < phaseNat n := by
    have : (0 : ℝ) < (phaseNat n : ℝ) := ha_pos
    exact_mod_cast this
  have hUnrest_diff :
      |finiteUnrestrictedDeficitEntropy (phaseNat n) T₁ -
          finiteUnrestrictedDeficitEntropy (phaseNat n) T₂| ≤
        4 * C * M_tilt * w / L := by
    have hu := abs_finiteUnrestrictedDeficitEntropy_sub_le halpha_pos
      (htilt_corr r₁ hr₁).1 (htilt_corr r₂ hr₂).1
      (htilt_corr r₁ hr₁).2 (htilt_corr r₂ hr₂).2
    calc |finiteUnrestrictedDeficitEntropy (phaseNat n) T₁ -
            finiteUnrestrictedDeficitEntropy (phaseNat n) T₂|
        ≤ M_tilt * (4 * C * w / L) := hu.trans (mul_le_mul_of_nonneg_left hT_diff hM_tilt)
      _ = 4 * C * M_tilt * w / L := by ring
  have hH_err : |(H₁ - H₂) - Δ_main| ≤ (2 * K_E + 4 * C * M_tilt) * w / L := by
    have hrew_H : (H₁ - H₂) - Δ_main =
        (finiteUnrestrictedDeficitEntropy (phaseNat n) T₁ -
          finiteUnrestrictedDeficitEntropy (phaseNat n) T₂) -
        (G₁ - F₁_lim) + (G₂ - F₂_lim) := by
      dsimp [H₁, H₂, Δ_main]; ring
    rw [hrew_H]
    calc |(finiteUnrestrictedDeficitEntropy (phaseNat n) T₁ -
            finiteUnrestrictedDeficitEntropy (phaseNat n) T₂) -
            (G₁ - F₁_lim) + (G₂ - F₂_lim)|
        ≤ |finiteUnrestrictedDeficitEntropy (phaseNat n) T₁ -
            finiteUnrestrictedDeficitEntropy (phaseNat n) T₂| +
          |G₁ - F₁_lim| + |G₂ - F₂_lim| := by
          linarith [abs_add_le
              ((finiteUnrestrictedDeficitEntropy (phaseNat n) T₁ -
                finiteUnrestrictedDeficitEntropy (phaseNat n) T₂) - (G₁ - F₁_lim))
              (G₂ - F₂_lim),
            abs_sub
              (finiteUnrestrictedDeficitEntropy (phaseNat n) T₁ -
                finiteUnrestrictedDeficitEntropy (phaseNat n) T₂)
              (G₁ - F₁_lim)]
      _ ≤ 4 * C * M_tilt * w / L + K_E * w / L + K_E * w / L :=
          add_le_add (add_le_add hUnrest_diff hG₁_err) hG₂_err
      _ = (2 * K_E + 4 * C * M_tilt) * w / L := by ring
  set main_term : ℝ := (Real.log 2) ^ 2 / 4 * Δ_main * ((n : ℝ) / L ^ 3)
  have hS₀_mul_main : S₀ * main_term = r₀ * Δ_main := by
    dsimp [S₀, main_term, r₀]
    field_simp [hq_pos.ne', hL_pos.ne']
    ring
  have hprod_id : S' * ((r₁ - r₂) - main_term) =
      (r₁ - r₀) * Δ_main + r₁ * ((H₁ - H₂) - Δ_main) - (S' - S₀) * main_term := by
    calc S' * ((r₁ - r₂) - main_term)
        = S' * (r₁ - r₂) - S₀ * main_term - (S' - S₀) * main_term := by ring
      _ = r₁ * (H₁ - H₂) - r₀ * Δ_main - (S' - S₀) * main_term := by
          rw [hlin_eq, hS₀_mul_main]
      _ = (r₁ - r₀) * Δ_main + r₁ * ((H₁ - H₂) - Δ_main) - (S' - S₀) * main_term := by ring
  have hterm1 : |(r₁ - r₀) * Δ_main| ≤ (4 + C) * B_H * ((n : ℝ) * w / L ^ 2) := by
    rw [abs_mul]
    calc |r₁ - r₀| * |Δ_main|
        ≤ ((4 + C) * (n : ℝ) * w / L ^ 2) * B_H :=
          mul_le_mul hr₁_r₀ hΔ_abs (abs_nonneg _) (by positivity)
      _ = (4 + C) * B_H * ((n : ℝ) * w / L ^ 2) := by ring
  have hterm2 : |r₁ * ((H₁ - H₂) - Δ_main)| ≤
      4 * (K_E + 2 * C * M_tilt) * ((n : ℝ) * w / L ^ 2) := by
    rw [abs_mul, abs_of_pos hr₁_pos]
    calc r₁ * |(H₁ - H₂) - Δ_main|
        ≤ (2 * ((n : ℝ) / L)) * ((2 * K_E + 4 * C * M_tilt) * w / L) :=
          mul_le_mul hr₁_le hH_err (abs_nonneg _) (by positivity)
      _ = 4 * (K_E + 2 * C * M_tilt) * ((n : ℝ) * w / L ^ 2) := by ring
  have hterm3 : |(S' - S₀) * main_term| ≤
      (K_slope + B_H) * B_H * ((n : ℝ) * w / L ^ 2) := by
    have hmain_abs : |main_term| ≤ B_H * ((n : ℝ) / L ^ 3) := by
      dsimp [main_term]
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < (Real.log 2) ^ 2 / 4),
        abs_of_pos (by positivity : 0 < (n : ℝ) / L ^ 3)]
      have hq24_le1 : (Real.log 2) ^ 2 / 4 ≤ 1 := by
        have : (Real.log 2) ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ hq_pos.le hq_le1 2
        linarith
      calc (Real.log 2) ^ 2 / 4 * |Δ_main| * ((n : ℝ) / L ^ 3)
          ≤ 1 * B_H * ((n : ℝ) / L ^ 3) := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul hq24_le1 hΔ_abs (abs_nonneg _) zero_le_one) (by positivity)
        _ = B_H * ((n : ℝ) / L ^ 3) := by ring
    rw [abs_mul]
    have hKS_nn : 0 ≤ K_slope + B_H :=
      nonneg_of_mul_nonneg_left
        (nonneg_of_mul_nonneg_left ((abs_nonneg _).trans hS'_err) hw_pos) hL_pos
    calc |S' - S₀| * |main_term|
        ≤ ((K_slope + B_H) * L * w) * (B_H * ((n : ℝ) / L ^ 3)) :=
          mul_le_mul hS'_err hmain_abs (abs_nonneg _) (by positivity)
      _ = (K_slope + B_H) * B_H * ((n : ℝ) * w / L ^ 2) := by
          field_simp [hL_pos.ne']
  have hnum_bound : |S' * ((r₁ - r₂) - main_term)| ≤
      ((4 + C) * B_H + 4 * (K_E + 2 * C * M_tilt) + (K_slope + B_H) * B_H) *
        ((n : ℝ) * w / L ^ 2) := by
    rw [hprod_id]
    have htri :
        |(r₁ - r₀) * Δ_main + r₁ * ((H₁ - H₂) - Δ_main) - (S' - S₀) * main_term| ≤
          |(r₁ - r₀) * Δ_main| + |r₁ * ((H₁ - H₂) - Δ_main)| + |(S' - S₀) * main_term| := by
      linarith [abs_sub ((r₁ - r₀) * Δ_main + r₁ * ((H₁ - H₂) - Δ_main)) ((S' - S₀) * main_term),
        abs_add_le ((r₁ - r₀) * Δ_main) (r₁ * ((H₁ - H₂) - Δ_main))]
    linarith
  rw [abs_mul, abs_of_pos hS'_pos] at hnum_bound
  have hdiv_S' : |(r₁ - r₂) - main_term| ≤
      (((4 + C) * B_H + 4 * (K_E + 2 * C * M_tilt) + (K_slope + B_H) * B_H) *
        ((n : ℝ) * w / L ^ 2)) / ((1 / Real.log 2) * L ^ 2) := by
    calc |(r₁ - r₂) - main_term|
        ≤ (((4 + C) * B_H + 4 * (K_E + 2 * C * M_tilt) + (K_slope + B_H) * B_H) *
            ((n : ℝ) * w / L ^ 2)) / S' := (le_div_iff₀' hS'_pos).mpr hnum_bound
      _ ≤ (((4 + C) * B_H + 4 * (K_E + 2 * C * M_tilt) + (K_slope + B_H) * B_H) *
            ((n : ℝ) * w / L ^ 2)) / ((1 / Real.log 2) * L ^ 2) :=
          div_le_div_of_nonneg_left ((mul_nonneg hS'_pos.le (abs_nonneg _)).trans hnum_bound)
            (by positivity) hS'_lo
  refine hdiv_S'.trans ?_
  have hcoeff_nn : 0 ≤ (4 + C) * B_H + 4 * (K_E + 2 * C * M_tilt) + (K_slope + B_H) * B_H := by
    have hnum_nn : 0 ≤ ((4 + C) * B_H + 4 * (K_E + 2 * C * M_tilt) + (K_slope + B_H) * B_H) *
        ((n : ℝ) * w / L ^ 2) := (mul_nonneg hS'_pos.le (abs_nonneg _)).trans hnum_bound
    exact nonneg_of_mul_nonneg_left hnum_nn (by positivity)
  have hrew_rhs :
      (((4 + C) * B_H + 4 * (K_E + 2 * C * M_tilt) + (K_slope + B_H) * B_H) *
        ((n : ℝ) * w / L ^ 2)) / ((1 / Real.log 2) * L ^ 2) =
      Real.log 2 * (((4 + C) * B_H + 4 * (K_E + 2 * C * M_tilt) + (K_slope + B_H) * B_H) *
        (n : ℝ) * w / L ^ 4) := by
    field_simp [hq_pos.ne', hL_pos.ne']
  rw [hrew_rhs]
  calc Real.log 2 * (((4 + C) * B_H + 4 * (K_E + 2 * C * M_tilt) + (K_slope + B_H) * B_H) *
          (n : ℝ) * w / L ^ 4)
      ≤ 1 * (((4 + C) * B_H + 4 * (K_E + 2 * C * M_tilt) + (K_slope + B_H) * B_H) *
          (n : ℝ) * w / L ^ 4) :=
        mul_le_mul_of_nonneg_right hq_le1 (by positivity)
    _ = ((4 + C) * B_H + 4 * (K_E + 2 * C * M_tilt) + (K_slope + B_H) * B_H) *
          (n : ℝ) * w / L ^ 4 := one_mul _

private theorem eventually_capped_corridorRoot_separation_aux
    {M : ℕ} (C : ℝ) (hC : 0 ≤ C) :
    ∃ K_sep : ℝ, 0 < K_sep ∧ ∀ᶠ n : ℕ in atTop,
      (8 ≤ M → phaseDelta n ∈ Set.Icc (0 : ℝ) deltaStar →
        ∀ (M₁ M₂ : ℕ), 8 ≤ M₁ → M₁ ≤ M → 8 ≤ M₂ → M₂ ≤ M →
          ∀ theta₁ ∈ Set.Icc (0 : ℝ) (1 / 20),
            ∀ theta₂ ∈ Set.Icc (0 : ℝ) (1 / 20),
              ∀ tau₁ ∈ Set.Icc (0 : ℝ) (Real.log 2),
                ∀ tau₂ ∈ Set.Icc (0 : ℝ) (Real.log 2),
                  let obj₁ : ℝ → ℝ := fun s ↦
                    (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + s - s * Real.log s +
                      s * (profileDeficitAffineA (phaseNat n) +
                        profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s +
                        (binEntropy theta₁ - Real.log 2 / 2 * theta₁ +
                          (1 - theta₁) * (⨅ l : ℝ,
                            (Real.log (∑ i ∈ Finset.Icc 2 M₁,
                                Real.exp (l * (i : ℝ) +
                                  (Real.log ((phaseNat n).descFactorial i : ℝ) -
                                    (i : ℝ) * Real.log (phaseNat n : ℝ) -
                                    Real.log 2 / 2 * (i : ℝ) ^ 2))) -
                              l * ((fourSizeTarget n (phaseNat n) s - theta₁) / (1 - theta₁))))) +
                        tau₁)
                  let obj₂ : ℝ → ℝ := fun s ↦
                    (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + s - s * Real.log s +
                      s * (profileDeficitAffineA (phaseNat n) +
                        profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s +
                        (binEntropy theta₂ - Real.log 2 / 2 * theta₂ +
                          (1 - theta₂) * (⨅ l : ℝ,
                            (Real.log (∑ i ∈ Finset.Icc 2 M₂,
                                Real.exp (l * (i : ℝ) +
                                  (Real.log ((phaseNat n).descFactorial i : ℝ) -
                                    (i : ℝ) * Real.log (phaseNat n : ℝ) -
                                    Real.log 2 / 2 * (i : ℝ) ^ 2))) -
                              l * ((fourSizeTarget n (phaseNat n) s - theta₂) / (1 - theta₂))))) +
                        tau₂)
                  ∀ r₁ ∈ Set.Icc (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
                                 (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n),
                    ∀ r₂ ∈ Set.Icc (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
                                   (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n),
                      obj₁ r₁ = 0 → obj₂ r₂ = 0 →
                        |(r₁ - r₂) - (Real.log 2) ^ 2 / 4 *
                            (tau₂ - tau₁ +
                              cappedDualValue (S0M M₂) theta₂ (phaseTarget (phaseDelta n)) -
                              cappedDualValue (S0M M₁) theta₁ (phaseTarget (phaseDelta n))) *
                            ((n : ℝ) / (Real.log (n : ℝ)) ^ 3)| ≤
                          K_sep * (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ 4) := by
  obtain ⟨K_slope, hK_slope_pos, hSlopeEv⟩ := eventually_unrestrictedPhaseObjective_deriv_logLogRate C hC
  obtain ⟨Mtilt, hMtilt_nn, huniformTilt⟩ :=
    exists_eventually_forall_mem_Icc_abs_profileDeficitTilt_le
      (by norm_num : (-1 : ℝ) < 9 / 4) (by norm_num : (9 / 4 : ℝ) ≤ 17 / 4)
  obtain ⟨Ntilt, hNtilt⟩ := eventually_atTop.1 huniformTilt
  set K_E : ℝ := ((1 + M : ℕ) : ℝ) ^ 2 + 2 * C * universalDualLip
  set B_F0 : ℝ := |Real.log (partitionFn Splus 0)| +
    |min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))| + Real.log 2 + 1
  set B_H : ℝ := 5 * Mtilt + |Real.log (partitionFn Splus 0)| + 2 * B_F0 + 2 * Real.log 2 + 2
  set K_sep : ℝ := (4 + C) * B_H + 4 * (K_E + 2 * C * Mtilt) + (K_slope + B_H) * B_H + 1
  have hK_E_nn : 0 ≤ K_E := by
    have := universalDualLip_nonneg
    dsimp [K_E]; positivity
  have hB_F0_nn : 0 ≤ B_F0 := by
    dsimp [B_F0]; linarith [Real.log_pos one_lt_two,
      abs_nonneg (Real.log (partitionFn Splus 0)),
      abs_nonneg (min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8)))]
  have hB_H_nn : 0 ≤ B_H := by
    dsimp [B_H]; linarith [Real.log_pos one_lt_two, abs_nonneg (Real.log (partitionFn Splus 0))]
  have hK_sep_pos : 0 < K_sep := by dsimp [K_sep]; positivity
  refine ⟨K_sep, hK_sep_pos, ?_⟩
  have hphaseN : ∀ᶠ n : ℕ in atTop, max Ntilt (2 * (1 + M)) ≤ phaseNat n := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop ((max Ntilt (2 * (1 + M)) : ℕ) : ℝ),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact_mod_cast hn.trans hph.1
  have hS_small : ∀ᶠ n : ℕ in atTop,
      ‖logLogOrder n‖ ≤
        min (1 / (Real.log 2 * (K_slope + B_H + 1))) (1 / (K_E + 1)) * ‖logOrder n‖ :=
    logLogOrder_isLittleO_logOrder.bound (lt_min
      (by have := Real.log_pos one_lt_two; positivity)
      (by positivity))
  have hW1 : ∀ᶠ n : ℕ in atTop, 1 ≤ logLogOrder n :=
    tendsto_logLogOrder_atTop.eventually_ge_atTop 1
  have hL4 : ∀ᶠ n : ℕ in atTop, 4 ≤ logOrder n :=
    tendsto_logOrder_atTop.eventually_ge_atTop 4
  filter_upwards [hSlopeEv, hphaseN, hS_small, hW1, hL4,
    eventually_phaseRootCenter_sub_main_logLogRate,
    eventually_corridor_inv_target_logLogRate C hC,
    eventually_phaseRootLogLogCorridor_fourSize_domain C hC,
    eventually_phaseRootLogLogCorridor_fourSize_target_mem_Icc C hC,
    eventually_cappedWindow_target_mem_KcapInterval C hC,
    eventually_phaseRoot_domain_pos_and_target_corridor,
    eventually_five_lt_phaseNat,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with
    n hSlope hphN hSsm hWn hLn hcMain hInv hDom hTarget hKcap hcenterDom hfive hphase
  set L : ℝ := logOrder n
  set w : ℝ := logLogOrder n
  have hL_pos : 0 < L := by linarith
  have hw_pos : 0 < w := lt_of_lt_of_le zero_lt_one hWn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_trans Nat.zero_lt_one hcenterDom.1.1)
  rw [Real.norm_eq_abs, abs_of_pos hw_pos, Real.norm_eq_abs, abs_of_pos hL_pos] at hSsm
  have hSsm1 : w ≤ (1 / (Real.log 2 * (K_slope + B_H + 1))) * L :=
    hSsm.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hL_pos.le)
  have hSsm2 : w ≤ (1 / (K_E + 1)) * L :=
    hSsm.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hL_pos.le)
  have hS_lower : (K_slope + B_H) * L * w ≤ (1 / Real.log 2) * L ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hSsm1
      (show (0 : ℝ) ≤ (K_slope + B_H + 1) * L by positivity)
    have hrhs : (K_slope + B_H + 1) * L *
        (1 / (Real.log 2 * (K_slope + B_H + 1)) * L) = (1 / Real.log 2) * L ^ 2 := by
      field_simp [(Real.log_pos one_lt_two).ne',
        (show (0 : ℝ) < K_slope + B_H + 1 by positivity).ne']
    have hlhs : (K_slope + B_H) * L * w ≤ (K_slope + B_H + 1) * L * w := by
      have : 0 ≤ L * w := mul_nonneg hL_pos.le hw_pos.le
      linarith
    linarith
  have hKE_le1 : K_E * w / L ≤ 1 := by
    rw [div_le_iff₀ hL_pos, one_mul]
    have hm := mul_le_mul_of_nonneg_left hSsm2 (show (0 : ℝ) ≤ K_E + 1 by positivity)
    have hrhs : (K_E + 1) * (1 / (K_E + 1) * L) = L := by
      field_simp [(show (0 : ℝ) < K_E + 1 by positivity).ne']
    have hexp : (K_E + 1) * w = K_E * w + w := by ring
    linarith [hw_pos]
  have htilt_corr : ∀ s ∈ Set.Icc
      (phaseRootCenter n - C * w * phaseRootGapRadius n)
      (phaseRootCenter n + C * w * phaseRootGapRadius n),
      fourSizeTarget n (phaseNat n) s ∈ Set.Ioo (-1 : ℝ) ((phaseNat n : ℝ) - 1) ∧
        |profileDeficitTilt (phaseNat n) (fourSizeTarget n (phaseNat n) s)| ≤ Mtilt := by
    intro s hs
    exact hNtilt (phaseNat n) ((le_max_left _ _).trans hphN) _ (hTarget s hs)
  have hslope0 : ∀ s ∈ Set.Icc
      (phaseRootCenter n - C * w * phaseRootGapRadius n)
      (phaseRootCenter n + C * w * phaseRootGapRadius n),
      |deriv (unrestrictedPhaseObjective n) s - (2 / Real.log 2) * L ^ 2| ≤
        K_slope * L * w := by
    intro s hs
    have h0 := hSlope 0 ⟨le_rfl, (Real.log_pos one_lt_two).le⟩ s hs
    simpa only [zero_mul, add_zero, L, w, logOrder, logLogOrder] using h0
  have hUnrestAbs : ∀ s ∈ Set.Icc
      (phaseRootCenter n - C * w * phaseRootGapRadius n)
      (phaseRootCenter n + C * w * phaseRootGapRadius n),
      |finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) s)| ≤
        5 * Mtilt + |Real.log (partitionFn Splus 0)| := by
    intro s hs
    set T : ℝ := fourSizeTarget n (phaseNat n) s
    have hTK : T ∈ Set.Icc (9 / 4 : ℝ) (17 / 4) := hTarget s hs
    have hT25 : T ∈ Set.Ioo (2 : ℝ) 5 := ⟨by linarith [hTK.1], by linarith [hTK.2]⟩
    have hHi : finiteUnrestrictedDeficitEntropy (phaseNat n) T ≤
        |Real.log (partitionFn Splus 0)| := by
      have h1 := (finiteProfileDeficitEntropy_le_extendedGaussianEntropyValue
        (phaseNat n) hfive hT25).trans (extendedGaussianEntropyValue_le_dualValue_Splus hT25)
      have hm4 := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT25)
      have h2 := dualValue_le_at S4_subset_Splus hm4 0
      unfold finiteUnrestrictedDeficitEntropy
      linarith [le_abs_self (Real.log (partitionFn Splus 0))]
    have hLo : -(5 * Mtilt) ≤ finiteUnrestrictedDeficitEntropy (phaseNat n) T := by
      obtain ⟨_, htiltB⟩ := htilt_corr s hs
      have hp1 := one_le_profileDeficitPartition (phaseNat n) (by omega)
        (profileDeficitTilt (phaseNat n) T)
      have hlognn := Real.log_nonneg hp1
      have hmul : |profileDeficitTilt (phaseNat n) T * T| ≤ 5 * Mtilt := by
        rw [abs_mul, abs_of_pos (by linarith [hTK.1] : 0 < T)]
        have := mul_le_mul htiltB (show T ≤ 5 by linarith [hTK.2]) (by linarith [hTK.1]) hMtilt_nn
        linarith
      unfold finiteUnrestrictedDeficitEntropy
      linarith [(abs_le.mp hmul).2]
    exact abs_le.mpr ⟨by linarith [abs_nonneg (Real.log (partitionFn Splus 0))],
      by linarith [hMtilt_nn]⟩
  have hObjZero_to_eq : ∀ {s G tau : ℝ}, 0 < s →
      (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + s - s * Real.log s +
        s * (profileDeficitAffineA (phaseNat n) +
          profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s + G + tau) = 0 →
      unrestrictedPhaseObjective n s =
        s * (finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) s) -
          G - tau) := by
    intro s G tau hspos hzero
    have hu := unrestrictedPhaseObjective_div_eq_deficitCentered n hspos.ne'
    have huMul : unrestrictedPhaseObjective n s =
        s * ((n : ℝ) * Real.log (n : ℝ) / s - (n : ℝ) / s + 1 - Real.log s +
          (profileDeficitAffineA (phaseNat n) +
            profileDeficitAffineB (phaseNat n) * profileDeficitTarget (phaseNat n) (n : ℝ) s +
            finiteUnrestrictedDeficitEntropy (phaseNat n)
              (profileDeficitTarget (phaseNat n) (n : ℝ) s))) := by
      rw [div_eq_iff hspos.ne'] at hu
      unfold finiteUnrestrictedDeficitEntropy
      linarith
    rw [huMul]
    have hzero' :
        s * ((n : ℝ) * Real.log (n : ℝ) / s - (n : ℝ) / s + 1 - Real.log s +
          (profileDeficitAffineA (phaseNat n) +
            profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s + G + tau)) = 0 := by
      have : s * ((n : ℝ) * Real.log (n : ℝ) / s - (n : ℝ) / s + 1 - Real.log s +
          (profileDeficitAffineA (phaseNat n) +
            profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s + G + tau)) =
        (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + s - s * Real.log s +
          s * (profileDeficitAffineA (phaseNat n) +
            profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s + G + tau) := by
        field_simp [hspos.ne']
      rw [this, hzero]
    change _ = s * (finiteUnrestrictedDeficitEntropy (phaseNat n)
      (profileDeficitTarget (phaseNat n) (n : ℝ) s) - G - tau)
    have hft : fourSizeTarget n (phaseNat n) s = profileDeficitTarget (phaseNat n) (n : ℝ) s := rfl
    rw [hft] at hzero'
    linarith
  intro _hM8 hd
  have hTd_cap : phaseTarget (phaseDelta n) ∈ KcapInterval := by
    unfold deltaStar at hd
    unfold phaseTarget KcapInterval
    exact ⟨by linarith [hd.2], by linarith [hd.1]⟩
  have hCapAbs : ∀ {M' : ℕ} {th : ℝ}, 8 ≤ M' → th ∈ Set.Icc (0 : ℝ) (1 / 20) →
      |cappedDualValue (S0M M') th (phaseTarget (phaseDelta n))| ≤ B_F0 := by
    intro M' th hM'8 hth
    have hu_icc := (reducedTarget_mem_Icc_and_Ioo hth hTd_cap).1
    have hd_win := dualValue_window_bounds_on_padded (m := 1) (M := M' - 1)
      le_rfl (by omega) ((phaseTarget (phaseDelta n) - th) / (1 - th))
      ⟨by linarith [hu_icc.1], by linarith [hu_icc.2]⟩
    have hbin := binEntropy_bounds_Icc ⟨hth.1, by linarith [hth.2]⟩
    have h1m_pos : 0 < 1 - th := by linarith [hth.2]
    have h1m_le1 : 1 - th ≤ 1 := by linarith [hth.1]
    unfold cappedDualValue
    rw [s0m_diff_one_eq_windowSupportSet (by omega : 2 ≤ M')]
    have htail_abs :
        |(1 - th) * dualValue (windowSupportSet 1 (M' - 1))
          ((phaseTarget (phaseDelta n) - th) / (1 - th))| ≤
        |Real.log (partitionFn Splus 0)| +
          |min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))| := by
      rw [abs_mul, abs_of_pos h1m_pos]
      have hw_abs :
          |dualValue (windowSupportSet 1 (M' - 1))
            ((phaseTarget (phaseDelta n) - th) / (1 - th))| ≤
          |Real.log (partitionFn Splus 0)| +
            |min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))| := by
        rw [abs_le]
        exact ⟨by linarith [hd_win.1,
            neg_abs_le (min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))),
            abs_nonneg (Real.log (partitionFn Splus 0))],
          by linarith [hd_win.2, le_abs_self (Real.log (partitionFn Splus 0)),
            abs_nonneg (min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8)))]⟩
      exact (mul_le_mul_of_nonneg_right h1m_le1 (abs_nonneg _)).trans (by simpa using hw_abs)
    have hq_th : Real.log 2 / 2 * th ≤ Real.log 2 := by
      have := mul_le_mul_of_nonneg_left hth.2 (div_pos (Real.log_pos one_lt_two) two_pos).le
      linarith [Real.log_pos one_lt_two]
    have hq_th_nn : 0 ≤ Real.log 2 / 2 * th :=
      mul_nonneg (div_nonneg (Real.log_pos one_lt_two).le zero_le_two) hth.1
    rw [abs_le]
    dsimp [B_F0]
    exact ⟨by linarith [hbin.1, hq_th, (abs_le.mp htail_abs).1],
      by linarith [hbin.2, hq_th_nn, (abs_le.mp htail_abs).2, Real.log_pos one_lt_two]⟩
  have hCapErr : ∀ {M' : ℕ} {th r : ℝ}, 8 ≤ M' → M' ≤ M → th ∈ Set.Icc (0 : ℝ) (1 / 20) →
      r ∈ Set.Icc (phaseRootCenter n - C * w * phaseRootGapRadius n)
                  (phaseRootCenter n + C * w * phaseRootGapRadius n) →
      |cappedWindowFiniteEntropy (phaseNat n) M' th (fourSizeTarget n (phaseNat n) r) -
          cappedDualValue (S0M M') th (phaseTarget (phaseDelta n))| ≤ K_E * w / L := by
    intro M' th r hM'8 hM'M hth hr
    set Tr : ℝ := fourSizeTarget n (phaseNat n) r
    have hTr_cap : Tr ∈ KcapInterval := hKcap hd r hr
    have halpha : 2 * M' ≤ phaseNat n := by
      have := (le_max_right Ntilt (2 * (1 + M))).trans hphN; omega
    have herr1_raw := cappedWindowFiniteEntropy_bounds hM'8 halpha hth hTr_cap
    have herr2 := (abs_cappedDualValue_S0M_sub_le hM'8 hth hTr_cap hTd_cap).trans
      (mul_le_mul_of_nonneg_left (hInv.2 r hr).2.2.2 universalDualLip_nonneg)
    have hsq_le : (M' : ℝ) ^ 2 / (phaseNat n : ℝ) ≤ ((1 + M : ℕ) : ℝ) ^ 2 * w / L := by
      have hm_le : (M' : ℝ) ^ 2 ≤ ((1 + M : ℕ) : ℝ) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (by omega)) 2
      calc (M' : ℝ) ^ 2 / (phaseNat n : ℝ)
          ≤ ((1 + M : ℕ) : ℝ) ^ 2 / L :=
            div_le_div₀ (sq_nonneg _) hm_le hL_pos hphase.1
        _ ≤ ((1 + M : ℕ) : ℝ) ^ 2 * w / L := by
            apply div_le_div_of_nonneg_right _ hL_pos.le
            exact le_mul_of_one_le_right (sq_nonneg _) hWn
    calc |cappedWindowFiniteEntropy (phaseNat n) M' th Tr -
            cappedDualValue (S0M M') th (phaseTarget (phaseDelta n))|
        ≤ |cappedWindowFiniteEntropy (phaseNat n) M' th Tr - cappedDualValue (S0M M') th Tr| +
            |cappedDualValue (S0M M') th Tr -
              cappedDualValue (S0M M') th (phaseTarget (phaseDelta n))| :=
          abs_sub_le _ _ _
      _ ≤ ((1 + M : ℕ) : ℝ) ^ 2 * w / L + universalDualLip * (2 * C * w / L) :=
          add_le_add (herr1_raw.trans hsq_le) herr2
      _ = K_E * w / L := by dsimp [K_E]; ring
  intro M₁ M₂ hM₁8 hM₁M hM₂8 hM₂M theta₁ hth₁ theta₂ hth₂ tau₁ htau₁ tau₂ htau₂
  have hM₁_eq : 1 + (M₁ - 1) = M₁ := by omega
  have hM₂_eq : 1 + (M₂ - 1) = M₂ := by omega
  intro obj₁ obj₂ r₁ hr₁ r₂ hr₂ hzero₁ hzero₂
  set G₁ : ℝ := cappedWindowFiniteEntropy (phaseNat n) M₁ theta₁ (fourSizeTarget n (phaseNat n) r₁)
  set G₂ : ℝ := cappedWindowFiniteEntropy (phaseNat n) M₂ theta₂ (fourSizeTarget n (phaseNat n) r₂)
  set F₁_lim : ℝ := cappedDualValue (S0M M₁) theta₁ (phaseTarget (phaseDelta n))
  set F₂_lim : ℝ := cappedDualValue (S0M M₂) theta₂ (phaseTarget (phaseDelta n))
  have hzero₁' :
      (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + r₁ - r₁ * Real.log r₁ +
        r₁ * (profileDeficitAffineA (phaseNat n) +
          profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) r₁ + G₁ + tau₁) = 0 := by
    have hG₁_def : G₁ =
        binEntropy theta₁ - Real.log 2 / 2 * theta₁ +
          (1 - theta₁) * (⨅ l : ℝ,
            (Real.log (∑ i ∈ Finset.Icc 2 M₁,
                Real.exp (l * (i : ℝ) +
                  (Real.log ((phaseNat n).descFactorial i : ℝ) -
                    (i : ℝ) * Real.log (phaseNat n : ℝ) -
                    Real.log 2 / 2 * (i : ℝ) ^ 2))) -
              l * ((fourSizeTarget n (phaseNat n) r₁ - theta₁) / (1 - theta₁)))) := by
      dsimp [G₁]
      unfold cappedWindowFiniteEntropy windowFiniteEntropy windowFinitePartition windowFiniteScore
      simp only [hM₁_eq]
    have hobj₁_eq :
        (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + r₁ - r₁ * Real.log r₁ +
          r₁ * (profileDeficitAffineA (phaseNat n) +
            profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) r₁ + G₁ + tau₁) =
          obj₁ r₁ := by
      dsimp only [obj₁]
      rw [hG₁_def]
    exact hobj₁_eq.trans hzero₁
  have hzero₂' :
      (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + r₂ - r₂ * Real.log r₂ +
        r₂ * (profileDeficitAffineA (phaseNat n) +
          profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) r₂ + G₂ + tau₂) = 0 := by
    have hG₂_def : G₂ =
        binEntropy theta₂ - Real.log 2 / 2 * theta₂ +
          (1 - theta₂) * (⨅ l : ℝ,
            (Real.log (∑ i ∈ Finset.Icc 2 M₂,
                Real.exp (l * (i : ℝ) +
                  (Real.log ((phaseNat n).descFactorial i : ℝ) -
                    (i : ℝ) * Real.log (phaseNat n : ℝ) -
                    Real.log 2 / 2 * (i : ℝ) ^ 2))) -
              l * ((fourSizeTarget n (phaseNat n) r₂ - theta₂) / (1 - theta₂)))) := by
      dsimp [G₂]
      unfold cappedWindowFiniteEntropy windowFiniteEntropy windowFinitePartition windowFiniteScore
      simp only [hM₂_eq]
    have hobj₂_eq :
        (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + r₂ - r₂ * Real.log r₂ +
          r₂ * (profileDeficitAffineA (phaseNat n) +
            profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) r₂ + G₂ + tau₂) =
          obj₂ r₂ := by
      dsimp only [obj₂]
      rw [hG₂_def]
    exact hobj₂_eq.trans hzero₂
  clear obj₁ obj₂ hzero₁ hzero₂
  have heq₁ := hObjZero_to_eq (hDom r₁ hr₁).1 hzero₁'
  have heq₂ := hObjZero_to_eq (hDom r₂ hr₂).1 hzero₂'
  have hG₁_err := hCapErr hM₁8 hM₁M hth₁ hr₁
  have hG₂_err := hCapErr hM₂8 hM₂M hth₂ hr₂
  have hF₁_abs := hCapAbs hM₁8 hth₁
  have hF₂_abs := hCapAbs hM₂8 hth₂
  have hG₂_abs : |G₂| ≤ B_F0 + 1 := by
    have htri : |G₂| ≤ |G₂ - F₂_lim| + |F₂_lim| := by
      simpa using abs_add_le (G₂ - F₂_lim) F₂_lim
    linarith [hG₂_err, hKE_le1, hF₂_abs]
  have htau₁_abs : |tau₁| ≤ Real.log 2 :=
    abs_le.mpr ⟨by linarith [htau₁.1, Real.log_pos one_lt_two], htau₁.2⟩
  have htau₂_abs : |tau₂| ≤ Real.log 2 :=
    abs_le.mpr ⟨by linarith [htau₂.1, Real.log_pos one_lt_two], htau₂.2⟩
  have hH₂_abs :
      |finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) r₂) -
        G₂ - tau₂| ≤ B_H := by
    have hu2 := hUnrestAbs r₂ hr₂
    have htri :
        |finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) r₂) -
            G₂ - tau₂| ≤
          |finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) r₂)| +
            |G₂| + |tau₂| := by
      linarith [abs_sub
          (finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) r₂) - G₂) tau₂,
        abs_sub
          (finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) r₂)) G₂]
    dsimp [B_H]
    linarith [Real.log_pos one_lt_two, hB_F0_nn]
  have hΔ_abs : |tau₂ - tau₁ + F₂_lim - F₁_lim| ≤ B_H := by
    have htri : |tau₂ - tau₁ + F₂_lim - F₁_lim| ≤ |tau₂| + |tau₁| + |F₂_lim| + |F₁_lim| := by
      have h1 := abs_sub (tau₂ - tau₁ + F₂_lim) F₁_lim
      have h2 := abs_add_le (tau₂ - tau₁) F₂_lim
      have h3 := abs_sub tau₂ tau₁
      linarith
    dsimp [B_H]
    linarith [hMtilt_nn, abs_nonneg (Real.log (partitionFn Splus 0))]
  have hmaster := corridor_root_separation_master hC hMtilt_nn hK_E_nn hLn hWn hn_pos
    hcenterDom.2.1 hfive hphase.1 hcMain.1 hcMain.2
    (fun s hs ↦ ⟨(hInv.2 s hs).1, (hInv.2 s hs).2.1, (hInv.2 s hs).2.2.2⟩)
    hDom htilt_corr hslope0 hr₁ hr₂ heq₁ heq₂ hG₁_err hG₂_err hH₂_abs hΔ_abs hS_lower
  have hstep :
      ((4 + C) * B_H + 4 * (K_E + 2 * C * Mtilt) + (K_slope + B_H) * B_H) *
        (n : ℝ) * w / L ^ 4 ≤ K_sep * (n : ℝ) * w / L ^ 4 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ hw_pos.le
    apply mul_le_mul_of_nonneg_right _ hn_pos.le
    dsimp [K_sep]; linarith
  exact hmaster.trans hstep

/-- **Section 5.2, eq. `(5.19)` (`eq:general-root-sep`) explicit `O_M(n log log n / (log n)⁴)`
corridor-root separation:**
for every `M : ℕ` and corridor half-width constant `C ≥ 0`, there exists `K_sep > 0` such that
eventually:
1. **(Unconstrained window pairs):** for all `m₁, m₂ ≤ 1`, `7 ≤ M₁, M₂ ≤ M`, `τ₁, τ₂ ∈ [0, log 2]`,
   and any `r₁, r₂ ∈ [c_n - C Δ_n, c_n + C Δ_n]` solving `𝓛_{S_{m₁, M₁}}(n, r₁) + τ₁ r₁ = 0` and
   `𝓛_{S_{m₂, M₂}}(n, r₂) + τ₂ r₂ = 0`,
   `|(r₁ - r₂) - (log 2)² / 4 · (τ₂ - τ₁ + 𝓕_{S_{m₂, M₂}}(T_{δ_n}) - 𝓕_{S_{m₁, M₁}}(T_{δ_n})) · n / (log n)³|`
   `≤ K_sep n log log n / (log n)⁴`;
2. **(Capped window pairs):** when `8 ≤ M` and `δ_n ∈ [0, δ_*]`, for all `8 ≤ M₁, M₂ ≤ M`,
   `ϑ₁, ϑ₂ ∈ [0, 1/20]`, `τ₁, τ₂ ∈ [0, log 2]`, and any `r₁, r₂ ∈ [c_n - C Δ_n, c_n + C Δ_n]`
   solving `𝓛_{S_{0, M₁}}^{=ϑ₁}(n, r₁) + τ₁ r₁ = 0` and `𝓛_{S_{0, M₂}}^{=ϑ₂}(n, r₂) + τ₂ r₂ = 0`,
   `|(r₁ - r₂) - (log 2)² / 4 · (τ₂ - τ₁ + 𝓕_{S_{0, M₂}}^{=ϑ₂}(T_{δ_n}) - 𝓕_{S_{0, M₁}}^{=ϑ₁}(T_{δ_n})) · n / (log n)³|`
   `≤ K_sep n log log n / (log n)⁴`. -/
theorem eventually_window_and_capped_corridorRoot_separation_logLogRate
    (M : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ K_sep : ℝ, 0 < K_sep ∧ ∀ᶠ n : ℕ in atTop,
      (∀ (m₁ m₂ M₁ M₂ : ℕ), m₁ ≤ 1 → m₂ ≤ 1 → 7 ≤ M₁ → M₁ ≤ M → 7 ≤ M₂ → M₂ ≤ M →
        ∀ tau₁ ∈ Set.Icc (0 : ℝ) (Real.log 2),
          ∀ tau₂ ∈ Set.Icc (0 : ℝ) (Real.log 2),
            let S₁ : Set ℤ := {j : ℤ | ((m₁ + 1 : ℕ) : ℤ) ≤ j ∧ j ≤ ((m₁ + M₁ : ℕ) : ℤ)}
            let S₂ : Set ℤ := {j : ℤ | ((m₂ + 1 : ℕ) : ℤ) ≤ j ∧ j ≤ ((m₂ + M₂ : ℕ) : ℤ)}
            let obj₁ : ℝ → ℝ := fun s ↦
              (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + s - s * Real.log s +
                s * (profileDeficitAffineA (phaseNat n) +
                  profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s +
                  (⨅ l : ℝ,
                    (Real.log (∑ i ∈ Finset.Icc (m₁ + 1) (m₁ + M₁),
                        Real.exp (l * (i : ℝ) +
                          (Real.log ((phaseNat n).descFactorial i : ℝ) -
                            (i : ℝ) * Real.log (phaseNat n : ℝ) -
                            Real.log 2 / 2 * (i : ℝ) ^ 2))) -
                      l * fourSizeTarget n (phaseNat n) s)) + tau₁)
            let obj₂ : ℝ → ℝ := fun s ↦
              (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + s - s * Real.log s +
                s * (profileDeficitAffineA (phaseNat n) +
                  profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s +
                  (⨅ l : ℝ,
                    (Real.log (∑ i ∈ Finset.Icc (m₂ + 1) (m₂ + M₂),
                        Real.exp (l * (i : ℝ) +
                          (Real.log ((phaseNat n).descFactorial i : ℝ) -
                            (i : ℝ) * Real.log (phaseNat n : ℝ) -
                            Real.log 2 / 2 * (i : ℝ) ^ 2))) -
                      l * fourSizeTarget n (phaseNat n) s)) + tau₂)
            ∀ r₁ ∈ Set.Icc (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
                           (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n),
              ∀ r₂ ∈ Set.Icc (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
                             (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n),
                obj₁ r₁ = 0 → obj₂ r₂ = 0 →
                  |(r₁ - r₂) - (Real.log 2) ^ 2 / 4 *
                      (tau₂ - tau₁ +
                        dualValue S₂ (phaseTarget (phaseDelta n)) -
                        dualValue S₁ (phaseTarget (phaseDelta n))) *
                      ((n : ℝ) / (Real.log (n : ℝ)) ^ 3)| ≤
                    K_sep * (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ 4) ∧
      (8 ≤ M → phaseDelta n ∈ Set.Icc (0 : ℝ) deltaStar →
        ∀ (M₁ M₂ : ℕ), 8 ≤ M₁ → M₁ ≤ M → 8 ≤ M₂ → M₂ ≤ M →
          ∀ theta₁ ∈ Set.Icc (0 : ℝ) (1 / 20),
            ∀ theta₂ ∈ Set.Icc (0 : ℝ) (1 / 20),
              ∀ tau₁ ∈ Set.Icc (0 : ℝ) (Real.log 2),
                ∀ tau₂ ∈ Set.Icc (0 : ℝ) (Real.log 2),
                  let obj₁ : ℝ → ℝ := fun s ↦
                    (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + s - s * Real.log s +
                      s * (profileDeficitAffineA (phaseNat n) +
                        profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s +
                        (binEntropy theta₁ - Real.log 2 / 2 * theta₁ +
                          (1 - theta₁) * (⨅ l : ℝ,
                            (Real.log (∑ i ∈ Finset.Icc 2 M₁,
                                Real.exp (l * (i : ℝ) +
                                  (Real.log ((phaseNat n).descFactorial i : ℝ) -
                                    (i : ℝ) * Real.log (phaseNat n : ℝ) -
                                    Real.log 2 / 2 * (i : ℝ) ^ 2))) -
                              l * ((fourSizeTarget n (phaseNat n) s - theta₁) / (1 - theta₁))))) +
                        tau₁)
                  let obj₂ : ℝ → ℝ := fun s ↦
                    (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + s - s * Real.log s +
                      s * (profileDeficitAffineA (phaseNat n) +
                        profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s +
                        (binEntropy theta₂ - Real.log 2 / 2 * theta₂ +
                          (1 - theta₂) * (⨅ l : ℝ,
                            (Real.log (∑ i ∈ Finset.Icc 2 M₂,
                                Real.exp (l * (i : ℝ) +
                                  (Real.log ((phaseNat n).descFactorial i : ℝ) -
                                    (i : ℝ) * Real.log (phaseNat n : ℝ) -
                                    Real.log 2 / 2 * (i : ℝ) ^ 2))) -
                              l * ((fourSizeTarget n (phaseNat n) s - theta₂) / (1 - theta₂))))) +
                        tau₂)
                  ∀ r₁ ∈ Set.Icc (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
                                 (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n),
                    ∀ r₂ ∈ Set.Icc (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
                                   (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n),
                      obj₁ r₁ = 0 → obj₂ r₂ = 0 →
                        |(r₁ - r₂) - (Real.log 2) ^ 2 / 4 *
                            (tau₂ - tau₁ +
                              cappedDualValue (S0M M₂) theta₂ (phaseTarget (phaseDelta n)) -
                              cappedDualValue (S0M M₁) theta₁ (phaseTarget (phaseDelta n))) *
                            ((n : ℝ) / (Real.log (n : ℝ)) ^ 3)| ≤
                          K_sep * (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ 4) := by
  obtain ⟨K_slope, hK_slope_pos, hSlopeEv⟩ := eventually_unrestrictedPhaseObjective_deriv_logLogRate C hC
  obtain ⟨Mtilt, hMtilt_nn, huniformTilt⟩ :=
    exists_eventually_forall_mem_Icc_abs_profileDeficitTilt_le
      (by norm_num : (-1 : ℝ) < 9 / 4) (by norm_num : (9 / 4 : ℝ) ≤ 17 / 4)
  obtain ⟨Ntilt, hNtilt⟩ := eventually_atTop.1 huniformTilt
  set K_E : ℝ := ((1 + M : ℕ) : ℝ) ^ 2 + 2 * C * universalDualLip
  set B_F0 : ℝ := |Real.log (partitionFn Splus 0)| +
    |min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))| + Real.log 2 + 1
  set B_H : ℝ := 5 * Mtilt + |Real.log (partitionFn Splus 0)| + 2 * B_F0 + 2 * Real.log 2 + 2
  set K_sep : ℝ := (4 + C) * B_H + 4 * (K_E + 2 * C * Mtilt) + (K_slope + B_H) * B_H + 1
  have hK_E_nn : 0 ≤ K_E := by
    have := universalDualLip_nonneg
    dsimp [K_E]; positivity
  have hB_F0_nn : 0 ≤ B_F0 := by
    dsimp [B_F0]; linarith [Real.log_pos one_lt_two,
      abs_nonneg (Real.log (partitionFn Splus 0)),
      abs_nonneg (min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8)))]
  have hB_H_nn : 0 ≤ B_H := by
    dsimp [B_H]; linarith [Real.log_pos one_lt_two, abs_nonneg (Real.log (partitionFn Splus 0))]
  obtain ⟨K_cap_sep, hK_cap_pos, hCapEv⟩ := eventually_capped_corridorRoot_separation_aux (M := M) C hC
  let K_tot : ℝ := max K_sep K_cap_sep
  have hK_tot_pos : 0 < K_tot := lt_max_of_lt_left (by dsimp [K_sep]; positivity)
  refine ⟨K_tot, hK_tot_pos, ?_⟩
  have hphaseN : ∀ᶠ n : ℕ in atTop, max Ntilt (2 * (1 + M)) ≤ phaseNat n := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop ((max Ntilt (2 * (1 + M)) : ℕ) : ℝ),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact_mod_cast hn.trans hph.1
  have hS_small : ∀ᶠ n : ℕ in atTop,
      ‖logLogOrder n‖ ≤
        min (1 / (Real.log 2 * (K_slope + B_H + 1))) (1 / (K_E + 1)) * ‖logOrder n‖ :=
    logLogOrder_isLittleO_logOrder.bound (lt_min
      (by have := Real.log_pos one_lt_two; positivity)
      (by positivity))
  have hW1 : ∀ᶠ n : ℕ in atTop, 1 ≤ logLogOrder n :=
    tendsto_logLogOrder_atTop.eventually_ge_atTop 1
  have hL4 : ∀ᶠ n : ℕ in atTop, 4 ≤ logOrder n :=
    tendsto_logOrder_atTop.eventually_ge_atTop 4
  filter_upwards [hCapEv, hSlopeEv, hphaseN, hS_small, hW1, hL4,
    eventually_phaseRootCenter_sub_main_logLogRate,
    eventually_corridor_inv_target_logLogRate C hC,
    eventually_phaseRootLogLogCorridor_fourSize_domain C hC,
    eventually_phaseRootLogLogCorridor_fourSize_target_mem_Icc C hC,
    eventually_phaseRoot_domain_pos_and_target_corridor,
    eventually_five_lt_phaseNat,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with
    n hCapSep hSlope hphN hSsm hWn hLn hcMain hInv hDom hTarget hcenterDom hfive hphase
  set L : ℝ := logOrder n
  set w : ℝ := logLogOrder n
  have hL_pos : 0 < L := by linarith
  have hw_pos : 0 < w := lt_of_lt_of_le zero_lt_one hWn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_trans Nat.zero_lt_one hcenterDom.1.1)
  have ha_ge6 : (6 : ℝ) ≤ (phaseNat n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hfive)
  have ha_pos : (0 : ℝ) < (phaseNat n : ℝ) := by linarith
  rw [Real.norm_eq_abs, abs_of_pos hw_pos, Real.norm_eq_abs, abs_of_pos hL_pos] at hSsm
  have hSsm1 : w ≤ (1 / (Real.log 2 * (K_slope + B_H + 1))) * L :=
    hSsm.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hL_pos.le)
  have hSsm2 : w ≤ (1 / (K_E + 1)) * L :=
    hSsm.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hL_pos.le)
  have hS_lower : (K_slope + B_H) * L * w ≤ (1 / Real.log 2) * L ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hSsm1
      (show (0 : ℝ) ≤ (K_slope + B_H + 1) * L by positivity)
    have hrhs : (K_slope + B_H + 1) * L *
        (1 / (Real.log 2 * (K_slope + B_H + 1)) * L) = (1 / Real.log 2) * L ^ 2 := by
      field_simp [(Real.log_pos one_lt_two).ne',
        (show (0 : ℝ) < K_slope + B_H + 1 by positivity).ne']
    have hlhs : (K_slope + B_H) * L * w ≤ (K_slope + B_H + 1) * L * w := by
      have : 0 ≤ L * w := mul_nonneg hL_pos.le hw_pos.le
      linarith
    linarith
  have hKE_le1 : K_E * w / L ≤ 1 := by
    rw [div_le_iff₀ hL_pos, one_mul]
    have hm := mul_le_mul_of_nonneg_left hSsm2 (show (0 : ℝ) ≤ K_E + 1 by positivity)
    have hrhs : (K_E + 1) * (1 / (K_E + 1) * L) = L := by
      field_simp [(show (0 : ℝ) < K_E + 1 by positivity).ne']
    have hexp : (K_E + 1) * w = K_E * w + w := by ring
    linarith [hw_pos]
  have htilt_corr : ∀ s ∈ Set.Icc
      (phaseRootCenter n - C * w * phaseRootGapRadius n)
      (phaseRootCenter n + C * w * phaseRootGapRadius n),
      fourSizeTarget n (phaseNat n) s ∈ Set.Ioo (-1 : ℝ) ((phaseNat n : ℝ) - 1) ∧
        |profileDeficitTilt (phaseNat n) (fourSizeTarget n (phaseNat n) s)| ≤ Mtilt := by
    intro s hs
    exact hNtilt (phaseNat n) ((le_max_left _ _).trans hphN) _ (hTarget s hs)
  have hslope0 : ∀ s ∈ Set.Icc
      (phaseRootCenter n - C * w * phaseRootGapRadius n)
      (phaseRootCenter n + C * w * phaseRootGapRadius n),
      |deriv (unrestrictedPhaseObjective n) s - (2 / Real.log 2) * L ^ 2| ≤
        K_slope * L * w := by
    intro s hs
    have h0 := hSlope 0 ⟨le_rfl, (Real.log_pos one_lt_two).le⟩ s hs
    simpa only [zero_mul, add_zero, L, w, logOrder, logLogOrder] using h0
  have hUnrestAbs : ∀ s ∈ Set.Icc
      (phaseRootCenter n - C * w * phaseRootGapRadius n)
      (phaseRootCenter n + C * w * phaseRootGapRadius n),
      |finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) s)| ≤
        5 * Mtilt + |Real.log (partitionFn Splus 0)| := by
    intro s hs
    set T : ℝ := fourSizeTarget n (phaseNat n) s
    have hTK : T ∈ Set.Icc (9 / 4 : ℝ) (17 / 4) := hTarget s hs
    have hT25 : T ∈ Set.Ioo (2 : ℝ) 5 := ⟨by linarith [hTK.1], by linarith [hTK.2]⟩
    have hHi : finiteUnrestrictedDeficitEntropy (phaseNat n) T ≤
        |Real.log (partitionFn Splus 0)| := by
      have h1 := (finiteProfileDeficitEntropy_le_extendedGaussianEntropyValue
        (phaseNat n) hfive hT25).trans (extendedGaussianEntropyValue_le_dualValue_Splus hT25)
      have hm4 := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT25)
      have h2 := dualValue_le_at S4_subset_Splus hm4 0
      unfold finiteUnrestrictedDeficitEntropy
      linarith [le_abs_self (Real.log (partitionFn Splus 0))]
    have hLo : -(5 * Mtilt) ≤ finiteUnrestrictedDeficitEntropy (phaseNat n) T := by
      obtain ⟨_, htiltB⟩ := htilt_corr s hs
      have hp1 := one_le_profileDeficitPartition (phaseNat n) (by omega)
        (profileDeficitTilt (phaseNat n) T)
      have hlognn := Real.log_nonneg hp1
      have hmul : |profileDeficitTilt (phaseNat n) T * T| ≤ 5 * Mtilt := by
        rw [abs_mul, abs_of_pos (by linarith [hTK.1] : 0 < T)]
        have := mul_le_mul htiltB (show T ≤ 5 by linarith [hTK.2]) (by linarith [hTK.1]) hMtilt_nn
        linarith
      unfold finiteUnrestrictedDeficitEntropy
      linarith [(abs_le.mp hmul).2]
    exact abs_le.mpr ⟨by linarith [abs_nonneg (Real.log (partitionFn Splus 0))],
      by linarith [hMtilt_nn]⟩
  have hT_delta_wide : phaseTarget (phaseDelta n) ∈ Set.Icc (9 / 4 : ℝ) (9 / 2) := by
    obtain ⟨h2lo, h2hi⟩ := two_div_log_two_bounds
    unfold phaseTarget
    exact ⟨by linarith [phaseDelta_lt_one n, h2lo], by linarith [phaseDelta_nonneg n, h2hi]⟩
  have hDualWinAbs : ∀ {m' M' : ℕ}, m' ≤ 1 → 7 ≤ M' →
      ∀ {T : ℝ}, T ∈ Set.Icc (9 / 4 : ℝ) (9 / 2) →
        |dualValue (windowSupportSet m' M') T| ≤ B_F0 := by
    intro m' M' hm' hM' T hT
    have hd := dualValue_window_bounds_on_padded hm' hM' T
      ⟨by linarith [hT.1], by linarith [hT.2]⟩
    rw [abs_le]
    dsimp [B_F0]
    exact ⟨by linarith [hd.1,
        neg_abs_le (min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))),
        abs_nonneg (Real.log (partitionFn Splus 0)), Real.log_pos one_lt_two],
      by linarith [hd.2, le_abs_self (Real.log (partitionFn Splus 0)),
        abs_nonneg (min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))),
        Real.log_pos one_lt_two]⟩
  have hObjZero_to_eq : ∀ {s G tau : ℝ}, 0 < s →
      (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + s - s * Real.log s +
        s * (profileDeficitAffineA (phaseNat n) +
          profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s + G + tau) = 0 →
      unrestrictedPhaseObjective n s =
        s * (finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) s) -
          G - tau) := by
    intro s G tau hspos hzero
    have hu := unrestrictedPhaseObjective_div_eq_deficitCentered n hspos.ne'
    have huMul : unrestrictedPhaseObjective n s =
        s * ((n : ℝ) * Real.log (n : ℝ) / s - (n : ℝ) / s + 1 - Real.log s +
          (profileDeficitAffineA (phaseNat n) +
            profileDeficitAffineB (phaseNat n) * profileDeficitTarget (phaseNat n) (n : ℝ) s +
            finiteUnrestrictedDeficitEntropy (phaseNat n)
              (profileDeficitTarget (phaseNat n) (n : ℝ) s))) := by
      rw [div_eq_iff hspos.ne'] at hu
      unfold finiteUnrestrictedDeficitEntropy
      linarith
    rw [huMul]
    have hzero' :
        s * ((n : ℝ) * Real.log (n : ℝ) / s - (n : ℝ) / s + 1 - Real.log s +
          (profileDeficitAffineA (phaseNat n) +
            profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s + G + tau)) = 0 := by
      have : s * ((n : ℝ) * Real.log (n : ℝ) / s - (n : ℝ) / s + 1 - Real.log s +
          (profileDeficitAffineA (phaseNat n) +
            profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s + G + tau)) =
        (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + s - s * Real.log s +
          s * (profileDeficitAffineA (phaseNat n) +
            profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s + G + tau) := by
        field_simp [hspos.ne']
      rw [this, hzero]
    change _ = s * (finiteUnrestrictedDeficitEntropy (phaseNat n)
      (profileDeficitTarget (phaseNat n) (n : ℝ) s) - G - tau)
    have hft : fourSizeTarget n (phaseNat n) s = profileDeficitTarget (phaseNat n) (n : ℝ) s := rfl
    rw [hft] at hzero'
    linarith
  have hWinErr : ∀ {m' M' : ℕ} {r : ℝ},
      m' ≤ 1 → 7 ≤ M' → M' ≤ M →
      r ∈ Set.Icc (phaseRootCenter n - C * w * phaseRootGapRadius n)
                  (phaseRootCenter n + C * w * phaseRootGapRadius n) →
      |windowFiniteEntropy (phaseNat n) m' M' (fourSizeTarget n (phaseNat n) r) -
          dualValue (windowSupportSet m' M') (phaseTarget (phaseDelta n))| ≤ K_E * w / L := by
    intro m' M' r hm' hM'7 hM'M hr
    set Tr : ℝ := fourSizeTarget n (phaseNat n) r
    have hTK : Tr ∈ Set.Icc (9 / 4 : ℝ) (17 / 4) := hTarget r hr
    have hT25 : Tr ∈ Set.Ioo (2 : ℝ) 5 := ⟨by linarith [hTK.1], by linarith [hTK.2]⟩
    have hT_wide : Tr ∈ Set.Icc (9 / 4 : ℝ) (9 / 2) := ⟨hTK.1, by linarith [hTK.2]⟩
    have halpha : 2 * (m' + M') ≤ phaseNat n := by
      have := (le_max_right Ntilt (2 * (1 + M))).trans hphN; omega
    have herr1 := (windowFiniteEntropy_bounds hm' hM'7 halpha hT25).2
    have herr2 := (abs_dualValue_window_sub_le hm' hM'7 hT_wide hT_delta_wide).trans
      (mul_le_mul_of_nonneg_left (hInv.2 r hr).2.2.2 universalDualLip_nonneg)
    have hsq_le : ((m' + M' : ℕ) : ℝ) ^ 2 / (phaseNat n : ℝ) ≤
        ((1 + M : ℕ) : ℝ) ^ 2 * w / L := by
      have hm_le : ((m' + M' : ℕ) : ℝ) ^ 2 ≤ ((1 + M : ℕ) : ℝ) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (by omega)) 2
      calc ((m' + M' : ℕ) : ℝ) ^ 2 / (phaseNat n : ℝ)
          ≤ ((1 + M : ℕ) : ℝ) ^ 2 / L :=
            div_le_div₀ (sq_nonneg _) hm_le hL_pos hphase.1
        _ ≤ ((1 + M : ℕ) : ℝ) ^ 2 * w / L := by
            apply div_le_div_of_nonneg_right _ hL_pos.le
            exact le_mul_of_one_le_right (sq_nonneg _) hWn
    calc |windowFiniteEntropy (phaseNat n) m' M' Tr -
            dualValue (windowSupportSet m' M') (phaseTarget (phaseDelta n))|
        ≤ |windowFiniteEntropy (phaseNat n) m' M' Tr - dualValue (windowSupportSet m' M') Tr| +
            |dualValue (windowSupportSet m' M') Tr -
              dualValue (windowSupportSet m' M') (phaseTarget (phaseDelta n))| :=
          abs_sub_le _ _ _
      _ ≤ ((1 + M : ℕ) : ℝ) ^ 2 * w / L + universalDualLip * (2 * C * w / L) :=
          add_le_add (herr1.trans hsq_le) herr2
      _ = K_E * w / L := by dsimp [K_E]; ring
  constructor
  · intro m₁ m₂ M₁ M₂ hm₁ hm₂ hM₁7 hM₁M hM₂7 hM₂M tau₁ htau₁ tau₂ htau₂
      S₁ S₂ obj₁ obj₂ r₁ hr₁ r₂ hr₂ hzero₁ hzero₂
    set G₁ : ℝ := windowFiniteEntropy (phaseNat n) m₁ M₁ (fourSizeTarget n (phaseNat n) r₁)
    set G₂ : ℝ := windowFiniteEntropy (phaseNat n) m₂ M₂ (fourSizeTarget n (phaseNat n) r₂)
    set F₁_lim : ℝ := dualValue (windowSupportSet m₁ M₁) (phaseTarget (phaseDelta n))
    set F₂_lim : ℝ := dualValue (windowSupportSet m₂ M₂) (phaseTarget (phaseDelta n))
    have heq₁ : unrestrictedPhaseObjective n r₁ =
        r₁ * (finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) r₁) -
          G₁ - tau₁) := hObjZero_to_eq (hDom r₁ hr₁).1 hzero₁
    have heq₂ : unrestrictedPhaseObjective n r₂ =
        r₂ * (finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) r₂) -
          G₂ - tau₂) := hObjZero_to_eq (hDom r₂ hr₂).1 hzero₂
    clear obj₁ obj₂ hzero₁ hzero₂
    have hG₁_err : |G₁ - F₁_lim| ≤ K_E * w / L := hWinErr hm₁ hM₁7 hM₁M hr₁
    have hG₂_err : |G₂ - F₂_lim| ≤ K_E * w / L := hWinErr hm₂ hM₂7 hM₂M hr₂
    have hF₁_abs : |F₁_lim| ≤ B_F0 := hDualWinAbs hm₁ hM₁7 hT_delta_wide
    have hF₂_abs : |F₂_lim| ≤ B_F0 := hDualWinAbs hm₂ hM₂7 hT_delta_wide
    have hG₂_abs : |G₂| ≤ B_F0 + 1 := by
      have htri : |G₂| ≤ |G₂ - F₂_lim| + |F₂_lim| := by
        simpa using abs_add_le (G₂ - F₂_lim) F₂_lim
      linarith [hG₂_err, hKE_le1, hF₂_abs]
    have htau₁_abs : |tau₁| ≤ Real.log 2 :=
      abs_le.mpr ⟨by linarith [htau₁.1, Real.log_pos one_lt_two], htau₁.2⟩
    have htau₂_abs : |tau₂| ≤ Real.log 2 :=
      abs_le.mpr ⟨by linarith [htau₂.1, Real.log_pos one_lt_two], htau₂.2⟩
    have hH₂_abs :
        |finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) r₂) -
          G₂ - tau₂| ≤ B_H := by
      have hu2 := hUnrestAbs r₂ hr₂
      have htri :
          |finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) r₂) -
              G₂ - tau₂| ≤
            |finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) r₂)| +
              |G₂| + |tau₂| := by
        linarith [abs_sub
            (finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) r₂) - G₂) tau₂,
          abs_sub
            (finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) r₂)) G₂]
      dsimp [B_H]
      linarith [Real.log_pos one_lt_two, hB_F0_nn]
    have hΔ_abs : |tau₂ - tau₁ + F₂_lim - F₁_lim| ≤ B_H := by
      have htri : |tau₂ - tau₁ + F₂_lim - F₁_lim| ≤ |tau₂| + |tau₁| + |F₂_lim| + |F₁_lim| := by
        have h1 := abs_sub (tau₂ - tau₁ + F₂_lim) F₁_lim
        have h2 := abs_add_le (tau₂ - tau₁) F₂_lim
        have h3 := abs_sub tau₂ tau₁
        linarith
      dsimp [B_H]
      linarith [hMtilt_nn, abs_nonneg (Real.log (partitionFn Splus 0))]
    have hmaster := corridor_root_separation_master hC hMtilt_nn hK_E_nn hLn hWn hn_pos
      hcenterDom.2.1 hfive hphase.1 hcMain.1 hcMain.2
      (fun s hs ↦ ⟨(hInv.2 s hs).1, (hInv.2 s hs).2.1, (hInv.2 s hs).2.2.2⟩)
      hDom htilt_corr hslope0 hr₁ hr₂ heq₁ heq₂ hG₁_err hG₂_err hH₂_abs hΔ_abs hS_lower
    have hstep :
        ((4 + C) * B_H + 4 * (K_E + 2 * C * Mtilt) + (K_slope + B_H) * B_H) *
          (n : ℝ) * w / L ^ 4 ≤ K_tot * (n : ℝ) * w / L ^ 4 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hw_pos.le
      apply mul_le_mul_of_nonneg_right _ hn_pos.le
      have hk1 : K_sep ≤ K_tot := le_max_left _ _
      dsimp [K_sep] at hk1; linarith
    exact hmaster.trans hstep
  · intro hM8 hd M₁ M₂ hM₁8 hM₁M hM₂8 hM₂M theta₁ hth₁ theta₂ hth₂ tau₁ htau₁ tau₂ htau₂
      obj₁ obj₂ r₁ hr₁ r₂ hr₂ hzero₁ hzero₂
    have hc := hCapSep hM8 hd M₁ M₂ hM₁8 hM₁M hM₂8 hM₂M theta₁ hth₁ theta₂ hth₂
      tau₁ htau₁ tau₂ htau₂ r₁ hr₁ r₂ hr₂ hzero₁ hzero₂
    have hstep :
        K_cap_sep * (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ 4 ≤
          K_tot * (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ 4 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hw_pos.le
      apply mul_le_mul_of_nonneg_right (le_max_right _ _) hn_pos.le
    exact hc.trans hstep

/-!
## 3. Section 7 `Lemma 7.1` — cross-edge conditioning, `E_π / C_π / D_π` regularity, and `Π_rel`
-/

private def toggleSinglePairAdj {n : ℕ} (u₀ v₀ : Fin n)
    (G : LabeledGraph n) (u v : Fin n) : Prop :=
  u ≠ v ∧ if ({u, v} : Finset (Fin n)) = {u₀, v₀} then ¬ G.Adj u v else G.Adj u v

private def toggleSinglePair {n : ℕ} (u₀ v₀ : Fin n) (G : LabeledGraph n) : LabeledGraph n where
  Adj := toggleSinglePairAdj u₀ v₀ G
  symm := ⟨by
    intro u v huv
    unfold toggleSinglePairAdj at huv ⊢
    refine ⟨huv.1.symm, ?_⟩
    rw [Finset.pair_comm v u]
    by_cases h : ({u, v} : Finset (Fin n)) = {u₀, v₀}
    · rw [if_pos h] at huv ⊢; exact fun hadj ↦ huv.2 (G.adj_symm hadj)
    · rw [if_neg h] at huv ⊢; exact G.adj_symm huv.2⟩
  loopless := ⟨fun u hu ↦ hu.1 rfl⟩

private theorem toggleSinglePair_involutive {n : ℕ} (u₀ v₀ : Fin n) :
    Function.Involutive (toggleSinglePair u₀ v₀) := by
  intro G
  ext u v
  change toggleSinglePairAdj u₀ v₀ (toggleSinglePair u₀ v₀ G) u v ↔ G.Adj u v
  unfold toggleSinglePairAdj
  change (u ≠ v ∧ if ({u, v} : Finset (Fin n)) = {u₀, v₀}
    then ¬ toggleSinglePairAdj u₀ v₀ G u v else toggleSinglePairAdj u₀ v₀ G u v) ↔ G.Adj u v
  unfold toggleSinglePairAdj
  by_cases huv : u = v
  · subst v
    constructor
    · intro h; exact (h.1 rfl).elim
    · intro h; exact (G.ne_of_adj h rfl).elim
  · by_cases h : ({u, v} : Finset (Fin n)) = {u₀, v₀} <;> simp [huv, h]

private theorem pair_eq_iff_unordered {α : Type*} [DecidableEq α]
    {u v u₀ v₀ : α} (huv₀ : u₀ ≠ v₀) :
    ({u, v} : Finset α) = {u₀, v₀} ↔ (u = u₀ ∧ v = v₀) ∨ (u = v₀ ∧ v = u₀) := by
  constructor
  · intro heq
    have hu : u ∈ ({u₀, v₀} : Finset α) := heq ▸ Finset.mem_insert_self u {v}
    have hv : v ∈ ({u₀, v₀} : Finset α) :=
      heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self v)
    have hcard : ({u, v} : Finset α).card = 2 := by rw [heq, Finset.card_pair huv₀]
    have huv : u ≠ v := by
      intro h; subst h; simp at hcard
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact (huv rfl).elim
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact (huv rfl).elim
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact Finset.pair_comm _ _

private theorem randomGraphMeasure_inter_noEdges_eq_half_pow
    {n : ℕ} {S : Set (LabeledGraph n)} (F : Finset (Finset (Fin n)))
    (hF_card : ∀ e ∈ F, e.card = 2)
    (hS_inv : ∀ G H : LabeledGraph n,
      (∀ u v : Fin n, u ≠ v → ({u, v} : Finset (Fin n)) ∉ F → (G.Adj u v ↔ H.Adj u v)) →
      (G ∈ S ↔ H ∈ S)) :
    randomGraphMeasure n (S ∩ {G | ∀ u v : Fin n, ({u, v} : Finset (Fin n)) ∈ F → ¬ G.Adj u v}) =
        (1 / 2 : ENNReal) ^ F.card * randomGraphMeasure n S ∧
      (randomGraphMeasure n).real
          (S ∩ {G | ∀ u v : Fin n, ({u, v} : Finset (Fin n)) ∈ F → ¬ G.Adj u v}) =
        (1 / 2 : ℝ) ^ F.card * (randomGraphMeasure n).real S := by
  classical
  have henn :
      randomGraphMeasure n (S ∩ {G | ∀ u v : Fin n, ({u, v} : Finset (Fin n)) ∈ F → ¬ G.Adj u v}) =
        (1 / 2 : ENNReal) ^ F.card * randomGraphMeasure n S := by
    induction F using Finset.induction_on with
    | empty =>
      simp
    | @insert e F' he_notMem ih =>
      have he2 : e.card = 2 := hF_card e (Finset.mem_insert_self e F')
      obtain ⟨u₀, v₀, huv₀, rfl⟩ := Finset.card_eq_two.mp he2
      have hF'_card : ∀ e' ∈ F', e'.card = 2 :=
        fun e' he' ↦ hF_card e' (Finset.mem_insert_of_mem he')
      have hS_inv' : ∀ G H : LabeledGraph n,
          (∀ u v : Fin n, u ≠ v → ({u, v} : Finset (Fin n)) ∉ F' → (G.Adj u v ↔ H.Adj u v)) →
          (G ∈ S ↔ H ∈ S) := by
        intro G H hGH
        exact hS_inv G H fun u v huv hnot ↦
          hGH u v huv fun hmem ↦ hnot (Finset.mem_insert_of_mem hmem)
      set T : Set (LabeledGraph n) :=
        S ∩ {G | ∀ u v : Fin n, ({u, v} : Finset (Fin n)) ∈ F' → ¬ G.Adj u v}
      set T₀ : Set (LabeledGraph n) := T ∩ {G | ¬ G.Adj u₀ v₀}
      set T₁ : Set (LabeledGraph n) := T ∩ {G | G.Adj u₀ v₀}
      have hT_preserve : ∀ {G : LabeledGraph n}, G ∈ T → toggleSinglePair u₀ v₀ G ∈ T := by
        intro G ⟨hGS, hGF'⟩
        refine ⟨?_, ?_⟩
        · refine (hS_inv G (toggleSinglePair u₀ v₀ G) fun u v huv hnot ↦ ?_).mp hGS
          have hne_pair : ({u, v} : Finset (Fin n)) ≠ {u₀, v₀} :=
            fun heq ↦ hnot (heq ▸ Finset.mem_insert_self _ _)
          change G.Adj u v ↔ toggleSinglePairAdj u₀ v₀ G u v
          unfold toggleSinglePairAdj
          simp [huv, hne_pair]
        · intro u v hmem_F'
          have hne_pair : ({u, v} : Finset (Fin n)) ≠ {u₀, v₀} :=
            fun heq ↦ he_notMem (heq ▸ hmem_F')
          change ¬ toggleSinglePairAdj u₀ v₀ G u v
          unfold toggleSinglePairAdj
          rw [if_neg hne_pair]
          exact fun h ↦ hGF' u v hmem_F' h.2
      have hT₀_le_T₁ : randomGraphMeasure n T₀ ≤ randomGraphMeasure n T₁ := by
        refine randomGraphMeasure_image_le_of_involutive (toggleSinglePair u₀ v₀)
          (toggleSinglePair_involutive u₀ v₀) fun G ⟨hGT, hnAdj⟩ ↦ ⟨hT_preserve hGT, ?_⟩
        change ¬ G.Adj u₀ v₀ at hnAdj
        change toggleSinglePairAdj u₀ v₀ G u₀ v₀
        unfold toggleSinglePairAdj
        simp [huv₀, hnAdj]
      have hT₁_le_T₀ : randomGraphMeasure n T₁ ≤ randomGraphMeasure n T₀ := by
        refine randomGraphMeasure_image_le_of_involutive (toggleSinglePair u₀ v₀)
          (toggleSinglePair_involutive u₀ v₀) fun G ⟨hGT, hAdj⟩ ↦ ⟨hT_preserve hGT, ?_⟩
        change G.Adj u₀ v₀ at hAdj
        change ¬ toggleSinglePairAdj u₀ v₀ G u₀ v₀
        unfold toggleSinglePairAdj
        simp [huv₀, hAdj]
      have hT_eq : randomGraphMeasure n T₀ = randomGraphMeasure n T₁ :=
        le_antisymm hT₀_le_T₁ hT₁_le_T₀
      have hunion : T = T₀ ∪ T₁ := by
        ext G; simp only [T₀, T₁, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]; tauto
      have hdisj : Disjoint T₀ T₁ := by
        rw [Set.disjoint_left]
        intro G h0 h1; exact h0.2 h1.2
      have hsum_T : randomGraphMeasure n T = 2 * randomGraphMeasure n T₀ := by
        rw [hunion, measure_union hdisj (Set.toFinite T₁).measurableSet, ← hT_eq, two_mul]
      have hhalf_T : (1 / 2 : ENNReal) * randomGraphMeasure n T = randomGraphMeasure n T₀ := by
        rw [hsum_T, ← mul_assoc, ENNReal.div_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
      have hT₀_set :
          S ∩ {G | ∀ u v : Fin n, ({u, v} : Finset (Fin n)) ∈ insert ({u₀, v₀} : Finset (Fin n)) F' →
            ¬ G.Adj u v} = T₀ := by
        ext G
        simp only [T₀, T, Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_insert]
        refine ⟨fun ⟨hGS, hall⟩ ↦ ⟨⟨hGS, fun u v hmem ↦ hall u v (Or.inr hmem)⟩,
            hall u₀ v₀ (Or.inl rfl)⟩,
          fun ⟨⟨hGS, hF'G⟩, hnAdj⟩ ↦ ⟨hGS, fun u v hmem ↦ ?_⟩⟩
        rcases hmem with heq | hmem'
        · rcases (pair_eq_iff_unordered huv₀).mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hnAdj
          · exact fun hadj ↦ hnAdj (G.adj_symm hadj)
        · exact hF'G u v hmem'
      rw [hT₀_set, ← hhalf_T, ih hF'_card hS_inv', Finset.card_insert_of_notMem he_notMem,
        pow_succ', mul_assoc]
  refine ⟨henn, ?_⟩
  simp only [Measure.real, henn, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div,
    ENNReal.toReal_one, ENNReal.toReal_ofNat]

private theorem randomGraphMeasure_coloring_inter_noCrossBipartite_eq
    {n : ℕ} (P : VertexPartition n) (U₁ U₂ : Finset (Fin n))
    (hdisj : Disjoint U₁ U₂)
    (hcross : ∀ x ∈ U₁, ∀ y ∈ U₂, ¬ ∃ B ∈ P.parts, x ∈ B ∧ y ∈ B) :
    (randomGraphMeasure n).real
        (partitionColoringEvent P ∩ {G : LabeledGraph n | ∀ x ∈ U₁, ∀ y ∈ U₂, ¬ G.Adj x y}) =
      (1 / 2 : ℝ) ^ (U₁.card * U₂.card) *
        (randomGraphMeasure n).real (partitionColoringEvent P) := by
  classical
  let F : Finset (Finset (Fin n)) := (U₁ ×ˢ U₂).image fun p ↦ ({p.1, p.2} : Finset (Fin n))
  have hne_xy : ∀ x ∈ U₁, ∀ y ∈ U₂, x ≠ y :=
    fun x hx y hy heq ↦ Finset.disjoint_left.mp hdisj hx (heq ▸ hy)
  have hF_card2 : ∀ e ∈ F, e.card = 2 := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨⟨x, y⟩, hxy, rfl⟩
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
    exact Finset.card_pair (hne_xy x hx y hy)
  have hF_size : F.card = U₁.card * U₂.card := by
    rw [Finset.card_image_of_injOn, Finset.card_product]
    intro ⟨x₁, y₁⟩ h1 ⟨x₂, y₂⟩ h2 heq
    dsimp only at heq
    obtain ⟨hx₁, hy₁⟩ := Finset.mem_product.mp h1
    obtain ⟨hx₂, hy₂⟩ := Finset.mem_product.mp h2
    rcases (pair_eq_iff_unordered (hne_xy x₂ hx₂ y₂ hy₂)).mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact (Finset.disjoint_left.mp hdisj hx₁ hy₂).elim
  have hP_inv : ∀ G H : LabeledGraph n,
      (∀ u v : Fin n, u ≠ v → ({u, v} : Finset (Fin n)) ∉ F → (G.Adj u v ↔ H.Adj u v)) →
      (G ∈ partitionColoringEvent P ↔ H ∈ partitionColoringEvent P) := by
    intro G H hGH
    have hnotF : ∀ B ∈ P.parts, ∀ u ∈ B, ∀ v ∈ B, ({u, v} : Finset (Fin n)) ∉ F := by
      intro B hBP u huB v hvB hmem
      rcases Finset.mem_image.mp hmem with ⟨⟨x, y⟩, hxy, heq⟩
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
      rcases (pair_eq_iff_unordered (hne_xy x hx y hy)).mp heq.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hcross u hx v hy ⟨B, hBP, huB, hvB⟩
      · exact hcross v hx u hy ⟨B, hBP, hvB, huB⟩
    constructor
    · intro hG B hBP u hu v hv huv hadjH
      exact hG B hBP hu hv huv ((hGH u v huv (hnotF B hBP u hu v hv)).mpr hadjH)
    · intro hH B hBP u hu v hv huv hadjG
      exact hH B hBP hu hv huv ((hGH u v huv (hnotF B hBP u hu v hv)).mp hadjG)
  have hset_eq :
      {G : LabeledGraph n | ∀ x ∈ U₁, ∀ y ∈ U₂, ¬ G.Adj x y} =
        {G : LabeledGraph n | ∀ u v : Fin n, ({u, v} : Finset (Fin n)) ∈ F → ¬ G.Adj u v} := by
    ext G
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h u v hmem
      rcases Finset.mem_image.mp hmem with ⟨⟨x, y⟩, hxy, heq⟩
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
      rcases (pair_eq_iff_unordered (hne_xy x hx y hy)).mp heq.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h u hx v hy
      · exact fun hadj ↦ h v hx u hy (G.adj_symm hadj)
    · intro h x hx y hy
      exact h x y (Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩)
  rw [hset_eq, ← hF_size]
  exact (randomGraphMeasure_inter_noEdges_eq_half_pow F hF_card2 hP_inv).2

/-- **Lemma 7.1 cross-edge `Bernoulli(1/2)` conditioning and mark-invariance (`main.tex` lines 981, 1023–1024):**
for any vertex partition `P : VertexPartition n`:
1. **(Independent `Bernoulli(1/2)` cross-class edges given `A_P`):** for every set `F` of unordered
   cross-class pairs (`e.card = 2` and `¬ ∃ B ∈ P.parts, e ⊆ B`),
   `P(A_P ∩ {no edges on F}) = (1/2)^|F| * P(A_P)`;
2. **(Mark-invariance of cross-class events):** for every cross-class event `E` (whose membership
   depends only on edges between distinct parts of `P`) and every marking `σ : P.parts → Bool`,
   `P(partitionMarkedEvent P σ ∩ E) = P(A_P ∩ E)` (in both `ENNReal` and `.real`), and when all
   parts of `P` have size `≥ 2`, `P(A_P^co ∩ E) = 2^|P.parts| * P(A_P ∩ E)`. -/
theorem randomGraphMeasure_partitionColoring_and_marked_inter_crossEvent_eq
    {n : ℕ} (P : VertexPartition n) :
    (∀ F : Finset (Finset (Fin n)),
      (∀ e ∈ F, e.card = 2 ∧ ¬ ∃ B ∈ P.parts, e ⊆ B) →
      (randomGraphMeasure n).real
          (partitionColoringEvent P ∩
            {G : LabeledGraph n | ∀ u v : Fin n, ({u, v} : Finset (Fin n)) ∈ F → ¬ G.Adj u v}) =
        (1 / 2 : ℝ) ^ F.card * (randomGraphMeasure n).real (partitionColoringEvent P)) ∧
    (∀ (E : Set (LabeledGraph n)),
      (∀ G H : LabeledGraph n,
        (∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B → ∀ u ∈ A, ∀ v ∈ B, (G.Adj u v ↔ H.Adj u v)) →
        (G ∈ E ↔ H ∈ E)) →
      (∀ σ : P.parts → Bool,
        randomGraphMeasure n (partitionMarkedEvent P σ ∩ E) =
          randomGraphMeasure n (partitionColoringEvent P ∩ E) ∧
        (randomGraphMeasure n).real (partitionMarkedEvent P σ ∩ E) =
          (randomGraphMeasure n).real (partitionColoringEvent P ∩ E)) ∧
      ((∀ B ∈ P.parts, 2 ≤ B.card) →
        (randomGraphMeasure n).real (partitionCocoloringEvent P ∩ E) =
          (2 : ℝ) ^ P.parts.card *
            (randomGraphMeasure n).real (partitionColoringEvent P ∩ E))) := by
  classical
  refine ⟨fun F hF ↦ ?_, fun E hCross ↦ ?_⟩
  · refine (randomGraphMeasure_inter_noEdges_eq_half_pow F (fun e he ↦ (hF e he).1) ?_).2
    intro G H hGH
    have hnotF : ∀ B ∈ P.parts, ∀ u ∈ B, ∀ v ∈ B, ({u, v} : Finset (Fin n)) ∉ F := by
      intro B hBP u huB v hvB hmem
      apply (hF _ hmem).2
      refine ⟨B, hBP, fun x hx ↦ ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    constructor
    · intro hG B hBP u hu v hv huv hadjH
      exact hG B hBP hu hv huv ((hGH u v huv (hnotF B hBP u hu v hv)).mpr hadjH)
    · intro hH B hBP u hu v hv huv hadjG
      exact hH B hBP hu hv huv ((hGH u v huv (hnotF B hBP u hu v hv)).mp hadjG)
  · have hflip_cross : ∀ (σ : P.parts → Bool) (G : LabeledGraph n),
        flipMarkedInternal P σ G ∈ E ↔ G ∈ E := by
      intro σ G
      refine hCross (flipMarkedInternal P σ G) G fun A hA B hB hAB u huA v hvB ↦ ?_
      have huv : u ≠ v := fun heq ↦ Finset.disjoint_left.mp (P.disjoint hA hB hAB) huA (heq ▸ hvB)
      have hnot_mk : ¬ markedPair P σ u v := by
        rintro ⟨D, _, huD, hvD⟩
        have hDA : D.1 = A := by
          by_contra hne; exact Finset.disjoint_left.mp (P.disjoint D.2 hA hne) huD huA
        have hDB : D.1 = B := by
          by_contra hne; exact Finset.disjoint_left.mp (P.disjoint D.2 hB hne) hvD hvB
        exact hAB (hDA.symm.trans hDB)
      change flipMarkedAdj P σ G u v ↔ G.Adj u v
      unfold flipMarkedAdj
      simp [huv, hnot_mk]
    have hmark : ∀ σ : P.parts → Bool,
        randomGraphMeasure n (partitionMarkedEvent P σ ∩ E) =
          randomGraphMeasure n (partitionColoringEvent P ∩ E) := by
      intro σ
      apply le_antisymm
      · exact randomGraphMeasure_image_le_of_involutive (flipMarkedInternal P σ)
          (flipMarkedInternal_involutive P σ)
          fun G ⟨hGm, hGE⟩ ↦ ⟨flipMarkedInternal_mem_partitionColoringEvent hGm,
            (hflip_cross σ G).mpr hGE⟩
      · refine randomGraphMeasure_image_le_of_involutive (flipMarkedInternal P σ)
          (flipMarkedInternal_involutive P σ) fun G ⟨hGc, hGE⟩ ↦ ⟨?_, (hflip_cross σ G).mpr hGE⟩
        intro B
        have hB_eq : ∀ D : P.parts, ∀ u ∈ B.1, u ∈ D.1 → D = B := by
          intro D u huB huD
          apply Subtype.ext
          by_contra hne
          exact (Finset.disjoint_left.mp (P.disjoint D.2 B.2 hne) huD) huB
        have hBind := hGc B.1 B.2
        cases hσB : σ B
        · simp only [Bool.false_eq_true, ↓reduceIte]
          intro u hu v hv huv hadj
          change flipMarkedAdj P σ G u v at hadj
          unfold flipMarkedAdj at hadj
          have hnot : ¬ markedPair P σ u v := by
            rintro ⟨D, hσD, huD, -⟩
            rw [hB_eq D u hu huD, hσB] at hσD
            exact Bool.false_ne_true hσD
          rw [if_neg hnot] at hadj
          exact hBind hu hv huv hadj.2
        · simp only [↓reduceIte]
          intro u hu v hv huv
          change flipMarkedAdj P σ G u v
          unfold flipMarkedAdj
          have hex : markedPair P σ u v := ⟨B, hσB, hu, hv⟩
          exact ⟨huv, by rw [if_pos hex]; exact hBind hu hv huv⟩
    refine ⟨fun σ ↦ ⟨hmark σ, by simp only [Measure.real, hmark σ]⟩, fun hP2 ↦ ?_⟩
    have hunion :
        partitionCocoloringEvent P ∩ E = ⋃ σ : P.parts → Bool, (partitionMarkedEvent P σ ∩ E) := by
      ext G
      simp only [Set.mem_inter_iff, Set.mem_iUnion]
      constructor
      · rintro ⟨hGco, hGE⟩
        refine ⟨fun B ↦ decide (G.IsClique (B.1 : Set (Fin n))), ⟨?_, hGE⟩⟩
        intro B
        by_cases hcl : G.IsClique (B.1 : Set (Fin n))
        · simp [hcl]
        · simp only [hcl, decide_false, Bool.false_eq_true, ↓reduceIte]
          exact (hGco B.1 B.2).resolve_right hcl
      · rintro ⟨σ, hGσ, hGE⟩
        refine ⟨fun B hB ↦ ?_, hGE⟩
        have hBσ := hGσ ⟨B, hB⟩
        cases hval : σ ⟨B, hB⟩
        · simp only [hval, Bool.false_eq_true, ↓reduceIte] at hBσ; exact Or.inl hBσ
        · simp only [hval, ↓reduceIte] at hBσ; exact Or.inr hBσ
    have hdisj : Pairwise fun σ τ : P.parts → Bool ↦
        Disjoint (partitionMarkedEvent P σ ∩ E) (partitionMarkedEvent P τ ∩ E) := by
      intro σ τ hne
      rw [Set.disjoint_left]
      intro G ⟨hGσ, _⟩ ⟨hGτ, _⟩
      obtain ⟨B, hBne⟩ := Function.ne_iff.mp hne
      obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (Nat.lt_of_lt_of_le Nat.one_lt_two (hP2 B.1 B.2))
      have hσB := hGσ B
      have hτB := hGτ B
      cases hs : σ B <;> cases ht : τ B
      · exact hBne (hs.trans ht.symm)
      · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hσB
        simp only [ht, ↓reduceIte] at hτB
        exact hσB hu hv huv (hτB hu hv huv)
      · simp only [hs, ↓reduceIte] at hσB
        simp only [ht, Bool.false_eq_true, ↓reduceIte] at hτB
        exact hτB hu hv huv (hσB hu hv huv)
      · exact hBne (hs.trans ht.symm)
    have henn :
        randomGraphMeasure n (partitionCocoloringEvent P ∩ E) =
          (2 : ENNReal) ^ P.parts.card * randomGraphMeasure n (partitionColoringEvent P ∩ E) := by
      rw [hunion, measure_iUnion hdisj (fun _ ↦ (Set.toFinite _).measurableSet), tsum_fintype]
      calc ∑ σ : P.parts → Bool, randomGraphMeasure n (partitionMarkedEvent P σ ∩ E)
          = ∑ _σ : P.parts → Bool, randomGraphMeasure n (partitionColoringEvent P ∩ E) :=
            Finset.sum_congr rfl fun σ _ ↦ hmark σ
        _ = (Fintype.card (P.parts → Bool) : ENNReal) *
              randomGraphMeasure n (partitionColoringEvent P ∩ E) := by
            simp [Finset.sum_const, nsmul_eq_mul]
        _ = (2 : ENNReal) ^ P.parts.card * randomGraphMeasure n (partitionColoringEvent P ∩ E) := by
            rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]; norm_cast
    simp only [Measure.real, henn, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat]

private theorem rg_mono {n : ℕ} {A B : Set (LabeledGraph n)} (h : A ⊆ B) :
    (randomGraphMeasure n).real A ≤ (randomGraphMeasure n).real B :=
  measureReal_mono h (measure_ne_top _ _)

private theorem rg_biUnion_finset_le {α_idx : Type*} {n : ℕ}
    (S : Finset α_idx) (f : α_idx → Set (LabeledGraph n)) :
    (randomGraphMeasure n).real (⋃ x ∈ S, f x) ≤
      ∑ x ∈ S, (randomGraphMeasure n).real (f x) := by
  classical
  have henn : randomGraphMeasure n (⋃ x ∈ S, f x) ≤ ∑ x ∈ S, randomGraphMeasure n (f x) :=
    measure_biUnion_finset_le S f
  have hfin : (∑ x ∈ S, randomGraphMeasure n (f x)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun _ _ ↦ measure_ne_top _ _
  have htr := ENNReal.toReal_mono hfin henn
  unfold Measure.real
  rwa [ENNReal.toReal_sum fun _ _ ↦ measure_ne_top _ _] at htr

private theorem vertexPartition_parts_card_le {n : ℕ} (P : VertexPartition n) :
    P.parts.card ≤ n := by
  calc P.parts.card
      = ∑ _B ∈ P.parts, 1 := by simp
    _ ≤ ∑ B ∈ P.parts, B.card :=
        Finset.sum_le_sum fun B hB ↦ (P.nonempty_of_mem_parts hB).card_pos
    _ = (Finset.univ : Finset (Fin n)).card := P.sum_card_parts
    _ = n := Finset.card_fin n

private theorem nat_choose_le_pow : ∀ a k : ℕ, a.choose k ≤ a ^ k
  | _, 0 => by simp
  | 0, _ + 1 => by simp
  | a + 1, k + 1 => by
    rw [Nat.choose_succ_succ]
    calc a.choose k + a.choose (k + 1)
        ≤ a ^ k + a ^ (k + 1) :=
          Nat.add_le_add (nat_choose_le_pow a k) (nat_choose_le_pow a (k + 1))
      _ = a ^ k * (a + 1) := by ring
      _ ≤ (a + 1) ^ k * (a + 1) :=
          Nat.mul_le_mul_right (a + 1) (Nat.pow_le_pow_left (Nat.le_succ a) k)
      _ = (a + 1) ^ (k + 1) := by ring

private theorem nat_choose_le_two_pow : ∀ a k : ℕ, a.choose k ≤ 2 ^ a
  | 0, 0 => by simp
  | 0, _ + 1 => by simp
  | a + 1, 0 => by simp [Nat.one_le_two_pow]
  | a + 1, k + 1 => by
    rw [Nat.choose_succ_succ, pow_succ]
    linarith [nat_choose_le_two_pow a k, nat_choose_le_two_pow a (k + 1)]

private theorem half_pow_le_two_pow_mul_half_pow {A B K : ℕ} (h : A ≤ B + K) :
    (1 / 2 : ℝ) ^ B ≤ (2 : ℝ) ^ K * (1 / 2 : ℝ) ^ A := by
  have h1 : (1 / 2 : ℝ) ^ (B + K) ≤ (1 / 2 : ℝ) ^ A :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) h
  rw [pow_add] at h1
  have hm := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ K)
  have hc : (2 : ℝ) ^ K * ((1 / 2 : ℝ) ^ B * (1 / 2 : ℝ) ^ K) = (1 / 2 : ℝ) ^ B := by
    calc (2 : ℝ) ^ K * ((1 / 2 : ℝ) ^ B * (1 / 2 : ℝ) ^ K)
        = ((2 : ℝ) ^ K * (1 / 2 : ℝ) ^ K) * (1 / 2 : ℝ) ^ B := by ring
      _ = ((2 : ℝ) * (1 / 2 : ℝ)) ^ K * (1 / 2 : ℝ) ^ B := by rw [← mul_pow]
      _ = (1 / 2 : ℝ) ^ B := by norm_num
  rwa [hc] at hm

private theorem log_pow_div_sq_le {x : ℝ} (hx : 1 ≤ x) {K : ℕ} (hK : 1 ≤ K) :
    (Real.log x) ^ K / x ^ 2 ≤ (2 * (K : ℝ)) ^ K / x := by
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have h2K_pos : (0 : ℝ) < 2 * (K : ℝ) := by exact_mod_cast (show 0 < 2 * K by omega)
  have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog_le : Real.log x ≤ 2 * (K : ℝ) * x ^ (1 / (2 * (K : ℝ))) := by
    have hrp_pos : 0 < x ^ (1 / (2 * (K : ℝ))) := Real.rpow_pos_of_pos hx_pos _
    have h1 := Real.log_le_sub_one_of_pos hrp_pos
    rw [Real.log_rpow hx_pos] at h1
    have hm := mul_le_mul_of_nonneg_left h1 h2K_pos.le
    have hc : 2 * (K : ℝ) * (1 / (2 * (K : ℝ)) * Real.log x) = Real.log x := by
      field_simp [h2K_pos.ne']
    linarith
  have hpow_le : (Real.log x) ^ K ≤ (2 * (K : ℝ)) ^ K * x ^ (1 / 2 : ℝ) := by
    calc (Real.log x) ^ K
        ≤ (2 * (K : ℝ) * x ^ (1 / (2 * (K : ℝ)))) ^ K :=
          pow_le_pow_left₀ hlog_nn hlog_le K
      _ = (2 * (K : ℝ)) ^ K * (x ^ (1 / (2 * (K : ℝ)))) ^ (K : ℝ) := by
          rw [mul_pow, Real.rpow_natCast]
      _ = (2 * (K : ℝ)) ^ K * x ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_mul hx_pos.le]
          congr 2
          have hK_ne : (K : ℝ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
          field_simp [hK_ne]
  have hx_half_le : x ^ (1 / 2 : ℝ) ≤ x := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (1 / 2 : ℝ) ≤ 1)
  calc (Real.log x) ^ K / x ^ 2
      ≤ ((2 * (K : ℝ)) ^ K * x) / x ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg x)
        exact hpow_le.trans (mul_le_mul_of_nonneg_left hx_half_le (by positivity))
    _ = (2 * (K : ℝ)) ^ K / x := by field_simp [hx_pos.ne']

private theorem half_pow_phaseNat_le_of_phaseDomain {n : ℕ} (hdom : PhaseDomain n) :
    (1 / 2 : ℝ) ^ (phaseNat n) ≤
      (4 / (Real.log 2) ^ 2) * (Real.log (n : ℝ)) ^ 2 / (n : ℝ) ^ 2 := by
  have hn1 : 1 < n := hdom.1
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_trans Nat.zero_lt_one hn1)
  have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1.le)
  have ha_ge : alphaZero n - 1 ≤ (phaseNat n : ℝ) := by
    rw [alphaZero_eq_phaseNat_add_delta hdom]
    linarith [phaseDelta_lt_one n]
  have hpow_le : (1 / 2 : ℝ) ^ (phaseNat n) ≤ (2 : ℝ) ^ (-(alphaZero n - 1)) := by
    have h1 : (1 / 2 : ℝ) ^ (phaseNat n) = (2 : ℝ) ^ (-(phaseNat n : ℝ)) := by
      rw [one_div, inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg two_pos.le]
    rw [h1]
    exact Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
  have hsq : (2 : ℝ) ^ (-(alphaZero n - 1)) = ((2 : ℝ) ^ (-(alphaZero n - 1) / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul two_pos.le]
    congr 1; push_cast; ring
  rw [hsq, two_rpow_neg_half_alphaZero_sub_one hn1] at hpow_le
  have hexp1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have hlb_nn : 0 ≤ 2 * logBaseTwo (n : ℝ) := by
    unfold logBaseTwo; exact mul_nonneg zero_le_two (div_nonneg hlog_nn q_pos.le)
  have hdiv_le : (2 * logBaseTwo (n : ℝ)) / (Real.exp 1 * (n : ℝ)) ≤
      (2 * logBaseTwo (n : ℝ)) / (n : ℝ) :=
    div_le_div_of_nonneg_left hlb_nn hn_pos
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hexp1 hn_pos.le)
  have hsq_le : ((2 * logBaseTwo (n : ℝ)) / (Real.exp 1 * (n : ℝ))) ^ 2 ≤
      ((2 * logBaseTwo (n : ℝ)) / (n : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hdiv_le 2
  refine hpow_le.trans (hsq_le.trans_eq ?_)
  unfold logBaseTwo q
  field_simp [hq_pos.ne', hn_pos.ne']
  ring

/-- **Lemma 7.1 `E_π` heavy cross-pair conditional probability (`main.tex` lines 982–985):**
1. **(Exact finite bound):** for every `P : VertexPartition n`, `a, m_prod : ℕ` with
   `∀ B ∈ P.parts, B.card ≤ a`, the event `E_P` that some independent set `S` satisfies
   `m_prod ≤ |S ∩ A| · |S ∩ B|` for distinct parts `A ≠ B` of `P` obeys
   `P(A_P ∩ E_P) ≤ C(|P.parts|, 2) · 2^(2 a) · 2^(-m_prod) · P(A_P)`;
2. **(Asymptotic `O(n⁻¹)` rate at `m_prod = ⌈7 log₂ n⌉`):** eventually in `n`, uniformly over all
   `P : VertexPartition n` with part sizes `≤ phaseNat n`,
   `P(A_P ∩ E_P) ≤ (1 / n) · P(A_P)`. -/
theorem condProb_heavyCrossPairEvent_le_and_eventually_inv_n :
    (∀ {n a m_prod : ℕ} (P : VertexPartition n),
      (∀ B ∈ P.parts, B.card ≤ a) →
      let E_P : Set (LabeledGraph n) :=
        {G | ∃ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) ∧
          ∃ A ∈ P.parts, ∃ B ∈ P.parts, A ≠ B ∧ m_prod ≤ (S ∩ A).card * (S ∩ B).card}
      (randomGraphMeasure n).real (partitionColoringEvent P ∩ E_P) ≤
        (P.parts.card.choose 2 : ℝ) * (2 : ℝ) ^ (2 * a) * (1 / 2 : ℝ) ^ m_prod *
          (randomGraphMeasure n).real (partitionColoringEvent P)) ∧
    (∀ᶠ n : ℕ in atTop,
      ∀ P : VertexPartition n,
        (∀ B ∈ P.parts, B.card ≤ phaseNat n) →
        let m_prod : ℕ := Nat.ceil (7 * logBaseTwo (n : ℝ))
        let E_P : Set (LabeledGraph n) :=
          {G | ∃ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) ∧
            ∃ A ∈ P.parts, ∃ B ∈ P.parts, A ≠ B ∧ m_prod ≤ (S ∩ A).card * (S ∩ B).card}
        (randomGraphMeasure n).real (partitionColoringEvent P ∩ E_P) ≤
          (1 / (n : ℝ)) * (randomGraphMeasure n).real (partitionColoringEvent P)) := by
  classical
  have hfin : ∀ {n a m_prod : ℕ} (P : VertexPartition n),
      (∀ B ∈ P.parts, B.card ≤ a) →
      let E_P : Set (LabeledGraph n) :=
        {G | ∃ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) ∧
          ∃ A ∈ P.parts, ∃ B ∈ P.parts, A ≠ B ∧ m_prod ≤ (S ∩ A).card * (S ∩ B).card}
      (randomGraphMeasure n).real (partitionColoringEvent P ∩ E_P) ≤
        (P.parts.card.choose 2 : ℝ) * (2 : ℝ) ^ (2 * a) * (1 / 2 : ℝ) ^ m_prod *
          (randomGraphMeasure n).real (partitionColoringEvent P) := by
    intro n a m_prod P hPa E_P
    let Pairs := P.parts.powersetCard 2
    let BadCell (pair : Finset (Finset (Fin n))) (U : Finset (Fin n)) : Set (LabeledGraph n) :=
      {G | ∃ A ∈ pair, ∃ B ∈ pair, A ≠ B ∧ m_prod ≤ (U ∩ A).card * (U ∩ B).card ∧
        ∀ x ∈ U ∩ A, ∀ y ∈ U ∩ B, ¬ G.Adj x y}
    have hcov : partitionColoringEvent P ∩ E_P ⊆
        ⋃ pair ∈ Pairs, ⋃ U ∈ (pair.biUnion id).powerset,
          (partitionColoringEvent P ∩ BadCell pair U) := by
      intro G ⟨hGP, S, hS_ind, A, hAP, B, hBP, hAB, hm⟩
      let pair : Finset (Finset (Fin n)) := {A, B}
      have hpair_mem : pair ∈ Pairs :=
        Finset.mem_powersetCard.mpr ⟨fun X hX ↦ by
          simp only [pair, Finset.mem_insert, Finset.mem_singleton] at hX
          rcases hX with rfl | rfl <;> assumption, Finset.card_pair hAB⟩
      let U : Finset (Fin n) := S ∩ pair.biUnion id
      have hU_mem : U ∈ (pair.biUnion id).powerset :=
        Finset.mem_powerset.mpr Finset.inter_subset_right
      have hUA : U ∩ A = S ∩ A := by
        ext x
        simp only [U, pair, Finset.mem_inter, Finset.mem_biUnion, Finset.mem_insert,
          Finset.mem_singleton, id_eq]
        exact ⟨fun ⟨⟨hxS, _⟩, hxA⟩ ↦ ⟨hxS, hxA⟩,
          fun ⟨hxS, hxA⟩ ↦ ⟨⟨hxS, A, Or.inl rfl, hxA⟩, hxA⟩⟩
      have hUB : U ∩ B = S ∩ B := by
        ext x
        simp only [U, pair, Finset.mem_inter, Finset.mem_biUnion, Finset.mem_insert,
          Finset.mem_singleton, id_eq]
        exact ⟨fun ⟨⟨hxS, _⟩, hxB⟩ ↦ ⟨hxS, hxB⟩,
          fun ⟨hxS, hxB⟩ ↦ ⟨⟨hxS, B, Or.inr rfl, hxB⟩, hxB⟩⟩
      simp only [Set.mem_iUnion, exists_prop]
      refine ⟨pair, hpair_mem, U, hU_mem, hGP, A, Finset.mem_insert_self A {B},
        B, Finset.mem_insert_of_mem (Finset.mem_singleton_self B), hAB, ?_, ?_⟩
      · rwa [hUA, hUB]
      · intro x hx y hy
        have hxS : x ∈ S := (Finset.mem_inter.mp (hUA ▸ hx)).1
        have hyS : y ∈ S := (Finset.mem_inter.mp (hUB ▸ hy)).1
        have hxy : x ≠ y := fun heq ↦
          Finset.disjoint_left.mp (P.disjoint hAP hBP hAB) (Finset.mem_inter.mp hx).2
            (heq ▸ (Finset.mem_inter.mp hy).2)
        exact hS_ind hxS hyS hxy
    have hcell_le : ∀ pair ∈ Pairs, ∀ U ∈ (pair.biUnion id).powerset,
        (randomGraphMeasure n).real (partitionColoringEvent P ∩ BadCell pair U) ≤
          (1 / 2 : ℝ) ^ m_prod * (randomGraphMeasure n).real (partitionColoringEvent P) := by
      intro pair hpair U _hU
      obtain ⟨hpair_sub, hpair_card⟩ := Finset.mem_powersetCard.mp hpair
      obtain ⟨A₀, B₀, hAB₀, rfl⟩ := Finset.card_eq_two.mp hpair_card
      have hA₀P : A₀ ∈ P.parts := hpair_sub (Finset.mem_insert_self A₀ {B₀})
      have hB₀P : B₀ ∈ P.parts :=
        hpair_sub (Finset.mem_insert_of_mem (Finset.mem_singleton_self B₀))
      by_cases hm : m_prod ≤ (U ∩ A₀).card * (U ∩ B₀).card
      · have hsub_bip : BadCell {A₀, B₀} U ⊆
            {G | ∀ x ∈ U ∩ A₀, ∀ y ∈ U ∩ B₀, ¬ G.Adj x y} := by
          rintro G ⟨A, hA, B, hB, hAB, _, hno⟩ x hx y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hA hB
          rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
          · exact (hAB rfl).elim
          · exact hno x hx y hy
          · exact fun hadj ↦ hno y hy x hx (G.adj_symm hadj)
          · exact (hAB rfl).elim
        have hdisj_U : Disjoint (U ∩ A₀) (U ∩ B₀) :=
          (P.disjoint hA₀P hB₀P hAB₀).mono Finset.inter_subset_right Finset.inter_subset_right
        have hcross_U : ∀ x ∈ U ∩ A₀, ∀ y ∈ U ∩ B₀, ¬ ∃ D ∈ P.parts, x ∈ D ∧ y ∈ D := by
          rintro x hx y hy ⟨D, hDP, hxD, hyD⟩
          have hDA : D = A₀ := by
            by_contra hne
            exact Finset.disjoint_left.mp (P.disjoint hDP hA₀P hne) hxD (Finset.mem_inter.mp hx).2
          subst hDA
          exact Finset.disjoint_left.mp (P.disjoint hA₀P hB₀P hAB₀) hyD (Finset.mem_inter.mp hy).2
        have heq_bip := randomGraphMeasure_coloring_inter_noCrossBipartite_eq P
          (U ∩ A₀) (U ∩ B₀) hdisj_U hcross_U
        have hpow_le : (1 / 2 : ℝ) ^ ((U ∩ A₀).card * (U ∩ B₀).card) ≤ (1 / 2 : ℝ) ^ m_prod :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
        calc (randomGraphMeasure n).real (partitionColoringEvent P ∩ BadCell {A₀, B₀} U)
            ≤ (randomGraphMeasure n).real
                (partitionColoringEvent P ∩ {G | ∀ x ∈ U ∩ A₀, ∀ y ∈ U ∩ B₀, ¬ G.Adj x y}) :=
              rg_mono (Set.inter_subset_inter_right _ hsub_bip)
          _ = (1 / 2 : ℝ) ^ ((U ∩ A₀).card * (U ∩ B₀).card) *
                (randomGraphMeasure n).real (partitionColoringEvent P) := heq_bip
          _ ≤ (1 / 2 : ℝ) ^ m_prod * (randomGraphMeasure n).real (partitionColoringEvent P) :=
              mul_le_mul_of_nonneg_right hpow_le measureReal_nonneg
      · have hempty : BadCell {A₀, B₀} U = ∅ := by
          ext G
          simp only [BadCell, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨A, hA, B, hB, hAB, hm', _⟩
          simp only [Finset.mem_insert, Finset.mem_singleton] at hA hB
          rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
          · exact hAB rfl
          · exact hm hm'
          · exact hm (by rwa [mul_comm])
          · exact hAB rfl
        rw [hempty, Set.inter_empty, measureReal_empty]
        positivity
    have hpowerset_card : ∀ pair ∈ Pairs,
        ((pair.biUnion id).powerset.card : ℝ) ≤ (2 : ℝ) ^ (2 * a) := by
      intro pair hpair
      obtain ⟨hpair_sub, hpair_card⟩ := Finset.mem_powersetCard.mp hpair
      obtain ⟨A₀, B₀, hAB₀, rfl⟩ := Finset.card_eq_two.mp hpair_card
      have hA₀P : A₀ ∈ P.parts := hpair_sub (Finset.mem_insert_self A₀ {B₀})
      have hB₀P : B₀ ∈ P.parts :=
        hpair_sub (Finset.mem_insert_of_mem (Finset.mem_singleton_self B₀))
      have hbi : ({A₀, B₀} : Finset (Finset (Fin n))).biUnion id = A₀ ∪ B₀ := by simp
      have hc_le : (A₀ ∪ B₀).card ≤ 2 * a := by
        calc (A₀ ∪ B₀).card ≤ A₀.card + B₀.card := Finset.card_union_le A₀ B₀
          _ ≤ a + a := Nat.add_le_add (hPa A₀ hA₀P) (hPa B₀ hB₀P)
          _ = 2 * a := by omega
      rw [hbi, Finset.card_powerset]
      exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2) hc_le
    calc (randomGraphMeasure n).real (partitionColoringEvent P ∩ E_P)
        ≤ (randomGraphMeasure n).real
            (⋃ pair ∈ Pairs, ⋃ U ∈ (pair.biUnion id).powerset,
              (partitionColoringEvent P ∩ BadCell pair U)) := rg_mono hcov
      _ ≤ ∑ pair ∈ Pairs,
            (randomGraphMeasure n).real
              (⋃ U ∈ (pair.biUnion id).powerset, (partitionColoringEvent P ∩ BadCell pair U)) :=
          rg_biUnion_finset_le Pairs _
      _ ≤ ∑ pair ∈ Pairs, ∑ U ∈ (pair.biUnion id).powerset,
            (randomGraphMeasure n).real (partitionColoringEvent P ∩ BadCell pair U) :=
          Finset.sum_le_sum fun pair _ ↦ rg_biUnion_finset_le _ _
      _ ≤ ∑ pair ∈ Pairs, ∑ _U ∈ (pair.biUnion id).powerset,
            ((1 / 2 : ℝ) ^ m_prod * (randomGraphMeasure n).real (partitionColoringEvent P)) :=
          Finset.sum_le_sum fun pair hp ↦ Finset.sum_le_sum fun U hU ↦ hcell_le pair hp U hU
      _ = ∑ pair ∈ Pairs,
            (((pair.biUnion id).powerset.card : ℝ) *
              ((1 / 2 : ℝ) ^ m_prod * (randomGraphMeasure n).real (partitionColoringEvent P))) := by
          refine Finset.sum_congr rfl fun pair _ ↦ ?_
          simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ _pair ∈ Pairs,
            ((2 : ℝ) ^ (2 * a) *
              ((1 / 2 : ℝ) ^ m_prod * (randomGraphMeasure n).real (partitionColoringEvent P))) :=
          Finset.sum_le_sum fun pair hp ↦
            mul_le_mul_of_nonneg_right (hpowerset_card pair hp) (by positivity)
      _ = (P.parts.card.choose 2 : ℝ) * (2 : ℝ) ^ (2 * a) * (1 / 2 : ℝ) ^ m_prod *
            (randomGraphMeasure n).real (partitionColoringEvent P) := by
          simp [Pairs, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
          ring
  refine ⟨hfin, ?_⟩
  have hlog_big : ∀ᶠ n : ℕ in atTop, Real.exp 1 ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (Real.exp 1)
  filter_upwards [hlog_big, eventually_phaseRoot_domain_pos_and_target_corridor] with
    n hlog_e hcenterDom P hPa
  intro m_prod E_P
  have hdom : PhaseDomain n := hcenterDom.1
  have hn1 : 1 < n := hdom.1
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_trans Nat.zero_lt_one hn1)
  have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hq_le1 : Real.log 2 ≤ 1 := le_trans Real.log_two_lt_d9.le (by norm_num)
  have hlb_ge_e : Real.exp 1 ≤ logBaseTwo (n : ℝ) := by
    unfold logBaseTwo q
    calc Real.exp 1 = Real.exp 1 / 1 := (div_one _).symm
      _ ≤ Real.log (n : ℝ) / Real.log 2 :=
          div_le_div₀ ((Real.exp_pos 1).le.trans hlog_e) hlog_e hq_pos hq_le1
  have hlb_pos : 0 < logBaseTwo (n : ℝ) := lt_of_lt_of_le (Real.exp_pos 1) hlb_ge_e
  have h1 : (randomGraphMeasure n).real (partitionColoringEvent P ∩ E_P) ≤
      (P.parts.card.choose 2 : ℝ) * (2 : ℝ) ^ (2 * phaseNat n) * (1 / 2 : ℝ) ^ m_prod *
        (randomGraphMeasure n).real (partitionColoringEvent P) := hfin P hPa
  have hchoose_le : (P.parts.card.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hc := nat_choose_le_pow P.parts.card 2
    have hcard := vertexPartition_parts_card_le P
    exact_mod_cast hc.trans (Nat.pow_le_pow_left hcard 2)
  have h2a_le : (2 : ℝ) ^ (2 * phaseNat n) ≤
      ((Real.exp 1) ^ 4 / 4) * (n : ℝ) ^ 4 / (logBaseTwo (n : ℝ)) ^ 4 := by
    have ha_le : (phaseNat n : ℝ) ≤ alphaZero n := by
      rw [alphaZero_eq_phaseNat_add_delta hdom]
      linarith [phaseDelta_nonneg n]
    have hpow1 : (2 : ℝ) ^ (2 * phaseNat n) ≤ (2 : ℝ) ^ (2 * alphaZero n) := by
      rw [← Real.rpow_natCast]
      push_cast
      exact Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
    have hid_c := two_rpow_neg_half_alphaZero_sub_one hn1
    have hpow4 : ((2 : ℝ) ^ (-(alphaZero n - 1) / 2)) ^ (4 : ℕ) = (2 : ℝ) ^ (-(2 * alphaZero n - 2)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul two_pos.le]
      congr 1; push_cast; ring
    have h2a0 : (2 : ℝ) ^ (2 * alphaZero n) =
        4 * (((2 : ℝ) ^ (-(alphaZero n - 1) / 2)) ^ (4 : ℕ))⁻¹ := by
      rw [hpow4, ← Real.rpow_neg two_pos.le, show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num,
        ← Real.rpow_add two_pos]
      congr 1; ring
    rw [h2a0, hid_c] at hpow1
    refine hpow1.trans_eq ?_
    field_simp [hlb_pos.ne', hn_pos.ne', (Real.exp_pos 1).ne']
    ring
  have hm_le : (1 / 2 : ℝ) ^ m_prod ≤ 1 / (n : ℝ) ^ 7 := by
    have hceil : 7 * logBaseTwo (n : ℝ) ≤ (m_prod : ℝ) := Nat.le_ceil _
    have hp1 : (1 / 2 : ℝ) ^ m_prod = (2 : ℝ) ^ (-(m_prod : ℝ)) := by
      rw [one_div, inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg two_pos.le]
    rw [hp1]
    calc (2 : ℝ) ^ (-(m_prod : ℝ))
        ≤ (2 : ℝ) ^ (-(7 * logBaseTwo (n : ℝ))) :=
          Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
      _ = 1 / (n : ℝ) ^ 7 := by
          rw [Real.rpow_def_of_pos two_pos]
          unfold logBaseTwo q
          have hexp_eq : Real.log 2 * -(7 * (Real.log (n : ℝ) / Real.log 2)) =
              Real.log (1 / (n : ℝ) ^ 7) := by
            rw [one_div, Real.log_inv, Real.log_pow]
            field_simp [hq_pos.ne']
            push_cast
            ring
          rw [hexp_eq, Real.exp_log (by positivity)]
  have hprod_coeff :
      (P.parts.card.choose 2 : ℝ) * (2 : ℝ) ^ (2 * phaseNat n) * (1 / 2 : ℝ) ^ m_prod ≤
        1 / (n : ℝ) := by
    have hstep1 :
        (P.parts.card.choose 2 : ℝ) * (2 : ℝ) ^ (2 * phaseNat n) * (1 / 2 : ℝ) ^ m_prod ≤
          (n : ℝ) ^ 2 * (((Real.exp 1) ^ 4 / 4) * (n : ℝ) ^ 4 / (logBaseTwo (n : ℝ)) ^ 4) *
            (1 / (n : ℝ) ^ 7) := by
      refine mul_le_mul (mul_le_mul hchoose_le h2a_le (by positivity) (by positivity))
        hm_le (by positivity) (by positivity)
    have hlb4 : (Real.exp 1) ^ 4 / 4 ≤ (logBaseTwo (n : ℝ)) ^ 4 := by
      have hpow := pow_le_pow_left₀ (Real.exp_pos 1).le hlb_ge_e 4
      linarith [pow_pos (Real.exp_pos 1) 4]
    have hfrac_le1 : ((Real.exp 1) ^ 4 / 4) / (logBaseTwo (n : ℝ)) ^ 4 ≤ 1 :=
      (div_le_one (pow_pos hlb_pos 4)).mpr hlb4
    refine hstep1.trans ?_
    calc (n : ℝ) ^ 2 * (((Real.exp 1) ^ 4 / 4) * (n : ℝ) ^ 4 / (logBaseTwo (n : ℝ)) ^ 4) *
            (1 / (n : ℝ) ^ 7)
        = (((Real.exp 1) ^ 4 / 4) / (logBaseTwo (n : ℝ)) ^ 4) * (1 / (n : ℝ)) := by
            field_simp [hn_pos.ne', hlb_pos.ne']
      _ ≤ 1 * (1 / (n : ℝ)) := mul_le_mul_of_nonneg_right hfrac_le1 (by positivity)
      _ = 1 / (n : ℝ) := one_mul _
  exact h1.trans (mul_le_mul_of_nonneg_right hprod_coeff measureReal_nonneg)

/-- **Lemma 7.1 `¬ C_π` conditional regularity (`main.tex` lines 935–936, 1012–1018):**
for every `M : ℕ` and `eps > 0`, eventually in `n`, uniformly over all `P : VertexPartition n`
with part sizes `≤ phaseNat n`, the event `C_P` that every independent set `S` with
`phaseNat n - (M + 1) ≤ |S| ≤ phaseNat n` and `z(S, P) = 2` satisfies `|S ∩ B| = |S| - 1` for
some `B ∈ P.parts` obeys `P(A_P ∩ C_Pᶜ) ≤ eps · P(A_P)`. -/
theorem eventually_condProb_badTwoClassSplit_tendsto_zero
    (M : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop,
      ∀ P : VertexPartition n,
        (∀ B ∈ P.parts, B.card ≤ phaseNat n) →
        let C_P : Set (LabeledGraph n) :=
          {G | ∀ S : Finset (Fin n),
            G.IsIndepSet (S : Set (Fin n)) →
            phaseNat n - (M + 1) ≤ S.card →
            S.card ≤ phaseNat n →
            (P.parts.filter fun B ↦ (S ∩ B).Nonempty).card = 2 →
            ∃ B ∈ P.parts, (S ∩ B).card = S.card - 1}
        (randomGraphMeasure n).real (partitionColoringEvent P ∩ C_Pᶜ) ≤
          eps * (randomGraphMeasure n).real (partitionColoringEvent P) := by
  classical
  have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  set K_pow : ℕ := M + 12
  set C_coeff : ℝ := ((M + 2 : ℕ) : ℝ) * (4 : ℝ) ^ (M + 8) *
    ((2 : ℝ) ^ (4 * M + 20) * (16 / (Real.log 2) ^ 4))
  set B_top : ℝ := C_coeff * (2 * (K_pow : ℝ)) ^ K_pow
  have hB_top_pos : 0 < B_top := by dsimp [B_top, C_coeff, K_pow]; positivity
  have hn_big : ∀ᶠ n : ℕ in atTop, max 3 (Nat.ceil (B_top / eps) + 1) ≤ n :=
    eventually_ge_atTop _
  have hph_big : ∀ᶠ n : ℕ in atTop, 2 * M + 10 ≤ phaseNat n := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop ((2 * M + 10 : ℕ) : ℝ),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact_mod_cast hn.trans hph.1
  have hL1 : ∀ᶠ n : ℕ in atTop, 1 ≤ logOrder n := tendsto_logOrder_atTop.eventually_ge_atTop 1
  filter_upwards [hn_big, hph_big, hL1,
    eventually_phaseRoot_domain_pos_and_target_corridor,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with
    n hn_ge hph_ge hLn1 hcenterDom hphase P hPa
  intro C_P
  set α : ℕ := phaseNat n
  have hn3 : 3 ≤ n := (le_max_left _ _).trans hn_ge
  have hn_eps : Nat.ceil (B_top / eps) + 1 ≤ n := (le_max_right _ _).trans hn_ge
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hn1_real : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hα_ge1 : (1 : ℝ) ≤ (α : ℝ) := by exact_mod_cast (show 1 ≤ α by omega)
  let OrdPairs := (P.parts ×ˢ P.parts).filter fun p ↦ p.1 ≠ p.2
  let BadTuple (A B : Finset (Fin n)) (u ℓ : ℕ) : Set (LabeledGraph n) :=
    ⋃ U₁ ∈ A.powersetCard ℓ, ⋃ U₂ ∈ B.powersetCard (u - ℓ),
      {G : LabeledGraph n | ∀ x ∈ U₁, ∀ y ∈ U₂, ¬ G.Adj x y}
  have hcov : partitionColoringEvent P ∩ C_Pᶜ ⊆
      ⋃ p ∈ OrdPairs, ⋃ u ∈ Finset.Icc (α - (M + 1)) α, ⋃ ℓ ∈ Finset.Icc 2 (u - 2),
        (partitionColoringEvent P ∩ BadTuple p.1 p.2 u ℓ) := by
    intro G ⟨hGP, hnotC⟩
    rw [Set.mem_compl_iff] at hnotC
    simp only [C_P, Set.mem_setOf_eq, not_forall, not_exists] at hnotC
    rcases hnotC with ⟨S, hS_ind, hu_lo, hu_hi, hz2, hno_m1⟩
    obtain ⟨A, B, hAB, hfilt_eq⟩ := Finset.card_eq_two.mp hz2
    have hAmem : A ∈ P.parts.filter (fun D ↦ (S ∩ D).Nonempty) := by
      rw [hfilt_eq]; exact Finset.mem_insert_self A {B}
    have hBmem : B ∈ P.parts.filter (fun D ↦ (S ∩ D).Nonempty) := by
      rw [hfilt_eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self B)
    obtain ⟨hAP, hSA_ne⟩ := Finset.mem_filter.mp hAmem
    obtain ⟨hBP, hSB_ne⟩ := Finset.mem_filter.mp hBmem
    have hS_union : S = (S ∩ A) ∪ (S ∩ B) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_inter]
      refine ⟨fun hxS ↦ ?_, fun h ↦ h.elim And.left And.left⟩
      have hxU : x ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ x
      rw [← P.sup_parts, Finset.sup_eq_biUnion, Finset.mem_biUnion] at hxU
      rcases hxU with ⟨D, hDP, hxD⟩
      have hDf : D ∈ P.parts.filter (fun E ↦ (S ∩ E).Nonempty) :=
        Finset.mem_filter.mpr ⟨hDP, ⟨x, Finset.mem_inter.mpr ⟨hxS, hxD⟩⟩⟩
      rw [hfilt_eq, Finset.mem_insert, Finset.mem_singleton] at hDf
      rcases hDf with rfl | rfl
      · exact Or.inl ⟨hxS, hxD⟩
      · exact Or.inr ⟨hxS, hxD⟩
    have hdisj_AB : Disjoint (S ∩ A) (S ∩ B) :=
      (P.disjoint hAP hBP hAB).mono Finset.inter_subset_right Finset.inter_subset_right
    have hcard_sum : (S ∩ A).card + (S ∩ B).card = S.card := by
      conv_rhs => rw [hS_union, Finset.card_union_of_disjoint hdisj_AB]
    have hcA1 : 1 ≤ (S ∩ A).card := hSA_ne.card_pos
    have hcB1 : 1 ≤ (S ∩ B).card := hSB_ne.card_pos
    have hcA_ne : (S ∩ A).card ≠ S.card - 1 := fun h ↦ hno_m1 A ⟨hAP, h⟩
    have hcB_ne : (S ∩ B).card ≠ S.card - 1 := fun h ↦ hno_m1 B ⟨hBP, h⟩
    have hℓ_ge2 : 2 ≤ (S ∩ A).card := by omega
    have hℓ_le : (S ∩ A).card ≤ S.card - 2 := by omega
    have hSB_card : (S ∩ B).card = S.card - (S ∩ A).card := by omega
    simp only [Set.mem_iUnion, exists_prop]
    refine ⟨(A, B), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hAP, hBP⟩, hAB⟩,
      S.card, Finset.mem_Icc.mpr ⟨hu_lo, hu_hi⟩,
      (S ∩ A).card, Finset.mem_Icc.mpr ⟨hℓ_ge2, hℓ_le⟩, hGP, ?_⟩
    simp only [BadTuple, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    refine ⟨S ∩ A, Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, rfl⟩,
      S ∩ B, Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, hSB_card⟩, ?_⟩
    intro x hx y hy
    have hxy : x ≠ y := fun heq ↦ Finset.disjoint_left.mp hdisj_AB hx (heq ▸ hy)
    exact hS_ind (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hy).1 hxy
  have hhalf_α := half_pow_phaseNat_le_of_phaseDomain hcenterDom.1
  have hhalf_2α : ((1 / 2 : ℝ) ^ α) ^ 2 ≤
      (16 / (Real.log 2) ^ 4) * (Real.log (n : ℝ)) ^ 4 / (n : ℝ) ^ 4 := by
    calc ((1 / 2 : ℝ) ^ α) ^ 2
        ≤ ((4 / (Real.log 2) ^ 2) * (Real.log (n : ℝ)) ^ 2 / (n : ℝ) ^ 2) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hhalf_α 2
      _ = (16 / (Real.log 2) ^ 4) * (Real.log (n : ℝ)) ^ 4 / (n : ℝ) ^ 4 := by ring
  have htuple_le : ∀ p ∈ OrdPairs, ∀ u ∈ Finset.Icc (α - (M + 1)) α, ∀ ℓ ∈ Finset.Icc 2 (u - 2),
      (randomGraphMeasure n).real (partitionColoringEvent P ∩ BadTuple p.1 p.2 u ℓ) ≤
        ((α : ℝ) ^ (M + 7) * ((2 : ℝ) ^ (4 * M + 20) * ((1 / 2 : ℝ) ^ α) ^ 2)) *
          (randomGraphMeasure n).real (partitionColoringEvent P) := by
    intro p hp u hu ℓ hℓ
    obtain ⟨hp_prod, hAB⟩ := Finset.mem_filter.mp hp
    obtain ⟨hAP, hBP⟩ := Finset.mem_product.mp hp_prod
    obtain ⟨hu_lo, hu_hi⟩ := Finset.mem_Icc.mp hu
    obtain ⟨hℓ_lo, hℓ_hi⟩ := Finset.mem_Icc.mp hℓ
    have hcell : ∀ U₁ ∈ p.1.powersetCard ℓ, ∀ U₂ ∈ p.2.powersetCard (u - ℓ),
        (randomGraphMeasure n).real
            (partitionColoringEvent P ∩ {G | ∀ x ∈ U₁, ∀ y ∈ U₂, ¬ G.Adj x y}) =
          (1 / 2 : ℝ) ^ (ℓ * (u - ℓ)) *
            (randomGraphMeasure n).real (partitionColoringEvent P) := by
      intro U₁ hU₁ U₂ hU₂
      obtain ⟨hU₁_sub, hU₁_c⟩ := Finset.mem_powersetCard.mp hU₁
      obtain ⟨hU₂_sub, hU₂_c⟩ := Finset.mem_powersetCard.mp hU₂
      have hdisj_U : Disjoint U₁ U₂ := (P.disjoint hAP hBP hAB).mono hU₁_sub hU₂_sub
      have hcross_U : ∀ x ∈ U₁, ∀ y ∈ U₂, ¬ ∃ D ∈ P.parts, x ∈ D ∧ y ∈ D := by
        rintro x hx y hy ⟨D, hDP, hxD, hyD⟩
        have hDA : D = p.1 := by
          by_contra hne; exact Finset.disjoint_left.mp (P.disjoint hDP hAP hne) hxD (hU₁_sub hx)
        subst hDA
        exact Finset.disjoint_left.mp (P.disjoint hAP hBP hAB) hyD (hU₂_sub hy)
      rw [← hU₂_c, ← hU₁_c]
      exact randomGraphMeasure_coloring_inter_noCrossBipartite_eq P U₁ U₂ hdisj_U hcross_U
    have hunion_le :
        (randomGraphMeasure n).real (partitionColoringEvent P ∩ BadTuple p.1 p.2 u ℓ) ≤
          (p.1.card.choose ℓ : ℝ) * (p.2.card.choose (u - ℓ) : ℝ) *
            (1 / 2 : ℝ) ^ (ℓ * (u - ℓ)) *
            (randomGraphMeasure n).real (partitionColoringEvent P) := by
      have hid_int : partitionColoringEvent P ∩ BadTuple p.1 p.2 u ℓ =
          ⋃ U₁ ∈ p.1.powersetCard ℓ, ⋃ U₂ ∈ p.2.powersetCard (u - ℓ),
            (partitionColoringEvent P ∩ {G | ∀ x ∈ U₁, ∀ y ∈ U₂, ¬ G.Adj x y}) := by
        ext G; simp [BadTuple]
      rw [hid_int]
      calc (randomGraphMeasure n).real
              (⋃ U₁ ∈ p.1.powersetCard ℓ, ⋃ U₂ ∈ p.2.powersetCard (u - ℓ),
                (partitionColoringEvent P ∩ {G | ∀ x ∈ U₁, ∀ y ∈ U₂, ¬ G.Adj x y}))
          ≤ ∑ U₁ ∈ p.1.powersetCard ℓ,
              (randomGraphMeasure n).real
                (⋃ U₂ ∈ p.2.powersetCard (u - ℓ),
                  (partitionColoringEvent P ∩ {G | ∀ x ∈ U₁, ∀ y ∈ U₂, ¬ G.Adj x y})) :=
            rg_biUnion_finset_le _ _
        _ ≤ ∑ U₁ ∈ p.1.powersetCard ℓ, ∑ U₂ ∈ p.2.powersetCard (u - ℓ),
              (randomGraphMeasure n).real
                (partitionColoringEvent P ∩ {G | ∀ x ∈ U₁, ∀ y ∈ U₂, ¬ G.Adj x y}) :=
            Finset.sum_le_sum fun U₁ _ ↦ rg_biUnion_finset_le _ _
        _ = ∑ U₁ ∈ p.1.powersetCard ℓ, ∑ U₂ ∈ p.2.powersetCard (u - ℓ),
              ((1 / 2 : ℝ) ^ (ℓ * (u - ℓ)) *
                (randomGraphMeasure n).real (partitionColoringEvent P)) :=
            Finset.sum_congr rfl fun U₁ hU₁ ↦ Finset.sum_congr rfl fun U₂ hU₂ ↦ hcell U₁ hU₁ U₂ hU₂
        _ = (p.1.card.choose ℓ : ℝ) * (p.2.card.choose (u - ℓ) : ℝ) *
              (1 / 2 : ℝ) ^ (ℓ * (u - ℓ)) *
              (randomGraphMeasure n).real (partitionColoringEvent P) := by
            simp [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
            ring
    have hch_mono : (p.1.card.choose ℓ : ℝ) * (p.2.card.choose (u - ℓ) : ℝ) ≤
        (α.choose ℓ : ℝ) * (α.choose (u - ℓ) : ℝ) := by
      have h1 : p.1.card.choose ℓ ≤ α.choose ℓ := Nat.choose_le_choose ℓ (hPa p.1 hAP)
      have h2 : p.2.card.choose (u - ℓ) ≤ α.choose (u - ℓ) :=
        Nat.choose_le_choose (u - ℓ) (hPa p.2 hBP)
      exact_mod_cast Nat.mul_le_mul h1 h2
    have hcase_split :
        (α.choose ℓ : ℝ) * (α.choose (u - ℓ) : ℝ) * (1 / 2 : ℝ) ^ (ℓ * (u - ℓ)) ≤
          (α : ℝ) ^ (M + 7) * ((2 : ℝ) ^ (4 * M + 20) * ((1 / 2 : ℝ) ^ α) ^ 2) := by
      by_cases h4 : 4 ≤ ℓ ∧ 4 ≤ u - ℓ
      · have hpow_ge : 4 * α ≤ ℓ * (u - ℓ) + (4 * M + 20) := by
          have hmul4 : 4 * (u - 4) ≤ ℓ * (u - ℓ) := by
            have h0 : 0 ≤ (ℓ - 4) * ((u - ℓ) - 4) := Nat.zero_le _
            zify [h4.1, h4.2, (show ℓ ≤ u by omega), (show 4 ≤ u by omega)] at h0 ⊢
            nlinarith
          have : 2 * M + 10 ≤ α := hph_ge
          omega
        have hch2 : (α.choose ℓ : ℝ) * (α.choose (u - ℓ) : ℝ) ≤ (2 : ℝ) ^ (2 * α) := by
          have c1 := nat_choose_le_two_pow α ℓ
          have c2 := nat_choose_le_two_pow α (u - ℓ)
          have cm : α.choose ℓ * α.choose (u - ℓ) ≤ 2 ^ (2 * α) := by
            calc α.choose ℓ * α.choose (u - ℓ) ≤ 2 ^ α * 2 ^ α := Nat.mul_le_mul c1 c2
              _ = 2 ^ (2 * α) := by rw [← pow_add, two_mul]
          exact_mod_cast cm
        have hp_sub := half_pow_le_two_pow_mul_half_pow hpow_ge
        have hcancel : (2 : ℝ) ^ (2 * α) * ((2 : ℝ) ^ (4 * M + 20) * (1 / 2 : ℝ) ^ (4 * α)) =
            (2 : ℝ) ^ (4 * M + 20) * ((1 / 2 : ℝ) ^ α) ^ 2 := by
          have h4a : 4 * α = 2 * α + 2 * α := by omega
          rw [h4a, pow_add (1 / 2 : ℝ) (2 * α) (2 * α)]
          have hc : (2 : ℝ) ^ (2 * α) * (1 / 2 : ℝ) ^ (2 * α) = 1 := by
            rw [← mul_pow]; norm_num
          have hsq_a : (1 / 2 : ℝ) ^ (2 * α) = ((1 / 2 : ℝ) ^ α) ^ 2 := by
            rw [two_mul, pow_add, sq]
          calc (2 : ℝ) ^ (2 * α) * ((2 : ℝ) ^ (4 * M + 20) *
                ((1 / 2 : ℝ) ^ (2 * α) * (1 / 2 : ℝ) ^ (2 * α)))
              = (2 : ℝ) ^ (4 * M + 20) * ((2 : ℝ) ^ (2 * α) * (1 / 2 : ℝ) ^ (2 * α)) *
                  (1 / 2 : ℝ) ^ (2 * α) := by ring
            _ = (2 : ℝ) ^ (4 * M + 20) * ((1 / 2 : ℝ) ^ α) ^ 2 := by rw [hc, mul_one, hsq_a]
        have hα_pow_ge1 : (1 : ℝ) ≤ (α : ℝ) ^ (M + 7) := one_le_pow₀ hα_ge1
        calc (α.choose ℓ : ℝ) * (α.choose (u - ℓ) : ℝ) * (1 / 2 : ℝ) ^ (ℓ * (u - ℓ))
            ≤ (2 : ℝ) ^ (2 * α) * ((2 : ℝ) ^ (4 * M + 20) * (1 / 2 : ℝ) ^ (4 * α)) :=
              mul_le_mul hch2 hp_sub (by positivity) (by positivity)
          _ = 1 * ((2 : ℝ) ^ (4 * M + 20) * ((1 / 2 : ℝ) ^ α) ^ 2) := by rw [hcancel, one_mul]
          _ ≤ (α : ℝ) ^ (M + 7) * ((2 : ℝ) ^ (4 * M + 20) * ((1 / 2 : ℝ) ^ α) ^ 2) :=
              mul_le_mul_of_nonneg_right hα_pow_ge1 (by positivity)
      · have hpow_ge2 : 2 * α ≤ ℓ * (u - ℓ) + (2 * M + 6) := by
          have h2_lo : 2 ≤ u - ℓ := by omega
          have hmul2 : 2 * (u - 2) ≤ ℓ * (u - ℓ) := by
            have h0 : 0 ≤ (ℓ - 2) * ((u - ℓ) - 2) := Nat.zero_le _
            zify [hℓ_lo, h2_lo, (show ℓ ≤ u by omega), (show 2 ≤ u by omega)] at h0 ⊢
            nlinarith
          have : 2 * M + 10 ≤ α := hph_ge
          omega
        have hsmall_ch : ∀ {a_small b_big : ℕ},
            a_small ≤ 3 → b_big ≤ α → α - M - 4 ≤ b_big →
              α.choose a_small * α.choose b_big ≤ α ^ (M + 7) := by
          intro a_small b_big has hba hblo
          have h1 : α.choose a_small ≤ α ^ 3 :=
            (nat_choose_le_pow α a_small).trans
              (Nat.pow_le_pow_right (show 0 < α by omega) has)
          have h2 : α.choose b_big ≤ α ^ (M + 4) := by
            rw [← Nat.choose_symm hba]
            exact (nat_choose_le_pow α (α - b_big)).trans
              (Nat.pow_le_pow_right (show 0 < α by omega) (by omega))
          calc α.choose a_small * α.choose b_big
              ≤ α ^ 3 * α ^ (M + 4) := Nat.mul_le_mul h1 h2
            _ = α ^ (M + 7) := by rw [← pow_add]; congr 1; omega
        have hch_poly : (α.choose ℓ : ℝ) * (α.choose (u - ℓ) : ℝ) ≤ (α : ℝ) ^ (M + 7) := by
          rcases not_and_or.mp h4 with hℓ_lt4 | hℓ'_lt4
          · exact_mod_cast hsmall_ch (by omega : ℓ ≤ 3) (by omega) (by omega)
          · rw [mul_comm]
            exact_mod_cast hsmall_ch (by omega : u - ℓ ≤ 3) (by omega) (by omega)
        have hp_sub2 := half_pow_le_two_pow_mul_half_pow hpow_ge2
        have hsq_a : (1 / 2 : ℝ) ^ (2 * α) = ((1 / 2 : ℝ) ^ α) ^ 2 := by
          rw [two_mul, pow_add, sq]
        have h2M_le : (2 : ℝ) ^ (2 * M + 6) ≤ (2 : ℝ) ^ (4 * M + 20) :=
          pow_le_pow_right₀ one_le_two (by omega)
        calc (α.choose ℓ : ℝ) * (α.choose (u - ℓ) : ℝ) * (1 / 2 : ℝ) ^ (ℓ * (u - ℓ))
            ≤ (α : ℝ) ^ (M + 7) * ((2 : ℝ) ^ (2 * M + 6) * (1 / 2 : ℝ) ^ (2 * α)) :=
              mul_le_mul hch_poly hp_sub2 (by positivity) (by positivity)
          _ ≤ (α : ℝ) ^ (M + 7) * ((2 : ℝ) ^ (4 * M + 20) * ((1 / 2 : ℝ) ^ α) ^ 2) := by
              rw [hsq_a]
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right h2M_le (by positivity)) (by positivity)
    exact hunion_le.trans (mul_le_mul_of_nonneg_right
      ((mul_le_mul_of_nonneg_right hch_mono (by positivity)).trans hcase_split) measureReal_nonneg)
  set U_per : ℝ := (α : ℝ) ^ (M + 7) * ((2 : ℝ) ^ (4 * M + 20) * ((1 / 2 : ℝ) ^ α) ^ 2)
  have hU_per_nn : 0 ≤ U_per := by dsimp [U_per]; positivity
  have hOrd_card : (OrdPairs.card : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hsub : OrdPairs.card ≤ (P.parts ×ˢ P.parts).card := Finset.card_filter_le _ _
    rw [Finset.card_product] at hsub
    have hc := vertexPartition_parts_card_le P
    exact_mod_cast hsub.trans (by nlinarith : P.parts.card * P.parts.card ≤ n ^ 2)
  have hu_card : ((Finset.Icc (α - (M + 1)) α).card : ℝ) ≤ ((M + 2 : ℕ) : ℝ) := by
    rw [Nat.card_Icc]
    exact_mod_cast (show α + 1 - (α - (M + 1)) ≤ M + 2 by omega)
  have hℓ_card : ∀ u ∈ Finset.Icc (α - (M + 1)) α,
      ((Finset.Icc 2 (u - 2)).card : ℝ) ≤ (α : ℝ) := by
    intro u hu
    obtain ⟨_, hu_hi⟩ := Finset.mem_Icc.mp hu
    rw [Nat.card_Icc]
    exact_mod_cast (show u - 2 + 1 - 2 ≤ α by omega)
  have hsum_all :
      (randomGraphMeasure n).real (partitionColoringEvent P ∩ C_Pᶜ) ≤
        ((n : ℝ) ^ 2 * ((M + 2 : ℕ) : ℝ) * (α : ℝ) * U_per) *
          (randomGraphMeasure n).real (partitionColoringEvent P) := by
    calc (randomGraphMeasure n).real (partitionColoringEvent P ∩ C_Pᶜ)
        ≤ ∑ p ∈ OrdPairs, ∑ u ∈ Finset.Icc (α - (M + 1)) α, ∑ ℓ ∈ Finset.Icc 2 (u - 2),
            (randomGraphMeasure n).real (partitionColoringEvent P ∩ BadTuple p.1 p.2 u ℓ) := by
          refine (rg_mono hcov).trans ?_
          refine (rg_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun p _ ↦ ?_)
          exact (rg_biUnion_finset_le _ _).trans
            (Finset.sum_le_sum fun u _ ↦ rg_biUnion_finset_le _ _)
      _ ≤ ∑ _p ∈ OrdPairs, ∑ u ∈ Finset.Icc (α - (M + 1)) α, ∑ _ℓ ∈ Finset.Icc 2 (u - 2),
            (U_per * (randomGraphMeasure n).real (partitionColoringEvent P)) :=
          Finset.sum_le_sum fun p hp ↦ Finset.sum_le_sum fun u hu ↦
            Finset.sum_le_sum fun ℓ hℓ ↦ htuple_le p hp u hu ℓ hℓ
      _ ≤ ∑ _p ∈ OrdPairs, ∑ _u ∈ Finset.Icc (α - (M + 1)) α,
            ((α : ℝ) * (U_per * (randomGraphMeasure n).real (partitionColoringEvent P))) := by
          refine Finset.sum_le_sum fun _ _ ↦ Finset.sum_le_sum fun u hu ↦ ?_
          simp only [Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (hℓ_card u hu) (by positivity)
      _ ≤ ((n : ℝ) ^ 2 * ((M + 2 : ℕ) : ℝ) * (α : ℝ) * U_per) *
            (randomGraphMeasure n).real (partitionColoringEvent P) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          set Z_tail : ℝ := (α : ℝ) * (U_per * (randomGraphMeasure n).real (partitionColoringEvent P))
          have hZ_nn : 0 ≤ Z_tail := by dsimp [Z_tail]; positivity
          calc (OrdPairs.card : ℝ) * (((Finset.Icc (α - (M + 1)) α).card : ℝ) * Z_tail)
              ≤ (OrdPairs.card : ℝ) * (((M + 2 : ℕ) : ℝ) * Z_tail) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hu_card hZ_nn) (Nat.cast_nonneg _)
            _ ≤ (n : ℝ) ^ 2 * (((M + 2 : ℕ) : ℝ) * Z_tail) :=
                mul_le_mul_of_nonneg_right hOrd_card (by positivity)
            _ = ((n : ℝ) ^ 2 * ((M + 2 : ℕ) : ℝ) * (α : ℝ) * U_per) *
                  (randomGraphMeasure n).real (partitionColoringEvent P) := by
                dsimp [Z_tail]; ring
  have hcoeff_le_eps : (n : ℝ) ^ 2 * ((M + 2 : ℕ) : ℝ) * (α : ℝ) * U_per ≤ eps := by
    have hα_le_4L : (α : ℝ) ≤ 4 * Real.log (n : ℝ) := hphase.2
    have hα_pow : (α : ℝ) ^ (M + 8) ≤ (4 : ℝ) ^ (M + 8) * (Real.log (n : ℝ)) ^ (M + 8) := by
      calc (α : ℝ) ^ (M + 8) ≤ (4 * Real.log (n : ℝ)) ^ (M + 8) :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hα_le_4L (M + 8)
        _ = (4 : ℝ) ^ (M + 8) * (Real.log (n : ℝ)) ^ (M + 8) := mul_pow _ _ _
    have halg1 : (n : ℝ) ^ 2 * ((M + 2 : ℕ) : ℝ) * (α : ℝ) * U_per ≤
        C_coeff * ((Real.log (n : ℝ)) ^ K_pow / (n : ℝ) ^ 2) := by
      have hid1 : (n : ℝ) ^ 2 * ((M + 2 : ℕ) : ℝ) * (α : ℝ) * U_per =
          (n : ℝ) ^ 2 * ((M + 2 : ℕ) : ℝ) * (α : ℝ) ^ (M + 8) *
            (2 : ℝ) ^ (4 * M + 20) * ((1 / 2 : ℝ) ^ α) ^ 2 := by
        dsimp [U_per]
        rw [show M + 8 = (M + 7) + 1 by omega, pow_succ]
        ring
      rw [hid1]
      calc (n : ℝ) ^ 2 * ((M + 2 : ℕ) : ℝ) * (α : ℝ) ^ (M + 8) *
              (2 : ℝ) ^ (4 * M + 20) * ((1 / 2 : ℝ) ^ α) ^ 2
          ≤ (n : ℝ) ^ 2 * ((M + 2 : ℕ) : ℝ) *
              ((4 : ℝ) ^ (M + 8) * (Real.log (n : ℝ)) ^ (M + 8)) *
              (2 : ℝ) ^ (4 * M + 20) *
              ((16 / (Real.log 2) ^ 4) * (Real.log (n : ℝ)) ^ 4 / (n : ℝ) ^ 4) := by
            refine mul_le_mul ?_ hhalf_2α (by positivity) (by positivity)
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left hα_pow (by positivity)
        _ = C_coeff * ((Real.log (n : ℝ)) ^ K_pow / (n : ℝ) ^ 2) := by
            dsimp [C_coeff, K_pow]
            rw [show M + 12 = (M + 8) + 4 by omega, pow_add]
            field_simp [hn_pos.ne']
            ring
    have hlog_div := log_pow_div_sq_le hn1_real (show 1 ≤ K_pow by dsimp [K_pow]; omega)
    have hC_coeff_nn : 0 ≤ C_coeff :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity))
        (mul_nonneg (by positivity) (div_nonneg (by norm_num) (pow_nonneg hq_pos.le 4)))
    have hB_le : C_coeff * ((Real.log (n : ℝ)) ^ K_pow / (n : ℝ) ^ 2) ≤ B_top / (n : ℝ) := by
      calc C_coeff * ((Real.log (n : ℝ)) ^ K_pow / (n : ℝ) ^ 2)
          ≤ C_coeff * ((2 * (K_pow : ℝ)) ^ K_pow / (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hlog_div hC_coeff_nn
        _ = B_top / (n : ℝ) := by dsimp [B_top]; ring
    have hn_gt : B_top / eps ≤ (n : ℝ) := by
      have hc : B_top / eps ≤ (Nat.ceil (B_top / eps) : ℝ) := Nat.le_ceil _
      have hn_cast : (Nat.ceil (B_top / eps) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (show Nat.ceil (B_top / eps) ≤ n by omega)
      exact hc.trans hn_cast
    have hdiv_eps : B_top / (n : ℝ) ≤ eps := by
      rw [div_le_iff₀ hn_pos]
      have := (div_le_iff₀ heps).mp hn_gt
      linarith
    exact halg1.trans (hB_le.trans hdiv_eps)
  exact hsum_all.trans (mul_le_mul_of_nonneg_right hcoeff_le_eps measureReal_nonneg)

private theorem randomGraphMeasure_real_eq_card_filter_mul {n : ℕ}
    (U : Set (LabeledGraph n)) [DecidablePred (· ∈ U)] :
    (randomGraphMeasure n).real U =
      (((Finset.univ : Finset (LabeledGraph n)).filter (· ∈ U)).card : ℝ) *
        (1 / 2 : ℝ) ^ n.choose 2 := by
  have henn : randomGraphMeasure n U =
      (((Finset.univ : Finset (LabeledGraph n)).filter (· ∈ U)).card : ENNReal) *
        (1 / 2 : ENNReal) ^ n.choose 2 := by
    calc randomGraphMeasure n U
        = randomGraphMeasure n
            (((Finset.univ : Finset (LabeledGraph n)).filter (· ∈ U) : Finset (LabeledGraph n)) :
              Set (LabeledGraph n)) := by
            congr 1; ext G; simp
      _ = ∑ G ∈ (Finset.univ : Finset (LabeledGraph n)).filter (· ∈ U),
            randomGraphMeasure n {G} := by
            rw [MeasureTheory.sum_measure_singleton]
      _ = ∑ _G ∈ (Finset.univ : Finset (LabeledGraph n)).filter (· ∈ U),
            (1 / 2 : ENNReal) ^ n.choose 2 := by
            simp_rw [randomGraphMeasure_singleton_uniform]
      _ = (((Finset.univ : Finset (LabeledGraph n)).filter (· ∈ U)).card : ENNReal) *
            (1 / 2 : ENNReal) ^ n.choose 2 := by
            simp [Finset.sum_const, nsmul_eq_mul]
  simp only [Measure.real, henn, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]

open scoped Classical in
/-- **Lemma 7.1 `¬ D_π` (and `¬ D'_π`) conditional regularity (`main.tex` lines 936–939, 1018–1023):**
for every `M : ℕ`, `c_D > 0` (covering `c_D = 1/2` for `D_π` and `c_D = 1` for `D'_π`), and
`eps > 0`, eventually in `n`, uniformly over all `P : VertexPartition n` with part sizes in
`[phaseNat n - (M + 1), phaseNat n]`, the event `D_P` that at most `c_D (log n)³` independent
sets `S` with `phaseNat n - (M + 1) ≤ |S| ≤ phaseNat n` and `z(S, P) = 2` satisfy
`max_B |S ∩ B| ≥ |B| - 1` obeys both
`P(A_P ∩ C_P ∩ D_Pᶜ) ≤ (eps / 2) · P(A_P)` and `P(A_P ∩ D_Pᶜ) ≤ eps · P(A_P)`. -/
theorem eventually_condProb_manyNearParts_tendsto_zero
    (M : ℕ) {c_D eps : ℝ} (hc_D : 0 < c_D) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop,
      ∀ P : VertexPartition n,
        (∀ B ∈ P.parts, phaseNat n - (M + 1) ≤ B.card ∧ B.card ≤ phaseNat n) →
        let C_P : Set (LabeledGraph n) :=
          {G | ∀ S : Finset (Fin n),
            G.IsIndepSet (S : Set (Fin n)) →
            phaseNat n - (M + 1) ≤ S.card →
            S.card ≤ phaseNat n →
            (P.parts.filter fun B ↦ (S ∩ B).Nonempty).card = 2 →
            ∃ B ∈ P.parts, (S ∩ B).card = S.card - 1}
        let NearSet : LabeledGraph n → Finset (Finset (Fin n)) := fun G ↦
          (Finset.univ : Finset (Fin n)).powerset.filter fun S : Finset (Fin n) ↦
            G.IsIndepSet (S : Set (Fin n)) ∧
            phaseNat n - (M + 1) ≤ S.card ∧
            S.card ≤ phaseNat n ∧
            (P.parts.filter fun B ↦ (S ∩ B).Nonempty).card = 2 ∧
            ∃ B ∈ P.parts, B.card - 1 ≤ (S ∩ B).card
        let D_P : Set (LabeledGraph n) :=
          {G | ((NearSet G).card : ℝ) ≤ c_D * (Real.log (n : ℝ)) ^ 3}
        (randomGraphMeasure n).real (partitionColoringEvent P ∩ C_P ∩ D_Pᶜ) ≤
            (eps / 2) * (randomGraphMeasure n).real (partitionColoringEvent P) ∧
          (randomGraphMeasure n).real (partitionColoringEvent P ∩ D_Pᶜ) ≤
            eps * (randomGraphMeasure n).real (partitionColoringEvent P) := by
  have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  set K_markov : ℝ := 8 * (2 : ℝ) ^ (M + 2) / (c_D * (Real.log 2) ^ 2)
  have hK_pos : 0 < K_markov := by dsimp [K_markov]; positivity
  have hL_big : ∀ᶠ n : ℕ in atTop, max 1 (K_markov / (eps / 2)) ≤ logOrder n :=
    tendsto_logOrder_atTop.eventually_ge_atTop _
  have hph_big : ∀ᶠ n : ℕ in atTop, M + 7 ≤ phaseNat n := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop ((M + 7 : ℕ) : ℝ),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact_mod_cast hn.trans hph.1
  filter_upwards [hL_big, hph_big,
    eventually_condProb_badTwoClassSplit_tendsto_zero M (half_pos heps),
    eventually_phaseRoot_domain_pos_and_target_corridor] with
    n hLn hph_ge hC_ev hcenterDom P hP_bds
  intro C_P NearSet D_P
  set α : ℕ := phaseNat n
  have hL_pos : 0 < Real.log (n : ℝ) := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hLn)
  have hL_ge_K : K_markov / (eps / 2) ≤ Real.log (n : ℝ) := (le_max_right _ _).trans hLn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_trans Nat.zero_lt_one hcenterDom.1.1)
  let CandTriples : Finset (Σ _ : Finset (Fin n), Finset (Fin n) × Fin n) :=
    P.parts.sigma fun B ↦ (insert B (B.image B.erase)) ×ˢ ((Finset.univ : Finset (Fin n)) \ B)
  have hCand_card : CandTriples.card ≤ 2 * n ^ 2 := by
    rw [Finset.card_sigma]
    have hterm : ∀ B ∈ P.parts,
        ((insert B (B.image B.erase)) ×ˢ ((Finset.univ : Finset (Fin n)) \ B)).card ≤
          2 * B.card * n := by
      intro B hBP
      rw [Finset.card_product]
      have hB_pos : 1 ≤ B.card := by have := (hP_bds B hBP).1; omega
      have hc1 : (insert B (B.image B.erase)).card ≤ 2 * B.card := by
        have hi := Finset.card_insert_le B (B.image B.erase)
        have him := @Finset.card_image_le _ _ B B.erase _
        omega
      have hc2 : ((Finset.univ : Finset (Fin n)) \ B).card ≤ n := by
        exact (Finset.card_le_univ _).trans_eq (Finset.card_fin n)
      exact Nat.mul_le_mul hc1 hc2
    calc ∑ B ∈ P.parts,
            ((insert B (B.image B.erase)) ×ˢ ((Finset.univ : Finset (Fin n)) \ B)).card
        ≤ ∑ B ∈ P.parts, (2 * B.card * n) := Finset.sum_le_sum hterm
      _ = 2 * n * (∑ B ∈ P.parts, B.card) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun B _ ↦ by ring
      _ = 2 * n ^ 2 := by rw [P.sum_card_parts, Finset.card_fin]; ring
  have hNear_le_Cand : ∀ G : LabeledGraph n,
      G ∈ partitionColoringEvent P ∩ C_P →
      (NearSet G).card ≤
        (CandTriples.filter fun t ↦ ∀ x ∈ t.2.1, ¬ G.Adj x t.2.2).card := by
    intro G ⟨_hGP, hGC⟩
    have hmap_ex : ∀ S ∈ NearSet G,
        ∃ t ∈ CandTriples.filter (fun t ↦ ∀ x ∈ t.2.1, ¬ G.Adj x t.2.2),
          insert t.2.2 t.2.1 = S := by
      intro S hSN
      simp only [NearSet, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and] at hSN
      obtain ⟨hS_ind, hS_lo, hS_hi, hz2, B₂, hB₂P, hSB₂_ge⟩ := hSN
      obtain ⟨B₁, hB₁P, hSB₁_eq⟩ := hGC S hS_ind hS_lo hS_hi hz2
      have hB_eq : B₁ = B₂ := by
        by_contra hne
        have hdisj : Disjoint (S ∩ B₁) (S ∩ B₂) :=
          (P.disjoint hB₁P hB₂P hne).mono Finset.inter_subset_right Finset.inter_subset_right
        have hsub : (S ∩ B₁) ∪ (S ∩ B₂) ⊆ S :=
          Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
        have hc := Finset.card_le_card hsub
        rw [Finset.card_union_of_disjoint hdisj] at hc
        have hB₂_lo := (hP_bds B₂ hB₂P).1
        omega
      subst hB_eq
      have hsdiff_card : (S \ B₁).card = 1 := by
        have hsum := Finset.card_sdiff_add_card_inter S B₁
        omega
      obtain ⟨v, hv_sing⟩ := Finset.card_eq_one.mp hsdiff_card
      have hv_mem : v ∈ S \ B₁ := hv_sing ▸ Finset.mem_singleton_self v
      obtain ⟨hvS, hvnB₁⟩ := Finset.mem_sdiff.mp hv_mem
      have hS_rec : insert v (S ∩ B₁) = S := by
        have hun := Finset.sdiff_union_inter S B₁
        rw [hv_sing, Finset.singleton_union] at hun
        exact hun
      have hSB₁_mem : S ∩ B₁ ∈ insert B₁ (B₁.image B₁.erase) := by
        have hle_B₁ : (S ∩ B₁).card ≤ B₁.card := Finset.card_le_card Finset.inter_subset_right
        rcases (show (S ∩ B₁).card = B₁.card ∨ (S ∩ B₁).card = B₁.card - 1 by omega) with heq_c | hm1_c
        · exact Finset.mem_insert.mpr
            (Or.inl (Finset.eq_of_subset_of_card_le Finset.inter_subset_right heq_c.symm.le))
        · have hB_sd : (B₁ \ (S ∩ B₁)).card = 1 := by
            have hs := Finset.card_sdiff_add_card_inter B₁ (S ∩ B₁)
            rw [Finset.inter_eq_right.mpr Finset.inter_subset_right] at hs
            omega
          obtain ⟨w, hw_sing⟩ := Finset.card_eq_one.mp hB_sd
          have hw_mem : w ∈ B₁ \ (S ∩ B₁) := hw_sing ▸ Finset.mem_singleton_self w
          obtain ⟨hwB₁, hwnSB⟩ := Finset.mem_sdiff.mp hw_mem
          have herase_eq : B₁.erase w = S ∩ B₁ := by
            ext u
            simp only [Finset.mem_erase, Finset.mem_inter]
            constructor
            · rintro ⟨huw, huB₁⟩
              refine ⟨?_, huB₁⟩
              by_contra hunS
              have hu_sd : u ∈ B₁ \ (S ∩ B₁) :=
                Finset.mem_sdiff.mpr ⟨huB₁, fun h ↦ hunS (Finset.mem_inter.mp h).1⟩
              rw [hw_sing, Finset.mem_singleton] at hu_sd
              exact huw hu_sd
            · rintro ⟨huS, huB₁⟩
              exact ⟨fun h ↦ hwnSB (h ▸ Finset.mem_inter.mpr ⟨huS, huB₁⟩), huB₁⟩
          exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w, hwB₁, herase_eq⟩)
      let t : Σ _ : Finset (Fin n), Finset (Fin n) × Fin n := ⟨B₁, (S ∩ B₁, v)⟩
      have ht_mem : t ∈ CandTriples := by
        simp only [t, CandTriples, Finset.mem_sigma, Finset.mem_product, Finset.mem_sdiff,
          Finset.mem_univ, true_and]
        exact ⟨hB₁P, hSB₁_mem, hvnB₁⟩
      have ht_noAdj : ∀ x ∈ t.2.1, ¬ G.Adj x t.2.2 := by
        intro x hx
        have hxS : x ∈ S := (Finset.mem_inter.mp hx).1
        have hxB₁ : x ∈ B₁ := (Finset.mem_inter.mp hx).2
        have hxv : x ≠ v := fun heq ↦ hvnB₁ (heq ▸ hxB₁)
        exact hS_ind hxS hvS hxv
      exact ⟨t, Finset.mem_filter.mpr ⟨ht_mem, ht_noAdj⟩, hS_rec⟩
    let f_inj : {S // S ∈ NearSet G} →
        {t // t ∈ CandTriples.filter (fun t ↦ ∀ x ∈ t.2.1, ¬ G.Adj x t.2.2)} :=
      fun S ↦ ⟨(hmap_ex S.1 S.2).choose, (hmap_ex S.1 S.2).choose_spec.1⟩
    have hinj : Function.Injective f_inj := by
      intro S₁ S₂ heq
      apply Subtype.ext
      have h1 := (hmap_ex S₁.1 S₁.2).choose_spec.2
      have h2 := (hmap_ex S₂.1 S₂.2).choose_spec.2
      have ht_eq : (f_inj S₁).1 = (f_inj S₂).1 := congrArg Subtype.val heq
      change (hmap_ex S₁.1 S₁.2).choose = (hmap_ex S₂.1 S₂.2).choose at ht_eq
      rw [← h1, ← h2, ht_eq]
    have hc := Fintype.card_le_of_injective f_inj hinj
    simpa only [Fintype.card_coe] using hc
  let BadG := (Finset.univ : Finset (LabeledGraph n)).filter
    (· ∈ partitionColoringEvent P ∩ C_P ∩ D_Pᶜ)
  let GoodG := (Finset.univ : Finset (LabeledGraph n)).filter (· ∈ partitionColoringEvent P)
  have hBad_sub : BadG ⊆ GoodG :=
    fun G hG ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ G, (Finset.mem_filter.mp hG).2.1.1⟩
  have hp₀_pos : (0 : ℝ) < (1 / 2 : ℝ) ^ n.choose 2 := by positivity
  have hMarkov_count :
      c_D * (Real.log (n : ℝ)) ^ 3 * (BadG.card : ℝ) ≤
        ∑ t ∈ CandTriples,
          ((GoodG.filter fun G ↦ ∀ x ∈ t.2.1, ¬ G.Adj x t.2.2).card : ℝ) := by
    have h1 : c_D * (Real.log (n : ℝ)) ^ 3 * (BadG.card : ℝ) ≤
        ∑ G ∈ BadG, ((NearSet G).card : ℝ) := by
      rw [mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun G hG ↦ ?_
      have hnotD : G ∉ D_P := (Finset.mem_filter.mp hG).2.2
      simp only [D_P, Set.mem_setOf_eq, not_le] at hnotD
      exact hnotD.le
    have h2 : ∑ G ∈ BadG, ((NearSet G).card : ℝ) ≤
        ∑ G ∈ BadG, ((CandTriples.filter fun t ↦ ∀ x ∈ t.2.1, ¬ G.Adj x t.2.2).card : ℝ) :=
      Finset.sum_le_sum fun G hG ↦ by
        exact_mod_cast hNear_le_Cand G (Finset.mem_filter.mp hG).2.1
    have h3 : ∑ G ∈ BadG, ((CandTriples.filter fun t ↦ ∀ x ∈ t.2.1, ¬ G.Adj x t.2.2).card : ℝ) ≤
        ∑ G ∈ GoodG, ((CandTriples.filter fun t ↦ ∀ x ∈ t.2.1, ¬ G.Adj x t.2.2).card : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hBad_sub (fun _ _ _ ↦ Nat.cast_nonneg _)
    have h4 : (∑ G ∈ GoodG,
          ((CandTriples.filter fun t ↦ ∀ x ∈ t.2.1, ¬ G.Adj x t.2.2).card : ℝ)) =
        ∑ t ∈ CandTriples,
          ((GoodG.filter fun G ↦ ∀ x ∈ t.2.1, ¬ G.Adj x t.2.2).card : ℝ) := by
      norm_cast
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    exact h1.trans (h2.trans (h3.trans_eq h4))
  have ht_prob : ∀ t ∈ CandTriples,
      (((GoodG.filter fun G ↦ ∀ x ∈ t.2.1, ¬ G.Adj x t.2.2).card : ℝ) *
          (1 / 2 : ℝ) ^ n.choose 2) ≤
        (2 : ℝ) ^ (M + 2) * (1 / 2 : ℝ) ^ α *
          (randomGraphMeasure n).real (partitionColoringEvent P) := by
    intro t ht
    simp only [CandTriples, Finset.mem_sigma, Finset.mem_product, Finset.mem_sdiff,
      Finset.mem_univ, true_and] at ht
    obtain ⟨hBP, hW_mem, hvnB⟩ := ht
    have hW_sub_and_card : t.2.1 ⊆ t.1 ∧ t.1.card - 1 ≤ t.2.1.card := by
      simp only [Finset.mem_insert, Finset.mem_image] at hW_mem
      rcases hW_mem with heq | ⟨w, hwB, heq⟩
      · rw [heq]; exact ⟨Finset.Subset.refl _, Nat.sub_le _ _⟩
      · rw [← heq]; exact ⟨Finset.erase_subset w t.1, by rw [Finset.card_erase_of_mem hwB]⟩
    have hfilt_eq :
        GoodG.filter (fun G ↦ ∀ x ∈ t.2.1, ¬ G.Adj x t.2.2) =
          (Finset.univ : Finset (LabeledGraph n)).filter
            (· ∈ partitionColoringEvent P ∩
              {G : LabeledGraph n | ∀ x ∈ t.2.1, ∀ y ∈ ({t.2.2} : Finset (Fin n)), ¬ G.Adj x y}) := by
      ext G
      simp [GoodG]
    rw [hfilt_eq, ← randomGraphMeasure_real_eq_card_filter_mul]
    have hdisj_Wv : Disjoint t.2.1 ({t.2.2} : Finset (Fin n)) := by
      rw [Finset.disjoint_singleton_right]
      exact fun hxv ↦ hvnB (hW_sub_and_card.1 hxv)
    have hcross_Wv : ∀ x ∈ t.2.1, ∀ y ∈ ({t.2.2} : Finset (Fin n)),
        ¬ ∃ D ∈ P.parts, x ∈ D ∧ y ∈ D := by
      rintro x hx y hy ⟨D, hDP, hxD, hyD⟩
      rw [Finset.mem_singleton] at hy
      subst hy
      have hDt : D = t.1 := by
        by_contra hne
        exact Finset.disjoint_left.mp (P.disjoint hDP hBP hne) hxD (hW_sub_and_card.1 hx)
      subst hDt
      exact hvnB hyD
    rw [randomGraphMeasure_coloring_inter_noCrossBipartite_eq P t.2.1 {t.2.2} hdisj_Wv hcross_Wv,
      Finset.card_singleton, mul_one]
    have hα_le_W : α ≤ t.2.1.card + (M + 2) := by
      have hb_lo := (hP_bds t.1 hBP).1
      have hW_lo := hW_sub_and_card.2
      omega
    exact mul_le_mul_of_nonneg_right (half_pow_le_two_pow_mul_half_pow hα_le_W) measureReal_nonneg
  have hCD_le :
      (randomGraphMeasure n).real (partitionColoringEvent P ∩ C_P ∩ D_Pᶜ) ≤
        (eps / 2) * (randomGraphMeasure n).real (partitionColoringEvent P) := by
    have hm_p₀ := mul_le_mul_of_nonneg_right hMarkov_count hp₀_pos.le
    rw [mul_assoc (c_D * (Real.log (n : ℝ)) ^ 3),
      ← randomGraphMeasure_real_eq_card_filter_mul (partitionColoringEvent P ∩ C_P ∩ D_Pᶜ),
      Finset.sum_mul] at hm_p₀
    have hsum_t :
        (∑ t ∈ CandTriples,
          ((GoodG.filter fun G ↦ ∀ x ∈ t.2.1, ¬ G.Adj x t.2.2).card : ℝ) *
            (1 / 2 : ℝ) ^ n.choose 2) ≤
        (2 * (n : ℝ) ^ 2) * ((2 : ℝ) ^ (M + 2) * (1 / 2 : ℝ) ^ α *
          (randomGraphMeasure n).real (partitionColoringEvent P)) := by
      calc ∑ t ∈ CandTriples,
              ((GoodG.filter fun G ↦ ∀ x ∈ t.2.1, ¬ G.Adj x t.2.2).card : ℝ) *
                (1 / 2 : ℝ) ^ n.choose 2
          ≤ ∑ _t ∈ CandTriples,
              ((2 : ℝ) ^ (M + 2) * (1 / 2 : ℝ) ^ α *
                (randomGraphMeasure n).real (partitionColoringEvent P)) :=
            Finset.sum_le_sum ht_prob
        _ = (CandTriples.card : ℝ) *
              ((2 : ℝ) ^ (M + 2) * (1 / 2 : ℝ) ^ α *
                (randomGraphMeasure n).real (partitionColoringEvent P)) := by
            simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 * (n : ℝ) ^ 2) *
              ((2 : ℝ) ^ (M + 2) * (1 / 2 : ℝ) ^ α *
                (randomGraphMeasure n).real (partitionColoringEvent P)) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact_mod_cast hCand_card
    have hhalf_α := half_pow_phaseNat_le_of_phaseDomain hcenterDom.1
    have hnum_le :
        (2 * (n : ℝ) ^ 2) * ((2 : ℝ) ^ (M + 2) * (1 / 2 : ℝ) ^ α) ≤
          (c_D * (Real.log (n : ℝ)) ^ 3) * (K_markov / Real.log (n : ℝ)) := by
      calc (2 * (n : ℝ) ^ 2) * ((2 : ℝ) ^ (M + 2) * (1 / 2 : ℝ) ^ α)
          ≤ (2 * (n : ℝ) ^ 2) * ((2 : ℝ) ^ (M + 2) *
              ((4 / (Real.log 2) ^ 2) * (Real.log (n : ℝ)) ^ 2 / (n : ℝ) ^ 2)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hhalf_α (by positivity)
        _ = (c_D * (Real.log (n : ℝ)) ^ 3) * (K_markov / Real.log (n : ℝ)) := by
            dsimp [K_markov]
            field_simp [hn_pos.ne', hL_pos.ne', hc_D.ne', hq_pos.ne']
            ring
    have hKL_le : K_markov / Real.log (n : ℝ) ≤ eps / 2 := by
      rw [div_le_iff₀ hL_pos]
      have := (div_le_iff₀ (half_pos heps)).mp hL_ge_K
      linarith
    have hcL3_pos : 0 < c_D * (Real.log (n : ℝ)) ^ 3 := by positivity
    have hprod_in :
        (c_D * (Real.log (n : ℝ)) ^ 3) *
          (randomGraphMeasure n).real (partitionColoringEvent P ∩ C_P ∩ D_Pᶜ) ≤
        (c_D * (Real.log (n : ℝ)) ^ 3) *
          ((eps / 2) * (randomGraphMeasure n).real (partitionColoringEvent P)) := by
      calc (c_D * (Real.log (n : ℝ)) ^ 3) *
              (randomGraphMeasure n).real (partitionColoringEvent P ∩ C_P ∩ D_Pᶜ)
          ≤ (2 * (n : ℝ) ^ 2) * ((2 : ℝ) ^ (M + 2) * (1 / 2 : ℝ) ^ α *
              (randomGraphMeasure n).real (partitionColoringEvent P)) := hm_p₀.trans hsum_t
        _ = ((2 * (n : ℝ) ^ 2) * ((2 : ℝ) ^ (M + 2) * (1 / 2 : ℝ) ^ α)) *
              (randomGraphMeasure n).real (partitionColoringEvent P) := by ring
        _ ≤ ((c_D * (Real.log (n : ℝ)) ^ 3) * (eps / 2)) *
              (randomGraphMeasure n).real (partitionColoringEvent P) :=
            mul_le_mul_of_nonneg_right
              (hnum_le.trans (mul_le_mul_of_nonneg_left hKL_le hcL3_pos.le))
              measureReal_nonneg
        _ = (c_D * (Real.log (n : ℝ)) ^ 3) *
              ((eps / 2) * (randomGraphMeasure n).real (partitionColoringEvent P)) := by ring
    exact le_of_mul_le_mul_left hprod_in hcL3_pos
  refine ⟨hCD_le, ?_⟩
  have hsub_D : partitionColoringEvent P ∩ D_Pᶜ ⊆
      (partitionColoringEvent P ∩ C_Pᶜ) ∪ (partitionColoringEvent P ∩ C_P ∩ D_Pᶜ) := by
    intro G ⟨hGP, hnD⟩
    by_cases hGC : G ∈ C_P
    · exact Or.inr ⟨⟨hGP, hGC⟩, hnD⟩
    · exact Or.inl ⟨hGP, hGC⟩
  have hC_bound := hC_ev P (fun B hB ↦ (hP_bds B hB).2)
  calc (randomGraphMeasure n).real (partitionColoringEvent P ∩ D_Pᶜ)
      ≤ (randomGraphMeasure n).real (partitionColoringEvent P ∩ C_Pᶜ) +
          (randomGraphMeasure n).real (partitionColoringEvent P ∩ C_P ∩ D_Pᶜ) :=
        (rg_mono hsub_D).trans (measureReal_union_le _ _)
    _ ≤ (eps / 2) * (randomGraphMeasure n).real (partitionColoringEvent P) +
          (eps / 2) * (randomGraphMeasure n).real (partitionColoringEvent P) :=
        add_le_add hC_bound hCD_le
    _ = eps * (randomGraphMeasure n).real (partitionColoringEvent P) := by ring

open scoped Classical in
/-- **Lemma 7.1 `(Z^{ch})²` and `Z²` restriction to `Π_rel` (`main.tex` lines 942–957, 976–977):**
for any finite family `(P i)_{i ∈ S_idx}` of vertex partitions of `Fin n` with part sizes in
`U_sizes : Set ℕ`, `α : ℕ`, and real near-part caps `c_full, c_half : ℝ`:
1. **(Chromatic sum `Z^{ch}`):** `Z_ch(G)²` is bounded pointwise by the indicator sum of
   `A_{P i} ∩ A_{P j}` over `(i, j) ∈ S_idx ×ˢ S_idx` satisfying all symmetric `Π_rel` conditions
   with integer cap `⌊c_full⌋₊`, so `E[Z_ch²] ≤ ∑_{(i,j) ∈ Π_rel(⌊c_full⌋₊)} P(A_{P i} ∩ A_{P j})`;
2. **(Cochromatic sum `Z`):** `Z_co(G)²` (imposing both independent-set and clique regularity with
   cap `c_half`) is bounded pointwise by the indicator sum of `A_{P i}^co ∩ A_{P j}^co` over
   `(i, j) ∈ S_idx ×ˢ S_idx` satisfying all symmetric `Π_rel` conditions with integer cap
   `⌊2 c_half⌋₊`, so `E[Z_co²] ≤ ∑_{(i,j) ∈ Π_rel(⌊2 c_half⌋₊)} P(A_{P i}^co ∩ A_{P j}^co)`. -/
theorem sq_regularPartitionSum_le_relevantPairs_and_integral_le
    {ι : Type*} [DecidableEq ι]
    {n α : ℕ} (U_sizes : Set ℕ)
    (S_idx : Finset ι) (P : ι → VertexPartition n)
    (hP_sizes : ∀ i ∈ S_idx, ∀ D ∈ (P i).parts, D.card ∈ U_sizes)
    (c_full c_half : ℝ) :
    let B_ind : VertexPartition n → Set (LabeledGraph n) := fun Q ↦
      {G | ∀ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) → S.card ∈ U_sizes →
        (Q.parts.filter fun E ↦ (S ∩ E).Nonempty).card ≤ 2 ∨
          S.card ≤ (Q.parts.filter fun E ↦ (S ∩ E).Nonempty).card + 2 * (α - S.card) + 1}
    let C_ind : VertexPartition n → Set (LabeledGraph n) := fun Q ↦
      {G | ∀ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) → S.card ∈ U_sizes →
        (Q.parts.filter fun E ↦ (S ∩ E).Nonempty).card = 2 →
          ∃ E ∈ Q.parts, (S ∩ E).card = S.card - 1}
    let D_ind : VertexPartition n → ℝ → Set (LabeledGraph n) := fun Q c_cap ↦
      {G | (((Finset.univ : Finset (Fin n)).powerset.filter fun S : Finset (Fin n) ↦
          G.IsIndepSet (S : Set (Fin n)) ∧ S.card ∈ U_sizes ∧
          (Q.parts.filter fun E ↦ (S ∩ E).Nonempty).card = 2 ∧
          ∃ E ∈ Q.parts, E.card - 1 ≤ (S ∩ E).card).card : ℝ) ≤ c_cap}
    let B_cl : VertexPartition n → Set (LabeledGraph n) := fun Q ↦
      {G | ∀ S : Finset (Fin n), G.IsClique (S : Set (Fin n)) → S.card ∈ U_sizes →
        (Q.parts.filter fun E ↦ (S ∩ E).Nonempty).card ≤ 2 ∨
          S.card ≤ (Q.parts.filter fun E ↦ (S ∩ E).Nonempty).card + 2 * (α - S.card) + 1}
    let C_cl : VertexPartition n → Set (LabeledGraph n) := fun Q ↦
      {G | ∀ S : Finset (Fin n), G.IsClique (S : Set (Fin n)) → S.card ∈ U_sizes →
        (Q.parts.filter fun E ↦ (S ∩ E).Nonempty).card = 2 →
          ∃ E ∈ Q.parts, (S ∩ E).card = S.card - 1}
    let D_cl : VertexPartition n → ℝ → Set (LabeledGraph n) := fun Q c_cap ↦
      {G | (((Finset.univ : Finset (Fin n)).powerset.filter fun S : Finset (Fin n) ↦
          G.IsClique (S : Set (Fin n)) ∧ S.card ∈ U_sizes ∧
          (Q.parts.filter fun E ↦ (S ∩ E).Nonempty).card = 2 ∧
          ∃ E ∈ Q.parts, E.card - 1 ≤ (S ∩ E).card).card : ℝ) ≤ c_cap}
    let RelPair : ℕ → VertexPartition n → VertexPartition n → Prop := fun B Q Q' ↦
      ((∀ D ∈ Q.parts,
          (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card ≤ 2 ∨
            D.card ≤ (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card + 2 * (α - D.card) + 1) ∧
        (∀ D' ∈ Q'.parts,
          (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card ≤ 2 ∨
            D'.card ≤ (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card + 2 * (α - D'.card) + 1)) ∧
      ((∀ D ∈ Q.parts, (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card = 2 →
          ∃ D' ∈ Q'.parts, (D ∩ D').card = D.card - 1) ∧
        (∀ D' ∈ Q'.parts, (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card = 2 →
          ∃ D ∈ Q.parts, (D' ∩ D).card = D'.card - 1)) ∧
      ((Q.parts.filter fun D ↦
          (Q'.parts.filter fun E ↦ (D ∩ E).Nonempty).card = 2 ∧
            ∃ D' ∈ Q'.parts, D'.card - 1 ≤ (D ∩ D').card).card ≤ B ∧
        (Q'.parts.filter fun D' ↦
          (Q.parts.filter fun E ↦ (D' ∩ E).Nonempty).card = 2 ∧
            ∃ D ∈ Q.parts, D.card - 1 ≤ (D' ∩ D).card).card ≤ B)
    let Z_ch : LabeledGraph n → ℝ := fun G ↦
      ∑ i ∈ S_idx,
        if G ∈ partitionColoringEvent (P i) ∩ B_ind (P i) ∩ C_ind (P i) ∩ D_ind (P i) c_full
        then (1 : ℝ) else 0
    let Z_co : LabeledGraph n → ℝ := fun G ↦
      ∑ i ∈ S_idx,
        if G ∈ partitionCocoloringEvent (P i) ∩ B_ind (P i) ∩ C_ind (P i) ∩ D_ind (P i) c_half ∩
            B_cl (P i) ∩ C_cl (P i) ∩ D_cl (P i) c_half
        then (1 : ℝ) else 0
    ((∀ G : LabeledGraph n,
        (Z_ch G) ^ 2 ≤
          ∑ p ∈ (S_idx ×ˢ S_idx).filter (fun p ↦ RelPair (Nat.floor c_full) (P p.1) (P p.2)),
            if G ∈ partitionColoringEvent (P p.1) ∩ partitionColoringEvent (P p.2)
            then (1 : ℝ) else 0) ∧
      (∫ G : LabeledGraph n, (Z_ch G) ^ 2 ∂randomGraphMeasure n) ≤
        ∑ p ∈ (S_idx ×ˢ S_idx).filter (fun p ↦ RelPair (Nat.floor c_full) (P p.1) (P p.2)),
          (randomGraphMeasure n).real
            (partitionColoringEvent (P p.1) ∩ partitionColoringEvent (P p.2))) ∧
    ((∀ G : LabeledGraph n,
        (Z_co G) ^ 2 ≤
          ∑ p ∈ (S_idx ×ˢ S_idx).filter (fun p ↦ RelPair (Nat.floor (2 * c_half)) (P p.1) (P p.2)),
            if G ∈ partitionCocoloringEvent (P p.1) ∩ partitionCocoloringEvent (P p.2)
            then (1 : ℝ) else 0) ∧
      (∫ G : LabeledGraph n, (Z_co G) ^ 2 ∂randomGraphMeasure n) ≤
        ∑ p ∈ (S_idx ×ˢ S_idx).filter (fun p ↦ RelPair (Nat.floor (2 * c_half)) (P p.1) (P p.2)),
          (randomGraphMeasure n).real
            (partitionCocoloringEvent (P p.1) ∩ partitionCocoloringEvent (P p.2))) := by
  intro B_ind C_ind D_ind B_cl C_cl D_cl RelPair Z_ch Z_co
  have and_of_imp : ∀ {A B : Prop}, A → (A → B) → A ∧ B := fun ha h ↦ ⟨ha, h ha⟩
  have hint_ind_sum : ∀ (Pairs : Finset (ι × ι)) (Ev : ι × ι → Set (LabeledGraph n))
      (d : ∀ p G, Decidable (G ∈ Ev p)) (Z_fn : LabeledGraph n → ℝ),
      (∀ G : LabeledGraph n, (Z_fn G) ^ 2 ≤ ∑ p ∈ Pairs, @ite ℝ (G ∈ Ev p) (d p G) (1 : ℝ) 0) →
      (∫ G : LabeledGraph n, (Z_fn G) ^ 2 ∂randomGraphMeasure n) ≤
        ∑ p ∈ Pairs, (randomGraphMeasure n).real (Ev p) := by
    intro Pairs Ev d Z_fn hpt
    have hmono : (∫ G : LabeledGraph n, (Z_fn G) ^ 2 ∂randomGraphMeasure n) ≤
        ∫ G : LabeledGraph n,
          (∑ p ∈ Pairs, @ite ℝ (G ∈ Ev p) (d p G) (1 : ℝ) 0) ∂randomGraphMeasure n :=
      integral_mono Integrable.of_finite Integrable.of_finite hpt
    have hsum_eq :
        (∫ G : LabeledGraph n,
          (∑ p ∈ Pairs, @ite ℝ (G ∈ Ev p) (d p G) (1 : ℝ) 0) ∂randomGraphMeasure n) =
          ∑ p ∈ Pairs, (randomGraphMeasure n).real (Ev p) := by
      rw [integral_finsetSum _ fun _ _ ↦ Integrable.of_finite]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      have hind_eq : (fun G : LabeledGraph n ↦ @ite ℝ (G ∈ Ev p) (d p G) (1 : ℝ) 0) =
          (Ev p).indicator (fun _ ↦ (1 : ℝ)) := by
        funext G; by_cases hG : G ∈ Ev p <;> simp [hG]
      rw [hind_eq, integral_indicator_const _ (Set.toFinite _).measurableSet, smul_eq_mul, mul_one]
    exact hmono.trans_eq hsum_eq
  have hch_dir : ∀ {i j : ι} {G : LabeledGraph n},
      i ∈ S_idx → j ∈ S_idx →
      G ∈ partitionColoringEvent (P i) →
      G ∈ B_ind (P j) ∩ C_ind (P j) ∩ D_ind (P j) c_full →
      (∀ D ∈ (P i).parts,
        ((P j).parts.filter fun E ↦ (D ∩ E).Nonempty).card ≤ 2 ∨
          D.card ≤ ((P j).parts.filter fun E ↦ (D ∩ E).Nonempty).card + 2 * (α - D.card) + 1) ∧
      (∀ D ∈ (P i).parts, ((P j).parts.filter fun E ↦ (D ∩ E).Nonempty).card = 2 →
        ∃ D' ∈ (P j).parts, (D ∩ D').card = D.card - 1) ∧
      ((P i).parts.filter fun D ↦
        ((P j).parts.filter fun E ↦ (D ∩ E).Nonempty).card = 2 ∧
          ∃ D' ∈ (P j).parts, D'.card - 1 ≤ (D ∩ D').card).card ≤ Nat.floor c_full := by
    intro i j G hi _hj hGi ⟨⟨hBj, hCj⟩, hDj⟩
    refine ⟨fun D hDP ↦ hBj D (hGi D hDP) (hP_sizes i hi D hDP),
      fun D hDP hz2 ↦ hCj D (hGi D hDP) (hP_sizes i hi D hDP) hz2, ?_⟩
    have hsub : ((P i).parts.filter fun D ↦
        ((P j).parts.filter fun E ↦ (D ∩ E).Nonempty).card = 2 ∧
          ∃ D' ∈ (P j).parts, D'.card - 1 ≤ (D ∩ D').card) ⊆
        (Finset.univ : Finset (Fin n)).powerset.filter fun S : Finset (Fin n) ↦
          G.IsIndepSet (S : Set (Fin n)) ∧ S.card ∈ U_sizes ∧
          ((P j).parts.filter fun E ↦ (S ∩ E).Nonempty).card = 2 ∧
          ∃ E ∈ (P j).parts, E.card - 1 ≤ (S ∩ E).card := by
      intro D hDf
      obtain ⟨hDP, hz2, hex⟩ := Finset.mem_filter.mp hDf
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ D),
        hGi D hDP, hP_sizes i hi D hDP, hz2, hex⟩
    dsimp [D_ind] at hDj
    have hc_real : (((P i).parts.filter fun D ↦
        ((P j).parts.filter fun E ↦ (D ∩ E).Nonempty).card = 2 ∧
          ∃ D' ∈ (P j).parts, D'.card - 1 ≤ (D ∩ D').card).card : ℝ) ≤ c_full :=
      (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hDj
    exact Nat.le_floor hc_real
  have hco_dir : ∀ {i j : ι} {G : LabeledGraph n},
      i ∈ S_idx → j ∈ S_idx →
      G ∈ partitionCocoloringEvent (P i) →
      G ∈ B_ind (P j) ∩ C_ind (P j) ∩ D_ind (P j) c_half ∩
          B_cl (P j) ∩ C_cl (P j) ∩ D_cl (P j) c_half →
      (∀ D ∈ (P i).parts,
        ((P j).parts.filter fun E ↦ (D ∩ E).Nonempty).card ≤ 2 ∨
          D.card ≤ ((P j).parts.filter fun E ↦ (D ∩ E).Nonempty).card + 2 * (α - D.card) + 1) ∧
      (∀ D ∈ (P i).parts, ((P j).parts.filter fun E ↦ (D ∩ E).Nonempty).card = 2 →
        ∃ D' ∈ (P j).parts, (D ∩ D').card = D.card - 1) ∧
      ((P i).parts.filter fun D ↦
        ((P j).parts.filter fun E ↦ (D ∩ E).Nonempty).card = 2 ∧
          ∃ D' ∈ (P j).parts, D'.card - 1 ≤ (D ∩ D').card).card ≤ Nat.floor (2 * c_half) := by
    intro i j G hi _hj hGi ⟨⟨⟨⟨⟨hBi, hCi⟩, hDi⟩, hBc⟩, hCc⟩, hDc⟩
    refine ⟨fun D hDP ↦ (hGi D hDP).elim
        (fun hind ↦ hBi D hind (hP_sizes i hi D hDP))
        (fun hcl ↦ hBc D hcl (hP_sizes i hi D hDP)),
      fun D hDP hz2 ↦ (hGi D hDP).elim
        (fun hind ↦ hCi D hind (hP_sizes i hi D hDP) hz2)
        (fun hcl ↦ hCc D hcl (hP_sizes i hi D hDP) hz2), ?_⟩
    let F_near := (P i).parts.filter fun D ↦
      ((P j).parts.filter fun E ↦ (D ∩ E).Nonempty).card = 2 ∧
        ∃ D' ∈ (P j).parts, D'.card - 1 ≤ (D ∩ D').card
    let N_ind := (Finset.univ : Finset (Fin n)).powerset.filter fun S : Finset (Fin n) ↦
      G.IsIndepSet (S : Set (Fin n)) ∧ S.card ∈ U_sizes ∧
      ((P j).parts.filter fun E ↦ (S ∩ E).Nonempty).card = 2 ∧
      ∃ E ∈ (P j).parts, E.card - 1 ≤ (S ∩ E).card
    let N_cl := (Finset.univ : Finset (Fin n)).powerset.filter fun S : Finset (Fin n) ↦
      G.IsClique (S : Set (Fin n)) ∧ S.card ∈ U_sizes ∧
      ((P j).parts.filter fun E ↦ (S ∩ E).Nonempty).card = 2 ∧
      ∃ E ∈ (P j).parts, E.card - 1 ≤ (S ∩ E).card
    have hsub_u : F_near ⊆ N_ind ∪ N_cl := by
      intro D hDf
      obtain ⟨hDP, hz2, hex⟩ := Finset.mem_filter.mp hDf
      rcases hGi D hDP with hind | hcl
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr (Finset.subset_univ D), hind, hP_sizes i hi D hDP, hz2, hex⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr (Finset.subset_univ D), hcl, hP_sizes i hi D hDP, hz2, hex⟩)
    have hc_le : (F_near.card : ℝ) ≤ 2 * c_half := by
      have hnat : F_near.card ≤ N_ind.card + N_cl.card :=
        (Finset.card_le_card hsub_u).trans (Finset.card_union_le N_ind N_cl)
      have hreal : (F_near.card : ℝ) ≤ (N_ind.card : ℝ) + (N_cl.card : ℝ) := by exact_mod_cast hnat
      have hDi' : (N_ind.card : ℝ) ≤ c_half := hDi
      have hDc' : (N_cl.card : ℝ) ≤ c_half := hDc
      linarith
    exact Nat.le_floor hc_le
  refine ⟨and_of_imp ?_ (hint_ind_sum _ _ _ Z_ch), and_of_imp ?_ (hint_ind_sum _ _ _ Z_co)⟩
  · intro G
    dsimp only [Z_ch]
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_product', Finset.sum_filter]
    refine Finset.sum_le_sum fun p hp ↦ ?_
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    by_cases h1 :
        G ∈ partitionColoringEvent (P p.1) ∩ B_ind (P p.1) ∩ C_ind (P p.1) ∩ D_ind (P p.1) c_full
    · by_cases h2 :
          G ∈ partitionColoringEvent (P p.2) ∩ B_ind (P p.2) ∩ C_ind (P p.2) ∩ D_ind (P p.2) c_full
      · have hd12 := hch_dir hp1 hp2 h1.1.1.1 ⟨⟨h2.1.1.2, h2.1.2⟩, h2.2⟩
        have hd21 := hch_dir hp2 hp1 h2.1.1.1 ⟨⟨h1.1.1.2, h1.1.2⟩, h1.2⟩
        have hrel : RelPair (Nat.floor c_full) (P p.1) (P p.2) :=
          ⟨⟨hd12.1, hd21.1⟩, ⟨hd12.2.1, hd21.2.1⟩, ⟨hd12.2.2, hd21.2.2⟩⟩
        have hA12 : G ∈ partitionColoringEvent (P p.1) ∩ partitionColoringEvent (P p.2) :=
          ⟨h1.1.1.1, h2.1.1.1⟩
        rw [if_pos h1, if_pos h2, mul_one, if_pos hrel, if_pos hA12]
      · rw [if_neg h2, mul_zero]
        split_ifs <;> norm_num
    · rw [if_neg h1, zero_mul]
      split_ifs <;> norm_num
  · intro G
    dsimp only [Z_co]
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_product', Finset.sum_filter]
    refine Finset.sum_le_sum fun p hp ↦ ?_
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    by_cases h1 :
        G ∈ partitionCocoloringEvent (P p.1) ∩ B_ind (P p.1) ∩ C_ind (P p.1) ∩ D_ind (P p.1) c_half ∩
            B_cl (P p.1) ∩ C_cl (P p.1) ∩ D_cl (P p.1) c_half
    · by_cases h2 :
          G ∈ partitionCocoloringEvent (P p.2) ∩ B_ind (P p.2) ∩ C_ind (P p.2) ∩ D_ind (P p.2) c_half ∩
              B_cl (P p.2) ∩ C_cl (P p.2) ∩ D_cl (P p.2) c_half
      · have hco1 : G ∈ partitionCocoloringEvent (P p.1) := h1.1.1.1.1.1.1
        have hco2 : G ∈ partitionCocoloringEvent (P p.2) := h2.1.1.1.1.1.1
        have hd12 := hco_dir hp1 hp2 hco1
          ⟨⟨⟨⟨⟨h2.1.1.1.1.1.2, h2.1.1.1.1.2⟩, h2.1.1.1.2⟩, h2.1.1.2⟩, h2.1.2⟩, h2.2⟩
        have hd21 := hco_dir hp2 hp1 hco2
          ⟨⟨⟨⟨⟨h1.1.1.1.1.1.2, h1.1.1.1.1.2⟩, h1.1.1.1.2⟩, h1.1.1.2⟩, h1.1.2⟩, h1.2⟩
        have hrel : RelPair (Nat.floor (2 * c_half)) (P p.1) (P p.2) :=
          ⟨⟨hd12.1, hd21.1⟩, ⟨hd12.2.1, hd21.2.1⟩, ⟨hd12.2.2, hd21.2.2⟩⟩
        have hA12 : G ∈ partitionCocoloringEvent (P p.1) ∩ partitionCocoloringEvent (P p.2) :=
          ⟨hco1, hco2⟩
        rw [if_pos h1, if_pos h2, mul_one, if_pos hrel, if_pos hA12]
      · rw [if_neg h2, mul_zero]
        split_ifs <;> norm_num
    · rw [if_neg h1, zero_mul]
      split_ifs <;> norm_num

/-!
## 4. Section 9 — Coupling-uniform `∃ m ≥ n` tail-union rates & complete v11 syntheses
-/

private theorem ae_eventually_notMem_of_tailUnion_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    {E : ℕ → Set Ω} {b : ℕ → ℝ}
    (htail : ∀ᶠ n : ℕ in atTop, ℙ.real {ω : Ω | ∃ m ≥ n, ω ∈ E m} ≤ b n)
    (hb_zero : Tendsto b atTop (nhds 0)) :
    ∀ᵐ ω ∂ℙ, ∀ᶠ m : ℕ in atTop, ω ∉ E m := by
  let S : Set Ω := {ω : Ω | ¬ ∀ᶠ m : ℕ in atTop, ω ∉ E m}
  have hS_sub : ∀ n : ℕ, S ⊆ {ω : Ω | ∃ m ≥ n, ω ∈ E m} := by
    intro n ω hω
    rw [Set.mem_setOf_eq]
    by_contra hnone
    apply hω
    rw [Filter.eventually_atTop]
    exact ⟨n, fun m hm hmem ↦ hnone ⟨m, hm, hmem⟩⟩
  have htoReal_zero : (ℙ S).toReal = 0 := by
    apply le_antisymm _ ENNReal.toReal_nonneg
    by_contra hpos
    have heps : 0 < (ℙ S).toReal := not_le.mp hpos
    have hb_small : ∀ᶠ n : ℕ in atTop, b n < (ℙ S).toReal :=
      hb_zero.eventually (Iio_mem_nhds heps)
    obtain ⟨n, hn_tail, hn_lt⟩ := (htail.and hb_small).exists
    have hle : (ℙ S).toReal ≤ b n := (measureReal_mono (hS_sub n)).trans hn_tail
    linarith
  rw [ae_iff]
  exact (ENNReal.toReal_eq_zero_iff _).mp htoReal_zero |>.resolve_right (measure_ne_top ℙ S)

private theorem tendsto_exp_neg_div_log_pow_six_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ 2 * Real.exp (-c * (n : ℝ) / (Real.log (n : ℝ)) ^ 6))
      atTop (nhds 0) := by
  have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  set c_b2 : ℝ := c / (Real.log 2) ^ 6
  have hc_b2 : 0 < c_b2 := by dsimp [c_b2]; positivity
  have hsum := (summable_subgaussianGapTail hc_b2).mul_left 2
  refine hsum.tendsto_atTop_zero.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn2
  have hL_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  congr 2
  dsimp [c_b2]
  rw [Real.logb, div_pow]
  field_simp [hL_pos.ne', hq_pos.ne']

/-- **Section 9 coupling-uniform `∃ m ≥ n` sub-Gaussian tail-union rate (`main.tex` lines 120–123, 246–249, 1283–1287):**
if a sequence of graph events `Bad m` (`m : ℕ`) satisfies the single-`m` sub-Gaussian marginal bound
`P(G_m ∈ Bad m) ≤ 2 exp(-ϑ₁² a m / (2 (log m)⁶))` eventually for every `ϑ₁ ∈ (0, 1)` (`a > 0`),
then for every `ϑ ∈ (0, 1)` there exists a threshold `N : ℕ` **independent of the coupling** such
that for every probability space `(Ω, ℙ)` and every sequence `(G m)_{m ≥ 2}` with marginals
`G_m ∼ G(m, 1/2)`, all `n ≥ N` satisfy
`ℙ(∃ m ≥ n : G_m ∈ Bad m) ≤ 2 exp(-ϑ² a n / (2 (log n)⁶))`. -/
theorem eventually_coupling_tailUnion_of_subgaussian_marginals
    (Bad : ∀ m : ℕ, Set (LabeledGraph m)) {a : ℝ} (ha : 0 < a)
    (hMargTail : ∀ {ϑ₁ : ℝ}, ϑ₁ ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ᶠ m : ℕ in atTop,
        (randomGraphMeasure m).real (Bad m) ≤
          2 * Real.exp (-ϑ₁ ^ 2 * a * (m : ℝ) / (2 * (Real.log (m : ℝ)) ^ 6)))
    {ϑ : ℝ} (hϑ : ϑ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ N : ℕ,
      ∀ {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
        (G : ∀ m : ℕ, Ω → LabeledGraph m),
        (∀ m : ℕ, 2 ≤ m → Measure.map (G m) ℙ = randomGraphMeasure m) →
        ∀ n ≥ N,
          ℙ.real {ω : Ω | ∃ m ≥ n, G m ω ∈ Bad m} ≤
            2 * Real.exp (-ϑ ^ 2 * a * (n : ℝ) / (2 * (Real.log (n : ℝ)) ^ 6)) := by
  have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  set ϑ₁ : ℝ := (1 + ϑ) / 2
  have hϑ₁_ioo : ϑ₁ ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp [ϑ₁]; exact ⟨by linarith [hϑ.1], by linarith [hϑ.2]⟩
  have hϑ_lt : ϑ < ϑ₁ := by dsimp [ϑ₁]; linarith [hϑ.2]
  have hdiff_sq_pos : 0 < ϑ₁ ^ 2 - ϑ ^ 2 := by nlinarith [hϑ.1, hϑ_lt]
  set δ_c : ℝ := (ϑ₁ ^ 2 - ϑ ^ 2) * a / 2
  have hδ_c_pos : 0 < δ_c := by dsimp [δ_c]; positivity
  set c_b2 : ℝ := δ_c / (Real.log 2) ^ 6
  have hc_b2_pos : 0 < c_b2 := by dsimp [c_b2]; positivity
  let g_rem : ℕ → ℝ := fun m ↦ 2 * Real.exp (-c_b2 * (m : ℝ) / (Real.logb 2 (m : ℝ)) ^ 6)
  have hg_sum : Summable g_rem := (summable_subgaussianGapTail hc_b2_pos).mul_left 2
  have hg_rew : ∀ m : ℕ, 2 ≤ m →
      g_rem m = 2 * Real.exp (-δ_c * (m : ℝ) / (Real.log (m : ℝ)) ^ 6) := by
    intro m hm2
    have hL_pos : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
    dsimp [g_rem, c_b2]
    congr 2
    rw [Real.logb, div_pow]
    field_simp [hL_pos.ne', hq_pos.ne']
  have htail_zero : Tendsto (fun n : ℕ ↦ ∑' k : ℕ, g_rem (k + n)) atTop (nhds 0) := by
    have hpart := hg_sum.hasSum.tendsto_sum_nat
    have hsub : Tendsto (fun n : ℕ ↦ (∑' i : ℕ, g_rem i) - ∑ i ∈ Finset.range n, g_rem i)
        atTop (nhds 0) := by
      simpa only [sub_self] using (tendsto_const_nhds (x := ∑' i : ℕ, g_rem i)).sub hpart
    refine hsub.congr fun n ↦ ?_
    linarith [hg_sum.sum_add_tsum_nat_add n]
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (hMargTail hϑ₁_ioo)
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp
    (htail_zero.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 2)))
  set N : ℕ := max (max 2 (Nat.ceil (Real.exp 6))) (max N₁ N₂)
  refine ⟨N, ?_⟩
  intro Ω _ ℙ _ G hMarg n hnN
  have hn2 : 2 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hnN
  have hn_exp6 : Real.exp 6 ≤ (n : ℝ) := by
    have hc : Nat.ceil (Real.exp 6) ≤ n :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hnN
    exact (Nat.le_ceil _).trans (by exact_mod_cast hc)
  have hn_N₁ : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hnN
  have hn_N₂ : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hnN
  have htsum_g_le2 : (∑' k : ℕ, g_rem (k + n)) ≤ 2 := (hN₂ n hn_N₂).le
  set E_pre : ℕ → Set Ω := fun m ↦ (G m) ⁻¹' (Bad m)
  have hterm_le : ∀ k : ℕ,
      ℙ.real (E_pre (k + n)) ≤
        Real.exp (-ϑ ^ 2 * a * (n : ℝ) / (2 * (Real.log (n : ℝ)) ^ 6)) * g_rem (k + n) := by
    intro k
    set m : ℕ := k + n
    have hm_ge_n : n ≤ m := Nat.le_add_left n k
    have hm2 : 2 ≤ m := le_trans hn2 hm_ge_n
    have haem := aemeasurable_of_map_eq_randomGraphMeasure (hMarg m hm2)
    have hms : MeasurableSet (Bad m) := (Set.toFinite _).measurableSet
    have hpre_eq : ℙ.real (E_pre m) = (randomGraphMeasure m).real (Bad m) := by
      dsimp only [E_pre, Measure.real]
      rw [← Measure.map_apply_of_aemeasurable haem hms, hMarg m hm2]
    rw [hpre_eq]
    have hm_tail := hN₁ m (le_trans hn_N₁ hm_ge_n)
    have hfn_le : (n : ℝ) / (Real.log (n : ℝ)) ^ 6 ≤ (m : ℝ) / (Real.log (m : ℝ)) ^ 6 := by
      rcases eq_or_lt_of_le hm_ge_n with heq | hlt
      · rw [heq]
      · exact (strictMonoOn_div_log_pow_six.1 hn_exp6
          (hn_exp6.trans (by exact_mod_cast hm_ge_n)) (by exact_mod_cast hlt)).le
    have hexp_split :
        2 * Real.exp (-ϑ₁ ^ 2 * a * (m : ℝ) / (2 * (Real.log (m : ℝ)) ^ 6)) ≤
          Real.exp (-ϑ ^ 2 * a * (n : ℝ) / (2 * (Real.log (n : ℝ)) ^ 6)) * g_rem m := by
      rw [hg_rew m hm2]
      have hrw : Real.exp (-ϑ ^ 2 * a * (n : ℝ) / (2 * (Real.log (n : ℝ)) ^ 6)) *
            (2 * Real.exp (-δ_c * (m : ℝ) / (Real.log (m : ℝ)) ^ 6)) =
          2 * Real.exp (-ϑ ^ 2 * a * (n : ℝ) / (2 * (Real.log (n : ℝ)) ^ 6) +
            (-δ_c * (m : ℝ) / (Real.log (m : ℝ)) ^ 6)) := by
        calc Real.exp (-ϑ ^ 2 * a * (n : ℝ) / (2 * (Real.log (n : ℝ)) ^ 6)) *
              (2 * Real.exp (-δ_c * (m : ℝ) / (Real.log (m : ℝ)) ^ 6))
            = 2 * (Real.exp (-ϑ ^ 2 * a * (n : ℝ) / (2 * (Real.log (n : ℝ)) ^ 6)) *
                Real.exp (-δ_c * (m : ℝ) / (Real.log (m : ℝ)) ^ 6)) := by ring
          _ = 2 * Real.exp (-ϑ ^ 2 * a * (n : ℝ) / (2 * (Real.log (n : ℝ)) ^ 6) +
                (-δ_c * (m : ℝ) / (Real.log (m : ℝ)) ^ 6)) := by rw [← Real.exp_add]
      rw [hrw]
      apply mul_le_mul_of_nonneg_left _ zero_le_two
      apply Real.exp_le_exp.mpr
      have hm_ineq := mul_le_mul_of_nonneg_left hfn_le
        (show (0 : ℝ) ≤ ϑ ^ 2 * a / 2 by positivity)
      have hid_m :
          -(ϑ ^ 2 * a / 2 * ((m : ℝ) / (Real.log (m : ℝ)) ^ 6)) +
            (-δ_c * (m : ℝ) / (Real.log (m : ℝ)) ^ 6) =
          -ϑ₁ ^ 2 * a * (m : ℝ) / (2 * (Real.log (m : ℝ)) ^ 6) := by
        dsimp [δ_c]; ring
      have hid_n :
          -(ϑ ^ 2 * a / 2 * ((n : ℝ) / (Real.log (n : ℝ)) ^ 6)) =
            -ϑ ^ 2 * a * (n : ℝ) / (2 * (Real.log (n : ℝ)) ^ 6) := by ring
      linarith
    exact hm_tail.trans hexp_split
  have hsum_dom : Summable (fun k : ℕ ↦
      Real.exp (-ϑ ^ 2 * a * (n : ℝ) / (2 * (Real.log (n : ℝ)) ^ 6)) * g_rem (k + n)) :=
    (hg_sum.comp_injective (add_left_injective n)).mul_left _
  have hsum_pre : Summable (fun k : ℕ ↦ ℙ.real (E_pre (k + n))) :=
    Summable.of_nonneg_of_le (fun _ ↦ measureReal_nonneg) hterm_le hsum_dom
  have hsub_u : {ω : Ω | ∃ m ≥ n, G m ω ∈ Bad m} ⊆ ⋃ k : ℕ, E_pre (k + n) := by
    rintro ω ⟨m, hmn, hm_bad⟩
    rw [Set.mem_iUnion]
    exact ⟨m - n, by dsimp [E_pre]; rwa [Nat.sub_add_cancel hmn]⟩
  have hmeas_u : ℙ {ω : Ω | ∃ m ≥ n, G m ω ∈ Bad m} ≤
      ENNReal.ofReal (∑' k : ℕ, ℙ.real (E_pre (k + n))) := by
    calc ℙ {ω : Ω | ∃ m ≥ n, G m ω ∈ Bad m}
        ≤ ℙ (⋃ k : ℕ, E_pre (k + n)) := measure_mono hsub_u
      _ ≤ ∑' k : ℕ, ℙ (E_pre (k + n)) := measure_iUnion_le _
      _ ≤ ENNReal.ofReal (∑' k : ℕ, ℙ.real (E_pre (k + n))) := by
          rw [ENNReal.tsum_eq_iSup_sum]
          refine iSup_le fun s ↦ ?_
          have heq : ∑ k ∈ s, ℙ (E_pre (k + n)) =
              ENNReal.ofReal (∑ k ∈ s, ℙ.real (E_pre (k + n))) := by
            rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ measureReal_nonneg)]
            exact Finset.sum_congr rfl fun k _ ↦
              (ENNReal.ofReal_toReal (measure_ne_top ℙ _)).symm
          rw [heq]
          exact ENNReal.ofReal_le_ofReal
            (hsum_pre.sum_le_tsum s (fun _ _ ↦ measureReal_nonneg))
  have hreal_u : ℙ.real {ω : Ω | ∃ m ≥ n, G m ω ∈ Bad m} ≤
      ∑' k : ℕ, ℙ.real (E_pre (k + n)) := by
    have hnn : 0 ≤ ∑' k : ℕ, ℙ.real (E_pre (k + n)) := tsum_nonneg fun _ ↦ measureReal_nonneg
    have htr := (ENNReal.toReal_le_toReal (measure_ne_top ℙ _) ENNReal.ofReal_ne_top).mpr hmeas_u
    rwa [ENNReal.toReal_ofReal hnn] at htr
  calc ℙ.real {ω : Ω | ∃ m ≥ n, G m ω ∈ Bad m}
      ≤ ∑' k : ℕ, ℙ.real (E_pre (k + n)) := hreal_u
    _ ≤ ∑' k : ℕ,
          (Real.exp (-ϑ ^ 2 * a * (n : ℝ) / (2 * (Real.log (n : ℝ)) ^ 6)) * g_rem (k + n)) :=
        hsum_pre.tsum_le_tsum hterm_le hsum_dom
    _ = Real.exp (-ϑ ^ 2 * a * (n : ℝ) / (2 * (Real.log (n : ℝ)) ^ 6)) *
          (∑' k : ℕ, g_rem (k + n)) := tsum_mul_left
    _ ≤ Real.exp (-ϑ ^ 2 * a * (n : ℝ) / (2 * (Real.log (n : ℝ)) ^ 6)) * 2 :=
        mul_le_mul_of_nonneg_left htsum_g_le2 (Real.exp_pos _).le
    _ = 2 * Real.exp (-ϑ ^ 2 * a * (n : ℝ) / (2 * (Real.log (n : ℝ)) ^ 6)) := mul_comm _ 2

/-- **Complete v11 Phase Refinement synthesis (`main.tex` lines 235–251):**
upgrades `phaseRefinement_v10_complete` with the coupling-uniform `∃ m ≥ n` sub-Gaussian
tail-union bound `ℙ(∃ m ≥ n : ((log m)³ / m) Δ(G_m) ∉ [c', C']) ≤ 2 exp(-ϑ² η₀² n / (2 (log n)⁶))`
under every joint coupling of `(G_m)_{m ≥ 2}` with marginals `G_m ∼ G(m, 1/2)`. -/
theorem phaseRefinement_v11_complete
    (tildeEps : ℕ → ℝ)
    (htilde_nn : ∀ n : ℕ, 0 ≤ tildeEps n)
    (htilde_O : tildeEps =O[atTop] (fun n : ℕ ↦
      Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)))
    (htail : (fun n : ℕ ↦ (randomGraphMeasure n).real
      (twoSidedGapEvent
        (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - tildeEps n)
        (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + tildeEps n) n)ᶜ)
      =O[atTop] quasiExpTail) :
    let c₇ : ℝ := (Real.log 2) ^ 2 / 4 * sInf (phaseGain7 '' Set.Icc deltaStar (1 + deltaStar))
    let C₇ : ℝ := (Real.log 2) ^ 3 / 2 - c₇
    let eps : ℕ → ℝ := fun n ↦
      if 3 ≤ n then tildeEps n + (1 + Real.log (Real.log (n : ℝ))) / Real.log (n : ℝ) else 0
    (80 / 1000 < (Real.log 2) ^ 2 / 4 * Real.log (391 / 200) ∧
      (Real.log 2) ^ 2 / 4 * Real.log (391 / 200) < c₇ ∧
      C₇ < (Real.log 2) ^ 2 / 4 * Real.log (800 / 391) ∧
      (Real.log 2) ^ 2 / 4 * Real.log (800 / 391) < 86 / 1000) ∧
    (∃ C₁ : ℝ, 0 < C₁ ∧ (∀ n : ℕ, 0 ≤ eps n) ∧
      ∀ n : ℕ, 3 ≤ n → eps n ≤ C₁ * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) ∧
    (∀ᶠ n : ℕ in atTop,
      (randomGraphMeasure n).real
          (twoSidedGapEvent
            (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - eps n)
            (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + eps n) n)ᶜ ≤
        2 * Real.exp (-(n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2 /
          (2 * (Real.log (n : ℝ)) ^ 8))) ∧
    (∀ᶠ n : ℕ in atTop,
      lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - eps n ≤
          (Real.log (n : ℝ)) ^ 3 / (n : ℝ) *
            (∫ G : LabeledGraph n,
              ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
              ∂randomGraphMeasure n) ∧
        (Real.log (n : ℝ)) ^ 3 / (n : ℝ) *
            (∫ G : LabeledGraph n,
              ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
              ∂randomGraphMeasure n) ≤
          upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + eps n) ∧
    (∀ {c' C' ϑ : ℝ}, c' < c₇ → C₇ < C' → ϑ ∈ Set.Ioo (0 : ℝ) 1 →
      let η₀ : ℝ := min (c₇ - c') (C' - C₇)
      (∀ᶠ n : ℕ in atTop,
        (randomGraphMeasure n).real (twoSidedGapEvent c' C' n)ᶜ ≤
          2 * Real.exp (-ϑ ^ 2 * η₀ ^ 2 * (n : ℝ) / (2 * (Real.log (n : ℝ)) ^ 6))) ∧
      (∀ᶠ n : ℕ in atTop,
        c' * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3) ≤
            (∫ G : LabeledGraph n,
              ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
              ∂randomGraphMeasure n) ∧
          (∫ G : LabeledGraph n,
              ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
              ∂randomGraphMeasure n) ≤
            C' * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3)) ∧
      (∀ {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
        (G : ∀ m : ℕ, Ω → LabeledGraph m),
        (∀ m : ℕ, 2 ≤ m → Measure.map (G m) ℙ = randomGraphMeasure m) →
        (∀ᶠ n : ℕ in atTop,
          ℙ.real {ω : Ω | ∃ m ≥ n,
              (Real.log (m : ℝ)) ^ 3 / (m : ℝ) *
                ((chromaticNumberNat (G m ω) : ℝ) - (cochromaticNumber (G m ω) : ℝ)) ∉
                Set.Icc c' C'} ≤
            2 * Real.exp (-ϑ ^ 2 * η₀ ^ 2 * (n : ℝ) / (2 * (Real.log (n : ℝ)) ^ 6))) ∧
        (∀ᵐ ω ∂ℙ, ∀ᶠ n : ℕ in atTop,
          c' * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3) ≤
              (chromaticNumberNat (G n ω) : ℝ) - (cochromaticNumber (G n ω) : ℝ) ∧
            (chromaticNumberNat (G n ω) : ℝ) - (cochromaticNumber (G n ω) : ℝ) ≤
              C' * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3)))) := by
  intro c₇ C₇ eps
  obtain ⟨hbounds, h1_eps, h2_mov, h3_exp, hv10_fixed⟩ :=
    phaseRefinement_v10_complete.{0} tildeEps htilde_nn htilde_O htail
  refine ⟨hbounds, h1_eps, h2_mov, h3_exp, ?_⟩
  intro c' C' ϑ hc' hC' hϑ η₀
  obtain ⟨htail_single, hexp_fixed, -⟩ := hv10_fixed hc' hC' hϑ
  have hη₀_pos : 0 < η₀ := lt_min (by linarith) (by linarith)
  obtain ⟨N_u, hN_u⟩ := eventually_coupling_tailUnion_of_subgaussian_marginals
    (fun m ↦ (twoSidedGapEvent c' C' m)ᶜ) (sq_pos_of_pos hη₀_pos)
    (fun {_} hϑ₁ ↦ (hv10_fixed hc' hC' hϑ₁).1) hϑ
  refine ⟨htail_single, hexp_fixed, ?_⟩
  intro Ω _ ℙ _ G hMarg
  have hiff_bad : ∀ {m : ℕ} {H : LabeledGraph m}, 2 ≤ m →
      ((Real.log (m : ℝ)) ^ 3 / (m : ℝ) *
          ((chromaticNumberNat H : ℝ) - (cochromaticNumber H : ℝ)) ∉ Set.Icc c' C' ↔
        H ∈ (twoSidedGapEvent c' C' m)ᶜ) := by
    intro m H hm2
    have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
    have hL_pos : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
    unfold twoSidedGapEvent
    rw [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_Icc]
    refine not_congr ⟨fun ⟨hlo, hhi⟩ ↦ ?_, fun ⟨hlo, hhi⟩ ↦ ?_⟩
    · have hscale_pos : 0 < (m : ℝ) / (Real.log (m : ℝ)) ^ 3 := by positivity
      have m1 := mul_le_mul_of_nonneg_right hlo hscale_pos.le
      have m2 := mul_le_mul_of_nonneg_right hhi hscale_pos.le
      have hcanc :
          (Real.log (m : ℝ)) ^ 3 / (m : ℝ) *
            ((chromaticNumberNat H : ℝ) - (cochromaticNumber H : ℝ)) *
            ((m : ℝ) / (Real.log (m : ℝ)) ^ 3) =
          (chromaticNumberNat H : ℝ) - (cochromaticNumber H : ℝ) := by
        field_simp [hm_pos.ne', hL_pos.ne']
      exact ⟨by linarith, by linarith⟩
    · have hfac_pos : 0 < (Real.log (m : ℝ)) ^ 3 / (m : ℝ) := by positivity
      have m1 := mul_le_mul_of_nonneg_left hlo hfac_pos.le
      have m2 := mul_le_mul_of_nonneg_left hhi hfac_pos.le
      have hcanc1 : (Real.log (m : ℝ)) ^ 3 / (m : ℝ) *
          (c' * ((m : ℝ) / (Real.log (m : ℝ)) ^ 3)) = c' := by
        field_simp [hm_pos.ne', hL_pos.ne']
      have hcanc2 : (Real.log (m : ℝ)) ^ 3 / (m : ℝ) *
          (C' * ((m : ℝ) / (Real.log (m : ℝ)) ^ 3)) = C' := by
        field_simp [hm_pos.ne', hL_pos.ne']
      exact ⟨by linarith, by linarith⟩
  have hunion_ev : ∀ᶠ n : ℕ in atTop,
      ℙ.real {ω : Ω | ∃ m ≥ n,
          (Real.log (m : ℝ)) ^ 3 / (m : ℝ) *
            ((chromaticNumberNat (G m ω) : ℝ) - (cochromaticNumber (G m ω) : ℝ)) ∉
            Set.Icc c' C'} ≤
        2 * Real.exp (-ϑ ^ 2 * η₀ ^ 2 * (n : ℝ) / (2 * (Real.log (n : ℝ)) ^ 6)) := by
    filter_upwards [eventually_ge_atTop (max 2 N_u)] with n hn
    have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
    have hn_Nu : N_u ≤ n := le_trans (le_max_right _ _) hn
    have hset :
        {ω : Ω | ∃ m ≥ n,
          (Real.log (m : ℝ)) ^ 3 / (m : ℝ) *
            ((chromaticNumberNat (G m ω) : ℝ) - (cochromaticNumber (G m ω) : ℝ)) ∉
            Set.Icc c' C'} =
        {ω : Ω | ∃ m ≥ n, G m ω ∈ (twoSidedGapEvent c' C' m)ᶜ} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      exact exists_congr fun m ↦ and_congr_right fun hmn ↦ hiff_bad (le_trans hn2 hmn)
    rw [hset]
    exact hN_u ℙ G hMarg n hn_Nu
  have hunion_ev_gap : ∀ᶠ n : ℕ in atTop,
      ℙ.real {ω : Ω | ∃ m ≥ n, ω ∈ (fun m ↦ (G m) ⁻¹' (twoSidedGapEvent c' C' m)ᶜ) m} ≤
        2 * Real.exp (-(ϑ ^ 2 * η₀ ^ 2 / 2) * (n : ℝ) / (Real.log (n : ℝ)) ^ 6) := by
    filter_upwards [eventually_ge_atTop N_u] with n hn_Nu
    have h := hN_u ℙ G hMarg n hn_Nu
    have hrw : -ϑ ^ 2 * η₀ ^ 2 * (n : ℝ) / (2 * (Real.log (n : ℝ)) ^ 6) =
        -(ϑ ^ 2 * η₀ ^ 2 / 2) * (n : ℝ) / (Real.log (n : ℝ)) ^ 6 := by ring
    rwa [hrw] at h
  have hae_gap := ae_eventually_notMem_of_tailUnion_tendsto_zero ℙ hunion_ev_gap
    (tendsto_exp_neg_div_log_pow_six_zero (by have := hϑ.1; positivity))
  refine ⟨hunion_ev, ?_⟩
  filter_upwards [hae_gap] with ω hω
  filter_upwards [hω] with n hn
  exact Set.notMem_compl_iff.mp hn

/-- **Complete v11 Main Theorem `(i)–(iv)` synthesis (`main.tex` lines 107–135):**
upgrades `mainTheorem_v10_complete` with:
- in `(i)`: the exact Gaussian-constant `√(8/3)` Orlicz `ψ₂`-norm bounds
  `‖Δ(G_n) - E[Δ(G_n)]‖_{ψ₂} ≤ √(8/3 · (n - 1))` and
  `‖Y_n - E[Y_n]‖_{ψ₂} ≤ √(8/3) · (log₂ n)³ / √n` for every `n ≥ 2`;
- in `(iii)`: under every joint coupling of `(G_m)_{m ≥ 2}` with marginals `G_m ∼ G(m, 1/2)`,
  the explicit sub-Gaussian tail-union rate
  `ℙ(∃ m ≥ n : |Y_m - 1/4| > ε) ≤ 2 exp(-ϑ² ε² n / (2 (log₂ n)⁶))` eventually for all `ε > 0`
  and `ϑ ∈ (0, 1)`, together with almost-sure convergence `Y_n → 1/4` and
  `((log n)³ / n) Δ(G_n) → (log 2)³ / 4`. -/
theorem mainTheorem_v11_complete
    (htail : ∀ eps : ℝ, 0 < eps →
      (fun n : ℕ ↦ (randomGraphMeasure n).real
        {G : LabeledGraph n |
          eps < |(Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
            ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) - 1 / 4|})
        =O[atTop] quasiExpTail) :
    let D : ∀ n : ℕ, LabeledGraph n → ℝ := fun _ G ↦
      (chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)
    let Y : ∀ n : ℕ, LabeledGraph n → ℝ := fun n G ↦
      (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) * D n G
    ((∀ n : ℕ,
        (∫ G : LabeledGraph n, (D n G - ∫ H, D n H ∂randomGraphMeasure n) ^ 2
          ∂randomGraphMeasure n) ≤ ((n - 1 : ℕ) : ℝ)) ∧
      (∀ {n : ℕ}, 2 ≤ n → ∀ lam : ℝ,
        0 ≤ Real.log (∫ G : LabeledGraph n, Real.exp (lam * Y n G) ∂randomGraphMeasure n) -
            lam * (∫ H : LabeledGraph n, Y n H ∂randomGraphMeasure n) ∧
          Real.log (∫ G : LabeledGraph n, Real.exp (lam * Y n G) ∂randomGraphMeasure n) -
            lam * (∫ H : LabeledGraph n, Y n H ∂randomGraphMeasure n) ≤
          lam ^ 2 * (Real.logb 2 (n : ℝ)) ^ 6 / (2 * (n : ℝ))) ∧
      (∀ {n : ℕ}, 2 ≤ n → ∀ {u : ℝ}, 0 ≤ u →
        (randomGraphMeasure n).real
            {G : LabeledGraph n | u ≤ |Y n G - ∫ H, Y n H ∂randomGraphMeasure n|} ≤
          2 * Real.exp (-u ^ 2 * (n : ℝ) / (2 * (Real.logb 2 (n : ℝ)) ^ 6))) ∧
      (∀ {n : ℕ}, 2 ≤ n → ∀ {θ : ℝ}, θ ∈ Set.Ico (0 : ℝ) (1 / 2) →
        (∫ G : LabeledGraph n,
            Real.exp (θ * (D n G - ∫ H, D n H ∂randomGraphMeasure n) ^ 2 / ((n - 1 : ℕ) : ℝ))
            ∂randomGraphMeasure n) ≤ (1 - 2 * θ) ^ (-(1 / 2 : ℝ)) ∧
        (∫ G : LabeledGraph n,
            Real.exp (θ * (n : ℝ) * (Y n G - ∫ H, Y n H ∂randomGraphMeasure n) ^ 2 /
              (Real.logb 2 (n : ℝ)) ^ 6)
            ∂randomGraphMeasure n) ≤ (1 - 2 * θ) ^ (-(1 / 2 : ℝ))) ∧
      (∀ {n : ℕ}, 2 ≤ n →
        let S_D : Set ℝ := {s : ℝ | 0 < s ∧
          (∫ G : LabeledGraph n,
              Real.exp ((D n G - ∫ H, D n H ∂randomGraphMeasure n) ^ 2 / s ^ 2)
              ∂randomGraphMeasure n) ≤ 2}
        let S_Y : Set ℝ := {s : ℝ | 0 < s ∧
          (∫ G : LabeledGraph n,
              Real.exp ((Y n G - ∫ H, Y n H ∂randomGraphMeasure n) ^ 2 / s ^ 2)
              ∂randomGraphMeasure n) ≤ 2}
        (S_D.Nonempty ∧ BddBelow S_D ∧
          sInf S_D ≤ Real.sqrt (8 / 3 * ((n - 1 : ℕ) : ℝ))) ∧
        (S_Y.Nonempty ∧ BddBelow S_Y ∧
          sInf S_Y ≤ Real.sqrt (8 / 3) * (Real.logb 2 (n : ℝ)) ^ 3 / Real.sqrt (n : ℝ))) ∧
      (∀ {n : ℕ}, 2 ≤ n → ∀ {p : ℝ}, 1 ≤ p →
        (∫ G : LabeledGraph n, |D n G - ∫ H, D n H ∂randomGraphMeasure n| ^ p
          ∂randomGraphMeasure n) ≤
          2 * (p / Real.exp 1 * ((n - 1 : ℕ) : ℝ)) ^ (p / 2) ∧
        (∫ G : LabeledGraph n, |Y n G - ∫ H, Y n H ∂randomGraphMeasure n| ^ p
          ∂randomGraphMeasure n) ≤
          2 * (p * (Real.logb 2 (n : ℝ)) ^ 6 / (Real.exp 1 * (n : ℝ))) ^ (p / 2))) ∧
    (∀ {eps theta : ℝ}, 0 < eps → theta ∈ Set.Ioo 0 1 →
      ∀ᶠ n : ℕ in atTop,
        (randomGraphMeasure n).real {G : LabeledGraph n | eps < |Y n G - 1 / 4|} ≤
          2 * Real.exp (-theta ^ 2 * eps ^ 2 * (n : ℝ) / (2 * (Real.logb 2 (n : ℝ)) ^ 6))) ∧
    (∀ {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
      (G : ∀ m : ℕ, Ω → LabeledGraph m),
      (∀ m : ℕ, 2 ≤ m → Measure.map (G m) ℙ = randomGraphMeasure m) →
      (∀ {eps theta : ℝ}, 0 < eps → theta ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ᶠ n : ℕ in atTop,
          ℙ.real {ω : Ω | ∃ m ≥ n, eps < |Y m (G m ω) - 1 / 4|} ≤
            2 * Real.exp (-theta ^ 2 * eps ^ 2 * (n : ℝ) / (2 * (Real.logb 2 (n : ℝ)) ^ 6))) ∧
      (∀ᵐ ω ∂ℙ,
        Tendsto (fun n : ℕ ↦ (Real.log n) ^ 3 / (n : ℝ) * D n (G n ω))
          atTop (nhds sharpGapConstant) ∧
        Tendsto (fun n : ℕ ↦ Y n (G n ω)) atTop (nhds (1 / 4 : ℝ)))) ∧
    ((∀ {p : ℝ}, 1 ≤ p →
        Tendsto (fun n : ℕ ↦ ∫ G : LabeledGraph n, |Y n G - 1 / 4| ^ p ∂randomGraphMeasure n)
          atTop (nhds 0)) ∧
      Tendsto (fun n : ℕ ↦
        (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
          ∫ G : LabeledGraph n, D n G ∂randomGraphMeasure n)
        atTop (nhds (1 / 4 : ℝ)) ∧
      (∀ {T : ℝ}, 0 ≤ T →
        TendstoUniformlyOn
          (fun n t ↦ Real.log (∫ G : LabeledGraph n, Real.exp (t * Y n G) ∂randomGraphMeasure n))
          (fun t ↦ t / 4) atTop (Set.Icc (-T) T) ∧
        TendstoUniformlyOn
          (fun n t ↦ ∫ G : LabeledGraph n, Real.exp (t * Y n G) ∂randomGraphMeasure n)
          (fun t ↦ Real.exp (t / 4)) atTop (Set.Icc (-T) T))) := by
  intro D Y
  obtain ⟨⟨hvar, hcgf, hmean_tail, hsq_exp, hlp_central⟩, hsubg, _, hconv⟩ :=
    mainTheorem_v10_complete.{0} htail
  have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hexp_rew : ∀ {a_c : ℝ} {m : ℕ}, 2 ≤ m →
      -a_c * (m : ℝ) / (2 * (Real.logb 2 (m : ℝ)) ^ 6) =
        -(a_c * (Real.log 2) ^ 6) * (m : ℝ) / (2 * (Real.log (m : ℝ)) ^ 6) := by
    intro a_c m hm2
    have hL_pos : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
    rw [Real.logb, div_pow]
    field_simp [hL_pos.ne', hq_pos.ne']
  refine ⟨⟨hvar, hcgf, hmean_tail, hsq_exp,
    fun {_} hn ↦ ⟨orliczPsi2_chromaticSubCochromatic_le hn, orliczPsi2_normalizedGap_le hn⟩,
    hlp_central⟩, hsubg, ?_, hconv⟩
  intro Ω _ ℙ _ G hMarg
  have hcoupling_tail :
      ∀ {eps theta : ℝ}, 0 < eps → theta ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ᶠ n : ℕ in atTop,
          ℙ.real {ω : Ω | ∃ m ≥ n, eps < |Y m (G m ω) - 1 / 4|} ≤
            2 * Real.exp (-theta ^ 2 * eps ^ 2 * (n : ℝ) / (2 * (Real.logb 2 (n : ℝ)) ^ 6)) := by
    intro eps theta heps htheta
    have ha_pos : 0 < eps ^ 2 * (Real.log 2) ^ 6 := by positivity
    obtain ⟨N_u, hN_u⟩ := eventually_coupling_tailUnion_of_subgaussian_marginals
      (fun m ↦ {H : LabeledGraph m | eps < |Y m H - 1 / 4|}) ha_pos
      (fun {ϑ₁} hϑ₁ ↦ by
        filter_upwards [eventually_ge_atTop 2, hsubg heps hϑ₁] with m hm2 hm_tail
        have hL_pos : 0 < Real.log (m : ℝ) :=
          Real.log_pos (by exact_mod_cast (show 1 < m by omega))
        have hrw : -ϑ₁ ^ 2 * eps ^ 2 * (m : ℝ) / (2 * (Real.logb 2 (m : ℝ)) ^ 6) =
            -ϑ₁ ^ 2 * (eps ^ 2 * (Real.log 2) ^ 6) * (m : ℝ) / (2 * (Real.log (m : ℝ)) ^ 6) := by
          rw [Real.logb, div_pow]
          field_simp [hL_pos.ne', hq_pos.ne']
        rwa [hrw] at hm_tail)
      htheta
    filter_upwards [eventually_ge_atTop (max 2 N_u)] with n hn
    have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
    have hn_Nu : N_u ≤ n := le_trans (le_max_right _ _) hn
    have hbound := hN_u ℙ G hMarg n hn_Nu
    have hL_pos : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hrw : -theta ^ 2 * eps ^ 2 * (n : ℝ) / (2 * (Real.logb 2 (n : ℝ)) ^ 6) =
        -theta ^ 2 * (eps ^ 2 * (Real.log 2) ^ 6) * (n : ℝ) / (2 * (Real.log (n : ℝ)) ^ 6) := by
      rw [Real.logb, div_pow]
      field_simp [hL_pos.ne', hq_pos.ne']
    rwa [← hrw] at hbound
  refine ⟨fun heps hth ↦ hcoupling_tail heps hth, ?_⟩
  have hall : ∀ᵐ ω ∂ℙ, ∀ r : ℕ, ∀ᶠ m : ℕ in atTop,
      |Y m (G m ω) - 1 / 4| ≤ 1 / ((r : ℝ) + 1) := by
    rw [ae_all_iff]
    intro r
    set eps_r : ℝ := 1 / ((r : ℝ) + 1)
    have heps_r : 0 < eps_r := by dsimp [eps_r]; positivity
    have hth_half : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num
    have hunion_r : ∀ᶠ n : ℕ in atTop,
        ℙ.real {ω : Ω | ∃ m ≥ n, ω ∈ (fun m ↦ {ω' : Ω | eps_r < |Y m (G m ω') - 1 / 4|}) m} ≤
          2 * Real.exp (-((1 / 2 : ℝ) ^ 2 * eps_r ^ 2 * (Real.log 2) ^ 6 / 2) *
            (n : ℝ) / (Real.log (n : ℝ)) ^ 6) := by
      filter_upwards [eventually_ge_atTop 2, hcoupling_tail heps_r hth_half] with
        n hn2 hn_tail
      have hL_pos : 0 < Real.log (n : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      have hrw_all : -(1 / 2 : ℝ) ^ 2 * eps_r ^ 2 * (n : ℝ) / (2 * (Real.logb 2 (n : ℝ)) ^ 6) =
          -((1 / 2 : ℝ) ^ 2 * eps_r ^ 2 * (Real.log 2) ^ 6 / 2) *
            (n : ℝ) / (Real.log (n : ℝ)) ^ 6 := by
        rw [Real.logb, div_pow]
        field_simp [hL_pos.ne', hq_pos.ne']
      rwa [hrw_all] at hn_tail
    have hae_r := ae_eventually_notMem_of_tailUnion_tendsto_zero ℙ hunion_r
      (tendsto_exp_neg_div_log_pow_six_zero (by positivity))
    filter_upwards [hae_r] with ω hω
    filter_upwards [hω] with m hm
    exact not_lt.mp hm
  filter_upwards [hall] with ω hω
  have hY_lim : Tendsto (fun m : ℕ ↦ Y m (G m ω)) atTop (nhds (1 / 4 : ℝ)) := by
    rw [Metric.tendsto_nhds]
    intro delta hdelta
    obtain ⟨r, hr⟩ := exists_nat_one_div_lt hdelta
    filter_upwards [hω r] with m hm
    rw [Real.dist_eq]
    exact lt_of_le_of_lt hm hr
  refine ⟨?_, hY_lim⟩
  have hmul_lim := hY_lim.const_mul ((Real.log 2) ^ 3)
  have hsharp_eq : (Real.log 2) ^ 3 * (1 / 4 : ℝ) = sharpGapConstant := by
    unfold sharpGapConstant; ring
  rw [hsharp_eq] at hmul_lim
  refine hmul_lim.congr fun n ↦ ?_
  dsimp [Y]
  rw [Real.logb, div_pow]
  have hq3_ne : (Real.log 2) ^ 3 ≠ 0 := pow_ne_zero 3 hq_pos.ne'
  calc (Real.log 2) ^ 3 * ((Real.log (n : ℝ)) ^ 3 / (Real.log 2) ^ 3 / (n : ℝ) * D n (G n ω))
      = ((Real.log 2) ^ 3 * ((Real.log (n : ℝ)) ^ 3 / (Real.log 2) ^ 3)) / (n : ℝ) * D n (G n ω) := by
        ring
    _ = (Real.log (n : ℝ)) ^ 3 / (n : ℝ) * D n (G n ω) := by
        rw [mul_div_cancel₀ _ hq3_ne]

end

end Erdos625HP
