import Erdos625HP.FiniteDualsCorridorRootsAndRegularity

/-!
# v12 Orlicz `ψ₂` subadditivity & moment convergence, non-asymptotic `√(2 n log n)` fluctuations, infinite-support duals & corridor roots, unconditional Proposition 4.1(i)–(iii) & `(5.20)`, and Lemma 7.1 `B_π` regularity

This module formalizes the v12 mathematical and Lean 4 upgrades across the Abstract, Main Theorem,
Phase Refinement, Sections 3, 4, 5.2, 7, 8, and 9 using **zero** public definitions (`0` public
`def`/`abbrev`/`structure` declarations) and only the standard Lean kernel foundations
(`propext`, `Classical.choice`, `Quot.sound`):

1. **Main Theorem `(iv)` & Corollary 8.1 — Orlicz `ψ₂` constant formula, triangle inequality
   (`‖X + Y‖_{ψ₂} ≤ ‖X‖_{ψ₂} + ‖Y‖_{ψ₂}`), non-asymptotic `‖Y_n - 1/4‖_{ψ₂}` bound, and
   arbitrary-rate square-exponential moment convergence (`E[exp(M Z_n²)] → 1`):**
   - `orliczPsi2_const_and_add_le`: proves `‖c‖_{ψ₂} = |c| / √(log 2)` and subadditivity
     `‖X + Y‖_{ψ₂} ≤ ‖X‖_{ψ₂} + ‖Y‖_{ψ₂}` on general probability spaces via convexity and
     monotonicity of `u ↦ exp(u²)` on `[0, ∞)`.
   - `orliczPsi2_normalizedGap_sub_quarter_le`: proves for all `n ≥ 2` that
     `‖Y_n - 1/4‖_{ψ₂} ≤ ‖Y_n - E[Y_n]‖_{ψ₂} + |E[Y_n] - 1/4| / √(log 2)`
     `≤ √(8/3) (log₂ n)³ / √n + |E[Y_n] - 1/4| / √(log 2)`.
   - `tendsto_sqExpMoment_one_of_orliczPsi2_tendsto_zero`: proves that `‖Z_n‖_{ψ₂} → 0` implies
     `E[exp(M Z_n²)] → 1` for every `M ≥ 0` via tangent-line concave Jensen on `u ↦ u^(M s²)`.

2. **Main Theorem `(i)` & Corollary 8.1 — Non-asymptotic coupling-uniform tail-union bound &
   arbitrary-coupling almost-sure `√(2 n log n)` fluctuation envelope:**
   - `coupling_tailUnion_chromaticSubCochromatic_sqrt_log_le`: for all `n ≥ 2`, `η > 0`, and every
     joint coupling of `(G_m)_{m ≥ 2}` with marginals `G(m, 1/2)`,
     `ℙ(∃ m ≥ n : |Δ(G_m) - E[Δ(G_m)]| ≥ √(2(1 + η)(m - 1) log m)) ≤ 2 (1/η + 1/n) n^(-η)`.
   - `ae_limsup_chromaticSubCochromatic_and_normalizedGap_le_one`: under every joint coupling,
     almost surely `limsup |Δ(G_n) - E[Δ(G_n)]| / √(2 n log n) ≤ 1` and
     `limsup (√n / ((log₂ n)³ √(2 log n))) |Y_n - E[Y_n]| ≤ 1`.

3. **Section 3 & Section 5.2 — Infinite-support Lemma 3.2(i),(iv) `O(1/α)` dual errors, Lemma 3.1
   corridor roots (`∃!`), mixed `(5.19)` root separations, and unconditional Proposition 5.3(iii) `(5.20)`:**
   - `abs_infiniteFiniteEntropy_sub_dualValue_le` and
     `abs_cappedInfiniteFiniteEntropy_sub_cappedDualValue_le`: `O(1/α)` dual errors for `S_{≥ m}`
     (`m ∈ {0, 1, 2}`) on `[9/4, 9/2] ⊃ K_*` and capped `S_{≥ 1}^{=ϑ}` on `[0, 1/20] × K_cap`.
   - `exists_pos_eventually_existsUnique_infinitePhaseObjective_zero_logLogCorridor` and
     `exists_pos_eventually_existsUnique_cappedInfinitePhaseObjective_zero_logLogCorridor`:
     strict monotonicity, `∃!` corridor roots, and `(3.6)` `O(log log n / log n)` location for
     `𝓛_{S_{≥ m}}(n, ·) + τ ·` (`m ≤ 2`) and `𝓛_{S_{≥ 1}}^{=ϑ}(n, ·) + τ ·`.
   - `eventually_allSupport_corridorRoot_separation_and_prop53_iii`: mixed infinite-vs-finite
     corridor-root separation `(5.19)` and **unconditional** Proposition 5.3(iii) `(5.20)`
     (including unconditional `tildeEps n = O(log log n / log n)` for `(m_n, 7)`).

4. **Section 4 — Complete unconditional Proposition 4.1(i)–(iii) quasi-exponential lower tails:**
   - `eventually_randomGraph_lowerTails_prop41_i`, `eventually_randomGraph_lowerTails_prop41_ii`,
     and `eventually_randomGraph_lowerTails_prop41_iii`.

5. **Section 7 & Section 9 — Unconditional Lemma 7.1 `B_π` regularity, complete Lemma 7.1
   synthesis, and upgraded `phaseRefinement_v12_complete` & `mainTheorem_v12_complete`
   (with coupling-independent `∃ N : ℕ` placed outside `∀ Ω ℙ G`).**
-/

namespace Erdos625HP

open Erdos625 Erdos625.FiveSizeEntropyGap FiveSizePhaseGainSharp FiveSizePhaseGainCertificate
open Filter Asymptotics MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal

noncomputable section

set_option autoImplicit false

/-!
## 1. Orlicz `ψ₂` constant formula, subadditivity, and square-exponential moment convergence
-/

private theorem monotoneOn_and_convexOn_exp_sq :
    MonotoneOn (fun u : ℝ ↦ Real.exp (u ^ 2)) (Set.Ici 0) ∧
      ConvexOn ℝ (Set.Ici 0) (fun u : ℝ ↦ Real.exp (u ^ 2)) := by
  let f : ℝ → ℝ := fun u ↦ Real.exp (u ^ 2)
  let df : ℝ → ℝ := fun u ↦ 2 * u * Real.exp (u ^ 2)
  have hdf : ∀ u : ℝ, HasDerivAt f (df u) u := by
    intro u
    have hsq : HasDerivAt (fun x : ℝ ↦ x ^ 2) (2 * u) u := by
      simpa using hasDerivAt_pow 2 u
    exact (hsq.exp).congr_deriv (by dsimp [df]; ring)
  have hddf : ∀ u : ℝ, HasDerivAt df ((2 + 4 * u ^ 2) * Real.exp (u ^ 2)) u := by
    intro u
    have h1 : HasDerivAt (fun x : ℝ ↦ 2 * x) 2 u := by
      simpa using (hasDerivAt_id u).const_mul 2
    have h2 : HasDerivAt (fun x : ℝ ↦ Real.exp (x ^ 2)) (2 * u * Real.exp (u ^ 2)) u := hdf u
    exact (h1.mul h2).congr_deriv (by ring)
  have hmono_f : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun u _ ↦ (hdf u).continuousAt.continuousWithinAt
    · exact fun u _ ↦ (hdf u).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Ici] at hu
      have hu0 : 0 < u := hu
      rw [(hdf u).deriv]
      dsimp [df]
      positivity
  have hmono_df : Monotone df := by
    apply monotone_of_deriv_nonneg (fun u ↦ (hddf u).differentiableAt)
    intro u
    rw [(hddf u).deriv]
    positivity
  have hsubgrad : ∀ m t : ℝ, f m + df m * (t - m) ≤ f t := by
    intro m t
    let g : ℝ → ℝ := fun u ↦ f u - f m - df m * (u - m)
    have hdg : ∀ u : ℝ, HasDerivAt g (df u - df m) u := by
      intro u
      have hlin : HasDerivAt (fun v : ℝ ↦ df m * (v - m)) (df m) u := by
        simpa using ((hasDerivAt_id u).sub_const m).const_mul (df m)
      exact ((hdf u).sub_const (f m)).sub hlin
    rcases le_total m t with hmt | htm
    · have hm_g : MonotoneOn g (Set.Icc m t) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc m t)
        · exact fun u _ ↦ (hdg u).continuousAt.continuousWithinAt
        · exact fun u _ ↦ (hdg u).differentiableAt.differentiableWithinAt
        · intro u hu
          rw [interior_Icc] at hu
          rw [(hdg u).deriv]
          linarith [hmono_df hu.1.le]
      have h0 : g m ≤ g t := hm_g ⟨le_rfl, hmt⟩ ⟨hmt, le_rfl⟩ hmt
      dsimp [g] at h0
      linarith
    · have hm_ng : MonotoneOn (-g) (Set.Icc t m) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc t m)
        · exact fun u _ ↦ (hdg u).neg.continuousAt.continuousWithinAt
        · exact fun u _ ↦ (hdg u).neg.differentiableAt.differentiableWithinAt
        · intro u hu
          rw [interior_Icc] at hu
          rw [((hdg u).neg).deriv]
          linarith [hmono_df hu.2.le]
      have h0 : (-g) t ≤ (-g) m := hm_ng ⟨le_rfl, htm⟩ ⟨htm, le_rfl⟩ htm
      simp only [Pi.neg_apply, g] at h0
      linarith
  refine ⟨hmono_f, convex_Ici 0, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  set m : ℝ := a * x + b * y
  have hsx := mul_le_mul_of_nonneg_left (hsubgrad m x) ha
  have hsy := mul_le_mul_of_nonneg_left (hsubgrad m y) hb
  have hcomb : a * (f m + df m * (x - m)) + b * (f m + df m * (y - m)) = f m := by
    dsimp [m]
    linear_combination (f m - df m * (a * x + b * y)) * hab
  linarith

private theorem exp_sq_add_div_le {x y s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) :
    Real.exp ((x + y) ^ 2 / (s₁ + s₂) ^ 2) ≤
      s₁ / (s₁ + s₂) * Real.exp (x ^ 2 / s₁ ^ 2) +
        s₂ / (s₁ + s₂) * Real.exp (y ^ 2 / s₂ ^ 2) := by
  obtain ⟨hmono, hconv⟩ := monotoneOn_and_convexOn_exp_sq
  have hsum_pos : 0 < s₁ + s₂ := add_pos hs₁ hs₂
  set w₁ : ℝ := s₁ / (s₁ + s₂)
  set w₂ : ℝ := s₂ / (s₁ + s₂)
  have hw₁ : 0 ≤ w₁ := div_nonneg hs₁.le hsum_pos.le
  have hw₂ : 0 ≤ w₂ := div_nonneg hs₂.le hsum_pos.le
  have hw_sum : w₁ + w₂ = 1 := by dsimp [w₁, w₂]; rw [← add_div, div_self hsum_pos.ne']
  have htri : |x + y| / (s₁ + s₂) ≤ w₁ * (|x| / s₁) + w₂ * (|y| / s₂) := by
    have h1 : w₁ * (|x| / s₁) + w₂ * (|y| / s₂) = (|x| + |y|) / (s₁ + s₂) := by
      dsimp [w₁, w₂]
      field_simp [hs₁.ne', hs₂.ne', hsum_pos.ne']
    rw [h1]
    exact div_le_div_of_nonneg_right (abs_add_le x y) hsum_pos.le
  have hstep1 :
      Real.exp ((|x + y| / (s₁ + s₂)) ^ 2) ≤
        Real.exp ((w₁ * (|x| / s₁) + w₂ * (|y| / s₂)) ^ 2) :=
    hmono (div_nonneg (abs_nonneg _) hsum_pos.le)
      (add_nonneg (mul_nonneg hw₁ (div_nonneg (abs_nonneg _) hs₁.le))
        (mul_nonneg hw₂ (div_nonneg (abs_nonneg _) hs₂.le)))
      htri
  have hstep2 :
      Real.exp ((w₁ * (|x| / s₁) + w₂ * (|y| / s₂)) ^ 2) ≤
        w₁ * Real.exp ((|x| / s₁) ^ 2) + w₂ * Real.exp ((|y| / s₂) ^ 2) := by
    have hc := hconv.2 (show |x| / s₁ ∈ Set.Ici 0 from div_nonneg (abs_nonneg _) hs₁.le)
      (show |y| / s₂ ∈ Set.Ici 0 from div_nonneg (abs_nonneg _) hs₂.le) hw₁ hw₂ hw_sum
    simpa only [smul_eq_mul] using hc
  have hsq_xy : (|x + y| / (s₁ + s₂)) ^ 2 = (x + y) ^ 2 / (s₁ + s₂) ^ 2 := by
    rw [div_pow, sq_abs]
  have hsq_x : (|x| / s₁) ^ 2 = x ^ 2 / s₁ ^ 2 := by rw [div_pow, sq_abs]
  have hsq_y : (|y| / s₂) ^ 2 = y ^ 2 / s₂ ^ 2 := by rw [div_pow, sq_abs]
  rw [← hsq_xy, ← hsq_x, ← hsq_y]
  exact hstep1.trans hstep2

/-- **Main Theorem `(iv)` & Corollary 8.1 Orlicz `ψ₂` constant formula and triangle inequality:**
on any probability space `(Ω, ℙ)`:
1. for every deterministic constant `c ∈ ℝ`, the Orlicz `ψ₂` scale set has infimum
   `‖c‖_{ψ₂} = |c| / √(log 2)` (both with and without the `Integrable` guard, which is automatic
   for constants);
2. for any `AEStronglyMeasurable` random variables `X, Y : Ω → ℝ` with finite Orlicz `ψ₂` norms
   (`S_X.Nonempty` and `S_Y.Nonempty`), `S_{X + Y}.Nonempty`, `BddBelow S_{X + Y}`, and
   `‖X + Y‖_{ψ₂} ≤ ‖X‖_{ψ₂} + ‖Y‖_{ψ₂}`. -/
theorem orliczPsi2_const_and_add_le
    {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ] :
    (∀ c : ℝ,
      let S_c : Set ℝ := {s : ℝ | 0 < s ∧
        (∫ _ : Ω, Real.exp (c ^ 2 / s ^ 2) ∂ℙ) ≤ 2}
      S_c.Nonempty ∧ BddBelow S_c ∧ sInf S_c = |c| / Real.sqrt (Real.log 2)) ∧
    (∀ {X Y : Ω → ℝ},
      AEStronglyMeasurable X ℙ → AEStronglyMeasurable Y ℙ →
      let S_X : Set ℝ := {s : ℝ | 0 < s ∧
        Integrable (fun ω ↦ Real.exp ((X ω) ^ 2 / s ^ 2)) ℙ ∧
        (∫ ω : Ω, Real.exp ((X ω) ^ 2 / s ^ 2) ∂ℙ) ≤ 2}
      let S_Y : Set ℝ := {s : ℝ | 0 < s ∧
        Integrable (fun ω ↦ Real.exp ((Y ω) ^ 2 / s ^ 2)) ℙ ∧
        (∫ ω : Ω, Real.exp ((Y ω) ^ 2 / s ^ 2) ∂ℙ) ≤ 2}
      let S_XY : Set ℝ := {s : ℝ | 0 < s ∧
        Integrable (fun ω ↦ Real.exp ((X ω + Y ω) ^ 2 / s ^ 2)) ℙ ∧
        (∫ ω : Ω, Real.exp ((X ω + Y ω) ^ 2 / s ^ 2) ∂ℙ) ≤ 2}
      S_X.Nonempty → S_Y.Nonempty →
      S_XY.Nonempty ∧ BddBelow S_XY ∧ sInf S_XY ≤ sInf S_X + sInf S_Y) := by
  have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hsqrt_q_pos : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.mpr hq_pos
  constructor
  · intro c S_c
    have hbdd : BddBelow S_c := ⟨0, fun s hs ↦ hs.1.le⟩
    have hint_const : ∀ s : ℝ,
        (∫ _ : Ω, Real.exp (c ^ 2 / s ^ 2) ∂ℙ) = Real.exp (c ^ 2 / s ^ 2) := by
      intro s
      simp [integral_const, probReal_univ]
    by_cases hc : c = 0
    · subst hc
      have h1_mem : (1 : ℝ) ∈ S_c := by
        refine ⟨zero_lt_one, ?_⟩
        rw [hint_const]; norm_num
      refine ⟨⟨1, h1_mem⟩, hbdd, ?_⟩
      rw [abs_zero, zero_div]
      apply le_antisymm
      · refine le_of_forall_pos_lt_add fun eps heps ↦ ?_
        rw [zero_add]
        have heps_half_mem : eps / 2 ∈ S_c := by
          refine ⟨half_pos heps, ?_⟩
          rw [hint_const]; norm_num
        exact (csInf_le hbdd heps_half_mem).trans_lt (half_lt_self heps)
      · exact le_csInf ⟨1, h1_mem⟩ fun s hs ↦ hs.1.le
    · set s₀ : ℝ := |c| / Real.sqrt (Real.log 2)
      have habs_pos : 0 < |c| := abs_pos.mpr hc
      have hs₀_pos : 0 < s₀ := div_pos habs_pos hsqrt_q_pos
      have hs₀_sq : c ^ 2 / s₀ ^ 2 = Real.log 2 := by
        dsimp [s₀]
        rw [div_pow, sq_abs, Real.sq_sqrt hq_pos.le]
        field_simp [hq_pos.ne', (sq_pos_of_ne_zero hc).ne']
      have hs₀_mem : s₀ ∈ S_c := by
        refine ⟨hs₀_pos, ?_⟩
        rw [hint_const, hs₀_sq, Real.exp_log two_pos]
      refine ⟨⟨s₀, hs₀_mem⟩, hbdd, le_antisymm (csInf_le hbdd hs₀_mem) ?_⟩
      refine le_csInf ⟨s₀, hs₀_mem⟩ fun s ⟨hs_pos, hs_int⟩ ↦ ?_
      rw [hint_const] at hs_int
      have hlog_le : c ^ 2 / s ^ 2 ≤ Real.log 2 := by
        have h := Real.log_le_log (Real.exp_pos _) hs_int
        rwa [Real.log_exp] at h
      have hsq_le : (|c| / Real.sqrt (Real.log 2)) ^ 2 ≤ s ^ 2 := by
        rw [div_pow, sq_abs, Real.sq_sqrt hq_pos.le, div_le_iff₀ hq_pos]
        have hm := (div_le_iff₀ (sq_pos_of_pos hs_pos)).mp hlog_le
        linarith
      exact le_of_pow_le_pow_left₀ (by norm_num : 2 ≠ 0) hs_pos.le hsq_le
  · intro X Y hX hY S_X S_Y S_XY hSX hSY
    have hbddX : BddBelow S_X := ⟨0, fun s hs ↦ hs.1.le⟩
    have hbddY : BddBelow S_Y := ⟨0, fun s hs ↦ hs.1.le⟩
    have hbddXY : BddBelow S_XY := ⟨0, fun s hs ↦ hs.1.le⟩
    have hpair_mem : ∀ {s₁ s₂ : ℝ}, s₁ ∈ S_X → s₂ ∈ S_Y → s₁ + s₂ ∈ S_XY := by
      intro s₁ s₂ ⟨hs₁_pos, hInt₁, hle₁⟩ ⟨hs₂_pos, hInt₂, hle₂⟩
      have hsum_pos : 0 < s₁ + s₂ := add_pos hs₁_pos hs₂_pos
      set maj : Ω → ℝ := fun ω ↦
        s₁ / (s₁ + s₂) * Real.exp ((X ω) ^ 2 / s₁ ^ 2) +
          s₂ / (s₁ + s₂) * Real.exp ((Y ω) ^ 2 / s₂ ^ 2)
      have hInt_maj : Integrable maj ℙ :=
        (hInt₁.const_mul (s₁ / (s₁ + s₂))).add (hInt₂.const_mul (s₂ / (s₁ + s₂)))
      have hcont_exp : Continuous (fun t : ℝ ↦ Real.exp (t ^ 2 / (s₁ + s₂) ^ 2)) := by
        fun_prop
      have haesm : AEStronglyMeasurable (fun ω ↦ Real.exp ((X ω + Y ω) ^ 2 / (s₁ + s₂) ^ 2)) ℙ :=
        hcont_exp.comp_aestronglyMeasurable (hX.add hY)
      have hpt : ∀ ω : Ω, Real.exp ((X ω + Y ω) ^ 2 / (s₁ + s₂) ^ 2) ≤ maj ω :=
        fun ω ↦ exp_sq_add_div_le hs₁_pos hs₂_pos
      have hInt_XY : Integrable (fun ω ↦ Real.exp ((X ω + Y ω) ^ 2 / (s₁ + s₂) ^ 2)) ℙ :=
        hInt_maj.mono' haesm (Filter.Eventually.of_forall fun ω ↦ by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact hpt ω)
      refine ⟨hsum_pos, hInt_XY, ?_⟩
      calc (∫ ω : Ω, Real.exp ((X ω + Y ω) ^ 2 / (s₁ + s₂) ^ 2) ∂ℙ)
          ≤ ∫ ω : Ω, maj ω ∂ℙ := integral_mono hInt_XY hInt_maj hpt
        _ = s₁ / (s₁ + s₂) * (∫ ω : Ω, Real.exp ((X ω) ^ 2 / s₁ ^ 2) ∂ℙ) +
              s₂ / (s₁ + s₂) * (∫ ω : Ω, Real.exp ((Y ω) ^ 2 / s₂ ^ 2) ∂ℙ) := by
            dsimp [maj]
            rw [integral_add (hInt₁.const_mul _) (hInt₂.const_mul _),
              integral_const_mul, integral_const_mul]
        _ ≤ s₁ / (s₁ + s₂) * 2 + s₂ / (s₁ + s₂) * 2 :=
            add_le_add (mul_le_mul_of_nonneg_left hle₁ (div_nonneg hs₁_pos.le hsum_pos.le))
              (mul_le_mul_of_nonneg_left hle₂ (div_nonneg hs₂_pos.le hsum_pos.le))
        _ = 2 := by field_simp [hsum_pos.ne']
    rcases hSX with ⟨s₁₀, hs₁₀⟩
    rcases hSY with ⟨s₂₀, hs₂₀⟩
    have hXY_ne : S_XY.Nonempty := ⟨s₁₀ + s₂₀, hpair_mem hs₁₀ hs₂₀⟩
    refine ⟨hXY_ne, hbddXY, ?_⟩
    have hle_all : ∀ s₁ ∈ S_X, ∀ s₂ ∈ S_Y, sInf S_XY ≤ s₁ + s₂ :=
      fun s₁ hs₁ s₂ hs₂ ↦ csInf_le hbddXY (hpair_mem hs₁ hs₂)
    have hstep_X : ∀ s₂ ∈ S_Y, sInf S_XY - s₂ ≤ sInf S_X := by
      intro s₂ hs₂
      refine le_csInf ⟨s₁₀, hs₁₀⟩ fun s₁ hs₁ ↦ ?_
      linarith [hle_all s₁ hs₁ s₂ hs₂]
    have hstep_Y : sInf S_XY - sInf S_X ≤ sInf S_Y := by
      refine le_csInf ⟨s₂₀, hs₂₀⟩ fun s₂ hs₂ ↦ ?_
      linarith [hstep_X s₂ hs₂]
    linarith

/-- **Main Theorem `(iv)` non-asymptotic Orlicz `ψ₂` bound for `Y_n - 1/4` (`main.tex` line 133):**
for every `n ≥ 2`, `‖Y_n - 1/4‖_{ψ₂} ≤ ‖Y_n - E[Y_n]‖_{ψ₂} + |E[Y_n] - 1/4| / √(log 2)`
`≤ √(8/3) · (log₂ n)³ / √n + |E[Y_n] - 1/4| / √(log 2)`. -/
theorem orliczPsi2_normalizedGap_sub_quarter_le {n : ℕ} (hn : 2 ≤ n) :
    let Y : LabeledGraph n → ℝ := fun G ↦
      (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
        ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
    let μ : ℝ := ∫ H : LabeledGraph n, Y H ∂randomGraphMeasure n
    let S_center : Set ℝ := {s : ℝ | 0 < s ∧
      (∫ G : LabeledGraph n, Real.exp ((Y G - μ) ^ 2 / s ^ 2) ∂randomGraphMeasure n) ≤ 2}
    let S_quarter : Set ℝ := {s : ℝ | 0 < s ∧
      (∫ G : LabeledGraph n, Real.exp ((Y G - 1 / 4) ^ 2 / s ^ 2) ∂randomGraphMeasure n) ≤ 2}
    S_quarter.Nonempty ∧ BddBelow S_quarter ∧
      sInf S_quarter ≤ sInf S_center + |μ - 1 / 4| / Real.sqrt (Real.log 2) ∧
      sInf S_quarter ≤
        Real.sqrt (8 / 3) * (Real.logb 2 (n : ℝ)) ^ 3 / Real.sqrt (n : ℝ) +
          |μ - 1 / 4| / Real.sqrt (Real.log 2) := by
  intro Y μ S_center S_quarter
  obtain ⟨hconst, hsubadd⟩ := orliczPsi2_const_and_add_le (randomGraphMeasure n)
  obtain ⟨hSc_ne, _, hSc_ub⟩ := orliczPsi2_normalizedGap_le hn
  obtain ⟨hSconst_ne, _, hSconst_eq⟩ := hconst (μ - 1 / 4)
  let X : LabeledGraph n → ℝ := fun G ↦ Y G - μ
  let C : LabeledGraph n → ℝ := fun _ ↦ μ - 1 / 4
  have hX_meas : AEStronglyMeasurable X (randomGraphMeasure n) :=
    (Integrable.of_finite : Integrable X (randomGraphMeasure n)).aestronglyMeasurable
  have hC_meas : AEStronglyMeasurable C (randomGraphMeasure n) :=
    aestronglyMeasurable_const
  have hSX_eq :
      {s : ℝ | 0 < s ∧ Integrable (fun G ↦ Real.exp ((X G) ^ 2 / s ^ 2)) (randomGraphMeasure n) ∧
        (∫ G, Real.exp ((X G) ^ 2 / s ^ 2) ∂randomGraphMeasure n) ≤ 2} = S_center := by
    ext s
    simp only [Set.mem_setOf_eq, S_center, X, Integrable.of_finite, true_and]
  have hSC_eq :
      {s : ℝ | 0 < s ∧ Integrable (fun G ↦ Real.exp ((C G) ^ 2 / s ^ 2)) (randomGraphMeasure n) ∧
        (∫ G, Real.exp ((C G) ^ 2 / s ^ 2) ∂randomGraphMeasure n) ≤ 2} =
      {s : ℝ | 0 < s ∧
        (∫ _ : LabeledGraph n, Real.exp ((μ - 1 / 4) ^ 2 / s ^ 2) ∂randomGraphMeasure n) ≤ 2} := by
    ext s
    simp only [Set.mem_setOf_eq, C, Integrable.of_finite, true_and]
  have hSXY_eq :
      {s : ℝ | 0 < s ∧
        Integrable (fun G ↦ Real.exp ((X G + C G) ^ 2 / s ^ 2)) (randomGraphMeasure n) ∧
        (∫ G, Real.exp ((X G + C G) ^ 2 / s ^ 2) ∂randomGraphMeasure n) ≤ 2} = S_quarter := by
    ext s
    have hsum : ∀ G : LabeledGraph n, X G + C G = Y G - 1 / 4 := fun G ↦ by dsimp [X, C]; ring
    simp only [Set.mem_setOf_eq, S_quarter, hsum, Integrable.of_finite, true_and]
  have htri := hsubadd hX_meas hC_meas (by rwa [hSX_eq]) (by rwa [hSC_eq])
  rw [hSX_eq, hSC_eq, hSXY_eq, hSconst_eq] at htri
  exact ⟨htri.1, htri.2.1, htri.2.2, by linarith [htri.2.2, hSc_ub]⟩

private theorem rpow_le_one_add_mul_sub_one {t p : ℝ} (ht : 0 < t)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    t ^ p ≤ 1 + p * (t - 1) := by
  let g : ℝ → ℝ := fun x ↦ 1 + p * (x - 1) - x ^ p
  have hdg : ∀ x > 0, HasDerivAt g (p * (1 - x ^ (p - 1))) x := by
    intro x hx
    have h1 : HasDerivAt (fun u : ℝ ↦ 1 + p * (u - 1)) p x := by
      simpa using (((hasDerivAt_id x).sub_const 1).const_mul p).const_add 1
    have h2 : HasDerivAt (fun u : ℝ ↦ u ^ p) (p * x ^ (p - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl hx.ne')
    exact (h1.sub h2).congr_deriv (by ring)
  have hg1 : g 1 = 0 := by dsimp [g]; simp
  rcases le_total 1 t with h1t | ht1
  · have hm : MonotoneOn g (Set.Icc 1 t) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 1 t)
      · exact fun x hx ↦ (hdg x (lt_of_lt_of_le zero_lt_one hx.1)).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        exact (hdg x (lt_trans zero_lt_one hx.1)).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hx_pos : 0 < x := lt_trans zero_lt_one hx.1
        rw [(hdg x hx_pos).deriv]
        have hrp_le1 : x ^ (p - 1) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos hx.1.le (by linarith [hp.2])
        exact mul_nonneg hp.1.le (by linarith)
    have h0 : g 1 ≤ g t := hm ⟨le_rfl, h1t⟩ ⟨h1t, le_rfl⟩ h1t
    rw [hg1] at h0; dsimp [g] at h0; linarith
  · have hm : MonotoneOn (-g) (Set.Icc t 1) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc t 1)
      · exact fun x hx ↦ (hdg x (lt_of_lt_of_le ht hx.1)).neg.continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        exact (hdg x (lt_trans ht hx.1)).neg.differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hx_pos : 0 < x := lt_trans ht hx.1
        rw [((hdg x hx_pos).neg).deriv]
        have hrp_ge1 : 1 ≤ x ^ (p - 1) :=
          Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx_pos hx.2.le (by linarith [hp.2])
        have hneg : p * (1 - x ^ (p - 1)) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hp.1.le (by linarith)
        linarith
    have h0 : (-g) t ≤ (-g) 1 := hm ⟨le_rfl, ht1⟩ ⟨ht1, le_rfl⟩ ht1
    simp only [Pi.neg_apply] at h0
    rw [hg1] at h0; dsimp [g] at h0; linarith

/-- **Main Theorem `(iv)` & Section 9 general sub-Gaussian square-exponential moment convergence:**
if a sequence `Z_n` on probability spaces `(Ω_n, ℙ_n)` satisfies `‖Z_n‖_{ψ₂} → 0` (with
`S_n.Nonempty` eventually), then for every `M ≥ 0`, `exp(M Z_n²)` is eventually integrable and
`lim_{n → ∞} E[exp(M Z_n²)] = 1`. -/
theorem tendsto_sqExpMoment_one_of_orliczPsi2_tendsto_zero
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (ℙ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (ℙ n)]
    (Z : ∀ n, Ω n → ℝ) (hZ : ∀ n, AEStronglyMeasurable (Z n) (ℙ n))
    (hNe : ∀ᶠ n : ℕ in atTop,
      ({s : ℝ | 0 < s ∧
        Integrable (fun ω ↦ Real.exp ((Z n ω) ^ 2 / s ^ 2)) (ℙ n) ∧
        (∫ ω, Real.exp ((Z n ω) ^ 2 / s ^ 2) ∂ℙ n) ≤ 2}).Nonempty)
    (hPsi2 : Tendsto (fun n : ℕ ↦
      sInf {s : ℝ | 0 < s ∧
        Integrable (fun ω ↦ Real.exp ((Z n ω) ^ 2 / s ^ 2)) (ℙ n) ∧
        (∫ ω, Real.exp ((Z n ω) ^ 2 / s ^ 2) ∂ℙ n) ≤ 2}) atTop (nhds 0))
    {M : ℝ} (hM : 0 ≤ M) :
    (∀ᶠ n : ℕ in atTop, Integrable (fun ω ↦ Real.exp (M * (Z n ω) ^ 2)) (ℙ n)) ∧
      Tendsto (fun n : ℕ ↦ ∫ ω, Real.exp (M * (Z n ω) ^ 2) ∂ℙ n) atTop (nhds 1) := by
  rcases eq_or_lt_of_le hM with rfl | hM_pos
  · refine ⟨Filter.Eventually.of_forall fun n ↦ by simp, ?_⟩
    have hconst : (fun n : ℕ ↦ ∫ ω : Ω n, Real.exp (0 * (Z n ω) ^ 2) ∂ℙ n) = fun _ ↦ 1 := by
      funext n
      simp [integral_const, probReal_univ]
    rw [hconst]
    exact tendsto_const_nhds
  · set S : ℕ → Set ℝ := fun n ↦ {s : ℝ | 0 < s ∧
      Integrable (fun ω ↦ Real.exp ((Z n ω) ^ 2 / s ^ 2)) (ℙ n) ∧
      (∫ ω, Real.exp ((Z n ω) ^ 2 / s ^ 2) ∂ℙ n) ≤ 2}
    have hs_small : ∀ δ : ℝ, 0 < δ → δ < 1 →
        ∀ᶠ n : ℕ in atTop,
          Integrable (fun ω ↦ Real.exp (M * (Z n ω) ^ 2)) (ℙ n) ∧
          1 ≤ ∫ ω, Real.exp (M * (Z n ω) ^ 2) ∂ℙ n ∧
          (∫ ω, Real.exp (M * (Z n ω) ^ 2) ∂ℙ n) ≤ (2 : ℝ) ^ δ := by
      intro δ hδ_pos hδ_lt1
      set s₀ : ℝ := Real.sqrt (δ / M)
      have hs₀_pos : 0 < s₀ := Real.sqrt_pos.mpr (div_pos hδ_pos hM_pos)
      have hs₀_sq : M * s₀ ^ 2 = δ := by
        dsimp [s₀]; rw [Real.sq_sqrt (div_nonneg hδ_pos.le hM_pos.le), mul_div_cancel₀ _ hM_pos.ne']
      filter_upwards [hNe, hPsi2.eventually (gt_mem_nhds hs₀_pos)] with n hSn_ne hinf_lt
      obtain ⟨s, hs_mem, hs_lt⟩ := exists_lt_of_csInf_lt hSn_ne hinf_lt
      obtain ⟨hs_pos, hInt_s, hle2⟩ := hs_mem
      set p : ℝ := M * s ^ 2
      have hp_pos : 0 < p := mul_pos hM_pos (sq_pos_of_pos hs_pos)
      have hp_lt_δ : p < δ := by
        dsimp [p]
        rw [← hs₀_sq]
        exact mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hs_lt hs_pos.le (by norm_num : 2 ≠ 0)) hM_pos
      have hp_lt1 : p < 1 := hp_lt_δ.trans hδ_lt1
      let u : Ω n → ℝ := fun ω ↦ Real.exp ((Z n ω) ^ 2 / s ^ 2)
      have hu_ge1 : ∀ ω, 1 ≤ u ω := fun ω ↦ Real.one_le_exp (div_nonneg (sq_nonneg _) (sq_nonneg _))
      have hrew_M : ∀ ω, Real.exp (M * (Z n ω) ^ 2) = (u ω) ^ p := by
        intro ω
        dsimp [u, p]
        rw [← Real.exp_mul]
        congr 1
        field_simp [hs_pos.ne']
      have hcont_M : Continuous (fun t : ℝ ↦ Real.exp (M * t ^ 2)) := by fun_prop
      have haesm_M : AEStronglyMeasurable (fun ω ↦ Real.exp (M * (Z n ω) ^ 2)) (ℙ n) :=
        hcont_M.comp_aestronglyMeasurable (hZ n)
      have hInt_M : Integrable (fun ω ↦ Real.exp (M * (Z n ω) ^ 2)) (ℙ n) := by
        refine hInt_s.mono' haesm_M (Filter.Eventually.of_forall fun ω ↦ ?_)
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hrew_M ω]
        calc (u ω) ^ p ≤ (u ω) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (hu_ge1 ω) hp_lt1.le
          _ = u ω := Real.rpow_one _
      have hlo1 : 1 ≤ ∫ ω, Real.exp (M * (Z n ω) ^ 2) ∂ℙ n := by
        have hc1 : (∫ _ : Ω n, (1 : ℝ) ∂ℙ n) = 1 := by simp [integral_const, probReal_univ]
        rw [← hc1]
        exact integral_mono (integrable_const 1) hInt_M fun ω ↦
          Real.one_le_exp (mul_nonneg hM_pos.le (sq_nonneg _))
      set μ : ℝ := ∫ ω, u ω ∂ℙ n
      have hμ_ge1 : 1 ≤ μ := by
        have hc1 : (∫ _ : Ω n, (1 : ℝ) ∂ℙ n) = 1 := by simp [integral_const, probReal_univ]
        rw [← hc1]
        exact integral_mono (integrable_const 1) hInt_s hu_ge1
      have hμ_pos : 0 < μ := lt_of_lt_of_le zero_lt_one hμ_ge1
      have hpt_jensen : ∀ ω : Ω n,
          Real.exp (M * (Z n ω) ^ 2) ≤ μ ^ p * ((1 - p) + (p / μ) * u ω) := by
        intro ω
        rw [hrew_M ω]
        have hu_pos : 0 < u ω := Real.exp_pos _
        have htan := rpow_le_one_add_mul_sub_one (div_pos hu_pos hμ_pos) ⟨hp_pos, hp_lt1⟩
        have hm := mul_le_mul_of_nonneg_left htan (Real.rpow_pos_of_pos hμ_pos p).le
        have hlhs : μ ^ p * (u ω / μ) ^ p = (u ω) ^ p := by
          rw [Real.div_rpow hu_pos.le hμ_pos.le, mul_div_cancel₀ _ (Real.rpow_pos_of_pos hμ_pos p).ne']
        have hrhs : μ ^ p * (1 + p * (u ω / μ - 1)) = μ ^ p * ((1 - p) + (p / μ) * u ω) := by
          field_simp [hμ_pos.ne']; ring
        rwa [hlhs, hrhs] at hm
      have hInt_rhs : Integrable (fun ω ↦ μ ^ p * ((1 - p) + (p / μ) * u ω)) (ℙ n) :=
        ((integrable_const (1 - p)).add (hInt_s.const_mul (p / μ))).const_mul (μ ^ p)
      have hint_jensen : (∫ ω, Real.exp (M * (Z n ω) ^ 2) ∂ℙ n) ≤ μ ^ p := by
        calc (∫ ω, Real.exp (M * (Z n ω) ^ 2) ∂ℙ n)
            ≤ ∫ ω, μ ^ p * ((1 - p) + (p / μ) * u ω) ∂ℙ n :=
              integral_mono hInt_M hInt_rhs hpt_jensen
          _ = μ ^ p * ((1 - p) + (p / μ) * μ) := by
              rw [integral_const_mul, integral_add (integrable_const _) (hInt_s.const_mul _),
                integral_const_mul]
              have hc_int : (∫ _ : Ω n, (1 - p) ∂ℙ n) = 1 - p := by
                simp [integral_const, probReal_univ]
              rw [hc_int]
          _ = μ ^ p := by field_simp [hμ_pos.ne']; ring
      have hμ_le_2δ : μ ^ p ≤ (2 : ℝ) ^ δ := by
        calc μ ^ p ≤ (2 : ℝ) ^ p := Real.rpow_le_rpow hμ_pos.le hle2 hp_pos.le
          _ ≤ (2 : ℝ) ^ δ := Real.rpow_le_rpow_of_exponent_le one_le_two hp_lt_δ.le
      exact ⟨hInt_M, hlo1, hint_jensen.trans hμ_le_2δ⟩
    refine ⟨(hs_small (1 / 2) (by norm_num) (by norm_num)).mono fun _ h ↦ h.1, ?_⟩
    rw [Metric.tendsto_nhds]
    intro eps heps
    have hcont2 : Continuous (fun x : ℝ ↦ (2 : ℝ) ^ x) := by
      have heq : (fun x : ℝ ↦ (2 : ℝ) ^ x) = fun x : ℝ ↦ Real.exp (Real.log 2 * x) := by
        funext x
        rw [Real.rpow_def_of_pos two_pos]
      rw [heq]
      fun_prop
    have hlim2 : Tendsto (fun x : ℝ ↦ (2 : ℝ) ^ x) (nhds 0) (nhds 1) := by
      simpa using hcont2.tendsto 0
    obtain ⟨r₀, hr₀_pos, hr₀_spec⟩ := Metric.tendsto_nhds_nhds.mp hlim2 eps heps
    set δ : ℝ := min (1 / 2) (r₀ / 2)
    have hδ_pos : 0 < δ := lt_min (by norm_num) (half_pos hr₀_pos)
    have hδ_lt1 : δ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    have h2δ_dist : |(2 : ℝ) ^ δ - 1| < eps := by
      have hd : dist δ 0 < r₀ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hδ_pos]
        exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hr₀_pos)
      simpa [Real.dist_eq] using hr₀_spec hd
    have h2δ_ge1 : 1 ≤ (2 : ℝ) ^ δ := Real.one_le_rpow one_le_two hδ_pos.le
    rw [abs_of_nonneg (by linarith)] at h2δ_dist
    filter_upwards [hs_small δ hδ_pos hδ_lt1] with n ⟨_, hlo, hhi⟩
    rw [Real.dist_eq, abs_of_nonneg (by linarith)]
    linarith

/-!
## 2. Non-asymptotic coupling-uniform tail-union & almost-sure `√(2 n log n)` fluctuations
-/

private theorem rpow_neg_one_add_le_inv_mul_diff {x η : ℝ} (hx : 1 ≤ x) (hη : 0 < η) :
    (x + 1) ^ (-(1 + η)) ≤ (1 / η) * (x ^ (-η) - (x + 1) ^ (-η)) := by
  let f : ℝ → ℝ := fun t ↦ -(1 / η) * t ^ (-η)
  have hdf : ∀ t > 0, HasDerivAt f (t ^ (-(1 + η))) t := by
    intro t ht
    have h1 : HasDerivAt (fun u : ℝ ↦ u ^ (-η)) ((-η) * t ^ (-η - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl ht.ne')
    refine (h1.const_mul (-(1 / η))).congr_deriv ?_
    have hexp : -η - 1 = -(1 + η) := by ring
    rw [hexp]
    field_simp [hη.ne']
  have hmvt := Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc x (x + 1))
    (fun t ht ↦ (hdf t (lt_of_lt_of_le zero_lt_one (hx.trans ht.1))).continuousAt.continuousWithinAt)
    (by
      intro t ht
      rw [interior_Icc] at ht
      exact (hdf t (lt_trans zero_lt_one (hx.trans_lt ht.1))).differentiableAt.differentiableWithinAt)
    (by
      intro t ht
      rw [interior_Icc] at ht
      have ht_pos : 0 < t := lt_trans zero_lt_one (hx.trans_lt ht.1)
      rw [(hdf t ht_pos).deriv]
      exact Real.rpow_le_rpow_of_nonpos ht_pos ht.2.le (by linarith))
    x ⟨le_rfl, by linarith⟩ (x + 1) ⟨by linarith, le_rfl⟩ (by linarith)
  have hdiff_f : f (x + 1) - f x = (1 / η) * (x ^ (-η) - (x + 1) ^ (-η)) := by
    dsimp [f]; ring
  have hsub1 : (x + 1) - x = 1 := by ring
  rw [hsub1, mul_one, hdiff_f] at hmvt
  exact hmvt

/-- **Main Theorem `(i)` & Corollary 8.1 non-asymptotic coupling-uniform tail-union bound:**
for every `n ≥ 2`, `η > 0`, and every joint coupling `(Ω, ℙ, G)` with marginals
`G_m ∼ G(m, 1/2)` (`m ≥ 2`),
`ℙ(∃ m ≥ n : |Δ(G_m) - E[Δ(G_m)]| ≥ √(2(1 + η)(m - 1) log m)) ≤ 2 (1/η + 1/n) n^(-η)`. -/
theorem coupling_tailUnion_chromaticSubCochromatic_sqrt_log_le
    {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (G : ∀ m : ℕ, Ω → LabeledGraph m)
    (hMarg : ∀ m : ℕ, 2 ≤ m → Measure.map (G m) ℙ = randomGraphMeasure m)
    {n : ℕ} (hn : 2 ≤ n) {η : ℝ} (hη : 0 < η) :
    let D : ∀ m : ℕ, LabeledGraph m → ℝ := fun _ H ↦
      (chromaticNumberNat H : ℝ) - (cochromaticNumber H : ℝ)
    let meanD : ℕ → ℝ := fun m ↦ ∫ H : LabeledGraph m, D m H ∂randomGraphMeasure m
    ℙ.real {ω : Ω | ∃ m ≥ n,
        Real.sqrt (2 * (1 + η) * ((m - 1 : ℕ) : ℝ) * Real.log (m : ℝ)) ≤
          |D m (G m ω) - meanD m|} ≤
      2 * (1 / η + 1 / (n : ℝ)) * (n : ℝ) ^ (-η) := by
  intro D meanD
  let Bad : ∀ m : ℕ, Set (LabeledGraph m) := fun m ↦
    {H | Real.sqrt (2 * (1 + η) * ((m - 1 : ℕ) : ℝ) * Real.log (m : ℝ)) ≤ |D m H - meanD m|}
  let E_pre : ℕ → Set Ω := fun k ↦ (G (n + k)) ⁻¹' (Bad (n + k))
  let maj : ℕ → ℝ := fun k ↦ 2 * ((n + k : ℕ) : ℝ) ^ (-(1 + η))
  have hterm_le : ∀ k : ℕ, ℙ.real (E_pre k) ≤ maj k := by
    intro k
    set m : ℕ := n + k
    have hm2 : 2 ≤ m := by omega
    have hm1_pos : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < m - 1 by omega)
    have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
    have hlog_nn : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
    have haem := aemeasurable_of_map_eq_randomGraphMeasure (hMarg m hm2)
    have hms : MeasurableSet (Bad m) := (Set.toFinite _).measurableSet
    have hpre_eq : ℙ.real (E_pre k) = (randomGraphMeasure m).real (Bad m) := by
      dsimp only [E_pre, m, Measure.real]
      rw [← Measure.map_apply_of_aemeasurable haem hms, hMarg m hm2]
    rw [hpre_eq]
    set t_m : ℝ := Real.sqrt (2 * (1 + η) * ((m - 1 : ℕ) : ℝ) * Real.log (m : ℝ))
    have hrad_nn : 0 ≤ 2 * (1 + η) * ((m - 1 : ℕ) : ℝ) * Real.log (m : ℝ) := by positivity
    have ht_nn : 0 ≤ t_m := Real.sqrt_nonneg _
    have htail := randomGraph_abs_chromaticSubCochromatic_sub_mean_ge_le hm2 ht_nn
    have hexp_eq : -t_m ^ 2 / (2 * ((m - 1 : ℕ) : ℝ)) = -(1 + η) * Real.log (m : ℝ) := by
      dsimp [t_m]
      rw [Real.sq_sqrt hrad_nn]
      field_simp [hm1_pos.ne']
    have hrpow_eq : Real.exp (-(1 + η) * Real.log (m : ℝ)) = (m : ℝ) ^ (-(1 + η)) := by
      rw [Real.rpow_def_of_pos hm_pos, mul_comm]
    dsimp [Bad, D, meanD, maj, m] at htail ⊢
    rwa [hexp_eq, hrpow_eq] at htail
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hpart_sum_le : ∀ K : ℕ,
      (∑ k ∈ Finset.range K, maj k) ≤ 2 * (1 / η + 1 / (n : ℝ)) * (n : ℝ) ^ (-η) := by
    intro K
    rcases K with _ | K
    · simp only [Finset.range_zero, Finset.sum_empty]
      positivity
    · rw [Finset.sum_range_succ']
      have hk0 : maj 0 = 2 * (1 / (n : ℝ)) * (n : ℝ) ^ (-η) := by
        dsimp [maj]
        have h1 : -(1 + η) = -1 + (-η) := by ring
        rw [h1, Real.rpow_add hn_pos, Real.rpow_neg_one]
        ring
      have hstep : ∀ j : ℕ,
          maj (j + 1) ≤ 2 * (1 / η) * (((n + j : ℕ) : ℝ) ^ (-η) - ((n + (j + 1) : ℕ) : ℝ) ^ (-η)) := by
        intro j
        dsimp [maj]
        have hcast : ((n + (j + 1) : ℕ) : ℝ) = ((n + j : ℕ) : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        have hx1 : (1 : ℝ) ≤ ((n + j : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n + j by omega)
        have hm := mul_le_mul_of_nonneg_left (rpow_neg_one_add_le_inv_mul_diff hx1 hη) zero_le_two
        linarith
      have htel :
          (∑ j ∈ Finset.range K,
              2 * (1 / η) * (((n + j : ℕ) : ℝ) ^ (-η) - ((n + (j + 1) : ℕ) : ℝ) ^ (-η))) =
            2 * (1 / η) * ((n : ℝ) ^ (-η) - ((n + K : ℕ) : ℝ) ^ (-η)) := by
        rw [← Finset.mul_sum]
        congr 1
        let g_t : ℕ → ℝ := fun j ↦ ((n + j : ℕ) : ℝ) ^ (-η)
        have htel_g := Finset.sum_range_sub' g_t K
        dsimp [g_t] at htel_g
        simpa only [Nat.add_zero] using htel_g
      have hsum_tail : (∑ j ∈ Finset.range K, maj (j + 1)) ≤ 2 * (1 / η) * (n : ℝ) ^ (-η) := by
        calc (∑ j ∈ Finset.range K, maj (j + 1))
            ≤ ∑ j ∈ Finset.range K,
                2 * (1 / η) * (((n + j : ℕ) : ℝ) ^ (-η) - ((n + (j + 1) : ℕ) : ℝ) ^ (-η)) :=
              Finset.sum_le_sum fun j _ ↦ hstep j
          _ = 2 * (1 / η) * ((n : ℝ) ^ (-η) - ((n + K : ℕ) : ℝ) ^ (-η)) := htel
          _ ≤ 2 * (1 / η) * (n : ℝ) ^ (-η) := by
              have hpos_end : 0 ≤ ((n + K : ℕ) : ℝ) ^ (-η) :=
                Real.rpow_nonneg (Nat.cast_nonneg _) _
              nlinarith [div_pos one_pos hη]
      rw [hk0]
      linarith
  have hmaj_nn : ∀ k : ℕ, 0 ≤ maj k := fun k ↦ by
    dsimp [maj]; exact mul_nonneg zero_le_two (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hsum_maj : Summable maj := summable_of_sum_range_le hmaj_nn hpart_sum_le
  have htsum_maj_le : (∑' k : ℕ, maj k) ≤ 2 * (1 / η + 1 / (n : ℝ)) * (n : ℝ) ^ (-η) :=
    hsum_maj.tsum_le_of_sum_range_le hpart_sum_le
  have hsum_pre : Summable (fun k : ℕ ↦ ℙ.real (E_pre k)) :=
    Summable.of_nonneg_of_le (fun _ ↦ measureReal_nonneg) hterm_le hsum_maj
  have hsub_u :
      {ω : Ω | ∃ m ≥ n,
        Real.sqrt (2 * (1 + η) * ((m - 1 : ℕ) : ℝ) * Real.log (m : ℝ)) ≤
          |D m (G m ω) - meanD m|} ⊆ ⋃ k : ℕ, E_pre k := by
    rintro ω ⟨m, hmn, hm_bad⟩
    rw [Set.mem_iUnion]
    exact ⟨m - n, by dsimp [E_pre, Bad]; rwa [Nat.add_sub_of_le hmn]⟩
  have hmeas_u : ℙ {ω : Ω | ∃ m ≥ n,
      Real.sqrt (2 * (1 + η) * ((m - 1 : ℕ) : ℝ) * Real.log (m : ℝ)) ≤
        |D m (G m ω) - meanD m|} ≤
      ENNReal.ofReal (∑' k : ℕ, ℙ.real (E_pre k)) := by
    calc ℙ _ ≤ ℙ (⋃ k : ℕ, E_pre k) := measure_mono hsub_u
      _ ≤ ∑' k : ℕ, ℙ (E_pre k) := measure_iUnion_le _
      _ ≤ ENNReal.ofReal (∑' k : ℕ, ℙ.real (E_pre k)) := by
          rw [ENNReal.tsum_eq_iSup_sum]
          refine iSup_le fun s ↦ ?_
          have heq : ∑ k ∈ s, ℙ (E_pre k) = ENNReal.ofReal (∑ k ∈ s, ℙ.real (E_pre k)) := by
            rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ measureReal_nonneg)]
            exact Finset.sum_congr rfl fun k _ ↦ (ENNReal.ofReal_toReal (measure_ne_top ℙ _)).symm
          rw [heq]
          exact ENNReal.ofReal_le_ofReal (hsum_pre.sum_le_tsum s (fun _ _ ↦ measureReal_nonneg))
  have hreal_u : ℙ.real {ω : Ω | ∃ m ≥ n,
      Real.sqrt (2 * (1 + η) * ((m - 1 : ℕ) : ℝ) * Real.log (m : ℝ)) ≤
        |D m (G m ω) - meanD m|} ≤ ∑' k : ℕ, ℙ.real (E_pre k) := by
    have hnn : 0 ≤ ∑' k : ℕ, ℙ.real (E_pre k) := tsum_nonneg fun _ ↦ measureReal_nonneg
    have htr := (ENNReal.toReal_le_toReal (measure_ne_top ℙ _) ENNReal.ofReal_ne_top).mpr hmeas_u
    rwa [ENNReal.toReal_ofReal hnn] at htr
  exact hreal_u.trans ((hsum_pre.tsum_le_tsum hterm_le hsum_maj).trans htsum_maj_le)

private theorem ae_eventually_notMem_of_tailUnion_tendsto_zero_v12
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

/-- **Main Theorem `(i)` & Corollary 8.1 arbitrary-coupling almost-sure `√(2 n log n)` fluctuation
envelope (`main.tex` lines 119, 1152):**
under every joint coupling `(Ω, ℙ, G)` with marginals `G_m ∼ G(m, 1/2)` (`m ≥ 2`):
1. for every `ε > 0`, almost surely eventually
   `|Δ(G_n) - E[Δ(G_n)]| ≤ (1 + ε) √(2 n log n)` and
   `|Y_n - E[Y_n]| ≤ (1 + ε) (log₂ n)³ √(2 log n / n)`;
2. almost surely in `ℝ≥0∞`, `limsup |Δ(G_n) - E[Δ(G_n)]| / √(2 n log n) ≤ 1` and
   `limsup (√n / ((log₂ n)³ √(2 log n))) |Y_n - E[Y_n]| ≤ 1`. -/
theorem ae_limsup_chromaticSubCochromatic_and_normalizedGap_le_one
    {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (G : ∀ m : ℕ, Ω → LabeledGraph m)
    (hMarg : ∀ m : ℕ, 2 ≤ m → Measure.map (G m) ℙ = randomGraphMeasure m) :
    let D : ∀ m : ℕ, LabeledGraph m → ℝ := fun _ H ↦
      (chromaticNumberNat H : ℝ) - (cochromaticNumber H : ℝ)
    let meanD : ℕ → ℝ := fun m ↦ ∫ H : LabeledGraph m, D m H ∂randomGraphMeasure m
    let Y : ∀ m : ℕ, LabeledGraph m → ℝ := fun m H ↦
      (Real.logb 2 (m : ℝ)) ^ 3 / (m : ℝ) * D m H
    let meanY : ℕ → ℝ := fun m ↦ ∫ H : LabeledGraph m, Y m H ∂randomGraphMeasure m
    (∀ {eps : ℝ}, 0 < eps →
      ∀ᵐ ω ∂ℙ, ∀ᶠ n : ℕ in atTop,
        |D n (G n ω) - meanD n| ≤ (1 + eps) * Real.sqrt (2 * (n : ℝ) * Real.log (n : ℝ)) ∧
        |Y n (G n ω) - meanY n| ≤
          (1 + eps) * (Real.logb 2 (n : ℝ)) ^ 3 * Real.sqrt (2 * Real.log (n : ℝ) / (n : ℝ))) ∧
    (∀ᵐ ω ∂ℙ,
      Filter.limsup (fun n : ℕ ↦
        ENNReal.ofReal (|D n (G n ω) - meanD n| / Real.sqrt (2 * (n : ℝ) * Real.log (n : ℝ))))
          atTop ≤ 1 ∧
      Filter.limsup (fun n : ℕ ↦
        ENNReal.ofReal (Real.sqrt (n : ℝ) /
          ((Real.logb 2 (n : ℝ)) ^ 3 * Real.sqrt (2 * Real.log (n : ℝ))) *
          |Y n (G n ω) - meanY n|)) atTop ≤ 1) := by
  intro D meanD Y meanY
  have hae_eps : ∀ {eps : ℝ}, 0 < eps →
      ∀ᵐ ω ∂ℙ, ∀ᶠ n : ℕ in atTop,
        |D n (G n ω) - meanD n| ≤ (1 + eps) * Real.sqrt (2 * (n : ℝ) * Real.log (n : ℝ)) ∧
        |Y n (G n ω) - meanY n| ≤
          (1 + eps) * (Real.logb 2 (n : ℝ)) ^ 3 * Real.sqrt (2 * Real.log (n : ℝ) / (n : ℝ)) := by
    intro eps heps
    set η : ℝ := (1 + eps) ^ 2 - 1
    have hη_pos : 0 < η := by dsimp [η]; nlinarith
    have h1pη : 1 + η = (1 + eps) ^ 2 := by dsimp [η]; ring
    let E_bad : ℕ → Set Ω := fun m ↦
      {ω : Ω | (1 + eps) * Real.sqrt (2 * (m : ℝ) * Real.log (m : ℝ)) < |D m (G m ω) - meanD m|}
    let U_maj : ℕ → ℝ := fun n ↦ 2 * (1 / η + 1) * (n : ℝ) ^ (-η)
    have htail_le : ∀ᶠ n : ℕ in atTop, ℙ.real {ω : Ω | ∃ m ≥ n, ω ∈ E_bad m} ≤ U_maj n := by
      filter_upwards [eventually_ge_atTop 2] with n hn2
      have hsub : {ω : Ω | ∃ m ≥ n, ω ∈ E_bad m} ⊆
          {ω : Ω | ∃ m ≥ n,
            Real.sqrt (2 * (1 + η) * ((m - 1 : ℕ) : ℝ) * Real.log (m : ℝ)) ≤
              |D m (G m ω) - meanD m|} := by
        rintro ω ⟨m, hmn, hgt⟩
        refine ⟨m, hmn, ?_⟩
        have hm2 : 2 ≤ m := le_trans hn2 hmn
        have hm1_le : ((m - 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.sub_le m 1
        have hlog_nn : 0 ≤ Real.log (m : ℝ) :=
          Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
        have hsq_le :
            Real.sqrt (2 * (1 + η) * ((m - 1 : ℕ) : ℝ) * Real.log (m : ℝ)) ≤
              (1 + eps) * Real.sqrt (2 * (m : ℝ) * Real.log (m : ℝ)) := by
          rw [h1pη]
          have h1 : 2 * (1 + eps) ^ 2 * ((m - 1 : ℕ) : ℝ) * Real.log (m : ℝ) ≤
              (1 + eps) ^ 2 * (2 * (m : ℝ) * Real.log (m : ℝ)) := by
            have hd := mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hm1_le (by positivity : (0 : ℝ) ≤ 2 * (1 + eps) ^ 2))
              hlog_nn
            linarith
          calc Real.sqrt (2 * (1 + eps) ^ 2 * ((m - 1 : ℕ) : ℝ) * Real.log (m : ℝ))
              ≤ Real.sqrt ((1 + eps) ^ 2 * (2 * (m : ℝ) * Real.log (m : ℝ))) := Real.sqrt_le_sqrt h1
            _ = (1 + eps) * Real.sqrt (2 * (m : ℝ) * Real.log (m : ℝ)) := by
                rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]
        exact hsq_le.trans hgt.le
      have hc := coupling_tailUnion_chromaticSubCochromatic_sqrt_log_le ℙ G hMarg hn2 hη_pos
      have hn1_inv : 1 / (n : ℝ) ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast (show 1 ≤ n by omega))
        (Nat.cast_nonneg n)
      have hmaj_le : 2 * (1 / η + 1 / (n : ℝ)) * (n : ℝ) ^ (-η) ≤ U_maj n := by
        dsimp [U_maj]
        exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      exact (measureReal_mono hsub).trans (hc.trans hmaj_le)
    have hU_zero : Tendsto U_maj atTop (nhds 0) := by
      have hrp := (tendsto_rpow_neg_atTop hη_pos).comp (tendsto_natCast_atTop_atTop (R := ℝ))
      have hm := hrp.const_mul (2 * (1 / η + 1))
      simpa only [U_maj, Function.comp_def, mul_zero] using hm
    have hbc : ∀ᵐ ω ∂ℙ, ∀ᶠ n : ℕ in atTop, ω ∉ E_bad n :=
      ae_eventually_notMem_of_tailUnion_tendsto_zero_v12 ℙ htail_le hU_zero
    filter_upwards [hbc] with ω hω
    filter_upwards [eventually_ge_atTop 2, hω] with n hn2 hnot_bad
    have hD_le : |D n (G n ω) - meanD n| ≤
        (1 + eps) * Real.sqrt (2 * (n : ℝ) * Real.log (n : ℝ)) := not_lt.mp hnot_bad
    refine ⟨hD_le, ?_⟩
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hlb_nn : 0 ≤ (Real.logb 2 (n : ℝ)) ^ 3 :=
      pow_nonneg (Real.logb_nonneg one_lt_two (by exact_mod_cast (show 1 ≤ n by omega))) 3
    have hmeanY_eq : meanY n = ((Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ)) * meanD n :=
      integral_const_mul _ (D n)
    have hY_diff : |Y n (G n ω) - meanY n| =
        ((Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ)) * |D n (G n ω) - meanD n| := by
      have hid : Y n (G n ω) - meanY n =
          ((Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ)) * (D n (G n ω) - meanD n) := by
        rw [hmeanY_eq]; dsimp [Y]; ring
      rw [hid, abs_mul, abs_of_nonneg (div_nonneg hlb_nn hn_pos.le)]
    rw [hY_diff]
    calc ((Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ)) * |D n (G n ω) - meanD n|
        ≤ ((Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ)) *
            ((1 + eps) * Real.sqrt (2 * (n : ℝ) * Real.log (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hD_le (div_nonneg hlb_nn hn_pos.le)
      _ = (1 + eps) * (Real.logb 2 (n : ℝ)) ^ 3 * Real.sqrt (2 * Real.log (n : ℝ) / (n : ℝ)) := by
          have hsq_div : Real.sqrt (2 * (n : ℝ) * Real.log (n : ℝ)) / (n : ℝ) =
              Real.sqrt (2 * Real.log (n : ℝ) / (n : ℝ)) := by
            have hlog_nn : 0 ≤ Real.log (n : ℝ) :=
              Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
            rw [div_eq_iff hn_pos.ne',
              show 2 * (n : ℝ) * Real.log (n : ℝ) = (n : ℝ) * (2 * Real.log (n : ℝ)) by ring,
              Real.sqrt_mul hn_pos.le, Real.sqrt_div (by positivity),
              div_mul_eq_mul_div, eq_div_iff (Real.sqrt_pos.mpr hn_pos).ne']
            calc Real.sqrt (n : ℝ) * Real.sqrt (2 * Real.log (n : ℝ)) * Real.sqrt (n : ℝ)
                = Real.sqrt (2 * Real.log (n : ℝ)) * (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by
                    ring
              _ = Real.sqrt (2 * Real.log (n : ℝ)) * (n : ℝ) := by
                    rw [Real.mul_self_sqrt hn_pos.le]
          calc ((Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ)) *
                ((1 + eps) * Real.sqrt (2 * (n : ℝ) * Real.log (n : ℝ)))
              = (1 + eps) * (Real.logb 2 (n : ℝ)) ^ 3 *
                  (Real.sqrt (2 * (n : ℝ) * Real.log (n : ℝ)) / (n : ℝ)) := by ring
            _ = _ := by rw [hsq_div]
  refine ⟨fun heps ↦ hae_eps heps, ?_⟩
  have hall : ∀ᵐ ω ∂ℙ, ∀ r : ℕ, ∀ᶠ n : ℕ in atTop,
      |D n (G n ω) - meanD n| ≤
          (1 + 1 / ((r : ℝ) + 1)) * Real.sqrt (2 * (n : ℝ) * Real.log (n : ℝ)) ∧
        |Y n (G n ω) - meanY n| ≤
          (1 + 1 / ((r : ℝ) + 1)) * (Real.logb 2 (n : ℝ)) ^ 3 *
            Real.sqrt (2 * Real.log (n : ℝ) / (n : ℝ)) :=
    ae_all_iff.mpr fun r ↦ hae_eps (by positivity : 0 < 1 / ((r : ℝ) + 1))
  filter_upwards [hall] with ω hω
  let fD : ℕ → ENNReal := fun n ↦
    ENNReal.ofReal (|D n (G n ω) - meanD n| / Real.sqrt (2 * (n : ℝ) * Real.log (n : ℝ)))
  let fY : ℕ → ENNReal := fun n ↦
    ENNReal.ofReal (Real.sqrt (n : ℝ) /
      ((Real.logb 2 (n : ℝ)) ^ 3 * Real.sqrt (2 * Real.log (n : ℝ))) * |Y n (G n ω) - meanY n|)
  have hlim_r : ∀ r : ℕ,
      Filter.limsup fD atTop ≤ ENNReal.ofReal (1 + 1 / ((r : ℝ) + 1)) ∧
        Filter.limsup fY atTop ≤ ENNReal.ofReal (1 + 1 / ((r : ℝ) + 1)) := by
    intro r
    have hev : ∀ᶠ n : ℕ in atTop,
        fD n ≤ ENNReal.ofReal (1 + 1 / ((r : ℝ) + 1)) ∧
          fY n ≤ ENNReal.ofReal (1 + 1 / ((r : ℝ) + 1)) := by
      filter_upwards [eventually_ge_atTop 2, hω r] with n hn2 ⟨hD_r, hY_r⟩
      have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
      have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      have hlb_pos : 0 < Real.logb 2 (n : ℝ) :=
        Real.logb_pos one_lt_two (by exact_mod_cast (show 1 < n by omega))
      have hsq_pos : 0 < Real.sqrt (2 * (n : ℝ) * Real.log (n : ℝ)) :=
        Real.sqrt_pos.mpr (by positivity)
      have hD_div : |D n (G n ω) - meanD n| / Real.sqrt (2 * (n : ℝ) * Real.log (n : ℝ)) ≤
          1 + 1 / ((r : ℝ) + 1) := (div_le_iff₀ hsq_pos).mpr hD_r
      have hY_mul :
          Real.sqrt (n : ℝ) / ((Real.logb 2 (n : ℝ)) ^ 3 * Real.sqrt (2 * Real.log (n : ℝ))) *
              |Y n (G n ω) - meanY n| ≤ 1 + 1 / ((r : ℝ) + 1) := by
        have hfac_pos : 0 < Real.sqrt (n : ℝ) /
            ((Real.logb 2 (n : ℝ)) ^ 3 * Real.sqrt (2 * Real.log (n : ℝ))) := by positivity
        have hm := mul_le_mul_of_nonneg_left hY_r hfac_pos.le
        have hsq_split : Real.sqrt (2 * Real.log (n : ℝ) / (n : ℝ)) =
            Real.sqrt (2 * Real.log (n : ℝ)) / Real.sqrt (n : ℝ) :=
          Real.sqrt_div (by positivity) (n : ℝ)
        rw [hsq_split] at hm
        have hcanc :
            Real.sqrt (n : ℝ) / ((Real.logb 2 (n : ℝ)) ^ 3 * Real.sqrt (2 * Real.log (n : ℝ))) *
              ((1 + 1 / ((r : ℝ) + 1)) * (Real.logb 2 (n : ℝ)) ^ 3 *
                (Real.sqrt (2 * Real.log (n : ℝ)) / Real.sqrt (n : ℝ))) =
            1 + 1 / ((r : ℝ) + 1) := by
          field_simp [(Real.sqrt_pos.mpr hn_pos).ne', hlb_pos.ne',
            (Real.sqrt_pos.mpr (mul_pos two_pos hlog_pos)).ne']
        rwa [hcanc] at hm
      exact ⟨ENNReal.ofReal_le_ofReal hD_div, ENNReal.ofReal_le_ofReal hY_mul⟩
    exact ⟨Filter.limsup_le_of_le (h := hev.mono fun _ h ↦ h.1),
      Filter.limsup_le_of_le (h := hev.mono fun _ h ↦ h.2)⟩
  have htend_1 : Tendsto (fun r : ℕ ↦ ENNReal.ofReal (1 + 1 / ((r : ℝ) + 1))) atTop (nhds 1) := by
    have h1 : Tendsto (fun r : ℕ ↦ (1 : ℝ) + 1 / ((r : ℝ) + 1)) atTop (nhds 1) := by
      have hd : Tendsto (fun r : ℕ ↦ 1 / ((r : ℝ) + 1)) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop
          ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds)
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hd
    simpa only [Function.comp_def, ENNReal.ofReal_one] using ENNReal.tendsto_ofReal h1
  exact ⟨le_of_tendsto_of_tendsto tendsto_const_nhds htend_1
      (Filter.Eventually.of_forall fun r ↦ (hlim_r r).1),
    le_of_tendsto_of_tendsto tendsto_const_nhds htend_1
      (Filter.Eventually.of_forall fun r ↦ (hlim_r r).2)⟩

/-!
## 3. Infinite-support Lemma 3.2(i),(iv) `O(1/α)` dual errors (`S_{≥ 0}`, `S_{≥ 1}`, `S_{≥ 2}`, and `S_{≥ 1}^{=ϑ}`)
-/

private def infiniteSupportSet (m : ℕ) : Set ℤ :=
  {j : ℤ | (m : ℤ) ≤ j}

private def infiniteFiniteScore (alpha i : ℕ) : ℝ :=
  Real.log (alpha.descFactorial i : ℝ) - (i : ℝ) * Real.log (alpha : ℝ) -
    Real.log 2 / 2 * (i : ℝ) ^ 2

private def infiniteFinitePartition (alpha m : ℕ) (l : ℝ) : ℝ :=
  ∑ i ∈ Finset.Ico m alpha, Real.exp (l * (i : ℝ) + infiniteFiniteScore alpha i)

private def infiniteFiniteEntropy (alpha m : ℕ) (T : ℝ) : ℝ :=
  ⨅ l : ℝ, (Real.log (infiniteFinitePartition alpha m l) - l * T)

private def cappedInfiniteFiniteEntropy (alpha : ℕ) (theta T : ℝ) : ℝ :=
  binEntropy theta - Real.log 2 / 2 * theta +
    (1 - theta) * infiniteFiniteEntropy alpha 2 ((T - theta) / (1 - theta))

private theorem s4_subset_infiniteSupportSet {m : ℕ} (hm : m ≤ 2) :
    S4 ⊆ infiniteSupportSet m := by
  intro j hj
  simp only [S4, Set.mem_insert_iff, Set.mem_singleton_iff] at hj
  simp only [infiniteSupportSet, Set.mem_setOf_eq]
  rcases hj with rfl | rfl | rfl | rfl <;> omega

private theorem infiniteSupportSet_subset_Splus (m : ℕ) :
    infiniteSupportSet m ⊆ Splus := by
  intro j hj
  simp only [infiniteSupportSet, Splus, Set.mem_setOf_eq] at hj ⊢
  omega

private theorem infiniteSupportSet_zero_eq_Sge0 :
    infiniteSupportSet 0 = Sge0 := by
  ext j
  simp only [infiniteSupportSet, Sge0, Set.mem_setOf_eq]
  omega

private theorem infiniteSupportSet_one_eq_Sge1 :
    infiniteSupportSet 1 = Sge1 := by
  ext j
  simp only [infiniteSupportSet, Sge1, Set.mem_setOf_eq]
  omega

private theorem infiniteSupportSet_two_eq_sge1_diff_one :
    infiniteSupportSet 2 = Sge1 \ {1} := by
  ext j
  simp only [infiniteSupportSet, Sge1, Set.mem_setOf_eq, Set.mem_sdiff, Set.mem_singleton_iff]
  omega

private theorem infiniteFinitePartition_pos {alpha m : ℕ} (hm : m < alpha) (l : ℝ) :
    0 < infiniteFinitePartition alpha m l := by
  unfold infiniteFinitePartition
  exact Finset.sum_pos (fun _ _ ↦ Real.exp_pos _) ⟨m, Finset.mem_Ico.mpr ⟨le_rfl, hm⟩⟩

private theorem infiniteFiniteScore_bounds_small {alpha i : ℕ} (hi5 : i ≤ 5) (halpha : 10 ≤ alpha) :
    -(38 : ℝ) ≤ infiniteFiniteScore alpha i ∧
      infiniteFiniteScore alpha i ≤ -Real.log 2 / 2 * (i : ℝ) ^ 2 := by
  have hi_lt : i < alpha := by omega
  have h2i : 2 * i ≤ alpha := by omega
  obtain ⟨hid, hle0, hge⟩ := finiteDeficitResidualScore_bounds hi_lt
  unfold infiniteFiniteScore
  rw [hid]
  refine ⟨?_, by linarith⟩
  have ha_ge1 : (1 : ℝ) ≤ (alpha : ℝ) := by exact_mod_cast (show 1 ≤ alpha by omega)
  have hi_le5 : (i : ℝ) ≤ 5 := by exact_mod_cast hi5
  have hsq25 : (i : ℝ) ^ 2 ≤ 25 := by nlinarith [Nat.cast_nonneg (α := ℝ) i]
  have hdiv25 : (i : ℝ) ^ 2 / (alpha : ℝ) ≤ 25 := by
    calc (i : ℝ) ^ 2 / (alpha : ℝ) ≤ (i : ℝ) ^ 2 / 1 :=
          div_le_div_of_nonneg_left (sq_nonneg _) zero_lt_one ha_ge1
      _ ≤ 25 := by linarith
  have hq_le1 : Real.log 2 ≤ 1 := le_trans Real.log_two_lt_d9.le (by norm_num)
  have hq_i : Real.log 2 / 2 * (i : ℝ) ^ 2 ≤ 25 / 2 := by
    nlinarith [sq_nonneg (i : ℝ), Real.log_pos one_lt_two]
  have h1 := hge h2i
  rw [neg_div] at h1
  linarith

private theorem bddBelow_and_tilt_trap_infiniteFiniteDual
    {alpha m : ℕ} (hm : m ≤ 2) (halpha : 10 ≤ alpha)
    {T : ℝ} (hT : T ∈ Set.Icc (17 / 8 : ℝ) (37 / 8)) :
    BddBelow (Set.range fun l : ℝ ↦ Real.log (infiniteFinitePartition alpha m l) - l * T) ∧
      ∀ {l U : ℝ},
        Real.log (infiniteFinitePartition alpha m l) - l * T ≤ U →
          |l| ≤ max 0 (8 * (U + 38)) ∧
          -(max 0 (8 * (U + 38))) * ((alpha : ℝ) + 2) - 38 ≤
            Real.log (infiniteFinitePartition alpha m l) - l * (alpha : ℝ) := by
  have hm_mem : m ∈ Finset.Ico m alpha := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
  have h5_mem : 5 ∈ Finset.Ico m alpha := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hsm : -(38 : ℝ) ≤ infiniteFiniteScore alpha m :=
    (infiniteFiniteScore_bounds_small (by omega) halpha).1
  have hs5 : -(38 : ℝ) ≤ infiniteFiniteScore alpha 5 :=
    (infiniteFiniteScore_bounds_small le_rfl halpha).1
  have hterm_m : ∀ l : ℝ, l * (m : ℝ) - 38 ≤ Real.log (infiniteFinitePartition alpha m l) := by
    intro l
    have hsub : Real.exp (l * (m : ℝ) + infiniteFiniteScore alpha m) ≤
        infiniteFinitePartition alpha m l :=
      Finset.single_le_sum (f := fun j : ℕ ↦ Real.exp (l * (j : ℝ) + infiniteFiniteScore alpha j))
        (fun _ _ ↦ (Real.exp_pos _).le) hm_mem
    have hlog := Real.log_le_log (Real.exp_pos _) hsub
    rw [Real.log_exp] at hlog
    linarith
  have hterm_5 : ∀ l : ℝ, l * 5 - 38 ≤ Real.log (infiniteFinitePartition alpha m l) := by
    intro l
    have hsub : Real.exp (l * (5 : ℕ) + infiniteFiniteScore alpha 5) ≤
        infiniteFinitePartition alpha m l :=
      Finset.single_le_sum (f := fun j : ℕ ↦ Real.exp (l * (j : ℝ) + infiniteFiniteScore alpha j))
        (fun _ _ ↦ (Real.exp_pos _).le) h5_mem
    have hlog := Real.log_le_log (Real.exp_pos _) hsub
    rw [Real.log_exp] at hlog
    push_cast at hlog
    linarith
  have hm_le2 : (m : ℝ) ≤ 2 := by exact_mod_cast hm
  have hgap_lo : (1 / 8 : ℝ) ≤ T - (m : ℝ) := by linarith [hT.1]
  have hgap_hi : (3 / 8 : ℝ) ≤ 5 - T := by linarith [hT.2]
  refine ⟨⟨-38, ?_⟩, ?_⟩
  · rintro y ⟨l, rfl⟩
    rcases le_total l 0 with hl0 | hl0
    · have ht := hterm_m l
      have hnn : 0 ≤ (-l) * (T - (m : ℝ)) := mul_nonneg (by linarith) (by linarith)
      linarith
    · have ht := hterm_5 l
      have hnn : 0 ≤ l * (5 - T) := mul_nonneg hl0 (by linarith)
      linarith
  · intro l U hl
    set Mt : ℝ := max 0 (8 * (U + 38))
    have hMt_nn : 0 ≤ Mt := le_max_left 0 _
    have hMt_ge : 8 * (U + 38) ≤ Mt := le_max_right 0 _
    have habs : |l| ≤ Mt := by
      rcases le_total l 0 with hl0 | hl0
      · rw [abs_of_nonpos hl0]
        have ht := hterm_m l
        have hm1 : (-l) * (1 / 8 : ℝ) ≤ (-l) * (T - (m : ℝ)) :=
          mul_le_mul_of_nonneg_left hgap_lo (by linarith)
        have hsum : (-l) * (T - (m : ℝ)) ≤ U + 38 := by linarith
        linarith
      · rw [abs_of_nonneg hl0]
        have ht := hterm_5 l
        have hm1 : l * (3 / 8 : ℝ) ≤ l * (5 - T) :=
          mul_le_mul_of_nonneg_left hgap_hi hl0
        have hsum : l * (5 - T) ≤ U + 38 := by linarith
        linarith
    refine ⟨habs, ?_⟩
    have ht := hterm_m l
    have hdiff_abs : |(m : ℝ) - (alpha : ℝ)| ≤ (alpha : ℝ) + 2 := by
      rw [abs_le]
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      exact ⟨by linarith, by linarith⟩
    have hprod_abs : |l * ((m : ℝ) - (alpha : ℝ))| ≤ Mt * ((alpha : ℝ) + 2) := by
      rw [abs_mul]
      exact mul_le_mul habs hdiff_abs (abs_nonneg _) hMt_nn
    have hlo_prod : -(Mt * ((alpha : ℝ) + 2)) ≤ l * ((m : ℝ) - (alpha : ℝ)) :=
      (abs_le.mp hprod_abs).1
    linarith

private theorem infiniteFinitePartition_le_partitionFn
    {alpha m : ℕ} (l : ℝ) :
    infiniteFinitePartition alpha m l ≤ partitionFn (infiniteSupportSet m) l := by
  have hscore_le : ∀ i ∈ Finset.Ico m alpha,
      Real.exp (l * (i : ℝ) + infiniteFiniteScore alpha i) ≤ gaussWeight l (i : ℤ) := by
    intro i hi
    obtain ⟨_, hi_lt⟩ := Finset.mem_Ico.mp hi
    obtain ⟨hid, hle0, _⟩ := finiteDeficitResidualScore_bounds hi_lt
    unfold infiniteFiniteScore gaussWeight
    rw [hid]
    apply Real.exp_le_exp.mpr
    push_cast
    linarith
  have hsum_le : infiniteFinitePartition alpha m l ≤
      ∑ i ∈ Finset.Ico m alpha, gaussWeight l (i : ℤ) :=
    Finset.sum_le_sum hscore_le
  refine hsum_le.trans ?_
  unfold partitionFn
  let emb : {i : ℕ // i ∈ Finset.Ico m alpha} ↪ infiniteSupportSet m :=
    ⟨fun x ↦ ⟨(x.1 : ℤ), by
        simp only [infiniteSupportSet, Set.mem_setOf_eq]
        exact_mod_cast (Finset.mem_Ico.mp x.2).1⟩,
      fun a b h ↦ Subtype.ext (Int.ofNat.inj (Subtype.mk.inj h))⟩
  have hsum_attach :
      (∑ i ∈ Finset.Ico m alpha, gaussWeight l (i : ℤ)) =
        ∑ j ∈ (Finset.Ico m alpha).attach.map emb, gaussWeight l j.1 := by
    rw [Finset.sum_map, ← Finset.sum_attach (Finset.Ico m alpha) (fun i ↦ gaussWeight l (i : ℤ))]
    rfl
  rw [hsum_attach]
  exact ((hasSum_partitionFn (infiniteSupportSet m) l).summable).sum_le_tsum _
    fun j _ ↦ (gaussWeight_pos l j.1).le

private theorem dualValue_infinite_bounds_on_padded
    {m : ℕ} (hm : m ≤ 2) {T : ℝ} (hT : T ∈ Set.Icc (17 / 8 : ℝ) (37 / 8)) :
    min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8)) ≤
        dualValue (infiniteSupportSet m) T ∧
      dualValue (infiniteSupportSet m) T ≤ Real.log (partitionFn Splus 0) := by
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
  have hm0_le : m0 ≤ dualValue S4 T := by
    have e1 := mul_le_mul_of_nonneg_left
      (min_le_left (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))) hwL_nn
    have e2 := mul_le_mul_of_nonneg_left
      (min_le_right (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))) hwR_nn
    have : m0 = (wL + wR) * m0 := by rw [hw_sum, one_mul]
    linarith
  have hmono := dualValue_mono subset_rfl (s4_subset_infiniteSupportSet hm) hmT
  have h0 := dualValue_le_at (s4_subset_infiniteSupportSet hm) hmT 0
  have h2_mem : (2 : ℤ) ∈ infiniteSupportSet m := by
    simp only [infiniteSupportSet, Set.mem_setOf_eq]; exact_mod_cast hm
  have hpos_inf : 0 < partitionFn (infiniteSupportSet m) 0 :=
    lt_of_lt_of_le (gaussWeight_pos 0 2)
      (((hasSum_partitionFn (infiniteSupportSet m) 0).summable).le_tsum ⟨2, h2_mem⟩
        fun j _ ↦ (gaussWeight_pos 0 j.1).le)
  have hhi : dualValue (infiniteSupportSet m) T ≤ Real.log (partitionFn Splus 0) := by
    linarith [Real.log_le_log hpos_inf (partitionFn_mono (infiniteSupportSet_subset_Splus m) 0)]
  exact ⟨hm0_le.trans hmono, hhi⟩

/-- **Lemma 3.2(i) uniform `O(1/α)` dual error for infinite supports `S_{≥ 0}, S_{≥ 1}, S_{≥ 2}`:**
there exist `C_dual > 0` and `Alpha₀ ≥ 10` such that for all `α ≥ Alpha₀`, `m ≤ 2`, and
`T ∈ [9/4, 9/2]` (strictly containing `K_* = [2/log 2 - 1/10, 1 + 2/log 2 + 3/10]`):
1. both the finite dual range on `S_{≥ m}^{(n)} = Finset.Ico m α` and the limiting dual range on
   `S_{≥ m} = {j : ℤ | m ≤ j}` are `BddBelow`,
2. `𝓕_{S_{≥ m}}(T) - C_dual / α ≤ 𝓕_{n, S_{≥ m}}(T) ≤ 𝓕_{S_{≥ m}}(T)`, hence
   `|𝓕_{n, S_{≥ m}}(T) - 𝓕_{S_{≥ m}}(T)| ≤ C_dual / α`. -/
theorem abs_infiniteFiniteEntropy_sub_dualValue_le :
    ∃ C_dual : ℝ, ∃ Alpha₀ : ℕ, 0 < C_dual ∧ 10 ≤ Alpha₀ ∧
      ∀ {alpha m : ℕ}, Alpha₀ ≤ alpha → m ≤ 2 →
        ∀ {T : ℝ}, T ∈ Set.Icc (9 / 4 : ℝ) (9 / 2) →
          let S_inf : Set ℤ := {j : ℤ | (m : ℤ) ≤ j}
          let F_fin : ℝ := ⨅ l : ℝ,
            (Real.log (∑ i ∈ Finset.Ico m alpha,
                Real.exp (l * (i : ℝ) +
                  (Real.log (alpha.descFactorial i : ℝ) - (i : ℝ) * Real.log (alpha : ℝ) -
                    Real.log 2 / 2 * (i : ℝ) ^ 2))) - l * T)
          BddBelow (Set.range fun l : ℝ ↦
              Real.log (∑ i ∈ Finset.Ico m alpha,
                Real.exp (l * (i : ℝ) +
                  (Real.log (alpha.descFactorial i : ℝ) - (i : ℝ) * Real.log (alpha : ℝ) -
                    Real.log 2 / 2 * (i : ℝ) ^ 2))) - l * T) ∧
            BddBelow (Set.range fun l : ℝ ↦ Real.log (partitionFn S_inf l) - l * T) ∧
            (dualValue S_inf T - C_dual / (alpha : ℝ) ≤ F_fin ∧ F_fin ≤ dualValue S_inf T) ∧
            |F_fin - dualValue S_inf T| ≤ C_dual / (alpha : ℝ) := by
  classical
  have hq_pos : 0 < q := q_pos
  set U_top : ℝ := |Real.log (partitionFn Splus 0)| + 1
  set Λ : ℝ := max 1 (8 * (U_top + 38))
  have hΛ_pos : 0 < Λ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  -- Summable second-moment series `M₂ := ∑'_{k : ℕ} k² exp(Λ k - (q/2) k²)`
  have hM₂_sum : Summable (fun k : ℕ ↦ (k : ℝ) ^ 2 * extendedGaussianNaturalTerm q Λ k) :=
    summable_extendedGaussianSecondMoment (a := q) (lambda := Λ) hq_pos
  set M₂ : ℝ := ∑' k : ℕ, (k : ℝ) ^ 2 * extendedGaussianNaturalTerm q Λ k
  have hM₂_nn : 0 ≤ M₂ := tsum_nonneg fun k ↦
    mul_nonneg (sq_nonneg _) (extendedGaussianNaturalTerm_pos q Λ k).le
  -- Summable first-order tail `∑'_{k : ℕ} k * extendedGaussianNaturalTerm q Λ k` (dominated by `1 + k²`)
  have hM₁_sum : Summable (fun k : ℕ ↦ ((k : ℝ) + 1) * extendedGaussianNaturalTerm q Λ k) := by
    have hbase : Summable (fun k : ℕ ↦ extendedGaussianNaturalTerm q Λ k) :=
      summable_extendedGaussianNaturalTerm (a := q) (lambda := Λ) hq_pos
    refine Summable.of_nonneg_of_le
      (fun k ↦ mul_nonneg (by positivity) (extendedGaussianNaturalTerm_pos q Λ k).le)
      (fun k ↦ ?_) ((hbase.mul_left 2).add hM₂_sum)
    have hk_le : (k : ℝ) + 1 ≤ 2 + (k : ℝ) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have hm := mul_le_mul_of_nonneg_right hk_le (extendedGaussianNaturalTerm_pos q Λ k).le
    linarith
  set M₁ : ℝ := ∑' k : ℕ, ((k : ℝ) + 1) * extendedGaussianNaturalTerm q Λ k
  have hM₁_nn : 0 ≤ M₁ := tsum_nonneg fun k ↦
    mul_nonneg (by positivity) (extendedGaussianNaturalTerm_pos q Λ k).le
  -- Uniform lower bound on `partitionFn (infiniteSupportSet m) l` on `[-Λ, Λ]` via `2 ∈ S_{≥ m}`
  set z_min : ℝ := Real.exp (-2 * Λ - 2 * Real.log 2)
  have hz_min_pos : 0 < z_min := Real.exp_pos _
  set Err_num : ℝ := M₂ + 2 * M₁ + 1
  have hErr_pos : 0 < Err_num := by dsimp [Err_num]; positivity
  set Alpha₀ : ℕ := max 10 (Nat.ceil (2 * Err_num / z_min) + 1)
  set C_dual : ℝ := 2 * Err_num / z_min
  have hC_dual_pos : 0 < C_dual := div_pos (mul_pos two_pos hErr_pos) hz_min_pos
  refine ⟨C_dual, Alpha₀, hC_dual_pos, le_max_left _ _, ?_⟩
  intro alpha m halpha hm T hT S_inf F_fin
  have ha10 : 10 ≤ alpha := le_trans (le_max_left _ _) halpha
  have ha_big : Nat.ceil (2 * Err_num / z_min) + 1 ≤ alpha := le_trans (le_max_right _ _) halpha
  have ha_pos : (0 : ℝ) < (alpha : ℝ) := by exact_mod_cast (show 0 < alpha by omega)
  have hS_eq : S_inf = infiniteSupportSet m := rfl
  have hF_eq : F_fin = infiniteFiniteEntropy alpha m T := rfl
  have hT_pad : T ∈ Set.Icc (17 / 8 : ℝ) (37 / 8) := ⟨by linarith [hT.1], by linarith [hT.2]⟩
  have hT_25 : T ∈ Set.Ioo (2 : ℝ) 5 := ⟨by linarith [hT.1], by linarith [hT.2]⟩
  obtain ⟨hbdd_fin, htrap⟩ := bddBelow_and_tilt_trap_infiniteFiniteDual hm ha10 hT_pad
  have hmT := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT_25)
  have hbdd_inf : BddBelow (Set.range fun l : ℝ ↦ Real.log (partitionFn S_inf l) - l * T) :=
    bddBelow_dual (s4_subset_infiniteSupportSet hm) hmT
  -- Upper bound: `F_fin ≤ dualValue S_inf T`
  have hub_fin : F_fin ≤ dualValue S_inf T := by
    rw [hF_eq, hS_eq]
    refine le_ciInf fun l ↦ ?_
    have hZ_le : Real.log (infiniteFinitePartition alpha m l) ≤
        Real.log (partitionFn (infiniteSupportSet m) l) :=
      Real.log_le_log (infiniteFinitePartition_pos (by omega) l)
        (infiniteFinitePartition_le_partitionFn l)
    exact (ciInf_le hbdd_fin l).trans (by linarith)
  -- Lower bound: `dualValue S_inf T - C_dual / alpha ≤ F_fin`
  have hdual_hi : dualValue S_inf T ≤ U_top - 1 := by
    rw [hS_eq]
    have hd := (dualValue_infinite_bounds_on_padded hm hT_pad).2
    dsimp [U_top]
    linarith [le_abs_self (Real.log (partitionFn Splus 0))]
  have hlb_fin : dualValue S_inf T - C_dual / (alpha : ℝ) ≤ F_fin := by
    rw [hF_eq]
    refine le_ciInf fun l ↦ ?_
    by_cases hl_big : U_top < Real.log (infiniteFinitePartition alpha m l) - l * T
    · have : dualValue S_inf T - C_dual / (alpha : ℝ) ≤ dualValue S_inf T :=
        sub_le_self _ (div_nonneg hC_dual_pos.le ha_pos.le)
      linarith
    · replace hl_big : Real.log (infiniteFinitePartition alpha m l) - l * T ≤ U_top :=
        le_of_not_gt hl_big
      have hl_abs_raw := (htrap hl_big).1
      have hl_abs : |l| ≤ Λ := hl_abs_raw.trans (max_le_max (by norm_num : (0 : ℝ) ≤ 1) le_rfl)
      obtain ⟨hl_lo, hl_hi⟩ := abs_le.mp hl_abs
      -- Lower-bound `partitionFn S_inf l ≥ z_min` via `j = 2 ∈ S_inf`
      have hZ_inf_ge : z_min ≤ partitionFn S_inf l := by
        have h2_mem : (2 : ℤ) ∈ S_inf := by
          simp only [S_inf, Set.mem_setOf_eq]; exact_mod_cast hm
        have hgw2 : z_min ≤ gaussWeight l 2 := by
          dsimp [z_min]
          unfold gaussWeight
          apply Real.exp_le_exp.mpr
          push_cast
          linarith
        have h2_le_tsum : gaussWeight l 2 ≤ partitionFn S_inf l :=
          ((hasSum_partitionFn S_inf l).summable).le_tsum ⟨2, h2_mem⟩
            fun j _ ↦ (gaussWeight_pos l j.1).le
        exact hgw2.trans h2_le_tsum
      -- Split `S_inf` at `N_half := alpha / 2` (`m ≤ N_half < alpha`)
      set N_half : ℕ := alpha / 2
      have hm_le_Nh : m ≤ N_half := by omega
      have hNh_lt_a : N_half < alpha := by omega
      have hsub_ico : Finset.Icc m N_half ⊆ Finset.Ico m alpha := by
        intro i hi
        obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hi
        exact Finset.mem_Ico.mpr ⟨h1, lt_of_le_of_lt h2 hNh_lt_a⟩
      -- Head comparison on `Finset.Icc m N_half`
      have hhead_ge :
          (∑ i ∈ Finset.Icc m N_half, gaussWeight l (i : ℤ)) - M₂ / (alpha : ℝ) ≤
            infiniteFinitePartition alpha m l := by
        have hterm_ge : ∀ i ∈ Finset.Icc m N_half,
            gaussWeight l (i : ℤ) -
                ((i : ℝ) ^ 2 * extendedGaussianNaturalTerm q Λ i) / (alpha : ℝ) ≤
              Real.exp (l * (i : ℝ) + infiniteFiniteScore alpha i) := by
          intro i hi
          obtain ⟨_, hi_Nh⟩ := Finset.mem_Icc.mp hi
          have hi_lt : i < alpha := lt_of_le_of_lt hi_Nh hNh_lt_a
          have h2i : 2 * i ≤ alpha := by omega
          obtain ⟨hid, _, hge⟩ := finiteDeficitResidualScore_bounds hi_lt
          have hexp_ge : 1 - (i : ℝ) ^ 2 / (alpha : ℝ) ≤
              Real.exp (Real.log (alpha.descFactorial i : ℝ) - (i : ℝ) * Real.log (alpha : ℝ)) := by
            rw [hid]
            have h1 := Real.add_one_le_exp (∑ r ∈ Finset.range i, Real.log (1 - (r : ℝ) / (alpha : ℝ)))
            have h2 := hge h2i
            rw [neg_div] at h2
            linarith
          have hrew_exp : Real.exp (l * (i : ℝ) + infiniteFiniteScore alpha i) =
              gaussWeight l (i : ℤ) *
                Real.exp (Real.log (alpha.descFactorial i : ℝ) - (i : ℝ) * Real.log (alpha : ℝ)) := by
            unfold infiniteFiniteScore gaussWeight
            rw [← Real.exp_add]
            congr 1; push_cast; ring
          have hgw_le_Λ : gaussWeight l (i : ℤ) ≤ extendedGaussianNaturalTerm q Λ i := by
            unfold gaussWeight extendedGaussianNaturalTerm q
            apply Real.exp_le_exp.mpr
            push_cast
            have hm_l := mul_le_mul_of_nonneg_right hl_hi (Nat.cast_nonneg (α := ℝ) i)
            linarith
          rw [hrew_exp]
          have hm1 := mul_le_mul_of_nonneg_left hexp_ge (gaussWeight_pos l (i : ℤ)).le
          have hm2 : gaussWeight l (i : ℤ) * ((i : ℝ) ^ 2 / (alpha : ℝ)) ≤
              ((i : ℝ) ^ 2 * extendedGaussianNaturalTerm q Λ i) / (alpha : ℝ) := by
            rw [mul_div_assoc', mul_comm (gaussWeight l (i : ℤ))]
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hgw_le_Λ (sq_nonneg _)) ha_pos.le
          linarith
        have hsum_m2 :
            (∑ i ∈ Finset.Icc m N_half, (i : ℝ) ^ 2 * extendedGaussianNaturalTerm q Λ i) ≤ M₂ :=
          hM₂_sum.sum_le_tsum _ fun k _ ↦
            mul_nonneg (sq_nonneg _) (extendedGaussianNaturalTerm_pos q Λ k).le
        have h1 := Finset.sum_le_sum hterm_ge
        rw [Finset.sum_sub_distrib, ← Finset.sum_div] at h1
        have h2 : infiniteFinitePartition alpha m l ≥
            ∑ i ∈ Finset.Icc m N_half, Real.exp (l * (i : ℝ) + infiniteFiniteScore alpha i) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub_ico fun _ _ _ ↦ (Real.exp_pos _).le
        have hdiv_le :
            (∑ i ∈ Finset.Icc m N_half, (i : ℝ) ^ 2 * extendedGaussianNaturalTerm q Λ i) / (alpha : ℝ) ≤
              M₂ / (alpha : ℝ) :=
          div_le_div_of_nonneg_right hsum_m2 ha_pos.le
        linarith
      -- Tail bound: `partitionFn S_inf l - ∑_{i=m}^{N_half} gaussWeight l i ≤ 2 M₁ / alpha`
      have htail_le :
          partitionFn S_inf l - (∑ i ∈ Finset.Icc m N_half, gaussWeight l (i : ℤ)) ≤
            (2 * M₁) / (alpha : ℝ) := by
        -- Rewrite `partitionFn S_inf l` as `∑' k : ℕ, gaussWeight l (k : ℤ)` restricted to `k ≥ m`
        let f_nat : ℕ → ℝ := fun k ↦ if m ≤ k then gaussWeight l (k : ℤ) else 0
        have hf_sum : Summable f_nat :=
          Summable.of_nonneg_of_le
            (fun k ↦ by
              dsimp [f_nat]
              split_ifs
              · exact (gaussWeight_pos l (k : ℤ)).le
              · exact le_rfl)
            (fun k ↦ by
              dsimp [f_nat]
              split_ifs
              · unfold gaussWeight extendedGaussianNaturalTerm q
                apply Real.exp_le_exp.mpr; push_cast
                linarith [mul_le_mul_of_nonneg_right hl_hi (Nat.cast_nonneg (α := ℝ) k)]
              · exact (extendedGaussianNaturalTerm_pos q Λ k).le)
            (summable_extendedGaussianNaturalTerm (a := q) (lambda := Λ) hq_pos)
        have hpart_eq_nat : partitionFn S_inf l = ∑' k : ℕ, f_nat k := by
          unfold partitionFn
          rw [tsum_subtype S_inf (gaussWeight l)]
          refine tsum_eq_tsum_of_ne_zero_bij (fun (x : {k : ℕ // f_nat k ≠ 0}) ↦ (x.1 : ℤ))
            (fun a b h ↦ Subtype.ext (Int.ofNat.inj h)) ?_ ?_
          · intro j hj
            rw [Function.mem_support, Set.indicator_apply] at hj
            by_cases hmem : j ∈ S_inf
            · have hj_nn : 0 ≤ j := le_trans (Nat.cast_nonneg m) hmem
              lift j to ℕ using hj_nn
              have hmk : m ≤ j := by
                simp only [S_inf, Set.mem_setOf_eq] at hmem
                exact_mod_cast hmem
              have hfn_ne : f_nat j ≠ 0 := by simp [f_nat, hmk, (gaussWeight_pos l (j : ℤ)).ne']
              exact ⟨⟨j, hfn_ne⟩, rfl⟩
            · simp [hmem] at hj
          · intro ⟨k, hk⟩
            dsimp [f_nat] at hk ⊢
            by_cases hmk : m ≤ k
            · have hz : (k : ℤ) ∈ S_inf := by simp only [S_inf, Set.mem_setOf_eq]; exact_mod_cast hmk
              simp [hmk, Set.indicator_of_mem hz]
            · simp [hmk] at hk
        have hsplit_nat :
            (∑' k : ℕ, f_nat k) =
              (∑ k ∈ Finset.range (N_half + 1), f_nat k) +
                ∑' k : ℕ, f_nat (k + (N_half + 1)) :=
          (hf_sum.sum_add_tsum_nat_add (N_half + 1)).symm
        have hrange_eq :
            (∑ k ∈ Finset.range (N_half + 1), f_nat k) =
              ∑ i ∈ Finset.Icc m N_half, gaussWeight l (i : ℤ) := by
          have hsub_r : Finset.Icc m N_half ⊆ Finset.range (N_half + 1) := by
            intro i hi; exact Finset.mem_range.mpr (by linarith [(Finset.mem_Icc.mp hi).2])
          rw [← Finset.sum_subset hsub_r]
          · refine Finset.sum_congr rfl fun i hi ↦ ?_
            simp [f_nat, (Finset.mem_Icc.mp hi).1]
          · intro i hi hnot
            rw [Finset.mem_range] at hi
            rw [Finset.mem_Icc, not_and_or] at hnot
            rcases hnot with hlt_m | hgt
            · simp [f_nat, hlt_m]
            · omega
        have hrem_term : ∀ k : ℕ,
            f_nat (k + (N_half + 1)) ≤
              (2 / (alpha : ℝ)) *
                (((k + (N_half + 1) : ℕ) : ℝ) + 1) *
                extendedGaussianNaturalTerm q Λ (k + (N_half + 1)) := by
          intro k
          set idx : ℕ := k + (N_half + 1)
          have hidx_ge_a2 : (alpha : ℝ) / 2 ≤ ((idx : ℝ) + 1) := by
            have : alpha ≤ 2 * (N_half + 1) := by dsimp [N_half]; omega
            have hR : (alpha : ℝ) ≤ 2 * ((N_half : ℝ) + 1) := by exact_mod_cast this
            have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
            dsimp [idx]; push_cast; linarith
          have h1_le : 1 ≤ (2 / (alpha : ℝ)) * ((idx : ℝ) + 1) := by
            rw [div_mul_eq_mul_div, one_le_div ha_pos]; linarith
          have hgw_le : f_nat idx ≤ extendedGaussianNaturalTerm q Λ idx := by
            dsimp [f_nat]
            split_ifs
            · unfold gaussWeight extendedGaussianNaturalTerm q
              apply Real.exp_le_exp.mpr; push_cast
              linarith [mul_le_mul_of_nonneg_right hl_hi (Nat.cast_nonneg (α := ℝ) idx)]
            · exact (extendedGaussianNaturalTerm_pos q Λ idx).le
          calc f_nat idx ≤ 1 * extendedGaussianNaturalTerm q Λ idx := by rwa [one_mul]
            _ ≤ ((2 / (alpha : ℝ)) * ((idx : ℝ) + 1)) * extendedGaussianNaturalTerm q Λ idx :=
                mul_le_mul_of_nonneg_right h1_le (extendedGaussianNaturalTerm_pos q Λ idx).le
            _ = _ := by ring
        have hsum_shift :
            Summable (fun k : ℕ ↦
              (2 / (alpha : ℝ)) * (((k + (N_half + 1) : ℕ) : ℝ) + 1) *
                extendedGaussianNaturalTerm q Λ (k + (N_half + 1))) := by
          have hs := (hM₁_sum.comp_injective (add_left_injective (N_half + 1))).mul_left
            (2 / (alpha : ℝ))
          exact hs.congr fun k ↦ by simp only [Function.comp_def]; ring
        have hrem_tsum :
            (∑' k : ℕ, f_nat (k + (N_half + 1))) ≤ (2 * M₁) / (alpha : ℝ) := by
          calc (∑' k : ℕ, f_nat (k + (N_half + 1)))
              ≤ ∑' k : ℕ,
                  (2 / (alpha : ℝ)) * (((k + (N_half + 1) : ℕ) : ℝ) + 1) *
                    extendedGaussianNaturalTerm q Λ (k + (N_half + 1)) :=
                (hf_sum.comp_injective (add_left_injective (N_half + 1))).tsum_le_tsum
                  hrem_term hsum_shift
            _ = (2 / (alpha : ℝ)) *
                  ∑' k : ℕ, (((k + (N_half + 1) : ℕ) : ℝ) + 1) *
                    extendedGaussianNaturalTerm q Λ (k + (N_half + 1)) := by
                have hrw : (fun k : ℕ ↦
                    (2 / (alpha : ℝ)) * (((k + (N_half + 1) : ℕ) : ℝ) + 1) *
                      extendedGaussianNaturalTerm q Λ (k + (N_half + 1))) =
                  fun k : ℕ ↦ (2 / (alpha : ℝ)) *
                    ((((k + (N_half + 1) : ℕ) : ℝ) + 1) *
                      extendedGaussianNaturalTerm q Λ (k + (N_half + 1))) := by
                  funext k; ring
                rw [hrw, tsum_mul_left]
            _ ≤ (2 / (alpha : ℝ)) * M₁ := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                have hfull := (hM₁_sum.sum_add_tsum_nat_add (N_half + 1)).symm
                have hnonneg_pref : 0 ≤ ∑ k ∈ Finset.range (N_half + 1),
                    ((k : ℝ) + 1) * extendedGaussianNaturalTerm q Λ k :=
                  Finset.sum_nonneg fun k _ ↦
                    mul_nonneg (by positivity) (extendedGaussianNaturalTerm_pos q Λ k).le
                dsimp [M₁]
                linarith
            _ = (2 * M₁) / (alpha : ℝ) := by ring
        rw [hpart_eq_nat, hsplit_nat, hrange_eq]
        linarith
      -- Combine head + tail into `infiniteFinitePartition alpha m l ≥ partitionFn S_inf l * (1 - u)`
      have hZ_fin_ge :
          partitionFn S_inf l - Err_num / (alpha : ℝ) ≤ infiniteFinitePartition alpha m l := by
        have h1 : (M₂ + 2 * M₁) / (alpha : ℝ) ≤ Err_num / (alpha : ℝ) :=
          div_le_div_of_nonneg_right (by dsimp [Err_num]; linarith) ha_pos.le
        have h2 : M₂ / (alpha : ℝ) + (2 * M₁) / (alpha : ℝ) = (M₂ + 2 * M₁) / (alpha : ℝ) :=
          (add_div _ _ _).symm
        linarith [hhead_ge, htail_le]
      set u_rel : ℝ := Err_num / ((alpha : ℝ) * partitionFn S_inf l)
      have hZ_inf_pos : 0 < partitionFn S_inf l := lt_of_lt_of_le hz_min_pos hZ_inf_ge
      have hu_rel_nn : 0 ≤ u_rel := div_nonneg hErr_pos.le (mul_pos ha_pos hZ_inf_pos).le
      have hu_rel_le : u_rel ≤ (C_dual / 2) / (alpha : ℝ) := by
        dsimp [u_rel, C_dual]
        have h1 : (2 * Err_num / z_min / 2) / (alpha : ℝ) = Err_num / ((alpha : ℝ) * z_min) := by
          field_simp [hz_min_pos.ne', ha_pos.ne']
        rw [h1]
        exact div_le_div_of_nonneg_left hErr_pos.le (mul_pos ha_pos hz_min_pos)
          (mul_le_mul_of_nonneg_left hZ_inf_ge ha_pos.le)
      have hu_rel_half : u_rel ≤ 1 / 2 := by
        have ha_gt : 2 * Err_num / z_min ≤ (alpha : ℝ) := by
          have hc : 2 * Err_num / z_min ≤ (Nat.ceil (2 * Err_num / z_min) : ℝ) := Nat.le_ceil _
          have ha_c : (Nat.ceil (2 * Err_num / z_min) : ℝ) ≤ (alpha : ℝ) := by
            exact_mod_cast (show Nat.ceil (2 * Err_num / z_min) ≤ alpha by omega)
          exact hc.trans ha_c
        have hhalf : (C_dual / 2) / (alpha : ℝ) ≤ 1 / 2 := by
          rw [div_le_iff₀ ha_pos]
          dsimp [C_dual]
          linarith
        exact hu_rel_le.trans hhalf
      have hexp_neg2 : Real.exp (-2 * u_rel) ≤ 1 - u_rel := by
        have h1m_pos0 : 0 < 1 - u_rel := by linarith
        have hquot_le : u_rel / (1 - u_rel) ≤ 2 * u_rel := by
          rw [div_le_iff₀ h1m_pos0]; nlinarith
        have hexp_inv : 1 / (1 - u_rel) ≤ Real.exp (2 * u_rel) := by
          have hid1 : 1 / (1 - u_rel) = u_rel / (1 - u_rel) + 1 := by
            field_simp [h1m_pos0.ne']; ring
          rw [hid1]
          exact (Real.add_one_le_exp (u_rel / (1 - u_rel))).trans (Real.exp_le_exp.mpr hquot_le)
        have hm := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hexp_inv h1m_pos0.le) (Real.exp_pos (-2 * u_rel)).le
        have hl : (1 - u_rel) * (1 / (1 - u_rel)) * Real.exp (-2 * u_rel) = Real.exp (-2 * u_rel) := by
          field_simp [h1m_pos0.ne']
        have hr_eq : (1 - u_rel) * Real.exp (2 * u_rel) * Real.exp (-2 * u_rel) = 1 - u_rel := by
          rw [mul_assoc, ← Real.exp_add]; simp
        rwa [hl, hr_eq] at hm
      have hZ_fin_exp :
          partitionFn S_inf l * Real.exp (-2 * u_rel) ≤ infiniteFinitePartition alpha m l := by
        have hm := mul_le_mul_of_nonneg_left hexp_neg2 hZ_inf_pos.le
        have hrhs : partitionFn S_inf l * (1 - u_rel) =
            partitionFn S_inf l - Err_num / (alpha : ℝ) := by
          dsimp [u_rel]
          field_simp [ha_pos.ne', hZ_inf_pos.ne']
        exact hm.trans (hrhs.symm ▸ hZ_fin_ge)
      have hlog_ge :
          Real.log (partitionFn S_inf l) - C_dual / (alpha : ℝ) ≤
            Real.log (infiniteFinitePartition alpha m l) := by
        have hlog1 := Real.log_le_log (mul_pos hZ_inf_pos (Real.exp_pos _)) hZ_fin_exp
        rw [Real.log_mul hZ_inf_pos.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog1
        have h2u : 2 * u_rel ≤ C_dual / (alpha : ℝ) := by
          have := mul_le_mul_of_nonneg_left hu_rel_le zero_le_two
          linarith [show 2 * (C_dual / 2 / (alpha : ℝ)) = C_dual / (alpha : ℝ) by ring]
        linarith
      have hdual_le_l : dualValue S_inf T ≤ Real.log (partitionFn S_inf l) - l * T :=
        ciInf_le hbdd_inf l
      linarith
  exact ⟨hbdd_fin, hbdd_inf, ⟨hlb_fin, hub_fin⟩,
    abs_le.mpr ⟨by linarith [hlb_fin], by linarith [hub_fin]⟩⟩

/-- **Lemma 3.2(iv) uniform `O(1/α)` capped infinite-support dual error (`S_{≥ 1}^{=ϑ}`):**
there exist `C_dual > 0` and `Alpha₀ ≥ 10` such that for all `α ≥ Alpha₀`, `ϑ ∈ [0, 1/20]`,
and `T ∈ K_cap`,
`|𝓕_{n, S_{≥ 1}}^{=ϑ}(T) - 𝓕_{S_{≥ 1}}^{=ϑ}(T)| ≤ (1 - ϑ) C_dual / α ≤ C_dual / α`. -/
theorem abs_cappedInfiniteFiniteEntropy_sub_cappedDualValue_le :
    ∃ C_dual : ℝ, ∃ Alpha₀ : ℕ, 0 < C_dual ∧ 10 ≤ Alpha₀ ∧
      ∀ {alpha : ℕ}, Alpha₀ ≤ alpha →
        ∀ {theta T : ℝ}, theta ∈ Set.Icc (0 : ℝ) (1 / 20) → T ∈ KcapInterval →
          let u : ℝ := (T - theta) / (1 - theta)
          let F_tail : ℝ := ⨅ l : ℝ,
            (Real.log (∑ i ∈ Finset.Ico 2 alpha,
                Real.exp (l * (i : ℝ) +
                  (Real.log (alpha.descFactorial i : ℝ) - (i : ℝ) * Real.log (alpha : ℝ) -
                    Real.log 2 / 2 * (i : ℝ) ^ 2))) - l * u)
          let F_cap_fin : ℝ := binEntropy theta - Real.log 2 / 2 * theta + (1 - theta) * F_tail
          |F_cap_fin - cappedDualValue Sge1 theta T| ≤ (1 - theta) * C_dual / (alpha : ℝ) ∧
            |F_cap_fin - cappedDualValue Sge1 theta T| ≤ C_dual / (alpha : ℝ) := by
  obtain ⟨C_dual, Alpha₀, hC_pos, hA10, hinf⟩ := abs_infiniteFiniteEntropy_sub_dualValue_le
  refine ⟨C_dual, Alpha₀, hC_pos, hA10, ?_⟩
  intro alpha halpha theta T htheta hT u F_tail F_cap_fin
  obtain ⟨h2lo, h2hi⟩ := two_div_log_two_bounds
  obtain ⟨hT_lo, hT_hi⟩ := hT
  have h1m_pos : 0 < 1 - theta := by linarith [htheta.2]
  have h1m_le1 : 1 - theta ≤ 1 := by linarith [htheta.1]
  have hu_icc : u ∈ Set.Icc (9 / 4 : ℝ) (9 / 2) := by
    dsimp [u]
    constructor
    · rw [le_div_iff₀ h1m_pos]; nlinarith [htheta.1, htheta.2, hT_lo, h2lo]
    · rw [div_le_iff₀ h1m_pos]; nlinarith [htheta.1, htheta.2, hT_hi, h2hi]
  have htail := (hinf halpha (le_rfl : 2 ≤ 2) hu_icc).2.2.2
  have hdiff_ring :
      F_cap_fin - cappedDualValue Sge1 theta T =
        (1 - theta) * (F_tail - dualValue (Sge1 \ {1}) u) := by
    unfold F_cap_fin cappedDualValue
    ring
  have hset_eq : Sge1 \ {1} = {j : ℤ | (2 : ℤ) ≤ j} := infiniteSupportSet_two_eq_sge1_diff_one.symm
  rw [hdiff_ring, hset_eq, abs_mul, abs_of_pos h1m_pos]
  have h1 : (1 - theta) * |F_tail - dualValue {j : ℤ | (2 : ℤ) ≤ j} u| ≤
      (1 - theta) * (C_dual / (alpha : ℝ)) :=
    mul_le_mul_of_nonneg_left htail h1m_pos.le
  have ha_pos : (0 : ℝ) < (alpha : ℝ) := by exact_mod_cast (show 0 < alpha by omega)
  have h2 : (1 - theta) * (C_dual / (alpha : ℝ)) ≤ 1 * (C_dual / (alpha : ℝ)) :=
    mul_le_mul_of_nonneg_right h1m_le1 (div_nonneg hC_pos.le ha_pos.le)
  exact ⟨by simpa [mul_div_assoc] using h1, by linarith [one_mul (C_dual / (alpha : ℝ))]⟩

/-!
## 4. Infinite-support & capped Lemma 3.1 corridor roots (`∃!`), mixed `(5.19)`, and unconditional `(5.20)`
-/

private def finiteUnrestrictedDeficitEntropy (alpha : ℕ) (T : ℝ) : ℝ :=
  Real.log (profileDeficitPartition alpha (profileDeficitTilt alpha T)) -
    profileDeficitTilt alpha T * T

private def infinitePhaseObjective (m n : ℕ) (tau s : ℝ) : ℝ :=
  (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + s - s * Real.log s +
    s * (profileDeficitAffineA (phaseNat n) +
      profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s +
      infiniteFiniteEntropy (phaseNat n) m (fourSizeTarget n (phaseNat n) s) + tau)

private def cappedInfinitePhaseObjective (n : ℕ) (theta tau s : ℝ) : ℝ :=
  (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + s - s * Real.log s +
    s * (profileDeficitAffineA (phaseNat n) +
      profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s +
      cappedInfiniteFiniteEntropy (phaseNat n) theta (fourSizeTarget n (phaseNat n) s) + tau)

private def windowSupportSet_v12 (m M : ℕ) : Set ℤ :=
  {j : ℤ | ((m + 1 : ℕ) : ℤ) ≤ j ∧ j ≤ ((m + M : ℕ) : ℤ)}

private def windowFinitePartition_v12 (alpha m M : ℕ) (l : ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc (m + 1) (m + M), Real.exp (l * (i : ℝ) + infiniteFiniteScore alpha i)

private def windowFiniteEntropy_v12 (alpha m M : ℕ) (T : ℝ) : ℝ :=
  ⨅ l : ℝ, (Real.log (windowFinitePartition_v12 alpha m M l) - l * T)

private def cappedWindowFiniteEntropy_v12 (alpha M : ℕ) (theta T : ℝ) : ℝ :=
  binEntropy theta - Real.log 2 / 2 * theta +
    (1 - theta) * windowFiniteEntropy_v12 alpha 1 (M - 1) ((T - theta) / (1 - theta))

private def windowPhaseObjective_v12 (m M n : ℕ) (tau s : ℝ) : ℝ :=
  (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + s - s * Real.log s +
    s * (profileDeficitAffineA (phaseNat n) +
      profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s +
      windowFiniteEntropy_v12 (phaseNat n) m M (fourSizeTarget n (phaseNat n) s) + tau)

private def cappedWindowPhaseObjective_v12 (M n : ℕ) (theta tau s : ℝ) : ℝ :=
  (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + s - s * Real.log s +
    s * (profileDeficitAffineA (phaseNat n) +
      profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s +
      cappedWindowFiniteEntropy_v12 (phaseNat n) M theta (fourSizeTarget n (phaseNat n) s) + tau)

private theorem lipschitz_of_concave_on_padded_Icc_v12
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

private def universalDualLip_v12 : ℝ :=
  8 * (Real.log (partitionFn Splus 0) - min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8)))

private theorem universalDualLip_v12_nonneg : 0 ≤ universalDualLip_v12 := by
  have hb := dualValue_infinite_bounds_on_padded (m := 0) (by omega) (T := 3) (by norm_num)
  unfold universalDualLip_v12
  linarith [hb.1, hb.2]

private theorem abs_dualValue_infinite_sub_le
    {m : ℕ} (hm : m ≤ 2)
    {T₁ T₂ : ℝ} (hT₁ : T₁ ∈ Set.Icc (9 / 4 : ℝ) (9 / 2))
    (hT₂ : T₂ ∈ Set.Icc (9 / 4 : ℝ) (9 / 2)) :
    |dualValue (infiniteSupportSet m) T₁ - dualValue (infiniteSupportSet m) T₂| ≤
      universalDualLip_v12 * |T₁ - T₂| := by
  have hconc : ∀ {u v a b : ℝ},
      u ∈ Set.Icc ((9 / 4 : ℝ) - 1 / 8) ((9 / 2 : ℝ) + 1 / 8) →
      v ∈ Set.Icc ((9 / 4 : ℝ) - 1 / 8) ((9 / 2 : ℝ) + 1 / 8) →
      0 ≤ a → 0 ≤ b → a + b = 1 →
      a * dualValue (infiniteSupportSet m) u + b * dualValue (infiniteSupportSet m) v ≤
        dualValue (infiniteSupportSet m) (a * u + b * v) := by
    intro u v a b hu hv ha hb hsum
    have hu25 : u ∈ Set.Ioo (2 : ℝ) 5 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hv25 : v ∈ Set.Ioo (2 : ℝ) 5 := ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hmu := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hu25)
    have hmv := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hv25)
    have hbu := bddBelow_dual (s4_subset_infiniteSupportSet hm) hmu
    have hbv := bddBelow_dual (s4_subset_infiniteSupportSet hm) hmv
    refine le_ciInf fun l ↦ ?_
    have e1 := mul_le_mul_of_nonneg_left (ciInf_le hbu l) ha
    have e2 := mul_le_mul_of_nonneg_left (ciInf_le hbv l) hb
    calc a * dualValue (infiniteSupportSet m) u + b * dualValue (infiniteSupportSet m) v
        ≤ a * (Real.log (partitionFn (infiniteSupportSet m) l) - l * u) +
            b * (Real.log (partitionFn (infiniteSupportSet m) l) - l * v) := add_le_add e1 e2
      _ = (a + b) * Real.log (partitionFn (infiniteSupportSet m) l) -
            l * (a * u + b * v) := by ring
      _ = Real.log (partitionFn (infiniteSupportSet m) l) - l * (a * u + b * v) := by
            rw [hsum, one_mul]
  have hbdd : ∀ t ∈ Set.Icc ((9 / 4 : ℝ) - 1 / 8) ((9 / 2 : ℝ) + 1 / 8),
      min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8)) ≤
        dualValue (infiniteSupportSet m) t ∧
      dualValue (infiniteSupportSet m) t ≤ Real.log (partitionFn Splus 0) := by
    intro t ht
    exact dualValue_infinite_bounds_on_padded hm ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hlip := lipschitz_of_concave_on_padded_Icc_v12 (r_pad := 1 / 8) (by norm_num)
    hconc hbdd hT₂ hT₁
  have hconst : (Real.log (partitionFn Splus 0) -
      min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))) / (1 / 8 : ℝ) =
      universalDualLip_v12 := by
    unfold universalDualLip_v12; ring
  rwa [hconst] at hlip

private theorem reducedTarget_mem_Icc_and_Ioo_v12
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

private theorem abs_cappedDualValue_Sge1_sub_le
    {theta T₁ T₂ : ℝ}
    (htheta : theta ∈ Set.Icc (0 : ℝ) (1 / 20))
    (hT₁ : T₁ ∈ KcapInterval) (hT₂ : T₂ ∈ KcapInterval) :
    |cappedDualValue Sge1 theta T₁ - cappedDualValue Sge1 theta T₂| ≤
      universalDualLip_v12 * |T₁ - T₂| := by
  have h1m_pos : 0 < 1 - theta := by linarith [htheta.2]
  have hu₁ := (reducedTarget_mem_Icc_and_Ioo_v12 htheta hT₁).1
  have hu₂ := (reducedTarget_mem_Icc_and_Ioo_v12 htheta hT₂).1
  have hu₁_wide : (T₁ - theta) / (1 - theta) ∈ Set.Icc (9 / 4 : ℝ) (9 / 2) :=
    ⟨by linarith [hu₁.1], hu₁.2⟩
  have hu₂_wide : (T₂ - theta) / (1 - theta) ∈ Set.Icc (9 / 4 : ℝ) (9 / 2) :=
    ⟨by linarith [hu₂.1], hu₂.2⟩
  have hdiff : cappedDualValue Sge1 theta T₁ - cappedDualValue Sge1 theta T₂ =
      (1 - theta) *
        (dualValue (infiniteSupportSet 2) ((T₁ - theta) / (1 - theta)) -
          dualValue (infiniteSupportSet 2) ((T₂ - theta) / (1 - theta))) := by
    unfold cappedDualValue
    rw [← infiniteSupportSet_two_eq_sge1_diff_one]
    ring
  rw [hdiff, abs_mul, abs_of_pos h1m_pos]
  have hinf := abs_dualValue_infinite_sub_le (m := 2) le_rfl hu₁_wide hu₂_wide
  have hsub_u : (T₁ - theta) / (1 - theta) - (T₂ - theta) / (1 - theta) =
      (T₁ - T₂) / (1 - theta) := by ring
  rw [hsub_u, abs_div, abs_of_pos h1m_pos] at hinf
  calc (1 - theta) *
        |dualValue (infiniteSupportSet 2) ((T₁ - theta) / (1 - theta)) -
          dualValue (infiniteSupportSet 2) ((T₂ - theta) / (1 - theta))|
      ≤ (1 - theta) * (universalDualLip_v12 * (|T₁ - T₂| / (1 - theta))) :=
        mul_le_mul_of_nonneg_left hinf h1m_pos.le
    _ = universalDualLip_v12 * |T₁ - T₂| := by field_simp [h1m_pos.ne']

private theorem s4_subset_windowSupportSet_v12 {m M : ℕ} (hm : m ≤ 1) (hM : 7 ≤ M) :
    S4 ⊆ windowSupportSet_v12 m M := by
  intro j hj
  simp only [S4, Set.mem_insert_iff, Set.mem_singleton_iff] at hj
  simp only [windowSupportSet_v12, Set.mem_setOf_eq]
  rcases hj with rfl | rfl | rfl | rfl <;> omega

private theorem windowSupportSet_subset_Splus_v12 (m M : ℕ) :
    windowSupportSet_v12 m M ⊆ Splus := by
  intro j hj
  simp only [windowSupportSet_v12, Splus, Set.mem_setOf_eq] at hj ⊢
  omega

private theorem dualValue_window_bounds_on_padded_v12
    {m M : ℕ} (hm : m ≤ 1) (hM : 7 ≤ M)
    (T : ℝ) (hT : T ∈ Set.Icc (17 / 8 : ℝ) (37 / 8)) :
    min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8)) ≤
        dualValue (windowSupportSet_v12 m M) T ∧
      dualValue (windowSupportSet_v12 m M) T ≤ Real.log (partitionFn Splus 0) := by
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
  have hmono := dualValue_mono subset_rfl (s4_subset_windowSupportSet_v12 hm hM) hmT
  have h0 := dualValue_le_at (s4_subset_windowSupportSet_v12 hm hM) hmT 0
  have h2_mem : (2 : ℤ) ∈ windowSupportSet_v12 m M := by
    simp only [windowSupportSet_v12, Set.mem_setOf_eq]; omega
  have hpos : 0 < partitionFn (windowSupportSet_v12 m M) 0 :=
    lt_of_lt_of_le (gaussWeight_pos 0 2)
      (((hasSum_partitionFn (windowSupportSet_v12 m M) 0).summable).le_tsum ⟨2, h2_mem⟩
        fun j _ ↦ (gaussWeight_pos 0 j.1).le)
  have hhi : dualValue (windowSupportSet_v12 m M) T ≤ Real.log (partitionFn Splus 0) := by
    linarith [Real.log_le_log hpos (partitionFn_mono (windowSupportSet_subset_Splus_v12 m M) 0)]
  exact ⟨hm0_le_S4.trans hmono, hhi⟩

private theorem abs_dualValue_window_sub_le_v12
    {m M : ℕ} (hm : m ≤ 1) (hM : 7 ≤ M)
    {T₁ T₂ : ℝ} (hT₁ : T₁ ∈ Set.Icc (9 / 4 : ℝ) (9 / 2))
    (hT₂ : T₂ ∈ Set.Icc (9 / 4 : ℝ) (9 / 2)) :
    |dualValue (windowSupportSet_v12 m M) T₁ - dualValue (windowSupportSet_v12 m M) T₂| ≤
      universalDualLip_v12 * |T₁ - T₂| := by
  have hconc : ∀ {u v a b : ℝ},
      u ∈ Set.Icc ((9 / 4 : ℝ) - 1 / 8) ((9 / 2 : ℝ) + 1 / 8) →
      v ∈ Set.Icc ((9 / 4 : ℝ) - 1 / 8) ((9 / 2 : ℝ) + 1 / 8) →
      0 ≤ a → 0 ≤ b → a + b = 1 →
      a * dualValue (windowSupportSet_v12 m M) u + b * dualValue (windowSupportSet_v12 m M) v ≤
        dualValue (windowSupportSet_v12 m M) (a * u + b * v) := by
    intro u v a b hu hv ha hb hsum
    have hu25 : u ∈ Set.Ioo (2 : ℝ) 5 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hv25 : v ∈ Set.Ioo (2 : ℝ) 5 := ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hmu := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hu25)
    have hmv := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hv25)
    have hbu := bddBelow_dual (s4_subset_windowSupportSet_v12 hm hM) hmu
    have hbv := bddBelow_dual (s4_subset_windowSupportSet_v12 hm hM) hmv
    refine le_ciInf fun l ↦ ?_
    have e1 := mul_le_mul_of_nonneg_left (ciInf_le hbu l) ha
    have e2 := mul_le_mul_of_nonneg_left (ciInf_le hbv l) hb
    calc a * dualValue (windowSupportSet_v12 m M) u + b * dualValue (windowSupportSet_v12 m M) v
        ≤ a * (Real.log (partitionFn (windowSupportSet_v12 m M) l) - l * u) +
            b * (Real.log (partitionFn (windowSupportSet_v12 m M) l) - l * v) := add_le_add e1 e2
      _ = (a + b) * Real.log (partitionFn (windowSupportSet_v12 m M) l) -
            l * (a * u + b * v) := by ring
      _ = Real.log (partitionFn (windowSupportSet_v12 m M) l) - l * (a * u + b * v) := by
            rw [hsum, one_mul]
  have hbdd : ∀ t ∈ Set.Icc ((9 / 4 : ℝ) - 1 / 8) ((9 / 2 : ℝ) + 1 / 8),
      min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8)) ≤
        dualValue (windowSupportSet_v12 m M) t ∧
      dualValue (windowSupportSet_v12 m M) t ≤ Real.log (partitionFn Splus 0) := by
    intro t ht
    exact dualValue_window_bounds_on_padded_v12 hm hM t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hlip := lipschitz_of_concave_on_padded_Icc_v12 (r_pad := 1 / 8) (by norm_num)
    hconc hbdd hT₂ hT₁
  have hconst : (Real.log (partitionFn Splus 0) -
      min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))) / (1 / 8 : ℝ) =
      universalDualLip_v12 := by
    unfold universalDualLip_v12; ring
  rwa [hconst] at hlip

private theorem abs_cappedDualValue_S0M_sub_le_v12
    {M : ℕ} (hM : 8 ≤ M) {theta T₁ T₂ : ℝ}
    (htheta : theta ∈ Set.Icc (0 : ℝ) (1 / 20))
    (hT₁ : T₁ ∈ KcapInterval) (hT₂ : T₂ ∈ KcapInterval) :
    |cappedDualValue (S0M M) theta T₁ - cappedDualValue (S0M M) theta T₂| ≤
      universalDualLip_v12 * |T₁ - T₂| := by
  have h1m_pos : 0 < 1 - theta := by linarith [htheta.2]
  have hu₁ := (reducedTarget_mem_Icc_and_Ioo_v12 htheta hT₁).1
  have hu₂ := (reducedTarget_mem_Icc_and_Ioo_v12 htheta hT₂).1
  have hu₁_wide : (T₁ - theta) / (1 - theta) ∈ Set.Icc (9 / 4 : ℝ) (9 / 2) :=
    ⟨by linarith [hu₁.1], hu₁.2⟩
  have hu₂_wide : (T₂ - theta) / (1 - theta) ∈ Set.Icc (9 / 4 : ℝ) (9 / 2) :=
    ⟨by linarith [hu₂.1], hu₂.2⟩
  have hs0m_eq : S0M M \ {1} = windowSupportSet_v12 1 (M - 1) := by
    ext j
    simp only [S0M, windowSupportSet_v12, Set.mem_sdiff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    have : ((1 + (M - 1) : ℕ) : ℤ) = (M : ℤ) := by exact_mod_cast (show 1 + (M - 1) = M by omega)
    omega
  have hdiff : cappedDualValue (S0M M) theta T₁ - cappedDualValue (S0M M) theta T₂ =
      (1 - theta) *
        (dualValue (windowSupportSet_v12 1 (M - 1)) ((T₁ - theta) / (1 - theta)) -
          dualValue (windowSupportSet_v12 1 (M - 1)) ((T₂ - theta) / (1 - theta))) := by
    unfold cappedDualValue
    rw [hs0m_eq]
    ring
  rw [hdiff, abs_mul, abs_of_pos h1m_pos]
  have hwin := abs_dualValue_window_sub_le_v12 (m := 1) (M := M - 1) le_rfl (by omega)
    hu₁_wide hu₂_wide
  have hsub_u : (T₁ - theta) / (1 - theta) - (T₂ - theta) / (1 - theta) =
      (T₁ - T₂) / (1 - theta) := by ring
  rw [hsub_u, abs_div, abs_of_pos h1m_pos] at hwin
  calc (1 - theta) *
        |dualValue (windowSupportSet_v12 1 (M - 1)) ((T₁ - theta) / (1 - theta)) -
          dualValue (windowSupportSet_v12 1 (M - 1)) ((T₂ - theta) / (1 - theta))|
      ≤ (1 - theta) * (universalDualLip_v12 * (|T₁ - T₂| / (1 - theta))) :=
        mul_le_mul_of_nonneg_left hwin h1m_pos.le
    _ = universalDualLip_v12 * |T₁ - T₂| := by field_simp [h1m_pos.ne']

private theorem continuousOn_infiniteFiniteEntropy_Icc
    {alpha m : ℕ} (hm : m ≤ 2) (halpha : 10 ≤ alpha) :
    ContinuousOn (infiniteFiniteEntropy alpha m) (Set.Icc (9 / 4 : ℝ) (9 / 2)) := by
  have hconc : ∀ {u v a b : ℝ},
      u ∈ Set.Icc ((9 / 4 : ℝ) - 1 / 8) ((9 / 2 : ℝ) + 1 / 8) →
      v ∈ Set.Icc ((9 / 4 : ℝ) - 1 / 8) ((9 / 2 : ℝ) + 1 / 8) →
      0 ≤ a → 0 ≤ b → a + b = 1 →
      a * infiniteFiniteEntropy alpha m u + b * infiniteFiniteEntropy alpha m v ≤
        infiniteFiniteEntropy alpha m (a * u + b * v) := by
    intro u v a b hu hv ha hb hsum
    have hu_pad : u ∈ Set.Icc (17 / 8 : ℝ) (37 / 8) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hv_pad : v ∈ Set.Icc (17 / 8 : ℝ) (37 / 8) := ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hbu := (bddBelow_and_tilt_trap_infiniteFiniteDual hm halpha hu_pad).1
    have hbv := (bddBelow_and_tilt_trap_infiniteFiniteDual hm halpha hv_pad).1
    refine le_ciInf fun l ↦ ?_
    have e1 := mul_le_mul_of_nonneg_left (ciInf_le hbu l) ha
    have e2 := mul_le_mul_of_nonneg_left (ciInf_le hbv l) hb
    calc a * infiniteFiniteEntropy alpha m u + b * infiniteFiniteEntropy alpha m v
        ≤ a * (Real.log (infiniteFinitePartition alpha m l) - l * u) +
            b * (Real.log (infiniteFinitePartition alpha m l) - l * v) := add_le_add e1 e2
      _ = (a + b) * Real.log (infiniteFinitePartition alpha m l) -
            l * (a * u + b * v) := by ring
      _ = Real.log (infiniteFinitePartition alpha m l) - l * (a * u + b * v) := by
            rw [hsum, one_mul]
  set B_lo : ℝ := -38
  set U_hi : ℝ := Real.log (partitionFn Splus 0)
  have hbdd : ∀ t ∈ Set.Icc ((9 / 4 : ℝ) - 1 / 8) ((9 / 2 : ℝ) + 1 / 8),
      B_lo ≤ infiniteFiniteEntropy alpha m t ∧ infiniteFiniteEntropy alpha m t ≤ U_hi := by
    intro t ht
    have ht_icc : t ∈ Set.Icc (17 / 8 : ℝ) (37 / 8) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hbt := (bddBelow_and_tilt_trap_infiniteFiniteDual hm halpha ht_icc).1
    have hlo : B_lo ≤ infiniteFiniteEntropy alpha m t := by
      refine le_ciInf fun l ↦ ?_
      have htrap_pt : -38 ≤ Real.log (infiniteFinitePartition alpha m l) - l * t := by
        by_cases hl : Real.log (infiniteFinitePartition alpha m l) - l * t < -38
        · obtain ⟨habs, _⟩ := (bddBelow_and_tilt_trap_infiniteFiniteDual hm halpha ht_icc).2 hl.le
          have h0 : max 0 (8 * (-38 + 38 : ℝ)) = 0 := by norm_num
          rw [h0] at habs
          have hl0 : l = 0 := abs_nonpos_iff.mp habs
          subst hl0
          have hm_mem : m ∈ Finset.Ico m alpha := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
          have hsm : -(38 : ℝ) ≤ infiniteFiniteScore alpha m :=
            (infiniteFiniteScore_bounds_small (by omega) halpha).1
          have hsub : Real.exp (0 * (m : ℝ) + infiniteFiniteScore alpha m) ≤
              infiniteFinitePartition alpha m 0 :=
            Finset.single_le_sum (f := fun j : ℕ ↦ Real.exp (0 * (j : ℝ) + infiniteFiniteScore alpha j))
              (fun _ _ ↦ (Real.exp_pos _).le) hm_mem
          have hlog := Real.log_le_log (Real.exp_pos _) hsub
          rw [Real.log_exp] at hlog
          linarith
        · exact le_of_not_gt hl
      exact htrap_pt
    have hhi : infiniteFiniteEntropy alpha m t ≤ U_hi := by
      have h0 := ciInf_le hbt 0
      change infiniteFiniteEntropy alpha m t ≤
        Real.log (infiniteFinitePartition alpha m 0) - 0 * t at h0
      rw [zero_mul, sub_zero] at h0
      have hZ1 := Real.log_le_log (infiniteFinitePartition_pos (alpha := alpha) (m := m) (by omega) 0)
        ((infiniteFinitePartition_le_partitionFn (alpha := alpha) (m := m) 0).trans
          (partitionFn_mono (infiniteSupportSet_subset_Splus m) 0))
      dsimp [U_hi]
      linarith
    exact ⟨hlo, hhi⟩
  set K : ℝ := (U_hi - B_lo) / (1 / 8 : ℝ) + 1
  have hKpos : 0 < K := by
    have hb3 := hbdd 3 (by norm_num)
    have : 0 ≤ U_hi - B_lo := by linarith [hb3.1, hb3.2]
    dsimp [K]; positivity
  rw [Metric.continuousOn_iff]
  intro x hx eps heps
  refine ⟨eps / K, div_pos heps hKpos, fun y hy hdist ↦ ?_⟩
  rw [Real.dist_eq] at hdist ⊢
  have hlip := lipschitz_of_concave_on_padded_Icc_v12 (r_pad := 1 / 8) (by norm_num) hconc hbdd hx hy
  have h1 : ((U_hi - B_lo) / (1 / 8 : ℝ)) * |y - x| ≤ K * |y - x| := by
    dsimp [K]; linarith [abs_nonneg (y - x)]
  have h2 : K * |y - x| < K * (eps / K) := mul_lt_mul_of_pos_left hdist hKpos
  rw [mul_div_cancel₀ _ hKpos.ne'] at h2
  linarith

private theorem binEntropy_bounds_Icc_v12 {theta : ℝ} (htheta : theta ∈ Set.Icc (0 : ℝ) 1) :
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

private theorem hasDerivAt_branchObjective_v12 (c m : ℝ) {s : ℝ} (hs : 0 < s) :
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

private theorem eventually_corridor_inv_target_logLogRate_v12 (C : ℝ) (hC : 0 ≤ C) :
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

private theorem eventually_cappedInfinite_target_mem_KcapInterval (C : ℝ) (hC : 0 ≤ C) :
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
  filter_upwards [hsmall, eventually_corridor_inv_target_logLogRate_v12 C hC] with
    n hsm hInv hd s hs
  have htar := (hInv.2 s hs).2.2.2
  rw [abs_le] at htar
  unfold phaseTarget at htar
  unfold KcapInterval
  unfold deltaStar at hd
  exact ⟨by linarith [htar.1, hd.2, hsm], by linarith [htar.2, hd.1, hsm]⟩

private theorem eventually_infinitePhaseObjective_strictMonoOn_and_drop
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      ∀ m : ℕ, m ≤ 2 →
        ∀ tau ∈ Set.Icc (0 : ℝ) (Real.log 2),
          StrictMonoOn (infinitePhaseObjective m n tau)
              (Set.Icc (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
                       (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n)) ∧
            ∀ s₁ ∈ Set.Icc (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
                           (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n),
              ∀ s₂ ∈ Set.Icc (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
                             (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n),
                s₁ ≤ s₂ →
                  infinitePhaseObjective m n tau s₁ ≤
                    infinitePhaseObjective m n tau s₂ + 1 -
                      (q / 4 * (phaseNat n : ℝ) ^ 2) * (s₂ - s₁) := by
  obtain ⟨K, hKnn, hKlog⟩ := eventually_corridor_abs_log_linear C hC
  set Uent : ℝ := |Real.log (partitionFn Splus 0)| + 2
  set Ml : ℝ := max 0 (8 * (Uent + 38))
  have hMlnn : 0 ≤ Ml := le_max_left 0 _
  let C0 : ℝ := Real.log 2 + 5 + 2 * Ml + 38
  let C1 : ℝ := K + Ml
  have hC0pos : 0 < C0 := by have := Real.log_pos one_lt_two; dsimp [C0]; positivity
  have hphase10 : ∀ᶠ n : ℕ in atTop, 10 ≤ phaseNat n := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop (10 : ℝ),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact_mod_cast hn.trans hph.1
  have hphaseBig : ∀ᶠ n : ℕ in atTop, 4 * (C0 + C1) / q + 1 ≤ (phaseNat n : ℝ) := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop (4 * (C0 + C1) / q + 1),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact hn.trans hph.1
  have hc_ge2 : ∀ᶠ n : ℕ in atTop, 2 ≤ phaseRootCenter n := by
    filter_upwards [eventually_ge_atTop 100,
      eventually_phaseRoot_domain_pos_and_target_corridor,
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn100 hdom hph
    have hs0_le_a : phaseRootS0 n ≤ (phaseNat n : ℝ) := by
      rw [phaseRootS0, alphaZero_eq_phaseNat_add_delta hdom.1]
      have h2q : (1 : ℝ) < 2 / q := by
        rw [lt_div_iff₀ q_pos]; unfold q; linarith [Real.log_two_lt_d9]
      linarith [phaseDelta_lt_one n]
    have hs0_le_4L : phaseRootS0 n ≤ 4 * logOrder n := hs0_le_a.trans hph.2
    have hL_le_n8 : 8 * logOrder n ≤ (n : ℝ) := by
      have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
      have h1 : Real.log ((n : ℝ) / 16) ≤ (n : ℝ) / 16 - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have hlog16 : Real.log 16 ≤ 4 := by
        have h16e : (16 : ℝ) ≤ Real.exp 4 := by
          have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
          have he4 : (2 : ℝ) ^ 4 ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) he1 4
          rw [← Real.exp_nat_mul] at he4
          norm_num at he4
          exact he4
        exact (Real.log_le_log (by norm_num) h16e).trans_eq (Real.log_exp 4)
      rw [Real.log_div hn_pos.ne' (by norm_num)] at h1
      unfold logOrder
      have hn100' : (100 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn100
      linarith
    unfold phaseRootCenter
    rw [le_div_iff₀ hdom.2.1]
    linarith
  filter_upwards [hKlog, hphase10, hphaseBig, hc_ge2,
    eventually_corridor_inv_target_logLogRate_v12 C hC,
    eventually_phaseRootLogLogCorridor_fourSize_domain C hC,
    eventually_phaseRootLogLogCorridor_fourSize_target_mem_Icc C hC,
    eventually_five_lt_phaseNat] with
    n hLogN ha10 hBig hc2 hInv hDom hTarget hfive m hm tau htau
  set a : ℝ := (phaseNat n : ℝ)
  have haSix : (6 : ℝ) ≤ a := by
    change (6 : ℝ) ≤ (phaseNat n : ℝ); exact_mod_cast (Nat.succ_le_of_lt hfive)
  have haPos : 0 < a := by linarith
  have haSqPos : 0 < a ^ 2 := sq_pos_of_pos haPos
  -- Unified comparison helper for any `s₁ < s₂` in the corridor and `δ ∈ (0, 1]`
  have hPair : ∀ {s₁ s₂ δ : ℝ},
      s₁ ∈ Set.Icc (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
                   (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n) →
      s₂ ∈ Set.Icc (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
                   (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n) →
      s₁ < s₂ → 0 < δ → δ ≤ 1 →
      infinitePhaseObjective m n tau s₁ + (q / 4 * a ^ 2) * (s₂ - s₁) <
        infinitePhaseObjective m n tau s₂ + s₂ * δ := by
    intro s₁ s₂ δ hs₁ hs₂ hlt hδpos hδ1
    have hs₁pos : 0 < s₁ := (hDom s₁ hs₁).1
    have hs₂pos : 0 < s₂ := (hDom s₂ hs₂).1
    set T₁ : ℝ := fourSizeTarget n (phaseNat n) s₁
    set T₂ : ℝ := fourSizeTarget n (phaseNat n) s₂
    have hTK₁ : T₁ ∈ Set.Icc (9 / 4 : ℝ) (17 / 4) := hTarget s₁ hs₁
    have hTK₂ : T₂ ∈ Set.Icc (9 / 4 : ℝ) (17 / 4) := hTarget s₂ hs₂
    have hT₁_pad : T₁ ∈ Set.Icc (17 / 8 : ℝ) (37 / 8) := ⟨by linarith [hTK₁.1], by linarith [hTK₁.2]⟩
    have hT₂_pad : T₂ ∈ Set.Icc (17 / 8 : ℝ) (37 / 8) := ⟨by linarith [hTK₂.1], by linarith [hTK₂.2]⟩
    have hent₂ : infiniteFiniteEntropy (phaseNat n) m T₂ ≤ Uent - 2 := by
      have hbt := (bddBelow_and_tilt_trap_infiniteFiniteDual hm ha10 hT₂_pad).1
      have h0 := ciInf_le hbt 0
      change infiniteFiniteEntropy (phaseNat n) m T₂ ≤
        Real.log (infiniteFinitePartition (phaseNat n) m 0) - 0 * T₂ at h0
      rw [zero_mul, sub_zero] at h0
      have hZ1 := Real.log_le_log
        (infiniteFinitePartition_pos (alpha := phaseNat n) (m := m) (by omega) 0)
        ((infiniteFinitePartition_le_partitionFn (alpha := phaseNat n) (m := m) 0).trans
          (partitionFn_mono (infiniteSupportSet_subset_Splus m) 0))
      dsimp [Uent]
      linarith [le_abs_self (Real.log (partitionFn Splus 0))]
    obtain ⟨l, hlLt⟩ := exists_lt_of_ciInf_lt
      (lt_add_of_pos_right (infiniteFiniteEntropy (phaseNat n) m T₂) hδpos)
    have hlU : Real.log (infiniteFinitePartition (phaseNat n) m l) - l * T₂ ≤ Uent := by linarith
    have hLinLo : -Ml * (a + 2) - 38 ≤
        Real.log (infiniteFinitePartition (phaseNat n) m l) - l * a :=
      ((bddBelow_and_tilt_trap_infiniteFiniteDual hm ha10 hT₂_pad).2 hlU).2
    set m_slope : ℝ := profileDeficitAffineA (phaseNat n) + profileDeficitAffineB (phaseNat n) * a +
      tau + Real.log (infiniteFinitePartition (phaseNat n) m l) - l * a
    set c_const : ℝ := (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) +
      (l - profileDeficitAffineB (phaseNat n)) * (n : ℝ)
    set g : ℝ → ℝ := fun x ↦ c_const + x - x * Real.log x + m_slope * x
    have g_eq : ∀ {x : ℝ}, x ≠ 0 →
        g x = (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + x - x * Real.log x +
          x * (profileDeficitAffineA (phaseNat n) +
            profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) x +
            (Real.log (infiniteFinitePartition (phaseNat n) m l) -
              l * fourSizeTarget n (phaseNat n) x) + tau) := by
      intro x hx
      have hnx : x * ((n : ℝ) / x) = (n : ℝ) := mul_div_cancel₀ _ hx
      dsimp [g, c_const, m_slope, a]
      unfold fourSizeTarget
      field_simp [hx]
      ring
    have hAt1 : infinitePhaseObjective m n tau s₁ ≤ g s₁ := by
      rw [g_eq hs₁pos.ne']; unfold infinitePhaseObjective
      have hle1 : infiniteFiniteEntropy (phaseNat n) m T₁ ≤
          Real.log (infiniteFinitePartition (phaseNat n) m l) - l * T₁ :=
        ciInf_le (bddBelow_and_tilt_trap_infiniteFiniteDual hm ha10 hT₁_pad).1 l
      have hm1 := mul_le_mul_of_nonneg_left hle1 hs₁pos.le
      dsimp [T₁] at hm1; linarith
    have hAt2 : g s₂ - s₂ * δ < infinitePhaseObjective m n tau s₂ := by
      rw [g_eq hs₂pos.ne']; unfold infinitePhaseObjective
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
      have h3 : 4 * (C0 + C1) * a ≤ (a * q) * a := mul_le_mul_of_nonneg_right h1 haPos.le
      linarith [show 4 * ((C0 + C1) * a) = 4 * (C0 + C1) * a by ring,
        show (a * q) * a = 4 * (q / 4 * a ^ 2) by ring]
    have hSubIcc : Set.Icc s₁ s₂ ⊆ Set.Icc
        (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
        (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n) :=
      fun x hx ↦ ⟨hs₁.1.trans hx.1, hx.2.trans hs₂.2⟩
    have hHasDerivG : ∀ x ∈ Set.Icc s₁ s₂, HasDerivAt g (-Real.log x + m_slope) x :=
      fun x hx ↦ hasDerivAt_branchObjective_v12 c_const m_slope (lt_of_lt_of_le hs₁pos hx.1)
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
    linarith
  refine ⟨fun s₁ hs₁ s₂ hs₂ hlt ↦ ?_, fun s₁ hs₁ s₂ hs₂ hle ↦ ?_⟩
  · have hs₂pos : 0 < s₂ := (hDom s₂ hs₂).1
    set δ : ℝ := min 1 ((q / 8 * a ^ 2) * (s₂ - s₁) / s₂)
    have hδpos : 0 < δ := lt_min zero_lt_one
      (div_pos (mul_pos (mul_pos (div_pos q_pos (by norm_num)) haSqPos) (sub_pos.mpr hlt)) hs₂pos)
    have hs₂δ : s₂ * δ ≤ (q / 8 * a ^ 2) * (s₂ - s₁) := by
      have h := mul_le_mul_of_nonneg_left (min_le_right 1 ((q / 8 * a ^ 2) * (s₂ - s₁) / s₂)) hs₂pos.le
      rwa [mul_div_cancel₀ _ hs₂pos.ne'] at h
    have hp := hPair hs₁ hs₂ hlt hδpos (min_le_left _ _)
    have hPosGain : 0 < (q / 8 * a ^ 2) * (s₂ - s₁) :=
      mul_pos (mul_pos (div_pos q_pos (by norm_num)) haSqPos) (sub_pos.mpr hlt)
    linarith
  · rcases eq_or_lt_of_le hle with rfl | hlt
    · simp
    · have hs₂_ge1 : 1 ≤ s₂ := by linarith [(hInv.2 s₂ hs₂).1, hc2]
      have hs₂pos : 0 < s₂ := lt_of_lt_of_le zero_lt_one hs₂_ge1
      have hinv_le1 : 1 / s₂ ≤ 1 := div_le_one_of_le₀ hs₂_ge1 hs₂pos.le
      have hp := hPair hs₁ hs₂ hlt (div_pos one_pos hs₂pos) hinv_le1
      rw [mul_one_div_cancel hs₂pos.ne'] at hp
      linarith

private theorem eventually_cappedInfinitePhaseObjective_strictMonoOn_and_drop
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      phaseDelta n ∈ Set.Icc (0 : ℝ) deltaStar →
        ∀ theta ∈ Set.Icc (0 : ℝ) (1 / 20),
          ∀ tau ∈ Set.Icc (0 : ℝ) (Real.log 2),
            StrictMonoOn (cappedInfinitePhaseObjective n theta tau)
                (Set.Icc (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
                         (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n)) ∧
              ∀ s₁ ∈ Set.Icc (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
                             (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n),
                ∀ s₂ ∈ Set.Icc (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
                               (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n),
                  s₁ ≤ s₂ →
                    cappedInfinitePhaseObjective n theta tau s₁ ≤
                      cappedInfinitePhaseObjective n theta tau s₂ + 1 -
                        (q / 4 * (phaseNat n : ℝ) ^ 2) * (s₂ - s₁) := by
  obtain ⟨K, hKnn, hKlog⟩ := eventually_corridor_abs_log_linear C hC
  set Uent : ℝ := |Real.log (partitionFn Splus 0)| + 4
  set Ml : ℝ := max 0 (8 * (Uent + 38))
  have hMlnn : 0 ≤ Ml := le_max_left 0 _
  let C0 : ℝ := 2 * Real.log 2 + 5 + 2 * Ml + 38
  let C1 : ℝ := K + 2 * Ml
  have hC0pos : 0 < C0 := by have := Real.log_pos one_lt_two; dsimp [C0]; positivity
  have hphase10 : ∀ᶠ n : ℕ in atTop, 10 ≤ phaseNat n := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop (10 : ℝ),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact_mod_cast hn.trans hph.1
  have hphaseBig : ∀ᶠ n : ℕ in atTop, 4 * (C0 + C1) / q + 1 ≤ (phaseNat n : ℝ) := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop (4 * (C0 + C1) / q + 1),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact hn.trans hph.1
  have hc_ge2 : ∀ᶠ n : ℕ in atTop, 2 ≤ phaseRootCenter n := by
    filter_upwards [eventually_ge_atTop 100,
      eventually_phaseRoot_domain_pos_and_target_corridor,
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn100 hdom hph
    have hs0_le_a : phaseRootS0 n ≤ (phaseNat n : ℝ) := by
      rw [phaseRootS0, alphaZero_eq_phaseNat_add_delta hdom.1]
      have h2q : (1 : ℝ) < 2 / q := by
        rw [lt_div_iff₀ q_pos]; unfold q; linarith [Real.log_two_lt_d9]
      linarith [phaseDelta_lt_one n]
    have hs0_le_4L : phaseRootS0 n ≤ 4 * logOrder n := hs0_le_a.trans hph.2
    have hL_le_n8 : 8 * logOrder n ≤ (n : ℝ) := by
      have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
      have h1 : Real.log ((n : ℝ) / 16) ≤ (n : ℝ) / 16 - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have hlog16 : Real.log 16 ≤ 4 := by
        have h16e : (16 : ℝ) ≤ Real.exp 4 := by
          have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
          have he4 : (2 : ℝ) ^ 4 ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) he1 4
          rw [← Real.exp_nat_mul] at he4
          norm_num at he4
          exact he4
        exact (Real.log_le_log (by norm_num) h16e).trans_eq (Real.log_exp 4)
      rw [Real.log_div hn_pos.ne' (by norm_num)] at h1
      unfold logOrder
      have hn100' : (100 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn100
      linarith
    unfold phaseRootCenter
    rw [le_div_iff₀ hdom.2.1]
    linarith
  filter_upwards [hKlog, hphase10, hphaseBig, hc_ge2,
    eventually_corridor_inv_target_logLogRate_v12 C hC,
    eventually_phaseRootLogLogCorridor_fourSize_domain C hC,
    eventually_cappedInfinite_target_mem_KcapInterval C hC,
    eventually_five_lt_phaseNat] with
    n hLogN ha10 hBig hc2 hInv hDom hKcap hfive hd theta htheta tau htau
  set a : ℝ := (phaseNat n : ℝ)
  have haSix : (6 : ℝ) ≤ a := by
    change (6 : ℝ) ≤ (phaseNat n : ℝ); exact_mod_cast (Nat.succ_le_of_lt hfive)
  have haPos : 0 < a := by linarith
  have haSqPos : 0 < a ^ 2 := sq_pos_of_pos haPos
  have h1m_pos : 0 < 1 - theta := by linarith [htheta.2]
  have h1m_le1 : 1 - theta ≤ 1 := by linarith [htheta.1]
  have hPair : ∀ {s₁ s₂ δ : ℝ},
      s₁ ∈ Set.Icc (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
                   (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n) →
      s₂ ∈ Set.Icc (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
                   (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n) →
      s₁ < s₂ → 0 < δ → δ ≤ 1 →
      cappedInfinitePhaseObjective n theta tau s₁ + (q / 4 * a ^ 2) * (s₂ - s₁) <
        cappedInfinitePhaseObjective n theta tau s₂ + s₂ * δ := by
    intro s₁ s₂ δ hs₁ hs₂ hlt hδpos hδ1
    have hs₁pos : 0 < s₁ := (hDom s₁ hs₁).1
    have hs₂pos : 0 < s₂ := (hDom s₂ hs₂).1
    set T₁ : ℝ := fourSizeTarget n (phaseNat n) s₁
    set T₂ : ℝ := fourSizeTarget n (phaseNat n) s₂
    have hTK₁ : T₁ ∈ KcapInterval := hKcap hd s₁ hs₁
    have hTK₂ : T₂ ∈ KcapInterval := hKcap hd s₂ hs₂
    set u₁ : ℝ := (T₁ - theta) / (1 - theta)
    set u₂ : ℝ := (T₂ - theta) / (1 - theta)
    obtain ⟨hu₁_icc, _⟩ := reducedTarget_mem_Icc_and_Ioo_v12 htheta hTK₁
    obtain ⟨hu₂_icc, _⟩ := reducedTarget_mem_Icc_and_Ioo_v12 htheta hTK₂
    have hu₁_pad : u₁ ∈ Set.Icc (17 / 8 : ℝ) (37 / 8) := ⟨by linarith [hu₁_icc.1], by linarith [hu₁_icc.2]⟩
    have hu₂_pad : u₂ ∈ Set.Icc (17 / 8 : ℝ) (37 / 8) := ⟨by linarith [hu₂_icc.1], by linarith [hu₂_icc.2]⟩
    have hent₂ : infiniteFiniteEntropy (phaseNat n) 2 u₂ ≤ Uent - 4 := by
      have hbt := (bddBelow_and_tilt_trap_infiniteFiniteDual (le_rfl : 2 ≤ 2) ha10 hu₂_pad).1
      have h0 := ciInf_le hbt 0
      change infiniteFiniteEntropy (phaseNat n) 2 u₂ ≤
        Real.log (infiniteFinitePartition (phaseNat n) 2 0) - 0 * u₂ at h0
      rw [zero_mul, sub_zero] at h0
      have hZ1 := Real.log_le_log
        (infiniteFinitePartition_pos (alpha := phaseNat n) (m := 2) (by omega) 0)
        ((infiniteFinitePartition_le_partitionFn (alpha := phaseNat n) (m := 2) 0).trans
          (partitionFn_mono (infiniteSupportSet_subset_Splus 2) 0))
      dsimp [Uent]
      linarith [le_abs_self (Real.log (partitionFn Splus 0))]
    have hδ_div_le : δ / (1 - theta) ≤ 2 := by
      rw [div_le_iff₀ h1m_pos]; linarith [htheta.2]
    obtain ⟨l, hlLt⟩ := exists_lt_of_ciInf_lt
      (lt_add_of_pos_right (infiniteFiniteEntropy (phaseNat n) 2 u₂) (div_pos hδpos h1m_pos))
    have hlU : Real.log (infiniteFinitePartition (phaseNat n) 2 l) - l * u₂ ≤ Uent := by linarith
    obtain ⟨hl_abs, hLinLo_raw⟩ :=
      (bddBelow_and_tilt_trap_infiniteFiniteDual (le_rfl : 2 ≤ 2) ha10 hu₂_pad).2 hlU
    set m_slope : ℝ := profileDeficitAffineA (phaseNat n) + profileDeficitAffineB (phaseNat n) * a +
      tau + binEntropy theta - Real.log 2 / 2 * theta +
      (1 - theta) * Real.log (infiniteFinitePartition (phaseNat n) 2 l) - l * (a - theta)
    set c_const : ℝ := (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) +
      (l - profileDeficitAffineB (phaseNat n)) * (n : ℝ)
    set g : ℝ → ℝ := fun x ↦ c_const + x - x * Real.log x + m_slope * x
    have g_eq : ∀ {x : ℝ}, x ≠ 0 →
        g x = (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + x - x * Real.log x +
          x * (profileDeficitAffineA (phaseNat n) +
            profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) x +
            (binEntropy theta - Real.log 2 / 2 * theta +
              (1 - theta) *
                (Real.log (infiniteFinitePartition (phaseNat n) 2 l) -
                  l * ((fourSizeTarget n (phaseNat n) x - theta) / (1 - theta)))) + tau) := by
      intro x hx
      dsimp [g, c_const, m_slope, a]
      unfold fourSizeTarget
      field_simp [hx, h1m_pos.ne']
      ring
    have hAt1 : cappedInfinitePhaseObjective n theta tau s₁ ≤ g s₁ := by
      rw [g_eq hs₁pos.ne']; unfold cappedInfinitePhaseObjective cappedInfiniteFiniteEntropy
      have hle1 : infiniteFiniteEntropy (phaseNat n) 2 u₁ ≤
          Real.log (infiniteFinitePartition (phaseNat n) 2 l) - l * u₁ :=
        ciInf_le (bddBelow_and_tilt_trap_infiniteFiniteDual (le_rfl : 2 ≤ 2) ha10 hu₁_pad).1 l
      have hm1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle1 h1m_pos.le) hs₁pos.le
      dsimp [u₁, T₁] at hm1; linarith
    have hAt2 : g s₂ - s₂ * δ < cappedInfinitePhaseObjective n theta tau s₂ := by
      rw [g_eq hs₂pos.ne']; unfold cappedInfinitePhaseObjective cappedInfiniteFiniteEntropy
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
      have h3 : 4 * (C0 + C1) * a ≤ (a * q) * a := mul_le_mul_of_nonneg_right h1 haPos.le
      linarith [show 4 * ((C0 + C1) * a) = 4 * (C0 + C1) * a by ring,
        show (a * q) * a = 4 * (q / 4 * a ^ 2) by ring]
    have hbin_nn : 0 ≤ binEntropy theta :=
      (binEntropy_bounds_Icc_v12 ⟨htheta.1, by linarith [htheta.2]⟩).1
    have hcap_lin_lo :
        -2 * Ml * a - 2 * Ml - 38 ≤
          (1 - theta) * Real.log (infiniteFinitePartition (phaseNat n) 2 l) - l * (a - theta) := by
      have hid : (1 - theta) * Real.log (infiniteFinitePartition (phaseNat n) 2 l) - l * (a - theta) =
          (1 - theta) * (Real.log (infiniteFinitePartition (phaseNat n) 2 l) - l * a) -
            theta * l * (a - 1) := by ring
      rw [hid]
      have hm1 :
          (1 - theta) * (-Ml * (a + 2) - 38) ≤
            (1 - theta) * (Real.log (infiniteFinitePartition (phaseNat n) 2 l) - l * a) :=
        mul_le_mul_of_nonneg_left hLinLo_raw h1m_pos.le
      have hlo1 : -(Ml * (a + 2) + 38) ≤ (1 - theta) * (-Ml * (a + 2) - 38) := by
        have hnn : 0 ≤ Ml * (a + 2) + 38 := by dsimp [Ml]; positivity
        have hm_le := mul_le_mul_of_nonneg_right h1m_le1 hnn
        linarith
      have hl_th : |theta * l * (a - 1)| ≤ Ml * a := by
        rw [abs_mul, abs_mul, abs_of_nonneg htheta.1, abs_of_pos (by linarith : 0 < a - 1)]
        calc theta * |l| * (a - 1)
            ≤ (1 * Ml) * a := by
              refine mul_le_mul (mul_le_mul (by linarith [htheta.2]) hl_abs (abs_nonneg _) zero_le_one)
                (by linarith) (by linarith) (mul_nonneg zero_le_one hMlnn)
          _ = Ml * a := by ring
      have hexp_lo1 : -(Ml * (a + 2) + 38) - Ml * a = -2 * Ml * a - 2 * Ml - 38 := by ring
      linarith [(abs_le.mp hl_th).2, hexp_lo1]
    have hSubIcc : Set.Icc s₁ s₂ ⊆ Set.Icc
        (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
        (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n) :=
      fun x hx ↦ ⟨hs₁.1.trans hx.1, hx.2.trans hs₂.2⟩
    have hHasDerivG : ∀ x ∈ Set.Icc s₁ s₂, HasDerivAt g (-Real.log x + m_slope) x :=
      fun x hx ↦ hasDerivAt_branchObjective_v12 c_const m_slope (lt_of_lt_of_le hs₁pos hx.1)
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
            ((1 - theta) * Real.log (infiniteFinitePartition (phaseNat n) 2 l) - l * (a - theta)) := by
        dsimp [m_slope]; ring
      have hC_comb : C0 + C1 * a =
          2 * Real.log 2 + 5 + 2 * Ml + 38 + K * a + 2 * Ml * a := by
        dsimp [C0, C1]; ring
      rw [hm_def]
      linarith [htau.1, hAff, hRemLe, hbin_nn, hcap_lin_lo, hlogx, hq_th, hC_comb]
    have hIncG := derivative_lower_bound_mul_sub_le_sub hlt.le hContG hDiffG hSlopeG
    linarith
  refine ⟨fun s₁ hs₁ s₂ hs₂ hlt ↦ ?_, fun s₁ hs₁ s₂ hs₂ hle ↦ ?_⟩
  · have hs₂pos : 0 < s₂ := (hDom s₂ hs₂).1
    set δ : ℝ := min 1 ((q / 8 * a ^ 2) * (s₂ - s₁) / s₂)
    have hδpos : 0 < δ := lt_min zero_lt_one
      (div_pos (mul_pos (mul_pos (div_pos q_pos (by norm_num)) haSqPos) (sub_pos.mpr hlt)) hs₂pos)
    have hs₂δ : s₂ * δ ≤ (q / 8 * a ^ 2) * (s₂ - s₁) := by
      have h := mul_le_mul_of_nonneg_left (min_le_right 1 ((q / 8 * a ^ 2) * (s₂ - s₁) / s₂)) hs₂pos.le
      rwa [mul_div_cancel₀ _ hs₂pos.ne'] at h
    have hp := hPair hs₁ hs₂ hlt hδpos (min_le_left _ _)
    have hPosGain : 0 < (q / 8 * a ^ 2) * (s₂ - s₁) :=
      mul_pos (mul_pos (div_pos q_pos (by norm_num)) haSqPos) (sub_pos.mpr hlt)
    linarith
  · rcases eq_or_lt_of_le hle with rfl | hlt
    · simp
    · have hs₂_ge1 : 1 ≤ s₂ := by linarith [(hInv.2 s₂ hs₂).1, hc2]
      have hs₂pos : 0 < s₂ := lt_of_lt_of_le zero_lt_one hs₂_ge1
      have hinv_le1 : 1 / s₂ ≤ 1 := div_le_one_of_le₀ hs₂_ge1 hs₂pos.le
      have hp := hPair hs₁ hs₂ hlt (div_pos one_pos hs₂pos) hinv_le1
      rw [mul_one_div_cancel hs₂pos.ne'] at hp
      linarith

/-- **Lemma 3.1 infinite-support corridor roots (`∃!`) and `(3.6)` location (`S_{≥ 0}, S_{≥ 1}, S_{≥ 2}`):**
there exist `C > 0` and `A_* > 0` such that eventually (uniformly over `m ≤ 2` and `τ ∈ [0, log 2]`):
1. `𝓛_{S_{≥ m}}(n, ·) + τ ·` is strictly increasing on `[c_n - C Δ_n, c_n + C Δ_n]`,
2. `𝓛_{S_{≥ m}}(n, r) + τ r = 0` has a unique solution `r` in `(c_n - C Δ_n, c_n + C Δ_n)`,
3. that root satisfies `|n / r - s₀| ≤ A_* log log n / log n` and
   `|(α - n / r) - T_{δ_n}| ≤ A_* log log n / log n` (`(3.6)`). -/
theorem exists_pos_eventually_existsUnique_infinitePhaseObjective_zero_logLogCorridor :
    ∃ C A_star : ℝ, 0 < C ∧ 0 < A_star ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ m : ℕ, m ≤ 2 →
          ∀ tau ∈ Set.Icc (0 : ℝ) (Real.log 2),
            let F_fin : ℝ → ℝ := fun T ↦ ⨅ l : ℝ,
              (Real.log (∑ i ∈ Finset.Ico m (phaseNat n),
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
  let Gbound : ℝ := Real.log 2 + 5 * Mtilt + 2 * |Real.log (partitionFn Splus 0)| + 40
  have hLLBig : ∀ᶠ n : ℕ in atTop, max 1 (2 * Gbound + 1) ≤ logLogOrder n :=
    tendsto_logLogOrder_atTop.eventually_ge_atTop _
  have hphaseN : ∀ᶠ n : ℕ in atTop, max Ntilt 10 ≤ phaseNat n := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop ((max Ntilt 10 : ℕ) : ℝ),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact_mod_cast hn.trans hph.1
  filter_upwards [hB.bound, hLLBig, hphaseN,
    eventually_infinitePhaseObjective_strictMonoOn_and_drop C hCpos.le,
    eventually_corridor_inv_target_logLogRate_v12 C hCpos.le,
    eventually_phaseRootLogLogCorridor_fourSize_domain C hCpos.le,
    eventually_phaseRootLogLogCorridor_fourSize_target_mem_Icc C hCpos.le,
    eventually_unrestrictedPhaseObjective_deriv_logLogCorridor_lower C hCpos.le,
    eventually_phaseRoot_domain_pos_and_target_corridor,
    eventually_five_lt_phaseNat] with
    n hcenterBound hLL hphN hStrictDrop hInvRate hdomain htarget hderiv hcenterDom hfive m hm tau htau
  intro F_fin obj
  have hobj_eq : obj = infinitePhaseObjective m n tau := rfl
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
  have ha10 : 10 ≤ phaseNat n := (le_max_right Ntilt 10).trans hphN
  have hCont : ContinuousOn (infinitePhaseObjective m n tau) (Set.Icc (s0 - Delta) (s0 + Delta)) := by
    have hPosOn : ∀ s ∈ Set.Icc (s0 - Delta) (s0 + Delta), s ≠ 0 := by
      intro s hs; linarith [(hInvRate.2 s hs).1, hs0Pos]
    have hTargetCont : ContinuousOn (fourSizeTarget n (phaseNat n))
        (Set.Icc (s0 - Delta) (s0 + Delta)) := by
      unfold fourSizeTarget
      exact continuousOn_const.sub (continuousOn_const.div continuousOn_id hPosOn)
    have hMaps : MapsTo (fourSizeTarget n (phaseNat n))
        (Set.Icc (s0 - Delta) (s0 + Delta)) (Set.Icc (9 / 4 : ℝ) (9 / 2)) := by
      intro s hs
      have ht := htarget s (by simpa [s0, Delta] using hs)
      exact ⟨ht.1, by linarith [ht.2]⟩
    have hEntCont := (continuousOn_infiniteFiniteEntropy_Icc hm ha10).comp hTargetCont hMaps
    unfold infinitePhaseObjective
    exact (((continuousOn_const.add continuousOn_id).sub
      (continuousOn_id.mul (continuousOn_id.log hPosOn))).add
      (continuousOn_id.mul (((continuousOn_const.add
        (continuousOn_const.mul hTargetCont)).add hEntCont).add continuousOn_const)))
  have hShiftBound : ∀ s ∈ Set.Icc (s0 - Delta) (s0 + Delta),
      |s * (tau - finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) s) +
          infiniteFiniteEntropy (phaseNat n) m (fourSizeTarget n (phaseNat n) s))| ≤
        logLogOrder n * s0 := by
    intro s hs
    have hsPos : 0 < s := by linarith [(hInvRate.2 s hs).1, hs0Pos]
    have hsLe2 : s ≤ 2 * s0 := (hInvRate.2 s hs).2.1
    set T : ℝ := fourSizeTarget n (phaseNat n) s
    have hTK : T ∈ Set.Icc (9 / 4 : ℝ) (17 / 4) := htarget s (by simpa [s0, Delta] using hs)
    have hT25 : T ∈ Set.Ioo (2 : ℝ) 5 := ⟨by linarith [hTK.1], by linarith [hTK.2]⟩
    have hT_pad : T ∈ Set.Icc (17 / 8 : ℝ) (37 / 8) := ⟨by linarith [hTK.1], by linarith [hTK.2]⟩
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
    have hInfHi : infiniteFiniteEntropy (phaseNat n) m T ≤ |Real.log (partitionFn Splus 0)| := by
      have hbt := (bddBelow_and_tilt_trap_infiniteFiniteDual hm ha10 hT_pad).1
      have h0 := ciInf_le hbt 0
      change infiniteFiniteEntropy (phaseNat n) m T ≤
        Real.log (infiniteFinitePartition (phaseNat n) m 0) - 0 * T at h0
      rw [zero_mul, sub_zero] at h0
      have hZ1 := Real.log_le_log
        (infiniteFinitePartition_pos (alpha := phaseNat n) (m := m) (by omega) 0)
        ((infiniteFinitePartition_le_partitionFn (alpha := phaseNat n) (m := m) 0).trans
          (partitionFn_mono (infiniteSupportSet_subset_Splus m) 0))
      linarith [le_abs_self (Real.log (partitionFn Splus 0))]
    have hInfLo : -38 ≤ infiniteFiniteEntropy (phaseNat n) m T := by
      refine le_ciInf fun l ↦ ?_
      by_cases hl : Real.log (infiniteFinitePartition (phaseNat n) m l) - l * T < -38
      · obtain ⟨habs, _⟩ := (bddBelow_and_tilt_trap_infiniteFiniteDual hm ha10 hT_pad).2 hl.le
        have h0 : max 0 (8 * (-38 + 38 : ℝ)) = 0 := by norm_num
        rw [h0] at habs
        have hl0 : l = 0 := abs_nonpos_iff.mp habs
        subst hl0
        have hm_mem : m ∈ Finset.Ico m (phaseNat n) := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
        have hsm := (infiniteFiniteScore_bounds_small (alpha := phaseNat n) (i := m) (by omega) ha10).1
        have hsub : Real.exp (0 * (m : ℝ) + infiniteFiniteScore (phaseNat n) m) ≤
            infiniteFinitePartition (phaseNat n) m 0 :=
          Finset.single_le_sum (f := fun j : ℕ ↦ Real.exp (0 * (j : ℝ) + infiniteFiniteScore (phaseNat n) j))
            (fun _ _ ↦ (Real.exp_pos _).le) hm_mem
        have hlog := Real.log_le_log (Real.exp_pos _) hsub
        rw [Real.log_exp] at hlog
        linarith
      · exact le_of_not_gt hl
    have hInnerAbs :
        |tau - finiteUnrestrictedDeficitEntropy (phaseNat n) T +
          infiniteFiniteEntropy (phaseNat n) m T| ≤ Gbound := by
      rw [abs_le]
      dsimp [Gbound]
      exact ⟨by linarith [htau.1, hUnrestHi, hInfLo, hMtiltnn, Real.log_pos one_lt_two,
          abs_nonneg (Real.log (partitionFn Splus 0))],
        by linarith [htau.2, hUnrestLo, hInfHi, abs_nonneg (Real.log (partitionFn Splus 0))]⟩
    rw [abs_mul, abs_of_pos hsPos]
    calc s * |tau - finiteUnrestrictedDeficitEntropy (phaseNat n) T +
            infiniteFiniteEntropy (phaseNat n) m T|
        ≤ (2 * s0) * Gbound :=
          mul_le_mul hsLe2 hInnerAbs (abs_nonneg _) (mul_pos two_pos hs0Pos).le
      _ ≤ logLogOrder n * s0 := by
          have := mul_le_mul_of_nonneg_right hLLG hs0Pos.le
          linarith
  have hDiffId : ∀ {s : ℝ}, s ≠ 0 →
      infinitePhaseObjective m n tau s =
        unrestrictedPhaseObjective n s +
          s * (tau - finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) s) +
            infiniteFiniteEntropy (phaseNat n) m (fourSizeTarget n (phaseNat n) s)) := by
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
    unfold infinitePhaseObjective fourSizeTarget profileDeficitTarget
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
  have hB_pos_ll : 0 < B * logLogOrder n * s0 := mul_pos (mul_pos hBpos hLLPos) hs0Pos
  have hNegLeft : infinitePhaseObjective m n tau (s0 - Delta) < 0 := by
    have hsL_mem : s0 - Delta ∈ Set.Icc (s0 - Delta) (s0 + Delta) := ⟨le_rfl, by linarith⟩
    have hsL_pos : 0 < s0 - Delta := by linarith [(hInvRate.2 _ hsL_mem).1, hs0Pos]
    rw [hDiffId hsL_pos.ne']
    have hsh := (abs_le.mp (hShiftBound (s0 - Delta) hsL_mem)).2
    have hc_hi := (abs_le.mp hCenterAbs).2
    have hpos_ll : 0 < logLogOrder n * s0 := mul_pos hLLPos hs0Pos
    linarith
  have hPosRight : 0 < infinitePhaseObjective m n tau (s0 + Delta) := by
    have hsR_mem : s0 + Delta ∈ Set.Icc (s0 - Delta) (s0 + Delta) := ⟨by linarith, le_rfl⟩
    have hsR_pos : 0 < s0 + Delta := by linarith
    rw [hDiffId hsR_pos.ne']
    have hsh := (abs_le.mp (hShiftBound (s0 + Delta) hsR_mem)).1
    have hc_lo := (abs_le.mp hCenterAbs).1
    have hpos_ll : 0 < logLogOrder n * s0 := mul_pos hLLPos hs0Pos
    linarith
  have hStrict_n := (hStrictDrop m hm tau htau).1
  refine ⟨hStrict_n, ?_, ?_⟩
  · have hivt : (0 : ℝ) ∈ infinitePhaseObjective m n tau '' Set.Icc (s0 - Delta) (s0 + Delta) :=
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

/-- **Lemma 3.1 capped infinite-support corridor roots (`∃!`) and `(3.6)` location (`S_{≥ 1}^{=ϑ}`):**
there exist `C > 0` and `A_* > 0` such that eventually whenever `δ_n ∈ [0, δ_*]`, uniformly over
`ϑ ∈ [0, 1/20]` and `τ ∈ [0, log 2]`:
1. `𝓛_{S_{≥ 1}}^{=ϑ}(n, ·) + τ ·` is strictly increasing on `[c_n - C Δ_n, c_n + C Δ_n]`,
2. `𝓛_{S_{≥ 1}}^{=ϑ}(n, r) + τ r = 0` has a unique solution `r` in `(c_n - C Δ_n, c_n + C Δ_n)`,
3. that root satisfies `|n / r - s₀| ≤ A_* log log n / log n` and
   `|(α - n / r) - T_{δ_n}| ≤ A_* log log n / log n` (`(3.6)`). -/
theorem exists_pos_eventually_existsUnique_cappedInfinitePhaseObjective_zero_logLogCorridor :
    ∃ C A_star : ℝ, 0 < C ∧ 0 < A_star ∧
      ∀ᶠ n : ℕ in atTop,
        phaseDelta n ∈ Set.Icc (0 : ℝ) deltaStar →
          ∀ theta ∈ Set.Icc (0 : ℝ) (1 / 20),
            ∀ tau ∈ Set.Icc (0 : ℝ) (Real.log 2),
              let F_cap_fin : ℝ → ℝ := fun T ↦
                binEntropy theta - Real.log 2 / 2 * theta +
                  (1 - theta) * (⨅ l : ℝ,
                    (Real.log (∑ i ∈ Finset.Ico 2 (phaseNat n),
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
  let Gbound : ℝ := 2 * Real.log 2 + 5 * Mtilt + 2 * |Real.log (partitionFn Splus 0)| + 42
  have hLLBig : ∀ᶠ n : ℕ in atTop, max 1 (2 * Gbound + 1) ≤ logLogOrder n :=
    tendsto_logLogOrder_atTop.eventually_ge_atTop _
  have hphaseN : ∀ᶠ n : ℕ in atTop, max Ntilt 10 ≤ phaseNat n := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop ((max Ntilt 10 : ℕ) : ℝ),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact_mod_cast hn.trans hph.1
  filter_upwards [hB.bound, hLLBig, hphaseN,
    eventually_cappedInfinitePhaseObjective_strictMonoOn_and_drop C hCpos.le,
    eventually_corridor_inv_target_logLogRate_v12 C hCpos.le,
    eventually_phaseRootLogLogCorridor_fourSize_domain C hCpos.le,
    eventually_phaseRootLogLogCorridor_fourSize_target_mem_Icc C hCpos.le,
    eventually_cappedInfinite_target_mem_KcapInterval C hCpos.le,
    eventually_unrestrictedPhaseObjective_deriv_logLogCorridor_lower C hCpos.le,
    eventually_phaseRoot_domain_pos_and_target_corridor,
    eventually_five_lt_phaseNat] with
    n hcenterBound hLL hphN hStrictDrop hInvRate hdomain htarget hKcap hderiv hcenterDom hfive
    hd theta htheta tau htau
  intro F_cap_fin obj
  have hobj_eq : obj = cappedInfinitePhaseObjective n theta tau := rfl
  rw [hobj_eq]
  clear hobj_eq obj F_cap_fin
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
  have ha10 : 10 ≤ phaseNat n := (le_max_right Ntilt 10).trans hphN
  have h1m_pos : 0 < 1 - theta := by linarith [htheta.2]
  have h1m_le1 : 1 - theta ≤ 1 := by linarith [htheta.1]
  have hCont : ContinuousOn (cappedInfinitePhaseObjective n theta tau)
      (Set.Icc (s0 - Delta) (s0 + Delta)) := by
    have hPosOn : ∀ s ∈ Set.Icc (s0 - Delta) (s0 + Delta), s ≠ 0 := by
      intro s hs; linarith [(hInvRate.2 s hs).1, hs0Pos]
    have hTargetCont : ContinuousOn (fourSizeTarget n (phaseNat n))
        (Set.Icc (s0 - Delta) (s0 + Delta)) := by
      unfold fourSizeTarget
      exact continuousOn_const.sub (continuousOn_const.div continuousOn_id hPosOn)
    have hRedCont : ContinuousOn (fun s : ℝ ↦ (fourSizeTarget n (phaseNat n) s - theta) / (1 - theta))
        (Set.Icc (s0 - Delta) (s0 + Delta)) :=
      (hTargetCont.sub continuousOn_const).div_const (1 - theta)
    have hMaps : MapsTo (fun s : ℝ ↦ (fourSizeTarget n (phaseNat n) s - theta) / (1 - theta))
        (Set.Icc (s0 - Delta) (s0 + Delta)) (Set.Icc (9 / 4 : ℝ) (9 / 2)) := by
      intro s hs
      have htk := hKcap hd s (by simpa [s0, Delta] using hs)
      have hu := (reducedTarget_mem_Icc_and_Ioo_v12 htheta htk).1
      exact ⟨by linarith [hu.1], hu.2⟩
    have hTailCont := (continuousOn_infiniteFiniteEntropy_Icc (le_rfl : 2 ≤ 2) ha10).comp hRedCont hMaps
    have hCapCont : ContinuousOn
        (fun s : ℝ ↦ cappedInfiniteFiniteEntropy (phaseNat n) theta (fourSizeTarget n (phaseNat n) s))
        (Set.Icc (s0 - Delta) (s0 + Delta)) :=
      continuousOn_const.add (continuousOn_const.mul hTailCont)
    unfold cappedInfinitePhaseObjective
    exact (((continuousOn_const.add continuousOn_id).sub
      (continuousOn_id.mul (continuousOn_id.log hPosOn))).add
      (continuousOn_id.mul (((continuousOn_const.add
        (continuousOn_const.mul hTargetCont)).add hCapCont).add continuousOn_const)))
  have hShiftBound : ∀ s ∈ Set.Icc (s0 - Delta) (s0 + Delta),
      |s * (tau - finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) s) +
          cappedInfiniteFiniteEntropy (phaseNat n) theta (fourSizeTarget n (phaseNat n) s))| ≤
        logLogOrder n * s0 := by
    intro s hs
    have hsPos : 0 < s := by linarith [(hInvRate.2 s hs).1, hs0Pos]
    have hsLe2 : s ≤ 2 * s0 := (hInvRate.2 s hs).2.1
    set T : ℝ := fourSizeTarget n (phaseNat n) s
    have hTK : T ∈ Set.Icc (9 / 4 : ℝ) (17 / 4) := htarget s (by simpa [s0, Delta] using hs)
    have hT25 : T ∈ Set.Ioo (2 : ℝ) 5 := ⟨by linarith [hTK.1], by linarith [hTK.2]⟩
    have hTKcap : T ∈ KcapInterval := hKcap hd s (by simpa [s0, Delta] using hs)
    set u : ℝ := (T - theta) / (1 - theta)
    obtain ⟨hu_icc, _⟩ := reducedTarget_mem_Icc_and_Ioo_v12 htheta hTKcap
    have hu_pad : u ∈ Set.Icc (17 / 8 : ℝ) (37 / 8) := ⟨by linarith [hu_icc.1], by linarith [hu_icc.2]⟩
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
    have hTailHi : infiniteFiniteEntropy (phaseNat n) 2 u ≤ |Real.log (partitionFn Splus 0)| := by
      have hbt := (bddBelow_and_tilt_trap_infiniteFiniteDual (le_rfl : 2 ≤ 2) ha10 hu_pad).1
      have h0 := ciInf_le hbt 0
      change infiniteFiniteEntropy (phaseNat n) 2 u ≤
        Real.log (infiniteFinitePartition (phaseNat n) 2 0) - 0 * u at h0
      rw [zero_mul, sub_zero] at h0
      have hZ1 := Real.log_le_log
        (infiniteFinitePartition_pos (alpha := phaseNat n) (m := 2) (by omega) 0)
        ((infiniteFinitePartition_le_partitionFn (alpha := phaseNat n) (m := 2) 0).trans
          (partitionFn_mono (infiniteSupportSet_subset_Splus 2) 0))
      linarith [le_abs_self (Real.log (partitionFn Splus 0))]
    have hTailLo : -38 ≤ infiniteFiniteEntropy (phaseNat n) 2 u := by
      refine le_ciInf fun l ↦ ?_
      by_cases hl : Real.log (infiniteFinitePartition (phaseNat n) 2 l) - l * u < -38
      · obtain ⟨habs, _⟩ :=
          (bddBelow_and_tilt_trap_infiniteFiniteDual (le_rfl : 2 ≤ 2) ha10 hu_pad).2 hl.le
        have h0 : max 0 (8 * (-38 + 38 : ℝ)) = 0 := by norm_num
        rw [h0] at habs
        have hl0 : l = 0 := abs_nonpos_iff.mp habs
        subst hl0
        have h2_mem : 2 ∈ Finset.Ico 2 (phaseNat n) := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
        have hs2 := (infiniteFiniteScore_bounds_small (alpha := phaseNat n) (i := 2) (by omega) ha10).1
        have hsub : Real.exp (0 * (2 : ℝ) + infiniteFiniteScore (phaseNat n) 2) ≤
            infiniteFinitePartition (phaseNat n) 2 0 :=
          Finset.single_le_sum (f := fun j : ℕ ↦ Real.exp (0 * (j : ℝ) + infiniteFiniteScore (phaseNat n) j))
            (fun _ _ ↦ (Real.exp_pos _).le) h2_mem
        have hlog := Real.log_le_log (Real.exp_pos _) hsub
        rw [Real.log_exp] at hlog
        linarith
      · exact le_of_not_gt hl
    have hbin_bds := binEntropy_bounds_Icc_v12 ⟨htheta.1, by linarith [htheta.2]⟩
    have htail_abs : |(1 - theta) * infiniteFiniteEntropy (phaseNat n) 2 u| ≤
        |Real.log (partitionFn Splus 0)| + 38 := by
      rw [abs_mul, abs_of_pos h1m_pos]
      have habs_t : |infiniteFiniteEntropy (phaseNat n) 2 u| ≤
          |Real.log (partitionFn Splus 0)| + 38 :=
        abs_le.mpr ⟨by linarith [abs_nonneg (Real.log (partitionFn Splus 0))], by linarith⟩
      calc (1 - theta) * |infiniteFiniteEntropy (phaseNat n) 2 u|
          ≤ 1 * (|Real.log (partitionFn Splus 0)| + 38) :=
            mul_le_mul h1m_le1 habs_t (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    have hInnerAbs :
        |tau - finiteUnrestrictedDeficitEntropy (phaseNat n) T +
          cappedInfiniteFiniteEntropy (phaseNat n) theta T| ≤ Gbound := by
      unfold cappedInfiniteFiniteEntropy
      rw [abs_le]
      dsimp [Gbound, u] at htail_abs ⊢
      have hq_th : Real.log 2 / 2 * theta ≤ Real.log 2 := by
        have := mul_le_mul_of_nonneg_left htheta.2 (div_pos (Real.log_pos one_lt_two) two_pos).le
        linarith [Real.log_pos one_lt_two]
      have hq_th_nn : 0 ≤ Real.log 2 / 2 * theta :=
        mul_nonneg (div_nonneg (Real.log_pos one_lt_two).le zero_le_two) htheta.1
      exact ⟨by linarith [htau.1, hUnrestHi, hbin_bds.1, (abs_le.mp htail_abs).1, hq_th,
          hMtiltnn, Real.log_pos one_lt_two, abs_nonneg (Real.log (partitionFn Splus 0))],
        by linarith [htau.2, hUnrestLo, hbin_bds.2, (abs_le.mp htail_abs).2, hq_th_nn,
          Real.log_pos one_lt_two, abs_nonneg (Real.log (partitionFn Splus 0))]⟩
    rw [abs_mul, abs_of_pos hsPos]
    calc s * |tau - finiteUnrestrictedDeficitEntropy (phaseNat n) T +
            cappedInfiniteFiniteEntropy (phaseNat n) theta T|
        ≤ (2 * s0) * Gbound :=
          mul_le_mul hsLe2 hInnerAbs (abs_nonneg _) (mul_pos two_pos hs0Pos).le
      _ ≤ logLogOrder n * s0 := by
          have := mul_le_mul_of_nonneg_right hLLG hs0Pos.le
          linarith
  have hDiffId : ∀ {s : ℝ}, s ≠ 0 →
      cappedInfinitePhaseObjective n theta tau s =
        unrestrictedPhaseObjective n s +
          s * (tau - finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) s) +
            cappedInfiniteFiniteEntropy (phaseNat n) theta (fourSizeTarget n (phaseNat n) s)) := by
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
    unfold cappedInfinitePhaseObjective fourSizeTarget profileDeficitTarget
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
  have hB_pos_ll : 0 < B * logLogOrder n * s0 := mul_pos (mul_pos hBpos hLLPos) hs0Pos
  have hNegLeft : cappedInfinitePhaseObjective n theta tau (s0 - Delta) < 0 := by
    have hsL_mem : s0 - Delta ∈ Set.Icc (s0 - Delta) (s0 + Delta) := ⟨le_rfl, by linarith⟩
    have hsL_pos : 0 < s0 - Delta := by linarith [(hInvRate.2 _ hsL_mem).1, hs0Pos]
    rw [hDiffId hsL_pos.ne']
    have hsh := (abs_le.mp (hShiftBound (s0 - Delta) hsL_mem)).2
    have hc_hi := (abs_le.mp hCenterAbs).2
    have hpos_ll : 0 < logLogOrder n * s0 := mul_pos hLLPos hs0Pos
    linarith
  have hPosRight : 0 < cappedInfinitePhaseObjective n theta tau (s0 + Delta) := by
    have hsR_mem : s0 + Delta ∈ Set.Icc (s0 - Delta) (s0 + Delta) := ⟨by linarith, le_rfl⟩
    have hsR_pos : 0 < s0 + Delta := by linarith
    rw [hDiffId hsR_pos.ne']
    have hsh := (abs_le.mp (hShiftBound (s0 + Delta) hsR_mem)).1
    have hc_lo := (abs_le.mp hCenterAbs).1
    have hpos_ll : 0 < logLogOrder n * s0 := mul_pos hLLPos hs0Pos
    linarith
  have hStrict_n := (hStrictDrop hd theta htheta tau htau).1
  refine ⟨hStrict_n, ?_, ?_⟩
  · have hivt : (0 : ℝ) ∈ cappedInfinitePhaseObjective n theta tau '' Set.Icc (s0 - Delta) (s0 + Delta) :=
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

/-!
### 4b. Mixed `(5.19)` corridor-root separation and unconditional Proposition 5.3(iii) `(5.20)`
-/

private theorem finiteUnrestrictedDeficitEntropy_le_at_tilt_v12
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
    have hrhs : w i * (qw i / w i - 1) = qw i - w i := by field_simp [(hw_pos i).ne']
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

private theorem abs_finiteUnrestrictedDeficitEntropy_sub_le_v12
    {alpha : ℕ} (halpha : 0 < alpha) {T₁ T₂ M_tilt : ℝ}
    (hT₁ : T₁ ∈ Set.Ioo (-1 : ℝ) ((alpha : ℝ) - 1))
    (hT₂ : T₂ ∈ Set.Ioo (-1 : ℝ) ((alpha : ℝ) - 1))
    (hM₁ : |profileDeficitTilt alpha T₁| ≤ M_tilt)
    (hM₂ : |profileDeficitTilt alpha T₂| ≤ M_tilt) :
    |finiteUnrestrictedDeficitEntropy alpha T₁ -
        finiteUnrestrictedDeficitEntropy alpha T₂| ≤ M_tilt * |T₁ - T₂| := by
  have h12 : finiteUnrestrictedDeficitEntropy alpha T₁ -
      finiteUnrestrictedDeficitEntropy alpha T₂ ≤ M_tilt * |T₁ - T₂| := by
    have hle := finiteUnrestrictedDeficitEntropy_le_at_tilt_v12 halpha hT₁
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
    have hle := finiteUnrestrictedDeficitEntropy_le_at_tilt_v12 halpha hT₂
      (profileDeficitTilt alpha T₁)
    unfold finiteUnrestrictedDeficitEntropy at hle ⊢
    have hprod : profileDeficitTilt alpha T₁ * (T₁ - T₂) ≤ M_tilt * |T₁ - T₂| := by
      calc profileDeficitTilt alpha T₁ * (T₁ - T₂)
          ≤ |profileDeficitTilt alpha T₁ * (T₁ - T₂)| := le_abs_self _
        _ = |profileDeficitTilt alpha T₁| * |T₁ - T₂| := abs_mul _ _
        _ ≤ M_tilt * |T₁ - T₂| := mul_le_mul_of_nonneg_right hM₁ (abs_nonneg _)
    linarith
  exact abs_le.mpr ⟨by linarith, h12⟩

private theorem eventually_phaseRootCenter_sub_main_logLogRate_v12 :
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
      unfold q at this ⊢; linarith [Real.log_two_lt_d9]
    have hqb_hi : q * (phaseB n + phaseDelta n - 1) ≤ 2 := by
      have := mul_le_mul_of_nonneg_left hb_hi q_pos.le
      unfold q at this ⊢; linarith [Real.log_two_lt_d9]
    have hc_bds := abs_le.mp (le_rfl : |2 * phaseC| ≤ |2 * phaseC|)
    rw [hqs0, abs_le]
    exact ⟨by linarith [hc_bds.1], by linarith [hc_bds.2]⟩
  have hqs0_lo : L ≤ q * s0 := by linarith [(abs_le.mp hqs0_abs).1]
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
    _ = (3 * q / 2) * ((n : ℝ) * w / L ^ 2) := by field_simp [q_pos.ne', hL_pos.ne']
    _ ≤ 4 * ((n : ℝ) * w / L ^ 2) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        unfold q; linarith [Real.log_two_lt_d9]
    _ = 4 * (n : ℝ) * w / L ^ 2 := by ring

private theorem corridor_separation_algebra_core_v12
    {L w n_r C K_slope M_tilt K_E B_H r₁ r₂ c S_ξ u₁ u₂ G₁ G₂ F₁_lim F₂_lim tau₁ tau₂ : ℝ}
    (hC : 0 ≤ C) (_hM_tilt : 0 ≤ M_tilt) (_hK_E : 0 ≤ K_E)
    (hK_slope_B_nn : 0 ≤ K_slope + B_H) (hB_H_nn : 0 ≤ B_H)
    (hL_ge4 : 4 ≤ L) (hw_ge1 : 1 ≤ w) (hn_pos : 0 < n_r)
    (hc_approx : |c - (Real.log 2 / 2) * (n_r / L)| ≤ 4 * n_r * w / L ^ 2)
    (hr₁_pos : 0 < r₁) (hr₁_le : r₁ ≤ 2 * (n_r / L))
    (hr₁_c_abs : |r₁ - c| ≤ C * n_r * w / L ^ 2)
    (hmvt_eq : r₁ * (u₁ - G₁ - tau₁) - r₂ * (u₂ - G₂ - tau₂) = S_ξ * (r₁ - r₂))
    (hslope_ξ : |S_ξ - (2 / Real.log 2) * L ^ 2| ≤ K_slope * L * w)
    (hu_diff : |u₁ - u₂| ≤ 4 * C * M_tilt * w / L)
    (hG₁_err : |G₁ - F₁_lim| ≤ K_E * w / L)
    (hG₂_err : |G₂ - F₂_lim| ≤ K_E * w / L)
    (hH₂_abs : |u₂ - G₂ - tau₂| ≤ B_H)
    (hΔ_abs : |tau₂ - tau₁ + F₂_lim - F₁_lim| ≤ B_H)
    (hS_lower : (K_slope + B_H) * L * w ≤ (1 / Real.log 2) * L ^ 2) :
    |(r₁ - r₂) - (Real.log 2) ^ 2 / 4 * (tau₂ - tau₁ + F₂_lim - F₁_lim) *
        (n_r / L ^ 3)| ≤
      ((4 + C) * B_H + 4 * (K_E + 2 * C * M_tilt) + (K_slope + B_H) * B_H) *
        n_r * w / L ^ 4 := by
  have hL_pos : 0 < L := by linarith
  have hw_pos : 0 < w := by linarith
  have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hq_le1 : Real.log 2 ≤ 1 := le_trans Real.log_two_lt_d9.le (by norm_num)
  let H₁ : ℝ := u₁ - G₁ - tau₁
  let H₂ : ℝ := u₂ - G₂ - tau₂
  let S' : ℝ := S_ξ - H₂
  let S₀ : ℝ := (2 / Real.log 2) * L ^ 2
  let r₀ : ℝ := (Real.log 2 / 2) * (n_r / L)
  let Δ_main : ℝ := tau₂ - tau₁ + F₂_lim - F₁_lim
  let main_approx : ℝ := (Real.log 2) ^ 2 / 4 * Δ_main * (n_r / L ^ 3)
  have hlin_eq : S' * (r₁ - r₂) = r₁ * (H₁ - H₂) := by
    dsimp only [S', H₁, H₂]
    linarith [hmvt_eq]
  have hS₀_main : S₀ * main_approx = r₀ * Δ_main := by
    dsimp only [S₀, r₀, main_approx]
    field_simp [hq_pos.ne', hL_pos.ne']
    ring
  have hdecomp :
      S' * ((r₁ - r₂) - main_approx) =
        (r₁ - r₀) * Δ_main + r₁ * ((H₁ - H₂) - Δ_main) - (S' - S₀) * main_approx := by
    calc S' * ((r₁ - r₂) - main_approx)
        = S' * (r₁ - r₂) - S₀ * main_approx - (S' - S₀) * main_approx := by ring
      _ = r₁ * (H₁ - H₂) - r₀ * Δ_main - (S' - S₀) * main_approx := by rw [hlin_eq, hS₀_main]
      _ = (r₁ - r₀) * Δ_main + r₁ * ((H₁ - H₂) - Δ_main) - (S' - S₀) * main_approx := by ring
  have hS'_err : |S' - S₀| ≤ (K_slope + B_H) * L * w := by
    have h1 : |S' - S₀| ≤ |S_ξ - S₀| + |H₂| := by
      simpa only [S', sub_right_comm] using abs_sub (S_ξ - S₀) H₂
    have hLw_ge1 : 1 ≤ L * w := by nlinarith
    have hB_le : |H₂| ≤ B_H * (L * w) := hH₂_abs.trans (le_mul_of_one_le_right hB_H_nn hLw_ge1)
    change |S_ξ - S₀| ≤ K_slope * L * w at hslope_ξ
    linarith
  have hS'_lo : (1 / Real.log 2) * L ^ 2 ≤ S' := by
    have hl := (abs_le.mp hS'_err).1
    have hsub_S : S₀ - (1 / Real.log 2) * L ^ 2 = (1 / Real.log 2) * L ^ 2 := by
      dsimp only [S₀]; ring
    linarith [hS_lower]
  have hS'_pos : 0 < S' := lt_of_lt_of_le (by positivity) hS'_lo
  have hr₁_r₀ : |r₁ - r₀| ≤ (4 + C) * n_r * w / L ^ 2 := by
    calc |r₁ - r₀| = |(r₁ - c) + (c - r₀)| := by ring_nf
      _ ≤ |r₁ - c| + |c - r₀| := abs_add_le _ _
      _ ≤ C * n_r * w / L ^ 2 + 4 * n_r * w / L ^ 2 := add_le_add hr₁_c_abs hc_approx
      _ = (4 + C) * n_r * w / L ^ 2 := by ring
  have hH_diff_err :
      |(H₁ - H₂) - Δ_main| ≤ 2 * (K_E + 2 * C * M_tilt) * w / L := by
    have hid_H : (H₁ - H₂) - Δ_main =
        (u₁ - u₂) - (G₁ - F₁_lim) + (G₂ - F₂_lim) := by
      dsimp only [H₁, H₂, Δ_main]; ring
    rw [hid_H]
    have htri1 := abs_add_le ((u₁ - u₂) - (G₁ - F₁_lim)) (G₂ - F₂_lim)
    have htri2 := abs_sub (u₁ - u₂) (G₁ - F₁_lim)
    have hrhs_eq :
        4 * C * M_tilt * w / L + K_E * w / L + K_E * w / L =
          2 * (K_E + 2 * C * M_tilt) * w / L := by ring
    linarith [hu_diff, hG₁_err, hG₂_err, hrhs_eq]
  have hterm1 : |(r₁ - r₀) * Δ_main| ≤ (4 + C) * B_H * (n_r * w / L ^ 2) := by
    rw [abs_mul]
    calc |r₁ - r₀| * |Δ_main|
        ≤ ((4 + C) * n_r * w / L ^ 2) * B_H :=
          mul_le_mul hr₁_r₀ hΔ_abs (abs_nonneg _) (by positivity)
      _ = (4 + C) * B_H * (n_r * w / L ^ 2) := by ring
  have hterm2 : |r₁ * ((H₁ - H₂) - Δ_main)| ≤
      4 * (K_E + 2 * C * M_tilt) * (n_r * w / L ^ 2) := by
    rw [abs_mul, abs_of_pos hr₁_pos]
    calc r₁ * |(H₁ - H₂) - Δ_main|
        ≤ (2 * (n_r / L)) * (2 * (K_E + 2 * C * M_tilt) * w / L) :=
          mul_le_mul hr₁_le hH_diff_err (abs_nonneg _) (by positivity)
      _ = 4 * (K_E + 2 * C * M_tilt) * (n_r * w / L ^ 2) := by ring
  have hmain_abs : |main_approx| ≤ B_H * (n_r / L ^ 3) := by
    dsimp only [main_approx]
    have hq4_pos : 0 < (Real.log 2) ^ 2 / 4 := by positivity
    have hnL3_pos : 0 < n_r / L ^ 3 := div_pos hn_pos (pow_pos hL_pos 3)
    rw [abs_mul, abs_mul, abs_of_pos hq4_pos, abs_of_pos hnL3_pos]
    have hq2_le1 : (Real.log 2) ^ 2 / 4 ≤ 1 := by
      have : (Real.log 2) ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ hq_pos.le hq_le1 2
      linarith
    calc (Real.log 2) ^ 2 / 4 * |Δ_main| * (n_r / L ^ 3)
        ≤ 1 * B_H * (n_r / L ^ 3) := by
          apply mul_le_mul_of_nonneg_right _ hnL3_pos.le
          exact mul_le_mul hq2_le1 hΔ_abs (abs_nonneg _) zero_le_one
      _ = B_H * (n_r / L ^ 3) := by ring
  have hterm3 : |(S' - S₀) * main_approx| ≤
      (K_slope + B_H) * B_H * (n_r * w / L ^ 2) := by
    rw [abs_mul]
    have hLw_nn : 0 ≤ (K_slope + B_H) * L * w :=
      mul_nonneg (mul_nonneg hK_slope_B_nn hL_pos.le) hw_pos.le
    calc |S' - S₀| * |main_approx|
        ≤ ((K_slope + B_H) * L * w) * (B_H * (n_r / L ^ 3)) :=
          mul_le_mul hS'_err hmain_abs (abs_nonneg _) hLw_nn
      _ = (K_slope + B_H) * B_H * (n_r * w / L ^ 2) := by
          field_simp [hL_pos.ne']
  have hnum_bound :
      S' * |(r₁ - r₂) - main_approx| ≤
        ((4 + C) * B_H + 4 * (K_E + 2 * C * M_tilt) + (K_slope + B_H) * B_H) *
          (n_r * w / L ^ 2) := by
    have habs_lhs : S' * |(r₁ - r₂) - main_approx| = |S' * ((r₁ - r₂) - main_approx)| := by
      rw [abs_mul, abs_of_pos hS'_pos]
    rw [habs_lhs, hdecomp]
    have ht12 := abs_sub ((r₁ - r₀) * Δ_main + r₁ * ((H₁ - H₂) - Δ_main)) ((S' - S₀) * main_approx)
    have ht11 := abs_add_le ((r₁ - r₀) * Δ_main) (r₁ * ((H₁ - H₂) - Δ_main))
    linarith [hterm1, hterm2, hterm3]
  have hnum_nn :
      0 ≤ ((4 + C) * B_H + 4 * (K_E + 2 * C * M_tilt) + (K_slope + B_H) * B_H) *
        (n_r * w / L ^ 2) :=
    (mul_nonneg hS'_pos.le (abs_nonneg _)).trans hnum_bound
  have hcoeff_nn : 0 ≤ (4 + C) * B_H + 4 * (K_E + 2 * C * M_tilt) + (K_slope + B_H) * B_H :=
    nonneg_of_mul_nonneg_left hnum_nn (div_pos (mul_pos hn_pos hw_pos) (sq_pos_of_pos hL_pos))
  have hdiv_bound :
      |(r₁ - r₂) - main_approx| ≤
        (((4 + C) * B_H + 4 * (K_E + 2 * C * M_tilt) + (K_slope + B_H) * B_H) *
          (n_r * w / L ^ 2)) / ((1 / Real.log 2) * L ^ 2) := by
    have h1 : |(r₁ - r₂) - main_approx| ≤
        (((4 + C) * B_H + 4 * (K_E + 2 * C * M_tilt) + (K_slope + B_H) * B_H) *
          (n_r * w / L ^ 2)) / S' :=
      (le_div_iff₀' hS'_pos).mpr hnum_bound
    exact h1.trans (div_le_div_of_nonneg_left hnum_nn
      (mul_pos (one_div_pos.mpr hq_pos) (sq_pos_of_pos hL_pos)) hS'_lo)
  have hrew_rhs :
      (((4 + C) * B_H + 4 * (K_E + 2 * C * M_tilt) + (K_slope + B_H) * B_H) *
        (n_r * w / L ^ 2)) / ((1 / Real.log 2) * L ^ 2) =
      Real.log 2 * (((4 + C) * B_H + 4 * (K_E + 2 * C * M_tilt) + (K_slope + B_H) * B_H) *
        n_r * w / L ^ 4) := by
    field_simp [hq_pos.ne', hL_pos.ne']
  rw [hrew_rhs] at hdiv_bound
  have hrhs_nn :
      0 ≤ ((4 + C) * B_H + 4 * (K_E + 2 * C * M_tilt) + (K_slope + B_H) * B_H) *
        n_r * w / L ^ 4 :=
    div_nonneg (mul_nonneg (mul_nonneg hcoeff_nn hn_pos.le) hw_pos.le) (pow_nonneg hL_pos.le 4)
  exact hdiv_bound.trans ((mul_le_mul_of_nonneg_right hq_le1 hrhs_nn).trans_eq (one_mul _))

private theorem corridor_root_separation_master_v12
    {n : ℕ} {C K_slope M_tilt r₁ r₂ G₁ G₂ F₁_lim F₂_lim tau₁ tau₂ K_E B_H : ℝ}
    (hC : 0 ≤ C) (hM_tilt : 0 ≤ M_tilt) (hK_E : 0 ≤ K_E)
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
  have hL_pos : 0 < logOrder n := by linarith
  have hw_pos : 0 < logLogOrder n := by linarith
  have hc_pos : 0 < phaseRootCenter n := div_pos hn_pos hs0_pos
  have ha_ge6 : (6 : ℝ) ≤ (phaseNat n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hfive)
  have hB_H_nn : 0 ≤ B_H := (abs_nonneg _).trans hH₂_abs
  have hgap_nn : 0 ≤ C * logLogOrder n * phaseRootGapRadius n := by
    unfold phaseRootGapRadius
    exact mul_nonneg (mul_nonneg hC hw_pos.le) (div_nonneg hc_pos.le (sq_nonneg _))
  have hK_slope_B_nn : 0 ≤ K_slope + B_H := by
    have h0 := (abs_nonneg _).trans (hslope (phaseRootCenter n) ⟨by linarith, by linarith⟩)
    have hK_nn : 0 ≤ K_slope := nonneg_of_mul_nonneg_left
      (nonneg_of_mul_nonneg_left h0 hw_pos) hL_pos
    linarith
  have hKeyU : ∀ x ∈ Set.Icc
      (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
      (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n),
      HasDerivAt (unrestrictedPhaseObjective n)
        (Real.log (profileDualPartition (phaseNat n + 1)
            (profileDualTilt (phaseNat n + 1) ((n : ℝ) / x))) - Real.log x) x := by
    intro x hx
    obtain ⟨hxpos, htar⟩ := hdomain x hx
    rw [fourSizeTarget, Set.mem_Ioo] at htar
    exact hasDerivAt_profileDualOptimalValue_parts (by omega) hxpos (by
      rw [Set.mem_Ioo, show (((phaseNat n + 1 : ℕ) : ℝ)) = (phaseNat n : ℝ) + 1 by push_cast; ring]
      exact ⟨by linarith [htar.2, ha_ge6], by linarith [htar.1]⟩)
  have hmvt : ∃ ξ ∈ Set.Icc
      (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
      (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n),
      unrestrictedPhaseObjective n r₁ - unrestrictedPhaseObjective n r₂ =
        deriv (unrestrictedPhaseObjective n) ξ * (r₁ - r₂) := by
    rcases lt_trichotomy r₁ r₂ with hlt | rfl | hgt
    · have hsub : Set.Icc r₁ r₂ ⊆ Set.Icc
          (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n) :=
        fun x hx ↦ ⟨hr₁.1.trans hx.1, hx.2.trans hr₂.2⟩
      obtain ⟨ξ, hξ_ioo, hξ_eq⟩ := exists_deriv_eq_slope (unrestrictedPhaseObjective n) hlt
        (fun x hx ↦ (hKeyU x (hsub hx)).continuousAt.continuousWithinAt)
        (fun x hx ↦ (hKeyU x (hsub (Ioo_subset_Icc_self hx))).differentiableAt.differentiableWithinAt)
      refine ⟨ξ, hsub (Ioo_subset_Icc_self hξ_ioo), ?_⟩
      have hne : r₂ - r₁ ≠ 0 := sub_ne_zero.mpr hlt.ne'
      rw [hξ_eq]; field_simp [hne]; ring
    · exact ⟨r₁, hr₁, by simp⟩
    · have hsub : Set.Icc r₂ r₁ ⊆ Set.Icc
          (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n) :=
        fun x hx ↦ ⟨hr₂.1.trans hx.1, hx.2.trans hr₁.2⟩
      obtain ⟨ξ, hξ_ioo, hξ_eq⟩ := exists_deriv_eq_slope (unrestrictedPhaseObjective n) hgt
        (fun x hx ↦ (hKeyU x (hsub hx)).continuousAt.continuousWithinAt)
        (fun x hx ↦ (hKeyU x (hsub (Ioo_subset_Icc_self hx))).differentiableAt.differentiableWithinAt)
      refine ⟨ξ, hsub (Ioo_subset_Icc_self hξ_ioo), ?_⟩
      have hne : r₁ - r₂ ≠ 0 := sub_ne_zero.mpr hgt.ne'
      rw [hξ_eq]; field_simp [hne]
  rcases hmvt with ⟨ξ, hξ_mem, hξ_mvt⟩
  have hr₁_c_abs : |r₁ - phaseRootCenter n| ≤ C * (n : ℝ) * logLogOrder n / (logOrder n) ^ 2 := by
    have habs_rc : |r₁ - phaseRootCenter n| ≤
        C * logLogOrder n * (phaseRootCenter n / (phaseNat n : ℝ) ^ 2) := by
      rw [abs_le]
      have hgap : phaseRootGapRadius n = phaseRootCenter n / (phaseNat n : ℝ) ^ 2 := rfl
      have hr₁' : phaseRootCenter n - C * logLogOrder n * (phaseRootCenter n / (phaseNat n : ℝ) ^ 2) ≤ r₁ ∧
          r₁ ≤ phaseRootCenter n + C * logLogOrder n * (phaseRootCenter n / (phaseNat n : ℝ) ^ 2) := by
        simpa only [hgap, Set.mem_Icc] using hr₁
      exact ⟨by linarith [hr₁'.1], by linarith [hr₁'.2]⟩
    have ha_sq_ge : (logOrder n) ^ 2 ≤ (phaseNat n : ℝ) ^ 2 := pow_le_pow_left₀ hL_pos.le hL_le_a 2
    have hca_le : phaseRootCenter n / (phaseNat n : ℝ) ^ 2 ≤ ((n : ℝ) / logOrder n) / (logOrder n) ^ 2 :=
      (div_le_div_of_nonneg_left hc_pos.le (sq_pos_of_pos hL_pos) ha_sq_ge).trans
        (div_le_div_of_nonneg_right hc_le (sq_nonneg _))
    calc |r₁ - phaseRootCenter n|
        ≤ C * logLogOrder n * (((n : ℝ) / logOrder n) / (logOrder n) ^ 2) :=
          habs_rc.trans (mul_le_mul_of_nonneg_left hca_le (by positivity))
      _ ≤ C * logLogOrder n * ((n : ℝ) / (logOrder n) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hL1 : 1 ≤ logOrder n := by linarith
          calc ((n : ℝ) / logOrder n) / (logOrder n) ^ 2 = (n : ℝ) / ((logOrder n) ^ 2 * logOrder n) := by ring
            _ ≤ (n : ℝ) / ((logOrder n) ^ 2 * 1) :=
                div_le_div_of_nonneg_left hn_pos.le (by positivity)
                  (mul_le_mul_of_nonneg_left hL1 (sq_nonneg _))
            _ = (n : ℝ) / (logOrder n) ^ 2 := by ring
      _ = C * (n : ℝ) * logLogOrder n / (logOrder n) ^ 2 := by ring
  have hT_diff : |fourSizeTarget n (phaseNat n) r₁ - fourSizeTarget n (phaseNat n) r₂| ≤
      4 * C * logLogOrder n / logOrder n := by
    have ht1 := (hcorr_inv r₁ hr₁).2.2
    have ht2 := (hcorr_inv r₂ hr₂).2.2
    calc |fourSizeTarget n (phaseNat n) r₁ - fourSizeTarget n (phaseNat n) r₂|
        = |(fourSizeTarget n (phaseNat n) r₁ - phaseTarget (phaseDelta n)) -
            (fourSizeTarget n (phaseNat n) r₂ - phaseTarget (phaseDelta n))| := by ring_nf
      _ ≤ |fourSizeTarget n (phaseNat n) r₁ - phaseTarget (phaseDelta n)| +
            |fourSizeTarget n (phaseNat n) r₂ - phaseTarget (phaseDelta n)| := abs_sub _ _
      _ ≤ 2 * C * logLogOrder n / logOrder n + 2 * C * logLogOrder n / logOrder n := add_le_add ht1 ht2
      _ = 4 * C * logLogOrder n / logOrder n := by ring
  have hUnrest_diff :
      |finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) r₁) -
          finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) r₂)| ≤
        4 * C * M_tilt * logLogOrder n / logOrder n := by
    have hu := abs_finiteUnrestrictedDeficitEntropy_sub_le_v12 (by omega : 0 < phaseNat n)
      (htilt_corr r₁ hr₁).1 (htilt_corr r₂ hr₂).1
      (htilt_corr r₁ hr₁).2 (htilt_corr r₂ hr₂).2
    calc |finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) r₁) -
            finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) r₂)|
        ≤ M_tilt * (4 * C * logLogOrder n / logOrder n) := hu.trans (mul_le_mul_of_nonneg_left hT_diff hM_tilt)
      _ = 4 * C * M_tilt * logLogOrder n / logOrder n := by ring
  exact corridor_separation_algebra_core_v12 hC hM_tilt hK_E hK_slope_B_nn hB_H_nn hL_ge4 hw_ge1 hn_pos
    hc_approx (hdomain r₁ hr₁).1
    ((hcorr_inv r₁ hr₁).2.1.trans (mul_le_mul_of_nonneg_left hc_le zero_le_two))
    hr₁_c_abs (by linarith [hξ_mvt, heq₁, heq₂]) (hslope ξ hξ_mem)
    hUnrest_diff hG₁_err hG₂_err hH₂_abs hΔ_abs hS_lower

private theorem eventually_mu_phaseNat_succ_and_deltaStar_le_v12 :
    ∀ᶠ n : ℕ in atTop,
      mu n (phaseNat n + 1) ≤ universalShift n ∧
      (phaseDelta n ≤ deltaStar → mu n (phaseNat n) ≤ universalShift n) ∧
      (phaseDelta n ≤ deltaStar → mu n (phaseNat n) ≤ (n : ℝ) / (16 * Real.log (n : ℝ))) := by
  obtain ⟨C₂, _, hC₂_pos, _, hmu_ev⟩ := exists_uniform_phaseExpansion_and_adjacent_bounds
  have ho_succ : (fun x : ℝ ↦ (Real.log x) ^ (2 / q - 1 / 2 + 5 : ℝ)) =o[atTop]
      (fun x : ℝ ↦ x ^ (1 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop _ zero_lt_one
  have hsucc_small : ∀ᶠ n : ℕ in atTop,
      C₂ * (Real.log (n : ℝ)) ^ (2 / q - 1 / 2 + 5 : ℝ) ≤ (n : ℝ) := by
    have hb := (ho_succ.comp_tendsto tendsto_natCast_atTop_atTop).bound (inv_pos.mpr hC₂_pos)
    filter_upwards [hb, eventually_gt_atTop 2] with n hn hn2
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hL_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    dsimp only [Function.comp_apply] at hn
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hL_pos _),
      Real.rpow_one, Real.norm_eq_abs, abs_of_pos hn_pos] at hn
    have hm := mul_le_mul_of_nonneg_left hn hC₂_pos.le
    rwa [← mul_assoc, mul_inv_cancel₀ hC₂_pos.ne', one_mul] at hm
  have ho_L5 : (fun x : ℝ ↦ (Real.log x) ^ ((5 : ℕ) : ℝ)) =o[atTop]
      (fun x : ℝ ↦ x ^ (1 / 2 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop ((5 : ℕ) : ℝ) (by norm_num)
  have hL5_small : ∀ᶠ n : ℕ in atTop, (Real.log (n : ℝ)) ^ 5 ≤ Real.sqrt (n : ℝ) := by
    have hb := (ho_L5.comp_tendsto tendsto_natCast_atTop_atTop).bound zero_lt_one
    filter_upwards [hb, eventually_gt_atTop 2] with n hn hn2
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hL_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    dsimp only [Function.comp_apply] at hn
    rw [Real.rpow_natCast] at hn
    rw [Real.norm_eq_abs, abs_of_pos (pow_pos hL_pos 5), Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hn_pos _), one_mul, ← Real.sqrt_eq_rpow] at hn
    exact hn
  have hll_small : ∀ᶠ n : ℕ in atTop,
      (2 / q) * logLogOrder n + C₂ ≤ (1 / 4 : ℝ) * logOrder n := by
    have hb := logLogOrder_isLittleO_logOrder.bound
      (show (0 : ℝ) < (1 / 8) / (2 / q) by have := q_pos; positivity)
    filter_upwards [hb, tendsto_logOrder_atTop.eventually_ge_atTop (8 * C₂ + 16),
      (tendsto_logLogOrder_atTop.eventually_gt_atTop 0)] with n h1 hL hll
    have hL_pos : 0 < logOrder n := by linarith
    rw [Real.norm_eq_abs, abs_of_pos hll, Real.norm_eq_abs, abs_of_pos hL_pos] at h1
    have hm := mul_le_mul_of_nonneg_left h1 (div_pos two_pos q_pos).le
    have hc : (2 / q) * ((1 / 8) / (2 / q) * logOrder n) = (1 / 8 : ℝ) * logOrder n := by
      field_simp [q_pos.ne']
    rw [hc] at hm
    linarith
  filter_upwards [hmu_ev, hsucc_small, hL5_small, hll_small,
    tendsto_logOrder_atTop.eventually_ge_atTop 16, eventually_gt_atTop 2] with
    n hmu hsucc hL5 hll hL16 hn2
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hL_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have h1 : mu n (phaseNat n + 1) ≤ universalShift n := by
    unfold universalShift
    rw [le_div_iff₀ (pow_pos hL_pos 5)]
    calc mu n (phaseNat n + 1) * (Real.log (n : ℝ)) ^ 5
        ≤ (C₂ * (logOrder n) ^ (2 / q - 1 / 2 : ℝ)) * (Real.log (n : ℝ)) ^ 5 :=
          mul_le_mul_of_nonneg_right hmu.2.1 (pow_nonneg hL_pos.le 5)
      _ = C₂ * (Real.log (n : ℝ)) ^ (2 / q - 1 / 2 + 5 : ℝ) := by
          unfold logOrder
          rw [mul_assoc, ← Real.rpow_natCast (Real.log (n : ℝ)) 5, ← Real.rpow_add hL_pos]
          push_cast; rfl
      _ ≤ (n : ℝ) := hsucc
  have h2 : phaseDelta n ≤ deltaStar → mu n (phaseNat n) ≤ universalShift n := by
    intro hd
    rcases eq_or_lt_of_le (mu_nonneg n (phaseNat n)) with h0 | hmu_pos
    · rw [← h0]; unfold universalShift; positivity
    · have hlog_hi := (abs_le.mp hmu.1).2
      have hd_nn : 0 ≤ phaseDelta n := phaseDelta_nonneg n
      have hll_pos : 0 ≤ logLogOrder n :=
        Real.log_nonneg (by unfold logOrder at hL16 ⊢; linarith)
      have hcoef : (2 / q - 1 / 2 - phaseDelta n) * logLogOrder n ≤ (2 / q) * logLogOrder n :=
        mul_le_mul_of_nonneg_right (by linarith) hll_pos
      have hd_L : phaseDelta n * logOrder n ≤ (1 / 4 : ℝ) * logOrder n := by
        unfold deltaStar at hd
        exact mul_le_mul_of_nonneg_right (by linarith) (by unfold logOrder; linarith)
      have hlog_le : Real.log (mu n (phaseNat n)) ≤ (1 / 2 : ℝ) * Real.log (n : ℝ) := by
        unfold logOrder at hlog_hi hd_L hll
        linarith
      have hmu_le_sqrt : mu n (phaseNat n) ≤ Real.sqrt (n : ℝ) := by
        rw [← Real.exp_log hmu_pos, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn_pos, mul_comm]
        exact Real.exp_le_exp.mpr hlog_le
      unfold universalShift
      rw [le_div_iff₀ (pow_pos hL_pos 5)]
      calc mu n (phaseNat n) * (Real.log (n : ℝ)) ^ 5
          ≤ Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) :=
            mul_le_mul hmu_le_sqrt hL5 (pow_nonneg hL_pos.le 5) (Real.sqrt_nonneg _)
        _ = (n : ℝ) := Real.mul_self_sqrt hn_pos.le
  refine ⟨h1, h2, fun hd ↦ (h2 hd).trans ?_⟩
  unfold universalShift
  apply div_le_div_of_nonneg_left hn_pos.le (by positivity)
  have h16 : (16 : ℝ) ≤ (Real.log (n : ℝ)) ^ 4 := by
    unfold logOrder at hL16
    calc (16 : ℝ) ≤ (16 : ℝ) ^ 4 := by norm_num
      _ ≤ (Real.log (n : ℝ)) ^ 4 := pow_le_pow_left₀ (by norm_num) hL16 4
  calc 16 * Real.log (n : ℝ) ≤ (Real.log (n : ℝ)) ^ 4 * Real.log (n : ℝ) :=
        mul_le_mul_of_nonneg_right h16 hL_pos.le
    _ = (Real.log (n : ℝ)) ^ 5 := by ring

private theorem exists_pos_le_phaseGain7_and_sub_log_two :
    ∃ η_root : ℝ, 0 < η_root ∧
      ∀ td ∈ Set.Icc (0 : ℝ) (207 / 200),
        η_root ≤ phaseGain7 td ∧ η_root ≤ Real.log 2 - phaseGain7 td := by
  set U_top : ℝ := |Real.log (partitionFn Splus 0)| + 1
  set Λ₀ : ℝ := max 1 (8 * (U_top + 14))
  have hΛ₀_pos : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  set Z_cap : ℝ := 7 * Real.exp (7 * Λ₀)
  have hZ_cap_pos : 0 < Z_cap := by dsimp [Z_cap]; positivity
  set δ_gap : ℝ := min (Real.log (391 / 200)) (min (1 / 2) (Real.log (1 + 1 / Z_cap)))
  have hδ_pos : 0 < δ_gap := by
    refine lt_min (Real.log_pos (by norm_num)) (lt_min (by norm_num) ?_)
    exact Real.log_pos (by linarith [div_pos one_pos hZ_cap_pos])
  refine ⟨δ_gap, hδ_pos, fun td htd ↦ ?_⟩
  have h1 : δ_gap ≤ phaseGain7 td :=
    (min_le_left _ _).trans (log_391_div_200_lt_phaseGain7 td htd).le
  refine ⟨h1, ?_⟩
  obtain ⟨h2lo, h2hi⟩ := two_div_log_two_bounds
  set T : ℝ := phaseTarget td
  have hT_pad : T ∈ Set.Icc (17 / 8 : ℝ) (37 / 8) := by
    dsimp [T]; unfold phaseTarget
    exact ⟨by linarith [htd.2, h2lo], by linarith [htd.1, h2hi]⟩
  have hT_25 : T ∈ Set.Ioo (2 : ℝ) 5 := ⟨by linarith [hT_pad.1], by linarith [hT_pad.2]⟩
  have hm4 := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT_25)
  have hbdd_07 := bddBelow_dual S4_subset_S07 hm4
  have h07_hi : dualValue S07 T ≤ Real.log (partitionFn Splus 0) := by
    have h0 := dualValue_le_at S4_subset_S07 hm4 0
    have h2_mem : (2 : ℤ) ∈ S07 := by simp [S07]
    have hpos_07 : 0 < partitionFn S07 0 :=
      lt_of_lt_of_le (gaussWeight_pos 0 2)
        (((hasSum_partitionFn S07 0).summable).le_tsum ⟨2, h2_mem⟩
          fun j _ ↦ (gaussWeight_pos 0 j.1).le)
    linarith [Real.log_le_log hpos_07 (partitionFn_mono (S07_subset_Sge0.trans Sge0_subset_Splus) 0)]
  have hsub_eq : Real.log 2 - phaseGain7 td = dualValue Sge0 T - dualValue S07 T := by
    unfold phaseGain7; dsimp [T]; ring
  rw [hsub_eq]
  suffices dualValue S07 T + δ_gap ≤ dualValue Sge0 T by linarith
  refine le_ciInf fun l ↦ ?_
  by_cases hl_big : U_top < Real.log (partitionFn Sge0 l) - l * T
  · have hδ_half : δ_gap ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
    dsimp [U_top] at hl_big
    linarith [le_abs_self (Real.log (partitionFn Splus 0))]
  · replace hl_big : Real.log (partitionFn Sge0 l) - l * T ≤ U_top := le_of_not_gt hl_big
    have h0_mem : (0 : ℤ) ∈ Sge0 := by simp [Sge0]
    have h5_mem : (5 : ℤ) ∈ Sge0 := by simp [Sge0]
    have hgw0 : gaussWeight l 0 = 1 := by unfold gaussWeight; simp
    have hZ0_ge1 : 1 ≤ partitionFn Sge0 l := by
      have h := ((hasSum_partitionFn Sge0 l).summable).le_tsum ⟨0, h0_mem⟩
        fun j _ ↦ (gaussWeight_pos l j.1).le
      rwa [hgw0] at h
    have hZ5_ge : Real.exp (5 * l - 13) ≤ partitionFn Sge0 l := by
      have h := ((hasSum_partitionFn Sge0 l).summable).le_tsum ⟨5, h5_mem⟩
        fun j _ ↦ (gaussWeight_pos l j.1).le
      have hgw5 : Real.exp (5 * l - 13) ≤ gaussWeight l 5 := by
        unfold gaussWeight; apply Real.exp_le_exp.mpr; push_cast
        linarith [Real.log_two_lt_d9]
      exact hgw5.trans h
    have hl_abs : |l| ≤ Λ₀ := by
      have hΛ_ge : 8 * (U_top + 14) ≤ Λ₀ := le_max_right _ _
      rcases le_total l 0 with hl0 | hl0
      · rw [abs_of_nonpos hl0]
        have hlog0 : 0 ≤ Real.log (partitionFn Sge0 l) := Real.log_nonneg hZ0_ge1
        have hm : (-l) * 2 ≤ (-l) * T := mul_le_mul_of_nonneg_left (by linarith [hT_pad.1]) (by linarith)
        have hU_nn : 0 ≤ U_top := by dsimp [U_top]; positivity
        linarith
      · rw [abs_of_nonneg hl0]
        have hlog5 : 5 * l - 13 ≤ Real.log (partitionFn Sge0 l) := by
          have hl := Real.log_le_log (Real.exp_pos _) hZ5_ge
          rwa [Real.log_exp] at hl
        have hm : l * (3 / 8 : ℝ) ≤ l * (5 - T) :=
          mul_le_mul_of_nonneg_left (by linarith [hT_pad.2]) hl0
        linarith
    -- Compare `partitionFn Sge0 l ≥ 1 + partitionFn S07 l` and `partitionFn S07 l ≤ Z_cap`
    have hF07_eq : S07 = (F07 : Set ℤ) := by
      ext j; simp [S07, F07]
    have hZ07_sum : partitionFn S07 l = ∑ j ∈ F07, gaussWeight l j := by
      unfold partitionFn
      rw [tsum_subtype S07 (gaussWeight l), hF07_eq, tsum_eq_sum]
      · refine Finset.sum_congr rfl fun j hj ↦ ?_
        exact Set.indicator_of_mem (Finset.mem_coe.mpr hj) _
      · intro j hj
        exact Set.indicator_of_notMem (Finset.mem_coe.not.mpr hj) _
    have hZ07_pos : 0 < partitionFn S07 l := by
      rw [hZ07_sum]
      exact Finset.sum_pos (fun j _ ↦ gaussWeight_pos l j) ⟨1, by decide⟩
    have hZ07_le_cap : partitionFn S07 l ≤ Z_cap := by
      rw [hZ07_sum]
      have hl_hi : l ≤ Λ₀ := (abs_le.mp hl_abs).2
      have hterm : ∀ j ∈ F07, gaussWeight l j ≤ Real.exp (7 * Λ₀) := by
        intro j hj
        have hj_bds : 1 ≤ j ∧ j ≤ 7 := by
          simp only [F07, Finset.mem_insert, Finset.mem_singleton] at hj
          rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
        unfold gaussWeight
        apply Real.exp_le_exp.mpr
        have hj_nn : (0 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (show 0 ≤ j by omega)
        have hj_le7 : (j : ℝ) ≤ 7 := by exact_mod_cast hj_bds.2
        have hq_nn : 0 ≤ Real.log 2 / 2 * (j : ℝ) ^ 2 :=
          mul_nonneg (div_nonneg (Real.log_pos one_lt_two).le zero_le_two) (sq_nonneg _)
        have hlj : l * (j : ℝ) ≤ 7 * Λ₀ := by
          calc l * (j : ℝ) ≤ Λ₀ * (j : ℝ) := mul_le_mul_of_nonneg_right hl_hi hj_nn
            _ ≤ Λ₀ * 7 := mul_le_mul_of_nonneg_left hj_le7 hΛ₀_pos.le
            _ = 7 * Λ₀ := mul_comm _ _
        linarith
      calc ∑ j ∈ F07, gaussWeight l j
          ≤ ∑ _j ∈ F07, Real.exp (7 * Λ₀) := Finset.sum_le_sum hterm
        _ = 7 * Real.exp (7 * Λ₀) := by simp [F07]
    have hZge0_ge_add : 1 + partitionFn S07 l ≤ partitionFn Sge0 l := by
      rw [hZ07_sum, ← hgw0]
      have h0_not : (0 : ℤ) ∉ F07 := by decide
      rw [← Finset.sum_insert h0_not]
      unfold partitionFn
      let emb : {j : ℤ // j ∈ insert (0 : ℤ) F07} ↪ Sge0 :=
        ⟨fun ⟨j, hj⟩ ↦ ⟨j, by
            simp only [F07, Finset.mem_insert, Finset.mem_singleton] at hj
            simp only [Sge0, Set.mem_setOf_eq]
            rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega⟩,
          fun a b h ↦ Subtype.ext (Subtype.mk.inj h)⟩
      have hatt : (∑ j ∈ insert (0 : ℤ) F07, gaussWeight l j) =
          ∑ x ∈ (insert (0 : ℤ) F07).attach.map emb, gaussWeight l x.1 := by
        rw [Finset.sum_map, ← Finset.sum_attach]; rfl
      rw [hatt]
      exact ((hasSum_partitionFn Sge0 l).summable).sum_le_tsum _
        fun x _ ↦ (gaussWeight_pos l x.1).le
    have hprod_le : partitionFn S07 l * (1 + 1 / Z_cap) ≤ partitionFn Sge0 l := by
      have hdiv_le : partitionFn S07 l / Z_cap ≤ 1 := (div_le_one hZ_cap_pos).mpr hZ07_le_cap
      calc partitionFn S07 l * (1 + 1 / Z_cap)
          = partitionFn S07 l + partitionFn S07 l / Z_cap := by ring
        _ ≤ partitionFn S07 l + 1 := by linarith
        _ ≤ partitionFn Sge0 l := by linarith
    have hlog_step := Real.log_le_log
      (mul_pos hZ07_pos (by linarith [div_pos one_pos hZ_cap_pos])) hprod_le
    rw [Real.log_mul hZ07_pos.ne' (by linarith [div_pos one_pos hZ_cap_pos])] at hlog_step
    have hd07 : dualValue S07 T ≤ Real.log (partitionFn S07 l) - l * T := ciInf_le hbdd_07 l
    have hδ_le_log : δ_gap ≤ Real.log (1 + 1 / Z_cap) :=
      (min_le_right _ _).trans (min_le_right _ _)
    linarith

private def genericPhaseObj_v12 (n : ℕ) (G : ℝ → ℝ) (tau s : ℝ) : ℝ :=
  (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + s - s * Real.log s +
    s * (profileDeficitAffineA (phaseNat n) +
      profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s +
      G (fourSizeTarget n (phaseNat n) s) + tau)

private theorem unrestrictedDeficitEntropy_abs_le_of_tilt_v12
    {alpha : ℕ} (hfive : 5 < alpha) {T Mtilt : ℝ} (hMtilt_nn : 0 ≤ Mtilt)
    (hTK : T ∈ Set.Icc (9 / 4 : ℝ) (17 / 4))
    (htiltB : |profileDeficitTilt alpha T| ≤ Mtilt) :
    |finiteUnrestrictedDeficitEntropy alpha T| ≤
      5 * Mtilt + |Real.log (partitionFn Splus 0)| := by
  have hT25 : T ∈ Set.Ioo (2 : ℝ) 5 := ⟨by linarith only [hTK.1], by linarith only [hTK.2]⟩
  have hHi : finiteUnrestrictedDeficitEntropy alpha T ≤
      |Real.log (partitionFn Splus 0)| := by
    have h1 := (finiteProfileDeficitEntropy_le_extendedGaussianEntropyValue
      alpha hfive hT25).trans (extendedGaussianEntropyValue_le_dualValue_Splus hT25)
    have hm4 := mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT25)
    have h2 := dualValue_le_at S4_subset_Splus hm4 0
    unfold finiteUnrestrictedDeficitEntropy
    linarith [le_abs_self (Real.log (partitionFn Splus 0))]
  have hLo : -(5 * Mtilt) ≤ finiteUnrestrictedDeficitEntropy alpha T := by
    have hp1 := one_le_profileDeficitPartition alpha (by omega) (profileDeficitTilt alpha T)
    have hlognn := Real.log_nonneg hp1
    have hmul : |profileDeficitTilt alpha T * T| ≤ 5 * Mtilt := by
      rw [abs_mul, abs_of_pos (by linarith only [hTK.1] : 0 < T)]
      have := mul_le_mul htiltB (show T ≤ 5 by linarith only [hTK.2])
        (by linarith only [hTK.1]) hMtilt_nn
      linarith
    unfold finiteUnrestrictedDeficitEntropy
    linarith [(abs_le.mp hmul).2]
  exact abs_le.mpr ⟨by linarith [abs_nonneg (Real.log (partitionFn Splus 0))],
    by linarith [hMtilt_nn]⟩

private theorem genericPhaseObj_zero_imp_unrestricted_eq_v12
    {n : ℕ} {G : ℝ → ℝ} {s tau : ℝ}
    (hspos : 0 < s) (hzero : genericPhaseObj_v12 n G tau s = 0) :
    unrestrictedPhaseObjective n s =
      s * (finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) s) -
        G (fourSizeTarget n (phaseNat n) s) - tau) := by
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
  unfold genericPhaseObj_v12 at hzero
  have hzero' :
      s * ((n : ℝ) * Real.log (n : ℝ) / s - (n : ℝ) / s + 1 - Real.log s +
        (profileDeficitAffineA (phaseNat n) +
          profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s +
          G (fourSizeTarget n (phaseNat n) s) + tau)) = 0 := by
    have : s * ((n : ℝ) * Real.log (n : ℝ) / s - (n : ℝ) / s + 1 - Real.log s +
        (profileDeficitAffineA (phaseNat n) +
          profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s +
          G (fourSizeTarget n (phaseNat n) s) + tau)) =
      (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + s - s * Real.log s +
        s * (profileDeficitAffineA (phaseNat n) +
          profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s +
          G (fourSizeTarget n (phaseNat n) s) + tau) := by
      field_simp [hspos.ne']
    rw [this, hzero]
  change _ = s * (finiteUnrestrictedDeficitEntropy (phaseNat n)
    (profileDeficitTarget (phaseNat n) (n : ℝ) s) - G (fourSizeTarget n (phaseNat n) s) - tau)
  have hft : fourSizeTarget n (phaseNat n) s = profileDeficitTarget (phaseNat n) (n : ℝ) s := rfl
  rw [hft] at hzero' ⊢
  linarith

private theorem abs_cappedDualValue_S0M_le_v12
    {M₂ : ℕ} (hM₂8 : 8 ≤ M₂) {theta T B_F0 : ℝ}
    (hth : theta ∈ Set.Icc (0 : ℝ) (1 / 20))
    (hT : T ∈ KcapInterval)
    (hBF0_def : B_F0 = |Real.log (partitionFn Splus 0)| +
      |min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))| + Real.log 2 + 1) :
    |cappedDualValue (S0M M₂) theta T| ≤ B_F0 := by
  have hu_icc := (reducedTarget_mem_Icc_and_Ioo_v12 hth hT).1
  have hd_win := dualValue_window_bounds_on_padded_v12 (m := 1) (M := M₂ - 1)
    le_rfl (by omega) ((T - theta) / (1 - theta))
    ⟨by linarith only [hu_icc.1], by linarith only [hu_icc.2]⟩
  have hs0m_eq : S0M M₂ \ {1} = windowSupportSet_v12 1 (M₂ - 1) := by
    ext j
    simp only [S0M, windowSupportSet_v12, Set.mem_sdiff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    have : ((1 + (M₂ - 1) : ℕ) : ℤ) = (M₂ : ℤ) := by
      exact_mod_cast (show 1 + (M₂ - 1) = M₂ by omega)
    omega
  have hbin := binEntropy_bounds_Icc_v12 ⟨hth.1, hth.2.trans (by norm_num)⟩
  have h1m_pos : 0 < 1 - theta := sub_pos.mpr (lt_of_le_of_lt hth.2 (by norm_num))
  have h1m_le1 : 1 - theta ≤ 1 := sub_le_self 1 hth.1
  unfold cappedDualValue
  rw [hs0m_eq]
  have htail_abs :
      |(1 - theta) * dualValue (windowSupportSet_v12 1 (M₂ - 1))
        ((T - theta) / (1 - theta))| ≤
      |Real.log (partitionFn Splus 0)| +
        |min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))| := by
    rw [abs_mul, abs_of_pos h1m_pos]
    have hw_abs :
        |dualValue (windowSupportSet_v12 1 (M₂ - 1))
          ((T - theta) / (1 - theta))| ≤
        |Real.log (partitionFn Splus 0)| +
          |min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))| :=
      abs_le.mpr ⟨by
          linarith only [hd_win.1,
            neg_abs_le (min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))),
            abs_nonneg (Real.log (partitionFn Splus 0))],
        by
          linarith only [hd_win.2, le_abs_self (Real.log (partitionFn Splus 0)),
            abs_nonneg (min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8)))]⟩
    exact (mul_le_mul_of_nonneg_right h1m_le1 (abs_nonneg _)).trans ((one_mul _).le.trans hw_abs)
  have hq_th : Real.log 2 / 2 * theta ≤ Real.log 2 := by
    calc Real.log 2 / 2 * theta
        ≤ Real.log 2 / 2 * 2 :=
          mul_le_mul_of_nonneg_left (hth.2.trans (by norm_num))
            (div_nonneg (Real.log_pos one_lt_two).le zero_le_two)
      _ = Real.log 2 := by ring
  have hq_th_nn : 0 ≤ Real.log 2 / 2 * theta :=
    mul_nonneg (div_nonneg (Real.log_pos one_lt_two).le zero_le_two) hth.1
  rw [abs_le, hBF0_def]
  exact ⟨by linarith only [hbin.1, hq_th, (abs_le.mp htail_abs).1],
    by linarith only [hbin.2, hq_th_nn, (abs_le.mp htail_abs).2, Real.log_pos one_lt_two]⟩

private theorem abs_cappedDualValue_Sge1_le_v12
    {theta T B_F0 : ℝ}
    (hth : theta ∈ Set.Icc (0 : ℝ) (1 / 20))
    (hT : T ∈ KcapInterval)
    (hBF0_def : B_F0 = |Real.log (partitionFn Splus 0)| +
      |min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))| + Real.log 2 + 1) :
    |cappedDualValue Sge1 theta T| ≤ B_F0 := by
  have hu_icc := (reducedTarget_mem_Icc_and_Ioo_v12 hth hT).1
  have hd_inf := dualValue_infinite_bounds_on_padded (m := 2) le_rfl
    (T := (T - theta) / (1 - theta))
    ⟨by linarith only [hu_icc.1], by linarith only [hu_icc.2]⟩
  have hbin := binEntropy_bounds_Icc_v12 ⟨hth.1, hth.2.trans (by norm_num)⟩
  have h1m_pos : 0 < 1 - theta := sub_pos.mpr (lt_of_le_of_lt hth.2 (by norm_num))
  have h1m_le1 : 1 - theta ≤ 1 := sub_le_self 1 hth.1
  unfold cappedDualValue
  rw [← infiniteSupportSet_two_eq_sge1_diff_one]
  have htail_abs :
      |(1 - theta) * dualValue (infiniteSupportSet 2) ((T - theta) / (1 - theta))| ≤
      |Real.log (partitionFn Splus 0)| +
        |min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))| := by
    rw [abs_mul, abs_of_pos h1m_pos]
    have hw_abs :
        |dualValue (infiniteSupportSet 2) ((T - theta) / (1 - theta))| ≤
        |Real.log (partitionFn Splus 0)| +
          |min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))| :=
      abs_le.mpr ⟨by
          linarith only [hd_inf.1,
            neg_abs_le (min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))),
            abs_nonneg (Real.log (partitionFn Splus 0))],
        by
          linarith only [hd_inf.2, le_abs_self (Real.log (partitionFn Splus 0)),
            abs_nonneg (min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8)))]⟩
    exact (mul_le_mul_of_nonneg_right h1m_le1 (abs_nonneg _)).trans ((one_mul _).le.trans hw_abs)
  have hq_th : Real.log 2 / 2 * theta ≤ Real.log 2 := by
    calc Real.log 2 / 2 * theta
        ≤ Real.log 2 / 2 * 2 :=
          mul_le_mul_of_nonneg_left (hth.2.trans (by norm_num))
            (div_nonneg (Real.log_pos one_lt_two).le zero_le_two)
      _ = Real.log 2 := by ring
  have hq_th_nn : 0 ≤ Real.log 2 / 2 * theta :=
    mul_nonneg (div_nonneg (Real.log_pos one_lt_two).le zero_le_two) hth.1
  rw [abs_le, hBF0_def]
  exact ⟨by linarith only [hbin.1, hq_th, (abs_le.mp htail_abs).1],
    by linarith only [hbin.2, hq_th_nn, (abs_le.mp htail_abs).2, Real.log_pos one_lt_two]⟩

private theorem prop53_iii_conj3_from_seps_v12
    {n m M' : ℕ}
    {r_inf0 r_infCo r_winCo r_win0 K_core K_sep η_root : ℝ}
    (hn_pos : 0 < (n : ℝ))
    (hLn16 : 16 ≤ logOrder n)
    (hWn : 1 ≤ logLogOrder n)
    (hL5n : 100 * (Real.log (n : ℝ)) ^ 5 ≤ (n : ℝ))
    (hr_winCo_nn : 0 ≤ r_winCo)
    (hr_win0_nn : 0 ≤ r_win0)
    (hr_infCo_lo : phaseRootCenter n / 2 ≤ r_infCo)
    (hcMain2 : |phaseRootCenter n - (Real.log 2 / 2) * ((n : ℝ) / logOrder n)| ≤
      4 * (n : ℝ) * logLogOrder n / (logOrder n) ^ 2)
    (hwL_q16 : logLogOrder n ≤ (Real.log 2 / 16) * logOrder n)
    (hMuBds1 : mu n (phaseNat n + 1) ≤ universalShift n)
    (hMuBds2 : phaseDelta n ≤ deltaStar → mu n (phaseNat n) ≤ universalShift n)
    (hK_core_pos : 0 < K_core)
    (hKsep_def : K_sep = K_core + 40)
    (hη_root_pos : 0 < η_root)
    (hη_bds : ∀ td ∈ Set.Icc (0 : ℝ) (207 / 200),
      η_root ≤ phaseGain7 td ∧ η_root ≤ Real.log 2 - phaseGain7 td)
    (hSsm3 : logLogOrder n ≤ ((Real.log 2) ^ 2 / 8 * η_root / K_core) * logOrder n)
    (hsep_chi : |(r_inf0 - r_winCo) - (Real.log 2) ^ 2 / 4 *
        (Real.log 2 - 0 +
          dualValue {j : ℤ | ((m + 1 : ℕ) : ℤ) ≤ j ∧ j ≤ ((m + M' : ℕ) : ℤ)} (phaseTarget (phaseDelta n)) -
          dualValue {j : ℤ | (m : ℤ) ≤ j} (phaseTarget (phaseDelta n))) *
        ((n : ℝ) / (logOrder n) ^ 3)| ≤
      K_core * (n : ℝ) * logLogOrder n / (logOrder n) ^ 4)
    (hsep_zeta : |(r_win0 - r_infCo) - (Real.log 2) ^ 2 / 4 *
        (Real.log 2 - 0 +
          dualValue {j : ℤ | (m : ℤ) ≤ j} (phaseTarget (phaseDelta n)) -
          dualValue {j : ℤ | ((m + 1 : ℕ) : ℤ) ≤ j ∧ j ≤ ((m + M' : ℕ) : ℤ)} (phaseTarget (phaseDelta n))) *
        ((n : ℝ) / (logOrder n) ^ 3)| ≤
      K_core * (n : ℝ) * logLogOrder n / (logOrder n) ^ 4)
    (hsep_12 : |(r_winCo - r_infCo) - (Real.log 2) ^ 2 / 4 *
        (Real.log 2 - Real.log 2 +
          dualValue {j : ℤ | (m : ℤ) ≤ j} (phaseTarget (phaseDelta n)) -
          dualValue {j : ℤ | ((m + 1 : ℕ) : ℤ) ≤ j ∧ j ≤ ((m + M' : ℕ) : ℤ)} (phaseTarget (phaseDelta n))) *
        ((n : ℝ) / (logOrder n) ^ 3)| ≤
      K_core * (n : ℝ) * logLogOrder n / (logOrder n) ^ 4)
    (hsep_34 : |(r_win0 - r_inf0) - (Real.log 2) ^ 2 / 4 *
        (0 - 0 +
          dualValue {j : ℤ | (m : ℤ) ≤ j} (phaseTarget (phaseDelta n)) -
          dualValue {j : ℤ | ((m + 1 : ℕ) : ℤ) ≤ j ∧ j ≤ ((m + M' : ℕ) : ℤ)} (phaseTarget (phaseDelta n))) *
        ((n : ℝ) / (logOrder n) ^ 3)| ≤
      K_core * (n : ℝ) * logLogOrder n / (logOrder n) ^ 4) :
    let S_inf : Set ℤ := {j : ℤ | (m : ℤ) ≤ j}
    let S_win : Set ℤ := {j : ℤ | ((m + 1 : ℕ) : ℤ) ≤ j ∧ j ≤ ((m + M' : ℕ) : ℤ)}
    let t_n : ℝ := universalShift n
    let d_m : ℕ := Nat.ceil (mu n (phaseNat n + 1 - m) + t_n)
    let k_chi_minus : ℤ := ⌊r_inf0⌋ - (Nat.ceil t_n : ℤ) - 2 * (d_m : ℤ)
    let k_zeta_minus : ℤ := ⌊r_infCo⌋ - (Nat.ceil t_n : ℤ) - 4 * (d_m : ℤ)
    let k_co : ℕ := Nat.ceil r_winCo + 16
    let k_ch : ℕ := Nat.ceil r_win0 + Nat.ceil (Real.log (n : ℝ))
    let A_mM : ℝ := Real.log 2 - dualValue S_inf (phaseTarget (phaseDelta n)) +
      dualValue S_win (phaseTarget (phaseDelta n))
    (|((k_chi_minus : ℝ) - (k_co : ℝ)) -
        ((Real.log 2) ^ 2 / 4 * A_mM * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3) -
          2 * (d_m : ℝ))| ≤
      K_sep * (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ 4) ∧
    (|((k_ch : ℝ) - (k_zeta_minus : ℝ)) -
        ((Real.log 2) ^ 2 / 4 * (2 * Real.log 2 - A_mM) *
            ((n : ℝ) / (Real.log (n : ℝ)) ^ 3) +
          4 * (d_m : ℝ))| ≤
      K_sep * (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ 4) ∧
    (m = boundaryShift (phaseDelta n) → M' = 7 →
      A_mM = phaseGain7 (shiftedPhase (phaseDelta n)) ∧
      r_infCo < r_winCo ∧ r_winCo < r_inf0 ∧ r_inf0 < r_win0 ∧
      1 ≤ k_zeta_minus ∧ k_zeta_minus ≤ k_chi_minus ∧
      (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) -
          K_sep * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) *
          ((n : ℝ) / (Real.log (n : ℝ)) ^ 3) ≤
        (k_chi_minus : ℝ) - (k_co : ℝ) - universalAllowance n ∧
      (k_ch : ℝ) + universalAllowance n - (k_zeta_minus : ℝ) ≤
        (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) +
            K_sep * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) *
          ((n : ℝ) / (Real.log (n : ℝ)) ^ 3)) := by
  intro S_inf S_win t_n d_m k_chi_minus k_zeta_minus k_co k_ch A_mM
  set L : ℝ := logOrder n
  set w : ℝ := logLogOrder n
  have hL_pos : 0 < L := by linarith only [hLn16]
  have hw_pos : 0 < w := by linarith only [hWn]
  have htn_nn : 0 ≤ t_n := by dsimp [t_n]; unfold universalShift; positivity
  have htn_le : t_n ≤ (n : ℝ) * w / L ^ 4 := by
    dsimp [t_n, L, w]; unfold universalShift logOrder logLogOrder
    calc (n : ℝ) / (Real.log (n : ℝ)) ^ 5
        ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 4 :=
          div_le_div_of_nonneg_left hn_pos.le (pow_pos hL_pos 4)
            (by
              have hL1 : 1 ≤ Real.log (n : ℝ) := by
                change 16 ≤ Real.log (n : ℝ) at hLn16; linarith only [hLn16]
              calc (Real.log (n : ℝ)) ^ 4 = (Real.log (n : ℝ)) ^ 4 * 1 := (mul_one _).symm
                _ ≤ (Real.log (n : ℝ)) ^ 4 * Real.log (n : ℝ) :=
                    mul_le_mul_of_nonneg_left hL1 (by positivity)
                _ = (Real.log (n : ℝ)) ^ 5 := by ring)
      _ ≤ (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ 4 :=
          div_le_div_of_nonneg_right (le_mul_of_one_le_right hn_pos.le hWn) (by positivity)
  have hunit_le : 1 ≤ (n : ℝ) * w / L ^ 4 := by
    have h100 : 100 ≤ (n : ℝ) / L ^ 5 := (le_div_iff₀ (pow_pos hL_pos 5)).mpr hL5n
    calc (1 : ℝ) ≤ (n : ℝ) / L ^ 5 := by linarith only [h100]
      _ = t_n := rfl
      _ ≤ (n : ℝ) * w / L ^ 4 := htn_le
  have hlog_le_err : L ≤ (n : ℝ) * w / L ^ 4 := by
    have h100 : 100 * L ^ 5 ≤ (n : ℝ) := hL5n
    rw [le_div_iff₀ (pow_pos hL_pos 4)]
    calc L * L ^ 4 = L ^ 5 := by ring
      _ ≤ (n : ℝ) * 1 := by linarith only [h100, pow_pos hL_pos 5]
      _ ≤ (n : ℝ) * w := mul_le_mul_of_nonneg_left hWn hn_pos.le
  have hfl_inf0 := Int.floor_le r_inf0
  have hfl_inf0_gt := Int.lt_floor_add_one r_inf0
  have hfl_infCo := Int.floor_le r_infCo
  have hfl_infCo_gt := Int.lt_floor_add_one r_infCo
  have hcl_tn := Nat.le_ceil t_n
  have hcl_tn_lt := Nat.ceil_lt_add_one htn_nn
  have hcl_wCo := Nat.le_ceil r_winCo
  have hcl_wCo_lt := Nat.ceil_lt_add_one hr_winCo_nn
  have hcl_w0 := Nat.le_ceil r_win0
  have hcl_w0_lt := Nat.ceil_lt_add_one hr_win0_nn
  have hcl_L := Nat.le_ceil L
  have hcl_L_lt := Nat.ceil_lt_add_one hL_pos.le
  have hround_chi :
      |((k_chi_minus : ℝ) - (k_co : ℝ)) - ((r_inf0 - r_winCo) - 2 * (d_m : ℝ))| ≤
        20 * ((n : ℝ) * w / L ^ 4) := by
    dsimp [k_chi_minus, k_co]
    push_cast
    rw [abs_le]
    exact ⟨by linarith only [hfl_inf0_gt, hcl_tn_lt, hcl_wCo_lt, htn_le, hunit_le],
      by linarith only [hfl_inf0, hcl_tn, hcl_wCo, htn_nn, hunit_le]⟩
  have hround_zeta :
      |((k_ch : ℝ) - (k_zeta_minus : ℝ)) - ((r_win0 - r_infCo) + 4 * (d_m : ℝ))| ≤
        6 * ((n : ℝ) * w / L ^ 4) := by
    dsimp [k_ch, k_zeta_minus]
    push_cast
    have hL_eq : Real.log (n : ℝ) = L := rfl
    rw [hL_eq]
    rw [abs_le]
    exact ⟨by linarith only [hcl_w0, hcl_L, hfl_infCo, hcl_tn, htn_nn, hunit_le, hL_pos],
      by linarith only [hcl_w0_lt, hcl_L_lt, hfl_infCo_gt, hcl_tn_lt, htn_le, hunit_le, hlog_le_err]⟩
  have h520_1 :
      |((k_chi_minus : ℝ) - (k_co : ℝ)) -
          ((Real.log 2) ^ 2 / 4 * A_mM * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3) -
            2 * (d_m : ℝ))| ≤
        K_sep * (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ 4 := by
    have hA_eq : Real.log 2 - 0 + dualValue S_win (phaseTarget (phaseDelta n)) -
        dualValue S_inf (phaseTarget (phaseDelta n)) = A_mM := by
      dsimp [A_mM]; ring
    have hsep_chi' := hsep_chi
    dsimp only [S_inf, S_win] at hA_eq
    rw [hA_eq] at hsep_chi'
    have htri :
        |((k_chi_minus : ℝ) - (k_co : ℝ)) -
            ((Real.log 2) ^ 2 / 4 * A_mM * ((n : ℝ) / L ^ 3) - 2 * (d_m : ℝ))| ≤
          |((k_chi_minus : ℝ) - (k_co : ℝ)) - ((r_inf0 - r_winCo) - 2 * (d_m : ℝ))| +
            |(r_inf0 - r_winCo) - (Real.log 2) ^ 2 / 4 * A_mM * ((n : ℝ) / L ^ 3)| := by
      have hid : ((k_chi_minus : ℝ) - (k_co : ℝ)) -
          ((Real.log 2) ^ 2 / 4 * A_mM * ((n : ℝ) / L ^ 3) - 2 * (d_m : ℝ)) =
        (((k_chi_minus : ℝ) - (k_co : ℝ)) - ((r_inf0 - r_winCo) - 2 * (d_m : ℝ))) +
          ((r_inf0 - r_winCo) - (Real.log 2) ^ 2 / 4 * A_mM * ((n : ℝ) / L ^ 3)) := by ring
      rw [hid]; exact abs_add_le _ _
    have hsum : 20 * ((n : ℝ) * w / L ^ 4) + K_core * (n : ℝ) * w / L ^ 4 ≤
        K_sep * (n : ℝ) * w / L ^ 4 := by
      have hpos_f : 0 ≤ (n : ℝ) * w / L ^ 4 := by positivity
      rw [hKsep_def]
      calc 20 * ((n : ℝ) * w / L ^ 4) + K_core * (n : ℝ) * w / L ^ 4
          = (K_core + 20) * ((n : ℝ) * w / L ^ 4) := by ring
        _ ≤ (K_core + 40) * ((n : ℝ) * w / L ^ 4) :=
            mul_le_mul_of_nonneg_right (by linarith only) hpos_f
        _ = (K_core + 40) * (n : ℝ) * w / L ^ 4 := by ring
    simpa only [L, w, logOrder, logLogOrder] using htri.trans ((add_le_add hround_chi hsep_chi').trans hsum)
  have h520_2 :
      |((k_ch : ℝ) - (k_zeta_minus : ℝ)) -
          ((Real.log 2) ^ 2 / 4 * (2 * Real.log 2 - A_mM) *
              ((n : ℝ) / (Real.log (n : ℝ)) ^ 3) +
            4 * (d_m : ℝ))| ≤
        K_sep * (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ 4 := by
    have hA_eq : Real.log 2 - 0 + dualValue S_inf (phaseTarget (phaseDelta n)) -
        dualValue S_win (phaseTarget (phaseDelta n)) = 2 * Real.log 2 - A_mM := by
      dsimp [A_mM]; ring
    have hsep_zeta' := hsep_zeta
    dsimp only [S_inf, S_win] at hA_eq
    rw [hA_eq] at hsep_zeta'
    have htri :
        |((k_ch : ℝ) - (k_zeta_minus : ℝ)) -
            ((Real.log 2) ^ 2 / 4 * (2 * Real.log 2 - A_mM) * ((n : ℝ) / L ^ 3) +
              4 * (d_m : ℝ))| ≤
          |((k_ch : ℝ) - (k_zeta_minus : ℝ)) - ((r_win0 - r_infCo) + 4 * (d_m : ℝ))| +
            |(r_win0 - r_infCo) -
              (Real.log 2) ^ 2 / 4 * (2 * Real.log 2 - A_mM) * ((n : ℝ) / L ^ 3)| := by
      have hid : ((k_ch : ℝ) - (k_zeta_minus : ℝ)) -
          ((Real.log 2) ^ 2 / 4 * (2 * Real.log 2 - A_mM) * ((n : ℝ) / L ^ 3) +
            4 * (d_m : ℝ)) =
        (((k_ch : ℝ) - (k_zeta_minus : ℝ)) - ((r_win0 - r_infCo) + 4 * (d_m : ℝ))) +
          ((r_win0 - r_infCo) -
            (Real.log 2) ^ 2 / 4 * (2 * Real.log 2 - A_mM) * ((n : ℝ) / L ^ 3)) := by ring
      rw [hid]; exact abs_add_le _ _
    have hsum : 6 * ((n : ℝ) * w / L ^ 4) + K_core * (n : ℝ) * w / L ^ 4 ≤
        K_sep * (n : ℝ) * w / L ^ 4 := by
      have hpos_f : 0 ≤ (n : ℝ) * w / L ^ 4 := by positivity
      rw [hKsep_def]
      calc 6 * ((n : ℝ) * w / L ^ 4) + K_core * (n : ℝ) * w / L ^ 4
          = (K_core + 6) * ((n : ℝ) * w / L ^ 4) := by ring
        _ ≤ (K_core + 40) * ((n : ℝ) * w / L ^ 4) :=
            mul_le_mul_of_nonneg_right (by linarith only) hpos_f
        _ = (K_core + 40) * (n : ℝ) * w / L ^ 4 := by ring
    simpa only [L, w, logOrder, logLogOrder] using htri.trans ((add_le_add hround_zeta hsep_zeta').trans hsum)
  refine ⟨h520_1, h520_2, fun hm_bs hM7 ↦ ?_⟩
  subst hM7
  have hA_eq_gain7 : A_mM = phaseGain7 (shiftedPhase (phaseDelta n)) := by
    dsimp only [A_mM, S_inf, S_win]
    unfold shiftedPhase
    rw [hm_bs]
    unfold boundaryShift
    by_cases hlt_ds : phaseDelta n < deltaStar
    · simp only [hlt_ds, ↓reduceIte]
      have hS1 : {j : ℤ | ((1 : ℕ) : ℤ) ≤ j} = Sge1 := by ext j; simp [Sge1]
      have hW17 : {j : ℤ | ((1 + 1 : ℕ) : ℤ) ≤ j ∧ j ≤ ((1 + 7 : ℕ) : ℤ)} = S17 := by
        ext j
        simp only [S17, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
        omega
      rw [hS1, hW17, Nat.cast_one, add_comm (phaseDelta n) 1]
      exact dualValue_Sge1_sub_S17_eq_phaseGain7_add_one ⟨phaseDelta_nonneg n, hlt_ds.le⟩
    · simp only [hlt_ds, ↓reduceIte]
      have hS0 : {j : ℤ | ((0 : ℕ) : ℤ) ≤ j} = Sge0 := by ext j; simp [Sge0]
      have hW07 : {j : ℤ | ((0 + 1 : ℕ) : ℤ) ≤ j ∧ j ≤ ((0 + 7 : ℕ) : ℤ)} = S07 := by
        ext j
        simp only [S07, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
        omega
      rw [hS0, hW07, Nat.cast_zero, add_zero]
      rfl
  have hmu_le_tn : mu n (phaseNat n + 1 - m) ≤ t_n := by
    rw [hm_bs]; unfold boundaryShift
    by_cases hlt_ds : phaseDelta n < deltaStar
    · simp only [hlt_ds, ↓reduceIte, Nat.add_sub_cancel]
      exact hMuBds2 hlt_ds.le
    · simp only [hlt_ds, ↓reduceIte, Nat.sub_zero]
      exact hMuBds1
  have hdm_le : (d_m : ℝ) ≤ 2 * t_n + 1 := by
    have hc := Nat.ceil_lt_add_one (add_nonneg (mu_nonneg n (phaseNat n + 1 - m)) htn_nn)
    change (Nat.ceil (mu n (phaseNat n + 1 - m) + t_n) : ℝ) ≤ 2 * t_n + 1
    linarith only [hc, hmu_le_tn]
  have htd_mem : shiftedPhase (phaseDelta n) ∈ Set.Icc (0 : ℝ) (207 / 200) :=
    shiftedPhase_mem_Icc_wide (phaseDelta_mem_Ico n)
  obtain ⟨hη_A, hη_sub⟩ := hη_bds _ htd_mem
  have herr_half : K_core * (n : ℝ) * w / L ^ 4 ≤
      (Real.log 2) ^ 2 / 8 * η_root * ((n : ℝ) / L ^ 3) := by
    calc K_core * (n : ℝ) * w / L ^ 4
        = (K_core * ((n : ℝ) / L ^ 4)) * w := by ring
      _ ≤ (K_core * ((n : ℝ) / L ^ 4)) * (((Real.log 2) ^ 2 / 8 * η_root / K_core) * L) :=
          mul_le_mul_of_nonneg_left hSsm3 (by positivity)
      _ = (Real.log 2) ^ 2 / 8 * η_root * ((n : ℝ) / L ^ 3) := by
          field_simp [hK_core_pos.ne', hL_pos.ne']
  have hpos_step : 0 < (Real.log 2) ^ 2 / 8 * η_root * ((n : ℝ) / L ^ 3) := by
    have := Real.log_pos one_lt_two; positivity
  have hlt_12 : r_infCo < r_winCo := by
    have hd_eq : Real.log 2 - Real.log 2 + dualValue S_inf (phaseTarget (phaseDelta n)) -
        dualValue S_win (phaseTarget (phaseDelta n)) =
        Real.log 2 - phaseGain7 (shiftedPhase (phaseDelta n)) := by
      rw [← hA_eq_gain7]; dsimp [A_mM]; ring
    have hsep_12' := hsep_12
    dsimp only [S_inf, S_win] at hd_eq
    rw [hd_eq] at hsep_12'
    have hmain_ge : (Real.log 2) ^ 2 / 4 * η_root * ((n : ℝ) / L ^ 3) ≤
        (Real.log 2) ^ 2 / 4 * (Real.log 2 - phaseGain7 (shiftedPhase (phaseDelta n))) *
          ((n : ℝ) / L ^ 3) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hη_sub (by positivity)
    linarith only [(abs_le.mp hsep_12').1, hmain_ge, herr_half, hpos_step]
  have hlt_23 : r_winCo < r_inf0 := by
    have hd_eq : Real.log 2 - 0 + dualValue S_win (phaseTarget (phaseDelta n)) -
        dualValue S_inf (phaseTarget (phaseDelta n)) =
        phaseGain7 (shiftedPhase (phaseDelta n)) := by
      rw [← hA_eq_gain7]; dsimp [A_mM]; ring
    have hsep_chi' := hsep_chi
    dsimp only [S_inf, S_win] at hd_eq
    rw [hd_eq] at hsep_chi'
    have hmain_ge : (Real.log 2) ^ 2 / 4 * η_root * ((n : ℝ) / L ^ 3) ≤
        (Real.log 2) ^ 2 / 4 * phaseGain7 (shiftedPhase (phaseDelta n)) *
          ((n : ℝ) / L ^ 3) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hη_A (by positivity)
    linarith only [(abs_le.mp hsep_chi').1, hmain_ge, herr_half, hpos_step]
  have hlt_34 : r_inf0 < r_win0 := by
    have hd_eq : 0 - 0 + dualValue S_inf (phaseTarget (phaseDelta n)) -
        dualValue S_win (phaseTarget (phaseDelta n)) =
        Real.log 2 - phaseGain7 (shiftedPhase (phaseDelta n)) := by
      rw [← hA_eq_gain7]; dsimp [A_mM]; ring
    have hsep_34' := hsep_34
    dsimp only [S_inf, S_win] at hd_eq
    rw [hd_eq] at hsep_34'
    have hmain_ge : (Real.log 2) ^ 2 / 4 * η_root * ((n : ℝ) / L ^ 3) ≤
        (Real.log 2) ^ 2 / 4 * (Real.log 2 - phaseGain7 (shiftedPhase (phaseDelta n))) *
          ((n : ℝ) / L ^ 3) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hη_sub (by positivity)
    linarith only [(abs_le.mp hsep_34').1, hmain_ge, herr_half, hpos_step]
  have hk_zeta_pos : 1 ≤ k_zeta_minus := by
    have hc_lo : (Real.log 2 / 4) * ((n : ℝ) / L) ≤ phaseRootCenter n := by
      have h1 : -(4 * (n : ℝ) * w / L ^ 2) ≤
          phaseRootCenter n - (Real.log 2 / 2) * ((n : ℝ) / L) := (abs_le.mp hcMain2).1
      have h2 : 4 * (n : ℝ) * w / L ^ 2 ≤ (Real.log 2 / 4) * ((n : ℝ) / L) := by
        calc 4 * (n : ℝ) * w / L ^ 2
            ≤ 4 * (n : ℝ) * ((Real.log 2 / 16) * L) / L ^ 2 := by
              apply div_le_div_of_nonneg_right _ (sq_nonneg L)
              exact mul_le_mul_of_nonneg_left hwL_q16 (by positivity)
          _ = (Real.log 2 / 4) * ((n : ℝ) / L) := by field_simp [hL_pos.ne']; ring
      linarith only [h1, h2]
    have htn_small : t_n ≤ (1 / 1000) * ((n : ℝ) / L) := by
      dsimp [t_n]; unfold universalShift
      have hL4 : (1000 : ℝ) ≤ L ^ 4 := by
        calc (1000 : ℝ) ≤ (16 : ℝ) ^ 4 := by norm_num
          _ ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hLn16 4
      calc (n : ℝ) / (Real.log (n : ℝ)) ^ 5
          = (n : ℝ) / (L ^ 4 * L) := by dsimp [L]; unfold logOrder; ring
        _ ≤ (n : ℝ) / (1000 * L) :=
            div_le_div_of_nonneg_left hn_pos.le (by positivity)
              (mul_le_mul_of_nonneg_right hL4 hL_pos.le)
        _ = (1 / 1000) * ((n : ℝ) / L) := by ring
    have hnL_ge : (1000 : ℝ) ≤ (n : ℝ) / L := by
      rw [le_div_iff₀ hL_pos]
      have hL4 : (1000 : ℝ) ≤ L ^ 4 := by
        calc (1000 : ℝ) ≤ (16 : ℝ) ^ 4 := by norm_num
          _ ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hLn16 4
      have hm : 1000 * L ≤ L ^ 5 := by
        calc 1000 * L ≤ L ^ 4 * L := mul_le_mul_of_nonneg_right hL4 hL_pos.le
          _ = L ^ 5 := by ring
      have hL_def : Real.log (n : ℝ) = L := rfl
      rw [hL_def] at hL5n
      linarith only [hm, hL5n, pow_pos hL_pos 5]
    have hc_lo_num : (16 / 100 : ℝ) * ((n : ℝ) / L) ≤ phaseRootCenter n := by
      have hq4 : (16 / 100 : ℝ) * ((n : ℝ) / L) ≤ (Real.log 2 / 4) * ((n : ℝ) / L) :=
        mul_le_mul_of_nonneg_right (by linarith only [Real.log_two_gt_d9]) (div_nonneg hn_pos.le hL_pos.le)
      exact hq4.trans hc_lo
    have hreal_ge : (2 : ℝ) ≤ (k_zeta_minus : ℝ) := by
      dsimp [k_zeta_minus]; push_cast
      linarith only [hfl_infCo_gt, hcl_tn_lt, hdm_le, hr_infCo_lo, hc_lo_num, htn_small, hnL_ge]
    exact_mod_cast (show (1 : ℤ) ≤ k_zeta_minus by
      exact Int.lt_iff_add_one_le.mp
        (by exact_mod_cast (show (0 : ℝ) < (k_zeta_minus : ℝ) by linarith only [hreal_ge])))
  have hk_le_chi : k_zeta_minus ≤ k_chi_minus := by
    have hfl_mono : ⌊r_infCo⌋ ≤ ⌊r_inf0⌋ := Int.floor_mono (hlt_12.trans hlt_23).le
    dsimp [k_zeta_minus, k_chi_minus]
    omega
  have hall_le : universalAllowance n = 2 * t_n := by
    dsimp [t_n]; unfold universalAllowance universalShift; ring
  have hbr_lo :
      (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) -
          K_sep * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) *
          ((n : ℝ) / (Real.log (n : ℝ)) ^ 3) ≤
        (k_chi_minus : ℝ) - (k_co : ℝ) - universalAllowance n := by
    have hd_eq : Real.log 2 - 0 + dualValue S_win (phaseTarget (phaseDelta n)) -
        dualValue S_inf (phaseTarget (phaseDelta n)) =
        phaseGain7 (shiftedPhase (phaseDelta n)) := by
      rw [← hA_eq_gain7]; dsimp [A_mM]; ring
    have hsep_chi' := hsep_chi
    dsimp only [S_inf, S_win] at hd_eq
    rw [hd_eq] at hsep_chi'
    have h1 := (abs_le.mp hsep_chi').1
    have h2 := (abs_le.mp hround_chi).1
    have hdm_tn : 2 * (d_m : ℝ) + universalAllowance n ≤ 8 * ((n : ℝ) * w / L ^ 4) := by
      rw [hall_le]
      linarith only [hdm_le, htn_le, hunit_le]
    have hlhs_rew :
        (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - K_sep * w / L) * ((n : ℝ) / L ^ 3) =
          lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) * ((n : ℝ) / L ^ 3) -
            (K_core + 40) * ((n : ℝ) * w / L ^ 4) := by
      rw [hKsep_def]; field_simp [hL_pos.ne']
    have hexp_K : (K_core + 40) * ((n : ℝ) * w / L ^ 4) =
        K_core * (n : ℝ) * w / L ^ 4 + 40 * ((n : ℝ) * w / L ^ 4) := by ring
    have hmain_eq : (Real.log 2) ^ 2 / 4 * phaseGain7 (shiftedPhase (phaseDelta n)) =
        lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) := rfl
    have hpos_err : 0 ≤ (n : ℝ) * w / L ^ 4 := by positivity
    change (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - K_sep * w / L) * ((n : ℝ) / L ^ 3) ≤ _
    rw [hmain_eq] at h1
    linarith only [hlhs_rew, hexp_K, h1, h2, hdm_tn, hpos_err]
  have hbr_hi :
      (k_ch : ℝ) + universalAllowance n - (k_zeta_minus : ℝ) ≤
        (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) +
            K_sep * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) *
          ((n : ℝ) / (Real.log (n : ℝ)) ^ 3) := by
    have hd_eq : Real.log 2 - 0 + dualValue S_inf (phaseTarget (phaseDelta n)) -
        dualValue S_win (phaseTarget (phaseDelta n)) =
        2 * Real.log 2 - phaseGain7 (shiftedPhase (phaseDelta n)) := by
      rw [← hA_eq_gain7]; dsimp [A_mM]; ring
    have hsep_zeta' := hsep_zeta
    dsimp only [S_inf, S_win] at hd_eq
    rw [hd_eq] at hsep_zeta'
    have h1 := (abs_le.mp hsep_zeta').2
    have h2 := (abs_le.mp hround_zeta).2
    have hdm_tn : 4 * (d_m : ℝ) + universalAllowance n ≤ 14 * ((n : ℝ) * w / L ^ 4) := by
      rw [hall_le]
      linarith only [hdm_le, htn_le, hunit_le]
    have hrhs_rew :
        (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + K_sep * w / L) * ((n : ℝ) / L ^ 3) =
          upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) * ((n : ℝ) / L ^ 3) +
            (K_core + 40) * ((n : ℝ) * w / L ^ 4) := by
      rw [hKsep_def]; field_simp [hL_pos.ne']
    have hexp_K : (K_core + 40) * ((n : ℝ) * w / L ^ 4) =
        K_core * (n : ℝ) * w / L ^ 4 + 40 * ((n : ℝ) * w / L ^ 4) := by ring
    have hmain_eq : (Real.log 2) ^ 2 / 4 *
        (2 * Real.log 2 - phaseGain7 (shiftedPhase (phaseDelta n))) =
        upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) := rfl
    have hpos_err : 0 ≤ (n : ℝ) * w / L ^ 4 := by positivity
    change _ ≤ (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + K_sep * w / L) * ((n : ℝ) / L ^ 3)
    rw [hmain_eq] at h1
    linarith only [hrhs_rew, hexp_K, h1, h2, hdm_tn, hpos_err]
  exact ⟨hA_eq_gain7, hlt_12, hlt_23, hlt_34, hk_zeta_pos, hk_le_chi, hbr_lo, hbr_hi⟩

/-- **Section 5.2 mixed `(5.19)` corridor-root separation and unconditional Proposition 5.3(iii) `(5.20)`:**
for every `M : ℕ` and corridor half-width constant `C ≥ 0`, there exists `K_sep > 0` such that
eventually:
1. **(Unconstrained infinite `S_{≥ m₁}` vs finite window `S_{m₂, M₂}`):**
   for all `m₁ ≤ 2`, `m₂ ≤ 1`, `7 ≤ M₂ ≤ M`, `τ₁, τ₂ ∈ [0, log 2]`, and corridor zeros `r₁, r₂`,
   `|(r₁ - r₂) - (log 2)² / 4 · (τ₂ - τ₁ + 𝓕_{S_{m₂, M₂}}(T_{δ_n}) - 𝓕_{S_{≥ m₁}}(T_{δ_n})) · n / (log n)³| ≤ K_sep n log log n / (log n)⁴`;
2. **(Capped infinite `S_{≥ 1}^{=ϑ₁}` and unconstrained `S_{≥ m₁}` vs capped window `S_{0, M₂}^{=ϑ₂}`):**
   when `8 ≤ M` and `δ_n ∈ [0, δ_*]`, for all `8 ≤ M₂ ≤ M`, `ϑ₁, ϑ₂ ∈ [0, 1/20]`, `m₁ ≤ 2`,
   and `τ₁, τ₂ ∈ [0, log 2]`, both the `(S_{≥ 1}^{=ϑ₁}, S_{0, M₂}^{=ϑ₂})` and `(S_{≥ m₁}, S_{0, M₂}^{=ϑ₂})`
   corridor-root differences satisfy `(5.19)` with error `≤ K_sep n log log n / (log n)⁴`;
3. **(Unconditional Proposition 5.3(iii) `(5.20)` + concrete `(m_n, 7)` Phase-Refinement separation):**
   for all `m ≤ 1` and `7 ≤ M' ≤ M`, both equations of `(5.20)` hold unconditionally with error
   `≤ K_sep n log log n / (log n)⁴`; moreover, when `7 ≤ M`, `m = boundaryShift (phaseDelta n)`, and
   `M' = 7`, `A_{m_n, 7}(δ_n) = phaseGain7 (shiftedPhase (phaseDelta n))`,
   `r_{≥ m_n, log 2} < r_{S_{m_n, 7}, log 2} < r_{≥ m_n, 0} < r_{S_{m_n, 7}, 0}`, and the integer
   thresholds satisfy both Phase-Refinement bracket inequalities with error
   `K_sep log log n / log n`. -/
theorem eventually_allSupport_corridorRoot_separation_and_prop53_iii
    (M : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ K_sep : ℝ, 0 < K_sep ∧ ∀ᶠ n : ℕ in atTop,
      let F_inf : ℕ → ℝ → ℝ := fun m T ↦ ⨅ l : ℝ,
        (Real.log (∑ i ∈ Finset.Ico m (phaseNat n),
            Real.exp (l * (i : ℝ) +
              (Real.log ((phaseNat n).descFactorial i : ℝ) -
                (i : ℝ) * Real.log (phaseNat n : ℝ) -
                Real.log 2 / 2 * (i : ℝ) ^ 2))) - l * T)
      let F_win : ℕ → ℕ → ℝ → ℝ := fun m M' T ↦ ⨅ l : ℝ,
        (Real.log (∑ i ∈ Finset.Icc (m + 1) (m + M'),
            Real.exp (l * (i : ℝ) +
              (Real.log ((phaseNat n).descFactorial i : ℝ) -
                (i : ℝ) * Real.log (phaseNat n : ℝ) -
                Real.log 2 / 2 * (i : ℝ) ^ 2))) - l * T)
      let F_cap_inf : ℝ → ℝ → ℝ := fun theta T ↦
        binEntropy theta - Real.log 2 / 2 * theta +
          (1 - theta) * F_inf 2 ((T - theta) / (1 - theta))
      let F_cap_win : ℕ → ℝ → ℝ → ℝ := fun M' theta T ↦
        binEntropy theta - Real.log 2 / 2 * theta +
          (1 - theta) * (⨅ l : ℝ,
            (Real.log (∑ i ∈ Finset.Icc 2 M',
                Real.exp (l * (i : ℝ) +
                  (Real.log ((phaseNat n).descFactorial i : ℝ) -
                    (i : ℝ) * Real.log (phaseNat n : ℝ) -
                    Real.log 2 / 2 * (i : ℝ) ^ 2))) -
              l * ((T - theta) / (1 - theta))))
      let mkObj : (ℝ → ℝ) → ℝ → ℝ → ℝ := fun G tau s ↦
        (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + s - s * Real.log s +
          s * (profileDeficitAffineA (phaseNat n) +
            profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s +
            G (fourSizeTarget n (phaseNat n) s) + tau)
      let Corr : Set ℝ := Set.Icc
        (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
        (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n)
      (∀ (m₁ m₂ M₂ : ℕ), m₁ ≤ 2 → m₂ ≤ 1 → 7 ≤ M₂ → M₂ ≤ M →
        ∀ tau₁ ∈ Set.Icc (0 : ℝ) (Real.log 2),
          ∀ tau₂ ∈ Set.Icc (0 : ℝ) (Real.log 2),
            let S₁ : Set ℤ := {j : ℤ | (m₁ : ℤ) ≤ j}
            let S₂ : Set ℤ := {j : ℤ | ((m₂ + 1 : ℕ) : ℤ) ≤ j ∧ j ≤ ((m₂ + M₂ : ℕ) : ℤ)}
            ∀ r₁ ∈ Corr, ∀ r₂ ∈ Corr,
              mkObj (F_inf m₁) tau₁ r₁ = 0 → mkObj (F_win m₂ M₂) tau₂ r₂ = 0 →
                |(r₁ - r₂) - (Real.log 2) ^ 2 / 4 *
                    (tau₂ - tau₁ +
                      dualValue S₂ (phaseTarget (phaseDelta n)) -
                      dualValue S₁ (phaseTarget (phaseDelta n))) *
                    ((n : ℝ) / (Real.log (n : ℝ)) ^ 3)| ≤
                  K_sep * (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ 4) ∧
      (8 ≤ M → phaseDelta n ∈ Set.Icc (0 : ℝ) deltaStar →
        ∀ (M₂ : ℕ), 8 ≤ M₂ → M₂ ≤ M →
          ∀ theta₁ ∈ Set.Icc (0 : ℝ) (1 / 20),
            ∀ theta₂ ∈ Set.Icc (0 : ℝ) (1 / 20),
              ∀ tau₁ ∈ Set.Icc (0 : ℝ) (Real.log 2),
                ∀ tau₂ ∈ Set.Icc (0 : ℝ) (Real.log 2),
                  ∀ r₂ ∈ Corr, mkObj (F_cap_win M₂ theta₂) tau₂ r₂ = 0 →
                    (∀ r₁ ∈ Corr, mkObj (F_cap_inf theta₁) tau₁ r₁ = 0 →
                      |(r₁ - r₂) - (Real.log 2) ^ 2 / 4 *
                          (tau₂ - tau₁ +
                            cappedDualValue (S0M M₂) theta₂ (phaseTarget (phaseDelta n)) -
                            cappedDualValue Sge1 theta₁ (phaseTarget (phaseDelta n))) *
                          ((n : ℝ) / (Real.log (n : ℝ)) ^ 3)| ≤
                        K_sep * (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ 4) ∧
                    (∀ (m₁ : ℕ), m₁ ≤ 2 → ∀ r₁ ∈ Corr, mkObj (F_inf m₁) tau₁ r₁ = 0 →
                      |(r₁ - r₂) - (Real.log 2) ^ 2 / 4 *
                          (tau₂ - tau₁ +
                            cappedDualValue (S0M M₂) theta₂ (phaseTarget (phaseDelta n)) -
                            dualValue {j : ℤ | (m₁ : ℤ) ≤ j} (phaseTarget (phaseDelta n))) *
                          ((n : ℝ) / (Real.log (n : ℝ)) ^ 3)| ≤
                        K_sep * (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ 4)) ∧
      (∀ (m M' : ℕ), m ≤ 1 → 7 ≤ M' → M' ≤ M →
        ∀ r_inf0 ∈ Corr, ∀ r_infCo ∈ Corr, ∀ r_winCo ∈ Corr, ∀ r_win0 ∈ Corr,
          mkObj (F_inf m) 0 r_inf0 = 0 →
          mkObj (F_inf m) (Real.log 2) r_infCo = 0 →
          mkObj (F_win m M') (Real.log 2) r_winCo = 0 →
          mkObj (F_win m M') 0 r_win0 = 0 →
          let S_inf : Set ℤ := {j : ℤ | (m : ℤ) ≤ j}
          let S_win : Set ℤ := {j : ℤ | ((m + 1 : ℕ) : ℤ) ≤ j ∧ j ≤ ((m + M' : ℕ) : ℤ)}
          let t_n : ℝ := universalShift n
          let d_m : ℕ := Nat.ceil (mu n (phaseNat n + 1 - m) + t_n)
          let k_chi_minus : ℤ := ⌊r_inf0⌋ - (Nat.ceil t_n : ℤ) - 2 * (d_m : ℤ)
          let k_zeta_minus : ℤ := ⌊r_infCo⌋ - (Nat.ceil t_n : ℤ) - 4 * (d_m : ℤ)
          let k_co : ℕ := Nat.ceil r_winCo + 16
          let k_ch : ℕ := Nat.ceil r_win0 + Nat.ceil (Real.log (n : ℝ))
          let A_mM : ℝ := Real.log 2 - dualValue S_inf (phaseTarget (phaseDelta n)) +
            dualValue S_win (phaseTarget (phaseDelta n))
          (|((k_chi_minus : ℝ) - (k_co : ℝ)) -
              ((Real.log 2) ^ 2 / 4 * A_mM * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3) -
                2 * (d_m : ℝ))| ≤
            K_sep * (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ 4) ∧
          (|((k_ch : ℝ) - (k_zeta_minus : ℝ)) -
              ((Real.log 2) ^ 2 / 4 * (2 * Real.log 2 - A_mM) *
                  ((n : ℝ) / (Real.log (n : ℝ)) ^ 3) +
                4 * (d_m : ℝ))| ≤
            K_sep * (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ 4) ∧
          (m = boundaryShift (phaseDelta n) → M' = 7 →
            A_mM = phaseGain7 (shiftedPhase (phaseDelta n)) ∧
            r_infCo < r_winCo ∧ r_winCo < r_inf0 ∧ r_inf0 < r_win0 ∧
            1 ≤ k_zeta_minus ∧ k_zeta_minus ≤ k_chi_minus ∧
            (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) -
                K_sep * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) *
                ((n : ℝ) / (Real.log (n : ℝ)) ^ 3) ≤
              (k_chi_minus : ℝ) - (k_co : ℝ) - universalAllowance n ∧
            (k_ch : ℝ) + universalAllowance n - (k_zeta_minus : ℝ) ≤
              (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) +
                  K_sep * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) *
                ((n : ℝ) / (Real.log (n : ℝ)) ^ 3))) := by
  obtain ⟨C_dual_i, Alpha₀_i, hC_dual_i_pos, _, hInfDual⟩ := abs_infiniteFiniteEntropy_sub_dualValue_le
  obtain ⟨C_dual_c, Alpha₀_c, _, _, hCapInfDual⟩ := abs_cappedInfiniteFiniteEntropy_sub_cappedDualValue_le
  set C_dual : ℝ := max C_dual_i C_dual_c
  set Alpha₀ : ℕ := max Alpha₀_i Alpha₀_c
  have hC_dual_pos : 0 < C_dual := lt_max_of_lt_left hC_dual_i_pos
  obtain ⟨K_slope, hK_slope_pos, hSlopeEv⟩ := eventually_unrestrictedPhaseObjective_deriv_logLogRate C hC
  obtain ⟨Mtilt, hMtilt_nn, huniformTilt⟩ :=
    exists_eventually_forall_mem_Icc_abs_profileDeficitTilt_le
      (by norm_num : (-1 : ℝ) < 9 / 4) (by norm_num : (9 / 4 : ℝ) ≤ 17 / 4)
  obtain ⟨Ntilt, hNtilt⟩ := eventually_atTop.1 huniformTilt
  obtain ⟨η_root, hη_root_pos, hη_bds⟩ := exists_pos_le_phaseGain7_and_sub_log_two
  set K_E : ℝ := max C_dual (((1 + M : ℕ) : ℝ) ^ 2) + 2 * C * universalDualLip_v12
  set B_F0 : ℝ := |Real.log (partitionFn Splus 0)| +
    |min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))| + Real.log 2 + 1
  set B_H : ℝ := 5 * Mtilt + |Real.log (partitionFn Splus 0)| + 2 * B_F0 + 2 * Real.log 2 + 2
  set K_core : ℝ := (4 + C) * B_H + 4 * (K_E + 2 * C * Mtilt) + (K_slope + B_H) * B_H + 1
  set K_sep : ℝ := K_core + 40
  have hK_E_nn : 0 ≤ K_E := by
    have := universalDualLip_v12_nonneg
    have : 0 ≤ max C_dual (((1 + M : ℕ) : ℝ) ^ 2) := le_max_of_le_left hC_dual_pos.le
    dsimp [K_E]; positivity
  have hB_F0_nn : 0 ≤ B_F0 := by
    dsimp [B_F0]; linarith [Real.log_pos one_lt_two,
      abs_nonneg (Real.log (partitionFn Splus 0)),
      abs_nonneg (min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8)))]
  have hB_H_nn : 0 ≤ B_H := by
    dsimp [B_H]; linarith [Real.log_pos one_lt_two, abs_nonneg (Real.log (partitionFn Splus 0))]
  have hK_core_pos : 0 < K_core := by dsimp [K_core]; positivity
  have hK_sep_pos : 0 < K_sep := by dsimp [K_sep]; positivity
  refine ⟨K_sep, hK_sep_pos, ?_⟩
  have hphaseN : ∀ᶠ n : ℕ in atTop, max (max Ntilt Alpha₀) (2 * (1 + M) + 16) ≤ phaseNat n := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop
        ((max (max Ntilt Alpha₀) (2 * (1 + M) + 16) : ℕ) : ℝ),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact_mod_cast hn.trans hph.1
  set eps_small : ℝ := min (Real.log 2 / 16)
    (min (min (1 / (Real.log 2 * (K_slope + B_H + 1))) (1 / (K_E + 1)))
      ((Real.log 2) ^ 2 / 8 * η_root / K_core))
  have heps_pos : 0 < eps_small := by
    have := Real.log_pos one_lt_two
    dsimp [eps_small]
    exact lt_min (by positivity) (lt_min (lt_min (by positivity) (by positivity)) (by positivity))
  have hS_small : ∀ᶠ n : ℕ in atTop, ‖logLogOrder n‖ ≤ eps_small * ‖logOrder n‖ :=
    logLogOrder_isLittleO_logOrder.bound heps_pos
  have ho_L5 : (fun x : ℝ ↦ (Real.log x) ^ ((5 : ℕ) : ℝ)) =o[atTop] (fun x : ℝ ↦ x ^ (1 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop ((5 : ℕ) : ℝ) zero_lt_one
  have hL5_le_n : ∀ᶠ n : ℕ in atTop, 100 * (Real.log (n : ℝ)) ^ 5 ≤ (n : ℝ) := by
    have hb := (ho_L5.comp_tendsto tendsto_natCast_atTop_atTop).bound (by norm_num : (0 : ℝ) < 1 / 100)
    filter_upwards [hb, eventually_gt_atTop 2] with n hn hn2
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hL_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    dsimp only [Function.comp_apply] at hn
    rw [Real.rpow_natCast] at hn
    rw [Real.norm_eq_abs, abs_of_pos (pow_pos hL_pos 5), Real.rpow_one,
      Real.norm_eq_abs, abs_of_pos hn_pos] at hn
    linarith
  filter_upwards [hSlopeEv, hphaseN, hS_small, hL5_le_n,
    tendsto_logLogOrder_atTop.eventually_ge_atTop 2,
    tendsto_logOrder_atTop.eventually_ge_atTop 16,
    eventually_mu_phaseNat_succ_and_deltaStar_le_v12,
    eventually_phaseRootCenter_sub_main_logLogRate_v12,
    eventually_corridor_inv_target_logLogRate_v12 C hC,
    eventually_phaseRootLogLogCorridor_fourSize_domain C hC,
    eventually_phaseRootLogLogCorridor_fourSize_target_mem_Icc C hC,
    eventually_cappedInfinite_target_mem_KcapInterval C hC,
    eventually_phaseRoot_domain_pos_and_target_corridor,
    eventually_five_lt_phaseNat,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with
    n hSlope hphN hSsm hL5n hWn2 hLn16 hMuBds hcMain hInv hDom hTarget hKcap hcenterDom hfive hphase
  intro F_inf F_win F_cap_inf F_cap_win mkObj Corr
  have hFinf_eq : F_inf = infiniteFiniteEntropy (phaseNat n) := rfl
  have hFwin_eq : F_win = windowFiniteEntropy_v12 (phaseNat n) := rfl
  have hFcap_inf_eq : F_cap_inf = cappedInfiniteFiniteEntropy (phaseNat n) := rfl
  have hFcap_win_eq : ∀ M' : ℕ, 2 ≤ M' →
      F_cap_win M' = cappedWindowFiniteEntropy_v12 (phaseNat n) M' := by
    intro M' hM'2; ext theta T
    dsimp only [F_cap_win]
    unfold cappedWindowFiniteEntropy_v12 windowFiniteEntropy_v12 windowFinitePartition_v12
      infiniteFiniteScore
    rw [show 1 + 1 = 2 from rfl, show 1 + (M' - 1) = M' by omega]
  have hmkObj_eq : mkObj = genericPhaseObj_v12 n := rfl
  rw [hFinf_eq, hFwin_eq, hFcap_inf_eq, hmkObj_eq]
  clear hFinf_eq hFwin_eq hFcap_inf_eq hmkObj_eq F_inf F_win F_cap_inf mkObj
  have hKE_def : K_E = max C_dual (((1 + M : ℕ) : ℝ) ^ 2) + 2 * C * universalDualLip_v12 := rfl
  have hBF0_def : B_F0 = |Real.log (partitionFn Splus 0)| +
      |min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))| + Real.log 2 + 1 := rfl
  have hBH_def : B_H = 5 * Mtilt + |Real.log (partitionFn Splus 0)| + 2 * B_F0 + 2 * Real.log 2 + 2 := rfl
  have hKcore_def : K_core = (4 + C) * B_H + 4 * (K_E + 2 * C * Mtilt) + (K_slope + B_H) * B_H + 1 := rfl
  have hKsep_def : K_sep = K_core + 40 := rfl
  have heps_le_q16 : eps_small ≤ Real.log 2 / 16 := min_le_left _ _
  set L : ℝ := logOrder n
  set w : ℝ := logLogOrder n
  have hWn : 1 ≤ w := by dsimp [w]; linarith
  have hLn : 4 ≤ L := by dsimp [L]; linarith
  have hL_pos : 0 < L := by linarith
  have hw_pos : 0 < w := by linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_trans Nat.zero_lt_one hcenterDom.1.1)
  have halpha_N : Ntilt ≤ phaseNat n :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hphN
  have halpha_A0 : Alpha₀ ≤ phaseNat n :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hphN
  have halpha_M : 2 * (1 + M) + 16 ≤ phaseNat n := le_trans (le_max_right _ _) hphN
  rw [Real.norm_eq_abs, abs_of_pos hw_pos, Real.norm_eq_abs, abs_of_pos hL_pos] at hSsm
  have hSsm1 : w ≤ (1 / (Real.log 2 * (K_slope + B_H + 1))) * L :=
    hSsm.trans (mul_le_mul_of_nonneg_right
      ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))) hL_pos.le)
  have hSsm2 : w ≤ (1 / (K_E + 1)) * L :=
    hSsm.trans (mul_le_mul_of_nonneg_right
      ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))) hL_pos.le)
  have hSsm3 : w ≤ ((Real.log 2) ^ 2 / 8 * η_root / K_core) * L :=
    hSsm.trans (mul_le_mul_of_nonneg_right
      ((min_le_right _ _).trans (min_le_right _ _)) hL_pos.le)
  clear_value K_E B_F0 B_H K_core K_sep eps_small
  have hS_lower : (K_slope + B_H) * L * w ≤ (1 / Real.log 2) * L ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hSsm1
      (show (0 : ℝ) ≤ (K_slope + B_H + 1) * L by positivity)
    have hrhs : (K_slope + B_H + 1) * L *
        (1 / (Real.log 2 * (K_slope + B_H + 1)) * L) = (1 / Real.log 2) * L ^ 2 := by
      field_simp [(Real.log_pos one_lt_two).ne',
        (show (0 : ℝ) < K_slope + B_H + 1 by positivity).ne']
    have hlhs : (K_slope + B_H) * L * w ≤ (K_slope + B_H + 1) * L * w := by
      have : 0 ≤ L * w := mul_nonneg hL_pos.le hw_pos.le; linarith
    linarith
  have hKE_le1 : K_E * w / L ≤ 1 := by
    rw [div_le_iff₀ hL_pos, one_mul]
    have hm := mul_le_mul_of_nonneg_left hSsm2 (show (0 : ℝ) ≤ K_E + 1 by positivity)
    have hrhs : (K_E + 1) * (1 / (K_E + 1) * L) = L := by
      field_simp [(show (0 : ℝ) < K_E + 1 by positivity).ne']
    have hexp : (K_E + 1) * w = K_E * w + w := by ring
    linarith [hw_pos]
  have htilt_corr : ∀ s ∈ Corr,
      fourSizeTarget n (phaseNat n) s ∈ Set.Ioo (-1 : ℝ) ((phaseNat n : ℝ) - 1) ∧
        |profileDeficitTilt (phaseNat n) (fourSizeTarget n (phaseNat n) s)| ≤ Mtilt := by
    intro s hs
    exact hNtilt (phaseNat n) halpha_N _ (hTarget s hs)
  have hslope0 : ∀ s ∈ Corr,
      |deriv (unrestrictedPhaseObjective n) s - (2 / Real.log 2) * L ^ 2| ≤
        K_slope * L * w := by
    intro s hs
    have h0 := hSlope 0 ⟨le_rfl, (Real.log_pos one_lt_two).le⟩ s hs
    simpa only [zero_mul, add_zero, L, w, logOrder, logLogOrder] using h0
  have hUnrestAbs : ∀ s ∈ Corr,
      |finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) s)| ≤
        5 * Mtilt + |Real.log (partitionFn Splus 0)| :=
    fun s hs ↦ unrestrictedDeficitEntropy_abs_le_of_tilt_v12 hfive hMtilt_nn
      (hTarget s hs) (htilt_corr s hs).2
  -- Generic pair-application of `corridor_root_separation_master_v12`
  have hApplyMaster : ∀ {r₁ r₂ G₁ G₂ F₁_lim F₂_lim tau₁ tau₂ : ℝ},
      r₁ ∈ Corr → r₂ ∈ Corr →
      tau₁ ∈ Set.Icc (0 : ℝ) (Real.log 2) → tau₂ ∈ Set.Icc (0 : ℝ) (Real.log 2) →
      unrestrictedPhaseObjective n r₁ =
        r₁ * (finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) r₁) -
          G₁ - tau₁) →
      unrestrictedPhaseObjective n r₂ =
        r₂ * (finiteUnrestrictedDeficitEntropy (phaseNat n) (fourSizeTarget n (phaseNat n) r₂) -
          G₂ - tau₂) →
      |G₁ - F₁_lim| ≤ K_E * w / L →
      |G₂ - F₂_lim| ≤ K_E * w / L →
      |F₁_lim| ≤ B_F0 → |F₂_lim| ≤ B_F0 →
      |(r₁ - r₂) - (Real.log 2) ^ 2 / 4 * (tau₂ - tau₁ + F₂_lim - F₁_lim) *
          ((n : ℝ) / L ^ 3)| ≤
        K_core * (n : ℝ) * w / L ^ 4 := by
    intro r₁ r₂ G₁ G₂ F₁_lim F₂_lim tau₁ tau₂ hr₁ hr₂ htau₁ htau₂ heq₁ heq₂ hE₁ hE₂ hF₁ hF₂
    have hG₂_abs : |G₂| ≤ B_F0 + 1 := by
      have htri : |G₂| ≤ |G₂ - F₂_lim| + |F₂_lim| := by simpa using abs_add_le (G₂ - F₂_lim) F₂_lim
      linarith [hE₂, hKE_le1, hF₂]
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
      linarith [hBH_def, Real.log_pos one_lt_two, hB_F0_nn]
    have hΔ_abs : |tau₂ - tau₁ + F₂_lim - F₁_lim| ≤ B_H := by
      have htri : |tau₂ - tau₁ + F₂_lim - F₁_lim| ≤ |tau₂| + |tau₁| + |F₂_lim| + |F₁_lim| := by
        linarith [abs_sub (tau₂ - tau₁ + F₂_lim) F₁_lim, abs_add_le (tau₂ - tau₁) F₂_lim,
          abs_sub tau₂ tau₁]
      linarith [hBH_def, hMtilt_nn, abs_nonneg (Real.log (partitionFn Splus 0))]
    have hm := corridor_root_separation_master_v12 hC hMtilt_nn hK_E_nn hLn hWn hn_pos
      hcenterDom.2.1 hfive hphase.1 hcMain.1 hcMain.2
      (fun s hs ↦ ⟨(hInv.2 s hs).1, (hInv.2 s hs).2.1, (hInv.2 s hs).2.2.2⟩)
      hDom htilt_corr hslope0 hr₁ hr₂ heq₁ heq₂ hE₁ hE₂ hH₂_abs hΔ_abs hS_lower
    exact hm.trans (by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hw_pos.le
      apply mul_le_mul_of_nonneg_right _ hn_pos.le
      linarith [hKcore_def])
  have hT_delta_wide : phaseTarget (phaseDelta n) ∈ Set.Icc (9 / 4 : ℝ) (9 / 2) := by
    obtain ⟨h2lo, h2hi⟩ := two_div_log_two_bounds
    unfold phaseTarget
    exact ⟨by linarith [phaseDelta_lt_one n, h2lo], by linarith [phaseDelta_nonneg n, h2hi]⟩
  -- Error + bound helpers for the four support classes
  have hInfErr_and_Bds : ∀ {m' : ℕ} {r : ℝ}, m' ≤ 2 → r ∈ Corr →
      |infiniteFiniteEntropy (phaseNat n) m' (fourSizeTarget n (phaseNat n) r) -
          dualValue {j : ℤ | (m' : ℤ) ≤ j} (phaseTarget (phaseDelta n))| ≤ K_E * w / L ∧
        |dualValue {j : ℤ | (m' : ℤ) ≤ j} (phaseTarget (phaseDelta n))| ≤ B_F0 := by
    intro m' r hm' hr
    have hB_i : |dualValue {j : ℤ | (m' : ℤ) ≤ j} (phaseTarget (phaseDelta n))| ≤ B_F0 := by
      have hd_bds := dualValue_infinite_bounds_on_padded hm'
        (T := phaseTarget (phaseDelta n))
        ⟨by linarith only [hT_delta_wide.1], by linarith only [hT_delta_wide.2]⟩
      refine abs_le.mpr ?_
      change -B_F0 ≤ dualValue (infiniteSupportSet m') (phaseTarget (phaseDelta n)) ∧
        dualValue (infiniteSupportSet m') (phaseTarget (phaseDelta n)) ≤ B_F0
      rw [hBF0_def]
      exact ⟨by linarith only [hd_bds.1,
          neg_abs_le (min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))),
          abs_nonneg (Real.log (partitionFn Splus 0)), Real.log_pos one_lt_two],
        by linarith only [hd_bds.2, le_abs_self (Real.log (partitionFn Splus 0)),
          abs_nonneg (min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))),
          Real.log_pos one_lt_two]⟩
    set Tr : ℝ := fourSizeTarget n (phaseNat n) r
    have hTr_wide : Tr ∈ Set.Icc (9 / 4 : ℝ) (9 / 2) :=
      ⟨(hTarget r hr).1, by linarith only [(hTarget r hr).2]⟩
    have herr1 : |infiniteFiniteEntropy (phaseNat n) m' Tr - dualValue {j : ℤ | (m' : ℤ) ≤ j} Tr| ≤
        C_dual / (phaseNat n : ℝ) :=
      ((hInfDual ((le_max_left _ _).trans halpha_A0) hm' hTr_wide).2.2.2).trans
        (div_le_div_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
    have herr2 := (abs_dualValue_infinite_sub_le hm' hTr_wide hT_delta_wide).trans
      (mul_le_mul_of_nonneg_left (hInv.2 r hr).2.2.2 universalDualLip_v12_nonneg)
    have h1_le : C_dual / (phaseNat n : ℝ) ≤ max C_dual (((1 + M : ℕ) : ℝ) ^ 2) * w / L := by
      calc C_dual / (phaseNat n : ℝ)
          ≤ max C_dual (((1 + M : ℕ) : ℝ) ^ 2) / L :=
            div_le_div₀ (le_max_of_le_left hC_dual_pos.le) (le_max_left _ _) hL_pos hphase.1
        _ ≤ max C_dual (((1 + M : ℕ) : ℝ) ^ 2) * w / L :=
            div_le_div_of_nonneg_right
              (le_mul_of_one_le_right (le_max_of_le_left hC_dual_pos.le) hWn) hL_pos.le
    have htot : |infiniteFiniteEntropy (phaseNat n) m' Tr -
        dualValue {j : ℤ | (m' : ℤ) ≤ j} (phaseTarget (phaseDelta n))| ≤ K_E * w / L := by
      calc |infiniteFiniteEntropy (phaseNat n) m' Tr -
              dualValue {j : ℤ | (m' : ℤ) ≤ j} (phaseTarget (phaseDelta n))|
          ≤ |infiniteFiniteEntropy (phaseNat n) m' Tr - dualValue {j : ℤ | (m' : ℤ) ≤ j} Tr| +
              |dualValue {j : ℤ | (m' : ℤ) ≤ j} Tr -
                dualValue {j : ℤ | (m' : ℤ) ≤ j} (phaseTarget (phaseDelta n))| :=
            abs_sub_le _ _ _
        _ ≤ max C_dual (((1 + M : ℕ) : ℝ) ^ 2) * w / L +
              universalDualLip_v12 * (2 * C * w / L) :=
            add_le_add (herr1.trans h1_le) herr2
        _ = K_E * w / L := by rw [hKE_def]; ring
    exact ⟨htot, hB_i⟩
  have hWinErr_and_Bds : ∀ {m' M' : ℕ} {r : ℝ}, m' ≤ 1 → 7 ≤ M' → M' ≤ M → r ∈ Corr →
      let S_w : Set ℤ := {j : ℤ | ((m' + 1 : ℕ) : ℤ) ≤ j ∧ j ≤ ((m' + M' : ℕ) : ℤ)}
      |windowFiniteEntropy_v12 (phaseNat n) m' M' (fourSizeTarget n (phaseNat n) r) -
          dualValue S_w (phaseTarget (phaseDelta n))| ≤ K_E * w / L ∧
        |dualValue S_w (phaseTarget (phaseDelta n))| ≤ B_F0 := by
    intro m' M' r hm' hM'7 hM'M hr S_w
    have hB_w : |dualValue S_w (phaseTarget (phaseDelta n))| ≤ B_F0 := by
      have hd_bds := dualValue_window_bounds_on_padded_v12 hm' hM'7 (phaseTarget (phaseDelta n))
        ⟨by linarith only [hT_delta_wide.1], by linarith only [hT_delta_wide.2]⟩
      refine abs_le.mpr ?_
      change -B_F0 ≤ dualValue (windowSupportSet_v12 m' M') (phaseTarget (phaseDelta n)) ∧
        dualValue (windowSupportSet_v12 m' M') (phaseTarget (phaseDelta n)) ≤ B_F0
      rw [hBF0_def]
      exact ⟨by linarith only [hd_bds.1,
          neg_abs_le (min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))),
          abs_nonneg (Real.log (partitionFn Splus 0)), Real.log_pos one_lt_two],
        by linarith only [hd_bds.2, le_abs_self (Real.log (partitionFn Splus 0)),
          abs_nonneg (min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))),
          Real.log_pos one_lt_two]⟩
    set Tr : ℝ := fourSizeTarget n (phaseNat n) r
    have hTr_wide : Tr ∈ Set.Icc (9 / 4 : ℝ) (9 / 2) :=
      ⟨(hTarget r hr).1, by linarith only [(hTarget r hr).2]⟩
    have herr1 : |windowFiniteEntropy_v12 (phaseNat n) m' M' Tr - dualValue S_w Tr| ≤
        ((m' + M' : ℕ) : ℝ) ^ 2 / (phaseNat n : ℝ) :=
      (abs_windowFiniteEntropy_sub_dualValue_le hm' hM'7
        (by omega : 2 * (m' + M') ≤ phaseNat n) (hDom r hr).2).2
    have herr2 := (abs_dualValue_window_sub_le_v12 hm' hM'7 hTr_wide hT_delta_wide).trans
      (mul_le_mul_of_nonneg_left (hInv.2 r hr).2.2.2 universalDualLip_v12_nonneg)
    have hsq_le : ((m' + M' : ℕ) : ℝ) ^ 2 / (phaseNat n : ℝ) ≤
        max C_dual (((1 + M : ℕ) : ℝ) ^ 2) * w / L := by
      have hm_le : ((m' + M' : ℕ) : ℝ) ^ 2 ≤ ((1 + M : ℕ) : ℝ) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (by omega)) 2
      calc ((m' + M' : ℕ) : ℝ) ^ 2 / (phaseNat n : ℝ)
          ≤ max C_dual (((1 + M : ℕ) : ℝ) ^ 2) / L :=
            div_le_div₀ (le_max_of_le_right (sq_nonneg _))
              (hm_le.trans (le_max_right _ _)) hL_pos hphase.1
        _ ≤ max C_dual (((1 + M : ℕ) : ℝ) ^ 2) * w / L :=
            div_le_div_of_nonneg_right
              (le_mul_of_one_le_right (le_max_of_le_left hC_dual_pos.le) hWn) hL_pos.le
    have htot : |windowFiniteEntropy_v12 (phaseNat n) m' M' Tr -
        dualValue S_w (phaseTarget (phaseDelta n))| ≤ K_E * w / L := by
      calc |windowFiniteEntropy_v12 (phaseNat n) m' M' Tr -
              dualValue S_w (phaseTarget (phaseDelta n))|
          ≤ |windowFiniteEntropy_v12 (phaseNat n) m' M' Tr - dualValue S_w Tr| +
              |dualValue S_w Tr - dualValue S_w (phaseTarget (phaseDelta n))| := abs_sub_le _ _ _
        _ ≤ max C_dual (((1 + M : ℕ) : ℝ) ^ 2) * w / L +
              universalDualLip_v12 * (2 * C * w / L) :=
            add_le_add (herr1.trans hsq_le) herr2
        _ = K_E * w / L := by rw [hKE_def]; ring
    exact ⟨htot, hB_w⟩
  have hK_core_le_sep :
      K_core * (n : ℝ) * w / L ^ 4 ≤ K_sep * (n : ℝ) * w / L ^ 4 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ hw_pos.le
    apply mul_le_mul_of_nonneg_right _ hn_pos.le
    linarith [hKsep_def]
  refine ⟨?_, ?_, ?_⟩
  -- Conjunct 1: Unconstrained `S_{≥ m₁}` vs `S_{m₂, M₂}`
  · intro m₁ m₂ M₂ hm₁ hm₂ hM₂7 hM₂M tau₁ htau₁ tau₂ htau₂ S₁ S₂ r₁ hr₁ r₂ hr₂ hz₁ hz₂
    obtain ⟨hE₁, hB₁⟩ := hInfErr_and_Bds hm₁ hr₁
    obtain ⟨hE₂, hB₂⟩ := hWinErr_and_Bds hm₂ hM₂7 hM₂M hr₂
    have hm := hApplyMaster hr₁ hr₂ htau₁ htau₂
      (genericPhaseObj_zero_imp_unrestricted_eq_v12 (hDom r₁ hr₁).1 hz₁)
      (genericPhaseObj_zero_imp_unrestricted_eq_v12 (hDom r₂ hr₂).1 hz₂)
      hE₁ hE₂ hB₁ hB₂
    simpa only [L, w, logOrder, logLogOrder] using hm.trans hK_core_le_sep
  -- Conjunct 2: Capped `S_{≥ 1}^{=θ₁}` and `S_{≥ m₁}` vs `S_{0, M₂}^{=θ₂}`
  · intro hM8 hd M₂ hM₂8 hM₂M theta₁ hth₁ theta₂ hth₂ tau₁ htau₁ tau₂ htau₂ r₂ hr₂ hz₂
    rw [hFcap_win_eq M₂ (by omega)] at hz₂
    clear hFcap_win_eq F_cap_win
    have hTd_cap : phaseTarget (phaseDelta n) ∈ KcapInterval := by
      unfold deltaStar at hd; unfold phaseTarget KcapInterval
      exact ⟨by linarith only [hd.2], by linarith only [hd.1]⟩
    have hB₂ : |cappedDualValue (S0M M₂) theta₂ (phaseTarget (phaseDelta n))| ≤ B_F0 :=
      abs_cappedDualValue_S0M_le_v12 hM₂8 hth₂ hTd_cap hBF0_def
    set Tr₂ : ℝ := fourSizeTarget n (phaseNat n) r₂
    have hTr₂_cap : Tr₂ ∈ KcapInterval := hKcap hd r₂ hr₂
    have herr_w := (abs_cappedWindowFiniteEntropy_sub_cappedDualValue_le hM₂8
      (by omega : 2 * M₂ ≤ phaseNat n) hth₂ hTr₂_cap).2
    have hlip_w := (abs_cappedDualValue_S0M_sub_le_v12 hM₂8 hth₂ hTr₂_cap hTd_cap).trans
      (mul_le_mul_of_nonneg_left (hInv.2 r₂ hr₂).2.2.2 universalDualLip_v12_nonneg)
    have hM₂_sq : (M₂ : ℝ) ^ 2 / (phaseNat n : ℝ) ≤
        max C_dual (((1 + M : ℕ) : ℝ) ^ 2) * w / L := by
      have hm_le : (M₂ : ℝ) ^ 2 ≤ ((1 + M : ℕ) : ℝ) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (by omega)) 2
      calc (M₂ : ℝ) ^ 2 / (phaseNat n : ℝ)
          ≤ max C_dual (((1 + M : ℕ) : ℝ) ^ 2) / L :=
            div_le_div₀ (le_max_of_le_right (sq_nonneg _))
              (hm_le.trans (le_max_right _ _)) hL_pos hphase.1
        _ ≤ max C_dual (((1 + M : ℕ) : ℝ) ^ 2) * w / L :=
            div_le_div_of_nonneg_right
              (le_mul_of_one_le_right (le_max_of_le_left hC_dual_pos.le) hWn) hL_pos.le
    have herr_w' : |cappedWindowFiniteEntropy_v12 (phaseNat n) M₂ theta₂ Tr₂ -
        cappedDualValue (S0M M₂) theta₂ Tr₂| ≤ (M₂ : ℝ) ^ 2 / (phaseNat n : ℝ) := by
      unfold cappedWindowFiniteEntropy_v12 windowFiniteEntropy_v12 windowFinitePartition_v12
        infiniteFiniteScore
      rw [show 1 + 1 = 2 from rfl, show 1 + (M₂ - 1) = M₂ by omega]
      exact herr_w
    have hE₂ : |cappedWindowFiniteEntropy_v12 (phaseNat n) M₂ theta₂ Tr₂ -
        cappedDualValue (S0M M₂) theta₂ (phaseTarget (phaseDelta n))| ≤ K_E * w / L := by
      calc |cappedWindowFiniteEntropy_v12 (phaseNat n) M₂ theta₂ Tr₂ -
              cappedDualValue (S0M M₂) theta₂ (phaseTarget (phaseDelta n))|
          ≤ |cappedWindowFiniteEntropy_v12 (phaseNat n) M₂ theta₂ Tr₂ -
                cappedDualValue (S0M M₂) theta₂ Tr₂| +
              |cappedDualValue (S0M M₂) theta₂ Tr₂ -
                cappedDualValue (S0M M₂) theta₂ (phaseTarget (phaseDelta n))| := abs_sub_le _ _ _
        _ ≤ max C_dual (((1 + M : ℕ) : ℝ) ^ 2) * w / L +
              universalDualLip_v12 * (2 * C * w / L) := add_le_add (herr_w'.trans hM₂_sq) hlip_w
        _ = K_E * w / L := by rw [hKE_def]; ring
    clear herr_w herr_w' hlip_w hM₂_sq
    refine ⟨?_, ?_⟩
    · intro r₁ hr₁ hz₁
      have hB₁ : |cappedDualValue Sge1 theta₁ (phaseTarget (phaseDelta n))| ≤ B_F0 :=
        abs_cappedDualValue_Sge1_le_v12 hth₁ hTd_cap hBF0_def
      set Tr₁ : ℝ := fourSizeTarget n (phaseNat n) r₁
      have hTr₁_cap : Tr₁ ∈ KcapInterval := hKcap hd r₁ hr₁
      have herr_i' : |cappedInfiniteFiniteEntropy (phaseNat n) theta₁ Tr₁ -
          cappedDualValue Sge1 theta₁ Tr₁| ≤ C_dual / (phaseNat n : ℝ) :=
        ((hCapInfDual ((le_max_right Alpha₀_i Alpha₀_c).trans halpha_A0) hth₁ hTr₁_cap).2).trans
          (div_le_div_of_nonneg_right (le_max_right C_dual_i C_dual_c) (Nat.cast_nonneg _))
      have hlip_i := (abs_cappedDualValue_Sge1_sub_le hth₁ hTr₁_cap hTd_cap).trans
        (mul_le_mul_of_nonneg_left (hInv.2 r₁ hr₁).2.2.2 universalDualLip_v12_nonneg)
      have hc_le : C_dual / (phaseNat n : ℝ) ≤ max C_dual (((1 + M : ℕ) : ℝ) ^ 2) * w / L := by
        calc C_dual / (phaseNat n : ℝ)
            ≤ max C_dual (((1 + M : ℕ) : ℝ) ^ 2) / L :=
              div_le_div₀ (le_max_of_le_left hC_dual_pos.le) (le_max_left _ _) hL_pos hphase.1
          _ ≤ max C_dual (((1 + M : ℕ) : ℝ) ^ 2) * w / L :=
              div_le_div_of_nonneg_right
                (le_mul_of_one_le_right (le_max_of_le_left hC_dual_pos.le) hWn) hL_pos.le
      have hE₁ : |cappedInfiniteFiniteEntropy (phaseNat n) theta₁ Tr₁ -
          cappedDualValue Sge1 theta₁ (phaseTarget (phaseDelta n))| ≤ K_E * w / L := by
        calc |cappedInfiniteFiniteEntropy (phaseNat n) theta₁ Tr₁ -
                cappedDualValue Sge1 theta₁ (phaseTarget (phaseDelta n))|
            ≤ |cappedInfiniteFiniteEntropy (phaseNat n) theta₁ Tr₁ -
                  cappedDualValue Sge1 theta₁ Tr₁| +
                |cappedDualValue Sge1 theta₁ Tr₁ -
                  cappedDualValue Sge1 theta₁ (phaseTarget (phaseDelta n))| := abs_sub_le _ _ _
          _ ≤ max C_dual (((1 + M : ℕ) : ℝ) ^ 2) * w / L +
                universalDualLip_v12 * (2 * C * w / L) := add_le_add (herr_i'.trans hc_le) hlip_i
          _ = K_E * w / L := by rw [hKE_def]; ring
      have hm := hApplyMaster hr₁ hr₂ htau₁ htau₂
        (genericPhaseObj_zero_imp_unrestricted_eq_v12 (hDom r₁ hr₁).1 hz₁)
        (genericPhaseObj_zero_imp_unrestricted_eq_v12 (hDom r₂ hr₂).1 hz₂)
        hE₁ hE₂ hB₁ hB₂
      simpa only [L, w, logOrder, logLogOrder] using hm.trans hK_core_le_sep
    · intro m₁ hm₁ r₁ hr₁ hz₁
      obtain ⟨hE₁, hB₁⟩ := hInfErr_and_Bds hm₁ hr₁
      have hm := hApplyMaster hr₁ hr₂ htau₁ htau₂
        (genericPhaseObj_zero_imp_unrestricted_eq_v12 (hDom r₁ hr₁).1 hz₁)
        (genericPhaseObj_zero_imp_unrestricted_eq_v12 (hDom r₂ hr₂).1 hz₂)
        hE₁ hE₂ hB₁ hB₂
      simpa only [L, w, logOrder, logLogOrder] using hm.trans hK_core_le_sep
  -- Conjunct 3: Unconditional Proposition 5.3(iii) `(5.20)` + concrete `(m_n, 7)` specialization
  · intro m M' hm hM'7 hM'M r_inf0 hr_inf0 r_infCo hr_infCo r_winCo hr_winCo r_win0 hr_win0
      hz_inf0 hz_infCo hz_winCo hz_win0
    have htau0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.log 2) := ⟨le_rfl, (Real.log_pos one_lt_two).le⟩
    have htauL : Real.log 2 ∈ Set.Icc (0 : ℝ) (Real.log 2) := ⟨(Real.log_pos one_lt_two).le, le_rfl⟩
    obtain ⟨hE_inf0, hB_inf⟩ := hInfErr_and_Bds (by omega : m ≤ 2) hr_inf0
    obtain ⟨hE_infCo, _⟩ := hInfErr_and_Bds (by omega : m ≤ 2) hr_infCo
    obtain ⟨hE_winCo, hB_win⟩ := hWinErr_and_Bds hm hM'7 hM'M hr_winCo
    obtain ⟨hE_win0, _⟩ := hWinErr_and_Bds hm hM'7 hM'M hr_win0
    have hsep_chi := hApplyMaster hr_inf0 hr_winCo htau0 htauL
      (genericPhaseObj_zero_imp_unrestricted_eq_v12 (hDom r_inf0 hr_inf0).1 hz_inf0)
      (genericPhaseObj_zero_imp_unrestricted_eq_v12 (hDom r_winCo hr_winCo).1 hz_winCo)
      hE_inf0 hE_winCo hB_inf hB_win
    have hsep_zeta := hApplyMaster hr_win0 hr_infCo htau0 htauL
      (genericPhaseObj_zero_imp_unrestricted_eq_v12 (hDom r_win0 hr_win0).1 hz_win0)
      (genericPhaseObj_zero_imp_unrestricted_eq_v12 (hDom r_infCo hr_infCo).1 hz_infCo)
      hE_win0 hE_infCo hB_win hB_inf
    have hsep_12 := hApplyMaster hr_winCo hr_infCo htauL htauL
      (genericPhaseObj_zero_imp_unrestricted_eq_v12 (hDom r_winCo hr_winCo).1 hz_winCo)
      (genericPhaseObj_zero_imp_unrestricted_eq_v12 (hDom r_infCo hr_infCo).1 hz_infCo)
      hE_winCo hE_infCo hB_win hB_inf
    have hsep_34 := hApplyMaster hr_win0 hr_inf0 htau0 htau0
      (genericPhaseObj_zero_imp_unrestricted_eq_v12 (hDom r_win0 hr_win0).1 hz_win0)
      (genericPhaseObj_zero_imp_unrestricted_eq_v12 (hDom r_inf0 hr_inf0).1 hz_inf0)
      hE_win0 hE_inf0 hB_win hB_inf
    exact prop53_iii_conj3_from_seps_v12 hn_pos hLn16 hWn hL5n
      (hDom r_winCo hr_winCo).1.le (hDom r_win0 hr_win0).1.le
      (hInv.2 r_infCo hr_infCo).1 hcMain.2
      (hSsm.trans (mul_le_mul_of_nonneg_right heps_le_q16 hL_pos.le))
      hMuBds.1 hMuBds.2.1 hK_core_pos hKsep_def hη_root_pos hη_bds hSsm3
      hsep_chi hsep_zeta hsep_12 hsep_34

/-!
## 5. Complete unconditional Proposition 4.1(i)–(iii) quasi-exponential lower tails
-/

private theorem profileDualPartition_eq_infiniteFinitePartition_v12
    {alpha m : ℕ} (hm : m < alpha) (l : ℝ) :
    profileDualPartition (alpha - m) (profileDeficitAffineB alpha - l) =
      Real.exp (profileDeficitAffineA alpha + (profileDeficitAffineB alpha - l) * (alpha : ℝ)) *
        infiniteFinitePartition alpha m l := by
  unfold profileDualPartition infiniteFinitePartition
  rw [Finset.mul_sum]
  refine Finset.sum_bij (fun (j : Fin (alpha - m)) _ ↦ alpha - (j.1 + 1)) ?_ ?_ ?_ ?_
  · intro j _
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  · intro j₁ _ j₂ _ heq
    ext
    omega
  · intro d hd
    obtain ⟨hd_lo, hd_hi⟩ := Finset.mem_Ico.mp hd
    exact ⟨⟨alpha - 1 - d, by omega⟩, Finset.mem_univ _, by dsimp; omega⟩
  · intro j _
    let j_ext : Fin (alpha + 1) := ⟨j.1, by omega⟩
    have hunn : profileDualUnnormalized (profileDeficitAffineB alpha - l) j =
        profileDualUnnormalized (profileDeficitAffineB alpha - l) j_ext := rfl
    rw [hunn, profileDualUnnormalized_eq_deficitScaled alpha l j_ext]
    congr 1
    unfold profileDeficitUnnormalized
    have hdef : profileDeficit alpha j_ext = ((alpha - (j.1 + 1) : ℕ) : ℝ) := by
      unfold profileDeficit profileClassSize
      dsimp [j_ext]
      have hle : j.1 + 1 ≤ alpha := by omega
      rw [Nat.cast_sub hle]
    have hres : profileDeficitResidualScore alpha j_ext =
        infiniteFiniteScore alpha (alpha - (j.1 + 1)) := by
      rw [profileDeficitResidualScore_eq_descFactorial alpha j_ext (by dsimp [j_ext]; omega)]
      dsimp [j_ext]
      rfl
    rw [hdef, hres]
    congr 1; ring

private theorem profileStirlingUpperMain_add_tau_le_infinitePhaseObjective_v12
    {n alpha m parts : ℕ} (hm : m ≤ 2) (halpha : 10 ≤ alpha) (hparts : 1 ≤ parts)
    (tau : ℝ) {kp : ColoringProfile (alpha - m)}
    (hkp : kp ∈ boundedColoringProfiles n (alpha - m) parts)
    (_hT : fourSizeTarget n alpha parts ∈ Set.Icc (17 / 8 : ℝ) (37 / 8)) :
    profileStirlingUpperMain n kp + tau * (parts : ℝ) ≤
      (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + (parts : ℝ) - (parts : ℝ) * Real.log (parts : ℝ) +
        (parts : ℝ) * (profileDeficitAffineA alpha +
          profileDeficitAffineB alpha * fourSizeTarget n alpha parts +
          infiniteFiniteEntropy alpha m (fourSizeTarget n alpha parts) + tau) := by
  have hb_pos : 0 < alpha - m := by omega
  have hp_pos : (0 : ℝ) < (parts : ℝ) := by exact_mod_cast hparts
  obtain ⟨hmass, hcount⟩ := (mem_boundedColoringProfiles kp).mp hkp
  have hfeas := RealColoringProfile.isFeasible_ofNat kp hcount hmass
  have hbranch : ∀ l : ℝ,
      Real.log (infiniteFinitePartition alpha m l) - l * fourSizeTarget n alpha parts ≥
        ((profileStirlingUpperMain n kp + tau * (parts : ℝ)) -
          ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + (parts : ℝ) -
            (parts : ℝ) * Real.log (parts : ℝ))) / (parts : ℝ) -
          profileDeficitAffineA alpha -
          profileDeficitAffineB alpha * fourSizeTarget n alpha parts - tau := by
    intro l
    have hdual := profileRealObjective_le_profileDualUpper hb_pos hp_pos
      (RealColoringProfile.ofNat kp) hfeas (profileDeficitAffineB alpha - l)
    rw [profileRealObjective_ofNat, ← profileStirlingUpperMain_eq_profileDiscreteObjective] at hdual
    unfold profileDualUpper at hdual
    rw [profileDualPartition_eq_infiniteFinitePartition_v12 (by omega : m < alpha) l,
      Real.log_mul (Real.exp_pos _).ne' (infiniteFinitePartition_pos (by omega) l).ne',
      Real.log_exp] at hdual
    have htar_id :
        (parts : ℝ) * (profileDeficitAffineA alpha +
            (profileDeficitAffineB alpha - l) * (alpha : ℝ) +
            Real.log (infiniteFinitePartition alpha m l)) -
          (profileDeficitAffineB alpha - l) * (n : ℝ) =
        (parts : ℝ) * (profileDeficitAffineA alpha +
          profileDeficitAffineB alpha * fourSizeTarget n alpha parts +
          (Real.log (infiniteFinitePartition alpha m l) - l * fourSizeTarget n alpha parts)) := by
      unfold fourSizeTarget
      field_simp [hp_pos.ne']
      ring
    rw [ge_iff_le, sub_le_iff_le_add, sub_le_iff_le_add, sub_le_iff_le_add, div_le_iff₀ hp_pos]
    linarith [htar_id, hdual]
  have hinf := le_ciInf hbranch
  change _ ≤ infiniteFiniteEntropy alpha m (fourSizeTarget n alpha parts) at hinf
  rw [sub_le_iff_le_add, sub_le_iff_le_add, sub_le_iff_le_add, div_le_iff₀ hp_pos] at hinf
  linarith

private theorem profileStirlingUpperMain_topCap_le_v12
    {n alpha m parts : ℕ} (hm : m ≤ 1) (halpha : 10 ≤ alpha) (hparts : 1 ≤ parts)
    (tau : ℝ) {kp : ColoringProfile (alpha - m)}
    (hkp : kp ∈ boundedColoringProfiles n (alpha - m) parts)
    (htop : kp ⟨alpha - m - 1, by omega⟩ < parts) (l : ℝ) :
    let p_top : ℝ := (kp ⟨alpha - m - 1, by omega⟩ : ℝ) / (parts : ℝ)
    let T : ℝ := fourSizeTarget n alpha parts
    profileStirlingUpperMain n kp + tau * (parts : ℝ) ≤
      (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + (parts : ℝ) - (parts : ℝ) * Real.log (parts : ℝ) +
        (parts : ℝ) * (profileDeficitAffineA alpha + profileDeficitAffineB alpha * T +
          binEntropy p_top - Real.log 2 / 2 * (m : ℝ) * p_top +
          (1 - p_top) *
            (Real.log (infiniteFinitePartition alpha (m + 1) l) -
              l * ((T - (m : ℝ) * p_top) / (1 - p_top))) + tau) := by
  intro p_top T
  let i_top : Fin (alpha - m) := ⟨alpha - m - 1, by omega⟩
  set k_top : ℝ := (kp i_top : ℝ)
  have hp_pos : (0 : ℝ) < (parts : ℝ) := by exact_mod_cast hparts
  have hk_top_nn : 0 ≤ k_top := Nat.cast_nonneg _
  have hk_top_lt : k_top < (parts : ℝ) := by dsimp [k_top, i_top]; exact_mod_cast htop
  have hp_top_def : p_top = k_top / (parts : ℝ) := rfl
  have hp_top_nn : 0 ≤ p_top := by rw [hp_top_def]; exact div_nonneg hk_top_nn hp_pos.le
  have hp_top_lt1 : p_top < 1 := by rw [hp_top_def]; exact (div_lt_one hp_pos).mpr hk_top_lt
  have h1mp_pos : 0 < 1 - p_top := sub_pos.mpr hp_top_lt1
  have hk_rem_pos : 0 < (parts : ℝ) - k_top := sub_pos.mpr hk_top_lt
  have hk_top_eq : k_top = (parts : ℝ) * p_top := by
    rw [hp_top_def]; exact (mul_div_cancel₀ _ hp_pos.ne').symm
  have hk_rem_eq : (parts : ℝ) - k_top = (parts : ℝ) * (1 - p_top) := by rw [hk_top_eq]; ring
  obtain ⟨hmass, hcount⟩ := (mem_boundedColoringProfiles kp).mp hkp
  -- Express `profileStirlingUpperMain n kp` in deficit coordinates
  have hdisc : profileStirlingUpperMain n kp =
      (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + (parts : ℝ) -
        ∑ j : Fin (alpha - m), (kp j : ℝ) * (Real.log (kp j : ℝ) + coloringClassLogCost (j.1 + 1)) := by
    rw [profileStirlingUpperMain_eq_profileDiscreteObjective,
      profileDiscreteObjective_eq_profileManuscriptObjective]
    unfold profileManuscriptObjective
    rw [hcount]
  let defOf : Fin (alpha - m) → ℕ := fun j ↦ alpha - (j.1 + 1)
  have hcost_eq : ∀ j : Fin (alpha - m),
      -coloringClassLogCost (j.1 + 1) =
        profileDeficitAffineA alpha + profileDeficitAffineB alpha * (defOf j : ℝ) +
          infiniteFiniteScore alpha (defOf j) := by
    intro j
    let j_ext : Fin (alpha + 1) := ⟨j.1, by omega⟩
    have h1 := profileDualScore_eq_deficitAffine_add_residual alpha j_ext
    have hdef : profileDeficit alpha j_ext = (defOf j : ℝ) := by
      unfold profileDeficit profileClassSize
      dsimp [j_ext, defOf]
      have hle : j.1 + 1 ≤ alpha := by omega
      rw [Nat.cast_sub hle]
    have hres : profileDeficitResidualScore alpha j_ext = infiniteFiniteScore alpha (defOf j) := by
      rw [profileDeficitResidualScore_eq_descFactorial alpha j_ext (by dsimp [j_ext]; omega)]
      rfl
    simpa only [profileDualScore, j_ext, hdef, hres] using h1
  have hsum_kp : ∑ j : Fin (alpha - m), (kp j : ℝ) = (parts : ℝ) := by
    rw [← Nat.cast_sum, ← ColoringProfile.partCount_eq_sum, hcount]
  have hsum_def : ∑ j : Fin (alpha - m), (kp j : ℝ) * (defOf j : ℝ) = (parts : ℝ) * T := by
    have hpt : ∀ j : Fin (alpha - m), (kp j : ℝ) * (defOf j : ℝ) =
        (alpha : ℝ) * (kp j : ℝ) - (((j.1 + 1) * kp j : ℕ) : ℝ) := by
      intro j
      dsimp [defOf]
      have hle : j.1 + 1 ≤ alpha := by omega
      rw [Nat.cast_sub hle, Nat.cast_mul]
      ring
    rw [Finset.sum_congr rfl fun j _ ↦ hpt j, Finset.sum_sub_distrib, ← Finset.mul_sum,
      hsum_kp, ← Nat.cast_sum, ← ColoringProfile.vertexMass_eq_sum, hmass]
    dsimp [T]; unfold fourSizeTarget
    field_simp [hp_pos.ne']
  have hstirling_decomp :
      profileStirlingUpperMain n kp =
        (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + (parts : ℝ) +
          (parts : ℝ) * (profileDeficitAffineA alpha + profileDeficitAffineB alpha * T) +
          ∑ j : Fin (alpha - m), (-(kp j : ℝ) * Real.log (kp j : ℝ) +
            (kp j : ℝ) * infiniteFiniteScore alpha (defOf j)) := by
    rw [hdisc]
    have hrew : ∀ j : Fin (alpha - m),
        -((kp j : ℝ) * (Real.log (kp j : ℝ) + coloringClassLogCost (j.1 + 1))) =
          (kp j : ℝ) * profileDeficitAffineA alpha +
            profileDeficitAffineB alpha * ((kp j : ℝ) * (defOf j : ℝ)) +
            (-(kp j : ℝ) * Real.log (kp j : ℝ) + (kp j : ℝ) * infiniteFiniteScore alpha (defOf j)) := by
      intro j
      have hc := hcost_eq j
      calc -((kp j : ℝ) * (Real.log (kp j : ℝ) + coloringClassLogCost (j.1 + 1)))
          = -(kp j : ℝ) * Real.log (kp j : ℝ) + (kp j : ℝ) * (-coloringClassLogCost (j.1 + 1)) := by ring
        _ = (kp j : ℝ) * profileDeficitAffineA alpha +
              profileDeficitAffineB alpha * ((kp j : ℝ) * (defOf j : ℝ)) +
              (-(kp j : ℝ) * Real.log (kp j : ℝ) + (kp j : ℝ) * infiniteFiniteScore alpha (defOf j)) := by
            rw [hc]; ring
    have hsum_neg :
        -(∑ j : Fin (alpha - m), (kp j : ℝ) * (Real.log (kp j : ℝ) + coloringClassLogCost (j.1 + 1))) =
          ∑ j : Fin (alpha - m), -((kp j : ℝ) * (Real.log (kp j : ℝ) + coloringClassLogCost (j.1 + 1))) := by
      simp [Finset.sum_neg_distrib]
    have h1 : (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + (parts : ℝ) -
          ∑ j : Fin (alpha - m), (kp j : ℝ) * (Real.log (kp j : ℝ) + coloringClassLogCost (j.1 + 1)) =
        (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + (parts : ℝ) +
          ∑ j : Fin (alpha - m), -((kp j : ℝ) * (Real.log (kp j : ℝ) + coloringClassLogCost (j.1 + 1))) := by
      rw [← hsum_neg]; ring
    rw [h1, Finset.sum_congr rfl fun j _ ↦ hrew j, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, hsum_kp, hsum_def]
    ring
  -- Split `Finset.univ` into `i_top` and `Rest := Finset.univ.erase i_top`
  let Rest : Finset (Fin (alpha - m)) := Finset.univ.erase i_top
  have hdef_top : defOf i_top = m := by dsimp [defOf, i_top]; omega
  have hscore_top : infiniteFiniteScore alpha m = -Real.log 2 / 2 * (m : ℝ) := by
    unfold infiniteFiniteScore
    rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
    · simp
    · simp; ring
  have htop_ent :
      -k_top * Real.log k_top + k_top * infiniteFiniteScore alpha (defOf i_top) =
        -k_top * Real.log (parts : ℝ) +
          (parts : ℝ) * (-p_top * Real.log p_top - Real.log 2 / 2 * (m : ℝ) * p_top) := by
    rw [hdef_top, hscore_top]
    rcases eq_or_lt_of_le hk_top_nn with h0 | hk_pos
    · have hp0 : p_top = 0 := by rw [hp_top_def, ← h0, zero_div]
      rw [← h0, hp0]; simp
    · have hp_pos' : 0 < p_top := by rw [hp_top_def]; exact div_pos hk_pos hp_pos
      rw [hk_top_eq, Real.log_mul hp_pos.ne' hp_pos'.ne']
      ring
  -- Tail sum on `Rest` via relative-entropy inequality against `ref`
  set Z_tail : ℝ := infiniteFinitePartition alpha (m + 1) l
  have hZ_tail_pos : 0 < Z_tail := infiniteFinitePartition_pos (by omega) l
  let ref : Fin (alpha - m) → ℝ := fun j ↦
    ((parts : ℝ) - k_top) * Real.exp (l * (defOf j : ℝ) + infiniteFiniteScore alpha (defOf j)) / Z_tail
  have href_pos : ∀ j : Fin (alpha - m), 0 < ref j :=
    fun j ↦ div_pos (mul_pos hk_rem_pos (Real.exp_pos _)) hZ_tail_pos
  have hRest_sum_ref : ∑ j ∈ Rest, ref j = (parts : ℝ) - k_top := by
    dsimp [ref]
    simp_rw [mul_div_assoc]
    rw [← Finset.mul_sum, ← Finset.sum_div]
    have hbij : (∑ j ∈ Rest, Real.exp (l * (defOf j : ℝ) + infiniteFiniteScore alpha (defOf j))) =
        Z_tail := by
      dsimp [Z_tail]; unfold infiniteFinitePartition
      refine Finset.sum_bij (fun j _ ↦ defOf j) ?_ ?_ ?_ (fun _ _ ↦ rfl)
      · intro j hj
        have hj_ne : j ≠ i_top := (Finset.mem_erase.mp hj).1
        have hj_lt : j.1 < alpha - m - 1 := by
          have : j.1 ≠ alpha - m - 1 := fun h ↦ hj_ne (Fin.ext h)
          omega
        exact Finset.mem_Ico.mpr ⟨by dsimp [defOf]; omega, by dsimp [defOf]; omega⟩
      · intro j₁ _ j₂ _ heq
        ext; dsimp [defOf] at heq; omega
      · intro d hd
        obtain ⟨hd_lo, hd_hi⟩ := Finset.mem_Ico.mp hd
        refine ⟨⟨alpha - 1 - d, by omega⟩, ?_, by dsimp [defOf]; omega⟩
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
        intro heq
        have hv : alpha - 1 - d = alpha - m - 1 := congrArg Fin.val heq
        omega
    rw [hbij, div_self hZ_tail_pos.ne', mul_one]
  have hRest_sum_kp : ∑ j ∈ Rest, (kp j : ℝ) = (parts : ℝ) - k_top := by
    have h := Finset.add_sum_erase Finset.univ (fun j : Fin (alpha - m) ↦ (kp j : ℝ)) (Finset.mem_univ i_top)
    dsimp [Rest, k_top] at h ⊢
    linarith [hsum_kp]
  have hRest_sum_def : ∑ j ∈ Rest, (kp j : ℝ) * (defOf j : ℝ) =
      (parts : ℝ) * (T - (m : ℝ) * p_top) := by
    have h := Finset.add_sum_erase Finset.univ (fun j : Fin (alpha - m) ↦ (kp j : ℝ) * (defOf j : ℝ))
      (Finset.mem_univ i_top)
    rw [hdef_top] at h
    change k_top * (m : ℝ) + ∑ j ∈ Rest, (kp j : ℝ) * (defOf j : ℝ) =
      ∑ j : Fin (alpha - m), (kp j : ℝ) * (defOf j : ℝ) at h
    rw [hk_top_eq] at h
    linarith [hsum_def]
  have hkl_rest :
      ∑ j ∈ Rest, (-(kp j : ℝ) * Real.log (kp j : ℝ) +
          (kp j : ℝ) * infiniteFiniteScore alpha (defOf j)) ≤
        -((parts : ℝ) - k_top) * Real.log (parts : ℝ) +
          (parts : ℝ) * (-(1 - p_top) * Real.log (1 - p_top) +
            (1 - p_top) *
              (Real.log Z_tail - l * ((T - (m : ℝ) * p_top) / (1 - p_top)))) := by
    have hrel : ∑ j ∈ Rest, (-(kp j : ℝ) * Real.log (kp j : ℝ) + (kp j : ℝ) * Real.log (ref j)) ≤
        ∑ j ∈ Rest, (ref j - (kp j : ℝ)) :=
      Finset.sum_le_sum fun j _ ↦
        profile_neg_mul_log_add_mul_log_le_sub (Nat.cast_nonneg _) (href_pos j)
    rw [Finset.sum_sub_distrib, hRest_sum_ref, hRest_sum_kp, sub_self] at hrel
    have hlog_rem : Real.log ((parts : ℝ) - k_top) = Real.log (parts : ℝ) + Real.log (1 - p_top) := by
      rw [hk_rem_eq, Real.log_mul hp_pos.ne' h1mp_pos.ne']
    have hpt_log : ∀ j ∈ Rest,
        -(kp j : ℝ) * Real.log (kp j : ℝ) + (kp j : ℝ) * Real.log (ref j) =
          (-(kp j : ℝ) * Real.log (kp j : ℝ) + (kp j : ℝ) * infiniteFiniteScore alpha (defOf j)) +
            (Real.log (parts : ℝ) + Real.log (1 - p_top) - Real.log Z_tail) * (kp j : ℝ) +
            l * ((kp j : ℝ) * (defOf j : ℝ)) := by
      intro j _
      dsimp [ref]
      rw [Real.log_div (mul_pos hk_rem_pos (Real.exp_pos _)).ne' hZ_tail_pos.ne',
        Real.log_mul hk_rem_pos.ne' (Real.exp_pos _).ne', Real.log_exp, hlog_rem]
      ring
    rw [Finset.sum_congr rfl hpt_log, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hRest_sum_kp, hRest_sum_def] at hrel
    have halg :
        -((Real.log (parts : ℝ) + Real.log (1 - p_top) - Real.log Z_tail) * ((parts : ℝ) - k_top)) -
          l * ((parts : ℝ) * (T - (m : ℝ) * p_top)) =
        -((parts : ℝ) - k_top) * Real.log (parts : ℝ) +
          (parts : ℝ) * (-(1 - p_top) * Real.log (1 - p_top) +
            (1 - p_top) * (Real.log Z_tail - l * ((T - (m : ℝ) * p_top) / (1 - p_top)))) := by
      rw [hk_rem_eq]
      field_simp [h1mp_pos.ne']
      ring
    linarith
  have hsplit_all := (Finset.add_sum_erase Finset.univ
    (fun j : Fin (alpha - m) ↦ -(kp j : ℝ) * Real.log (kp j : ℝ) +
      (kp j : ℝ) * infiniteFiniteScore alpha (defOf j))
    (Finset.mem_univ i_top)).symm
  rw [hstirling_decomp, hsplit_all]
  change (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + (parts : ℝ) +
      (parts : ℝ) * (profileDeficitAffineA alpha + profileDeficitAffineB alpha * T) +
      ((-k_top * Real.log k_top + k_top * infiniteFiniteScore alpha (defOf i_top)) +
        ∑ j ∈ Rest, (-(kp j : ℝ) * Real.log (kp j : ℝ) +
          (kp j : ℝ) * infiniteFiniteScore alpha (defOf j))) +
      tau * (parts : ℝ) ≤ _
  rw [htop_ent]
  have hbin_def : -p_top * Real.log p_top + -(1 - p_top) * Real.log (1 - p_top) = binEntropy p_top := by
    unfold binEntropy; ring
  have halg_end :
      -k_top * Real.log (parts : ℝ) +
        (parts : ℝ) * (-p_top * Real.log p_top - Real.log 2 / 2 * (m : ℝ) * p_top) +
        (-((parts : ℝ) - k_top) * Real.log (parts : ℝ) +
          (parts : ℝ) * (-(1 - p_top) * Real.log (1 - p_top) +
            (1 - p_top) * (Real.log Z_tail - l * ((T - (m : ℝ) * p_top) / (1 - p_top))))) =
      -(parts : ℝ) * Real.log (parts : ℝ) +
        (parts : ℝ) * (binEntropy p_top - Real.log 2 / 2 * (m : ℝ) * p_top +
          (1 - p_top) * (Real.log Z_tail - l * ((T - (m : ℝ) * p_top) / (1 - p_top)))) := by
    rw [← hbin_def]; ring
  linarith [hkl_rest, halg_end]

private theorem count_partitionShape_eq_card_filter_v12 {n : ℕ}
    (Q : VertexPartition n) (s : ℕ) :
    (partitionShape Q).count s = (Q.parts.filter fun B ↦ B.card = s).card := by
  change (Q.parts.val.map Finset.card).count s = (Q.parts.filter fun B ↦ B.card = s).card
  generalize Q.parts = S
  induction S using Finset.induction_on with
  | empty => simp
  | @insert B S' hnot ih =>
    rw [Finset.insert_val_of_notMem hnot, Multiset.map_cons, Multiset.count_cons,
      Finset.filter_insert]
    by_cases hBs : B.card = s
    · simp [hBs, Finset.card_insert_of_notMem (fun hm ↦ hnot (Finset.mem_filter.mp hm).1),
        ih, Nat.add_comm]
    · have hne : s ≠ B.card := fun h ↦ hBs h.symm
      simp [hBs, hne, ih]

private theorem randomGraph_filtered_coloring_and_cocoloring_le_v12
    {n alpha m k_chi k_zeta d m_cap : ℕ}
    (hn : 2 ≤ n) (hm : m ≤ 1) (halpha : 4 ≤ alpha)
    {t : ℝ} (ht : 0 ≤ t) (hd : mu n (alpha + 1 - m) + t ≤ (d : ℝ))
    (hk_chi_n : k_chi + 2 * d ≤ n) (hk_zeta_n : k_zeta + 4 * d ≤ n)
    {L_chi L_zeta : ℝ}
    (hL_chi : ∀ kp ∈ boundedColoringProfiles n (alpha - m) (k_chi + 2 * d),
      kp ⟨alpha - m - 1, by omega⟩ < m_cap →
      profileStirlingUpperMain n kp + factorialLogErrorBound n ≤ L_chi)
    (hL_zeta : ∀ kp ∈ boundedColoringProfiles n (alpha - m) (k_zeta + 4 * d),
      kp ⟨alpha - m - 1, by omega⟩ < m_cap →
      profileStirlingUpperMain n kp + factorialLogErrorBound n +
        Real.log 2 * ((k_zeta + 4 * d : ℕ) : ℝ) ≤ L_zeta) :
    (randomGraphMeasure n).real {G : LabeledGraph n | chromaticNumberNat G ≤ k_chi} ≤
        Real.exp (-2 * t ^ 2 / ((n - 1 : ℕ) : ℝ)) +
          (randomGraphMeasure n).real
            {G : LabeledGraph n | m_cap ≤ maxDisjointHomogeneousEq G (alpha - m)} +
          (((n + 1) ^ (alpha - m) : ℕ) : ℝ) * Real.exp L_chi ∧
      (randomGraphMeasure n).real {G : LabeledGraph n | cochromaticNumber G ≤ k_zeta} ≤
        2 * Real.exp (-2 * t ^ 2 / ((n - 1 : ℕ) : ℝ)) +
          (randomGraphMeasure n).real
            {G : LabeledGraph n | m_cap ≤ maxDisjointHomogeneousEq G (alpha - m)} +
          (((n + 1) ^ (alpha - m) : ℕ) : ℝ) * Real.exp L_zeta := by
  classical
  set u : ℕ := alpha + 1 - m
  have hu2 : 2 ≤ u := by dsimp [u]; omega
  have hu1 : u - 1 = alpha - m := by dsimp [u]; omega
  let i_top : Fin (alpha - m) := ⟨alpha - m - 1, by omega⟩
  have hi_top_size : i_top.1 + 1 = alpha - m := by dsimp [i_top]; omega
  let Exc₁ : Set (LabeledGraph n) := {G | mu n u + t < (maxDisjointIndepGe G u : ℝ)}
  let Exc₂ : Set (LabeledGraph n) := {G | mu n u + t < (maxDisjointIndepGe Gᶜ u : ℝ)}
  let ExcH : Set (LabeledGraph n) := {G | m_cap ≤ maxDisjointHomogeneousEq G (alpha - m)}
  -- 1. Chromatic bound
  let FiltChi := (boundedColoringProfiles n (alpha - m) (k_chi + 2 * d)).filter
    fun kp ↦ kp i_top < m_cap
  let GoodChi : Set (LabeledGraph n) :=
    ⋃ kp ∈ FiltChi, ⋃ P : ProfilePartition n kp, partitionColoringEvent P.1
  have hcov_chi :
      {G : LabeledGraph n | chromaticNumberNat G ≤ k_chi} ⊆ (Exc₁ ∪ ExcH) ∪ GoodChi := by
    intro G hchi
    by_cases hDu : maxDisjointIndepGe G u ≤ d
    · by_cases hH : maxDisjointHomogeneousEq G (alpha - m) < m_cap
      · right
        obtain ⟨Q, hQcard, hQcol, hQsmall⟩ :=
          exists_unconditional_bounded_coloring_partition_of_maxDisjointIndepGe_le
            hu2 hk_chi_n G hDu hchi
        rw [hu1] at hQsmall
        let kp : ColoringProfile (alpha - m) := vertexPartitionProfile (alpha - m) Q
        let Qp : ProfilePartition n kp := vertexPartitionAsProfilePartition Q hQsmall
        have hkp_mem : kp ∈ boundedColoringProfiles n (alpha - m) (k_chi + 2 * d) :=
          mem_boundedColoringProfiles_of_constraints Qp.vertexMass_eq
            (Qp.card_parts_eq.symm.trans hQcard)
        have hkp_top : kp i_top < m_cap := by
          change (partitionShape Q).count (i_top.1 + 1) < m_cap
          rw [hi_top_size, count_partitionShape_eq_card_filter_v12]
          exact lt_of_le_of_lt (coloring_card_filter_eq_le_maxDisjointHomogeneousEq hQcol) hH
        exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨hkp_mem, hkp_top⟩)
          (Set.mem_iUnion.mpr ⟨Qp, hQcol⟩)
      · left; right; exact not_lt.mp hH
    · left; left
      have hgt : (d : ℝ) < (maxDisjointIndepGe G u : ℝ) := by exact_mod_cast not_le.mp hDu
      exact lt_of_le_of_lt hd hgt
  have hGoodChi_enn :
      randomGraphMeasure n GoodChi ≤
        (((n + 1) ^ (alpha - m) : ℕ) : ENNReal) * ENNReal.ofReal (Real.exp L_chi) := by
    calc randomGraphMeasure n GoodChi
        ≤ ∑ kp ∈ FiltChi,
            randomGraphMeasure n (⋃ P : ProfilePartition n kp, partitionColoringEvent P.1) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ kp ∈ FiltChi, ∑ P : ProfilePartition n kp,
            randomGraphMeasure n (partitionColoringEvent P.1) :=
          Finset.sum_le_sum fun kp _ ↦ measure_iUnion_fintype_le _ _
      _ = ∑ kp ∈ FiltChi, profileColoringExpectation n kp := by
          refine Finset.sum_congr rfl fun kp _ ↦ ?_
          rw [profileColoringExpectation_eq_card_mul]
          simp_rw [randomGraphMeasure_partitionColoringEvent]
          simp [Finset.sum_const, nsmul_eq_mul, Nat.card_eq_fintype_card]
      _ ≤ ∑ _kp ∈ FiltChi, ENNReal.ofReal (Real.exp L_chi) := by
          refine Finset.sum_le_sum fun kp hkp_f ↦ ?_
          obtain ⟨hkp_b, hkp_top⟩ := Finset.mem_filter.mp hkp_f
          exact profileColoringExpectation_le_of_stirlingUpperMain_add_error_le n kp L_chi
            ((mem_boundedColoringProfiles kp).mp hkp_b).1 (hL_chi kp hkp_b hkp_top)
      _ = (FiltChi.card : ENNReal) * ENNReal.ofReal (Real.exp L_chi) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (((n + 1) ^ (alpha - m) : ℕ) : ENNReal) * ENNReal.ofReal (Real.exp L_chi) := by
          gcongr
          have h1 : FiltChi.card ≤ (boundedColoringProfiles n (alpha - m) (k_chi + 2 * d)).card :=
            Finset.card_filter_le _ _
          exact_mod_cast h1.trans (card_boundedColoringProfiles_le _ _ _)
  have hGoodChi_real :
      (randomGraphMeasure n).real GoodChi ≤ (((n + 1) ^ (alpha - m) : ℕ) : ℝ) * Real.exp L_chi := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top) hGoodChi_enn
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (Real.exp_pos _).le] at h
    exact h
  -- 2. Cochromatic bound
  let FiltZeta := (boundedColoringProfiles n (alpha - m) (k_zeta + 4 * d)).filter
    fun kp ↦ kp i_top < m_cap
  let GoodZeta : Set (LabeledGraph n) :=
    ⋃ kp ∈ FiltZeta, ⋃ P : ProfilePartition n kp, partitionCocoloringEvent P.1
  have hcov_zeta :
      {G : LabeledGraph n | cochromaticNumber G ≤ k_zeta} ⊆ ((Exc₁ ∪ Exc₂) ∪ ExcH) ∪ GoodZeta := by
    intro G hzeta
    by_cases hDu₁ : maxDisjointIndepGe G u ≤ d
    · by_cases hDu₂ : maxDisjointIndepGe Gᶜ u ≤ d
      · by_cases hH : maxDisjointHomogeneousEq G (alpha - m) < m_cap
        · right
          obtain ⟨Q, hQcard, hQco, hQsmall⟩ :=
            exists_unconditional_bounded_cocoloring_partition_of_maxDisjointIndepGe_le
              hu2 hk_zeta_n G hDu₁ hDu₂ hzeta
          rw [hu1] at hQsmall
          let kp : ColoringProfile (alpha - m) := vertexPartitionProfile (alpha - m) Q
          let Qp : ProfilePartition n kp := vertexPartitionAsProfilePartition Q hQsmall
          have hkp_mem : kp ∈ boundedColoringProfiles n (alpha - m) (k_zeta + 4 * d) :=
            mem_boundedColoringProfiles_of_constraints Qp.vertexMass_eq
              (Qp.card_parts_eq.symm.trans hQcard)
          have hkp_top : kp i_top < m_cap := by
            change (partitionShape Q).count (i_top.1 + 1) < m_cap
            rw [hi_top_size, count_partitionShape_eq_card_filter_v12]
            exact lt_of_le_of_lt (cocoloring_card_filter_eq_le_maxDisjointHomogeneousEq hQco) hH
          exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨hkp_mem, hkp_top⟩)
            (Set.mem_iUnion.mpr ⟨Qp, hQco⟩)
        · left; right; exact not_lt.mp hH
      · left; left; right
        have hgt : (d : ℝ) < (maxDisjointIndepGe Gᶜ u : ℝ) := by exact_mod_cast not_le.mp hDu₂
        exact lt_of_le_of_lt hd hgt
    · left; left; left
      have hgt : (d : ℝ) < (maxDisjointIndepGe G u : ℝ) := by exact_mod_cast not_le.mp hDu₁
      exact lt_of_le_of_lt hd hgt
  have hGoodZeta_enn :
      randomGraphMeasure n GoodZeta ≤
        (((n + 1) ^ (alpha - m) : ℕ) : ENNReal) * ENNReal.ofReal (Real.exp L_zeta) := by
    calc randomGraphMeasure n GoodZeta
        ≤ ∑ kp ∈ FiltZeta,
            randomGraphMeasure n (⋃ P : ProfilePartition n kp, partitionCocoloringEvent P.1) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ kp ∈ FiltZeta, ∑ P : ProfilePartition n kp,
            randomGraphMeasure n (partitionCocoloringEvent P.1) :=
          Finset.sum_le_sum fun kp _ ↦ measure_iUnion_fintype_le _ _
      _ ≤ ∑ kp ∈ FiltZeta, ∑ P : ProfilePartition n kp,
            (2 : ENNReal) ^ (k_zeta + 4 * d) *
              randomGraphMeasure n (partitionColoringEvent P.1) := by
          refine Finset.sum_le_sum fun kp hkp_f ↦ Finset.sum_le_sum fun P _ ↦ ?_
          have hkparts : P.1.parts.card = k_zeta + 4 * d :=
            P.card_parts_eq.trans ((mem_boundedColoringProfiles kp).mp (Finset.mem_filter.mp hkp_f).1).2
          simpa [hkparts] using randomGraphMeasure_partitionCocoloringEvent_le_two_pow_mul P.1
      _ = ∑ kp ∈ FiltZeta,
            (2 : ENNReal) ^ (k_zeta + 4 * d) * profileColoringExpectation n kp := by
          refine Finset.sum_congr rfl fun kp _ ↦ ?_
          rw [← Finset.mul_sum, profileColoringExpectation_eq_card_mul]
          simp_rw [randomGraphMeasure_partitionColoringEvent]
          simp [Finset.sum_const, nsmul_eq_mul, Nat.card_eq_fintype_card]
      _ ≤ ∑ _kp ∈ FiltZeta, ENNReal.ofReal (Real.exp L_zeta) := by
          refine Finset.sum_le_sum fun kp hkp_f ↦ ?_
          obtain ⟨hkp_b, hkp_top⟩ := Finset.mem_filter.mp hkp_f
          have hexp_kp := profileColoringExpectation_le_of_stirlingUpperMain_add_error_le n kp
            (L_zeta - Real.log 2 * ((k_zeta + 4 * d : ℕ) : ℝ))
            ((mem_boundedColoringProfiles kp).mp hkp_b).1
            (by linarith [hL_zeta kp hkp_b hkp_top])
          have h2pow_eq : (2 : ENNReal) ^ (k_zeta + 4 * d) =
              ENNReal.ofReal (Real.exp (Real.log 2 * ((k_zeta + 4 * d : ℕ) : ℝ))) := by
            rw [mul_comm (Real.log 2), Real.exp_nat_mul, Real.exp_log two_pos,
              ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]
          calc (2 : ENNReal) ^ (k_zeta + 4 * d) * profileColoringExpectation n kp
              ≤ ENNReal.ofReal (Real.exp (Real.log 2 * ((k_zeta + 4 * d : ℕ) : ℝ))) *
                  ENNReal.ofReal (Real.exp (L_zeta - Real.log 2 * ((k_zeta + 4 * d : ℕ) : ℝ))) := by
                rw [← h2pow_eq]
                exact mul_le_mul_of_nonneg_left hexp_kp zero_le
            _ = ENNReal.ofReal (Real.exp L_zeta) := by
                rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
                congr 2; ring
      _ = (FiltZeta.card : ENNReal) * ENNReal.ofReal (Real.exp L_zeta) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (((n + 1) ^ (alpha - m) : ℕ) : ENNReal) * ENNReal.ofReal (Real.exp L_zeta) := by
          gcongr
          have h1 : FiltZeta.card ≤ (boundedColoringProfiles n (alpha - m) (k_zeta + 4 * d)).card :=
            Finset.card_filter_le _ _
          exact_mod_cast h1.trans (card_boundedColoringProfiles_le _ _ _)
  have hGoodZeta_real :
      (randomGraphMeasure n).real GoodZeta ≤ (((n + 1) ^ (alpha - m) : ℕ) : ℝ) * Real.exp L_zeta := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top) hGoodZeta_enn
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (Real.exp_pos _).le] at h
    exact h
  have hExc₁_le : (randomGraphMeasure n).real Exc₁ ≤ Real.exp (-2 * t ^ 2 / ((n - 1 : ℕ) : ℝ)) :=
    randomGraph_maxDisjointIndepGe_gt_mu_add_le_exp hn (by omega) ht
  have hExc₂_le : (randomGraphMeasure n).real Exc₂ ≤ Real.exp (-2 * t ^ 2 / ((n - 1 : ℕ) : ℝ)) := by
    have henn := randomGraphMeasure_image_le_of_involutive (S := Exc₂) (T := Exc₁)
      (fun G : LabeledGraph n ↦ Gᶜ) compl_involutive (fun _ hG ↦ hG)
    exact (ENNReal.toReal_mono (measure_ne_top _ _) henn).trans hExc₁_le
  refine ⟨?_, ?_⟩
  · calc (randomGraphMeasure n).real {G : LabeledGraph n | chromaticNumberNat G ≤ k_chi}
        ≤ (randomGraphMeasure n).real ((Exc₁ ∪ ExcH) ∪ GoodChi) := measureReal_mono hcov_chi
      _ ≤ (randomGraphMeasure n).real (Exc₁ ∪ ExcH) + (randomGraphMeasure n).real GoodChi :=
          measureReal_union_le _ _
      _ ≤ ((randomGraphMeasure n).real Exc₁ + (randomGraphMeasure n).real ExcH) +
            (randomGraphMeasure n).real GoodChi :=
          add_le_add (measureReal_union_le _ _) le_rfl
      _ ≤ _ := by linarith [hExc₁_le, hGoodChi_real]
  · calc (randomGraphMeasure n).real {G : LabeledGraph n | cochromaticNumber G ≤ k_zeta}
        ≤ (randomGraphMeasure n).real (((Exc₁ ∪ Exc₂) ∪ ExcH) ∪ GoodZeta) := measureReal_mono hcov_zeta
      _ ≤ (randomGraphMeasure n).real ((Exc₁ ∪ Exc₂) ∪ ExcH) + (randomGraphMeasure n).real GoodZeta :=
          measureReal_union_le _ _
      _ ≤ ((randomGraphMeasure n).real (Exc₁ ∪ Exc₂) + (randomGraphMeasure n).real ExcH) +
            (randomGraphMeasure n).real GoodZeta :=
          add_le_add (measureReal_union_le _ _) le_rfl
      _ ≤ (((randomGraphMeasure n).real Exc₁ + (randomGraphMeasure n).real Exc₂) +
            (randomGraphMeasure n).real ExcH) + (randomGraphMeasure n).real GoodZeta :=
          add_le_add (add_le_add (measureReal_union_le _ _) le_rfl) le_rfl
      _ ≤ _ := by linarith [hExc₁_le, hExc₂_le, hGoodZeta_real]

private theorem exp_mcdiarmid_universalShift_le_quasiExpTail {n : ℕ} (hn : 2 ≤ n) :
    Real.exp (-2 * (universalShift n) ^ 2 / ((n - 1 : ℕ) : ℝ)) ≤ quasiExpTail n := by
  unfold universalShift quasiExpTail
  apply Real.exp_le_exp.mpr
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hn1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
  have hn1_le : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
  have hL_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hden :
      2 * (n : ℝ) / (Real.log (n : ℝ)) ^ 10 ≤
        2 * ((n : ℝ) / (Real.log (n : ℝ)) ^ 5) ^ 2 / ((n - 1 : ℕ) : ℝ) := by
    have h1 : 2 * ((n : ℝ) / (Real.log (n : ℝ)) ^ 5) ^ 2 / (n : ℝ) =
        2 * (n : ℝ) / (Real.log (n : ℝ)) ^ 10 := by
      field_simp [hn_pos.ne', hL_pos.ne']
    rw [← h1]
    exact div_le_div_of_nonneg_left (by positivity) hn1_pos hn1_le
  linarith [hden,
    show -2 * ((n : ℝ) / (Real.log (n : ℝ)) ^ 5) ^ 2 / ((n - 1 : ℕ) : ℝ) =
      -(2 * ((n : ℝ) / (Real.log (n : ℝ)) ^ 5) ^ 2 / ((n - 1 : ℕ) : ℝ)) by ring,
    show -2 * (n : ℝ) / (Real.log (n : ℝ)) ^ 10 =
      -(2 * (n : ℝ) / (Real.log (n : ℝ)) ^ 10) by ring]

private theorem eventually_two_85_logOrder_le_phaseNat :
    ∀ᶠ n : ℕ in atTop, (285 / 100 : ℝ) * logOrder n ≤ (phaseNat n : ℝ) := by
  have hratio : Tendsto (fun n : ℕ ↦ (phaseNat n : ℝ) / logOrder n) atTop (nhds (2 / q)) := by
    have hScaleTop : Tendsto (fun n : ℕ ↦ (2 / q) * logOrder n) atTop atTop :=
      tendsto_logOrder_atTop.const_mul_atTop (div_pos two_pos q_pos)
    have hDenom : ∀ᶠ n : ℕ in atTop, (2 / q) * logOrder n ≠ 0 :=
      hScaleTop.eventually_ne_atTop 0
    have hEq := (isEquivalent_iff_tendsto_one hDenom).mp phaseNat_isEquivalent_scaled_logOrder
    have hmul := hEq.const_mul (2 / q)
    rw [mul_one] at hmul
    refine hmul.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    have hL : logOrder n ≠ 0 := (Real.log_pos (by exact_mod_cast hn)).ne'
    simp only [Pi.div_apply]; field_simp [hL, q_ne_zero]
  have hlt : (285 / 100 : ℝ) < 2 / q := by
    rw [lt_div_iff₀ q_pos]; unfold q; linarith [Real.log_two_lt_d9]
  filter_upwards [hratio.eventually (Ici_mem_nhds hlt), eventually_gt_atTop 1] with n hrat hn
  exact (le_div_iff₀ (Real.log_pos (by exact_mod_cast hn))).mp hrat

private theorem eventually_box_mul_error_le_five_log_sq :
    ∀ᶠ n : ℕ in atTop,
      ∀ b : ℕ, b ≤ phaseNat n →
        Real.log (((n + 1) ^ b : ℕ) : ℝ) + factorialLogErrorBound n + 2 ≤
          6 * (Real.log (n : ℝ)) ^ 2 := by
  filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop 10,
    eventually_gt_atTop 10,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hL10 hn10 hph
  intro b hb
  have hL10' : 10 ≤ Real.log (n : ℝ) := hL10
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hL_pos : 0 < Real.log (n : ℝ) := by linarith
  have hlog_n1 : Real.log ((n + 1 : ℕ) : ℝ) ≤ Real.log (n : ℝ) + 1 := by
    have hle : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
      exact_mod_cast (show n + 1 ≤ 2 * n by omega)
    calc Real.log ((n + 1 : ℕ) : ℝ) ≤ Real.log (2 * (n : ℝ)) := Real.log_le_log (by positivity) hle
      _ = Real.log 2 + Real.log (n : ℝ) := Real.log_mul two_ne_zero hn_pos.ne'
      _ ≤ Real.log (n : ℝ) + 1 := by linarith [Real.log_two_lt_d9]
  have hlog_pow : Real.log (((n + 1) ^ b : ℕ) : ℝ) ≤
      4 * Real.log (n : ℝ) * (Real.log (n : ℝ) + 1) := by
    rw [Nat.cast_pow, Real.log_pow]
    have hb_le : (b : ℝ) ≤ 4 * Real.log (n : ℝ) := (Nat.cast_le.mpr hb).trans hph.2
    exact mul_le_mul hb_le hlog_n1
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 1 by omega))) (by positivity)
  have hfac : factorialLogErrorBound n ≤ Real.log (n : ℝ) + 5 := by
    have hEq : factorialLogErrorBound n = Real.log ((n + 1 : ℕ) : ℝ) + 4 := rfl
    rw [hEq]; linarith [hlog_n1]
  nlinarith [hL10', hlog_pow, hfac]

private theorem prop41_i_starBound_v12
    {n m : ℕ} (hm : m ≤ 1) (ha10 : 10 ≤ phaseNat n)
    {c₁ C_corr C_wide : ℝ}
    (hc₁_def : c₁ = Real.log 2 / 8)
    (hCw_def : C_wide = C_corr + 2)
    (hn_pos : 0 < (n : ℝ))
    (hL20 : 20 ≤ logOrder n)
    (hw_pos : 0 < logLogOrder n)
    (hL5n : 200 * (Real.log (n : ℝ)) ^ 5 ≤ (n : ℝ))
    (hphase1 : logOrder n ≤ (phaseNat n : ℝ))
    (hgap_nn : 0 ≤ phaseRootGapRadius n)
    (htn_add2_le_gap : universalShift n + 2 ≤ 2 * logLogOrder n * phaseRootGapRadius n)
    (h4_L : (4 : ℝ) ≤ (1 / 100 : ℝ) * ((n : ℝ) / logOrder n))
    (htn_L : universalShift n ≤ (1 / 400 : ℝ) * ((n : ℝ) / logOrder n))
    (hdm_le : 4 * (Nat.ceil (mu n (phaseNat n + 1 - m) + universalShift n) : ℝ) ≤
      (11 / 40 : ℝ) * ((n : ℝ) / logOrder n))
    (hr_bounds : ∀ r ∈ Set.Icc
        (phaseRootCenter n - C_corr * logLogOrder n * phaseRootGapRadius n)
        (phaseRootCenter n + C_corr * logLogOrder n * phaseRootGapRadius n),
      (29 / 100 : ℝ) * ((n : ℝ) / logOrder n) ≤ r ∧ r ≤ 2 * ((n : ℝ) / logOrder n))
    {tau r : ℝ}
    (hr : r ∈ Set.Icc (phaseRootCenter n - C_corr * logLogOrder n * phaseRootGapRadius n)
                      (phaseRootCenter n + C_corr * logLogOrder n * phaseRootGapRadius n))
    (hzr : infinitePhaseObjective m n tau r = 0)
    (hDrop_tau : ∀ s₁ ∈ Set.Icc (phaseRootCenter n - C_wide * logLogOrder n * phaseRootGapRadius n)
                                (phaseRootCenter n + C_wide * logLogOrder n * phaseRootGapRadius n),
      ∀ s₂ ∈ Set.Icc (phaseRootCenter n - C_wide * logLogOrder n * phaseRootGapRadius n)
                     (phaseRootCenter n + C_wide * logLogOrder n * phaseRootGapRadius n),
        s₁ ≤ s₂ →
          infinitePhaseObjective m n tau s₁ ≤
            infinitePhaseObjective m n tau s₂ + 1 - (q / 4 * (phaseNat n : ℝ) ^ 2) * (s₂ - s₁))
    (hTargetWide : ∀ s ∈ Set.Icc
        (phaseRootCenter n - C_wide * logLogOrder n * phaseRootGapRadius n)
        (phaseRootCenter n + C_wide * logLogOrder n * phaseRootGapRadius n),
      fourSizeTarget n (phaseNat n) s ∈ Set.Icc (9 / 4 : ℝ) (17 / 4))
    (hbox : Real.log (((n + 1) ^ (phaseNat n - m) : ℕ) : ℝ) + factorialLogErrorBound n + 2 ≤
      6 * (Real.log (n : ℝ)) ^ 2) :
    let t_n : ℝ := universalShift n
    let d_m : ℕ := Nat.ceil (mu n (phaseNat n + 1 - m) + t_n)
    let k_star : ℕ := Nat.floor r - Nat.ceil t_n
    Nat.ceil t_n + 4 * d_m + 1 ≤ Nat.floor r ∧
      (Nat.floor r : ℤ) = ⌊r⌋ ∧
      k_star < n ∧
      ∀ kp ∈ boundedColoringProfiles n (phaseNat n - m) k_star,
        profileStirlingUpperMain n kp + tau * (k_star : ℝ) +
            Real.log (((n + 1) ^ (phaseNat n - m) : ℕ) : ℝ) + factorialLogErrorBound n ≤
          -c₁ * (n : ℝ) / (Real.log (n : ℝ)) ^ 3 := by
  intro t_n d_m k_star
  set L : ℝ := logOrder n
  set w : ℝ := logLogOrder n
  have hL_real : Real.log (n : ℝ) = L := rfl
  have hL_pos : 0 < L := by linarith only [hL20]
  have hc₁_pos : 0 < c₁ := by rw [hc₁_def]; exact div_pos (Real.log_pos one_lt_two) (by norm_num)
  have htn_pos : 0 < t_n := by dsimp [t_n]; unfold universalShift; positivity
  obtain ⟨hr_lo, hr_hi⟩ := hr_bounds r hr
  have hr_nn : 0 ≤ r := le_trans (by positivity) hr_lo
  have hfl_gt : r - 1 < (Nat.floor r : ℝ) := by linarith only [Nat.lt_floor_add_one r]
  have hfl_le : (Nat.floor r : ℝ) ≤ r := Nat.floor_le hr_nn
  have hct_lt : (Nat.ceil t_n : ℝ) < t_n + 1 := Nat.ceil_lt_add_one htn_pos.le
  have hct_ge : t_n ≤ (Nat.ceil t_n : ℝ) := Nat.le_ceil t_n
  have hsub_ok_real : ((Nat.ceil t_n + 4 * d_m + 1 : ℕ) : ℝ) ≤ (Nat.floor r : ℝ) := by
    push_cast
    linarith only [hfl_gt, hct_lt, h4_L, htn_L, hdm_le, hr_lo, div_pos hn_pos hL_pos]
  have hsub_ok : Nat.ceil t_n + 4 * d_m + 1 ≤ Nat.floor r := Nat.cast_le.mp hsub_ok_real
  have hfl_int : (Nat.floor r : ℤ) = ⌊r⌋ :=
    (Int.floor_eq_iff.mpr ⟨by exact_mod_cast hfl_le,
      by exact_mod_cast Nat.lt_floor_add_one r⟩).symm
  have hk_lt_n : k_star < n := by
    have hk_le_fl : (k_star : ℝ) ≤ (Nat.floor r : ℝ) := Nat.cast_le.mpr (Nat.sub_le _ _)
    have hr_lt_n : r < (n : ℝ) := by
      have h2L : 2 * ((n : ℝ) / L) ≤ (1 / 10 : ℝ) * (n : ℝ) := by
        rw [mul_div_assoc', div_le_iff₀ hL_pos]
        have hm := mul_le_mul_of_nonneg_left hL20 hn_pos.le
        linarith only [hm]
      linarith only [hr_hi, h2L, hn_pos]
    exact Nat.cast_lt.mp (lt_of_le_of_lt (hk_le_fl.trans hfl_le) hr_lt_n)
  refine ⟨hsub_ok, hfl_int, hk_lt_n, ?_⟩
  have hk_cast : (k_star : ℝ) = (Nat.floor r : ℝ) - (Nat.ceil t_n : ℝ) :=
    Nat.cast_sub (by omega : Nat.ceil t_n ≤ Nat.floor r)
  have hk_ge : r - (t_n + 2) ≤ (k_star : ℝ) := by linarith only [hk_cast, hfl_gt, hct_lt]
  have hk_le_r : (k_star : ℝ) ≤ r - t_n := by linarith only [hk_cast, hfl_le, hct_ge]
  have hk_wide : (k_star : ℝ) ∈ Set.Icc
      (phaseRootCenter n - C_wide * w * phaseRootGapRadius n)
      (phaseRootCenter n + C_wide * w * phaseRootGapRadius n) := by
    have hcw : C_wide * w * phaseRootGapRadius n =
        C_corr * w * phaseRootGapRadius n + 2 * w * phaseRootGapRadius n := by
      rw [hCw_def]; ring
    rw [hcw]
    exact ⟨by linarith only [hk_ge, hr.1, htn_add2_le_gap],
      by linarith only [hk_le_r, hr.2, htn_pos, htn_add2_le_gap]⟩
  have hr_wide : r ∈ Set.Icc
      (phaseRootCenter n - C_wide * w * phaseRootGapRadius n)
      (phaseRootCenter n + C_wide * w * phaseRootGapRadius n) := by
    have hcw : C_corr * w * phaseRootGapRadius n ≤ C_wide * w * phaseRootGapRadius n := by
      rw [hCw_def]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith only) hw_pos.le) hgap_nn
    exact ⟨by linarith only [hr.1, hcw], by linarith only [hr.2, hcw]⟩
  have hdrop_k := hDrop_tau (k_star : ℝ) hk_wide r hr_wide (by linarith only [hk_le_r, htn_pos])
  rw [hzr, zero_add] at hdrop_k
  have ha_sq : L ^ 2 ≤ (phaseNat n : ℝ) ^ 2 := pow_le_pow_left₀ hL_pos.le hphase1 2
  have hgain : 2 * c₁ * ((n : ℝ) / L ^ 3) ≤
      (q / 4 * (phaseNat n : ℝ) ^ 2) * (r - (k_star : ℝ)) := by
    calc 2 * c₁ * ((n : ℝ) / L ^ 3)
        = (q / 4 * L ^ 2) * t_n := by
          rw [hc₁_def]; dsimp [t_n, L]; unfold universalShift q logOrder
          field_simp [hL_pos.ne']; ring
      _ ≤ (q / 4 * (phaseNat n : ℝ) ^ 2) * (r - (k_star : ℝ)) := by
          refine mul_le_mul
            (mul_le_mul_of_nonneg_left ha_sq (div_nonneg q_pos.le (by norm_num)))
            (by linarith only [hk_le_r]) htn_pos.le
            (mul_nonneg (div_nonneg q_pos.le (by norm_num)) (sq_nonneg _))
  have hTK := hTargetWide (k_star : ℝ) hk_wide
  have hT_pad : fourSizeTarget n (phaseNat n) k_star ∈ Set.Icc (17 / 8 : ℝ) (37 / 8) :=
    ⟨by linarith only [hTK.1], by linarith only [hTK.2]⟩
  intro kp hkp
  have hst := profileStirlingUpperMain_add_tau_le_infinitePhaseObjective_v12
    (hm := (by omega : m ≤ 2)) ha10 (by dsimp [k_star]; omega) tau hkp hT_pad
  change profileStirlingUpperMain n kp + tau * (k_star : ℝ) ≤
    infinitePhaseObjective m n tau (k_star : ℝ) at hst
  have hc1_lo : (1 / 12 : ℝ) ≤ c₁ := by rw [hc₁_def]; linarith only [Real.log_two_gt_d9]
  have h6L2 : 6 * (Real.log (n : ℝ)) ^ 2 + 1 ≤ c₁ * ((n : ℝ) / L ^ 3) := by
    have hnL3 : 200 * L ^ 2 ≤ (n : ℝ) / L ^ 3 := by
      rw [le_div_iff₀ (pow_pos hL_pos 3)]
      have : 200 * L ^ 2 * L ^ 3 = 200 * (Real.log (n : ℝ)) ^ 5 := by
        dsimp [L]; unfold logOrder; ring
      linarith only [this, hL5n]
    have h1 : (200 / 12 : ℝ) * L ^ 2 ≤ c₁ * ((n : ℝ) / L ^ 3) := by
      calc (200 / 12 : ℝ) * L ^ 2 = (1 / 12 : ℝ) * (200 * L ^ 2) := by ring
        _ ≤ c₁ * ((n : ℝ) / L ^ 3) := mul_le_mul hc1_lo hnL3 (by positivity) hc₁_pos.le
    have h1_L2 : (1 : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 := by
      rw [hL_real]
      calc (1 : ℝ) ≤ (20 : ℝ) ^ 2 := by norm_num
        _ ≤ L ^ 2 := pow_le_pow_left₀ (by norm_num) hL20 2
    have h1' : (200 / 12 : ℝ) * (Real.log (n : ℝ)) ^ 2 ≤ c₁ * ((n : ℝ) / L ^ 3) := by
      simpa only [hL_real] using h1
    linarith only [h1', h1_L2]
  have hneg_rw : -c₁ * (n : ℝ) / (Real.log (n : ℝ)) ^ 3 = -(c₁ * ((n : ℝ) / L ^ 3)) := by
    rw [hL_real]; ring
  linarith only [hst, hdrop_k, hgain, hbox, h6L2, hneg_rw]

private theorem prop41_i_tails_of_starBound_v12
    {n m : ℕ} (hn2 : 2 ≤ n) (ha10 : 10 ≤ phaseNat n) (hm : m ≤ 1)
    (hL20 : 20 ≤ Real.log (n : ℝ))
    {c₁ r₀ r_co : ℝ} (hc₁_def : c₁ = Real.log 2 / 8)
    (hsub0 : Nat.ceil (universalShift n) +
      4 * Nat.ceil (mu n (phaseNat n + 1 - m) + universalShift n) + 1 ≤ Nat.floor r₀)
    (hfl0 : (Nat.floor r₀ : ℤ) = ⌊r₀⌋)
    (hk0_lt : Nat.floor r₀ - Nat.ceil (universalShift n) < n)
    (hkp0 : ∀ kp ∈ boundedColoringProfiles n (phaseNat n - m) (Nat.floor r₀ - Nat.ceil (universalShift n)),
      profileStirlingUpperMain n kp + (0 : ℝ) * ((Nat.floor r₀ - Nat.ceil (universalShift n) : ℕ) : ℝ) +
          Real.log (((n + 1) ^ (phaseNat n - m) : ℕ) : ℝ) + factorialLogErrorBound n ≤
        -c₁ * (n : ℝ) / (Real.log (n : ℝ)) ^ 3)
    (hsubCo : Nat.ceil (universalShift n) +
      4 * Nat.ceil (mu n (phaseNat n + 1 - m) + universalShift n) + 1 ≤ Nat.floor r_co)
    (hflCo : (Nat.floor r_co : ℤ) = ⌊r_co⌋)
    (hkCo_lt : Nat.floor r_co - Nat.ceil (universalShift n) < n)
    (hkpCo : ∀ kp ∈ boundedColoringProfiles n (phaseNat n - m) (Nat.floor r_co - Nat.ceil (universalShift n)),
      profileStirlingUpperMain n kp + Real.log 2 * ((Nat.floor r_co - Nat.ceil (universalShift n) : ℕ) : ℝ) +
          Real.log (((n + 1) ^ (phaseNat n - m) : ℕ) : ℝ) + factorialLogErrorBound n ≤
        -c₁ * (n : ℝ) / (Real.log (n : ℝ)) ^ 3) :
    let t_n : ℝ := universalShift n
    let d_m : ℕ := Nat.ceil (mu n (phaseNat n + 1 - m) + t_n)
    let k_chi : ℕ := Nat.floor r₀ - Nat.ceil t_n - 2 * d_m
    let k_zeta : ℕ := Nat.floor r_co - Nat.ceil t_n - 4 * d_m
    1 ≤ k_zeta ∧ k_zeta + 4 * d_m < n ∧ k_chi + 2 * d_m < n ∧
      (k_chi : ℤ) = ⌊r₀⌋ - (Nat.ceil t_n : ℤ) - 2 * (d_m : ℤ) ∧
      (k_zeta : ℤ) = ⌊r_co⌋ - (Nat.ceil t_n : ℤ) - 4 * (d_m : ℤ) ∧
      (randomGraphMeasure n).real {G : LabeledGraph n | chromaticNumberNat G ≤ k_chi} ≤
        2 * quasiExpTail n + Real.exp (-c₁ * (n : ℝ) / (Real.log (n : ℝ)) ^ 3) ∧
      (randomGraphMeasure n).real {G : LabeledGraph n | cochromaticNumber G ≤ k_zeta} ≤
        2 * quasiExpTail n + Real.exp (-c₁ * (n : ℝ) / (Real.log (n : ℝ)) ^ 3) ∧
      (randomGraphMeasure n).real {G : LabeledGraph n | chromaticNumberNat G ≤ k_chi} ≤
        3 * quasiExpTail n ∧
      (randomGraphMeasure n).real {G : LabeledGraph n | cochromaticNumber G ≤ k_zeta} ≤
        3 * quasiExpTail n := by
  intro t_n d_m k_chi k_zeta
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hL_real_pos : 0 < Real.log (n : ℝ) := by linarith only [hL20]
  have hc₁_pos : 0 < c₁ := by rw [hc₁_def]; exact div_pos (Real.log_pos one_lt_two) (by norm_num)
  have htn_pos : 0 < t_n := by dsimp [t_n]; unfold universalShift; positivity
  have hk_zeta_pos : 1 ≤ k_zeta := by dsimp [k_zeta, d_m, t_n]; omega
  have hk_zeta_sum : k_zeta + 4 * d_m = Nat.floor r_co - Nat.ceil t_n := by
    dsimp [k_zeta, d_m, t_n]; omega
  have hk_chi_sum : k_chi + 2 * d_m = Nat.floor r₀ - Nat.ceil t_n := by
    dsimp [k_chi, d_m, t_n]; omega
  have hk_chi_int : (k_chi : ℤ) = ⌊r₀⌋ - (Nat.ceil t_n : ℤ) - 2 * (d_m : ℤ) := by
    rw [← hfl0]; dsimp [k_chi, d_m, t_n]; omega
  have hk_zeta_int : (k_zeta : ℤ) = ⌊r_co⌋ - (Nat.ceil t_n : ℤ) - 4 * (d_m : ℤ) := by
    rw [← hflCo]; dsimp [k_zeta, d_m, t_n]; omega
  set B_box : ℝ := Real.log (((n + 1) ^ (phaseNat n - m) : ℕ) : ℝ)
  have hB_exp : (((n + 1) ^ (phaseNat n - m) : ℕ) : ℝ) = Real.exp B_box :=
    (Real.exp_log (by positivity)).symm
  have hk0_lt_n : k_chi + 2 * d_m < n := by rw [hk_chi_sum]; exact hk0_lt
  have hkCo_lt_n : k_zeta + 4 * d_m < n := by rw [hk_zeta_sum]; exact hkCo_lt
  have htn_eq : t_n = universalShift n := rfl
  have hq_nn : 0 ≤ quasiExpTail n := by unfold quasiExpTail; positivity
  have hexp_le_quasi : Real.exp (-c₁ * (n : ℝ) / (Real.log (n : ℝ)) ^ 3) ≤ quasiExpTail n := by
    unfold quasiExpTail
    apply Real.exp_le_exp.mpr
    have hc1_lo : (1 / 12 : ℝ) ≤ c₁ := by rw [hc₁_def]; linarith only [Real.log_two_gt_d9]
    have hL7 : (24 : ℝ) ≤ (Real.log (n : ℝ)) ^ 7 := by
      have h1 : (20 : ℝ) ^ 7 ≤ (Real.log (n : ℝ)) ^ 7 := pow_le_pow_left₀ (by norm_num) hL20 7
      have hnum : (24 : ℝ) ≤ (20 : ℝ) ^ 7 := by norm_num
      linarith only [h1, hnum]
    rw [div_le_div_iff₀ (pow_pos hL_real_pos 3) (pow_pos hL_real_pos 10)]
    have hrew : -c₁ * (n : ℝ) * (Real.log (n : ℝ)) ^ 10 =
        -(c₁ * (Real.log (n : ℝ)) ^ 7) * ((n : ℝ) * (Real.log (n : ℝ)) ^ 3) := by ring
    rw [hrew]
    have h2 : 2 ≤ c₁ * (Real.log (n : ℝ)) ^ 7 := by
      have hm := mul_le_mul hc1_lo hL7 (by norm_num) hc₁_pos.le
      have hr : (1 / 12 : ℝ) * 24 = 2 := by norm_num
      linarith only [hm, hr]
    have hm_fin := mul_le_mul_of_nonneg_right h2 (mul_pos hn_pos (pow_pos hL_real_pos 3)).le
    have hr2 : -2 * (n : ℝ) * (Real.log (n : ℝ)) ^ 3 =
        -(2 * ((n : ℝ) * (Real.log (n : ℝ)) ^ 3)) := by ring
    have hr3 : -(c₁ * (Real.log (n : ℝ)) ^ 7) * ((n : ℝ) * (Real.log (n : ℝ)) ^ 3) =
        -(c₁ * (Real.log (n : ℝ)) ^ 7 * ((n : ℝ) * (Real.log (n : ℝ)) ^ 3)) := by ring
    linarith only [hm_fin, hr2, hr3]
  let k_star0 : ℕ := k_chi + 2 * d_m
  have hexp0_enn := boundedProfileColoringExpectation_le_box_mul_exp n (phaseNat n - m) k_star0
    (-c₁ * (n : ℝ) / (Real.log (n : ℝ)) ^ 3 - B_box) (fun kp hkp ↦ by
      have hkp' : kp ∈ boundedColoringProfiles n (phaseNat n - m) (Nat.floor r₀ - Nat.ceil t_n) := by
        change kp ∈ boundedColoringProfiles n (phaseNat n - m) (k_chi + 2 * d_m) at hkp
        rwa [← hk_chi_sum]
      have h := hkp0 kp hkp'
      simp only [zero_mul, add_zero] at h
      change profileStirlingUpperMain n kp + B_box + factorialLogErrorBound n ≤
        -c₁ * (n : ℝ) / (Real.log (n : ℝ)) ^ 3 at h
      linarith only [h])
  have hexp0_real :
      (boundedProfileColoringExpectation n (phaseNat n - m) (k_chi + 2 * d_m)).toReal ≤
        Real.exp (-c₁ * (n : ℝ) / (Real.log (n : ℝ)) ^ 3) := by
    have htr := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top) hexp0_enn
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (Real.exp_pos _).le,
      hB_exp, ← Real.exp_add] at htr
    exact htr.trans_eq (by congr 1; ring)
  let k_starCo : ℕ := k_zeta + 4 * d_m
  have hexpCo_enn := boundedProfileColoringExpectation_le_box_mul_exp n (phaseNat n - m) k_starCo
    (-c₁ * (n : ℝ) / (Real.log (n : ℝ)) ^ 3 - B_box - Real.log 2 * (k_starCo : ℝ))
    (fun kp hkp ↦ by
      have hkp' : kp ∈ boundedColoringProfiles n (phaseNat n - m) (Nat.floor r_co - Nat.ceil t_n) := by
        change kp ∈ boundedColoringProfiles n (phaseNat n - m) (k_zeta + 4 * d_m) at hkp
        rwa [← hk_zeta_sum]
      have h := hkpCo kp hkp'
      have hk_eq : ((Nat.floor r_co - Nat.ceil t_n : ℕ) : ℝ) = (k_starCo : ℝ) := by
        dsimp [k_starCo]; rw [hk_zeta_sum]
      rw [hk_eq] at h
      change profileStirlingUpperMain n kp + Real.log 2 * (k_starCo : ℝ) +
          B_box + factorialLogErrorBound n ≤
        -c₁ * (n : ℝ) / (Real.log (n : ℝ)) ^ 3 at h
      linarith only [h])
  have hexpCo_real :
      (2 : ℝ) ^ (k_zeta + 4 * d_m) *
          (boundedProfileColoringExpectation n (phaseNat n - m) (k_zeta + 4 * d_m)).toReal ≤
        Real.exp (-c₁ * (n : ℝ) / (Real.log (n : ℝ)) ^ 3) := by
    have htr := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top) hexpCo_enn
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (Real.exp_pos _).le,
      hB_exp, ← Real.exp_add] at htr
    have h2k : (2 : ℝ) ^ k_starCo = Real.exp (Real.log 2 * (k_starCo : ℝ)) := by
      rw [mul_comm, Real.exp_nat_mul, Real.exp_log two_pos]
    calc (2 : ℝ) ^ k_starCo *
            (boundedProfileColoringExpectation n (phaseNat n - m) k_starCo).toReal
        ≤ Real.exp (Real.log 2 * (k_starCo : ℝ)) *
            Real.exp (B_box + (-c₁ * (n : ℝ) / (Real.log (n : ℝ)) ^ 3 - B_box -
              Real.log 2 * (k_starCo : ℝ))) := by
          rw [← h2k]
          exact mul_le_mul_of_nonneg_left htr (by positivity)
      _ = Real.exp (-c₁ * (n : ℝ) / (Real.log (n : ℝ)) ^ 3) := by
          rw [← Real.exp_add]; congr 1; ring
  have hmcd := exp_mcdiarmid_universalShift_le_quasiExpTail hn2
  have hchi_prob :
      (randomGraphMeasure n).real {G : LabeledGraph n | chromaticNumberNat G ≤ k_chi} ≤
        2 * quasiExpTail n + Real.exp (-c₁ * (n : ℝ) / (Real.log (n : ℝ)) ^ 3) := by
    have hsp := randomGraph_chromaticNumberAtMost_le_of_unconditional_splitting
      (u := phaseNat n + 1 - m) hn2 (by omega) htn_pos.le (Nat.le_ceil _) hk0_lt_n.le
    rw [show phaseNat n + 1 - m - 1 = phaseNat n - m by omega, htn_eq] at hsp
    linarith only [hsp, hmcd, hexp0_real, hq_nn]
  have hzeta_prob :
      (randomGraphMeasure n).real {G : LabeledGraph n | cochromaticNumber G ≤ k_zeta} ≤
        2 * quasiExpTail n + Real.exp (-c₁ * (n : ℝ) / (Real.log (n : ℝ)) ^ 3) := by
    have hsp := randomGraph_cochromaticNumberAtMost_le_of_unconditional_splitting
      (u := phaseNat n + 1 - m) hn2 (by omega) htn_pos.le (Nat.le_ceil _) hkCo_lt_n.le
    rw [show phaseNat n + 1 - m - 1 = phaseNat n - m by omega, htn_eq] at hsp
    linarith only [hsp, hmcd, hexpCo_real]
  exact ⟨hk_zeta_pos, hkCo_lt_n, hk0_lt_n, hk_chi_int, hk_zeta_int, hchi_prob, hzeta_prob,
    by linarith only [hchi_prob, hexp_le_quasi], by linarith only [hzeta_prob, hexp_le_quasi]⟩

/-- **Proposition 4.1(i) (`prop:lower-tails`, `main.tex` lines 653–656) unconditional lower tails:**
there exist `c₁ > 0` (`c₁ = log 2 / 8`) and `C_corr > 0` such that eventually for all `m ≤ 1`
(restricted when `m = 1` to `μ_α ≤ n / (16 log n)`):
1. `𝓛_{S_{≥ m}}(n, ·)` and `𝓛_{S_{≥ m}}(n, ·) + (log 2) ·` have unique zeros `r₀, r_co` in the
   corridor `(c_n - C_corr Δ_n, c_n + C_corr Δ_n)`,
2. at `k_{χ, m}^- := ⌊r₀⌋₊ - ⌈t_n⌉₊ - 2 d_{n, m}` and `k_{ζ, m}^- := ⌊r_co⌋₊ - ⌈t_n⌉₊ - 4 d_{n, m}`,
   `1 ≤ k_{ζ, m}^-`, `ℕ`-subtraction agrees with exact `ℤ`-subtraction, and both
   `P(χ(G_n) ≤ k_{χ, m}^-)` and `P(ζ(G_n) ≤ k_{ζ, m}^-)` are bounded by
   `2 * quasiExpTail n + exp(-c₁ n / (log n)³)` AND by `3 * quasiExpTail n`. -/
theorem eventually_randomGraph_lowerTails_prop41_i :
    ∃ c₁ C_corr : ℝ, 0 < c₁ ∧ 0 < C_corr ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ m : ℕ, m ≤ 1 →
          (m = 1 → mu n (phaseNat n) ≤ (n : ℝ) / (16 * Real.log (n : ℝ))) →
            let F_fin : ℝ → ℝ := fun T ↦ ⨅ l : ℝ,
              (Real.log (∑ i ∈ Finset.Ico m (phaseNat n),
                  Real.exp (l * (i : ℝ) +
                    (Real.log ((phaseNat n).descFactorial i : ℝ) -
                      (i : ℝ) * Real.log (phaseNat n : ℝ) -
                      Real.log 2 / 2 * (i : ℝ) ^ 2))) - l * T)
            let obj : ℝ → ℝ → ℝ := fun tau s ↦
              (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + s - s * Real.log s +
                s * (profileDeficitAffineA (phaseNat n) +
                  profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s +
                  F_fin (fourSizeTarget n (phaseNat n) s) + tau)
            (∃! r₀ : ℝ,
              r₀ ∈ Set.Ioo (phaseRootCenter n - C_corr * logLogOrder n * phaseRootGapRadius n)
                           (phaseRootCenter n + C_corr * logLogOrder n * phaseRootGapRadius n) ∧
                obj 0 r₀ = 0) ∧
            (∃! r_co : ℝ,
              r_co ∈ Set.Ioo (phaseRootCenter n - C_corr * logLogOrder n * phaseRootGapRadius n)
                             (phaseRootCenter n + C_corr * logLogOrder n * phaseRootGapRadius n) ∧
                obj (Real.log 2) r_co = 0) ∧
            ∀ r₀ ∈ Set.Icc (phaseRootCenter n - C_corr * logLogOrder n * phaseRootGapRadius n)
                           (phaseRootCenter n + C_corr * logLogOrder n * phaseRootGapRadius n),
              obj 0 r₀ = 0 →
              ∀ r_co ∈ Set.Icc (phaseRootCenter n - C_corr * logLogOrder n * phaseRootGapRadius n)
                               (phaseRootCenter n + C_corr * logLogOrder n * phaseRootGapRadius n),
                obj (Real.log 2) r_co = 0 →
                let t_n : ℝ := universalShift n
                let d_m : ℕ := Nat.ceil (mu n (phaseNat n + 1 - m) + t_n)
                let k_chi : ℕ := Nat.floor r₀ - Nat.ceil t_n - 2 * d_m
                let k_zeta : ℕ := Nat.floor r_co - Nat.ceil t_n - 4 * d_m
                1 ≤ k_zeta ∧ k_zeta + 4 * d_m < n ∧ k_chi + 2 * d_m < n ∧
                  (k_chi : ℤ) = ⌊r₀⌋ - (Nat.ceil t_n : ℤ) - 2 * (d_m : ℤ) ∧
                  (k_zeta : ℤ) = ⌊r_co⌋ - (Nat.ceil t_n : ℤ) - 4 * (d_m : ℤ) ∧
                  (randomGraphMeasure n).real {G : LabeledGraph n | chromaticNumberNat G ≤ k_chi} ≤
                    2 * quasiExpTail n + Real.exp (-c₁ * (n : ℝ) / (Real.log (n : ℝ)) ^ 3) ∧
                  (randomGraphMeasure n).real {G : LabeledGraph n | cochromaticNumber G ≤ k_zeta} ≤
                    2 * quasiExpTail n + Real.exp (-c₁ * (n : ℝ) / (Real.log (n : ℝ)) ^ 3) ∧
                  (randomGraphMeasure n).real {G : LabeledGraph n | chromaticNumberNat G ≤ k_chi} ≤
                    3 * quasiExpTail n ∧
                  (randomGraphMeasure n).real {G : LabeledGraph n | cochromaticNumber G ≤ k_zeta} ≤
                    3 * quasiExpTail n := by
  obtain ⟨C_corr, _, hC_pos, _, hRootEv⟩ :=
    exists_pos_eventually_existsUnique_infinitePhaseObjective_zero_logLogCorridor
  set c₁ : ℝ := Real.log 2 / 8
  have hc₁_pos : 0 < c₁ := div_pos (Real.log_pos one_lt_two) (by norm_num)
  refine ⟨c₁, C_corr, hc₁_pos, hC_pos, ?_⟩
  set C_wide : ℝ := C_corr + 2
  have hC_wide_nn : 0 ≤ C_wide := by dsimp [C_wide]; positivity
  have ho_L5 : (fun x : ℝ ↦ (Real.log x) ^ ((5 : ℕ) : ℝ)) =o[atTop] (fun x : ℝ ↦ x ^ (1 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop ((5 : ℕ) : ℝ) zero_lt_one
  have hL5_small : ∀ᶠ n : ℕ in atTop, 200 * (Real.log (n : ℝ)) ^ 5 ≤ (n : ℝ) := by
    have hb := (ho_L5.comp_tendsto tendsto_natCast_atTop_atTop).bound (by norm_num : (0 : ℝ) < 1 / 200)
    filter_upwards [hb, eventually_gt_atTop 2] with n hn hn2
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hL_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    dsimp only [Function.comp_apply] at hn
    rw [Real.rpow_natCast, Real.norm_eq_abs, abs_of_pos (pow_pos hL_pos 5),
      Real.rpow_one, Real.norm_eq_abs, abs_of_pos hn_pos] at hn
    linarith
  set eps_w : ℝ := min (1 / 200) (1 / (100 * (C_corr + 1)))
  have heps_w_pos : 0 < eps_w := lt_min (by norm_num) (by positivity)
  have hwL_small : ∀ᶠ n : ℕ in atTop, ‖logLogOrder n‖ ≤ eps_w * ‖logOrder n‖ :=
    logLogOrder_isLittleO_logOrder.bound heps_w_pos
  filter_upwards [hRootEv,
    eventually_infinitePhaseObjective_strictMonoOn_and_drop C_wide hC_wide_nn,
    eventually_phaseRootLogLogCorridor_fourSize_target_mem_Icc C_wide hC_wide_nn,
    eventually_mu_phaseNat_succ_and_deltaStar_le_v12,
    eventually_phaseRootCenter_sub_main_logLogRate_v12,
    eventually_corridor_inv_target_logLogRate_v12 C_corr hC_pos.le,
    eventually_box_mul_error_le_five_log_sq,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
    hL5_small, hwL_small,
    tendsto_logLogOrder_atTop.eventually_ge_atTop 2,
    tendsto_logOrder_atTop.eventually_ge_atTop (max 20 (64 / Real.log 2))] with
    n hRoots hDrop hTargetWide hMuBds hcMain hInv hBoxErr hphase hL5n hwL hw2 hLbig
    m hm hmu1 F_fin obj
  have hobj_eq : obj = infinitePhaseObjective m n := rfl
  rw [hobj_eq]
  clear hobj_eq obj F_fin
  clear hRootEv
  have htau0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.log 2) := ⟨le_rfl, (Real.log_pos one_lt_two).le⟩
  have htauL : Real.log 2 ∈ Set.Icc (0 : ℝ) (Real.log 2) := ⟨(Real.log_pos one_lt_two).le, le_rfl⟩
  have hex0 := (hRoots m (by omega) 0 htau0).2.1
  have hexCo := (hRoots m (by omega) (Real.log 2) htauL).2.1
  clear hRoots
  refine ⟨hex0, hexCo, ?_⟩
  clear hex0 hexCo
  intro r₀ hr₀ hz₀ r_co hr_co hz_co t_n d_m k_chi k_zeta
  set L : ℝ := logOrder n
  set w : ℝ := logLogOrder n
  have hL_real : Real.log (n : ℝ) = L := rfl
  have hL20 : 20 ≤ L := (le_max_left _ _).trans hLbig
  have hL_pos : 0 < L := by linarith
  have hw_pos : 0 < w := by linarith
  have hL5n' : 200 * L ^ 5 ≤ (n : ℝ) := by rwa [← hL_real]
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have hle0 : Real.log (n : ℝ) ≤ 0 := by
      rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl <;> simp
    rw [hL_real] at hle0
    linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have ha10 : 10 ≤ phaseNat n := by
    have : (20 : ℝ) ≤ (phaseNat n : ℝ) := hL20.trans hphase.1
    exact_mod_cast (by linarith : (10 : ℝ) ≤ (phaseNat n : ℝ))
  rw [Real.norm_eq_abs, abs_of_pos hw_pos, Real.norm_eq_abs, abs_of_pos hL_pos] at hwL
  have hwL_200 : w ≤ (1 / 200) * L :=
    hwL.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hL_pos.le)
  have hwL_corr : C_corr * w ≤ (1 / 100) * L := by
    have h1 := hwL.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hL_pos.le)
    have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ C_corr + 1 by positivity)
    have h3 : (C_corr + 1) * (1 / (100 * (C_corr + 1)) * L) = (1 / 100) * L := by
      field_simp [(show (0 : ℝ) < C_corr + 1 by positivity).ne']
    linarith [mul_pos hC_pos hw_pos]
  clear ho_L5 hL5_small hwL_small hwL hLbig
  clear_value eps_w
  have htn_pos : 0 < t_n := by dsimp [t_n]; unfold universalShift; positivity
  have hc_lo : (3 / 10 : ℝ) * ((n : ℝ) / L) ≤ phaseRootCenter n := by
    have h1 := (abs_le.mp hcMain.2).1
    have h2 : 4 * (n : ℝ) * w / L ^ 2 ≤ (1 / 50 : ℝ) * ((n : ℝ) / L) := by
      calc 4 * (n : ℝ) * w / L ^ 2
          ≤ 4 * (n : ℝ) * ((1 / 200) * L) / L ^ 2 :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hwL_200 (by positivity)) (sq_nonneg L)
        _ = (1 / 50 : ℝ) * ((n : ℝ) / L) := by field_simp [hL_pos.ne']; ring
    have hq_num : (16 / 50 : ℝ) * ((n : ℝ) / L) ≤ (Real.log 2 / 2) * ((n : ℝ) / L) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.log_two_gt_d9]) (div_nonneg hn_pos.le hL_pos.le)
    linarith [div_pos hn_pos hL_pos]
  have hgap_lo : (1 / 60 : ℝ) * ((n : ℝ) / L ^ 3) ≤ phaseRootGapRadius n := by
    unfold phaseRootGapRadius
    have ha_sq : (phaseNat n : ℝ) ^ 2 ≤ 16 * L ^ 2 := by
      calc (phaseNat n : ℝ) ^ 2 ≤ (4 * L) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hphase.2 2
        _ = 16 * L ^ 2 := by ring
    calc (1 / 60 : ℝ) * ((n : ℝ) / L ^ 3)
        ≤ (3 / 160 : ℝ) * ((n : ℝ) / L ^ 3) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = ((3 / 10 : ℝ) * ((n : ℝ) / L)) / (16 * L ^ 2) := by field_simp [hL_pos.ne']; ring
      _ ≤ phaseRootCenter n / (16 * L ^ 2) :=
          div_le_div_of_nonneg_right hc_lo (by positivity)
      _ ≤ phaseRootCenter n / (phaseNat n : ℝ) ^ 2 :=
          div_le_div_of_nonneg_left (by linarith [div_pos hn_pos hL_pos])
            (sq_pos_of_pos (lt_of_lt_of_le hL_pos hphase.1)) ha_sq
  have hgap_nn : 0 ≤ phaseRootGapRadius n := le_trans (by positivity) hgap_lo
  have hgap_hi : phaseRootGapRadius n ≤ (n : ℝ) / L ^ 3 := by
    unfold phaseRootGapRadius
    have ha_sq : L ^ 2 ≤ (phaseNat n : ℝ) ^ 2 := pow_le_pow_left₀ hL_pos.le hphase.1 2
    calc phaseRootCenter n / (phaseNat n : ℝ) ^ 2
        ≤ ((n : ℝ) / L) / L ^ 2 :=
          div_le_div₀ (div_nonneg hn_pos.le hL_pos.le) hcMain.1 (sq_pos_of_pos hL_pos) ha_sq
      _ = (n : ℝ) / L ^ 3 := by ring
  have htn_add2_le_gap : t_n + 2 ≤ 2 * w * phaseRootGapRadius n := by
    have h1 : t_n ≤ (1 / 400 : ℝ) * ((n : ℝ) / L ^ 3) := by
      dsimp [t_n]; unfold universalShift
      have hL2 : (400 : ℝ) ≤ L ^ 2 := by
        have := pow_le_pow_left₀ (by norm_num) hL20 2; norm_num at this; exact this
      calc (n : ℝ) / (Real.log (n : ℝ)) ^ 5
          = (n : ℝ) / (L ^ 2 * L ^ 3) := by rw [hL_real]; ring
        _ ≤ (n : ℝ) / (400 * L ^ 3) :=
            div_le_div_of_nonneg_left hn_pos.le (by positivity)
              (mul_le_mul_of_nonneg_right hL2 (by positivity))
        _ = (1 / 400 : ℝ) * ((n : ℝ) / L ^ 3) := by ring
    have h2 : (2 : ℝ) ≤ (1 / 100 : ℝ) * ((n : ℝ) / L ^ 3) := by
      rw [mul_div_assoc', le_div_iff₀ (pow_pos hL_pos 3)]
      have hL35 : L ^ 3 ≤ L ^ 5 := pow_le_pow_right₀ (by linarith : 1 ≤ L) (by omega)
      linarith [hL5n', pow_pos hL_pos 3]
    have hw_gap : (4 / 60 : ℝ) * ((n : ℝ) / L ^ 3) ≤ 2 * w * phaseRootGapRadius n :=
      calc (4 / 60 : ℝ) * ((n : ℝ) / L ^ 3)
          = 4 * ((1 / 60 : ℝ) * ((n : ℝ) / L ^ 3)) := by ring
        _ ≤ (2 * w) * phaseRootGapRadius n :=
            mul_le_mul (by linarith [hw2]) hgap_lo (by positivity) (by positivity)
        _ = 2 * w * phaseRootGapRadius n := by ring
    linarith [div_pos hn_pos (pow_pos hL_pos 3)]
  have hmu_le_16 : mu n (phaseNat n + 1 - m) ≤ (n : ℝ) / (16 * L) := by
    rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
    · simp only [Nat.sub_zero]
      refine hMuBds.1.trans ?_
      unfold universalShift
      rw [hL_real]
      exact div_le_div_of_nonneg_left hn_pos.le (by positivity) (by
        have h16 : (16 : ℝ) ≤ L ^ 4 := by
          calc (16 : ℝ) ≤ (20 : ℝ) ^ 4 := by norm_num
            _ ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hL20 4
        calc 16 * L ≤ L ^ 4 * L := mul_le_mul_of_nonneg_right h16 hL_pos.le
          _ = L ^ 5 := by ring)
    · rw [← hL_real]; exact hmu1 rfl
  have h4_L : (4 : ℝ) ≤ (1 / 100 : ℝ) * ((n : ℝ) / L) := by
    rw [mul_div_assoc', le_div_iff₀ hL_pos]
    have h2L5 : 2 * L ≤ L ^ 5 := by
      have h2L4 : (2 : ℝ) ≤ L ^ 4 := by
        calc (2 : ℝ) ≤ (20 : ℝ) ^ 4 := by norm_num
          _ ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hL20 4
      calc 2 * L ≤ L ^ 4 * L := mul_le_mul_of_nonneg_right h2L4 hL_pos.le
        _ = L ^ 5 := by ring
    linarith [hL5n']
  have htn_L : t_n ≤ (1 / 400 : ℝ) * ((n : ℝ) / L) := by
    dsimp [t_n]; unfold universalShift
    have hL4 : (400 : ℝ) ≤ L ^ 4 := by
      calc (400 : ℝ) ≤ (20 : ℝ) ^ 4 := by norm_num
        _ ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hL20 4
    calc (n : ℝ) / (Real.log (n : ℝ)) ^ 5 = (n : ℝ) / (L ^ 4 * L) := by rw [hL_real]; ring
      _ ≤ (n : ℝ) / (400 * L) := div_le_div_of_nonneg_left hn_pos.le (by positivity)
          (mul_le_mul_of_nonneg_right hL4 hL_pos.le)
      _ = (1 / 400 : ℝ) * ((n : ℝ) / L) := by ring
  have hdm_le : 4 * (d_m : ℝ) ≤ (11 / 40 : ℝ) * ((n : ℝ) / L) := by
    have hc := Nat.ceil_lt_add_one (add_nonneg (mu_nonneg n (phaseNat n + 1 - m)) htn_pos.le)
    have hmu_eq : (n : ℝ) / (16 * L) = (1 / 16 : ℝ) * ((n : ℝ) / L) := by ring
    change 4 * (Nat.ceil (mu n (phaseNat n + 1 - m) + t_n) : ℝ) ≤ (11 / 40 : ℝ) * ((n : ℝ) / L)
    linarith only [hc, hmu_le_16, hmu_eq, htn_L, h4_L, div_pos hn_pos hL_pos]
  have hr_bounds : ∀ r ∈ Set.Icc
      (phaseRootCenter n - C_corr * w * phaseRootGapRadius n)
      (phaseRootCenter n + C_corr * w * phaseRootGapRadius n),
      (29 / 100 : ℝ) * ((n : ℝ) / L) ≤ r ∧ r ≤ 2 * ((n : ℝ) / L) := by
    intro r hr
    have hdelta_le : C_corr * w * phaseRootGapRadius n ≤ (1 / 100 : ℝ) * ((n : ℝ) / L) := by
      have hgap_L : phaseRootGapRadius n ≤ (n : ℝ) / L ^ 2 := by
        calc phaseRootGapRadius n ≤ (n : ℝ) / L ^ 3 := hgap_hi
          _ = ((n : ℝ) / L ^ 2) / L := by ring
          _ ≤ ((n : ℝ) / L ^ 2) / 1 :=
              div_le_div_of_nonneg_left (by positivity) zero_lt_one (by linarith [hL20])
          _ = (n : ℝ) / L ^ 2 := div_one _
      calc C_corr * w * phaseRootGapRadius n
          ≤ ((1 / 100) * L) * ((n : ℝ) / L ^ 2) :=
            mul_le_mul hwL_corr hgap_L hgap_nn (by positivity)
        _ = (1 / 100 : ℝ) * ((n : ℝ) / L) := by field_simp [hL_pos.ne']
    exact ⟨by linarith [hr.1, hc_lo],
      (hInv.2 r hr).2.1.trans (mul_le_mul_of_nonneg_left hcMain.1 zero_le_two)⟩
  obtain ⟨hsub0, hfl0, hk0_lt, hkp0⟩ := prop41_i_starBound_v12 hm ha10 rfl rfl hn_pos hL20 hw_pos
    hL5n hphase.1 hgap_nn htn_add2_le_gap h4_L htn_L hdm_le hr_bounds hr₀ hz₀
    (hDrop m (by omega) 0 htau0).2 hTargetWide (hBoxErr (phaseNat n - m) (Nat.sub_le _ _))
  obtain ⟨hsubCo, hflCo, hkCo_lt, hkpCo⟩ := prop41_i_starBound_v12 hm ha10 rfl rfl hn_pos hL20 hw_pos
    hL5n hphase.1 hgap_nn htn_add2_le_gap h4_L htn_L hdm_le hr_bounds hr_co hz_co
    (hDrop m (by omega) (Real.log 2) htauL).2 hTargetWide (hBoxErr (phaseNat n - m) (Nat.sub_le _ _))
  exact prop41_i_tails_of_starBound_v12 hn2 ha10 hm (hL_real ▸ hL20) rfl
    hsub0 hfl0 hk0_lt hkp0 hsubCo hflCo hkCo_lt hkpCo

private theorem binEntropy_le_seventyThree_sq_div_v12
    {p w L : ℝ} (hp0 : 0 ≤ p) (hpu : p ≤ 36 * (w / L)) (hp1 : p < 1)
    (hw1 : 1 ≤ w) (hL_pos : 0 < L) (hw_eq : w = Real.log L) :
    binEntropy p ≤ 73 * w ^ 2 / L := by
  set u : ℝ := w / L
  have hw_pos : 0 < w := lt_of_lt_of_le zero_lt_one hw1
  have hu_pos : 0 < u := div_pos hw_pos hL_pos
  have h1mp : 0 < 1 - p := sub_pos.mpr hp1
  have hterm2 : -(1 - p) * Real.log (1 - p) ≤ 36 * u * w := by
    have hlog := Real.log_le_sub_one_of_pos (div_pos one_pos h1mp)
    rw [one_div, Real.log_inv] at hlog
    have hm := mul_le_mul_of_nonneg_left hlog h1mp.le
    have hc : (1 - p) * ((1 - p)⁻¹ - 1) = p := by field_simp [h1mp.ne']; ring
    have hpw : p ≤ 36 * u * w :=
      hpu.trans (le_mul_of_one_le_right (by positivity) hw1)
    linarith
  have hterm1 : -p * Real.log p ≤ 37 * u * w := by
    rcases eq_or_lt_of_le hp0 with rfl | hp_pos
    · simp; positivity
    · have hlog_up := Real.log_le_sub_one_of_pos (div_pos hu_pos hp_pos)
      rw [Real.log_div hu_pos.ne' hp_pos.ne'] at hlog_up
      have hm1 := mul_le_mul_of_nonneg_left hlog_up hp_pos.le
      have hc1 : p * (u / p - 1) = u - p := by field_simp [hp_pos.ne']
      have hlog_u : -Real.log u ≤ w := by
        dsimp [u]
        rw [Real.log_div hw_pos.ne' hL_pos.ne', ← hw_eq]
        linarith [Real.log_nonneg hw1]
      have hm2' : p * (-Real.log u) ≤ (36 * u) * w := by
        calc p * (-Real.log u) ≤ p * w := mul_le_mul_of_nonneg_left hlog_u hp_pos.le
          _ ≤ (36 * u) * w := mul_le_mul_of_nonneg_right hpu hw_pos.le
      have huw : u ≤ u * w := le_mul_of_one_le_right hu_pos.le hw1
      linarith
  unfold binEntropy
  have hrhs : 37 * u * w + 36 * u * w = 73 * w ^ 2 / L := by dsimp [u]; ring
  linarith

private theorem prop41_ii_discrepancy_le_v12
    {n : ℕ}
    {C_dual B_F0 C_err T p_top : ℝ}
    (hC_dual_pos : 0 < C_dual)
    (hBF0_def : B_F0 = |Real.log (partitionFn Splus 0)| +
      |min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))| + 1)
    (hC_err_def : C_err = 73 + 2 * C_dual + 360 * universalDualLip_v12 + 36 * B_F0 + 1)
    (hphase1 : logOrder n ≤ (phaseNat n : ℝ))
    (hL_pos : 0 < logOrder n)
    (hw2 : 2 ≤ logLogOrder n)
    (hTK : T ∈ Set.Icc (9 / 4 : ℝ) (17 / 4))
    (hp_nn : 0 ≤ p_top)
    (hp_le_36 : p_top ≤ 36 * (logLogOrder n / logOrder n))
    (hp_le_20 : p_top ≤ 1 / 20)
    (hInfDual_1 : ∀ {T' : ℝ}, T' ∈ Set.Icc (9 / 4 : ℝ) (9 / 2) →
      |infiniteFiniteEntropy (phaseNat n) 1 T' - dualValue {j : ℤ | ((1 : ℕ) : ℤ) ≤ j} T'| ≤
        C_dual / (phaseNat n : ℝ)) :
    binEntropy p_top +
      (1 - p_top) * infiniteFiniteEntropy (phaseNat n) 1 (T / (1 - p_top)) -
      infiniteFiniteEntropy (phaseNat n) 1 T ≤
    C_err * (logLogOrder n) ^ 2 / logOrder n := by
  set L : ℝ := logOrder n
  set ell : ℝ := logLogOrder n
  have h1mp_pos : 0 < 1 - p_top := sub_pos.mpr (lt_of_le_of_lt hp_le_20 (by norm_num))
  have h1mp_le1 : 1 - p_top ≤ 1 := sub_le_self 1 hp_nn
  have hT_wide : T ∈ Set.Icc (9 / 4 : ℝ) (9 / 2) := ⟨hTK.1, by linarith only [hTK.2]⟩
  have hTu_wide : T / (1 - p_top) ∈ Set.Icc (9 / 4 : ℝ) (9 / 2) := by
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ h1mp_pos]
      linarith only [hTK.1, mul_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 4) hp_nn]
    · rw [div_le_iff₀ h1mp_pos]; linarith only [hTK.2, hp_le_20]
  have hd1 := hInfDual_1 hTu_wide
  have hd2 := hInfDual_1 hT_wide
  have hlip := abs_dualValue_infinite_sub_le (m := 1) (by omega) hTu_wide hT_wide
  have hS1_eq : infiniteSupportSet 1 = {j : ℤ | ((1 : ℕ) : ℤ) ≤ j} := rfl
  rw [hS1_eq] at hlip
  have hTu_diff : |T / (1 - p_top) - T| ≤ 10 * p_top := by
    have hT_nn : 0 ≤ T := by linarith only [hTK.1]
    have hid : T / (1 - p_top) - T = T * p_top / (1 - p_top) := by field_simp [h1mp_pos.ne']; ring
    rw [hid, abs_of_nonneg (div_nonneg (mul_nonneg hT_nn hp_nn) h1mp_pos.le), div_le_iff₀ h1mp_pos]
    have hm := mul_le_mul_of_nonneg_right (by linarith only [hTK.2, hp_le_20] : T ≤ 10 * (1 - p_top)) hp_nn
    linarith only [hm, show 10 * (1 - p_top) * p_top = 10 * p_top * (1 - p_top) by ring]
  have hd_bds := dualValue_infinite_bounds_on_padded (m := 1) (by omega)
    (T := T / (1 - p_top)) ⟨by linarith only [hTu_wide.1], by linarith only [hTu_wide.2]⟩
  rw [hS1_eq] at hd_bds
  have hd_abs : |dualValue {j : ℤ | ((1 : ℕ) : ℤ) ≤ j} (T / (1 - p_top))| ≤ B_F0 := by
    rw [hBF0_def]
    exact abs_le.mpr ⟨by
        linarith only [hd_bds.1,
          abs_nonneg (Real.log (partitionFn Splus 0)),
          neg_abs_le (min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8)))],
      by
        linarith only [hd_bds.2, le_abs_self (Real.log (partitionFn Splus 0)),
          abs_nonneg (min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8)))]⟩
  have hbin_le := binEntropy_le_seventyThree_sq_div_v12 hp_nn hp_le_36
    (lt_of_le_of_lt hp_le_20 (by norm_num)) (by linarith only [hw2]) hL_pos rfl
  have hcd_le : C_dual / (phaseNat n : ℝ) ≤ C_dual * ell ^ 2 / L := by
    calc C_dual / (phaseNat n : ℝ) ≤ C_dual / L :=
          div_le_div_of_nonneg_left hC_dual_pos.le hL_pos hphase1
      _ ≤ C_dual * ell ^ 2 / L := by
          apply div_le_div_of_nonneg_right _ hL_pos.le
          exact le_mul_of_one_le_right hC_dual_pos.le (one_le_pow₀ (by linarith only [hw2]))
  have h1_err : |(1 - p_top) *
      (infiniteFiniteEntropy (phaseNat n) 1 (T / (1 - p_top)) -
        dualValue {j : ℤ | ((1 : ℕ) : ℤ) ≤ j} (T / (1 - p_top)))| ≤
      C_dual * ell ^ 2 / L := by
    rw [abs_mul, abs_of_pos h1mp_pos]
    calc (1 - p_top) * |infiniteFiniteEntropy (phaseNat n) 1 (T / (1 - p_top)) -
            dualValue {j : ℤ | ((1 : ℕ) : ℤ) ≤ j} (T / (1 - p_top))|
        ≤ 1 * (C_dual / (phaseNat n : ℝ)) :=
          mul_le_mul h1mp_le1 hd1 (abs_nonneg _) zero_le_one
      _ ≤ C_dual * ell ^ 2 / L := by rw [one_mul]; exact hcd_le
  have h2_err : |infiniteFiniteEntropy (phaseNat n) 1 T -
      dualValue {j : ℤ | ((1 : ℕ) : ℤ) ≤ j} T| ≤ C_dual * ell ^ 2 / L :=
    hd2.trans hcd_le
  have h3_err : |dualValue {j : ℤ | ((1 : ℕ) : ℤ) ≤ j} (T / (1 - p_top)) -
      dualValue {j : ℤ | ((1 : ℕ) : ℤ) ≤ j} T| ≤
      360 * universalDualLip_v12 * ell ^ 2 / L := by
    have hp_w2 : 10 * p_top ≤ 360 * ell ^ 2 / L := by
      calc 10 * p_top ≤ 360 * (ell / L) := by linarith only [hp_le_36]
        _ ≤ 360 * ell ^ 2 / L := by
            rw [mul_div_assoc', div_le_div_iff_of_pos_right hL_pos]
            have hpow := pow_le_pow_right₀ (by linarith only [hw2] : 1 ≤ ell) (by omega : 1 ≤ 2)
            rw [pow_one] at hpow; linarith only [hpow]
    calc |dualValue {j : ℤ | ((1 : ℕ) : ℤ) ≤ j} (T / (1 - p_top)) -
            dualValue {j : ℤ | ((1 : ℕ) : ℤ) ≤ j} T|
        ≤ universalDualLip_v12 * (360 * ell ^ 2 / L) :=
          hlip.trans (mul_le_mul_of_nonneg_left (hTu_diff.trans hp_w2) universalDualLip_v12_nonneg)
      _ = 360 * universalDualLip_v12 * ell ^ 2 / L := by ring
  have h4_err : |-p_top * dualValue {j : ℤ | ((1 : ℕ) : ℤ) ≤ j} (T / (1 - p_top))| ≤
      36 * B_F0 * ell ^ 2 / L := by
    rw [abs_mul, abs_neg, abs_of_nonneg hp_nn]
    have hp_w2 : p_top ≤ 36 * ell ^ 2 / L := by
      calc p_top ≤ 36 * (ell / L) := hp_le_36
        _ ≤ 36 * ell ^ 2 / L := by
            rw [mul_div_assoc', div_le_div_iff_of_pos_right hL_pos]
            have hpow := pow_le_pow_right₀ (by linarith only [hw2] : 1 ≤ ell) (by omega : 1 ≤ 2)
            rw [pow_one] at hpow; linarith only [hpow]
    calc p_top * |dualValue {j : ℤ | ((1 : ℕ) : ℤ) ≤ j} (T / (1 - p_top))|
        ≤ (36 * ell ^ 2 / L) * B_F0 := mul_le_mul hp_w2 hd_abs (abs_nonneg _) (by positivity)
      _ = 36 * B_F0 * ell ^ 2 / L := by ring
  have hdecomp :
      (1 - p_top) * infiniteFiniteEntropy (phaseNat n) 1 (T / (1 - p_top)) -
        infiniteFiniteEntropy (phaseNat n) 1 T =
      (1 - p_top) * (infiniteFiniteEntropy (phaseNat n) 1 (T / (1 - p_top)) -
          dualValue {j : ℤ | ((1 : ℕ) : ℤ) ≤ j} (T / (1 - p_top))) +
        (dualValue {j : ℤ | ((1 : ℕ) : ℤ) ≤ j} T -
          infiniteFiniteEntropy (phaseNat n) 1 T) +
        (dualValue {j : ℤ | ((1 : ℕ) : ℤ) ≤ j} (T / (1 - p_top)) -
          dualValue {j : ℤ | ((1 : ℕ) : ℤ) ≤ j} T) +
        (-p_top * dualValue {j : ℤ | ((1 : ℕ) : ℤ) ≤ j} (T / (1 - p_top))) := by ring
  have t1 : (1 - p_top) * (infiniteFiniteEntropy (phaseNat n) 1 (T / (1 - p_top)) -
      dualValue {j : ℤ | ((1 : ℕ) : ℤ) ≤ j} (T / (1 - p_top))) ≤ C_dual * ell ^ 2 / L :=
    (le_abs_self _).trans h1_err
  have t2 : dualValue {j : ℤ | ((1 : ℕ) : ℤ) ≤ j} T -
      infiniteFiniteEntropy (phaseNat n) 1 T ≤ C_dual * ell ^ 2 / L :=
    (le_abs_self _).trans (by rwa [abs_sub_comm])
  have t3 : dualValue {j : ℤ | ((1 : ℕ) : ℤ) ≤ j} (T / (1 - p_top)) -
      dualValue {j : ℤ | ((1 : ℕ) : ℤ) ≤ j} T ≤ 360 * universalDualLip_v12 * ell ^ 2 / L :=
    (le_abs_self _).trans h3_err
  have t4 : -p_top * dualValue {j : ℤ | ((1 : ℕ) : ℤ) ≤ j} (T / (1 - p_top)) ≤
      36 * B_F0 * ell ^ 2 / L :=
    (le_abs_self _).trans h4_err
  have hsum4 :
      (1 - p_top) * infiniteFiniteEntropy (phaseNat n) 1 (T / (1 - p_top)) -
        infiniteFiniteEntropy (phaseNat n) 1 T ≤
      (2 * C_dual + 360 * universalDualLip_v12 + 36 * B_F0) * (ell ^ 2 / L) := by
    rw [hdecomp]
    exact (add_le_add (add_le_add (add_le_add t1 t2) t3) t4).trans_eq (by ring)
  have hbin_ell : binEntropy p_top ≤ 73 * ell ^ 2 / L := hbin_le
  calc binEntropy p_top +
          (1 - p_top) * infiniteFiniteEntropy (phaseNat n) 1 (T / (1 - p_top)) -
          infiniteFiniteEntropy (phaseNat n) 1 T
      = binEntropy p_top +
          ((1 - p_top) * infiniteFiniteEntropy (phaseNat n) 1 (T / (1 - p_top)) -
            infiniteFiniteEntropy (phaseNat n) 1 T) := add_sub_assoc _ _ _
    _ ≤ 73 * ell ^ 2 / L +
          (2 * C_dual + 360 * universalDualLip_v12 + 36 * B_F0) * (ell ^ 2 / L) :=
        add_le_add hbin_ell hsum4
    _ ≤ 73 * ell ^ 2 / L +
          (2 * C_dual + 360 * universalDualLip_v12 + 36 * B_F0) * (ell ^ 2 / L) +
          ell ^ 2 / L := le_add_of_nonneg_right (by positivity)
    _ = C_err * ell ^ 2 / L := by rw [hC_err_def]; ring

private theorem prop41_ii_starAll_v12
    {n m_cap d_all shift_all : ℕ}
    (ha10 : 10 ≤ phaseNat n)
    {C_corr C_wide C_dual B_F0 C_err : ℝ}
    (hCw_def : C_wide = C_corr + 2)
    (hC_dual_pos : 0 < C_dual)
    (hC_err_pos : 0 < C_err)
    (hBF0_def : B_F0 = |Real.log (partitionFn Splus 0)| +
      |min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))| + 1)
    (hC_err_def : C_err = 73 + 2 * C_dual + 360 * universalDualLip_v12 + 36 * B_F0 + 1)
    (hn_pos : 0 < (n : ℝ))
    (hL20 : 20 ≤ logOrder n)
    (hw2 : 2 ≤ logLogOrder n)
    (hw_Cerr : 10 * C_err + 10 ≤ logLogOrder n)
    (hwL_1000 : logLogOrder n ≤ (1 / 1000) * logOrder n)
    (hL5n : 200 * (logOrder n) ^ 5 ≤ (n : ℝ))
    (hphase1 : logOrder n ≤ (phaseNat n : ℝ))
    (hgap_nn : 0 ≤ phaseRootGapRadius n)
    (hshift_add2_le_gap : (shift_all : ℝ) + 2 ≤ 2 * logLogOrder n * phaseRootGapRadius n)
    (hd_all_le : 4 * (d_all : ℝ) ≤ (1 / 20 : ℝ) * ((n : ℝ) / logOrder n))
    (hshift_L : (shift_all : ℝ) ≤ (1 / 100 : ℝ) * ((n : ℝ) / logOrder n))
    (hsh_all_ge : (n : ℝ) * (logLogOrder n) ^ 3 / (logOrder n) ^ 4 ≤ (shift_all : ℝ))
    (hslope_7_5 : (7 / 5 : ℝ) * (logOrder n) ^ 2 ≤ q / 4 * (phaseNat n : ℝ) ^ 2)
    (hm_cap_le : (m_cap : ℝ) ≤ 9 * (n : ℝ) * logLogOrder n / (logOrder n) ^ 2)
    (hr_bounds : ∀ r ∈ Set.Icc
        (phaseRootCenter n - C_corr * logLogOrder n * phaseRootGapRadius n)
        (phaseRootCenter n + C_corr * logLogOrder n * phaseRootGapRadius n),
      (29 / 100 : ℝ) * ((n : ℝ) / logOrder n) ≤ r ∧ r ≤ 2 * ((n : ℝ) / logOrder n))
    (hInfDual_1 : ∀ {T' : ℝ}, T' ∈ Set.Icc (9 / 4 : ℝ) (9 / 2) →
      |infiniteFiniteEntropy (phaseNat n) 1 T' - dualValue {j : ℤ | ((1 : ℕ) : ℤ) ≤ j} T'| ≤
        C_dual / (phaseNat n : ℝ))
    (hTargetWide : ∀ s ∈ Set.Icc
        (phaseRootCenter n - C_wide * logLogOrder n * phaseRootGapRadius n)
        (phaseRootCenter n + C_wide * logLogOrder n * phaseRootGapRadius n),
      fourSizeTarget n (phaseNat n) s ∈ Set.Icc (9 / 4 : ℝ) (17 / 4))
    (hbox : Real.log (((n + 1) ^ (phaseNat n) : ℕ) : ℝ) + factorialLogErrorBound n + 2 ≤
      6 * (logOrder n) ^ 2)
    {tau r : ℝ}
    (hr : r ∈ Set.Icc (phaseRootCenter n - C_corr * logLogOrder n * phaseRootGapRadius n)
                      (phaseRootCenter n + C_corr * logLogOrder n * phaseRootGapRadius n))
    (hzr : infinitePhaseObjective 1 n tau r = 0)
    (hDrop_tau : ∀ s₁ ∈ Set.Icc (phaseRootCenter n - C_wide * logLogOrder n * phaseRootGapRadius n)
                                (phaseRootCenter n + C_wide * logLogOrder n * phaseRootGapRadius n),
      ∀ s₂ ∈ Set.Icc (phaseRootCenter n - C_wide * logLogOrder n * phaseRootGapRadius n)
                     (phaseRootCenter n + C_wide * logLogOrder n * phaseRootGapRadius n),
        s₁ ≤ s₂ →
          infinitePhaseObjective 1 n tau s₁ ≤
            infinitePhaseObjective 1 n tau s₂ + 1 - (q / 4 * (phaseNat n : ℝ) ^ 2) * (s₂ - s₁)) :
    let k_star : ℕ := Nat.floor r - shift_all
    shift_all + 4 * d_all + 1 ≤ Nat.floor r ∧
      (Nat.floor r : ℤ) = ⌊r⌋ ∧
      k_star < n ∧
      ∀ kp ∈ boundedColoringProfiles n (phaseNat n) k_star,
        kp ⟨phaseNat n - 1, by omega⟩ < m_cap →
        profileStirlingUpperMain n kp + tau * (k_star : ℝ) +
            Real.log (((n + 1) ^ (phaseNat n) : ℕ) : ℝ) + factorialLogErrorBound n ≤
          -(n : ℝ) * (logLogOrder n) ^ 3 / (logOrder n) ^ 2 := by
  intro k_star
  set L : ℝ := logOrder n
  set ell : ℝ := logLogOrder n
  have hL_pos : 0 < L := by linarith only [hL20]
  have hw_pos : 0 < ell := by linarith only [hw2]
  obtain ⟨hr_lo, hr_hi⟩ := hr_bounds r hr
  have hr_nn : 0 ≤ r := le_trans (by positivity) hr_lo
  have hfl_gt : r - 1 < (Nat.floor r : ℝ) := by linarith only [Nat.lt_floor_add_one r]
  have hfl_le : (Nat.floor r : ℝ) ≤ r := Nat.floor_le hr_nn
  have h1_L : (1 : ℝ) ≤ (1 / 100 : ℝ) * ((n : ℝ) / L) := by
    rw [mul_div_assoc', le_div_iff₀ hL_pos]
    have hL15 : L ≤ L ^ 5 := by
      simpa only [pow_one] using pow_le_pow_right₀ (by linarith only [hL20] : 1 ≤ L) (by omega : 1 ≤ 5)
    linarith only [hL15, hL5n, hL_pos]
  have hsub_ok_real : ((shift_all + 4 * d_all + 1 : ℕ) : ℝ) ≤ (Nat.floor r : ℝ) := by
    push_cast; linarith only [hfl_gt, hr_lo, hshift_L, hd_all_le, h1_L, div_pos hn_pos hL_pos]
  have hsub_ok : shift_all + 4 * d_all + 1 ≤ Nat.floor r := Nat.cast_le.mp hsub_ok_real
  have hfl_int : (Nat.floor r : ℤ) = ⌊r⌋ :=
    (Int.floor_eq_iff.mpr ⟨by exact_mod_cast hfl_le,
      by exact_mod_cast Nat.lt_floor_add_one r⟩).symm
  have hk_lt_n : k_star < n := by
    have hk_le_fl : (k_star : ℝ) ≤ (Nat.floor r : ℝ) := Nat.cast_le.mpr (Nat.sub_le _ _)
    have hr_lt_n : r < (n : ℝ) := by
      have h2L : 2 * ((n : ℝ) / L) ≤ (1 / 10 : ℝ) * (n : ℝ) := by
        rw [mul_div_assoc', div_le_iff₀ hL_pos]
        have hm := mul_le_mul_of_nonneg_left hL20 hn_pos.le
        linarith only [hm]
      linarith only [hr_hi, h2L, hn_pos]
    exact Nat.cast_lt.mp (lt_of_le_of_lt (hk_le_fl.trans hfl_le) hr_lt_n)
  refine ⟨hsub_ok, hfl_int, hk_lt_n, ?_⟩
  have hk_cast : (k_star : ℝ) = (Nat.floor r : ℝ) - (shift_all : ℝ) :=
    Nat.cast_sub (by omega : shift_all ≤ Nat.floor r)
  have hsh_nn : (0 : ℝ) ≤ (shift_all : ℝ) := Nat.cast_nonneg shift_all
  have hk_lo : (1 / 4 : ℝ) * ((n : ℝ) / L) ≤ (k_star : ℝ) := by
    linarith only [hk_cast, hr_lo, hfl_gt, hshift_L, h1_L, div_pos hn_pos hL_pos]
  have hk_le_hi : (k_star : ℝ) ≤ 2 * ((n : ℝ) / L) := by
    linarith only [hk_cast, hfl_le, hr_hi, hsh_nn]
  have hk_pos : 0 < (k_star : ℝ) :=
    lt_of_lt_of_le (mul_pos (by norm_num) (div_pos hn_pos hL_pos)) hk_lo
  have hk_wide : (k_star : ℝ) ∈ Set.Icc
      (phaseRootCenter n - C_wide * ell * phaseRootGapRadius n)
      (phaseRootCenter n + C_wide * ell * phaseRootGapRadius n) := by
    have hcw : C_wide * ell * phaseRootGapRadius n =
        C_corr * ell * phaseRootGapRadius n + 2 * ell * phaseRootGapRadius n := by
      rw [hCw_def]; ring
    rw [hcw]
    exact ⟨by linarith only [hk_cast, hr.1, hfl_gt, hshift_add2_le_gap],
      by linarith only [hk_cast, hr.2, hfl_le, hsh_nn, hshift_add2_le_gap]⟩
  have hr_wide : r ∈ Set.Icc
      (phaseRootCenter n - C_wide * ell * phaseRootGapRadius n)
      (phaseRootCenter n + C_wide * ell * phaseRootGapRadius n) := by
    have hcw : C_corr * ell * phaseRootGapRadius n ≤ C_wide * ell * phaseRootGapRadius n := by
      rw [hCw_def]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith only) hw_pos.le) hgap_nn
    exact ⟨by linarith only [hr.1, hcw], by linarith only [hr.2, hcw]⟩
  have hdrop_k := hDrop_tau (k_star : ℝ) hk_wide r hr_wide
    (by linarith only [hk_cast, hfl_le, hsh_nn])
  rw [hzr, zero_add] at hdrop_k
  have hdrop_num : (7 / 5 : ℝ) * ((n : ℝ) * ell ^ 3 / L ^ 2) ≤
      (q / 4 * (phaseNat n : ℝ) ^ 2) * (r - (k_star : ℝ)) := by
    calc (7 / 5 : ℝ) * ((n : ℝ) * ell ^ 3 / L ^ 2)
        = ((7 / 5 : ℝ) * L ^ 2) * ((n : ℝ) * ell ^ 3 / L ^ 4) := by
          field_simp [hL_pos.ne']
      _ ≤ (q / 4 * (phaseNat n : ℝ) ^ 2) * (r - (k_star : ℝ)) :=
          mul_le_mul hslope_7_5 (by linarith only [hk_cast, hfl_le, hsh_all_ge])
            (by positivity) (le_trans (by positivity) hslope_7_5)
  set T : ℝ := fourSizeTarget n (phaseNat n) k_star
  have hTK : T ∈ Set.Icc (9 / 4 : ℝ) (17 / 4) := hTargetWide (k_star : ℝ) hk_wide
  intro kp hkp hkp_cap
  have hm_cap_lt_k : m_cap ≤ k_star := by
    suffices (m_cap : ℝ) ≤ (k_star : ℝ) from Nat.cast_le.mp this
    have h36 : 9 * (n : ℝ) * ell / L ^ 2 ≤ (1 / 4 : ℝ) * ((n : ℝ) / L) := by
      calc 9 * (n : ℝ) * ell / L ^ 2
          ≤ 9 * (n : ℝ) * ((1 / 1000) * L) / L ^ 2 :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hwL_1000 (by positivity)) (sq_nonneg L)
        _ = (9 / 1000 : ℝ) * ((n : ℝ) / L) := by field_simp [hL_pos.ne']
        _ ≤ (1 / 4 : ℝ) * ((n : ℝ) / L) :=
            mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    exact hm_cap_le.trans (h36.trans hk_lo)
  have htop_lt : kp ⟨phaseNat n - 1, by omega⟩ < k_star := lt_of_lt_of_le hkp_cap hm_cap_lt_k
  set p_top : ℝ := (kp ⟨phaseNat n - 1, by omega⟩ : ℝ) / (k_star : ℝ)
  have hp_nn : 0 ≤ p_top := div_nonneg (Nat.cast_nonneg _) hk_pos.le
  have hp_le_36 : p_top ≤ 36 * (ell / L) := by
    have h1 : (kp ⟨phaseNat n - 1, by omega⟩ : ℝ) ≤ (m_cap : ℝ) :=
      Nat.cast_le.mpr hkp_cap.le
    rw [div_le_iff₀ hk_pos]
    calc (kp ⟨phaseNat n - 1, by omega⟩ : ℝ)
        ≤ 9 * (n : ℝ) * ell / L ^ 2 := h1.trans hm_cap_le
      _ = 36 * (ell / L) * ((1 / 4 : ℝ) * ((n : ℝ) / L)) := by ring
      _ ≤ 36 * (ell / L) * (k_star : ℝ) :=
          mul_le_mul_of_nonneg_left hk_lo (by positivity)
  have hp_le_20 : p_top ≤ 1 / 20 := by
    calc p_top ≤ 36 * (ell / L) := hp_le_36
      _ ≤ 36 * (1 / 1000) :=
          mul_le_mul_of_nonneg_left ((div_le_iff₀ hL_pos).mpr hwL_1000) (by norm_num)
      _ ≤ 1 / 20 := by norm_num
  have h1mp_pos : 0 < 1 - p_top := sub_pos.mpr (lt_of_le_of_lt hp_le_20 (by norm_num))
  have hst_branch : ∀ l : ℝ,
      Real.log (infiniteFinitePartition (phaseNat n) 1 l) - l * (T / (1 - p_top)) ≥
        ((profileStirlingUpperMain n kp + tau * (k_star : ℝ) -
            ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + (k_star : ℝ) -
              (k_star : ℝ) * Real.log (k_star : ℝ)) -
            (k_star : ℝ) * (profileDeficitAffineA (phaseNat n) +
              profileDeficitAffineB (phaseNat n) * T + binEntropy p_top + tau)) /
          ((k_star : ℝ) * (1 - p_top))) := by
    intro l
    have h0 := profileStirlingUpperMain_topCap_le_v12 (m := 0) (Nat.zero_le 1) ha10
      (by omega : 1 ≤ k_star) tau (by simpa using hkp)
      (by simpa using htop_lt) l
    simp only [Nat.sub_zero, Nat.zero_add, Nat.cast_zero, mul_zero, zero_mul, sub_zero] at h0
    change profileStirlingUpperMain n kp + tau * (k_star : ℝ) ≤
      (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + (k_star : ℝ) -
        (k_star : ℝ) * Real.log (k_star : ℝ) +
        (k_star : ℝ) * (profileDeficitAffineA (phaseNat n) +
          profileDeficitAffineB (phaseNat n) * T + binEntropy p_top +
          (1 - p_top) * (Real.log (infiniteFinitePartition (phaseNat n) 1 l) -
            l * (T / (1 - p_top))) + tau) at h0
    rw [ge_iff_le, div_le_iff₀ (mul_pos hk_pos h1mp_pos)]
    linarith only [h0]
  have hinf_k := le_ciInf hst_branch
  change _ ≤ infiniteFiniteEntropy (phaseNat n) 1 (T / (1 - p_top)) at hinf_k
  rw [div_le_iff₀ (mul_pos hk_pos h1mp_pos)] at hinf_k
  have hst_cap : profileStirlingUpperMain n kp + tau * (k_star : ℝ) ≤
      infinitePhaseObjective 1 n tau (k_star : ℝ) +
        (k_star : ℝ) * (binEntropy p_top +
          (1 - p_top) * infiniteFiniteEntropy (phaseNat n) 1 (T / (1 - p_top)) -
          infiniteFiniteEntropy (phaseNat n) 1 T) := by
    unfold infinitePhaseObjective
    change profileStirlingUpperMain n kp + tau * (k_star : ℝ) ≤
      (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + (k_star : ℝ) -
        (k_star : ℝ) * Real.log (k_star : ℝ) +
        (k_star : ℝ) * (profileDeficitAffineA (phaseNat n) +
          profileDeficitAffineB (phaseNat n) * T +
          infiniteFiniteEntropy (phaseNat n) 1 T + tau) + _
    linarith only [hinf_k]
  have hdisc_le :
      binEntropy p_top +
        (1 - p_top) * infiniteFiniteEntropy (phaseNat n) 1 (T / (1 - p_top)) -
        infiniteFiniteEntropy (phaseNat n) 1 T ≤
      C_err * ell ^ 2 / L :=
    prop41_ii_discrepancy_le_v12 hC_dual_pos hBF0_def hC_err_def hphase1 hL_pos hw2
      hTK hp_nn hp_le_36 hp_le_20 hInfDual_1
  have hk_disc :
      (k_star : ℝ) * (binEntropy p_top +
        (1 - p_top) * infiniteFiniteEntropy (phaseNat n) 1 (T / (1 - p_top)) -
        infiniteFiniteEntropy (phaseNat n) 1 T) ≤
      2 * C_err * ((n : ℝ) * ell ^ 2 / L ^ 2) := by
    calc (k_star : ℝ) * (binEntropy p_top +
            (1 - p_top) * infiniteFiniteEntropy (phaseNat n) 1 (T / (1 - p_top)) -
            infiniteFiniteEntropy (phaseNat n) 1 T)
        ≤ (2 * ((n : ℝ) / L)) * (C_err * ell ^ 2 / L) := by
          by_cases hnn : 0 ≤ binEntropy p_top +
              (1 - p_top) * infiniteFiniteEntropy (phaseNat n) 1 (T / (1 - p_top)) -
              infiniteFiniteEntropy (phaseNat n) 1 T
          · exact mul_le_mul hk_le_hi hdisc_le hnn (by positivity)
          · exact le_trans (mul_nonpos_of_nonneg_of_nonpos hk_pos.le (le_of_not_ge hnn))
              (by positivity)
      _ = 2 * C_err * ((n : ℝ) * ell ^ 2 / L ^ 2) := by ring
  have h6L2_small : 6 * L ^ 2 + 1 ≤ (1 / 5 : ℝ) * ((n : ℝ) * ell ^ 3 / L ^ 2) := by
    have hnL2 : 200 * L ^ 3 ≤ (n : ℝ) / L ^ 2 := by
      rw [le_div_iff₀ (sq_pos_of_pos hL_pos)]
      linarith only [show 200 * L ^ 3 * L ^ 2 = 200 * L ^ 5 by ring, hL5n]
    have hw3_ge8 : (8 : ℝ) ≤ ell ^ 3 := by
      calc (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
        _ ≤ ell ^ 3 := pow_le_pow_left₀ (by norm_num) hw2 3
    have h1 : 320 * L ^ 3 ≤ (1 / 5 : ℝ) * ((n : ℝ) * ell ^ 3 / L ^ 2) := by
      calc 320 * L ^ 3 = (1 / 5 : ℝ) * ((200 * L ^ 3) * 8) := by ring
        _ ≤ (1 / 5 : ℝ) * (((n : ℝ) / L ^ 2) * ell ^ 3) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul hnL2 hw3_ge8 (by positivity) (by positivity)) (by norm_num)
        _ = (1 / 5 : ℝ) * ((n : ℝ) * ell ^ 3 / L ^ 2) := by ring
    have h20L2 : 20 * L ^ 2 ≤ L ^ 3 := by
      calc 20 * L ^ 2 ≤ L * L ^ 2 := mul_le_mul_of_nonneg_right hL20 (sq_nonneg L)
        _ = L ^ 3 := by ring
    have h1L2 : (1 : ℝ) ≤ L ^ 2 := by
      calc (1 : ℝ) ≤ (20 : ℝ) ^ 2 := by norm_num
        _ ≤ L ^ 2 := pow_le_pow_left₀ (by norm_num) hL20 2
    linarith only [h1, h20L2, h1L2]
  have herr_small : 2 * C_err * ((n : ℝ) * ell ^ 2 / L ^ 2) ≤
      (1 / 5 : ℝ) * ((n : ℝ) * ell ^ 3 / L ^ 2) := by
    have hc : 2 * C_err ≤ (1 / 5 : ℝ) * ell := by linarith only [hw_Cerr]
    calc 2 * C_err * ((n : ℝ) * ell ^ 2 / L ^ 2)
        ≤ ((1 / 5 : ℝ) * ell) * ((n : ℝ) * ell ^ 2 / L ^ 2) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = (1 / 5 : ℝ) * ((n : ℝ) * ell ^ 3 / L ^ 2) := by ring
  have hneg_goal : -(n : ℝ) * ell ^ 3 / L ^ 2 = -((n : ℝ) * ell ^ 3 / L ^ 2) := by ring
  linarith only [hst_cap, hk_disc, herr_small, hdrop_k, hdrop_num, hbox, h6L2_small, hneg_goal]

private theorem prop41_ii_tails_of_starAll_v12
    {n m_cap : ℕ} (hn2 : 2 ≤ n) (ha10 : 10 ≤ phaseNat n)
    (hL20 : 20 ≤ Real.log (n : ℝ))
    (hw2 : 2 ≤ Real.log (Real.log (n : ℝ)))
    (hL5n : 200 * (Real.log (n : ℝ)) ^ 5 ≤ (n : ℝ))
    (hpack_bound : (randomGraphMeasure n).real
      {G : LabeledGraph n | m_cap ≤ maxDisjointHomogeneousEq G (phaseNat n)} ≤
      Real.exp (-200 * (n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2 / (Real.log (n : ℝ)) ^ 2))
    {r₀ r_co : ℝ}
    (hsub0 : Nat.ceil ((n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 3 / (Real.log (n : ℝ)) ^ 4) +
      4 * Nat.ceil (mu n (phaseNat n + 1) + universalShift n) + 1 ≤ Nat.floor r₀)
    (hfl0 : (Nat.floor r₀ : ℤ) = ⌊r₀⌋)
    (hk0_lt : Nat.floor r₀ -
      Nat.ceil ((n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 3 / (Real.log (n : ℝ)) ^ 4) < n)
    (hkp0 : ∀ kp ∈ boundedColoringProfiles n (phaseNat n)
        (Nat.floor r₀ -
          Nat.ceil ((n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 3 / (Real.log (n : ℝ)) ^ 4)),
      kp ⟨phaseNat n - 1, by omega⟩ < m_cap →
      profileStirlingUpperMain n kp +
          (0 : ℝ) * ((Nat.floor r₀ -
            Nat.ceil ((n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 3 / (Real.log (n : ℝ)) ^ 4) : ℕ) : ℝ) +
          Real.log (((n + 1) ^ (phaseNat n) : ℕ) : ℝ) + factorialLogErrorBound n ≤
        -(n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 3 / (Real.log (n : ℝ)) ^ 2)
    (hsubCo : Nat.ceil ((n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 3 / (Real.log (n : ℝ)) ^ 4) +
      4 * Nat.ceil (mu n (phaseNat n + 1) + universalShift n) + 1 ≤ Nat.floor r_co)
    (hflCo : (Nat.floor r_co : ℤ) = ⌊r_co⌋)
    (hkCo_lt : Nat.floor r_co -
      Nat.ceil ((n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 3 / (Real.log (n : ℝ)) ^ 4) < n)
    (hkpCo : ∀ kp ∈ boundedColoringProfiles n (phaseNat n)
        (Nat.floor r_co -
          Nat.ceil ((n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 3 / (Real.log (n : ℝ)) ^ 4)),
      kp ⟨phaseNat n - 1, by omega⟩ < m_cap →
      profileStirlingUpperMain n kp +
          Real.log 2 * ((Nat.floor r_co -
            Nat.ceil ((n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 3 / (Real.log (n : ℝ)) ^ 4) : ℕ) : ℝ) +
          Real.log (((n + 1) ^ (phaseNat n) : ℕ) : ℝ) + factorialLogErrorBound n ≤
        -(n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 3 / (Real.log (n : ℝ)) ^ 2) :
    let L : ℝ := Real.log (n : ℝ)
    let ell : ℝ := Real.log (Real.log (n : ℝ))
    let t_n : ℝ := universalShift n
    let d_all : ℕ := Nat.ceil (mu n (phaseNat n + 1) + t_n)
    let shift_all : ℕ := Nat.ceil ((n : ℝ) * ell ^ 3 / L ^ 4)
    let k_chi_all : ℕ := Nat.floor r₀ - shift_all - 2 * d_all
    let k_zeta_all : ℕ := Nat.floor r_co - shift_all - 4 * d_all
    1 ≤ k_zeta_all ∧ k_zeta_all + 4 * d_all < n ∧ k_chi_all + 2 * d_all < n ∧
      (k_chi_all : ℤ) = ⌊r₀⌋ - (shift_all : ℤ) - 2 * (d_all : ℤ) ∧
      (k_zeta_all : ℤ) = ⌊r_co⌋ - (shift_all : ℤ) - 4 * (d_all : ℤ) ∧
      (randomGraphMeasure n).real {G : LabeledGraph n | chromaticNumberNat G ≤ k_chi_all} ≤
        2 * quasiExpTail n + Real.exp (-200 * (n : ℝ) * ell ^ 2 / L ^ 2) +
          Real.exp (-(n : ℝ) * ell ^ 3 / L ^ 2) ∧
      (randomGraphMeasure n).real {G : LabeledGraph n | cochromaticNumber G ≤ k_zeta_all} ≤
        2 * quasiExpTail n + Real.exp (-200 * (n : ℝ) * ell ^ 2 / L ^ 2) +
          Real.exp (-(n : ℝ) * ell ^ 3 / L ^ 2) ∧
      (randomGraphMeasure n).real {G : LabeledGraph n | chromaticNumberNat G ≤ k_chi_all} ≤
        3 * quasiExpTail n ∧
      (randomGraphMeasure n).real {G : LabeledGraph n | cochromaticNumber G ≤ k_zeta_all} ≤
        3 * quasiExpTail n := by
  intro L ell t_n d_all shift_all k_chi_all k_zeta_all
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hL_pos : 0 < L := by linarith only [hL20]
  have htn_pos : 0 < t_n := by dsimp [t_n]; unfold universalShift; positivity
  have hd_all_ge : mu n (phaseNat n + 1) + t_n ≤ (d_all : ℝ) := Nat.le_ceil _
  have hk_zeta_pos : 1 ≤ k_zeta_all := by dsimp [k_zeta_all, shift_all, d_all, t_n, ell, L]; omega
  have hk_zeta_sum : k_zeta_all + 4 * d_all = Nat.floor r_co - shift_all := by
    dsimp [k_zeta_all, shift_all, d_all, t_n, ell, L]; omega
  have hk_chi_sum : k_chi_all + 2 * d_all = Nat.floor r₀ - shift_all := by
    dsimp [k_chi_all, shift_all, d_all, t_n, ell, L]; omega
  have hk_chi_int : (k_chi_all : ℤ) = ⌊r₀⌋ - (shift_all : ℤ) - 2 * (d_all : ℤ) := by
    rw [← hfl0]; dsimp [k_chi_all, shift_all, d_all, t_n, ell, L]; omega
  have hk_zeta_int : (k_zeta_all : ℤ) = ⌊r_co⌋ - (shift_all : ℤ) - 4 * (d_all : ℤ) := by
    rw [← hflCo]; dsimp [k_zeta_all, shift_all, d_all, t_n, ell, L]; omega
  set B_box : ℝ := Real.log (((n + 1) ^ (phaseNat n) : ℕ) : ℝ)
  have hB_exp : (((n + 1) ^ (phaseNat n) : ℕ) : ℝ) = Real.exp B_box :=
    (Real.exp_log (by positivity)).symm
  have hfilt := randomGraph_filtered_coloring_and_cocoloring_le_v12
    (n := n) (alpha := phaseNat n) (m := 0) (k_chi := k_chi_all) (k_zeta := k_zeta_all)
    (d := d_all) (m_cap := m_cap) hn2 (by omega) (by omega) htn_pos.le
    (by simpa only [Nat.sub_zero] using hd_all_ge)
    (by rw [hk_chi_sum]; exact hk0_lt.le)
    (by rw [hk_zeta_sum]; exact hkCo_lt.le)
    (L_chi := -(n : ℝ) * ell ^ 3 / L ^ 2 - B_box)
    (L_zeta := -(n : ℝ) * ell ^ 3 / L ^ 2 - B_box)
    (fun kp hkp hcap ↦ by
      have hkp' : kp ∈ boundedColoringProfiles n (phaseNat n) (Nat.floor r₀ - shift_all) := by
        simpa only [Nat.sub_zero, ← hk_chi_sum] using hkp
      have h := hkp0 kp hkp' hcap
      simp only [zero_mul, add_zero] at h
      change profileStirlingUpperMain n kp + B_box + factorialLogErrorBound n ≤
        -(n : ℝ) * ell ^ 3 / L ^ 2 at h
      linarith only [h])
    (fun kp hkp hcap ↦ by
      have hkp' : kp ∈ boundedColoringProfiles n (phaseNat n) (Nat.floor r_co - shift_all) := by
        simpa only [Nat.sub_zero, ← hk_zeta_sum] using hkp
      have h := hkpCo kp hkp' hcap
      have hks : ((k_zeta_all + 4 * d_all : ℕ) : ℝ) = ((Nat.floor r_co - shift_all : ℕ) : ℝ) := by
        rw [hk_zeta_sum]
      rw [hks]
      change profileStirlingUpperMain n kp + Real.log 2 * ((Nat.floor r_co - shift_all : ℕ) : ℝ) +
          B_box + factorialLogErrorBound n ≤
        -(n : ℝ) * ell ^ 3 / L ^ 2 at h
      linarith only [h])
  have hboth_half :
      Real.exp (-200 * (n : ℝ) * ell ^ 2 / L ^ 2) + Real.exp (-(n : ℝ) * ell ^ 3 / L ^ 2) ≤
        quasiExpTail n := by
    have hbase : 2 * (n : ℝ) / L ^ 10 + Real.log 2 ≤ (n : ℝ) * ell ^ 2 / L ^ 2 := by
      have h1 : 2 * (n : ℝ) / L ^ 10 ≤ (n : ℝ) / L ^ 2 := by
        rw [div_le_div_iff₀ (pow_pos hL_pos 10) (sq_pos_of_pos hL_pos)]
        have h2L8 : (2 : ℝ) ≤ L ^ 8 := by
          calc (2 : ℝ) ≤ (20 : ℝ) ^ 8 := by norm_num
            _ ≤ L ^ 8 := pow_le_pow_left₀ (by norm_num) hL20 8
        have hm := mul_le_mul_of_nonneg_left h2L8 (mul_nonneg hn_pos.le (sq_nonneg L))
        linarith only [hm, show (n : ℝ) * L ^ 2 * 2 = 2 * (n : ℝ) * L ^ 2 by ring,
          show (n : ℝ) * L ^ 2 * L ^ 8 = (n : ℝ) * L ^ 10 by ring]
      have h2 : Real.log 2 ≤ (n : ℝ) / L ^ 2 := by
        rw [le_div_iff₀ (sq_pos_of_pos hL_pos)]
        have hL25 : L ^ 2 ≤ L ^ 5 := pow_le_pow_right₀ (by linarith only [hL20] : 1 ≤ L) (by omega)
        have hm := mul_le_mul_of_nonneg_right Real.log_two_lt_d9.le (sq_nonneg L)
        change 200 * L ^ 5 ≤ (n : ℝ) at hL5n
        linarith only [hL25, hm, hL5n, sq_pos_of_pos hL_pos]
      have h3 : 4 * ((n : ℝ) / L ^ 2) ≤ (n : ℝ) * ell ^ 2 / L ^ 2 := by
        have hw4 : (4 : ℝ) ≤ ell ^ 2 := by
          have := pow_le_pow_left₀ (by norm_num) hw2 2; norm_num at this; exact this
        calc 4 * ((n : ℝ) / L ^ 2) = (n : ℝ) * 4 / L ^ 2 := by ring
          _ ≤ (n : ℝ) * ell ^ 2 / L ^ 2 :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hw4 hn_pos.le) (sq_nonneg L)
      linarith only [h1, h2, h3, div_pos hn_pos (sq_pos_of_pos hL_pos)]
    have he1 : Real.exp (-200 * (n : ℝ) * ell ^ 2 / L ^ 2) ≤ (1 / 2) * quasiExpTail n := by
      have hle : -200 * (n : ℝ) * ell ^ 2 / L ^ 2 ≤ -(2 * (n : ℝ) / L ^ 10) - Real.log 2 := by
        have hnn : 0 ≤ (n : ℝ) * ell ^ 2 / L ^ 2 := by positivity
        linarith only [hbase, hnn,
          show -200 * (n : ℝ) * ell ^ 2 / L ^ 2 = -200 * ((n : ℝ) * ell ^ 2 / L ^ 2) by ring]
      calc Real.exp (-200 * (n : ℝ) * ell ^ 2 / L ^ 2)
          ≤ Real.exp (-(2 * (n : ℝ) / L ^ 10) - Real.log 2) := Real.exp_le_exp.mpr hle
        _ = (1 / 2) * quasiExpTail n := by
            unfold quasiExpTail
            have hrew : -(2 * (n : ℝ) / L ^ 10) - Real.log 2 =
                -Real.log 2 + (-2 * (n : ℝ) / (Real.log (n : ℝ)) ^ 10) := by dsimp [L]; ring
            rw [hrew, Real.exp_add, Real.exp_neg, Real.exp_log two_pos]
            ring
    have he2 : Real.exp (-(n : ℝ) * ell ^ 3 / L ^ 2) ≤ (1 / 2) * quasiExpTail n := by
      have hle : -(n : ℝ) * ell ^ 3 / L ^ 2 ≤ -(2 * (n : ℝ) / L ^ 10) - Real.log 2 := by
        have hw_ge : (n : ℝ) * ell ^ 2 / L ^ 2 ≤ (n : ℝ) * ell ^ 3 / L ^ 2 := by
          apply div_le_div_of_nonneg_right _ (sq_nonneg L)
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ (by linarith only [hw2] : 1 ≤ ell) (by omega)) hn_pos.le
        linarith only [hbase, hw_ge,
          show -(n : ℝ) * ell ^ 3 / L ^ 2 = -((n : ℝ) * ell ^ 3 / L ^ 2) by ring]
      calc Real.exp (-(n : ℝ) * ell ^ 3 / L ^ 2)
          ≤ Real.exp (-(2 * (n : ℝ) / L ^ 10) - Real.log 2) := Real.exp_le_exp.mpr hle
        _ = (1 / 2) * quasiExpTail n := by
            unfold quasiExpTail
            have hrew : -(2 * (n : ℝ) / L ^ 10) - Real.log 2 =
                -Real.log 2 + (-2 * (n : ℝ) / (Real.log (n : ℝ)) ^ 10) := by dsimp [L]; ring
            rw [hrew, Real.exp_add, Real.exp_neg, Real.exp_log two_pos]
            ring
    linarith only [he1, he2]
  simp only [Nat.sub_zero, hB_exp, ← Real.exp_add,
    show B_box + (-(n : ℝ) * ell ^ 3 / L ^ 2 - B_box) = -(n : ℝ) * ell ^ 3 / L ^ 2 by ring] at hfilt
  have hmcd := exp_mcdiarmid_universalShift_le_quasiExpTail hn2
  have hq_nn : 0 ≤ quasiExpTail n := by unfold quasiExpTail; positivity
  have hchi_prob :
      (randomGraphMeasure n).real {G : LabeledGraph n | chromaticNumberNat G ≤ k_chi_all} ≤
        2 * quasiExpTail n + Real.exp (-200 * (n : ℝ) * ell ^ 2 / L ^ 2) +
          Real.exp (-(n : ℝ) * ell ^ 3 / L ^ 2) := by
    linarith only [hfilt.1, hmcd, hpack_bound, hq_nn]
  have hzeta_prob :
      (randomGraphMeasure n).real {G : LabeledGraph n | cochromaticNumber G ≤ k_zeta_all} ≤
        2 * quasiExpTail n + Real.exp (-200 * (n : ℝ) * ell ^ 2 / L ^ 2) +
          Real.exp (-(n : ℝ) * ell ^ 3 / L ^ 2) := by
    linarith only [hfilt.2, hmcd, hpack_bound]
  refine ⟨hk_zeta_pos, ?_, ?_, hk_chi_int, hk_zeta_int, hchi_prob, hzeta_prob,
    by linarith only [hchi_prob, hboth_half], by linarith only [hzeta_prob, hboth_half]⟩
  · rw [hk_zeta_sum]; exact hkCo_lt
  · rw [hk_chi_sum]; exact hk0_lt

/-- **Proposition 4.1(ii) (`prop:lower-tails`, `main.tex` lines 657–659) unconditional all-`δ_n` lower tails:**
there exists `C_corr > 0` such that eventually for all `n` (uniformly across all `δ_n ∈ [0, 1)`):
1. `𝓛_{S_{≥ 1}}(n, ·)` and `𝓛_{S_{≥ 1}}(n, ·) + (log 2) ·` have unique zeros `r₀, r_co` in
   `(c_n - C_corr Δ_n, c_n + C_corr Δ_n)`,
2. at `k_{χ, all}^- := ⌊r₀⌋₊ - ⌈n ℓ³ / L⁴⌉₊ - 2 d_{n, 0}` and
   `k_{ζ, all}^- := ⌊r_co⌋₊ - ⌈n ℓ³ / L⁴⌉₊ - 4 d_{n, 0}` (`L = log n`, `ℓ = log log n`,
   `d_{n, 0} = ⌈μ_{α + 1} + t_n⌉₊`), both `P(χ(G_n) ≤ k_{χ, all}^-)` and `P(ζ(G_n) ≤ k_{ζ, all}^-)`
   are bounded by `2 * quasiExpTail n + exp(-200 n ℓ² / L²) + exp(-n ℓ³ / L²)` AND by
   `3 * quasiExpTail n`. -/
theorem eventually_randomGraph_lowerTails_prop41_ii :
    ∃ C_corr : ℝ, 0 < C_corr ∧
      ∀ᶠ n : ℕ in atTop,
        let F_fin1 : ℝ → ℝ := fun T ↦ ⨅ l : ℝ,
          (Real.log (∑ i ∈ Finset.Ico 1 (phaseNat n),
              Real.exp (l * (i : ℝ) +
                (Real.log ((phaseNat n).descFactorial i : ℝ) -
                  (i : ℝ) * Real.log (phaseNat n : ℝ) -
                  Real.log 2 / 2 * (i : ℝ) ^ 2))) - l * T)
        let obj1 : ℝ → ℝ → ℝ := fun tau s ↦
          (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + s - s * Real.log s +
            s * (profileDeficitAffineA (phaseNat n) +
              profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s +
              F_fin1 (fourSizeTarget n (phaseNat n) s) + tau)
        (∃! r₀ : ℝ,
          r₀ ∈ Set.Ioo (phaseRootCenter n - C_corr * logLogOrder n * phaseRootGapRadius n)
                       (phaseRootCenter n + C_corr * logLogOrder n * phaseRootGapRadius n) ∧
            obj1 0 r₀ = 0) ∧
        (∃! r_co : ℝ,
          r_co ∈ Set.Ioo (phaseRootCenter n - C_corr * logLogOrder n * phaseRootGapRadius n)
                         (phaseRootCenter n + C_corr * logLogOrder n * phaseRootGapRadius n) ∧
            obj1 (Real.log 2) r_co = 0) ∧
        ∀ r₀ ∈ Set.Icc (phaseRootCenter n - C_corr * logLogOrder n * phaseRootGapRadius n)
                       (phaseRootCenter n + C_corr * logLogOrder n * phaseRootGapRadius n),
          obj1 0 r₀ = 0 →
          ∀ r_co ∈ Set.Icc (phaseRootCenter n - C_corr * logLogOrder n * phaseRootGapRadius n)
                           (phaseRootCenter n + C_corr * logLogOrder n * phaseRootGapRadius n),
            obj1 (Real.log 2) r_co = 0 →
            let L : ℝ := Real.log (n : ℝ)
            let ell : ℝ := Real.log (Real.log (n : ℝ))
            let t_n : ℝ := universalShift n
            let d_all : ℕ := Nat.ceil (mu n (phaseNat n + 1) + t_n)
            let shift_all : ℕ := Nat.ceil ((n : ℝ) * ell ^ 3 / L ^ 4)
            let k_chi_all : ℕ := Nat.floor r₀ - shift_all - 2 * d_all
            let k_zeta_all : ℕ := Nat.floor r_co - shift_all - 4 * d_all
            1 ≤ k_zeta_all ∧ k_zeta_all + 4 * d_all < n ∧ k_chi_all + 2 * d_all < n ∧
              (k_chi_all : ℤ) = ⌊r₀⌋ - (shift_all : ℤ) - 2 * (d_all : ℤ) ∧
              (k_zeta_all : ℤ) = ⌊r_co⌋ - (shift_all : ℤ) - 4 * (d_all : ℤ) ∧
              (randomGraphMeasure n).real {G : LabeledGraph n | chromaticNumberNat G ≤ k_chi_all} ≤
                2 * quasiExpTail n + Real.exp (-200 * (n : ℝ) * ell ^ 2 / L ^ 2) +
                  Real.exp (-(n : ℝ) * ell ^ 3 / L ^ 2) ∧
              (randomGraphMeasure n).real {G : LabeledGraph n | cochromaticNumber G ≤ k_zeta_all} ≤
                2 * quasiExpTail n + Real.exp (-200 * (n : ℝ) * ell ^ 2 / L ^ 2) +
                  Real.exp (-(n : ℝ) * ell ^ 3 / L ^ 2) ∧
              (randomGraphMeasure n).real {G : LabeledGraph n | chromaticNumberNat G ≤ k_chi_all} ≤
                3 * quasiExpTail n ∧
              (randomGraphMeasure n).real {G : LabeledGraph n | cochromaticNumber G ≤ k_zeta_all} ≤
                3 * quasiExpTail n := by
  obtain ⟨C_corr, _, hC_pos, _, hRootEv⟩ :=
    exists_pos_eventually_existsUnique_infinitePhaseObjective_zero_logLogCorridor
  obtain ⟨C_dual, Alpha₀, hC_dual_pos, _, hInfDual⟩ := abs_infiniteFiniteEntropy_sub_dualValue_le
  refine ⟨C_corr, hC_pos, ?_⟩
  set C_wide : ℝ := C_corr + 2
  have hC_wide_nn : 0 ≤ C_wide := by dsimp [C_wide]; positivity
  set B_F0 : ℝ := |Real.log (partitionFn Splus 0)| +
    |min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))| + 1
  have hBF0_def : B_F0 = |Real.log (partitionFn Splus 0)| +
      |min (dualValue S4 (17 / 8)) (dualValue S4 (37 / 8))| + 1 := rfl
  set C_err : ℝ := 73 + 2 * C_dual + 360 * universalDualLip_v12 + 36 * B_F0 + 1
  have hC_err_def : C_err = 73 + 2 * C_dual + 360 * universalDualLip_v12 + 36 * B_F0 + 1 := rfl
  have hC_err_pos : 0 < C_err := by
    have := universalDualLip_v12_nonneg; dsimp [C_err, B_F0]; positivity
  clear_value B_F0 C_err
  have ho_L5 : (fun x : ℝ ↦ (Real.log x) ^ ((5 : ℕ) : ℝ)) =o[atTop] (fun x : ℝ ↦ x ^ (1 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop ((5 : ℕ) : ℝ) zero_lt_one
  have hL5_small : ∀ᶠ n : ℕ in atTop, 200 * (Real.log (n : ℝ)) ^ 5 ≤ (n : ℝ) := by
    have hb := (ho_L5.comp_tendsto tendsto_natCast_atTop_atTop).bound (by norm_num : (0 : ℝ) < 1 / 200)
    filter_upwards [hb, eventually_gt_atTop 2] with n hn _
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hL_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    dsimp only [Function.comp_apply] at hn
    rw [Real.rpow_natCast, Real.norm_eq_abs, abs_of_pos (pow_pos hL_pos 5),
      Real.rpow_one, Real.norm_eq_abs, abs_of_pos hn_pos] at hn
    linarith
  have ho_w3 : (fun x : ℝ ↦ (Real.log x) ^ ((3 : ℕ) : ℝ)) =o[atTop] (fun x : ℝ ↦ x ^ (1 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop ((3 : ℕ) : ℝ) zero_lt_one
  have hw3_small : ∀ᶠ n : ℕ in atTop, (logLogOrder n) ^ 3 ≤ (1 / 100) * logOrder n := by
    have hb := (ho_w3.comp_tendsto tendsto_logOrder_atTop).bound (by norm_num : (0 : ℝ) < 1 / 100)
    filter_upwards [hb, tendsto_logLogOrder_atTop.eventually_ge_atTop 2,
      tendsto_logOrder_atTop.eventually_ge_atTop 4] with n hn hw2 hL4
    have hw_pos : 0 < logLogOrder n := by linarith
    have hL_pos : 0 < logOrder n := by linarith
    dsimp only [Function.comp_apply] at hn
    change ‖(logLogOrder n) ^ ((3 : ℕ) : ℝ)‖ ≤ (1 / 100) * ‖(logOrder n) ^ (1 : ℝ)‖ at hn
    rw [Real.rpow_natCast, Real.norm_eq_abs, abs_of_pos (pow_pos hw_pos 3),
      Real.rpow_one, Real.norm_eq_abs, abs_of_pos hL_pos] at hn
    exact hn
  set eps_w : ℝ := min (1 / 1000) (1 / (100 * (C_corr + 1)))
  have hwL_small : ∀ᶠ n : ℕ in atTop, ‖logLogOrder n‖ ≤ eps_w * ‖logOrder n‖ :=
    logLogOrder_isLittleO_logOrder.bound (lt_min (by norm_num) (by positivity))
  have hphase_A0 : ∀ᶠ n : ℕ in atTop, max Alpha₀ 10 ≤ phaseNat n := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop ((max Alpha₀ 10 : ℕ) : ℝ),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact_mod_cast hn.trans hph.1
  filter_upwards [hRootEv,
    eventually_infinitePhaseObjective_strictMonoOn_and_drop C_wide hC_wide_nn,
    eventually_phaseRootLogLogCorridor_fourSize_target_mem_Icc C_wide hC_wide_nn,
    eventually_mu_phaseNat_succ_and_deltaStar_le_v12,
    eventually_phaseRootCenter_sub_main_logLogRate_v12,
    eventually_corridor_inv_target_logLogRate_v12 C_corr hC_pos.le,
    eventually_two_85_logOrder_le_phaseNat,
    eventually_box_mul_error_le_five_log_sq,
    eventually_randomGraph_homogeneousPacking_alpha_tail,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
    hL5_small, hw3_small, hwL_small, hphase_A0,
    tendsto_logLogOrder_atTop.eventually_ge_atTop (max 2 (10 * C_err + 10)),
    tendsto_logOrder_atTop.eventually_ge_atTop 20] with
    n hRoots hDrop hTargetWide hMuBds hcMain hInv hph285 hBoxErr hPackAlpha hphase
    hL5n hw3L hwL hphA0 hw_big hL20
  intro F_fin1 obj1
  have hobj1_eq : obj1 = infinitePhaseObjective 1 n := rfl
  rw [hobj1_eq]
  clear hobj1_eq obj1 F_fin1
  clear hRootEv
  have htau0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.log 2) := ⟨le_rfl, (Real.log_pos one_lt_two).le⟩
  have htauL : Real.log 2 ∈ Set.Icc (0 : ℝ) (Real.log 2) := ⟨(Real.log_pos one_lt_two).le, le_rfl⟩
  have hex0 := (hRoots 1 (by omega) 0 htau0).2.1
  have hexCo := (hRoots 1 (by omega) (Real.log 2) htauL).2.1
  clear hRoots
  refine ⟨hex0, hexCo, ?_⟩
  clear hex0 hexCo
  intro r₀ hr₀ hz₀ r_co hr_co hz_co L ell t_n d_all shift_all k_chi_all k_zeta_all
  change ell ^ 3 ≤ (1 / 100) * L at hw3L
  change 200 * L ^ 5 ≤ (n : ℝ) at hL5n
  have hL_eq : L = logOrder n := rfl
  have hell_eq : ell = logLogOrder n := rfl
  have hw2 : 2 ≤ ell := (le_max_left _ _).trans hw_big
  have hw_Cerr : 10 * C_err + 10 ≤ ell := (le_max_right _ _).trans hw_big
  have hL_pos : 0 < L := by linarith [hL20]
  have hw_pos : 0 < ell := by linarith
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have : Real.log (n : ℝ) ≤ 0 := by
      rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl <;> simp
    linarith [hL20]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have ha_A0 : Alpha₀ ≤ phaseNat n := (le_max_left _ _).trans hphA0
  have ha10 : 10 ≤ phaseNat n := (le_max_right _ _).trans hphA0
  rw [Real.norm_eq_abs, abs_of_pos (show 0 < logLogOrder n from hw_pos),
    Real.norm_eq_abs, abs_of_pos (show 0 < logOrder n from hL_pos)] at hwL
  change ell ≤ eps_w * L at hwL
  have hwL_1000 : ell ≤ (1 / 1000) * L :=
    hwL.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hL_pos.le)
  have hwL_corr : C_corr * ell ≤ (1 / 100) * L := by
    have h1 := hwL.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hL_pos.le)
    have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ C_corr + 1 by positivity)
    have h3 : (C_corr + 1) * (1 / (100 * (C_corr + 1)) * L) = (1 / 100) * L := by
      field_simp [(show (0 : ℝ) < C_corr + 1 by positivity).ne']
    linarith [mul_pos hC_pos hw_pos]
  clear ho_L5 hL5_small ho_w3 hw3_small hwL_small hphase_A0 hw_big hphA0 hwL
  clear_value eps_w
  have htn_pos : 0 < t_n := by dsimp [t_n]; unfold universalShift; positivity
  have hc_lo : (3 / 10 : ℝ) * ((n : ℝ) / L) ≤ phaseRootCenter n := by
    have h1 : -(4 * (n : ℝ) * ell / L ^ 2) ≤
        phaseRootCenter n - (Real.log 2 / 2) * ((n : ℝ) / L) := (abs_le.mp hcMain.2).1
    have h2 : 4 * (n : ℝ) * ell / L ^ 2 ≤ (1 / 50 : ℝ) * ((n : ℝ) / L) := by
      calc 4 * (n : ℝ) * ell / L ^ 2
          ≤ 4 * (n : ℝ) * ((1 / 200) * L) / L ^ 2 :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left (by linarith [hwL_1000]) (by positivity)) (sq_nonneg L)
        _ = (1 / 50 : ℝ) * ((n : ℝ) / L) := by field_simp [hL_pos.ne']; ring
    have hq_num : (16 / 50 : ℝ) * ((n : ℝ) / L) ≤ (Real.log 2 / 2) * ((n : ℝ) / L) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.log_two_gt_d9]) (div_nonneg hn_pos.le hL_pos.le)
    linarith [div_pos hn_pos hL_pos]
  have hgap_lo : (1 / 60 : ℝ) * ((n : ℝ) / L ^ 3) ≤ phaseRootGapRadius n := by
    unfold phaseRootGapRadius
    have ha_sq : (phaseNat n : ℝ) ^ 2 ≤ 16 * L ^ 2 := by
      calc (phaseNat n : ℝ) ^ 2 ≤ (4 * L) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hphase.2 2
        _ = 16 * L ^ 2 := by ring
    calc (1 / 60 : ℝ) * ((n : ℝ) / L ^ 3)
        ≤ (3 / 160 : ℝ) * ((n : ℝ) / L ^ 3) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = ((3 / 10 : ℝ) * ((n : ℝ) / L)) / (16 * L ^ 2) := by field_simp [hL_pos.ne']; ring
      _ ≤ phaseRootCenter n / (16 * L ^ 2) := div_le_div_of_nonneg_right hc_lo (by positivity)
      _ ≤ phaseRootCenter n / (phaseNat n : ℝ) ^ 2 :=
          div_le_div_of_nonneg_left (by linarith [div_pos hn_pos hL_pos])
            (sq_pos_of_pos (lt_of_lt_of_le hL_pos hphase.1)) ha_sq
  have hgap_nn : 0 ≤ phaseRootGapRadius n := le_trans (by positivity) hgap_lo
  have hgap_hi : phaseRootGapRadius n ≤ (n : ℝ) / L ^ 3 := by
    unfold phaseRootGapRadius
    have ha_sq : L ^ 2 ≤ (phaseNat n : ℝ) ^ 2 := pow_le_pow_left₀ hL_pos.le hphase.1 2
    calc phaseRootCenter n / (phaseNat n : ℝ) ^ 2
        ≤ ((n : ℝ) / L) / L ^ 2 :=
          div_le_div₀ (div_nonneg hn_pos.le hL_pos.le) hcMain.1 (sq_pos_of_pos hL_pos) ha_sq
      _ = (n : ℝ) / L ^ 3 := by ring
  have hw2_le_L : ell ^ 2 ≤ (1 / 100) * L := by
    have : ell ^ 2 ≤ ell ^ 3 := pow_le_pow_right₀ (by linarith : 1 ≤ ell) (by omega)
    linarith [hw3L]
  have hshift_add2_le_gap : (shift_all : ℝ) + 2 ≤ 2 * ell * phaseRootGapRadius n := by
    have hs_lt : (shift_all : ℝ) < (n : ℝ) * ell ^ 3 / L ^ 4 + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hmain_sh : (n : ℝ) * ell ^ 3 / L ^ 4 ≤ (1 / 100 : ℝ) * ((n : ℝ) * ell / L ^ 3) := by
      calc (n : ℝ) * ell ^ 3 / L ^ 4
          = (ell ^ 2 / L) * ((n : ℝ) * ell / L ^ 3) := by field_simp [hL_pos.ne']
        _ ≤ (1 / 100 : ℝ) * ((n : ℝ) * ell / L ^ 3) :=
            mul_le_mul_of_nonneg_right ((div_le_iff₀ hL_pos).mpr hw2_le_L) (by positivity)
    have h3_le : (3 : ℝ) ≤ (1 / 50 : ℝ) * ((n : ℝ) * ell / L ^ 3) := by
      have h3' : (3 : ℝ) ≤ (1 / 50 : ℝ) * ((n : ℝ) / L ^ 3) := by
        rw [mul_div_assoc', le_div_iff₀ (pow_pos hL_pos 3)]
        have hL35 : L ^ 3 ≤ L ^ 5 := pow_le_pow_right₀ (by linarith : 1 ≤ L) (by omega)
        change 200 * L ^ 5 ≤ (n : ℝ) at hL5n
        linarith [hL5n, pow_pos hL_pos 3]
      exact h3'.trans (by
        have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ ell by linarith)
          (show (0 : ℝ) ≤ (1 / 50 : ℝ) * ((n : ℝ) / L ^ 3) by positivity)
        linarith [show (1 / 50 : ℝ) * ((n : ℝ) / L ^ 3) * ell =
            (1 / 50 : ℝ) * ((n : ℝ) * ell / L ^ 3) by ring])
    have hw_gap : (1 / 30 : ℝ) * ((n : ℝ) * ell / L ^ 3) ≤ 2 * ell * phaseRootGapRadius n := by
      calc (1 / 30 : ℝ) * ((n : ℝ) * ell / L ^ 3)
          = 2 * ell * ((1 / 60 : ℝ) * ((n : ℝ) / L ^ 3)) := by ring
        _ ≤ 2 * ell * phaseRootGapRadius n :=
            mul_le_mul_of_nonneg_left hgap_lo (by positivity)
    linarith [ (show 0 < (n : ℝ) * ell / L ^ 3 by positivity) ]
  have hd_all_le : 4 * (d_all : ℝ) ≤ (1 / 20 : ℝ) * ((n : ℝ) / L) := by
    have hc := Nat.ceil_lt_add_one (add_nonneg (mu_nonneg n (phaseNat n + 1)) htn_pos.le)
    have hmu_le : mu n (phaseNat n + 1) ≤ t_n := hMuBds.1
    have htn_L : t_n ≤ (1 / 400 : ℝ) * ((n : ℝ) / L) := by
      dsimp [t_n]; unfold universalShift
      have hL4 : (400 : ℝ) ≤ L ^ 4 := by
        calc (400 : ℝ) ≤ (20 : ℝ) ^ 4 := by norm_num
          _ ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hL20 4
      calc (n : ℝ) / (Real.log (n : ℝ)) ^ 5 = (n : ℝ) / (L ^ 4 * L) := by dsimp [L]; ring
        _ ≤ (n : ℝ) / (400 * L) := div_le_div_of_nonneg_left hn_pos.le (by positivity)
            (mul_le_mul_of_nonneg_right hL4 hL_pos.le)
        _ = (1 / 400 : ℝ) * ((n : ℝ) / L) := by ring
    have h4_L : (4 : ℝ) ≤ (1 / 100 : ℝ) * ((n : ℝ) / L) := by
      rw [mul_div_assoc', le_div_iff₀ hL_pos]
      have h2L5 : 2 * L ≤ L ^ 5 := by
        have h2L4 : (2 : ℝ) ≤ L ^ 4 := by
          calc (2 : ℝ) ≤ (20 : ℝ) ^ 4 := by norm_num
            _ ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hL20 4
        calc 2 * L ≤ L ^ 4 * L := mul_le_mul_of_nonneg_right h2L4 hL_pos.le
          _ = L ^ 5 := by ring
      linarith [hL5n]
    change 4 * (Nat.ceil (mu n (phaseNat n + 1) + t_n) : ℝ) ≤ (1 / 20 : ℝ) * ((n : ℝ) / L)
    linarith only [hc, hmu_le, htn_L, h4_L, div_pos hn_pos hL_pos]
  have hshift_L : (shift_all : ℝ) ≤ (1 / 100 : ℝ) * ((n : ℝ) / L) := by
    have hs_lt : (shift_all : ℝ) < (n : ℝ) * ell ^ 3 / L ^ 4 + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h1 : (n : ℝ) * ell ^ 3 / L ^ 4 ≤ (1 / 200 : ℝ) * ((n : ℝ) / L) := by
      calc (n : ℝ) * ell ^ 3 / L ^ 4 = (ell ^ 3 / L ^ 3) * ((n : ℝ) / L) := by ring
        _ ≤ (1 / 200 : ℝ) * ((n : ℝ) / L) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            rw [div_le_iff₀ (pow_pos hL_pos 3)]
            have hL13 : (2 : ℝ) * L ≤ L ^ 3 := by
              have h400 : (400 : ℝ) ≤ L ^ 2 := by
                have := pow_le_pow_left₀ (by norm_num) hL20 2; norm_num at this; exact this
              have h20 := mul_le_mul_of_nonneg_right h400 hL_pos.le
              linarith [show L ^ 2 * L = L ^ 3 by ring]
            linarith [hw3L, hL_pos]
    have h2 : (1 : ℝ) ≤ (1 / 200 : ℝ) * ((n : ℝ) / L) := by
      rw [mul_div_assoc', le_div_iff₀ hL_pos]
      have hL15 : L ^ 1 ≤ L ^ 5 := pow_le_pow_right₀ (by linarith : 1 ≤ L) (by omega)
      rw [pow_one] at hL15
      linarith [hL5n, hL_pos]
    linarith
  have hr_bounds : ∀ r ∈ Set.Icc
      (phaseRootCenter n - C_corr * ell * phaseRootGapRadius n)
      (phaseRootCenter n + C_corr * ell * phaseRootGapRadius n),
      (29 / 100 : ℝ) * ((n : ℝ) / L) ≤ r ∧ r ≤ 2 * ((n : ℝ) / L) := by
    intro r hr
    have hdelta_le : C_corr * ell * phaseRootGapRadius n ≤ (1 / 100 : ℝ) * ((n : ℝ) / L) := by
      have hgap_L : phaseRootGapRadius n ≤ (n : ℝ) / L ^ 2 := by
        calc phaseRootGapRadius n ≤ (n : ℝ) / L ^ 3 := hgap_hi
          _ = ((n : ℝ) / L ^ 2) / L := by ring
          _ ≤ ((n : ℝ) / L ^ 2) / 1 :=
              div_le_div_of_nonneg_left (by positivity) zero_lt_one (by linarith [hL20])
          _ = (n : ℝ) / L ^ 2 := div_one _
      calc C_corr * ell * phaseRootGapRadius n
          ≤ ((1 / 100) * L) * ((n : ℝ) / L ^ 2) :=
            mul_le_mul hwL_corr hgap_L hgap_nn (by positivity)
        _ = (1 / 100 : ℝ) * ((n : ℝ) / L) := by field_simp [hL_pos.ne']
    exact ⟨by linarith [hr.1, hc_lo],
      (hInv.2 r hr).2.1.trans (mul_le_mul_of_nonneg_left hcMain.1 zero_le_two)⟩
  have hslope_7_5 : (7 / 5 : ℝ) * L ^ 2 ≤ q / 4 * (phaseNat n : ℝ) ^ 2 := by
    have hsq := pow_le_pow_left₀ (by positivity) hph285 2
    have hnum : (7 / 5 : ℝ) ≤ q / 4 * (285 / 100 : ℝ) ^ 2 := by
      unfold q; linarith [Real.log_two_gt_d9]
    calc (7 / 5 : ℝ) * L ^ 2 ≤ (q / 4 * (285 / 100 : ℝ) ^ 2) * L ^ 2 :=
          mul_le_mul_of_nonneg_right hnum (sq_nonneg L)
      _ = q / 4 * ((285 / 100 : ℝ) * L) ^ 2 := by ring
      _ ≤ q / 4 * (phaseNat n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (div_nonneg q_pos.le (by norm_num))
  set m_cap : ℕ := Nat.ceil (8 * (n : ℝ) * ell / L ^ 2)
  have hpack_fn : Unit →
      (randomGraphMeasure n).real
        {G : LabeledGraph n | m_cap ≤ maxDisjointHomogeneousEq G (phaseNat n)} ≤
      Real.exp (-200 * (n : ℝ) * ell ^ 2 / L ^ 2) := fun _ ↦ by
    simpa [m_cap, L, ell, logOrder, logLogOrder] using hPackAlpha
  clear hPackAlpha
  have hm_cap_le : (m_cap : ℝ) ≤ 9 * (n : ℝ) * ell / L ^ 2 := by
    have hc := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 8 * (n : ℝ) * ell / L ^ 2 by positivity)
    have h1 : (1 : ℝ) ≤ (n : ℝ) * ell / L ^ 2 := by
      rw [le_div_iff₀ (sq_pos_of_pos hL_pos), one_mul]
      have hL25 : L ^ 2 ≤ L ^ 5 := pow_le_pow_right₀ (by linarith : 1 ≤ L) (by omega)
      have hn_ge : L ^ 2 ≤ (n : ℝ) := by linarith [hL5n, sq_pos_of_pos hL_pos]
      calc L ^ 2 = L ^ 2 * 1 := (mul_one _).symm
        _ ≤ (n : ℝ) * ell := mul_le_mul hn_ge (by linarith [hw2]) zero_le_one hn_pos.le
    linarith [show 8 * (n : ℝ) * ell / L ^ 2 + (n : ℝ) * ell / L ^ 2 =
        9 * (n : ℝ) * ell / L ^ 2 by ring]
  have hsh_all_ge : (n : ℝ) * ell ^ 3 / L ^ 4 ≤ (shift_all : ℝ) := Nat.le_ceil _
  have hInfDual_1 : ∀ {T' : ℝ}, T' ∈ Set.Icc (9 / 4 : ℝ) (9 / 2) →
      |infiniteFiniteEntropy (phaseNat n) 1 T' - dualValue {j : ℤ | ((1 : ℕ) : ℤ) ≤ j} T'| ≤
        C_dual / (phaseNat n : ℝ) :=
    fun hT' ↦ (hInfDual ha_A0 (by omega : 1 ≤ 2) hT').2.2.2
  have hbox_n : Real.log (((n + 1) ^ (phaseNat n) : ℕ) : ℝ) + factorialLogErrorBound n + 2 ≤
      6 * (logOrder n) ^ 2 := hBoxErr (phaseNat n) le_rfl
  obtain ⟨hsub0, hfl0, hk0_lt, hkp0⟩ := prop41_ii_starAll_v12 (m_cap := m_cap)
    (d_all := d_all) (shift_all := shift_all) ha10 rfl hC_dual_pos hC_err_pos hBF0_def hC_err_def
    hn_pos hL20 hw2 hw_Cerr hwL_1000 hL5n hphase.1 hgap_nn hshift_add2_le_gap hd_all_le hshift_L
    hsh_all_ge hslope_7_5 hm_cap_le hr_bounds hInfDual_1 hTargetWide hbox_n hr₀ hz₀
    (hDrop 1 (by omega) 0 htau0).2
  obtain ⟨hsubCo, hflCo, hkCo_lt, hkpCo⟩ := prop41_ii_starAll_v12 (m_cap := m_cap)
    (d_all := d_all) (shift_all := shift_all) ha10 rfl hC_dual_pos hC_err_pos hBF0_def hC_err_def
    hn_pos hL20 hw2 hw_Cerr hwL_1000 hL5n hphase.1 hgap_nn hshift_add2_le_gap hd_all_le hshift_L
    hsh_all_ge hslope_7_5 hm_cap_le hr_bounds hInfDual_1 hTargetWide hbox_n hr_co hz_co
    (hDrop 1 (by omega) (Real.log 2) htauL).2
  exact prop41_ii_tails_of_starAll_v12 hn2 ha10 hL20 hw2 hL5n (hpack_fn ())
    hsub0 hfl0 hk0_lt hkp0 hsubCo hflCo hkCo_lt hkpCo

private theorem prop41_iii_cap_diff_le_v12
    {n : ℕ}
    {thetaBar p_1 T C_dual C_wide C_err : ℝ}
    (htheta_icc : thetaBar ∈ Set.Icc (0 : ℝ) (1 / 20))
    (hp1_icc : p_1 ∈ Set.Icc (0 : ℝ) (1 / 20))
    (hp1_lt_th : p_1 < thetaBar)
    (hp1_ge : thetaBar ≤ p1Inf (phaseDelta n))
    (hT_delta_cap : phaseTarget (phaseDelta n) ∈ KcapInterval)
    (hT_delta_gt2 : 2 < phaseTarget (phaseDelta n))
    (hTK_cap : T ∈ KcapInterval)
    (hT_dist : |T - phaseTarget (phaseDelta n)| ≤ 2 * C_wide * logLogOrder n / logOrder n)
    (hC_dual_pos : 0 < C_dual)
    (hC_err_def : C_err = 2 * C_dual + 4 * C_wide * universalDualLip_v12 + 1)
    (hphase1 : logOrder n ≤ (phaseNat n : ℝ))
    (hL_pos : 0 < logOrder n)
    (hw2 : 2 ≤ logLogOrder n)
    (hCapDual_n : ∀ {theta : ℝ}, theta ∈ Set.Icc (0 : ℝ) (1 / 20) →
      |cappedInfiniteFiniteEntropy (phaseNat n) theta T - cappedDualValue Sge1 theta T| ≤
        C_dual / (phaseNat n : ℝ)) :
    cappedInfiniteFiniteEntropy (phaseNat n) p_1 T -
      cappedInfiniteFiniteEntropy (phaseNat n) thetaBar T ≤
    C_err * logLogOrder n / logOrder n := by
  set L : ℝ := logOrder n
  set ell : ℝ := logLogOrder n
  have hw_pos : 0 < ell := by linarith only [hw2]
  have hp1_mono := (cappedDualValue_Sge1_concave_strictMono_and_eq_dualValue hT_delta_gt2).2.1
  have hd_p1 := hCapDual_n hp1_icc
  have hd_th := hCapDual_n htheta_icc
  have hlip_p1 := abs_cappedDualValue_Sge1_sub_le hp1_icc hTK_cap hT_delta_cap
  have hlip_th := abs_cappedDualValue_Sge1_sub_le htheta_icc hTK_cap hT_delta_cap
  have hmono_le :
      cappedDualValue Sge1 p_1 (phaseTarget (phaseDelta n)) ≤
        cappedDualValue Sge1 thetaBar (phaseTarget (phaseDelta n)) := by
    have hp1_eq : p1Inf (phaseDelta n) =
        gibbsProb Sge1 (sge1Tilt (phaseTarget (phaseDelta n))) 1 := rfl
    exact hp1_mono.monotoneOn ⟨hp1_icc.1, hp1_lt_th.le.trans (hp1_eq ▸ hp1_ge)⟩
      ⟨htheta_icc.1, hp1_eq ▸ hp1_ge⟩ hp1_lt_th.le
  have hcd_le : C_dual / (phaseNat n : ℝ) ≤ C_dual * ell / L := by
    calc C_dual / (phaseNat n : ℝ) ≤ C_dual / L :=
          div_le_div_of_nonneg_left hC_dual_pos.le hL_pos hphase1
      _ ≤ C_dual * ell / L := by
          apply div_le_div_of_nonneg_right _ hL_pos.le
          exact le_mul_of_one_le_right hC_dual_pos.le (by linarith only [hw2])
  have hl1 : |cappedDualValue Sge1 p_1 T -
      cappedDualValue Sge1 p_1 (phaseTarget (phaseDelta n))| ≤
      2 * C_wide * universalDualLip_v12 * ell / L := by
    calc |cappedDualValue Sge1 p_1 T -
            cappedDualValue Sge1 p_1 (phaseTarget (phaseDelta n))|
        ≤ universalDualLip_v12 * (2 * C_wide * ell / L) :=
          hlip_p1.trans (mul_le_mul_of_nonneg_left hT_dist universalDualLip_v12_nonneg)
      _ = 2 * C_wide * universalDualLip_v12 * ell / L := by ring
  have hl2 : |cappedDualValue Sge1 thetaBar T -
      cappedDualValue Sge1 thetaBar (phaseTarget (phaseDelta n))| ≤
      2 * C_wide * universalDualLip_v12 * ell / L := by
    calc |cappedDualValue Sge1 thetaBar T -
            cappedDualValue Sge1 thetaBar (phaseTarget (phaseDelta n))|
        ≤ universalDualLip_v12 * (2 * C_wide * ell / L) :=
          hlip_th.trans (mul_le_mul_of_nonneg_left hT_dist universalDualLip_v12_nonneg)
      _ = 2 * C_wide * universalDualLip_v12 * ell / L := by ring
  have hexp_C : C_err * ell / L =
      2 * (C_dual * ell / L) + 2 * (2 * C_wide * universalDualLip_v12 * ell / L) + ell / L := by
    rw [hC_err_def]; ring
  have e1 : |cappedInfiniteFiniteEntropy (phaseNat n) p_1 T - cappedDualValue Sge1 p_1 T| ≤
      C_dual * ell / L := hd_p1.trans hcd_le
  have e2 : |cappedInfiniteFiniteEntropy (phaseNat n) thetaBar T -
      cappedDualValue Sge1 thetaBar T| ≤ C_dual * ell / L := hd_th.trans hcd_le
  change cappedInfiniteFiniteEntropy (phaseNat n) p_1 T -
    cappedInfiniteFiniteEntropy (phaseNat n) thetaBar T ≤ C_err * ell / L
  rw [hexp_C]
  linarith only [(abs_le.mp e1).2, (abs_le.mp e2).1, (abs_le.mp hl1).2, (abs_le.mp hl2).1,
    hmono_le, div_pos hw_pos hL_pos]

private theorem prop41_iii_starTh_v12
    {n m_cap d_th shift_th : ℕ}
    (ha10 : 10 ≤ phaseNat n)
    {thetaBar C_corr C_wide C_dual C_err : ℝ}
    (htheta : thetaBar ∈ Set.Ioc (0 : ℝ) (1 / 20))
    (hp1_ge : thetaBar ≤ p1Inf (phaseDelta n))
    (hd : phaseDelta n ∈ Set.Icc (0 : ℝ) deltaStar)
    (hCw_def : C_wide = C_corr + 2)
    (hC_dual_pos : 0 < C_dual)
    (hC_err_pos : 0 < C_err)
    (hC_err_def : C_err = 2 * C_dual + 4 * C_wide * universalDualLip_v12 + 1)
    (hn_pos : 0 < (n : ℝ))
    (hL20 : 20 ≤ logOrder n)
    (hw2 : 2 ≤ logLogOrder n)
    (hw_Cerr : 10 * C_err + 10 ≤ logLogOrder n)
    (hL5n : 200 * (logOrder n) ^ 5 ≤ (n : ℝ))
    (hphase1 : logOrder n ≤ (phaseNat n : ℝ))
    (hgap_nn : 0 ≤ phaseRootGapRadius n)
    (hshift_add2_le_gap : (shift_th : ℝ) + 2 ≤ 2 * logLogOrder n * phaseRootGapRadius n)
    (hd_th_le : 4 * (d_th : ℝ) ≤ (1 / 20 : ℝ) * ((n : ℝ) / logOrder n))
    (hshift_L : (shift_th : ℝ) ≤ (1 / 100 : ℝ) * ((n : ℝ) / logOrder n))
    (hsh_th_ge : (n : ℝ) * (logLogOrder n) ^ 2 / (logOrder n) ^ 4 ≤ (shift_th : ℝ))
    (hslope_7_5 : (7 / 5 : ℝ) * (logOrder n) ^ 2 ≤ q / 4 * (phaseNat n : ℝ) ^ 2)
    (hm_cap_lt_imp : ∀ k : ℕ, k < m_cap →
      (k : ℝ) < thetaBar * (n : ℝ) / ((phaseNat n - 1 : ℕ) : ℝ))
    (hr_bounds : ∀ r ∈ Set.Icc
        (phaseRootCenter n - C_corr * logLogOrder n * phaseRootGapRadius n)
        (phaseRootCenter n + C_corr * logLogOrder n * phaseRootGapRadius n),
      (29 / 100 : ℝ) * ((n : ℝ) / logOrder n) ≤ r ∧ r ≤ 2 * ((n : ℝ) / logOrder n))
    (hKcapWide_n : ∀ s ∈ Set.Icc
        (phaseRootCenter n - C_wide * logLogOrder n * phaseRootGapRadius n)
        (phaseRootCenter n + C_wide * logLogOrder n * phaseRootGapRadius n),
      fourSizeTarget n (phaseNat n) s ∈ KcapInterval)
    (hInvWide_dist : ∀ s ∈ Set.Icc
        (phaseRootCenter n - C_wide * logLogOrder n * phaseRootGapRadius n)
        (phaseRootCenter n + C_wide * logLogOrder n * phaseRootGapRadius n),
      |fourSizeTarget n (phaseNat n) s - phaseTarget (phaseDelta n)| ≤
        2 * C_wide * logLogOrder n / logOrder n)
    (hCapDual_all : ∀ {theta T' : ℝ}, theta ∈ Set.Icc (0 : ℝ) (1 / 20) → T' ∈ KcapInterval →
      |cappedInfiniteFiniteEntropy (phaseNat n) theta T' - cappedDualValue Sge1 theta T'| ≤
        C_dual / (phaseNat n : ℝ))
    (hbox : Real.log (((n + 1) ^ (phaseNat n - 1) : ℕ) : ℝ) + factorialLogErrorBound n + 2 ≤
      6 * (logOrder n) ^ 2)
    {tau r : ℝ}
    (hr : r ∈ Set.Icc (phaseRootCenter n - C_corr * logLogOrder n * phaseRootGapRadius n)
                      (phaseRootCenter n + C_corr * logLogOrder n * phaseRootGapRadius n))
    (hzr : cappedInfinitePhaseObjective n thetaBar tau r = 0)
    (hDrop_tau : ∀ s₁ ∈ Set.Icc (phaseRootCenter n - C_wide * logLogOrder n * phaseRootGapRadius n)
                                (phaseRootCenter n + C_wide * logLogOrder n * phaseRootGapRadius n),
      ∀ s₂ ∈ Set.Icc (phaseRootCenter n - C_wide * logLogOrder n * phaseRootGapRadius n)
                     (phaseRootCenter n + C_wide * logLogOrder n * phaseRootGapRadius n),
        s₁ ≤ s₂ →
          cappedInfinitePhaseObjective n thetaBar tau s₁ ≤
            cappedInfinitePhaseObjective n thetaBar tau s₂ + 1 -
              (q / 4 * (phaseNat n : ℝ) ^ 2) * (s₂ - s₁)) :
    let k_star : ℕ := Nat.floor r - shift_th
    shift_th + 4 * d_th + 1 ≤ Nat.floor r ∧
      (Nat.floor r : ℤ) = ⌊r⌋ ∧
      k_star < n ∧
      ∀ kp ∈ boundedColoringProfiles n (phaseNat n - 1) k_star,
        kp ⟨phaseNat n - 1 - 1, by omega⟩ < m_cap →
        profileStirlingUpperMain n kp + tau * (k_star : ℝ) +
            Real.log (((n + 1) ^ (phaseNat n - 1) : ℕ) : ℝ) + factorialLogErrorBound n ≤
          -(n : ℝ) * (logLogOrder n) ^ 2 / (logOrder n) ^ 2 := by
  intro k_star
  set L : ℝ := logOrder n
  set ell : ℝ := logLogOrder n
  have htheta_pos : 0 < thetaBar := htheta.1
  have htheta_hi : thetaBar ≤ 1 / 20 := htheta.2
  have htheta_icc : thetaBar ∈ Set.Icc (0 : ℝ) (1 / 20) := ⟨htheta_pos.le, htheta_hi⟩
  have hL_pos : 0 < L := by linarith only [hL20]
  have hw_pos : 0 < ell := by linarith only [hw2]
  have hd_bds : 0 ≤ phaseDelta n ∧ phaseDelta n ≤ 1 / 10 := by
    unfold deltaStar at hd; exact ⟨hd.1, by linarith only [hd.2]⟩
  have hT_delta_cap : phaseTarget (phaseDelta n) ∈ KcapInterval := by
    unfold KcapInterval phaseTarget
    exact ⟨by linarith only [hd_bds.2], by linarith only [hd_bds.1]⟩
  have hT_delta_gt2 : 2 < phaseTarget (phaseDelta n) := by
    obtain ⟨h2lo, _⟩ := two_div_log_two_bounds
    unfold phaseTarget
    linarith only [hd_bds.2, h2lo]
  obtain ⟨hr_lo, hr_hi⟩ := hr_bounds r hr
  have hr_nn : 0 ≤ r := le_trans (by positivity) hr_lo
  have hfl_gt : r - 1 < (Nat.floor r : ℝ) := by linarith only [Nat.lt_floor_add_one r]
  have hfl_le : (Nat.floor r : ℝ) ≤ r := Nat.floor_le hr_nn
  have h1_L : (1 : ℝ) ≤ (1 / 100 : ℝ) * ((n : ℝ) / L) := by
    rw [mul_div_assoc', le_div_iff₀ hL_pos]
    have hL15 : L ≤ L ^ 5 := by
      simpa only [pow_one] using pow_le_pow_right₀ (by linarith only [hL20] : 1 ≤ L) (by omega : 1 ≤ 5)
    linarith only [hL15, hL5n, hL_pos]
  have hsub_ok_real : ((shift_th + 4 * d_th + 1 : ℕ) : ℝ) ≤ (Nat.floor r : ℝ) := by
    push_cast; linarith only [hfl_gt, hr_lo, hshift_L, hd_th_le, h1_L, div_pos hn_pos hL_pos]
  have hsub_ok : shift_th + 4 * d_th + 1 ≤ Nat.floor r := Nat.cast_le.mp hsub_ok_real
  have hfl_int : (Nat.floor r : ℤ) = ⌊r⌋ :=
    (Int.floor_eq_iff.mpr ⟨by exact_mod_cast hfl_le,
      by exact_mod_cast Nat.lt_floor_add_one r⟩).symm
  have hk_lt_n : k_star < n := by
    have hk_le_fl : (k_star : ℝ) ≤ (Nat.floor r : ℝ) := Nat.cast_le.mpr (Nat.sub_le _ _)
    have hr_lt_n : r < (n : ℝ) := by
      have h2L : 2 * ((n : ℝ) / L) ≤ (1 / 10 : ℝ) * (n : ℝ) := by
        rw [mul_div_assoc', div_le_iff₀ hL_pos]
        have hm := mul_le_mul_of_nonneg_left hL20 hn_pos.le
        linarith only [hm]
      linarith only [hr_hi, h2L, hn_pos]
    exact Nat.cast_lt.mp (lt_of_le_of_lt (hk_le_fl.trans hfl_le) hr_lt_n)
  refine ⟨hsub_ok, hfl_int, hk_lt_n, ?_⟩
  have hk_cast : (k_star : ℝ) = (Nat.floor r : ℝ) - (shift_th : ℝ) :=
    Nat.cast_sub (by omega : shift_th ≤ Nat.floor r)
  have hsh_nn : (0 : ℝ) ≤ (shift_th : ℝ) := Nat.cast_nonneg shift_th
  have hk_lo : (1 / 4 : ℝ) * ((n : ℝ) / L) ≤ (k_star : ℝ) := by
    linarith only [hk_cast, hr_lo, hfl_gt, hshift_L, h1_L, div_pos hn_pos hL_pos]
  have hk_le_hi : (k_star : ℝ) ≤ 2 * ((n : ℝ) / L) := by
    linarith only [hk_cast, hfl_le, hr_hi, hsh_nn]
  have hk_pos : 0 < (k_star : ℝ) :=
    lt_of_lt_of_le (mul_pos (by norm_num) (div_pos hn_pos hL_pos)) hk_lo
  have hk_wide : (k_star : ℝ) ∈ Set.Icc
      (phaseRootCenter n - C_wide * ell * phaseRootGapRadius n)
      (phaseRootCenter n + C_wide * ell * phaseRootGapRadius n) := by
    have hcw : C_wide * ell * phaseRootGapRadius n =
        C_corr * ell * phaseRootGapRadius n + 2 * ell * phaseRootGapRadius n := by
      rw [hCw_def]; ring
    rw [hcw]
    exact ⟨by linarith only [hk_cast, hr.1, hfl_gt, hshift_add2_le_gap],
      by linarith only [hk_cast, hr.2, hfl_le, hsh_nn, hshift_add2_le_gap]⟩
  have hr_wide : r ∈ Set.Icc
      (phaseRootCenter n - C_wide * ell * phaseRootGapRadius n)
      (phaseRootCenter n + C_wide * ell * phaseRootGapRadius n) := by
    have hcw : C_corr * ell * phaseRootGapRadius n ≤ C_wide * ell * phaseRootGapRadius n := by
      rw [hCw_def]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith only) hw_pos.le) hgap_nn
    exact ⟨by linarith only [hr.1, hcw], by linarith only [hr.2, hcw]⟩
  have hdrop_k := hDrop_tau (k_star : ℝ) hk_wide r hr_wide
    (by linarith only [hk_cast, hfl_le, hsh_nn])
  rw [hzr, zero_add] at hdrop_k
  have hdrop_num : (7 / 5 : ℝ) * ((n : ℝ) * ell ^ 2 / L ^ 2) ≤
      (q / 4 * (phaseNat n : ℝ) ^ 2) * (r - (k_star : ℝ)) := by
    calc (7 / 5 : ℝ) * ((n : ℝ) * ell ^ 2 / L ^ 2)
        = ((7 / 5 : ℝ) * L ^ 2) * ((n : ℝ) * ell ^ 2 / L ^ 4) := by
          field_simp [hL_pos.ne']
      _ ≤ (q / 4 * (phaseNat n : ℝ) ^ 2) * (r - (k_star : ℝ)) :=
          mul_le_mul hslope_7_5 (by linarith only [hk_cast, hfl_le, hsh_th_ge])
            (by positivity) (le_trans (by positivity) hslope_7_5)
  set T : ℝ := fourSizeTarget n (phaseNat n) k_star
  have hTK_cap : T ∈ KcapInterval := hKcapWide_n (k_star : ℝ) hk_wide
  have hT_gt2 : 2 < T := by
    obtain ⟨h2lo, _⟩ := two_div_log_two_bounds
    unfold KcapInterval at hTK_cap
    linarith only [hTK_cap.1, h2lo]
  have hT_dist : |T - phaseTarget (phaseDelta n)| ≤ 2 * C_wide * ell / L :=
    hInvWide_dist (k_star : ℝ) hk_wide
  intro kp hkp hkp_cap
  have hk_top_lt_real : (kp ⟨phaseNat n - 1 - 1, by omega⟩ : ℝ) <
      thetaBar * (n : ℝ) / ((phaseNat n - 1 : ℕ) : ℝ) :=
    hm_cap_lt_imp _ hkp_cap
  have hn_div_am1_lt_k : (n : ℝ) / ((phaseNat n - 1 : ℕ) : ℝ) < (k_star : ℝ) := by
    have ha_sub1 : ((phaseNat n - 1 : ℕ) : ℝ) = (phaseNat n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ phaseNat n), Nat.cast_one]
    have ha_sub1_pos : (0 : ℝ) < ((phaseNat n - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    rw [div_lt_iff₀ ha_sub1_pos, ha_sub1]
    have hT_eq : (phaseNat n : ℝ) * (k_star : ℝ) - (n : ℝ) = T * (k_star : ℝ) := by
      dsimp [T]; unfold fourSizeTarget; field_simp [hk_pos.ne']
    have h2k : 2 * (k_star : ℝ) < T * (k_star : ℝ) := mul_lt_mul_of_pos_right hT_gt2 hk_pos
    linarith only [hT_eq, h2k, hk_pos]
  have hk_top_lt_th : (kp ⟨phaseNat n - 1 - 1, by omega⟩ : ℝ) < thetaBar * (k_star : ℝ) := by
    calc (kp ⟨phaseNat n - 1 - 1, by omega⟩ : ℝ)
        < thetaBar * (n : ℝ) / ((phaseNat n - 1 : ℕ) : ℝ) := hk_top_lt_real
      _ = thetaBar * ((n : ℝ) / ((phaseNat n - 1 : ℕ) : ℝ)) := by ring
      _ < thetaBar * (k_star : ℝ) := mul_lt_mul_of_pos_left hn_div_am1_lt_k htheta_pos
  have htop_lt_k : kp ⟨phaseNat n - 1 - 1, by omega⟩ < k_star := by
    suffices (kp ⟨phaseNat n - 1 - 1, by omega⟩ : ℝ) < (k_star : ℝ) from Nat.cast_lt.mp this
    have hth_le1 : thetaBar ≤ 1 := htheta_hi.trans (by norm_num)
    exact lt_of_lt_of_le hk_top_lt_th ((mul_le_mul_of_nonneg_right hth_le1 hk_pos.le).trans_eq (one_mul _))
  set p_1 : ℝ := (kp ⟨phaseNat n - 1 - 1, by omega⟩ : ℝ) / (k_star : ℝ)
  have hp1_nn : 0 ≤ p_1 := div_nonneg (Nat.cast_nonneg _) hk_pos.le
  have hp1_lt_th : p_1 < thetaBar := (div_lt_iff₀ hk_pos).mpr hk_top_lt_th
  have hp1_icc : p_1 ∈ Set.Icc (0 : ℝ) (1 / 20) := ⟨hp1_nn, hp1_lt_th.le.trans htheta_hi⟩
  have h1mp1_pos : 0 < 1 - p_1 := sub_pos.mpr (lt_of_le_of_lt hp1_icc.2 (by norm_num))
  have hst_branch : ∀ l : ℝ,
      Real.log (infiniteFinitePartition (phaseNat n) 2 l) - l * ((T - p_1) / (1 - p_1)) ≥
        ((profileStirlingUpperMain n kp + tau * (k_star : ℝ) -
            ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + (k_star : ℝ) -
              (k_star : ℝ) * Real.log (k_star : ℝ)) -
            (k_star : ℝ) * (profileDeficitAffineA (phaseNat n) +
              profileDeficitAffineB (phaseNat n) * T +
              binEntropy p_1 - Real.log 2 / 2 * p_1 + tau)) /
          ((k_star : ℝ) * (1 - p_1))) := by
    intro l
    have h0 := profileStirlingUpperMain_topCap_le_v12 (m := 1) le_rfl ha10
      (by omega : 1 ≤ k_star) tau hkp htop_lt_k l
    simp only [Nat.cast_one, mul_one, one_mul] at h0
    change profileStirlingUpperMain n kp + tau * (k_star : ℝ) ≤
      (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + (k_star : ℝ) -
        (k_star : ℝ) * Real.log (k_star : ℝ) +
        (k_star : ℝ) * (profileDeficitAffineA (phaseNat n) +
          profileDeficitAffineB (phaseNat n) * T +
          binEntropy p_1 - Real.log 2 / 2 * p_1 +
          (1 - p_1) * (Real.log (infiniteFinitePartition (phaseNat n) 2 l) -
            l * ((T - p_1) / (1 - p_1))) + tau) at h0
    rw [ge_iff_le, div_le_iff₀ (mul_pos hk_pos h1mp1_pos)]
    linarith only [h0]
  have hinf_k := le_ciInf hst_branch
  change _ ≤ infiniteFiniteEntropy (phaseNat n) 2 ((T - p_1) / (1 - p_1)) at hinf_k
  rw [div_le_iff₀ (mul_pos hk_pos h1mp1_pos)] at hinf_k
  have hst_p1 : profileStirlingUpperMain n kp + tau * (k_star : ℝ) ≤
      cappedInfinitePhaseObjective n p_1 tau (k_star : ℝ) := by
    unfold cappedInfinitePhaseObjective cappedInfiniteFiniteEntropy
    change profileStirlingUpperMain n kp + tau * (k_star : ℝ) ≤
      (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + (k_star : ℝ) -
        (k_star : ℝ) * Real.log (k_star : ℝ) +
        (k_star : ℝ) * (profileDeficitAffineA (phaseNat n) +
          profileDeficitAffineB (phaseNat n) * T +
          (binEntropy p_1 - Real.log 2 / 2 * p_1 +
            (1 - p_1) * infiniteFiniteEntropy (phaseNat n) 2 ((T - p_1) / (1 - p_1))) + tau)
    linarith only [hinf_k]
  have hcap_diff :
      cappedInfiniteFiniteEntropy (phaseNat n) p_1 T -
        cappedInfiniteFiniteEntropy (phaseNat n) thetaBar T ≤
      C_err * ell / L :=
    prop41_iii_cap_diff_le_v12 htheta_icc hp1_icc hp1_lt_th hp1_ge hT_delta_cap hT_delta_gt2
      hTK_cap hT_dist hC_dual_pos hC_err_def hphase1 hL_pos hw2
      (fun hth' ↦ hCapDual_all hth' hTK_cap)
  have hobj_diff :
      cappedInfinitePhaseObjective n p_1 tau (k_star : ℝ) -
        cappedInfinitePhaseObjective n thetaBar tau (k_star : ℝ) ≤
      2 * C_err * ((n : ℝ) * ell / L ^ 2) := by
    have hid : cappedInfinitePhaseObjective n p_1 tau (k_star : ℝ) -
        cappedInfinitePhaseObjective n thetaBar tau (k_star : ℝ) =
      (k_star : ℝ) * (cappedInfiniteFiniteEntropy (phaseNat n) p_1 T -
        cappedInfiniteFiniteEntropy (phaseNat n) thetaBar T) := by
      unfold cappedInfinitePhaseObjective; dsimp [T]; ring
    rw [hid]
    by_cases hnn : 0 ≤ cappedInfiniteFiniteEntropy (phaseNat n) p_1 T -
        cappedInfiniteFiniteEntropy (phaseNat n) thetaBar T
    · calc (k_star : ℝ) * (cappedInfiniteFiniteEntropy (phaseNat n) p_1 T -
              cappedInfiniteFiniteEntropy (phaseNat n) thetaBar T)
          ≤ (2 * ((n : ℝ) / L)) * (C_err * ell / L) :=
            mul_le_mul hk_le_hi hcap_diff hnn (by positivity)
        _ = 2 * C_err * ((n : ℝ) * ell / L ^ 2) := by ring
    · exact le_trans (mul_nonpos_of_nonneg_of_nonpos hk_pos.le (le_of_not_ge hnn))
        (by positivity)
  have h6L2_small : 6 * L ^ 2 + 1 ≤ (1 / 5 : ℝ) * ((n : ℝ) * ell ^ 2 / L ^ 2) := by
    have hnL2 : 200 * L ^ 3 ≤ (n : ℝ) / L ^ 2 := by
      rw [le_div_iff₀ (sq_pos_of_pos hL_pos)]
      linarith only [show 200 * L ^ 3 * L ^ 2 = 200 * L ^ 5 by ring, hL5n]
    have hw2_ge4 : (4 : ℝ) ≤ ell ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num) hw2 2; norm_num at this; exact this
    have h1 : 160 * L ^ 3 ≤ (1 / 5 : ℝ) * ((n : ℝ) * ell ^ 2 / L ^ 2) := by
      calc 160 * L ^ 3 = (1 / 5 : ℝ) * ((200 * L ^ 3) * 4) := by ring
        _ ≤ (1 / 5 : ℝ) * (((n : ℝ) / L ^ 2) * ell ^ 2) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul hnL2 hw2_ge4 (by positivity) (by positivity)) (by norm_num)
        _ = (1 / 5 : ℝ) * ((n : ℝ) * ell ^ 2 / L ^ 2) := by ring
    have h20L2 : 20 * L ^ 2 ≤ L ^ 3 := by
      calc 20 * L ^ 2 ≤ L * L ^ 2 := mul_le_mul_of_nonneg_right hL20 (sq_nonneg L)
        _ = L ^ 3 := by ring
    have h1L2 : (1 : ℝ) ≤ L ^ 2 := by
      calc (1 : ℝ) ≤ (20 : ℝ) ^ 2 := by norm_num
        _ ≤ L ^ 2 := pow_le_pow_left₀ (by norm_num) hL20 2
    linarith only [h1, h20L2, h1L2]
  have herr_small : 2 * C_err * ((n : ℝ) * ell / L ^ 2) ≤
      (1 / 5 : ℝ) * ((n : ℝ) * ell ^ 2 / L ^ 2) := by
    have hc : 2 * C_err ≤ (1 / 5 : ℝ) * ell := by linarith only [hw_Cerr]
    calc 2 * C_err * ((n : ℝ) * ell / L ^ 2)
        ≤ ((1 / 5 : ℝ) * ell) * ((n : ℝ) * ell / L ^ 2) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = (1 / 5 : ℝ) * ((n : ℝ) * ell ^ 2 / L ^ 2) := by ring
  have hneg_goal : -(n : ℝ) * ell ^ 2 / L ^ 2 = -((n : ℝ) * ell ^ 2 / L ^ 2) := by ring
  linarith only [hst_p1, hobj_diff, herr_small, hdrop_k, hdrop_num, hbox, h6L2_small, hneg_goal]

private theorem prop41_iii_tails_of_starTh_v12
    {n m_cap : ℕ} (hn2 : 2 ≤ n) (ha10 : 10 ≤ phaseNat n)
    {thetaBar gamma : ℝ} (htheta_pos : 0 < thetaBar) (hgamma : 0 < gamma)
    (hL20 : 20 ≤ Real.log (n : ℝ))
    (hL_th : 3 / (thetaBar * gamma) ≤ Real.log (n : ℝ))
    (hw2 : 2 ≤ Real.log (Real.log (n : ℝ)))
    (hL5n : 200 * (Real.log (n : ℝ)) ^ 5 ≤ (n : ℝ))
    (hpack_bound : (randomGraphMeasure n).real
      {G : LabeledGraph n | m_cap ≤ maxDisjointHomogeneousEq G (phaseNat n - 1)} ≤
      Real.exp (-thetaBar * gamma * (n : ℝ)))
    {r₀ r_co : ℝ}
    (hsub0 : Nat.ceil ((n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2 / (Real.log (n : ℝ)) ^ 4) +
      4 * Nat.ceil (mu n (phaseNat n) + universalShift n) + 1 ≤ Nat.floor r₀)
    (hfl0 : (Nat.floor r₀ : ℤ) = ⌊r₀⌋)
    (hk0_lt : Nat.floor r₀ -
      Nat.ceil ((n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2 / (Real.log (n : ℝ)) ^ 4) < n)
    (hkp0 : ∀ kp ∈ boundedColoringProfiles n (phaseNat n - 1)
        (Nat.floor r₀ -
          Nat.ceil ((n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2 / (Real.log (n : ℝ)) ^ 4)),
      kp ⟨phaseNat n - 1 - 1, by omega⟩ < m_cap →
      profileStirlingUpperMain n kp +
          (0 : ℝ) * ((Nat.floor r₀ -
            Nat.ceil ((n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2 / (Real.log (n : ℝ)) ^ 4) : ℕ) : ℝ) +
          Real.log (((n + 1) ^ (phaseNat n - 1) : ℕ) : ℝ) + factorialLogErrorBound n ≤
        -(n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2 / (Real.log (n : ℝ)) ^ 2)
    (hsubCo : Nat.ceil ((n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2 / (Real.log (n : ℝ)) ^ 4) +
      4 * Nat.ceil (mu n (phaseNat n) + universalShift n) + 1 ≤ Nat.floor r_co)
    (hflCo : (Nat.floor r_co : ℤ) = ⌊r_co⌋)
    (hkCo_lt : Nat.floor r_co -
      Nat.ceil ((n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2 / (Real.log (n : ℝ)) ^ 4) < n)
    (hkpCo : ∀ kp ∈ boundedColoringProfiles n (phaseNat n - 1)
        (Nat.floor r_co -
          Nat.ceil ((n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2 / (Real.log (n : ℝ)) ^ 4)),
      kp ⟨phaseNat n - 1 - 1, by omega⟩ < m_cap →
      profileStirlingUpperMain n kp +
          Real.log 2 * ((Nat.floor r_co -
            Nat.ceil ((n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2 / (Real.log (n : ℝ)) ^ 4) : ℕ) : ℝ) +
          Real.log (((n + 1) ^ (phaseNat n - 1) : ℕ) : ℝ) + factorialLogErrorBound n ≤
        -(n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2 / (Real.log (n : ℝ)) ^ 2) :
    let L : ℝ := Real.log (n : ℝ)
    let ell : ℝ := Real.log (Real.log (n : ℝ))
    let t_n : ℝ := universalShift n
    let d_th : ℕ := Nat.ceil (mu n (phaseNat n) + t_n)
    let shift_th : ℕ := Nat.ceil ((n : ℝ) * ell ^ 2 / L ^ 4)
    let k_chi_th : ℕ := Nat.floor r₀ - shift_th - 2 * d_th
    let k_zeta_th : ℕ := Nat.floor r_co - shift_th - 4 * d_th
    1 ≤ k_zeta_th ∧ k_zeta_th + 4 * d_th < n ∧ k_chi_th + 2 * d_th < n ∧
      (k_chi_th : ℤ) = ⌊r₀⌋ - (shift_th : ℤ) - 2 * (d_th : ℤ) ∧
      (k_zeta_th : ℤ) = ⌊r_co⌋ - (shift_th : ℤ) - 4 * (d_th : ℤ) ∧
      (randomGraphMeasure n).real {G : LabeledGraph n | chromaticNumberNat G ≤ k_chi_th} ≤
        2 * quasiExpTail n + Real.exp (-thetaBar * gamma * (n : ℝ)) +
          Real.exp (-(n : ℝ) * ell ^ 2 / L ^ 2) ∧
      (randomGraphMeasure n).real {G : LabeledGraph n | cochromaticNumber G ≤ k_zeta_th} ≤
        2 * quasiExpTail n + Real.exp (-thetaBar * gamma * (n : ℝ)) +
          Real.exp (-(n : ℝ) * ell ^ 2 / L ^ 2) ∧
      (randomGraphMeasure n).real {G : LabeledGraph n | chromaticNumberNat G ≤ k_chi_th} ≤
        3 * quasiExpTail n ∧
      (randomGraphMeasure n).real {G : LabeledGraph n | cochromaticNumber G ≤ k_zeta_th} ≤
        3 * quasiExpTail n := by
  intro L ell t_n d_th shift_th k_chi_th k_zeta_th
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hL_pos : 0 < L := by linarith only [hL20]
  have htn_pos : 0 < t_n := by dsimp [t_n]; unfold universalShift; positivity
  have hd_th_ge : mu n (phaseNat n) + t_n ≤ (d_th : ℝ) := Nat.le_ceil _
  have hk_zeta_pos : 1 ≤ k_zeta_th := by dsimp [k_zeta_th, shift_th, d_th, t_n, ell, L]; omega
  have hk_zeta_sum : k_zeta_th + 4 * d_th = Nat.floor r_co - shift_th := by
    dsimp [k_zeta_th, shift_th, d_th, t_n, ell, L]; omega
  have hk_chi_sum : k_chi_th + 2 * d_th = Nat.floor r₀ - shift_th := by
    dsimp [k_chi_th, shift_th, d_th, t_n, ell, L]; omega
  have hk_chi_int : (k_chi_th : ℤ) = ⌊r₀⌋ - (shift_th : ℤ) - 2 * (d_th : ℤ) := by
    rw [← hfl0]; dsimp [k_chi_th, shift_th, d_th, t_n, ell, L]; omega
  have hk_zeta_int : (k_zeta_th : ℤ) = ⌊r_co⌋ - (shift_th : ℤ) - 4 * (d_th : ℤ) := by
    rw [← hflCo]; dsimp [k_zeta_th, shift_th, d_th, t_n, ell, L]; omega
  set B_box : ℝ := Real.log (((n + 1) ^ (phaseNat n - 1) : ℕ) : ℝ)
  have hB_exp : (((n + 1) ^ (phaseNat n - 1) : ℕ) : ℝ) = Real.exp B_box :=
    (Real.exp_log (by positivity)).symm
  have hfilt := randomGraph_filtered_coloring_and_cocoloring_le_v12
    (n := n) (alpha := phaseNat n) (m := 1) (k_chi := k_chi_th) (k_zeta := k_zeta_th)
    (d := d_th) (m_cap := m_cap) hn2 le_rfl (by omega) htn_pos.le
    (by simpa only [Nat.add_sub_cancel] using hd_th_ge)
    (by rw [hk_chi_sum]; exact hk0_lt.le)
    (by rw [hk_zeta_sum]; exact hkCo_lt.le)
    (L_chi := -(n : ℝ) * ell ^ 2 / L ^ 2 - B_box)
    (L_zeta := -(n : ℝ) * ell ^ 2 / L ^ 2 - B_box)
    (fun kp hkp hcap ↦ by
      have hkp' : kp ∈ boundedColoringProfiles n (phaseNat n - 1) (Nat.floor r₀ - shift_th) := by
        rwa [← hk_chi_sum]
      have h := hkp0 kp hkp' hcap
      simp only [zero_mul, add_zero] at h
      change profileStirlingUpperMain n kp + B_box + factorialLogErrorBound n ≤
        -(n : ℝ) * ell ^ 2 / L ^ 2 at h
      linarith only [h])
    (fun kp hkp hcap ↦ by
      have hkp' : kp ∈ boundedColoringProfiles n (phaseNat n - 1) (Nat.floor r_co - shift_th) := by
        rwa [← hk_zeta_sum]
      have h := hkpCo kp hkp' hcap
      have hks : ((k_zeta_th + 4 * d_th : ℕ) : ℝ) = ((Nat.floor r_co - shift_th : ℕ) : ℝ) := by
        rw [hk_zeta_sum]
      rw [hks]
      change profileStirlingUpperMain n kp + Real.log 2 * ((Nat.floor r_co - shift_th : ℕ) : ℝ) +
          B_box + factorialLogErrorBound n ≤
        -(n : ℝ) * ell ^ 2 / L ^ 2 at h
      linarith only [h])
  have hboth_half :
      Real.exp (-thetaBar * gamma * (n : ℝ)) + Real.exp (-(n : ℝ) * ell ^ 2 / L ^ 2) ≤
        quasiExpTail n := by
    have hbase : 2 * (n : ℝ) / L ^ 10 + Real.log 2 ≤ (n : ℝ) * ell ^ 2 / L ^ 2 := by
      have h1 : 2 * (n : ℝ) / L ^ 10 ≤ (n : ℝ) / L ^ 2 := by
        rw [div_le_div_iff₀ (pow_pos hL_pos 10) (sq_pos_of_pos hL_pos)]
        have h2L8 : (2 : ℝ) ≤ L ^ 8 := by
          calc (2 : ℝ) ≤ (20 : ℝ) ^ 8 := by norm_num
            _ ≤ L ^ 8 := pow_le_pow_left₀ (by norm_num) hL20 8
        have hm := mul_le_mul_of_nonneg_left h2L8 (mul_nonneg hn_pos.le (sq_nonneg L))
        linarith only [hm, show (n : ℝ) * L ^ 2 * 2 = 2 * (n : ℝ) * L ^ 2 by ring,
          show (n : ℝ) * L ^ 2 * L ^ 8 = (n : ℝ) * L ^ 10 by ring]
      have h2 : Real.log 2 ≤ (n : ℝ) / L ^ 2 := by
        rw [le_div_iff₀ (sq_pos_of_pos hL_pos)]
        have hL25 : L ^ 2 ≤ L ^ 5 := pow_le_pow_right₀ (by linarith only [hL20] : 1 ≤ L) (by omega)
        have hm := mul_le_mul_of_nonneg_right Real.log_two_lt_d9.le (sq_nonneg L)
        change 200 * L ^ 5 ≤ (n : ℝ) at hL5n
        linarith only [hL25, hm, hL5n, sq_pos_of_pos hL_pos]
      have h3 : 4 * ((n : ℝ) / L ^ 2) ≤ (n : ℝ) * ell ^ 2 / L ^ 2 := by
        have hw4 : (4 : ℝ) ≤ ell ^ 2 := by
          have := pow_le_pow_left₀ (by norm_num) hw2 2; norm_num at this; exact this
        calc 4 * ((n : ℝ) / L ^ 2) = (n : ℝ) * 4 / L ^ 2 := by ring
          _ ≤ (n : ℝ) * ell ^ 2 / L ^ 2 :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hw4 hn_pos.le) (sq_nonneg L)
      linarith only [h1, h2, h3, div_pos hn_pos (sq_pos_of_pos hL_pos)]
    have he2 : Real.exp (-(n : ℝ) * ell ^ 2 / L ^ 2) ≤ (1 / 2) * quasiExpTail n := by
      have hle : -(n : ℝ) * ell ^ 2 / L ^ 2 ≤ -(2 * (n : ℝ) / L ^ 10) - Real.log 2 := by
        linarith only [hbase, show -(n : ℝ) * ell ^ 2 / L ^ 2 = -((n : ℝ) * ell ^ 2 / L ^ 2) by ring]
      calc Real.exp (-(n : ℝ) * ell ^ 2 / L ^ 2)
          ≤ Real.exp (-(2 * (n : ℝ) / L ^ 10) - Real.log 2) := Real.exp_le_exp.mpr hle
        _ = (1 / 2) * quasiExpTail n := by
            unfold quasiExpTail
            have hrew : -(2 * (n : ℝ) / L ^ 10) - Real.log 2 =
                -Real.log 2 + (-2 * (n : ℝ) / (Real.log (n : ℝ)) ^ 10) := by dsimp [L]; ring
            rw [hrew, Real.exp_add, Real.exp_neg, Real.exp_log two_pos]
            ring
    have he1 : Real.exp (-thetaBar * gamma * (n : ℝ)) ≤ (1 / 2) * quasiExpTail n := by
      have hth_ge : 3 / L ≤ thetaBar * gamma := by
        rw [div_le_iff₀ hL_pos]
        have hthL := (div_le_iff₀ (mul_pos htheta_pos hgamma)).mp hL_th
        linarith only [hthL, show L * (thetaBar * gamma) = thetaBar * gamma * L by ring]
      have h1 : 2 * (n : ℝ) / L ^ 10 + Real.log 2 ≤ thetaBar * gamma * (n : ℝ) := by
        have ha : 2 * (n : ℝ) / L ^ 10 ≤ (2 / L) * (n : ℝ) := by
          rw [div_mul_eq_mul_div, mul_comm 2 (n : ℝ), div_le_div_iff₀ (pow_pos hL_pos 10) hL_pos]
          have hp : L ≤ L ^ 10 := by
            simpa only [pow_one] using pow_le_pow_right₀ (by linarith only [hL20] : 1 ≤ L) (by omega : 1 ≤ 10)
          have hm := mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ (n : ℝ) * 2 by positivity)
          linarith only [hm, show (n : ℝ) * 2 * L = 2 * (n : ℝ) * L by ring]
        have hb : Real.log 2 ≤ (1 / L) * (n : ℝ) := by
          rw [one_div_mul_eq_div, le_div_iff₀ hL_pos]
          have hL15 : L ≤ L ^ 5 := by
            simpa only [pow_one] using pow_le_pow_right₀ (by linarith only [hL20] : 1 ≤ L) (by omega : 1 ≤ 5)
          have hqL : Real.log 2 * L ≤ L :=
            mul_le_of_le_one_left hL_pos.le (Real.log_two_lt_d9.le.trans (by norm_num))
          change 200 * L ^ 5 ≤ (n : ℝ) at hL5n
          linarith only [hqL, hL15, hL5n, hL_pos]
        have hc := mul_le_mul_of_nonneg_right hth_ge hn_pos.le
        linarith only [ha, hb, hc, show (2 / L) * (n : ℝ) + (1 / L) * (n : ℝ) = (3 / L) * (n : ℝ) by ring]
      have hle : -thetaBar * gamma * (n : ℝ) ≤ -(2 * (n : ℝ) / L ^ 10) - Real.log 2 := by
        linarith only [h1, show -thetaBar * gamma * (n : ℝ) = -(thetaBar * gamma * (n : ℝ)) by ring]
      calc Real.exp (-thetaBar * gamma * (n : ℝ))
          ≤ Real.exp (-(2 * (n : ℝ) / L ^ 10) - Real.log 2) := Real.exp_le_exp.mpr hle
        _ = (1 / 2) * quasiExpTail n := by
            unfold quasiExpTail
            have hrew : -(2 * (n : ℝ) / L ^ 10) - Real.log 2 =
                -Real.log 2 + (-2 * (n : ℝ) / (Real.log (n : ℝ)) ^ 10) := by dsimp [L]; ring
            rw [hrew, Real.exp_add, Real.exp_neg, Real.exp_log two_pos]
            ring
    linarith only [he1, he2]
  simp only [hB_exp, ← Real.exp_add,
    show B_box + (-(n : ℝ) * ell ^ 2 / L ^ 2 - B_box) = -(n : ℝ) * ell ^ 2 / L ^ 2 by ring] at hfilt
  have hmcd := exp_mcdiarmid_universalShift_le_quasiExpTail hn2
  have hq_nn : 0 ≤ quasiExpTail n := by unfold quasiExpTail; positivity
  have hchi_prob :
      (randomGraphMeasure n).real {G : LabeledGraph n | chromaticNumberNat G ≤ k_chi_th} ≤
        2 * quasiExpTail n + Real.exp (-thetaBar * gamma * (n : ℝ)) +
          Real.exp (-(n : ℝ) * ell ^ 2 / L ^ 2) := by
    linarith only [hfilt.1, hmcd, hpack_bound, hq_nn]
  have hzeta_prob :
      (randomGraphMeasure n).real {G : LabeledGraph n | cochromaticNumber G ≤ k_zeta_th} ≤
        2 * quasiExpTail n + Real.exp (-thetaBar * gamma * (n : ℝ)) +
          Real.exp (-(n : ℝ) * ell ^ 2 / L ^ 2) := by
    linarith only [hfilt.2, hmcd, hpack_bound]
  refine ⟨hk_zeta_pos, ?_, ?_, hk_chi_int, hk_zeta_int, hchi_prob, hzeta_prob,
    by linarith only [hchi_prob, hboth_half], by linarith only [hzeta_prob, hboth_half]⟩
  · rw [hk_zeta_sum]; exact hkCo_lt
  · rw [hk_chi_sum]; exact hk0_lt

/-- **Proposition 4.1(iii) (`prop:lower-tails`, `main.tex` lines 660–664) unconditional capped lower tails:**
for fixed `thetaBar ∈ (0, 1/20]` and `gamma > 0`, there exists `C_corr > 0` such that eventually
uniformly over all `n` satisfying `δ_n ∈ [0, δ_*]`, `thetaBar ≤ p_{1, ∞}(δ_n)`, and
`g(thetaBar) + (log 2 / 2)(T_{δ_n} - 1) ≥ 2 gamma`:
1. `𝓛_{S_{≥ 1}}^{=thetaBar}(n, ·)` and `𝓛_{S_{≥ 1}}^{=thetaBar}(n, ·) + (log 2) ·` have unique
   zeros `r₀, r_co` in `(c_n - C_corr Δ_n, c_n + C_corr Δ_n)`,
2. at `k_{χ, thetaBar}^- := ⌊r₀⌋₊ - ⌈n ℓ² / L⁴⌉₊ - 2 d_{n, 1}` and
   `k_{ζ, thetaBar}^- := ⌊r_co⌋₊ - ⌈n ℓ² / L⁴⌉₊ - 4 d_{n, 1}` (`d_{n, 1} = ⌈μ_α + t_n⌉₊`),
   both `P(χ(G_n) ≤ k_{χ, thetaBar}^-)` and `P(ζ(G_n) ≤ k_{ζ, thetaBar}^-)` are bounded by
   `2 * quasiExpTail n + exp(-thetaBar * gamma * n) + exp(-n ℓ² / L²)` AND by
   `3 * quasiExpTail n`. -/
theorem eventually_randomGraph_lowerTails_prop41_iii
    {thetaBar gamma : ℝ}
    (htheta : thetaBar ∈ Set.Ioc (0 : ℝ) (1 / 20))
    (hgamma : 0 < gamma) :
    ∃ C_corr : ℝ, 0 < C_corr ∧
      ∀ᶠ n : ℕ in atTop,
        phaseDelta n ∈ Set.Icc (0 : ℝ) deltaStar →
        thetaBar ≤ p1Inf (phaseDelta n) →
        2 * gamma ≤ phiInfAux thetaBar + Real.log 2 / 2 * (phaseTarget (phaseDelta n) - 1) →
          let F_cap : ℝ → ℝ := fun T ↦
            binEntropy thetaBar - Real.log 2 / 2 * thetaBar +
              (1 - thetaBar) * (⨅ l : ℝ,
                (Real.log (∑ i ∈ Finset.Ico 2 (phaseNat n),
                    Real.exp (l * (i : ℝ) +
                      (Real.log ((phaseNat n).descFactorial i : ℝ) -
                        (i : ℝ) * Real.log (phaseNat n : ℝ) -
                        Real.log 2 / 2 * (i : ℝ) ^ 2))) -
                  l * ((T - thetaBar) / (1 - thetaBar))))
          let obj_cap : ℝ → ℝ → ℝ := fun tau s ↦
            (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + s - s * Real.log s +
              s * (profileDeficitAffineA (phaseNat n) +
                profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s +
                F_cap (fourSizeTarget n (phaseNat n) s) + tau)
          (∃! r₀ : ℝ,
            r₀ ∈ Set.Ioo (phaseRootCenter n - C_corr * logLogOrder n * phaseRootGapRadius n)
                         (phaseRootCenter n + C_corr * logLogOrder n * phaseRootGapRadius n) ∧
              obj_cap 0 r₀ = 0) ∧
          (∃! r_co : ℝ,
            r_co ∈ Set.Ioo (phaseRootCenter n - C_corr * logLogOrder n * phaseRootGapRadius n)
                           (phaseRootCenter n + C_corr * logLogOrder n * phaseRootGapRadius n) ∧
              obj_cap (Real.log 2) r_co = 0) ∧
          ∀ r₀ ∈ Set.Icc (phaseRootCenter n - C_corr * logLogOrder n * phaseRootGapRadius n)
                         (phaseRootCenter n + C_corr * logLogOrder n * phaseRootGapRadius n),
            obj_cap 0 r₀ = 0 →
            ∀ r_co ∈ Set.Icc (phaseRootCenter n - C_corr * logLogOrder n * phaseRootGapRadius n)
                             (phaseRootCenter n + C_corr * logLogOrder n * phaseRootGapRadius n),
              obj_cap (Real.log 2) r_co = 0 →
              let L : ℝ := Real.log (n : ℝ)
              let ell : ℝ := Real.log (Real.log (n : ℝ))
              let t_n : ℝ := universalShift n
              let d_th : ℕ := Nat.ceil (mu n (phaseNat n) + t_n)
              let shift_th : ℕ := Nat.ceil ((n : ℝ) * ell ^ 2 / L ^ 4)
              let k_chi_th : ℕ := Nat.floor r₀ - shift_th - 2 * d_th
              let k_zeta_th : ℕ := Nat.floor r_co - shift_th - 4 * d_th
              1 ≤ k_zeta_th ∧ k_zeta_th + 4 * d_th < n ∧ k_chi_th + 2 * d_th < n ∧
                (k_chi_th : ℤ) = ⌊r₀⌋ - (shift_th : ℤ) - 2 * (d_th : ℤ) ∧
                (k_zeta_th : ℤ) = ⌊r_co⌋ - (shift_th : ℤ) - 4 * (d_th : ℤ) ∧
                (randomGraphMeasure n).real {G : LabeledGraph n | chromaticNumberNat G ≤ k_chi_th} ≤
                  2 * quasiExpTail n + Real.exp (-thetaBar * gamma * (n : ℝ)) +
                    Real.exp (-(n : ℝ) * ell ^ 2 / L ^ 2) ∧
                (randomGraphMeasure n).real {G : LabeledGraph n | cochromaticNumber G ≤ k_zeta_th} ≤
                  2 * quasiExpTail n + Real.exp (-thetaBar * gamma * (n : ℝ)) +
                    Real.exp (-(n : ℝ) * ell ^ 2 / L ^ 2) ∧
                (randomGraphMeasure n).real {G : LabeledGraph n | chromaticNumberNat G ≤ k_chi_th} ≤
                  3 * quasiExpTail n ∧
                (randomGraphMeasure n).real {G : LabeledGraph n | cochromaticNumber G ≤ k_zeta_th} ≤
                  3 * quasiExpTail n := by
  have htheta_pos : 0 < thetaBar := htheta.1
  have htheta_hi : thetaBar ≤ 1 / 20 := htheta.2
  have htheta_icc : thetaBar ∈ Set.Icc (0 : ℝ) (1 / 20) := ⟨htheta_pos.le, htheta_hi⟩
  obtain ⟨C_corr, _, hC_pos, _, hRootEv⟩ :=
    exists_pos_eventually_existsUnique_cappedInfinitePhaseObjective_zero_logLogCorridor
  obtain ⟨C_dual, Alpha₀, hC_dual_pos, _, hCapDual⟩ :=
    abs_cappedInfiniteFiniteEntropy_sub_cappedDualValue_le
  refine ⟨C_corr, hC_pos, ?_⟩
  set C_wide : ℝ := C_corr + 2
  have hC_wide_nn : 0 ≤ C_wide := by dsimp [C_wide]; positivity
  set C_err : ℝ := 2 * C_dual + 4 * C_wide * universalDualLip_v12 + 1
  have hC_err_def : C_err = 2 * C_dual + 4 * C_wide * universalDualLip_v12 + 1 := rfl
  have hC_err_pos : 0 < C_err := by
    have := universalDualLip_v12_nonneg; dsimp [C_err]; positivity
  clear_value C_err
  have ho_L5 : (fun x : ℝ ↦ (Real.log x) ^ ((5 : ℕ) : ℝ)) =o[atTop] (fun x : ℝ ↦ x ^ (1 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop ((5 : ℕ) : ℝ) zero_lt_one
  have hL5_small : ∀ᶠ n : ℕ in atTop, 200 * (Real.log (n : ℝ)) ^ 5 ≤ (n : ℝ) := by
    have hb := (ho_L5.comp_tendsto tendsto_natCast_atTop_atTop).bound (by norm_num : (0 : ℝ) < 1 / 200)
    filter_upwards [hb, eventually_gt_atTop 2] with n hn _
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hL_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    dsimp only [Function.comp_apply] at hn
    rw [Real.rpow_natCast, Real.norm_eq_abs, abs_of_pos (pow_pos hL_pos 5),
      Real.rpow_one, Real.norm_eq_abs, abs_of_pos hn_pos] at hn
    linarith
  have ho_w2 : (fun x : ℝ ↦ (Real.log x) ^ ((2 : ℕ) : ℝ)) =o[atTop] (fun x : ℝ ↦ x ^ (1 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop ((2 : ℕ) : ℝ) zero_lt_one
  have hw2_small : ∀ᶠ n : ℕ in atTop, (logLogOrder n) ^ 2 ≤ (1 / 200) * logOrder n := by
    have hb := (ho_w2.comp_tendsto tendsto_logOrder_atTop).bound (by norm_num : (0 : ℝ) < 1 / 200)
    filter_upwards [hb, tendsto_logLogOrder_atTop.eventually_ge_atTop 2,
      tendsto_logOrder_atTop.eventually_ge_atTop 4] with n hn hw2 hL4
    have hw_pos : 0 < logLogOrder n := by linarith
    have hL_pos : 0 < logOrder n := by linarith
    dsimp only [Function.comp_apply] at hn
    change ‖(logLogOrder n) ^ ((2 : ℕ) : ℝ)‖ ≤ (1 / 200) * ‖(logOrder n) ^ (1 : ℝ)‖ at hn
    rw [Real.rpow_natCast, Real.norm_eq_abs, abs_of_pos (sq_pos_of_pos hw_pos),
      Real.rpow_one, Real.norm_eq_abs, abs_of_pos hL_pos] at hn
    exact hn
  set eps_w : ℝ := min (1 / 200) (1 / (100 * (C_corr + 1)))
  have hwL_small : ∀ᶠ n : ℕ in atTop, ‖logLogOrder n‖ ≤ eps_w * ‖logOrder n‖ :=
    logLogOrder_isLittleO_logOrder.bound (lt_min (by norm_num) (by positivity))
  have hphase_A0 : ∀ᶠ n : ℕ in atTop, max Alpha₀ 10 ≤ phaseNat n := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop ((max Alpha₀ 10 : ℕ) : ℝ),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact_mod_cast hn.trans hph.1
  filter_upwards [hRootEv,
    eventually_cappedInfinitePhaseObjective_strictMonoOn_and_drop C_wide hC_wide_nn,
    eventually_cappedInfinite_target_mem_KcapInterval C_wide hC_wide_nn,
    eventually_corridor_inv_target_logLogRate_v12 C_wide hC_wide_nn,
    eventually_corridor_inv_target_logLogRate_v12 C_corr hC_pos.le,
    eventually_mu_phaseNat_succ_and_deltaStar_le_v12,
    eventually_phaseRootCenter_sub_main_logLogRate_v12,
    eventually_two_85_logOrder_le_phaseNat,
    eventually_box_mul_error_le_five_log_sq,
    eventually_randomGraph_homogeneousPacking_alpha_sub_one_tail htheta hgamma,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
    hL5_small, hw2_small, hwL_small, hphase_A0,
    tendsto_logLogOrder_atTop.eventually_ge_atTop (max 2 (10 * C_err + 10)),
    tendsto_logOrder_atTop.eventually_ge_atTop (max 20 (3 / (thetaBar * gamma)))] with
    n hRoots hDrop hKcapWide hInvWide hInv hMuBds hcMain hph285 hBoxErr hPackSub1 hphase
    hL5n hw2L hwL hphA0 hw_big hL_big
    hd hp1_ge hphi_ge F_cap obj_cap
  have hobj_cap_eq : obj_cap = cappedInfinitePhaseObjective n thetaBar := rfl
  rw [hobj_cap_eq]
  clear hobj_cap_eq obj_cap F_cap
  clear hRootEv
  have htau0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.log 2) := ⟨le_rfl, (Real.log_pos one_lt_two).le⟩
  have htauL : Real.log 2 ∈ Set.Icc (0 : ℝ) (Real.log 2) := ⟨(Real.log_pos one_lt_two).le, le_rfl⟩
  have hex0 := (hRoots hd thetaBar htheta_icc 0 htau0).2.1
  have hexCo := (hRoots hd thetaBar htheta_icc (Real.log 2) htauL).2.1
  clear hRoots
  refine ⟨hex0, hexCo, ?_⟩
  clear hex0 hexCo
  intro r₀ hr₀ hz₀ r_co hr_co hz_co L ell t_n d_th shift_th k_chi_th k_zeta_th
  change ell ^ 2 ≤ (1 / 200) * L at hw2L
  change 200 * L ^ 5 ≤ (n : ℝ) at hL5n
  have hw2 : 2 ≤ ell := (le_max_left _ _).trans hw_big
  have hw_Cerr : 10 * C_err + 10 ≤ ell := (le_max_right _ _).trans hw_big
  have hL20 : 20 ≤ L := (le_max_left _ _).trans hL_big
  have hL_th : 3 / (thetaBar * gamma) ≤ L := (le_max_right _ _).trans hL_big
  have hL_pos : 0 < L := by linarith
  have hw_pos : 0 < ell := by linarith
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have : Real.log (n : ℝ) ≤ 0 := by
      rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl <;> simp
    linarith [hL20]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have ha_A0 : Alpha₀ ≤ phaseNat n := (le_max_left _ _).trans hphA0
  have ha10 : 10 ≤ phaseNat n := (le_max_right _ _).trans hphA0
  rw [Real.norm_eq_abs, abs_of_pos (show 0 < logLogOrder n from hw_pos),
    Real.norm_eq_abs, abs_of_pos (show 0 < logOrder n from hL_pos)] at hwL
  change ell ≤ eps_w * L at hwL
  have hwL_200 : ell ≤ (1 / 200) * L :=
    hwL.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hL_pos.le)
  have hwL_corr : C_corr * ell ≤ (1 / 100) * L := by
    have h1 := hwL.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hL_pos.le)
    have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ C_corr + 1 by positivity)
    have h3 : (C_corr + 1) * (1 / (100 * (C_corr + 1)) * L) = (1 / 100) * L := by
      field_simp [(show (0 : ℝ) < C_corr + 1 by positivity).ne']
    linarith [mul_pos hC_pos hw_pos]
  clear ho_L5 hL5_small ho_w2 hw2_small hwL_small hphase_A0 hw_big hL_big hphA0 hwL
  clear_value eps_w
  have htn_pos : 0 < t_n := by dsimp [t_n]; unfold universalShift; positivity
  have hc_lo : (3 / 10 : ℝ) * ((n : ℝ) / L) ≤ phaseRootCenter n := by
    have h1 : -(4 * (n : ℝ) * ell / L ^ 2) ≤
        phaseRootCenter n - (Real.log 2 / 2) * ((n : ℝ) / L) := (abs_le.mp hcMain.2).1
    have h2 : 4 * (n : ℝ) * ell / L ^ 2 ≤ (1 / 50 : ℝ) * ((n : ℝ) / L) := by
      calc 4 * (n : ℝ) * ell / L ^ 2
          ≤ 4 * (n : ℝ) * ((1 / 200) * L) / L ^ 2 :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hwL_200 (by positivity)) (sq_nonneg L)
        _ = (1 / 50 : ℝ) * ((n : ℝ) / L) := by field_simp [hL_pos.ne']; ring
    have hq_num : (16 / 50 : ℝ) * ((n : ℝ) / L) ≤ (Real.log 2 / 2) * ((n : ℝ) / L) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.log_two_gt_d9]) (div_nonneg hn_pos.le hL_pos.le)
    linarith [div_pos hn_pos hL_pos]
  have hgap_lo : (1 / 60 : ℝ) * ((n : ℝ) / L ^ 3) ≤ phaseRootGapRadius n := by
    unfold phaseRootGapRadius
    have ha_sq : (phaseNat n : ℝ) ^ 2 ≤ 16 * L ^ 2 := by
      calc (phaseNat n : ℝ) ^ 2 ≤ (4 * L) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hphase.2 2
        _ = 16 * L ^ 2 := by ring
    calc (1 / 60 : ℝ) * ((n : ℝ) / L ^ 3)
        ≤ (3 / 160 : ℝ) * ((n : ℝ) / L ^ 3) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = ((3 / 10 : ℝ) * ((n : ℝ) / L)) / (16 * L ^ 2) := by field_simp [hL_pos.ne']; ring
      _ ≤ phaseRootCenter n / (16 * L ^ 2) := div_le_div_of_nonneg_right hc_lo (by positivity)
      _ ≤ phaseRootCenter n / (phaseNat n : ℝ) ^ 2 :=
          div_le_div_of_nonneg_left (by linarith [div_pos hn_pos hL_pos])
            (sq_pos_of_pos (lt_of_lt_of_le hL_pos hphase.1)) ha_sq
  have hgap_nn : 0 ≤ phaseRootGapRadius n := le_trans (by positivity) hgap_lo
  have hgap_hi : phaseRootGapRadius n ≤ (n : ℝ) / L ^ 3 := by
    unfold phaseRootGapRadius
    have ha_sq : L ^ 2 ≤ (phaseNat n : ℝ) ^ 2 := pow_le_pow_left₀ hL_pos.le hphase.1 2
    calc phaseRootCenter n / (phaseNat n : ℝ) ^ 2
        ≤ ((n : ℝ) / L) / L ^ 2 :=
          div_le_div₀ (div_nonneg hn_pos.le hL_pos.le) hcMain.1 (sq_pos_of_pos hL_pos) ha_sq
      _ = (n : ℝ) / L ^ 3 := by ring
  have hshift_add2_le_gap : (shift_th : ℝ) + 2 ≤ 2 * ell * phaseRootGapRadius n := by
    have hs_lt : (shift_th : ℝ) < (n : ℝ) * ell ^ 2 / L ^ 4 + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hmain_sh : (n : ℝ) * ell ^ 2 / L ^ 4 ≤ (1 / 200 : ℝ) * ((n : ℝ) * ell / L ^ 3) := by
      calc (n : ℝ) * ell ^ 2 / L ^ 4
          = (ell / L) * ((n : ℝ) * ell / L ^ 3) := by field_simp [hL_pos.ne']
        _ ≤ (1 / 200 : ℝ) * ((n : ℝ) * ell / L ^ 3) :=
            mul_le_mul_of_nonneg_right ((div_le_iff₀ hL_pos).mpr hwL_200) (by positivity)
    have h3_le : (3 : ℝ) ≤ (1 / 50 : ℝ) * ((n : ℝ) * ell / L ^ 3) := by
      have h3' : (3 : ℝ) ≤ (1 / 50 : ℝ) * ((n : ℝ) / L ^ 3) := by
        rw [mul_div_assoc', le_div_iff₀ (pow_pos hL_pos 3)]
        have hL35 : L ^ 3 ≤ L ^ 5 := pow_le_pow_right₀ (by linarith : 1 ≤ L) (by omega)
        change 200 * L ^ 5 ≤ (n : ℝ) at hL5n
        linarith [hL5n, pow_pos hL_pos 3]
      exact h3'.trans (by
        have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ ell by linarith)
          (show (0 : ℝ) ≤ (1 / 50 : ℝ) * ((n : ℝ) / L ^ 3) by positivity)
        linarith [show (1 / 50 : ℝ) * ((n : ℝ) / L ^ 3) * ell =
            (1 / 50 : ℝ) * ((n : ℝ) * ell / L ^ 3) by ring])
    have hw_gap : (1 / 30 : ℝ) * ((n : ℝ) * ell / L ^ 3) ≤ 2 * ell * phaseRootGapRadius n := by
      calc (1 / 30 : ℝ) * ((n : ℝ) * ell / L ^ 3)
          = 2 * ell * ((1 / 60 : ℝ) * ((n : ℝ) / L ^ 3)) := by ring
        _ ≤ 2 * ell * phaseRootGapRadius n :=
            mul_le_mul_of_nonneg_left hgap_lo (by positivity)
    linarith [(show 0 < (n : ℝ) * ell / L ^ 3 by positivity)]
  have hd_th_le : 4 * (d_th : ℝ) ≤ (1 / 20 : ℝ) * ((n : ℝ) / L) := by
    have hc := Nat.ceil_lt_add_one (add_nonneg (mu_nonneg n (phaseNat n)) htn_pos.le)
    have hmu_le : mu n (phaseNat n) ≤ t_n := hMuBds.2.1 hd.2
    have htn_L : t_n ≤ (1 / 400 : ℝ) * ((n : ℝ) / L) := by
      dsimp [t_n]; unfold universalShift
      have hL4 : (400 : ℝ) ≤ L ^ 4 := by
        calc (400 : ℝ) ≤ (20 : ℝ) ^ 4 := by norm_num
          _ ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hL20 4
      calc (n : ℝ) / (Real.log (n : ℝ)) ^ 5 = (n : ℝ) / (L ^ 4 * L) := by dsimp [L]; ring
        _ ≤ (n : ℝ) / (400 * L) := div_le_div_of_nonneg_left hn_pos.le (by positivity)
            (mul_le_mul_of_nonneg_right hL4 hL_pos.le)
        _ = (1 / 400 : ℝ) * ((n : ℝ) / L) := by ring
    have h4_L : (4 : ℝ) ≤ (1 / 100 : ℝ) * ((n : ℝ) / L) := by
      rw [mul_div_assoc', le_div_iff₀ hL_pos]
      have h2L5 : 2 * L ≤ L ^ 5 := by
        have h2L4 : (2 : ℝ) ≤ L ^ 4 := by
          calc (2 : ℝ) ≤ (20 : ℝ) ^ 4 := by norm_num
            _ ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hL20 4
        calc 2 * L ≤ L ^ 4 * L := mul_le_mul_of_nonneg_right h2L4 hL_pos.le
          _ = L ^ 5 := by ring
      linarith [hL5n]
    change 4 * (Nat.ceil (mu n (phaseNat n) + t_n) : ℝ) ≤ (1 / 20 : ℝ) * ((n : ℝ) / L)
    linarith only [hc, hmu_le, htn_L, h4_L, div_pos hn_pos hL_pos]
  have hshift_L : (shift_th : ℝ) ≤ (1 / 100 : ℝ) * ((n : ℝ) / L) := by
    have hs_lt : (shift_th : ℝ) < (n : ℝ) * ell ^ 2 / L ^ 4 + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h1 : (n : ℝ) * ell ^ 2 / L ^ 4 ≤ (1 / 200 : ℝ) * ((n : ℝ) / L) := by
      calc (n : ℝ) * ell ^ 2 / L ^ 4 = (ell ^ 2 / L ^ 3) * ((n : ℝ) / L) := by ring
        _ ≤ (1 / 200 : ℝ) * ((n : ℝ) / L) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            rw [div_le_iff₀ (pow_pos hL_pos 3)]
            have hL13 : L ^ 1 ≤ L ^ 3 := pow_le_pow_right₀ (by linarith : 1 ≤ L) (by omega)
            rw [pow_one] at hL13
            change ell ^ 2 ≤ (1 / 200) * L at hw2L
            linarith [hw2L]
    have h2 : (1 : ℝ) ≤ (1 / 200 : ℝ) * ((n : ℝ) / L) := by
      rw [mul_div_assoc', le_div_iff₀ hL_pos]
      have hL15 : L ^ 1 ≤ L ^ 5 := pow_le_pow_right₀ (by linarith : 1 ≤ L) (by omega)
      rw [pow_one] at hL15
      change 200 * L ^ 5 ≤ (n : ℝ) at hL5n
      linarith [hL5n, hL_pos]
    linarith
  have hr_bounds : ∀ r ∈ Set.Icc
      (phaseRootCenter n - C_corr * ell * phaseRootGapRadius n)
      (phaseRootCenter n + C_corr * ell * phaseRootGapRadius n),
      (29 / 100 : ℝ) * ((n : ℝ) / L) ≤ r ∧ r ≤ 2 * ((n : ℝ) / L) := by
    intro r hr
    have hdelta_le : C_corr * ell * phaseRootGapRadius n ≤ (1 / 100 : ℝ) * ((n : ℝ) / L) := by
      have hgap_L : phaseRootGapRadius n ≤ (n : ℝ) / L ^ 2 := by
        calc phaseRootGapRadius n ≤ (n : ℝ) / L ^ 3 := hgap_hi
          _ = ((n : ℝ) / L ^ 2) / L := by ring
          _ ≤ ((n : ℝ) / L ^ 2) / 1 :=
              div_le_div_of_nonneg_left (by positivity) zero_lt_one (by linarith [hL20])
          _ = (n : ℝ) / L ^ 2 := div_one _
      calc C_corr * ell * phaseRootGapRadius n
          ≤ ((1 / 100) * L) * ((n : ℝ) / L ^ 2) :=
            mul_le_mul hwL_corr hgap_L hgap_nn (by positivity)
        _ = (1 / 100 : ℝ) * ((n : ℝ) / L) := by field_simp [hL_pos.ne']
    exact ⟨by linarith [hr.1, hc_lo],
      (hInv.2 r hr).2.1.trans (mul_le_mul_of_nonneg_left hcMain.1 zero_le_two)⟩
  have hslope_7_5 : (7 / 5 : ℝ) * L ^ 2 ≤ q / 4 * (phaseNat n : ℝ) ^ 2 := by
    have hsq := pow_le_pow_left₀ (by positivity) hph285 2
    have hnum : (7 / 5 : ℝ) ≤ q / 4 * (285 / 100 : ℝ) ^ 2 := by
      unfold q; linarith [Real.log_two_gt_d9]
    calc (7 / 5 : ℝ) * L ^ 2 ≤ (q / 4 * (285 / 100 : ℝ) ^ 2) * L ^ 2 :=
          mul_le_mul_of_nonneg_right hnum (sq_nonneg L)
      _ = q / 4 * ((285 / 100 : ℝ) * L) ^ 2 := by ring
      _ ≤ q / 4 * (phaseNat n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (div_nonneg q_pos.le (by norm_num))
  set m_cap : ℕ := Nat.ceil (thetaBar * (n : ℝ) / ((phaseNat n - 1 : ℕ) : ℝ))
  have hpack_fn : Unit →
      (randomGraphMeasure n).real
        {G : LabeledGraph n | m_cap ≤ maxDisjointHomogeneousEq G (phaseNat n - 1)} ≤
      Real.exp (-thetaBar * gamma * (n : ℝ)) :=
    fun _ ↦ hPackSub1 hd hphi_ge
  clear hPackSub1
  have hm_cap_lt_imp : ∀ k : ℕ, k < m_cap →
      (k : ℝ) < thetaBar * (n : ℝ) / ((phaseNat n - 1 : ℕ) : ℝ) := by
    intro k hk
    by_contra hge
    exact not_le_of_gt hk (Nat.ceil_le.mpr (not_lt.mp hge))
  have hsh_th_ge : (n : ℝ) * ell ^ 2 / L ^ 4 ≤ (shift_th : ℝ) := Nat.le_ceil _
  have hCapDual_all : ∀ {theta T' : ℝ}, theta ∈ Set.Icc (0 : ℝ) (1 / 20) → T' ∈ KcapInterval →
      |cappedInfiniteFiniteEntropy (phaseNat n) theta T' - cappedDualValue Sge1 theta T'| ≤
        C_dual / (phaseNat n : ℝ) :=
    fun hth' hT' ↦ (hCapDual ha_A0 hth' hT').2
  have hbox_n1 : Real.log (((n + 1) ^ (phaseNat n - 1) : ℕ) : ℝ) + factorialLogErrorBound n + 2 ≤
      6 * (logOrder n) ^ 2 := hBoxErr (phaseNat n - 1) (Nat.sub_le _ _)
  obtain ⟨hsub0, hfl0, hk0_lt, hkp0⟩ := prop41_iii_starTh_v12 (m_cap := m_cap)
    (d_th := d_th) (shift_th := shift_th) ha10 htheta hp1_ge hd rfl hC_dual_pos hC_err_pos hC_err_def
    hn_pos hL20 hw2 hw_Cerr hL5n hphase.1 hgap_nn hshift_add2_le_gap hd_th_le hshift_L
    hsh_th_ge hslope_7_5 hm_cap_lt_imp hr_bounds (hKcapWide hd)
    (fun s hs ↦ (hInvWide.2 s hs).2.2.2) hCapDual_all hbox_n1 hr₀ hz₀
    (hDrop hd thetaBar htheta_icc 0 htau0).2
  obtain ⟨hsubCo, hflCo, hkCo_lt, hkpCo⟩ := prop41_iii_starTh_v12 (m_cap := m_cap)
    (d_th := d_th) (shift_th := shift_th) ha10 htheta hp1_ge hd rfl hC_dual_pos hC_err_pos hC_err_def
    hn_pos hL20 hw2 hw_Cerr hL5n hphase.1 hgap_nn hshift_add2_le_gap hd_th_le hshift_L
    hsh_th_ge hslope_7_5 hm_cap_lt_imp hr_bounds (hKcapWide hd)
    (fun s hs ↦ (hInvWide.2 s hs).2.2.2) hCapDual_all hbox_n1 hr_co hz_co
    (hDrop hd thetaBar htheta_icc (Real.log 2) htauL).2
  exact prop41_iii_tails_of_starTh_v12 hn2 ha10 htheta_pos hgamma hL20 hL_th hw2 hL5n
    (hpack_fn ()) hsub0 hfl0 hk0_lt hkp0 hsubCo hflCo hkCo_lt hkpCo

/-!
## 6. Unconditional Lemma 7.1 `B_π` regularity and complete Lemma 7.1 synthesis
-/

private theorem rg_mono_v12 {n : ℕ} {A B : Set (LabeledGraph n)} (h : A ⊆ B) :
    (randomGraphMeasure n).real A ≤ (randomGraphMeasure n).real B :=
  measureReal_mono h (measure_ne_top _ _)

private theorem rg_biUnion_finset_le_v12 {α_idx : Type*} {n : ℕ}
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

private theorem nat_choose_le_pow_v12 : ∀ a k : ℕ, a.choose k ≤ a ^ k
  | _, 0 => by simp
  | 0, _ + 1 => by simp
  | a + 1, k + 1 => by
    rw [Nat.choose_succ_succ]
    calc a.choose k + a.choose (k + 1)
        ≤ a ^ k + a ^ (k + 1) :=
          Nat.add_le_add (nat_choose_le_pow_v12 a k) (nat_choose_le_pow_v12 a (k + 1))
      _ = a ^ k * (a + 1) := by ring
      _ ≤ (a + 1) ^ k * (a + 1) :=
          Nat.mul_le_mul_right (a + 1) (Nat.pow_le_pow_left (Nat.le_succ a) k)
      _ = (a + 1) ^ (k + 1) := by ring

private theorem vertexPartition_parts_card_le_v12 {n : ℕ} (P : VertexPartition n) :
    P.parts.card ≤ n := by
  calc P.parts.card
      = ∑ _B ∈ P.parts, 1 := by simp
    _ ≤ ∑ B ∈ P.parts, B.card :=
        Finset.sum_le_sum fun B hB ↦ (P.nonempty_of_mem_parts hB).card_pos
    _ = (Finset.univ : Finset (Fin n)).card := P.sum_card_parts
    _ = n := Finset.card_fin n

private theorem half_pow_phaseNat_le_v12 {n : ℕ} (hdom : PhaseDomain n) :
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

private theorem half_pow_le_two_pow_mul_half_pow_v12 {A B K : ℕ} (h : A ≤ B + K) :
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

private theorem pair_eq_iff_unordered_v12 {α : Type*} [DecidableEq α]
    {u v u₀ v₀ : α} (huv₀ : u₀ ≠ v₀) :
    ({u, v} : Finset α) = {u₀, v₀} ↔ (u = u₀ ∧ v = v₀) ∨ (u = v₀ ∧ v = u₀) := by
  constructor
  · intro heq
    have hu : u ∈ ({u₀, v₀} : Finset α) := heq ▸ Finset.mem_insert_self u {v}
    have hv : v ∈ ({u₀, v₀} : Finset α) :=
      heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self v)
    have hcard : ({u, v} : Finset α).card = 2 := by rw [heq, Finset.card_pair huv₀]
    have huv : u ≠ v := fun h ↦ by subst h; simp at hcard
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact (huv rfl).elim
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact (huv rfl).elim
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact Finset.pair_comm _ _

private theorem rg_coloring_inter_noCrossBipartite_eq_v12
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
  have hF_ok : ∀ e ∈ F, e.card = 2 ∧ ¬ ∃ B ∈ P.parts, e ⊆ B := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨⟨x, y⟩, hxy, rfl⟩
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
    refine ⟨Finset.card_pair (hne_xy x hx y hy), ?_⟩
    rintro ⟨B, hBP, hsub⟩
    exact hcross x hx y hy ⟨B, hBP, hsub (Finset.mem_insert_self x {y}),
      hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))⟩
  have hF_size : F.card = U₁.card * U₂.card := by
    rw [Finset.card_image_of_injOn, Finset.card_product]
    intro ⟨x₁, y₁⟩ h1 ⟨x₂, y₂⟩ h2 heq
    dsimp only at heq
    obtain ⟨hx₁, _⟩ := Finset.mem_product.mp h1
    obtain ⟨hx₂, hy₂⟩ := Finset.mem_product.mp h2
    rcases (pair_eq_iff_unordered_v12 (hne_xy x₂ hx₂ y₂ hy₂)).mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact (Finset.disjoint_left.mp hdisj hx₁ hy₂).elim
  have hset_eq :
      {G : LabeledGraph n | ∀ x ∈ U₁, ∀ y ∈ U₂, ¬ G.Adj x y} =
        {G : LabeledGraph n | ∀ u v : Fin n, ({u, v} : Finset (Fin n)) ∈ F → ¬ G.Adj u v} := by
    ext G
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h u v hmem
      rcases Finset.mem_image.mp hmem with ⟨⟨x, y⟩, hxy, heq⟩
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
      rcases (pair_eq_iff_unordered_v12 (hne_xy x hx y hy)).mp heq.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h u hx v hy
      · exact fun hadj ↦ h v hx u hy (G.adj_symm hadj)
    · intro h x hx y hy
      exact h x y (Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩)
  rw [hset_eq, ← hF_size]
  exact (randomGraphMeasure_partitionColoring_and_marked_inter_crossEvent_eq P).1 F hF_ok

private def badZComposedEvent_v12 {n : ℕ} (M : ℕ) (P : VertexPartition n) : Set (LabeledGraph n) :=
  {G | ∀ S : Finset (Fin n),
    G.IsIndepSet (S : Set (Fin n)) →
    phaseNat n - (M + 1) ≤ S.card →
    S.card ≤ phaseNat n →
    (P.parts.filter fun E ↦ (S ∩ E).Nonempty).card ≤ 2 ∨
      S.card ≤ (P.parts.filter fun E ↦ (S ∩ E).Nonempty).card +
        2 * (phaseNat n - S.card) + 1}

private def heavyCrossPairEvent_v12 {n : ℕ} (P : VertexPartition n) : Set (LabeledGraph n) :=
  {G | ∃ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) ∧
    ∃ A ∈ P.parts, ∃ B ∈ P.parts, A ≠ B ∧
      Nat.ceil (7 * logBaseTwo (n : ℝ)) ≤ (S ∩ A).card * (S ∩ B).card}

private def bad1Cell_v12 {n : ℕ} (B_star : Finset (Fin n)) (u r_out : ℕ) : Set (LabeledGraph n) :=
  ⋃ U_in ∈ B_star.powersetCard (u - r_out),
    ⋃ U_out ∈ ((Finset.univ : Finset (Fin n)) \ B_star).powersetCard r_out,
      {G : LabeledGraph n | ∀ x ∈ U_in, ∀ y ∈ U_out, ¬ G.Adj x y}

private def bad1Event_v12 {n : ℕ} (M R_max : ℕ) (P : VertexPartition n) : Set (LabeledGraph n) :=
  ⋃ B_star ∈ P.parts, ⋃ u ∈ Finset.Icc (phaseNat n - (M + 1)) (phaseNat n),
    ⋃ r_out ∈ Finset.Icc 2 R_max, bad1Cell_v12 B_star u r_out

private def hitParts_v12 {n : ℕ} (P : VertexPartition n) (Z : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  P.parts.filter fun B ↦ (Z ∩ B).Nonempty

private def transversalFinset_v12 {n : ℕ} (P : VertexPartition n) (z : ℕ) :
    Finset (Finset (Fin n)) :=
  ((Finset.univ : Finset (Fin n)).powersetCard z).filter
    fun Z ↦ (hitParts_v12 P Z).card = z

private def bad2Cell_v12 {n : ℕ} (P : VertexPartition n) (u z : ℕ) : Set (LabeledGraph n) :=
  ⋃ Z ∈ transversalFinset_v12 P z,
    ⋃ W ∈ (((hitParts_v12 P Z).biUnion id) \ Z).powersetCard (u - z),
      {G : LabeledGraph n |
        (∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → ¬ G.Adj x y) ∧
        (∀ x ∈ W, ∀ y ∈ Z, (¬ ∃ B ∈ P.parts, x ∈ B ∧ y ∈ B) → ¬ G.Adj x y)}

private def bad2Event_v12 {n : ℕ} (M z_cut : ℕ) (P : VertexPartition n) : Set (LabeledGraph n) :=
  ⋃ u ∈ Finset.Icc (phaseNat n - (M + 1)) (phaseNat n),
    ⋃ z ∈ Finset.Icc (z_cut + 1) (u - 2 * (phaseNat n - u) - 2),
      bad2Cell_v12 P u z

private theorem badZComposed_compl_subset_v12
    {n M z_cut : ℕ} (hn1 : 1 < n)
    (hL_M : ((60 * (M + 10) : ℕ) : ℝ) ≤ logOrder n)
    (hα_ge_2L : 2 * logOrder n ≤ (phaseNat n : ℝ))
    (P : VertexPartition n) :
    partitionColoringEvent P ∩ (badZComposedEvent_v12 M P)ᶜ ⊆
      (partitionColoringEvent P ∩ heavyCrossPairEvent_v12 P) ∪
        ((partitionColoringEvent P ∩ bad1Event_v12 M (12 * z_cut ^ 2) P) ∪
          (partitionColoringEvent P ∩ bad2Event_v12 M z_cut P)) := by
  classical
  have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL_pos : 0 < logOrder n := by
    have h1 : (1 : ℝ) ≤ ((60 * (M + 10) : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ 60 * (M + 10) by omega)
    linarith
  have hm_prod_le : (Nat.ceil (7 * logBaseTwo (n : ℝ)) : ℝ) ≤ 12 * logOrder n := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ 7 * logBaseTwo (n : ℝ) by
      unfold logBaseTwo; exact mul_nonneg (by norm_num) (div_nonneg hL_pos.le q_pos.le))
    have hlb : 7 * logBaseTwo (n : ℝ) ≤ 11 * logOrder n := by
      unfold logBaseTwo q
      change 7 * (logOrder n / Real.log 2) ≤ 11 * logOrder n
      rw [mul_div_assoc', div_le_iff₀ hq_pos]
      have h7 : (7 : ℝ) ≤ 11 * Real.log 2 := by linarith [Real.log_two_gt_d9]
      have hm := mul_le_mul_of_nonneg_right h7 hL_pos.le
      linarith [show (11 * Real.log 2) * logOrder n = 11 * logOrder n * Real.log 2 by ring]
    have hL1 : (1 : ℝ) ≤ logOrder n := by
      have : (60 : ℝ) ≤ ((60 * (M + 10) : ℕ) : ℝ) := by
        exact_mod_cast (show 60 ≤ 60 * (M + 10) by omega)
      linarith
    linarith
  intro G ⟨hGP, hnotB⟩
  by_cases hGE : G ∈ heavyCrossPairEvent_v12 P
  · exact Or.inl ⟨hGP, hGE⟩
  · right
    rw [Set.mem_compl_iff] at hnotB
    simp only [badZComposedEvent_v12, Set.mem_setOf_eq, not_forall, not_or, not_le] at hnotB
    rcases hnotB with ⟨S, hS_ind, hu_lo, hu_hi, hz_gt2, hz_small⟩
    set u : ℕ := S.card
    let Hit : Finset (Finset (Fin n)) := hitParts_v12 P S
    set z : ℕ := Hit.card
    have hz_eq : (P.parts.filter fun E ↦ (S ∩ E).Nonempty).card = z := rfl
    rw [hz_eq] at hz_gt2 hz_small
    have hz3 : 3 ≤ z := hz_gt2
    have hz_hi : z ≤ u - 2 * (phaseNat n - u) - 2 := by omega
    have hS_biUnion : Hit.biUnion (fun B ↦ S ∩ B) = S := by
      ext x
      simp only [Hit, hitParts_v12, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_inter]
      refine ⟨fun ⟨_, _, hxS, _⟩ ↦ hxS, fun hxS ↦ ?_⟩
      have hxU : x ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ x
      rw [← P.sup_parts, Finset.sup_eq_biUnion, Finset.mem_biUnion] at hxU
      rcases hxU with ⟨B, hBP, hxB⟩
      exact ⟨B, ⟨hBP, ⟨x, Finset.mem_inter.mpr ⟨hxS, hxB⟩⟩⟩, hxS, hxB⟩
    have hHit_disj : (Hit : Set (Finset (Fin n))).PairwiseDisjoint (fun B ↦ S ∩ B) :=
      fun A hA B hB hAB ↦
        (P.disjoint (Finset.mem_filter.mp hA).1 (Finset.mem_filter.mp hB).1 hAB).mono
          Finset.inter_subset_right Finset.inter_subset_right
    have hsum_Hit : ∑ B ∈ Hit, (S ∩ B).card = u := by
      rw [← Finset.card_biUnion hHit_disj, hS_biUnion]
    by_cases hzc : z ≤ z_cut
    · left
      refine ⟨hGP, ?_⟩
      have hHit_ne : Hit.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨B_star, hBs_Hit, hBs_max⟩ :=
        Finset.exists_max_image Hit (fun B ↦ (S ∩ B).card) hHit_ne
      obtain ⟨hBs_P, hSBs_ne⟩ := Finset.mem_filter.mp hBs_Hit
      have hu_le_z_max : u ≤ z * (S ∩ B_star).card := by
        calc u = ∑ B ∈ Hit, (S ∩ B).card := hsum_Hit.symm
          _ ≤ ∑ _B ∈ Hit, (S ∩ B_star).card := Finset.sum_le_sum fun B hB ↦ hBs_max B hB
          _ = z * (S ∩ B_star).card := by simp [z, Finset.sum_const, smul_eq_mul]
      have hu_ge_L : logOrder n ≤ (u : ℝ) := by
        have hM_le : ((M + 1 : ℕ) : ℝ) ≤ logOrder n := by push_cast at hL_M ⊢; linarith
        have h1 : (phaseNat n : ℝ) - ((M + 1 : ℕ) : ℝ) ≤ (u : ℝ) := by
          have := Nat.cast_le (α := ℝ).mpr hu_lo
          rw [Nat.cast_sub (by
            have : ((M + 1 : ℕ) : ℝ) ≤ (phaseNat n : ℝ) := by linarith
            exact_mod_cast this)] at this
          exact this
        linarith
      have hother_le : ∀ B ∈ Hit.erase B_star, (S ∩ B).card ≤ 12 * z_cut := by
        intro B hBe
        have hBne : B ≠ B_star := (Finset.mem_erase.mp hBe).1
        have hBP : B ∈ P.parts := (Finset.mem_filter.mp (Finset.mem_erase.mp hBe).2).1
        have hprod_lt : (S ∩ B_star).card * (S ∩ B).card < Nat.ceil (7 * logBaseTwo (n : ℝ)) := by
          by_contra hge
          exact hGE ⟨S, hS_ind, B_star, hBs_P, B, hBP, hBne.symm, not_lt.mp hge⟩
        have hBs_pos : (0 : ℝ) < ((S ∩ B_star).card : ℝ) := by exact_mod_cast hSBs_ne.card_pos
        have hreal_lt : ((S ∩ B).card : ℝ) < 12 * (z_cut : ℝ) + 1 := by
          have hp : ((S ∩ B_star).card : ℝ) * ((S ∩ B).card : ℝ) < 12 * logOrder n :=
            lt_of_lt_of_le (by exact_mod_cast hprod_lt) hm_prod_le
          have hLM : 12 * logOrder n ≤ 12 * (z : ℝ) * ((S ∩ B_star).card : ℝ) := by
            calc 12 * logOrder n ≤ 12 * (u : ℝ) := mul_le_mul_of_nonneg_left hu_ge_L (by norm_num)
              _ ≤ 12 * ((z : ℝ) * ((S ∩ B_star).card : ℝ)) :=
                  mul_le_mul_of_nonneg_left (by exact_mod_cast hu_le_z_max) (by norm_num)
              _ = 12 * (z : ℝ) * ((S ∩ B_star).card : ℝ) := by ring
          have hzc_r : (z : ℝ) ≤ (z_cut : ℝ) := by exact_mod_cast hzc
          have hlt1 : ((S ∩ B).card : ℝ) < 12 * (z : ℝ) := by nlinarith
          linarith
        exact Nat.lt_succ_iff.mp (by exact_mod_cast hreal_lt)
      set r_out : ℕ := (S \ B_star).card
      have hr_sum_eq : r_out = ∑ B ∈ Hit.erase B_star, (S ∩ B).card := by
        have hadd := Finset.add_sum_erase Hit (fun B ↦ (S ∩ B).card) hBs_Hit
        rw [hsum_Hit] at hadd
        have hsd := Finset.card_sdiff_add_card_inter S B_star
        dsimp [r_out, u] at hadd hsd ⊢
        omega
      have hr_ge2 : 2 ≤ r_out := by
        have hc_er : (Hit.erase B_star).card = z - 1 := Finset.card_erase_of_mem hBs_Hit
        have hge : ∑ _B ∈ Hit.erase B_star, 1 ≤ ∑ B ∈ Hit.erase B_star, (S ∩ B).card :=
          Finset.sum_le_sum fun B hBe ↦
            (Finset.mem_filter.mp (Finset.mem_erase.mp hBe).2).2.card_pos
        rw [Finset.sum_const, hc_er, smul_eq_mul, mul_one, ← hr_sum_eq] at hge
        omega
      have hr_le_max : r_out ≤ 12 * z_cut ^ 2 := by
        rw [hr_sum_eq]
        calc ∑ B ∈ Hit.erase B_star, (S ∩ B).card
            ≤ ∑ _B ∈ Hit.erase B_star, (12 * z_cut) := Finset.sum_le_sum hother_le
          _ = (Hit.erase B_star).card * (12 * z_cut) := by simp [Finset.sum_const, smul_eq_mul]
          _ ≤ z_cut * (12 * z_cut) :=
              Nat.mul_le_mul_right _ ((Finset.card_erase_le).trans hzc)
          _ = 12 * z_cut ^ 2 := by ring
      have hU_in_card : (S ∩ B_star).card = u - r_out := by
        have hsd := Finset.card_sdiff_add_card_inter S B_star
        dsimp [r_out, u] at hsd ⊢; omega
      simp only [bad1Event_v12, bad1Cell_v12, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
      refine ⟨B_star, hBs_P, u, Finset.mem_Icc.mpr ⟨hu_lo, hu_hi⟩,
        r_out, Finset.mem_Icc.mpr ⟨hr_ge2, hr_le_max⟩,
        S ∩ B_star, Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, hU_in_card⟩,
        S \ B_star, Finset.mem_powersetCard.mpr ⟨fun x hx ↦
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, (Finset.mem_sdiff.mp hx).2⟩, rfl⟩, ?_⟩
      intro x hx y hy
      have hxy : x ≠ y := fun heq ↦
        (Finset.mem_sdiff.mp hy).2 (heq ▸ (Finset.mem_inter.mp hx).2)
      exact hS_ind (Finset.mem_inter.mp hx).1 (Finset.mem_sdiff.mp hy).1 hxy
    · right
      refine ⟨hGP, ?_⟩
      have hzc1 : z_cut + 1 ≤ z := by omega
      let rep : Finset (Fin n) → Fin n := fun B ↦
        if h : (S ∩ B).Nonempty then (S ∩ B).min' h else ⟨0, by omega⟩
      have hrep_mem : ∀ B ∈ Hit, rep B ∈ S ∩ B := by
        intro B hB
        have hne := (Finset.mem_filter.mp hB).2
        simp only [rep, dif_pos hne]
        exact Finset.min'_mem (S ∩ B) hne
      let Z : Finset (Fin n) := Hit.image rep
      have hrep_inj : Set.InjOn rep (Hit : Set (Finset (Fin n))) := by
        intro A hA B hB heq
        have hxA := (Finset.mem_inter.mp (hrep_mem A hA)).2
        have hxB : rep A ∈ B := heq ▸ (Finset.mem_inter.mp (hrep_mem B hB)).2
        by_contra hne
        exact Finset.disjoint_left.mp
          (P.disjoint (Finset.mem_filter.mp hA).1 (Finset.mem_filter.mp hB).1 hne) hxA hxB
      have hZ_card : Z.card = z := Finset.card_image_of_injOn hrep_inj
      have hZ_sub_S : Z ⊆ S := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨B, hB, rfl⟩
        exact (Finset.mem_inter.mp (hrep_mem B hB)).1
      have hHitOf_Z : hitParts_v12 P Z = Hit := by
        ext B
        constructor
        · intro hBZ
          obtain ⟨hBP, x, hx⟩ := Finset.mem_filter.mp hBZ
          exact Finset.mem_filter.mpr ⟨hBP, x, Finset.mem_inter.mpr
            ⟨hZ_sub_S (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩⟩
        · intro hB
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hB).1, rep B,
            Finset.mem_inter.mpr
              ⟨Finset.mem_image_of_mem rep hB, (Finset.mem_inter.mp (hrep_mem B hB)).2⟩⟩
      have hZ_trans : Z ∈ transversalFinset_v12 P z :=
        Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ Z, hZ_card⟩,
          by rw [hHitOf_Z]⟩
      let W : Finset (Fin n) := S \ Z
      have hW_card : W.card = u - z := by rw [Finset.card_sdiff_of_subset hZ_sub_S, hZ_card]
      have hW_sub : W ⊆ ((hitParts_v12 P Z).biUnion id) \ Z := by
        intro x hx
        obtain ⟨hxS, hxnZ⟩ := Finset.mem_sdiff.mp hx
        rw [← hS_biUnion, ← hHitOf_Z] at hxS
        rcases Finset.mem_biUnion.mp hxS with ⟨B, hBH, hxSB⟩
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_biUnion.mpr ⟨B, hBH, (Finset.mem_inter.mp hxSB).2⟩, hxnZ⟩
      simp only [bad2Event_v12, bad2Cell_v12, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
      refine ⟨u, Finset.mem_Icc.mpr ⟨hu_lo, hu_hi⟩,
        z, Finset.mem_Icc.mpr ⟨hzc1, hz_hi⟩,
        Z, hZ_trans, W, Finset.mem_powersetCard.mpr ⟨hW_sub, hW_card⟩, ?_, ?_⟩
      · intro x hx y hy hxy
        exact hS_ind (hZ_sub_S hx) (hZ_sub_S hy) hxy
      · intro x hx y hy _hdiff
        have hxy : x ≠ y := fun heq ↦ (Finset.mem_sdiff.mp hx).2 (heq ▸ hy)
        exact hS_ind (Finset.mem_sdiff.mp hx).1 (hZ_sub_S hy) hxy

private theorem condProb_bad1Event_le_v12
    {n M : ℕ} {eps : ℝ}
    (hdom : PhaseDomain n)
    (hα_ge_2L : 2 * logOrder n ≤ (phaseNat n : ℝ))
    (hα_le_4L : (phaseNat n : ℝ) ≤ 4 * logOrder n)
    (hw64 : 64 ≤ logLogOrder n)
    (hw_M : ((4 * M + 20 : ℕ) : ℝ) ≤ logLogOrder n)
    (hL_M : ((60 * (M + 10) : ℕ) : ℝ) ≤ logOrder n)
    (hw5L : (logLogOrder n) ^ 5 ≤ (1 / 400) * logOrder n)
    (hExp1 : Real.exp (-(1 / 6 : ℝ) * logOrder n) ≤ eps / 4)
    (P : VertexPartition n) (hPa : ∀ B ∈ P.parts, B.card ≤ phaseNat n) :
    (randomGraphMeasure n).real
        (partitionColoringEvent P ∩ bad1Event_v12 M (12 * (Nat.floor ((logLogOrder n) ^ 2)) ^ 2) P) ≤
      (eps / 4) * (randomGraphMeasure n).real (partitionColoringEvent P) := by
  set α : ℕ := phaseNat n
  set L : ℝ := logOrder n
  set w : ℝ := logLogOrder n
  set z_cut : ℕ := Nat.floor (w ^ 2)
  set R_max : ℕ := 12 * z_cut ^ 2
  have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hw_pos : 0 < w := by linarith
  have hL_pos : 0 < L := by
    have : (1 : ℝ) ≤ ((60 * (M + 10) : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ 60 * (M + 10) by omega)
    linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_trans Nat.zero_lt_one hdom.1)
  have hL_log : Real.log (n : ℝ) = L := rfl
  have hw_log : Real.log L = w := rfl
  have hR_max_real : (R_max : ℝ) ≤ 12 * w ^ 4 := by
    have hz_le : (z_cut : ℝ) ≤ w ^ 2 := Nat.floor_le (sq_nonneg w)
    calc (R_max : ℝ) = 12 * (z_cut : ℝ) ^ 2 := by dsimp [R_max]; push_cast; ring
      _ ≤ 12 * (w ^ 2) ^ 2 := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Nat.cast_nonneg _) hz_le 2) (by norm_num)
      _ = 12 * w ^ 4 := by ring
  have hw4_L : 12 * w ^ 4 ≤ (3 / 6400 : ℝ) * L := by
    have : 12 * w ^ 4 * 64 ≤ 12 * w ^ 5 := by nlinarith [hw64, pow_pos hw_pos 4]
    linarith [hw5L]
  let Q_fac : ℝ := (2 : ℝ) ^ (M + 1 + R_max) * (4 / (Real.log 2) ^ 2) * L ^ 2 / (n : ℝ)
  have hQ_pos : 0 < Q_fac := by dsimp [Q_fac]; positivity
  have hQ_le_exp : Q_fac ≤ Real.exp (-(3 / 4 : ℝ) * L) := by
    have hlogQ : Real.log Q_fac ≤ -(3 / 4 : ℝ) * L := by
      dsimp only [Q_fac]
      rw [Real.log_div (by positivity) hn_pos.ne',
        Real.log_mul (by positivity) (sq_pos_of_pos hL_pos).ne',
        Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, hL_log, hw_log]
      have hlog_c : Real.log (4 / (Real.log 2) ^ 2) ≤ 10 := by
        have hle : 4 / (Real.log 2) ^ 2 ≤ Real.exp 10 := by
          have hq2 : (4 / 9 : ℝ) ≤ (Real.log 2) ^ 2 := by nlinarith [Real.log_two_gt_d9]
          have h9 : 4 / (Real.log 2) ^ 2 ≤ 9 := by
            rw [div_le_iff₀ (sq_pos_of_pos hq_pos)]; linarith
          have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
          have he10 : (2 : ℝ) ^ 10 ≤ (Real.exp 1) ^ 10 := pow_le_pow_left₀ (by norm_num) he1 10
          rw [← Real.exp_nat_mul] at he10
          norm_num at he10
          linarith
        exact (Real.log_le_log (by positivity) hle).trans_eq (Real.log_exp 10)
      have hq_le1 : Real.log 2 ≤ 1 := le_trans Real.log_two_lt_d9.le (by norm_num)
      have hm1 : ((M + 1 + R_max : ℕ) : ℝ) * Real.log 2 ≤ ((M + 1 : ℕ) : ℝ) + (R_max : ℝ) := by
        have := mul_le_mul_of_nonneg_left hq_le1 (Nat.cast_nonneg (M + 1 + R_max))
        push_cast at this ⊢; linarith
      have hw_L : 2 * w ≤ (1 / 32 : ℝ) * L := by
        have hp : (64 : ℝ) ^ 4 ≤ w ^ 4 := pow_le_pow_left₀ (by norm_num) hw64 4
        have : 2 * w * 64 ^ 4 ≤ 2 * w ^ 5 := by nlinarith [hw_pos]
        linarith [hw5L]
      push_cast at hm1 hL_M ⊢
      linarith [hm1, hR_max_real, hw4_L, hlog_c, hw_L]
    exact (Real.exp_log hQ_pos).symm.le.trans (Real.exp_le_exp.mpr hlogQ)
  have hQ_le1 : Q_fac ≤ 1 := hQ_le_exp.trans (Real.exp_le_one_iff.mpr (by linarith))
  have hcell1 : ∀ B_star ∈ P.parts, ∀ u ∈ Finset.Icc (α - (M + 1)) α, ∀ r_out ∈ Finset.Icc 2 R_max,
      (randomGraphMeasure n).real (partitionColoringEvent P ∩ bad1Cell_v12 B_star u r_out) ≤
        ((α : ℝ) ^ (M + 1 + R_max) * Real.exp (-(3 / 2 : ℝ) * L)) *
          (randomGraphMeasure n).real (partitionColoringEvent P) := by
    intro B_star hBs_P u hu r_out hr
    obtain ⟨hu_lo, _hu_hi⟩ := Finset.mem_Icc.mp hu
    obtain ⟨hr_lo, hr_hi⟩ := Finset.mem_Icc.mp hr
    by_cases hBs_ge : u - r_out ≤ B_star.card
    · have hpair_eq : ∀ U_in ∈ B_star.powersetCard (u - r_out),
          ∀ U_out ∈ ((Finset.univ : Finset (Fin n)) \ B_star).powersetCard r_out,
            (randomGraphMeasure n).real
                (partitionColoringEvent P ∩ {G | ∀ x ∈ U_in, ∀ y ∈ U_out, ¬ G.Adj x y}) =
              (1 / 2 : ℝ) ^ ((u - r_out) * r_out) *
                (randomGraphMeasure n).real (partitionColoringEvent P) := by
        intro U_in hU_in U_out hU_out
        obtain ⟨hU_in_sub, hU_in_c⟩ := Finset.mem_powersetCard.mp hU_in
        obtain ⟨hU_out_sub, hU_out_c⟩ := Finset.mem_powersetCard.mp hU_out
        have hdisj : Disjoint U_in U_out :=
          disjoint_sdiff_self_right.mono hU_in_sub hU_out_sub
        have hcross : ∀ x ∈ U_in, ∀ y ∈ U_out, ¬ ∃ D ∈ P.parts, x ∈ D ∧ y ∈ D := by
          rintro x hx y hy ⟨D, hDP, hxD, hyD⟩
          have hDB : D = B_star := by
            by_contra hne
            exact Finset.disjoint_left.mp (P.disjoint hDP hBs_P hne) hxD (hU_in_sub hx)
          subst hDB
          exact (Finset.mem_sdiff.mp (hU_out_sub hy)).2 hyD
        rw [← hU_in_c, ← hU_out_c]
        exact rg_coloring_inter_noCrossBipartite_eq_v12 P U_in U_out hdisj hcross
      have hid_int : partitionColoringEvent P ∩ bad1Cell_v12 B_star u r_out =
          ⋃ U_in ∈ B_star.powersetCard (u - r_out),
            ⋃ U_out ∈ ((Finset.univ : Finset (Fin n)) \ B_star).powersetCard r_out,
              (partitionColoringEvent P ∩ {G | ∀ x ∈ U_in, ∀ y ∈ U_out, ¬ G.Adj x y}) := by
        ext G; simp [bad1Cell_v12]
      have hunion :
          (randomGraphMeasure n).real (partitionColoringEvent P ∩ bad1Cell_v12 B_star u r_out) ≤
            (B_star.card.choose (u - r_out) : ℝ) *
              (((Finset.univ : Finset (Fin n)) \ B_star).card.choose r_out : ℝ) *
              (1 / 2 : ℝ) ^ ((u - r_out) * r_out) *
              (randomGraphMeasure n).real (partitionColoringEvent P) := by
        rw [hid_int]
        calc (randomGraphMeasure n).real _
            ≤ ∑ U_in ∈ B_star.powersetCard (u - r_out),
                ∑ U_out ∈ ((Finset.univ : Finset (Fin n)) \ B_star).powersetCard r_out,
                  (randomGraphMeasure n).real
                    (partitionColoringEvent P ∩ {G | ∀ x ∈ U_in, ∀ y ∈ U_out, ¬ G.Adj x y}) :=
              (rg_biUnion_finset_le_v12 _ _).trans
                (Finset.sum_le_sum fun _ _ ↦ rg_biUnion_finset_le_v12 _ _)
          _ = ∑ _U_in ∈ B_star.powersetCard (u - r_out),
                ∑ _U_out ∈ ((Finset.univ : Finset (Fin n)) \ B_star).powersetCard r_out,
                  ((1 / 2 : ℝ) ^ ((u - r_out) * r_out) *
                    (randomGraphMeasure n).real (partitionColoringEvent P)) :=
              Finset.sum_congr rfl fun U_in h1 ↦ Finset.sum_congr rfl fun U_out h2 ↦
                hpair_eq U_in h1 U_out h2
          _ = _ := by simp [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]; ring
      have hch_in : (B_star.card.choose (u - r_out) : ℝ) ≤ (α : ℝ) ^ (M + 1 + R_max) := by
        rw [← Nat.choose_symm hBs_ge]
        have hc1 := nat_choose_le_pow_v12 B_star.card (B_star.card - (u - r_out))
        have hB_le : B_star.card ≤ α := hPa B_star hBs_P
        have hexp_le : B_star.card - (u - r_out) ≤ M + 1 + R_max := by omega
        have hc2 : B_star.card ^ (B_star.card - (u - r_out)) ≤ α ^ (M + 1 + R_max) :=
          (Nat.pow_le_pow_left hB_le _).trans
            (Nat.pow_le_pow_right (show 0 < α by
              have : (0 : ℝ) < (α : ℝ) := by linarith [hα_ge_2L]
              exact_mod_cast this) hexp_le)
        exact_mod_cast hc1.trans hc2
      have hch_out : (((Finset.univ : Finset (Fin n)) \ B_star).card.choose r_out : ℝ) ≤
          (n : ℝ) ^ r_out := by
        have hc1 := nat_choose_le_pow_v12 ((Finset.univ : Finset (Fin n)) \ B_star).card r_out
        have hc2 : ((Finset.univ : Finset (Fin n)) \ B_star).card ≤ n :=
          (Finset.card_le_univ _).trans_eq (Finset.card_fin n)
        exact_mod_cast hc1.trans (Nat.pow_le_pow_left hc2 r_out)
      have hpow_each : (1 / 2 : ℝ) ^ (u - r_out) ≤
          (2 : ℝ) ^ (M + 1 + R_max) *
            ((4 / (Real.log 2) ^ 2) * L ^ 2 / (n : ℝ) ^ 2) := by
        have h1 := half_pow_le_two_pow_mul_half_pow_v12
          (show α ≤ (u - r_out) + (M + 1 + R_max) by omega)
        exact h1.trans (mul_le_mul_of_nonneg_left (half_pow_phaseNat_le_v12 hdom) (by positivity))
      have hQ_r : (n : ℝ) ^ r_out * (1 / 2 : ℝ) ^ ((u - r_out) * r_out) ≤
          Real.exp (-(3 / 2 : ℝ) * L) := by
        rw [pow_mul (1 / 2 : ℝ) (u - r_out) r_out, ← mul_pow]
        have hbase : (n : ℝ) * (1 / 2 : ℝ) ^ (u - r_out) ≤ Q_fac := by
          calc (n : ℝ) * (1 / 2 : ℝ) ^ (u - r_out)
              ≤ (n : ℝ) * ((2 : ℝ) ^ (M + 1 + R_max) *
                  ((4 / (Real.log 2) ^ 2) * L ^ 2 / (n : ℝ) ^ 2)) :=
                mul_le_mul_of_nonneg_left hpow_each hn_pos.le
            _ = Q_fac := by dsimp [Q_fac]; field_simp [hn_pos.ne']
        calc ((n : ℝ) * (1 / 2 : ℝ) ^ (u - r_out)) ^ r_out
            ≤ Q_fac ^ r_out := pow_le_pow_left₀ (by positivity) hbase r_out
          _ ≤ Q_fac ^ 2 := pow_le_pow_of_le_one hQ_pos.le hQ_le1 hr_lo
          _ ≤ (Real.exp (-(3 / 4 : ℝ) * L)) ^ 2 := pow_le_pow_left₀ hQ_pos.le hQ_le_exp 2
          _ = Real.exp (-(3 / 2 : ℝ) * L) := by
              rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      refine hunion.trans ?_
      have hprod_in :
          (B_star.card.choose (u - r_out) : ℝ) *
              (((Finset.univ : Finset (Fin n)) \ B_star).card.choose r_out : ℝ) *
              (1 / 2 : ℝ) ^ ((u - r_out) * r_out) ≤
            (α : ℝ) ^ (M + 1 + R_max) * Real.exp (-(3 / 2 : ℝ) * L) := by
        calc (B_star.card.choose (u - r_out) : ℝ) *
                (((Finset.univ : Finset (Fin n)) \ B_star).card.choose r_out : ℝ) *
                (1 / 2 : ℝ) ^ ((u - r_out) * r_out)
            ≤ (α : ℝ) ^ (M + 1 + R_max) *
                ((n : ℝ) ^ r_out * (1 / 2 : ℝ) ^ ((u - r_out) * r_out)) := by
              have := mul_le_mul hch_in hch_out (Nat.cast_nonneg _) (by positivity)
              have hm := mul_le_mul_of_nonneg_right this
                (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ ((u - r_out) * r_out))
              linarith [show (α : ℝ) ^ (M + 1 + R_max) * (n : ℝ) ^ r_out *
                  (1 / 2 : ℝ) ^ ((u - r_out) * r_out) =
                (α : ℝ) ^ (M + 1 + R_max) *
                  ((n : ℝ) ^ r_out * (1 / 2 : ℝ) ^ ((u - r_out) * r_out)) by ring]
          _ ≤ (α : ℝ) ^ (M + 1 + R_max) * Real.exp (-(3 / 2 : ℝ) * L) :=
              mul_le_mul_of_nonneg_left hQ_r (by positivity)
      exact mul_le_mul_of_nonneg_right hprod_in measureReal_nonneg
    · have hempty : B_star.powersetCard (u - r_out) = ∅ :=
        Finset.powersetCard_eq_empty.mpr (not_le.mp hBs_ge)
      have hcell_empty : bad1Cell_v12 B_star u r_out = ∅ := by simp [bad1Cell_v12, hempty]
      rw [hcell_empty, Set.inter_empty, measureReal_empty]
      positivity
  have hsum1 :
      (randomGraphMeasure n).real (partitionColoringEvent P ∩ bad1Event_v12 M R_max P) ≤
        ((n : ℝ) * ((M + 2 : ℕ) : ℝ) * ((R_max + 1 : ℕ) : ℝ) *
          (α : ℝ) ^ (M + 1 + R_max) * Real.exp (-(3 / 2 : ℝ) * L)) *
          (randomGraphMeasure n).real (partitionColoringEvent P) := by
    have hid1 : partitionColoringEvent P ∩ bad1Event_v12 M R_max P =
        ⋃ B_star ∈ P.parts, ⋃ u ∈ Finset.Icc (α - (M + 1)) α, ⋃ r_out ∈ Finset.Icc 2 R_max,
          (partitionColoringEvent P ∩ bad1Cell_v12 B_star u r_out) := by
      ext G; simp [bad1Event_v12, α]
    rw [hid1]
    let Z0 : ℝ := ((α : ℝ) ^ (M + 1 + R_max) * Real.exp (-(3 / 2 : ℝ) * L)) *
      (randomGraphMeasure n).real (partitionColoringEvent P)
    have hZ0_nn : 0 ≤ Z0 := by dsimp [Z0]; positivity
    calc (randomGraphMeasure n).real _
        ≤ ∑ B_star ∈ P.parts, ∑ u ∈ Finset.Icc (α - (M + 1)) α, ∑ r_out ∈ Finset.Icc 2 R_max,
            (randomGraphMeasure n).real (partitionColoringEvent P ∩ bad1Cell_v12 B_star u r_out) := by
          refine (rg_biUnion_finset_le_v12 _ _).trans (Finset.sum_le_sum fun _ _ ↦ ?_)
          exact (rg_biUnion_finset_le_v12 _ _).trans
            (Finset.sum_le_sum fun _ _ ↦ rg_biUnion_finset_le_v12 _ _)
      _ ≤ ∑ _B_star ∈ P.parts, ∑ _u ∈ Finset.Icc (α - (M + 1)) α, ∑ _r_out ∈ Finset.Icc 2 R_max,
            Z0 :=
          Finset.sum_le_sum fun B_star hB ↦ Finset.sum_le_sum fun u hu ↦
            Finset.sum_le_sum fun r_out hr ↦ hcell1 B_star hB u hu r_out hr
      _ ≤ _ := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          have hcP : (P.parts.card : ℝ) ≤ (n : ℝ) :=
            by exact_mod_cast vertexPartition_parts_card_le_v12 P
          have hcu : ((Finset.Icc (α - (M + 1)) α).card : ℝ) ≤ ((M + 2 : ℕ) : ℝ) := by
            rw [Nat.card_Icc]; exact_mod_cast (show α + 1 - (α - (M + 1)) ≤ M + 2 by omega)
          have hcr : ((Finset.Icc 2 R_max).card : ℝ) ≤ ((R_max + 1 : ℕ) : ℝ) := by
            rw [Nat.card_Icc]; exact_mod_cast (show R_max + 1 - 2 ≤ R_max + 1 by omega)
          calc (P.parts.card : ℝ) *
                  (((Finset.Icc (α - (M + 1)) α).card : ℝ) *
                    (((Finset.Icc 2 R_max).card : ℝ) * Z0))
              ≤ (n : ℝ) * (((M + 2 : ℕ) : ℝ) * (((R_max + 1 : ℕ) : ℝ) * Z0)) := by
                refine mul_le_mul hcP (mul_le_mul hcu (mul_le_mul_of_nonneg_right hcr hZ0_nn)
                  (by positivity) (by positivity)) (by positivity) hn_pos.le
            _ = _ := by dsimp [Z0]; ring
  have hpref_le :
      (n : ℝ) * ((M + 2 : ℕ) : ℝ) * ((R_max + 1 : ℕ) : ℝ) *
        (α : ℝ) ^ (M + 1 + R_max) * Real.exp (-(3 / 2 : ℝ) * L) ≤ eps / 4 := by
    have hα_pos : (0 : ℝ) < (α : ℝ) := lt_of_lt_of_le (by positivity) hα_ge_2L
    have hα_ge1 : (1 : ℝ) ≤ (α : ℝ) := by
      have : (60 : ℝ) ≤ ((60 * (M + 10) : ℕ) : ℝ) := by
        exact_mod_cast (show 60 ≤ 60 * (M + 10) by omega)
      linarith [hL_M, hα_ge_2L]
    have hlog_α : Real.log (α : ℝ) ≤ 2 + w := by
      have hl4 : Real.log 4 ≤ 2 := by
        have h4e : (4 : ℝ) ≤ Real.exp 2 := by
          have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
          have he2 : (2 : ℝ) ^ 2 ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) he1 2
          rw [← Real.exp_nat_mul] at he2; norm_num at he2; exact he2
        exact (Real.log_le_log (by norm_num) h4e).trans_eq (Real.log_exp 2)
      calc Real.log (α : ℝ) ≤ Real.log (4 * L) := Real.log_le_log hα_pos hα_le_4L
        _ = Real.log 4 + Real.log L := Real.log_mul (by norm_num) hL_pos.ne'
        _ ≤ 2 + w := by linarith [hw_log]
    have hα_pow_exp : (α : ℝ) ^ (M + 1 + R_max) ≤ Real.exp ((1 / 6 : ℝ) * L) := by
      rw [← Real.exp_log hα_pos, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have h1 : ((M + 1 + R_max : ℕ) : ℝ) * Real.log (α : ℝ) ≤
          (((M + 1 : ℕ) : ℝ) + 12 * w ^ 4) * (2 + w) :=
        mul_le_mul (by push_cast; linarith [hR_max_real]) hlog_α
          (Real.log_nonneg hα_ge1) (by positivity)
      have h2 : (((M + 1 : ℕ) : ℝ) + 12 * w ^ 4) * (2 + w) ≤ (1 / 6 : ℝ) * L := by
        have hM_w : ((M + 1 : ℕ) : ℝ) ≤ w := by push_cast at hw_M ⊢; linarith
        have hw15 : w ≤ w ^ 5 := by
          simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ w) (by omega : 1 ≤ 5)
        have hw25 : w ^ 2 ≤ w ^ 5 := pow_le_pow_right₀ (by linarith : 1 ≤ w) (by omega : 2 ≤ 5)
        have h24w4 : 24 * w ^ 4 ≤ w ^ 5 := by
          calc 24 * w ^ 4 ≤ w * w ^ 4 :=
                mul_le_mul_of_nonneg_right (by linarith [hw64]) (by positivity)
            _ = w ^ 5 := by ring
        have hm_exp : (((M + 1 : ℕ) : ℝ) + 12 * w ^ 4) * (2 + w) ≤
            (w + 12 * w ^ 4) * (2 + w) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        have hring_w : (w + 12 * w ^ 4) * (2 + w) = 2 * w + w ^ 2 + 24 * w ^ 4 + 12 * w ^ 5 := by ring
        linarith [hw5L]
      exact h1.trans h2
    have hMR_poly : ((M + 2 : ℕ) : ℝ) * ((R_max + 1 : ℕ) : ℝ) ≤ Real.exp ((1 / 6 : ℝ) * L) := by
      have h1 : ((M + 2 : ℕ) : ℝ) * ((R_max + 1 : ℕ) : ℝ) ≤ (1 / 6 : ℝ) * L := by
        have hM_w : ((M + 2 : ℕ) : ℝ) ≤ w := by push_cast at hw_M ⊢; linarith
        have h1_w4 : (1 : ℝ) ≤ w ^ 4 := one_le_pow₀ (by linarith : 1 ≤ w)
        have hR1 : ((R_max + 1 : ℕ) : ℝ) ≤ 13 * w ^ 4 := by
          push_cast; linarith [hR_max_real, h1_w4]
        have hm : ((M + 2 : ℕ) : ℝ) * ((R_max + 1 : ℕ) : ℝ) ≤ 13 * w ^ 5 := by
          calc ((M + 2 : ℕ) : ℝ) * ((R_max + 1 : ℕ) : ℝ) ≤ w * (13 * w ^ 4) :=
                mul_le_mul hM_w hR1 (by positivity) hw_pos.le
            _ = 13 * w ^ 5 := by ring
        linarith [hw5L]
      exact h1.trans ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _))
    have hn_exp : (n : ℝ) = Real.exp L := (Real.exp_log hn_pos).symm
    calc (n : ℝ) * ((M + 2 : ℕ) : ℝ) * ((R_max + 1 : ℕ) : ℝ) *
            (α : ℝ) ^ (M + 1 + R_max) * Real.exp (-(3 / 2 : ℝ) * L)
        = Real.exp L * (((M + 2 : ℕ) : ℝ) * ((R_max + 1 : ℕ) : ℝ)) *
            (α : ℝ) ^ (M + 1 + R_max) * Real.exp (-(3 / 2 : ℝ) * L) := by rw [hn_exp]; ring
      _ ≤ Real.exp L * Real.exp ((1 / 6 : ℝ) * L) * Real.exp ((1 / 6 : ℝ) * L) *
            Real.exp (-(3 / 2 : ℝ) * L) := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul (mul_le_mul_of_nonneg_left hMR_poly (Real.exp_pos L).le)
              hα_pow_exp (by positivity) (by positivity))
            (Real.exp_pos _).le
      _ = Real.exp (-(1 / 6 : ℝ) * L) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ eps / 4 := hExp1
  exact hsum1.trans (mul_le_mul_of_nonneg_right hpref_le measureReal_nonneg)

private theorem bad2Cell_measureReal_le_v12
    {n M u z : ℕ} (P : VertexPartition n)
    (hPa : ∀ B ∈ P.parts, B.card ≤ phaseNat n)
    (hα_pos : 0 < phaseNat n)
    (hu_lo : phaseNat n - (M + 1) ≤ u) (hu_hi : u ≤ phaseNat n)
    (hz3 : 3 ≤ z) (hz_hi : z ≤ u - 2 * (phaseNat n - u) - 2) :
    (randomGraphMeasure n).real (partitionColoringEvent P ∩ bad2Cell_v12 P u z) ≤
      ((n.choose z : ℝ) * (2 : ℝ) ^ (-(((z : ℝ) - 1) * ((u : ℝ) - (z : ℝ) / 2))) *
        (phaseNat n : ℝ) ^ (4 * M + 4 + 2 * (u - 2 * (phaseNat n - u) - z))) *
        (randomGraphMeasure n).real (partitionColoringEvent P) := by
  classical
  let α : ℕ := phaseNat n
  let d_nat : ℕ := u - 2 * (α - u) - z
  have hZW_prob : ∀ Z ∈ transversalFinset_v12 P z,
      ∀ W ∈ (((hitParts_v12 P Z).biUnion id) \ Z).powersetCard (u - z),
        (randomGraphMeasure n).real
            (partitionColoringEvent P ∩
              {G : LabeledGraph n |
                (∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → ¬ G.Adj x y) ∧
                (∀ x ∈ W, ∀ y ∈ Z, (¬ ∃ B ∈ P.parts, x ∈ B ∧ y ∈ B) → ¬ G.Adj x y)}) ≤
          (2 : ℝ) ^ (-(((z : ℝ) - 1) * ((u : ℝ) - (z : ℝ) / 2))) *
            (randomGraphMeasure n).real (partitionColoringEvent P) := by
    intro Z hZ W hW
    obtain ⟨hZ_pc, hHitZ_card⟩ := Finset.mem_filter.mp hZ
    have hZ_card : Z.card = z := (Finset.mem_powersetCard.mp hZ_pc).2
    obtain ⟨hW_sub, hW_card⟩ := Finset.mem_powersetCard.mp hW
    have hZ_bi : (hitParts_v12 P Z).biUnion (fun B ↦ Z ∩ B) = Z := by
      ext x
      simp only [hitParts_v12, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_inter]
      refine ⟨fun ⟨_, _, hxZ, _⟩ ↦ hxZ, fun hxZ ↦ ?_⟩
      have hxU : x ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ x
      rw [← P.sup_parts, Finset.sup_eq_biUnion, Finset.mem_biUnion] at hxU
      rcases hxU with ⟨B, hBP, hxB⟩
      exact ⟨B, ⟨hBP, ⟨x, Finset.mem_inter.mpr ⟨hxZ, hxB⟩⟩⟩, hxZ, hxB⟩
    have hZ_disj : (hitParts_v12 P Z : Set (Finset (Fin n))).PairwiseDisjoint (fun B ↦ Z ∩ B) :=
      fun A hA B hB hAB ↦
        (P.disjoint (Finset.mem_filter.mp hA).1 (Finset.mem_filter.mp hB).1 hAB).mono
          Finset.inter_subset_right Finset.inter_subset_right
    have hsum_Z : ∑ B ∈ hitParts_v12 P Z, (Z ∩ B).card = z := by
      rw [← Finset.card_biUnion hZ_disj, hZ_bi, hZ_card]
    have hZB_one : ∀ B ∈ hitParts_v12 P Z, (Z ∩ B).card = 1 := by
      have hge1 : ∀ B ∈ hitParts_v12 P Z, 1 ≤ (Z ∩ B).card :=
        fun B hB ↦ (Finset.mem_filter.mp hB).2.card_pos
      have hsum_lb : ∑ _B ∈ hitParts_v12 P Z, 1 = z := by
        simp [Finset.sum_const, hHitZ_card, smul_eq_mul]
      intro B₀ hB₀
      by_contra hne1
      have hgt1 : 1 < (Z ∩ B₀).card := lt_of_le_of_ne (hge1 B₀ hB₀) (Ne.symm hne1)
      have hlt_sum : ∑ _B ∈ hitParts_v12 P Z, 1 < ∑ B ∈ hitParts_v12 P Z, (Z ∩ B).card :=
        Finset.sum_lt_sum hge1 ⟨B₀, hB₀, hgt1⟩
      omega
    let F₁ : Finset (Finset (Fin n)) := Z.powersetCard 2
    let Pairs₂ : Finset (Fin n × Fin n) :=
      (W ×ˢ Z).filter fun p ↦ ¬ ∃ B ∈ P.parts, p.1 ∈ B ∧ p.2 ∈ B
    let F₂ : Finset (Finset (Fin n)) := Pairs₂.image fun p ↦ ({p.1, p.2} : Finset (Fin n))
    have hWZ_disj : Disjoint W Z := disjoint_sdiff_self_left.mono_left hW_sub
    have hF₁_ok : ∀ e ∈ F₁, e.card = 2 ∧ ¬ ∃ B ∈ P.parts, e ⊆ B := by
      intro e he
      obtain ⟨he_sub, he_c⟩ := Finset.mem_powersetCard.mp he
      refine ⟨he_c, ?_⟩
      rintro ⟨B, hBP, heB⟩
      obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp he_c
      have hxB : x ∈ Z ∩ B := Finset.mem_inter.mpr
        ⟨he_sub (Finset.mem_insert_self x {y}), heB (Finset.mem_insert_self x {y})⟩
      have hyB : y ∈ Z ∩ B := Finset.mem_inter.mpr
        ⟨he_sub (Finset.mem_insert_of_mem (Finset.mem_singleton_self y)),
          heB (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))⟩
      have hBH : B ∈ hitParts_v12 P Z := Finset.mem_filter.mpr ⟨hBP, ⟨x, hxB⟩⟩
      have hc2 : 2 ≤ (Z ∩ B).card := by
        rw [← Finset.card_pair hxy]
        exact Finset.card_le_card fun v hv ↦ by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl <;> assumption
      have hc1 := hZB_one B hBH
      omega
    have hF₂_ok : ∀ e ∈ F₂, e.card = 2 ∧ ¬ ∃ B ∈ P.parts, e ⊆ B := by
      intro e he
      rcases Finset.mem_image.mp he with ⟨⟨x, y⟩, hp, rfl⟩
      obtain ⟨hxy_pr, hnotB⟩ := Finset.mem_filter.mp hp
      obtain ⟨hxW, hyZ⟩ := Finset.mem_product.mp hxy_pr
      have hxy : x ≠ y := fun heq ↦ Finset.disjoint_left.mp hWZ_disj hxW (heq ▸ hyZ)
      refine ⟨Finset.card_pair hxy, ?_⟩
      rintro ⟨B, hBP, hsub⟩
      exact hnotB ⟨B, hBP, hsub (Finset.mem_insert_self x {y}),
        hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))⟩
    have hF_disj : Disjoint F₁ F₂ := by
      rw [Finset.disjoint_left]
      intro e he₁ he₂
      have heZ := (Finset.mem_powersetCard.mp he₁).1
      rcases Finset.mem_image.mp he₂ with ⟨⟨x, _⟩, hp, rfl⟩
      have hxW := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
      exact Finset.disjoint_left.mp hWZ_disj hxW (heZ (Finset.mem_insert_self x _))
    have hF₂_card : F₂.card = (u - z) * (z - 1) := by
      have hinj : Set.InjOn (fun p : Fin n × Fin n ↦ ({p.1, p.2} : Finset (Fin n)))
          (Pairs₂ : Set (Fin n × Fin n)) := by
        intro ⟨x₁, y₁⟩ h1 ⟨x₂, y₂⟩ h2 heq
        dsimp only at heq
        obtain ⟨hx₁W, _⟩ := Finset.mem_product.mp (Finset.mem_filter.mp h1).1
        obtain ⟨hx₂W, hy₂Z⟩ := Finset.mem_product.mp (Finset.mem_filter.mp h2).1
        have hne₂ : x₂ ≠ y₂ := fun h ↦ Finset.disjoint_left.mp hWZ_disj hx₂W (h ▸ hy₂Z)
        rcases (pair_eq_iff_unordered_v12 hne₂).mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact (Finset.disjoint_left.mp hWZ_disj hx₁W hy₂Z).elim
      rw [Finset.card_image_of_injOn hinj]
      have hfib : ∀ x ∈ W,
          (Z.filter fun y ↦ ¬ ∃ B ∈ P.parts, x ∈ B ∧ y ∈ B).card = z - 1 := by
        intro x hxW
        have hx_bi := (Finset.mem_sdiff.mp (hW_sub hxW)).1
        rw [Finset.mem_biUnion] at hx_bi
        rcases hx_bi with ⟨B_x, hBx_H, hxBx⟩
        have hBx_P : B_x ∈ P.parts := (Finset.mem_filter.mp hBx_H).1
        have hfilt_eq : (Z.filter fun y ↦ ¬ ∃ B ∈ P.parts, x ∈ B ∧ y ∈ B) =
            Z \ (Z ∩ B_x) := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_inter]
          refine ⟨fun ⟨hyZ, hno⟩ ↦ ⟨hyZ, fun ⟨_, hyBx⟩ ↦ hno ⟨B_x, hBx_P, hxBx, hyBx⟩⟩,
            fun ⟨hyZ, hnot⟩ ↦ ⟨hyZ, ?_⟩⟩
          rintro ⟨B, hBP, hxB, hyB⟩
          have hBBx : B = B_x := by
            by_contra hne
            exact Finset.disjoint_left.mp (P.disjoint hBP hBx_P hne) hxB hxBx
          subst hBBx
          exact hnot ⟨hyZ, hyB⟩
        rw [hfilt_eq, Finset.card_sdiff_of_subset Finset.inter_subset_left,
          hZ_card, hZB_one B_x hBx_H]
      have hp2_eq : Pairs₂ = W.biUnion fun x ↦
          (Z.filter fun y ↦ ¬ ∃ B ∈ P.parts, x ∈ B ∧ y ∈ B).image (fun y ↦ (x, y)) := by
        ext ⟨x, y⟩; simp [Pairs₂, and_assoc]
      rw [hp2_eq, Finset.card_biUnion]
      · have hper : ∀ x ∈ W,
            ((Z.filter fun y ↦ ¬ ∃ B ∈ P.parts, x ∈ B ∧ y ∈ B).image (fun y ↦ (x, y))).card =
              z - 1 := by
          intro x hxW
          rw [Finset.card_image_of_injective _ (fun _ _ h ↦ (Prod.mk.inj h).2), hfib x hxW]
        rw [Finset.sum_congr rfl hper, Finset.sum_const, hW_card, smul_eq_mul]
      · intro x₁ _ x₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro p hp₁ hp₂
        rcases Finset.mem_image.mp hp₁ with ⟨_, _, rfl⟩
        rcases Finset.mem_image.mp hp₂ with ⟨_, _, heq⟩
        exact hne (Prod.mk.inj heq).1.symm
    let F : Finset (Finset (Fin n)) := F₁ ∪ F₂
    have hF_card : F.card = z.choose 2 + (u - z) * (z - 1) := by
      rw [Finset.card_union_of_disjoint hF_disj, Finset.card_powersetCard, hZ_card, hF₂_card]
    have hF_ok : ∀ e ∈ F, e.card = 2 ∧ ¬ ∃ B ∈ P.parts, e ⊆ B := by
      intro e he
      rcases Finset.mem_union.mp he with h1 | h2
      · exact hF₁_ok e h1
      · exact hF₂_ok e h2
    have hsub_ev :
        {G : LabeledGraph n |
          (∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → ¬ G.Adj x y) ∧
          (∀ x ∈ W, ∀ y ∈ Z, (¬ ∃ B ∈ P.parts, x ∈ B ∧ y ∈ B) → ¬ G.Adj x y)} ⊆
        {G : LabeledGraph n | ∀ x y : Fin n, ({x, y} : Finset (Fin n)) ∈ F → ¬ G.Adj x y} := by
      intro G ⟨hZZ, hWZ⟩ x y hmem
      rcases Finset.mem_union.mp hmem with hm1 | hm2
      · obtain ⟨hsub, hc2⟩ := Finset.mem_powersetCard.mp hm1
        have hxy : x ≠ y := fun h ↦ by subst h; simp at hc2
        exact hZZ x (hsub (Finset.mem_insert_self x {y}))
          y (hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))) hxy
      · rcases Finset.mem_image.mp hm2 with ⟨⟨w₀, y₀⟩, hp, heq⟩
        obtain ⟨hwy_pr, hnoB⟩ := Finset.mem_filter.mp hp
        obtain ⟨hwW, hyZ⟩ := Finset.mem_product.mp hwy_pr
        have hwy : w₀ ≠ y₀ := fun h ↦ Finset.disjoint_left.mp hWZ_disj hwW (h ▸ hyZ)
        rcases (pair_eq_iff_unordered_v12 hwy).mp heq.symm with ⟨hxw, hyy⟩ | ⟨hxy, hyw⟩
        · rw [hxw, hyy]; exact hWZ w₀ hwW y₀ hyZ hnoB
        · rw [hxy, hyw]; exact fun hadj ↦ hWZ w₀ hwW y₀ hyZ hnoB (G.adj_symm hadj)
    have hprob_F := (randomGraphMeasure_partitionColoring_and_marked_inter_crossEvent_eq P).1 F hF_ok
    have hpow_eq : (1 / 2 : ℝ) ^ F.card =
        (2 : ℝ) ^ (-(((z : ℝ) - 1) * ((u : ℝ) - (z : ℝ) / 2))) := by
      rw [hF_card, one_div, inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg two_pos.le]
      congr 1
      push_cast
      rw [Nat.cast_choose_two ℝ z, Nat.cast_sub (by omega : z ≤ u),
        Nat.cast_sub (by omega : 1 ≤ z), Nat.cast_one]
      ring
    calc (randomGraphMeasure n).real _
        ≤ (randomGraphMeasure n).real
            (partitionColoringEvent P ∩
              {G | ∀ x y : Fin n, ({x, y} : Finset (Fin n)) ∈ F → ¬ G.Adj x y}) :=
          rg_mono_v12 (Set.inter_subset_inter_right _ hsub_ev)
      _ = (2 : ℝ) ^ (-(((z : ℝ) - 1) * ((u : ℝ) - (z : ℝ) / 2))) *
            (randomGraphMeasure n).real (partitionColoringEvent P) := by
          rw [hprob_F, hpow_eq]
  have hW_choices : ∀ Z ∈ transversalFinset_v12 P z,
      ((((hitParts_v12 P Z).biUnion id) \ Z).powersetCard (u - z)).card ≤
        α ^ (4 * M + 4 + 2 * d_nat) := by
    intro Z hZ
    have hHit_c : (hitParts_v12 P Z).card = z := (Finset.mem_filter.mp hZ).2
    have hbi_c : ((hitParts_v12 P Z).biUnion id).card ≤ α ^ 2 := by
      calc ((hitParts_v12 P Z).biUnion id).card
          ≤ ∑ B ∈ hitParts_v12 P Z, B.card := Finset.card_biUnion_le
        _ ≤ ∑ _B ∈ hitParts_v12 P Z, α :=
            Finset.sum_le_sum fun B hB ↦ hPa B (Finset.mem_filter.mp hB).1
        _ = z * α := by simp [Finset.sum_const, hHit_c, smul_eq_mul]
        _ ≤ α ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right α (by dsimp [α] at *; omega)
    have hsd_c : (((hitParts_v12 P Z).biUnion id) \ Z).card ≤ α ^ 2 :=
      (Finset.card_le_card Finset.sdiff_subset).trans hbi_c
    rw [Finset.card_powersetCard]
    calc (((hitParts_v12 P Z).biUnion id) \ Z).card.choose (u - z)
        ≤ (α ^ 2).choose (u - z) := Nat.choose_le_choose (u - z) hsd_c
      _ ≤ (α ^ 2) ^ (u - z) := nat_choose_le_pow_v12 _ _
      _ = α ^ (2 * (u - z)) := (pow_mul α 2 (u - z)).symm
      _ ≤ α ^ (4 * M + 4 + 2 * d_nat) :=
          Nat.pow_le_pow_right hα_pos (by dsimp [α, d_nat] at *; omega)
  have hZ_choices : (transversalFinset_v12 P z).card ≤ n.choose z :=
    (Finset.card_filter_le _ _).trans_eq (by simp [Finset.card_powersetCard])
  have hid2 : partitionColoringEvent P ∩ bad2Cell_v12 P u z =
      ⋃ Z ∈ transversalFinset_v12 P z,
        ⋃ W ∈ (((hitParts_v12 P Z).biUnion id) \ Z).powersetCard (u - z),
          (partitionColoringEvent P ∩
            {G : LabeledGraph n |
              (∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → ¬ G.Adj x y) ∧
              (∀ x ∈ W, ∀ y ∈ Z, (¬ ∃ B ∈ P.parts, x ∈ B ∧ y ∈ B) → ¬ G.Adj x y)}) := by
    ext G; simp [bad2Cell_v12]
  rw [hid2]
  let p_zw : ℝ := (2 : ℝ) ^ (-(((z : ℝ) - 1) * ((u : ℝ) - (z : ℝ) / 2))) *
    (randomGraphMeasure n).real (partitionColoringEvent P)
  have hp_nn : 0 ≤ p_zw := by dsimp [p_zw]; positivity
  calc (randomGraphMeasure n).real _
      ≤ ∑ Z ∈ transversalFinset_v12 P z,
          ∑ _W ∈ (((hitParts_v12 P Z).biUnion id) \ Z).powersetCard (u - z), p_zw := by
        refine (rg_biUnion_finset_le_v12 _ _).trans (Finset.sum_le_sum fun Z hZ ↦ ?_)
        exact (rg_biUnion_finset_le_v12 _ _).trans
          (Finset.sum_le_sum fun W hW ↦ hZW_prob Z hZ W hW)
    _ ≤ ∑ _Z ∈ transversalFinset_v12 P z, ((α : ℝ) ^ (4 * M + 4 + 2 * d_nat) * p_zw) := by
        refine Finset.sum_le_sum fun Z hZ ↦ ?_
        simp only [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hW_choices Z hZ) hp_nn
    _ ≤ _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        calc ((transversalFinset_v12 P z).card : ℝ) *
                ((α : ℝ) ^ (4 * M + 4 + 2 * d_nat) * p_zw)
            ≤ (n.choose z : ℝ) * ((α : ℝ) ^ (4 * M + 4 + 2 * d_nat) * p_zw) :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast hZ_choices) (by positivity)
          _ = _ := by dsimp [p_zw, α, d_nat]; ring

private theorem bad2Cell_exp_majorant_le_v12
    {n M u z z_cut d_nat : ℕ} {L w : ℝ}
    (hn_pos : (0 : ℝ) < (n : ℝ))
    (hL_pos : 0 < L)
    (hw_pos : 0 < w)
    (hL_eq : L = logOrder n)
    (hw_log : Real.log L = w)
    (hph285 : (285 / 100 : ℝ) * L ≤ (phaseNat n : ℝ))
    (hα_pos : (0 : ℝ) < (phaseNat n : ℝ))
    (hα_ge1 : (1 : ℝ) ≤ (phaseNat n : ℝ))
    (hlog_α : Real.log (phaseNat n : ℝ) ≤ 2 + w)
    (hw64 : 64 ≤ w)
    (h64w : 64 * w ≤ w ^ 2)
    (hw_M : ((4 * M + 20 : ℕ) : ℝ) ≤ w)
    (hL_M : ((60 * (M + 10) : ℕ) : ℝ) ≤ L)
    (hw5L : w ^ 5 ≤ (1 / 400) * L)
    (hM1_le_ph : M + 1 ≤ phaseNat n)
    (hz_cut_def : z_cut = Nat.floor (w ^ 2))
    (hu_lo : phaseNat n - (M + 1) ≤ u)
    (hu_hi : u ≤ phaseNat n)
    (hz_lo : z_cut + 1 ≤ z)
    (hz3 : 3 ≤ z)
    (hzn : z ≤ n)
    (hd_ge2 : 2 ≤ d_nat)
    (hd_cast : (d_nat : ℝ) = (u : ℝ) - 2 * ((phaseNat n : ℝ) - (u : ℝ)) - (z : ℝ)) :
    (n.choose z : ℝ) * (2 : ℝ) ^ (-(((z : ℝ) - 1) * ((u : ℝ) - (z : ℝ) / 2))) *
      (phaseNat n : ℝ) ^ (4 * M + 4 + 2 * d_nat) ≤
    Real.exp (-(1 / 10 : ℝ) * L) := by
  have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL_nn : 0 ≤ logOrder n := hL_eq ▸ hL_pos.le
  have hlog_nn : 0 ≤ Real.log (n : ℝ) := hL_nn
  have h59_exp : (5 / 9 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
    have he_sq : (Real.exp (1 / 2 : ℝ)) ^ 2 ≤ (9 / 5 : ℝ) ^ 2 := by
      rw [← Real.exp_nat_mul]
      have h1 : ((2 : ℕ) : ℝ) * (1 / 2 : ℝ) = 1 := by norm_num
      rw [h1]
      have hnum : (2.7182818286 : ℝ) ≤ (9 / 5 : ℝ) ^ 2 := by norm_num
      linarith only [Real.exp_one_lt_d9, hnum]
    have he_le : Real.exp (1 / 2 : ℝ) ≤ 9 / 5 :=
      (abs_le_of_sq_le_sq' he_sq (by norm_num)).2
    rw [Real.exp_neg]
    have hm := inv_anti₀ (Real.exp_pos (1 / 2 : ℝ)) he_le
    simpa only [inv_div] using hm
  have hcross_b := crossEdge_binom_pow_le hz3 hzn u
  dsimp only at hcross_b
  rw [← hd_cast] at hcross_b
  have hstep1 := mul_le_mul_of_nonneg_right hcross_b
    (by positivity : (0 : ℝ) ≤ (phaseNat n : ℝ) ^ (4 * M + 4 + 2 * d_nat))
  refine hstep1.trans ?_
  clear hcross_b hstep1
  have hn_exp : (n : ℝ) = Real.exp L := by
    rw [hL_eq]; exact (Real.exp_log hn_pos).symm
  have hlb_nn : 0 ≤ 2 * logBaseTwo (n : ℝ) / (z : ℝ) := by
    unfold logBaseTwo
    exact div_nonneg (mul_nonneg zero_le_two (div_nonneg hlog_nn q_pos.le)) (by positivity)
  have hlb_nn0 : 0 ≤ 2 * logBaseTwo (n : ℝ) / (z : ℝ) *
      (2 : ℝ) ^ (-(((phaseNat n : ℝ) - (u : ℝ) + (d_nat : ℝ)) / 2)) :=
    mul_nonneg hlb_nn (by positivity)
  by_cases hd_small : d_nat ≤ z_cut
  · have hz_ge_95 : (9 / 5 : ℝ) * logBaseTwo (n : ℝ) ≤ (z : ℝ) := by
      have hd_r : (d_nat : ℝ) ≤ w ^ 2 :=
        (Nat.cast_le.mpr (hd_small.trans_eq hz_cut_def)).trans (Nat.floor_le (sq_nonneg w))
      have hw2_L : w ^ 2 ≤ (1 / 400 : ℝ) * L := by
        have hw25 : w ^ 2 ≤ w ^ 5 := pow_le_pow_right₀ (by linarith only [hw64] : 1 ≤ w) (by omega)
        linarith only [hw25, hw5L]
      have hlb_eq : (9 / 5 : ℝ) * logBaseTwo (n : ℝ) ≤ (27 / 10 : ℝ) * L := by
        rw [hL_eq]; unfold logBaseTwo q
        change (9 / 5 : ℝ) * (logOrder n / Real.log 2) ≤ (27 / 10 : ℝ) * logOrder n
        rw [mul_div_assoc', div_le_iff₀ hq_pos]
        have h95 : (9 / 5 : ℝ) ≤ (27 / 10 : ℝ) * Real.log 2 := by linarith only [Real.log_two_gt_d9]
        have hm := mul_le_mul_of_nonneg_right h95 hL_nn
        have hr : (27 / 10 : ℝ) * Real.log 2 * logOrder n =
            (27 / 10 : ℝ) * logOrder n * Real.log 2 := by ring
        linarith only [hm, hr]
      have hau : (phaseNat n : ℝ) - (u : ℝ) ≤ (M : ℝ) + 1 := by
        have h1 := Nat.cast_le (α := ℝ).mpr hu_lo
        rw [Nat.cast_sub hM1_le_ph, Nat.cast_add, Nat.cast_one] at h1
        linarith only [h1]
      have hL_M' : 60 * ((M : ℝ) + 10) ≤ L := by exact_mod_cast hL_M
      linarith only [hd_cast, hph285, hlb_eq, hd_r, hw2_L, hau, hL_M']
    have hbase_59 :
        2 * logBaseTwo (n : ℝ) / (z : ℝ) *
          (2 : ℝ) ^ (-(((phaseNat n : ℝ) - (u : ℝ) + (d_nat : ℝ)) / 2)) ≤ 5 / 9 := by
      have hexp_le1 : -(((phaseNat n : ℝ) - (u : ℝ) + (d_nat : ℝ)) / 2) ≤ -1 := by
        have hau_nn : 0 ≤ (phaseNat n : ℝ) - (u : ℝ) := sub_nonneg.mpr (by exact_mod_cast hu_hi)
        have hd2 : (2 : ℝ) ≤ (d_nat : ℝ) := by exact_mod_cast hd_ge2
        linarith only [hau_nn, hd2]
      have hrp : (2 : ℝ) ^ (-(((phaseNat n : ℝ) - (u : ℝ) + (d_nat : ℝ)) / 2)) ≤ 1 / 2 := by
        calc (2 : ℝ) ^ (-(((phaseNat n : ℝ) - (u : ℝ) + (d_nat : ℝ)) / 2))
            ≤ (2 : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le one_le_two hexp_le1
          _ = 1 / 2 := by norm_num
      have hrat : 2 * logBaseTwo (n : ℝ) / (z : ℝ) * (1 / 2) ≤ 5 / 9 := by
        have hz_pos : (0 : ℝ) < (z : ℝ) := by positivity
        rw [show 2 * logBaseTwo (n : ℝ) / (z : ℝ) * (1 / 2) =
            logBaseTwo (n : ℝ) / (z : ℝ) by ring, div_le_iff₀ hz_pos]
        linarith only [hz_ge_95]
      exact (mul_le_mul_of_nonneg_left hrp hlb_nn).trans hrat
    have hzm1_ge : (12 / 5 : ℝ) * L ≤ ((z - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ z), Nat.cast_one]
      have hlb_lo : (18 / 7 : ℝ) * L ≤ (9 / 5 : ℝ) * logBaseTwo (n : ℝ) := by
        rw [hL_eq]; unfold logBaseTwo q
        change (18 / 7 : ℝ) * logOrder n ≤ (9 / 5 : ℝ) * (logOrder n / Real.log 2)
        rw [mul_div_assoc', le_div_iff₀ hq_pos]
        have h187 : (18 / 7 : ℝ) * Real.log 2 ≤ 9 / 5 := by linarith only [Real.log_two_lt_d9]
        have hm := mul_le_mul_of_nonneg_right h187 hL_nn
        have hr : (18 / 7 : ℝ) * Real.log 2 * logOrder n =
            (18 / 7 : ℝ) * logOrder n * Real.log 2 := by ring
        linarith only [hm, hr]
      have hL60 : (60 : ℝ) ≤ L := by
        have h1 : (600 : ℝ) ≤ ((60 * (M + 10) : ℕ) : ℝ) := by
          exact_mod_cast (show 600 ≤ 60 * (M + 10) by omega)
        linarith only [h1, hL_M]
      linarith only [hlb_lo, hL60, hz_ge_95]
    have hpow_z :
        (2 * logBaseTwo (n : ℝ) / (z : ℝ) *
          (2 : ℝ) ^ (-(((phaseNat n : ℝ) - (u : ℝ) + (d_nat : ℝ)) / 2))) ^ (z - 1) ≤
        Real.exp (-(6 / 5 : ℝ) * L) := by
      calc _ ≤ (Real.exp (-(1 / 2 : ℝ))) ^ (z - 1) :=
            pow_le_pow_left₀ hlb_nn0 (hbase_59.trans h59_exp) (z - 1)
        _ = Real.exp (-(1 / 2 : ℝ) * ((z - 1 : ℕ) : ℝ)) := by
            rw [← Real.exp_nat_mul]; congr 1; ring
        _ ≤ Real.exp (-(6 / 5 : ℝ) * L) :=
            Real.exp_le_exp.mpr (by linarith only [hzm1_ge])
    have hα_exp : (phaseNat n : ℝ) ^ (4 * M + 4 + 2 * d_nat) ≤ Real.exp ((1 / 10 : ℝ) * L) := by
      rw [← Real.exp_log hα_pos, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have hd_r : (d_nat : ℝ) ≤ w ^ 2 :=
        (Nat.cast_le.mpr (hd_small.trans_eq hz_cut_def)).trans (Nat.floor_le (sq_nonneg w))
      have h1 : ((4 * M + 4 + 2 * d_nat : ℕ) : ℝ) * Real.log (phaseNat n : ℝ) ≤
          (w + 2 * w ^ 2) * (2 + w) := by
        have hw_M' : 4 * (M : ℝ) + 20 ≤ w := by exact_mod_cast hw_M
        have hM_w : 4 * (M : ℝ) + 4 ≤ w := by linarith only [hw_M']
        have hle_lhs : ((4 * M + 4 + 2 * d_nat : ℕ) : ℝ) ≤ w + 2 * w ^ 2 := by
          push_cast; linarith only [hM_w, hd_r]
        exact mul_le_mul hle_lhs hlog_α (Real.log_nonneg hα_ge1)
          (add_nonneg hw_pos.le (mul_nonneg zero_le_two (sq_nonneg w)))
      have h2 : (w + 2 * w ^ 2) * (2 + w) ≤ (1 / 10 : ℝ) * L := by
        have hw15 : w ≤ w ^ 5 := by
          simpa only [pow_one] using pow_le_pow_right₀ (by linarith only [hw64] : 1 ≤ w) (by omega : 1 ≤ 5)
        have hw25 : w ^ 2 ≤ w ^ 5 := pow_le_pow_right₀ (by linarith only [hw64] : 1 ≤ w) (by omega : 2 ≤ 5)
        have hw35 : w ^ 3 ≤ w ^ 5 := pow_le_pow_right₀ (by linarith only [hw64] : 1 ≤ w) (by omega : 3 ≤ 5)
        have hring_w : (w + 2 * w ^ 2) * (2 + w) = 2 * w + 5 * w ^ 2 + 2 * w ^ 3 := by ring
        linarith only [hw15, hw25, hw35, hring_w, hw5L, hL_pos]
      exact h1.trans h2
    calc (n : ℝ) *
            (2 * logBaseTwo (n : ℝ) / (z : ℝ) *
              (2 : ℝ) ^ (-(((phaseNat n : ℝ) - (u : ℝ) + (d_nat : ℝ)) / 2))) ^ (z - 1) *
            (phaseNat n : ℝ) ^ (4 * M + 4 + 2 * d_nat)
        ≤ Real.exp L * Real.exp (-(6 / 5 : ℝ) * L) * Real.exp ((1 / 10 : ℝ) * L) := by
          exact mul_le_mul
            (mul_le_mul hn_exp.le hpow_z (pow_nonneg hlb_nn0 _) (Real.exp_pos L).le)
            hα_exp (pow_nonneg hα_pos.le _) (mul_nonneg (Real.exp_pos L).le (Real.exp_pos _).le)
      _ = Real.exp (-(1 / 10 : ℝ) * L) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  · have hd_gt : w ^ 2 < (d_nat : ℝ) := by
      have h1 : Nat.floor (w ^ 2) + 1 ≤ d_nat := by omega
      exact lt_of_lt_of_le (Nat.lt_floor_add_one (w ^ 2)) (by exact_mod_cast h1)
    have hz_gt : w ^ 2 < (z : ℝ) := by
      have h1 : Nat.floor (w ^ 2) + 1 ≤ z := by omega
      exact lt_of_lt_of_le (Nat.lt_floor_add_one (w ^ 2)) (by exact_mod_cast h1)
    have hzm1_ge : w ^ 2 / 2 ≤ ((z - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ z), Nat.cast_one]
      linarith only [hw64, h64w, hz_gt]
    have hbase_d :
        2 * logBaseTwo (n : ℝ) / (z : ℝ) *
          (2 : ℝ) ^ (-(((phaseNat n : ℝ) - (u : ℝ) + (d_nat : ℝ)) / 2)) ≤
        Real.exp (-(1 / 4 : ℝ) * (d_nat : ℝ)) := by
      have h1 : 2 * logBaseTwo (n : ℝ) / (z : ℝ) ≤ 4 * L := by
        have hlb : 2 * logBaseTwo (n : ℝ) ≤ 4 * L := by
          rw [hL_eq]; unfold logBaseTwo q
          change 2 * (logOrder n / Real.log 2) ≤ 4 * logOrder n
          rw [mul_div_assoc', div_le_iff₀ hq_pos]
          have h24 : (2 : ℝ) ≤ 4 * Real.log 2 := by linarith only [Real.log_two_gt_d9]
          have hm := mul_le_mul_of_nonneg_right h24 hL_nn
          have hr : (4 * Real.log 2) * logOrder n = 4 * logOrder n * Real.log 2 := by ring
          linarith only [hm, hr]
        have hz1 : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (show 1 ≤ z by omega)
        exact (div_le_self (mul_nonneg zero_le_two (div_nonneg hlog_nn q_pos.le)) hz1).trans hlb
      have h4L_exp : 4 * L ≤ Real.exp ((1 / 12 : ℝ) * (d_nat : ℝ)) := by
        have hl4 : Real.log (4 * L) ≤ 2 + w := by
          have hlog4 : Real.log 4 ≤ 2 := by
            have h4e : (4 : ℝ) ≤ Real.exp 2 := by
              have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
              have he2 : (2 : ℝ) ^ 2 ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) he1 2
              rw [← Real.exp_nat_mul] at he2; norm_num at he2; exact he2
            exact (Real.log_le_log (by norm_num) h4e).trans_eq (Real.log_exp 2)
          rw [Real.log_mul (by norm_num) hL_pos.ne', hw_log]
          linarith only [hlog4]
        have hw_d : 2 + w ≤ (1 / 12 : ℝ) * (d_nat : ℝ) := by linarith only [hw64, h64w, hd_gt]
        exact (Real.exp_log (by positivity : 0 < 4 * L)).symm.le.trans
          (Real.exp_le_exp.mpr (hl4.trans hw_d))
      have h2_pow :
          (2 : ℝ) ^ (-(((phaseNat n : ℝ) - (u : ℝ) + (d_nat : ℝ)) / 2)) ≤
            Real.exp (-(1 / 3 : ℝ) * (d_nat : ℝ)) := by
        have hau_nn : 0 ≤ (phaseNat n : ℝ) - (u : ℝ) := sub_nonneg.mpr (by exact_mod_cast hu_hi)
        have hrp : (2 : ℝ) ^ (-(((phaseNat n : ℝ) - (u : ℝ) + (d_nat : ℝ)) / 2)) ≤
            (2 : ℝ) ^ (-(d_nat : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith only [hau_nn])
        refine hrp.trans ?_
        rw [Real.rpow_def_of_pos two_pos]
        apply Real.exp_le_exp.mpr
        have hq23 : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
        have hm := mul_le_mul_of_nonneg_right hq23
          (show (0 : ℝ) ≤ (d_nat : ℝ) / 2 by positivity)
        have hr1 : Real.log 2 * (-(d_nat : ℝ) / 2) = -(Real.log 2 * ((d_nat : ℝ) / 2)) := by ring
        have hr2 : -(1 / 3 : ℝ) * (d_nat : ℝ) = -((2 / 3 : ℝ) * ((d_nat : ℝ) / 2)) := by ring
        linarith only [hm, hr1, hr2]
      calc 2 * logBaseTwo (n : ℝ) / (z : ℝ) *
              (2 : ℝ) ^ (-(((phaseNat n : ℝ) - (u : ℝ) + (d_nat : ℝ)) / 2))
          ≤ Real.exp ((1 / 12 : ℝ) * (d_nat : ℝ)) *
              Real.exp (-(1 / 3 : ℝ) * (d_nat : ℝ)) :=
            mul_le_mul (h1.trans h4L_exp) h2_pow (by positivity) (Real.exp_pos _).le
        _ = Real.exp (-(1 / 4 : ℝ) * (d_nat : ℝ)) := by
            rw [← Real.exp_add]; congr 1; ring
    have hpow_d :
        (2 * logBaseTwo (n : ℝ) / (z : ℝ) *
          (2 : ℝ) ^ (-(((phaseNat n : ℝ) - (u : ℝ) + (d_nat : ℝ)) / 2))) ^ (z - 1) ≤
        Real.exp (-(1 / 4 : ℝ) * (d_nat : ℝ) * ((z - 1 : ℕ) : ℝ)) := by
      calc _ ≤ (Real.exp (-(1 / 4 : ℝ) * (d_nat : ℝ))) ^ (z - 1) :=
            pow_le_pow_left₀ hlb_nn0 hbase_d (z - 1)
        _ = Real.exp (-(1 / 4 : ℝ) * (d_nat : ℝ) * ((z - 1 : ℕ) : ℝ)) := by
            rw [← Real.exp_nat_mul]; congr 1; ring
    have hsum_dz_ge : 2 * L ≤ (d_nat : ℝ) + ((z - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ z), Nat.cast_one]
      have hau : (phaseNat n : ℝ) - (u : ℝ) ≤ (M : ℝ) + 1 := by
        have h1 := Nat.cast_le (α := ℝ).mpr hu_lo
        rw [Nat.cast_sub hM1_le_ph, Nat.cast_add, Nat.cast_one] at h1
        linarith only [h1]
      have hL_M' : 60 * ((M : ℝ) + 10) ≤ L := by exact_mod_cast hL_M
      linarith only [hd_cast, hph285, hau, hL_M']
    have hprod_dz_L : 2 * L ≤ (1 / 8 : ℝ) * (d_nat : ℝ) * ((z - 1 : ℕ) : ℝ) := by
      have hw2_32 : (32 : ℝ) ≤ w ^ 2 := by linarith only [hw64, h64w]
      have h32L := mul_le_mul_of_nonneg_right hw2_32 hL_pos.le
      rcases le_total (d_nat : ℝ) ((z - 1 : ℕ) : ℝ) with hdz | hzd
      · have hz_L : L ≤ ((z - 1 : ℕ) : ℝ) := by linarith only [hsum_dz_ge, hdz]
        have hd_half : w ^ 2 / 2 ≤ (d_nat : ℝ) := by linarith only [hw64, h64w, hd_gt]
        have hm := mul_le_mul hd_half hz_L hL_pos.le (Nat.cast_nonneg _)
        have hr1 : (w ^ 2 / 2) * L = (1 / 2 : ℝ) * (w ^ 2 * L) := by ring
        have hr2 : (d_nat : ℝ) * ((z - 1 : ℕ) : ℝ) =
            8 * ((1 / 8 : ℝ) * (d_nat : ℝ) * ((z - 1 : ℕ) : ℝ)) := by ring
        linarith only [h32L, hm, hr1, hr2]
      · have hd_L : L ≤ (d_nat : ℝ) := by linarith only [hsum_dz_ge, hzd]
        have hm := mul_le_mul hd_L hzm1_ge (by positivity) (Nat.cast_nonneg _)
        have hr1 : L * (w ^ 2 / 2) = (1 / 2 : ℝ) * (w ^ 2 * L) := by ring
        have hr2 : (d_nat : ℝ) * ((z - 1 : ℕ) : ℝ) =
            8 * ((1 / 8 : ℝ) * (d_nat : ℝ) * ((z - 1 : ℕ) : ℝ)) := by ring
        linarith only [h32L, hm, hr1, hr2]
    have hα_exp_d :
        (phaseNat n : ℝ) ^ (4 * M + 4 + 2 * d_nat) ≤
          Real.exp ((1 / 8 : ℝ) * (d_nat : ℝ) * ((z - 1 : ℕ) : ℝ)) := by
      rw [← Real.exp_log hα_pos, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have hw_M' : 4 * (M : ℝ) + 20 ≤ w := by exact_mod_cast hw_M
      have hM_d : 4 * (M : ℝ) + 4 ≤ (d_nat : ℝ) := by
        linarith only [hw_M', hw64, h64w, hd_gt]
      have hle_lhs : ((4 * M + 4 + 2 * d_nat : ℕ) : ℝ) ≤ 3 * (d_nat : ℝ) := by
        push_cast; linarith only [hM_d]
      have h1 : ((4 * M + 4 + 2 * d_nat : ℕ) : ℝ) * Real.log (phaseNat n : ℝ) ≤
          (3 * (d_nat : ℝ)) * (2 + w) :=
        mul_le_mul hle_lhs hlog_α (Real.log_nonneg hα_ge1) (by positivity)
      have h2 : 3 * (2 + w) ≤ (1 / 8 : ℝ) * ((z - 1 : ℕ) : ℝ) := by
        linarith only [hw64, h64w, hzm1_ge]
      have hm := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg d_nat)
      have hr1 : (d_nat : ℝ) * (3 * (2 + w)) = (3 * (d_nat : ℝ)) * (2 + w) := by ring
      have hr2 : (d_nat : ℝ) * ((1 / 8 : ℝ) * ((z - 1 : ℕ) : ℝ)) =
          (1 / 8 : ℝ) * (d_nat : ℝ) * ((z - 1 : ℕ) : ℝ) := by ring
      linarith only [h1, hm, hr1, hr2]
    calc (n : ℝ) *
            (2 * logBaseTwo (n : ℝ) / (z : ℝ) *
              (2 : ℝ) ^ (-(((phaseNat n : ℝ) - (u : ℝ) + (d_nat : ℝ)) / 2))) ^ (z - 1) *
            (phaseNat n : ℝ) ^ (4 * M + 4 + 2 * d_nat)
        ≤ Real.exp L * Real.exp (-(1 / 4 : ℝ) * (d_nat : ℝ) * ((z - 1 : ℕ) : ℝ)) *
            Real.exp ((1 / 8 : ℝ) * (d_nat : ℝ) * ((z - 1 : ℕ) : ℝ)) := by
          exact mul_le_mul
            (mul_le_mul hn_exp.le hpow_d (pow_nonneg hlb_nn0 _) (Real.exp_pos L).le)
            hα_exp_d (pow_nonneg hα_pos.le _) (mul_nonneg (Real.exp_pos L).le (Real.exp_pos _).le)
      _ = Real.exp (L - (1 / 8 : ℝ) * (d_nat : ℝ) * ((z - 1 : ℕ) : ℝ)) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-(1 / 10 : ℝ) * L) :=
          Real.exp_le_exp.mpr (by linarith only [hprod_dz_L, hL_pos])

private theorem condProb_bad2Event_le_v12
    {n M : ℕ} {eps : ℝ}
    (hdom : PhaseDomain n)
    (hph285 : (285 / 100 : ℝ) * logOrder n ≤ (phaseNat n : ℝ))
    (hα_le_4L : (phaseNat n : ℝ) ≤ 4 * logOrder n)
    (hw64 : 64 ≤ logLogOrder n)
    (hw_M : ((4 * M + 20 : ℕ) : ℝ) ≤ logLogOrder n)
    (hL_M : ((60 * (M + 10) : ℕ) : ℝ) ≤ logOrder n)
    (hw5L : (logLogOrder n) ^ 5 ≤ (1 / 400) * logOrder n)
    (hExp2 : 4 * ((M + 2 : ℕ) : ℝ) * logOrder n * Real.exp (-(1 / 10 : ℝ) * logOrder n) ≤ eps / 4)
    (P : VertexPartition n) (hPa : ∀ B ∈ P.parts, B.card ≤ phaseNat n) :
    (randomGraphMeasure n).real
        (partitionColoringEvent P ∩ bad2Event_v12 M (Nat.floor ((logLogOrder n) ^ 2)) P) ≤
      (eps / 4) * (randomGraphMeasure n).real (partitionColoringEvent P) := by
  classical
  set α : ℕ := phaseNat n
  set L : ℝ := logOrder n
  set w : ℝ := logLogOrder n
  set z_cut : ℕ := Nat.floor (w ^ 2)
  have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hw_pos : 0 < w := by linarith
  have hL_pos : 0 < L := by
    have : (1 : ℝ) ≤ ((60 * (M + 10) : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ 60 * (M + 10) by omega)
    linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_trans Nat.zero_lt_one hdom.1)
  have hw_log : Real.log L = w := rfl
  have hα_ge_2L : 2 * L ≤ (α : ℝ) := by linarith [hph285]
  have hα_pos : (0 : ℝ) < (α : ℝ) := lt_of_lt_of_le (by positivity) hα_ge_2L
  have hα_pos_nat : 0 < phaseNat n := by exact_mod_cast hα_pos
  have hα_ge1 : (1 : ℝ) ≤ (α : ℝ) := by
    have : (60 : ℝ) ≤ ((60 * (M + 10) : ℕ) : ℝ) := by
      exact_mod_cast (show 60 ≤ 60 * (M + 10) by omega)
    linarith [hL_M, hα_ge_2L]
  have hM1_le_ph : M + 1 ≤ phaseNat n := by
    have : ((M + 1 : ℕ) : ℝ) ≤ (phaseNat n : ℝ) := by push_cast at hL_M ⊢; linarith [hph285]
    exact Nat.cast_le.mp this
  have hlog_α : Real.log (α : ℝ) ≤ 2 + w := by
    have hl4 : Real.log 4 ≤ 2 := by
      have h4e : (4 : ℝ) ≤ Real.exp 2 := by
        have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        have he2 : (2 : ℝ) ^ 2 ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) he1 2
        rw [← Real.exp_nat_mul] at he2; norm_num at he2; exact he2
      exact (Real.log_le_log (by norm_num) h4e).trans_eq (Real.log_exp 2)
    calc Real.log (α : ℝ) ≤ Real.log (4 * L) := Real.log_le_log hα_pos hα_le_4L
      _ = Real.log 4 + Real.log L := Real.log_mul (by norm_num) hL_pos.ne'
      _ ≤ 2 + w := by linarith [hw_log]
  have h64w : 64 * w ≤ w ^ 2 := by
    calc 64 * w ≤ w * w := mul_le_mul_of_nonneg_right hw64 hw_pos.le
      _ = w ^ 2 := (sq w).symm
  clear hq_pos
  have huz_le : ∀ u ∈ Finset.Icc (α - (M + 1)) α,
      ∀ z ∈ Finset.Icc (z_cut + 1) (u - 2 * (α - u) - 2),
        (randomGraphMeasure n).real (partitionColoringEvent P ∩ bad2Cell_v12 P u z) ≤
          Real.exp (-(1 / 10 : ℝ) * L) *
            (randomGraphMeasure n).real (partitionColoringEvent P) := by
    intro u hu z hz
    obtain ⟨hu_lo, hu_hi⟩ := Finset.mem_Icc.mp hu
    obtain ⟨hz_lo, hz_hi⟩ := Finset.mem_Icc.mp hz
    have hzc_ge : 4096 ≤ z_cut :=
      Nat.le_floor (by have := pow_le_pow_left₀ (by norm_num) hw64 2; norm_num at this; exact this)
    have hz3 : 3 ≤ z := by omega
    have hzn : z ≤ n := by
      have hu_n : α ≤ n := by
        by_contra hgt
        have : (n : ℝ) < 4 * L := lt_of_lt_of_le (by exact_mod_cast not_le.mp hgt) hα_le_4L
        have hL5 : (600 : ℝ) ≤ L := by
          have : (600 : ℝ) ≤ ((60 * (M + 10) : ℕ) : ℝ) := by
            exact_mod_cast (show 600 ≤ 60 * (M + 10) by omega)
          linarith [hL_M]
        have he : (n : ℝ) = Real.exp L := (Real.exp_log hn_pos).symm
        have hquad : L ^ 2 / 2 ≤ Real.exp L := by
          have := Real.sum_le_exp_of_nonneg hL_pos.le 3
          simp [Finset.sum_range_succ, Nat.factorial] at this
          linarith
        have h300L : 300 * L ≤ L ^ 2 / 2 := by
          have hm := mul_le_mul_of_nonneg_right hL5 hL_pos.le
          linarith [show 600 * L = 2 * (300 * L) by ring, show L * L = L ^ 2 by ring]
        linarith
      omega
    have hunion_uz := bad2Cell_measureReal_le_v12 P hPa hα_pos_nat hu_lo hu_hi hz3 hz_hi
    set d_nat : ℕ := u - 2 * (phaseNat n - u) - z
    have hd_ge2 : 2 ≤ d_nat := by dsimp [d_nat, α] at *; omega
    have hd_cast : (d_nat : ℝ) = (u : ℝ) - 2 * ((phaseNat n : ℝ) - (u : ℝ)) - (z : ℝ) := by
      dsimp [d_nat]
      rw [Nat.cast_sub (by dsimp [α] at *; omega : z ≤ u - 2 * (phaseNat n - u)),
        Nat.cast_sub (by dsimp [α] at *; omega : 2 * (phaseNat n - u) ≤ u),
        Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hu_hi]
    have hmain_uz := bad2Cell_exp_majorant_le_v12 hn_pos hL_pos hw_pos rfl hw_log
      hph285 hα_pos hα_ge1 hlog_α hw64 h64w hw_M hL_M hw5L hM1_le_ph rfl
      hu_lo hu_hi hz_lo hz3 hzn hd_ge2 hd_cast
    exact hunion_uz.trans (mul_le_mul_of_nonneg_right hmain_uz measureReal_nonneg)
  have hid_b2 : partitionColoringEvent P ∩ bad2Event_v12 M z_cut P =
      ⋃ u ∈ Finset.Icc (α - (M + 1)) α,
        ⋃ z ∈ Finset.Icc (z_cut + 1) (u - 2 * (α - u) - 2),
          (partitionColoringEvent P ∩ bad2Cell_v12 P u z) := by
    ext G; simp [bad2Event_v12, α]
  rw [hid_b2]
  let Z2 : ℝ := Real.exp (-(1 / 10 : ℝ) * L) *
    (randomGraphMeasure n).real (partitionColoringEvent P)
  have hZ2_nn : 0 ≤ Z2 := by dsimp [Z2]; positivity
  have hsum2 :
      (randomGraphMeasure n).real
          (⋃ u ∈ Finset.Icc (α - (M + 1)) α,
            ⋃ z ∈ Finset.Icc (z_cut + 1) (u - 2 * (α - u) - 2),
              (partitionColoringEvent P ∩ bad2Cell_v12 P u z)) ≤
        (4 * ((M + 2 : ℕ) : ℝ) * L * Real.exp (-(1 / 10 : ℝ) * L)) *
          (randomGraphMeasure n).real (partitionColoringEvent P) := by
    calc (randomGraphMeasure n).real _
        ≤ ∑ u ∈ Finset.Icc (α - (M + 1)) α,
            ∑ z ∈ Finset.Icc (z_cut + 1) (u - 2 * (α - u) - 2),
              (randomGraphMeasure n).real (partitionColoringEvent P ∩ bad2Cell_v12 P u z) :=
          (rg_biUnion_finset_le_v12 _ _).trans
            (Finset.sum_le_sum fun _ _ ↦ rg_biUnion_finset_le_v12 _ _)
      _ ≤ ∑ u ∈ Finset.Icc (α - (M + 1)) α,
            ∑ _z ∈ Finset.Icc (z_cut + 1) (u - 2 * (α - u) - 2), Z2 :=
          Finset.sum_le_sum fun u hu ↦ Finset.sum_le_sum fun z hz ↦ huz_le u hu z hz
      _ ≤ ∑ _u ∈ Finset.Icc (α - (M + 1)) α, (4 * L * Z2) := by
          refine Finset.sum_le_sum fun u hu ↦ ?_
          simp only [Finset.sum_const, nsmul_eq_mul]
          have hcz : ((Finset.Icc (z_cut + 1) (u - 2 * (α - u) - 2)).card : ℝ) ≤ 4 * L := by
            rw [Nat.card_Icc]
            have hu_le : u ≤ α := (Finset.mem_Icc.mp hu).2
            have hnat : u - 2 * (α - u) - 2 + 1 - (z_cut + 1) ≤ phaseNat n := by omega
            exact (Nat.cast_le.mpr hnat).trans hα_le_4L
          exact mul_le_mul_of_nonneg_right hcz hZ2_nn
      _ ≤ _ := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          have hcu : ((Finset.Icc (α - (M + 1)) α).card : ℝ) ≤ ((M + 2 : ℕ) : ℝ) := by
            rw [Nat.card_Icc]; exact_mod_cast (show α + 1 - (α - (M + 1)) ≤ M + 2 by omega)
          calc (((Finset.Icc (α - (M + 1)) α).card : ℝ) * (4 * L * Z2))
              ≤ ((M + 2 : ℕ) : ℝ) * (4 * L * Z2) :=
                mul_le_mul_of_nonneg_right hcu (by positivity)
            _ = _ := by dsimp [Z2]; ring
  exact hsum2.trans (mul_le_mul_of_nonneg_right hExp2 measureReal_nonneg)

/-- **Lemma 7.1 `¬ B_π` conditional regularity (`main.tex` lines 927–928, 960, 968–994):**
for every `M : ℕ` and `eps > 0`, eventually in `n`, uniformly over all `P : VertexPartition n`
with part sizes `≤ phaseNat n`, the event `B_P` that every independent set `S` with
`phaseNat n - (M + 1) ≤ |S| ≤ phaseNat n` satisfies `z(S, P) ≤ 2` or
`z(S, P) ≥ |S| - 2 (phaseNat n - |S|) - 1` obeys `P(A_P ∩ B_Pᶜ) ≤ eps · P(A_P)`. -/
theorem eventually_condProb_badZComposed_tendsto_zero
    (M : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop,
      ∀ P : VertexPartition n,
        (∀ B ∈ P.parts, B.card ≤ phaseNat n) →
        let B_P : Set (LabeledGraph n) :=
          {G | ∀ S : Finset (Fin n),
            G.IsIndepSet (S : Set (Fin n)) →
            phaseNat n - (M + 1) ≤ S.card →
            S.card ≤ phaseNat n →
            (P.parts.filter fun E ↦ (S ∩ E).Nonempty).card ≤ 2 ∨
              S.card ≤ (P.parts.filter fun E ↦ (S ∩ E).Nonempty).card +
                2 * (phaseNat n - S.card) + 1}
        (randomGraphMeasure n).real (partitionColoringEvent P ∩ B_Pᶜ) ≤
          eps * (randomGraphMeasure n).real (partitionColoringEvent P) := by
  have ho_w5 : (fun x : ℝ ↦ (Real.log x) ^ ((5 : ℕ) : ℝ)) =o[atTop] (fun x : ℝ ↦ x ^ (1 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop ((5 : ℕ) : ℝ) zero_lt_one
  have hw5_small : ∀ᶠ n : ℕ in atTop, (logLogOrder n) ^ 5 ≤ (1 / 400) * logOrder n := by
    have hb := (ho_w5.comp_tendsto tendsto_logOrder_atTop).bound (by norm_num : (0 : ℝ) < 1 / 400)
    filter_upwards [hb, tendsto_logLogOrder_atTop.eventually_ge_atTop 2,
      tendsto_logOrder_atTop.eventually_ge_atTop 4] with n hn hw2 hL4
    have hw_pos : 0 < logLogOrder n := by linarith
    have hL_pos : 0 < logOrder n := by linarith
    dsimp only [Function.comp_apply] at hn
    change ‖(logLogOrder n) ^ ((5 : ℕ) : ℝ)‖ ≤ (1 / 400) * ‖(logOrder n) ^ (1 : ℝ)‖ at hn
    rw [Real.rpow_natCast, Real.norm_eq_abs, abs_of_pos (pow_pos hw_pos 5),
      Real.rpow_one, Real.norm_eq_abs, abs_of_pos hL_pos] at hn
    exact hn
  have hdec1 : ∀ᶠ n : ℕ in atTop, Real.exp (-(1 / 6 : ℝ) * logOrder n) ≤ eps / 4 := by
    have ht : Tendsto (fun n : ℕ ↦ Real.exp (-(1 / 6 : ℝ) * logOrder n)) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_logOrder_atTop.const_mul_atTop_of_neg (by norm_num))
    exact ht.eventually (Iic_mem_nhds (show (0 : ℝ) < eps / 4 by positivity))
  have hdec2 : ∀ᶠ n : ℕ in atTop,
      4 * ((M + 2 : ℕ) : ℝ) * logOrder n * Real.exp (-(1 / 10 : ℝ) * logOrder n) ≤ eps / 4 := by
    have ho : (fun x : ℝ ↦ x ^ (1 : ℝ)) =o[atTop] (fun x : ℝ ↦ Real.exp ((1 / 10 : ℝ) * x)) :=
      isLittleO_rpow_exp_pos_mul_atTop 1 (by norm_num)
    have ht0 := (ho.comp_tendsto tendsto_logOrder_atTop).tendsto_div_nhds_zero
    have ht := ht0.const_mul (4 * ((M + 2 : ℕ) : ℝ))
    rw [mul_zero] at ht
    refine (ht.eventually (Iic_mem_nhds (show (0 : ℝ) < eps / 4 by positivity))).mono fun n hn ↦ ?_
    dsimp only [Function.comp_apply] at hn
    rw [Real.rpow_one, div_eq_mul_inv, ← Real.exp_neg] at hn
    have heq : 4 * ((M + 2 : ℕ) : ℝ) * logOrder n * Real.exp (-(1 / 10 : ℝ) * logOrder n) =
        4 * ((M + 2 : ℕ) : ℝ) * (logOrder n * Real.exp (-((1 / 10 : ℝ) * logOrder n))) := by
      rw [show -(1 / 10 : ℝ) * logOrder n = -((1 / 10 : ℝ) * logOrder n) by ring]; ring
    rwa [heq]
  filter_upwards [condProb_heavyCrossPairEvent_le_and_eventually_inv_n.2,
    eventually_two_85_logOrder_le_phaseNat,
    eventually_phaseRoot_domain_pos_and_target_corridor,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
    hw5_small, hdec1, hdec2,
    eventually_ge_atTop (Nat.ceil (2 / eps) + 10),
    tendsto_logLogOrder_atTop.eventually_ge_atTop (max 64 ((4 * M + 20 : ℕ) : ℝ)),
    tendsto_logOrder_atTop.eventually_ge_atTop ((60 * (M + 10) : ℕ) : ℝ)] with
    n hEP_ev hph285 hcenterDom hphase hw5L hExp1 hExp2 hn_eps hw_big hL_big P hPa
  intro B_P
  have hBP_eq : B_P = badZComposedEvent_v12 M P := rfl
  rw [hBP_eq]
  clear hBP_eq B_P
  have hw64 : 64 ≤ logLogOrder n := (le_max_left _ _).trans hw_big
  have hw_M : ((4 * M + 20 : ℕ) : ℝ) ≤ logLogOrder n := (le_max_right _ _).trans hw_big
  have hα_ge_2L : 2 * logOrder n ≤ (phaseNat n : ℝ) := by
    have : 0 < logOrder n := by
      have : (1 : ℝ) ≤ ((60 * (M + 10) : ℕ) : ℝ) := by
        exact_mod_cast (show 1 ≤ 60 * (M + 10) by omega)
      linarith
    linarith [hph285]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_trans Nat.zero_lt_one hcenterDom.1.1)
  have hcov := badZComposed_compl_subset_v12 (z_cut := Nat.floor ((logLogOrder n) ^ 2))
    hcenterDom.1.1 hL_big hα_ge_2L P
  have h0_le :
      (randomGraphMeasure n).real (partitionColoringEvent P ∩ heavyCrossPairEvent_v12 P) ≤
        (eps / 2) * (randomGraphMeasure n).real (partitionColoringEvent P) := by
    have h1 : (randomGraphMeasure n).real (partitionColoringEvent P ∩ heavyCrossPairEvent_v12 P) ≤
        (1 / (n : ℝ)) * (randomGraphMeasure n).real (partitionColoringEvent P) := hEP_ev P hPa
    have hinv_le : 1 / (n : ℝ) ≤ eps / 2 := by
      rw [div_le_iff₀ hn_pos]
      have hc : 2 / eps ≤ (Nat.ceil (2 / eps) : ℝ) := Nat.le_ceil _
      have hn_ge : (Nat.ceil (2 / eps) : ℝ) ≤ (n : ℝ) :=
        by exact_mod_cast (show Nat.ceil (2 / eps) ≤ n by omega)
      have := (div_le_iff₀ heps).mp (hc.trans hn_ge)
      linarith
    exact h1.trans (mul_le_mul_of_nonneg_right hinv_le measureReal_nonneg)
  have h1_le := condProb_bad1Event_le_v12 hcenterDom.1 hα_ge_2L hphase.2
    hw64 hw_M hL_big hw5L hExp1 P hPa
  have h2_le := condProb_bad2Event_le_v12 hcenterDom.1 hph285 hphase.2
    hw64 hw_M hL_big hw5L hExp2 P hPa
  calc (randomGraphMeasure n).real (partitionColoringEvent P ∩ (badZComposedEvent_v12 M P)ᶜ)
      ≤ (randomGraphMeasure n).real (partitionColoringEvent P ∩ heavyCrossPairEvent_v12 P) +
          ((randomGraphMeasure n).real
              (partitionColoringEvent P ∩ bad1Event_v12 M (12 * (Nat.floor ((logLogOrder n) ^ 2)) ^ 2) P) +
            (randomGraphMeasure n).real
              (partitionColoringEvent P ∩ bad2Event_v12 M (Nat.floor ((logLogOrder n) ^ 2)) P)) :=
        (rg_mono_v12 hcov).trans
          ((measureReal_union_le _ _).trans (add_le_add le_rfl (measureReal_union_le _ _)))
    _ ≤ (eps / 2) * (randomGraphMeasure n).real (partitionColoringEvent P) +
          ((eps / 4) * (randomGraphMeasure n).real (partitionColoringEvent P) +
            (eps / 4) * (randomGraphMeasure n).real (partitionColoringEvent P)) :=
        add_le_add h0_le (add_le_add h1_le h2_le)
    _ = eps * (randomGraphMeasure n).real (partitionColoringEvent P) := by ring

private theorem filter_eq_of_iff_v12 {α_t : Type*} {s : Finset α_t}
    {p q : α_t → Prop} {dp : DecidablePred p} {dq : DecidablePred q}
    (h : ∀ x ∈ s, p x ↔ q x) :
    @Finset.filter α_t p dp s = @Finset.filter α_t q dq s :=
  @Finset.filter_congr α_t p q dp dq s h

private theorem card_filter_le_of_imp_v12 {α_t : Type*} {s : Finset α_t}
    {p q : α_t → Prop} {dp : DecidablePred p} {dq : DecidablePred q}
    (h : ∀ x ∈ s, p x → q x) :
    (@Finset.filter α_t p dp s).card ≤ (@Finset.filter α_t q dq s).card :=
  Finset.card_le_card fun x hx ↦ by
    obtain ⟨hxs, hpx⟩ := (@Finset.mem_filter α_t p dp s x).mp hx
    exact (@Finset.mem_filter α_t q dq s x).mpr ⟨hxs, h x hxs hpx⟩

private theorem ite_eq_of_iff_v12 {P Q : Prop} {dP : Decidable P} {dQ : Decidable Q}
    (h : P ↔ Q) (a b : ℝ) :
    @ite ℝ P dP a b = @ite ℝ Q dQ a b := by
  cases dP with
  | isTrue hP =>
    cases dQ with
    | isTrue _ => rfl
    | isFalse hnQ => exact False.elim (hnQ (h.mp hP))
  | isFalse hnP =>
    cases dQ with
    | isTrue hQ => exact False.elim (hnP (h.mpr hQ))
    | isFalse _ => rfl

private theorem inter_iff_of_eq_v12 {α_t : Type*} {x : α_t} {A₁ A₂ B₁ B₂ : Set α_t}
    (hA : x ∈ A₁ ↔ x ∈ A₂) (hB : x ∈ B₁ ↔ x ∈ B₂) :
    x ∈ A₁ ∩ B₁ ↔ x ∈ A₂ ∩ B₂ :=
  and_congr hA hB

private def lemma71_B_ind {n : ℕ} (α : ℕ) (U_sizes : Set ℕ) (Q : VertexPartition n) :
    Set (LabeledGraph n) :=
  {G | ∀ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) → S.card ∈ U_sizes →
    (Q.parts.filter fun E ↦ (S ∩ E).Nonempty).card ≤ 2 ∨
      S.card ≤ (Q.parts.filter fun E ↦ (S ∩ E).Nonempty).card + 2 * (α - S.card) + 1}

private def lemma71_C_ind {n : ℕ} (U_sizes : Set ℕ) (Q : VertexPartition n) :
    Set (LabeledGraph n) :=
  {G | ∀ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) → S.card ∈ U_sizes →
    (Q.parts.filter fun E ↦ (S ∩ E).Nonempty).card = 2 →
      ∃ E ∈ Q.parts, (S ∩ E).card = S.card - 1}

open scoped Classical in
private def lemma71_D_ind {n : ℕ} (U_sizes : Set ℕ) (Q : VertexPartition n) (c_cap : ℝ) :
    Set (LabeledGraph n) :=
  {G | (((Finset.univ : Finset (Fin n)).powerset.filter fun S : Finset (Fin n) ↦
      G.IsIndepSet (S : Set (Fin n)) ∧ S.card ∈ U_sizes ∧
      (Q.parts.filter fun E ↦ (S ∩ E).Nonempty).card = 2 ∧
      ∃ E ∈ Q.parts, E.card - 1 ≤ (S ∩ E).card).card : ℝ) ≤ c_cap}

private def lemma71_B_cl {n : ℕ} (α : ℕ) (U_sizes : Set ℕ) (Q : VertexPartition n) :
    Set (LabeledGraph n) :=
  {G | ∀ S : Finset (Fin n), G.IsClique (S : Set (Fin n)) → S.card ∈ U_sizes →
    (Q.parts.filter fun E ↦ (S ∩ E).Nonempty).card ≤ 2 ∨
      S.card ≤ (Q.parts.filter fun E ↦ (S ∩ E).Nonempty).card + 2 * (α - S.card) + 1}

private def lemma71_C_cl {n : ℕ} (U_sizes : Set ℕ) (Q : VertexPartition n) :
    Set (LabeledGraph n) :=
  {G | ∀ S : Finset (Fin n), G.IsClique (S : Set (Fin n)) → S.card ∈ U_sizes →
    (Q.parts.filter fun E ↦ (S ∩ E).Nonempty).card = 2 →
      ∃ E ∈ Q.parts, (S ∩ E).card = S.card - 1}

open scoped Classical in
private def lemma71_D_cl {n : ℕ} (U_sizes : Set ℕ) (Q : VertexPartition n) (c_cap : ℝ) :
    Set (LabeledGraph n) :=
  {G | (((Finset.univ : Finset (Fin n)).powerset.filter fun S : Finset (Fin n) ↦
      G.IsClique (S : Set (Fin n)) ∧ S.card ∈ U_sizes ∧
      (Q.parts.filter fun E ↦ (S ∩ E).Nonempty).card = 2 ∧
      ∃ E ∈ Q.parts, E.card - 1 ≤ (S ∩ E).card).card : ℝ) ≤ c_cap}

open scoped Classical in
private theorem lemma71_single_partition_bounds_v12
    {n M : ℕ} {P : VertexPartition n} {eps : ℝ}
    (heps_pos : 0 < eps) (hn2 : 2 < n) (hphM : M + 4 ≤ phaseNat n)
    (hB_P : (randomGraphMeasure n).real
        (partitionColoringEvent P ∩
          (lemma71_B_ind (phaseNat n) {s : ℕ | phaseNat n - (M + 1) ≤ s ∧ s ≤ phaseNat n} P)ᶜ) ≤
      (eps / 6) * (randomGraphMeasure n).real (partitionColoringEvent P))
    (hC_P : (randomGraphMeasure n).real
        (partitionColoringEvent P ∩
          (lemma71_C_ind {s : ℕ | phaseNat n - (M + 1) ≤ s ∧ s ≤ phaseNat n} P)ᶜ) ≤
      (eps / 6) * (randomGraphMeasure n).real (partitionColoringEvent P))
    (hD_P : (randomGraphMeasure n).real
        (partitionColoringEvent P ∩
          (lemma71_D_ind {s : ℕ | phaseNat n - (M + 1) ≤ s ∧ s ≤ phaseNat n} P
            ((1 / 2 : ℝ) * (Real.log (n : ℝ)) ^ 3))ᶜ) ≤
      (eps / 6) * (randomGraphMeasure n).real (partitionColoringEvent P))
    (hPU : ∀ D ∈ P.parts, phaseNat n - (M + 1) ≤ D.card ∧ D.card ≤ phaseNat n) :
    let U_s : Set ℕ := {s : ℕ | phaseNat n - (M + 1) ≤ s ∧ s ≤ phaseNat n}
    let c_full : ℝ := (Real.log (n : ℝ)) ^ 3
    let c_half : ℝ := (1 / 2 : ℝ) * (Real.log (n : ℝ)) ^ 3
    (1 - eps) * (randomGraphMeasure n).real (partitionColoringEvent P) ≤
        (randomGraphMeasure n).real
          (partitionColoringEvent P ∩ lemma71_B_ind (phaseNat n) U_s P ∩
            lemma71_C_ind U_s P ∩ lemma71_D_ind U_s P c_full) ∧
      (1 - eps) * (2 : ℝ) ^ P.parts.card *
          (randomGraphMeasure n).real (partitionColoringEvent P) ≤
        (randomGraphMeasure n).real
          (partitionCocoloringEvent P ∩ lemma71_B_ind (phaseNat n) U_s P ∩
            lemma71_C_ind U_s P ∩ lemma71_D_ind U_s P c_half ∩
            lemma71_B_cl (phaseNat n) U_s P ∩ lemma71_C_cl U_s P ∩
            lemma71_D_cl U_s P c_half) := by
  intro U_s c_full c_half
  change (randomGraphMeasure n).real
    (partitionColoringEvent P ∩ (lemma71_B_ind (phaseNat n) U_s P)ᶜ) ≤
      (eps / 6) * (randomGraphMeasure n).real (partitionColoringEvent P) at hB_P
  change (randomGraphMeasure n).real
    (partitionColoringEvent P ∩ (lemma71_C_ind U_s P)ᶜ) ≤
      (eps / 6) * (randomGraphMeasure n).real (partitionColoringEvent P) at hC_P
  change (randomGraphMeasure n).real
    (partitionColoringEvent P ∩ (lemma71_D_ind U_s P c_half)ᶜ) ≤
      (eps / 6) * (randomGraphMeasure n).real (partitionColoringEvent P) at hD_P
  have hP2 : ∀ D ∈ P.parts, 2 ≤ D.card := by
    intro D hD; have := (hPU D hD).1; omega
  have hc_le : c_half ≤ c_full := by
    dsimp only [c_half, c_full]
    have hL_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    nlinarith [pow_nonneg hL_nn 3]
  have hD_mono : lemma71_D_ind U_s P c_half ⊆ lemma71_D_ind U_s P c_full :=
    fun _ hG ↦ le_trans hG hc_le
  let Bad_ind : Set (LabeledGraph n) :=
    (lemma71_B_ind (phaseNat n) U_s P)ᶜ ∪ (lemma71_C_ind U_s P)ᶜ ∪ (lemma71_D_ind U_s P c_half)ᶜ
  have hBad_ind_prob :
      (randomGraphMeasure n).real (partitionColoringEvent P ∩ Bad_ind) ≤
        (eps / 2) * (randomGraphMeasure n).real (partitionColoringEvent P) := by
    have hid : partitionColoringEvent P ∩ Bad_ind =
        ((partitionColoringEvent P ∩ (lemma71_B_ind (phaseNat n) U_s P)ᶜ) ∪
          (partitionColoringEvent P ∩ (lemma71_C_ind U_s P)ᶜ)) ∪
          (partitionColoringEvent P ∩ (lemma71_D_ind U_s P c_half)ᶜ) := by
      ext G; simp only [Bad_ind, Set.mem_inter_iff, Set.mem_union]; tauto
    rw [hid]
    calc (randomGraphMeasure n).real _
        ≤ ((randomGraphMeasure n).real (partitionColoringEvent P ∩ (lemma71_B_ind (phaseNat n) U_s P)ᶜ) +
            (randomGraphMeasure n).real (partitionColoringEvent P ∩ (lemma71_C_ind U_s P)ᶜ)) +
            (randomGraphMeasure n).real (partitionColoringEvent P ∩ (lemma71_D_ind U_s P c_half)ᶜ) :=
          (measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl)
      _ ≤ (eps / 2) * (randomGraphMeasure n).real (partitionColoringEvent P) := by
          linarith [hB_P, hC_P, hD_P]
  have hCh_good :
      (1 - eps) * (randomGraphMeasure n).real (partitionColoringEvent P) ≤
        (randomGraphMeasure n).real
          (partitionColoringEvent P ∩ lemma71_B_ind (phaseNat n) U_s P ∩
            lemma71_C_ind U_s P ∩ lemma71_D_ind U_s P c_full) := by
    have hcov_ch : partitionColoringEvent P ⊆
        (partitionColoringEvent P ∩ lemma71_B_ind (phaseNat n) U_s P ∩
            lemma71_C_ind U_s P ∩ lemma71_D_ind U_s P c_full) ∪
          (partitionColoringEvent P ∩ Bad_ind) := by
      intro G hGA
      by_cases hGB : G ∈ lemma71_B_ind (phaseNat n) U_s P
      · by_cases hGC : G ∈ lemma71_C_ind U_s P
        · by_cases hGD : G ∈ lemma71_D_ind U_s P c_half
          · exact Or.inl ⟨⟨⟨hGA, hGB⟩, hGC⟩, hD_mono hGD⟩
          · exact Or.inr ⟨hGA, Or.inr hGD⟩
        · exact Or.inr ⟨hGA, Or.inl (Or.inr hGC)⟩
      · exact Or.inr ⟨hGA, Or.inl (Or.inl hGB)⟩
    have htot := (rg_mono_v12 hcov_ch).trans (measureReal_union_le _ _)
    have heps2 : 0 ≤ (eps / 2) * (randomGraphMeasure n).real (partitionColoringEvent P) :=
      mul_nonneg (by linarith) measureReal_nonneg
    have hring : (1 - eps) * (randomGraphMeasure n).real (partitionColoringEvent P) =
        (randomGraphMeasure n).real (partitionColoringEvent P) -
          2 * ((eps / 2) * (randomGraphMeasure n).real (partitionColoringEvent P)) := by ring
    linarith [hBad_ind_prob, hring]
  have hflip_ind : ∀ (σ : P.parts → Bool) (G : LabeledGraph n),
      G ∈ partitionMarkedEvent P σ →
      ∀ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) →
        (flipMarkedInternal P σ G).IsIndepSet (S : Set (Fin n)) := by
    intro σ G hGm S hS x hx y hy hxy hadj
    change flipMarkedAdj P σ G x y at hadj
    unfold flipMarkedAdj at hadj
    by_cases hmk : markedPair P σ x y
    · rcases hmk with ⟨B, hσB, hxB, hyB⟩
      have hBσ := hGm B
      rw [hσB] at hBσ
      simp only [↓reduceIte] at hBσ
      exact hS hx hy hxy (hBσ hxB hyB hxy)
    · have hadj2 := hadj.2
      rw [if_neg hmk] at hadj2
      exact hS hx hy hxy hadj2
  have hmark_bad : ∀ σ : P.parts → Bool,
      (randomGraphMeasure n).real (partitionMarkedEvent P σ ∩ Bad_ind) ≤
        (eps / 2) * (randomGraphMeasure n).real (partitionColoringEvent P) := by
    intro σ
    have hmap_sub : ∀ G ∈ partitionMarkedEvent P σ ∩ Bad_ind,
        flipMarkedInternal P σ G ∈ partitionColoringEvent P ∩ Bad_ind := by
      rintro G ⟨hGm, hGbad⟩
      refine ⟨flipMarkedInternal_mem_partitionColoringEvent hGm, ?_⟩
      have hind_mono := hflip_ind σ G hGm
      rcases hGbad with (hnB | hnC) | hnD
      · refine Or.inl (Or.inl fun hBf ↦ hnB fun S hS hu ↦ hBf S (hind_mono S hS) hu)
      · refine Or.inl (Or.inr fun hCf ↦ hnC fun S hS hu hz ↦ hCf S (hind_mono S hS) hu hz)
      · refine Or.inr fun hDf ↦ hnD ?_
        dsimp only [lemma71_D_ind, Set.mem_setOf_eq] at hDf ⊢
        refine le_trans ?_ hDf
        exact Nat.cast_le.mpr (card_filter_le_of_imp_v12 fun S _ ⟨hSi, hrest⟩ ↦
          ⟨hind_mono S hSi, hrest⟩)
    have henn := randomGraphMeasure_image_le_of_involutive (flipMarkedInternal P σ)
      (flipMarkedInternal_involutive P σ) hmap_sub
    exact (ENNReal.toReal_mono (measure_ne_top _ _) henn).trans hBad_ind_prob
  have hCo_bad_ind :
      (randomGraphMeasure n).real (partitionCocoloringEvent P ∩ Bad_ind) ≤
        (eps / 2) * (2 : ℝ) ^ P.parts.card *
          (randomGraphMeasure n).real (partitionColoringEvent P) := by
    have hcov_m : partitionCocoloringEvent P ∩ Bad_ind ⊆
        ⋃ σ ∈ (Finset.univ : Finset (P.parts → Bool)),
          (partitionMarkedEvent P σ ∩ Bad_ind) := by
      intro G ⟨hGco, hGb⟩
      simp only [Set.mem_iUnion, Finset.mem_univ, exists_prop, true_and]
      refine ⟨fun B ↦ decide (G.IsClique (B.1 : Set (Fin n))), ?_, hGb⟩
      intro B
      by_cases hcl : G.IsClique (B.1 : Set (Fin n))
      · simp [hcl]
      · simp only [hcl, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact (hGco B.1 B.2).resolve_right hcl
    calc (randomGraphMeasure n).real (partitionCocoloringEvent P ∩ Bad_ind)
        ≤ ∑ σ ∈ (Finset.univ : Finset (P.parts → Bool)),
            (randomGraphMeasure n).real (partitionMarkedEvent P σ ∩ Bad_ind) :=
          (rg_mono_v12 hcov_m).trans (rg_biUnion_finset_le_v12 _ _)
      _ ≤ ∑ _σ ∈ (Finset.univ : Finset (P.parts → Bool)),
            ((eps / 2) * (randomGraphMeasure n).real (partitionColoringEvent P)) :=
          Finset.sum_le_sum fun σ _ ↦ hmark_bad σ
      _ = (eps / 2) * (2 : ℝ) ^ P.parts.card *
            (randomGraphMeasure n).real (partitionColoringEvent P) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
            Fintype.card_coe, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
          ring
  let Bad_cl : Set (LabeledGraph n) :=
    (lemma71_B_cl (phaseNat n) U_s P)ᶜ ∪ (lemma71_C_cl U_s P)ᶜ ∪ (lemma71_D_cl U_s P c_half)ᶜ
  have hcl_iff_compl : ∀ (G : LabeledGraph n) (S : Finset (Fin n)),
      G.IsClique (S : Set (Fin n)) ↔ Gᶜ.IsIndepSet (S : Set (Fin n)) := by
    intro G S
    constructor
    · intro hcl x hx y hy hxy hadj; exact hadj.2 (hcl hx hy hxy)
    · intro hind x hx y hy hxy
      by_contra hnadj
      exact hind hx hy hxy ⟨hxy, hnadj⟩
  have hCo_bad_cl :
      (randomGraphMeasure n).real (partitionCocoloringEvent P ∩ Bad_cl) ≤
        (eps / 2) * (2 : ℝ) ^ P.parts.card *
          (randomGraphMeasure n).real (partitionColoringEvent P) := by
    have hmap_cl : ∀ G ∈ partitionCocoloringEvent P ∩ Bad_cl,
        Gᶜ ∈ partitionCocoloringEvent P ∩ Bad_ind := by
      rintro G ⟨hGco, hGcl⟩
      have hGco_c : Gᶜ ∈ partitionCocoloringEvent P := by
        intro B hB
        rcases hGco B hB with hind | hcl
        · exact Or.inr ((hcl_iff_compl Gᶜ B).mpr (by simpa [compl_compl] using hind))
        · exact Or.inl ((hcl_iff_compl G B).mp hcl)
      refine ⟨hGco_c, ?_⟩
      rcases hGcl with (hnB | hnC) | hnD
      · refine Or.inl (Or.inl fun hBc ↦ hnB fun S hS hu ↦
          hBc S ((hcl_iff_compl G S).mp hS) hu)
      · refine Or.inl (Or.inr fun hCc ↦ hnC fun S hS hu hz ↦
          hCc S ((hcl_iff_compl G S).mp hS) hu hz)
      · refine Or.inr fun hDc ↦ hnD ?_
        dsimp only [lemma71_D_cl, Set.mem_setOf_eq]
        dsimp only [lemma71_D_ind, Set.mem_setOf_eq] at hDc
        refine le_trans ?_ hDc
        exact Nat.cast_le.mpr (card_filter_le_of_imp_v12 fun S _ ⟨hSc, hrest⟩ ↦
          ⟨(hcl_iff_compl G S).mp hSc, hrest⟩)
    have henn := randomGraphMeasure_image_le_of_involutive
      (fun G : LabeledGraph n ↦ Gᶜ) compl_involutive hmap_cl
    exact (ENNReal.toReal_mono (measure_ne_top _ _) henn).trans hCo_bad_ind
  have hCo_tot : (randomGraphMeasure n).real (partitionCocoloringEvent P) =
      (2 : ℝ) ^ P.parts.card * (randomGraphMeasure n).real (partitionColoringEvent P) := by
    have h := ((randomGraphMeasure_partitionColoring_and_marked_inter_crossEvent_eq P).2
      Set.univ (by simp)).2 hP2
    simpa using h
  have hCo_good :
      (1 - eps) * (2 : ℝ) ^ P.parts.card *
          (randomGraphMeasure n).real (partitionColoringEvent P) ≤
        (randomGraphMeasure n).real
          (partitionCocoloringEvent P ∩ lemma71_B_ind (phaseNat n) U_s P ∩
            lemma71_C_ind U_s P ∩ lemma71_D_ind U_s P c_half ∩
            lemma71_B_cl (phaseNat n) U_s P ∩ lemma71_C_cl U_s P ∩
            lemma71_D_cl U_s P c_half) := by
    have hcov_co : partitionCocoloringEvent P ⊆
        (partitionCocoloringEvent P ∩ lemma71_B_ind (phaseNat n) U_s P ∩
            lemma71_C_ind U_s P ∩ lemma71_D_ind U_s P c_half ∩
            lemma71_B_cl (phaseNat n) U_s P ∩ lemma71_C_cl U_s P ∩
            lemma71_D_cl U_s P c_half) ∪
          ((partitionCocoloringEvent P ∩ Bad_ind) ∪
            (partitionCocoloringEvent P ∩ Bad_cl)) := by
      intro G hGco
      by_cases h1 : G ∈ lemma71_B_ind (phaseNat n) U_s P
      · by_cases h2 : G ∈ lemma71_C_ind U_s P
        · by_cases h3 : G ∈ lemma71_D_ind U_s P c_half
          · by_cases h4 : G ∈ lemma71_B_cl (phaseNat n) U_s P
            · by_cases h5 : G ∈ lemma71_C_cl U_s P
              · by_cases h6 : G ∈ lemma71_D_cl U_s P c_half
                · exact Or.inl ⟨⟨⟨⟨⟨⟨hGco, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
                · exact Or.inr (Or.inr ⟨hGco, Or.inr h6⟩)
              · exact Or.inr (Or.inr ⟨hGco, Or.inl (Or.inr h5)⟩)
            · exact Or.inr (Or.inr ⟨hGco, Or.inl (Or.inl h4)⟩)
          · exact Or.inr (Or.inl ⟨hGco, Or.inr h3⟩)
        · exact Or.inr (Or.inl ⟨hGco, Or.inl (Or.inr h2)⟩)
      · exact Or.inr (Or.inl ⟨hGco, Or.inl (Or.inl h1)⟩)
    have htot := (rg_mono_v12 hcov_co).trans
      ((measureReal_union_le _ _).trans (add_le_add le_rfl (measureReal_union_le _ _)))
    rw [hCo_tot] at htot
    have hring_co :
        (1 - eps) * (2 : ℝ) ^ P.parts.card *
            (randomGraphMeasure n).real (partitionColoringEvent P) =
          (2 : ℝ) ^ P.parts.card * (randomGraphMeasure n).real (partitionColoringEvent P) -
            ((eps / 2) * (2 : ℝ) ^ P.parts.card *
                (randomGraphMeasure n).real (partitionColoringEvent P) +
              (eps / 2) * (2 : ℝ) ^ P.parts.card *
                (randomGraphMeasure n).real (partitionColoringEvent P)) := by ring
    linarith [hCo_bad_ind, hCo_bad_cl, hring_co]
  exact ⟨hCh_good, hCo_good⟩

open scoped Classical in
/-- **Complete unconditional Lemma 7.1 (`lem:hp-first`, `main.tex` lines 956–965):**
for every `M : ℕ` and `eps ∈ (0, 1)`, eventually in `n` (with `α = phaseNat n`,
`U = [α - (M + 1), α]`, `c_full = (log n)³`, `c_half = (1/2) (log n)³`), uniformly across all
partitions `P` with part sizes in `U` and all finite partition families `(P i)_{i ∈ S_idx}`:
1. `P(A_P ∩ B_Pᶜ)`, `P(A_P ∩ C_Pᶜ)`, and `P(A_P ∩ D_Pᶜ)` are each `≤ (eps / 6) · P(A_P)`,
2. `(1 - eps) · P(A_P) ≤ P(A_P ∩ B_P ∩ C_P ∩ D'_P)` and
   `(1 - eps) · 2^|P.parts| · P(A_P) ≤ P(A_P^co ∩ B_P ∩ C_P ∩ D_P ∩ B_P^cl ∩ C_P^cl ∩ D_P^cl)`,
3. `(1 - eps) · ∑_{i ∈ S_idx} P(A_{P i}) ≤ E[Z^{ch}]` and
   `(1 - eps) · ∑_{i ∈ S_idx} 2^|(P i).parts| · P(A_{P i}) ≤ E[Z]`,
4. `E[(Z^{ch})²] ≤ ∑_{(i,j) ∈ Π_rel(⌊(log n)³⌋₊)} P(A_{P i} ∩ A_{P j})` and
   `E[Z²] ≤ ∑_{(i,j) ∈ Π_rel(⌊2 · (1/2)(log n)³⌋₊)} P(A_{P i}^co ∩ A_{P j}^co)`. -/
theorem eventually_lemma71_complete_regularity
    (M : ℕ) {eps : ℝ} (heps : eps ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᶠ n : ℕ in atTop,
      let α : ℕ := phaseNat n
      let U_sizes : Set ℕ := {s : ℕ | α - (M + 1) ≤ s ∧ s ≤ α}
      let c_full : ℝ := (Real.log (n : ℝ)) ^ 3
      let c_half : ℝ := (1 / 2 : ℝ) * (Real.log (n : ℝ)) ^ 3
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
      (∀ P : VertexPartition n, (∀ D ∈ P.parts, D.card ∈ U_sizes) →
        (randomGraphMeasure n).real (partitionColoringEvent P ∩ (B_ind P)ᶜ) ≤
            (eps / 6) * (randomGraphMeasure n).real (partitionColoringEvent P) ∧
          (randomGraphMeasure n).real (partitionColoringEvent P ∩ (C_ind P)ᶜ) ≤
            (eps / 6) * (randomGraphMeasure n).real (partitionColoringEvent P) ∧
          (randomGraphMeasure n).real (partitionColoringEvent P ∩ (D_ind P c_half)ᶜ) ≤
            (eps / 6) * (randomGraphMeasure n).real (partitionColoringEvent P) ∧
          (1 - eps) * (randomGraphMeasure n).real (partitionColoringEvent P) ≤
            (randomGraphMeasure n).real
              (partitionColoringEvent P ∩ B_ind P ∩ C_ind P ∩ D_ind P c_full) ∧
          (1 - eps) * (2 : ℝ) ^ P.parts.card *
              (randomGraphMeasure n).real (partitionColoringEvent P) ≤
            (randomGraphMeasure n).real
              (partitionCocoloringEvent P ∩ B_ind P ∩ C_ind P ∩ D_ind P c_half ∩
                B_cl P ∩ C_cl P ∩ D_cl P c_half)) ∧
      (∀ (S_idx : Finset ℕ) (P : ℕ → VertexPartition n),
        (∀ i ∈ S_idx, ∀ D ∈ (P i).parts, D.card ∈ U_sizes) →
        let Z_ch : LabeledGraph n → ℝ := fun G ↦
          ∑ i ∈ S_idx,
            if G ∈ partitionColoringEvent (P i) ∩ B_ind (P i) ∩ C_ind (P i) ∩ D_ind (P i) c_full
            then (1 : ℝ) else 0
        let Z_co : LabeledGraph n → ℝ := fun G ↦
          ∑ i ∈ S_idx,
            if G ∈ partitionCocoloringEvent (P i) ∩ B_ind (P i) ∩ C_ind (P i) ∩
                D_ind (P i) c_half ∩ B_cl (P i) ∩ C_cl (P i) ∩ D_cl (P i) c_half
            then (1 : ℝ) else 0
        (1 - eps) * (∑ i ∈ S_idx, (randomGraphMeasure n).real (partitionColoringEvent (P i))) ≤
            (∫ G : LabeledGraph n, Z_ch G ∂randomGraphMeasure n) ∧
          (1 - eps) * (∑ i ∈ S_idx,
              (2 : ℝ) ^ (P i).parts.card *
                (randomGraphMeasure n).real (partitionColoringEvent (P i))) ≤
            (∫ G : LabeledGraph n, Z_co G ∂randomGraphMeasure n) ∧
          (∫ G : LabeledGraph n, (Z_ch G) ^ 2 ∂randomGraphMeasure n) ≤
            ∑ p ∈ (S_idx ×ˢ S_idx).filter (fun p ↦ RelPair (Nat.floor c_full) (P p.1) (P p.2)),
              (randomGraphMeasure n).real
                (partitionColoringEvent (P p.1) ∩ partitionColoringEvent (P p.2)) ∧
          (∫ G : LabeledGraph n, (Z_co G) ^ 2 ∂randomGraphMeasure n) ≤
            ∑ p ∈ (S_idx ×ˢ S_idx).filter (fun p ↦ RelPair (Nat.floor (2 * c_half)) (P p.1) (P p.2)),
              (randomGraphMeasure n).real
                (partitionCocoloringEvent (P p.1) ∩ partitionCocoloringEvent (P p.2))) := by
  obtain ⟨heps_pos, _heps_lt1⟩ := heps
  have he6 : 0 < eps / 6 := by positivity
  have hph_ge : ∀ᶠ n : ℕ in atTop, M + 4 ≤ phaseNat n := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop ((M + 4 : ℕ) : ℝ),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact_mod_cast hn.trans hph.1
  filter_upwards [eventually_condProb_badZComposed_tendsto_zero M he6,
    eventually_condProb_badTwoClassSplit_tendsto_zero M he6,
    eventually_condProb_manyNearParts_tendsto_zero M (c_D := 1 / 2) (by norm_num) he6,
    hph_ge, eventually_gt_atTop 2] with
    n hB_ev hC_ev hD_ev hphM hn2
  intro α U_sizes c_full c_half B_ind C_ind D_ind B_cl C_cl D_cl RelPair
  have hDi : ∀ (Q : VertexPartition n) (c_cap : ℝ), D_ind Q c_cap = lemma71_D_ind U_sizes Q c_cap := by
    intro Q c_cap; ext G
    dsimp only [D_ind, lemma71_D_ind, Set.mem_setOf_eq]
    constructor <;> intro hle <;> refine le_trans ?_ hle <;>
      exact Nat.cast_le.mpr (card_filter_le_of_imp_v12 fun _ _ h ↦ h)
  have hDc : ∀ (Q : VertexPartition n) (c_cap : ℝ), D_cl Q c_cap = lemma71_D_cl U_sizes Q c_cap := by
    intro Q c_cap; ext G
    dsimp only [D_cl, lemma71_D_cl, Set.mem_setOf_eq]
    constructor <;> intro hle <;> refine le_trans ?_ hle <;>
      exact Nat.cast_le.mpr (card_filter_le_of_imp_v12 fun _ _ h ↦ h)
  have hSingle : ∀ P : VertexPartition n, (∀ D ∈ P.parts, D.card ∈ U_sizes) →
      (randomGraphMeasure n).real (partitionColoringEvent P ∩ (B_ind P)ᶜ) ≤
          (eps / 6) * (randomGraphMeasure n).real (partitionColoringEvent P) ∧
        (randomGraphMeasure n).real (partitionColoringEvent P ∩ (C_ind P)ᶜ) ≤
          (eps / 6) * (randomGraphMeasure n).real (partitionColoringEvent P) ∧
        (randomGraphMeasure n).real (partitionColoringEvent P ∩ (D_ind P c_half)ᶜ) ≤
          (eps / 6) * (randomGraphMeasure n).real (partitionColoringEvent P) ∧
        (1 - eps) * (randomGraphMeasure n).real (partitionColoringEvent P) ≤
          (randomGraphMeasure n).real
            (partitionColoringEvent P ∩ B_ind P ∩ C_ind P ∩ D_ind P c_full) ∧
        (1 - eps) * (2 : ℝ) ^ P.parts.card *
            (randomGraphMeasure n).real (partitionColoringEvent P) ≤
          (randomGraphMeasure n).real
            (partitionCocoloringEvent P ∩ B_ind P ∩ C_ind P ∩ D_ind P c_half ∩
              B_cl P ∩ C_cl P ∩ D_cl P c_half) := by
    intro P hPU
    have hPa : ∀ D ∈ P.parts, D.card ≤ phaseNat n := fun D hD ↦ (hPU D hD).2
    have hB_b : (randomGraphMeasure n).real (partitionColoringEvent P ∩ (lemma71_B_ind α U_sizes P)ᶜ) ≤
        (eps / 6) * (randomGraphMeasure n).real (partitionColoringEvent P) := by
      refine (le_of_eq ?_).trans (hB_ev P hPa)
      congr 2; ext G; simp [lemma71_B_ind, U_sizes, α, and_imp]
    have hC_b : (randomGraphMeasure n).real (partitionColoringEvent P ∩ (lemma71_C_ind U_sizes P)ᶜ) ≤
        (eps / 6) * (randomGraphMeasure n).real (partitionColoringEvent P) := by
      refine (le_of_eq ?_).trans (hC_ev P hPa)
      congr 2; ext G; simp [lemma71_C_ind, U_sizes, α, and_imp]
    have hD_b : (randomGraphMeasure n).real (partitionColoringEvent P ∩ (lemma71_D_ind U_sizes P c_half)ᶜ) ≤
        (eps / 6) * (randomGraphMeasure n).real (partitionColoringEvent P) := by
      have hset_eq : lemma71_D_ind U_sizes P c_half =
          {G : LabeledGraph n |
            (((Finset.univ : Finset (Fin n)).powerset.filter fun S : Finset (Fin n) ↦
              G.IsIndepSet (S : Set (Fin n)) ∧
              phaseNat n - (M + 1) ≤ S.card ∧
              S.card ≤ phaseNat n ∧
              (P.parts.filter fun E ↦ (S ∩ E).Nonempty).card = 2 ∧
              ∃ E ∈ P.parts, E.card - 1 ≤ (S ∩ E).card).card : ℝ) ≤
            (1 / 2 : ℝ) * (Real.log (n : ℝ)) ^ 3} := by
        ext G
        dsimp only [lemma71_D_ind, c_half, Set.mem_setOf_eq]
        constructor <;> intro hle <;> refine le_trans ?_ hle <;>
          exact Nat.cast_le.mpr (card_filter_le_of_imp_v12 fun S _ hS ↦ by
            simpa only [U_sizes, α, Set.mem_setOf_eq, and_assoc] using hS)
      rw [hset_eq]
      exact (hD_ev P hPU).2
    obtain ⟨hCh_g, hCo_g⟩ := lemma71_single_partition_bounds_v12 heps_pos hn2 hphM hB_b hC_b hD_b hPU
    have hD_b' : (randomGraphMeasure n).real (partitionColoringEvent P ∩ (D_ind P c_half)ᶜ) ≤
        (eps / 6) * (randomGraphMeasure n).real (partitionColoringEvent P) := by
      rw [hDi P c_half]; exact hD_b
    have hCh_g' : (1 - eps) * (randomGraphMeasure n).real (partitionColoringEvent P) ≤
        (randomGraphMeasure n).real
          (partitionColoringEvent P ∩ B_ind P ∩ C_ind P ∩ D_ind P c_full) := by
      change (1 - eps) * (randomGraphMeasure n).real (partitionColoringEvent P) ≤
        (randomGraphMeasure n).real
          (partitionColoringEvent P ∩ lemma71_B_ind α U_sizes P ∩
            lemma71_C_ind U_sizes P ∩ D_ind P c_full)
      rw [hDi P c_full]; exact hCh_g
    have hCo_g' : (1 - eps) * (2 : ℝ) ^ P.parts.card *
          (randomGraphMeasure n).real (partitionColoringEvent P) ≤
        (randomGraphMeasure n).real
          (partitionCocoloringEvent P ∩ B_ind P ∩ C_ind P ∩ D_ind P c_half ∩
            B_cl P ∩ C_cl P ∩ D_cl P c_half) := by
      change (1 - eps) * (2 : ℝ) ^ P.parts.card *
          (randomGraphMeasure n).real (partitionColoringEvent P) ≤
        (randomGraphMeasure n).real
          (partitionCocoloringEvent P ∩ lemma71_B_ind α U_sizes P ∩
            lemma71_C_ind U_sizes P ∩ D_ind P c_half ∩
            lemma71_B_cl α U_sizes P ∩ lemma71_C_cl U_sizes P ∩ D_cl P c_half)
      rw [hDi P c_half, hDc P c_half]; exact hCo_g
    exact ⟨hB_b, hC_b, hD_b', hCh_g', hCo_g'⟩
  refine ⟨hSingle, ?_⟩
  intro S_idx P hP_fam Z_ch Z_co
  have hsq_rel := sq_regularPartitionSum_le_relevantPairs_and_integral_le
    (α := α) U_sizes S_idx P hP_fam c_full c_half
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hsum_ch : ∀ G : LabeledGraph n, Z_ch G =
        ∑ i ∈ S_idx,
          (partitionColoringEvent (P i) ∩ B_ind (P i) ∩ C_ind (P i) ∩ D_ind (P i) c_full).indicator
            (fun _ ↦ (1 : ℝ)) G := by
      intro G; dsimp only [Z_ch]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      by_cases hG : G ∈ partitionColoringEvent (P i) ∩ B_ind (P i) ∩ C_ind (P i) ∩ D_ind (P i) c_full
      · rw [if_pos hG, Set.indicator_of_mem hG]
      · rw [if_neg hG, Set.indicator_of_notMem hG]
    rw [integral_congr_ae (Eventually.of_forall hsum_ch),
      integral_finsetSum _ fun _ _ ↦ Integrable.of_finite, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi ↦ ?_
    rw [integral_indicator_const _ (Set.toFinite _).measurableSet, smul_eq_mul, mul_one]
    exact (hSingle (P i) (hP_fam i hi)).2.2.2.1
  · have hsum_co : ∀ G : LabeledGraph n, Z_co G =
        ∑ i ∈ S_idx,
          (partitionCocoloringEvent (P i) ∩ B_ind (P i) ∩ C_ind (P i) ∩ D_ind (P i) c_half ∩
            B_cl (P i) ∩ C_cl (P i) ∩ D_cl (P i) c_half).indicator (fun _ ↦ (1 : ℝ)) G := by
      intro G; dsimp only [Z_co]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      by_cases hG : G ∈ partitionCocoloringEvent (P i) ∩ B_ind (P i) ∩ C_ind (P i) ∩
          D_ind (P i) c_half ∩ B_cl (P i) ∩ C_cl (P i) ∩ D_cl (P i) c_half
      · rw [if_pos hG, Set.indicator_of_mem hG]
      · rw [if_neg hG, Set.indicator_of_notMem hG]
    rw [integral_congr_ae (Eventually.of_forall hsum_co),
      integral_finsetSum _ fun _ _ ↦ Integrable.of_finite, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi ↦ ?_
    rw [integral_indicator_const _ (Set.toFinite _).measurableSet, smul_eq_mul, mul_one,
      ← mul_assoc]
    exact (hSingle (P i) (hP_fam i hi)).2.2.2.2
  · refine (integral_congr_ae (Eventually.of_forall fun G ↦ ?_)).le.trans
      (hsq_rel.1.2.trans_eq
        (Finset.sum_congr (filter_eq_of_iff_v12 fun _ _ ↦ Iff.rfl) fun _ _ ↦ rfl))
    dsimp only [Z_ch]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ite_eq_of_iff_v12 ?_ 1 0
    refine inter_iff_of_eq_v12 Iff.rfl ?_
    dsimp only [D_ind, Set.mem_setOf_eq]
    exact ⟨fun hle ↦ le_trans (Nat.cast_le.mpr (card_filter_le_of_imp_v12 fun _ _ h ↦ h)) hle,
      fun hle ↦ le_trans (Nat.cast_le.mpr (card_filter_le_of_imp_v12 fun _ _ h ↦ h)) hle⟩
  · refine (integral_congr_ae (Eventually.of_forall fun G ↦ ?_)).le.trans
      (hsq_rel.2.2.trans_eq
        (Finset.sum_congr (filter_eq_of_iff_v12 fun _ _ ↦ Iff.rfl) fun _ _ ↦ rfl))
    dsimp only [Z_co]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ite_eq_of_iff_v12 ?_ 1 0
    refine inter_iff_of_eq_v12
      (inter_iff_of_eq_v12
        (inter_iff_of_eq_v12
          (inter_iff_of_eq_v12 Iff.rfl ?_) Iff.rfl) Iff.rfl) ?_
    · dsimp only [D_ind, Set.mem_setOf_eq]
      exact ⟨fun hle ↦ le_trans (Nat.cast_le.mpr (card_filter_le_of_imp_v12 fun _ _ h ↦ h)) hle,
        fun hle ↦ le_trans (Nat.cast_le.mpr (card_filter_le_of_imp_v12 fun _ _ h ↦ h)) hle⟩
    · dsimp only [D_cl, Set.mem_setOf_eq]
      exact ⟨fun hle ↦ le_trans (Nat.cast_le.mpr (card_filter_le_of_imp_v12 fun _ _ h ↦ h)) hle,
        fun hle ↦ le_trans (Nat.cast_le.mpr (card_filter_le_of_imp_v12 fun _ _ h ↦ h)) hle⟩

/-!
## 7. Complete v12 Phase Refinement & Main Theorem syntheses (coupling-independent `∃ N : ℕ`)
-/

/-- **Complete v12 Phase Refinement synthesis (`main.tex` lines 235–251):**
eliminates the abstract `tildeEps` parameter of `phaseRefinement_v11_complete` by deriving the
explicit `O(log log n / log n)` moving-corridor error directly from Proposition 4.1(i)
(`eventually_randomGraph_lowerTails_prop41_i`) + unconditional Proposition 5.3(iii) `(5.20)`
(`eventually_allSupport_corridorRoot_separation_and_prop53_iii`), taking ONLY the single
Corollary 8.1 `(m_n, 7)` upper-tail hypothesis `hUpper7`, AND places `∃ N : ℕ` **outside**
`∀ {Ω} [MeasurableSpace Ω] (ℙ) [IsProbabilityMeasure ℙ] (G)` in the coupling-uniform `∃ m ≥ n`
sub-Gaussian tail-union bound. -/
theorem phaseRefinement_v12_complete
    (hUpper7 : ∃ C_up C_w : ℝ, 0 < C_up ∧ 0 < C_w ∧
      ∀ᶠ n : ℕ in atTop,
        let m_n : ℕ := boundaryShift (phaseDelta n)
        let F_win : ℝ → ℝ := fun T ↦ ⨅ l : ℝ,
          (Real.log (∑ i ∈ Finset.Icc (m_n + 1) (m_n + 7),
              Real.exp (l * (i : ℝ) +
                (Real.log ((phaseNat n).descFactorial i : ℝ) -
                  (i : ℝ) * Real.log (phaseNat n : ℝ) -
                  Real.log 2 / 2 * (i : ℝ) ^ 2))) - l * T)
        let obj_win : ℝ → ℝ → ℝ := fun tau s ↦
          (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + s - s * Real.log s +
            s * (profileDeficitAffineA (phaseNat n) +
              profileDeficitAffineB (phaseNat n) * fourSizeTarget n (phaseNat n) s +
              F_win (fourSizeTarget n (phaseNat n) s) + tau)
        ∃ r_winCo ∈ Set.Icc (phaseRootCenter n - C_w * logLogOrder n * phaseRootGapRadius n)
                            (phaseRootCenter n + C_w * logLogOrder n * phaseRootGapRadius n),
          obj_win (Real.log 2) r_winCo = 0 ∧
          ∃ r_win0 ∈ Set.Icc (phaseRootCenter n - C_w * logLogOrder n * phaseRootGapRadius n)
                             (phaseRootCenter n + C_w * logLogOrder n * phaseRootGapRadius n),
            obj_win 0 r_win0 = 0 ∧
            let k_co : ℕ := Nat.ceil r_winCo + 16
            let k_ch : ℕ := Nat.ceil r_win0 + Nat.ceil (Real.log (n : ℝ))
            (randomGraphMeasure n).real
                ({G : LabeledGraph n |
                    (k_co : ℝ) + universalAllowance n < (cochromaticNumber G : ℝ)} ∪
                  {G : LabeledGraph n |
                    (k_ch : ℝ) + universalAllowance n < (chromaticNumberNat G : ℝ)}) ≤
              C_up * quasiExpTail n) :
    let c₇ : ℝ := (Real.log 2) ^ 2 / 4 * sInf (phaseGain7 '' Set.Icc deltaStar (1 + deltaStar))
    let C₇ : ℝ := (Real.log 2) ^ 3 / 2 - c₇
    (80 / 1000 < (Real.log 2) ^ 2 / 4 * Real.log (391 / 200) ∧
      (Real.log 2) ^ 2 / 4 * Real.log (391 / 200) < c₇ ∧
      C₇ < (Real.log 2) ^ 2 / 4 * Real.log (800 / 391) ∧
      (Real.log 2) ^ 2 / 4 * Real.log (800 / 391) < 86 / 1000) ∧
    (∃ eps : ℕ → ℝ,
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
            upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + eps n)) ∧
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
      (∃ N : ℕ,
        ∀ {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
          (G : ∀ m : ℕ, Ω → LabeledGraph m),
          (∀ m : ℕ, 2 ≤ m → Measure.map (G m) ℙ = randomGraphMeasure m) →
          (∀ n ≥ N,
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
  intro c₇ C₇
  obtain ⟨C_up, C_w, hC_up_pos, hC_w_pos, hUpEv⟩ := hUpper7
  obtain ⟨_, C_inf, _, hC_inf_pos, hLowEv⟩ := eventually_randomGraph_lowerTails_prop41_i
  set C_all : ℝ := max C_w C_inf
  have hC_all_nn : 0 ≤ C_all := le_trans hC_w_pos.le (le_max_left _ _)
  obtain ⟨K_sep, hK_sep_pos, hSepEv⟩ :=
    eventually_allSupport_corridorRoot_separation_and_prop53_iii (M := 7) C_all hC_all_nn
  let tildeEps : ℕ → ℝ := fun n ↦
    if 3 ≤ n then K_sep * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) else 0
  have htilde_nn : ∀ n : ℕ, 0 ≤ tildeEps n := by
    intro n
    dsimp [tildeEps]
    split_ifs with hn3
    · have hL_gt1 : 1 < Real.log (n : ℝ) := by
        have he_lt3 : Real.exp 1 < (n : ℝ) :=
          lt_of_lt_of_le (lt_trans Real.exp_one_lt_d9 (by norm_num : (2.7182818286 : ℝ) < 3))
            (show (3 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn3)
        simpa using Real.log_lt_log (Real.exp_pos 1) he_lt3
      exact div_nonneg (mul_nonneg hK_sep_pos.le (Real.log_nonneg hL_gt1.le)) (by linarith)
    · exact le_rfl
  have htilde_O : tildeEps =O[atTop] (fun n : ℕ ↦
      Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) := by
    refine IsBigO.of_bound K_sep ?_
    filter_upwards [eventually_ge_atTop 3] with n hn3
    have hL_gt1 : 1 < Real.log (n : ℝ) := by
      have he_lt3 : Real.exp 1 < (n : ℝ) :=
        lt_of_lt_of_le (lt_trans Real.exp_one_lt_d9 (by norm_num : (2.7182818286 : ℝ) < 3))
          (show (3 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn3)
      simpa using Real.log_lt_log (Real.exp_pos 1) he_lt3
    have hdiv_nn : 0 ≤ Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) :=
      div_nonneg (Real.log_nonneg hL_gt1.le) (by linarith)
    have hnum_nn : 0 ≤ K_sep * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) :=
      div_nonneg (mul_nonneg hK_sep_pos.le (Real.log_nonneg hL_gt1.le)) (by linarith)
    simp only [tildeEps, if_pos hn3, Real.norm_eq_abs, abs_of_nonneg hnum_nn, abs_of_nonneg hdiv_nn]
    exact (mul_div_assoc K_sep _ _).le
  have htail_two :
      (fun n : ℕ ↦ (randomGraphMeasure n).real
        (twoSidedGapEvent
          (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - tildeEps n)
          (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + tildeEps n) n)ᶜ)
      =O[atTop] quasiExpTail := by
    refine IsBigO.of_bound (6 + C_up) ?_
    filter_upwards [hUpEv, hLowEv, hSepEv,
      eventually_mu_phaseNat_succ_and_deltaStar_le_v12,
      eventually_phaseRoot_domain_pos_and_target_corridor,
      tendsto_logLogOrder_atTop.eventually_ge_atTop 1,
      eventually_ge_atTop 3] with n hUp hLow hSep hMuBds hcenterDom hw1 hn3
    set m_n : ℕ := boundaryShift (phaseDelta n)
    have hm_le1 : m_n ≤ 1 := by
      dsimp [m_n]; unfold boundaryShift; split_ifs <;> omega
    have hmu1 : m_n = 1 → mu n (phaseNat n) ≤ (n : ℝ) / (16 * Real.log (n : ℝ)) := by
      intro hm1
      have hd_lt : phaseDelta n < deltaStar := by
        by_contra hge
        have hm0 : m_n = 0 := by dsimp [m_n]; unfold boundaryShift; rw [if_neg hge]
        omega
      exact hMuBds.2.2 hd_lt.le
    obtain ⟨⟨r_inf0, ⟨hr_inf0_ioo, hz_inf0⟩, _⟩, ⟨r_infCo, ⟨hr_infCo_ioo, hz_infCo⟩, _⟩, hLowTails⟩ :=
      hLow m_n hm_le1 hmu1
    have hr_inf0_icc := Ioo_subset_Icc_self hr_inf0_ioo
    have hr_infCo_icc := Ioo_subset_Icc_self hr_infCo_ioo
    have hLow_r := hLowTails r_inf0 hr_inf0_icc hz_inf0 r_infCo hr_infCo_icc hz_infCo
    obtain ⟨r_winCo, hr_winCo_w, hz_winCo, r_win0, hr_win0_w, hz_win0, hUpTail⟩ := hUp
    have hw_nn : 0 ≤ logLogOrder n * phaseRootGapRadius n := by
      unfold phaseRootGapRadius
      have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
      exact mul_nonneg (by linarith) (div_nonneg (div_nonneg hn_pos.le
        hcenterDom.2.1.le) (sq_nonneg _))
    have hsub_w : Set.Icc (phaseRootCenter n - C_w * logLogOrder n * phaseRootGapRadius n)
                          (phaseRootCenter n + C_w * logLogOrder n * phaseRootGapRadius n) ⊆
                  Set.Icc (phaseRootCenter n - C_all * logLogOrder n * phaseRootGapRadius n)
                          (phaseRootCenter n + C_all * logLogOrder n * phaseRootGapRadius n) := by
      intro x hx
      have hm := mul_le_mul_of_nonneg_right (le_max_left C_w C_inf) hw_nn
      exact ⟨by linarith [hx.1, hm], by linarith [hx.2, hm]⟩
    have hsub_inf : Set.Icc (phaseRootCenter n - C_inf * logLogOrder n * phaseRootGapRadius n)
                            (phaseRootCenter n + C_inf * logLogOrder n * phaseRootGapRadius n) ⊆
                    Set.Icc (phaseRootCenter n - C_all * logLogOrder n * phaseRootGapRadius n)
                            (phaseRootCenter n + C_all * logLogOrder n * phaseRootGapRadius n) := by
      intro x hx
      have hm := mul_le_mul_of_nonneg_right (le_max_right C_w C_inf) hw_nn
      exact ⟨by linarith [hx.1, hm], by linarith [hx.2, hm]⟩
    have hbr := (hSep.2.2 m_n 7 hm_le1 le_rfl le_rfl
      r_inf0 (hsub_inf hr_inf0_icc) r_infCo (hsub_inf hr_infCo_icc)
      r_winCo (hsub_w hr_winCo_w) r_win0 (hsub_w hr_win0_w)
      hz_inf0 hz_infCo hz_winCo hz_win0).2.2 rfl rfl
    obtain ⟨_, _, _, _, _, _, hbr_lo, hbr_hi⟩ := hbr
    set t_n : ℝ := universalShift n
    set d_m : ℕ := Nat.ceil (mu n (phaseNat n + 1 - m_n) + t_n)
    set k_chi : ℕ := Nat.floor r_inf0 - Nat.ceil t_n - 2 * d_m
    set k_zeta : ℕ := Nat.floor r_infCo - Nat.ceil t_n - 4 * d_m
    set k_co : ℕ := Nat.ceil r_winCo + 16
    set k_ch : ℕ := Nat.ceil r_win0 + Nat.ceil (Real.log (n : ℝ))
    obtain ⟨_, _, _, hk_chi_int, hk_zeta_int, _, _, hchi_3q, hzeta_3q⟩ := hLow_r
    have hk_chi_real : (k_chi : ℝ) =
        ((⌊r_inf0⌋ - (Nat.ceil t_n : ℤ) - 2 * (d_m : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast hk_chi_int
    have hk_zeta_real : (k_zeta : ℝ) =
        ((⌊r_infCo⌋ - (Nat.ceil t_n : ℤ) - 4 * (d_m : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast hk_zeta_int
    have hbad_sub :
        (twoSidedGapEvent
          (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - tildeEps n)
          (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + tildeEps n) n)ᶜ ⊆
        ({G : LabeledGraph n | chromaticNumberNat G ≤ k_chi} ∪
          {G : LabeledGraph n | cochromaticNumber G ≤ k_zeta}) ∪
        ({G : LabeledGraph n | (k_co : ℝ) + universalAllowance n < (cochromaticNumber G : ℝ)} ∪
          {G : LabeledGraph n | (k_ch : ℝ) + universalAllowance n < (chromaticNumberNat G : ℝ)}) := by
      intro G hGnot
      by_cases h1 : chromaticNumberNat G ≤ k_chi
      · exact Or.inl (Or.inl h1)
      · by_cases h2 : cochromaticNumber G ≤ k_zeta
        · exact Or.inl (Or.inr h2)
        · by_cases h3 : (k_co : ℝ) + universalAllowance n < (cochromaticNumber G : ℝ)
          · exact Or.inr (Or.inl h3)
          · by_cases h4 : (k_ch : ℝ) + universalAllowance n < (chromaticNumberNat G : ℝ)
            · exact Or.inr (Or.inr h4)
            · exfalso
              apply hGnot
              unfold twoSidedGapEvent
              simp only [Set.mem_setOf_eq, tildeEps, if_pos hn3]
              have hchi_gt : (k_chi : ℝ) < (chromaticNumberNat G : ℝ) :=
                by exact_mod_cast not_le.mp h1
              have hzeta_gt : (k_zeta : ℝ) < (cochromaticNumber G : ℝ) :=
                by exact_mod_cast not_le.mp h2
              have hzeta_le : (cochromaticNumber G : ℝ) ≤ (k_co : ℝ) + universalAllowance n :=
                not_lt.mp h3
              have hchi_le : (chromaticNumberNat G : ℝ) ≤ (k_ch : ℝ) + universalAllowance n :=
                not_lt.mp h4
              rw [← hk_chi_real] at hbr_lo
              rw [← hk_zeta_real] at hbr_hi
              exact ⟨by linarith [hbr_lo], by linarith [hbr_hi]⟩
    have hprob_le :
        (randomGraphMeasure n).real
          (twoSidedGapEvent
            (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - tildeEps n)
            (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + tildeEps n) n)ᶜ ≤
        (6 + C_up) * quasiExpTail n := by
      calc (randomGraphMeasure n).real _
          ≤ ((randomGraphMeasure n).real {G | chromaticNumberNat G ≤ k_chi} +
              (randomGraphMeasure n).real {G | cochromaticNumber G ≤ k_zeta}) +
            (randomGraphMeasure n).real
              ({G | (k_co : ℝ) + universalAllowance n < (cochromaticNumber G : ℝ)} ∪
                {G | (k_ch : ℝ) + universalAllowance n < (chromaticNumberNat G : ℝ)}) :=
            (rg_mono_v12 hbad_sub).trans
              ((measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl))
        _ ≤ (6 + C_up) * quasiExpTail n := by linarith [hchi_3q, hzeta_3q, hUpTail]
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg,
      Real.norm_eq_abs, abs_of_pos (show 0 < quasiExpTail n by unfold quasiExpTail; positivity)]
    exact hprob_le
  obtain ⟨hbounds, h1_eps, h2_mov, h3_exp, hv11_fixed0⟩ :=
    phaseRefinement_v11_complete.{0} tildeEps htilde_nn htilde_O htail_two
  refine ⟨hbounds, ⟨_, h1_eps, h2_mov, h3_exp⟩, ?_⟩
  intro c' C' ϑ hc' hC' hϑ η₀
  obtain ⟨htail_single, hexp_fixed, -⟩ := hv11_fixed0 hc' hC' hϑ
  have hη₀_pos : 0 < η₀ := lt_min (by linarith) (by linarith)
  obtain ⟨N_u, hN_u⟩ := eventually_coupling_tailUnion_of_subgaussian_marginals
    (fun m ↦ (twoSidedGapEvent c' C' m)ᶜ) (sq_pos_of_pos hη₀_pos)
    (fun {_} hϑ₁ ↦ (hv11_fixed0 hc' hC' hϑ₁).1) hϑ
  refine ⟨htail_single, hexp_fixed, max 2 N_u, ?_⟩
  intro Ω _ ℙ _ G hMarg
  have hae_u :=
    (((phaseRefinement_v11_complete tildeEps htilde_nn htilde_O htail_two).2.2.2.2 hc' hC' hϑ).2.2
      ℙ G hMarg).2
  refine ⟨?_, hae_u⟩
  intro n hn
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
    refine exists_congr fun m ↦ and_congr_right fun hmn ↦ ?_
    have hm2 : 2 ≤ m := le_trans hn2 hmn
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
            ((chromaticNumberNat (G m ω) : ℝ) - (cochromaticNumber (G m ω) : ℝ)) *
            ((m : ℝ) / (Real.log (m : ℝ)) ^ 3) =
          (chromaticNumberNat (G m ω) : ℝ) - (cochromaticNumber (G m ω) : ℝ) := by
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
  rw [hset]
  exact hN_u ℙ G hMarg n hn_Nu

/-- **Complete v12 Main Theorem `(i)–(iv)` synthesis (`main.tex` lines 107–135):**
upgrades `mainTheorem_v11_complete` with:
- in `(i)`: the non-asymptotic coupling-uniform `2 (1/η + 1/n) n^(-η)` tail-union bound and
  arbitrary-coupling almost-sure `√(2 n log n)` fluctuation envelope
  (`coupling_tailUnion_chromaticSubCochromatic_sqrt_log_le` and
  `ae_limsup_chromaticSubCochromatic_and_normalizedGap_le_one`);
- in `(iii)`: coupling-independent `∃ N : ℕ` placed **outside**
  `∀ {Ω} [MeasurableSpace Ω] (ℙ) [IsProbabilityMeasure ℙ] (G)` for
  `ℙ(∃ m ≥ n : |Y_m - 1/4| > ε) ≤ 2 exp(-ϑ² ε² n / (2 (log₂ n)⁶))`;
- in `(iv)`: the non-asymptotic Orlicz `ψ₂` bound `‖Y_n - 1/4‖_{ψ₂} ≤ √(8/3)(log₂ n)³/√n + |E[Y_n] - 1/4|/√(log 2)`,
  convergence `‖Y_n - 1/4‖_{ψ₂} → 0`, and arbitrary-rate square-exponential moment convergence
  `E[exp(M (Y_n - 1/4)²)] → 1` for every `M ≥ 0`. -/
theorem mainTheorem_v12_complete.{u₁, u₂, u₃}
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
    let S_Yq : ℕ → Set ℝ := fun n ↦
      {s : ℝ | 0 < s ∧
        (∫ G : LabeledGraph n, Real.exp ((Y n G - 1 / 4) ^ 2 / s ^ 2) ∂randomGraphMeasure n) ≤ 2}
    (((∀ n : ℕ,
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
          2 * (p * (Real.logb 2 (n : ℝ)) ^ 6 / (Real.exp 1 * (n : ℝ))) ^ (p / 2)) ∧
      (∀ {Ω : Type u₁} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
        (G : ∀ m : ℕ, Ω → LabeledGraph m),
        (∀ m : ℕ, 2 ≤ m → Measure.map (G m) ℙ = randomGraphMeasure m) →
        (∀ {n : ℕ} {η : ℝ}, 2 ≤ n → 0 < η →
          ℙ.real {ω : Ω | ∃ m ≥ n,
              Real.sqrt (2 * (1 + η) * ((m - 1 : ℕ) : ℝ) * Real.log (m : ℝ)) ≤
                |D m (G m ω) - ∫ H : LabeledGraph m, D m H ∂randomGraphMeasure m|} ≤
            2 * (1 / η + 1 / (n : ℝ)) * (n : ℝ) ^ (-η)) ∧
        ((∀ {eps : ℝ}, 0 < eps →
            ∀ᵐ ω ∂ℙ, ∀ᶠ n : ℕ in atTop,
              |D n (G n ω) - ∫ H : LabeledGraph n, D n H ∂randomGraphMeasure n| ≤
                (1 + eps) * Real.sqrt (2 * (n : ℝ) * Real.log (n : ℝ)) ∧
              |Y n (G n ω) - ∫ H : LabeledGraph n, Y n H ∂randomGraphMeasure n| ≤
                (1 + eps) * (Real.logb 2 (n : ℝ)) ^ 3 *
                  Real.sqrt (2 * Real.log (n : ℝ) / (n : ℝ))) ∧
          (∀ᵐ ω ∂ℙ,
            Filter.limsup (fun n : ℕ ↦
              ENNReal.ofReal (|D n (G n ω) - ∫ H : LabeledGraph n, D n H ∂randomGraphMeasure n| /
                Real.sqrt (2 * (n : ℝ) * Real.log (n : ℝ)))) atTop ≤ 1 ∧
            Filter.limsup (fun n : ℕ ↦
              ENNReal.ofReal (Real.sqrt (n : ℝ) /
                ((Real.logb 2 (n : ℝ)) ^ 3 * Real.sqrt (2 * Real.log (n : ℝ))) *
                |Y n (G n ω) - ∫ H : LabeledGraph n, Y n H ∂randomGraphMeasure n|))
                atTop ≤ 1)))) ∧
    (∀ {eps theta : ℝ}, 0 < eps → theta ∈ Set.Ioo 0 1 →
      ∀ᶠ n : ℕ in atTop,
        (randomGraphMeasure n).real {G : LabeledGraph n | eps < |Y n G - 1 / 4|} ≤
          2 * Real.exp (-theta ^ 2 * eps ^ 2 * (n : ℝ) / (2 * (Real.logb 2 (n : ℝ)) ^ 6))) ∧
    ((∀ {eps theta : ℝ}, 0 < eps → theta ∈ Set.Ioo (0 : ℝ) 1 →
        ∃ N : ℕ,
          ∀ {Ω : Type u₂} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
            (G : ∀ m : ℕ, Ω → LabeledGraph m),
            (∀ m : ℕ, 2 ≤ m → Measure.map (G m) ℙ = randomGraphMeasure m) →
            ∀ n ≥ N,
              ℙ.real {ω : Ω | ∃ m ≥ n, eps < |Y m (G m ω) - 1 / 4|} ≤
                2 * Real.exp (-theta ^ 2 * eps ^ 2 * (n : ℝ) / (2 * (Real.logb 2 (n : ℝ)) ^ 6))) ∧
      (∀ {Ω : Type u₃} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
        (G : ∀ m : ℕ, Ω → LabeledGraph m),
        (∀ m : ℕ, 2 ≤ m → Measure.map (G m) ℙ = randomGraphMeasure m) →
        ∀ᵐ ω ∂ℙ,
          Tendsto (fun n : ℕ ↦ (Real.log n) ^ 3 / (n : ℝ) * D n (G n ω))
            atTop (nhds sharpGapConstant) ∧
          Tendsto (fun n : ℕ ↦ Y n (G n ω)) atTop (nhds (1 / 4 : ℝ)))) ∧
    ((∀ {n : ℕ}, 2 ≤ n →
        (S_Yq n).Nonempty ∧ BddBelow (S_Yq n) ∧
          sInf (S_Yq n) ≤ Real.sqrt (8 / 3) * (Real.logb 2 (n : ℝ)) ^ 3 / Real.sqrt (n : ℝ) +
            |(∫ H : LabeledGraph n, Y n H ∂randomGraphMeasure n) - 1 / 4| /
              Real.sqrt (Real.log 2)) ∧
      Tendsto (fun n : ℕ ↦ sInf (S_Yq n)) atTop (nhds 0) ∧
      (∀ {M : ℝ}, 0 ≤ M →
        Tendsto (fun n : ℕ ↦
            ∫ G : LabeledGraph n, Real.exp (M * (Y n G - 1 / 4) ^ 2) ∂randomGraphMeasure n)
          atTop (nhds 1)) ∧
      (∀ {p : ℝ}, 1 ≤ p →
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
          (fun t ↦ Real.exp (t / 4)) atTop (Set.Icc (-T) T)))) := by
  intro D Y S_Yq
  obtain ⟨⟨hvar, hcgf, hmean_tail, hsq_exp, hpsi2_c, hlp_c⟩, hsubg, -,
    ⟨hlp_q, hmean_lim, hmgf_unif⟩⟩ := mainTheorem_v11_complete.{0} htail
  have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- Part (i) new fluctuation clauses
  have hfluct : ∀ {Ω : Type u₁} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
      (G : ∀ m : ℕ, Ω → LabeledGraph m),
      (∀ m : ℕ, 2 ≤ m → Measure.map (G m) ℙ = randomGraphMeasure m) →
      (∀ {n : ℕ} {η : ℝ}, 2 ≤ n → 0 < η →
        ℙ.real {ω : Ω | ∃ m ≥ n,
            Real.sqrt (2 * (1 + η) * ((m - 1 : ℕ) : ℝ) * Real.log (m : ℝ)) ≤
              |D m (G m ω) - ∫ H : LabeledGraph m, D m H ∂randomGraphMeasure m|} ≤
          2 * (1 / η + 1 / (n : ℝ)) * (n : ℝ) ^ (-η)) ∧
      ((∀ {eps : ℝ}, 0 < eps →
          ∀ᵐ ω ∂ℙ, ∀ᶠ n : ℕ in atTop,
            |D n (G n ω) - ∫ H : LabeledGraph n, D n H ∂randomGraphMeasure n| ≤
              (1 + eps) * Real.sqrt (2 * (n : ℝ) * Real.log (n : ℝ)) ∧
            |Y n (G n ω) - ∫ H : LabeledGraph n, Y n H ∂randomGraphMeasure n| ≤
              (1 + eps) * (Real.logb 2 (n : ℝ)) ^ 3 *
                Real.sqrt (2 * Real.log (n : ℝ) / (n : ℝ))) ∧
        (∀ᵐ ω ∂ℙ,
          Filter.limsup (fun n : ℕ ↦
            ENNReal.ofReal (|D n (G n ω) - ∫ H : LabeledGraph n, D n H ∂randomGraphMeasure n| /
              Real.sqrt (2 * (n : ℝ) * Real.log (n : ℝ)))) atTop ≤ 1 ∧
          Filter.limsup (fun n : ℕ ↦
            ENNReal.ofReal (Real.sqrt (n : ℝ) /
              ((Real.logb 2 (n : ℝ)) ^ 3 * Real.sqrt (2 * Real.log (n : ℝ))) *
              |Y n (G n ω) - ∫ H : LabeledGraph n, Y n H ∂randomGraphMeasure n|))
              atTop ≤ 1)) := by
    intro Ω _ ℙ _ G hMarg
    exact ⟨fun hn hη ↦ coupling_tailUnion_chromaticSubCochromatic_sqrt_log_le ℙ G hMarg hn hη,
      ae_limsup_chromaticSubCochromatic_and_normalizedGap_le_one ℙ G hMarg⟩
  -- Part (iii) coupling-independent `∃ N : ℕ`
  have hcoupling_unif :
      ∀ {eps theta : ℝ}, 0 < eps → theta ∈ Set.Ioo (0 : ℝ) 1 →
        ∃ N : ℕ,
          ∀ {Ω : Type u₂} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
            (G : ∀ m : ℕ, Ω → LabeledGraph m),
            (∀ m : ℕ, 2 ≤ m → Measure.map (G m) ℙ = randomGraphMeasure m) →
            ∀ n ≥ N,
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
          rw [Real.logb, div_pow]; field_simp [hL_pos.ne', hq_pos.ne']
        rwa [hrw] at hm_tail)
      htheta
    refine ⟨max 2 N_u, ?_⟩
    intro Ω _ ℙ _ G hMarg n hn
    have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
    have hn_Nu : N_u ≤ n := le_trans (le_max_right _ _) hn
    have hbound := hN_u ℙ G hMarg n hn_Nu
    have hL_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hrw : -theta ^ 2 * eps ^ 2 * (n : ℝ) / (2 * (Real.logb 2 (n : ℝ)) ^ 6) =
        -theta ^ 2 * (eps ^ 2 * (Real.log 2) ^ 6) * (n : ℝ) / (2 * (Real.log (n : ℝ)) ^ 6) := by
      rw [Real.logb, div_pow]; field_simp [hL_pos.ne', hq_pos.ne']
    rwa [← hrw] at hbound
  -- Part (iv) `‖Y_n - 1/4‖_{ψ₂} → 0` and `E[exp(M (Y_n - 1/4)²)] → 1`
  have hpsi2_q : ∀ {n : ℕ}, 2 ≤ n →
      (S_Yq n).Nonempty ∧ BddBelow (S_Yq n) ∧
        sInf (S_Yq n) ≤ Real.sqrt (8 / 3) * (Real.logb 2 (n : ℝ)) ^ 3 / Real.sqrt (n : ℝ) +
          |(∫ H : LabeledGraph n, Y n H ∂randomGraphMeasure n) - 1 / 4| /
            Real.sqrt (Real.log 2) := by
    intro n hn2
    obtain ⟨hne, hbdd, _, hle⟩ := orliczPsi2_normalizedGap_sub_quarter_le hn2
    exact ⟨hne, hbdd, hle⟩
  have hpsi2_tendsto : Tendsto (fun n : ℕ ↦ sInf (S_Yq n)) atTop (nhds 0) := by
    have hterm1 : Tendsto (fun n : ℕ ↦
        Real.sqrt (8 / 3) * (Real.logb 2 (n : ℝ)) ^ 3 / Real.sqrt (n : ℝ)) atTop (nhds 0) := by
      have ho : (fun x : ℝ ↦ (Real.log x) ^ ((3 : ℕ) : ℝ)) =o[atTop]
          (fun x : ℝ ↦ x ^ (1 / 2 : ℝ)) :=
        isLittleO_log_rpow_rpow_atTop ((3 : ℕ) : ℝ) (by norm_num)
      have ht0 := (ho.comp_tendsto tendsto_natCast_atTop_atTop).tendsto_div_nhds_zero
      have ht1 := ht0.const_mul (Real.sqrt (8 / 3) / (Real.log 2) ^ 3)
      rw [mul_zero] at ht1
      refine ht1.congr fun n ↦ ?_
      change (Real.sqrt (8 / 3) / (Real.log 2) ^ 3) *
          ((Real.log (n : ℝ)) ^ ((3 : ℕ) : ℝ) / (n : ℝ) ^ (1 / 2 : ℝ)) =
        Real.sqrt (8 / 3) * (Real.logb 2 (n : ℝ)) ^ 3 / Real.sqrt (n : ℝ)
      rw [Real.rpow_natCast, Real.logb, div_pow, ← Real.sqrt_eq_rpow]
      ring
    have hmeanY_lim : Tendsto (fun n : ℕ ↦ ∫ H : LabeledGraph n, Y n H ∂randomGraphMeasure n)
        atTop (nhds (1 / 4 : ℝ)) := by
      refine hmean_lim.congr fun n ↦ ?_
      dsimp [Y]
      exact (integral_const_mul _ _).symm
    have hterm2 : Tendsto (fun n : ℕ ↦
        |(∫ H : LabeledGraph n, Y n H ∂randomGraphMeasure n) - 1 / 4| / Real.sqrt (Real.log 2))
        atTop (nhds 0) := by
      have hsub := (hmeanY_lim.sub (tendsto_const_nhds (x := (1 / 4 : ℝ)))).abs.div_const
        (Real.sqrt (Real.log 2))
      rwa [sub_self, abs_zero, zero_div] at hsub
    have hsum := hterm1.add hterm2
    rw [add_zero] at hsum
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (by filter_upwards [eventually_ge_atTop 2] with n hn2
          exact le_csInf (hpsi2_q hn2).1 fun s hs ↦ hs.1.le)
      (by filter_upwards [eventually_ge_atTop 2] with n hn2
          exact (hpsi2_q hn2).2.2)
  have hsqExp_lim : ∀ {M : ℝ}, 0 ≤ M →
      Tendsto (fun n : ℕ ↦
          ∫ G : LabeledGraph n, Real.exp (M * (Y n G - 1 / 4) ^ 2) ∂randomGraphMeasure n)
        atTop (nhds 1) := by
    intro M hM
    have hS_eq : ∀ n : ℕ,
        {s : ℝ | 0 < s ∧
          Integrable (fun G : LabeledGraph n ↦ Real.exp ((Y n G - 1 / 4) ^ 2 / s ^ 2))
            (randomGraphMeasure n) ∧
          (∫ G : LabeledGraph n, Real.exp ((Y n G - 1 / 4) ^ 2 / s ^ 2) ∂randomGraphMeasure n) ≤ 2} =
        S_Yq n := by
      intro n; ext s
      simp only [S_Yq, Set.mem_setOf_eq, Integrable.of_finite, true_and]
    exact (tendsto_sqExpMoment_one_of_orliczPsi2_tendsto_zero
      (Ω := fun n ↦ LabeledGraph n) (ℙ := fun n ↦ randomGraphMeasure n)
      (Z := fun n G ↦ Y n G - 1 / 4)
      (fun n ↦ (Integrable.of_finite :
        Integrable (fun G : LabeledGraph n ↦ Y n G - 1 / 4)
          (randomGraphMeasure n)).aestronglyMeasurable)
      (by filter_upwards [eventually_ge_atTop 2] with n hn2
          rw [hS_eq n]; exact (hpsi2_q hn2).1)
      (by simpa only [hS_eq] using hpsi2_tendsto)
      hM).2
  exact ⟨⟨hvar, hcgf, hmean_tail, hsq_exp, hpsi2_c, hlp_c, hfluct⟩,
    hsubg,
    ⟨hcoupling_unif, by
      intro Ω _ ℙ _ G hMarg
      exact ((mainTheorem_v11_complete.{u₃} htail).2.2.1 ℙ G hMarg).2⟩,
    ⟨hpsi2_q, hpsi2_tendsto, hsqExp_lim, hlp_q, hmean_lim, hmgf_unif⟩⟩

end

end Erdos625HP
