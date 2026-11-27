import Erdos625HP.BoundedLowerTailsAndMomentCore
import Erdos625HP.CappedAndGeneralRateCertificate
import Erdos625HP.SelfContainedSecondMomentCore
import Erdos625HP.PairMomentAndPhaseAsymptotics
import Erdos625HP.SubgaussianConcentrationAndMarkProbability

/-!
# v9 Common-class weights (`Lemma 6.1(i)`), scrambled/middle second-moment sums, sharpness, and CGF/`L^p` bounds

This module formalizes the v9 mathematical upgrades across the Main Theorem, Section 6
(`Lemma 6.1(i)`), Section 7 (`Proposition 7.3`), Section 8 (`Corollary 8.1`), Section 9,
and Appendix C using only the standard Lean foundations (`propext`, `Classical.choice`,
`Quot.sound`):

1. **Section 8 (`Corollary 8.1`) — Oscillation-`2` sharpness witness (`K_4` vs. `K_3 ⊔ K_1`):**
   - `exists_vertexDeletion_chromaticSubCochromatic_eq_two`: exhibits `G = K_4`
     (`(χ, ζ, Δ) = (4, 1, 3)`) and `H = K_3 ⊔ K_1` (`(χ, ζ, Δ) = (3, 2, 1)`) on `Fin 4`
     agreeing away from vertex `3` with `|Δ(G) - Δ(H)| = 2`.

2. **Main Theorem `(i)`, `(iv)` & `Corollary 8.1` — Non-asymptotic CGF squeeze, sub-Gaussian
   central `L^p` moments, and compact-uniform CGF/MGF convergence:**
   - `rpow_le_mul_exp_of_pos`: `u ^ p ≤ (p / (e * lam)) ^ p * exp (lam * u)` (`0 ≤ u`, `0 < p`, `0 < lam`).
   - `centralMoment_chromaticSubCochromatic_le`: `E[|Δ(G_n) - E[Δ(G_n)]|^p] ≤ 2 ((p / e)(n - 1))^(p / 2)`.
   - `centralMoment_normalizedGap_le`: `E[|Y_n - E[Y_n]|^p] ≤ 2 (p (log₂ n)⁶ / (e n))^(p / 2)`.
   - `cgf_normalizedGap_bounds`: `0 ≤ log E[exp(lam Y_n)] - lam E[Y_n] ≤ lam² (log₂ n)⁶ / (2 n)`.
   - `tendstoUniformlyOn_cgf_and_mgf_normalizedGap`: compact-uniform (`TendstoUniformlyOn` and `sSup`
     on `[-T, T]`) convergence `log E[exp(t Y_n)] → t / 4` and `E[exp(t Y_n)] → exp(t / 4)`.

3. **Appendix C — Unmarked common-class Stirling-free entropy bounds (`F_1^ch(ν)`):**
   - `log_unmarkedDiagonalWeight_le` and `log_unmarkedDiagonalWeight_self_ge`.

4. **Section 6 & Appendix C — Complete asymptotic `Lemma 6.1(i)` (`Regime U` and `Regime C`,
   both marked `W(ν)` and unmarked `F_1^ch(ν)`):**
   - `eventually_commonClass_subprofile_le_regimeU` and
     `eventually_commonClass_subprofile_le_regimeC`: uniform `c_W > 0` and eventual threshold `n_W`
     establishing `W(ν) ≤ exp(-c_W m_ν) ≤ exp(-c_W n / (log n)³)` and
     `F_1^ch(ν) ≤ exp(-c_W m_ν) ≤ exp(-c_W n / (log n)³)` across `m_ν ≥ n / (log n)³` and
     `n - m_ν > 2^{-(M+5)} n`.

5. **Section 7 (`Proposition 7.3`) & Section 9 — Direct scrambled-range bounds on `W(ν)` and
   `F_1^ch(ν)`, middle-range subprofile sums, and complete Main Theorem `(i)–(iv)` assembly:**
   - `partialDiagonalWeight_and_unmarked_scrambled_le` and
     `sum_scrambled_partial_and_unmarkedDiagonalWeight_le_exp`: `≤ exp(2 k² / μ_a)`.
   - `eventually_middleRange_commonClass_sum_small_regimeU` and
     `eventually_middleRange_commonClass_sum_small_regimeC`: combines `Lemma 6.1(i)` and
     `Lemma 6.1(ii)` across all `≤ (n + 1)^M` middle-range subprofiles against `exp(C_ov (log n)⁵)`.
   - `mainTheorem_v9_complete`: complete Main Theorem `(i)–(iv)` synthesis.
-/

namespace Erdos625HP

open Erdos625 Erdos625.FiveSizeEntropyGap Erdos625.FiveSizePhaseGainSharp
open Filter Asymptotics MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal

noncomputable section

set_option autoImplicit false

/-!
## 1. Oscillation-`2` sharpness witness (`K_4` vs. `K_3 ⊔ K_1`, Corollary 8.1)
-/

/-- **Corollary 8.1 sharpness witness (`K_4` vs. `K_3 ⊔ K_1`):**
on `4` vertices, `G = K_4` (`⊤`) has `(χ, ζ, Δ) = (4, 1, 3)` and `H = K_3 ⊔ K_1`
(edges on `{0, 1, 2}`, vertex `3` isolated) has `(χ, ζ, Δ) = (3, 2, 1)`; deleting vertex `3`
makes the induced subgraphs identical while `|Δ(G) - Δ(H)| = 2`. -/
theorem exists_vertexDeletion_chromaticSubCochromatic_eq_two :
    ∃ (G H : LabeledGraph 4) (i : Fin 4),
      G = ⊤ ∧
      (∀ u v : Fin 4, H.Adj u v ↔ u ≠ v ∧ u.1 < 3 ∧ v.1 < 3) ∧
      G.induce {v : Fin 4 | v ≠ i} = H.induce {v : Fin 4 | v ≠ i} ∧
      chromaticNumberNat G = 4 ∧
      cochromaticNumber G = 1 ∧
      chromaticNumberNat H = 3 ∧
      cochromaticNumber H = 2 ∧
      |((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) -
        ((chromaticNumberNat H : ℝ) - (cochromaticNumber H : ℝ))| = 2 := by
  let G : LabeledGraph 4 := ⊤
  let H : LabeledGraph 4 :=
    { Adj := fun u v ↦ u ≠ v ∧ u.1 < 3 ∧ v.1 < 3
      symm := ⟨fun _ _ ⟨h1, h2, h3⟩ ↦ ⟨h1.symm, h3, h2⟩⟩
      loopless := ⟨fun _ h ↦ h.1 rfl⟩ }
  let i : Fin 4 := ⟨3, by decide⟩
  have hind : G.induce {v : Fin 4 | v ≠ i} = H.induce {v : Fin 4 | v ≠ i} := by
    ext u v
    change (u : Fin 4) ≠ (v : Fin 4) ↔
      (u : Fin 4) ≠ (v : Fin 4) ∧ (u : Fin 4).1 < 3 ∧ (v : Fin 4).1 < 3
    have hu_ne : (u : Fin 4).1 ≠ 3 := fun h ↦ u.2 (Fin.ext h)
    have hv_ne : (v : Fin 4).1 ≠ 3 := fun h ↦ v.2 (Fin.ext h)
    have hu_lt : (u : Fin 4).1 < 3 := by have := u.1.2; omega
    have hv_lt : (v : Fin 4).1 < 3 := by have := v.1.2; omega
    exact ⟨fun h ↦ ⟨h, hu_lt, hv_lt⟩, fun h ↦ h.1⟩
  have hchiG : chromaticNumberNat G = 4 := by
    apply le_antisymm
    · simpa [Fintype.card_fin] using chromaticNumberNat_le_card G
    · obtain ⟨C⟩ := colorable_chromaticNumberNat G
      have hinj : Function.Injective C := by
        intro u v huv
        by_contra hne
        exact C.valid hne huv
      have hcard := Fintype.card_le_of_injective C hinj
      simpa [Fintype.card_fin] using hcard
  have hzetaG : cochromaticNumber G = 1 := by
    apply le_antisymm
    · refine cochromaticNumber_le_of_coColorable G ⟨{
        color := fun _ ↦ (0 : Fin 1)
        kind := fun _ ↦ .clique
        valid := fun _ _ _ _ _ hne ↦ hne }⟩
    · by_contra hlt
      have h0 : cochromaticNumber G = 0 := by omega
      obtain ⟨C⟩ := h0 ▸ coColorable_cochromaticNumber G
      exact Fin.elim0 (C.color 0)
  have hchiH : chromaticNumberNat H = 3 := by
    apply le_antisymm
    · have hCol3 : H.Colorable 3 := by
        refine ⟨SimpleGraph.Coloring.mk (fun v : Fin 4 ↦ ⟨v.1 % 3, Nat.mod_lt _ (by decide)⟩) ?_⟩
        intro u v ⟨hne, hu3, hv3⟩ heq
        have hval := congrArg Fin.val heq
        dsimp at hval
        rw [Nat.mod_eq_of_lt hu3, Nat.mod_eq_of_lt hv3] at hval
        exact hne (Fin.ext hval)
      unfold chromaticNumberNat
      exact ENat.toNat_le_of_le_coe hCol3.chromaticNumber_le
    · obtain ⟨C⟩ := colorable_chromaticNumberNat H
      let f : Fin 3 → Fin (chromaticNumberNat H) := fun a ↦ C ⟨a.1, by omega⟩
      have hinj : Function.Injective f := by
        intro a b hab
        by_contra hne
        have hadj : H.Adj ⟨a.1, by omega⟩ ⟨b.1, by omega⟩ :=
          ⟨fun h ↦ hne (Fin.ext (congrArg (fun v : Fin 4 ↦ v.1) h)), a.2, b.2⟩
        exact C.valid hadj hab
      have hcard := Fintype.card_le_of_injective f hinj
      simpa [Fintype.card_fin] using hcard
  have hzetaH : cochromaticNumber H = 2 := by
    apply le_antisymm
    · refine cochromaticNumber_le_of_coColorable H ⟨{
        color := fun v ↦ if v.1 < 3 then (0 : Fin 2) else 1
        kind := fun c ↦ if c = 0 then .clique else .independent
        valid := by
          intro c
          fin_cases c
          · dsimp
            intro x hx y hy hxy
            rw [Set.mem_setOf_eq] at hx hy
            have hx3 : x.1 < 3 := by by_contra h; simp [h] at hx
            have hy3 : y.1 < 3 := by by_contra h; simp [h] at hy
            exact ⟨hxy, hx3, hy3⟩
          · dsimp
            intro x hx y hy hxy
            rw [Set.mem_setOf_eq] at hx hy
            have hx3 : ¬ x.1 < 3 := fun h ↦ by simp [h] at hx
            have hy3 : ¬ y.1 < 3 := fun h ↦ by simp [h] at hy
            exfalso
            apply hxy
            apply Fin.ext
            have := x.2
            have := y.2
            omega }⟩
    · by_contra hlt
      have hle1 : cochromaticNumber H ≤ 1 := by omega
      obtain ⟨C⟩ := (coColorable_iff_cochromaticNumber_le H).mpr hle1
      cases hk0 : C.kind 0 with
      | independent =>
        have h0 : C.color 0 = 0 := Subsingleton.elim _ _
        have h1 : C.color 1 = 0 := Subsingleton.elim _ _
        have hadj01 : H.Adj 0 1 := ⟨by decide, by decide, by decide⟩
        exact C.valid_independent hk0 h0 h1 (by decide) hadj01
      | clique =>
        have h0 : C.color 0 = 0 := Subsingleton.elim _ _
        have h3 : C.color ⟨3, by decide⟩ = 0 := Subsingleton.elim _ _
        have hadj03 : H.Adj 0 ⟨3, by decide⟩ := C.valid_clique hk0 h0 h3 (by decide)
        exact absurd hadj03.2.2 (by decide)
  refine ⟨G, H, i, rfl, fun _ _ ↦ Iff.rfl, hind, hchiG, hzetaG, hchiH, hzetaH, ?_⟩
  rw [hchiG, hzetaG, hchiH, hzetaH]
  norm_num

/-!
## 2. Non-asymptotic CGF squeeze, central `L^p` bounds, and compact-uniform CGF/MGF convergence
-/

/-- **Pointwise Laplace-transform optimization inequality (`Corollary 8.1` proof):**
for `0 ≤ u`, `0 < p`, and `0 < lam`, `u ^ p ≤ (p / (e * lam)) ^ p * exp (lam * u)`. -/
theorem rpow_le_mul_exp_of_pos {u p lam : ℝ}
    (hu : 0 ≤ u) (hp : 0 < p) (hlam : 0 < lam) :
    u ^ p ≤ (p / (Real.exp 1 * lam)) ^ p * Real.exp (lam * u) := by
  rcases eq_or_lt_of_le hu with rfl | hu_pos
  · rw [Real.zero_rpow hp.ne']
    positivity
  · set t : ℝ := lam * u / p
    have ht_le : t ≤ Real.exp t / Real.exp 1 := by
      have h1 := Real.add_one_le_exp (t - 1)
      have h2 : t ≤ Real.exp (t - 1) := by linarith
      rwa [Real.exp_sub] at h2
    have hbase_nn : 0 ≤ p / (Real.exp 1 * lam) := by positivity
    have hu_le : u ≤ (p / (Real.exp 1 * lam)) * Real.exp t := by
      have hm := mul_le_mul_of_nonneg_left ht_le (div_nonneg hp.le hlam.le)
      have hlhs : (p / lam) * t = u := by
        dsimp [t]
        field_simp [hp.ne', hlam.ne']
      have hrhs : (p / lam) * (Real.exp t / Real.exp 1) =
          (p / (Real.exp 1 * lam)) * Real.exp t := by ring
      rwa [hlhs, hrhs] at hm
    calc
      u ^ p ≤ ((p / (Real.exp 1 * lam)) * Real.exp t) ^ p :=
        Real.rpow_le_rpow hu_pos.le hu_le hp.le
      _ = (p / (Real.exp 1 * lam)) ^ p * (Real.exp t) ^ p :=
        Real.mul_rpow hbase_nn (Real.exp_pos t).le
      _ = (p / (Real.exp 1 * lam)) ^ p * Real.exp (lam * u) := by
        rw [← Real.exp_mul]
        congr 2
        dsimp [t]
        exact div_mul_cancel₀ (lam * u) hp.ne'

/-- **Main Theorem `(i)` & Corollary 8.1 central `L^p` bound for `Δ(G_n) = χ(G_n) - ζ(G_n)`:**
for all `n ≥ 2` and `1 ≤ p < ∞`,
`E[|Δ(G_n) - E[Δ(G_n)]|^p] ≤ 2 * (p / e * (n - 1)) ^ (p / 2)`. -/
theorem centralMoment_chromaticSubCochromatic_le
    {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 1 ≤ p) :
    (∫ G : LabeledGraph n,
        |((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) -
          ∫ H : LabeledGraph n,
            ((chromaticNumberNat H : ℝ) - (cochromaticNumber H : ℝ))
            ∂randomGraphMeasure n| ^ p
        ∂randomGraphMeasure n) ≤
      2 * (p / Real.exp 1 * ((n - 1 : ℕ) : ℝ)) ^ (p / 2) := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  set σ2 : ℝ := ((n - 1 : ℕ) : ℝ)
  have hσ2_pos : 0 < σ2 := by
    dsimp [σ2]
    exact_mod_cast (show 0 < n - 1 by omega)
  set lam : ℝ := Real.sqrt (p / σ2)
  have hlam_pos : 0 < lam := Real.sqrt_pos.mpr (div_pos hp_pos hσ2_pos)
  set X : LabeledGraph n → ℝ := fun G ↦
    ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) -
      ∫ H : LabeledGraph n,
        ((chromaticNumberNat H : ℝ) - (cochromaticNumber H : ℝ))
        ∂randomGraphMeasure n
  set c : ℝ := (p / (Real.exp 1 * lam)) ^ p
  have hc_pos : 0 < c := Real.rpow_pos_of_pos (by positivity) p
  have hpt : ∀ G : LabeledGraph n,
      |X G| ^ p ≤ c * (Real.exp (lam * X G) + Real.exp ((-lam) * X G)) := by
    intro G
    have h1 := rpow_le_mul_exp_of_pos (abs_nonneg (X G)) hp_pos hlam_pos
    have hexp_abs : Real.exp (lam * |X G|) ≤
        Real.exp (lam * X G) + Real.exp ((-lam) * X G) := by
      rcases le_or_gt 0 (X G) with hnn | hneg
      · rw [abs_of_nonneg hnn]
        linarith [Real.exp_pos ((-lam) * X G)]
      · rw [abs_of_neg hneg]
        have heq : lam * -X G = (-lam) * X G := by ring
        rw [heq]
        linarith [Real.exp_pos (lam * X G)]
    exact h1.trans (mul_le_mul_of_nonneg_left hexp_abs hc_pos.le)
  have hint := integral_mono (μ := randomGraphMeasure n)
    (Integrable.of_finite) (Integrable.of_finite) hpt
  rw [integral_const_mul, integral_add (Integrable.of_finite) (Integrable.of_finite)] at hint
  have hmgf_pos := mgf_chromaticSubCochromatic_center_le n lam
  have hmgf_neg := mgf_chromaticSubCochromatic_center_le n (-lam)
  have hneg_sq : (-lam) ^ 2 = lam ^ 2 := by ring
  rw [hneg_sq] at hmgf_neg
  have hlam_sq : lam ^ 2 = p / σ2 := Real.sq_sqrt (div_nonneg hp_pos.le hσ2_pos.le)
  have hexp_arg : σ2 * lam ^ 2 / 2 = p / 2 := by
    rw [hlam_sq]
    field_simp [hσ2_pos.ne']
  have hsum_mgf :
      (∫ a : LabeledGraph n, Real.exp (lam * X a) ∂randomGraphMeasure n) +
        (∫ a : LabeledGraph n, Real.exp ((-lam) * X a) ∂randomGraphMeasure n) ≤
      2 * Real.exp (p / 2) := by
    have h1 : (∫ a : LabeledGraph n, Real.exp (lam * X a) ∂randomGraphMeasure n) ≤
        Real.exp (p / 2) := by simpa [X, σ2, hexp_arg] using hmgf_pos
    have h2 : (∫ a : LabeledGraph n, Real.exp ((-lam) * X a) ∂randomGraphMeasure n) ≤
        Real.exp (p / 2) := by simpa [X, σ2, hexp_arg] using hmgf_neg
    linarith
  have halg : c * (2 * Real.exp (p / 2)) = 2 * (p / Real.exp 1 * σ2) ^ (p / 2) := by
    have ha_pos : 0 < p / (Real.exp 1 * lam) := by positivity
    have hsq_a : (p / (Real.exp 1 * lam)) ^ (2 : ℝ) * Real.exp 1 = p / Real.exp 1 * σ2 := by
      rw [Real.rpow_two, div_pow, mul_pow, hlam_sq]
      field_simp [hp_pos.ne', hσ2_pos.ne', (Real.exp_pos 1).ne']
    have hc_rewrite : c = ((p / (Real.exp 1 * lam)) ^ (2 : ℝ)) ^ (p / 2) := by
      dsimp [c]
      rw [← Real.rpow_mul ha_pos.le]
      congr 1
      ring
    have hexp_rewrite : Real.exp (p / 2) = (Real.exp 1) ^ (p / 2) := by
      rw [← Real.exp_mul, one_mul]
    rw [hc_rewrite, hexp_rewrite]
    calc
      ((p / (Real.exp 1 * lam)) ^ (2 : ℝ)) ^ (p / 2) * (2 * (Real.exp 1) ^ (p / 2)) =
          2 * (((p / (Real.exp 1 * lam)) ^ (2 : ℝ)) ^ (p / 2) * (Real.exp 1) ^ (p / 2)) := by ring
      _ = 2 * (((p / (Real.exp 1 * lam)) ^ (2 : ℝ)) * Real.exp 1) ^ (p / 2) := by
          rw [← Real.mul_rpow (Real.rpow_nonneg ha_pos.le 2) (Real.exp_pos 1).le]
      _ = 2 * (p / Real.exp 1 * σ2) ^ (p / 2) := by rw [hsq_a]
  exact hint.trans ((mul_le_mul_of_nonneg_left hsum_mgf hc_pos.le).trans (le_of_eq halg))

/-- **Main Theorem `(i)` & Corollary 8.1 central `L^p` bound for `Y_n`:**
for all `n ≥ 2` and `1 ≤ p < ∞`,
`E[|Y_n - E[Y_n]|^p] ≤ 2 * (p * (log₂ n)⁶ / (e * n)) ^ (p / 2)`. -/
theorem centralMoment_normalizedGap_le
    {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 1 ≤ p) :
    let Y : LabeledGraph n → ℝ := fun G ↦
      (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
        ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
    (∫ G : LabeledGraph n, |Y G - ∫ H, Y H ∂randomGraphMeasure n| ^ p ∂randomGraphMeasure n) ≤
      2 * (p * (Real.logb 2 (n : ℝ)) ^ 6 / (Real.exp 1 * (n : ℝ))) ^ (p / 2) := by
  intro Y
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hn_pos : (0 : ℝ) < (n : ℝ) := lt_trans zero_lt_one hn1
  have hlog2_pos : 0 < Real.logb 2 (n : ℝ) := Real.logb_pos one_lt_two hn1
  set s : ℝ := (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ)
  have hs_pos : 0 < s := div_pos (pow_pos hlog2_pos 3) hn_pos
  set D : LabeledGraph n → ℝ := fun G ↦ (chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)
  have hmean : (∫ H : LabeledGraph n, Y H ∂randomGraphMeasure n) =
      s * ∫ H : LabeledGraph n, D H ∂randomGraphMeasure n :=
    integral_const_mul s D
  have hfun :
      (fun G : LabeledGraph n ↦ |Y G - ∫ H, Y H ∂randomGraphMeasure n| ^ p) =
        (fun G : LabeledGraph n ↦ s ^ p * |D G - ∫ H, D H ∂randomGraphMeasure n| ^ p) := by
    funext G
    rw [hmean]
    have h1 : Y G - s * ∫ H, D H ∂randomGraphMeasure n =
        s * (D G - ∫ H, D H ∂randomGraphMeasure n) := by
      dsimp [Y, D]; ring
    rw [h1, abs_mul, abs_of_pos hs_pos, Real.mul_rpow hs_pos.le (abs_nonneg _)]
  rw [hfun, integral_const_mul]
  have hD := centralMoment_chromaticSubCochromatic_le hn hp
  have hn1_le : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
  have hs_p : s ^ p = (s ^ (2 : ℝ)) ^ (p / 2) := by
    rw [← Real.rpow_mul hs_pos.le]
    congr 1
    ring
  calc
    s ^ p * (∫ G : LabeledGraph n, |D G - ∫ H, D H ∂randomGraphMeasure n| ^ p
        ∂randomGraphMeasure n) ≤
      s ^ p * (2 * (p / Real.exp 1 * ((n - 1 : ℕ) : ℝ)) ^ (p / 2)) :=
      mul_le_mul_of_nonneg_left hD (Real.rpow_nonneg hs_pos.le p)
    _ ≤ s ^ p * (2 * (p / Real.exp 1 * (n : ℝ)) ^ (p / 2)) := by
      gcongr
    _ = 2 * ((s ^ (2 : ℝ)) ^ (p / 2) * (p / Real.exp 1 * (n : ℝ)) ^ (p / 2)) := by
      rw [hs_p]; ring
    _ = 2 * (s ^ (2 : ℝ) * (p / Real.exp 1 * (n : ℝ))) ^ (p / 2) := by
      rw [← Real.mul_rpow (Real.rpow_nonneg hs_pos.le 2) (by positivity)]
    _ = 2 * (p * (Real.logb 2 (n : ℝ)) ^ 6 / (Real.exp 1 * (n : ℝ))) ^ (p / 2) := by
      congr 2
      rw [Real.rpow_two]
      dsimp [s]
      field_simp [hn_pos.ne', (Real.exp_pos 1).ne']

/-- **Main Theorem `(i)` & Corollary 8.1 non-asymptotic CGF squeeze for `Y_n`:**
for every `n ≥ 2` and `lam ∈ ℝ`,
`0 ≤ log E[exp(lam * Y_n)] - lam * E[Y_n] ≤ lam² (log₂ n)⁶ / (2 n)`. -/
theorem cgf_normalizedGap_bounds {n : ℕ} (hn : 2 ≤ n) (lam : ℝ) :
    let Y : LabeledGraph n → ℝ := fun G ↦
      (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
        ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
    let μ : ℝ := ∫ H : LabeledGraph n, Y H ∂randomGraphMeasure n
    0 ≤ Real.log (∫ G : LabeledGraph n, Real.exp (lam * Y G) ∂randomGraphMeasure n) - lam * μ ∧
      Real.log (∫ G : LabeledGraph n, Real.exp (lam * Y G) ∂randomGraphMeasure n) - lam * μ ≤
        lam ^ 2 * (Real.logb 2 (n : ℝ)) ^ 6 / (2 * (n : ℝ)) := by
  intro Y μ
  obtain ⟨hlo, hhi⟩ := mgf_normalizedGap_bounds hn lam
  have hexp_pos : 0 < Real.exp (lam * μ) := Real.exp_pos _
  have hmgf_pos : 0 < ∫ G : LabeledGraph n, Real.exp (lam * Y G) ∂randomGraphMeasure n :=
    lt_of_lt_of_le hexp_pos hlo
  have hlog_lo : lam * μ ≤
      Real.log (∫ G : LabeledGraph n, Real.exp (lam * Y G) ∂randomGraphMeasure n) := by
    have := Real.log_le_log hexp_pos hlo
    rwa [Real.log_exp] at this
  have hlog_hi :
      Real.log (∫ G : LabeledGraph n, Real.exp (lam * Y G) ∂randomGraphMeasure n) ≤
        lam * μ + lam ^ 2 * (Real.logb 2 (n : ℝ)) ^ 6 / (2 * (n : ℝ)) := by
    have := Real.log_le_log hmgf_pos hhi
    rwa [Real.log_mul hexp_pos.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp] at this
  exact ⟨by linarith, by linarith⟩

private theorem abs_exp_sub_exp_le_of_le {a b M : ℝ}
    (ha : a ≤ M) (hb : b ≤ M) :
    |Real.exp a - Real.exp b| ≤ Real.exp M * |a - b| := by
  have hstep : ∀ {x y : ℝ}, y ≤ x → x ≤ M → Real.exp x - Real.exp y ≤ Real.exp M * (x - y) := by
    intro x y hyx hxM
    have h1 : 1 - Real.exp (y - x) ≤ x - y := by
      linarith [Real.add_one_le_exp (y - x)]
    have h2 : Real.exp x - Real.exp y = Real.exp x * (1 - Real.exp (y - x)) := by
      rw [mul_sub, mul_one, ← Real.exp_add]
      congr 2
      ring
    rw [h2]
    calc
      Real.exp x * (1 - Real.exp (y - x)) ≤ Real.exp x * (x - y) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos x).le
      _ ≤ Real.exp M * (x - y) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hxM) (by linarith)
  rcases le_total b a with hba | hab
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hba)),
      abs_of_nonneg (sub_nonneg.mpr hba)]
    exact hstep hba ha
  · rw [abs_sub_comm (Real.exp a) (Real.exp b), abs_sub_comm a b,
      abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hab)),
      abs_of_nonneg (sub_nonneg.mpr hab)]
    exact hstep hab hb

/-- **Main Theorem `(iv)` compact-uniform CGF and MGF convergence:**
if `E[Y_n] → 1 / 4`, then for every `T ≥ 0`, both the cumulant-generating function
`log E[exp(t * Y_n)] → t / 4` and the moment-generating function `E[exp(t * Y_n)] → exp(t / 4)`
converge uniformly on `[-T, T]` (stated both via `TendstoUniformlyOn` and via `sup_{|t| ≤ T}`). -/
theorem tendstoUniformlyOn_cgf_and_mgf_normalizedGap
    (hμ : Tendsto (fun n : ℕ ↦
      (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
        ∫ G : LabeledGraph n,
          ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
          ∂randomGraphMeasure n)
      atTop (nhds (1 / 4 : ℝ)))
    {T : ℝ} (hT : 0 ≤ T) :
    let Y : ∀ n : ℕ, LabeledGraph n → ℝ := fun n G ↦
      (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
        ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
    TendstoUniformlyOn
        (fun n t ↦ Real.log (∫ G : LabeledGraph n, Real.exp (t * Y n G) ∂randomGraphMeasure n))
        (fun t ↦ t / 4) atTop (Set.Icc (-T) T) ∧
      TendstoUniformlyOn
        (fun n t ↦ ∫ G : LabeledGraph n, Real.exp (t * Y n G) ∂randomGraphMeasure n)
        (fun t ↦ Real.exp (t / 4)) atTop (Set.Icc (-T) T) ∧
      Tendsto
        (fun n : ℕ ↦ sSup ((fun t : ℝ ↦
          |Real.log (∫ G : LabeledGraph n, Real.exp (t * Y n G) ∂randomGraphMeasure n) -
            t / 4|) '' Set.Icc (-T) T))
        atTop (nhds 0) ∧
      Tendsto
        (fun n : ℕ ↦ sSup ((fun t : ℝ ↦
          |(∫ G : LabeledGraph n, Real.exp (t * Y n G) ∂randomGraphMeasure n) -
            Real.exp (t / 4)|) '' Set.Icc (-T) T))
        atTop (nhds 0) := by
  intro Y
  set μ : ℕ → ℝ := fun n ↦ ∫ G : LabeledGraph n, Y n G ∂randomGraphMeasure n
  have hμ_lim : Tendsto μ atTop (nhds (1 / 4 : ℝ)) := by
    refine hμ.congr fun n ↦ ?_
    exact (integral_const_mul _ _).symm
  set errCgf : ℕ → ℝ := fun n ↦
    T * |μ n - 1 / 4| + T ^ 2 * (Real.logb 2 (n : ℝ)) ^ 6 / (2 * (n : ℝ))
  have herr_lim : Tendsto errCgf atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ ↦ T * |μ n - 1 / 4|) atTop (nhds 0) := by
      have hsub0 : Tendsto (fun n : ℕ ↦ μ n - 1 / 4) atTop (nhds 0) := by
        simpa [sub_self] using hμ_lim.sub_const (1 / 4 : ℝ)
      have hsub : Tendsto (fun n : ℕ ↦ |μ n - 1 / 4|) atTop (nhds 0) := by
        have h := (continuous_abs.tendsto (0 : ℝ)).comp hsub0
        rw [abs_zero] at h
        exact h.congr fun _ ↦ rfl
      simpa using hsub.const_mul T
    have h2 : Tendsto (fun n : ℕ ↦ T ^ 2 * (Real.logb 2 (n : ℝ)) ^ 6 / (2 * (n : ℝ)))
        atTop (nhds 0) := by
      have hq6_pos : 0 < (Real.log 2) ^ 6 := pow_pos (Real.log_pos one_lt_two) 6
      have hdiv0 : Tendsto (fun x : ℝ ↦ (Real.log x) ^ 6 / x) atTop (nhds 0) := by
        simpa [div_eq_mul_inv] using (Real.isLittleO_pow_log_id_atTop (n := 6)).tendsto_div_nhds_zero
      have hnat : Tendsto (fun n : ℕ ↦ (Real.log (n : ℝ)) ^ 6 / (n : ℝ)) atTop (nhds 0) :=
        hdiv0.comp tendsto_natCast_atTop_atTop
      have hmul := hnat.const_mul (T ^ 2 / (2 * (Real.log 2) ^ 6))
      rw [mul_zero] at hmul
      refine hmul.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn1
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      rw [Real.logb, div_pow]
      field_simp [hn_pos.ne', hq6_pos.ne']
    simpa [errCgf] using h1.add h2
  have hcgf_pt : ∀ {n : ℕ}, 2 ≤ n → ∀ {t : ℝ}, t ∈ Set.Icc (-T) T →
      |Real.log (∫ G : LabeledGraph n, Real.exp (t * Y n G) ∂randomGraphMeasure n) - t / 4| ≤
        errCgf n := by
    intro n hn2 t ht
    obtain ⟨hc_lo, hc_hi⟩ := cgf_normalizedGap_bounds hn2 t
    have habs_t : |t| ≤ T := abs_le.mpr ht
    have ht_sq : t ^ 2 ≤ T ^ 2 := by nlinarith [ht.1, ht.2, hT]
    have hc_abs :
        |Real.log (∫ G : LabeledGraph n, Real.exp (t * Y n G) ∂randomGraphMeasure n) -
            t * μ n| ≤
          T ^ 2 * (Real.logb 2 (n : ℝ)) ^ 6 / (2 * (n : ℝ)) := by
      rw [abs_le]
      have hnn : 0 ≤ t ^ 2 * (Real.logb 2 (n : ℝ)) ^ 6 / (2 * (n : ℝ)) := by positivity
      have hmono : t ^ 2 * (Real.logb 2 (n : ℝ)) ^ 6 / (2 * (n : ℝ)) ≤
          T ^ 2 * (Real.logb 2 (n : ℝ)) ^ 6 / (2 * (n : ℝ)) := by gcongr
      exact ⟨by linarith, by linarith⟩
    have hlin_abs : |t * μ n - t / 4| ≤ T * |μ n - 1 / 4| := by
      have heq : t * μ n - t / 4 = t * (μ n - 1 / 4) := by ring
      rw [heq, abs_mul]
      exact mul_le_mul_of_nonneg_right habs_t (abs_nonneg _)
    have hsplit :
        Real.log (∫ G : LabeledGraph n, Real.exp (t * Y n G) ∂randomGraphMeasure n) - t / 4 =
          (Real.log (∫ G : LabeledGraph n, Real.exp (t * Y n G) ∂randomGraphMeasure n) -
              t * μ n) +
            (t * μ n - t / 4) := by ring
    rw [hsplit]
    exact (abs_add_le _ _).trans (by linarith [hlin_abs, hc_abs])
  have hmgf_pt : ∀ {n : ℕ}, 2 ≤ n → errCgf n ≤ 1 → ∀ {t : ℝ}, t ∈ Set.Icc (-T) T →
      |(∫ G : LabeledGraph n, Real.exp (t * Y n G) ∂randomGraphMeasure n) - Real.exp (t / 4)| ≤
        Real.exp (T / 4 + 1) * errCgf n := by
    intro n hn2 herr1 t ht
    have hpos : 0 < ∫ G : LabeledGraph n, Real.exp (t * Y n G) ∂randomGraphMeasure n :=
      lt_of_lt_of_le (Real.exp_pos _) (mgf_normalizedGap_bounds hn2 t).1
    have hcgf := hcgf_pt hn2 ht
    have hhi_a : Real.log (∫ G : LabeledGraph n, Real.exp (t * Y n G) ∂randomGraphMeasure n) ≤
        T / 4 + 1 := by
      have := (abs_le.mp hcgf).2
      linarith [ht.2]
    have hhi_b : t / 4 ≤ T / 4 + 1 := by linarith [ht.2]
    have hexp_eq :
        (∫ G : LabeledGraph n, Real.exp (t * Y n G) ∂randomGraphMeasure n) =
          Real.exp (Real.log (∫ G : LabeledGraph n, Real.exp (t * Y n G) ∂randomGraphMeasure n)) :=
      (Real.exp_log hpos).symm
    rw [hexp_eq]
    exact (abs_exp_sub_exp_le_of_le hhi_a hhi_b).trans
      (mul_le_mul_of_nonneg_left hcgf (Real.exp_pos _).le)
  have h0_mem : (0 : ℝ) ∈ Set.Icc (-T) T := ⟨by linarith, hT⟩
  have hunif_cgf : TendstoUniformlyOn
      (fun n t ↦ Real.log (∫ G : LabeledGraph n, Real.exp (t * Y n G) ∂randomGraphMeasure n))
      (fun t ↦ t / 4) atTop (Set.Icc (-T) T) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro eps heps
    filter_upwards [eventually_ge_atTop 2, herr_lim.eventually (gt_mem_nhds heps)] with n hn2 herr t ht
    rw [Real.dist_eq, abs_sub_comm]
    exact lt_of_le_of_lt (hcgf_pt hn2 ht) herr
  have herr_mgf_lim : Tendsto (fun n : ℕ ↦ Real.exp (T / 4 + 1) * errCgf n) atTop (nhds 0) := by
    simpa using herr_lim.const_mul (Real.exp (T / 4 + 1))
  have hunif_mgf : TendstoUniformlyOn
      (fun n t ↦ ∫ G : LabeledGraph n, Real.exp (t * Y n G) ∂randomGraphMeasure n)
      (fun t ↦ Real.exp (t / 4)) atTop (Set.Icc (-T) T) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro eps heps
    filter_upwards [eventually_ge_atTop 2, herr_lim.eventually (ge_mem_nhds zero_lt_one),
      herr_mgf_lim.eventually (gt_mem_nhds heps)] with n hn2 herr1 herr t ht
    rw [Real.dist_eq, abs_sub_comm]
    exact lt_of_le_of_lt (hmgf_pt hn2 herr1 ht) herr
  have hsup_cgf : Tendsto
      (fun n : ℕ ↦ sSup ((fun t : ℝ ↦
        |Real.log (∫ G : LabeledGraph n, Real.exp (t * Y n G) ∂randomGraphMeasure n) -
          t / 4|) '' Set.Icc (-T) T))
      atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds herr_lim ?_ ?_
    · filter_upwards [eventually_ge_atTop 2] with n hn2
      let g : ℝ → ℝ := fun t ↦
        |Real.log (∫ G : LabeledGraph n, Real.exp (t * Y n G) ∂randomGraphMeasure n) - t / 4|
      have hbdd : BddAbove (g '' Set.Icc (-T) T) :=
        ⟨errCgf n, fun _ ⟨t, ht, hgt⟩ ↦ hgt ▸ hcgf_pt hn2 ht⟩
      exact le_trans (abs_nonneg _) (le_csSup hbdd ⟨0, h0_mem, rfl⟩)
    · filter_upwards [eventually_ge_atTop 2] with n hn2
      exact csSup_le ⟨_, ⟨0, h0_mem, rfl⟩⟩ fun _ ⟨t, ht, hgt⟩ ↦ hgt ▸ hcgf_pt hn2 ht
  have hsup_mgf : Tendsto
      (fun n : ℕ ↦ sSup ((fun t : ℝ ↦
        |(∫ G : LabeledGraph n, Real.exp (t * Y n G) ∂randomGraphMeasure n) -
          Real.exp (t / 4)|) '' Set.Icc (-T) T))
      atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds herr_mgf_lim ?_ ?_
    · filter_upwards [eventually_ge_atTop 2, herr_lim.eventually (ge_mem_nhds zero_lt_one)] with
        n hn2 herr1
      let g : ℝ → ℝ := fun t ↦
        |(∫ G : LabeledGraph n, Real.exp (t * Y n G) ∂randomGraphMeasure n) - Real.exp (t / 4)|
      have hbdd : BddAbove (g '' Set.Icc (-T) T) :=
        ⟨Real.exp (T / 4 + 1) * errCgf n, fun _ ⟨t, ht, hgt⟩ ↦ hgt ▸ hmgf_pt hn2 herr1 ht⟩
      exact le_trans (abs_nonneg _) (le_csSup hbdd ⟨0, h0_mem, rfl⟩)
    · filter_upwards [eventually_ge_atTop 2, herr_lim.eventually (ge_mem_nhds zero_lt_one)] with
        n hn2 herr1
      exact csSup_le ⟨_, ⟨0, h0_mem, rfl⟩⟩ fun _ ⟨t, ht, hgt⟩ ↦ hgt ▸ hmgf_pt hn2 herr1 ht
  exact ⟨hunif_cgf, hunif_mgf, hsup_cgf, hsup_mgf⟩

/-!
## 3. Unmarked Appendix C common-class bounds (`log_unmarkedDiagonalWeight_le` and `_self_ge`)
-/

/-- **Appendix C Stirling-free upper bound on `log F_1^ch(ν)` (`Lemma 6.1(i)` unmarked case):**
the unmarked counterpart of `log_partialDiagonalWeight_le`, where multiplying by `2^(∑ ν_i)`
cancels `-log 2` inside `E_i`, leaving `E_i^ch = log K + log(u_i!) + u_i - u_i log n + (log 2) binom(u_i, 2)`. -/
theorem log_unmarkedDiagonalWeight_le {I : Type*} [Fintype I]
    {n : ℕ} {u k nu : I → ℕ}
    (hn : 1 ≤ n) (hu : ∀ i, 1 ≤ u i)
    (hMass : selectedVertexMass u k = n)
    (hnu : IsPartialSubprofile k nu) :
    let K : ℝ := (selectedBlockCount k : ℝ)
    let p : I → ℝ := fun i ↦ (k i : ℝ) / K
    let y : I → ℝ := fun i ↦ (nu i : ℝ) / K
    let z : I → ℝ := fun i ↦ ((k i - nu i : ℕ) : ℝ) / K
    let rho : ℝ := ((n - selectedVertexMass u nu : ℕ) : ℝ) / (n : ℝ)
    let Ech : I → ℝ := fun i ↦
      Real.log K + Real.log ((u i).factorial : ℝ) + (u i : ℝ) -
        (u i : ℝ) * Real.log (n : ℝ) + Real.log 2 * ((u i).choose 2 : ℝ)
    Real.log (unmarkedDiagonalWeight n u k nu) ≤
      (n : ℝ) * rho * Real.log rho +
        K * ∑ i : I,
          (2 * p i * Real.log (p i) - 2 * z i * Real.log (z i) -
            y i * Real.log (y i) - y i + y i * Ech i) +
        (2 * (Fintype.card I : ℝ) + 1) * Real.log (Real.exp 1 * ((n : ℝ) + 1)) := by
  intro K p y z rho Ech
  have hK_nat_pos : 0 < selectedBlockCount k := by
    by_contra hK0
    have hall0 : ∀ i, k i = 0 := by
      have hsum0 : ∑ i : I, k i = 0 := Nat.eq_zero_of_not_pos hK0
      exact fun i ↦ Finset.sum_eq_zero_iff.mp hsum0 i (Finset.mem_univ i)
    have hM0 : selectedVertexMass u k = 0 := by unfold selectedVertexMass; simp [hall0]
    omega
  have hK_pos : 0 < K := by dsimp [K]; exact_mod_cast hK_nat_pos
  have hW_pos : 0 < partialDiagonalWeight n u k nu := by
    unfold partialDiagonalWeight
    exact div_pos (by exact_mod_cast partialMarkingCount_pos k nu hnu)
      (partialSignedFirstMoment_pos n u nu)
  have h2_pos : 0 < (2 : ℝ) ^ (∑ i : I, nu i) := by positivity
  have hlog_eq : Real.log (unmarkedDiagonalWeight n u k nu) =
      ((∑ i : I, nu i : ℕ) : ℝ) * Real.log 2 + Real.log (partialDiagonalWeight n u k nu) := by
    unfold unmarkedDiagonalWeight
    rw [Real.log_mul h2_pos.ne' hW_pos.ne', Real.log_pow]
  have hmarked := log_partialDiagonalWeight_le hn hu hMass hnu
  have hcancel :
      ((∑ i : I, nu i : ℕ) : ℝ) * Real.log 2 +
        K * ∑ i : I,
          (2 * p i * Real.log (p i) - 2 * z i * Real.log (z i) -
            y i * Real.log (y i) - y i + y i * (Ech i - Real.log 2)) =
        K * ∑ i : I,
          (2 * p i * Real.log (p i) - 2 * z i * Real.log (z i) -
            y i * Real.log (y i) - y i + y i * Ech i) := by
    have hsum_nu : ((∑ i : I, nu i : ℕ) : ℝ) * Real.log 2 =
        K * ∑ i : I, y i * Real.log 2 := by
      rw [Nat.cast_sum, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      dsimp [y]
      field_simp [hK_pos.ne']
    rw [hsum_nu, ← mul_add, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hlog_eq]
  linarith [hmarked, hcancel]

/-- **Appendix C Stirling-free lower bound on `log F_1^ch(k)` (`Lemma 6.1(i)` unmarked case):**
at `ν = k` (`F_1^ch(k) = 1 / E[X̄_k]`), `log (unmarkedDiagonalWeight n u k k)` is at least
`K * ∑ i, (p i * log (p i) - p i + p i * Ech i) - log (e * (n + 1))`. -/
theorem log_unmarkedDiagonalWeight_self_ge {I : Type*} [Fintype I]
    {n : ℕ} {u k : I → ℕ}
    (hn : 1 ≤ n)
    (hMass : selectedVertexMass u k = n) :
    let K : ℝ := (selectedBlockCount k : ℝ)
    let p : I → ℝ := fun i ↦ (k i : ℝ) / K
    let Ech : I → ℝ := fun i ↦
      Real.log K + Real.log ((u i).factorial : ℝ) + (u i : ℝ) -
        (u i : ℝ) * Real.log (n : ℝ) + Real.log 2 * ((u i).choose 2 : ℝ)
    K * ∑ i : I, (p i * Real.log (p i) - p i + p i * Ech i) -
        Real.log (Real.exp 1 * ((n : ℝ) + 1)) ≤
      Real.log (unmarkedDiagonalWeight n u k k) := by
  intro K p Ech
  have hK_nat_pos : 0 < selectedBlockCount k := by
    by_contra hK0
    have hall0 : ∀ i, k i = 0 := by
      have hsum0 : ∑ i : I, k i = 0 := Nat.eq_zero_of_not_pos hK0
      exact fun i ↦ Finset.sum_eq_zero_iff.mp hsum0 i (Finset.mem_univ i)
    have hM0 : selectedVertexMass u k = 0 := by unfold selectedVertexMass; simp [hall0]
    omega
  have hK_pos : 0 < K := by dsimp [K]; exact_mod_cast hK_nat_pos
  have hW_pos : 0 < partialDiagonalWeight n u k k := by
    unfold partialDiagonalWeight
    exact div_pos (by exact_mod_cast partialMarkingCount_pos k k (fun _ ↦ le_rfl))
      (partialSignedFirstMoment_pos n u k)
  have h2_pos : 0 < (2 : ℝ) ^ (∑ i : I, k i) := by positivity
  have hlog_eq : Real.log (unmarkedDiagonalWeight n u k k) =
      ((∑ i : I, k i : ℕ) : ℝ) * Real.log 2 + Real.log (partialDiagonalWeight n u k k) := by
    unfold unmarkedDiagonalWeight
    rw [Real.log_mul h2_pos.ne' hW_pos.ne', Real.log_pow]
  have hmarked := log_partialDiagonalWeight_self_ge hn hMass
  have hcancel :
      ((∑ i : I, k i : ℕ) : ℝ) * Real.log 2 +
        K * ∑ i : I, (p i * Real.log (p i) - p i + p i * (Ech i - Real.log 2)) =
        K * ∑ i : I, (p i * Real.log (p i) - p i + p i * Ech i) := by
    have hsum_k : ((∑ i : I, k i : ℕ) : ℝ) * Real.log 2 =
        K * ∑ i : I, p i * Real.log 2 := by
      rw [Nat.cast_sum, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      dsimp [p]
      field_simp [hK_pos.ne']
    rw [hsum_k, ← mul_add, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hlog_eq]
  linarith [hmarked, hcancel]

/-!
## 4. Complete asymptotic `Lemma 6.1(i)` (`Regime U` and `Regime C`, marked and unmarked)
-/

private theorem sum_F0M_eq_fin (M : ℕ) (f : ℤ → ℝ) :
    ∑ i ∈ F0M M, f i = ∑ j : Fin M, f ((j.1 : ℤ) + 1) := by
  symm
  refine Finset.sum_bij (fun (j : Fin M) _ ↦ (j.1 : ℤ) + 1) ?_ ?_ ?_ (fun _ _ ↦ rfl)
  · intro j _
    rw [F0M, Finset.mem_Icc]
    exact ⟨by omega, by omega⟩
  · intro a _ b _ hab
    exact Fin.ext (by omega)
  · intro i hi
    rw [F0M, Finset.mem_Icc] at hi
    refine ⟨⟨(i - 1).toNat, by omega⟩, Finset.mem_univ _, ?_⟩
    dsimp
    omega

private theorem partialDiagonalWeight_self_eq_inv {I : Type*} [Fintype I]
    {n : ℕ} {u k : I → ℕ} (hMass : selectedVertexMass u k = n) :
    partialDiagonalWeight n u k k = (completeSignedFirstMoment u k)⁻¹ := by
  unfold partialDiagonalWeight completeSignedFirstMoment residualVertexMass
  have hmark1 : (partialMarkingCount k k : ℝ) = 1 := by unfold partialMarkingCount; simp
  rw [hmark1, hMass, one_div]

private theorem unmarkedDiagonalWeight_self_eq_inv {I : Type*} [Fintype I]
    {n : ℕ} {u k : I → ℕ} (hMass : selectedVertexMass u k = n) :
    unmarkedDiagonalWeight n u k k = (completeUnmarkedFirstMoment u k)⁻¹ := by
  unfold unmarkedDiagonalWeight completeUnmarkedFirstMoment
  rw [partialDiagonalWeight_self_eq_inv hMass, mul_inv_rev, inv_inv, mul_comm]

private theorem abs_mul_log_sub_le_of_mem_Icc {r₀ u v : ℝ}
    (hr₀ : 0 < r₀) (hu : u ∈ Set.Icc r₀ 1) (hv : v ∈ Set.Icc r₀ 1) :
    |u * Real.log u - v * Real.log v| ≤ max 1 (-Real.log r₀) * |u - v| := by
  have hstep : ∀ {a b : ℝ}, r₀ ≤ a → a ≤ b → b ≤ 1 →
      |b * Real.log b - a * Real.log a| ≤ max 1 (-Real.log r₀) * (b - a) := by
    intro a b ha hab hb1
    have ha_pos : 0 < a := lt_of_lt_of_le hr₀ ha
    have hb_pos : 0 < b := lt_of_lt_of_le ha_pos hab
    have hba_nn : 0 ≤ b - a := sub_nonneg.mpr hab
    have hdecomp : b * Real.log b - a * Real.log a =
        (b - a) * Real.log b + a * Real.log (b / a) := by
      rw [Real.log_div hb_pos.ne' ha_pos.ne']
      ring
    have hlog_div_nn : 0 ≤ a * Real.log (b / a) :=
      mul_nonneg ha_pos.le (Real.log_nonneg ((one_le_div ha_pos).mpr hab))
    have hlog_div_hi : a * Real.log (b / a) ≤ b - a := by
      have h1 : Real.log (b / a) ≤ b / a - 1 := by
        have := Real.add_one_le_exp (Real.log (b / a))
        rw [Real.exp_log (div_pos hb_pos ha_pos)] at this
        linarith
      calc
        a * Real.log (b / a) ≤ a * (b / a - 1) := mul_le_mul_of_nonneg_left h1 ha_pos.le
        _ = b - a := by field_simp [ha_pos.ne']
    have hlog_b_np : (b - a) * Real.log b ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hba_nn (Real.log_nonpos hb_pos.le hb1)
    have hlog_b_lo : -(max 1 (-Real.log r₀) * (b - a)) ≤ (b - a) * Real.log b := by
      have h1 : Real.log r₀ ≤ Real.log b := Real.log_le_log hr₀ (le_trans ha hab)
      have h2 : -Real.log b ≤ max 1 (-Real.log r₀) := le_trans (by linarith) (le_max_right _ _)
      have hm := mul_le_mul_of_nonneg_right h2 hba_nn
      linarith
    have h1_le : b - a ≤ max 1 (-Real.log r₀) * (b - a) := by
      calc b - a = 1 * (b - a) := (one_mul _).symm
        _ ≤ max 1 (-Real.log r₀) * (b - a) := mul_le_mul_of_nonneg_right (le_max_left _ _) hba_nn
    rw [hdecomp, abs_le]
    exact ⟨by linarith, by linarith⟩
  rcases le_total u v with huv | hvu
  · rw [abs_sub_comm (u * Real.log u) (v * Real.log v), abs_sub_comm u v,
      abs_of_nonneg (sub_nonneg.mpr huv)]
    exact hstep hu.1 huv hv.2
  · rw [abs_of_nonneg (sub_nonneg.mpr hvu)]
    exact hstep hv.1 hvu hu.2

private theorem neg_sum_mul_log_le_log_card {M : ℕ} (hM : 1 ≤ M)
    {p : Fin M → ℝ} (hp_nn : ∀ j, 0 ≤ p j) (hp_sum : ∑ j : Fin M, p j = 1) :
    -(∑ j : Fin M, p j * Real.log (p j)) ≤ Real.log (M : ℝ) := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hpt : ∀ j : Fin M,
      -(p j * Real.log (p j)) - p j * Real.log (M : ℝ) ≤ 1 / (M : ℝ) - p j := by
    intro j
    rcases eq_or_lt_of_le (hp_nn j) with hp0 | hp_pos
    · rw [← hp0]; simp
    · have hMp_pos : 0 < (M : ℝ) * p j := mul_pos hM_pos hp_pos
      have h1 : Real.log (1 / ((M : ℝ) * p j)) ≤ 1 / ((M : ℝ) * p j) - 1 := by
        have := Real.add_one_le_exp (Real.log (1 / ((M : ℝ) * p j)))
        rw [Real.exp_log (div_pos one_pos hMp_pos)] at this
        linarith
      have h2 := mul_le_mul_of_nonneg_left h1 hp_pos.le
      have hlhs : p j * Real.log (1 / ((M : ℝ) * p j)) =
          -(p j * Real.log (p j)) - p j * Real.log (M : ℝ) := by
        rw [Real.log_div one_ne_zero hMp_pos.ne', Real.log_one, zero_sub,
          Real.log_mul hM_pos.ne' hp_pos.ne']
        ring
      have hrhs : p j * (1 / ((M : ℝ) * p j) - 1) = 1 / (M : ℝ) - p j := by
        field_simp [hM_pos.ne', hp_pos.ne']
      rwa [hlhs, hrhs] at h2
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun (j : Fin M) _ ↦ hpt j
  have hlhs_sum :
      ∑ j : Fin M, (-(p j * Real.log (p j)) - p j * Real.log (M : ℝ)) =
        -(∑ j : Fin M, p j * Real.log (p j)) - Real.log (M : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.sum_mul, hp_sum, one_mul]
  have hrhs_sum : ∑ j : Fin M, (1 / (M : ℝ) - p j) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul,
      mul_one_div_cancel hM_pos.ne', hp_sum, sub_self]
  linarith

private def baseAppendixCE (n v : ℕ) : ℝ :=
  Real.log (v.factorial : ℝ) + (v : ℝ) -
    (v : ℝ) * Real.log (n : ℝ) + Real.log 2 * (v.choose 2 : ℝ)

private theorem baseAppendixCE_pred_sub {n v : ℕ} (hv : 1 ≤ v) :
    baseAppendixCE n (v - 1) - baseAppendixCE n v =
      Real.log (n : ℝ) - Real.log (v : ℝ) - Real.log 2 * ((v : ℝ) - 1) - 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : v ≠ 0)
  have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hfac_pos : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hlog_fac : Real.log (m.factorial : ℝ) - Real.log ((m + 1).factorial : ℝ) =
      -Real.log ((m + 1 : ℕ) : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul hm1_pos.ne' hfac_pos.ne']
    ring
  have hchoose : ((m + 1).choose 2 : ℝ) = (m.choose 2 : ℝ) + (m : ℝ) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.choose_succ_succ', Nat.choose_one_right,
      Nat.cast_add, add_comm]
  unfold baseAppendixCE
  rw [Nat.succ_eq_add_one, Nat.add_sub_cancel, hchoose]
  push_cast at hlog_fac ⊢
  linarith [hlog_fac, show ((m : ℝ) - ((m : ℝ) + 1)) -
      ((m : ℝ) * Real.log (n : ℝ) - ((m : ℝ) + 1) * Real.log (n : ℝ)) +
      (Real.log 2 * (m.choose 2 : ℝ) - Real.log 2 * ((m.choose 2 : ℝ) + (m : ℝ))) =
    Real.log (n : ℝ) - Real.log 2 * (((m : ℝ) + 1) - 1) - 1 by ring]

private theorem eventually_baseAppendixCE_diff_bound (M : ℕ) :
    ∃ C_E : ℝ, 0 < C_E ∧ ∀ᶠ n : ℕ in atTop,
      ∀ {m : ℕ}, m ≤ 1 →
        let u : Fin M → ℕ := fun j ↦ phaseNat n - (m + 1 + j.1)
        ∀ j₁ j₂ : Fin M,
          |(baseAppendixCE n (u j₁) - baseAppendixCE n (u j₂)) -
              (-(Real.log 2 / 2) * (phaseNat n : ℝ) * ((j₁.1 : ℝ) - (j₂.1 : ℝ)))| ≤ C_E := by
  let C_step : ℝ :=
    Real.log 4 + Real.log 2 * ((M : ℝ) + 3) + |phaseC| + Real.log 2 + 1
  have hC_step_pos : 0 < C_step := by
    dsimp [C_step]
    have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have habs : 0 ≤ |phaseC| := abs_nonneg phaseC
    positivity
  refine ⟨((M : ℝ) + 1) * C_step, by positivity, ?_⟩
  have hL_big : ∀ᶠ n : ℕ in atTop, 2 * ((M : ℝ) + 4) ≤ logOrder n :=
    tendsto_logOrder_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_phaseDomain,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder, hL_big] with
    n hnDom hPhBnd hL m hm u j₁ j₂
  set a : ℕ := phaseNat n
  have hL_pos : 0 < logOrder n := lt_of_lt_of_le (by positivity) hL
  have ha_ge : 2 * (M + 4) ≤ a := by
    have : (2 * ((M : ℝ) + 4) : ℝ) ≤ (a : ℝ) := le_trans hL hPhBnd.1
    exact_mod_cast this
  have haq : (a : ℝ) * Real.log 2 =
      2 * logOrder n - 2 * logLogOrder n + 2 * phaseC + (1 - phaseDelta n) * Real.log 2 := by
    have h := phaseNat_cast_eq_two_phaseS_div_q_add_phaseB hnDom
    simp only [phaseS, phaseB, q] at h
    have hq0 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    field_simp [hq0] at h ⊢
    linarith
  have hd0 : 0 ≤ phaseDelta n := phaseDelta_nonneg n
  have hd1 : phaseDelta n < 1 := phaseDelta_lt_one n
  have hone_step : ∀ r : ℕ, r ≤ m + M + 1 →
      |(baseAppendixCE n (a - (r + 1)) - baseAppendixCE n (a - r)) -
          (-(Real.log 2 / 2) * (a : ℝ))| ≤ C_step := by
    intro r hr
    have hr_lt : r + 1 ≤ a := by omega
    have hv1 : 1 ≤ a - r := by omega
    have hsub_eq : a - (r + 1) = (a - r) - 1 := by omega
    rw [hsub_eq, baseAppendixCE_pred_sub hv1]
    have hv_cast : ((a - r : ℕ) : ℝ) = (a : ℝ) - (r : ℝ) :=
      Nat.cast_sub (by omega : r ≤ a)
    have hv_lo : logOrder n / 2 ≤ ((a - r : ℕ) : ℝ) := by
      rw [hv_cast]
      have hr_le : (r : ℝ) ≤ (M : ℝ) + 2 := by exact_mod_cast (show r ≤ M + 2 by omega)
      linarith [hPhBnd.1, hL]
    have hv_hi : ((a - r : ℕ) : ℝ) ≤ 4 * logOrder n := by
      rw [hv_cast]
      have hr_nn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
      linarith [hPhBnd.2]
    have hlog_v_lo : logLogOrder n - Real.log 2 ≤ Real.log ((a - r : ℕ) : ℝ) := by
      have := Real.log_le_log (half_pos hL_pos) hv_lo
      rwa [Real.log_div hL_pos.ne' two_ne_zero, ← logLogOrder] at this
    have hlog_v_hi : Real.log ((a - r : ℕ) : ℝ) ≤ logLogOrder n + Real.log 4 := by
      have hv_pos : 0 < ((a - r : ℕ) : ℝ) := lt_of_lt_of_le (half_pos hL_pos) hv_lo
      have := Real.log_le_log hv_pos hv_hi
      rwa [Real.log_mul (by norm_num) hL_pos.ne', ← logLogOrder, add_comm] at this
    have hlog4_ge : Real.log 2 ≤ Real.log 4 := Real.log_le_log two_pos (by norm_num)
    have hlog_diff : |logLogOrder n - Real.log ((a - r : ℕ) : ℝ)| ≤ Real.log 4 := by
      rw [abs_le]; constructor <;> linarith
    have halg :
        (Real.log (n : ℝ) - Real.log ((a - r : ℕ) : ℝ) -
            Real.log 2 * (((a - r : ℕ) : ℝ) - 1) - 1) -
          (-(Real.log 2 / 2) * (a : ℝ)) =
        (logLogOrder n - Real.log ((a - r : ℕ) : ℝ)) +
          Real.log 2 * ((r : ℝ) + 1) - phaseC -
          (1 - phaseDelta n) * (Real.log 2 / 2) - 1 := by
      rw [hv_cast]
      change (logOrder n - Real.log ((a : ℝ) - (r : ℝ)) -
          Real.log 2 * ((a : ℝ) - (r : ℝ) - 1) - 1) -
        (-(Real.log 2 / 2) * (a : ℝ)) = _
      linarith [haq]
    rw [halg]
    obtain ⟨hl1, hl2⟩ := abs_le.mp hlog_diff
    obtain ⟨hc1, hc2⟩ := abs_le.mp (le_refl |phaseC|)
    have hr_bound : (r : ℝ) + 1 ≤ (M : ℝ) + 3 := by
      exact_mod_cast (show r + 1 ≤ M + 3 by omega)
    have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hq_mul : Real.log 2 * ((r : ℝ) + 1) ≤ Real.log 2 * ((M : ℝ) + 3) :=
      mul_le_mul_of_nonneg_left hr_bound hq_pos.le
    have hq_nn : 0 ≤ Real.log 2 * ((r : ℝ) + 1) := by positivity
    have hd_term_nn : 0 ≤ (1 - phaseDelta n) * (Real.log 2 / 2) := by positivity
    have hd_term_hi : (1 - phaseDelta n) * (Real.log 2 / 2) ≤ Real.log 2 := by nlinarith
    rw [abs_le]
    dsimp [C_step]
    constructor <;> linarith
  have htele : ∀ r d : ℕ, r + d ≤ m + M + 1 →
      |(baseAppendixCE n (a - (r + d)) - baseAppendixCE n (a - r)) -
          (-(Real.log 2 / 2) * (a : ℝ) * (d : ℝ))| ≤ (d : ℝ) * C_step := by
    intro r d hrd
    induction d with
    | zero => simp
    | succ d ih =>
      have ih' := ih (by omega)
      have hstep := hone_step (r + d) (by omega)
      have hsplit :
          (baseAppendixCE n (a - (r + (d + 1))) - baseAppendixCE n (a - r)) -
              (-(Real.log 2 / 2) * (a : ℝ) * ((d + 1 : ℕ) : ℝ)) =
            ((baseAppendixCE n (a - (r + d + 1)) - baseAppendixCE n (a - (r + d))) -
                (-(Real.log 2 / 2) * (a : ℝ))) +
              ((baseAppendixCE n (a - (r + d)) - baseAppendixCE n (a - r)) -
                (-(Real.log 2 / 2) * (a : ℝ) * (d : ℝ))) := by
        rw [show r + (d + 1) = r + d + 1 by omega]
        push_cast
        ring
      rw [hsplit]
      refine (abs_add_le _ _).trans ?_
      push_cast
      linarith
  rcases le_total j₁.1 j₂.1 with hle | hge
  · set d : ℕ := j₂.1 - j₁.1
    have hj₂_eq : m + 1 + j₂.1 = (m + 1 + j₁.1) + d := by omega
    have hd_cast : ((j₁.1 : ℝ) - (j₂.1 : ℝ)) = -(d : ℝ) := by
      have : (j₂.1 : ℝ) - (j₁.1 : ℝ) = (d : ℝ) := (Nat.cast_sub hle).symm
      linarith
    have hd_le : (d : ℝ) ≤ (M : ℝ) + 1 := by
      exact_mod_cast (show d ≤ M + 1 by omega)
    have ht := htele (m + 1 + j₁.1) d (by omega)
    have hneg_eq :
        |(baseAppendixCE n (u j₁) - baseAppendixCE n (u j₂)) -
            (-(Real.log 2 / 2) * (a : ℝ) * ((j₁.1 : ℝ) - (j₂.1 : ℝ)))| =
          |(baseAppendixCE n (a - ((m + 1 + j₁.1) + d)) -
              baseAppendixCE n (a - (m + 1 + j₁.1))) -
            (-(Real.log 2 / 2) * (a : ℝ) * (d : ℝ))| := by
      dsimp [u]
      rw [hj₂_eq, hd_cast, ← abs_neg]
      congr 1
      ring
    rw [hneg_eq]
    exact ht.trans (mul_le_mul_of_nonneg_right hd_le hC_step_pos.le)
  · set d : ℕ := j₁.1 - j₂.1
    have hj₁_eq : m + 1 + j₁.1 = (m + 1 + j₂.1) + d := by omega
    have hd_cast : ((j₁.1 : ℝ) - (j₂.1 : ℝ)) = (d : ℝ) := (Nat.cast_sub hge).symm
    have hd_le : (d : ℝ) ≤ (M : ℝ) + 1 := by
      exact_mod_cast (show d ≤ M + 1 by omega)
    have ht := htele (m + 1 + j₂.1) d (by omega)
    dsimp [u]
    rw [hj₁_eq, hd_cast]
    exact ht.trans (mul_le_mul_of_nonneg_right hd_le hC_step_pos.le)

/-- Pure-algebra and rate-approximation helper for `eventually_commonClass_subprofile_master`:
bridges the empirical coordinate ratios `(p, y, z)` on `Fin M` to the limiting Gibbs profile
`pStar` on `F0M M = {1, …, M}` across both small-`Y` (`0 < Y ≤ p^*_1 / 2`) and large-`Y`
(`Y > p^*_1 / 2`) regimes. -/
private theorem commonClass_rate_approx_bound
    {M : ℕ} {c_r p1_min err : ℝ} (hcr : 0 < c_r) (hp1_min : 0 < p1_min) (herr_nn : 0 ≤ err)
    (herr1 : Real.log 2 / 2 * (M : ℝ) ^ 2 * err ≤ c_r)
    (herr2 : (M : ℝ) * err ≤ ((2 : ℝ) ^ (M + 7))⁻¹)
    (herr3 :
      (max 1 (-Real.log (((2 : ℝ) ^ (M + 7))⁻¹)) * (M : ℝ) +
          Real.log 2 * ((M : ℝ) ^ 2 + (M : ℝ) ^ 2)) * err ≤
        (c_r * ((2 : ℝ) ^ (M + 7))⁻¹) * (p1_min / 2))
    {p y z : Fin M → ℝ}
    (hpzy : ∀ j, z j = p j - y j)
    (hp_sum : ∑ j : Fin M, p j = 1)
    (hy_nn : ∀ j, 0 ≤ y j)
    (hz_nn : ∀ j, 0 ≤ z j)
    (hY_pos : 0 < ∑ j : Fin M, y j)
    (hR_ge_2M6 : ((2 : ℝ) ^ (M + 6))⁻¹ ≤ ∑ j : Fin M, z j)
    {pStar : ℤ → ℝ} {Tstar : ℝ}
    (hpStar_nn : ∀ i ∈ F0M M, 0 ≤ pStar i)
    (hpStar_mean : ∑ i ∈ F0M M, (i : ℝ) * pStar i = Tstar)
    (hp1_lo : p1_min ≤ pStar 1)
    (hp1_lt1 : pStar 1 < 1)
    (hphi1_gap : phiInfAux (pStar 1) + Real.log 2 / 2 * (Tstar - 1) ≤ -2 * c_r)
    (hrate_star :
      ∀ {zStar : ℤ → ℝ},
        (∀ i ∈ F0M M, 0 ≤ zStar i ∧ zStar i ≤ pStar i) →
        let Rstar := ∑ i ∈ F0M M, zStar i
        Rstar * Real.log Rstar +
            Real.log 2 / 2 * ((∑ i ∈ F0M M, (i : ℝ) * zStar i) - Tstar * Rstar) ≤
          -2 * c_r * Rstar * (1 - Rstar))
    (herr_p : ∀ j : Fin M, |p j - pStar ((j.1 : ℤ) + 1)| ≤ err) :
    (∑ j : Fin M, z j) * Real.log (∑ j : Fin M, z j) +
        Real.log 2 / 2 *
          ((∑ j : Fin M, ((j.1 + 1 : ℕ) : ℝ) * p j) * (∑ j : Fin M, y j) -
            ∑ j : Fin M, ((j.1 + 1 : ℕ) : ℝ) * y j) ≤
      -(c_r * ((2 : ℝ) ^ (M + 7))⁻¹) * (∑ j : Fin M, y j) := by
  set r₀ : ℝ := ((2 : ℝ) ^ (M + 7))⁻¹
  have hr₀_pos : 0 < r₀ := by dsimp [r₀]; positivity
  set L_lip : ℝ := max 1 (-Real.log r₀)
  have hL_lip_pos : 0 < L_lip := lt_of_lt_of_le one_pos (le_max_left _ _)
  set c_rate0 : ℝ := c_r * r₀
  have hc_rate0_pos : 0 < c_rate0 := mul_pos hcr hr₀_pos
  set Y : ℝ := ∑ j : Fin M, y j
  set R : ℝ := ∑ j : Fin M, z j
  set T_sh : ℝ := ∑ j : Fin M, ((j.1 + 1 : ℕ) : ℝ) * p j
  set Iy_sh : ℝ := ∑ j : Fin M, ((j.1 + 1 : ℕ) : ℝ) * y j
  set Iz_sh : ℝ := ∑ j : Fin M, ((j.1 + 1 : ℕ) : ℝ) * z j
  have hRY : R = 1 - Y := by
    dsimp [R, Y]
    rw [Finset.sum_congr rfl fun j _ ↦ hpzy j, Finset.sum_sub_distrib, hp_sum]
  have hR_le1 : R ≤ 1 := by rw [hRY]; linarith [hY_pos]
  have hr₀_le_2M6 : r₀ ≤ ((2 : ℝ) ^ (M + 6))⁻¹ := by
    dsimp [r₀]
    rw [show M + 7 = (M + 6) + 1 by omega, pow_succ]
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ (M + 6) := by positivity
    rw [inv_le_inv₀ (by positivity) h2pos]
    linarith
  have hR_mem : R ∈ Set.Icc r₀ 1 := ⟨le_trans hr₀_le_2M6 hR_ge_2M6, hR_le1⟩
  have hIz_eq : Iz_sh - T_sh * R = T_sh * Y - Iy_sh := by
    have hsum_z : Iz_sh = T_sh - Iy_sh := by
      dsimp [Iz_sh, T_sh, Iy_sh]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [hpzy j]; ring
    rw [hsum_z, hRY]; ring
  have hT_diff : |T_sh - Tstar| ≤ (M : ℝ) ^ 2 * err := by
    have hTstar_fin : Tstar = ∑ j : Fin M, ((j.1 + 1 : ℕ) : ℝ) * pStar ((j.1 : ℤ) + 1) := by
      rw [← hpStar_mean, sum_F0M_eq_fin]
      exact Finset.sum_congr rfl fun j _ ↦ by push_cast; rfl
    rw [hTstar_fin]
    dsimp [T_sh]
    rw [← Finset.sum_sub_distrib]
    calc |∑ j : Fin M, (((j.1 + 1 : ℕ) : ℝ) * p j - ((j.1 + 1 : ℕ) : ℝ) * pStar ((j.1 : ℤ) + 1))|
        ≤ ∑ j : Fin M, |((j.1 + 1 : ℕ) : ℝ) * p j - ((j.1 + 1 : ℕ) : ℝ) * pStar ((j.1 : ℤ) + 1)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin M, |((j.1 + 1 : ℕ) : ℝ) * (p j - pStar ((j.1 : ℤ) + 1))| :=
          Finset.sum_congr rfl fun j _ ↦ by rw [← mul_sub]
      _ ≤ ∑ _j : Fin M, (M : ℝ) * err := by
          refine Finset.sum_le_sum fun j _ ↦ ?_
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
          exact mul_le_mul (by exact_mod_cast (show j.1 + 1 ≤ M by omega))
            (herr_p j) (abs_nonneg _) (by positivity)
      _ = (M : ℝ) ^ 2 * err := by
          rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; ring
  rcases le_or_gt Y (pStar 1 / 2) with hY_small | hY_large
  · -- Small-`Y` case: `0 < Y ≤ p^*_1 / 2`
    have hIy_ge_Y : Y ≤ Iy_sh := by
      dsimp [Y, Iy_sh]
      refine Finset.sum_le_sum fun j _ ↦ ?_
      calc y j = 1 * y j := (one_mul _).symm
        _ ≤ ((j.1 + 1 : ℕ) : ℝ) * y j :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast (show 1 ≤ j.1 + 1 by omega)) (hy_nn j)
    have hT_hi : T_sh - 1 ≤ Tstar - 1 + (M : ℝ) ^ 2 * err := by
      linarith [(abs_le.mp hT_diff).2]
    have hmom_le : T_sh * Y - Iy_sh ≤ (Tstar - 1 + (M : ℝ) ^ 2 * err) * Y := by
      have h1 : T_sh * Y - Iy_sh ≤ (T_sh - 1) * Y := by linarith
      exact h1.trans (mul_le_mul_of_nonneg_right hT_hi hY_pos.le)
    have hp1_pos : 0 < pStar 1 := lt_of_lt_of_le hp1_min hp1_lo
    have hY_lt_p1 : Y < pStar 1 := by linarith
    have hphi_mono : phiInfAux Y < phiInfAux (pStar 1) :=
      strictMonoOn_phiInfAux ⟨hY_pos, lt_trans hY_lt_p1 hp1_lt1⟩ ⟨hp1_pos, hp1_lt1⟩ hY_lt_p1
    have hRlogR : R * Real.log R = Y * phiInfAux Y := by
      unfold phiInfAux
      rw [hRY]
      field_simp [hY_pos.ne']
    have hc_le : c_rate0 ≤ c_r := by
      dsimp [c_rate0, r₀]
      calc c_r * ((2 : ℝ) ^ (M + 7))⁻¹ ≤ c_r * 1 :=
            mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))) hcr.le
        _ = c_r := mul_one _
    calc
      R * Real.log R + Real.log 2 / 2 * (T_sh * Y - Iy_sh) ≤
          Y * phiInfAux (pStar 1) +
            Real.log 2 / 2 * ((Tstar - 1 + (M : ℝ) ^ 2 * err) * Y) := by
        rw [hRlogR]
        exact add_le_add (mul_le_mul_of_nonneg_left hphi_mono.le hY_pos.le)
          (mul_le_mul_of_nonneg_left hmom_le (by positivity))
      _ = Y * ((phiInfAux (pStar 1) + Real.log 2 / 2 * (Tstar - 1)) +
            Real.log 2 / 2 * (M : ℝ) ^ 2 * err) := by ring
      _ ≤ Y * (-2 * c_r + c_r) :=
          mul_le_mul_of_nonneg_left (add_le_add hphi1_gap herr1) hY_pos.le
      _ = -c_r * Y := by ring
      _ ≤ -c_rate0 * Y := by
          have hm := mul_le_mul_of_nonneg_right hc_le hY_pos.le
          linarith
  · -- Large-`Y` case: `Y > p^*_1 / 2 ≥ p1_min / 2`
    rw [← hIz_eq]
    let zStar : ℤ → ℝ := fun i ↦
      if hi : 1 ≤ i ∧ i ≤ (M : ℤ) then
        min (z ⟨(i - 1).toNat, by omega⟩) (pStar i)
      else 0
    have hzStar_adm : ∀ i ∈ F0M M, 0 ≤ zStar i ∧ zStar i ≤ pStar i := by
      intro i hi
      have hi_b := Finset.mem_Icc.mp hi
      dsimp [zStar]
      rw [dif_pos hi_b]
      exact ⟨le_min (hz_nn _) (hpStar_nn i hi), min_le_right _ _⟩
    have hzStar_fin : ∀ j : Fin M,
        zStar ((j.1 : ℤ) + 1) = min (z j) (pStar ((j.1 : ℤ) + 1)) := by
      intro j
      have hj_b : 1 ≤ (j.1 : ℤ) + 1 ∧ (j.1 : ℤ) + 1 ≤ (M : ℤ) := ⟨by omega, by omega⟩
      dsimp [zStar]
      rw [dif_pos hj_b]
      congr 2
      apply Fin.ext
      dsimp
      omega
    set Rstar : ℝ := ∑ i ∈ F0M M, zStar i
    have hRstar_fin : Rstar = ∑ j : Fin M, min (z j) (pStar ((j.1 : ℤ) + 1)) := by
      dsimp [Rstar]
      rw [sum_F0M_eq_fin]
      exact Finset.sum_congr rfl fun j _ ↦ hzStar_fin j
    have hz_diff : ∀ j : Fin M,
        0 ≤ z j - min (z j) (pStar ((j.1 : ℤ) + 1)) ∧
          z j - min (z j) (pStar ((j.1 : ℤ) + 1)) ≤ err := by
      intro j
      refine ⟨sub_nonneg.mpr (min_le_left _ _), ?_⟩
      rcases le_total (z j) (pStar ((j.1 : ℤ) + 1)) with hle | hge
      · rw [min_eq_left hle, sub_self]; exact herr_nn
      · rw [min_eq_right hge]
        have hzj_le_pj : z j ≤ p j := by rw [hpzy j]; linarith [hy_nn j]
        linarith [(abs_le.mp (herr_p j)).2]
    have hR_sub_Rstar : 0 ≤ R - Rstar ∧ R - Rstar ≤ (M : ℝ) * err := by
      rw [hRstar_fin]
      dsimp [R]
      rw [← Finset.sum_sub_distrib]
      refine ⟨Finset.sum_nonneg fun j _ ↦ (hz_diff j).1, ?_⟩
      calc ∑ j : Fin M, (z j - min (z j) (pStar ((j.1 : ℤ) + 1)))
          ≤ ∑ _j : Fin M, err := Finset.sum_le_sum fun j _ ↦ (hz_diff j).2
        _ = (M : ℝ) * err := by rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    have hRstar_ge_r0 : r₀ ≤ Rstar := by
      have hpow_id : ((2 : ℝ) ^ (M + 6))⁻¹ - r₀ = r₀ := by
        dsimp [r₀]
        rw [show M + 7 = (M + 6) + 1 by omega, pow_succ]
        ring
      linarith [hR_ge_2M6, hR_sub_Rstar.2, herr2, hpow_id]
    have hRstar_le1 : Rstar ≤ 1 := le_trans (by linarith [hR_sub_Rstar.1]) hR_le1
    have h1mRstar_ge_Y : Y ≤ 1 - Rstar := by linarith [hRY, hR_sub_Rstar.1]
    have hrate_zStar := hrate_star hzStar_adm
    have hmain_neg :
        -2 * c_r * Rstar * (1 - Rstar) ≤ -2 * c_rate0 * Y := by
      have hprod : r₀ * Y ≤ Rstar * (1 - Rstar) :=
        mul_le_mul hRstar_ge_r0 h1mRstar_ge_Y hY_pos.le (le_trans hr₀_pos.le hRstar_ge_r0)
      have hm := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 2 * c_r by positivity)
      dsimp [c_rate0]
      linarith
    have hRlog_diff : |R * Real.log R - Rstar * Real.log Rstar| ≤
        L_lip * (M : ℝ) * err := by
      have hl := abs_mul_log_sub_le_of_mem_Icc hr₀_pos hR_mem ⟨hRstar_ge_r0, hRstar_le1⟩
      rw [abs_of_nonneg hR_sub_Rstar.1] at hl
      exact hl.trans (by
        calc L_lip * (R - Rstar) ≤ L_lip * ((M : ℝ) * err) :=
              mul_le_mul_of_nonneg_left hR_sub_Rstar.2 hL_lip_pos.le
          _ = L_lip * (M : ℝ) * err := by ring)
    have hIz_diff :
        Iz_sh - ∑ i ∈ F0M M, (i : ℝ) * zStar i ≤ (M : ℝ) ^ 2 * err := by
      rw [sum_F0M_eq_fin]
      dsimp [Iz_sh]
      rw [← Finset.sum_sub_distrib]
      calc ∑ j : Fin M, (((j.1 + 1 : ℕ) : ℝ) * z j -
            (((j.1 : ℤ) + 1 : ℤ) : ℝ) * zStar ((j.1 : ℤ) + 1))
          = ∑ j : Fin M, ((j.1 + 1 : ℕ) : ℝ) *
              (z j - min (z j) (pStar ((j.1 : ℤ) + 1))) := by
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            rw [hzStar_fin j]; push_cast; ring
        _ ≤ ∑ _j : Fin M, (M : ℝ) * err := by
            refine Finset.sum_le_sum fun j _ ↦ ?_
            exact mul_le_mul (by exact_mod_cast (show j.1 + 1 ≤ M by omega))
              (hz_diff j).2 (hz_diff j).1 (by positivity)
        _ = (M : ℝ) ^ 2 * err := by
            rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; ring
    have hTstar_nn : 0 ≤ Tstar := by
      rw [← hpStar_mean]
      exact Finset.sum_nonneg fun i hi ↦
        mul_nonneg (by exact_mod_cast (le_trans (by decide : (0 : ℤ) ≤ 1) (Finset.mem_Icc.mp hi).1))
          (hpStar_nn i hi)
    have hTR_diff : Tstar * Rstar - T_sh * R ≤ (M : ℝ) ^ 2 * err := by
      have hid : Tstar * Rstar - T_sh * R =
          Tstar * (Rstar - R) + (Tstar - T_sh) * R := by ring
      have h1 : Tstar * (Rstar - R) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hTstar_nn (by linarith [hR_sub_Rstar.1])
      have hM2_nn : 0 ≤ (M : ℝ) ^ 2 * err := by positivity
      have h2 : (Tstar - T_sh) * R ≤ (M : ℝ) ^ 2 * err := by
        have ht_le : Tstar - T_sh ≤ (M : ℝ) ^ 2 * err := by
          linarith [(abs_le.mp hT_diff).1]
        rcases le_or_gt (Tstar - T_sh) 0 with hnp | _
        · exact le_trans (mul_nonpos_of_nonpos_of_nonneg hnp (le_trans hr₀_pos.le hR_mem.1))
            hM2_nn
        · calc (Tstar - T_sh) * R ≤ ((M : ℝ) ^ 2 * err) * 1 :=
                mul_le_mul ht_le hR_le1 (le_trans hr₀_pos.le hR_mem.1) hM2_nn
            _ = (M : ℝ) ^ 2 * err := mul_one _
      linarith
    have htot_err :
        (R * Real.log R + Real.log 2 / 2 * (Iz_sh - T_sh * R)) -
          (Rstar * Real.log Rstar +
            Real.log 2 / 2 * ((∑ i ∈ F0M M, (i : ℝ) * zStar i) - Tstar * Rstar)) ≤
        (L_lip * (M : ℝ) + Real.log 2 * ((M : ℝ) ^ 2 + (M : ℝ) ^ 2)) * err := by
      have hq2_pos : 0 ≤ Real.log 2 / 2 := (half_pos (Real.log_pos one_lt_two)).le
      have hq_le : Real.log 2 / 2 ≤ Real.log 2 := by linarith [Real.log_pos one_lt_two]
      have hsum_m :
          (Iz_sh - T_sh * R) - ((∑ i ∈ F0M M, (i : ℝ) * zStar i) - Tstar * Rstar) ≤
            ((M : ℝ) ^ 2 + (M : ℝ) ^ 2) * err := by
        linarith [hIz_diff, hTR_diff]
      have hmom_err :
          Real.log 2 / 2 * ((Iz_sh - T_sh * R) -
              ((∑ i ∈ F0M M, (i : ℝ) * zStar i) - Tstar * Rstar)) ≤
            Real.log 2 * ((M : ℝ) ^ 2 + (M : ℝ) ^ 2) * err := by
        calc Real.log 2 / 2 * ((Iz_sh - T_sh * R) -
                ((∑ i ∈ F0M M, (i : ℝ) * zStar i) - Tstar * Rstar))
            ≤ Real.log 2 / 2 * (((M : ℝ) ^ 2 + (M : ℝ) ^ 2) * err) :=
              mul_le_mul_of_nonneg_left hsum_m hq2_pos
          _ ≤ Real.log 2 * (((M : ℝ) ^ 2 + (M : ℝ) ^ 2) * err) :=
              mul_le_mul_of_nonneg_right hq_le (by positivity)
          _ = Real.log 2 * ((M : ℝ) ^ 2 + (M : ℝ) ^ 2) * err := by ring
      linarith [(abs_le.mp hRlog_diff).2, hmom_err]
    have hY_gt_p1min : p1_min / 2 < Y := lt_of_le_of_lt (by linarith [hp1_lo]) hY_large
    have herr_le_cY :
        (L_lip * (M : ℝ) + Real.log 2 * ((M : ℝ) ^ 2 + (M : ℝ) ^ 2)) * err ≤ c_rate0 * Y :=
      herr3.trans (mul_le_mul_of_nonneg_left hY_gt_p1min.le hc_rate0_pos.le)
    linarith [hrate_zStar, hmain_neg, htot_err, herr_le_cY]

/-- Abstract real log-weight closer for `eventually_commonClass_subprofile_master`, isolating all
linear/sum inequalities away from transcendental expressions. -/
private theorem commonClass_logWeight_finish
    {M : ℕ} (hM1 : 1 ≤ M)
    {K a_real C_E V_err Ent_err LogN1 c_rate0 m_real m_min V_rem : ℝ}
    (hK_pos : 0 < K) (ha_pos : 0 < a_real) (hc_rate0_pos : 0 < c_rate0)
    (hLogN1_nn : 0 ≤ LogN1)
    {p y z E : Fin M → ℝ}
    (hp_nn : ∀ j, 0 ≤ p j) (hp_sum : ∑ j : Fin M, p j = 1)
    (hy_nn : ∀ j, 0 ≤ y j)
    (hY_pos : 0 < ∑ j : Fin M, y j) (hY_le1 : ∑ j : Fin M, y j ≤ 1)
    (hE_diff : ∀ i j : Fin M,
      E i - E j ≤ -(Real.log 2 / 2) * a_real * ((i.1 : ℝ) - (j.1 : ℝ)) + C_E)
    (hvertex_replace :
      V_rem ≤ K * a_real * ((∑ j : Fin M, z j) * Real.log (∑ j : Fin M, z j)) +
        V_err * (K * ∑ j : Fin M, y j))
    (hent_coord_sum :
      ∑ j : Fin M,
        (2 * p j * Real.log (p j) - 2 * z j * Real.log (z j) -
          y j * Real.log (y j) - y j) ≤
        (∑ j : Fin M, y j) * Ent_err)
    (hrate_all :
      (∑ j : Fin M, z j) * Real.log (∑ j : Fin M, z j) +
        Real.log 2 / 2 *
          ((∑ j : Fin M, ((j.1 + 1 : ℕ) : ℝ) * p j) * (∑ j : Fin M, y j) -
            ∑ j : Fin M, ((j.1 + 1 : ℕ) : ℝ) * y j) ≤
        -c_rate0 * (∑ j : Fin M, y j))
    (hover1 :
      (1 + Real.log (M : ℝ) + C_E + V_err) * (K * ∑ j : Fin M, y j) ≤
        (c_rate0 / 6) * (K * a_real * ∑ j : Fin M, y j))
    (hover2 :
      K * ((∑ j : Fin M, y j) * Ent_err) ≤
        (c_rate0 / 6) * (K * a_real * ∑ j : Fin M, y j))
    (hover3 :
      (2 * (M : ℝ) + 2) * LogN1 ≤
        (c_rate0 / 6) * (K * a_real * ∑ j : Fin M, y j))
    (hKaY_ge : m_real ≤ K * a_real * ∑ j : Fin M, y j)
    (hm_lo : m_min ≤ m_real)
    {W_val : ℝ}
    (hW_ub :
      Real.log W_val ≤
        V_rem +
          K * ∑ j : Fin M,
            (2 * p j * Real.log (p j) - 2 * z j * Real.log (z j) -
              y j * Real.log (y j) - y j + y j * E j) +
          (2 * (M : ℝ) + 1) * LogN1)
    (hself_le0 :
      K * ∑ j : Fin M, (p j * Real.log (p j) - p j + p j * E j) - LogN1 ≤ 0) :
    W_val ≤ Real.exp (-(c_rate0 / 2) * m_real) ∧
      Real.exp (-(c_rate0 / 2) * m_real) ≤ Real.exp (-(c_rate0 / 2) * m_min) := by
  set Y : ℝ := ∑ j : Fin M, y j
  set R : ℝ := ∑ j : Fin M, z j
  set T_sh : ℝ := ∑ j : Fin M, ((j.1 + 1 : ℕ) : ℝ) * p j
  set Iy_sh : ℝ := ∑ j : Fin M, ((j.1 + 1 : ℕ) : ℝ) * y j
  have hpE_ub :
      ∑ j : Fin M, p j * E j ≤ 1 + Real.log (M : ℝ) + LogN1 / K := by
    have h1 : K * ∑ j : Fin M, p j * E j ≤
        K * (1 - ∑ j : Fin M, p j * Real.log (p j)) + LogN1 := by
      have hexpnd :
          ∑ j : Fin M, (p j * Real.log (p j) - p j + p j * E j) =
            (∑ j : Fin M, p j * Real.log (p j)) - 1 + ∑ j : Fin M, p j * E j := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hp_sum]
      rw [hexpnd] at hself_le0
      linarith
    have h2 := neg_sum_mul_log_le_log_card hM1 hp_nn hp_sum
    have h2' : 1 - ∑ j : Fin M, p j * Real.log (p j) ≤ 1 + Real.log (M : ℝ) := by linarith
    have h3 : K * ∑ j : Fin M, p j * E j ≤ K * (1 + Real.log (M : ℝ)) + LogN1 :=
      h1.trans (add_le_add (mul_le_mul_of_nonneg_left h2' hK_pos.le) le_rfl)
    rw [← le_div_iff₀' hK_pos] at h3
    calc ∑ j : Fin M, p j * E j
        ≤ (K * (1 + Real.log (M : ℝ)) + LogN1) / K := h3
      _ = 1 + Real.log (M : ℝ) + LogN1 / K := by
          rw [add_div, mul_div_cancel_left₀ _ hK_pos.ne']
  have hEi_ub : ∀ i : Fin M,
      E i ≤ (∑ j : Fin M, p j * E j) +
        Real.log 2 / 2 * a_real * (T_sh - ((i.1 + 1 : ℕ) : ℝ)) + C_E := by
    intro i
    have hid : E i - ∑ j : Fin M, p j * E j = ∑ j : Fin M, p j * (E i - E j) := by
      rw [Finset.sum_congr rfl fun j _ ↦ mul_sub (p j) (E i) (E j),
        Finset.sum_sub_distrib, ← Finset.sum_mul, hp_sum, one_mul]
    have hterm_j : ∀ j : Fin M,
        p j * (E i - E j) ≤
          p j * (-(Real.log 2 / 2) * a_real * ((i.1 : ℝ) - (j.1 : ℝ)) + C_E) :=
      fun j ↦ mul_le_mul_of_nonneg_left (hE_diff i j) (hp_nn j)
    have hsum_j := Finset.sum_le_sum (s := Finset.univ) fun (j : Fin M) _ ↦ hterm_j j
    have hrhs_j :
        ∑ j : Fin M, p j * (-(Real.log 2 / 2) * a_real * ((i.1 : ℝ) - (j.1 : ℝ)) + C_E) =
          Real.log 2 / 2 * a_real * (T_sh - ((i.1 + 1 : ℕ) : ℝ)) + C_E := by
      have hsub_idx : ∀ j : Fin M, ((i.1 : ℝ) - (j.1 : ℝ)) =
          ((i.1 + 1 : ℕ) : ℝ) - ((j.1 + 1 : ℕ) : ℝ) := fun j ↦ by push_cast; ring
      simp only [hsub_idx]
      have hexp_j :
          ∑ j : Fin M,
              p j * (-(Real.log 2 / 2) * a_real *
                (((i.1 + 1 : ℕ) : ℝ) - ((j.1 + 1 : ℕ) : ℝ)) + C_E) =
            Real.log 2 / 2 * a_real * (∑ j : Fin M, ((j.1 + 1 : ℕ) : ℝ) * p j) -
              Real.log 2 / 2 * a_real * ((i.1 + 1 : ℕ) : ℝ) * (∑ j : Fin M, p j) +
              C_E * (∑ j : Fin M, p j) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
          ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ ↦ by ring
      rw [hexp_j, hp_sum]
      dsimp [T_sh]
      ring
    linarith
  have hyE_ub :
      K * ∑ i : Fin M, y i * E i ≤
        K * a_real * (Real.log 2 / 2 * (T_sh * Y - Iy_sh)) +
          (1 + Real.log (M : ℝ) + C_E) * (K * Y) + LogN1 := by
    have h1 : ∀ i : Fin M,
        y i * E i ≤
          y i * ((∑ j : Fin M, p j * E j) + C_E) +
            Real.log 2 / 2 * a_real * (T_sh * y i - ((i.1 + 1 : ℕ) : ℝ) * y i) := by
      intro i
      have hm_i := mul_le_mul_of_nonneg_left (hEi_ub i) (hy_nn i)
      linarith [show y i * ((∑ j, p j * E j) +
          Real.log 2 / 2 * a_real * (T_sh - ((i.1 + 1 : ℕ) : ℝ)) + C_E) =
        y i * ((∑ j, p j * E j) + C_E) +
          Real.log 2 / 2 * a_real * (T_sh * y i - ((i.1 + 1 : ℕ) : ℝ) * y i) by ring]
    have hsum_i := Finset.sum_le_sum (s := Finset.univ) fun (i : Fin M) _ ↦ h1 i
    have hrhs_i :
        ∑ i : Fin M,
            (y i * ((∑ j : Fin M, p j * E j) + C_E) +
              Real.log 2 / 2 * a_real * (T_sh * y i - ((i.1 + 1 : ℕ) : ℝ) * y i)) =
          Y * ((∑ j : Fin M, p j * E j) + C_E) +
            Real.log 2 / 2 * a_real * (T_sh * Y - Iy_sh) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
        Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hrhs_i] at hsum_i
    have hmulK := mul_le_mul_of_nonneg_left hsum_i hK_pos.le
    have hpE_mul := mul_le_mul_of_nonneg_left hpE_ub (mul_nonneg hK_pos.le hY_pos.le)
    have hK_cancel : K * Y * (LogN1 / K) = Y * LogN1 := by
      field_simp [hK_pos.ne']
    have hY_log_le : Y * LogN1 ≤ LogN1 := by
      calc Y * LogN1 ≤ 1 * LogN1 := mul_le_mul_of_nonneg_right hY_le1 hLogN1_nn
        _ = LogN1 := one_mul _
    linarith
  have hsplit_sum :
      K * ∑ j : Fin M,
          (2 * p j * Real.log (p j) - 2 * z j * Real.log (z j) -
            y j * Real.log (y j) - y j + y j * E j) =
        K * (∑ j : Fin M,
            (2 * p j * Real.log (p j) - 2 * z j * Real.log (z j) -
              y j * Real.log (y j) - y j)) +
          K * ∑ j : Fin M, y j * E j := by
    rw [Finset.sum_add_distrib, mul_add]
  have hentK := mul_le_mul_of_nonneg_left hent_coord_sum hK_pos.le
  have hrateK := mul_le_mul_of_nonneg_left hrate_all (mul_pos hK_pos ha_pos).le
  have hsum_all : Real.log W_val ≤ -(c_rate0 / 2) * (K * a_real * Y) := by
    linarith [hW_ub, hsplit_sum, hentK, hyE_ub, hvertex_replace, hrateK,
      hover1, hover2, hover3]
  have hlog_le : Real.log W_val ≤ -(c_rate0 / 2) * m_real := by
    have hm := mul_le_mul_of_nonneg_left hKaY_ge (show 0 ≤ c_rate0 / 2 by positivity)
    linarith
  have hW_pos_or_np : W_val ≤ Real.exp (-(c_rate0 / 2) * m_real) := by
    rcases le_or_gt W_val 0 with hnp | hpos
    · exact le_trans hnp (Real.exp_pos _).le
    · exact (Real.log_le_iff_le_exp hpos).mp hlog_le
  have hexp_mono : Real.exp (-(c_rate0 / 2) * m_real) ≤ Real.exp (-(c_rate0 / 2) * m_min) := by
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hm_lo (show 0 ≤ c_rate0 / 2 by positivity)
    linarith
  exact ⟨hW_pos_or_np, hexp_mono⟩

/-- Deterministic empirical geometry, vertex-remainder Lipschitz bridge, and coordinate-entropy
bound for a single `(n, m, a, k, ν)` instance in `eventually_commonClass_subprofile_master`. -/
private theorem commonClass_empirical_geometry_and_entropy
    {M n m a : ℕ} (hM1 : 1 ≤ M) (hn2 : 2 ≤ n) (hm : m ≤ 1)
    (ha_ge_big : 2 * ((M : ℝ) + 2) * (2 : ℝ) ^ (M + 6) ≤ (a : ℝ))
    {k nu : Fin M → ℕ}
    (hMass : selectedVertexMass (fun j : Fin M ↦ a - (m + 1 + j.1)) k = n)
    (hnu : IsPartialSubprofile k nu)
    (hm_lo : (n : ℝ) / (Real.log (n : ℝ)) ^ 3 ≤
      (selectedVertexMass (fun j : Fin M ↦ a - (m + 1 + j.1)) nu : ℝ))
    (hrem_gt : ((2 : ℝ) ^ (M + 5))⁻¹ * (n : ℝ) <
      ((n - selectedVertexMass (fun j : Fin M ↦ a - (m + 1 + j.1)) nu : ℕ) : ℝ)) :
    let u : Fin M → ℕ := fun j ↦ a - (m + 1 + j.1)
    let K : ℝ := (selectedBlockCount k : ℝ)
    let p : Fin M → ℝ := fun j ↦ (k j : ℝ) / K
    let y : Fin M → ℝ := fun j ↦ (nu j : ℝ) / K
    let z : Fin M → ℝ := fun j ↦ ((k j - nu j : ℕ) : ℝ) / K
    let Y : ℝ := ∑ j : Fin M, y j
    let R : ℝ := ∑ j : Fin M, z j
    let rho : ℝ := ((n - selectedVertexMass u nu : ℕ) : ℝ) / (n : ℝ)
    let L_lip : ℝ := max 1 (-Real.log (((2 : ℝ) ^ (M + 7))⁻¹))
    0 < (a : ℝ) ∧ 0 < K ∧
      (∀ j : Fin M, 1 ≤ u j) ∧
      (∀ j : Fin M, 0 ≤ p j) ∧ (∀ j : Fin M, 0 ≤ y j) ∧ (∀ j : Fin M, 0 ≤ z j) ∧
      (∀ j : Fin M, z j = p j - y j) ∧ (∑ j : Fin M, p j = 1) ∧
      0 < Y ∧ Y ≤ 1 ∧ ((2 : ℝ) ^ (M + 6))⁻¹ ≤ R ∧
      ((selectedVertexMass u nu : ℝ) ≤ K * (a : ℝ) * Y) ∧
      ((n : ℝ) * rho * Real.log rho ≤
        K * (a : ℝ) * (R * Real.log R) + 3 * L_lip * ((M : ℝ) + 2) * (K * Y)) ∧
      (∑ j : Fin M,
          (2 * p j * Real.log (p j) - 2 * z j * Real.log (z j) -
            y j * Real.log (y j) - y j) ≤
        Y * Real.log (2 * Real.exp 1 * (M : ℝ) * (Real.log (n : ℝ)) ^ 3)) := by
  intro u K p y z Y R rho L_lip
  set r₀ : ℝ := ((2 : ℝ) ^ (M + 7))⁻¹
  have hr₀_pos : 0 < r₀ := by dsimp [r₀]; positivity
  have hL_lip_pos : 0 < L_lip := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hL_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have ha_ge_2M2 : 2 * ((M : ℝ) + 2) ≤ (a : ℝ) := by
    have hpow_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (M + 6) := one_le_pow₀ (by norm_num)
    calc 2 * ((M : ℝ) + 2) = 2 * ((M : ℝ) + 2) * 1 := (mul_one _).symm
      _ ≤ 2 * ((M : ℝ) + 2) * (2 : ℝ) ^ (M + 6) :=
          mul_le_mul_of_nonneg_left hpow_ge1 (by positivity)
      _ ≤ (a : ℝ) := ha_ge_big
  have ha_gt_mM : m + M + 2 ≤ a := by
    have hnat : 2 * (M + 2) ≤ a := by exact_mod_cast ha_ge_2M2
    omega
  have ha_pos : (0 : ℝ) < (a : ℝ) := lt_of_lt_of_le (by positivity) ha_ge_2M2
  have hu_ge1 : ∀ j : Fin M, 1 ≤ u j := fun j ↦ by dsimp [u]; omega
  have hu_le_a : ∀ j : Fin M, u j ≤ a := fun j ↦ Nat.sub_le _ _
  have hK_nat_pos : 0 < selectedBlockCount k := by
    by_contra hK0
    have hall0 : ∀ j, k j = 0 := by
      have hs0 : ∑ j : Fin M, k j = 0 := Nat.eq_zero_of_not_pos hK0
      exact fun j ↦ Finset.sum_eq_zero_iff.mp hs0 j (Finset.mem_univ j)
    have hM0 : selectedVertexMass u k = 0 := by unfold selectedVertexMass; simp [hall0]
    dsimp [u] at hM0
    omega
  have hK_pos : 0 < K := by dsimp [K]; exact_mod_cast hK_nat_pos
  set m_nu : ℕ := selectedVertexMass u nu
  have hm_le_n : m_nu ≤ n := by
    rw [← hMass]; unfold m_nu selectedVertexMass
    exact Finset.sum_le_sum fun j _ ↦ Nat.mul_le_mul_left (u j) (hnu j)
  have hp_nn : ∀ j, 0 ≤ p j := fun j ↦ div_nonneg (Nat.cast_nonneg _) hK_pos.le
  have hy_nn : ∀ j, 0 ≤ y j := fun j ↦ div_nonneg (Nat.cast_nonneg _) hK_pos.le
  have hz_nn : ∀ j, 0 ≤ z j := fun j ↦ div_nonneg (Nat.cast_nonneg _) hK_pos.le
  have hy_le_p : ∀ j, y j ≤ p j := fun j ↦
    div_le_div_of_nonneg_right (by exact_mod_cast hnu j) hK_pos.le
  have hpzy : ∀ j, z j = p j - y j := fun j ↦ by
    dsimp [p, y, z]; rw [Nat.cast_sub (hnu j)]; ring
  have hp_sum : ∑ j : Fin M, p j = 1 := by
    dsimp [p]
    rw [← Finset.sum_div]
    have hK_sum : ∑ j : Fin M, (k j : ℝ) = K := by
      dsimp [K]; unfold selectedBlockCount; rw [Nat.cast_sum]
    rw [hK_sum]
    exact div_self hK_pos.ne'
  have hp_le1 : ∀ j, p j ≤ 1 := fun j ↦ by
    rw [← hp_sum]
    exact Finset.single_le_sum (fun i _ ↦ hp_nn i) (Finset.mem_univ j)
  have hRY : R = 1 - Y := by
    dsimp [R, Y]
    rw [Finset.sum_congr rfl fun j _ ↦ hpzy j, Finset.sum_sub_distrib, hp_sum]
  have hKaY_ge : (m_nu : ℝ) ≤ K * (a : ℝ) * Y := by
    have hnat : m_nu ≤ a * ∑ j : Fin M, nu j := by
      dsimp [m_nu]; unfold selectedVertexMass
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ ↦ Nat.mul_le_mul_right (nu j) (hu_le_a j)
    have hcast : (m_nu : ℝ) ≤ (a : ℝ) * ∑ j : Fin M, (nu j : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).mpr hnat
      push_cast at this; exact this
    have hKY : K * Y = ∑ j : Fin M, (nu j : ℝ) := by
      dsimp [Y, y]; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ mul_div_cancel₀ _ hK_pos.ne'
    calc (m_nu : ℝ) ≤ (a : ℝ) * (K * Y) := by rwa [hKY]
      _ = K * (a : ℝ) * Y := by ring
  have hKa_le_2n : K * (a : ℝ) ≤ 2 * (n : ℝ) := by
    have hu_half : ∀ j : Fin M, (a : ℝ) / 2 ≤ (u j : ℝ) := by
      intro j
      dsimp [u]
      rw [Nat.cast_sub (by omega : m + 1 + j.1 ≤ a)]
      have hj_le : ((m + 1 + j.1 : ℕ) : ℝ) ≤ (M : ℝ) + 2 := by
        exact_mod_cast (show m + 1 + j.1 ≤ M + 2 by omega)
      linarith [ha_ge_2M2, hj_le]
    have hn_ge : (a : ℝ) / 2 * K ≤ (n : ℝ) := by
      rw [← hMass]; unfold selectedVertexMass
      rw [Nat.cast_sum]
      have hK_sum : K = ∑ j : Fin M, (k j : ℝ) := by
        dsimp [K]; unfold selectedBlockCount; rw [Nat.cast_sum]
      rw [hK_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ ↦ ?_
      rw [Nat.cast_mul]
      exact mul_le_mul_of_nonneg_right (hu_half j) (Nat.cast_nonneg _)
    linarith
  have hY_pos : 0 < Y := by
    have hm_pos : 0 < (m_nu : ℝ) := lt_of_lt_of_le (by positivity) hm_lo
    have hKa_pos : 0 < K * (a : ℝ) := mul_pos hK_pos ha_pos
    by_contra hnp
    have hY0 : Y ≤ 0 := not_lt.mp hnp
    have hle0 : K * (a : ℝ) * Y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hKa_pos.le hY0
    linarith [hm_pos, hKaY_ge, hle0]
  have hY_lb : 1 / (2 * (Real.log (n : ℝ)) ^ 3) ≤ Y := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : (n : ℝ) / (Real.log (n : ℝ)) ^ 3 ≤ K * (a : ℝ) * Y := le_trans hm_lo hKaY_ge
    have h2 : K * (a : ℝ) * Y ≤ 2 * (n : ℝ) * Y :=
      mul_le_mul_of_nonneg_right hKa_le_2n hY_pos.le
    have h3 : (n : ℝ) ≤ 2 * (n : ℝ) * Y * (Real.log (n : ℝ)) ^ 3 :=
      (div_le_iff₀ (pow_pos hL_pos 3)).mp (le_trans h1 h2)
    have h4 : (n : ℝ) * 1 ≤ (n : ℝ) * (Y * (2 * (Real.log (n : ℝ)) ^ 3)) := by linarith
    exact le_of_mul_le_mul_left h4 hn_pos
  set T_sh : ℝ := ∑ j : Fin M, ((j.1 + 1 : ℕ) : ℝ) * p j
  set Iy_sh : ℝ := ∑ j : Fin M, ((j.1 + 1 : ℕ) : ℝ) * y j
  set T_tot : ℝ := (m : ℝ) + T_sh
  set Iy_tot : ℝ := (m : ℝ) * Y + Iy_sh
  have hn_div_K : (n : ℝ) = K * ((a : ℝ) - T_tot) := by
    have h1 : (n : ℝ) = ∑ j : Fin M, (u j : ℝ) * (k j : ℝ) := by
      rw [← hMass]; unfold selectedVertexMass; rw [Nat.cast_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by push_cast; rfl
    have h2 : ∀ j : Fin M, (u j : ℝ) = (a : ℝ) - (m : ℝ) - ((j.1 + 1 : ℕ) : ℝ) := by
      intro j; dsimp [u]; rw [Nat.cast_sub (by omega : m + 1 + j.1 ≤ a)]; push_cast; ring
    have h3 : ∀ j : Fin M, (k j : ℝ) = K * p j := fun j ↦ by
      dsimp [p]; exact (mul_div_cancel₀ _ hK_pos.ne').symm
    rw [h1, Finset.sum_congr rfl fun j _ ↦ by rw [h2 j, h3 j]]
    have hexpnd :
        ∑ j : Fin M, ((a : ℝ) - (m : ℝ) - ((j.1 + 1 : ℕ) : ℝ)) * (K * p j) =
          K * ((a : ℝ) - (m : ℝ)) * (∑ j : Fin M, p j) -
            K * ∑ j : Fin M, ((j.1 + 1 : ℕ) : ℝ) * p j := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    rw [hexpnd, hp_sum]
    dsimp [T_tot, T_sh]
    ring
  have hmnu_div_K : (m_nu : ℝ) = K * ((a : ℝ) * Y - Iy_tot) := by
    have h1 : (m_nu : ℝ) = ∑ j : Fin M, (u j : ℝ) * (nu j : ℝ) := by
      dsimp [m_nu]; unfold selectedVertexMass; rw [Nat.cast_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by push_cast; rfl
    have h2 : ∀ j : Fin M, (u j : ℝ) = (a : ℝ) - (m : ℝ) - ((j.1 + 1 : ℕ) : ℝ) := by
      intro j; dsimp [u]; rw [Nat.cast_sub (by omega : m + 1 + j.1 ≤ a)]; push_cast; ring
    have h3 : ∀ j : Fin M, (nu j : ℝ) = K * y j := fun j ↦ by
      dsimp [y]; exact (mul_div_cancel₀ _ hK_pos.ne').symm
    rw [h1, Finset.sum_congr rfl fun j _ ↦ by rw [h2 j, h3 j]]
    have hexpnd :
        ∑ j : Fin M, ((a : ℝ) - (m : ℝ) - ((j.1 + 1 : ℕ) : ℝ)) * (K * y j) =
          K * ((a : ℝ) - (m : ℝ)) * (∑ j : Fin M, y j) -
            K * ∑ j : Fin M, ((j.1 + 1 : ℕ) : ℝ) * y j := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    rw [hexpnd]
    dsimp [Iy_tot, Iy_sh, Y]
    ring
  have hT_tot_le : T_tot ≤ (M : ℝ) + 2 := by
    have hTsh_le : T_sh ≤ (M : ℝ) * ∑ j : Fin M, p j := by
      dsimp [T_sh]; rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_right ?_ (hp_nn j)
      exact_mod_cast (show j.1 + 1 ≤ M by omega)
    rw [hp_sum, mul_one] at hTsh_le
    have hm_le1 : (m : ℝ) ≤ 1 := by exact_mod_cast hm
    dsimp [T_tot]; linarith
  have hT_tot_nn : 0 ≤ T_tot := by
    dsimp [T_tot, T_sh]
    exact add_nonneg (Nat.cast_nonneg _)
      (Finset.sum_nonneg fun j _ ↦ mul_nonneg (Nat.cast_nonneg _) (hp_nn j))
  have hIy_tot_bounds : 0 ≤ Iy_tot ∧ Iy_tot ≤ ((M : ℝ) + 2) * Y := by
    have hIy_le : Iy_sh ≤ (M : ℝ) * Y := by
      dsimp [Iy_sh, Y]; rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_right ?_ (hy_nn j)
      exact_mod_cast (show j.1 + 1 ≤ M by omega)
    have hm_le1 : (m : ℝ) ≤ 1 := by exact_mod_cast hm
    have hmY_le : (m : ℝ) * Y ≤ 1 * Y := mul_le_mul_of_nonneg_right hm_le1 hY_pos.le
    refine ⟨add_nonneg (mul_nonneg (Nat.cast_nonneg _) hY_pos.le)
      (Finset.sum_nonneg fun j _ ↦ mul_nonneg (Nat.cast_nonneg _) (hy_nn j)), ?_⟩
    dsimp [Iy_tot]
    linarith
  have ha_sub_T_pos : (a : ℝ) / 2 ≤ (a : ℝ) - T_tot := by
    linarith [ha_ge_2M2, hT_tot_le]
  have hrho_sub_R : |rho - R| ≤ 2 * ((M : ℝ) + 2) * Y / (a : ℝ) := by
    have haT_pos : 0 < (a : ℝ) - T_tot := lt_of_lt_of_le (half_pos ha_pos) ha_sub_T_pos
    have hident : rho - R = (Iy_tot - T_tot * Y) / ((a : ℝ) - T_tot) := by
      dsimp [rho, m_nu]
      rw [Nat.cast_sub hm_le_n, hmnu_div_K, hn_div_K, hRY]
      field_simp [hK_pos.ne', haT_pos.ne']
      ring
    have hnum_abs : |Iy_tot - T_tot * Y| ≤ ((M : ℝ) + 2) * Y := by
      rw [abs_le]
      have hTY_le : T_tot * Y ≤ ((M : ℝ) + 2) * Y :=
        mul_le_mul_of_nonneg_right hT_tot_le hY_pos.le
      have hTY_nn : 0 ≤ T_tot * Y := mul_nonneg hT_tot_nn hY_pos.le
      exact ⟨by linarith [hIy_tot_bounds.1, hTY_le],
        by linarith [hIy_tot_bounds.2, hTY_nn]⟩
    rw [hident, abs_div, abs_of_pos haT_pos]
    calc |Iy_tot - T_tot * Y| / ((a : ℝ) - T_tot)
        ≤ (((M : ℝ) + 2) * Y) / ((a : ℝ) / 2) :=
          div_le_div₀ (by positivity) hnum_abs (half_pos ha_pos) ha_sub_T_pos
      _ = 2 * ((M : ℝ) + 2) * Y / (a : ℝ) := by ring
  have hY_le1 : Y ≤ 1 := by
    dsimp [Y]
    rw [← hp_sum]
    exact Finset.sum_le_sum fun j _ ↦ hy_le_p j
  have hrho_gt : ((2 : ℝ) ^ (M + 5))⁻¹ < rho := by
    dsimp [rho]
    rwa [lt_div_iff₀ hn_pos]
  have hrho_le1 : rho ≤ 1 := by
    dsimp [rho]
    rw [div_le_one hn_pos]
    exact_mod_cast Nat.sub_le n m_nu
  have hdiff_le_2M6 : 2 * ((M : ℝ) + 2) * Y / (a : ℝ) ≤ ((2 : ℝ) ^ (M + 6))⁻¹ := by
    rw [div_le_iff₀ ha_pos]
    have h1 : 2 * ((M : ℝ) + 2) * Y ≤ 2 * ((M : ℝ) + 2) * 1 :=
      mul_le_mul_of_nonneg_left hY_le1 (by positivity)
    have h2 : 2 * ((M : ℝ) + 2) ≤ ((2 : ℝ) ^ (M + 6))⁻¹ * (a : ℝ) := by
      rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
      exact ha_ge_big
    linarith
  have hR_ge_2M6 : ((2 : ℝ) ^ (M + 6))⁻¹ ≤ R := by
    have h1 := (abs_le.mp hrho_sub_R).2
    have hpow_id : ((2 : ℝ) ^ (M + 5))⁻¹ - ((2 : ℝ) ^ (M + 6))⁻¹ = ((2 : ℝ) ^ (M + 6))⁻¹ := by
      rw [show M + 6 = (M + 5) + 1 by omega, pow_succ]
      ring
    linarith [hrho_gt, hdiff_le_2M6, hpow_id]
  have hR_le1 : R ≤ 1 := by rw [hRY]; linarith [hY_pos]
  have hr₀_le_2M6 : r₀ ≤ ((2 : ℝ) ^ (M + 6))⁻¹ := by
    dsimp [r₀]
    rw [show M + 7 = (M + 6) + 1 by omega, pow_succ]
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ (M + 6) := by positivity
    rw [inv_le_inv₀ (by positivity) h2pos]
    linarith
  have hr₀_le1 : r₀ ≤ 1 := by
    dsimp [r₀]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hrho_mem : rho ∈ Set.Icc r₀ 1 :=
    ⟨le_trans hr₀_le_2M6 (le_trans (by
      rw [show M + 6 = (M + 5) + 1 by omega, pow_succ]
      have h2pos : (0 : ℝ) < (2 : ℝ) ^ (M + 5) := by positivity
      rw [inv_le_inv₀ (by positivity) h2pos]; linarith) hrho_gt.le), hrho_le1⟩
  have hR_mem : R ∈ Set.Icc r₀ 1 := ⟨le_trans hr₀_le_2M6 hR_ge_2M6, hR_le1⟩
  have hvertex_replace :
      (n : ℝ) * rho * Real.log rho ≤
        K * (a : ℝ) * (R * Real.log R) + 3 * L_lip * ((M : ℝ) + 2) * (K * Y) := by
    have hdecomp :
        (n : ℝ) * rho * Real.log rho - K * (a : ℝ) * (R * Real.log R) =
          K * (((a : ℝ) - T_tot) * (rho * Real.log rho - R * Real.log R) -
            T_tot * (R * Real.log R - 1 * Real.log 1)) := by
      rw [hn_div_K, Real.log_one, mul_zero, sub_zero]
      ring
    have hlip1 := abs_mul_log_sub_le_of_mem_Icc hr₀_pos hrho_mem hR_mem
    have hlip2 := abs_mul_log_sub_le_of_mem_Icc hr₀_pos hR_mem ⟨hr₀_le1, le_rfl⟩
    have haT_le_a : (a : ℝ) - T_tot ≤ (a : ℝ) := by linarith
    have haT_nn : 0 ≤ (a : ℝ) - T_tot := le_trans (half_pos ha_pos).le ha_sub_T_pos
    have hb1 : ((a : ℝ) - T_tot) * |rho * Real.log rho - R * Real.log R| ≤
        2 * L_lip * ((M : ℝ) + 2) * Y := by
      calc ((a : ℝ) - T_tot) * |rho * Real.log rho - R * Real.log R|
          ≤ (a : ℝ) * (L_lip * |rho - R|) :=
            mul_le_mul haT_le_a hlip1 (abs_nonneg _) ha_pos.le
        _ ≤ (a : ℝ) * (L_lip * (2 * ((M : ℝ) + 2) * Y / (a : ℝ))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hrho_sub_R hL_lip_pos.le) ha_pos.le
        _ = 2 * L_lip * ((M : ℝ) + 2) * Y := by field_simp [ha_pos.ne']
    have hb2 : T_tot * |R * Real.log R - 1 * Real.log 1| ≤
        L_lip * ((M : ℝ) + 2) * Y := by
      have habsR1 : |R - 1| = Y := by
        rw [hRY, show 1 - Y - 1 = -Y by ring, abs_neg, abs_of_pos hY_pos]
      rw [habsR1] at hlip2
      calc T_tot * |R * Real.log R - 1 * Real.log 1|
          ≤ ((M : ℝ) + 2) * (L_lip * Y) :=
            mul_le_mul hT_tot_le hlip2 (abs_nonneg _) (by positivity)
        _ = L_lip * ((M : ℝ) + 2) * Y := by ring
    have hcomb_abs :
        ((a : ℝ) - T_tot) * (rho * Real.log rho - R * Real.log R) -
            T_tot * (R * Real.log R - 1 * Real.log 1) ≤
          3 * L_lip * ((M : ℝ) + 2) * Y := by
      have h1 : ((a : ℝ) - T_tot) * (rho * Real.log rho - R * Real.log R) ≤
          ((a : ℝ) - T_tot) * |rho * Real.log rho - R * Real.log R| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) haT_nn
      have h2 : -(T_tot * (R * Real.log R - 1 * Real.log 1)) ≤
          T_tot * |R * Real.log R - 1 * Real.log 1| := by
        rw [← mul_neg]
        exact mul_le_mul_of_nonneg_left (neg_le_abs _) hT_tot_nn
      linarith
    have hmulK := mul_le_mul_of_nonneg_left hcomb_abs hK_pos.le
    linarith [hdecomp, show K * (3 * L_lip * ((M : ℝ) + 2) * Y) =
      3 * L_lip * ((M : ℝ) + 2) * (K * Y) by ring]
  have hent_coord_sum :
      ∑ j : Fin M,
          (2 * p j * Real.log (p j) - 2 * z j * Real.log (z j) -
            y j * Real.log (y j) - y j) ≤
        Y * Real.log (2 * Real.exp 1 * (M : ℝ) * (Real.log (n : ℝ)) ^ 3) := by
    have hterm_le : ∀ j : Fin M,
        2 * p j * Real.log (p j) - 2 * z j * Real.log (z j) -
            y j * Real.log (y j) - y j ≤
          y j - y j * Real.log (y j) := by
      intro j
      rw [hpzy j]
      rcases eq_or_lt_of_le (hy_nn j) with hy0 | hy_pos
      · rw [← hy0]; simp
      · have hpf := profileFree_commonClass_entropy_term_le hy_pos (hy_le_p j) (hp_le1 j)
        rw [Real.log_div (Real.exp_pos 1).ne' hy_pos.ne', Real.log_exp] at hpf
        linarith [hpf, show (2 * p j - 2 * y j) * Real.log (p j - y j) =
          2 * (p j - y j) * Real.log (p j - y j) by ring,
          show y j * (1 - Real.log (y j)) = y j - y j * Real.log (y j) by ring]
    have hsum1 := Finset.sum_le_sum (s := Finset.univ) fun (j : Fin M) _ ↦ hterm_le j
    let qy : Fin M → ℝ := fun j ↦ y j / Y
    have hqy_nn : ∀ j, 0 ≤ qy j := fun j ↦ div_nonneg (hy_nn j) hY_pos.le
    have hqy_sum : ∑ j : Fin M, qy j = 1 := by
      dsimp [qy]; rw [← Finset.sum_div, div_self hY_pos.ne']
    have hqy_ent := neg_sum_mul_log_le_log_card hM1 hqy_nn hqy_sum
    have hsum_id :
        ∑ j : Fin M, (y j - y j * Real.log (y j)) =
          Y * (1 - Real.log Y - ∑ j : Fin M, qy j * Real.log (qy j)) := by
      have hterm_q : ∀ j : Fin M,
          y j - y j * Real.log (y j) =
            Y * qy j - Y * (qy j * Real.log Y) - Y * (qy j * Real.log (qy j)) := by
        intro j
        rcases eq_or_lt_of_le (hy_nn j) with hy0 | hy_pos
        · dsimp [qy]; rw [← hy0]; simp
        · have hYqy : Y * qy j = y j := mul_div_cancel₀ _ hY_pos.ne'
          have hqy_pos : 0 < qy j := div_pos hy_pos hY_pos
          have hlog_y : Real.log (y j) = Real.log Y + Real.log (qy j) := by
            rw [← hYqy, Real.log_mul hY_pos.ne' hqy_pos.ne']
          rw [hlog_y, ← hYqy]
          ring
      rw [Finset.sum_congr rfl fun j _ ↦ hterm_q j, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      have hsum_qY : ∑ j : Fin M, qy j * Real.log Y = Real.log Y := by
        rw [← Finset.sum_mul, hqy_sum, one_mul]
      rw [hqy_sum, hsum_qY]
      ring
    have hsum2 : ∑ j : Fin M, (y j - y j * Real.log (y j)) ≤
        Y * Real.log (Real.exp 1 * (M : ℝ) / Y) := by
      rw [hsum_id]
      have hlog_rhs : Real.log (Real.exp 1 * (M : ℝ) / Y) =
          1 + Real.log (M : ℝ) - Real.log Y := by
        rw [Real.log_div (by positivity) hY_pos.ne',
          Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
      rw [hlog_rhs]
      exact mul_le_mul_of_nonneg_left (by linarith) hY_pos.le
    have hlog_Y_mono : Real.log (Real.exp 1 * (M : ℝ) / Y) ≤
        Real.log (2 * Real.exp 1 * (M : ℝ) * (Real.log (n : ℝ)) ^ 3) := by
      apply Real.log_le_log (by positivity)
      have hdiv_le : 1 / Y ≤ 2 * (Real.log (n : ℝ)) ^ 3 :=
        (one_div_le hY_pos (by positivity)).mpr hY_lb
      have hm_mul := mul_le_mul_of_nonneg_left hdiv_le
        (show 0 ≤ Real.exp 1 * (M : ℝ) by positivity)
      calc Real.exp 1 * (M : ℝ) / Y
          = Real.exp 1 * (M : ℝ) * (1 / Y) := by ring
        _ ≤ Real.exp 1 * (M : ℝ) * (2 * (Real.log (n : ℝ)) ^ 3) := hm_mul
        _ = 2 * Real.exp 1 * (M : ℝ) * (Real.log (n : ℝ)) ^ 3 := by ring
    exact hsum1.trans (hsum2.trans (mul_le_mul_of_nonneg_left hlog_Y_mono hY_pos.le))
  exact ⟨ha_pos, hK_pos, hu_ge1, hp_nn, hy_nn, hz_nn, hpzy, hp_sum,
    hY_pos, hY_le1, hR_ge_2M6, hKaY_ge, hvertex_replace, hent_coord_sum⟩

/-- Unified Appendix C asymptotic engine powering `Lemma 6.1(i)` across both `Regime U` and
`Regime C` and across both marked (`W(ν)`) and unmarked (`F_1^ch(ν)`) weights. -/
private theorem eventually_commonClass_subprofile_master
    {M : ℕ} (hM : 7 ≤ M) {c_r p1_min : ℝ} (hcr : 0 < c_r) (hp1_min : 0 < p1_min)
    (C_p : ℝ) :
    let cW : ℝ := c_r * ((2 : ℝ) ^ (M + 8))⁻¹
    0 < cW ∧ ∀ᶠ n : ℕ in atTop,
      ∀ {m : ℕ}, m ≤ 1 →
        let u : Fin M → ℕ := fun j ↦ phaseNat n - (m + 1 + j.1)
        ∀ (pStar : ℤ → ℝ) (Tstar : ℝ),
          (∀ i ∈ F0M M, 0 ≤ pStar i) →
          (∑ i ∈ F0M M, (i : ℝ) * pStar i = Tstar) →
          p1_min ≤ pStar 1 →
          pStar 1 < 1 →
          phiInfAux (pStar 1) + Real.log 2 / 2 * (Tstar - 1) ≤ -2 * c_r →
          (∀ {zStar : ℤ → ℝ},
            (∀ i ∈ F0M M, 0 ≤ zStar i ∧ zStar i ≤ pStar i) →
            let Rstar := ∑ i ∈ F0M M, zStar i
            Rstar * Real.log Rstar +
                Real.log 2 / 2 * ((∑ i ∈ F0M M, (i : ℝ) * zStar i) - Tstar * Rstar) ≤
              -2 * c_r * Rstar * (1 - Rstar)) →
          ∀ (k nu : Fin M → ℕ),
            selectedVertexMass u k = n →
            (∀ j : Fin M,
              |(k j : ℝ) / (selectedBlockCount k : ℝ) - pStar ((j.1 : ℤ) + 1)| ≤
                C_p * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) →
            IsPartialSubprofile k nu →
            (n : ℝ) / (Real.log (n : ℝ)) ^ 3 ≤ (selectedVertexMass u nu : ℝ) →
            ((2 : ℝ) ^ (M + 5))⁻¹ * (n : ℝ) < ((n - selectedVertexMass u nu : ℕ) : ℝ) →
            ((1 ≤ completeSignedFirstMoment u k →
                partialDiagonalWeight n u k nu ≤
                  Real.exp (-cW * (selectedVertexMass u nu : ℝ)) ∧
                Real.exp (-cW * (selectedVertexMass u nu : ℝ)) ≤
                  Real.exp (-cW * (n : ℝ) / (Real.log (n : ℝ)) ^ 3)) ∧
              (1 ≤ completeUnmarkedFirstMoment u k →
                unmarkedDiagonalWeight n u k nu ≤
                  Real.exp (-cW * (selectedVertexMass u nu : ℝ)) ∧
                Real.exp (-cW * (selectedVertexMass u nu : ℝ)) ≤
                  Real.exp (-cW * (n : ℝ) / (Real.log (n : ℝ)) ^ 3))) := by
  intro cW
  have hcW_pos : 0 < cW := by dsimp [cW]; positivity
  refine ⟨hcW_pos, ?_⟩
  have hM1 : 1 ≤ M := by omega
  obtain ⟨C_E, _, hCE_ev⟩ := eventually_baseAppendixCE_diff_bound M
  set r₀ : ℝ := ((2 : ℝ) ^ (M + 7))⁻¹
  have hr₀_pos : 0 < r₀ := by dsimp [r₀]; positivity
  set L_lip : ℝ := max 1 (-Real.log r₀)
  set C_lin : ℝ := 1 + Real.log (M : ℝ) + C_E + 3 * L_lip * ((M : ℝ) + 2)
  set c_rate0 : ℝ := c_r * r₀
  have hc_rate0_pos : 0 < c_rate0 := mul_pos hcr hr₀_pos
  have hcW_half : cW = c_rate0 / 2 := by
    dsimp [cW, c_rate0, r₀]
    rw [pow_succ, mul_inv, div_eq_mul_inv, mul_assoc]
  set errFn : ℕ → ℝ := fun n ↦ (|C_p| + 1) * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)
  have herr_zero : Tendsto errFn atTop (nhds 0) := by
    have hdiv := logLogOrder_isLittleO_logOrder.tendsto_div_nhds_zero
    have hm := hdiv.const_mul (|C_p| + 1)
    rw [mul_zero] at hm
    exact hm.congr fun n ↦ by dsimp [errFn, logLogOrder, logOrder]; ring
  set C_err_big : ℝ :=
    L_lip * (M : ℝ) + Real.log 2 * ((M : ℝ) ^ 2 + (M : ℝ) ^ 2)
  have herr_small1 : ∀ᶠ n : ℕ in atTop,
      Real.log 2 / 2 * (M : ℝ) ^ 2 * errFn n ≤ c_r := by
    have hm : Tendsto (fun n ↦ Real.log 2 / 2 * (M : ℝ) ^ 2 * errFn n) atTop (nhds 0) := by
      simpa using herr_zero.const_mul (Real.log 2 / 2 * (M : ℝ) ^ 2)
    exact hm.eventually (ge_mem_nhds hcr)
  have herr_small2 : ∀ᶠ n : ℕ in atTop, (M : ℝ) * errFn n ≤ r₀ := by
    have hm : Tendsto (fun n ↦ (M : ℝ) * errFn n) atTop (nhds 0) := by
      simpa using herr_zero.const_mul (M : ℝ)
    exact hm.eventually (ge_mem_nhds hr₀_pos)
  have herr_small3 : ∀ᶠ n : ℕ in atTop,
      C_err_big * errFn n ≤ c_rate0 * (p1_min / 2) := by
    have hm : Tendsto (fun n ↦ C_err_big * errFn n) atTop (nhds 0) := by
      simpa using herr_zero.const_mul C_err_big
    exact hm.eventually (ge_mem_nhds (mul_pos hc_rate0_pos (half_pos hp1_min)))
  have ha_big1 : ∀ᶠ n : ℕ in atTop,
      max (2 * ((M : ℝ) + 2) * (2 : ℝ) ^ (M + 6)) (6 * C_lin / c_rate0) ≤ logOrder n :=
    tendsto_logOrder_atTop.eventually (eventually_ge_atTop _)
  have hent_over_L : ∀ᶠ n : ℕ in atTop,
      Real.log (2 * Real.exp 1 * (M : ℝ) * (Real.log (n : ℝ)) ^ 3) / logOrder n ≤
        c_rate0 / 6 := by
    have hc6 : 0 < c_rate0 / 6 := by positivity
    have hll := logLogOrder_isLittleO_logOrder.tendsto_div_nhds_zero
    have hinvL : Tendsto (fun n : ℕ ↦ 1 / logOrder n) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_logOrder_atTop
    set C_c : ℝ := Real.log (2 * Real.exp 1 * (M : ℝ))
    have hcomb : Tendsto (fun n : ℕ ↦ C_c * (1 / logOrder n) + 3 * (logLogOrder n / logOrder n))
        atTop (nhds 0) := by
      simpa using (hinvL.const_mul C_c).add (hll.const_mul 3)
    filter_upwards [tendsto_logOrder_atTop.eventually (eventually_gt_atTop 1),
      hcomb.eventually (ge_mem_nhds hc6)] with n hL1 hle
    have hL_pos : 0 < Real.log (n : ℝ) := lt_trans zero_lt_one hL1
    have h2eM_pos : 0 < 2 * Real.exp 1 * (M : ℝ) := by positivity
    have hlog_eq :
        Real.log (2 * Real.exp 1 * (M : ℝ) * (Real.log (n : ℝ)) ^ 3) / logOrder n =
          C_c * (1 / logOrder n) + 3 * (logLogOrder n / logOrder n) := by
      rw [Real.log_mul h2eM_pos.ne' (pow_pos hL_pos 3).ne', Real.log_pow]
      dsimp [C_c, logOrder, logLogOrder]
      ring
    rw [hlog_eq]
    exact hle
  have hpoly_over_n : ∀ᶠ n : ℕ in atTop,
      (2 * (M : ℝ) + 2) * Real.log (Real.exp 1 * ((n : ℝ) + 1)) *
          (Real.log (n : ℝ)) ^ 3 / (n : ℝ) ≤
        c_rate0 / 6 := by
    have hc6 : 0 < c_rate0 / 6 := by positivity
    have hdiv0 : Tendsto (fun x : ℝ ↦ (Real.log x) ^ 4 / x) atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using (Real.isLittleO_pow_log_id_atTop (n := 4)).tendsto_div_nhds_zero
    have hnat := (hdiv0.comp tendsto_natCast_atTop_atTop).const_mul (3 * (2 * (M : ℝ) + 2))
    rw [mul_zero] at hnat
    filter_upwards [eventually_ge_atTop 8,
      tendsto_logOrder_atTop.eventually (eventually_ge_atTop 2),
      hnat.eventually (ge_mem_nhds hc6)] with n hn8 hL2 hsmall
    have hL_pos : 0 < Real.log (n : ℝ) := lt_of_lt_of_le two_pos hL2
    have hlog_en1 : Real.log (Real.exp 1 * ((n : ℝ) + 1)) ≤ 3 * Real.log (n : ℝ) := by
      have hn1_nat : n + 1 ≤ n ^ 2 := by
        rw [sq]
        calc n + 1 ≤ 2 * n := by omega
          _ ≤ n * n := Nat.mul_le_mul_right n (by omega)
      have hn1_le : (n : ℝ) + 1 ≤ (n : ℝ) ^ 2 := by exact_mod_cast hn1_nat
      have h1 : Real.log (Real.exp 1 * ((n : ℝ) + 1)) ≤ Real.log (Real.exp 1 * (n : ℝ) ^ 2) :=
        Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left hn1_le (Real.exp_pos 1).le)
      have hlog_rhs : Real.log (Real.exp 1 * (n : ℝ) ^ 2) = 1 + 2 * Real.log (n : ℝ) := by
        rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp, Real.log_pow]
        norm_num
      dsimp [logOrder] at hL2
      linarith
    calc
      (2 * (M : ℝ) + 2) * Real.log (Real.exp 1 * ((n : ℝ) + 1)) *
            (Real.log (n : ℝ)) ^ 3 / (n : ℝ) ≤
          (2 * (M : ℝ) + 2) * (3 * Real.log (n : ℝ)) * (Real.log (n : ℝ)) ^ 3 / (n : ℝ) := by
        gcongr
      _ = 3 * (2 * (M : ℝ) + 2) * ((Real.log (n : ℝ)) ^ 4 / (n : ℝ)) := by ring
      _ ≤ c_rate0 / 6 := hsmall
  filter_upwards [eventually_ge_atTop 8, hCE_ev,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
    tendsto_logLogOrder_atTop.eventually (eventually_ge_atTop 0),
    herr_small1, herr_small2, herr_small3, ha_big1, hent_over_L, hpoly_over_n] with
    n hn8 hCE hPhBnd hll_nn herr1 herr2 herr3 ha_big hentL hpolyn
    m hm u pStar Tstar hpStar_nn hpStar_mean hp1_lo hp1_lt1 hphi1_gap hrate_star
    k nu hMass hp_approx hnu hm_lo hrem_gt
  have hn1 : 1 ≤ n := by omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hL_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  set a : ℕ := phaseNat n
  have ha_ge_L : logOrder n ≤ (a : ℝ) := hPhBnd.1
  have ha_ge_big : 2 * ((M : ℝ) + 2) * (2 : ℝ) ^ (M + 6) ≤ (a : ℝ) :=
    le_trans (le_max_left _ _) (le_trans ha_big ha_ge_L)
  set K : ℝ := (selectedBlockCount k : ℝ)
  let p : Fin M → ℝ := fun j ↦ (k j : ℝ) / K
  let y : Fin M → ℝ := fun j ↦ (nu j : ℝ) / K
  let z : Fin M → ℝ := fun j ↦ ((k j - nu j : ℕ) : ℝ) / K
  set Y : ℝ := ∑ j : Fin M, y j
  set m_nu : ℕ := selectedVertexMass u nu
  set rho : ℝ := ((n - m_nu : ℕ) : ℝ) / (n : ℝ)
  obtain ⟨ha_pos, hK_pos, hu_ge1, hp_nn, hy_nn, hz_nn, hpzy, hp_sum,
    hY_pos, hY_le1, hR_ge_2M6, hKaY_ge, hvertex_replace, hent_coord_sum⟩ :=
    commonClass_empirical_geometry_and_entropy hM1 (by omega : 2 ≤ n) hm ha_ge_big
      hMass hnu hm_lo hrem_gt
  have herr_p : ∀ j : Fin M, |p j - pStar ((j.1 : ℤ) + 1)| ≤ errFn n := by
    intro j
    have hb := hp_approx j
    have hCp_le : C_p ≤ |C_p| + 1 := by linarith [le_abs_self C_p]
    have hll_div_nn : 0 ≤ Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) :=
      div_nonneg hll_nn hL_pos.le
    calc |p j - pStar ((j.1 : ℤ) + 1)|
        ≤ C_p * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := hb
      _ = C_p * (Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) := by ring
      _ ≤ (|C_p| + 1) * (Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hCp_le hll_div_nn
      _ = errFn n := by dsimp [errFn]; ring
  have herrFn_nn : 0 ≤ errFn n := le_trans (abs_nonneg _) (herr_p ⟨0, by omega⟩)
  have hrate_all := commonClass_rate_approx_bound hcr hp1_min herrFn_nn
    herr1 herr2 herr3 hpzy hp_sum hy_nn hz_nn hY_pos hR_ge_2M6
    hpStar_nn hpStar_mean hp1_lo hp1_lt1 hphi1_gap hrate_star herr_p
  have hover1 : C_lin * (K * Y) ≤ (c_rate0 / 6) * (K * (a : ℝ) * Y) := by
    have h1 : 6 * C_lin / c_rate0 ≤ (a : ℝ) :=
      le_trans (le_max_right _ _) (le_trans ha_big ha_ge_L)
    have h2 : C_lin ≤ (c_rate0 / 6) * (a : ℝ) := by
      have := (div_le_iff₀ hc_rate0_pos).mp h1
      linarith
    have hm := mul_le_mul_of_nonneg_right h2 (mul_nonneg hK_pos.le hY_pos.le)
    linarith
  have hover2 :
      K * (Y * Real.log (2 * Real.exp 1 * (M : ℝ) * (Real.log (n : ℝ)) ^ 3)) ≤
        (c_rate0 / 6) * (K * (a : ℝ) * Y) := by
    have hL_ge1 : (1 : ℝ) ≤ Real.log (n : ℝ) := by
      have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ (M + 6) := one_le_pow₀ (by norm_num)
      have hM_nn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
      have h4 : (4 : ℝ) ≤ 2 * ((M : ℝ) + 2) := by linarith
      have h4p : (4 : ℝ) * 1 ≤ 2 * ((M : ℝ) + 2) * (2 : ℝ) ^ (M + 6) :=
        mul_le_mul h4 hpow1 zero_le_one (by positivity)
      have hL4 : (4 : ℝ) ≤ logOrder n := le_trans (by linarith) (le_trans (le_max_left _ _) ha_big)
      dsimp [logOrder] at hL4
      linarith
    have hlog_nn : 0 ≤ Real.log (2 * Real.exp 1 * (M : ℝ) * (Real.log (n : ℝ)) ^ 3) := by
      apply Real.log_nonneg
      have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
      have hM1_r : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
      have hL3 : (1 : ℝ) ≤ (Real.log (n : ℝ)) ^ 3 := one_le_pow₀ hL_ge1
      have h2e : (1 : ℝ) ≤ 2 * Real.exp 1 := by linarith
      have h2eM : (1 : ℝ) ≤ 2 * Real.exp 1 * (M : ℝ) := by
        simpa using mul_le_mul h2e hM1_r zero_le_one (by positivity)
      simpa using mul_le_mul h2eM hL3 zero_le_one (by positivity)
    have hL_pos_ord : 0 < logOrder n := by dsimp [logOrder]; exact hL_pos
    have h1 :
        Real.log (2 * Real.exp 1 * (M : ℝ) * (Real.log (n : ℝ)) ^ 3) / (a : ℝ) ≤
          c_rate0 / 6 :=
      le_trans (div_le_div_of_nonneg_left hlog_nn hL_pos_ord ha_ge_L) hentL
    have h2 := (div_le_iff₀ ha_pos).mp h1
    have hm := mul_le_mul_of_nonneg_left h2 (mul_nonneg hK_pos.le hY_pos.le)
    linarith
  have hover3 :
      (2 * (M : ℝ) + 2) * Real.log (Real.exp 1 * ((n : ℝ) + 1)) ≤
        (c_rate0 / 6) * (K * (a : ℝ) * Y) := by
    have h1 := (div_le_iff₀ hn_pos).mp hpolyn
    have h2 := (le_div_iff₀ (pow_pos hL_pos 3)).mpr h1
    rw [mul_div_assoc] at h2
    exact h2.trans (mul_le_mul_of_nonneg_left (le_trans hm_lo hKaY_ge) (by positivity))
  have hLogN1_nn : 0 ≤ Real.log (Real.exp 1 * ((n : ℝ) + 1)) :=
    Real.log_nonneg (by
      have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
      have hn1_ge1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
      simpa using mul_le_mul he1 hn1_ge1 zero_le_one (by positivity))
  have hfinish : ∀ (W_val s_mark : ℝ),
      let E : Fin M → ℝ := fun j ↦ Real.log K + baseAppendixCE n (u j) + s_mark
      (Real.log W_val ≤
        (n : ℝ) * rho * Real.log rho +
          K * ∑ j : Fin M,
            (2 * p j * Real.log (p j) - 2 * z j * Real.log (z j) -
              y j * Real.log (y j) - y j + y j * E j) +
          (2 * (M : ℝ) + 1) * Real.log (Real.exp 1 * ((n : ℝ) + 1))) →
      (K * ∑ j : Fin M, (p j * Real.log (p j) - p j + p j * E j) -
          Real.log (Real.exp 1 * ((n : ℝ) + 1)) ≤ 0) →
      W_val ≤ Real.exp (-cW * (m_nu : ℝ)) ∧
        Real.exp (-cW * (m_nu : ℝ)) ≤ Real.exp (-cW * (n : ℝ) / (Real.log (n : ℝ)) ^ 3) := by
    intro W_val s_mark E hW_ub hself_le0
    have hE_diff : ∀ i j : Fin M,
        E i - E j ≤ -(Real.log 2 / 2) * (a : ℝ) * ((i.1 : ℝ) - (j.1 : ℝ)) + C_E := by
      intro i j
      have hdiff_eq : E i - E j = baseAppendixCE n (u i) - baseAppendixCE n (u j) := by
        dsimp [E]; ring
      rw [hdiff_eq]
      have hce := (abs_le.mp (hCE hm i j)).2
      linarith
    have hfin := commonClass_logWeight_finish hM1 hK_pos ha_pos hc_rate0_pos hLogN1_nn
      hp_nn hp_sum hy_nn hY_pos hY_le1 hE_diff hvertex_replace hent_coord_sum hrate_all
      hover1 hover2 hover3 hKaY_ge hm_lo hW_ub hself_le0
    rw [hcW_half, mul_div_assoc (-(c_rate0 / 2)) (n : ℝ) ((Real.log (n : ℝ)) ^ 3)]
    exact hfin
  refine ⟨fun hMom_mk ↦ ?_, fun hMom_ch ↦ ?_⟩
  · apply hfinish (partialDiagonalWeight n u k nu) (-Real.log 2)
    · simpa [Fintype.card_fin, baseAppendixCE, K, p, y, z, rho, m_nu, a, u,
        sub_eq_add_neg, add_assoc] using log_partialDiagonalWeight_le hn1 hu_ge1 hMass hnu
    · have hself := log_partialDiagonalWeight_self_ge hn1 hMass
      have hlog_np : Real.log (partialDiagonalWeight n u k k) ≤ 0 := by
        rw [partialDiagonalWeight_self_eq_inv hMass, Real.log_inv]
        linarith [Real.log_nonneg hMom_mk]
      have hself' :
          K * ∑ i : Fin M,
              (p i * Real.log (p i) - p i +
                p i * (Real.log K + baseAppendixCE n (u i) + -Real.log 2)) -
            Real.log (Real.exp 1 * ((n : ℝ) + 1)) ≤
          Real.log (partialDiagonalWeight n u k k) := by
        simpa [baseAppendixCE, K, p, a, u, sub_eq_add_neg, add_assoc] using hself
      linarith
  · apply hfinish (unmarkedDiagonalWeight n u k nu) 0
    · simpa [Fintype.card_fin, baseAppendixCE, K, p, y, z, rho, m_nu, a, u,
        sub_eq_add_neg, add_assoc] using log_unmarkedDiagonalWeight_le hn1 hu_ge1 hMass hnu
    · have hself := log_unmarkedDiagonalWeight_self_ge hn1 hMass
      have hlog_np : Real.log (unmarkedDiagonalWeight n u k k) ≤ 0 := by
        rw [unmarkedDiagonalWeight_self_eq_inv hMass, Real.log_inv]
        linarith [Real.log_nonneg hMom_ch]
      have hself' :
          K * ∑ i : Fin M,
              (p i * Real.log (p i) - p i +
                p i * (Real.log K + baseAppendixCE n (u i) + 0)) -
            Real.log (Real.exp 1 * ((n : ℝ) + 1)) ≤
          Real.log (unmarkedDiagonalWeight n u k k) := by
        simpa [baseAppendixCE, K, p, a, u, sub_eq_add_neg, add_assoc] using hself
      linarith

/-- **Complete asymptotic `Lemma 6.1(i)` in `Regime U` (`lemma-7.1-all-common-subprofiles(i)`):**
for `7 ≤ M`, `m ∈ {0, 1}`, and `δ_- ∈ (x₀, 1 + δ_*]`, there exists a regime-dependent constant
`c_W > 0` such that eventually for all `n` in `Regime U` (`δ_n + m ∈ [δ_-, 1 + δ_*]`) and all
selected profiles `k` (`u_j = α - (m + 1 + j)`, `∑_j u_j k_j = n`,
`|k_j / K - p^*_{j+1}| ≤ C_p log log n / log n`), every subprofile `ν ≤ k` with
`m_ν ≥ n / (log n)³` and `n - m_ν > 2^{-(M+5)} n` satisfies both
`W(ν) ≤ exp(-c_W m_ν) ≤ exp(-c_W n / (log n)³)` (when `1 ≤ E[Z_k^mk]`) and
`F_1^ch(ν) ≤ exp(-c_W m_ν) ≤ exp(-c_W n / (log n)³)` (when `1 ≤ E[X̄_k]`). -/
theorem eventually_commonClass_subprofile_le_regimeU
    {M m : ℕ} (hM : 7 ≤ M) (hm : m ≤ 1)
    {deltaMinus : ℝ} (hd : deltaMinus ∈ Set.Ioc criticalPhaseX0 (1 + deltaStar))
    (C_p : ℝ) :
    ∃ cW : ℝ, 0 < cW ∧ ∀ᶠ n : ℕ in atTop,
      phaseDelta n + (m : ℝ) ∈ Set.Icc deltaMinus (1 + deltaStar) →
      ∀ (lambda : ℝ),
        meanS0M M lambda = phaseTarget (phaseDelta n + (m : ℝ)) →
        let u : Fin M → ℕ := fun j ↦ phaseNat n - (m + 1 + j.1)
        ∀ (k nu : Fin M → ℕ),
          selectedVertexMass u k = n →
          (∀ j : Fin M,
            |(k j : ℝ) / (selectedBlockCount k : ℝ) -
              gibbsProbS0M M lambda ((j.1 : ℤ) + 1)| ≤
            C_p * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) →
          IsPartialSubprofile k nu →
          (n : ℝ) / (Real.log (n : ℝ)) ^ 3 ≤ (selectedVertexMass u nu : ℝ) →
          ((2 : ℝ) ^ (M + 5))⁻¹ * (n : ℝ) < ((n - selectedVertexMass u nu : ℕ) : ℝ) →
          ((1 ≤ completeSignedFirstMoment u k →
              partialDiagonalWeight n u k nu ≤
                Real.exp (-cW * (selectedVertexMass u nu : ℝ)) ∧
              Real.exp (-cW * (selectedVertexMass u nu : ℝ)) ≤
                Real.exp (-cW * (n : ℝ) / (Real.log (n : ℝ)) ^ 3)) ∧
            (1 ≤ completeUnmarkedFirstMoment u k →
              unmarkedDiagonalWeight n u k nu ≤
                Real.exp (-cW * (selectedVertexMass u nu : ℝ)) ∧
              Real.exp (-cW * (selectedVertexMass u nu : ℝ)) ≤
                Real.exp (-cW * (n : ℝ) / (Real.log (n : ℝ)) ^ 3))) := by
  have h1d_eq : 1 + deltaStar = (207 / 200 : ℝ) := by unfold deltaStar; norm_num
  obtain ⟨⟨hx0_pos, _⟩, -, -, hx0_neg⟩ := criticalPhaseX0_bounds_and_sign
  have hphi_dm_neg : phiInf deltaMinus < 0 :=
    hx0_neg deltaMinus ⟨hd.1, h1d_eq ▸ hd.2⟩
  set c_r : ℝ := min (1 / 240) (-phiInf deltaMinus) / 2
  have hcr_pos : 0 < c_r := half_pos (lt_min (by norm_num) (by linarith))
  set lamHi : ℝ := yTilt (209 / 20)
  have hlamHi_pos : 0 < lamHi := by
    dsimp [lamHi]; unfold yTilt
    have h1 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have h2 : 0 < Real.log (209 / 20 : ℝ) := Real.log_pos (by norm_num)
    positivity
  set p1_min : ℝ := ((M : ℝ) * Real.exp (lamHi * (M : ℝ)))⁻¹
  have hp1_min_pos : 0 < p1_min := by dsimp [p1_min]; positivity
  obtain ⟨hcW_pos, hmaster⟩ :=
    eventually_commonClass_subprofile_master hM hcr_pos hp1_min_pos C_p
  refine ⟨_, hcW_pos, ?_⟩
  filter_upwards [hmaster] with n hmn htd lam hmean u k nu hMass hp_ap hnu hm_lo hrem
  set td : ℝ := phaseDelta n + (m : ℝ)
  have htd_hi : td ≤ 207 / 200 := h1d_eq ▸ htd.2
  have h0_le_td : 0 ≤ td := le_trans (le_trans (by norm_num) hx0_pos.le) (le_trans hd.1.le htd.1)
  have hM1 : 1 ≤ M := by omega
  have hM2 : 2 ≤ M := by omega
  have hT_lt_7 : phaseTarget td < sevenMeanY (209 / 20) := by
    have h2hi : 2 / Real.log 2 < (288539009 / 100000000 : ℝ) := by
      rw [div_lt_iff₀ (Real.log_pos one_lt_two)]
      linarith [Real.log_two_gt_d9]
    have hM_hi : 1 + (288539009 / 100000000 : ℝ) < sevenMeanY (209 / 20) := by
      unfold sevenMeanY sevenFirstY sevenPartY; norm_num
    unfold phaseTarget
    linarith
  have hlam_le : lam ≤ lamHi := by
    apply (strictMono_meanS0M hM2).le_iff_le.mp
    rw [hmean]
    exact le_trans hT_lt_7.le (sevenMeanY_le_meanS0M hM (by norm_num))
  have h1_mem : (1 : ℤ) ∈ F0M M := by simp [F0M]; omega
  have hZM_pos := partitionFn_S0M_pos hM1 lam
  have hp1_ge : p1_min ≤ gibbsProbS0M M lam 1 := by
    simp only [gibbsProbS0M, h1_mem, ↓reduceIte]
    have hZM_le : partitionFn (S0M M) lam ≤
        ((M : ℝ) * Real.exp (lamHi * (M : ℝ))) * gaussWeight lam 1 := by
      rw [partitionFn_S0M_eq_sum]
      have hterm : ∀ i ∈ F0M M,
          gaussWeight lam i ≤ Real.exp (lamHi * (M : ℝ)) * gaussWeight lam 1 := by
        intro i hi
        have hi_b := Finset.mem_Icc.mp hi
        have hi_ge1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi_b.1
        have hi_leM : (i : ℝ) ≤ (M : ℝ) := by exact_mod_cast hi_b.2
        unfold gaussWeight
        rw [← Real.exp_add]
        push_cast
        apply Real.exp_le_exp.mpr
        have h1 : lam * ((i : ℝ) - 1) ≤ lamHi * (M : ℝ) := by
          calc lam * ((i : ℝ) - 1) ≤ lamHi * ((i : ℝ) - 1) :=
                mul_le_mul_of_nonneg_right hlam_le (by linarith)
            _ ≤ lamHi * (M : ℝ) := mul_le_mul_of_nonneg_left (by linarith) hlamHi_pos.le
        have h2 : (1 : ℝ) ≤ (i : ℝ) ^ 2 := by
          simpa using pow_le_pow_left₀ zero_le_one hi_ge1 2
        have hq_le : Real.log 2 / 2 * 1 ≤ Real.log 2 / 2 * (i : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (half_pos (Real.log_pos one_lt_two)).le
        linarith
      calc ∑ i ∈ F0M M, gaussWeight lam i
          ≤ ∑ _i ∈ F0M M, Real.exp (lamHi * (M : ℝ)) * gaussWeight lam 1 :=
            Finset.sum_le_sum hterm
        _ = ((F0M M).card : ℝ) * (Real.exp (lamHi * (M : ℝ)) * gaussWeight lam 1) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = ((M : ℝ) * Real.exp (lamHi * (M : ℝ))) * gaussWeight lam 1 := by
            have hcard : (F0M M).card = M := by simp [F0M]
            rw [hcard, mul_assoc]
    rw [le_div_iff₀ hZM_pos]
    have hm := mul_le_mul_of_nonneg_left hZM_le hp1_min_pos.le
    dsimp [p1_min] at hm ⊢
    rwa [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul] at hm
  have hp1_lt_inf : gibbsProbS0M M lam 1 < p1Inf td :=
    gibbsProbS0M_one_lt_p1Inf hM htd_hi hmean
  have hpinf_mem : p1Inf td ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [p1Inf_eq_p1AtTilt]; exact p1AtTilt_mem_Ioo _
  have hp1_lt1 : gibbsProbS0M M lam 1 < 1 := lt_trans hp1_lt_inf hpinf_mem.2
  have hp1_pos : 0 < gibbsProbS0M M lam 1 := lt_of_lt_of_le hp1_min_pos hp1_ge
  have hphi_gap :
      phiInfAux (gibbsProbS0M M lam 1) +
          Real.log 2 / 2 * (phaseTarget td - 1) ≤ -2 * c_r := by
    have hlt := strictMonoOn_phiInfAux ⟨hp1_pos, hp1_lt1⟩ hpinf_mem hp1_lt_inf
    have hphi_td_le : phiInf td ≤ phiInf deltaMinus := by
      rcases eq_or_lt_of_le htd.1 with heq | hlt_d
      · rw [heq]
      · exact (strictAntiOn_phiInf ⟨le_trans (by norm_num) (le_trans hx0_pos.le hd.1.le),
          h1d_eq ▸ hd.2⟩ ⟨h0_le_td, htd_hi⟩ hlt_d).le
    have hphi_def : phiInf td = phiInfAux (p1Inf td) + Real.log 2 / 2 * (phaseTarget td - 1) := rfl
    have hc_le : 2 * c_r ≤ -phiInf deltaMinus := by
      dsimp [c_r]
      have := min_le_right (1 / 240) (-phiInf deltaMinus)
      linarith
    linarith
  have hpStar_nn : ∀ i ∈ F0M M, 0 ≤ gibbsProbS0M M lam i := fun i hi ↦ by
    simp only [gibbsProbS0M, hi, ↓reduceIte]
    exact div_nonneg (gaussWeight_pos _ _).le hZM_pos.le
  exact hmn hm (gibbsProbS0M M lam) (phaseTarget td) hpStar_nn
    ((sum_mul_gibbsProbS0M M lam).trans hmean)
    hp1_ge hp1_lt1 hphi_gap
    (fun {zStar} hz ↦ by
      have hb := commonClass_rate_bound_S0M hM hd.1 htd.1 htd_hi hmean hz
      dsimp [c_r]
      linarith)
    k nu hMass hp_ap hnu hm_lo hrem

/-- **Complete asymptotic `Lemma 6.1(i)` in `Regime C` (`lemma-7.1-all-common-subprofiles(i)`):**
for `8 ≤ M`, `p̄₁ ∈ (0, 1/40]`, `δ_- ∈ (0, δ_*]`, and `γ > 0`, there exists a
regime-dependent constant `c_W > 0` such that eventually for all `n` in `Regime C`
(`δ_n ∈ [δ_-, δ_*]` and `g(p̄₁) + (log 2 / 2)(T_{δ_n} - 1) ≤ -γ`) and all selected capped profiles `k`
(`u_j = α - (1 + j)`, `∑_j u_j k_j = n`, `|k_j / K - p^{cap}_{j+1}| ≤ C_p log log n / log n`),
every subprofile `ν ≤ k` with `m_ν ≥ n / (log n)³` and `n - m_ν > 2^{-(M+5)} n` satisfies both
`W(ν) ≤ exp(-c_W m_ν) ≤ exp(-c_W n / (log n)³)` (when `1 ≤ E[Z_k^mk]`) and
`F_1^ch(ν) ≤ exp(-c_W m_ν) ≤ exp(-c_W n / (log n)³)` (when `1 ≤ E[X̄_k]`). -/
theorem eventually_commonClass_subprofile_le_regimeC
    {M : ℕ} (hM : 8 ≤ M)
    {p1Bar : ℝ} (hp1 : p1Bar ∈ Set.Ioc (0 : ℝ) (1 / 40))
    {deltaMinus : ℝ} (hd : deltaMinus ∈ Set.Ioc (0 : ℝ) deltaStar)
    {gamma : ℝ} (hgam : 0 < gamma)
    (C_p : ℝ) :
    ∃ cW : ℝ, 0 < cW ∧ ∀ᶠ n : ℕ in atTop,
      phaseDelta n ∈ Set.Icc deltaMinus deltaStar →
      phiInfAux p1Bar + Real.log 2 / 2 * (phaseTarget (phaseDelta n) - 1) ≤ -gamma →
      ∀ (lambdaTilde : ℝ),
        meanS0M (M - 1) lambdaTilde = (phaseTarget (phaseDelta n) - 1) / (1 - p1Bar) →
        let u : Fin M → ℕ := fun j ↦ phaseNat n - (1 + j.1)
        ∀ (k nu : Fin M → ℕ),
          selectedVertexMass u k = n →
          (∀ j : Fin M,
            |(k j : ℝ) / (selectedBlockCount k : ℝ) -
              cappedGibbsProbS0M M p1Bar lambdaTilde ((j.1 : ℤ) + 1)| ≤
            C_p * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) →
          IsPartialSubprofile k nu →
          (n : ℝ) / (Real.log (n : ℝ)) ^ 3 ≤ (selectedVertexMass u nu : ℝ) →
          ((2 : ℝ) ^ (M + 5))⁻¹ * (n : ℝ) < ((n - selectedVertexMass u nu : ℕ) : ℝ) →
          ((1 ≤ completeSignedFirstMoment u k →
              partialDiagonalWeight n u k nu ≤
                Real.exp (-cW * (selectedVertexMass u nu : ℝ)) ∧
              Real.exp (-cW * (selectedVertexMass u nu : ℝ)) ≤
                Real.exp (-cW * (n : ℝ) / (Real.log (n : ℝ)) ^ 3)) ∧
            (1 ≤ completeUnmarkedFirstMoment u k →
              unmarkedDiagonalWeight n u k nu ≤
                Real.exp (-cW * (selectedVertexMass u nu : ℝ)) ∧
              Real.exp (-cW * (selectedVertexMass u nu : ℝ)) ≤
                Real.exp (-cW * (n : ℝ) / (Real.log (n : ℝ)) ^ 3))) := by
  have hM7 : 7 ≤ M := by omega
  have hx0_lt_half : criticalPhaseX0 < 1 / 2 :=
    lt_trans criticalPhaseX0_bounds_and_sign.1.2 (by norm_num)
  have hphi_half_neg : phiInf (1 / 2) < 0 :=
    criticalPhaseX0_bounds_and_sign.2.2.2 (1 / 2) ⟨hx0_lt_half, by norm_num⟩
  set c2_half : ℝ := min (1 / 240) (-phiInf (1 / 2))
  set c2_cap : ℝ := min (39 / 40 * c2_half) (min gamma (1 / 2))
  have hc2_half_pos : 0 < c2_half := lt_min (by norm_num) (by linarith)
  have hc2_cap_pos : 0 < c2_cap := lt_min (by positivity) (lt_min hgam (by norm_num))
  set c_r : ℝ := c2_cap / 2
  have hcr_pos : 0 < c_r := half_pos hc2_cap_pos
  obtain ⟨hcW_pos, hmaster⟩ :=
    eventually_commonClass_subprofile_master hM7 hcr_pos hp1.1 C_p
  refine ⟨_, hcW_pos, ?_⟩
  filter_upwards [hmaster] with n hmn hdn hcap_gap lamT hmean_red u k nu hMass hp_ap hnu hm_lo hrem
  have hd_icc : phaseDelta n ∈ Set.Icc (0 : ℝ) deltaStar :=
    ⟨le_trans hd.1.le hdn.1, hdn.2⟩
  have h1mp1_pos : 0 < 1 - p1Bar := by linarith [hp1.2]
  have hM1_pred : 1 ≤ M - 1 := by omega
  have hZ_pred := partitionFn_S0M_pos hM1_pred lamT
  have hsplit_M : ∀ g : ℤ → ℝ,
      ∑ i ∈ F0M M, g i = g 1 + ∑ j ∈ F0M (M - 1), g (j + 1) := by
    intro g
    have hdisj : Disjoint ({1} : Finset ℤ) (Finset.Icc 2 (M : ℤ)) := by simp [Finset.mem_Icc]
    have hun : ({1} : Finset ℤ) ∪ Finset.Icc 2 (M : ℤ) = F0M M := by
      ext i; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc, F0M]; omega
    rw [← hun, Finset.sum_union hdisj, Finset.sum_singleton]
    congr 1
    refine (Finset.sum_bij (fun j _ ↦ j + 1) ?_ ?_ ?_ (fun _ _ ↦ rfl)).symm
    · intro j hj; rw [F0M, Finset.mem_Icc] at hj; rw [Finset.mem_Icc]; exact ⟨by omega, by omega⟩
    · intro a _ b _ h; omega
    · intro i hi; rw [Finset.mem_Icc] at hi
      refine ⟨i - 1, ?_, by omega⟩
      rw [F0M, Finset.mem_Icc]; exact ⟨by omega, by omega⟩
  have hpCap_nn : ∀ i ∈ F0M M, 0 ≤ cappedGibbsProbS0M M p1Bar lamT i := by
    intro i _
    unfold cappedGibbsProbS0M
    split_ifs with h1 h2
    · exact hp1.1.le
    · have hj_mem : i - 1 ∈ F0M (M - 1) := by rw [F0M, Finset.mem_Icc]; omega
      simp only [gibbsProbS0M, hj_mem, ↓reduceIte]
      exact mul_nonneg h1mp1_pos.le (div_nonneg (gaussWeight_pos _ _).le hZ_pred.le)
    · exact le_rfl
  have hpCap_mean :
      ∑ i ∈ F0M M, (i : ℝ) * cappedGibbsProbS0M M p1Bar lamT i = phaseTarget (phaseDelta n) := by
    rw [hsplit_M]
    have h1 : (1 : ℝ) * cappedGibbsProbS0M M p1Bar lamT 1 = p1Bar := by simp [cappedGibbsProbS0M]
    have htail :
        ∑ j ∈ F0M (M - 1), ((j + 1 : ℤ) : ℝ) * cappedGibbsProbS0M M p1Bar lamT (j + 1) =
          (1 - p1Bar) * (1 + meanS0M (M - 1) lamT) := by
      have hcongr : ∀ j ∈ F0M (M - 1),
          ((j + 1 : ℤ) : ℝ) * cappedGibbsProbS0M M p1Bar lamT (j + 1) =
            (1 - p1Bar) * gibbsProbS0M (M - 1) lamT j +
              (1 - p1Bar) * ((j : ℝ) * gibbsProbS0M (M - 1) lamT j) := by
        intro j hj
        rw [F0M, Finset.mem_Icc] at hj
        have hne1 : j + 1 ≠ 1 := by omega
        have h2M : 2 ≤ j + 1 ∧ j + 1 ≤ (M : ℤ) := ⟨by omega, by omega⟩
        simp only [cappedGibbsProbS0M, hne1, h2M, and_self, ↓reduceIte, add_sub_cancel_right]
        push_cast; ring
      rw [Finset.sum_congr rfl hcongr, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, sum_gibbsProbS0M hM1_pred lamT, sum_mul_gibbsProbS0M]
      ring
    simp only [Int.cast_one]
    rw [h1, htail, hmean_red]
    field_simp [h1mp1_pos.ne']
    ring
  have hpCap_1 : cappedGibbsProbS0M M p1Bar lamT 1 = p1Bar := by simp [cappedGibbsProbS0M]
  have hc2_le_gam : 2 * c_r ≤ gamma := by
    dsimp [c_r]
    have h1 : c2_cap ≤ gamma := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hm0 := hmn (m := 0) (by omega)
    (cappedGibbsProbS0M M p1Bar lamT) (phaseTarget (phaseDelta n))
    hpCap_nn hpCap_mean
    (by rw [hpCap_1]) (by rw [hpCap_1]; linarith [hp1.2])
    (by rw [hpCap_1]; linarith [hcap_gap, hc2_le_gam])
    (fun {zStar} hz ↦ by
      have hb := commonClass_capped_rate_bound_S0M hM hd_icc hp1 hgam hcap_gap hmean_red hz
      dsimp [c_r, c2_cap, c2_half]
      linarith)
  have hu_eq : (fun j : Fin M ↦ phaseNat n - (0 + 1 + j.1)) = u := by
    funext j; simp [u]
  rw [hu_eq] at hm0
  exact hm0 k nu hMass hp_ap hnu hm_lo hrem

/-!
## 5. Scrambled-range direct bounds, middle-range sums (`Proposition 7.3`), and v9 Main Theorem
-/

/-- **Proposition 7.3 scrambled-range pointwise bound on `W(ν)` and `F_1^ch(ν)`:**
when `1 ≤ n`, `2 * m_ν ≤ n`, `μ_a ≤ μ(n, u_i)`, and `exp(u_i m_ν / n) ≤ 2`,
both `partialDiagonalWeight n u k nu` and `unmarkedDiagonalWeight n u k nu` are bounded by
`∏ i, (2 k_i² / μ_a)^(ν_i) / ν_i!`. -/
theorem partialDiagonalWeight_and_unmarked_scrambled_le
    {I : Type*} [Fintype I]
    {n : ℕ} (hn : 1 ≤ n)
    {u k nu : I → ℕ}
    {mu_a : ℝ} (hmu_pos : 0 < mu_a)
    (hmu_lb : ∀ i, mu_a ≤ mu n (u i))
    (hm2 : 2 * selectedVertexMass u nu ≤ n)
    (hexp2 : ∀ i, Real.exp ((u i : ℝ) * (selectedVertexMass u nu : ℝ) / (n : ℝ)) ≤ 2) :
    partialDiagonalWeight n u k nu ≤ unmarkedDiagonalWeight n u k nu ∧
      unmarkedDiagonalWeight n u k nu ≤
        ∏ i : I, ((2 * (k i : ℝ) ^ 2 / mu_a) ^ (nu i)) / ((nu i).factorial : ℝ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hW_nn : 0 ≤ partialDiagonalWeight n u k nu := by
    unfold partialDiagonalWeight
    exact div_nonneg (Nat.cast_nonneg _) (partialSignedFirstMoment_pos n u nu).le
  have hW_le_F1 : partialDiagonalWeight n u k nu ≤ unmarkedDiagonalWeight n u k nu := by
    unfold unmarkedDiagonalWeight
    calc partialDiagonalWeight n u k nu
        = 1 * partialDiagonalWeight n u k nu := (one_mul _).symm
      _ ≤ (2 : ℝ) ^ (∑ i, nu i) * partialDiagonalWeight n u k nu :=
          mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num)) hW_nn
  refine ⟨hW_le_F1, ?_⟩
  set m_nu : ℕ := selectedVertexMass u nu
  have hF1_eq :
      unmarkedDiagonalWeight n u k nu =
        (((n - m_nu).factorial : ℝ) / (n.factorial : ℝ)) *
          ∏ i : I,
            (((k i).choose (nu i) : ℝ) ^ 2 * ((nu i).factorial : ℝ) *
              (((u i).factorial : ℝ) * (2 : ℝ) ^ ((u i).choose 2)) ^ (nu i)) := by
    unfold unmarkedDiagonalWeight partialDiagonalWeight partialSignedFirstMoment
      partialMarkingCount partialProfileFactorialProduct selectedBlockCount
      selectedInternalEdgeCount
    have h2b_ne : (2 : ℝ) ^ (∑ i : I, nu i) ≠ 0 := by positivity
    have hnf_ne : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
    have hrem_ne : ((n - m_nu).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have hpf_ne : ((∏ i : I, (u i).factorial ^ nu i * (nu i).factorial : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.prod_pos fun i _ ↦
        mul_pos (pow_pos (Nat.factorial_pos _) _) (Nat.factorial_pos _)).ne'
    have h2e_ne : (2 : ℝ) ^ (∑ i : I, (u i).choose 2 * nu i) ≠ 0 := by positivity
    have hprod_eq :
        ((∏ i : I, (k i).choose (nu i) ^ 2 : ℕ) : ℝ) *
          ((∏ i : I, (u i).factorial ^ nu i * (nu i).factorial : ℕ) : ℝ) *
          (2 : ℝ) ^ (∑ i : I, (u i).choose 2 * nu i) =
        ∏ i : I,
          (((k i).choose (nu i) : ℝ) ^ 2 * ((nu i).factorial : ℝ) *
            (((u i).factorial : ℝ) * (2 : ℝ) ^ ((u i).choose 2)) ^ (nu i)) := by
      have h2pow_prod :
          (2 : ℝ) ^ (∑ i : I, (u i).choose 2 * nu i) =
            ∏ i : I, ((2 : ℝ) ^ ((u i).choose 2)) ^ (nu i) := by
        rw [← Finset.prod_pow_eq_pow_sum]
        exact Finset.prod_congr rfl fun i _ ↦ pow_mul (2 : ℝ) ((u i).choose 2) (nu i)
      rw [Nat.cast_prod, Nat.cast_prod, h2pow_prod, ← Finset.prod_mul_distrib,
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      push_cast
      rw [mul_pow]
      ring
    dsimp [m_nu] at hrem_ne ⊢
    field_simp [h2b_ne, hnf_ne, hrem_ne, hpf_ne, h2e_ne]
    rw [← hprod_eq]
  have hfac_le :
      ((n - m_nu).factorial : ℝ) / (n.factorial : ℝ) ≤
        ∏ i : I, ((((n : ℝ) ^ (u i))⁻¹) * 2) ^ (nu i) := by
    have htr := (transmuted_factorial_ratio_le hn hm2 ({1} : Finset ℕ) (fun _ ↦ m_nu)
      (by simp) (fun x hx _ ↦ by simp at hx; subst hx; exact hn)).1
    have hnpow : ((n : ℝ) ^ m_nu)⁻¹ = ∏ i : I, (((n : ℝ) ^ (u i))⁻¹) ^ (nu i) := by
      dsimp [m_nu]; unfold selectedVertexMass
      rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      rw [pow_mul, inv_pow]
    have hexp_prod : Real.exp ((m_nu : ℝ) ^ 2 / (n : ℝ)) ≤ ∏ i : I, (2 : ℝ) ^ (nu i) := by
      have hm_sq : (m_nu : ℝ) ^ 2 / (n : ℝ) =
          ∑ i : I, (nu i : ℝ) * ((u i : ℝ) * (m_nu : ℝ) / (n : ℝ)) := by
        have hm_sum : (m_nu : ℝ) = ∑ i : I, (u i : ℝ) * (nu i : ℝ) := by
          dsimp [m_nu]; unfold selectedVertexMass; rw [Nat.cast_sum]
          exact Finset.sum_congr rfl fun i _ ↦ by push_cast; rfl
        conv_lhs => rw [sq, hm_sum]
        rw [Finset.sum_mul, Finset.sum_div]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [← hm_sum]; ring
      rw [hm_sq, Real.exp_sum]
      refine Finset.prod_le_prod (fun _ _ ↦ (Real.exp_pos _).le) fun i _ ↦ ?_
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos _).le (hexp2 i) (nu i)
    calc ((n - m_nu).factorial : ℝ) / (n.factorial : ℝ)
        ≤ ((n : ℝ) ^ m_nu)⁻¹ * Real.exp ((m_nu : ℝ) ^ 2 / (n : ℝ)) := htr
      _ ≤ (∏ i : I, (((n : ℝ) ^ (u i))⁻¹) ^ (nu i)) * ∏ i : I, (2 : ℝ) ^ (nu i) := by
          rw [← hnpow]
          exact mul_le_mul_of_nonneg_left hexp_prod (by positivity)
      _ = ∏ i : I, ((((n : ℝ) ^ (u i))⁻¹) * 2) ^ (nu i) := by
          rw [← Finset.prod_mul_distrib]
          exact Finset.prod_congr rfl fun i _ ↦ (mul_pow _ _ _).symm
  have hcoord : ∀ i : I,
      ((((n : ℝ) ^ (u i))⁻¹ * 2) ^ (nu i)) *
          (((k i).choose (nu i) : ℝ) ^ 2 * ((nu i).factorial : ℝ) *
            (((u i).factorial : ℝ) * (2 : ℝ) ^ ((u i).choose 2)) ^ (nu i)) ≤
        ((2 * (k i : ℝ) ^ 2 / mu_a) ^ (nu i)) / ((nu i).factorial : ℝ) := by
    intro i
    have hch_le : ((k i).choose (nu i) : ℝ) ^ 2 * ((nu i).factorial : ℝ) ≤
        ((k i : ℝ) ^ 2) ^ (nu i) / ((nu i).factorial : ℝ) := by
      have hdesc : (k i).choose (nu i) * (nu i).factorial = (k i).descFactorial (nu i) := by
        rw [mul_comm, Nat.descFactorial_eq_factorial_mul_choose]
      have hle_pow : (k i).descFactorial (nu i) ≤ (k i) ^ (nu i) := Nat.descFactorial_le_pow _ _
      have hnat_sq : ((k i).choose (nu i) * (nu i).factorial) ^ 2 ≤ ((k i) ^ 2) ^ (nu i) := by
        rw [hdesc, pow_right_comm]
        exact Nat.pow_le_pow_left hle_pow 2
      have hreal_sq : (((k i).choose (nu i) : ℝ) * ((nu i).factorial : ℝ)) ^ 2 ≤
          ((k i : ℝ) ^ 2) ^ (nu i) := by exact_mod_cast hnat_sq
      have hnuf_pos : (0 : ℝ) < ((nu i).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
      rw [le_div_iff₀ hnuf_pos]
      calc ((k i).choose (nu i) : ℝ) ^ 2 * ((nu i).factorial : ℝ) * ((nu i).factorial : ℝ)
          = (((k i).choose (nu i) : ℝ) * ((nu i).factorial : ℝ)) ^ 2 := by ring
        _ ≤ ((k i : ℝ) ^ 2) ^ (nu i) := hreal_sq
    have hu_mu : ((u i).factorial : ℝ) * (2 : ℝ) ^ ((u i).choose 2) * ((n : ℝ) ^ (u i))⁻¹ ≤
        mu_a⁻¹ := by
      have hdesc_u : (u i).factorial * n.choose (u i) ≤ n ^ (u i) := by
        rw [← Nat.descFactorial_eq_factorial_mul_choose]
        exact Nat.descFactorial_le_pow n (u i)
      have hdesc_r : ((u i).factorial : ℝ) * (n.choose (u i) : ℝ) ≤ (n : ℝ) ^ (u i) := by
        exact_mod_cast hdesc_u
      have hmu_i_pos : 0 < mu n (u i) := lt_of_lt_of_le hmu_pos (hmu_lb i)
      have hmu_eq : mu n (u i) = (n.choose (u i) : ℝ) * ((2 : ℝ) ^ ((u i).choose 2))⁻¹ := rfl
      have h1 : ((u i).factorial : ℝ) * (2 : ℝ) ^ ((u i).choose 2) * ((n : ℝ) ^ (u i))⁻¹ *
          mu n (u i) ≤ 1 := by
        rw [hmu_eq]
        have h2ne : (2 : ℝ) ^ ((u i).choose 2) ≠ 0 := by positivity
        have hrew :
            ((u i).factorial : ℝ) * (2 : ℝ) ^ ((u i).choose 2) * ((n : ℝ) ^ (u i))⁻¹ *
                ((n.choose (u i) : ℝ) * ((2 : ℝ) ^ ((u i).choose 2))⁻¹) =
              (((u i).factorial : ℝ) * (n.choose (u i) : ℝ)) / (n : ℝ) ^ (u i) := by
          field_simp [h2ne, (pow_pos hn_pos (u i)).ne']
        rw [hrew, div_le_one (pow_pos hn_pos (u i))]
        exact hdesc_r
      have h2 : ((u i).factorial : ℝ) * (2 : ℝ) ^ ((u i).choose 2) * ((n : ℝ) ^ (u i))⁻¹ ≤
          (mu n (u i))⁻¹ := by
        rw [inv_eq_one_div (mu n (u i))]
        exact (le_div_iff₀ hmu_i_pos).mpr h1
      exact h2.trans (inv_anti₀ hmu_pos (hmu_lb i))
    have hpow_u :
        ((((n : ℝ) ^ (u i))⁻¹ * 2) *
            (((u i).factorial : ℝ) * (2 : ℝ) ^ ((u i).choose 2))) ^ (nu i) ≤
          (2 / mu_a) ^ (nu i) := by
      refine pow_le_pow_left₀ (by positivity) ?_ (nu i)
      have hrew : (((n : ℝ) ^ (u i))⁻¹ * 2) *
          (((u i).factorial : ℝ) * (2 : ℝ) ^ ((u i).choose 2)) =
        2 * (((u i).factorial : ℝ) * (2 : ℝ) ^ ((u i).choose 2) * ((n : ℝ) ^ (u i))⁻¹) := by ring
      rw [hrew, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hu_mu two_pos.le
    calc
      ((((n : ℝ) ^ (u i))⁻¹ * 2) ^ (nu i)) *
            (((k i).choose (nu i) : ℝ) ^ 2 * ((nu i).factorial : ℝ) *
              (((u i).factorial : ℝ) * (2 : ℝ) ^ ((u i).choose 2)) ^ (nu i)) =
          (((((n : ℝ) ^ (u i))⁻¹ * 2) *
              (((u i).factorial : ℝ) * (2 : ℝ) ^ ((u i).choose 2))) ^ (nu i)) *
            (((k i).choose (nu i) : ℝ) ^ 2 * ((nu i).factorial : ℝ)) := by
        rw [mul_pow]; ring
      _ ≤ ((2 / mu_a) ^ (nu i)) * (((k i : ℝ) ^ 2) ^ (nu i) / ((nu i).factorial : ℝ)) :=
          mul_le_mul hpow_u hch_le (by positivity) (by positivity)
      _ = ((2 * (k i : ℝ) ^ 2 / mu_a) ^ (nu i)) / ((nu i).factorial : ℝ) := by
          rw [← mul_div_assoc, ← mul_pow]
          congr 2
          ring
  rw [hF1_eq]
  calc
    (((n - m_nu).factorial : ℝ) / (n.factorial : ℝ)) *
          ∏ i : I,
            (((k i).choose (nu i) : ℝ) ^ 2 * ((nu i).factorial : ℝ) *
              (((u i).factorial : ℝ) * (2 : ℝ) ^ ((u i).choose 2)) ^ (nu i)) ≤
        (∏ i : I, ((((n : ℝ) ^ (u i))⁻¹) * 2) ^ (nu i)) *
          ∏ i : I,
            (((k i).choose (nu i) : ℝ) ^ 2 * ((nu i).factorial : ℝ) *
              (((u i).factorial : ℝ) * (2 : ℝ) ^ ((u i).choose 2)) ^ (nu i)) :=
      mul_le_mul_of_nonneg_right hfac_le
        (Finset.prod_nonneg fun _ _ ↦ by positivity)
    _ = ∏ i : I,
          (((((n : ℝ) ^ (u i))⁻¹ * 2) ^ (nu i)) *
            (((k i).choose (nu i) : ℝ) ^ 2 * ((nu i).factorial : ℝ) *
              (((u i).factorial : ℝ) * (2 : ℝ) ^ ((u i).choose 2)) ^ (nu i))) :=
        (Finset.prod_mul_distrib).symm
    _ ≤ ∏ i : I, ((2 * (k i : ℝ) ^ 2 / mu_a) ^ (nu i)) / ((nu i).factorial : ℝ) :=
        Finset.prod_le_prod (fun _ _ ↦ by positivity) fun i _ ↦ hcoord i

/-- **Proposition 7.3 scrambled-range subprofile sum bound on `W(ν)` and `F_1^ch(ν)`:**
summing `partialDiagonalWeight` or `unmarkedDiagonalWeight` over any finite family `S` of
scrambled subprofiles `ν ≤ k` (`2 m_ν ≤ n`, `exp(u_i m_ν / n) ≤ 2`) is bounded by
`exp(2 * (∑_i k_i)² / μ_a)`. -/
theorem sum_scrambled_partial_and_unmarkedDiagonalWeight_le_exp
    {I : Type*} [Fintype I] [DecidableEq I]
    {n : ℕ} (hn : 1 ≤ n)
    {u k : I → ℕ}
    {mu_a : ℝ} (hmu_pos : 0 < mu_a)
    (hmu_lb : ∀ i, mu_a ≤ mu n (u i))
    (S : Finset (I → ℕ))
    (hS : ∀ nu ∈ S,
      IsPartialSubprofile k nu ∧
      2 * selectedVertexMass u nu ≤ n ∧
      ∀ i, Real.exp ((u i : ℝ) * (selectedVertexMass u nu : ℝ) / (n : ℝ)) ≤ 2) :
    (∑ nu ∈ S, partialDiagonalWeight n u k nu) ≤
        (∑ nu ∈ S, unmarkedDiagonalWeight n u k nu) ∧
      (∑ nu ∈ S, unmarkedDiagonalWeight n u k nu) ≤
        Real.exp (2 * (selectedBlockCount k : ℝ) ^ 2 / mu_a) := by
  classical
  have hpt : ∀ nu ∈ S,
      partialDiagonalWeight n u k nu ≤ unmarkedDiagonalWeight n u k nu ∧
        unmarkedDiagonalWeight n u k nu ≤
          ∏ i : I, ((2 * (k i : ℝ) ^ 2 / mu_a) ^ (nu i)) / ((nu i).factorial : ℝ) := by
    intro nu hnuS
    obtain ⟨_, h2, h3⟩ := hS nu hnuS
    exact partialDiagonalWeight_and_unmarked_scrambled_le hn hmu_pos hmu_lb h2 h3
  refine ⟨Finset.sum_le_sum fun nu hnuS ↦ (hpt nu hnuS).1, ?_⟩
  let embed : {nu // nu ∈ S} → ((i : I) → Fin (k i + 1)) :=
    fun nu i ↦ ⟨nu.1 i, Nat.lt_succ_of_le ((hS nu.1 nu.2).1 i)⟩
  have hinj : Function.Injective embed := by
    intro a b hab
    apply Subtype.ext
    funext i
    exact congrArg Fin.val (congrFun hab i)
  have hsum_le_box :
      (∑ nu ∈ S, ∏ i : I, ((2 * (k i : ℝ) ^ 2 / mu_a) ^ (nu i)) / ((nu i).factorial : ℝ)) ≤
        ∑ g : (i : I) → Fin (k i + 1),
          ∏ i : I, ((2 * (k i : ℝ) ^ 2 / mu_a) ^ (g i : ℕ)) / ((g i : ℕ).factorial : ℝ) := by
    rw [← Finset.sum_coe_sort S]
    have hmap :
        (∑ x : {nu // nu ∈ S},
            ∏ i : I, ((2 * (k i : ℝ) ^ 2 / mu_a) ^ (x.1 i)) / ((x.1 i).factorial : ℝ)) =
          ∑ g ∈ Finset.univ.image embed,
            ∏ i : I, ((2 * (k i : ℝ) ^ 2 / mu_a) ^ (g i : ℕ)) / ((g i : ℕ).factorial : ℝ) := by
      rw [Finset.sum_image (fun a _ b _ hab ↦ hinj hab)]
    rw [hmap]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun _ _ _ ↦ Finset.prod_nonneg fun _ _ ↦ by positivity
  have hbox_le_exp :
      (∑ g : (i : I) → Fin (k i + 1),
          ∏ i : I, ((2 * (k i : ℝ) ^ 2 / mu_a) ^ (g i : ℕ)) / ((g i : ℕ).factorial : ℝ)) ≤
        Real.exp (2 * (selectedBlockCount k : ℝ) ^ 2 / mu_a) := by
    rw [← Fintype.prod_sum fun (i : I) (m : Fin (k i + 1)) ↦
      ((2 * (k i : ℝ) ^ 2 / mu_a) ^ (m : ℕ)) / ((m : ℕ).factorial : ℝ)]
    have hcoord_exp : ∀ i : I,
        (∑ m : Fin (k i + 1),
            ((2 * (k i : ℝ) ^ 2 / mu_a) ^ (m : ℕ)) / ((m : ℕ).factorial : ℝ)) ≤
          Real.exp (2 * (k i : ℝ) ^ 2 / mu_a) := by
      intro i
      rw [Fin.sum_univ_eq_sum_range
        (fun m : ℕ ↦ ((2 * (k i : ℝ) ^ 2 / mu_a) ^ m) / (m.factorial : ℝ)) (k i + 1)]
      exact Real.sum_le_exp_of_nonneg (by positivity) (k i + 1)
    have hprod_le :
        (∏ i : I, ∑ m : Fin (k i + 1),
            ((2 * (k i : ℝ) ^ 2 / mu_a) ^ (m : ℕ)) / ((m : ℕ).factorial : ℝ)) ≤
          ∏ i : I, Real.exp (2 * (k i : ℝ) ^ 2 / mu_a) :=
      Finset.prod_le_prod
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ by positivity)
        fun i _ ↦ hcoord_exp i
    rw [← Real.exp_sum] at hprod_le
    refine hprod_le.trans (Real.exp_le_exp.mpr ?_)
    have hsq : ∑ i : I, (k i : ℝ) ^ 2 ≤ (∑ i : I, (k i : ℝ)) ^ 2 := by
      have hnat : ∑ i : I, (k i) ^ 2 ≤ (∑ i : I, k i) ^ 2 := by
        induction (Finset.univ : Finset I) using Finset.induction_on with
        | empty => simp
        | @insert x s hxs ih =>
          rw [Finset.sum_insert hxs, Finset.sum_insert hxs]
          calc (k x) ^ 2 + ∑ a ∈ s, (k a) ^ 2
              ≤ (k x) ^ 2 + (∑ a ∈ s, k a) ^ 2 := Nat.add_le_add_left ih _
            _ ≤ (k x + ∑ a ∈ s, k a) ^ 2 := by rw [add_sq]; omega
      exact_mod_cast hnat
    have hrew_lhs : (∑ i : I, 2 * (k i : ℝ) ^ 2 / mu_a) =
        (2 / mu_a) * ∑ i : I, (k i : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
    have hK_eq : (selectedBlockCount k : ℝ) = ∑ i : I, (k i : ℝ) := by
      unfold selectedBlockCount; rw [Nat.cast_sum]
    rw [hrew_lhs, hK_eq]
    have hm := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 2 / mu_a by positivity)
    linarith [show (2 / mu_a) * (∑ i : I, (k i : ℝ)) ^ 2 =
      2 * (∑ i : I, (k i : ℝ)) ^ 2 / mu_a by ring]
  exact (Finset.sum_le_sum fun nu hnuS ↦ (hpt nu hnuS).2).trans
    (hsum_le_box.trans hbox_le_exp)

private theorem tendsto_middleRange_envelope_zero
    {M : ℕ} {cW c₀ : ℝ} (hcW : 0 < cW) (hc₀ : c₀ ∈ Set.Ioo (0 : ℝ) 1) (C_ov : ℝ) :
    Tendsto (fun n : ℕ ↦
      Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) * ((n + 1 : ℝ) ^ M) *
        (Real.exp (-cW * (n : ℝ) / (Real.log (n : ℝ)) ^ 3) +
          Real.exp (-(1 / 2 : ℝ) * (n : ℝ) ^ (1 - c₀))))
      atTop (nhds 0) := by
  have h1mc0_pos : 0 < 1 - c₀ := sub_pos.mpr hc₀.2
  have hterm1 : Tendsto (fun n : ℕ ↦
      Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) * ((n + 1 : ℝ) ^ M) *
        Real.exp (-cW * (n : ℝ) / (Real.log (n : ℝ)) ^ 3))
      atTop (nhds 0) := by
    have hL8 : Tendsto (fun x : ℝ ↦ (Real.log x) ^ 8 / x) atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using (Real.isLittleO_pow_log_id_atTop (n := 8)).tendsto_div_nhds_zero
    have hsmall : ∀ᶠ n : ℕ in atTop,
        (|C_ov| + (M : ℝ) + 2) * ((Real.log (n : ℝ)) ^ 8 / (n : ℝ)) ≤ cW / 2 := by
      have hm := (hL8.comp tendsto_natCast_atTop_atTop).const_mul (|C_ov| + (M : ℝ) + 2)
      rw [mul_zero] at hm
      exact hm.eventually (ge_mem_nhds (half_pos hcW))
    have hexp_neg : Tendsto (fun n : ℕ ↦ Real.exp (-(cW / 2) * (n : ℝ) / (Real.log (n : ℝ)) ^ 3))
        atTop (nhds 0) := by
      have hdiv0 : Tendsto (fun x : ℝ ↦ (Real.log x) ^ 3 / x) atTop (nhds 0) := by
        simpa [div_eq_mul_inv] using
          (Real.isLittleO_pow_log_id_atTop (n := 3)).tendsto_div_nhds_zero
      have hpos_ev : ∀ᶠ n : ℕ in atTop, 0 < (Real.log (n : ℝ)) ^ 3 / (n : ℝ) := by
        filter_upwards [eventually_ge_atTop 2] with n hn2
        have hL_pos : 0 < Real.log (n : ℝ) :=
          Real.log_pos (by exact_mod_cast (show 1 < n by omega))
        positivity
      have hinv_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ) / (Real.log (n : ℝ)) ^ 3) atTop atTop := by
        have h := Tendsto.inv_tendsto_nhdsGT_zero
          (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
            (hdiv0.comp tendsto_natCast_atTop_atTop) hpos_ev)
        exact h.congr fun n ↦ inv_div _ _
      have hneg_atBot :
          Tendsto (fun n : ℕ ↦ -(cW / 2) * (n : ℝ) / (Real.log (n : ℝ)) ^ 3) atTop atBot := by
        have hm := Tendsto.const_mul_atTop_of_neg (by linarith : -(cW / 2) < 0) hinv_atTop
        exact hm.congr fun n ↦ by ring
      exact Real.tendsto_exp_atBot.comp hneg_atBot
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ by positivity) ?_ hexp_neg
    filter_upwards [eventually_ge_atTop 8,
      tendsto_logOrder_atTop.eventually (eventually_ge_atTop 2), hsmall] with n hn8 hL2 hsm
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hL_pos : 0 < Real.log (n : ℝ) := lt_of_lt_of_le two_pos hL2
    have hn1_pos : (0 : ℝ) < (n + 1 : ℝ) := by positivity
    have hlog_n1 : Real.log (n + 1 : ℝ) ≤ 2 * Real.log (n : ℝ) := by
      have hn1_nat : n + 1 ≤ n ^ 2 := by
        rw [sq]
        calc n + 1 ≤ 2 * n := by omega
          _ ≤ n * n := Nat.mul_le_mul_right n (by omega)
      have hn1_le : (n + 1 : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hn1_nat
      have h1 := Real.log_le_log hn1_pos hn1_le
      rwa [Real.log_pow, Nat.cast_ofNat] at h1
    have hpow_M : ((n + 1 : ℝ) ^ M) = Real.exp ((M : ℝ) * Real.log (n + 1 : ℝ)) := by
      rw [Real.exp_nat_mul, Real.exp_log hn1_pos]
    rw [hpow_M, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h2L_le_L5 : 2 * Real.log (n : ℝ) ≤ (Real.log (n : ℝ)) ^ 5 := by
      dsimp [logOrder] at hL2
      have hL4 : (16 : ℝ) ≤ (Real.log (n : ℝ)) ^ 4 := by
        have := pow_le_pow_left₀ two_pos.le hL2 4
        norm_num at this; exact this
      calc 2 * Real.log (n : ℝ)
          ≤ (Real.log (n : ℝ)) ^ 4 * Real.log (n : ℝ) :=
            mul_le_mul_of_nonneg_right (by linarith) hL_pos.le
        _ = (Real.log (n : ℝ)) ^ 5 := by ring
    have hcov_tight : C_ov * (Real.log (n : ℝ)) ^ 5 + (M : ℝ) * Real.log (n + 1 : ℝ) ≤
        (|C_ov| + (M : ℝ) + 2) * (Real.log (n : ℝ)) ^ 5 := by
      have h1 : C_ov * (Real.log (n : ℝ)) ^ 5 ≤ |C_ov| * (Real.log (n : ℝ)) ^ 5 :=
        mul_le_mul_of_nonneg_right (le_abs_self C_ov) (by positivity)
      have h2 : (M : ℝ) * Real.log (n + 1 : ℝ) ≤ (M : ℝ) * (Real.log (n : ℝ)) ^ 5 :=
        mul_le_mul_of_nonneg_left (le_trans hlog_n1 h2L_le_L5) (by positivity)
      have h3 : (0 : ℝ) ≤ 2 * (Real.log (n : ℝ)) ^ 5 := by positivity
      linarith
    have hsm_mul :
        (|C_ov| + (M : ℝ) + 2) * (Real.log (n : ℝ)) ^ 5 ≤
          (cW / 2) * (n : ℝ) / (Real.log (n : ℝ)) ^ 3 := by
      have hmul : (|C_ov| + (M : ℝ) + 2) * (Real.log (n : ℝ)) ^ 8 ≤ (cW / 2) * (n : ℝ) := by
        rw [← mul_div_assoc, div_le_iff₀ hn_pos] at hsm
        exact hsm
      rw [le_div_iff₀ (pow_pos hL_pos 3)]
      calc (|C_ov| + (M : ℝ) + 2) * (Real.log (n : ℝ)) ^ 5 * (Real.log (n : ℝ)) ^ 3
          = (|C_ov| + (M : ℝ) + 2) * (Real.log (n : ℝ)) ^ 8 := by ring
        _ ≤ cW / 2 * (n : ℝ) := hmul
    have hdiv_alg :
        (cW / 2 * (n : ℝ) / (Real.log (n : ℝ)) ^ 3) +
          (-cW * (n : ℝ) / (Real.log (n : ℝ)) ^ 3) =
        -(cW / 2) * (n : ℝ) / (Real.log (n : ℝ)) ^ 3 := by ring
    linarith [hcov_tight, hsm_mul, hdiv_alg]
  have hterm2 : Tendsto (fun n : ℕ ↦
      Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) * ((n + 1 : ℝ) ^ M) *
        Real.exp (-(1 / 2 : ℝ) * (n : ℝ) ^ (1 - c₀)))
      atTop (nhds 0) := by
    have hlo := (isLittleO_log_rpow_rpow_atTop (5 : ℝ) h1mc0_pos).tendsto_div_nhds_zero
    have hsmall : ∀ᶠ n : ℕ in atTop,
        (|C_ov| + (M : ℝ) + 2) * ((Real.log (n : ℝ)) ^ (5 : ℝ) / (n : ℝ) ^ (1 - c₀)) ≤ 1 / 4 := by
      have hm := (hlo.comp tendsto_natCast_atTop_atTop).const_mul (|C_ov| + (M : ℝ) + 2)
      rw [mul_zero] at hm
      exact hm.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
    have hexp_neg : Tendsto (fun n : ℕ ↦ Real.exp (-(1 / 4 : ℝ) * (n : ℝ) ^ (1 - c₀)))
        atTop (nhds 0) := by
      have hrp : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (1 - c₀)) atTop atTop :=
        (tendsto_rpow_atTop h1mc0_pos).comp tendsto_natCast_atTop_atTop
      exact Real.tendsto_exp_atBot.comp
        (Tendsto.const_mul_atTop_of_neg (by norm_num : -(1 / 4 : ℝ) < 0) hrp)
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ by positivity) ?_ hexp_neg
    filter_upwards [eventually_ge_atTop 8,
      tendsto_logOrder_atTop.eventually (eventually_ge_atTop 2), hsmall] with n hn8 hL2 hsm
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hL_pos : 0 < Real.log (n : ℝ) := lt_of_lt_of_le two_pos hL2
    have hn1_pos : (0 : ℝ) < (n + 1 : ℝ) := by positivity
    have hrp_pos : 0 < (n : ℝ) ^ (1 - c₀) := Real.rpow_pos_of_pos hn_pos _
    have hlog_n1 : Real.log (n + 1 : ℝ) ≤ 2 * Real.log (n : ℝ) := by
      have hn1_nat : n + 1 ≤ n ^ 2 := by
        rw [sq]
        calc n + 1 ≤ 2 * n := by omega
          _ ≤ n * n := Nat.mul_le_mul_right n (by omega)
      have hn1_le : (n + 1 : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hn1_nat
      have h1 := Real.log_le_log hn1_pos hn1_le
      rwa [Real.log_pow, Nat.cast_ofNat] at h1
    have h2L_le_L5 : 2 * Real.log (n : ℝ) ≤ (Real.log (n : ℝ)) ^ 5 := by
      dsimp [logOrder] at hL2
      have hL4 : (16 : ℝ) ≤ (Real.log (n : ℝ)) ^ 4 := by
        have := pow_le_pow_left₀ two_pos.le hL2 4
        norm_num at this; exact this
      calc 2 * Real.log (n : ℝ)
          ≤ (Real.log (n : ℝ)) ^ 4 * Real.log (n : ℝ) :=
            mul_le_mul_of_nonneg_right (by linarith) hL_pos.le
        _ = (Real.log (n : ℝ)) ^ 5 := by ring
    have hpow_M : ((n + 1 : ℝ) ^ M) = Real.exp ((M : ℝ) * Real.log (n + 1 : ℝ)) := by
      rw [Real.exp_nat_mul, Real.exp_log hn1_pos]
    rw [hpow_M, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hcov_tight : C_ov * (Real.log (n : ℝ)) ^ 5 + (M : ℝ) * Real.log (n + 1 : ℝ) ≤
        (|C_ov| + (M : ℝ) + 2) * (Real.log (n : ℝ)) ^ 5 := by
      have h1 : C_ov * (Real.log (n : ℝ)) ^ 5 ≤ |C_ov| * (Real.log (n : ℝ)) ^ 5 :=
        mul_le_mul_of_nonneg_right (le_abs_self C_ov) (by positivity)
      have h2 : (M : ℝ) * Real.log (n + 1 : ℝ) ≤ (M : ℝ) * (Real.log (n : ℝ)) ^ 5 :=
        mul_le_mul_of_nonneg_left (le_trans hlog_n1 h2L_le_L5) (by positivity)
      have h3 : (0 : ℝ) ≤ 2 * (Real.log (n : ℝ)) ^ 5 := by positivity
      linarith
    have hsm_mul :
        (|C_ov| + (M : ℝ) + 2) * (Real.log (n : ℝ)) ^ 5 ≤
          (1 / 4 : ℝ) * (n : ℝ) ^ (1 - c₀) := by
      have h1 : (Real.log (n : ℝ)) ^ (5 : ℝ) = (Real.log (n : ℝ)) ^ (5 : ℕ) :=
        Real.rpow_natCast _ 5
      rw [h1, ← mul_div_assoc, div_le_iff₀ hrp_pos] at hsm
      exact hsm
    linarith
  simpa [mul_add] using hterm1.add hterm2

/-- **Proposition 7.3 middle-range subprofile sum convergence in `Regime U`:**
combining `Lemma 6.1(i)` (`eventually_commonClass_subprofile_le_regimeU`) and `Lemma 6.1(ii)`
(`eventually_partialDiagonalWeight_subprofile_le_exp_neg_half` and
`eventually_unmarkedDiagonalWeight_subprofile_le_exp_neg_half`), for every `ε > 0` and overlap
exponent constant `C_ov`, eventually across all `n` in `Regime U`, all admissible profiles `k`,
and any finite family `S` of middle-range subprofiles (`n / (log n)³ ≤ m_ν` and
`n^(1 - c₀) ≤ n - m_ν`, `c₀ = min(δ_- / 2, 1 / 60)`),
`exp(C_ov (log n)⁵) * ∑_{ν ∈ S} W(ν) < ε` and `exp(C_ov (log n)⁵) * ∑_{ν ∈ S} F_1^ch(ν) < ε`. -/
theorem eventually_middleRange_commonClass_sum_small_regimeU
    {M m : ℕ} (hM : 7 ≤ M) (hm : m ≤ 1)
    {deltaMinus : ℝ} (hd : deltaMinus ∈ Set.Ioc criticalPhaseX0 (1 + deltaStar))
    (C_p C_ov : ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop,
      phaseDelta n + (m : ℝ) ∈ Set.Icc deltaMinus (1 + deltaStar) →
      ∀ (lambda : ℝ),
        meanS0M M lambda = phaseTarget (phaseDelta n + (m : ℝ)) →
        let u : Fin M → ℕ := fun j ↦ phaseNat n - (m + 1 + j.1)
        ∀ (k : Fin M → ℕ) (S : Finset (Fin M → ℕ)),
          selectedVertexMass u k = n →
          (∀ j : Fin M,
            |(k j : ℝ) / (selectedBlockCount k : ℝ) -
              gibbsProbS0M M lambda ((j.1 : ℤ) + 1)| ≤
            C_p * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) →
          (∀ nu ∈ S,
            IsPartialSubprofile k nu ∧
            (n : ℝ) / (Real.log (n : ℝ)) ^ 3 ≤ (selectedVertexMass u nu : ℝ) ∧
            (n : ℝ) ^ (1 - secondMomentExponent deltaMinus) ≤
              ((n - selectedVertexMass u nu : ℕ) : ℝ)) →
          ((1 ≤ completeSignedFirstMoment u k →
              Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) *
                (∑ nu ∈ S, partialDiagonalWeight n u k nu) < eps) ∧
            (1 ≤ completeUnmarkedFirstMoment u k →
              Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) *
                (∑ nu ∈ S, unmarkedDiagonalWeight n u k nu) < eps)) := by
  classical
  obtain ⟨cW, hcW_pos, hPart1⟩ := eventually_commonClass_subprofile_le_regimeU hM hm hd C_p
  obtain ⟨⟨hx0_pos, _⟩, _⟩ := criticalPhaseX0_bounds_and_sign
  have hd_pos : 0 < deltaMinus := lt_trans (lt_of_le_of_lt (by norm_num) hx0_pos) hd.1
  set c₀ : ℝ := secondMomentExponent deltaMinus
  have hc₀_mem : c₀ ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_min (half_pos hd_pos) (by norm_num),
      lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩
  have henv := (tendsto_middleRange_envelope_zero (M := M) hcW_pos hc₀_mem C_ov).eventually
    (gt_mem_nhds heps)
  have ha_ge : ∀ᶠ n : ℕ in atTop, M + 3 ≤ phaseNat n := by
    filter_upwards [eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
      tendsto_logOrder_atTop.eventually (eventually_ge_atTop ((M : ℝ) + 3))] with n hPh hL
    have : ((M : ℝ) + 3 : ℝ) ≤ (phaseNat n : ℝ) := le_trans hL hPh.1
    exact_mod_cast this
  filter_upwards [hPart1, eventually_partialDiagonalWeight_subprofile_le_exp_neg_half M,
    eventually_unmarkedDiagonalWeight_subprofile_le_exp_neg_half M, henv, ha_ge] with
    n h1 h2_mk h2_ch henv_n ha_n htd lam hmean u k S hMass hp_ap hS
  have hu_bounds : ∀ j : Fin M, 1 ≤ u j ∧ phaseNat n - (M + 1) ≤ u j ∧ u j ≤ phaseNat n := by
    intro j; dsimp [u]; exact ⟨by omega, by omega, Nat.sub_le _ _⟩
  have hk_le_n : ∀ j : Fin M, k j ≤ n := by
    intro j
    calc k j = 1 * k j := (one_mul _).symm
      _ ≤ u j * k j := Nat.mul_le_mul_right (k j) (hu_bounds j).1
      _ ≤ selectedVertexMass u k :=
          Finset.single_le_sum (f := fun i ↦ u i * k i) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
      _ = n := hMass
  have hS_card : (S.card : ℝ) ≤ (n + 1 : ℝ) ^ M := by
    let emb : {nu // nu ∈ S} → (Fin M → Fin (n + 1)) :=
      fun nu j ↦ ⟨nu.1 j, Nat.lt_succ_of_le (le_trans ((hS nu.1 nu.2).1 j) (hk_le_n j))⟩
    have hinj : Function.Injective emb := by
      intro a b hab; apply Subtype.ext; funext j; exact congrArg Fin.val (congrFun hab j)
    have hcard_nat : S.card ≤ (n + 1) ^ M := by
      have := Fintype.card_le_of_injective emb hinj
      simpa [Fintype.card_coe, Fintype.card_pi, Fintype.card_fin] using this
    exact_mod_cast hcard_nat
  refine ⟨fun hMom_mk ↦ ?_, fun hMom_ch ↦ ?_⟩
  · have hpt : ∀ nu ∈ S,
        partialDiagonalWeight n u k nu ≤
          Real.exp (-cW * (n : ℝ) / (Real.log (n : ℝ)) ^ 3) +
            Real.exp (-(1 / 2 : ℝ) * (n : ℝ) ^ (1 - c₀)) := by
      intro nu hnuS
      obtain ⟨hsub, hm_lo, hrem_lo⟩ := hS nu hnuS
      rcases lt_or_ge (((2 : ℝ) ^ (M + 5))⁻¹ * (n : ℝ))
          ((n - selectedVertexMass u nu : ℕ) : ℝ) with hgt | hle
      · have hb := ((h1 htd lam hmean k nu hMass hp_ap hsub hm_lo hgt).1 hMom_mk)
        exact le_trans (hb.1.trans hb.2) (le_add_of_nonneg_right (Real.exp_pos _).le)
      · have hb := h2_mk u k nu 0 le_rfl hu_bounds hMass hsub hle (by simpa using hMom_mk)
        have hrem_exp :
            Real.exp (-(((n - selectedVertexMass u nu : ℕ) : ℝ) / 2)) ≤
              Real.exp (-(1 / 2 : ℝ) * (n : ℝ) ^ (1 - c₀)) :=
          Real.exp_le_exp.mpr (by linarith)
        exact le_trans (hb.1.trans (hb.2.trans hrem_exp))
          (le_add_of_nonneg_left (Real.exp_pos _).le)
    have hsum :
        (∑ nu ∈ S, partialDiagonalWeight n u k nu) ≤
          ((n + 1 : ℝ) ^ M) *
            (Real.exp (-cW * (n : ℝ) / (Real.log (n : ℝ)) ^ 3) +
              Real.exp (-(1 / 2 : ℝ) * (n : ℝ) ^ (1 - c₀))) := by
      calc ∑ nu ∈ S, partialDiagonalWeight n u k nu
          ≤ ∑ _nu ∈ S, (Real.exp (-cW * (n : ℝ) / (Real.log (n : ℝ)) ^ 3) +
              Real.exp (-(1 / 2 : ℝ) * (n : ℝ) ^ (1 - c₀))) := Finset.sum_le_sum hpt
        _ = (S.card : ℝ) * _ := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((n + 1 : ℝ) ^ M) * _ := mul_le_mul_of_nonneg_right hS_card (by positivity)
    exact lt_of_le_of_lt
      ((mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le).trans_eq (by ring)) henv_n
  · have hpt : ∀ nu ∈ S,
        unmarkedDiagonalWeight n u k nu ≤
          Real.exp (-cW * (n : ℝ) / (Real.log (n : ℝ)) ^ 3) +
            Real.exp (-(1 / 2 : ℝ) * (n : ℝ) ^ (1 - c₀)) := by
      intro nu hnuS
      obtain ⟨hsub, hm_lo, hrem_lo⟩ := hS nu hnuS
      rcases lt_or_ge (((2 : ℝ) ^ (M + 5))⁻¹ * (n : ℝ))
          ((n - selectedVertexMass u nu : ℕ) : ℝ) with hgt | hle
      · have hb := ((h1 htd lam hmean k nu hMass hp_ap hsub hm_lo hgt).2 hMom_ch)
        exact le_trans (hb.1.trans hb.2) (le_add_of_nonneg_right (Real.exp_pos _).le)
      · have hb := h2_ch u k nu 0 le_rfl hu_bounds hMass hsub hle (by simpa using hMom_ch)
        have hrem_exp :
            Real.exp (-(((n - selectedVertexMass u nu : ℕ) : ℝ) / 2)) ≤
              Real.exp (-(1 / 2 : ℝ) * (n : ℝ) ^ (1 - c₀)) :=
          Real.exp_le_exp.mpr (by linarith)
        exact le_trans (hb.1.trans (hb.2.trans hrem_exp))
          (le_add_of_nonneg_left (Real.exp_pos _).le)
    have hsum :
        (∑ nu ∈ S, unmarkedDiagonalWeight n u k nu) ≤
          ((n + 1 : ℝ) ^ M) *
            (Real.exp (-cW * (n : ℝ) / (Real.log (n : ℝ)) ^ 3) +
              Real.exp (-(1 / 2 : ℝ) * (n : ℝ) ^ (1 - c₀))) := by
      calc ∑ nu ∈ S, unmarkedDiagonalWeight n u k nu
          ≤ ∑ _nu ∈ S, (Real.exp (-cW * (n : ℝ) / (Real.log (n : ℝ)) ^ 3) +
              Real.exp (-(1 / 2 : ℝ) * (n : ℝ) ^ (1 - c₀))) := Finset.sum_le_sum hpt
        _ = (S.card : ℝ) * _ := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((n + 1 : ℝ) ^ M) * _ := mul_le_mul_of_nonneg_right hS_card (by positivity)
    exact lt_of_le_of_lt
      ((mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le).trans_eq (by ring)) henv_n

/-- **Proposition 7.3 middle-range subprofile sum convergence in `Regime C`:**
combining `Lemma 6.1(i)` (`eventually_commonClass_subprofile_le_regimeC`) and `Lemma 6.1(ii)`
across all middle-range subprofiles (`n / (log n)³ ≤ m_ν` and `n^(1 - c₀) ≤ n - m_ν`),
weighted by `exp(C_ov (log n)⁵)`. -/
theorem eventually_middleRange_commonClass_sum_small_regimeC
    {M : ℕ} (hM : 8 ≤ M)
    {p1Bar : ℝ} (hp1 : p1Bar ∈ Set.Ioc (0 : ℝ) (1 / 40))
    {deltaMinus : ℝ} (hd : deltaMinus ∈ Set.Ioc (0 : ℝ) deltaStar)
    {gamma : ℝ} (hgam : 0 < gamma)
    (C_p C_ov : ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop,
      phaseDelta n ∈ Set.Icc deltaMinus deltaStar →
      phiInfAux p1Bar + Real.log 2 / 2 * (phaseTarget (phaseDelta n) - 1) ≤ -gamma →
      ∀ (lambdaTilde : ℝ),
        meanS0M (M - 1) lambdaTilde = (phaseTarget (phaseDelta n) - 1) / (1 - p1Bar) →
        let u : Fin M → ℕ := fun j ↦ phaseNat n - (1 + j.1)
        ∀ (k : Fin M → ℕ) (S : Finset (Fin M → ℕ)),
          selectedVertexMass u k = n →
          (∀ j : Fin M,
            |(k j : ℝ) / (selectedBlockCount k : ℝ) -
              cappedGibbsProbS0M M p1Bar lambdaTilde ((j.1 : ℤ) + 1)| ≤
            C_p * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) →
          (∀ nu ∈ S,
            IsPartialSubprofile k nu ∧
            (n : ℝ) / (Real.log (n : ℝ)) ^ 3 ≤ (selectedVertexMass u nu : ℝ) ∧
            (n : ℝ) ^ (1 - secondMomentExponent deltaMinus) ≤
              ((n - selectedVertexMass u nu : ℕ) : ℝ)) →
          ((1 ≤ completeSignedFirstMoment u k →
              Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) *
                (∑ nu ∈ S, partialDiagonalWeight n u k nu) < eps) ∧
            (1 ≤ completeUnmarkedFirstMoment u k →
              Real.exp (C_ov * (Real.log (n : ℝ)) ^ 5) *
                (∑ nu ∈ S, unmarkedDiagonalWeight n u k nu) < eps)) := by
  classical
  obtain ⟨cW, hcW_pos, hPart1⟩ :=
    eventually_commonClass_subprofile_le_regimeC hM hp1 hd hgam C_p
  set c₀ : ℝ := secondMomentExponent deltaMinus
  have hc₀_mem : c₀ ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_min (half_pos hd.1) (by norm_num),
      lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩
  have henv := (tendsto_middleRange_envelope_zero (M := M) hcW_pos hc₀_mem C_ov).eventually
    (gt_mem_nhds heps)
  have ha_ge : ∀ᶠ n : ℕ in atTop, M + 3 ≤ phaseNat n := by
    filter_upwards [eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
      tendsto_logOrder_atTop.eventually (eventually_ge_atTop ((M : ℝ) + 3))] with n hPh hL
    have : ((M : ℝ) + 3 : ℝ) ≤ (phaseNat n : ℝ) := le_trans hL hPh.1
    exact_mod_cast this
  filter_upwards [hPart1, eventually_partialDiagonalWeight_subprofile_le_exp_neg_half M,
    eventually_unmarkedDiagonalWeight_subprofile_le_exp_neg_half M, henv, ha_ge] with
    n h1 h2_mk h2_ch henv_n ha_n hdn hcap lamT hmean_red u k S hMass hp_ap hS
  have hu_bounds : ∀ j : Fin M, 1 ≤ u j ∧ phaseNat n - (M + 1) ≤ u j ∧ u j ≤ phaseNat n := by
    intro j; dsimp [u]; exact ⟨by omega, by omega, Nat.sub_le _ _⟩
  have hk_le_n : ∀ j : Fin M, k j ≤ n := by
    intro j
    calc k j = 1 * k j := (one_mul _).symm
      _ ≤ u j * k j := Nat.mul_le_mul_right (k j) (hu_bounds j).1
      _ ≤ selectedVertexMass u k :=
          Finset.single_le_sum (f := fun i ↦ u i * k i) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
      _ = n := hMass
  have hS_card : (S.card : ℝ) ≤ (n + 1 : ℝ) ^ M := by
    let emb : {nu // nu ∈ S} → (Fin M → Fin (n + 1)) :=
      fun nu j ↦ ⟨nu.1 j, Nat.lt_succ_of_le (le_trans ((hS nu.1 nu.2).1 j) (hk_le_n j))⟩
    have hinj : Function.Injective emb := by
      intro a b hab; apply Subtype.ext; funext j; exact congrArg Fin.val (congrFun hab j)
    have hcard_nat : S.card ≤ (n + 1) ^ M := by
      have := Fintype.card_le_of_injective emb hinj
      simpa [Fintype.card_coe, Fintype.card_pi, Fintype.card_fin] using this
    exact_mod_cast hcard_nat
  refine ⟨fun hMom_mk ↦ ?_, fun hMom_ch ↦ ?_⟩
  · have hpt : ∀ nu ∈ S,
        partialDiagonalWeight n u k nu ≤
          Real.exp (-cW * (n : ℝ) / (Real.log (n : ℝ)) ^ 3) +
            Real.exp (-(1 / 2 : ℝ) * (n : ℝ) ^ (1 - c₀)) := by
      intro nu hnuS
      obtain ⟨hsub, hm_lo, hrem_lo⟩ := hS nu hnuS
      rcases lt_or_ge (((2 : ℝ) ^ (M + 5))⁻¹ * (n : ℝ))
          ((n - selectedVertexMass u nu : ℕ) : ℝ) with hgt | hle
      · have hb := ((h1 hdn hcap lamT hmean_red k nu hMass hp_ap hsub hm_lo hgt).1 hMom_mk)
        exact le_trans (hb.1.trans hb.2) (le_add_of_nonneg_right (Real.exp_pos _).le)
      · have hb := h2_mk u k nu 0 le_rfl hu_bounds hMass hsub hle (by simpa using hMom_mk)
        have hrem_exp :
            Real.exp (-(((n - selectedVertexMass u nu : ℕ) : ℝ) / 2)) ≤
              Real.exp (-(1 / 2 : ℝ) * (n : ℝ) ^ (1 - c₀)) :=
          Real.exp_le_exp.mpr (by linarith)
        exact le_trans (hb.1.trans (hb.2.trans hrem_exp))
          (le_add_of_nonneg_left (Real.exp_pos _).le)
    have hsum :
        (∑ nu ∈ S, partialDiagonalWeight n u k nu) ≤
          ((n + 1 : ℝ) ^ M) *
            (Real.exp (-cW * (n : ℝ) / (Real.log (n : ℝ)) ^ 3) +
              Real.exp (-(1 / 2 : ℝ) * (n : ℝ) ^ (1 - c₀))) := by
      calc ∑ nu ∈ S, partialDiagonalWeight n u k nu
          ≤ ∑ _nu ∈ S, (Real.exp (-cW * (n : ℝ) / (Real.log (n : ℝ)) ^ 3) +
              Real.exp (-(1 / 2 : ℝ) * (n : ℝ) ^ (1 - c₀))) := Finset.sum_le_sum hpt
        _ = (S.card : ℝ) * _ := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((n + 1 : ℝ) ^ M) * _ := mul_le_mul_of_nonneg_right hS_card (by positivity)
    exact lt_of_le_of_lt
      ((mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le).trans_eq (by ring)) henv_n
  · have hpt : ∀ nu ∈ S,
        unmarkedDiagonalWeight n u k nu ≤
          Real.exp (-cW * (n : ℝ) / (Real.log (n : ℝ)) ^ 3) +
            Real.exp (-(1 / 2 : ℝ) * (n : ℝ) ^ (1 - c₀)) := by
      intro nu hnuS
      obtain ⟨hsub, hm_lo, hrem_lo⟩ := hS nu hnuS
      rcases lt_or_ge (((2 : ℝ) ^ (M + 5))⁻¹ * (n : ℝ))
          ((n - selectedVertexMass u nu : ℕ) : ℝ) with hgt | hle
      · have hb := ((h1 hdn hcap lamT hmean_red k nu hMass hp_ap hsub hm_lo hgt).2 hMom_ch)
        exact le_trans (hb.1.trans hb.2) (le_add_of_nonneg_right (Real.exp_pos _).le)
      · have hb := h2_ch u k nu 0 le_rfl hu_bounds hMass hsub hle (by simpa using hMom_ch)
        have hrem_exp :
            Real.exp (-(((n - selectedVertexMass u nu : ℕ) : ℝ) / 2)) ≤
              Real.exp (-(1 / 2 : ℝ) * (n : ℝ) ^ (1 - c₀)) :=
          Real.exp_le_exp.mpr (by linarith)
        exact le_trans (hb.1.trans (hb.2.trans hrem_exp))
          (le_add_of_nonneg_left (Real.exp_pos _).le)
    have hsum :
        (∑ nu ∈ S, unmarkedDiagonalWeight n u k nu) ≤
          ((n + 1 : ℝ) ^ M) *
            (Real.exp (-cW * (n : ℝ) / (Real.log (n : ℝ)) ^ 3) +
              Real.exp (-(1 / 2 : ℝ) * (n : ℝ) ^ (1 - c₀))) := by
      calc ∑ nu ∈ S, unmarkedDiagonalWeight n u k nu
          ≤ ∑ _nu ∈ S, (Real.exp (-cW * (n : ℝ) / (Real.log (n : ℝ)) ^ 3) +
              Real.exp (-(1 / 2 : ℝ) * (n : ℝ) ^ (1 - c₀))) := Finset.sum_le_sum hpt
        _ = (S.card : ℝ) * _ := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((n + 1 : ℝ) ^ M) * _ := mul_le_mul_of_nonneg_right hS_card (by positivity)
    exact lt_of_le_of_lt
      ((mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le).trans_eq (by ring)) henv_n

/-- **Complete v9 Main Theorem `(i)–(iv)` synthesis:**
from the finite-phase-cover `O_ε(exp(-2 n / (log n)^10))` bound, simultaneously establishes:
- `(i)` `Var(Δ(G_n)) ≤ n - 1`, `0 ≤ log E[exp(lam Y_n)] - lam E[Y_n] ≤ lam² (log₂ n)⁶ / (2 n)`,
  `P(|Y_n - E[Y_n]| ≥ u) ≤ 2 exp(-u² n / (2 (log₂ n)⁶))`,
  `E[|Δ(G_n) - E[Δ(G_n)]|^p] ≤ 2 ((p / e)(n - 1))^(p / 2)`, and
  `E[|Y_n - E[Y_n]|^p] ≤ 2 (p (log₂ n)⁶ / (e n))^(p / 2)` (`n ≥ 2`, `u ≥ 0`, `1 ≤ p < ∞`);
- `(ii)` for each `ε > 0` and `ϑ ∈ (0, 1)`, eventually
  `P(|Y_n - 1/4| > ε) ≤ 2 exp(-ϑ² ε² n / (2 (log₂ n)⁶))`;
- `(iii)` under every joint coupling with `G(n, 1/2)` marginals, almost surely
  `(log₂ n)³ / n * Δ(G_n) → 1 / 4` and `(log n)³ / n * Δ(G_n) → (log 2)³ / 4`;
- `(iv)` `E[|Y_n - 1/4|^p] → 0` (`1 ≤ p < ∞`), `E[Y_n] → 1 / 4`, and for all `T ≥ 0`,
  `log E[exp(t Y_n)] → t / 4` and `E[exp(t Y_n)] → exp(t / 4)` uniformly on `[-T, T]`. -/
theorem mainTheorem_v9_complete
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
        (randomGraphMeasure n).real {G : LabeledGraph n | u ≤ |Y n G - ∫ H, Y n H ∂randomGraphMeasure n|} ≤
          2 * Real.exp (-u ^ 2 * (n : ℝ) / (2 * (Real.logb 2 (n : ℝ)) ^ 6))) ∧
      (∀ {n : ℕ}, 2 ≤ n → ∀ {p : ℝ}, 1 ≤ p →
        (∫ G : LabeledGraph n, |D n G - ∫ H, D n H ∂randomGraphMeasure n| ^ p
          ∂randomGraphMeasure n) ≤
          2 * (p / Real.exp 1 * ((n - 1 : ℕ) : ℝ)) ^ (p / 2) ∧
        (∫ G : LabeledGraph n, |Y n G - ∫ H, Y n H ∂randomGraphMeasure n| ^ p
          ∂randomGraphMeasure n) ≤
          2 * (p * (Real.logb 2 (n : ℝ)) ^ 6 / (Real.exp 1 * (n : ℝ))) ^ (p / 2))) ∧
    (∀ {eps theta : ℝ}, 0 < eps → theta ∈ Ioo 0 1 →
      ∀ᶠ n : ℕ in atTop,
        (randomGraphMeasure n).real {G : LabeledGraph n | eps < |Y n G - 1 / 4|} ≤
          2 * Real.exp (-theta ^ 2 * eps ^ 2 * (n : ℝ) / (2 * (Real.logb 2 (n : ℝ)) ^ 6))) ∧
    (∀ {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
      (G : ∀ n : ℕ, Ω → LabeledGraph n),
      (∀ n : ℕ, Measure.map (G n) ℙ = randomGraphMeasure n) →
      ∀ᵐ ω ∂ℙ,
        Tendsto (fun n : ℕ ↦ (Real.log n) ^ 3 / (n : ℝ) * D n (G n ω))
          atTop (nhds sharpGapConstant) ∧
        Tendsto (fun n : ℕ ↦ Y n (G n ω)) atTop (nhds (1 / 4 : ℝ))) ∧
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
  obtain ⟨hvar, hmean_tail, hsubg, hae, hlp, hexp, -⟩ :=
    mainTheorem_subgaussian_tail_ae_lp_expectation_and_mgf htail
  refine ⟨⟨hvar, fun {_} hn lam ↦ cgf_normalizedGap_bounds hn lam, hmean_tail,
    fun {_} hn {_} hp ↦ ⟨centralMoment_chromaticSubCochromatic_le hn hp,
      centralMoment_normalizedGap_le hn hp⟩⟩,
    hsubg, hae, ⟨hlp, hexp, fun {_} hT ↦ ?_⟩⟩
  obtain ⟨hcgf_u, hmgf_u, -, -⟩ := tendstoUniformlyOn_cgf_and_mgf_normalizedGap hexp hT
  exact ⟨hcgf_u, hmgf_u⟩

end

end Erdos625HP
