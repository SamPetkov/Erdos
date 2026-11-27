import Erdos625.Phase
import Erdos625.Section11AsymptoticAssembly
import Erdos625HP.PhaseConstants

/-!
# Conditional four-threshold assembly for Section 9 (`sec:final-assembly`)

Given arbitrary deterministic sequences `kZetaMinus, kCo, kChiMinus, kCh : ℕ → ℕ`
and allowances `a, b : ℕ → ℝ` assumed to satisfy:
* **(A)** the normalized inner gap `(log n)³ / n · (kChiMinus n - kCo n - a n)`
  is eventually at least `lowerPhaseCoeff (phaseDelta n) - eps n`, and the
  normalized outer span `(log n)³ / n · (kCh n + b n - kZetaMinus n)` is
  eventually at most `upperPhaseCoeff (phaseDelta n) + eps n` for `eps n → 0`;
* **(B)** `P(χ(G_n) > kChiMinus n) → 1` and `P(ζ(G_n) > kZetaMinus n) → 1`;
* **(C)** `P(ζ(G_n) ≤ kCo n + a n) → 1` and `P(χ(G_n) ≤ kCh n + b n) → 1`;

this module proves the conditional Section 9 implication from `(A)`, `(B)`, `(C)`
to both the phase-resolved two-sided gap event and the uniform `[0.063, 0.104]`
gap event. See `Erdos625HP.ConcreteTwoSidedInstantiation` for the concrete
manuscript sequences discharging `(A)`, `(B)`, and the Section 8 amplification
step unconditionally (leaving as hypotheses the two `G(n, 1/2)` rare-seed
probability lower bounds obtained from Proposition 7.7 via Paley–Zygmund), and `Erdos625HP.UnconditionalOneSixteenth` for the
hypothesis-free `1/16 = 0.0625` and phase-resolved `A₄(δ_n)` lower-bound theorems.
-/

namespace Erdos625HP

open Erdos625 Filter MeasureTheory

noncomputable section

set_option autoImplicit false

/-- The explicit two-sided gap event `c · n / (log n)³ ≤ χ(G) - ζ(G) ≤ C · n / (log n)³`. -/
def twoSidedGapEvent (c C : ℝ) (n : ℕ) : Set (LabeledGraph n) :=
  {G | c * ((n : ℝ) / (Real.log n) ^ 3) ≤
        (chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ) ∧
       (chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ) ≤
        C * ((n : ℝ) / (Real.log n) ^ 3)}

/-- Intersection of four high-probability events still has probability tending
to `1`. -/
theorem tendsto_measure_inter_four_one {n_space : ℕ → Type*}
    [∀ n, MeasurableSpace (n_space n)]
    (μ : ∀ n, Measure (n_space n)) [∀ n, IsProbabilityMeasure (μ n)]
    (A B C D : ∀ n, Set (n_space n))
    (hA : ∀ n, MeasurableSet (A n))
    (hB : ∀ n, MeasurableSet (B n))
    (hC : ∀ n, MeasurableSet (C n))
    (hD : ∀ n, MeasurableSet (D n))
    (hA1 : Tendsto (fun n ↦ μ n (A n)) atTop (nhds 1))
    (hB1 : Tendsto (fun n ↦ μ n (B n)) atTop (nhds 1))
    (hC1 : Tendsto (fun n ↦ μ n (C n)) atTop (nhds 1))
    (hD1 : Tendsto (fun n ↦ μ n (D n)) atTop (nhds 1)) :
    Tendsto (fun n ↦ μ n ((A n ∩ B n) ∩ (C n ∩ D n))) atTop (nhds 1) := by
  have hAB := tendsto_measure_inter_one μ A B hA hB hA1 hB1
  have hCD := tendsto_measure_inter_one μ C D hC hD hC1 hD1
  exact tendsto_measure_inter_one μ (fun n ↦ A n ∩ B n) (fun n ↦ C n ∩ D n)
    (fun n ↦ (hA n).inter (hB n)) (fun n ↦ (hC n).inter (hD n)) hAB hCD

/-- Pointwise sandwich on the intersection of the four threshold events. -/
theorem mem_twoSidedGapEvent_of_four_thresholds {n kZetaMinus kCo kChiMinus kCh : ℕ}
    {a b eps : ℝ}
    (hLowerLoc :
      (lowerPhaseCoeff (phaseDelta n) - eps) * ((n : ℝ) / (Real.log n) ^ 3) ≤
        (kChiMinus : ℝ) - (kCo : ℝ) - a)
    (hUpperLoc :
      (kCh : ℝ) + b - (kZetaMinus : ℝ) ≤
        (upperPhaseCoeff (phaseDelta n) + eps) * ((n : ℝ) / (Real.log n) ^ 3))
    {G : LabeledGraph n}
    (hChiLow : kChiMinus < chromaticNumberNat G)
    (hZetaUp : (cochromaticNumber G : ℝ) ≤ (kCo : ℝ) + a)
    (hZetaLow : kZetaMinus < cochromaticNumber G)
    (hChiUp : (chromaticNumberNat G : ℝ) ≤ (kCh : ℝ) + b) :
    G ∈ twoSidedGapEvent (lowerPhaseCoeff (phaseDelta n) - eps)
      (upperPhaseCoeff (phaseDelta n) + eps) n := by
  have hChiLowR : (kChiMinus : ℝ) < (chromaticNumberNat G : ℝ) := by
    exact_mod_cast hChiLow
  have hZetaLowR : (kZetaMinus : ℝ) < (cochromaticNumber G : ℝ) := by
    exact_mod_cast hZetaLow
  constructor <;> linarith

/-- **Conditional two-sided assembly** (not a proof of the Main Theorem, whose
inputs `(A)`, `(B)`, `(C)` are hypotheses here): given `(A)`, `(B)`,
`(C)` with error sequence `eps n → 0`, both the phase-resolved two-sided bound
and the uniform `[0.063, 0.104]` two-sided bound hold with probability tending
to `1` along all `n`. -/
theorem twoSided_phase_and_uniform_gap_tendsto_one
    (kZetaMinus kCo kChiMinus kCh : ℕ → ℕ)
    (a b eps : ℕ → ℝ)
    (heps_zero : Tendsto eps atTop (nhds 0))
    (hLoc : ∀ᶠ n in atTop,
      (lowerPhaseCoeff (phaseDelta n) - eps n) * ((n : ℝ) / (Real.log n) ^ 3) ≤
        (kChiMinus n : ℝ) - (kCo n : ℝ) - a n ∧
      (kCh n : ℝ) + b n - (kZetaMinus n : ℝ) ≤
        (upperPhaseCoeff (phaseDelta n) + eps n) * ((n : ℝ) / (Real.log n) ^ 3))
    (hChiLow : Tendsto (fun n ↦ randomGraphMeasure n
        {G | kChiMinus n < chromaticNumberNat G}) atTop (nhds 1))
    (hZetaUp : Tendsto (fun n ↦ randomGraphMeasure n
        {G | (cochromaticNumber G : ℝ) ≤ (kCo n : ℝ) + a n}) atTop (nhds 1))
    (hZetaLow : Tendsto (fun n ↦ randomGraphMeasure n
        {G | kZetaMinus n < cochromaticNumber G}) atTop (nhds 1))
    (hChiUp : Tendsto (fun n ↦ randomGraphMeasure n
        {G | (chromaticNumberNat G : ℝ) ≤ (kCh n : ℝ) + b n}) atTop (nhds 1)) :
    Tendsto (fun n ↦ randomGraphMeasure n
        (twoSidedGapEvent (lowerPhaseCoeff (phaseDelta n) - eps n)
          (upperPhaseCoeff (phaseDelta n) + eps n) n)) atTop (nhds 1) ∧
    Tendsto (fun n ↦ randomGraphMeasure n
        (twoSidedGapEvent (63 / 1000) (104 / 1000) n)) atTop (nhds 1) := by
  have hFour := tendsto_measure_inter_four_one randomGraphMeasure
    (fun n ↦ {G | kChiMinus n < chromaticNumberNat G})
    (fun n ↦ {G | (cochromaticNumber G : ℝ) ≤ (kCo n : ℝ) + a n})
    (fun n ↦ {G | kZetaMinus n < cochromaticNumber G})
    (fun n ↦ {G | (chromaticNumberNat G : ℝ) ≤ (kCh n : ℝ) + b n})
    (fun n ↦ (Set.toFinite _).measurableSet)
    (fun n ↦ (Set.toFinite _).measurableSet)
    (fun n ↦ (Set.toFinite _).measurableSet)
    (fun n ↦ (Set.toFinite _).measurableSet)
    hChiLow hZetaUp hZetaLow hChiUp
  have hPhase :
      Tendsto (fun n ↦ randomGraphMeasure n
        (twoSidedGapEvent (lowerPhaseCoeff (phaseDelta n) - eps n)
          (upperPhaseCoeff (phaseDelta n) + eps n) n)) atTop (nhds 1) := by
    apply tendsto_measure_one_of_eventually_subset randomGraphMeasure _ _ hFour
    filter_upwards [hLoc] with n hLn G ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    exact mem_twoSidedGapEvent_of_four_thresholds hLn.1 hLn.2 h1 h2 h3 h4
  refine ⟨hPhase, ?_⟩
  have hMarginLo : ∀ n, (6302 / 100000 : ℝ) < lowerPhaseCoeff (phaseDelta n) := by
    intro n
    have hph : phaseDelta n ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨phaseDelta_nonneg n, (phaseDelta_lt_one n).le⟩
    have hA : (5247 / 10000 : ℝ) < FiveSizeEntropyGap.phaseGain5 (phaseDelta n) :=
      lt_trans log_169_div_100_gt
        (FiveSizePhaseGainCertificate.log_169_div_100_lt_phaseGain5 (phaseDelta n) hph)
    have hqlo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hqsq : (0.6931471803 : ℝ) ^ 2 < (Real.log 2) ^ 2 := by nlinarith
    unfold lowerPhaseCoeff
    nlinarith
  have hMarginHi : ∀ n, upperPhaseCoeff (phaseDelta n) < (1035 / 10000 : ℝ) := by
    intro n
    have hph : phaseDelta n ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨phaseDelta_nonneg n, (phaseDelta_lt_one n).le⟩
    have hA : (5247 / 10000 : ℝ) < FiveSizeEntropyGap.phaseGain5 (phaseDelta n) :=
      lt_trans log_169_div_100_gt
        (FiveSizePhaseGainCertificate.log_169_div_100_lt_phaseGain5 (phaseDelta n) hph)
    have hqhi : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
    have hqpos : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hqsq : (Real.log 2) ^ 2 < (0.6931471808 : ℝ) ^ 2 := by nlinarith
    have hspan : 2 * Real.log 2 - FiveSizeEntropyGap.phaseGain5 (phaseDelta n) <
        2 * 0.6931471808 - 5247 / 10000 := by linarith
    unfold upperPhaseCoeff
    by_cases hnonneg : 0 ≤ 2 * Real.log 2 - FiveSizeEntropyGap.phaseGain5 (phaseDelta n)
    · have hmul :
          (Real.log 2) ^ 2 / 4 * (2 * Real.log 2 - FiveSizeEntropyGap.phaseGain5 (phaseDelta n)) ≤
            (0.6931471808 : ℝ) ^ 2 / 4 * (2 * 0.6931471808 - 5247 / 10000) :=
        mul_le_mul (by linarith) hspan.le hnonneg (by norm_num)
      linarith
    · have hneg_span : 2 * Real.log 2 - FiveSizeEntropyGap.phaseGain5 (phaseDelta n) < 0 :=
        not_le.mp hnonneg
      have hneg : (Real.log 2) ^ 2 / 4 *
          (2 * Real.log 2 - FiveSizeEntropyGap.phaseGain5 (phaseDelta n)) < 0 :=
        mul_neg_of_pos_of_neg (by positivity) hneg_span
      linarith
  have heps_small : ∀ᶠ n in atTop, eps n < 2 / 100000 ∧ -(5 / 10000 : ℝ) < eps n := by
    have h1 := (tendsto_order.1 heps_zero).2 (2 / 100000) (by norm_num)
    have h2 := (tendsto_order.1 heps_zero).1 (-(5 / 10000 : ℝ)) (by norm_num)
    exact h1.and h2
  apply tendsto_measure_one_of_eventually_subset randomGraphMeasure _ _ hPhase
  filter_upwards [eventually_ge_atTop 2, heps_small] with n hn ⟨heps_hi, heps_lo⟩ G ⟨hG_lo, hG_hi⟩
  have hn_pos : 0 < (n : ℝ) := by positivity
  have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hscale_nonneg : 0 ≤ (n : ℝ) / (Real.log n) ^ 3 := by positivity
  have hlo_coef : (63 / 1000 : ℝ) ≤ lowerPhaseCoeff (phaseDelta n) - eps n := by
    have := hMarginLo n
    linarith
  have hhi_coef : upperPhaseCoeff (phaseDelta n) + eps n ≤ (104 / 1000 : ℝ) := by
    have := hMarginHi n
    linarith
  constructor
  · exact le_trans (mul_le_mul_of_nonneg_right hlo_coef hscale_nonneg) hG_lo
  · exact le_trans hG_hi (mul_le_mul_of_nonneg_right hhi_coef hscale_nonneg)

end

end Erdos625HP
