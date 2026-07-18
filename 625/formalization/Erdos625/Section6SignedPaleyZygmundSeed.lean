import Erdos625.Section6SignedSecondMomentIdentity
import Erdos625.Section10CoColorablePaleyZygmundSeed
import Mathlib.Tactic

/-!
# Section VI: signed-profile Paley--Zygmund seed

This module connects the literal finite signed-profile count to the generic
Paley--Zygmund cocolourability adapter.  Its hypotheses expose, rather than
hide, the only analytic input: an upper bound on the exact normalized
fixed-margin overlap-table sum.
-/

namespace Erdos625

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory

noncomputable section

/-- The `lintegral` of the finite signed-profile count is its literal
singleton-mass first moment. -/
theorem lintegral_signedProfileCount_eq_signedProfileExpectation
    {b : ℕ} (n : ℕ) (k : ColoringProfile b) :
    ∫⁻ G, (signedProfileCount G k : ENNReal) ∂(randomGraphMeasure n) =
      signedProfileExpectation n k := by
  rw [MeasureTheory.lintegral_fintype]
  rfl

/-- The `lintegral` of the square of the finite signed-profile count is its
literal singleton-mass second moment. -/
theorem lintegral_signedProfileCount_sq_eq_signedProfileSecondMoment
    {b : ℕ} (n : ℕ) (k : ColoringProfile b) :
    ∫⁻ G, (signedProfileCount G k : ENNReal) ^ 2 ∂(randomGraphMeasure n) =
      signedProfileSecondMoment n k := by
  rw [MeasureTheory.lintegral_fintype]
  rfl

/-- A feasible ordered profile and an explicit upper bound on its exact
normalized signed overlap-table sum give the real seed probability needed by
the later amplification argument.  The proof derives all denominator
nonvanishing and finiteness facts from the feasible profile, the finite
sample space, and the displayed table-sum bound. -/
theorem signedProfile_real_seed_of_tableSum_bound
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (Λ : ℝ)
    (hTable : signedProfileSecondMomentTableSumENNReal row₀ ≤
      ENNReal.ofReal (Real.exp Λ)) :
    Real.exp (-Λ) ≤
      (randomGraphMeasure n).real
        {G | CoColorable G (ColoringProfile.partCount k)} := by
  let Z : LabeledGraph n → ENNReal := fun G => (signedProfileCount G k : ENNReal)
  let D : ENNReal := signedProfileExpectation n k ^ 2
  let M : ENNReal := signedProfileSecondMoment n k
  let B : ENNReal := ENNReal.ofReal (Real.exp Λ)
  have hZ : Measurable Z := measurable_of_finite _
  have hD0 : D ≠ 0 := by
    simpa only [D] using
      signedProfileExpectation_sq_ne_zero_of_orderedProfilePartition row₀
  have hDtop : D ≠ ∞ := by
    simpa only [D] using signedProfileExpectation_sq_ne_top n k
  have hB0 : B ≠ 0 := by
    apply ne_of_gt
    simpa only [B, ENNReal.ofReal_pos] using Real.exp_pos Λ
  have hBtop : B ≠ ∞ := by
    simpa only [B] using ENNReal.ofReal_ne_top
      (r := Real.exp Λ)
  have hnormalized : M / D =
      signedProfileSecondMomentTableSumENNReal row₀ := by
    simpa only [M, D] using
      normalizedSignedProfileSecondMoment_eq_tableSum row₀
  have hdiv : M / D ≤ B := by
    rw [hnormalized]
    simpa only [B] using hTable
  have hMle : M ≤ B * D :=
    (ENNReal.div_le_iff hD0 hDtop).mp hdiv
  have hMtop : M ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hBtop hDtop) hMle
  have hM0 : M ≠ 0 := by
    intro hMzero
    have hMzero' : signedProfileSecondMoment n k = 0 := by
      simpa only [M] using hMzero
    have hCS := lintegral_sq_le_measure_support_mul_lintegral_sq
      (mu := randomGraphMeasure n) (Z := Z) hZ
    rw [lintegral_signedProfileCount_eq_signedProfileExpectation,
      lintegral_signedProfileCount_sq_eq_signedProfileSecondMoment] at hCS
    have hDzero : D = 0 := by
      apply bot_unique
      change signedProfileExpectation n k ^ 2 ≤ 0
      calc
        signedProfileExpectation n k ^ 2 ≤
            (randomGraphMeasure n) (Function.support Z) *
              signedProfileSecondMoment n k := hCS
        _ = 0 := by rw [hMzero', mul_zero]
    exact hD0 (by simpa only [D] using hDzero)
  have hratioENN : B⁻¹ ≤ D / M := by
    rw [← ENNReal.inv_div (Or.inl hDtop) (Or.inl hD0)]
    exact ENNReal.inv_le_inv.mpr hdiv
  have hratioTop : D / M ≠ ∞ := ENNReal.div_ne_top hDtop hM0
  have hratioReal : Real.exp (-Λ) ≤ (D / M).toReal := by
    have htoReal := ENNReal.toReal_mono hratioTop hratioENN
    calc
      Real.exp (-Λ) = (B⁻¹).toReal := by
        rw [ENNReal.toReal_inv]
        simp only [B, ENNReal.toReal_ofReal (Real.exp_nonneg Λ)]
        exact Real.exp_neg Λ
      _ ≤ (D / M).toReal := htoReal
  have hPZ := coColorable_real_seed_of_count n
    (ColoringProfile.partCount k) Z hZ (fun G hG => by
      apply signedProfileCount_pos_implies_coColorable
      exact Nat.cast_pos.mp (by simpa only [Z] using hG))
  have hPZ' : (D / M).toReal ≤
      (randomGraphMeasure n).real
        {G | CoColorable G (ColoringProfile.partCount k)} := by
    simpa only [Z, D, M,
      lintegral_signedProfileCount_eq_signedProfileExpectation,
      lintegral_signedProfileCount_sq_eq_signedProfileSecondMoment] using hPZ
  exact hratioReal.trans hPZ'

#print axioms lintegral_signedProfileCount_eq_signedProfileExpectation
#print axioms lintegral_signedProfileCount_sq_eq_signedProfileSecondMoment
#print axioms signedProfile_real_seed_of_tableSum_bound

end

end Erdos625
