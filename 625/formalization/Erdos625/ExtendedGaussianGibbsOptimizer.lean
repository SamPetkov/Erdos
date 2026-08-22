import Erdos625.SPlusPrimalRepresentation
import Erdos625.ExtendedGaussianTilt
import Mathlib.Tactic

/-!
# The extended-Gaussian Gibbs profile attains the limiting entropy dual

The existing limiting `S₊` entropy development proves that every admissible
profile is bounded above by the extended-Gaussian dual test value.  This module
supplies the reverse inequality at the selected mean-matching tilt.

The normalized extended-Gaussian weights are inserted directly into the
manuscript primal.  Their truncated mass and moment converge to one and the
selected target.  At every finite truncation, the entropy-plus-score sum is
exactly

`log Z * truncated mass - tilt * truncated moment`.

Consequently the normalized Gibbs profile realizes `log Z - tilt * target`,
and the limiting entropy supremum equals its selected dual value on the
interior manuscript target interval.

No finite-cutoff convergence, root statement, first moment, chromatic tail,
partial diagonal, second moment, or final Erdős statement is proved here.
-/

namespace Erdos625

open Filter Set
open scoped Topology BigOperators

noncomputable section

set_option autoImplicit false

/-- Normalized mass of the exceptional deficit `-1` in the limiting Gibbs
profile. -/
noncomputable def extendedGaussianNormalizedExceptional
    (tilt : ℝ) : ℝ :=
  extendedGaussianExceptionalAtom q tilt /
    extendedGaussianPartition q tilt

/-- Normalized mass of a natural deficit in the limiting Gibbs profile. -/
noncomputable def extendedGaussianNormalizedNatural
    (tilt : ℝ) (d : ℕ) : ℝ :=
  extendedGaussianNaturalTerm q tilt d /
    extendedGaussianPartition q tilt

/-- Truncated first moment of the normalized limiting Gibbs profile, written
with one quotient outside the natural-coordinate sum. -/
noncomputable def extendedGaussianReferenceMomentTruncation
    (tilt : ℝ) (N : ℕ) : ℝ :=
  -extendedGaussianExceptionalAtom q tilt /
      extendedGaussianPartition q tilt +
    (∑ d ∈ Finset.range N,
      (d : ℝ) * extendedGaussianNaturalTerm q tilt d) /
        extendedGaussianPartition q tilt

/-- The normalized limiting Gibbs masses are strictly positive. -/
theorem extendedGaussianNormalizedExceptional_pos (tilt : ℝ) :
    0 < extendedGaussianNormalizedExceptional tilt := by
  exact div_pos (extendedGaussianExceptionalAtom_pos q tilt)
    (extendedGaussianPartition_pos q_pos)

/-- Every normalized natural-coordinate Gibbs mass is strictly positive. -/
theorem extendedGaussianNormalizedNatural_pos (tilt : ℝ) (d : ℕ) :
    0 < extendedGaussianNormalizedNatural tilt d := by
  exact div_pos (extendedGaussianNaturalTerm_pos q tilt d)
    (extendedGaussianPartition_pos q_pos)

/-- The manuscript mass truncation of the normalized Gibbs profile is exactly
the previously defined normalized reference-mass truncation. -/
theorem extendedGaussianMassTruncation_normalized_eq_reference
    (tilt : ℝ) (N : ℕ) :
    extendedGaussianMassTruncation
        (extendedGaussianNormalizedExceptional tilt)
        (extendedGaussianNormalizedNatural tilt) N =
      extendedGaussianReferenceMassTruncation q tilt N := by
  rfl

/-- The manuscript moment truncation of the normalized Gibbs profile equals
the reference first-moment truncation. -/
theorem extendedGaussianMomentTruncation_normalized_eq_reference
    (tilt : ℝ) (N : ℕ) :
    extendedGaussianMomentTruncation
        (extendedGaussianNormalizedExceptional tilt)
        (extendedGaussianNormalizedNatural tilt) N =
      extendedGaussianReferenceMomentTruncation tilt N := by
  unfold extendedGaussianMomentTruncation
    extendedGaussianNormalizedExceptional
    extendedGaussianNormalizedNatural
    extendedGaussianReferenceMomentTruncation
  rw [Finset.sum_div]
  apply congrArg (fun x : ℝ ↦
    -extendedGaussianExceptionalAtom q tilt /
        extendedGaussianPartition q tilt + x)
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- The normalized reference first moment converges to the extended-Gaussian
mean. -/
theorem tendsto_extendedGaussianReferenceMomentTruncation
    (tilt : ℝ) :
    Tendsto (extendedGaussianReferenceMomentTruncation tilt)
      atTop (𝓝 (extendedGaussianMean q tilt)) := by
  have hsum : Tendsto
      (fun N : ℕ ↦
        ∑ d ∈ Finset.range N,
          (d : ℝ) * extendedGaussianNaturalTerm q tilt d)
      atTop
      (𝓝 (∑' d : ℕ,
        (d : ℝ) * extendedGaussianNaturalTerm q tilt d)) :=
    (summable_extendedGaussianFirstMoment q_pos).hasSum.tendsto_sum_nat
  have hdiv := hsum.div_const (extendedGaussianPartition q tilt)
  have hadd :=
    tendsto_const_nhds.add hdiv
  refine hadd.congr' ?_
  filter_upwards with N
  constructor
  · rfl
  · unfold extendedGaussianReferenceMomentTruncation
      extendedGaussianMean extendedGaussianFirstNumerator
    rfl

/-- The normalized Gibbs moment truncations converge to the limiting mean. -/
theorem tendsto_extendedGaussianMomentTruncation_normalized
    (tilt : ℝ) :
    Tendsto
      (extendedGaussianMomentTruncation
        (extendedGaussianNormalizedExceptional tilt)
        (extendedGaussianNormalizedNatural tilt))
      atTop (𝓝 (extendedGaussianMean q tilt)) := by
  apply (tendsto_extendedGaussianReferenceMomentTruncation tilt).congr'
  filter_upwards with N
  exact
    (extendedGaussianMomentTruncation_normalized_eq_reference tilt N).symm

/-- Exact entropy ledger for every finite normalized Gibbs truncation. -/
theorem extendedGaussianEntropyTruncation_normalized_eq
    (tilt : ℝ) (N : ℕ) :
    extendedGaussianEntropyTruncation q
        (extendedGaussianNormalizedExceptional tilt)
        (extendedGaussianNormalizedNatural tilt) N =
      Real.log (extendedGaussianPartition q tilt) *
          extendedGaussianMassTruncation
            (extendedGaussianNormalizedExceptional tilt)
            (extendedGaussianNormalizedNatural tilt) N -
        tilt * extendedGaussianMomentTruncation
          (extendedGaussianNormalizedExceptional tilt)
          (extendedGaussianNormalizedNatural tilt) N := by
  unfold extendedGaussianEntropyTruncation
  rw [show Real.log (extendedGaussianNormalizedExceptional tilt) =
      -tilt + extendedGaussianExceptionalScore q -
        Real.log (extendedGaussianPartition q tilt) by
    simpa [extendedGaussianNormalizedExceptional] using
      log_normalized_extendedGaussianExceptionalAtom tilt]
  simp_rw [show ∀ d : ℕ,
      Real.log (extendedGaussianNormalizedNatural tilt d) =
        tilt * (d : ℝ) + extendedGaussianNaturalScore q d -
          Real.log (extendedGaussianPartition q tilt) by
    intro d
    simpa [extendedGaussianNormalizedNatural] using
      log_normalized_extendedGaussianNaturalTerm tilt d]
  unfold extendedGaussianMassTruncation
    extendedGaussianMomentTruncation
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum]
  ring

/-- The entropy truncations of the normalized Gibbs profile converge to its
selected dual value. -/
theorem tendsto_extendedGaussianEntropyTruncation_normalized
    (tilt : ℝ) :
    Tendsto
      (extendedGaussianEntropyTruncation q
        (extendedGaussianNormalizedExceptional tilt)
        (extendedGaussianNormalizedNatural tilt))
      atTop
      (𝓝 (Real.log (extendedGaussianPartition q tilt) -
        tilt * extendedGaussianMean q tilt)) := by
  have hMass : Tendsto
      (extendedGaussianMassTruncation
        (extendedGaussianNormalizedExceptional tilt)
        (extendedGaussianNormalizedNatural tilt))
      atTop (𝓝 1) := by
    apply (tendsto_extendedGaussianReferenceMassTruncation
      (a := q) (tilt := tilt) q_pos).congr'
    filter_upwards with N
    exact
      (extendedGaussianMassTruncation_normalized_eq_reference tilt N).symm
  have hMoment :=
    tendsto_extendedGaussianMomentTruncation_normalized tilt
  have hLimit :=
    (tendsto_const_nhds.mul hMass).sub
      (tendsto_const_nhds.mul hMoment)
  have hLimit' : Tendsto
      (fun N : ℕ ↦
        Real.log (extendedGaussianPartition q tilt) *
            extendedGaussianMassTruncation
              (extendedGaussianNormalizedExceptional tilt)
              (extendedGaussianNormalizedNatural tilt) N -
          tilt * extendedGaussianMomentTruncation
            (extendedGaussianNormalizedExceptional tilt)
            (extendedGaussianNormalizedNatural tilt) N)
      atTop
      (𝓝 (Real.log (extendedGaussianPartition q tilt) -
        tilt * extendedGaussianMean q tilt)) := by
    simpa only [mul_one] using hLimit
  exact hLimit'.congr'
    (Filter.Eventually.of_forall fun N ↦
      (extendedGaussianEntropyTruncation_normalized_eq tilt N).symm)

/-- The normalized selected Gibbs profile is directly admissible in the
manuscript `S₊` primal. -/
theorem selectedExtendedGaussian_sPlusPrimalProfile
    {target : ℝ} (htarget : -1 < target) :
    SPlusPrimalProfile target
      (extendedGaussianDualTestValue target
        (extendedGaussianTilt q target))
      (extendedGaussianNormalizedExceptional
        (extendedGaussianTilt q target))
      (extendedGaussianNormalizedNatural
        (extendedGaussianTilt q target)) := by
  let tilt : ℝ := extendedGaussianTilt q target
  have hMean : extendedGaussianMean q tilt = target := by
    dsimp only [tilt]
    exact extendedGaussianMean_extendedGaussianTilt q_pos htarget
  refine
    { exceptional_nonneg :=
        (extendedGaussianNormalizedExceptional_pos tilt).le
      natural_nonneg := fun d ↦
        (extendedGaussianNormalizedNatural_pos tilt d).le
      mass_limit := ?_
      moment_limit := ?_
      entropy_limit := ?_ }
  · exact (tendsto_extendedGaussianReferenceMassTruncation
      (a := q) (tilt := tilt) q_pos).congr'
      (Filter.Eventually.of_forall fun N ↦
        (extendedGaussianMassTruncation_normalized_eq_reference tilt N).symm)
  · simpa only [hMean] using
      tendsto_extendedGaussianMomentTruncation_normalized tilt
  · have hEntropy :=
      tendsto_extendedGaussianEntropyTruncation_normalized tilt
    unfold extendedGaussianDualTestValue
    simpa only [hMean] using hEntropy

/-- The selected dual value is realized by an all-tilts entropy witness. -/
theorem selectedExtendedGaussianDualValue_mem_candidateSet
    {target : ℝ} (htarget : -1 < target) :
    extendedGaussianDualTestValue target
        (extendedGaussianTilt q target) ∈
      extendedGaussianEntropyCandidateSet target := by
  refine ⟨extendedGaussianNormalizedExceptional
      (extendedGaussianTilt q target),
    extendedGaussianNormalizedNatural
      (extendedGaussianTilt q target), ?_⟩
  exact
    extendedGaussianEntropyWitnessAllTilts_iff_sPlusPrimalProfile.mpr
      (selectedExtendedGaussian_sPlusPrimalProfile htarget)

/-- Every entropy candidate is bounded above by the selected dual value. -/
theorem entropyCandidate_le_selectedExtendedGaussianDualValue
    {target value : ℝ}
    (htarget : -1 < target)
    (hvalue : value ∈ extendedGaussianEntropyCandidateSet target) :
    value ≤ extendedGaussianDualTestValue target
      (extendedGaussianTilt q target) := by
  rcases hvalue with ⟨exceptional, p, hw⟩
  exact extendedGaussianEntropy_le_dual_of_truncations_q
    hw.exceptional_nonneg hw.natural_nonneg
    (fun _ _ N ↦ hw.finite_dual_bound
      (extendedGaussianTilt q target) N)
    hw.mass_limit hw.moment_limit hw.entropy_limit

/-- On the manuscript interior target interval, the unrestricted limiting
entropy supremum is exactly the selected extended-Gaussian dual value. -/
theorem extendedGaussianEntropyValue_eq_selectedDual
    {target : ℝ} (htarget : target ∈ Ioo (2 : ℝ) 5) :
    extendedGaussianEntropyValue target =
      extendedGaussianDualTestValue target
        (extendedGaussianTilt q target) := by
  have htargetLower : -1 < target := by linarith [htarget.1]
  have hUpper : extendedGaussianEntropyValue target ≤
      extendedGaussianDualTestValue target
        (extendedGaussianTilt q target) :=
    extendedGaussianEntropyValue_le_dual_interior htarget
  have hBdd : BddAbove (extendedGaussianEntropyCandidateSet target) := by
    refine ⟨extendedGaussianDualTestValue target
      (extendedGaussianTilt q target), ?_⟩
    intro value hvalue
    exact entropyCandidate_le_selectedExtendedGaussianDualValue
      htargetLower hvalue
  have hLower :
      extendedGaussianDualTestValue target
          (extendedGaussianTilt q target) ≤
        extendedGaussianEntropyValue target := by
    unfold extendedGaussianEntropyValue
    exact le_csSup hBdd
      (selectedExtendedGaussianDualValue_mem_candidateSet htargetLower)
  exact le_antisymm hUpper hLower

/-- Expanded logarithmic form of the selected-dual identity. -/
theorem extendedGaussianEntropyValue_eq_log_partition_sub_tilt_mul
    {target : ℝ} (htarget : target ∈ Ioo (2 : ℝ) 5) :
    extendedGaussianEntropyValue target =
      Real.log
          (extendedGaussianPartition q
            (extendedGaussianTilt q target)) -
        extendedGaussianTilt q target * target := by
  simpa only [extendedGaussianDualTestValue] using
    extendedGaussianEntropyValue_eq_selectedDual htarget

#print axioms extendedGaussianMassTruncation_normalized_eq_reference
#print axioms extendedGaussianMomentTruncation_normalized_eq_reference
#print axioms tendsto_extendedGaussianReferenceMomentTruncation
#print axioms tendsto_extendedGaussianMomentTruncation_normalized
#print axioms extendedGaussianEntropyTruncation_normalized_eq
#print axioms tendsto_extendedGaussianEntropyTruncation_normalized
#print axioms selectedExtendedGaussian_sPlusPrimalProfile
#print axioms selectedExtendedGaussianDualValue_mem_candidateSet
#print axioms entropyCandidate_le_selectedExtendedGaussianDualValue
#print axioms extendedGaussianEntropyValue_eq_selectedDual
#print axioms extendedGaussianEntropyValue_eq_log_partition_sub_tilt_mul

end

end Erdos625