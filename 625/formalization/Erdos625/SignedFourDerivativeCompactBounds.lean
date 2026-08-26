import Erdos625.SignedFourDerivativeMainReduction
import Erdos625.SignedFourMidpointTargetCorridor
import Erdos625.FourDeficitScoreConvergence
import Erdos625.ProfileOptimizerUniformS4
import Erdos625.LimitingMarginTargetTransport
import Mathlib.Tactic

/-!
# Uniform compact-target bounds for the signed four-size derivative

The quadratic-main reduction leaves two profile-dependent lower-order terms:

* the selected finite four-deficit tilt;
* the logarithm of its finite partition function.

Both are uniformly bounded on the fixed manuscript target corridor
`[5/2, 9/2]`.  The limiting tilt and limiting optimized value are continuous on
this compact interval, hence have finite absolute maxima.  Existing uniform
score convergence transfers these bounds to the exact finite four-deficit
model.  Finally

`log partition = optimizedValue + tilt * target`

converts the two transferred bounds into a partition-logarithm bound.

No numerical optimizer substitution is made, and no derivative corridor,
root, first moment, chromatic lower tail, partial diagonal, skeleton, second
moment, or final Erdős statement is assumed or proved here.
-/

namespace Erdos625

open Filter Set
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- At fixed four-point scores, the selected tilt is continuous at every
interior target. -/
theorem ProfileEntropyS4.continuousAt_tilt_fixed_score
    (g : Fin 4 → ℝ) {T : ℝ} (hT : T ∈ Ioo (2 : ℝ) 5) :
    ContinuousAt (fun T' ↦ ProfileEntropyS4.tilt g T') T := by
  simpa only [id_eq] using
    (ProfileEntropyS4.tendsto_tilt_of_scores_and_target
      (h := fun _ : ℝ ↦ g) g (T' := id)
      (fun _ ↦ tendsto_const_nhds) tendsto_id hT)

/-- The limiting four-Gaussian tilt is continuous on the full explicit
admissibility corridor. -/
theorem continuousOn_fourGaussianTilt_admissibilityTargetCorridor :
    ContinuousOn
      (fun T ↦ ProfileEntropyS4.tilt fourGaussianScore T)
      signedFourAdmissibilityTargetCorridor := by
  intro T hT
  exact
    (ProfileEntropyS4.continuousAt_tilt_fixed_score fourGaussianScore
      (signedFourAdmissibilityTargetCorridor_subset_Ioo hT)).continuousWithinAt

/-- The limiting four-Gaussian optimized value is continuous on the same
explicit compact corridor. -/
theorem continuousOn_fourGaussianOptimizedValue_admissibilityTargetCorridor :
    ContinuousOn
      (ProfileEntropyS4.optimizedValue fourGaussianScore)
      signedFourAdmissibilityTargetCorridor := by
  intro T hT
  exact
    (tendsto_fourGaussianOptimizedValue_of_target id tendsto_id
      (signedFourAdmissibilityTargetCorridor_subset_Ioo hT)).continuousWithinAt

private theorem signedFourAdmissibilityTargetCorridor_nonempty :
    signedFourAdmissibilityTargetCorridor.Nonempty := by
  refine ⟨5 / 2, ?_⟩
  simp [signedFourAdmissibilityTargetCorridor]

/-- The limiting selected tilt has one finite absolute bound on the fixed
corridor. -/
theorem exists_uniform_abs_fourGaussianTilt_bound :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ T ∈ signedFourAdmissibilityTargetCorridor,
        |ProfileEntropyS4.tilt fourGaussianScore T| ≤ M := by
  have hContinuous : ContinuousOn
      (fun T ↦ |ProfileEntropyS4.tilt fourGaussianScore T|)
      signedFourAdmissibilityTargetCorridor :=
    continuousOn_fourGaussianTilt_admissibilityTargetCorridor.abs
  obtain ⟨T₀, hT₀, hMax⟩ :=
    signedFourAdmissibilityTargetCorridor_compact.exists_isMaxOn
      signedFourAdmissibilityTargetCorridor_nonempty hContinuous
  refine ⟨|ProfileEntropyS4.tilt fourGaussianScore T₀|,
    abs_nonneg _, ?_⟩
  intro T hT
  exact hMax T hT

/-- The limiting optimized value has one finite absolute bound on the fixed
corridor. -/
theorem exists_uniform_abs_fourGaussianOptimizedValue_bound :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ T ∈ signedFourAdmissibilityTargetCorridor,
        |ProfileEntropyS4.optimizedValue fourGaussianScore T| ≤ M := by
  have hContinuous : ContinuousOn
      (fun T ↦ |ProfileEntropyS4.optimizedValue fourGaussianScore T|)
      signedFourAdmissibilityTargetCorridor :=
    continuousOn_fourGaussianOptimizedValue_admissibilityTargetCorridor.abs
  obtain ⟨T₀, hT₀, hMax⟩ :=
    signedFourAdmissibilityTargetCorridor_compact.exists_isMaxOn
      signedFourAdmissibilityTargetCorridor_nonempty hContinuous
  refine ⟨|ProfileEntropyS4.optimizedValue fourGaussianScore T₀|,
    abs_nonneg _, ?_⟩
  intro T hT
  exact hMax T hT

/-- Uniform score convergence transfers compact bounds for both the selected
tilt and the logarithm of the finite partition function.  One threshold works
for every sufficiently large deficit parameter and every target in the full
admissibility corridor. -/
theorem
    exists_eventually_uniform_fourDeficit_tilt_and_logPartition_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
      ∀ alpha ≥ N, ∀ T ∈ signedFourAdmissibilityTargetCorridor,
        |ProfileEntropyS4.tilt (fourDeficitScore alpha) T| ≤ C ∧
        |Real.log
          (ProfileEntropyS4.partition (fourDeficitScore alpha)
            (ProfileEntropyS4.tilt (fourDeficitScore alpha) T))| ≤ C := by
  obtain ⟨Mtilt, hMtiltNonneg, hMtilt⟩ :=
    exists_uniform_abs_fourGaussianTilt_bound
  obtain ⟨Mvalue, hMvalueNonneg, hMvalue⟩ :=
    exists_uniform_abs_fourGaussianOptimizedValue_bound
  obtain ⟨Ntilt, hNtilt⟩ :=
    ProfileEntropyS4.eventually_uniformOn_tilt_of_uniform_scores
      fourDeficitScore fourGaussianScore
      signedFourAdmissibilityTargetCorridor
      signedFourAdmissibilityTargetCorridor_compact
      signedFourAdmissibilityTargetCorridor_subset_Ioo
      eventually_uniform_fourDeficitScore
      1 (by norm_num : (0 : ℝ) < 1)
  obtain ⟨Nvalue, hNvalue⟩ :=
    ProfileEntropyS4.eventually_uniformOn_optimizedValue_of_uniform_scores
      fourDeficitScore fourGaussianScore
      signedFourAdmissibilityTargetCorridor
      signedFourAdmissibilityTargetCorridor_subset_Ioo
      eventually_uniform_fourDeficitScore
      1 (by norm_num : (0 : ℝ) < 1)
  let C : ℝ :=
    (Mtilt + 1) + (Mvalue + 1) + (Mtilt + 1) * (9 / 2)
  have hTiltEnvelopeNonneg : 0 ≤ Mtilt + 1 := by linarith
  have hValueEnvelopeNonneg : 0 ≤ Mvalue + 1 := by linarith
  have hProductNonneg : 0 ≤ (Mtilt + 1) * (9 / 2 : ℝ) :=
    mul_nonneg hTiltEnvelopeNonneg (by norm_num)
  have hCNonneg : 0 ≤ C := by
    dsimp only [C]
    linarith
  refine ⟨C, hCNonneg, max Ntilt Nvalue, ?_⟩
  intro alpha halpha T hT
  have hTiltClose := hNtilt alpha (by omega) T hT
  have hValueClose := hNvalue alpha (by omega) T hT
  have hTiltLimit := hMtilt T hT
  have hValueLimit := hMvalue T hT
  have hTiltBound :
      |ProfileEntropyS4.tilt (fourDeficitScore alpha) T| ≤ Mtilt + 1 := by
    calc
      |ProfileEntropyS4.tilt (fourDeficitScore alpha) T| =
          |(ProfileEntropyS4.tilt (fourDeficitScore alpha) T -
              ProfileEntropyS4.tilt fourGaussianScore T) +
            ProfileEntropyS4.tilt fourGaussianScore T| := by
              congr 1
              ring
      _ ≤
          |ProfileEntropyS4.tilt (fourDeficitScore alpha) T -
            ProfileEntropyS4.tilt fourGaussianScore T| +
          |ProfileEntropyS4.tilt fourGaussianScore T| := abs_add_le _ _
      _ ≤ Mtilt + 1 := by linarith
  have hValueBound :
      |ProfileEntropyS4.optimizedValue (fourDeficitScore alpha) T| ≤
        Mvalue + 1 := by
    calc
      |ProfileEntropyS4.optimizedValue (fourDeficitScore alpha) T| =
          |(ProfileEntropyS4.optimizedValue (fourDeficitScore alpha) T -
              ProfileEntropyS4.optimizedValue fourGaussianScore T) +
            ProfileEntropyS4.optimizedValue fourGaussianScore T| := by
              congr 1
              ring
      _ ≤
          |ProfileEntropyS4.optimizedValue (fourDeficitScore alpha) T -
            ProfileEntropyS4.optimizedValue fourGaussianScore T| +
          |ProfileEntropyS4.optimizedValue fourGaussianScore T| :=
        abs_add_le _ _
      _ ≤ Mvalue + 1 := by linarith
  have hTargetAbs : |T| ≤ (9 / 2 : ℝ) := by
    have hT' := hT
    simp only [signedFourAdmissibilityTargetCorridor, mem_Icc] at hT'
    rw [abs_of_nonneg (by linarith [hT'.1])]
    exact hT'.2
  have hTiltTimesTarget :
      |ProfileEntropyS4.tilt (fourDeficitScore alpha) T| * |T| ≤
        (Mtilt + 1) * (9 / 2 : ℝ) :=
    mul_le_mul hTiltBound hTargetAbs (abs_nonneg T)
      hTiltEnvelopeNonneg
  have hLogIdentity :
      Real.log
          (ProfileEntropyS4.partition (fourDeficitScore alpha)
            (ProfileEntropyS4.tilt (fourDeficitScore alpha) T)) =
        ProfileEntropyS4.optimizedValue (fourDeficitScore alpha) T +
          ProfileEntropyS4.tilt (fourDeficitScore alpha) T * T := by
    unfold ProfileEntropyS4.optimizedValue
    ring
  have hLogBound :
      |Real.log
          (ProfileEntropyS4.partition (fourDeficitScore alpha)
            (ProfileEntropyS4.tilt (fourDeficitScore alpha) T))| ≤
        (Mvalue + 1) + (Mtilt + 1) * (9 / 2 : ℝ) := by
    rw [hLogIdentity]
    calc
      |ProfileEntropyS4.optimizedValue (fourDeficitScore alpha) T +
          ProfileEntropyS4.tilt (fourDeficitScore alpha) T * T| ≤
        |ProfileEntropyS4.optimizedValue (fourDeficitScore alpha) T| +
          |ProfileEntropyS4.tilt (fourDeficitScore alpha) T * T| :=
        abs_add_le _ _
      _ =
        |ProfileEntropyS4.optimizedValue (fourDeficitScore alpha) T| +
          |ProfileEntropyS4.tilt (fourDeficitScore alpha) T| * |T| := by
        rw [abs_mul]
      _ ≤ (Mvalue + 1) + (Mtilt + 1) * (9 / 2 : ℝ) :=
        add_le_add hValueBound hTiltTimesTarget
  constructor
  · exact hTiltBound.trans (by
      dsimp only [C]
      linarith)
  · exact hLogBound.trans (by
      dsimp only [C]
      linarith)

/-- Along the actual phase sequence, the exact finite selected tilt and
partition logarithm are eventually bounded by one common constant, uniformly
for every target in the manuscript corridor. -/
theorem
    exists_eventually_uniform_phaseFourDeficit_tilt_and_logPartition_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ T ∈ signedFourAdmissibilityTargetCorridor,
          |ProfileEntropyS4.tilt (fourDeficitScore (phaseNat n)) T| ≤ C ∧
          |Real.log
            (ProfileEntropyS4.partition (fourDeficitScore (phaseNat n))
              (ProfileEntropyS4.tilt
                (fourDeficitScore (phaseNat n)) T))| ≤ C := by
  obtain ⟨C, hC, N, hN⟩ :=
    exists_eventually_uniform_fourDeficit_tilt_and_logPartition_bound
  refine ⟨C, hC, ?_⟩
  have hPhaseN : ∀ᶠ n : ℕ in atTop, N ≤ phaseNat n :=
    tendsto_phaseNat_atTop_nat (eventually_ge_atTop N)
  filter_upwards [hPhaseN] with n hn
  exact fun T hT ↦ hN (phaseNat n) hn T hT

#print axioms ProfileEntropyS4.continuousAt_tilt_fixed_score
#print axioms continuousOn_fourGaussianTilt_admissibilityTargetCorridor
#print axioms continuousOn_fourGaussianOptimizedValue_admissibilityTargetCorridor
#print axioms exists_uniform_abs_fourGaussianTilt_bound
#print axioms exists_uniform_abs_fourGaussianOptimizedValue_bound
#print axioms exists_eventually_uniform_fourDeficit_tilt_and_logPartition_bound
#print axioms exists_eventually_uniform_phaseFourDeficit_tilt_and_logPartition_bound

end

end Erdos625
