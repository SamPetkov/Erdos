import Erdos625.Target
import Mathlib.Probability.UniformOn
import Mathlib.Tactic

/-!
# The half-binomial graph law is uniform

On the finite type of labelled graphs, every singleton under `G(n,1/2)` has
the same mass. Probability normalization therefore identifies the repository
measure exactly with `uniformOn Set.univ`.
-/

namespace Erdos625

open MeasureTheory ProbabilityTheory

noncomputable section

private theorem probabilityMeasure_eq_uniformOn_univ_of_singleton_eq
    {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [Nonempty Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hμ : ∀ x y : Ω, μ {x} = μ {y}) :
    μ = uniformOn Set.univ := by
  classical
  apply Measure.ext_of_singleton
  intro x
  have hsumμ : ∑ y : Ω, μ {y} = 1 := by
    calc
      ∑ y : Ω, μ {y} = μ (Finset.univ : Finset Ω) := by
        simp
      _ = 1 := by simp
  have hsumU : ∑ y : Ω, uniformOn (Set.univ : Set Ω) {y} = 1 := by
    calc
      ∑ y : Ω, uniformOn (Set.univ : Set Ω) {y} =
          uniformOn (Set.univ : Set Ω) (Finset.univ : Finset Ω) := by
        simp
      _ = 1 := by simp
  have hμcard : (Fintype.card Ω : ENNReal) * μ {x} = 1 := by
    calc
      (Fintype.card Ω : ENNReal) * μ {x} = ∑ _y : Ω, μ {x} := by
        simp
      _ = ∑ y : Ω, μ {y} := by
        apply Finset.sum_congr rfl
        intro y _
        exact (hμ y x).symm
      _ = 1 := hsumμ
  have hUcard :
      (Fintype.card Ω : ENNReal) * uniformOn (Set.univ : Set Ω) {x} = 1 := by
    have hU : ∀ y : Ω,
        uniformOn (Set.univ : Set Ω) {y} =
          uniformOn (Set.univ : Set Ω) {x} := by
      intro y
      simp [uniformOn_univ]
    calc
      (Fintype.card Ω : ENNReal) * uniformOn (Set.univ : Set Ω) {x} =
          ∑ _y : Ω, uniformOn (Set.univ : Set Ω) {x} := by
        simp
      _ = ∑ y : Ω, uniformOn (Set.univ : Set Ω) {y} := by
        apply Finset.sum_congr rfl
        intro y _
        exact (hU y).symm
      _ = 1 := hsumU
  apply (ENNReal.mul_right_inj
    (by positivity : (Fintype.card Ω : ENNReal) ≠ 0)
    (by simp : (Fintype.card Ω : ENNReal) ≠ (⊤ : ENNReal))).mp
  exact hμcard.trans hUcard.symm

/-- The repository's `G(n,1/2)` measure is exactly uniform on all labelled
graphs on `Fin n`. -/
theorem randomGraphMeasure_eq_uniformOn_univ (n : ℕ) :
    randomGraphMeasure n = uniformOn Set.univ := by
  classical
  apply probabilityMeasure_eq_uniformOn_univ_of_singleton_eq
  intro G H
  rw [randomGraphMeasure_singleton_uniform,
    randomGraphMeasure_singleton_uniform]

#print axioms randomGraphMeasure_eq_uniformOn_univ

end

end Erdos625
