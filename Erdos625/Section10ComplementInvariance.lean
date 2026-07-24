import Erdos625.Target
import Mathlib.Tactic

/-!
# Section X: complement invariance of the half-random graph law

Complementation is a measure-preserving involution of the finite labelled
`G(n, 1/2)` sample space.  This is only a symmetry of the ambient law; it does
not establish the fixed-induced-subgraph restriction law or any simultaneous
quarter-density event.
-/

namespace Erdos625

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Complementation preserves the labelled `G(n, 1/2)` law exactly. -/
theorem randomGraphMeasure_map_compl (n : ℕ) :
    (randomGraphMeasure n).map (fun G : LabeledGraph n => Gᶜ) =
      randomGraphMeasure n := by
  classical
  apply Measure.ext_of_singleton
  intro G
  rw [Measure.map_apply (measurable_of_finite _) (MeasurableSet.singleton G)]
  have hpre :
      (fun H : LabeledGraph n => Hᶜ) ⁻¹' ({G} : Set (LabeledGraph n)) =
        {Gᶜ} := by
    ext H
    constructor <;> intro h
    · rw [← h]
      simp
    · rw [h]
      simp
  rw [hpre, randomGraphMeasure_singleton_uniform,
    randomGraphMeasure_singleton_uniform]

#print axioms randomGraphMeasure_map_compl

end

end Erdos625
