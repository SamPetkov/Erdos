import Erdos625.ProbabilityTools
import Erdos625.Target
import Mathlib.Tactic

/-!
# Sections IX--X D4: count-to-cocolourable real seed

This task is a generic second-moment adapter.  The construction and moment
estimates for the count remain entirely external inputs.
-/

namespace Erdos625

open MeasureTheory Set
open scoped ENNReal NNReal ProbabilityTheory

/-- Any measurable nonnegative count whose positivity certifies a
`k`-cocolouring supplies the corresponding real-valued Paley--Zygmund seed
under the random-graph law. -/
theorem coColorable_real_seed_of_count
    (n k : Nat) (Z : LabeledGraph n -> ENNReal)
    (hZ : Measurable Z)
    (hPositive : ∀ G, 0 < Z G -> CoColorable G k) :
    (((∫⁻ G, Z G ∂(randomGraphMeasure n)) ^ 2 /
        (∫⁻ G, (Z G) ^ 2 ∂(randomGraphMeasure n))).toReal ≤
      (randomGraphMeasure n).real {G | CoColorable G k}) := by
  have hPZ := paleyZygmund_zero (mu := randomGraphMeasure n) hZ
  have hMono :
      (randomGraphMeasure n) {G | 0 < Z G} ≤
        (randomGraphMeasure n) {G | CoColorable G k} := by
    apply measure_mono
    intro G hG
    exact hPositive G hG
  have hENN :
      (∫⁻ G, Z G ∂(randomGraphMeasure n)) ^ 2 /
          (∫⁻ G, (Z G) ^ 2 ∂(randomGraphMeasure n)) ≤
        (randomGraphMeasure n) {G | CoColorable G k} :=
    hPZ.trans hMono
  rw [Measure.real]
  apply (ENNReal.toReal_le_toReal
    (ne_top_of_le_ne_top
      (measure_ne_top (randomGraphMeasure n) {G | CoColorable G k}) hENN)
    (measure_ne_top (randomGraphMeasure n) {G | CoColorable G k})).2
  exact hENN

end Erdos625

#print axioms Erdos625.coColorable_real_seed_of_count
