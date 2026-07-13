import Erdos625.VertexBlockGraph

/-!
# Exact expectation transport for the vertex-block graph model

The exact pushforward identity from `VertexBlockGraph` transports not only
events but every real-valued statistic.  Since both sample spaces are finite,
measurability and Bochner integrability require no hypotheses on the
statistic.
-/

open MeasureTheory

namespace Erdos625

/-- The Bochner expectation of any real-valued statistic under `G(n,1/2)` is
exactly its expectation on the uniform vertex-block product space. -/
theorem integral_randomGraphMeasure_eq_randomGraphBlockExpectation
    (n : ℕ) (F : LabeledGraph n → ℝ) :
    ∫ G, F G ∂(randomGraphMeasure n) = randomGraphBlockExpectation F := by
  rw [← map_vertexBlockMeasure_eq_randomGraphMeasure n]
  rw [MeasureTheory.integral_map
    (measurable_blocksToGraph_top n).aemeasurable
    (measurable_of_finite F).aestronglyMeasurable]
  rfl

/-- Consequently, the center used by vertex-block bounded differences is the
actual random-graph expectation, not merely an auxiliary block average. -/
theorem randomGraphBlockExpectation_eq_integral_randomGraphMeasure
    {n : ℕ} (F : LabeledGraph n → ℝ) :
    randomGraphBlockExpectation F = ∫ G, F G ∂(randomGraphMeasure n) :=
  (integral_randomGraphMeasure_eq_randomGraphBlockExpectation n F).symm

end Erdos625
