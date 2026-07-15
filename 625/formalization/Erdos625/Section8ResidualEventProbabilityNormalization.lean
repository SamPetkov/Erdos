import Erdos625.Section8CanonicalEventResidual
import Erdos625.ConfigurationModelProbability

/-!
# Section 8: residual-event probability normalization

This module specializes the exact finite-event uniform-law normalization to
the residual canonical event after a fixed labelled witness is exposed.  It
does not assert a conditional law for the ambient event or any asymptotic
estimate.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-! The residual canonical-event subtype is finite; keep this instance local
to avoid changing downstream instance search. -/
local instance instFintypeCanonicalResidualCellEventProbabilityNormalization
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) (U : ℕ) :
    Fintype (canonicalResidualCellEvent witness U) :=
  Fintype.ofFinite _

/-- Under the uniform residual configuration law, the literal residual
canonical event has its exact finite-cardinality probability. -/
theorem uniformConfigurationMatching_canonicalResidualCellEvent_apply
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) (U : ℕ)
    (hres : (∑ a, residualRowDegree witness a) =
      ∑ b, residualColumnDegree witness b) :
    (uniformConfigurationMatching (residualRowDegree witness)
        (residualColumnDegree witness) hres).toOuterMeasure
        (canonicalResidualCellEvent witness U) =
      (Fintype.card ↑(canonicalResidualCellEvent witness U) : ℝ≥0∞) /
        ((∑ a, residualRowDegree witness a).factorial : ℝ≥0∞) := by
  exact uniformConfigurationMatching_event_apply
    (residualRowDegree witness) (residualColumnDegree witness) hres
    (canonicalResidualCellEvent witness U)

#print axioms uniformConfigurationMatching_canonicalResidualCellEvent_apply

end

end Erdos625
