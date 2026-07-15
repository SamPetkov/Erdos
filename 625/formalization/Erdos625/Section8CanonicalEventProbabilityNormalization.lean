import Erdos625.Section8CanonicalEventResidual
import Erdos625.ConfigurationModelProbability

/-!
# Section 8: canonical-event probability normalization

This module evaluates the literal canonical-demand event under the ambient
uniform configuration law. It is intentionally only a finite normalization
identity: it makes no claim about a conditional law, event nonemptiness,
high-demand separation, labelled witnesses, or asymptotics.
-/

namespace Erdos625

open scoped ENNReal

noncomputable section

/-! The event subtype is finite, but the project deliberately avoids a global
instance-search change for canonical event subtypes. -/
local instance instFintypeCanonicalDemandEvent
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A -> B -> Nat) (row : A -> Nat) (col : B -> Nat) (U : Nat) :
    Fintype (canonicalDemandEvent demand row col U) :=
  Fintype.ofFinite _

/-- Under the uniform law on all configuration matchings, the literal
canonical-demand event has its exact finite-cardinality probability. -/
theorem uniformConfigurationMatching_canonicalDemandEvent_apply
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A -> B -> Nat) (row : A -> Nat) (col : B -> Nat) (U : Nat)
    (htotal : Finset.univ.sum row = Finset.univ.sum col) :
    (uniformConfigurationMatching row col htotal).toOuterMeasure
        (canonicalDemandEvent demand row col U) =
      (Fintype.card ↑(canonicalDemandEvent demand row col U) : ℝ≥0∞) /
        ((Finset.univ.sum row).factorial : ℝ≥0∞) := by
  letI : Nonempty (ConfigurationMatching row col) :=
    ⟨configurationMatchingEquiv row col htotal⟩
  change (PMF.uniformOfFintype (ConfigurationMatching row col)).toOuterMeasure
      (canonicalDemandEvent demand row col U) = _
  rw [PMF.toOuterMeasure_uniformOfFintype_apply,
    card_configurationMatching row col htotal]

#print axioms uniformConfigurationMatching_canonicalDemandEvent_apply

end

end Erdos625
