import Erdos625.Section8CanonicalDemandGlobalResidual
import Erdos625.Section8ResidualEventToSection9

/-!
# Section VIII--IX: tagged global canonical residuals

Every state of the global dependent canonical-demand/witness/residual sigma
space carries a residual configuration satisfying the literal Section IX
cap/no-return event for that state's own demand support and residual degrees.
This is a pointwise membership bridge only: it does not construct an untagged
residual PMF, condition a law, take an expectation, or assert an asymptotic
bound.
-/

namespace Erdos625

/-- A tagged state in the global canonical residual disintegration supplies
the exact cap/no-return hypothesis used by the Section IX fixed-family
machinery. -/
theorem sigmaCanonicalDemandResidual_mem_residualCapNoReturn
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A -> Nat} {col : B -> Nat} (U : Nat)
    (z : Sigma fun demand : canonicalDemandImage row col U =>
      Sigma fun witness : PrescribedDemandWitness demand.1 row col =>
        canonicalResidualCellEvent witness U) :
    z.2.2.1 ∈ ResidualCapNoReturnEvent
      (positiveDemandSupport z.1.1) (U / 2)
      (residualRowDegree z.2.1) (residualColumnDegree z.2.1) := by
  simpa only [canonicalResidualCellEvent_eq_residualCapNoReturnEvent]
    using z.2.2.2

#print axioms sigmaCanonicalDemandResidual_mem_residualCapNoReturn

end Erdos625
