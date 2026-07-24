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

noncomputable section

local instance fintypeCanonicalResidualCellEvent
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A -> B -> Nat} {row : A -> Nat} {col : B -> Nat}
    (witness : PrescribedDemandWitness demand row col) (U : Nat) :
    Fintype (canonicalResidualCellEvent witness U) :=
  Fintype.ofFinite _

local instance fintypeResidualCapNoReturnEvent
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (R : Nat) (row : A -> Nat) (col : B -> Nat) :
    Fintype (ResidualCapNoReturnEvent M R row col) :=
  Fintype.ofFinite _

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

/-- Fibrewise retyping of the global canonical residual sigma family by its
literal Section IX cap/no-return events.  The attained demand and labelled
witness remain part of the state, so this is not an identification of a
single residual space across demands. -/
noncomputable def sigmaCanonicalDemandResidualEquivSigmaCapNoReturn
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A -> Nat) (col : B -> Nat) (U : Nat) :
    (Sigma fun demand : canonicalDemandImage row col U =>
      Sigma fun witness : PrescribedDemandWitness demand.1 row col =>
        canonicalResidualCellEvent witness U) ≃
      (Sigma fun demand : canonicalDemandImage row col U =>
        Sigma fun witness : PrescribedDemandWitness demand.1 row col =>
          ResidualCapNoReturnEvent (positiveDemandSupport demand.1) (U / 2)
            (residualRowDegree witness) (residualColumnDegree witness)) := by
  refine Equiv.sigmaCongrRight fun demand => ?_
  refine Equiv.sigmaCongrRight fun witness => ?_
  exact Equiv.setCongr
    (canonicalResidualCellEvent_eq_residualCapNoReturnEvent witness U)

/-- The matching-space equivalence followed by fibrewise Section IX
retyping. -/
noncomputable def configurationMatchingEquivSigmaCapNoReturn
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A -> Nat) (col : B -> Nat) (U : Nat) :
    ConfigurationMatching row col ≃
      (Sigma fun demand : canonicalDemandImage row col U =>
        Sigma fun witness : PrescribedDemandWitness demand.1 row col =>
          ResidualCapNoReturnEvent (positiveDemandSupport demand.1) (U / 2)
            (residualRowDegree witness) (residualColumnDegree witness)) :=
  (configurationMatchingEquivSigmaCanonicalDemandResidual row col U).trans
    (sigmaCanonicalDemandResidualEquivSigmaCapNoReturn row col U)

/-- The uniform law on the tagged global Section IX cap/no-return family.
Its nonemptiness is supplied by the ambient matching equivalence. -/
noncomputable def uniformSigmaCapNoReturn
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A -> Nat) (col : B -> Nat) (U : Nat)
    (htotal : ∑ a, row a = ∑ b, col b) :
    PMF
      (Sigma fun demand : canonicalDemandImage row col U =>
        Sigma fun witness : PrescribedDemandWitness demand.1 row col =>
          ResidualCapNoReturnEvent (positiveDemandSupport demand.1) (U / 2)
            (residualRowDegree witness) (residualColumnDegree witness)) := by
  letI : Nonempty (ConfigurationMatching row col) :=
    ⟨configurationMatchingEquiv row col htotal⟩
  let equivalence := configurationMatchingEquivSigmaCapNoReturn row col U
  letI : Nonempty
      (Sigma fun demand : canonicalDemandImage row col U =>
        Sigma fun witness : PrescribedDemandWitness demand.1 row col =>
          ResidualCapNoReturnEvent (positiveDemandSupport demand.1) (U / 2)
            (residualRowDegree witness) (residualColumnDegree witness)) :=
    ⟨equivalence (Classical.choice inferInstance)⟩
  exact PMF.uniformOfFintype _

/-- Exact global finite-law transport to the tagged Section IX cap/no-return
family.  It retains demand and witness tags, and therefore asserts neither an
untagged residual law, conditioning statement, expectation, nor asymptotic
bound. -/
theorem uniformConfigurationMatching_map_sigmaCapNoReturn
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A -> Nat) (col : B -> Nat) (U : Nat)
    (htotal : ∑ a, row a = ∑ b, col b) :
    (uniformConfigurationMatching row col htotal).map
        (configurationMatchingEquivSigmaCapNoReturn row col U) =
      uniformSigmaCapNoReturn row col U htotal := by
  letI : Nonempty (ConfigurationMatching row col) :=
    ⟨configurationMatchingEquiv row col htotal⟩
  let equivalence := configurationMatchingEquivSigmaCapNoReturn row col U
  letI : Nonempty
      (Sigma fun demand : canonicalDemandImage row col U =>
        Sigma fun witness : PrescribedDemandWitness demand.1 row col =>
          ResidualCapNoReturnEvent (positiveDemandSupport demand.1) (U / 2)
            (residualRowDegree witness) (residualColumnDegree witness)) :=
    ⟨equivalence (Classical.choice inferInstance)⟩
  change (PMF.uniformOfFintype (ConfigurationMatching row col)).map equivalence = _
  simpa only [uniformSigmaCapNoReturn] using
    (uniformOfFintype_map_equiv equivalence)

#print axioms sigmaCanonicalDemandResidual_mem_residualCapNoReturn
#print axioms sigmaCanonicalDemandResidualEquivSigmaCapNoReturn
#print axioms configurationMatchingEquivSigmaCapNoReturn
#print axioms uniformSigmaCapNoReturn
#print axioms uniformConfigurationMatching_map_sigmaCapNoReturn

end

end Erdos625
