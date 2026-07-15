import Erdos625.Section8CanonicalEventCardinality
import Erdos625.Section8CanonicalDemandPartition
import Erdos625.ConfigurationModelProbability
import Erdos625.UniformEquivTransport
import Erdos625.UniformSigmaTransport

/-!
# Section VIII: global canonical-demand/residual disintegration

The literal canonical-demand map decomposes every configuration matching into
its attained canonical demand, the unique labelled witness for that demand,
and the corresponding residual cap/no-return configuration.  The residual
type depends on the attained demand (and its witness), so the result is a
dependent finite sigma decomposition.  This is structural only: it neither
asserts a common residual law across demands nor proves a quantitative
high-skeleton estimate.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-! Keep finite-event instances local, as in the fixed-fibre law modules. -/
local instance instFintypeCanonicalResidualCellEventGlobalResidual
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A -> B -> Nat} {row : A -> Nat} {col : B -> Nat}
    (witness : PrescribedDemandWitness demand row col) (U : Nat) :
    Fintype (canonicalResidualCellEvent witness U) :=
  Fintype.ofFinite _

local instance instFintypeCanonicalDemandEventGlobalResidual
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A -> B -> Nat) (row : A -> Nat) (col : B -> Nat) (U : Nat) :
    Fintype (canonicalDemandEvent demand row col U) :=
  Fintype.ofFinite _

/-- A nonzero entry retained by the literal canonical-demand map is strictly
above the half-cutoff. -/
theorem canonicalDemandOfMatching_high_of_ne_zero
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A -> Nat} {col : B -> Nat}
    (matching : ConfigurationMatching row col) (U : Nat) (a : A) (b : B)
    (h : canonicalDemandOfMatching matching U a b ≠ 0) :
    U / 2 < canonicalDemandOfMatching matching U a b := by
  by_cases hhigh : U / 2 < configurationCellCount matching a b
  · simp [canonicalDemandOfMatching, canonicalHighDemand, hhigh]
  · simp [canonicalDemandOfMatching, canonicalHighDemand, hhigh] at h

/-- Every demand table in the finite image has a literal matching in its
canonical-demand fibre.  No total-balance or probability hypothesis is used. -/
theorem nonempty_canonicalDemandEvent_of_canonicalDemandImage
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A -> Nat) (col : B -> Nat) (U : Nat)
    (demand : canonicalDemandImage row col U) :
    Nonempty (canonicalDemandEvent demand.1 row col U) := by
  classical
  obtain ⟨matching, -, hmatching⟩ := Finset.mem_image.mp demand.2
  exact ⟨⟨matching, hmatching⟩⟩

/-- The strict high-demand premise for the fixed-fibre residual equivalence
is automatic for any demand table actually attained by a matching. -/
theorem canonicalDemandImage_high
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A -> Nat) (col : B -> Nat) (U : Nat)
    (demand : canonicalDemandImage row col U)
    (a : A) (b : B) (h : demand.1 a b ≠ 0) :
    U / 2 < demand.1 a b := by
  classical
  obtain ⟨matching, -, hmatching⟩ := Finset.mem_image.mp demand.2
  have hnonzero : canonicalDemandOfMatching matching U a b ≠ 0 := by
    intro hzero
    apply h
    rw [← hmatching]
    exact hzero
  rw [← hmatching]
  exact canonicalDemandOfMatching_high_of_ne_zero matching U a b hnonzero

/-- Exact finite decomposition of every configuration matching into its
attained canonical demand, its labelled witness, and its residual canonical
event configuration.  The equivalence remains valid if the ambient matching
type is empty. -/
noncomputable def configurationMatchingEquivSigmaCanonicalDemandResidual
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A -> Nat) (col : B -> Nat) (U : Nat) :
    ConfigurationMatching row col ≃
      Σ demand : canonicalDemandImage row col U,
        Σ witness : PrescribedDemandWitness demand.1 row col,
          canonicalResidualCellEvent witness U :=
  (configurationMatchingEquivSigmaCanonicalDemandEvent row col U).trans
    (Equiv.sigmaCongrRight fun demand =>
      canonicalDemandEventEquivSigmaResidual demand.1 row col U
        (canonicalDemandImage_high row col U demand))

/-- The uniform finite PMF on the global dependent canonical-demand/witness/
residual sigma space.  The equal-total hypothesis supplies its nonemptiness
through the matching equivalence; no individual demand fibre is assumed
nonempty separately. -/
noncomputable def uniformSigmaCanonicalDemandResidual
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A -> Nat) (col : B -> Nat) (U : Nat)
    (htotal : ∑ a, row a = ∑ b, col b) :
    PMF
      (Σ demand : canonicalDemandImage row col U,
        Σ witness : PrescribedDemandWitness demand.1 row col,
          canonicalResidualCellEvent witness U) := by
  letI : Nonempty (ConfigurationMatching row col) :=
    ⟨configurationMatchingEquiv row col htotal⟩
  let equivalence :=
    configurationMatchingEquivSigmaCanonicalDemandResidual row col U
  letI : Nonempty
      (Σ demand : canonicalDemandImage row col U,
        Σ witness : PrescribedDemandWitness demand.1 row col,
          canonicalResidualCellEvent witness U) :=
    ⟨equivalence (Classical.choice inferInstance)⟩
  exact PMF.uniformOfFintype _

/-- With equal ambient stub totals, the uniform matching law transports
exactly to the uniform law on the full dependent canonical-demand/witness/
residual sigma space.  This is a finite-equivalence statement only. -/
theorem uniformConfigurationMatching_map_sigmaCanonicalDemandResidual
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A -> Nat) (col : B -> Nat) (U : Nat)
    (htotal : ∑ a, row a = ∑ b, col b) :
    (uniformConfigurationMatching row col htotal).map
        (configurationMatchingEquivSigmaCanonicalDemandResidual row col U) =
      uniformSigmaCanonicalDemandResidual row col U htotal := by
  letI : Nonempty (ConfigurationMatching row col) :=
    ⟨configurationMatchingEquiv row col htotal⟩
  let equivalence :=
    configurationMatchingEquivSigmaCanonicalDemandResidual row col U
  letI : Nonempty
      (Σ demand : canonicalDemandImage row col U,
        Σ witness : PrescribedDemandWitness demand.1 row col,
          canonicalResidualCellEvent witness U) :=
    ⟨equivalence (Classical.choice inferInstance)⟩
  change (PMF.uniformOfFintype (ConfigurationMatching row col)).map equivalence = _
  simpa only [uniformSigmaCanonicalDemandResidual] using
    (uniformOfFintype_map_equiv equivalence)

/-- The canonical-demand marginal of the ambient uniform matching law is
exactly proportional to the cardinality of its dependent witness/residual
fibre.  Thus the attained demand tables are not treated as uniformly likely;
their finite fibre sizes are the exact mixture weights. -/
theorem uniformConfigurationMatching_map_canonicalDemand_apply
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A -> Nat) (col : B -> Nat) (U : Nat)
    (htotal : ∑ a, row a = ∑ b, col b)
    (demand : canonicalDemandImage row col U) :
    ((uniformConfigurationMatching row col htotal).map
        (fun matching =>
          (configurationMatchingEquivSigmaCanonicalDemandResidual row col U
            matching).1)) demand =
      (Fintype.card
        (Σ witness : PrescribedDemandWitness demand.1 row col,
          canonicalResidualCellEvent witness U) : ENNReal) /
        (Fintype.card (ConfigurationMatching row col) : ENNReal) := by
  letI : Nonempty (ConfigurationMatching row col) :=
    ⟨configurationMatchingEquiv row col htotal⟩
  let equivalence :=
    configurationMatchingEquivSigmaCanonicalDemandResidual row col U
  letI : Nonempty
      (Σ demand : canonicalDemandImage row col U,
        Σ witness : PrescribedDemandWitness demand.1 row col,
          canonicalResidualCellEvent witness U) :=
    ⟨equivalence (Classical.choice inferInstance)⟩
  change ((uniformConfigurationMatching row col htotal).map
      (fun matching => (equivalence matching).1)) demand = _
  calc
    ((uniformConfigurationMatching row col htotal).map
        (fun matching => (equivalence matching).1)) demand =
        ((uniformConfigurationMatching row col htotal).map equivalence).map
          (fun z : Σ demand : canonicalDemandImage row col U,
            Σ witness : PrescribedDemandWitness demand.1 row col,
              canonicalResidualCellEvent witness U => z.1) demand := by
      exact congrArg
        (fun p : PMF (canonicalDemandImage row col U) => p demand)
        (by
          simpa only [Function.comp_def] using
            (PMF.map_comp (p := uniformConfigurationMatching row col htotal)
              (f := equivalence)
              (fun z : Σ demand : canonicalDemandImage row col U,
                Σ witness : PrescribedDemandWitness demand.1 row col,
                  canonicalResidualCellEvent witness U => z.1)).symm)
    _ = (uniformSigmaCanonicalDemandResidual row col U htotal).map
          (fun z : Σ demand : canonicalDemandImage row col U,
            Σ witness : PrescribedDemandWitness demand.1 row col,
              canonicalResidualCellEvent witness U => z.1) demand := by
      rw [uniformConfigurationMatching_map_sigmaCanonicalDemandResidual]
    _ =
        (Fintype.card
          (Σ witness : PrescribedDemandWitness demand.1 row col,
            canonicalResidualCellEvent witness U) : ENNReal) /
          (Fintype.card
            (Σ demand : canonicalDemandImage row col U,
              Σ witness : PrescribedDemandWitness demand.1 row col,
                canonicalResidualCellEvent witness U) : ENNReal) := by
      change ((PMF.uniformOfFintype
        (Σ demand : canonicalDemandImage row col U,
          Σ witness : PrescribedDemandWitness demand.1 row col,
            canonicalResidualCellEvent witness U)).map
          (fun z : Σ demand : canonicalDemandImage row col U,
            Σ witness : PrescribedDemandWitness demand.1 row col,
              canonicalResidualCellEvent witness U => z.1)) demand = _
      exact uniformOfFintype_sigma_map_fst_apply demand
    _ = _ := by
      rw [← Fintype.card_congr equivalence]

/-- Each global demand fibre factors exactly into its labelled-witness count
and one standardized residual-event count.  The reference witness remains an
explicit parameter: the residual event varies with the attained demand. -/
theorem card_sigmaCanonicalDemandResidual_fiber_eq_witness_mul_residual
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A -> Nat) (col : B -> Nat) (U : Nat)
    (demand : canonicalDemandImage row col U)
    (witness0 : PrescribedDemandWitness demand.1 row col) :
    Fintype.card
      (Σ witness : PrescribedDemandWitness demand.1 row col,
        canonicalResidualCellEvent witness U) =
      Fintype.card (PrescribedDemandWitness demand.1 row col) *
        Fintype.card (canonicalResidualCellEvent witness0 U) := by
  calc
    Fintype.card
        (Σ witness : PrescribedDemandWitness demand.1 row col,
          canonicalResidualCellEvent witness U) =
        Fintype.card (canonicalDemandEvent demand.1 row col U) := by
      exact Fintype.card_congr
        (canonicalDemandEventEquivSigmaResidual demand.1 row col U
          (canonicalDemandImage_high row col U demand)).symm
    _ = Fintype.card (PrescribedDemandWitness demand.1 row col) *
          Fintype.card (canonicalResidualCellEvent witness0 U) := by
      exact card_canonicalDemandEvent_eq_witness_mul_residual demand.1 row col U
        (canonicalDemandImage_high row col U demand) witness0

#print axioms canonicalDemandOfMatching_high_of_ne_zero
#print axioms nonempty_canonicalDemandEvent_of_canonicalDemandImage
#print axioms canonicalDemandImage_high
#print axioms configurationMatchingEquivSigmaCanonicalDemandResidual
#print axioms uniformSigmaCanonicalDemandResidual
#print axioms uniformConfigurationMatching_map_sigmaCanonicalDemandResidual
#print axioms uniformConfigurationMatching_map_canonicalDemand_apply
#print axioms card_sigmaCanonicalDemandResidual_fiber_eq_witness_mul_residual

end

end Erdos625
