import Erdos625.Section8CanonicalEventCardinality
import Erdos625.UniformConditionalLaw
import Erdos625.UniformProductTransport

/-!
# Section VIII: exact canonical conditional-law transport

Under the strict high-demand condition, the literal canonical-demand event is
already partitioned by a labelled prescribed-demand witness and its residual
cap/no-return configuration.  This module records the corresponding exact
finite-uniform-law transport: first on the *joint* sigma space, then (after a
reference witness is fixed) as a product law with a uniform standardized
residual-coordinate marginal.  It does not estimate the probability or
nonemptiness of the canonical event.
-/

namespace Erdos625

noncomputable section

/-! Keep finite instances local, just as in the cardinality and normalization
modules.  This avoids changing instance search outside this law-transport
module. -/
local instance instFintypeCanonicalDemandEventConditionalLaw
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) (U : ℕ) :
    Fintype (canonicalDemandEvent demand row col U) :=
  Fintype.ofFinite _

local instance instFintypeCanonicalResidualCellEventConditionalLaw
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) (U : ℕ) :
    Fintype (canonicalResidualCellEvent witness U) :=
  Fintype.ofFinite _

/-- A nonempty canonical-demand event gives a nonempty joint sigma family of
its labelled witnesses and residual configurations.  This is only an exact
finite equivalence; it supplies no probability lower bound. -/
theorem nonempty_sigmaCanonicalResidual_of_nonempty_canonicalDemandEvent
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) (U : ℕ)
    (hhigh : ∀ a b, demand a b ≠ 0 → U / 2 < demand a b)
    [Nonempty (canonicalDemandEvent demand row col U)] :
    Nonempty
      (Σ witness : PrescribedDemandWitness demand row col,
        canonicalResidualCellEvent witness U) := by
  let x : canonicalDemandEvent demand row col U := Classical.choice inferInstance
  exact ⟨canonicalDemandEventEquivSigmaResidual demand row col U hhigh x⟩

/-- The uniform law on the canonical-demand event transports exactly to the
uniform law on the joint sigma space of a labelled witness and its residual
canonical event. -/
theorem uniform_canonicalDemandEventSubtype_map_sigmaResidual
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) (U : ℕ)
    (hhigh : ∀ a b, demand a b ≠ 0 → U / 2 < demand a b)
    [Nonempty (canonicalDemandEvent demand row col U)]
    [Nonempty
      (Σ witness : PrescribedDemandWitness demand row col,
        canonicalResidualCellEvent witness U)] :
    (PMF.uniformOfFintype (canonicalDemandEvent demand row col U)).map
        (canonicalDemandEventEquivSigmaResidual demand row col U hhigh) =
      PMF.uniformOfFintype
        (Σ witness : PrescribedDemandWitness demand row col,
          canonicalResidualCellEvent witness U) := by
  exact uniformOfFintype_map_equiv
    (canonicalDemandEventEquivSigmaResidual demand row col U hhigh)

/-- Conditioning the ambient uniform configuration law on the nonempty
canonical-demand event is exactly reconstruction from the uniform joint sigma
law of its witness and residual configuration.  This does not yet identify a
fixed residual marginal or establish any global canonical-event estimate. -/
theorem uniform_filter_canonicalDemandEvent_eq_uniformSigmaResidual_reconstruction
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) (U : ℕ)
    (hhigh : ∀ a b, demand a b ≠ 0 → U / 2 < demand a b)
    [Nonempty (ConfigurationMatching row col)]
    [Nonempty (canonicalDemandEvent demand row col U)]
    [Nonempty
      (Σ witness : PrescribedDemandWitness demand row col,
        canonicalResidualCellEvent witness U)] :
    (PMF.uniformOfFintype (ConfigurationMatching row col)).filter
        (canonicalDemandEvent demand row col U)
        (uniformFilterWitness (canonicalDemandEvent demand row col U)) =
      ((PMF.uniformOfFintype
        (Σ witness : PrescribedDemandWitness demand row col,
          canonicalResidualCellEvent witness U)).map
        (canonicalDemandEventEquivSigmaResidual
          demand row col U hhigh).symm).map
        (fun x : canonicalDemandEvent demand row col U => x.1) := by
  calc
    _ = (PMF.uniformOfFintype
          (canonicalDemandEvent demand row col U)).map
          (fun x : canonicalDemandEvent demand row col U => x.1) :=
      uniform_filter_eq_uniformSubtype_map
        (canonicalDemandEvent demand row col U)
    _ = _ := by
      rw [uniformOfFintype_map_equiv
        (canonicalDemandEventEquivSigmaResidual
          demand row col U hhigh).symm]

/-- The residual configuration fibre is judgmentally independent of the
labelled witness: residual degrees retain only `demand`, `row`, and `col`.
This converts the joint sigma family into a product with any fixed residual
fibre. -/
noncomputable def sigmaCanonicalResidualEquivWitnessTimesResidual
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness₀ : PrescribedDemandWitness demand row col) (U : ℕ) :
    (Σ witness : PrescribedDemandWitness demand row col,
      canonicalResidualCellEvent witness U) ≃
      PrescribedDemandWitness demand row col ×
        canonicalResidualCellEvent witness₀ U := by
  change
    (Σ _witness : PrescribedDemandWitness demand row col,
      canonicalResidualCellEvent witness₀ U) ≃
      PrescribedDemandWitness demand row col ×
        canonicalResidualCellEvent witness₀ U
  exact Equiv.sigmaEquivProd _ _

/-- Under the high-demand condition, the canonical event is exactly a product
of a labelled witness choice and one fixed standardized residual fibre.  This
is a finite equivalence, without any claim that the canonical event is likely.
-/
noncomputable def canonicalDemandEventEquivWitnessTimesResidual
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) (U : ℕ)
    (hhigh : ∀ a b, demand a b ≠ 0 → U / 2 < demand a b)
    (witness₀ : PrescribedDemandWitness demand row col) :
    canonicalDemandEvent demand row col U ≃
      PrescribedDemandWitness demand row col ×
        canonicalResidualCellEvent witness₀ U :=
  (canonicalDemandEventEquivSigmaResidual demand row col U hhigh).trans
    (sigmaCanonicalResidualEquivWitnessTimesResidual witness₀ U)

/-- A nonempty canonical-demand event makes every standardized residual fibre
nonempty.  This follows from the exact product equivalence and is not a
probability lower bound. -/
theorem nonempty_canonicalResidualCellEvent_of_nonempty_canonicalDemandEvent
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness₀ : PrescribedDemandWitness demand row col) (U : ℕ)
    (hhigh : ∀ a b, demand a b ≠ 0 → U / 2 < demand a b)
    [Nonempty (canonicalDemandEvent demand row col U)] :
    Nonempty (canonicalResidualCellEvent witness₀ U) := by
  let x : canonicalDemandEvent demand row col U := Classical.choice inferInstance
  let product :=
    canonicalDemandEventEquivWitnessTimesResidual
      demand row col U hhigh witness₀ x
  exact ⟨product.2⟩

/-- The uniform canonical-event subtype law transports to the uniform product
of labelled witnesses and one fixed standardized residual fibre.  The two
nonemptiness instances on the right are derivable from the preceding exact
nonemptiness lemma together with the displayed witness, but remain explicit so
that `PMF.uniformOfFintype` can elaborate the proposition transparently. -/
theorem uniform_canonicalDemandEventSubtype_map_witnessTimesResidual
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) (U : ℕ)
    (hhigh : ∀ a b, demand a b ≠ 0 → U / 2 < demand a b)
    (witness₀ : PrescribedDemandWitness demand row col)
    [Nonempty (canonicalDemandEvent demand row col U)]
    [Nonempty (PrescribedDemandWitness demand row col)]
    [Nonempty (canonicalResidualCellEvent witness₀ U)] :
    (PMF.uniformOfFintype (canonicalDemandEvent demand row col U)).map
        (canonicalDemandEventEquivWitnessTimesResidual
          demand row col U hhigh witness₀) =
      PMF.uniformOfFintype
        (PrescribedDemandWitness demand row col ×
          canonicalResidualCellEvent witness₀ U) := by
  exact uniformOfFintype_map_equiv
    (canonicalDemandEventEquivWitnessTimesResidual
      demand row col U hhigh witness₀)

/-- The standardized residual coordinate of the uniform canonical-event
subtype has its own uniform law.  The residual event is fixed only on the
canonical-event subtype, so this statement intentionally does not extend a
residual-coordinate function to arbitrary ambient matchings. -/
theorem uniform_canonicalDemandEventSubtype_map_fixedResidual
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness₀ : PrescribedDemandWitness demand row col) (U : ℕ)
    (hhigh : ∀ a b, demand a b ≠ 0 → U / 2 < demand a b)
    [Nonempty (canonicalDemandEvent demand row col U)]
    [Nonempty (canonicalResidualCellEvent witness₀ U)] :
    (PMF.uniformOfFintype (canonicalDemandEvent demand row col U)).map
        (fun x : canonicalDemandEvent demand row col U =>
          (canonicalDemandEventEquivWitnessTimesResidual
            demand row col U hhigh witness₀ x).2) =
      PMF.uniformOfFintype (canonicalResidualCellEvent witness₀ U) := by
  letI : Nonempty (PrescribedDemandWitness demand row col) := ⟨witness₀⟩
  calc
    _ = ((PMF.uniformOfFintype (canonicalDemandEvent demand row col U)).map
          (canonicalDemandEventEquivWitnessTimesResidual
            demand row col U hhigh witness₀)).map
           (fun product : PrescribedDemandWitness demand row col ×
             canonicalResidualCellEvent witness₀ U => product.2) := by
      simpa only [Function.comp_def] using
        (PMF.map_comp
          (p := PMF.uniformOfFintype (canonicalDemandEvent demand row col U))
          (f := canonicalDemandEventEquivWitnessTimesResidual
            demand row col U hhigh witness₀)
          (fun product : PrescribedDemandWitness demand row col ×
            canonicalResidualCellEvent witness₀ U => product.2)).symm
    _ = (PMF.uniformOfFintype
          (PrescribedDemandWitness demand row col ×
            canonicalResidualCellEvent witness₀ U)).map
          (fun product : PrescribedDemandWitness demand row col ×
            canonicalResidualCellEvent witness₀ U => product.2) := by
      rw [uniform_canonicalDemandEventSubtype_map_witnessTimesResidual]
    _ = _ := uniformOfFintype_prod_map_snd

#print axioms nonempty_sigmaCanonicalResidual_of_nonempty_canonicalDemandEvent
#print axioms uniform_canonicalDemandEventSubtype_map_sigmaResidual
#print axioms uniform_filter_canonicalDemandEvent_eq_uniformSigmaResidual_reconstruction
#print axioms sigmaCanonicalResidualEquivWitnessTimesResidual
#print axioms canonicalDemandEventEquivWitnessTimesResidual
#print axioms nonempty_canonicalResidualCellEvent_of_nonempty_canonicalDemandEvent
#print axioms uniform_canonicalDemandEventSubtype_map_witnessTimesResidual
#print axioms uniform_canonicalDemandEventSubtype_map_fixedResidual

end

end Erdos625
