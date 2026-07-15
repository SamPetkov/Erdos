import Erdos625.Section8CanonicalEventCardinality
import Erdos625.UniformConditionalLaw

/-!
# Section VIII: exact canonical conditional-law transport

Under the strict high-demand condition, the literal canonical-demand event is
already partitioned by a labelled prescribed-demand witness and its residual
cap/no-return configuration.  This module records the corresponding exact
finite-uniform-law transport.  It is deliberately a law on the *joint* sigma
space of a witness and a residual configuration: it does not assert that the
residual coordinate alone has one fixed marginal law, nor does it estimate the
probability or nonemptiness of the canonical event.
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

#print axioms nonempty_sigmaCanonicalResidual_of_nonempty_canonicalDemandEvent
#print axioms uniform_canonicalDemandEventSubtype_map_sigmaResidual
#print axioms uniform_filter_canonicalDemandEvent_eq_uniformSigmaResidual_reconstruction

end

end Erdos625
