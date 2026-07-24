import Erdos625.Section8CanonicalEventResidual

/-!
# Section VIII: ambient canonical-demand partition

The canonical high-demand map partitions the whole finite configuration
matching space into its literal canonical-demand fibres.  This is an exact
finite counting identity; it makes no probability, residual-law, or
typed-skeleton estimate claim.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-! Keep the finite-event instance local, consistently with the other
canonical-event counting modules. -/
local instance instFintypeCanonicalDemandEventPartition
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) (U : ℕ) :
    Fintype (canonicalDemandEvent demand row col U) :=
  Fintype.ofFinite _

/-- The finite range of literal canonical high-demand tables realized by
ambient configuration matchings. -/
noncomputable def canonicalDemandImage
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A → ℕ) (col : B → ℕ) (U : ℕ) : Finset (A → B → ℕ) := by
  classical
  exact
    (Finset.univ : Finset (ConfigurationMatching row col)).image
      (fun matching => canonicalDemandOfMatching matching U)

/-- The explicit finite equivalence from ambient matchings to their attained
canonical demand and the corresponding literal fibre. -/
noncomputable def configurationMatchingEquivSigmaCanonicalDemandEvent
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A → ℕ) (col : B → ℕ) (U : ℕ) :
    ConfigurationMatching row col ≃
      Σ demand : canonicalDemandImage row col U,
        ↑(canonicalDemandEvent demand.1 row col U) := by
  classical
  exact
    (Equiv.sigmaSubtypeFiberEquiv
      (fun matching : ConfigurationMatching row col =>
        canonicalDemandOfMatching matching U)
      (fun demand => demand ∈ canonicalDemandImage row col U)
      (fun matching => Finset.mem_image_of_mem _ (Finset.mem_univ matching))).symm

/-- Exact ambient partition by the literal canonical high-demand table.
The statement is valid even when the configuration-matching type is empty,
so it requires no total-balance or nonemptiness hypothesis. -/
theorem card_configurationMatching_eq_sum_card_canonicalDemandEvent
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A → ℕ) (col : B → ℕ) (U : ℕ) :
    Fintype.card (ConfigurationMatching row col) =
      ∑ demand : canonicalDemandImage row col U,
        Fintype.card ↑(canonicalDemandEvent demand.1 row col U) := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr
    (configurationMatchingEquivSigmaCanonicalDemandEvent row col U)

#print axioms configurationMatchingEquivSigmaCanonicalDemandEvent
#print axioms card_configurationMatching_eq_sum_card_canonicalDemandEvent

end

end Erdos625
