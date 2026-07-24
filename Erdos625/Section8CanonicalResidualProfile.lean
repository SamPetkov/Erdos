import Erdos625.Section8ResidualDegreeTotal
import Erdos625.Section8CanonicalLabelledWitness

/-!
# Section VIII: canonical residual degree profile

The canonical high-demand exposure of a fixed configuration matching has a
uniquely determined labelled witness.  This module records the resulting
finite residual degree caps and total balance.  It makes no assertion about
the probability of the canonical event or the law of a conditioned residual
matching.
-/

namespace Erdos625

open scoped BigOperators

/-- The unique canonical high-demand witness of a matching has residual row
and column degrees bounded by any common ambient degree cap, with equal
residual totals. -/
theorem existsUnique_canonicalHighDemandWitness_residualProfile
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → ℕ} {col : B → ℕ}
    (matching : ConfigurationMatching row col) (U : ℕ)
    (hrowCap : ∀ a, row a ≤ U)
    (hcolCap : ∀ b, col b ≤ U) :
    ∃! witness : PrescribedDemandWitness
        (canonicalDemandOfMatching matching U) row col,
      ExtendsPrescribedDemandWitness matching witness ∧
        (∀ a, residualRowDegree witness a ≤ U) ∧
        (∀ b, residualColumnDegree witness b ≤ U) ∧
        ((∑ a, residualRowDegree witness a) =
          ∑ b, residualColumnDegree witness b) := by
  have htotal : (∑ a, row a) = ∑ b, col b := by
    calc
      (∑ a, row a) = Fintype.card (RowStub row) :=
        (card_rowStub row).symm
      _ = Fintype.card (ColumnStub col) :=
        Fintype.card_congr matching
      _ = ∑ b, col b := card_columnStub col
  obtain ⟨witness, hwitness, hunique⟩ :=
    existsUnique_canonicalHighDemandWitness row col matching U
  have hprofile := residualDegreeProfile_of_witness htotal witness
  refine ⟨witness, ?_, ?_⟩
  · refine ⟨hwitness, ?_⟩
    refine ⟨?_, ?_⟩
    · intro a
      exact (hprofile.1 a).trans (hrowCap a)
    · refine ⟨?_, hprofile.2.2⟩
      intro b
      exact (hprofile.2.1 b).trans (hcolCap b)
  · intro other hother
    exact hunique other hother.1

#print axioms existsUnique_canonicalHighDemandWitness_residualProfile

end Erdos625
