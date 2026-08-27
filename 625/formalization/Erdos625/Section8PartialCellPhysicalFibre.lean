import Erdos625.Section8EndpointPhysicalBlockReverse
import Mathlib.Tactic

/-!
# Section VIII: exact partial-cell physical fibres

Fix one endpoint block pairing.  A deficit vector lowers the full multiplicity
in each selected cell from `m_e` to `j_e = m_e - h_e`.  The literal local
physical data are then independent `SingleCellStubMatching` fibres, one per
selected block pair.

This module proves their exact finite cardinality and attaches the common local
signed reward and the single ambient falling-factorial normalization.  It is
the aggregate local-fibre identity needed before any all-deficit comparison.
It does not identify these data with the global attained canonical-demand
family.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- Full endpoint multiplicity in one selected block cell. -/
def fourEndpointCellFullMultiplicity
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)} {L : FourEndpointFullTable}
    (P : FourEndpointBlockPairing alpha hAlpha k L)
    (e : ↥P.1.edges) : Nat :=
  fourEndpointOverlapSize alpha hAlpha e.1.1.1 e.1.2.1

/-- Actual multiplicity obtained by subtracting the selected deficit. -/
def fourEndpointCellMultiplicityOfDeficit
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)} {L : FourEndpointFullTable}
    (P : FourEndpointBlockPairing alpha hAlpha k L)
    (deficit : ∀ _e : ↥P.1.edges, Nat)
    (e : ↥P.1.edges) : Nat :=
  fourEndpointCellFullMultiplicity alpha hAlpha P e - deficit e

/-- The local partial physical matching in one selected block pair. -/
abbrev FourEndpointSelectedCellPartialStubMatching
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)} {L : FourEndpointFullTable}
    (P : FourEndpointBlockPairing alpha hAlpha k L)
    (deficit : ∀ _e : ↥P.1.edges, Nat)
    (e : ↥P.1.edges) :=
  SingleCellStubMatching
    (fourEndpointSize alpha hAlpha e.1.1.1)
    (fourEndpointSize alpha hAlpha e.1.2.1)
    (fourEndpointCellMultiplicityOfDeficit alpha hAlpha P deficit e)

/-- Product of the independent literal partial-stub-matching fibres. -/
abbrev FourEndpointPartialStubDecoration
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)} {L : FourEndpointFullTable}
    (P : FourEndpointBlockPairing alpha hAlpha k L)
    (deficit : ∀ _e : ↥P.1.edges, Nat) :=
  ∀ e : ↥P.1.edges,
    FourEndpointSelectedCellPartialStubMatching
      alpha hAlpha P deficit e

/-- Product of the local `j_e!` denominators. -/
def fourEndpointPartialCellFactorialProduct
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)} {L : FourEndpointFullTable}
    (P : FourEndpointBlockPairing alpha hAlpha k L)
    (deficit : ∀ _e : ↥P.1.edges, Nat) : Nat :=
  ∏ e : ↥P.1.edges,
    (fourEndpointCellMultiplicityOfDeficit alpha hAlpha P deficit e).factorial

/-- Product of the two descending-factorial stub selections in each cell. -/
def fourEndpointPartialCellSelectionProduct
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)} {L : FourEndpointFullTable}
    (P : FourEndpointBlockPairing alpha hAlpha k L)
    (deficit : ∀ _e : ↥P.1.edges, Nat) : Nat :=
  ∏ e : ↥P.1.edges,
    (fourEndpointSize alpha hAlpha e.1.1.1).descFactorial
        (fourEndpointCellMultiplicityOfDeficit alpha hAlpha P deficit e) *
      (fourEndpointSize alpha hAlpha e.1.2.1).descFactorial
        (fourEndpointCellMultiplicityOfDeficit alpha hAlpha P deficit e)

/-- Exact cross-multiplied cardinality of the local partial physical fibre. -/
theorem card_fourEndpointPartialStubDecoration_mul_factorials
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)} {L : FourEndpointFullTable}
    (P : FourEndpointBlockPairing alpha hAlpha k L)
    (deficit : ∀ _e : ↥P.1.edges, Nat) :
    Fintype.card
        (FourEndpointPartialStubDecoration alpha hAlpha P deficit) *
      fourEndpointPartialCellFactorialProduct alpha hAlpha P deficit =
        fourEndpointPartialCellSelectionProduct alpha hAlpha P deficit := by
  classical
  rw [Fintype.card_pi]
  unfold fourEndpointPartialCellFactorialProduct
    fourEndpointPartialCellSelectionProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _he
  exact card_singleCellStubMatching_mul_factorial
    (fourEndpointSize alpha hAlpha e.1.1.1)
    (fourEndpointSize alpha hAlpha e.1.2.1)
    (fourEndpointCellMultiplicityOfDeficit alpha hAlpha P deficit e)

/-- The product of factorial denominators is positive. -/
theorem fourEndpointPartialCellFactorialProduct_ne_zero
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)} {L : FourEndpointFullTable}
    (P : FourEndpointBlockPairing alpha hAlpha k L)
    (deficit : ∀ _e : ↥P.1.edges, Nat) :
    fourEndpointPartialCellFactorialProduct alpha hAlpha P deficit ≠ 0 := by
  unfold fourEndpointPartialCellFactorialProduct
  exact Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _

/-- Division form of the exact local partial-fibre cardinality in `ENNReal`. -/
theorem ennreal_card_fourEndpointPartialStubDecoration_eq_quotient
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)} {L : FourEndpointFullTable}
    (P : FourEndpointBlockPairing alpha hAlpha k L)
    (deficit : ∀ _e : ↥P.1.edges, Nat) :
    (Fintype.card
      (FourEndpointPartialStubDecoration alpha hAlpha P deficit) : ENNReal) =
      (fourEndpointPartialCellSelectionProduct alpha hAlpha P deficit : ENNReal) /
        (fourEndpointPartialCellFactorialProduct alpha hAlpha P deficit : ENNReal) := by
  apply (ENNReal.eq_div_iff
    (Nat.cast_ne_zero.mpr
      (fourEndpointPartialCellFactorialProduct_ne_zero
        alpha hAlpha P deficit))
    (ENNReal.natCast_ne_top _)).2
  simpa only [Nat.cast_mul, mul_comm] using
    congrArg (fun x : Nat => (x : ENNReal))
      (card_fourEndpointPartialStubDecoration_mul_factorials
        alpha hAlpha P deficit)

/-- Total exposed multiplicity of the selected partial cells. -/
def fourEndpointPartialTotalMultiplicity
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)} {L : FourEndpointFullTable}
    (P : FourEndpointBlockPairing alpha hAlpha k L)
    (deficit : ∀ _e : ↥P.1.edges, Nat) : Nat :=
  ∑ e : ↥P.1.edges,
    fourEndpointCellMultiplicityOfDeficit alpha hAlpha P deficit e

/-- Product of the local signed rewards at the actual multiplicities. -/
def fourEndpointPartialRewardProduct
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)} {L : FourEndpointFullTable}
    (P : FourEndpointBlockPairing alpha hAlpha k L)
    (deficit : ∀ _e : ↥P.1.edges, Nat) : ENNReal :=
  ∏ e : ↥P.1.edges,
    (localSignRewardNat
      (fourEndpointCellMultiplicityOfDeficit alpha hAlpha P deficit e) : ENNReal)

/-- Common contribution of one literal local partial-stub decoration. -/
def fourEndpointPartialAtomWeight
    (n alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)} {L : FourEndpointFullTable}
    (P : FourEndpointBlockPairing alpha hAlpha k L)
    (deficit : ∀ _e : ↥P.1.edges, Nat) : ENNReal :=
  fourEndpointPartialRewardProduct alpha hAlpha P deficit /
    ((n.descFactorial
      (fourEndpointPartialTotalMultiplicity alpha hAlpha P deficit) : Nat) :
        ENNReal)

/-- Aggregate weight after summing the entire local partial physical fibre. -/
def fourEndpointPartialAggregateWeight
    (n alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)} {L : FourEndpointFullTable}
    (P : FourEndpointBlockPairing alpha hAlpha k L)
    (deficit : ∀ _e : ↥P.1.edges, Nat) : ENNReal :=
  ((fourEndpointPartialCellSelectionProduct alpha hAlpha P deficit : Nat) :
      ENNReal) /
    ((fourEndpointPartialCellFactorialProduct alpha hAlpha P deficit : Nat) :
      ENNReal) *
      fourEndpointPartialAtomWeight n alpha hAlpha P deficit

/-- Summing the common atom over the literal local partial fibre gives the
aggregate weight with exactly one local factorial denominator per cell. -/
theorem sum_fourEndpointPartialAtomWeight_eq_aggregateWeight
    (n alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)} {L : FourEndpointFullTable}
    (P : FourEndpointBlockPairing alpha hAlpha k L)
    (deficit : ∀ _e : ↥P.1.edges, Nat) :
    (∑ _ : FourEndpointPartialStubDecoration alpha hAlpha P deficit,
      fourEndpointPartialAtomWeight n alpha hAlpha P deficit) =
        fourEndpointPartialAggregateWeight n alpha hAlpha P deficit := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [ennreal_card_fourEndpointPartialStubDecoration_eq_quotient]
  rfl

#print axioms card_fourEndpointPartialStubDecoration_mul_factorials
#print axioms ennreal_card_fourEndpointPartialStubDecoration_eq_quotient
#print axioms sum_fourEndpointPartialAtomWeight_eq_aggregateWeight

end

end Erdos625
