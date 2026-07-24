import Erdos625.Section6SignedSecondMomentIdentity
import Erdos625.Section8ProfileSkeletonWeight
import Erdos625.Section9ProfileAttachmentPolymerAssembly
import Erdos625.Section9ZeroResidualMatchingAttachment
import Erdos625.Section9AttachmentAsymptotics
import Erdos625.Section10AmplificationScales
import Mathlib.Tactic

/-!
# Section IX: concrete second-moment seed endpoint and analytic dependency cut

This module joins the exact Section VI normalized overlap law to the attained
canonical-demand decomposition of Sections VIII--IX.  In particular, the
canonical demand is the one *attained by the literal configuration matching*;
it is neither replaced by an independent table nor assigned a uniform law.

The first theorem below is an unconditional finite identity for the normalized
second moment.  The second records an unconditional polymer majorization,
including the zero-residual branch.

The declaration `MidpointCanonicalPolymerEstimate` is the dependency cut, not
an assumption of a theorem advertised as Proposition 9.2.  It states the first
missing analytic estimate with all quantifiers visible: after a concrete
midpoint profile sequence and its ordered realizations have been constructed,
the literal attained-demand polymer sum must have a nonnegative exponent which
is little-o of `n / log(n)^4`.  No theorem in this file asserts that declaration.
-/

namespace Erdos625

open Filter MeasureTheory
open scoped BigOperators ENNReal Topology

noncomputable section

/-- The literal attained-canonical-demand attachment sum.  The incidence is
its exact labelled-witness mass and each residual factor retains the
cap/no-return indicator through `profileHighSkeletonAttachment`. -/
noncomputable def midpointCanonicalAttachmentSum
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (U : Nat) : ENNReal :=
  ∑ demand : ProfileCanonicalHighSkeleton k U,
    profileHighSkeletonContribution row₀ U demand

/-- The literal attained-demand polymer majorant.  This is not a product-law
surrogate: the sum ranges over `canonicalDemandImage`, and each summand carries
its exact labelled-witness incidence. -/
noncomputable def midpointCanonicalPolymerSum
    {b n : Nat} {k : ColoringProfile b}
    (_row₀ : OrderedProfilePartition n k) (U : Nat) : ENNReal :=
  ∑ demand : ProfileCanonicalHighSkeleton k U,
    (canonicalDemandLocalReward demand : ENNReal) *
      (labelledWitnessIncidence demand.1 (profileBlockMargin k)
        (profileBlockMargin k) *
        canonicalDemandPolymerMajorant
          (profileBlockMargin k) (profileBlockMargin k) U demand)

/-- The literal uniform ordered-column expectation is the corresponding
cardinality-normalized finite sum. -/
lemma sum_uniformOrderedProfile_reward_eq_div
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) :
    (∑ column : OrderedProfilePartition n k,
      uniformOrderedProfilePartition row₀ column *
        (signedOverlapReward
          (profileOverlapTableOfOrderedPair row₀ column).tableNat : ENNReal)) =
      (∑ column : OrderedProfilePartition n k,
        (signedOverlapReward
          (profileOverlapTableOfOrderedPair row₀ column).tableNat : ENNReal)) /
        (Fintype.card (OrderedProfilePartition n k) : ENNReal) := by
  unfold uniformOrderedProfilePartition
  simp only [PMF.uniformOfFintype_apply]
  rw [ENNReal.div_eq_inv_mul, Finset.mul_sum]

/-- Unconditional finite endpoint: the graph-level normalized signed second
moment is exactly the attained canonical-demand attachment sum. -/
theorem normalizedSignedProfileSecondMoment_eq_midpointCanonicalAttachmentSum
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (U : Nat) (hU : 2 ≤ U) :
    signedProfileSecondMoment n k / signedProfileExpectation n k ^ 2 =
      midpointCanonicalAttachmentSum row₀ U := by
  calc
    signedProfileSecondMoment n k / signedProfileExpectation n k ^ 2 =
        signedProfileSecondMomentTableSumENNReal row₀ :=
      normalizedSignedProfileSecondMoment_eq_tableSum row₀
    _ = (∑ column : OrderedProfilePartition n k,
          (signedOverlapReward
            (profileOverlapTableOfOrderedPair row₀ column).tableNat : ENNReal)) /
          (Fintype.card (OrderedProfilePartition n k) : ENNReal) :=
      (orderedSignedOverlapRewardAverage_eq_tableSum row₀).symm
    _ = ∑ column : OrderedProfilePartition n k,
          uniformOrderedProfilePartition row₀ column *
            (signedOverlapReward
              (profileOverlapTableOfOrderedPair row₀ column).tableNat : ENNReal) :=
      (sum_uniformOrderedProfile_reward_eq_div row₀).symm
    _ = midpointCanonicalAttachmentSum row₀ U := by
      exact sum_uniformProfile_signedOverlapReward_eq_sum_profileHighSkeletonContribution
        row₀ U hU

/-- The exact normalized second moment is bounded by the literal attained-demand
polymer sum in both residual regimes. -/
theorem normalizedSignedProfileSecondMoment_le_midpointCanonicalPolymerSum
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (U : Nat) (hU : 2 ≤ U)
    (hcap : ∀ a : ProfileBlockIndex k, profileBlockMargin k a ≤ U) :
    signedProfileSecondMoment n k / signedProfileExpectation n k ^ 2 ≤
      midpointCanonicalPolymerSum row₀ U := by
  calc
    signedProfileSecondMoment n k / signedProfileExpectation n k ^ 2 =
        ∑ column : OrderedProfilePartition n k,
          uniformOrderedProfilePartition row₀ column *
            (signedOverlapReward
              (profileOverlapTableOfOrderedPair row₀ column).tableNat : ENNReal) := by
      rw [normalizedSignedProfileSecondMoment_eq_midpointCanonicalAttachmentSum
        row₀ U hU]
      exact (sum_uniformProfile_signedOverlapReward_eq_sum_profileHighSkeletonContribution
        row₀ U hU).symm
    _ ≤ midpointCanonicalPolymerSum row₀ U := by
      exact sum_uniformProfile_signedOverlapReward_le_skeletonPolymerSum_unconditional
        row₀ U hU hcap

/-- A finite explicit exponential endpoint.  This theorem performs no
analytic estimation: its premises are exactly the finite polymer bound proved
above and a displayed bound on the literal canonical polymer sum. -/
theorem normalizedSignedProfileSecondMoment_le_exp_of_polymerSum
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (U : Nat) (hU : 2 ≤ U)
    (Lambda : Real)
    (hcap : ∀ a : ProfileBlockIndex k, profileBlockMargin k a ≤ U)
    (hpolymer : midpointCanonicalPolymerSum row₀ U ≤
      ENNReal.ofReal (Real.exp Lambda)) :
    signedProfileSecondMoment n k / signedProfileExpectation n k ^ 2 ≤
      ENNReal.ofReal (Real.exp Lambda) := by
  exact (normalizedSignedProfileSecondMoment_le_midpointCanonicalPolymerSum
    row₀ U hU hcap).trans hpolymer

/-- **Exact first missing analytic estimate.**  For a proposed concrete
midpoint profile sequence, this asks for one explicit exponent sequence which
simultaneously bounds the full attained-demand polymer sum, is eventually
nonnegative, and is little-o of the Section X amplification scale.

The quantification over every `n` in the exponential estimate is deliberate;
only nonnegativity and the asymptotic comparison are eventual.  The canonical
demand law remains inside `midpointCanonicalPolymerSum`.
-/
def MidpointCanonicalPolymerEstimate
    (b U : Nat → Nat)
    (k : (n : Nat) → ColoringProfile (b n))
    (row₀ : (n : Nat) → OrderedProfilePartition n (k n))
    (Lambda : Nat → Real) : Prop :=
  (∀ n,
    midpointCanonicalPolymerSum (row₀ n) (U n) ≤
      ENNReal.ofReal (Real.exp (Lambda n))) ∧
  (∀ᶠ n in atTop, 0 ≤ Lambda n) ∧
  Lambda =o[atTop] amplificationBase

/-- Once the dependency-cut estimate is supplied, the requested second-moment
bound and both stated properties of its exponent follow without any further
probabilistic or quotient assumptions. -/
theorem midpoint_secondMoment_seed_of_canonicalPolymerEstimate
    (b U : Nat → Nat)
    (k : (n : Nat) → ColoringProfile (b n))
    (row₀ : (n : Nat) → OrderedProfilePartition n (k n))
    (Lambda : Nat → Real)
    (hU : ∀ n, 2 ≤ U n)
    (hcap : ∀ n (a : ProfileBlockIndex (k n)),
      profileBlockMargin (k n) a ≤ U n)
    (hEstimate : MidpointCanonicalPolymerEstimate b U k row₀ Lambda) :
    (∀ n,
      signedProfileSecondMoment n (k n) /
          signedProfileExpectation n (k n) ^ 2 ≤
        ENNReal.ofReal (Real.exp (Lambda n))) ∧
      (∀ᶠ n in atTop, 0 ≤ Lambda n) ∧
      Lambda =o[atTop] amplificationBase := by
  refine ⟨fun n => ?_, hEstimate.2⟩
  exact normalizedSignedProfileSecondMoment_le_exp_of_polymerSum
    (row₀ n) (U n) (hU n) (Lambda n) (hcap n) (hEstimate.1 n)

#print axioms normalizedSignedProfileSecondMoment_eq_midpointCanonicalAttachmentSum
#print axioms normalizedSignedProfileSecondMoment_le_midpointCanonicalPolymerSum
#print axioms normalizedSignedProfileSecondMoment_le_exp_of_polymerSum
#print axioms midpoint_secondMoment_seed_of_canonicalPolymerEstimate

end

end Erdos625
