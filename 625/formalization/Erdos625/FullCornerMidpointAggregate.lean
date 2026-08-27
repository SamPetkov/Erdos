import Erdos625.FullCornerAggregateBound
import Erdos625.FullCornerMidpointMuActivity
import Mathlib.Tactic

/-!
# Eventual midpoint full-corner aggregate

This module instantiates the finite full-corner aggregate theorem with the
canonical midpoint activity and its separately proved uniform asymptotic.
It deliberately keeps the complete first-moment factor: removing that factor
uses the separate first-moment lower bound.  It also proves no empty-corner,
central-range, rounding-existence, skeleton, or attachment statement.
-/

namespace Erdos625

open Filter
open scoped BigOperators Topology

noncomputable section

set_option autoImplicit false

private lemma midpointFullCorner_selectedVertexMass_eq
    (n alpha K : Nat) (hround : MidpointRoundingAdmissible n alpha K) :
    selectedVertexMass (midpointPartialDiagonalSize alpha)
        (midpointMultiplicity n alpha K) = n := by
  have hcd :=
    midpointMultiplicity_count_deficit_intDisplacement n alpha K hround
  have hcount := hcd.1
  have hmom := hcd.2.1
  have hAlpha : 5 < alpha := hround.1
  have hnK : n ≤ alpha * K := hround.2.2.1
  rw [midpointDeficit] at hmom
  have hDeficitLe : ∀ i : Fin 4, fourDeficit i ≤ alpha := by
    intro i
    have hi := i.isLt
    simp only [fourDeficit]
    omega
  have hsplit :
      (∑ i : Fin 4,
          midpointPartialDiagonalSize alpha i *
            midpointMultiplicity n alpha K i) +
        (∑ i : Fin 4,
          tangentDeficitNat i * midpointMultiplicity n alpha K i) =
          alpha * K := by
    have hstep :
        (∑ i : Fin 4,
            midpointPartialDiagonalSize alpha i *
              midpointMultiplicity n alpha K i) +
          (∑ i : Fin 4,
            tangentDeficitNat i * midpointMultiplicity n alpha K i) =
            ∑ i : Fin 4,
              alpha * midpointMultiplicity n alpha K i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have ht : tangentDeficitNat i = fourDeficit i := rfl
      simp only [midpointPartialDiagonalSize, ht, ← Nat.add_mul]
      rw [Nat.sub_add_cancel (hDeficitLe i)]
    rw [hstep, ← Finset.mul_sum, hcount]
  unfold selectedVertexMass
  obtain ⟨P, hP⟩ : ∃ P, alpha * K = P := ⟨_, rfl⟩
  rw [hP] at hsplit hmom hnK
  omega

/-- The canonical filtered full-corner partial-diagonal aggregate, still
scaled by its complete signed first moment, is eventually at most
`exp epsilon`, uniformly over every supplied admissible midpoint rounding. -/
theorem eventually_sum_midpointPartialDiagonalWeight_fullCorner_filter_mul_complete_le_exp
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∀ᶠ n : Nat in atTop,
      ∀ K : Nat,
        MidpointRoundingAdmissible n (phaseNat n) K →
          (∑ ell ∈
              (partialSubprofileBox
                (midpointMultiplicity n (phaseNat n) K)).filter
                  (fun ell =>
                    n - selectedVertexMass
                        (midpointPartialDiagonalSize (phaseNat n)) ell ≤
                      n / 32),
            partialDiagonalWeight n
              (midpointPartialDiagonalSize (phaseNat n))
              (midpointMultiplicity n (phaseNat n) K) ell) *
              completeSignedFirstMoment
                (midpointPartialDiagonalSize (phaseNat n))
                (midpointMultiplicity n (phaseNat n) K) ≤
            Real.exp epsilon := by
  filter_upwards
    [eventually_sum_midpointPartialDiagonal_fullCorner_mu_activity_le
      epsilon hepsilon] with n hactivity
  intro K hround
  have hmass :
      selectedVertexMass (midpointPartialDiagonalSize (phaseNat n))
          (midpointMultiplicity n (phaseNat n) K) = n :=
    midpointFullCorner_selectedVertexMass_eq n (phaseNat n) K hround
  have hfinite :=
    sum_partialDiagonalWeight_fullCorner_filter_mul_complete_le_exp_sum_of_mu_cap
      n (n / 32)
      (midpointPartialDiagonalSize (phaseNat n))
      (midpointMultiplicity n (phaseNat n) K)
      (fun i : Fin 4 =>
        2 * (midpointMultiplicity n (phaseNat n) K i : Real) *
          mu (n / 32 + midpointPartialDiagonalSize (phaseNat n) i)
            (midpointPartialDiagonalSize (phaseNat n) i))
      hmass (fun _ => le_rfl)
  exact hfinite.trans (Real.exp_le_exp.mpr (hactivity K hround))

end

end Erdos625
