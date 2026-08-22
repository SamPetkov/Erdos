import Erdos625.FourDeficitFirstMomentStirlingBridge
import Erdos625.MidpointRoundedFourSizeEntropyLoss
import Mathlib.Tactic

/-!
# The tangent-rounded signed four-size objective bridge

This module identifies the discrete objective of the actual tangent-rounded
four-deficit profile with the signed finite four-size objective in which the
Gibbs entropy is replaced by the rounded entropy score.  The previously proved
`50 / 7` relative-entropy estimate then controls the exact difference.

Combining this with the four-coordinate Stirling bridge gives the finite
first-moment comparison required by E625-10:

`|log M_n - signedFourSizeObjective n alpha K|
  <= 4 * factorialLogErrorBound n + 50 / 7`.

No phase-root estimate, partial-diagonal bound, second moment, or final Erdős
statement is used.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- Entropy plus exact finite residual score evaluated at the actual natural
midpoint multiplicity proportions. -/
noncomputable def midpointRoundedFourSizeEntropyScore
    (n alpha K : Nat) : Real :=
  -(∑ i : Fin 4,
      midpointRoundedProportion n alpha K i *
        Real.log (midpointRoundedProportion n alpha K i)) +
    ∑ i : Fin 4,
      midpointRoundedProportion n alpha K i * fourDeficitScore alpha i

/-- The named finite loss from the KL-rounding module is exactly finite entropy
minus the rounded entropy score used by this bridge. -/
theorem midpointRoundedFourSizeEntropyLoss_eq_sub_score
    (n alpha K : Nat) :
    midpointRoundedFourSizeEntropyLoss n alpha K =
      fourSizeFiniteEntropy alpha (fourSizeTarget n alpha (K : Real)) -
        midpointRoundedFourSizeEntropyScore n alpha K := by
  rfl

/-- Admissibility forces every corrected natural multiplicity to be strictly
positive.  Quantitatively it is at least nine, since its optimizer coordinate
is at least fourteen and the correction displacement is at most five. -/
theorem midpointMultiplicity_pos_of_admissible
    (n alpha K : Nat) (h : MidpointRoundingAdmissible n alpha K)
    (i : Fin 4) :
    0 < midpointMultiplicity n alpha K i := by
  have hDisp := midpointMultiplicity_uniform_displacement n alpha K h i
  have hLower := h.2.2.2.2 i
  rw [abs_le] at hDisp
  have hReal : (0 : Real) < midpointMultiplicity n alpha K i := by
    linarith
  exact_mod_cast hReal

/-- The natural multiplicity is exactly `K` times its rounded proportion. -/
theorem midpointMultiplicity_cast_eq_mul_roundedProportion
    (n alpha K : Nat) (hK : 0 < K) (i : Fin 4) :
    (midpointMultiplicity n alpha K i : Real) =
      (K : Real) * midpointRoundedProportion n alpha K i := by
  unfold midpointRoundedProportion
  have hKReal : (K : Real) ≠ 0 := by exact_mod_cast hK.ne'
  field_simp [hKReal]

/-- The multiplicity logarithm sum splits into the total-count logarithm and
the normalized rounded entropy term. -/
theorem sum_midpointMultiplicity_mul_log_eq
    (n alpha K : Nat) (h : MidpointRoundingAdmissible n alpha K) :
    (∑ i : Fin 4,
        (midpointMultiplicity n alpha K i : Real) *
          Real.log (midpointMultiplicity n alpha K i : Real)) =
      (K : Real) * Real.log (K : Real) +
        (K : Real) *
          ∑ i : Fin 4,
            midpointRoundedProportion n alpha K i *
              Real.log (midpointRoundedProportion n alpha K i) := by
  have hK : 0 < K := h.2.1
  have hKReal : 0 < (K : Real) := by exact_mod_cast hK
  have hSum := sum_midpointRoundedProportion n alpha K h
  calc
    (∑ i : Fin 4,
        (midpointMultiplicity n alpha K i : Real) *
          Real.log (midpointMultiplicity n alpha K i : Real)) =
      ∑ i : Fin 4,
        ((K : Real) * midpointRoundedProportion n alpha K i) *
          (Real.log (K : Real) +
            Real.log (midpointRoundedProportion n alpha K i)) := by
        apply Finset.sum_congr rfl
        intro i _hi
        have hmPos : 0 < midpointMultiplicity n alpha K i :=
          midpointMultiplicity_pos_of_admissible n alpha K h i
        have hrPos : 0 < midpointRoundedProportion n alpha K i :=
          midpointRoundedProportion_pos_of_admissible n alpha K h i
        rw [← Real.log_mul (ne_of_gt hKReal) (ne_of_gt hrPos),
          ← midpointMultiplicity_cast_eq_mul_roundedProportion n alpha K hK i]
    _ = (∑ i : Fin 4,
          ((K : Real) * Real.log (K : Real)) *
            midpointRoundedProportion n alpha K i) +
        ∑ i : Fin 4,
          (K : Real) *
            (midpointRoundedProportion n alpha K i *
              Real.log (midpointRoundedProportion n alpha K i)) := by
        calc
          _ = ∑ i : Fin 4,
              (((K : Real) * Real.log (K : Real)) *
                  midpointRoundedProportion n alpha K i +
                (K : Real) *
                  (midpointRoundedProportion n alpha K i *
                    Real.log (midpointRoundedProportion n alpha K i))) := by
                apply Finset.sum_congr rfl
                intro i _hi
                ring
          _ = _ := by rw [Finset.sum_add_distrib]
    _ = (K : Real) * Real.log (K : Real) *
          (∑ i : Fin 4, midpointRoundedProportion n alpha K i) +
        (K : Real) *
          ∑ i : Fin 4,
            midpointRoundedProportion n alpha K i *
              Real.log (midpointRoundedProportion n alpha K i) := by
        rw [Finset.mul_sum, Finset.mul_sum]
    _ = _ := by rw [hSum]; ring

/-- Exact residual-score scaling from integer multiplicities to rounded
proportions. -/
theorem sum_midpointMultiplicity_mul_fourDeficitScore_eq
    (n alpha K : Nat) (h : MidpointRoundingAdmissible n alpha K) :
    (∑ i : Fin 4,
        (midpointMultiplicity n alpha K i : Real) *
          fourDeficitScore alpha i) =
      (K : Real) *
        ∑ i : Fin 4,
          midpointRoundedProportion n alpha K i *
            fourDeficitScore alpha i := by
  have hK : 0 < K := h.2.1
  calc
    (∑ i : Fin 4,
        (midpointMultiplicity n alpha K i : Real) *
          fourDeficitScore alpha i) =
      ∑ i : Fin 4,
        (K : Real) *
          (midpointRoundedProportion n alpha K i *
            fourDeficitScore alpha i) := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [midpointMultiplicity_cast_eq_mul_roundedProportion n alpha K hK i]
        ring
    _ = _ := by rw [Finset.mul_sum]

/-- The exact class cost at size `alpha - d` is the affine deficit cost plus
the finite residual score at deficit `d`. -/
theorem neg_coloringClassLogCost_fourDeficit_eq
    (alpha : Nat) (hAlpha : 5 < alpha) (i : Fin 4) :
    -coloringClassLogCost (alpha - fourDeficit i) =
      profileDeficitAffineA alpha +
        profileDeficitAffineB alpha * (fourDeficit i : Real) +
          fourDeficitScore alpha i := by
  have hDecomp :=
    profileDualScore_eq_deficitAffine_add_residual alpha
      (fourDeficitCoordinate alpha hAlpha i)
  rw [profileDeficit_fourDeficitCoordinate,
    profileDeficitResidualScore_fourDeficitCoordinate] at hDecomp
  unfold profileDualScore at hDecomp
  rw [fourDeficitCoordinate_val_add_one_eq] at hDecomp
  exact hDecomp

/-- The discrete objective of a four-deficit embedding has the literal
four-coordinate manuscript form. -/
theorem profileDiscreteObjective_fourDeficitEmbedding_eq
    (n alpha : Nat) (hAlpha : 5 < alpha) (m : Fin 4 → Nat) :
    profileDiscreteObjective n (fourDeficitEmbedding alpha hAlpha m) =
      (n : Real) * Real.log (n : Real) - n +
        (((∑ i : Fin 4, m i : Nat) : Real)) -
        ∑ i : Fin 4,
          (m i : Real) *
            (Real.log (m i : Real) +
              coloringClassLogCost (alpha - fourDeficit i)) := by
  let k : ColoringProfile (alpha + 1) :=
    fourDeficitEmbedding alpha hAlpha m
  have hInvariants := fourDeficitEmbedding_profile_invariants alpha hAlpha m
  have hEntropy := sum_apply_fourDeficitEmbedding alpha hAlpha m
    (fun t : Nat => (t : Real) * Real.log (t : Real)) (by simp)
  have hCost := sum_fourDeficitEmbedding_cast_mul alpha hAlpha m
    (fun j : Fin (alpha + 1) => coloringClassLogCost (j.1 + 1))
  have hCost' :
      (∑ j : Fin (alpha + 1),
          (k j : Real) * coloringClassLogCost (j.1 + 1)) =
        ∑ i : Fin 4,
          (m i : Real) *
            coloringClassLogCost (alpha - fourDeficit i) := by
    rw [show (∑ j : Fin (alpha + 1),
        (k j : Real) * coloringClassLogCost (j.1 + 1)) =
        ∑ i : Fin 4,
          (m i : Real) *
            coloringClassLogCost
              ((fourDeficitCoordinate alpha hAlpha i).1 + 1) by
      simpa only [k] using hCost]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [fourDeficitCoordinate_val_add_one_eq]
  have hSum :
      (∑ j : Fin (alpha + 1),
        (k j : Real) *
          (Real.log (k j : Real) + coloringClassLogCost (j.1 + 1))) =
      ∑ i : Fin 4,
        (m i : Real) *
          (Real.log (m i : Real) +
            coloringClassLogCost (alpha - fourDeficit i)) := by
    calc
      (∑ j : Fin (alpha + 1),
        (k j : Real) *
          (Real.log (k j : Real) + coloringClassLogCost (j.1 + 1))) =
        (∑ j : Fin (alpha + 1),
          (k j : Real) * Real.log (k j : Real)) +
        ∑ j : Fin (alpha + 1),
          (k j : Real) * coloringClassLogCost (j.1 + 1) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j _hj
            ring
      _ = (∑ i : Fin 4, (m i : Real) * Real.log (m i : Real)) +
          ∑ i : Fin 4,
            (m i : Real) *
              coloringClassLogCost (alpha - fourDeficit i) := by
            rw [show (∑ j : Fin (alpha + 1),
                (k j : Real) * Real.log (k j : Real)) =
              ∑ i : Fin 4, (m i : Real) * Real.log (m i : Real) by
                simpa only [k] using hEntropy,
              hCost']
      _ = _ := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
  rw [profileDiscreteObjective_eq_profileManuscriptObjective n k]
  unfold profileManuscriptObjective
  rw [show (ColoringProfile.partCount k : Real) =
      (((∑ i : Fin 4, m i : Nat) : Real)) by
        exact_mod_cast hInvariants.1,
    hSum]

/-- The negative class-cost sum of the midpoint multiplicities is exactly the
affine target contribution plus the rounded residual-score contribution. -/
theorem neg_sum_midpointMultiplicity_mul_coloringClassLogCost_eq
    (n alpha K : Nat) (h : MidpointRoundingAdmissible n alpha K) :
    -(∑ i : Fin 4,
        (midpointMultiplicity n alpha K i : Real) *
          coloringClassLogCost (alpha - fourDeficit i)) =
      (K : Real) *
        (profileDeficitAffineA alpha +
          profileDeficitAffineB alpha *
            fourSizeTarget n alpha (K : Real)) +
      (K : Real) *
        ∑ i : Fin 4,
          midpointRoundedProportion n alpha K i *
            fourDeficitScore alpha i := by
  have hK : 0 < K := h.2.1
  have hn : n ≤ alpha * K := h.2.2.1
  have hConservation :=
    midpointMultiplicity_count_deficit_intDisplacement n alpha K h
  have hCountReal :
      (∑ i : Fin 4,
        (midpointMultiplicity n alpha K i : Real)) = (K : Real) := by
    exact_mod_cast hConservation.1
  have hMomentNat :
      (∑ i : Fin 4,
        fourDeficit i * midpointMultiplicity n alpha K i) =
        midpointDeficit n alpha K := by
    simpa [tangentDeficitNat, fourDeficit] using hConservation.2.1
  have hMomentReal :
      (∑ i : Fin 4,
        (fourDeficit i : Real) *
          (midpointMultiplicity n alpha K i : Real)) =
        (midpointDeficit n alpha K : Real) := by
    exact_mod_cast hMomentNat
  have hDeficitReal :
      (midpointDeficit n alpha K : Real) =
        (K : Real) * fourSizeTarget n alpha (K : Real) := by
    simpa only [midpointDeficit] using
      deficit_cast_eq_parts_mul_fourSizeTarget n alpha K hK hn
  have hScore :=
    sum_midpointMultiplicity_mul_fourDeficitScore_eq n alpha K h
  calc
    -(∑ i : Fin 4,
        (midpointMultiplicity n alpha K i : Real) *
          coloringClassLogCost (alpha - fourDeficit i)) =
      ∑ i : Fin 4,
        (midpointMultiplicity n alpha K i : Real) *
          (-coloringClassLogCost (alpha - fourDeficit i)) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro i _hi
            ring
    _ = ∑ i : Fin 4,
        (midpointMultiplicity n alpha K i : Real) *
          (profileDeficitAffineA alpha +
            profileDeficitAffineB alpha * (fourDeficit i : Real) +
              fourDeficitScore alpha i) := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [neg_coloringClassLogCost_fourDeficit_eq alpha h.1 i]
    _ = (∑ i : Fin 4,
          profileDeficitAffineA alpha *
            (midpointMultiplicity n alpha K i : Real)) +
        (∑ i : Fin 4,
          profileDeficitAffineB alpha *
            ((fourDeficit i : Real) *
              (midpointMultiplicity n alpha K i : Real))) +
        ∑ i : Fin 4,
          (midpointMultiplicity n alpha K i : Real) *
            fourDeficitScore alpha i := by
              calc
                _ = ∑ i : Fin 4,
                    (profileDeficitAffineA alpha *
                        (midpointMultiplicity n alpha K i : Real) +
                      profileDeficitAffineB alpha *
                        ((fourDeficit i : Real) *
                          (midpointMultiplicity n alpha K i : Real)) +
                      (midpointMultiplicity n alpha K i : Real) *
                        fourDeficitScore alpha i) := by
                          apply Finset.sum_congr rfl
                          intro i _hi
                          ring
                _ = _ := by
                  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = profileDeficitAffineA alpha *
          (∑ i : Fin 4,
            (midpointMultiplicity n alpha K i : Real)) +
        profileDeficitAffineB alpha *
          (∑ i : Fin 4,
            (fourDeficit i : Real) *
              (midpointMultiplicity n alpha K i : Real)) +
        ∑ i : Fin 4,
          (midpointMultiplicity n alpha K i : Real) *
            fourDeficitScore alpha i := by
              rw [Finset.mul_sum, Finset.mul_sum]
    _ = _ := by
      rw [hCountReal, hMomentReal, hDeficitReal, hScore]
      ring

/-- Exact identity in the named KL-loss convention exported by the rounding
module. -/
theorem signedFourSizeObjective_sub_midpointDiscrete_eq_namedEntropyLoss
    (n alpha K : Nat) (h : MidpointRoundingAdmissible n alpha K) :
    signedFourSizeObjective n alpha (K : Real) -
        ((K : Real) * q +
          profileDiscreteObjective n
            (fourDeficitEmbedding alpha h.1
              (midpointMultiplicity n alpha K))) =
      (K : Real) * midpointRoundedFourSizeEntropyLoss n alpha K := by
  have hCount :=
    (midpointMultiplicity_count_deficit_intDisplacement n alpha K h).1
  have hLog := sum_midpointMultiplicity_mul_log_eq n alpha K h
  have hClass :=
    neg_sum_midpointMultiplicity_mul_coloringClassLogCost_eq n alpha K h
  have hDiscrete :=
    profileDiscreteObjective_fourDeficitEmbedding_eq n alpha h.1
      (midpointMultiplicity n alpha K)
  have hCountCast :
      ((((∑ i : Fin 4, midpointMultiplicity n alpha K i : Nat) : Real))) =
        (K : Real) := by exact_mod_cast hCount
  have hCombined :
      (∑ i : Fin 4,
        (midpointMultiplicity n alpha K i : Real) *
          (Real.log (midpointMultiplicity n alpha K i : Real) +
            coloringClassLogCost (alpha - fourDeficit i))) =
        (∑ i : Fin 4,
          (midpointMultiplicity n alpha K i : Real) *
            Real.log (midpointMultiplicity n alpha K i : Real)) +
        ∑ i : Fin 4,
          (midpointMultiplicity n alpha K i : Real) *
            coloringClassLogCost (alpha - fourDeficit i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [signedFourSizeObjective, signedFourSizeObjectiveAtTarget,
    hDiscrete, hCountCast, hCombined]
  unfold midpointRoundedFourSizeEntropyLoss
  rw [hLog]
  have hClass' :
      (∑ i : Fin 4,
        (midpointMultiplicity n alpha K i : Real) *
          coloringClassLogCost (alpha - fourDeficit i)) =
      -((K : Real) *
          (profileDeficitAffineA alpha +
            profileDeficitAffineB alpha *
              fourSizeTarget n alpha (K : Real)) +
        (K : Real) *
          ∑ i : Fin 4,
            midpointRoundedProportion n alpha K i *
              fourDeficitScore alpha i) := by
    linarith [hClass]
  rw [hClass']
  ring

/-- Exact identity: the finite signed objective exceeds the rounded discrete
objective by precisely `K` times the four-size entropy loss of the rounded
proportions. -/
theorem signedFourSizeObjective_sub_midpointDiscrete_eq_entropyLoss
    (n alpha K : Nat) (h : MidpointRoundingAdmissible n alpha K) :
    signedFourSizeObjective n alpha (K : Real) -
        ((K : Real) * q +
          profileDiscreteObjective n
            (fourDeficitEmbedding alpha h.1
              (midpointMultiplicity n alpha K))) =
      (K : Real) *
        (fourSizeFiniteEntropy alpha
            (fourSizeTarget n alpha (K : Real)) -
          midpointRoundedFourSizeEntropyScore n alpha K) := by
  simpa [midpointRoundedFourSizeEntropyLoss_eq_sub_score] using
    signedFourSizeObjective_sub_midpointDiscrete_eq_namedEntropyLoss
      n alpha K h

/-- The exact signed objective/discrete objective gap is nonnegative and at
most `50 / 7`. -/
theorem signedFourSizeObjective_sub_midpointDiscrete_nonneg_and_le
    (n alpha K : Nat) (h : MidpointRoundingAdmissible n alpha K) :
    0 ≤ signedFourSizeObjective n alpha (K : Real) -
        ((K : Real) * q +
          profileDiscreteObjective n
            (fourDeficitEmbedding alpha h.1
              (midpointMultiplicity n alpha K))) ∧
    signedFourSizeObjective n alpha (K : Real) -
        ((K : Real) * q +
          profileDiscreteObjective n
            (fourDeficitEmbedding alpha h.1
              (midpointMultiplicity n alpha K))) ≤
      (50 / 7 : Real) := by
  rw [signedFourSizeObjective_sub_midpointDiscrete_eq_namedEntropyLoss
    n alpha K h]
  exact ⟨mul_midpointRoundedFourSizeEntropyLoss_nonneg n alpha K h,
    mul_midpointRoundedFourSizeEntropyLoss_le n alpha K h⟩

/-- The midpoint multiplicities have exact full vertex mass. -/
theorem midpointMultiplicity_vertexMass
    (n alpha K : Nat) (h : MidpointRoundingAdmissible n alpha K) :
    (∑ i : Fin 4,
      (alpha - fourDeficit i) * midpointMultiplicity n alpha K i) = n := by
  have hK : 0 < K := h.2.1
  have hn : n ≤ alpha * K := h.2.2.1
  have hConservation :=
    midpointMultiplicity_count_deficit_intDisplacement n alpha K h
  have hCountReal :
      (∑ i : Fin 4,
        (midpointMultiplicity n alpha K i : Real)) = (K : Real) := by
    exact_mod_cast hConservation.1
  have hMomentNat :
      (∑ i : Fin 4,
        fourDeficit i * midpointMultiplicity n alpha K i) =
        midpointDeficit n alpha K := by
    simpa [tangentDeficitNat, fourDeficit] using hConservation.2.1
  have hMomentReal :
      (∑ i : Fin 4,
        (fourDeficit i : Real) *
          (midpointMultiplicity n alpha K i : Real)) =
        (midpointDeficit n alpha K : Real) := by
    exact_mod_cast hMomentNat
  have hDeficitCast :
      (midpointDeficit n alpha K : Real) =
        (alpha : Real) * (K : Real) - (n : Real) := by
    unfold midpointDeficit
    rw [Nat.cast_sub hn, Nat.cast_mul]
  have hMassReal :
      ((∑ i : Fin 4,
        (alpha - fourDeficit i) * midpointMultiplicity n alpha K i : Nat) : Real) =
        (n : Real) := by
    calc
      ((∑ i : Fin 4,
        (alpha - fourDeficit i) * midpointMultiplicity n alpha K i : Nat) : Real) =
        ∑ i : Fin 4,
          (((alpha : Real) - (fourDeficit i : Real)) *
            (midpointMultiplicity n alpha K i : Real)) := by
              rw [Nat.cast_sum]
              apply Finset.sum_congr rfl
              intro i _hi
              have hDeficit : fourDeficit i ≤ alpha := by
                have hDeficitFive : fourDeficit i ≤ 5 := by
                  fin_cases i <;> norm_num [fourDeficit]
                exact hDeficitFive.trans (Nat.le_of_lt h.1)
              rw [Nat.cast_mul, Nat.cast_sub hDeficit]
      _ = ∑ i : Fin 4,
          ((alpha : Real) *
              (midpointMultiplicity n alpha K i : Real) -
            (fourDeficit i : Real) *
              (midpointMultiplicity n alpha K i : Real)) := by
                apply Finset.sum_congr rfl
                intro i _hi
                ring
      _ = (∑ i : Fin 4,
            (alpha : Real) *
              (midpointMultiplicity n alpha K i : Real)) -
          ∑ i : Fin 4,
            (fourDeficit i : Real) *
              (midpointMultiplicity n alpha K i : Real) := by
                rw [Finset.sum_sub_distrib]
      _ = (alpha : Real) *
            (∑ i : Fin 4,
              (midpointMultiplicity n alpha K i : Real)) -
          ∑ i : Fin 4,
            (fourDeficit i : Real) *
              (midpointMultiplicity n alpha K i : Real) := by
                rw [Finset.mul_sum]
      _ = (n : Real) := by
        rw [hCountReal, hMomentReal, hDeficitCast]
        ring
  exact_mod_cast hMassReal

/-- Complete finite E625-10 bridge: the logarithm of the exact real signed
first moment differs from the signed finite four-size objective by at most the
four-coordinate Stirling error plus the exact tangent-rounding entropy loss. -/
theorem abs_log_midpointPartialSignedFirstMoment_sub_signedFourSizeObjective_le
    (n alpha K : Nat) (h : MidpointRoundingAdmissible n alpha K) :
    |Real.log
        (partialSignedFirstMoment n
          (fun i : Fin 4 ↦ alpha - fourDeficit i)
          (midpointMultiplicity n alpha K)) -
        signedFourSizeObjective n alpha (K : Real)| ≤
      4 * factorialLogErrorBound n + 50 / 7 := by
  have hMass := midpointMultiplicity_vertexMass n alpha K h
  have hStirling :=
    abs_log_partialSignedFirstMoment_fourDeficit_sub_discreteObjective_le
      n alpha h.1 (midpointMultiplicity n alpha K) hMass
  have hCount :=
    (midpointMultiplicity_count_deficit_intDisplacement n alpha K h).1
  have hCountCast :
      ((((∑ i : Fin 4, midpointMultiplicity n alpha K i : Nat) : Real))) =
        (K : Real) := by
    exact_mod_cast hCount
  rw [hCountCast] at hStirling
  have hGap :=
    signedFourSizeObjective_sub_midpointDiscrete_nonneg_and_le n alpha K h
  let firstMomentLog : Real :=
    Real.log
      (partialSignedFirstMoment n
        (fun i : Fin 4 ↦ alpha - fourDeficit i)
        (midpointMultiplicity n alpha K))
  let discrete : Real :=
    (K : Real) * q +
      profileDiscreteObjective n
        (fourDeficitEmbedding alpha h.1
          (midpointMultiplicity n alpha K))
  let objective : Real := signedFourSizeObjective n alpha (K : Real)
  have hStirling' : |firstMomentLog - discrete| ≤
      4 * factorialLogErrorBound n := by
    simpa only [firstMomentLog, discrete] using hStirling
  have hGapNonneg : 0 ≤ objective - discrete := by
    simpa only [objective, discrete] using hGap.1
  have hGapLe : objective - discrete ≤ (50 / 7 : Real) := by
    simpa only [objective, discrete] using hGap.2
  have hDiscreteObjectiveAbs : |discrete - objective| ≤ (50 / 7 : Real) := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  calc
    |Real.log
        (partialSignedFirstMoment n
          (fun i : Fin 4 ↦ alpha - fourDeficit i)
          (midpointMultiplicity n alpha K)) -
        signedFourSizeObjective n alpha (K : Real)| =
      |(firstMomentLog - discrete) + (discrete - objective)| := by
        simp only [firstMomentLog, objective]
        congr 1
        ring
    _ ≤ |firstMomentLog - discrete| + |discrete - objective| :=
      abs_add_le _ _
    _ ≤ 4 * factorialLogErrorBound n + 50 / 7 :=
      add_le_add hStirling' hDiscreteObjectiveAbs

#print axioms midpointRoundedFourSizeEntropyLoss_eq_sub_score
#print axioms signedFourSizeObjective_sub_midpointDiscrete_eq_namedEntropyLoss
#print axioms signedFourSizeObjective_sub_midpointDiscrete_eq_entropyLoss
#print axioms signedFourSizeObjective_sub_midpointDiscrete_nonneg_and_le
#print axioms midpointMultiplicity_vertexMass
#print axioms abs_log_midpointPartialSignedFirstMoment_sub_signedFourSizeObjective_le

end

end Erdos625
