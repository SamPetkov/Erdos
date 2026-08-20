import Erdos625.SignedFourFirstMomentNormalization
import Erdos625.ColoringProfileDiscreteObjective
import Mathlib.Tactic

/-!
# Four-coordinate Stirling bridge for the signed first moment

This module isolates the exact factorial remainder between the finite signed
four-size first moment and the discrete profile objective.  Only the four
active deficit coordinates contribute coordinate-factorial remainders, so the
absolute error is at most four copies of `factorialLogErrorBound n`, rather
than one copy for every coordinate in the ambient `Fin (alpha + 1)` profile.

No optimizer comparison, phase/root estimate, partial-diagonal bound, second
moment, or final Erdős statement is used here.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- The exact profile-log/discrete-objective discrepancy consists only of the
numerator and coordinate factorial remainders.  All class-size and forbidden-
edge terms cancel identically. -/
theorem profileLogWeight_sub_discreteObjective_eq_factorialRemainders
    {b : Nat} (n : Nat) (k : ColoringProfile b) :
    profileLogWeight n k - profileDiscreteObjective n k =
      (Real.log (Nat.factorial n : Real) - factorialEntropyMain n) -
        ((∑ i : Fin b, Real.log (Nat.factorial (k i) : Real)) -
          ∑ i : Fin b, factorialEntropyMain (k i)) := by
  rw [← profileStirlingUpperMain_eq_profileDiscreteObjective]
  unfold profileLogWeight profileStirlingUpperMain
    profileLogFactorialSum profileFactorialEntropyMain
  ring

/-- The coarse factorial error is monotone in its natural argument. -/
theorem factorialLogErrorBound_mono {a b : Nat} (hab : a ≤ b) :
    factorialLogErrorBound a ≤ factorialLogErrorBound b := by
  unfold factorialLogErrorBound
  have haPos : 0 < (((a + 1 : Nat) : Real)) := by positivity
  have hcast : (((a + 1 : Nat) : Real)) ≤ (((b + 1 : Nat) : Real)) := by
    exact_mod_cast Nat.succ_le_succ hab
  have hlog := Real.log_le_log haPos hcast
  linarith

/-- Exact full vertex mass forces every four-deficit multiplicity to be at
most the ambient number of vertices. -/
theorem fourDeficitMultiplicity_le_n
    (n alpha : Nat) (hAlpha : 5 < alpha) (m : Fin 4 → Nat)
    (hMass : ∑ i : Fin 4, (alpha - fourDeficit i) * m i = n)
    (i : Fin 4) :
    m i ≤ n := by
  have hDeficit : fourDeficit i ≤ 5 := by
    fin_cases i <;> norm_num [fourDeficit]
  have hSize : 1 ≤ alpha - fourDeficit i := by omega
  have hMul : m i ≤ (alpha - fourDeficit i) * m i := by
    have h := Nat.mul_le_mul_right (m i) hSize
    simpa using h
  have hTerm :
      (alpha - fourDeficit i) * m i ≤
        ∑ j : Fin 4, (alpha - fourDeficit j) * m j := by
    exact Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin 4)))
      (f := fun j : Fin 4 => (alpha - fourDeficit j) * m j)
      (fun j _hj => Nat.zero_le _)
      (Finset.mem_univ i)
  exact hMul.trans (hTerm.trans_eq hMass)

/-- For a mass-feasible four-deficit embedding, the exact profile log-weight
and the zero-safe discrete objective differ by at most four copies of the
ambient factorial error.  Zero ambient profile coordinates contribute
exactly zero and are not charged. -/
theorem abs_profileLogWeight_sub_discreteObjective_fourDeficitEmbedding_le
    (n alpha : Nat) (hAlpha : 5 < alpha) (m : Fin 4 → Nat)
    (hMass : ∑ i : Fin 4, (alpha - fourDeficit i) * m i = n) :
    |profileLogWeight n (fourDeficitEmbedding alpha hAlpha m) -
        profileDiscreteObjective n (fourDeficitEmbedding alpha hAlpha m)| ≤
      4 * factorialLogErrorBound n := by
  let k : ColoringProfile (alpha + 1) :=
    fourDeficitEmbedding alpha hAlpha m
  have hLog := sum_log_factorial_fourDeficitEmbedding alpha hAlpha m
  have hMain := sum_apply_fourDeficitEmbedding alpha hAlpha m
    factorialEntropyMain factorialEntropyMain_zero
  have hCoordinateRemainder :
      (∑ j : Fin (alpha + 1),
          Real.log (Nat.factorial (k j) : Real)) -
        (∑ j : Fin (alpha + 1), factorialEntropyMain (k j)) =
      ∑ i : Fin 4,
        (Real.log (Nat.factorial (m i) : Real) -
          factorialEntropyMain (m i)) := by
    rw [show (∑ j : Fin (alpha + 1),
        Real.log (Nat.factorial (k j) : Real)) =
        ∑ i : Fin 4, Real.log (Nat.factorial (m i) : Real) by
      simpa only [k] using hLog,
      show (∑ j : Fin (alpha + 1), factorialEntropyMain (k j)) =
        ∑ i : Fin 4, factorialEntropyMain (m i) by
      simpa only [k] using hMain,
      Finset.sum_sub_distrib]
  have hNumeratorNonneg :
      0 ≤ Real.log (Nat.factorial n : Real) - factorialEntropyMain n :=
    sub_nonneg.mpr (factorialEntropyMain_le_log_factorial n)
  have hNumeratorLe :
      Real.log (Nat.factorial n : Real) - factorialEntropyMain n ≤
        factorialLogErrorBound n := by
    linarith [log_factorial_le_factorialEntropyMain_add_error n]
  have hCoordinateNonneg : ∀ i : Fin 4,
      0 ≤ Real.log (Nat.factorial (m i) : Real) -
        factorialEntropyMain (m i) := by
    intro i
    exact sub_nonneg.mpr (factorialEntropyMain_le_log_factorial (m i))
  have hCoordinateLe : ∀ i : Fin 4,
      Real.log (Nat.factorial (m i) : Real) -
          factorialEntropyMain (m i) ≤ factorialLogErrorBound n := by
    intro i
    calc
      Real.log (Nat.factorial (m i) : Real) -
          factorialEntropyMain (m i) ≤ factorialLogErrorBound (m i) := by
        linarith [log_factorial_le_factorialEntropyMain_add_error (m i)]
      _ ≤ factorialLogErrorBound n :=
        factorialLogErrorBound_mono
          (fourDeficitMultiplicity_le_n n alpha hAlpha m hMass i)
  have hCoordinateSumNonneg :
      0 ≤ ∑ i : Fin 4,
        (Real.log (Nat.factorial (m i) : Real) -
          factorialEntropyMain (m i)) :=
    Finset.sum_nonneg fun i _hi => hCoordinateNonneg i
  have hCoordinateSumLe :
      (∑ i : Fin 4,
        (Real.log (Nat.factorial (m i) : Real) -
          factorialEntropyMain (m i))) ≤
        4 * factorialLogErrorBound n := by
    calc
      (∑ i : Fin 4,
          (Real.log (Nat.factorial (m i) : Real) -
            factorialEntropyMain (m i))) ≤
          ∑ _i : Fin 4, factorialLogErrorBound n :=
        Finset.sum_le_sum fun i _hi => hCoordinateLe i
      _ = 4 * factorialLogErrorBound n := by
        norm_num [Fin.sum_univ_four]
  have hErrorNonneg : 0 ≤ factorialLogErrorBound n :=
    factorialLogErrorBound_nonneg n
  rw [profileLogWeight_sub_discreteObjective_eq_factorialRemainders,
    hCoordinateRemainder, abs_le]
  constructor
  · linarith
  · linarith

/-- The exact graph-theoretic signed expectation obeys the four-coordinate
Stirling bridge. -/
theorem abs_log_signedProfileExpectation_fourDeficit_sub_discreteObjective_le
    (n alpha : Nat) (hAlpha : 5 < alpha) (m : Fin 4 → Nat)
    (hMass : ∑ i : Fin 4, (alpha - fourDeficit i) * m i = n) :
    |Real.log
          (signedProfileExpectation n
            (fourDeficitEmbedding alpha hAlpha m)).toReal -
        ((((∑ i : Fin 4, m i : Nat) : Real) * q) +
          profileDiscreteObjective n
            (fourDeficitEmbedding alpha hAlpha m))| ≤
      4 * factorialLogErrorBound n := by
  let k : ColoringProfile (alpha + 1) :=
    fourDeficitEmbedding alpha hAlpha m
  have hInvariants := fourDeficitEmbedding_profile_invariants alpha hAlpha m
  have hProfileMass : ColoringProfile.vertexMass k = n :=
    hInvariants.2.1.trans hMass
  have hCountCast :
      (ColoringProfile.partCount k : Real) =
        (((∑ i : Fin 4, m i : Nat) : Real)) := by
    exact_mod_cast hInvariants.1
  have hBound :=
    abs_profileLogWeight_sub_discreteObjective_fourDeficitEmbedding_le
      n alpha hAlpha m hMass
  rw [show signedProfileExpectation n
      (fourDeficitEmbedding alpha hAlpha m) =
      signedProfileExpectation n k by rfl,
    log_signedProfileExpectation_toReal_eq n k hProfileMass,
    hCountCast]
  have hCancel :
      ((((∑ i : Fin 4, m i : Nat) : Real) * q) +
          profileLogWeight n (fourDeficitEmbedding alpha hAlpha m)) -
        ((((∑ i : Fin 4, m i : Nat) : Real) * q) +
          profileDiscreteObjective n
            (fourDeficitEmbedding alpha hAlpha m)) =
      profileLogWeight n (fourDeficitEmbedding alpha hAlpha m) -
        profileDiscreteObjective n
          (fourDeficitEmbedding alpha hAlpha m) := by
    ring
  rw [hCancel]
  exact hBound

/-- The same bound in the exact real first-moment convention consumed by the
Section VII partial-diagonal denominator. -/
theorem abs_log_partialSignedFirstMoment_fourDeficit_sub_discreteObjective_le
    (n alpha : Nat) (hAlpha : 5 < alpha) (m : Fin 4 → Nat)
    (hMass : ∑ i : Fin 4, (alpha - fourDeficit i) * m i = n) :
    |Real.log
          (partialSignedFirstMoment n
            (fun i : Fin 4 ↦ alpha - fourDeficit i) m) -
        ((((∑ i : Fin 4, m i : Nat) : Real) * q) +
          profileDiscreteObjective n
            (fourDeficitEmbedding alpha hAlpha m))| ≤
      4 * factorialLogErrorBound n := by
  have hLog :=
    log_partialSignedFirstMoment_fourDeficitEmbedding
      n alpha hAlpha m hMass
  have hInvariants := fourDeficitEmbedding_profile_invariants alpha hAlpha m
  have hCountCast :
      (ColoringProfile.partCount
          (fourDeficitEmbedding alpha hAlpha m) : Real) =
        (((∑ i : Fin 4, m i : Nat) : Real)) := by
    exact_mod_cast hInvariants.1
  have hBound :=
    abs_profileLogWeight_sub_discreteObjective_fourDeficitEmbedding_le
      n alpha hAlpha m hMass
  rw [hLog, hCountCast]
  have hCancel :
      ((((∑ i : Fin 4, m i : Nat) : Real) * q) +
          profileLogWeight n (fourDeficitEmbedding alpha hAlpha m)) -
        ((((∑ i : Fin 4, m i : Nat) : Real) * q) +
          profileDiscreteObjective n
            (fourDeficitEmbedding alpha hAlpha m)) =
      profileLogWeight n (fourDeficitEmbedding alpha hAlpha m) -
        profileDiscreteObjective n
          (fourDeficitEmbedding alpha hAlpha m) := by
    ring
  rw [hCancel]
  exact hBound

#print axioms profileLogWeight_sub_discreteObjective_eq_factorialRemainders
#print axioms factorialLogErrorBound_mono
#print axioms fourDeficitMultiplicity_le_n
#print axioms abs_profileLogWeight_sub_discreteObjective_fourDeficitEmbedding_le
#print axioms abs_log_partialSignedFirstMoment_fourDeficit_sub_discreteObjective_le

end

end Erdos625
