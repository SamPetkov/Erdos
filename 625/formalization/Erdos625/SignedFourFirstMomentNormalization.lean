import Erdos625.MidpointRoundedFourSizeEntropyLoss
import Erdos625.PartialDiagonalWeights
import Erdos625.Section6SignedExpectationDenominator
import Erdos625.ColoringProfileLogWeight
import Mathlib.Tactic

/-!
# Exact normalization of the signed four-size first moment

This module identifies the graph-theoretic signed profile expectation with the
real factorial expression used as the Section VII partial-diagonal
denominator.  The proof is finite.  It first establishes a generic logarithmic
identity for a mass-feasible profile, then reindexes the four-deficit embedding
and expands the logarithm of `partialSignedFirstMoment`.

No phase asymptotic, root theorem, partial-diagonal estimate, skeleton bound,
second moment, or final Erdős statement is used here.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- The logarithm of the signed profile expectation is the ordinary profile
log-weight plus `q` for every nonempty part. -/
theorem log_signedProfileExpectation_toReal_eq
    {b n : Nat} (k : ColoringProfile b)
    (hMass : ColoringProfile.vertexMass k = n) :
    Real.log (signedProfileExpectation n k).toReal =
      (ColoringProfile.partCount k : Real) * q +
        profileLogWeight n k := by
  have hUnsignedPos : 0 < profileColoringExpectation n k :=
    profileColoringExpectation_pos n k hMass
  have hUnsignedTop : profileColoringExpectation n k ≠ ⊤ := by
    rw [profileColoringExpectation_eq_enumerativeCoefficient_mul_of n k
      (profileEnumerationStatement n k hMass)]
    finiteness
  have hUnsignedRealPos : 0 < (profileColoringExpectation n k).toReal :=
    ENNReal.toReal_pos hUnsignedPos.ne' hUnsignedTop
  rw [signedProfileExpectation_eq, ENNReal.toReal_mul, ENNReal.toReal_pow]
  norm_num
  rw [Real.log_mul]
  · rw [Real.log_pow,
      log_profileColoringExpectation_toReal_eq_profileLogWeight n k hMass]
    unfold q
    ring
  · positivity
  · exact hUnsignedRealPos.ne'

/-- The internal-edge count of a four-deficit embedding is the literal
four-coordinate sum. -/
theorem forbiddenEdges_fourDeficitEmbedding
    (alpha : Nat) (hAlpha : 5 < alpha) (m : Fin 4 → Nat) :
    ColoringProfile.forbiddenEdges
        (fourDeficitEmbedding alpha hAlpha m) =
      ∑ i : Fin 4,
        m i * (alpha - fourDeficit i).choose 2 := by
  rw [ColoringProfile.forbiddenEdges_eq_sum]
  simp only [fourDeficitEmbedding, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [ite_mul, zero_mul, Fintype.sum_ite_eq]
  rw [fourDeficitCoordinate_val_add_one_eq]

/-- Any real linear statistic of the embedded multiplicities reindexes to the
four distinguished coordinates. -/
theorem sum_fourDeficitEmbedding_cast_mul
    (alpha : Nat) (hAlpha : 5 < alpha) (m : Fin 4 → Nat)
    (g : Fin (alpha + 1) → Real) :
    (∑ j : Fin (alpha + 1),
        (fourDeficitEmbedding alpha hAlpha m j : Real) * g j) =
      ∑ i : Fin 4,
        (m i : Real) * g (fourDeficitCoordinate alpha hAlpha i) := by
  unfold fourDeficitEmbedding
  push_cast
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [ite_mul, zero_mul, Fintype.sum_ite_eq]

/-- The class-size factorial-log term of the embedded profile has exactly four
active coordinates. -/
theorem sum_fourDeficitEmbedding_mul_log_factorial
    (alpha : Nat) (hAlpha : 5 < alpha) (m : Fin 4 → Nat) :
    (∑ j : Fin (alpha + 1),
        (fourDeficitEmbedding alpha hAlpha m j : Real) *
          Real.log (Nat.factorial (j.1 + 1) : Real)) =
      ∑ i : Fin 4,
        (m i : Real) *
          Real.log (Nat.factorial (alpha - fourDeficit i) : Real) := by
  rw [sum_fourDeficitEmbedding_cast_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [fourDeficitCoordinate_val_add_one_eq]

/-- A zero-safe scalar statistic of embedded multiplicities reindexes to the
four active coordinates. -/
theorem sum_apply_fourDeficitEmbedding
    (alpha : Nat) (hAlpha : 5 < alpha) (m : Fin 4 → Nat)
    (f : Nat → Real) (hf : f 0 = 0) :
    (∑ j : Fin (alpha + 1),
        f (fourDeficitEmbedding alpha hAlpha m j)) =
      ∑ i : Fin 4, f (m i) := by
  classical
  let c : Fin 4 → Fin (alpha + 1) :=
    fourDeficitCoordinate alpha hAlpha
  have hc : Function.Injective c := by
    simpa only [c] using fourDeficitCoordinate_injective alpha hAlpha
  have heval :=
    (fourDeficitEmbedding_eval_and_off_image alpha hAlpha m).1
  have hoff :=
    (fourDeficitEmbedding_eval_and_off_image alpha hAlpha m).2
  change
    Finset.sum (Finset.univ : Finset (Fin (alpha + 1)))
        (fun j => f (fourDeficitEmbedding alpha hAlpha m j)) =
      Finset.sum (Finset.univ : Finset (Fin 4)) (fun i => f (m i))
  calc
    Finset.sum (Finset.univ : Finset (Fin (alpha + 1)))
        (fun j => f (fourDeficitEmbedding alpha hAlpha m j)) =
      Finset.sum ((Finset.univ : Finset (Fin 4)).image c)
        (fun j => f (fourDeficitEmbedding alpha hAlpha m j)) := by
      symm
      apply Finset.sum_subset
      · simp
      · intro j _hj hnot
        have hnone :
            ∀ i : Fin 4, fourDeficitCoordinate alpha hAlpha i ≠ j := by
          intro i hij
          apply hnot
          refine Finset.mem_image.mpr ?_
          exact ⟨i, Finset.mem_univ i, by simpa [c] using hij⟩
        rw [hoff j hnone, hf]
    _ = Finset.sum (Finset.univ : Finset (Fin 4)) (fun i => f (m i)) := by
      rw [Finset.sum_image hc.injOn]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [heval i]

/-- The equal-size multiplicity factorial-log term has exactly four active
coordinates. -/
theorem sum_log_factorial_fourDeficitEmbedding
    (alpha : Nat) (hAlpha : 5 < alpha) (m : Fin 4 → Nat) :
    (∑ j : Fin (alpha + 1),
        Real.log
          (Nat.factorial (fourDeficitEmbedding alpha hAlpha m j) : Real)) =
      ∑ i : Fin 4, Real.log (Nat.factorial (m i) : Real) := by
  exact sum_apply_fourDeficitEmbedding alpha hAlpha m
    (fun t ↦ Real.log (Nat.factorial t : Real)) (by norm_num)

/-- Logarithm of the four-coordinate factorial product. -/
theorem log_partialProfileFactorialProduct_eq
    (u m : Fin 4 → Nat) :
    Real.log (partialProfileFactorialProduct u m : Real) =
      (∑ i : Fin 4,
        (m i : Real) * Real.log (Nat.factorial (u i) : Real)) +
      ∑ i : Fin 4, Real.log (Nat.factorial (m i) : Real) := by
  unfold partialProfileFactorialProduct
  rw [Nat.cast_prod, Real.log_prod]
  · calc
      (∑ i : Fin 4,
          Real.log
            ((Nat.factorial (u i)) ^ m i * Nat.factorial (m i) : Nat)) =
        ∑ i : Fin 4,
          ((m i : Real) * Real.log (Nat.factorial (u i) : Real) +
            Real.log (Nat.factorial (m i) : Real)) := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Nat.cast_mul, Nat.cast_pow,
            Real.log_mul (by positivity) (by positivity), Real.log_pow]
      _ = (∑ i : Fin 4,
            (m i : Real) * Real.log (Nat.factorial (u i) : Real)) +
          ∑ i : Fin 4, Real.log (Nat.factorial (m i) : Real) := by
        rw [Finset.sum_add_distrib]
  · intro i _hi
    positivity

/-- Exact logarithm of `partialSignedFirstMoment` on the full-mass domain. -/
theorem log_partialSignedFirstMoment_eq
    (n : Nat) (u m : Fin 4 → Nat)
    (hMass : selectedVertexMass u m = n) :
    Real.log (partialSignedFirstMoment n u m) =
      (selectedBlockCount m : Real) * q +
        Real.log (Nat.factorial n : Real) -
        (∑ i : Fin 4,
          (m i : Real) * Real.log (Nat.factorial (u i) : Real)) -
        (∑ i : Fin 4, Real.log (Nat.factorial (m i) : Real)) -
        (selectedInternalEdgeCount u m : Real) * q := by
  have hBlockPow : (2 : Real) ^ selectedBlockCount m ≠ 0 := by positivity
  have hNFactorial : (Nat.factorial n : Real) ≠ 0 := by positivity
  have hProfileFactorialNat : partialProfileFactorialProduct u m ≠ 0 := by
    unfold partialProfileFactorialProduct
    positivity
  have hProfileFactorial :
      (partialProfileFactorialProduct u m : Real) ≠ 0 := by
    exact_mod_cast hProfileFactorialNat
  have hInternalPow :
      (2 : Real) ^ selectedInternalEdgeCount u m ≠ 0 := by
    positivity
  unfold partialSignedFirstMoment
  rw [hMass, Nat.sub_self]
  norm_num only [Nat.factorial_zero, Nat.cast_one, one_mul]
  rw [Real.log_div (mul_ne_zero hBlockPow hNFactorial)
      (mul_ne_zero hProfileFactorial hInternalPow),
    Real.log_mul hBlockPow hNFactorial,
    Real.log_mul hProfileFactorial hInternalPow,
    Real.log_pow, Real.log_pow,
    log_partialProfileFactorialProduct_eq]
  unfold q
  ring

/-- The logarithm of the exact four-size factorial first moment is the signed
profile log-weight of the embedded profile. -/
theorem log_partialSignedFirstMoment_fourDeficitEmbedding
    (n alpha : Nat) (hAlpha : 5 < alpha) (m : Fin 4 → Nat)
    (hMass :
      ∑ i : Fin 4, (alpha - fourDeficit i) * m i = n) :
    Real.log
        (partialSignedFirstMoment n
          (fun i : Fin 4 ↦ alpha - fourDeficit i) m) =
      (ColoringProfile.partCount
          (fourDeficitEmbedding alpha hAlpha m) : Real) * q +
        profileLogWeight n (fourDeficitEmbedding alpha hAlpha m) := by
  let u : Fin 4 → Nat := fun i ↦ alpha - fourDeficit i
  let k : ColoringProfile (alpha + 1) :=
    fourDeficitEmbedding alpha hAlpha m
  have hInvariants := fourDeficitEmbedding_profile_invariants alpha hAlpha m
  have hSelectedMass : selectedVertexMass u m = n := by
    simpa only [u, selectedVertexMass] using hMass
  have hClassLog :=
    sum_fourDeficitEmbedding_mul_log_factorial alpha hAlpha m
  have hMultiplicityLog :=
    sum_log_factorial_fourDeficitEmbedding alpha hAlpha m
  have hForbidden := forbiddenEdges_fourDeficitEmbedding alpha hAlpha m
  have hSelectedInternalCast :
      (selectedInternalEdgeCount u m : Real) =
        ∑ i : Fin 4,
          (m i : Real) * ((u i).choose 2 : Real) := by
    unfold selectedInternalEdgeCount
    push_cast
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [show partialSignedFirstMoment n
      (fun i : Fin 4 ↦ alpha - fourDeficit i) m =
      partialSignedFirstMoment n u m by rfl,
    log_partialSignedFirstMoment_eq n u m hSelectedMass]
  unfold profileLogWeight
  rw [show ColoringProfile.partCount k = ∑ i : Fin 4, m i from hInvariants.1]
  change
    (selectedBlockCount m : Real) * q +
        Real.log (Nat.factorial n : Real) -
        (∑ i : Fin 4,
          (m i : Real) * Real.log (Nat.factorial (u i) : Real)) -
        (∑ i : Fin 4, Real.log (Nat.factorial (m i) : Real)) -
        (selectedInternalEdgeCount u m : Real) * q =
      ((∑ i : Fin 4, m i : Nat) : Real) * q +
        (Real.log (Nat.factorial n : Real) -
          ∑ j : Fin (alpha + 1),
            (k j : Real) * Real.log (Nat.factorial (j.1 + 1) : Real) -
          ∑ j : Fin (alpha + 1),
            Real.log (Nat.factorial (k j) : Real) -
          (ColoringProfile.forbiddenEdges k : Real) * Real.log 2)
  rw [show (∑ j : Fin (alpha + 1),
      (k j : Real) * Real.log (Nat.factorial (j.1 + 1) : Real)) =
      ∑ i : Fin 4,
        (m i : Real) * Real.log (Nat.factorial (u i) : Real) by
      simpa only [k, u] using hClassLog,
    show (∑ j : Fin (alpha + 1),
      Real.log (Nat.factorial (k j) : Real)) =
      ∑ i : Fin 4, Real.log (Nat.factorial (m i) : Real) by
      simpa only [k] using hMultiplicityLog,
    show ColoringProfile.forbiddenEdges k =
      ∑ i : Fin 4, m i * (u i).choose 2 by
      simpa only [k, u] using hForbidden,
    hSelectedInternalCast]
  simp only [selectedBlockCount, u]
  unfold q
  push_cast
  ring

/-- Exact bridge between the graph-theoretic signed expectation and the real
factorial first moment used by the partial-diagonal normalization. -/
theorem signedProfileExpectation_toReal_eq_partialSignedFirstMoment_fourDeficit
    (n alpha : Nat) (hAlpha : 5 < alpha) (m : Fin 4 → Nat)
    (hMass :
      ∑ i : Fin 4, (alpha - fourDeficit i) * m i = n) :
    (signedProfileExpectation n
        (fourDeficitEmbedding alpha hAlpha m)).toReal =
      partialSignedFirstMoment n
        (fun i : Fin 4 ↦ alpha - fourDeficit i) m := by
  let k : ColoringProfile (alpha + 1) :=
    fourDeficitEmbedding alpha hAlpha m
  let u : Fin 4 → Nat := fun i ↦ alpha - fourDeficit i
  have hInvariants := fourDeficitEmbedding_profile_invariants alpha hAlpha m
  have hProfileMass : ColoringProfile.vertexMass k = n := by
    exact hInvariants.2.1.trans hMass
  have hUnsignedPos : 0 < profileColoringExpectation n k :=
    profileColoringExpectation_pos n k hProfileMass
  have hSignedPos : 0 < signedProfileExpectation n k := by
    rw [signedProfileExpectation_eq]
    exact ENNReal.mul_pos
      (ENNReal.pow_ne_zero (by norm_num) _) hUnsignedPos.ne'
  have hSignedTop : signedProfileExpectation n k ≠ ⊤ :=
    signedProfileExpectation_ne_top n k
  have hLeftPos : 0 < (signedProfileExpectation n k).toReal :=
    ENNReal.toReal_pos hSignedPos.ne' hSignedTop
  have hRightPos : 0 < partialSignedFirstMoment n u m :=
    partialSignedFirstMoment_pos n u m
  have hLog :
      Real.log (signedProfileExpectation n k).toReal =
        Real.log (partialSignedFirstMoment n u m) := by
    calc
      Real.log (signedProfileExpectation n k).toReal =
          (ColoringProfile.partCount k : Real) * q +
            profileLogWeight n k :=
        log_signedProfileExpectation_toReal_eq k hProfileMass
      _ = Real.log (partialSignedFirstMoment n u m) := by
        symm
        simpa only [k, u] using
          log_partialSignedFirstMoment_fourDeficitEmbedding
            n alpha hAlpha m hMass
  calc
    (signedProfileExpectation n k).toReal =
        Real.exp (Real.log (signedProfileExpectation n k).toReal) :=
      (Real.exp_log hLeftPos).symm
    _ = Real.exp (Real.log (partialSignedFirstMoment n u m)) := by rw [hLog]
    _ = partialSignedFirstMoment n u m := Real.exp_log hRightPos

#print axioms log_signedProfileExpectation_toReal_eq
#print axioms forbiddenEdges_fourDeficitEmbedding
#print axioms sum_fourDeficitEmbedding_cast_mul
#print axioms sum_apply_fourDeficitEmbedding
#print axioms log_partialSignedFirstMoment_fourDeficitEmbedding
#print axioms signedProfileExpectation_toReal_eq_partialSignedFirstMoment_fourDeficit

end

end Erdos625
