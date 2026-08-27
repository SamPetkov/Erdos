import Erdos625.Section8EndpointDecoratedReferenceWeight
import Mathlib.Tactic

/-!
# Section VIII: identify the decorated endpoint reference with `W(L)`

The preceding modules count the block-pairing and full-stub fibres and attach
the common local reward.  This file performs the remaining finite algebraic
regrouping.  Because `ENNReal` does not support unrestricted cancellation at
zero or infinity, the local product is first compared in cross-multiplied form;
only positive finite factorial factors are then cancelled.

Consequently the literal sum over decorated endpoint block pairings is exactly
`fourEndpointW`.  This is still a statement about the decorated
parameterization; the equivalence with `FourEndpointPhysicalFibre` is a
separate finite theorem.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- Cross-multiplied local-product identity.  Each local factorial is positive
and finite, so its literal full-cell quotient cancels after multiplication by
the same factorial. -/
theorem fourEndpointLocalProduct_mul_stubFactorialProduct
    (alpha : Nat) (hAlpha : 5 < alpha) (L : FourEndpointFullTable) :
    fourEndpointLocalProduct alpha hAlpha L *
        ((fourEndpointCellStubFactorialProduct alpha hAlpha L : Nat) : ENNReal) =
      ((fourEndpointCellStubSelectionProduct alpha hAlpha L : Nat) : ENNReal) *
        fourEndpointFullRewardProduct alpha hAlpha L := by
  classical
  unfold fourEndpointLocalProduct fourEndpointLocalCellFactor
    fourEndpointCellStubSelectionProduct
    fourEndpointCellStubFactorialProduct
    fourEndpointFullRewardProduct
  push_cast
  let A : Fin 4 → Fin 4 → ENNReal := fun i j =>
    ((fourEndpointSize alpha hAlpha i).descFactorial
      (fourEndpointOverlapSize alpha hAlpha i j) : Nat)
  let B : Fin 4 → Fin 4 → ENNReal := fun i j =>
    ((fourEndpointSize alpha hAlpha j).descFactorial
      (fourEndpointOverlapSize alpha hAlpha i j) : Nat)
  let F : Fin 4 → Fin 4 → ENNReal := fun i j =>
    ((fourEndpointOverlapSize alpha hAlpha i j).factorial : Nat)
  let R : Fin 4 → Fin 4 → ENNReal := fun i j =>
    (localSignRewardNat (fourEndpointOverlapSize alpha hAlpha i j) : Nat)
  let E : Fin 4 → Fin 4 → Nat := fun i j => L.toFun i j
  change
    (∏ i : Fin 4, ∏ j : Fin 4,
        (((A i j * B i j / F i j) * R i j) ^ E i j)) *
      (∏ i : Fin 4, ∏ j : Fin 4, (F i j) ^ E i j) =
    (∏ i : Fin 4, ∏ j : Fin 4, (A i j * B i j) ^ E i j) *
      (∏ i : Fin 4, ∏ j : Fin 4, (R i j) ^ E i j)
  calc
    (∏ i : Fin 4, ∏ j : Fin 4,
        (((A i j * B i j / F i j) * R i j) ^ E i j)) *
        (∏ i : Fin 4, ∏ j : Fin 4, (F i j) ^ E i j) =
      ∏ i : Fin 4,
        ((∏ j : Fin 4,
            (((A i j * B i j / F i j) * R i j) ^ E i j)) *
          (∏ j : Fin 4, (F i j) ^ E i j)) := by
        rw [← Finset.prod_mul_distrib]
    _ = ∏ i : Fin 4, ∏ j : Fin 4,
          (((A i j * B i j / F i j) * R i j) ^ E i j) *
            (F i j) ^ E i j := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [← Finset.prod_mul_distrib]
    _ = ∏ i : Fin 4, ∏ j : Fin 4,
          (A i j * B i j) ^ E i j * (R i j) ^ E i j := by
        apply Finset.prod_congr rfl
        intro i hi
        apply Finset.prod_congr rfl
        intro j hj
        have hF0 : F i j ≠ 0 := by
          dsimp [F]
          exact_mod_cast (Nat.factorial_pos
            (fourEndpointOverlapSize alpha hAlpha i j)).ne'
        have hFtop : F i j ≠ ⊤ := by
          dsimp [F]
          exact ENNReal.natCast_ne_top _
        have hbase :
            ((A i j * B i j / F i j) * R i j) * F i j =
              (A i j * B i j) * R i j := by
          calc
            ((A i j * B i j / F i j) * R i j) * F i j =
                (A i j * B i j / F i j * F i j) * R i j := by
              ac_rfl
            _ = (A i j * B i j) * R i j := by
              rw [ENNReal.div_mul_cancel hF0 hFtop]
        simpa only [mul_pow] using
          congrArg (fun z : ENNReal => z ^ E i j) hbase
    _ = ∏ i : Fin 4,
          ((∏ j : Fin 4, (A i j * B i j) ^ E i j) *
            (∏ j : Fin 4, (R i j) ^ E i j)) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [Finset.prod_mul_distrib]
    _ = (∏ i : Fin 4, ∏ j : Fin 4,
          (A i j * B i j) ^ E i j) *
        (∏ i : Fin 4, ∏ j : Fin 4, (R i j) ^ E i j) := by
      rw [Finset.prod_mul_distrib]

/-- The aggregate manuscript local factor is exactly the full-cell stub
selection quotient times the product of signed local rewards. -/
theorem fourEndpointLocalProduct_eq_stubQuotient_mul_reward
    (alpha : Nat) (hAlpha : 5 < alpha) (L : FourEndpointFullTable) :
    fourEndpointLocalProduct alpha hAlpha L =
      ((fourEndpointCellStubSelectionProduct alpha hAlpha L : Nat) : ENNReal) /
          ((fourEndpointCellStubFactorialProduct alpha hAlpha L : Nat) : ENNReal) *
        fourEndpointFullRewardProduct alpha hAlpha L := by
  have hStubPos : 0 < fourEndpointCellStubFactorialProduct alpha hAlpha L := by
    unfold fourEndpointCellStubFactorialProduct
    apply Finset.prod_pos
    intro i hi
    apply Finset.prod_pos
    intro j hj
    exact pow_pos (Nat.factorial_pos _) _
  have hStub0 :
      ((fourEndpointCellStubFactorialProduct alpha hAlpha L : Nat) : ENNReal) ≠ 0 := by
    exact_mod_cast hStubPos.ne'
  have hStubTop :
      ((fourEndpointCellStubFactorialProduct alpha hAlpha L : Nat) : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  rw [← ENNReal.mul_div_right_comm]
  apply (ENNReal.eq_div_iff hStub0 hStubTop).2
  simpa only [mul_comm] using
    fourEndpointLocalProduct_mul_stubFactorialProduct alpha hAlpha L

/-- The expanded decorated quotient weight is definitionally the manuscript
endpoint reference weight after the local-product regrouping. -/
theorem fourEndpointDecoratedReferenceQuotientWeight_eq_fourEndpointW
    (n alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) (L : FourEndpointFullTable) :
    fourEndpointDecoratedReferenceQuotientWeight n alpha hAlpha k L =
      fourEndpointW n alpha hAlpha k L := by
  unfold fourEndpointDecoratedReferenceQuotientWeight
    fourEndpointDecoratedNumerator fourEndpointDecoratedDenominator
    fourEndpointDecoratedReferenceAtomWeight fourEndpointW
  rw [fourEndpointLocalProduct_eq_stubQuotient_mul_reward]
  push_cast
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv
    (Or.inr (ENNReal.natCast_ne_top _))
    (Or.inl (ENNReal.natCast_ne_top _))]
  ring

/-- Exact full-endpoint normalization: summing the common reference atom over
all selected block pairings and all full-cell stub matchings gives `W(L)` with
no extra multiplicity. -/
theorem sum_fourEndpointDecoratedReferenceAtomWeight_eq_fourEndpointW
    (n alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) (L : FourEndpointFullTable) :
    (∑ _ : FourEndpointDecoratedBlockPairing alpha hAlpha k L,
      fourEndpointDecoratedReferenceAtomWeight n alpha hAlpha L) =
        fourEndpointW n alpha hAlpha k L := by
  rw [sum_fourEndpointDecoratedReferenceAtomWeight_eq_quotientWeight,
    fourEndpointDecoratedReferenceQuotientWeight_eq_fourEndpointW]

#print axioms fourEndpointLocalProduct_mul_stubFactorialProduct
#print axioms fourEndpointLocalProduct_eq_stubQuotient_mul_reward
#print axioms fourEndpointDecoratedReferenceQuotientWeight_eq_fourEndpointW
#print axioms sum_fourEndpointDecoratedReferenceAtomWeight_eq_fourEndpointW

end

end Erdos625
