import Erdos625.PartialDiagonalCentralLogEnvelope
import Mathlib.Tactic

namespace Erdos625

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-!
# Section VII: exact normalized midpoint residual identity

This is the cast-safe finite form of manuscript equation (7.13). It is purely
algebraic and remains separate from phase estimates, scalar rate negativity,
and the empty/central/full aggregate bounds.
-/

/-- Scalar form of (7.13): the pure field identity behind the normalized
residual decomposition, with `Dk` the total deficit mass of the full profile
and `Dl` that of the selected subprofile. -/
private lemma aux_e713_core_identity
    (a Kr Nr L M Dk Dl : Real) (hK : Kr ≠ 0) (hN : Nr ≠ 0)
    (hDk : Dk = a * Kr - Nr) (hDl : M + Dl = a * L) :
    (Nr - M) / Nr =
      (1 - L / Kr) + ((Dl / Kr) - (Dk / Kr) * (L / Kr)) / (a - Dk / Kr) := by
  subst hDk
  have hMv : M = a * L - Dl := by linarith
  subst hMv
  have hden : a - (a * Kr - Nr) / Kr = Nr / Kr := by
    field_simp
    ring
  rw [hden, div_div_eq_mul_div]
  field_simp
  ring

/-- Splitting each block size `alpha - fourDeficit i` off the full size `alpha`
converts any profile's vertex mass and deficit mass into `alpha` times its
block count. -/
private lemma aux_e713_mass_deficit_split
    (alpha : Nat) (halpha : 5 < alpha) (v : Fin 4 → Nat) :
    selectedVertexMass (midpointPartialDiagonalSize alpha) v
        + (∑ i : Fin 4, fourDeficit i * v i)
      = alpha * ∑ i : Fin 4, v i := by
  have hd : ∀ i : Fin 4, fourDeficit i ≤ alpha := by
    intro i
    have := i.isLt
    simp only [fourDeficit]
    omega
  unfold selectedVertexMass
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [midpointPartialDiagonalSize, ← Nat.add_mul]
  rw [Nat.sub_add_cancel (hd i)]

/-- For every feasible subprofile of an admissible midpoint profile, the
normalized residual vertex fraction is the residual block fraction plus the
exact deficit correction from manuscript (7.13). -/
theorem midpointPartialDiagonalRho_eq_residual_add_correction
    (n alpha K : Nat) (hadm : MidpointRoundingAdmissible n alpha K)
    (ell : Fin 4 → Nat)
    (hell : IsPartialSubprofile (midpointMultiplicity n alpha K) ell) :
    midpointPartialDiagonalRho n alpha ell =
      (∑ i : Fin 4, midpointPartialDiagonalZ n alpha K ell i) +
        ((∑ i : Fin 4,
              (fourDeficit i : Real) * midpointPartialDiagonalY K ell i) -
            (∑ i : Fin 4,
              (fourDeficit i : Real) * midpointPartialDiagonalP n alpha K i) *
              (∑ i : Fin 4, midpointPartialDiagonalY K ell i)) /
          ((alpha : Real) -
            ∑ i : Fin 4,
              (fourDeficit i : Real) * midpointPartialDiagonalP n alpha K i) := by
  have hcd :=
    midpointMultiplicity_count_deficit_intDisplacement n alpha K hadm
  obtain ⟨halpha, hK, hnK, -, -⟩ := hadm
  set k : Fin 4 → Nat := midpointMultiplicity n alpha K with hk
  have hsum : (∑ i : Fin 4, k i) = K := hcd.1
  have hmom : (∑ i : Fin 4, fourDeficit i * k i) = alpha * K - n := by
    have h := hcd.2.1
    rw [midpointDeficit] at h
    exact h
  -- full vertex-mass conservation
  have hmass : selectedVertexMass (midpointPartialDiagonalSize alpha) k = n := by
    have hsp := aux_e713_mass_deficit_split alpha halpha k
    rw [hsum, hmom] at hsp
    omega
  -- selected mass is at most `n`
  have hmle : selectedVertexMass (midpointPartialDiagonalSize alpha) ell ≤ n := by
    rw [← hmass]
    exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (hell i)
  -- positivity of `n`
  have hKn : K ≤ n := by
    have h1 : ∀ i : Fin 4, 0 < midpointPartialDiagonalSize alpha i := by
      intro i
      have := i.isLt
      simp only [midpointPartialDiagonalSize, fourDeficit]
      omega
    calc K = ∑ i : Fin 4, k i := hsum.symm
      _ ≤ ∑ i : Fin 4, midpointPartialDiagonalSize alpha i * k i :=
          Finset.sum_le_sum fun i _ => Nat.le_mul_of_pos_left _ (h1 i)
      _ = n := hmass
  have hn : 0 < n := lt_of_lt_of_le hK hKn
  have hKR : ((K : Real)) ≠ 0 := Nat.cast_ne_zero.mpr hK.ne'
  have hNR : ((n : Real)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  set M : Nat := selectedVertexMass (midpointPartialDiagonalSize alpha) ell with hM
  set L : Nat := ∑ i : Fin 4, ell i with hL
  set Dk : Nat := ∑ i : Fin 4, fourDeficit i * k i with hDkdef
  set Dl : Nat := ∑ i : Fin 4, fourDeficit i * ell i with hDldef
  have hZ : (∑ i : Fin 4, midpointPartialDiagonalZ n alpha K ell i)
      = 1 - (L : Real) / (K : Real) := by
    simp only [midpointPartialDiagonalZ, midpointPartialDiagonalP,
      midpointPartialDiagonalY, ← hk]
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div,
      ← Nat.cast_sum, ← Nat.cast_sum, hsum, ← hL]
    field_simp
  have hYsum : (∑ i : Fin 4, midpointPartialDiagonalY K ell i)
      = (L : Real) / (K : Real) := by
    simp only [midpointPartialDiagonalY]
    rw [← Finset.sum_div, ← Nat.cast_sum, ← hL]
  have hdY : (∑ i : Fin 4,
        (fourDeficit i : Real) * midpointPartialDiagonalY K ell i)
      = (Dl : Real) / (K : Real) := by
    simp only [midpointPartialDiagonalY, hDldef, Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  have hdP : (∑ i : Fin 4,
        (fourDeficit i : Real) * midpointPartialDiagonalP n alpha K i)
      = (Dk : Real) / (K : Real) := by
    simp only [midpointPartialDiagonalP, ← hk, hDkdef, Nat.cast_sum,
      Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  have hrho : midpointPartialDiagonalRho n alpha ell
      = ((n : Real) - (M : Real)) / (n : Real) := by
    simp only [midpointPartialDiagonalRho, ← hM]
    rw [Nat.cast_sub hmle]
  have hDkR : (Dk : Real) = (alpha : Real) * (K : Real) - (n : Real) := by
    have hsp := aux_e713_mass_deficit_split alpha halpha k
    rw [hmass, hsum, ← hDkdef] at hsp
    have hsp' : (n : Real) + (Dk : Real) = (alpha : Real) * (K : Real) := by
      exact_mod_cast hsp
    linarith
  have hDlR : (M : Real) + (Dl : Real) = (alpha : Real) * (L : Real) := by
    have hsp := aux_e713_mass_deficit_split alpha halpha ell
    rw [← hM, ← hL, ← hDldef] at hsp
    exact_mod_cast hsp
  rw [hrho, hZ, hYsum, hdY, hdP]
  exact aux_e713_core_identity (alpha : Real) (K : Real) (n : Real) (L : Real)
    (M : Real) (Dk : Real) (Dl : Real) hKR hNR hDkR hDlR

end

end Erdos625
