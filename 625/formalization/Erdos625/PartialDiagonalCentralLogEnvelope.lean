import Erdos625.MidpointProfileRoundingIntDisplacement
import Erdos625.PartialDiagonalWeights
import Erdos625.ColoringProfileFactorialBounds
import Mathlib.Tactic

namespace Erdos625

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-!
# Section VII: finite midpoint partial-diagonal logarithmic envelope

This is the zero-safe finite Stirling bridge from the exact marked weight to
the normalized four-coordinate entropy expression. It is uniform over all
midpoint-admissible parameters and all feasible partial subprofiles. The
empty-, central-, and full-corner asymptotic estimates remain separate.
-/

/-- The four midpoint block sizes `alpha - 2, ..., alpha - 5`. -/
def midpointPartialDiagonalSize (alpha : Nat) (i : Fin 4) : Nat :=
  alpha - fourDeficit i

/-- Normalized midpoint multiplicity `p_i = k_i / K`. -/
noncomputable def midpointPartialDiagonalP
    (n alpha K : Nat) (i : Fin 4) : Real :=
  (midpointMultiplicity n alpha K i : Real) / (K : Real)

/-- Normalized selected multiplicity `y_i = ell_i / K`. -/
noncomputable def midpointPartialDiagonalY
    (K : Nat) (ell : Fin 4 → Nat) (i : Fin 4) : Real :=
  (ell i : Real) / (K : Real)

/-- Normalized residual multiplicity `z_i = p_i - y_i`. -/
noncomputable def midpointPartialDiagonalZ
    (n alpha K : Nat) (ell : Fin 4 → Nat) (i : Fin 4) : Real :=
  midpointPartialDiagonalP n alpha K i - midpointPartialDiagonalY K ell i

/-- Residual vertex fraction `(n-m)/n`, retaining natural subtraction. -/
noncomputable def midpointPartialDiagonalRho
    (n alpha : Nat) (ell : Fin 4 → Nat) : Real :=
  ((n - selectedVertexMass (midpointPartialDiagonalSize alpha) ell : Nat) : Real) /
    (n : Real)

/-- The exact one-coordinate phase coefficient from manuscript (7.15). -/
noncomputable def midpointPartialDiagonalE
    (n alpha K : Nat) (i : Fin 4) : Real :=
  Real.log (K : Real)
    + Real.log (Nat.factorial (midpointPartialDiagonalSize alpha i) : Real)
    + (midpointPartialDiagonalSize alpha i : Real)
    - (midpointPartialDiagonalSize alpha i : Real) * logOrder n
    + q * ((midpointPartialDiagonalSize alpha i).choose 2 : Real)
    - q

/-! ### Local helper lemmas for the finite Stirling expansion -/

private lemma aux_log_choose (a b : ℕ) (h : b ≤ a) :
    Real.log ((a.choose b : ℕ) : ℝ) =
      Real.log ((a.factorial : ℕ) : ℝ) - Real.log ((b.factorial : ℕ) : ℝ)
        - Real.log (((a - b).factorial : ℕ) : ℝ) := by
  have h1 : ((a.choose b : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos h).ne'
  have h2 : ((b.factorial : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3 : (((a - b).factorial : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hkey : ((a.choose b : ℕ) : ℝ) * ((b.factorial : ℕ) : ℝ)
      * (((a - b).factorial : ℕ) : ℝ) = ((a.factorial : ℕ) : ℝ) := by
    exact_mod_cast congrArg (fun t : ℕ => (t : ℝ))
      (Nat.choose_mul_factorial_mul_factorial h)
  have hlog := congrArg Real.log hkey
  rw [Real.log_mul (mul_ne_zero h1 h2) h3, Real.log_mul h1 h2] at hlog
  linarith

private lemma aux_entropy_div (K a : ℕ) (hK : 0 < K) :
    (a : ℝ) * Real.log ((a : ℝ) / (K : ℝ))
      = factorialEntropyMain a + (a : ℝ) - (a : ℝ) * Real.log (K : ℝ) := by
  have hKne : ((K : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hK.ne'
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [factorialEntropyMain]
  · have hane : ((a : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
    rw [Real.log_div hane hKne, factorialEntropyMain_of_pos ha]
    ring

private lemma aux_coord_scalar (Kr a b c la lb lc EE : ℝ) (hK : Kr ≠ 0) :
    Kr * (2 * (a / Kr) * la - 2 * (c / Kr) * lc - (b / Kr) * lb - b / Kr
        + b / Kr * EE)
      = 2 * a * la - 2 * c * lc - b * lb - b + b * EE := by
  field_simp

private lemma aux_log_marking (k ell : Fin 4 → ℕ)
    (hell : IsPartialSubprofile k ell) :
    Real.log ((partialMarkingCount k ell : ℕ) : ℝ)
      = ∑ i, 2 * Real.log (((k i).choose (ell i) : ℕ) : ℝ) := by
  unfold partialMarkingCount
  push_cast
  rw [Real.log_prod]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.log_pow]
    push_cast
    ring
  · intro i _
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.choose_pos (hell i)).ne')

private lemma aux_log_factprod (u ell : Fin 4 → ℕ) :
    Real.log ((partialProfileFactorialProduct u ell : ℕ) : ℝ)
      = ∑ i, ((ell i : ℝ) * Real.log (((u i).factorial : ℕ) : ℝ)
              + Real.log (((ell i).factorial : ℕ) : ℝ)) := by
  unfold partialProfileFactorialProduct
  push_cast
  rw [Real.log_prod]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.log_mul (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)))
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)), Real.log_pow]
  · intro i _
    exact mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

private lemma aux_log_weight (n : ℕ) (u k ell : Fin 4 → ℕ)
    (hell : IsPartialSubprofile k ell) :
    Real.log (partialDiagonalWeight n u k ell)
      = (∑ i, (2 * Real.log (((k i).factorial : ℕ) : ℝ)
              - Real.log (((ell i).factorial : ℕ) : ℝ)
              - 2 * Real.log (((k i - ell i).factorial : ℕ) : ℝ)
              + (ell i : ℝ) * Real.log (((u i).factorial : ℕ) : ℝ)))
        + Real.log (((n - selectedVertexMass u ell).factorial : ℕ) : ℝ)
        - Real.log ((n.factorial : ℕ) : ℝ)
        + (selectedInternalEdgeCount u ell : ℝ) * Real.log 2
        - (selectedBlockCount ell : ℝ) * Real.log 2 := by
  have hPpos : (0 : ℝ) < ((partialMarkingCount k ell : ℕ) : ℝ) := by
    exact_mod_cast partialMarkingCount_pos k ell hell
  have hFpos : (0 : ℝ) < ((partialProfileFactorialProduct u ell : ℕ) : ℝ) := by
    have h : 0 < partialProfileFactorialProduct u ell := by
      unfold partialProfileFactorialProduct
      exact Finset.prod_pos fun i _ =>
        Nat.mul_pos (pow_pos (Nat.factorial_pos _) _) (Nat.factorial_pos _)
    exact_mod_cast h
  have hnmpos : (0 : ℝ) < (((n - selectedVertexMass u ell).factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hnfpos : (0 : ℝ) < ((n.factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  have h2M : (0 : ℝ) < (2 : ℝ) ^ selectedInternalEdgeCount u ell := by positivity
  have h2L : (0 : ℝ) < (2 : ℝ) ^ selectedBlockCount ell := by positivity
  have hweight : partialDiagonalWeight n u k ell
      = ((partialMarkingCount k ell : ℕ) : ℝ)
          * (((n - selectedVertexMass u ell).factorial : ℕ) : ℝ)
          * ((partialProfileFactorialProduct u ell : ℕ) : ℝ)
          * (2 : ℝ) ^ selectedInternalEdgeCount u ell
        / ((2 : ℝ) ^ selectedBlockCount ell * ((n.factorial : ℕ) : ℝ)) := by
    unfold partialDiagonalWeight partialSignedFirstMoment
    rw [div_div_eq_mul_div]
    ring
  rw [hweight,
    Real.log_div
      (ne_of_gt (mul_pos (mul_pos (mul_pos hPpos hnmpos) hFpos) h2M))
      (ne_of_gt (mul_pos h2L hnfpos)),
    Real.log_mul (ne_of_gt (mul_pos (mul_pos hPpos hnmpos) hFpos)) (ne_of_gt h2M),
    Real.log_mul (ne_of_gt (mul_pos hPpos hnmpos)) (ne_of_gt hFpos),
    Real.log_mul (ne_of_gt hPpos) (ne_of_gt hnmpos),
    Real.log_mul (ne_of_gt h2L) (ne_of_gt hnfpos),
    Real.log_pow, Real.log_pow,
    aux_log_marking k ell hell, aux_log_factprod u ell]
  have hs : (∑ i : Fin 4, 2 * Real.log (((k i).choose (ell i) : ℕ) : ℝ))
      + (∑ i : Fin 4, ((ell i : ℝ) * Real.log (((u i).factorial : ℕ) : ℝ)
              + Real.log (((ell i).factorial : ℕ) : ℝ)))
      = ∑ i : Fin 4, (2 * Real.log (((k i).factorial : ℕ) : ℝ)
              - Real.log (((ell i).factorial : ℕ) : ℝ)
              - 2 * Real.log (((k i - ell i).factorial : ℕ) : ℝ)
              + (ell i : ℝ) * Real.log (((u i).factorial : ℕ) : ℝ)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [aux_log_choose (k i) (ell i) (hell i)]
    ring
  linarith [hs]

private lemma aux_full_mass (n alpha K : ℕ)
    (hadm : MidpointRoundingAdmissible n alpha K) :
    selectedVertexMass (midpointPartialDiagonalSize alpha)
      (midpointMultiplicity n alpha K) = n := by
  have hcd := midpointMultiplicity_count_deficit_intDisplacement n alpha K hadm
  obtain ⟨halpha, hK, hnK, -, -⟩ := hadm
  have hsum := hcd.1
  have hmom := hcd.2.1
  rw [midpointDeficit] at hmom
  have hd : ∀ i : Fin 4, fourDeficit i ≤ alpha := by
    intro i
    have := i.isLt
    simp only [fourDeficit]
    omega
  have hsplit :
      (∑ i, midpointPartialDiagonalSize alpha i * midpointMultiplicity n alpha K i)
        + (∑ i, tangentDeficitNat i * midpointMultiplicity n alpha K i)
        = alpha * K := by
    have hstep :
        (∑ i, midpointPartialDiagonalSize alpha i * midpointMultiplicity n alpha K i)
          + (∑ i, tangentDeficitNat i * midpointMultiplicity n alpha K i)
          = ∑ i, alpha * midpointMultiplicity n alpha K i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have ht : tangentDeficitNat i = fourDeficit i := rfl
      simp only [midpointPartialDiagonalSize, ht, ← Nat.add_mul]
      rw [Nat.sub_add_cancel (hd i)]
    rw [hstep, ← Finset.mul_sum, hsum]
  unfold selectedVertexMass
  obtain ⟨P, hP⟩ : ∃ P, alpha * K = P := ⟨_, rfl⟩
  rw [hP] at hsplit hmom hnK
  omega

private lemma aux_K_le_n (n alpha K : ℕ)
    (hadm : MidpointRoundingAdmissible n alpha K) : K ≤ n := by
  have hmass := aux_full_mass n alpha K hadm
  have hcd := midpointMultiplicity_count_deficit_intDisplacement n alpha K hadm
  obtain ⟨halpha, hK, hnK, -, -⟩ := hadm
  have h1 : ∀ i : Fin 4, 0 < midpointPartialDiagonalSize alpha i := by
    intro i
    have := i.isLt
    simp only [midpointPartialDiagonalSize, fourDeficit]
    omega
  calc K = ∑ i, midpointMultiplicity n alpha K i := hcd.1.symm
    _ ≤ ∑ i, midpointPartialDiagonalSize alpha i * midpointMultiplicity n alpha K i :=
        Finset.sum_le_sum fun i _ => Nat.le_mul_of_pos_left _ (h1 i)
    _ = n := hmass

private lemma aux_log_succ_le (n a : ℕ) (hn : 2 ≤ n) (ha : a ≤ n) :
    Real.log ((a + 1 : ℕ) : ℝ) ≤ 2 * Real.log (n : ℝ) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have haR : ((a + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : a + 1 ≤ n * n := by nlinarith [ha, hn]
    calc ((a + 1 : ℕ) : ℝ) ≤ ((n * n : ℕ) : ℝ) := by exact_mod_cast this
      _ = (n : ℝ) ^ 2 := by push_cast; ring
  have hpos : (0 : ℝ) < ((a + 1 : ℕ) : ℝ) := by positivity
  calc Real.log ((a + 1 : ℕ) : ℝ) ≤ Real.log ((n : ℝ) ^ 2) :=
        Real.log_le_log hpos haR
    _ = 2 * Real.log (n : ℝ) := by
        rw [Real.log_pow]; push_cast; ring

private lemma aux_one_le_log (n : ℕ) (hn : 3 ≤ n) : (1 : ℝ) ≤ Real.log (n : ℝ) := by
  have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlt : (1 : ℝ) < Real.log 3 := by
    have h1 : Real.log (Real.exp 1) < Real.log 3 := by
      apply Real.log_lt_log (Real.exp_pos 1)
      linarith [Real.exp_one_lt_d9]
    simpa using h1
  have hmono : Real.log 3 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) h3
  linarith

private lemma aux_error_bound (n r : ℕ) (k : Fin 4 → ℕ) (hn : 3 ≤ n)
    (hk : ∀ i, k i ≤ n) (hr : r ≤ n) :
    (∑ i, 2 * factorialLogErrorBound (k i)) + factorialLogErrorBound r
      ≤ 54 * logOrder n := by
  have hlog1 := aux_one_le_log n hn
  have hb : ∀ a : ℕ, a ≤ n → factorialLogErrorBound a ≤ 2 * Real.log (n : ℝ) + 4 := by
    intro a ha
    have := aux_log_succ_le n a (by omega) ha
    simp only [factorialLogErrorBound]
    linarith
  have h0 := hb (k 0) (hk 0)
  have h1 := hb (k 1) (hk 1)
  have h2 := hb (k 2) (hk 2)
  have h3 := hb (k 3) (hk 3)
  have h4 := hb r hr
  simp only [Fin.sum_univ_four, logOrder]
  linarith

private lemma aux_envelope_identity (n alpha K : ℕ) (ell : Fin 4 → ℕ)
    (hn : 0 < n) (hK : 0 < K)
    (hell : IsPartialSubprofile (midpointMultiplicity n alpha K) ell)
    (hmle : selectedVertexMass (midpointPartialDiagonalSize alpha) ell ≤ n) :
    (n : ℝ) * midpointPartialDiagonalRho n alpha ell *
        Real.log (midpointPartialDiagonalRho n alpha ell)
      + (K : ℝ) * ∑ i : Fin 4,
          (2 * midpointPartialDiagonalP n alpha K i *
              Real.log (midpointPartialDiagonalP n alpha K i)
            - 2 * midpointPartialDiagonalZ n alpha K ell i *
                Real.log (midpointPartialDiagonalZ n alpha K ell i)
            - midpointPartialDiagonalY K ell i *
                Real.log (midpointPartialDiagonalY K ell i)
            - midpointPartialDiagonalY K ell i
            + midpointPartialDiagonalY K ell i *
                midpointPartialDiagonalE n alpha K i)
      = (∑ i : Fin 4,
            (2 * factorialEntropyMain (midpointMultiplicity n alpha K i)
              - factorialEntropyMain (ell i)
              - 2 * factorialEntropyMain (midpointMultiplicity n alpha K i - ell i)
              + (ell i : ℝ) *
                  Real.log (((midpointPartialDiagonalSize alpha i).factorial : ℕ) : ℝ)))
        + factorialEntropyMain
            (n - selectedVertexMass (midpointPartialDiagonalSize alpha) ell)
        - factorialEntropyMain n
        + (selectedInternalEdgeCount (midpointPartialDiagonalSize alpha) ell : ℝ)
            * Real.log 2
        - (selectedBlockCount ell : ℝ) * Real.log 2 := by
  have hKne : ((K : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hK.ne'
  have hnne : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  -- the residual entropy term
  have hrho : (n : ℝ) * midpointPartialDiagonalRho n alpha ell *
        Real.log (midpointPartialDiagonalRho n alpha ell)
      = factorialEntropyMain
            (n - selectedVertexMass (midpointPartialDiagonalSize alpha) ell)
        + ((n - selectedVertexMass (midpointPartialDiagonalSize alpha) ell : ℕ) : ℝ)
        - ((n - selectedVertexMass (midpointPartialDiagonalSize alpha) ell : ℕ) : ℝ)
            * Real.log (n : ℝ) := by
    unfold midpointPartialDiagonalRho
    rw [show (n : ℝ) *
        (((n - selectedVertexMass (midpointPartialDiagonalSize alpha) ell : ℕ) : ℝ)
          / (n : ℝ))
        = ((n - selectedVertexMass (midpointPartialDiagonalSize alpha) ell : ℕ) : ℝ) by
      field_simp]
    exact aux_entropy_div n _ hn
  have hcoord : ∀ i : Fin 4,
      (K : ℝ) * (2 * midpointPartialDiagonalP n alpha K i *
              Real.log (midpointPartialDiagonalP n alpha K i)
            - 2 * midpointPartialDiagonalZ n alpha K ell i *
                Real.log (midpointPartialDiagonalZ n alpha K ell i)
            - midpointPartialDiagonalY K ell i *
                Real.log (midpointPartialDiagonalY K ell i)
            - midpointPartialDiagonalY K ell i
            + midpointPartialDiagonalY K ell i *
                midpointPartialDiagonalE n alpha K i)
      = 2 * factorialEntropyMain (midpointMultiplicity n alpha K i)
        - factorialEntropyMain (ell i)
        - 2 * factorialEntropyMain (midpointMultiplicity n alpha K i - ell i)
        + (ell i : ℝ) *
            Real.log (((midpointPartialDiagonalSize alpha i).factorial : ℕ) : ℝ)
        + (ell i : ℝ) * (midpointPartialDiagonalSize alpha i : ℝ)
        - (ell i : ℝ) * (midpointPartialDiagonalSize alpha i : ℝ) * Real.log (n : ℝ)
        + Real.log 2 * ((ell i : ℝ) *
            (((midpointPartialDiagonalSize alpha i).choose 2 : ℕ) : ℝ))
        - Real.log 2 * (ell i : ℝ) := by
    intro i
    have hcast : ((midpointMultiplicity n alpha K i - ell i : ℕ) : ℝ)
        = (midpointMultiplicity n alpha K i : ℝ) - (ell i : ℝ) := by
      exact_mod_cast Nat.cast_sub (hell i)
    have hz : midpointPartialDiagonalZ n alpha K ell i
        = ((midpointMultiplicity n alpha K i - ell i : ℕ) : ℝ) / (K : ℝ) := by
      unfold midpointPartialDiagonalZ midpointPartialDiagonalP midpointPartialDiagonalY
      rw [hcast]
      ring
    have hA := aux_entropy_div K (midpointMultiplicity n alpha K i) hK
    have hB := aux_entropy_div K (ell i) hK
    have hC := aux_entropy_div K (midpointMultiplicity n alpha K i - ell i) hK
    rw [hz]
    unfold midpointPartialDiagonalP midpointPartialDiagonalY midpointPartialDiagonalE
    rw [aux_coord_scalar (K : ℝ) _ _ _ _ _ _ _ hKne]
    rw [hcast] at hC ⊢
    simp only [logOrder, q]
    linear_combination 2 * hA - hB - 2 * hC
  rw [hrho, Finset.mul_sum,
    Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) => hcoord i),
    factorialEntropyMain_of_pos hn]
  have hmR : ((selectedVertexMass (midpointPartialDiagonalSize alpha) ell : ℕ) : ℝ)
      = ∑ i, ((midpointPartialDiagonalSize alpha i : ℝ) * (ell i : ℝ)) := by
    unfold selectedVertexMass
    push_cast
    ring
  have hMR : ((selectedInternalEdgeCount (midpointPartialDiagonalSize alpha) ell : ℕ) : ℝ)
      = ∑ i, ((((midpointPartialDiagonalSize alpha i).choose 2 : ℕ) : ℝ) * (ell i : ℝ)) := by
    unfold selectedInternalEdgeCount
    push_cast
    ring
  have hLR : ((selectedBlockCount ell : ℕ) : ℝ) = ∑ i, (ell i : ℝ) := by
    unfold selectedBlockCount
    push_cast
    ring
  have hnmR : ((n - selectedVertexMass (midpointPartialDiagonalSize alpha) ell : ℕ) : ℝ)
      = (n : ℝ) - ∑ i, ((midpointPartialDiagonalSize alpha i : ℝ) * (ell i : ℝ)) := by
    rw [Nat.cast_sub hmle, hmR]
  rw [hnmR, hMR, hLR]
  simp only [Fin.sum_univ_four]
  ring

/-- The exact midpoint partial-diagonal weight lies below the one-sided
four-coordinate logarithmic envelope, with one uniform logarithmic error.
No central-range cutoff is needed for this finite expansion. -/
theorem partialDiagonal_log_upper_envelope_midpoint_fourDeficit :
    ∃ C : Real, 0 ≤ C ∧
      ∃ N₀ : Nat, ∀ n alpha K : Nat, N₀ ≤ n →
        MidpointRoundingAdmissible n alpha K →
          ∀ ell : Fin 4 → Nat,
            IsPartialSubprofile (midpointMultiplicity n alpha K) ell →
            Real.log
                (partialDiagonalWeight n (midpointPartialDiagonalSize alpha)
                  (midpointMultiplicity n alpha K) ell) ≤
              (n : Real) * midpointPartialDiagonalRho n alpha ell *
                  Real.log (midpointPartialDiagonalRho n alpha ell)
                + (K : Real) * ∑ i : Fin 4,
                    (2 * midpointPartialDiagonalP n alpha K i *
                        Real.log (midpointPartialDiagonalP n alpha K i)
                      - 2 * midpointPartialDiagonalZ n alpha K ell i *
                          Real.log (midpointPartialDiagonalZ n alpha K ell i)
                      - midpointPartialDiagonalY K ell i *
                          Real.log (midpointPartialDiagonalY K ell i)
                      - midpointPartialDiagonalY K ell i
                      + midpointPartialDiagonalY K ell i *
                          midpointPartialDiagonalE n alpha K i)
                + C * logOrder n := by
  refine ⟨54, by norm_num, 3, ?_⟩
  intro n alpha K hn hadm ell hell
  have hn0 : 0 < n := by omega
  have hmass := aux_full_mass n alpha K hadm
  have hKn := aux_K_le_n n alpha K hadm
  have hcd := midpointMultiplicity_count_deficit_intDisplacement n alpha K hadm
  have hK : 0 < K := hadm.2.1
  have hkin : ∀ i : Fin 4, midpointMultiplicity n alpha K i ≤ n := by
    intro i
    have hle : midpointMultiplicity n alpha K i
        ≤ ∑ j, midpointMultiplicity n alpha K j :=
      Finset.single_le_sum (f := fun j => midpointMultiplicity n alpha K j)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have hmle : selectedVertexMass (midpointPartialDiagonalSize alpha) ell ≤ n := by
    calc selectedVertexMass (midpointPartialDiagonalSize alpha) ell
        ≤ selectedVertexMass (midpointPartialDiagonalSize alpha)
            (midpointMultiplicity n alpha K) :=
          Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (hell i)
      _ = n := hmass
  rw [aux_log_weight n (midpointPartialDiagonalSize alpha)
    (midpointMultiplicity n alpha K) ell hell]
  rw [aux_envelope_identity n alpha K ell hn0 hK hell hmle]
  have hstir : (∑ i : Fin 4,
        (2 * Real.log (((midpointMultiplicity n alpha K i).factorial : ℕ) : ℝ)
          - Real.log (((ell i).factorial : ℕ) : ℝ)
          - 2 * Real.log (((midpointMultiplicity n alpha K i - ell i).factorial : ℕ) : ℝ)
          + (ell i : ℝ) *
              Real.log (((midpointPartialDiagonalSize alpha i).factorial : ℕ) : ℝ)))
      ≤ (∑ i : Fin 4,
          (2 * factorialEntropyMain (midpointMultiplicity n alpha K i)
            - factorialEntropyMain (ell i)
            - 2 * factorialEntropyMain (midpointMultiplicity n alpha K i - ell i)
            + (ell i : ℝ) *
                Real.log (((midpointPartialDiagonalSize alpha i).factorial : ℕ) : ℝ)
            + 2 * factorialLogErrorBound (midpointMultiplicity n alpha K i))) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 := log_factorial_le_factorialEntropyMain_add_error
      (midpointMultiplicity n alpha K i)
    have h2 := factorialEntropyMain_le_log_factorial (ell i)
    have h3 := factorialEntropyMain_le_log_factorial
      (midpointMultiplicity n alpha K i - ell i)
    linarith
  have hnmU := log_factorial_le_factorialEntropyMain_add_error
    (n - selectedVertexMass (midpointPartialDiagonalSize alpha) ell)
  have hnL := factorialEntropyMain_le_log_factorial n
  have herr := aux_error_bound n
    (n - selectedVertexMass (midpointPartialDiagonalSize alpha) ell)
    (midpointMultiplicity n alpha K) hn hkin (by omega)
  have hsplit : (∑ i : Fin 4,
          (2 * factorialEntropyMain (midpointMultiplicity n alpha K i)
            - factorialEntropyMain (ell i)
            - 2 * factorialEntropyMain (midpointMultiplicity n alpha K i - ell i)
            + (ell i : ℝ) *
                Real.log (((midpointPartialDiagonalSize alpha i).factorial : ℕ) : ℝ)
            + 2 * factorialLogErrorBound (midpointMultiplicity n alpha K i)))
      = (∑ i : Fin 4,
          (2 * factorialEntropyMain (midpointMultiplicity n alpha K i)
            - factorialEntropyMain (ell i)
            - 2 * factorialEntropyMain (midpointMultiplicity n alpha K i - ell i)
            + (ell i : ℝ) *
                Real.log (((midpointPartialDiagonalSize alpha i).factorial : ℕ) : ℝ)))
        + ∑ i : Fin 4, 2 * factorialLogErrorBound (midpointMultiplicity n alpha K i) := by
    rw [← Finset.sum_add_distrib]
  rw [hsplit] at hstir
  linarith

end

end Erdos625
