import Erdos625.Section8EndpointLocalSquaredTransport
import Erdos625.Section8RealizedTableDeficitSum
import Erdos625.Section8EndpointGlobalTransport
import Erdos625.Section8RowAssignmentExpansion
import Erdos625.PartialDiagonalDecayReindexing
import Erdos625.WeightedCauchyTools

/-!
# Fused weighted endpoint row sum

This module defines the exact fused endpoint row sum.  The final asymptotic
estimate for its maximum is proved downstream.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- Type-preserving geometric deficit factor for one endpoint cell. -/
def fourEndpointThreeQuarterDeficitFactor
    (n alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4) : ENNReal :=
  1 + 2 * threeQuarterHighCellBase n
    (fourEndpointOverlapSize alpha hAlpha i j)

/-- Product of the type-preserving deficit factor and endpoint transport
kernel for one cell. -/
def fourEndpointFusedKernel
    (n alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4) : ENNReal :=
  fourEndpointThreeQuarterDeficitFactor n alpha hAlpha i j *
    ENNReal.ofReal (fourEndpointQ n alpha hAlpha i j)

/-- One row sum of the fused four-by-four endpoint kernel. -/
def fourEndpointFusedRowSum
    (n alpha : Nat) (hAlpha : 5 < alpha) (i : Fin 4) : ENNReal :=
  ∑ j : Fin 4, fourEndpointFusedKernel n alpha hAlpha i j

/-- Maximum of the four fused endpoint-kernel row sums. -/
def fourEndpointFusedRowMax
    (n alpha : Nat) (hAlpha : 5 < alpha) : ENNReal :=
  Finset.univ.sup fun i : Fin 4 =>
    fourEndpointFusedRowSum n alpha hAlpha i

/-- Indicator that an endpoint size is degenerate (at most one). -/
private def e625Ind (x : ℕ) : ℕ := if x ≤ 1 then 1 else 0

private lemma e625_size_eq (alpha : Nat) (hAlpha : 5 < alpha) (i : Fin 4) :
    fourEndpointSize alpha hAlpha i = alpha - 2 - i.val := by
  unfold fourEndpointSize fourEndpointCoordinate fourDeficitCoordinate
  simp [fourDeficit]
  omega

private lemma e625_signReward_pow (x : ℕ) :
    2 * (localSignRewardNat x * 2 ^ e625Ind x) = 2 ^ (x.choose 2 + 2 * e625Ind x) := by
  rcases Nat.lt_or_ge x 3 with hx | hx
  · interval_cases x <;> norm_num [localSignRewardNat, e625Ind]
  · have h1 : 1 ≤ x.choose 2 := by
      have h := Nat.choose_le_choose 2 hx
      norm_num at h
      omega
    have hind : e625Ind x = 0 := by
      simp only [e625Ind, if_neg (by omega : ¬ x ≤ 1)]
    simp only [localSignRewardNat, if_pos hx, hind, mul_zero, pow_zero, mul_one, add_zero]
    rw [← pow_succ']
    congr 1
    omega

private lemma e625_choose_two_add (u d : ℕ) :
    (u + d).choose 2 = u.choose 2 + d * u + d.choose 2 := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Nat.add_succ, Nat.choose_succ_succ]
      simp only [Nat.choose_one_right]
      rw [ih]
      have hd : (d + 1).choose 2 = d + d.choose 2 := by
        rw [Nat.choose_succ_succ]
        simp
      rw [hd]
      simp only [Nat.add_mul, one_mul]
      omega

/-- Corrected diagonal-factor transport, valid for all sizes (no `8 < alpha`). -/
private lemma e625_diag_ratio (u v : ℕ) (h : u ≤ v) :
    (v.factorial * localSignRewardNat v) * 2 ^ e625Ind u
      = (u.factorial * localSignRewardNat u) * v.descFactorial (v - u)
          * 2 ^ ((v - u) * u + (v - u).choose 2) * 2 ^ e625Ind v := by
  obtain ⟨d, rfl⟩ : ∃ d, v = u + d := ⟨v - u, by omega⟩
  have hd : u + d - u = d := by omega
  rw [hd]
  have hfac : u.factorial * (u + d).descFactorial d = (u + d).factorial := by
    simpa using Nat.factorial_mul_descFactorial (show d ≤ u + d by omega)
  have hch := e625_choose_two_add u d
  -- reduce to the sign-reward exponent identity
  have key : localSignRewardNat (u + d) * 2 ^ e625Ind u
      = localSignRewardNat u * 2 ^ (d * u + d.choose 2) * 2 ^ e625Ind (u + d) := by
    have h1 := e625_signReward_pow (u + d)
    have h2 := e625_signReward_pow u
    have hmul : (2 * 2 ^ e625Ind u * 2 ^ e625Ind (u+d)) *
          (localSignRewardNat (u + d) * 2 ^ e625Ind u)
        = (2 * 2 ^ e625Ind u * 2 ^ e625Ind (u+d)) *
          (localSignRewardNat u * 2 ^ (d * u + d.choose 2) * 2 ^ e625Ind (u + d)) := by
      calc (2 * 2 ^ e625Ind u * 2 ^ e625Ind (u+d)) *
            (localSignRewardNat (u + d) * 2 ^ e625Ind u)
          = (2 * (localSignRewardNat (u+d) * 2 ^ e625Ind (u+d))) *
              (2 ^ e625Ind u * 2 ^ e625Ind u) := by ring
        _ = 2 ^ ((u+d).choose 2 + 2 * e625Ind (u+d)) * (2 ^ e625Ind u * 2 ^ e625Ind u) := by
              rw [h1]
        _ = 2 ^ ((u+d).choose 2 + 2 * e625Ind (u+d) + (e625Ind u + e625Ind u)) := by
              rw [← pow_add, ← pow_add]
        _ = 2 ^ (u.choose 2 + 2 * e625Ind u + (d * u + d.choose 2) +
              (e625Ind (u+d) + e625Ind (u+d))) := by
              congr 1
              omega
        _ = (2 * (localSignRewardNat u * 2 ^ e625Ind u)) *
              (2 ^ (d * u + d.choose 2) * (2 ^ e625Ind (u+d) * 2 ^ e625Ind (u+d))) := by
              rw [h2, ← pow_add, ← pow_add, ← pow_add]
              congr 1
              omega
        _ = (2 * 2 ^ e625Ind u * 2 ^ e625Ind (u+d)) *
              (localSignRewardNat u * 2 ^ (d * u + d.choose 2) * 2 ^ e625Ind (u + d)) := by
              ring
    have hposl : 0 < 2 * 2 ^ e625Ind u * 2 ^ e625Ind (u+d) := by positivity
    exact Nat.eq_of_mul_eq_mul_left hposl hmul
  calc (u + d).factorial * localSignRewardNat (u + d) * 2 ^ e625Ind u
      = ((u.factorial * (u+d).descFactorial d)) * (localSignRewardNat (u+d) * 2 ^ e625Ind u) := by
        rw [hfac]; ring
    _ = (u.factorial * (u+d).descFactorial d) *
          (localSignRewardNat u * 2 ^ (d * u + d.choose 2) * 2 ^ e625Ind (u + d)) := by rw [key]
    _ = u.factorial * localSignRewardNat u * (u+d).descFactorial d *
          2 ^ (d * u + d.choose 2) * 2 ^ e625Ind (u + d) := by ring

private def e625Gt (x : ℕ) : ℕ := x.factorial * localSignRewardNat x

private lemma e625_Q_nonneg (n alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4) :
    0 ≤ fourEndpointQ n alpha hAlpha i j := by
  unfold fourEndpointQ
  have h1 : (0:ℝ) ≤ Real.rpow ((n + 1 : Nat) : Real) ((fourEndpointDistance i j : Real) / 2) :=
    Real.rpow_nonneg (by positivity) _
  have h2 : (0:ℝ) ≤ Real.sqrt ((fourEndpointUpperSize alpha hAlpha i j).descFactorial
      (fourEndpointDistance i j) : Real) := Real.sqrt_nonneg _
  have h3 : (0:ℝ) ≤ Real.rpow 2
      (-((fourEndpointDistance i j * fourEndpointLowerSize alpha hAlpha i j +
        (fourEndpointDistance i j).choose 2 : Nat) : Real) / 2) := Real.rpow_nonneg (by norm_num) _
  positivity

private lemma e625_rpow_sq (x c : ℝ) (hx : 0 < x) :
    (Real.rpow x c) ^ 2 = Real.rpow x (2 * c) := by
  have h := Real.rpow_add hx c c
  show Real.rpow x c ^ 2 = Real.rpow x (2 * c)
  rw [pow_two, show (2:ℝ) * c = c + c by ring]
  exact h.symm

private lemma e625_Q_sq_real (n alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4) :
    (fourEndpointQ n alpha hAlpha i j) ^ 2 *
        ((((fourEndpointDistance i j).factorial ^ 2 *
            2 ^ (fourEndpointDistance i j * fourEndpointLowerSize alpha hAlpha i j +
              (fourEndpointDistance i j).choose 2) : ℕ) : Real))
      = (((n + 1) ^ (fourEndpointDistance i j) *
          (fourEndpointUpperSize alpha hAlpha i j).descFactorial
            (fourEndpointDistance i j) : ℕ) : Real) := by
  set d := fourEndpointDistance i j with hd
  set e := d * fourEndpointLowerSize alpha hAlpha i j + d.choose 2 with he
  set U := (fourEndpointUpperSize alpha hAlpha i j).descFactorial d with hU
  set A := Real.rpow ((n + 1 : Nat) : Real) ((d : Real) / 2) with hA0
  set B := Real.sqrt ((U : Nat) : Real) with hB0
  set C := ((d.factorial : Nat) : Real) with hC0
  set D := Real.rpow 2 (-((e : Nat) : Real) / 2) with hD0
  have hnpos : (0:ℝ) < ((n + 1 : Nat) : Real) := by positivity
  have hA : A ^ 2 = ((n + 1 : Nat) : Real) ^ d := by
    rw [hA0, e625_rpow_sq _ _ hnpos, show (2 : Real) * ((d : Real) / 2) = (d : Real) by ring]
    exact Real.rpow_natCast _ d
  have hB : B ^ 2 = (U : Real) := Real.sq_sqrt (by positivity)
  have hD : D ^ 2 * ((2:Real) ^ e) = 1 := by
    rw [hD0, e625_rpow_sq _ _ (by norm_num : (0:ℝ) < 2),
      show (2 : Real) * (-((e : Nat) : Real) / 2) = -((e : Nat) : Real) by ring,
      show Real.rpow 2 (-((e : Nat) : Real)) = (Real.rpow 2 ((e : Nat) : Real))⁻¹ from
        Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) _,
      show Real.rpow 2 ((e : Nat) : Real) = (2:Real) ^ e from Real.rpow_natCast _ e]
    field_simp
  have hCne : C ≠ 0 := by
    rw [hC0]
    exact_mod_cast Nat.factorial_ne_zero d
  have hQ : fourEndpointQ n alpha hAlpha i j = A * B / C * D := rfl
  rw [hQ]
  have hcast : ((((d.factorial) ^ 2 * 2 ^ e : ℕ)) : Real) = C ^ 2 * (2:Real) ^ e := by
    rw [hC0]; push_cast; ring
  have hcast2 : (((n + 1) ^ d * U : ℕ) : Real) = ((n+1 : Nat) : Real) ^ d * (U : Real) := by
    push_cast; ring
  rw [hcast, hcast2]
  have expand : (A * B / C * D) ^ 2 * (C ^ 2 * (2:Real) ^ e)
      = (A ^ 2 * B ^ 2) * (D ^ 2 * (2:Real) ^ e) := by
    field_simp
  rw [expand, hA, hB, hD, mul_one]


private lemma e625_dist_eq (alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4) :
    fourEndpointUpperSize alpha hAlpha i j - fourEndpointLowerSize alpha hAlpha i j
      = fourEndpointDistance i j := by
  have hsize := e625_size_eq alpha hAlpha
  unfold fourEndpointUpperSize fourEndpointLowerSize fourEndpointDistance
  rw [hsize, hsize, Nat.dist_eq_max_sub_min]
  by_cases hij : i.val ≤ j.val
  · have hs : alpha - 2 - j.val ≤ alpha - 2 - i.val := by omega
    rw [max_eq_left hs, min_eq_right hs, max_eq_right hij, min_eq_left hij]
    omega
  · have hji : j.val ≤ i.val := by omega
    have hs : alpha - 2 - i.val ≤ alpha - 2 - j.val := by omega
    rw [max_eq_right hs, min_eq_left hs, max_eq_left hji, min_eq_right hji]
    omega

private lemma e625_low_le_up (alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4) :
    fourEndpointLowerSize alpha hAlpha i j ≤ fourEndpointUpperSize alpha hAlpha i j := by
  unfold fourEndpointLowerSize fourEndpointUpperSize
  exact min_le_max

/-- The per-cell transport defect: the charge assigned to the row endpoint. -/
private def e625Charge (alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4) : ℕ :=
  if fourEndpointSize alpha hAlpha i ≤ 1 ∧ 2 ≤ fourEndpointSize alpha hAlpha j then 2 else 1

/-- The total per-cell transport defect. -/
private def e625Lam (alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4) : ℕ :=
  e625Charge alpha hAlpha i j * e625Charge alpha hAlpha j i

private lemma e625_lam_ind (alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4) :
    e625Lam alpha hAlpha i j * 2 ^ e625Ind (fourEndpointUpperSize alpha hAlpha i j)
      = 2 ^ e625Ind (fourEndpointLowerSize alpha hAlpha i j) := by
  unfold e625Lam e625Charge e625Ind fourEndpointUpperSize fourEndpointLowerSize
  rcases le_total (fourEndpointSize alpha hAlpha i) (fourEndpointSize alpha hAlpha j) with h | h
  · rw [min_eq_left h, max_eq_right h]; split_ifs <;> simp_all <;> omega
  · rw [min_eq_right h, max_eq_left h]; split_ifs <;> simp_all <;> omega

private lemma e625_nat_cell (u v : ℕ) (h : u ≤ v) :
    (e625Gt u * v.choose (v - u)) ^ 2 *
        ((v - u).factorial ^ 2 * 2 ^ ((v - u) * u + (v - u).choose 2)) * 2 ^ e625Ind v
      = e625Gt u * e625Gt v * v.descFactorial (v - u) * 2 ^ e625Ind u := by
  set d := v - u with hd
  have hdesc : v.descFactorial d = d.factorial * v.choose d :=
    Nat.descFactorial_eq_factorial_mul_choose v d
  have hratio := e625_diag_ratio u v h
  rw [← hd] at hratio
  calc (e625Gt u * v.choose d) ^ 2 * (d.factorial ^ 2 * 2 ^ (d * u + d.choose 2)) * 2 ^ e625Ind v
      = (e625Gt u * v.descFactorial d) *
          (e625Gt u * v.descFactorial d * 2 ^ (d * u + d.choose 2) * 2 ^ e625Ind v) := by
        rw [hdesc]; ring
    _ = (e625Gt u * v.descFactorial d) * (e625Gt v * 2 ^ e625Ind u) := by
        have hkey : e625Gt u * v.descFactorial d * 2 ^ (d * u + d.choose 2) * 2 ^ e625Ind v
            = e625Gt v * 2 ^ e625Ind u := by
          unfold e625Gt
          rw [hratio]
        rw [hkey]
    _ = e625Gt u * e625Gt v * v.descFactorial d * 2 ^ e625Ind u := by ring



/-! ### Global architecture -/

/-- Transpose of a full-cell table. -/
private def e625Tr (L : FourEndpointFullTable) : FourEndpointFullTable :=
  ⟨fun i j => L.toFun j i⟩

/-- Product over rows of the row multinomial coefficients. -/
private def e625Mult (L : FourEndpointFullTable) : ℕ :=
  ∏ i : Fin 4, Nat.multinomial Finset.univ (fun j => L.toFun i j)

/-- The charged fused kernel. -/
private def e625Kern (n alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4) : ENNReal :=
  (e625Charge alpha hAlpha i j : ENNReal) * fourEndpointFusedKernel n alpha hAlpha i j

/-- The charged row sum. -/
private def e625A (n alpha : Nat) (hAlpha : 5 < alpha) (i : Fin 4) : ENNReal :=
  ∑ j : Fin 4, e625Kern n alpha hAlpha i j

/-- The row half of the transported per-table majorant. -/
private def e625X (n alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable) : ENNReal :=
  fourEndpointD n alpha hAlpha k (fun i => fourEndpointRowMargin L i) *
    (e625Mult L : ENNReal) *
    ∏ i : Fin 4, ∏ j : Fin 4, (e625Kern n alpha hAlpha i j) ^ L.toFun i j

private lemma e625_Q_sq_ennreal (n alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4) :
    (ENNReal.ofReal (fourEndpointQ n alpha hAlpha i j)) ^ 2 *
        ((((fourEndpointDistance i j).factorial ^ 2 *
            2 ^ (fourEndpointDistance i j * fourEndpointLowerSize alpha hAlpha i j +
              (fourEndpointDistance i j).choose 2) : ℕ) : ENNReal))
      = (((n + 1) ^ (fourEndpointDistance i j) *
          (fourEndpointUpperSize alpha hAlpha i j).descFactorial
            (fourEndpointDistance i j) : ℕ) : ENNReal) := by
  have hQ := e625_Q_sq_real n alpha hAlpha i j
  have hnn := e625_Q_nonneg n alpha hAlpha i j
  have h := congrArg ENNReal.ofReal hQ
  rwa [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hnn,
    ENNReal.ofReal_natCast, ENNReal.ofReal_natCast] at h

private lemma e625_cell_identity (n alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4) :
    (fourEndpointLocalCellFactor alpha hAlpha i j) ^ 2 *
        (((n + 1) ^ (fourEndpointDistance i j) : ℕ) : ENNReal)
      = (e625Lam alpha hAlpha i j : ENNReal) *
          fourEndpointDiagonalLocalFactor alpha hAlpha i *
          fourEndpointDiagonalLocalFactor alpha hAlpha j *
          (ENNReal.ofReal (fourEndpointQ n alpha hAlpha i j)) ^ 2 := by
  have hlu : fourEndpointLowerSize alpha hAlpha i j ≤ fourEndpointUpperSize alpha hAlpha i j :=
    e625_low_le_up alpha hAlpha i j
  have hdist : fourEndpointUpperSize alpha hAlpha i j -
      fourEndpointLowerSize alpha hAlpha i j = fourEndpointDistance i j :=
    e625_dist_eq alpha hAlpha i j
  set d := fourEndpointDistance i j with hdd
  set low := fourEndpointLowerSize alpha hAlpha i j with hlow
  set up := fourEndpointUpperSize alpha hAlpha i j with hup
  have hg : fourEndpointLocalCellFactor alpha hAlpha i j
      = ((e625Gt low * up.choose d : ℕ) : ENNReal) := by
    rw [fourEndpointLocalCellFactor_eq_lowerDiagonal_mul_choose]
    unfold fourEndpointSizeDiagonalFactor e625Gt
    push_cast
    ring
  have hGij : fourEndpointDiagonalLocalFactor alpha hAlpha i *
      fourEndpointDiagonalLocalFactor alpha hAlpha j
      = ((e625Gt low * e625Gt up : ℕ) : ENNReal) := by
    have hnat : e625Gt (fourEndpointSize alpha hAlpha i) *
        e625Gt (fourEndpointSize alpha hAlpha j) = e625Gt low * e625Gt up := by
      rw [hlow, hup]
      unfold fourEndpointLowerSize fourEndpointUpperSize
      rcases le_total (fourEndpointSize alpha hAlpha i) (fourEndpointSize alpha hAlpha j)
        with h | h
      · rw [min_eq_left h, max_eq_right h]
      · rw [min_eq_right h, max_eq_left h]; ring
    rw [← hnat]
    unfold fourEndpointDiagonalLocalFactor e625Gt
    push_cast
    ring
  have hnatcell := e625_nat_cell low up hlu
  rw [hdist] at hnatcell
  have hlam := e625_lam_ind alpha hAlpha i j
  rw [← hlow, ← hup] at hlam
  have hnat : (e625Gt low * up.choose d) ^ 2 * (n + 1) ^ d *
        (d.factorial ^ 2 * 2 ^ (d * low + d.choose 2) * 2 ^ e625Ind up)
      = e625Lam alpha hAlpha i j * (e625Gt low * e625Gt up) *
          ((n + 1) ^ d * up.descFactorial d) * 2 ^ e625Ind up := by
    calc (e625Gt low * up.choose d) ^ 2 * (n + 1) ^ d *
          (d.factorial ^ 2 * 2 ^ (d * low + d.choose 2) * 2 ^ e625Ind up)
        = ((e625Gt low * up.choose d) ^ 2 *
            (d.factorial ^ 2 * 2 ^ (d * low + d.choose 2)) * 2 ^ e625Ind up) *
              (n + 1) ^ d := by ring
      _ = (e625Gt low * e625Gt up * up.descFactorial d * 2 ^ e625Ind low) * (n + 1) ^ d := by
            rw [hnatcell]
      _ = (e625Gt low * e625Gt up) * ((n + 1) ^ d * up.descFactorial d) *
            (e625Lam alpha hAlpha i j * 2 ^ e625Ind up) := by
            rw [hlam]; ring
      _ = e625Lam alpha hAlpha i j * (e625Gt low * e625Gt up) *
            ((n + 1) ^ d * up.descFactorial d) * 2 ^ e625Ind up := by ring
  set c : ENNReal :=
    ((d.factorial ^ 2 * 2 ^ (d * low + d.choose 2) * 2 ^ e625Ind up : ℕ) : ENNReal) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    have : d.factorial ^ 2 * 2 ^ (d * low + d.choose 2) * 2 ^ e625Ind up ≠ 0 := by
      have := Nat.factorial_ne_zero d
      positivity
    exact_mod_cast this
  have hct : c ≠ ⊤ := ENNReal.natCast_ne_top _
  refine (ENNReal.mul_left_inj hc0 hct).mp ?_
  have hQsq := e625_Q_sq_ennreal n alpha hAlpha i j
  rw [← hdd, ← hlow, ← hup] at hQsq
  calc fourEndpointLocalCellFactor alpha hAlpha i j ^ 2 * (((n + 1) ^ d : ℕ) : ENNReal) * c
      = (((e625Gt low * up.choose d) ^ 2 * (n + 1) ^ d *
          (d.factorial ^ 2 * 2 ^ (d * low + d.choose 2) * 2 ^ e625Ind up) : ℕ) : ENNReal) := by
        rw [hg, hc]; push_cast; ring
    _ = ((e625Lam alpha hAlpha i j * (e625Gt low * e625Gt up) *
          ((n + 1) ^ d * up.descFactorial d) * 2 ^ e625Ind up : ℕ) : ENNReal) := by
        rw [hnat]
    _ = (e625Lam alpha hAlpha i j : ENNReal) * ((e625Gt low * e625Gt up : ℕ) : ENNReal) *
          ((((n + 1) ^ d * up.descFactorial d : ℕ)) : ENNReal) *
          ((2 ^ e625Ind up : ℕ) : ENNReal) := by push_cast; ring
    _ = (e625Lam alpha hAlpha i j : ENNReal) * ((e625Gt low * e625Gt up : ℕ) : ENNReal) *
          ((ENNReal.ofReal (fourEndpointQ n alpha hAlpha i j)) ^ 2 *
            ((d.factorial ^ 2 * 2 ^ (d * low + d.choose 2) : ℕ) : ENNReal)) *
          ((2 ^ e625Ind up : ℕ) : ENNReal) := by rw [hQsq]
    _ = (e625Lam alpha hAlpha i j : ENNReal) *
          fourEndpointDiagonalLocalFactor alpha hAlpha i *
          fourEndpointDiagonalLocalFactor alpha hAlpha j *
          (ENNReal.ofReal (fourEndpointQ n alpha hAlpha i j)) ^ 2 * c := by
        have hgg : (e625Lam alpha hAlpha i j : ENNReal) *
            fourEndpointDiagonalLocalFactor alpha hAlpha i *
            fourEndpointDiagonalLocalFactor alpha hAlpha j
            = (e625Lam alpha hAlpha i j : ENNReal) *
              ((e625Gt low * e625Gt up : ℕ) : ENNReal) := by
          rw [mul_assoc, hGij]
        rw [hgg, hc]
        push_cast
        ring

/-! ### ENNReal division helpers -/

private lemma e625_div_div (a : ENNReal) (b c : ℕ) :
    a / (b : ENNReal) / (c : ENNReal) = a / ((b * c : ℕ) : ENNReal) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top c)) (Or.inl (ENNReal.natCast_ne_top b)),
    mul_assoc]

private lemma e625_div_mul_div (a c : ENNReal) (b d : ℕ) :
    (a / (b : ENNReal)) * (c / (d : ENNReal)) = (a * c) / ((b * d : ℕ) : ENNReal) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top d)) (Or.inl (ENNReal.natCast_ne_top b))]
  ring

private lemma e625_div_le_div_iff (a c : ENNReal) (b d : ℕ) (hb : b ≠ 0) (hd : d ≠ 0) :
    a / (b : ENNReal) ≤ c / (d : ENNReal) ↔ a * (d : ENNReal) ≤ c * (b : ENNReal) := by
  have hb0 : (b : ENNReal) ≠ 0 := by exact_mod_cast hb
  have hd0 : (d : ENNReal) ≠ 0 := by exact_mod_cast hd
  rw [ENNReal.div_le_iff hb0 (ENNReal.natCast_ne_top b),
    show c / (d : ENNReal) * (b : ENNReal) = c * (b : ENNReal) / (d : ENNReal) by
      rw [div_eq_mul_inv, div_eq_mul_inv]; ring,
    ENNReal.le_div_iff_mul_le (Or.inl hd0) (Or.inl (ENNReal.natCast_ne_top d))]

private lemma e625_two_mul_le_sq (x y : ENNReal) : 2 * (x * y) ≤ x ^ 2 + y ^ 2 := by
  rcases le_total x y with h | h
  · obtain ⟨t, rfl⟩ := le_iff_exists_add.mp h
    have hx : x ^ 2 + (x + t) ^ 2 = 2 * (x * (x + t)) + t ^ 2 := by ring
    rw [hx]
    exact self_le_add_right _ _
  · obtain ⟨t, rfl⟩ := le_iff_exists_add.mp h
    have hx : (y + t) ^ 2 + y ^ 2 = 2 * ((y + t) * y) + t ^ 2 := by ring
    rw [hx]
    exact self_le_add_right _ _

private lemma e625_amgm (a x y : ENNReal) (h : a ^ 2 ≤ x * y) : 2 * a ≤ x + y := by
  by_contra hc
  push Not at hc
  have h1 : (x + y) ^ 2 < (2 * a) ^ 2 := ENNReal.pow_lt_pow_left (by norm_num) hc
  have h3 : (2 * a) ^ 2 ≤ 4 * (x * y) := by
    calc (2 * a) ^ 2 = 4 * a ^ 2 := by ring
      _ ≤ 4 * (x * y) := by gcongr
  have h4 : 4 * (x * y) ≤ (x + y) ^ 2 := by
    have h5 := e625_two_mul_le_sq x y
    calc (4 : ENNReal) * (x * y) = 2 * (x * y) + 2 * (x * y) := by ring
      _ ≤ (x ^ 2 + y ^ 2) + 2 * (x * y) := by gcongr
      _ = (x + y) ^ 2 := by ring
  exact absurd (h1.trans_le (h3.trans h4)) (lt_irrefl _)

/-! ### Normal forms -/

private def e625Gnat (alpha : Nat) (hAlpha : 5 < alpha) (i : Fin 4) : ℕ :=
  e625Gt (fourEndpointSize alpha hAlpha i)

private def e625Gprod (alpha : Nat) (hAlpha : 5 < alpha) (r : Fin 4 → ℕ) : ℕ :=
  ∏ i : Fin 4, (e625Gnat alpha hAlpha i) ^ (r i)

private def e625Dnum (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) (r : Fin 4 → ℕ) : ℕ :=
  (fourEndpointMarginSelectionProduct alpha hAlpha k r) ^ 2 * e625Gprod alpha hAlpha r

private def e625Dden (n alpha : Nat) (hAlpha : 5 < alpha) (r : Fin 4 → ℕ) : ℕ :=
  fourEndpointMarginFactorialProduct r *
    n.descFactorial (fourEndpointMarginMass alpha hAlpha r)

private lemma e625_Gprod_cast (alpha : Nat) (hAlpha : 5 < alpha) (r : Fin 4 → ℕ) :
    fourEndpointDiagonalLocalProduct alpha hAlpha r
      = ((e625Gprod alpha hAlpha r : ℕ) : ENNReal) := by
  unfold fourEndpointDiagonalLocalProduct e625Gprod e625Gnat e625Gt
    fourEndpointDiagonalLocalFactor
  push_cast
  rfl

private lemma e625_D_eq (n alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) (r : Fin 4 → ℕ) :
    fourEndpointD n alpha hAlpha k r
      = ((e625Dnum alpha hAlpha k r : ℕ) : ENNReal) /
          ((e625Dden n alpha hAlpha r : ℕ) : ENNReal) := by
  unfold fourEndpointD e625Dnum e625Dden
  rw [e625_Gprod_cast, e625_div_mul_div]
  push_cast
  ring_nf

private lemma e625_W_eq (n alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) (L : FourEndpointFullTable) :
    fourEndpointW n alpha hAlpha k L
      = (((fourEndpointRowSelectionProduct alpha hAlpha k L *
            fourEndpointColumnSelectionProduct alpha hAlpha k L : ℕ)) : ENNReal) /
          ((fourEndpointCellFactorialProduct L *
            n.descFactorial (fourEndpointJ alpha hAlpha L) : ℕ) : ENNReal) *
          fourEndpointLocalProduct alpha hAlpha L := by
  unfold fourEndpointW
  rw [← e625_div_div]
  push_cast
  ring_nf

/-! ### Elementary table facts -/

private lemma e625_overlap_symm (alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4) :
    fourEndpointOverlapSize alpha hAlpha i j = fourEndpointOverlapSize alpha hAlpha j i := by
  unfold fourEndpointOverlapSize; exact min_comm _ _

private lemma e625_Q_symm (n alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4) :
    fourEndpointQ n alpha hAlpha i j = fourEndpointQ n alpha hAlpha j i := by
  unfold fourEndpointQ fourEndpointDistance fourEndpointUpperSize fourEndpointLowerSize
  rw [Nat.dist_comm, max_comm, min_comm]

private lemma e625_F_symm (n alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4) :
    fourEndpointThreeQuarterDeficitFactor n alpha hAlpha i j
      = fourEndpointThreeQuarterDeficitFactor n alpha hAlpha j i := by
  unfold fourEndpointThreeQuarterDeficitFactor
  rw [e625_overlap_symm alpha hAlpha i j]

private lemma e625_kernel_symm (n alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4) :
    fourEndpointFusedKernel n alpha hAlpha i j = fourEndpointFusedKernel n alpha hAlpha j i := by
  unfold fourEndpointFusedKernel fourEndpointThreeQuarterDeficitFactor
  rw [e625_overlap_symm alpha hAlpha i j, e625_Q_symm n alpha hAlpha i j]

private lemma e625_Tr_rowMargin (L : FourEndpointFullTable) (j : Fin 4) :
    fourEndpointRowMargin (e625Tr L) j = fourEndpointColumnMargin L j := rfl

private lemma e625_Tr_cellFact (L : FourEndpointFullTable) :
    fourEndpointCellFactorialProduct (e625Tr L) = fourEndpointCellFactorialProduct L := by
  unfold fourEndpointCellFactorialProduct e625Tr
  exact Finset.prod_comm

private lemma e625_mult_cellFact (L : FourEndpointFullTable) :
    e625Mult L * fourEndpointCellFactorialProduct L
      = ∏ i : Fin 4, (fourEndpointRowMargin L i).factorial := by
  unfold e625Mult fourEndpointCellFactorialProduct fourEndpointRowMargin
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by
    rw [mul_comm]
    exact Nat.multinomial_spec Finset.univ (fun j => L.toFun i j)

private lemma e625_pow_disp (n : Nat) (L : FourEndpointFullTable) :
    (n + 1) ^ fourEndpointDisplacement L
      = ∏ i : Fin 4, ∏ j : Fin 4,
          ((n + 1) ^ (fourEndpointDistance i j)) ^ L.toFun i j := by
  unfold fourEndpointDisplacement fourEndpointDistance
  simp_rw [← pow_mul]
  rw [Finset.prod_comm]
  simp_rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  exact Finset.sum_comm

private lemma e625_Gprod_row_col (alpha : Nat) (hAlpha : 5 < alpha)
    (L : FourEndpointFullTable) :
    e625Gprod alpha hAlpha (fun i => fourEndpointRowMargin L i) *
        e625Gprod alpha hAlpha (fun j => fourEndpointColumnMargin L j)
      = ∏ i : Fin 4, ∏ j : Fin 4,
          (e625Gnat alpha hAlpha i * e625Gnat alpha hAlpha j) ^ L.toFun i j := by
  unfold e625Gprod fourEndpointRowMargin fourEndpointColumnMargin
  have h1 : ∏ i : Fin 4, e625Gnat alpha hAlpha i ^ (∑ j : Fin 4, L.toFun i j)
      = ∏ i : Fin 4, ∏ j : Fin 4, e625Gnat alpha hAlpha i ^ L.toFun i j := by
    exact Finset.prod_congr rfl fun i _ => (Finset.prod_pow_eq_pow_sum _ _ _).symm
  have h2 : ∏ j : Fin 4, e625Gnat alpha hAlpha j ^ (∑ i : Fin 4, L.toFun i j)
      = ∏ i : Fin 4, ∏ j : Fin 4, e625Gnat alpha hAlpha j ^ L.toFun i j := by
    rw [Finset.prod_comm]
    exact Finset.prod_congr rfl fun j _ => (Finset.prod_pow_eq_pow_sum _ _ _).symm
  rw [h1, h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => (mul_pow _ _ _).symm

private lemma e625_cell_identity_kern (n alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4) :
    (fourEndpointLocalCellFactor alpha hAlpha i j *
        fourEndpointThreeQuarterDeficitFactor n alpha hAlpha i j) ^ 2 *
        (((n + 1) ^ (fourEndpointDistance i j) : ℕ) : ENNReal)
      = ((e625Gnat alpha hAlpha i * e625Gnat alpha hAlpha j : ℕ) : ENNReal) *
          (e625Kern n alpha hAlpha i j * e625Kern n alpha hAlpha j i) := by
  have hcell := e625_cell_identity n alpha hAlpha i j
  have hG : ((e625Gnat alpha hAlpha i * e625Gnat alpha hAlpha j : ℕ) : ENNReal)
      = fourEndpointDiagonalLocalFactor alpha hAlpha i *
        fourEndpointDiagonalLocalFactor alpha hAlpha j := by
    unfold e625Gnat e625Gt fourEndpointDiagonalLocalFactor
    push_cast
    ring
  have hlam : ((e625Lam alpha hAlpha i j : ℕ) : ENNReal)
      = ((e625Charge alpha hAlpha i j : ℕ) : ENNReal) *
        ((e625Charge alpha hAlpha j i : ℕ) : ENNReal) := by
    unfold e625Lam
    push_cast
    ring
  have hkern : e625Kern n alpha hAlpha i j * e625Kern n alpha hAlpha j i
      = (((e625Charge alpha hAlpha i j : ℕ) : ENNReal) *
          ((e625Charge alpha hAlpha j i : ℕ) : ENNReal)) *
        (fourEndpointThreeQuarterDeficitFactor n alpha hAlpha i j ^ 2 *
          (ENNReal.ofReal (fourEndpointQ n alpha hAlpha i j)) ^ 2) := by
    unfold e625Kern fourEndpointFusedKernel
    rw [e625_F_symm n alpha hAlpha j i, e625_Q_symm n alpha hAlpha j i]
    ring
  rw [hG, hkern, ← hlam]
  calc (fourEndpointLocalCellFactor alpha hAlpha i j *
        fourEndpointThreeQuarterDeficitFactor n alpha hAlpha i j) ^ 2 *
        (((n + 1) ^ (fourEndpointDistance i j) : ℕ) : ENNReal)
      = (fourEndpointLocalCellFactor alpha hAlpha i j ^ 2 *
          (((n + 1) ^ (fourEndpointDistance i j) : ℕ) : ENNReal)) *
          fourEndpointThreeQuarterDeficitFactor n alpha hAlpha i j ^ 2 := by ring
    _ = ((e625Lam alpha hAlpha i j : ENNReal) *
          fourEndpointDiagonalLocalFactor alpha hAlpha i *
          fourEndpointDiagonalLocalFactor alpha hAlpha j *
          (ENNReal.ofReal (fourEndpointQ n alpha hAlpha i j)) ^ 2) *
          fourEndpointThreeQuarterDeficitFactor n alpha hAlpha i j ^ 2 := by rw [hcell]
    _ = fourEndpointDiagonalLocalFactor alpha hAlpha i *
          fourEndpointDiagonalLocalFactor alpha hAlpha j *
          ((e625Lam alpha hAlpha i j : ENNReal) *
            (fourEndpointThreeQuarterDeficitFactor n alpha hAlpha i j ^ 2 *
              (ENNReal.ofReal (fourEndpointQ n alpha hAlpha i j)) ^ 2)) := by ring

private lemma e625_prod_cell_identity (n alpha : Nat) (hAlpha : 5 < alpha)
    (L : FourEndpointFullTable) :
    (∏ i : Fin 4, ∏ j : Fin 4,
        (fourEndpointLocalCellFactor alpha hAlpha i j *
          fourEndpointThreeQuarterDeficitFactor n alpha hAlpha i j) ^ L.toFun i j) ^ 2 *
        (((n + 1) ^ fourEndpointDisplacement L : ℕ) : ENNReal)
      = ((e625Gprod alpha hAlpha (fun i => fourEndpointRowMargin L i) *
          e625Gprod alpha hAlpha (fun j => fourEndpointColumnMargin L j) : ℕ) : ENNReal) *
        ((∏ i : Fin 4, ∏ j : Fin 4, (e625Kern n alpha hAlpha i j) ^ L.toFun i j) *
         (∏ i : Fin 4, ∏ j : Fin 4, (e625Kern n alpha hAlpha j i) ^ L.toFun i j)) := by
  have hdisp : (((n + 1) ^ fourEndpointDisplacement L : ℕ) : ENNReal)
      = ∏ i : Fin 4, ∏ j : Fin 4,
          ((((n + 1) ^ (fourEndpointDistance i j) : ℕ) : ENNReal)) ^ L.toFun i j := by
    rw [e625_pow_disp n L]
    push_cast
    rfl
  have hGp : ((e625Gprod alpha hAlpha (fun i => fourEndpointRowMargin L i) *
        e625Gprod alpha hAlpha (fun j => fourEndpointColumnMargin L j) : ℕ) : ENNReal)
      = ∏ i : Fin 4, ∏ j : Fin 4,
          (((e625Gnat alpha hAlpha i * e625Gnat alpha hAlpha j : ℕ) : ENNReal)) ^ L.toFun i j := by
    rw [e625_Gprod_row_col alpha hAlpha L]
    push_cast
    rfl
  rw [hdisp, hGp]
  rw [← Finset.prod_pow]
  simp_rw [← Finset.prod_pow]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← pow_mul, mul_comm (L.toFun i j) 2, pow_mul, ← mul_pow,
    e625_cell_identity_kern n alpha hAlpha i j, mul_pow, mul_pow]

private lemma e625_marginMass_mono (alpha : Nat) (hAlpha : 5 < alpha)
    {r s : Fin 4 → ℕ} (h : ∀ i, r i ≤ s i) :
    fourEndpointMarginMass alpha hAlpha r ≤ fourEndpointMarginMass alpha hAlpha s := by
  unfold fourEndpointMarginMass
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (h i)

private lemma e625_J_le_rowMass (alpha : Nat) (hAlpha : 5 < alpha)
    (L : FourEndpointFullTable) :
    fourEndpointJ alpha hAlpha L ≤ fourEndpointRowMass alpha hAlpha L := by
  unfold fourEndpointJ fourEndpointRowMass fourEndpointMarginMass
    fourEndpointRowMargin fourEndpointOverlapSize
  simp only [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right (L.toFun i j) (min_le_left _ _)

private lemma e625_J_le_colMass (alpha : Nat) (hAlpha : 5 < alpha)
    (L : FourEndpointFullTable) :
    fourEndpointJ alpha hAlpha L ≤ fourEndpointColumnMass alpha hAlpha L := by
  unfold fourEndpointJ fourEndpointColumnMass fourEndpointMarginMass
    fourEndpointColumnMargin fourEndpointOverlapSize
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun j _ =>
    Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right (L.toFun i j) (min_le_right _ _)

private lemma e625_localProduct_mul_deficit (n alpha : Nat) (hAlpha : 5 < alpha)
    (L : FourEndpointFullTable) :
    fourEndpointLocalProduct alpha hAlpha L *
        (∏ i : Fin 4, ∏ j : Fin 4,
          (fourEndpointThreeQuarterDeficitFactor n alpha hAlpha i j) ^ L.toFun i j)
      = ∏ i : Fin 4, ∏ j : Fin 4,
          (fourEndpointLocalCellFactor alpha hAlpha i j *
            fourEndpointThreeQuarterDeficitFactor n alpha hAlpha i j) ^ L.toFun i j := by
  unfold fourEndpointLocalProduct
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => (mul_pow _ _ _).symm

private lemma e625_Tr_kernProd (n alpha : Nat) (hAlpha : 5 < alpha)
    (L : FourEndpointFullTable) :
    (∏ i : Fin 4, ∏ j : Fin 4, (e625Kern n alpha hAlpha i j) ^ (e625Tr L).toFun i j)
      = ∏ i : Fin 4, ∏ j : Fin 4, (e625Kern n alpha hAlpha j i) ^ L.toFun i j := by
  unfold e625Tr
  exact Finset.prod_comm

private lemma e625_W_zero_of_row (n alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) (L : FourEndpointFullTable)
    (h : fourEndpointRowSelectionProduct alpha hAlpha k L *
      fourEndpointColumnSelectionProduct alpha hAlpha k L = 0) :
    fourEndpointW n alpha hAlpha k L = 0 := by
  rw [e625_W_eq, h]
  simp

private lemma e625_div_pow (a : ENNReal) (b m : ℕ) :
    (a / (b : ENNReal)) ^ m = a ^ m / ((b ^ m : ℕ) : ENNReal) := by
  rw [div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow, div_eq_mul_inv]
  push_cast
  ring

private lemma e625_table_amgm (n alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hkn : fourEndpointMarginMass alpha hAlpha
      (fourEndpointMultiplicity alpha hAlpha k) ≤ n)
    (L : FourEndpointFullTable) :
    2 * (fourEndpointW n alpha hAlpha k L *
        ∏ i : Fin 4, ∏ j : Fin 4,
          (fourEndpointThreeQuarterDeficitFactor n alpha hAlpha i j) ^ L.toFun i j)
      ≤ e625X n alpha hAlpha k L + e625X n alpha hAlpha k (e625Tr L) := by
  classical
  by_cases hz : fourEndpointRowSelectionProduct alpha hAlpha k L *
      fourEndpointColumnSelectionProduct alpha hAlpha k L = 0
  · rw [e625_W_zero_of_row n alpha hAlpha k L hz]
    simp
  -- non-degenerate case
  have hrow : ∀ i, fourEndpointRowMargin L i ≤ fourEndpointMultiplicity alpha hAlpha k i := by
    intro i
    by_contra hcon
    refine hz ?_
    have h0 : (fourEndpointMultiplicity alpha hAlpha k i).descFactorial
        (fourEndpointRowMargin L i) = 0 :=
      Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    have h1 : fourEndpointRowSelectionProduct alpha hAlpha k L = 0 := by
      unfold fourEndpointRowSelectionProduct fourEndpointMarginSelectionProduct
      exact Finset.prod_eq_zero (Finset.mem_univ i) h0
    rw [h1, zero_mul]
  have hcol : ∀ j, fourEndpointColumnMargin L j ≤ fourEndpointMultiplicity alpha hAlpha k j := by
    intro j
    by_contra hcon
    refine hz ?_
    have h0 : (fourEndpointMultiplicity alpha hAlpha k j).descFactorial
        (fourEndpointColumnMargin L j) = 0 :=
      Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    have h1 : fourEndpointColumnSelectionProduct alpha hAlpha k L = 0 := by
      unfold fourEndpointColumnSelectionProduct fourEndpointMarginSelectionProduct
      exact Finset.prod_eq_zero (Finset.mem_univ j) h0
    rw [h1, mul_zero]
  have hMr : fourEndpointMarginMass alpha hAlpha (fun i => fourEndpointRowMargin L i) ≤ n :=
    le_trans (e625_marginMass_mono alpha hAlpha hrow) hkn
  have hMc : fourEndpointMarginMass alpha hAlpha (fun j => fourEndpointColumnMargin L j) ≤ n :=
    le_trans (e625_marginMass_mono alpha hAlpha hcol) hkn
  have hJn : fourEndpointJ alpha hAlpha L ≤ n :=
    le_trans (e625_J_le_rowMass alpha hAlpha L) hMr
  -- normal forms
  have hA : fourEndpointW n alpha hAlpha k L *
      (∏ i : Fin 4, ∏ j : Fin 4,
        (fourEndpointThreeQuarterDeficitFactor n alpha hAlpha i j) ^ L.toFun i j)
      = (((fourEndpointRowSelectionProduct alpha hAlpha k L *
            fourEndpointColumnSelectionProduct alpha hAlpha k L : ℕ)) : ENNReal) /
          ((fourEndpointCellFactorialProduct L *
            n.descFactorial (fourEndpointJ alpha hAlpha L) : ℕ) : ENNReal) *
          (∏ i : Fin 4, ∏ j : Fin 4,
            (fourEndpointLocalCellFactor alpha hAlpha i j *
              fourEndpointThreeQuarterDeficitFactor n alpha hAlpha i j) ^ L.toFun i j) := by
    rw [e625_W_eq, mul_assoc, e625_localProduct_mul_deficit]
  have hX : e625X n alpha hAlpha k L
      = ((e625Dnum alpha hAlpha k (fun i => fourEndpointRowMargin L i) *
            e625Mult L : ℕ) : ENNReal) /
          ((e625Dden n alpha hAlpha (fun i => fourEndpointRowMargin L i) : ℕ) : ENNReal) *
          (∏ i : Fin 4, ∏ j : Fin 4, (e625Kern n alpha hAlpha i j) ^ L.toFun i j) := by
    unfold e625X
    rw [e625_D_eq]
    push_cast
    simp only [div_eq_mul_inv]
    ring
  have hY : e625X n alpha hAlpha k (e625Tr L)
      = ((e625Dnum alpha hAlpha k (fun j => fourEndpointColumnMargin L j) *
            e625Mult (e625Tr L) : ℕ) : ENNReal) /
          ((e625Dden n alpha hAlpha (fun j => fourEndpointColumnMargin L j) : ℕ) : ENNReal) *
          (∏ i : Fin 4, ∏ j : Fin 4, (e625Kern n alpha hAlpha j i) ^ L.toFun i j) := by
    unfold e625X
    rw [e625_D_eq, e625_Tr_kernProd]
    simp only [e625_Tr_rowMargin]
    push_cast
    simp only [div_eq_mul_inv]
    ring
  rw [hA, hX, hY]
  refine e625_amgm _ _ _ ?_
  -- the squared comparison
  set PX := ∏ i : Fin 4, ∏ j : Fin 4, (e625Kern n alpha hAlpha i j) ^ L.toFun i j with hPXdef
  set PY := ∏ i : Fin 4, ∏ j : Fin 4, (e625Kern n alpha hAlpha j i) ^ L.toFun i j with hPYdef
  have hP0 : (((n + 1) ^ fourEndpointDisplacement L : ℕ) : ENNReal) ≠ 0 := by
    have : ((n + 1) ^ fourEndpointDisplacement L : ℕ) ≠ 0 := by positivity
    exact_mod_cast this
  have hPt : (((n + 1) ^ fourEndpointDisplacement L : ℕ) : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  refine (ENNReal.mul_le_mul_iff_right hP0 hPt).mp ?_
  rw [mul_comm (((n + 1) ^ fourEndpointDisplacement L : ℕ) : ENNReal),
    mul_comm (((n + 1) ^ fourEndpointDisplacement L : ℕ) : ENNReal)]
  -- nat comparison
  have hden1 : e625Dden n alpha hAlpha (fun i => fourEndpointRowMargin L i) *
      e625Dden n alpha hAlpha (fun j => fourEndpointColumnMargin L j) ≠ 0 := by
    unfold e625Dden fourEndpointMarginFactorialProduct
    refine Nat.mul_ne_zero (Nat.mul_ne_zero ?_ ?_) (Nat.mul_ne_zero ?_ ?_)
    · exact Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero _
    · exact fun h => absurd (Nat.descFactorial_eq_zero_iff_lt.mp h) (by omega)
    · exact Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero _
    · exact fun h => absurd (Nat.descFactorial_eq_zero_iff_lt.mp h) (by omega)
  have hden2 : (fourEndpointCellFactorialProduct L *
      n.descFactorial (fourEndpointJ alpha hAlpha L)) ^ 2 ≠ 0 := by
    refine pow_ne_zero _ (Nat.mul_ne_zero ?_ ?_)
    · unfold fourEndpointCellFactorialProduct
      exact Finset.prod_ne_zero_iff.mpr fun i _ =>
        Finset.prod_ne_zero_iff.mpr fun j _ => Nat.factorial_ne_zero _
    · exact fun h => absurd (Nat.descFactorial_eq_zero_iff_lt.mp h) (by omega)
  have hnat : (fourEndpointRowSelectionProduct alpha hAlpha k L *
        fourEndpointColumnSelectionProduct alpha hAlpha k L) ^ 2 *
        (e625Gprod alpha hAlpha (fun i => fourEndpointRowMargin L i) *
          e625Gprod alpha hAlpha (fun j => fourEndpointColumnMargin L j)) *
        (e625Dden n alpha hAlpha (fun i => fourEndpointRowMargin L i) *
          e625Dden n alpha hAlpha (fun j => fourEndpointColumnMargin L j))
      ≤ (e625Dnum alpha hAlpha k (fun i => fourEndpointRowMargin L i) * e625Mult L) *
          (e625Dnum alpha hAlpha k (fun j => fourEndpointColumnMargin L j) *
            e625Mult (e625Tr L)) *
          ((n + 1) ^ fourEndpointDisplacement L) *
          (fourEndpointCellFactorialProduct L *
            n.descFactorial (fourEndpointJ alpha hAlpha L)) ^ 2 := by
    have hmL := e625_mult_cellFact L
    have hmT := e625_mult_cellFact (e625Tr L)
    rw [e625_Tr_cellFact] at hmT
    simp only [e625_Tr_rowMargin] at hmT
    have htrans := fourEndpoint_global_transport n alpha hAlpha L
    unfold e625Dnum e625Dden fourEndpointRowSelectionProduct
      fourEndpointColumnSelectionProduct fourEndpointMarginFactorialProduct at *
    unfold fourEndpointRowMass fourEndpointColumnMass at htrans
    calc (fourEndpointMarginSelectionProduct alpha hAlpha k
              (fun i => fourEndpointRowMargin L i) *
            fourEndpointMarginSelectionProduct alpha hAlpha k
              (fun j => fourEndpointColumnMargin L j)) ^ 2 *
          (e625Gprod alpha hAlpha (fun i => fourEndpointRowMargin L i) *
            e625Gprod alpha hAlpha (fun j => fourEndpointColumnMargin L j)) *
          ((∏ i : Fin 4, (fourEndpointRowMargin L i).factorial) *
              n.descFactorial (fourEndpointMarginMass alpha hAlpha
                fun i => fourEndpointRowMargin L i) *
            ((∏ j : Fin 4, (fourEndpointColumnMargin L j).factorial) *
              n.descFactorial (fourEndpointMarginMass alpha hAlpha
                fun j => fourEndpointColumnMargin L j)))
        = ((fourEndpointMarginSelectionProduct alpha hAlpha k
              (fun i => fourEndpointRowMargin L i)) ^ 2 *
            (fourEndpointMarginSelectionProduct alpha hAlpha k
              (fun j => fourEndpointColumnMargin L j)) ^ 2 *
            (e625Gprod alpha hAlpha (fun i => fourEndpointRowMargin L i) *
              e625Gprod alpha hAlpha (fun j => fourEndpointColumnMargin L j)) *
            ((∏ i : Fin 4, (fourEndpointRowMargin L i).factorial) *
              (∏ j : Fin 4, (fourEndpointColumnMargin L j).factorial))) *
            (n.descFactorial (fourEndpointMarginMass alpha hAlpha
                fun i => fourEndpointRowMargin L i) *
              n.descFactorial (fourEndpointMarginMass alpha hAlpha
                fun j => fourEndpointColumnMargin L j)) := by ring
      _ ≤ ((fourEndpointMarginSelectionProduct alpha hAlpha k
              (fun i => fourEndpointRowMargin L i)) ^ 2 *
            (fourEndpointMarginSelectionProduct alpha hAlpha k
              (fun j => fourEndpointColumnMargin L j)) ^ 2 *
            (e625Gprod alpha hAlpha (fun i => fourEndpointRowMargin L i) *
              e625Gprod alpha hAlpha (fun j => fourEndpointColumnMargin L j)) *
            ((∏ i : Fin 4, (fourEndpointRowMargin L i).factorial) *
              (∏ j : Fin 4, (fourEndpointColumnMargin L j).factorial))) *
            ((n.descFactorial (fourEndpointJ alpha hAlpha L)) ^ 2 *
              (n + 1) ^ fourEndpointDisplacement L) := Nat.mul_le_mul_left _ htrans
      _ = (fourEndpointMarginSelectionProduct alpha hAlpha k
              (fun i => fourEndpointRowMargin L i) ^ 2 *
            e625Gprod alpha hAlpha (fun i => fourEndpointRowMargin L i) * e625Mult L) *
          (fourEndpointMarginSelectionProduct alpha hAlpha k
              (fun j => fourEndpointColumnMargin L j) ^ 2 *
            e625Gprod alpha hAlpha (fun j => fourEndpointColumnMargin L j) *
            e625Mult (e625Tr L)) *
          ((n + 1) ^ fourEndpointDisplacement L) *
          (fourEndpointCellFactorialProduct L *
            n.descFactorial (fourEndpointJ alpha hAlpha L)) ^ 2 := by
            rw [← hmL, ← hmT]
            ring
  -- assemble
  calc ((((fourEndpointRowSelectionProduct alpha hAlpha k L *
          fourEndpointColumnSelectionProduct alpha hAlpha k L : ℕ)) : ENNReal) /
          ((fourEndpointCellFactorialProduct L *
            n.descFactorial (fourEndpointJ alpha hAlpha L) : ℕ) : ENNReal) *
          (∏ i : Fin 4, ∏ j : Fin 4,
            (fourEndpointLocalCellFactor alpha hAlpha i j *
              fourEndpointThreeQuarterDeficitFactor n alpha hAlpha i j) ^ L.toFun i j)) ^ 2 *
        (((n + 1) ^ fourEndpointDisplacement L : ℕ) : ENNReal)
      = (((fourEndpointRowSelectionProduct alpha hAlpha k L *
            fourEndpointColumnSelectionProduct alpha hAlpha k L : ℕ) : ENNReal) ^ 2 /
          (((fourEndpointCellFactorialProduct L *
            n.descFactorial (fourEndpointJ alpha hAlpha L)) ^ 2 : ℕ) : ENNReal)) *
          ((∏ i : Fin 4, ∏ j : Fin 4,
            (fourEndpointLocalCellFactor alpha hAlpha i j *
              fourEndpointThreeQuarterDeficitFactor n alpha hAlpha i j) ^ L.toFun i j) ^ 2 *
            (((n + 1) ^ fourEndpointDisplacement L : ℕ) : ENNReal)) := by
        rw [mul_pow, e625_div_pow]
        ring
    _ = (((fourEndpointRowSelectionProduct alpha hAlpha k L *
            fourEndpointColumnSelectionProduct alpha hAlpha k L : ℕ) : ENNReal) ^ 2 /
          (((fourEndpointCellFactorialProduct L *
            n.descFactorial (fourEndpointJ alpha hAlpha L)) ^ 2 : ℕ) : ENNReal)) *
          (((e625Gprod alpha hAlpha (fun i => fourEndpointRowMargin L i) *
            e625Gprod alpha hAlpha (fun j => fourEndpointColumnMargin L j) : ℕ) : ENNReal) *
            (PX * PY)) := by
        rw [e625_prod_cell_identity n alpha hAlpha L]
    _ = ((((fourEndpointRowSelectionProduct alpha hAlpha k L *
            fourEndpointColumnSelectionProduct alpha hAlpha k L) ^ 2 *
            (e625Gprod alpha hAlpha (fun i => fourEndpointRowMargin L i) *
              e625Gprod alpha hAlpha (fun j => fourEndpointColumnMargin L j)) : ℕ) : ENNReal) /
          (((fourEndpointCellFactorialProduct L *
            n.descFactorial (fourEndpointJ alpha hAlpha L)) ^ 2 : ℕ) : ENNReal)) *
          (PX * PY) := by
        push_cast
        simp only [div_eq_mul_inv]
        ring
    _ ≤ ((((e625Dnum alpha hAlpha k (fun i => fourEndpointRowMargin L i) * e625Mult L) *
            (e625Dnum alpha hAlpha k (fun j => fourEndpointColumnMargin L j) *
              e625Mult (e625Tr L)) *
            ((n + 1) ^ fourEndpointDisplacement L) : ℕ) : ENNReal) /
          ((e625Dden n alpha hAlpha (fun i => fourEndpointRowMargin L i) *
            e625Dden n alpha hAlpha (fun j => fourEndpointColumnMargin L j) : ℕ) : ENNReal)) *
          (PX * PY) := by
        refine mul_le_mul_left ?_ _
        rw [e625_div_le_div_iff _ _ _ _ hden2 hden1]
        exact_mod_cast hnat
    _ = (((e625Dnum alpha hAlpha k (fun i => fourEndpointRowMargin L i) *
            e625Mult L : ℕ) : ENNReal) /
          ((e625Dden n alpha hAlpha (fun i => fourEndpointRowMargin L i) : ℕ) : ENNReal) * PX) *
          (((e625Dnum alpha hAlpha k (fun j => fourEndpointColumnMargin L j) *
            e625Mult (e625Tr L) : ℕ) : ENNReal) /
          ((e625Dden n alpha hAlpha (fun j => fourEndpointColumnMargin L j) : ℕ) : ENNReal) * PY) *
          (((n + 1) ^ fourEndpointDisplacement L : ℕ) : ENNReal) := by
        rw [show (((e625Dnum alpha hAlpha k (fun i => fourEndpointRowMargin L i) *
              e625Mult L : ℕ) : ENNReal) /
            ((e625Dden n alpha hAlpha (fun i => fourEndpointRowMargin L i) : ℕ) : ENNReal) * PX) *
            (((e625Dnum alpha hAlpha k (fun j => fourEndpointColumnMargin L j) *
              e625Mult (e625Tr L) : ℕ) : ENNReal) /
            ((e625Dden n alpha hAlpha (fun j => fourEndpointColumnMargin L j) : ℕ) : ENNReal) * PY)
            = ((((e625Dnum alpha hAlpha k (fun i => fourEndpointRowMargin L i) *
                e625Mult L : ℕ) : ENNReal) /
              ((e625Dden n alpha hAlpha (fun i => fourEndpointRowMargin L i) : ℕ) : ENNReal)) *
              (((e625Dnum alpha hAlpha k (fun j => fourEndpointColumnMargin L j) *
                e625Mult (e625Tr L) : ℕ) : ENNReal) /
              ((e625Dden n alpha hAlpha (fun j => fourEndpointColumnMargin L j) : ℕ) : ENNReal))) *
              (PX * PY) from by ring, e625_div_mul_div]
        push_cast
        simp only [div_eq_mul_inv]
        ring

private lemma e625_D_zero_of_not_box (n alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) (r : Fin 4 → ℕ)
    (h : ¬ (∀ i, r i ≤ fourEndpointMultiplicity alpha hAlpha k i)) :
    fourEndpointD n alpha hAlpha k r = 0 := by
  push Not at h
  obtain ⟨i, hi⟩ := h
  have h0 : (fourEndpointMultiplicity alpha hAlpha k i).descFactorial (r i) = 0 :=
    Nat.descFactorial_eq_zero_iff_lt.mpr hi
  have h1 : fourEndpointMarginSelectionProduct alpha hAlpha k r = 0 := by
    unfold fourEndpointMarginSelectionProduct
    exact Finset.prod_eq_zero (Finset.mem_univ i) h0
  rw [e625_D_eq]
  unfold e625Dnum
  rw [h1]
  simp

private lemma e625_rowgroup (n alpha : Nat) (hAlpha : 5 < alpha) (r : Fin 4 → ℕ)
    (S : Finset FourEndpointFullTable)
    (hS : ∀ L ∈ S, ∀ i, fourEndpointRowMargin L i = r i) :
    (∑ L ∈ S, (e625Mult L : ENNReal) *
        ∏ i : Fin 4, ∏ j : Fin 4, (e625Kern n alpha hAlpha i j) ^ L.toFun i j)
      ≤ ∏ i : Fin 4, (e625A n alpha hAlpha i) ^ r i := by
  classical
  set t : Fin 4 → Finset (Fin 4 → ℕ) :=
    fun i => Finset.piAntidiag (Finset.univ : Finset (Fin 4)) (r i) with ht
  set F : (Fin 4 → Fin 4 → ℕ) → ENNReal := fun x =>
    ∏ i : Fin 4, (((Nat.multinomial Finset.univ (x i) : ℕ) : ENNReal) *
      ∏ j : Fin 4, (e625Kern n alpha hAlpha i j) ^ (x i j)) with hF
  have hexpand : ∏ i : Fin 4, (e625A n alpha hAlpha i) ^ r i
      = ∑ x ∈ Fintype.piFinset t, F x := by
    simp only [hF]
    rw [← Finset.prod_univ_sum t (fun (i : Fin 4) (v : Fin 4 → ℕ) =>
      ((Nat.multinomial Finset.univ v : ℕ) : ENNReal) *
        ∏ j : Fin 4, (e625Kern n alpha hAlpha i j) ^ (v j))]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [e625A, ht]
    exact Finset.sum_pow_eq_sum_piAntidiag _ _ _
  have hval : ∀ L : FourEndpointFullTable, F L.toFun
      = (e625Mult L : ENNReal) *
        ∏ i : Fin 4, ∏ j : Fin 4, (e625Kern n alpha hAlpha i j) ^ L.toFun i j := by
    intro L
    simp only [hF, e625Mult]
    push_cast
    rw [← Finset.prod_mul_distrib]
  have hinj : Set.InjOn (fun L : FourEndpointFullTable => L.toFun) ↑S := by
    intro a _ b _ hab
    exact FourEndpointFullTable.ext hab
  have hsub : S.image (fun L : FourEndpointFullTable => L.toFun) ⊆ Fintype.piFinset t := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨L, hL, rfl⟩ := hx
    rw [Fintype.mem_piFinset]
    intro i
    rw [ht]
    rw [Finset.mem_piAntidiag]
    exact ⟨hS L hL i, fun j _ => Finset.mem_univ j⟩
  calc (∑ L ∈ S, (e625Mult L : ENNReal) *
        ∏ i : Fin 4, ∏ j : Fin 4, (e625Kern n alpha hAlpha i j) ^ L.toFun i j)
      = ∑ x ∈ S.image (fun L : FourEndpointFullTable => L.toFun), F x := by
        rw [Finset.sum_image hinj]
        exact (Finset.sum_congr rfl fun L _ => hval L).symm
    _ ≤ ∑ x ∈ Fintype.piFinset t, F x := Finset.sum_le_sum_of_subset hsub
    _ = ∏ i : Fin 4, (e625A n alpha hAlpha i) ^ r i := hexpand.symm

private lemma e625_Q_diag (n alpha : Nat) (hAlpha : 5 < alpha) (i : Fin 4) :
    fourEndpointQ n alpha hAlpha i i = 1 := by
  have hd : fourEndpointDistance i i = 0 := by simp [fourEndpointDistance, Nat.dist_self]
  unfold fourEndpointQ
  rw [hd]
  norm_num

private lemma e625_one_le_rowMax (n alpha : Nat) (hAlpha : 5 < alpha) :
    1 ≤ fourEndpointFusedRowMax n alpha hAlpha := by
  have h1 : (1 : ENNReal) ≤ fourEndpointFusedKernel n alpha hAlpha 0 0 := by
    unfold fourEndpointFusedKernel fourEndpointThreeQuarterDeficitFactor
    rw [e625_Q_diag]
    simp
  have h2 : fourEndpointFusedKernel n alpha hAlpha 0 0 ≤
      fourEndpointFusedRowSum n alpha hAlpha 0 := by
    unfold fourEndpointFusedRowSum
    exact Finset.single_le_sum (f := fun j => fourEndpointFusedKernel n alpha hAlpha 0 j)
      (fun _ _ => zero_le) (Finset.mem_univ 0)
  have h3 : fourEndpointFusedRowSum n alpha hAlpha 0 ≤ fourEndpointFusedRowMax n alpha hAlpha :=
    Finset.le_sup (f := fun i : Fin 4 => fourEndpointFusedRowSum n alpha hAlpha i)
      (Finset.mem_univ 0)
  exact h1.trans (h2.trans h3)

private lemma e625_D_top_of_lt (n alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hkn : ¬ fourEndpointMarginMass alpha hAlpha
      (fourEndpointMultiplicity alpha hAlpha k) ≤ n) :
    fourEndpointD n alpha hAlpha k (fourEndpointMultiplicity alpha hAlpha k) = ⊤ := by
  set kk := fourEndpointMultiplicity alpha hAlpha k with hkk
  have hdesc : n.descFactorial (fourEndpointMarginMass alpha hAlpha kk) = 0 :=
    Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
  have hsel : fourEndpointMarginSelectionProduct alpha hAlpha k kk ≠ 0 := by
    unfold fourEndpointMarginSelectionProduct
    rw [Finset.prod_ne_zero_iff]
    intro i _
    rw [← hkk, Nat.descFactorial_self]
    exact Nat.factorial_ne_zero _
  have hG : fourEndpointDiagonalLocalProduct alpha hAlpha kk ≠ 0 := by
    unfold fourEndpointDiagonalLocalProduct fourEndpointDiagonalLocalFactor
    rw [Finset.prod_ne_zero_iff]
    intro i _
    refine pow_ne_zero _ (mul_ne_zero ?_ ?_)
    · exact_mod_cast Nat.factorial_ne_zero _
    · have : localSignRewardNat (fourEndpointSize alpha hAlpha i) ≠ 0 := by
        unfold localSignRewardNat
        split <;> positivity
      exact_mod_cast this
  unfold fourEndpointD
  rw [hdesc]
  rw [Nat.cast_zero, ENNReal.div_zero hG, ENNReal.mul_top]
  refine ENNReal.div_ne_zero.mpr ⟨?_, ?_⟩
  · exact pow_ne_zero _ (by exact_mod_cast hsel)
  · exact ENNReal.natCast_ne_top _


/-! ### Box decomposition and kernel row bounds -/

private lemma e625_box_split (kk : Fin 4 → ℕ) (f : (Fin 4 → ℕ) → ENNReal) :
    ∑ r ∈ partialSubprofileBox kk, f r
      = ∑ a ∈ Finset.range (kk 0 + 1), ∑ b ∈ Finset.range (kk 1 + 1),
          ∑ c ∈ Finset.range (kk 2 + 1), ∑ t ∈ Finset.range (kk 3 + 1),
            f ![a, b, c, t] := by
  rw [partialSubprofileBox, ← Finset.sum_product', ← Finset.sum_product', ← Finset.sum_product']
  refine Finset.sum_nbij' (i := fun r => (((r 0, r 1), r 2), r 3))
    (j := fun x => ![x.1.1.1, x.1.1.2, x.1.2, x.2]) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp [Fintype.mem_piFinset] at ha ⊢
    exact ⟨⟨⟨ha 0, ha 1⟩, ha 2⟩, ha 3⟩
  · intro b hb
    simp [Fintype.mem_piFinset] at hb ⊢
    intro i; fin_cases i <;> simp [hb.1.1.1, hb.1.1.2, hb.1.2, hb.2]
  · intro a _
    funext i; fin_cases i <;> rfl
  · intro b _
    rfl
  · intro a _
    congr 1
    funext i; fin_cases i <;> rfl

private lemma e625_charge_diag (alpha : Nat) (hAlpha : 5 < alpha) (i : Fin 4) :
    e625Charge alpha hAlpha i i = 1 := by
  unfold e625Charge
  rw [if_neg]
  rintro ⟨h1, h2⟩
  omega

private lemma e625_charge_le_two (alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4) :
    e625Charge alpha hAlpha i j ≤ 2 := by
  unfold e625Charge
  split_ifs <;> norm_num

private lemma e625_charge_one_of_two_le (alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4)
    (hu : 2 ≤ fourEndpointSize alpha hAlpha i) :
    e625Charge alpha hAlpha i j = 1 := by
  unfold e625Charge
  rw [if_neg]
  rintro ⟨h1, h2⟩
  omega

private lemma e625_one_le_kernel_diag (n alpha : Nat) (hAlpha : 5 < alpha) (i : Fin 4) :
    (1 : ENNReal) ≤ fourEndpointFusedKernel n alpha hAlpha i i := by
  unfold fourEndpointFusedKernel fourEndpointThreeQuarterDeficitFactor
  rw [e625_Q_diag]
  simp

private lemma e625_rowSum_le_rowMax (n alpha : Nat) (hAlpha : 5 < alpha) (i : Fin 4) :
    fourEndpointFusedRowSum n alpha hAlpha i ≤ fourEndpointFusedRowMax n alpha hAlpha :=
  Finset.le_sup (f := fun i : Fin 4 => fourEndpointFusedRowSum n alpha hAlpha i)
    (Finset.mem_univ i)

private lemma e625_A_le_rowMax (n alpha : Nat) (hAlpha : 5 < alpha) (i : Fin 4)
    (hu : 2 ≤ fourEndpointSize alpha hAlpha i) :
    e625A n alpha hAlpha i ≤ fourEndpointFusedRowMax n alpha hAlpha := by
  have hA : e625A n alpha hAlpha i = fourEndpointFusedRowSum n alpha hAlpha i := by
    unfold e625A e625Kern fourEndpointFusedRowSum
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [e625_charge_one_of_two_le alpha hAlpha i j hu]
    simp
  rw [hA]
  exact e625_rowSum_le_rowMax n alpha hAlpha i

private lemma e625_one_add_A_le (n alpha : Nat) (hAlpha : 5 < alpha) (i : Fin 4) :
    1 + e625A n alpha hAlpha i ≤ 2 * fourEndpointFusedRowMax n alpha hAlpha := by
  have hd : (1 : ENNReal) ≤ fourEndpointFusedKernel n alpha hAlpha i i :=
    e625_one_le_kernel_diag n alpha hAlpha i
  have hsum : ∑ j : Fin 4, (if j = i then fourEndpointFusedKernel n alpha hAlpha i j else 0)
      = fourEndpointFusedKernel n alpha hAlpha i i := by
    simp
  have hkey : e625A n alpha hAlpha i + fourEndpointFusedKernel n alpha hAlpha i i
      ≤ 2 * fourEndpointFusedRowSum n alpha hAlpha i := by
    have hstep : e625A n alpha hAlpha i + fourEndpointFusedKernel n alpha hAlpha i i
        = ∑ j : Fin 4, (e625Kern n alpha hAlpha i j +
            (if j = i then fourEndpointFusedKernel n alpha hAlpha i j else 0)) := by
      rw [Finset.sum_add_distrib, hsum, e625A]
    rw [hstep, fourEndpointFusedRowSum, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hj : j = i
    · subst hj
      rw [if_pos rfl, e625Kern, e625_charge_diag]
      simp [two_mul]
    · rw [if_neg hj, add_zero, e625Kern]
      have : ((e625Charge alpha hAlpha i j : ℕ) : ENNReal) ≤ 2 := by
        exact_mod_cast e625_charge_le_two alpha hAlpha i j
      exact mul_le_mul_left this _
  calc 1 + e625A n alpha hAlpha i
      ≤ fourEndpointFusedKernel n alpha hAlpha i i + e625A n alpha hAlpha i := by
        gcongr
    _ = e625A n alpha hAlpha i + fourEndpointFusedKernel n alpha hAlpha i i := by ring
    _ ≤ 2 * fourEndpointFusedRowSum n alpha hAlpha i := hkey
    _ ≤ 2 * fourEndpointFusedRowMax n alpha hAlpha := by
        exact mul_le_mul_right (e625_rowSum_le_rowMax n alpha hAlpha i) 2


/-! ### Arithmetic and Chebyshev ingredients -/

private lemma e625_desc_mono_base (a b c : ℕ) (h : a ≤ b) :
    a.descFactorial c ≤ b.descFactorial c := by
  induction c with
  | zero => simp
  | succ c ih =>
      rw [Nat.descFactorial_succ, Nat.descFactorial_succ]
      exact Nat.mul_le_mul (by omega) ih

private lemma e625_desc_shift (nn m N t s : ℕ) (hts : t ≤ s) (hsN : s ≤ N)
    (hmn : m + N ≤ nn) :
    N.descFactorial s * nn.descFactorial (m + t)
      ≤ N.descFactorial t * nn.descFactorial (m + s) := by
  have h1 : (N - t).descFactorial (s - t) * N.descFactorial t = N.descFactorial s :=
    Nat.descFactorial_mul_descFactorial hts
  have hst : (m + s) - (m + t) = s - t := by omega
  have h2 : (nn - (m + t)).descFactorial (s - t) * nn.descFactorial (m + t)
      = nn.descFactorial (m + s) := by
    have := Nat.descFactorial_mul_descFactorial (n := nn) (k := m + t) (m := m + s)
      (by omega)
    rwa [hst] at this
  have hbase : N - t ≤ nn - (m + t) := by omega
  calc N.descFactorial s * nn.descFactorial (m + t)
      = ((N - t).descFactorial (s - t) * N.descFactorial t) * nn.descFactorial (m + t) := by
        rw [h1]
    _ ≤ ((nn - (m + t)).descFactorial (s - t) * N.descFactorial t) * nn.descFactorial (m + t) := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
          (e625_desc_mono_base _ _ _ hbase))
    _ = N.descFactorial t *
          ((nn - (m + t)).descFactorial (s - t) * nn.descFactorial (m + t)) := by ring
    _ = N.descFactorial t * nn.descFactorial (m + s) := by rw [h2]

private lemma e625_cross_nat (P G F Ct Cs ft fs ds dt X Y : ℕ)
    (hds : ds = fs * Cs) (hdt : dt = ft * Ct) (hbase : ds * X ≤ dt * Y) :
    Ct * ((P * ds) ^ 2 * G) * (F * ft * X) ≤ Cs * ((P * dt) ^ 2 * G) * (F * fs * Y) := by
  calc Ct * ((P * ds) ^ 2 * G) * (F * ft * X)
      = (P ^ 2 * G * F * Ct * Cs * ft * fs) * (ds * X) := by subst hds; ring
    _ ≤ (P ^ 2 * G * F * Ct * Cs * ft * fs) * (dt * Y) := Nat.mul_le_mul_left _ hbase
    _ = Cs * ((P * dt) ^ 2 * G) * (F * fs * Y) := by subst hdt; ring

private lemma e625_rearr (p q x y : ENNReal) (hpq : p ≤ q) (hxy : x ≤ y) :
    p * y + q * x ≤ p * x + q * y := by
  obtain ⟨u, rfl⟩ := le_iff_exists_add.mp hpq
  obtain ⟨v, rfl⟩ := le_iff_exists_add.mp hxy
  have h : p * (x + v) + (p + u) * x + u * v = p * x + (p + u) * (x + v) := by ring
  rw [← h]
  exact self_le_add_right _ _

private lemma e625_sum_choose_cast (N : ℕ) :
    ∑ t ∈ Finset.range (N + 1), ((N.choose t : ℕ) : ENNReal) = 2 ^ N := by
  rw [← Nat.cast_sum, Nat.sum_range_choose]
  push_cast
  ring

private lemma e625_sum_choose_pow (N : ℕ) (A : ENNReal) :
    ∑ t ∈ Finset.range (N + 1), ((N.choose t : ℕ) : ENNReal) * A ^ t = (1 + A) ^ N := by
  have h : (1 + A) ^ N = (A + 1) ^ N := by rw [add_comm]
  rw [h, add_pow]
  exact Finset.sum_congr rfl fun t _ => by rw [one_pow]; ring

private lemma e625_cheb (N : ℕ) (C e : ℕ → ENNReal) (A : ENNReal) (hA : 1 ≤ A)
    (hmono : ∀ t s, t ≤ s → s ≤ N → C t * e s ≤ C s * e t) :
    (∑ t ∈ Finset.range (N + 1), C t) * (∑ s ∈ Finset.range (N + 1), e s * A ^ s)
      ≤ (∑ t ∈ Finset.range (N + 1), C t * A ^ t) *
        (∑ s ∈ Finset.range (N + 1), e s) := by
  classical
  set rg := Finset.range (N + 1) with hrg
  have hmemle : ∀ t ∈ rg, t ≤ N := by
    intro t ht
    have := Finset.mem_range.mp ht
    omega
  have key : ∀ t ∈ rg, ∀ s ∈ rg,
      C t * e s * A ^ s + C s * e t * A ^ t ≤ C t * A ^ t * e s + C s * A ^ s * e t := by
    intro t ht s hs
    have hswap : C t * A ^ t * e s + C s * A ^ s * e t
        = (C t * e s) * A ^ t + (C s * e t) * A ^ s := by ring
    have hswap' : C t * e s * A ^ s + C s * e t * A ^ t
        = (C t * e s) * A ^ s + (C s * e t) * A ^ t := by ring
    rw [hswap, hswap']
    rcases le_total t s with h | h
    · have hp := hmono t s h (hmemle s hs)
      have hx : A ^ t ≤ A ^ s := pow_le_pow_right₀ hA h
      exact e625_rearr (C t * e s) (C s * e t) (A ^ t) (A ^ s) hp hx
    · have hp := hmono s t h (hmemle t ht)
      have hx : A ^ s ≤ A ^ t := pow_le_pow_right₀ hA h
      have := e625_rearr (C s * e t) (C t * e s) (A ^ s) (A ^ t) hp hx
      calc (C t * e s) * A ^ s + (C s * e t) * A ^ t
          = (C s * e t) * A ^ t + (C t * e s) * A ^ s := by ring
        _ ≤ (C s * e t) * A ^ s + (C t * e s) * A ^ t := this
        _ = (C t * e s) * A ^ t + (C s * e t) * A ^ s := by ring
  have hL : ∑ t ∈ rg, ∑ s ∈ rg, (C t * e s * A ^ s + C s * e t * A ^ t)
      = 2 * ((∑ t ∈ rg, C t) * (∑ s ∈ rg, e s * A ^ s)) := by
    have e1 : ∑ t ∈ rg, ∑ s ∈ rg, C t * e s * A ^ s
        = (∑ t ∈ rg, C t) * (∑ s ∈ rg, e s * A ^ s) := by
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => by ring
    have e2 : ∑ t ∈ rg, ∑ s ∈ rg, C s * e t * A ^ t
        = (∑ t ∈ rg, C t) * (∑ s ∈ rg, e s * A ^ s) := by
      rw [Finset.sum_comm, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => by ring
    simp only [Finset.sum_add_distrib]
    rw [e1, e2, two_mul]
  have hR : ∑ t ∈ rg, ∑ s ∈ rg, (C t * A ^ t * e s + C s * A ^ s * e t)
      = 2 * ((∑ t ∈ rg, C t * A ^ t) * (∑ s ∈ rg, e s)) := by
    have e1 : ∑ t ∈ rg, ∑ s ∈ rg, C t * A ^ t * e s
        = (∑ t ∈ rg, C t * A ^ t) * (∑ s ∈ rg, e s) := by
      rw [Finset.sum_mul_sum]
    have e2 : ∑ t ∈ rg, ∑ s ∈ rg, C s * A ^ s * e t
        = (∑ t ∈ rg, C t * A ^ t) * (∑ s ∈ rg, e s) := by
      rw [Finset.sum_comm, Finset.sum_mul_sum]
    simp only [Finset.sum_add_distrib]
    rw [e1, e2, two_mul]
  have h2 : 2 * ((∑ t ∈ rg, C t) * (∑ s ∈ rg, e s * A ^ s))
      ≤ 2 * ((∑ t ∈ rg, C t * A ^ t) * (∑ s ∈ rg, e s)) := by
    rw [← hL, ← hR]
    exact Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun s hs => key t ht s hs
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h2


/-! ### One-coordinate slices of the subprofile weight -/

private lemma e625Dnum_slice (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) (a b c t : ℕ) :
    e625Dnum alpha hAlpha k ![a, b, c, t]
      = ((fourEndpointMultiplicity alpha hAlpha k 0).descFactorial a *
          (fourEndpointMultiplicity alpha hAlpha k 1).descFactorial b *
          (fourEndpointMultiplicity alpha hAlpha k 2).descFactorial c *
          (fourEndpointMultiplicity alpha hAlpha k 3).descFactorial t) ^ 2 *
        (e625Gnat alpha hAlpha 0 ^ a * e625Gnat alpha hAlpha 1 ^ b *
          e625Gnat alpha hAlpha 2 ^ c * e625Gnat alpha hAlpha 3 ^ t) := by
  unfold e625Dnum fourEndpointMarginSelectionProduct e625Gprod
  rw [Fin.prod_univ_four, Fin.prod_univ_four]
  rfl

private lemma e625Dden_slice (n alpha : Nat) (hAlpha : 5 < alpha) (a b c t : ℕ) :
    e625Dden n alpha hAlpha ![a, b, c, t]
      = a.factorial * b.factorial * c.factorial * t.factorial *
        n.descFactorial (fourEndpointSize alpha hAlpha 0 * a +
          fourEndpointSize alpha hAlpha 1 * b + fourEndpointSize alpha hAlpha 2 * c +
          fourEndpointSize alpha hAlpha 3 * t) := by
  unfold e625Dden fourEndpointMarginFactorialProduct fourEndpointMarginMass
  rw [Fin.prod_univ_four, Fin.sum_univ_four]
  rfl

private lemma e625_Gnat_three_eq_one (alpha : Nat) (hAlpha : 5 < alpha)
    (hu3 : fourEndpointSize alpha hAlpha 3 = 1) :
    e625Gnat alpha hAlpha 3 = 1 := by
  unfold e625Gnat e625Gt
  rw [hu3]
  simp [localSignRewardNat]

private lemma e625_slice_mono (n alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) (hu3 : fourEndpointSize alpha hAlpha 3 = 1)
    (a b c : ℕ)
    (hmn : fourEndpointSize alpha hAlpha 0 * a + fourEndpointSize alpha hAlpha 1 * b +
      fourEndpointSize alpha hAlpha 2 * c + fourEndpointMultiplicity alpha hAlpha k 3 ≤ n)
    (t s : ℕ) (hts : t ≤ s) (hsN : s ≤ fourEndpointMultiplicity alpha hAlpha k 3) :
    (((fourEndpointMultiplicity alpha hAlpha k 3).choose t : ℕ) : ENNReal) *
        fourEndpointD n alpha hAlpha k ![a, b, c, s]
      ≤ (((fourEndpointMultiplicity alpha hAlpha k 3).choose s : ℕ) : ENNReal) *
        fourEndpointD n alpha hAlpha k ![a, b, c, t] := by
  set N := fourEndpointMultiplicity alpha hAlpha k 3 with hN
  set m := fourEndpointSize alpha hAlpha 0 * a + fourEndpointSize alpha hAlpha 1 * b +
    fourEndpointSize alpha hAlpha 2 * c with hm
  have hG3 : e625Gnat alpha hAlpha 3 = 1 := e625_Gnat_three_eq_one alpha hAlpha hu3
  have hdenpos : ∀ x, x ≤ N → e625Dden n alpha hAlpha ![a, b, c, x] ≠ 0 := by
    intro x hx
    rw [e625Dden_slice, hu3, one_mul, ← hm]
    have hdesc : n.descFactorial (m + x) ≠ 0 := by
      have : ¬ n < m + x := by omega
      simp only [ne_eq, Nat.descFactorial_eq_zero_iff_lt]
      exact this
    exact Nat.mul_ne_zero (by positivity) hdesc
  rw [e625_D_eq n alpha hAlpha k ![a, b, c, s], e625_D_eq n alpha hAlpha k ![a, b, c, t],
    ← mul_div_assoc, ← mul_div_assoc,
    e625_div_le_div_iff _ _ _ _ (hdenpos s hsN) (hdenpos t (le_trans hts hsN))]
  have hbase : N.descFactorial s * n.descFactorial (m + t)
      ≤ N.descFactorial t * n.descFactorial (m + s) :=
    e625_desc_shift n m N t s hts hsN (by omega)
  have hnat : N.choose t * e625Dnum alpha hAlpha k ![a, b, c, s] *
        e625Dden n alpha hAlpha ![a, b, c, t]
      ≤ N.choose s * e625Dnum alpha hAlpha k ![a, b, c, t] *
        e625Dden n alpha hAlpha ![a, b, c, s] := by
    rw [e625Dnum_slice, e625Dnum_slice, e625Dden_slice, e625Dden_slice]
    simp only [hG3, hu3, one_pow, mul_one, one_mul, ← hm, ← hN]
    exact e625_cross_nat _ _ _ _ _ _ _ _ _ _ _
      (Nat.descFactorial_eq_factorial_mul_choose N s)
      (Nat.descFactorial_eq_factorial_mul_choose N t) hbase
  exact_mod_cast hnat


/-! ### The one-coordinate descent and the box bound -/

private lemma e625_inner_bound (n alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) (hu3 : fourEndpointSize alpha hAlpha 3 = 1)
    (a b c : ℕ)
    (hmn : fourEndpointSize alpha hAlpha 0 * a + fourEndpointSize alpha hAlpha 1 * b +
      fourEndpointSize alpha hAlpha 2 * c + fourEndpointMultiplicity alpha hAlpha k 3 ≤ n) :
    ∑ t ∈ Finset.range (fourEndpointMultiplicity alpha hAlpha k 3 + 1),
        fourEndpointD n alpha hAlpha k ![a, b, c, t] * e625A n alpha hAlpha 3 ^ t
      ≤ fourEndpointFusedRowMax n alpha hAlpha ^
          (fourEndpointMultiplicity alpha hAlpha k 3) *
        ∑ t ∈ Finset.range (fourEndpointMultiplicity alpha hAlpha k 3 + 1),
          fourEndpointD n alpha hAlpha k ![a, b, c, t] := by
  classical
  set N := fourEndpointMultiplicity alpha hAlpha k 3 with hN
  set R := fourEndpointFusedRowMax n alpha hAlpha with hRdef
  set A := e625A n alpha hAlpha 3 with hAdef
  have hR1 : (1 : ENNReal) ≤ R := e625_one_le_rowMax n alpha hAlpha
  have hRN : (1 : ENNReal) ≤ R ^ N := one_le_pow₀ hR1
  by_cases hA : A ≤ 1
  · calc ∑ t ∈ Finset.range (N + 1), fourEndpointD n alpha hAlpha k ![a, b, c, t] * A ^ t
        ≤ ∑ t ∈ Finset.range (N + 1), fourEndpointD n alpha hAlpha k ![a, b, c, t] := by
          refine Finset.sum_le_sum fun t _ => ?_
          calc fourEndpointD n alpha hAlpha k ![a, b, c, t] * A ^ t
              ≤ fourEndpointD n alpha hAlpha k ![a, b, c, t] * 1 :=
                mul_le_mul_right (pow_le_one₀ zero_le hA) _
            _ = fourEndpointD n alpha hAlpha k ![a, b, c, t] := mul_one _
      _ = 1 * ∑ t ∈ Finset.range (N + 1), fourEndpointD n alpha hAlpha k ![a, b, c, t] :=
          (one_mul _).symm
      _ ≤ R ^ N * ∑ t ∈ Finset.range (N + 1),
            fourEndpointD n alpha hAlpha k ![a, b, c, t] := mul_le_mul_left hRN _
  · push Not at hA
    have hA1 : (1 : ENNReal) ≤ A := le_of_lt hA
    have hmono : ∀ t s, t ≤ s → s ≤ N →
        (((N.choose t : ℕ) : ENNReal)) * fourEndpointD n alpha hAlpha k ![a, b, c, s]
          ≤ (((N.choose s : ℕ) : ENNReal)) * fourEndpointD n alpha hAlpha k ![a, b, c, t] :=
      fun t s hts hsN => e625_slice_mono n alpha hAlpha k hu3 a b c hmn t s hts hsN
    have hcheb := e625_cheb N (fun t => (((N.choose t : ℕ) : ENNReal)))
      (fun t => fourEndpointD n alpha hAlpha k ![a, b, c, t]) A hA1 hmono
    rw [e625_sum_choose_cast, e625_sum_choose_pow] at hcheb
    have hstep : (1 + A) ^ N ≤ (2 * R) ^ N := by
      have := e625_one_add_A_le n alpha hAlpha 3
      exact pow_le_pow_left' this N
    have h2 : (2 : ENNReal) ^ N *
          ∑ t ∈ Finset.range (N + 1), fourEndpointD n alpha hAlpha k ![a, b, c, t] * A ^ t
        ≤ (2 : ENNReal) ^ N * (R ^ N *
          ∑ t ∈ Finset.range (N + 1), fourEndpointD n alpha hAlpha k ![a, b, c, t]) := by
      calc (2 : ENNReal) ^ N *
            ∑ t ∈ Finset.range (N + 1), fourEndpointD n alpha hAlpha k ![a, b, c, t] * A ^ t
          ≤ (1 + A) ^ N *
            ∑ t ∈ Finset.range (N + 1), fourEndpointD n alpha hAlpha k ![a, b, c, t] := hcheb
        _ ≤ (2 * R) ^ N *
            ∑ t ∈ Finset.range (N + 1), fourEndpointD n alpha hAlpha k ![a, b, c, t] :=
              mul_le_mul_left hstep _
        _ = (2 : ENNReal) ^ N * (R ^ N *
            ∑ t ∈ Finset.range (N + 1), fourEndpointD n alpha hAlpha k ![a, b, c, t]) := by
              rw [mul_pow, mul_assoc]
    exact (ENNReal.mul_le_mul_iff_right (by positivity)
      (by exact ENNReal.pow_ne_top (by norm_num))).mp h2

private lemma e625_size_two_le (alpha : Nat) (hAlpha : 5 < alpha) (i : Fin 4)
    (hi : i.val ≤ 2) : 2 ≤ fourEndpointSize alpha hAlpha i := by
  rw [e625_size_eq]
  omega


private lemma e625_box_bound (n alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hkn : fourEndpointMarginMass alpha hAlpha
      (fourEndpointMultiplicity alpha hAlpha k) ≤ n) :
    (∑ r ∈ partialSubprofileBox (fourEndpointMultiplicity alpha hAlpha k),
        fourEndpointD n alpha hAlpha k r * ∏ i : Fin 4, (e625A n alpha hAlpha i) ^ r i)
      ≤ (fourEndpointFusedRowMax n alpha hAlpha) ^
          (∑ i : Fin 4, fourEndpointMultiplicity alpha hAlpha k i) *
        ∑ r ∈ partialSubprofileBox (fourEndpointMultiplicity alpha hAlpha k),
          fourEndpointD n alpha hAlpha k r := by
  classical
  have hR1 : (1 : ENNReal) ≤ fourEndpointFusedRowMax n alpha hAlpha :=
    e625_one_le_rowMax n alpha hAlpha
  by_cases hu3 : 2 ≤ fourEndpointSize alpha hAlpha 3
  · -- every charged row sum is already dominated by the row maximum
    have hAle : ∀ i : Fin 4, e625A n alpha hAlpha i ≤ fourEndpointFusedRowMax n alpha hAlpha := by
      intro i
      refine e625_A_le_rowMax n alpha hAlpha i ?_
      rcases Nat.lt_or_ge i.val 3 with h | h
      · exact e625_size_two_le alpha hAlpha i (by omega)
      · have hi3 : i = 3 := Fin.ext (by omega)
        rw [hi3]
        exact hu3
    calc (∑ r ∈ partialSubprofileBox (fourEndpointMultiplicity alpha hAlpha k),
          fourEndpointD n alpha hAlpha k r * ∏ i : Fin 4, (e625A n alpha hAlpha i) ^ r i)
        ≤ ∑ r ∈ partialSubprofileBox (fourEndpointMultiplicity alpha hAlpha k),
            (fourEndpointFusedRowMax n alpha hAlpha) ^
              (∑ i : Fin 4, fourEndpointMultiplicity alpha hAlpha k i) *
            fourEndpointD n alpha hAlpha k r := by
          refine Finset.sum_le_sum fun r hr => ?_
          have hrle : ∀ i, r i ≤ fourEndpointMultiplicity alpha hAlpha k i :=
            mem_partialSubprofileBox.mp hr
          have hprod : ∏ i : Fin 4, (e625A n alpha hAlpha i) ^ r i
              ≤ (fourEndpointFusedRowMax n alpha hAlpha) ^
                (∑ i : Fin 4, fourEndpointMultiplicity alpha hAlpha k i) := by
            calc ∏ i : Fin 4, (e625A n alpha hAlpha i) ^ r i
                ≤ ∏ i : Fin 4, (fourEndpointFusedRowMax n alpha hAlpha) ^ r i :=
                  Finset.prod_le_prod' fun i _ => pow_le_pow_left' (hAle i) _
              _ = (fourEndpointFusedRowMax n alpha hAlpha) ^ (∑ i : Fin 4, r i) :=
                  Finset.prod_pow_eq_pow_sum _ _ _
              _ ≤ (fourEndpointFusedRowMax n alpha hAlpha) ^
                    (∑ i : Fin 4, fourEndpointMultiplicity alpha hAlpha k i) :=
                  pow_le_pow_right₀ hR1 (Finset.sum_le_sum fun i _ => hrle i)
          rw [mul_comm (fourEndpointD n alpha hAlpha k r)]
          exact mul_le_mul_left hprod _
      _ = (fourEndpointFusedRowMax n alpha hAlpha) ^
            (∑ i : Fin 4, fourEndpointMultiplicity alpha hAlpha k i) *
          ∑ r ∈ partialSubprofileBox (fourEndpointMultiplicity alpha hAlpha k),
            fourEndpointD n alpha hAlpha k r := (Finset.mul_sum _ _ _).symm
  · -- the unit-size endpoint type carries a genuine transport charge
    have hu3' : fourEndpointSize alpha hAlpha 3 = 1 := by
      have h3 := e625_size_eq alpha hAlpha 3
      have hv : ((3 : Fin 4) : ℕ) = 3 := rfl
      rw [hv] at h3
      omega
    have hmass : fourEndpointMarginMass alpha hAlpha
        (fourEndpointMultiplicity alpha hAlpha k)
        = fourEndpointSize alpha hAlpha 0 * fourEndpointMultiplicity alpha hAlpha k 0 +
          fourEndpointSize alpha hAlpha 1 * fourEndpointMultiplicity alpha hAlpha k 1 +
          fourEndpointSize alpha hAlpha 2 * fourEndpointMultiplicity alpha hAlpha k 2 +
          fourEndpointMultiplicity alpha hAlpha k 3 := by
      unfold fourEndpointMarginMass
      rw [Fin.sum_univ_four, hu3', one_mul]
    rw [e625_box_split (fourEndpointMultiplicity alpha hAlpha k)
        (fun r => fourEndpointD n alpha hAlpha k r *
          ∏ i : Fin 4, (e625A n alpha hAlpha i) ^ r i),
      e625_box_split (fourEndpointMultiplicity alpha hAlpha k)
        (fun r => fourEndpointD n alpha hAlpha k r)]
    simp only [Finset.mul_sum]
    refine Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb =>
      Finset.sum_le_sum fun c hc => ?_
    rw [← Finset.mul_sum]
    have ha' : a ≤ fourEndpointMultiplicity alpha hAlpha k 0 := by
      have := Finset.mem_range.mp ha; omega
    have hb' : b ≤ fourEndpointMultiplicity alpha hAlpha k 1 := by
      have := Finset.mem_range.mp hb; omega
    have hc' : c ≤ fourEndpointMultiplicity alpha hAlpha k 2 := by
      have := Finset.mem_range.mp hc; omega
    have hmn : fourEndpointSize alpha hAlpha 0 * a + fourEndpointSize alpha hAlpha 1 * b +
        fourEndpointSize alpha hAlpha 2 * c + fourEndpointMultiplicity alpha hAlpha k 3 ≤ n := by
      refine le_trans ?_ (hmass ▸ hkn)
      exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
        (Nat.mul_le_mul_left _ ha') (Nat.mul_le_mul_left _ hb'))
        (Nat.mul_le_mul_left _ hc')) (le_refl _)
    have hprodeq : ∀ t : ℕ, ∏ i : Fin 4, (e625A n alpha hAlpha i) ^ (![a, b, c, t] i)
        = (e625A n alpha hAlpha 0 ^ a * e625A n alpha hAlpha 1 ^ b *
            e625A n alpha hAlpha 2 ^ c) * e625A n alpha hAlpha 3 ^ t := by
      intro t
      rw [Fin.prod_univ_four]
      rfl
    have hsumK : a + b + c + fourEndpointMultiplicity alpha hAlpha k 3
        ≤ ∑ i : Fin 4, fourEndpointMultiplicity alpha hAlpha k i := by
      rw [Fin.sum_univ_four]
      omega
    calc ∑ t ∈ Finset.range (fourEndpointMultiplicity alpha hAlpha k 3 + 1),
          fourEndpointD n alpha hAlpha k ![a, b, c, t] *
            ∏ i : Fin 4, (e625A n alpha hAlpha i) ^ (![a, b, c, t] i)
        = (e625A n alpha hAlpha 0 ^ a * e625A n alpha hAlpha 1 ^ b *
            e625A n alpha hAlpha 2 ^ c) *
          ∑ t ∈ Finset.range (fourEndpointMultiplicity alpha hAlpha k 3 + 1),
            fourEndpointD n alpha hAlpha k ![a, b, c, t] * e625A n alpha hAlpha 3 ^ t := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [hprodeq t]
          ring
      _ ≤ (e625A n alpha hAlpha 0 ^ a * e625A n alpha hAlpha 1 ^ b *
            e625A n alpha hAlpha 2 ^ c) *
          ((fourEndpointFusedRowMax n alpha hAlpha) ^
              (fourEndpointMultiplicity alpha hAlpha k 3) *
            ∑ t ∈ Finset.range (fourEndpointMultiplicity alpha hAlpha k 3 + 1),
              fourEndpointD n alpha hAlpha k ![a, b, c, t]) :=
          mul_le_mul_right (e625_inner_bound n alpha hAlpha k hu3' a b c hmn) _
      _ ≤ ((fourEndpointFusedRowMax n alpha hAlpha) ^ a *
            (fourEndpointFusedRowMax n alpha hAlpha) ^ b *
            (fourEndpointFusedRowMax n alpha hAlpha) ^ c) *
          ((fourEndpointFusedRowMax n alpha hAlpha) ^
              (fourEndpointMultiplicity alpha hAlpha k 3) *
            ∑ t ∈ Finset.range (fourEndpointMultiplicity alpha hAlpha k 3 + 1),
              fourEndpointD n alpha hAlpha k ![a, b, c, t]) := by
          have h0 := e625_A_le_rowMax n alpha hAlpha 0 (e625_size_two_le alpha hAlpha 0 (by norm_num))
          have h1 := e625_A_le_rowMax n alpha hAlpha 1 (e625_size_two_le alpha hAlpha 1 (by norm_num))
          have h2 := e625_A_le_rowMax n alpha hAlpha 2 (e625_size_two_le alpha hAlpha 2 (by norm_num))
          exact mul_le_mul_left (mul_le_mul' (mul_le_mul'
            (pow_le_pow_left' h0 a) (pow_le_pow_left' h1 b)) (pow_le_pow_left' h2 c)) _
      _ = (fourEndpointFusedRowMax n alpha hAlpha) ^
            (a + b + c + fourEndpointMultiplicity alpha hAlpha k 3) *
          ∑ t ∈ Finset.range (fourEndpointMultiplicity alpha hAlpha k 3 + 1),
            fourEndpointD n alpha hAlpha k ![a, b, c, t] := by
          rw [pow_add, pow_add, pow_add]
          ring
      _ ≤ (fourEndpointFusedRowMax n alpha hAlpha) ^
            (∑ i : Fin 4, fourEndpointMultiplicity alpha hAlpha k i) *
          ∑ t ∈ Finset.range (fourEndpointMultiplicity alpha hAlpha k 3 + 1),
            fourEndpointD n alpha hAlpha k ![a, b, c, t] :=
          mul_le_mul_left (pow_le_pow_right₀ hR1 hsumK) _

private lemma e625_sum_X_le (n alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hkn : fourEndpointMarginMass alpha hAlpha
      (fourEndpointMultiplicity alpha hAlpha k) ≤ n)
    (S : Finset FourEndpointFullTable) :
    ∑ L ∈ S, e625X n alpha hAlpha k L ≤
      (fourEndpointFusedRowMax n alpha hAlpha) ^
          (∑ i : Fin 4, fourEndpointMultiplicity alpha hAlpha k i) *
        ∑ r ∈ partialSubprofileBox (fourEndpointMultiplicity alpha hAlpha k),
          fourEndpointD n alpha hAlpha k r := by
  classical
  set box := partialSubprofileBox (fourEndpointMultiplicity alpha hAlpha k) with hbox
  set g : FourEndpointFullTable → (Fin 4 → ℕ) :=
    fun L => (fun i => fourEndpointRowMargin L i) with hg
  have hfilter : ∑ L ∈ S with g L ∈ box, e625X n alpha hAlpha k L
      = ∑ L ∈ S, e625X n alpha hAlpha k L := by
    refine Finset.sum_filter_of_ne ?_
    intro L _ hne
    by_contra hnb
    refine hne ?_
    have : fourEndpointD n alpha hAlpha k (g L) = 0 := by
      refine e625_D_zero_of_not_box n alpha hAlpha k _ ?_
      intro hcon
      exact hnb (by rw [hbox, mem_partialSubprofileBox]; exact hcon)
    unfold e625X
    rw [hg] at this
    rw [this, zero_mul, zero_mul]
  rw [← hfilter]
  have hmaps : ∀ L ∈ S.filter (fun L => g L ∈ box), g L ∈ box := by
    intro L hL
    exact (Finset.mem_filter.mp hL).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun L => e625X n alpha hAlpha k L)]
  refine le_trans (Finset.sum_le_sum (fun r _ => ?_)) (e625_box_bound n alpha hAlpha k hkn)
  have hcongr : ∀ L ∈ (S.filter (fun L => g L ∈ box)).filter (fun L => g L = r),
      e625X n alpha hAlpha k L
        = fourEndpointD n alpha hAlpha k r * ((e625Mult L : ENNReal) *
            ∏ i : Fin 4, ∏ j : Fin 4, (e625Kern n alpha hAlpha i j) ^ L.toFun i j) := by
    intro L hL
    have hgr : (fun i => fourEndpointRowMargin L i) = r := (Finset.mem_filter.mp hL).2
    unfold e625X
    rw [hgr, mul_assoc]
  rw [Finset.sum_congr rfl hcongr, ← Finset.mul_sum]
  refine mul_le_mul_right (e625_rowgroup n alpha hAlpha r _ ?_) _
  intro L hL i
  have hgr : (fun i => fourEndpointRowMargin L i) = r := (Finset.mem_filter.mp hL).2
  exact congrFun hgr i

/-- The general finite-set form of the target statement. -/
private lemma e625_main (n alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) (T : Finset FourEndpointFullTable) :
    (∑ L ∈ T, fourEndpointW n alpha hAlpha k L *
        ∏ i : Fin 4, ∏ j : Fin 4,
          (fourEndpointThreeQuarterDeficitFactor n alpha hAlpha i j) ^ L.toFun i j) ≤
      (fourEndpointFusedRowMax n alpha hAlpha) ^
          (∑ i : Fin 4, fourEndpointMultiplicity alpha hAlpha k i) *
        ∑ r ∈ partialSubprofileBox (fourEndpointMultiplicity alpha hAlpha k),
          fourEndpointD n alpha hAlpha k r := by
  classical
  by_cases hkn : fourEndpointMarginMass alpha hAlpha
      (fourEndpointMultiplicity alpha hAlpha k) ≤ n
  · -- finite branch
    have hstep : ∀ L ∈ T, 2 * (fourEndpointW n alpha hAlpha k L *
        ∏ i : Fin 4, ∏ j : Fin 4,
          (fourEndpointThreeQuarterDeficitFactor n alpha hAlpha i j) ^ L.toFun i j)
      ≤ e625X n alpha hAlpha k L + e625X n alpha hAlpha k (e625Tr L) :=
      fun L _ => e625_table_amgm n alpha hAlpha k hkn L
    have htr : ∑ L ∈ T, e625X n alpha hAlpha k (e625Tr L)
        = ∑ L ∈ T.image e625Tr, e625X n alpha hAlpha k L := by
      rw [Finset.sum_image]
      intro a _ b _ hab
      have : a.toFun = b.toFun := by
        funext i j
        have := congrArg (fun M => M.toFun j i) hab
        simpa [e625Tr] using this
      exact FourEndpointFullTable.ext this
    have hsum : 2 * (∑ L ∈ T, fourEndpointW n alpha hAlpha k L *
        ∏ i : Fin 4, ∏ j : Fin 4,
          (fourEndpointThreeQuarterDeficitFactor n alpha hAlpha i j) ^ L.toFun i j)
        ≤ 2 * ((fourEndpointFusedRowMax n alpha hAlpha) ^
          (∑ i : Fin 4, fourEndpointMultiplicity alpha hAlpha k i) *
        ∑ r ∈ partialSubprofileBox (fourEndpointMultiplicity alpha hAlpha k),
          fourEndpointD n alpha hAlpha k r) := by
      calc 2 * (∑ L ∈ T, fourEndpointW n alpha hAlpha k L *
            ∏ i : Fin 4, ∏ j : Fin 4,
              (fourEndpointThreeQuarterDeficitFactor n alpha hAlpha i j) ^ L.toFun i j)
          = ∑ L ∈ T, 2 * (fourEndpointW n alpha hAlpha k L *
            ∏ i : Fin 4, ∏ j : Fin 4,
              (fourEndpointThreeQuarterDeficitFactor n alpha hAlpha i j) ^ L.toFun i j) := by
            rw [Finset.mul_sum]
        _ ≤ ∑ L ∈ T, (e625X n alpha hAlpha k L + e625X n alpha hAlpha k (e625Tr L)) :=
            Finset.sum_le_sum hstep
        _ = (∑ L ∈ T, e625X n alpha hAlpha k L) +
              ∑ L ∈ T.image e625Tr, e625X n alpha hAlpha k L := by
            rw [Finset.sum_add_distrib, htr]
        _ ≤ ((fourEndpointFusedRowMax n alpha hAlpha) ^
              (∑ i : Fin 4, fourEndpointMultiplicity alpha hAlpha k i) *
            ∑ r ∈ partialSubprofileBox (fourEndpointMultiplicity alpha hAlpha k),
              fourEndpointD n alpha hAlpha k r) +
            ((fourEndpointFusedRowMax n alpha hAlpha) ^
              (∑ i : Fin 4, fourEndpointMultiplicity alpha hAlpha k i) *
            ∑ r ∈ partialSubprofileBox (fourEndpointMultiplicity alpha hAlpha k),
              fourEndpointD n alpha hAlpha k r) :=
            add_le_add (e625_sum_X_le n alpha hAlpha k hkn T)
              (e625_sum_X_le n alpha hAlpha k hkn _)
        _ = 2 * ((fourEndpointFusedRowMax n alpha hAlpha) ^
              (∑ i : Fin 4, fourEndpointMultiplicity alpha hAlpha k i) *
            ∑ r ∈ partialSubprofileBox (fourEndpointMultiplicity alpha hAlpha k),
              fourEndpointD n alpha hAlpha k r) := by ring
    exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp hsum
  · -- infinite branch
    have hmem : fourEndpointMultiplicity alpha hAlpha k ∈
        partialSubprofileBox (fourEndpointMultiplicity alpha hAlpha k) := by
      simp [mem_partialSubprofileBox, IsPartialSubprofile]
    have hle : fourEndpointD n alpha hAlpha k (fourEndpointMultiplicity alpha hAlpha k) ≤
        ∑ r ∈ partialSubprofileBox (fourEndpointMultiplicity alpha hAlpha k),
          fourEndpointD n alpha hAlpha k r :=
      Finset.single_le_sum (f := fun r => fourEndpointD n alpha hAlpha k r)
        (fun _ _ => zero_le) hmem
    have htop : ∑ r ∈ partialSubprofileBox (fourEndpointMultiplicity alpha hAlpha k),
        fourEndpointD n alpha hAlpha k r = ⊤ := by
      rw [← top_le_iff]
      exact (e625_D_top_of_lt n alpha hAlpha k hkn) ▸ hle
    rw [htop]
    have hR : (fourEndpointFusedRowMax n alpha hAlpha) ^
        (∑ i : Fin 4, fourEndpointMultiplicity alpha hAlpha k i) ≠ 0 := by
      have := e625_one_le_rowMax n alpha hAlpha
      exact pow_ne_zero _ (by rintro h; rw [h] at this; simp at this)
    rw [ENNReal.mul_top hR]
    exact le_top

/-- The realized-table deficit product is absorbed directly into the endpoint
transport kernel, leaving only a finite fused row maximum and the existing
one-sided diagonal-margin sum. -/
theorem sum_fourEndpointRealized_W_mul_threeQuarterProduct_le_fusedRowMax
    (n alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) :
    (∑ L : ↥(fourEndpointRealizedFullTables alpha hAlpha k),
      fourEndpointW n alpha hAlpha k L.1 *
        ∏ i : Fin 4, ∏ j : Fin 4,
          (fourEndpointThreeQuarterDeficitFactor n alpha hAlpha i j) ^
            L.1.toFun i j) ≤
      (fourEndpointFusedRowMax n alpha hAlpha) ^
          (∑ i : Fin 4, fourEndpointMultiplicity alpha hAlpha k i) *
        ∑ r ∈ partialSubprofileBox
            (fourEndpointMultiplicity alpha hAlpha k),
          fourEndpointD n alpha hAlpha k r := by
  rw [Finset.sum_coe_sort (fourEndpointRealizedFullTables alpha hAlpha k)
    (fun L => fourEndpointW n alpha hAlpha k L *
      ∏ i : Fin 4, ∏ j : Fin 4,
        (fourEndpointThreeQuarterDeficitFactor n alpha hAlpha i j) ^ L.toFun i j)]
  exact e625_main n alpha hAlpha k (fourEndpointRealizedFullTables alpha hAlpha k)

end

end Erdos625
