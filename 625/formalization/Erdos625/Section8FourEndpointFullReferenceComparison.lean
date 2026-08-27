import Erdos625.Section8FourEndpointPartialAggregateWeight
import Erdos625.Section8EndpointAllHighDecoration
import Mathlib.Tactic

/-!
# Section VIII: partial aggregates versus full endpoint references

This file compares one attained partial
four-endpoint aggregate with the zero-deficit reference on the same block
support. The comparison uses one global falling-factorial loss.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

private theorem scratch_nearDen_eq_ascFactorial (d h : Nat) :
    (∏ t ∈ Finset.Icc 1 h, (d + t : Nat)) =
      (d + 1).ascFactorial h := by
  induction h with
  | zero => simp
  | succ h ih =>
      rw [Finset.prod_Icc_succ_top (by omega), ih]
      rw [Nat.ascFactorial_succ]
      ring

private theorem scratch_lower_partial_div_factorial
    (m h : Nat) (hhm : h ≤ m) :
    ((m.descFactorial (m - h) : Nat) : ENNReal) /
        (((m - h).factorial : Nat) : ENNReal) =
      (Nat.choose m h : ENNReal) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  rw [Nat.choose_symm hhm]
  push_cast
  rw [div_eq_mul_inv]
  calc
    ((m - h).factorial : ENNReal) * (Nat.choose m h : ENNReal) *
        (((m - h).factorial : ENNReal))⁻¹ =
      (Nat.choose m h : ENNReal) *
        (((m - h).factorial : ENNReal) *
          (((m - h).factorial : ENNReal))⁻¹) := by ac_rfl
    _ = _ := by
      rw [ENNReal.mul_inv_cancel]
      · simp
      · exact_mod_cast Nat.factorial_ne_zero (m - h)
      · exact ENNReal.natCast_ne_top _

private theorem scratch_deficitExponent_succ
    (m h : Nat) (hhsucc : h + 1 ≤ m) :
    (h + 1) * m - (h + 1) * (h + 1 + 1) / 2 =
      h * m - h * (h + 1) / 2 + (m - (h + 1)) := by
  rw [tsub_eq_of_eq_add]
  zify [hhsucc]
  rw [Nat.cast_sub] <;>
    push_cast <;>
    repeat nlinarith [Nat.div_mul_le_self (h * (h + 1)) 2]
  grind

private theorem scratch_choose_sub_add_deficitExponent
    (m h : Nat) (hhm : h ≤ m) :
    (m - h).choose 2 + (h * m - h * (h + 1) / 2) =
      m.choose 2 := by
  induction h generalizing m with
  | zero => simp
  | succ h ih =>
      have hhsucc : h + 1 ≤ m := by omega
      have hhexp := scratch_deficitExponent_succ m h hhsucc
      have hpred : m - h = (m - (h + 1)) + 1 := by omega
      have hchoose :
          (m - h).choose 2 =
            (m - (h + 1)) + (m - (h + 1)).choose 2 := by
        rw [hpred, Nat.choose_succ_succ]
        simp
      have hind := ih m (by omega)
      omega

private theorem scratch_reward_deficit
    (m h : Nat) (hlarge : 3 ≤ m - h) :
    (localSignRewardNat (m - h) : ENNReal) *
        (2 : ENNReal) ^ (h * m - h * (h + 1) / 2) =
      (localSignRewardNat m : ENNReal) := by
  have hhm : h ≤ m := by omega
  have hm : 3 ≤ m := le_trans hlarge (Nat.sub_le m h)
  simp only [localSignRewardNat, if_pos hlarge, if_pos hm]
  push_cast
  rw [← pow_add]
  congr 1
  have hexp :=
    scratch_choose_sub_add_deficitExponent m h hhm
  have hchoosePartial : 1 ≤ (m - h).choose 2 := by
    have hmono := Nat.choose_le_choose 2 hlarge
    norm_num at hmono
    omega
  have hchooseFull : 1 ≤ m.choose 2 := by
    exact le_trans hchoosePartial
      (Nat.choose_le_choose 2 (Nat.sub_le m h))
  omega

private noncomputable def scratchPartialLocalFactor
    (m d x : Nat) : ENNReal :=
  (((m.descFactorial x : Nat) : ENNReal) *
      (((m + d).descFactorial x : Nat) : ENNReal) /
        (x.factorial : ENNReal)) *
    (localSignRewardNat x : ENNReal)

private theorem scratch_descFactorial_add_eq_ascFactorial
    (d h : Nat) :
    (d + h).descFactorial h = (d + 1).ascFactorial h := by
  have hdesc := Nat.factorial_mul_descFactorial
    (n := d + h) (k := h) (by omega)
  have hasc := Nat.factorial_mul_ascFactorial d h
  have hsub : d + h - h = d := by omega
  rw [hsub] at hdesc
  exact Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos d)
    (hdesc.trans hasc.symm)

private theorem scratch_upper_descFactorial_split
    (m d h : Nat) (hhm : h ≤ m) :
    (((m + d).descFactorial m : Nat) : ENNReal) =
      (((d + 1).ascFactorial h : Nat) : ENNReal) *
        (((m + d).descFactorial (m - h) : Nat) : ENNReal) := by
  have hsplit := Nat.descFactorial_mul_descFactorial
    (n := m + d) (k := m - h) (m := m) (by omega)
  have hsub₁ : m + d - (m - h) = d + h := by omega
  have hsub₂ : m - (m - h) = h := by omega
  rw [hsub₁, hsub₂,
    scratch_descFactorial_add_eq_ascFactorial d h] at hsplit
  exact_mod_cast hsplit.symm

private theorem scratch_partialLocalFactor_sub
    (m d h : Nat) (hhm : h ≤ m) :
    scratchPartialLocalFactor m d (m - h) =
      (Nat.choose m h : ENNReal) *
        (((m + d).descFactorial (m - h) : Nat) : ENNReal) *
          (localSignRewardNat (m - h) : ENNReal) := by
  unfold scratchPartialLocalFactor
  calc
    (((m.descFactorial (m - h) : Nat) : ENNReal) *
          (((m + d).descFactorial (m - h) : Nat) : ENNReal) /
          ((m - h).factorial : ENNReal)) *
        (localSignRewardNat (m - h) : ENNReal) =
      ((((m.descFactorial (m - h) : Nat) : ENNReal) /
          ((m - h).factorial : ENNReal)) *
        (((m + d).descFactorial (m - h) : Nat) : ENNReal)) *
          (localSignRewardNat (m - h) : ENNReal) := by
            simp only [div_eq_mul_inv]
            ac_rfl
    _ = _ := by
      rw [scratch_lower_partial_div_factorial m h hhm]

private theorem scratch_partialLocalFactor_full
    (m d : Nat) :
    scratchPartialLocalFactor m d m =
      (((m + d).descFactorial m : Nat) : ENNReal) *
        (localSignRewardNat m : ENNReal) := by
  unfold scratchPartialLocalFactor
  rw [Nat.descFactorial_self]
  rw [mul_div_assoc, ENNReal.mul_div_cancel]
  · exact_mod_cast Nat.factorial_ne_zero m
  · exact ENNReal.natCast_ne_top _

private theorem scratch_partialLocalFactor_cross
    (m d h : Nat) (hhm : h ≤ m) (hlarge : 3 ≤ m - h) :
    scratchPartialLocalFactor m d (m - h) *
        (((d + 1).ascFactorial h : Nat) : ENNReal) *
          (2 : ENNReal) ^ (h * m - h * (h + 1) / 2) =
      scratchPartialLocalFactor m d m *
        (Nat.choose m h : ENNReal) := by
  rw [scratch_partialLocalFactor_sub m d h hhm,
    scratch_partialLocalFactor_full,
    scratch_upper_descFactorial_split m d h hhm]
  have hreward := scratch_reward_deficit m h hlarge
  calc
    (Nat.choose m h : ENNReal) *
          (((m + d).descFactorial (m - h) : Nat) : ENNReal) *
          (localSignRewardNat (m - h) : ENNReal) *
          (((d + 1).ascFactorial h : Nat) : ENNReal) *
          (2 : ENNReal) ^ (h * m - h * (h + 1) / 2) =
      (Nat.choose m h : ENNReal) *
          (((m + d).descFactorial (m - h) : Nat) : ENNReal) *
          (((d + 1).ascFactorial h : Nat) : ENNReal) *
          ((localSignRewardNat (m - h) : ENNReal) *
            (2 : ENNReal) ^ (h * m - h * (h + 1) / 2)) := by ac_rfl
    _ = (Nat.choose m h : ENNReal) *
          (((m + d).descFactorial (m - h) : Nat) : ENNReal) *
          (((d + 1).ascFactorial h : Nat) : ENNReal) *
          (localSignRewardNat m : ENNReal) := by rw [hreward]
    _ = _ := by ac_rfl

private theorem scratch_partialLocalFactor_mul_pow_eq_full_mul_near
    (n m d h : Nat) (hhalf : 2 * h < m) (hlarge : 3 ≤ m - h) :
    scratchPartialLocalFactor m d (m - h) * (n : ENNReal) ^ h =
      scratchPartialLocalFactor m d m * nearCellTerm n m d h := by
  have hhm : h ≤ m := by omega
  let D : ENNReal := (((d + 1).ascFactorial h : Nat) : ENNReal)
  let E : Nat := h * m - h * (h + 1) / 2
  have hDnat : (d + 1).ascFactorial h ≠ 0 := by
    positivity
  have hD0 : D ≠ 0 := by
    change (((d + 1).ascFactorial h : Nat) : ENNReal) ≠ 0
    exact_mod_cast hDnat
  have hDtop : D ≠ ∞ := ENNReal.natCast_ne_top _
  have hpow0 : (2 : ENNReal) ^ E ≠ 0 := by positivity
  have hpowtop : (2 : ENNReal) ^ E ≠ ∞ := by
    exact ENNReal.pow_ne_top (by norm_num)
  have hlocal :=
    scratch_partialLocalFactor_cross m d h hhm hlarge
  change scratchPartialLocalFactor m d (m - h) * D *
      (2 : ENNReal) ^ E =
    scratchPartialLocalFactor m d m * (Nat.choose m h : ENNReal) at hlocal
  have hcancelD : D * D⁻¹ = 1 :=
    ENNReal.mul_inv_cancel hD0 hDtop
  have hcancelPow :
      (2 : ENNReal) ^ E * ((2 : ENNReal) ^ E)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel hpow0 hpowtop
  unfold nearCellTerm
  rw [scratch_nearDen_eq_ascFactorial]
  change
    scratchPartialLocalFactor m d (m - h) * (n : ENNReal) ^ h =
      scratchPartialLocalFactor m d m *
        ((((n : ENNReal) ^ h * (Nat.choose m h : ENNReal)) / D) *
          ((2 : ENNReal) ^ E)⁻¹)
  rw [div_eq_mul_inv]
  calc
    scratchPartialLocalFactor m d (m - h) * (n : ENNReal) ^ h =
        (scratchPartialLocalFactor m d (m - h) * D *
            (2 : ENNReal) ^ E) *
          ((n : ENNReal) ^ h * D⁻¹ * ((2 : ENNReal) ^ E)⁻¹) := by
      calc
        scratchPartialLocalFactor m d (m - h) * (n : ENNReal) ^ h =
            scratchPartialLocalFactor m d (m - h) * (n : ENNReal) ^ h *
              (D * D⁻¹) *
              ((2 : ENNReal) ^ E * ((2 : ENNReal) ^ E)⁻¹) := by
          rw [hcancelD, hcancelPow]
          simp
        _ = _ := by ac_rfl
    _ = (scratchPartialLocalFactor m d m *
          (Nat.choose m h : ENNReal)) *
          ((n : ENNReal) ^ h * D⁻¹ * ((2 : ENNReal) ^ E)⁻¹) := by
      rw [hlocal]
    _ = scratchPartialLocalFactor m d m *
          ((((n : ENNReal) ^ h * (Nat.choose m h : ENNReal)) * D⁻¹) *
            ((2 : ENNReal) ^ E)⁻¹) := by ac_rfl

private theorem scratch_fourEndpoint_max_eq_overlap_add_distance
    (alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4) :
    max (fourEndpointSize alpha hAlpha i)
        (fourEndpointSize alpha hAlpha j) =
      fourEndpointOverlapSize alpha hAlpha i j +
        Nat.dist i.val j.val := by
  have hsize (q : Fin 4) :
      fourEndpointSize alpha hAlpha q = alpha - 2 - q.val := by
    unfold fourEndpointSize fourEndpointCoordinate fourDeficitCoordinate
    simp [fourDeficit]
    omega
  have hdist :
      max (fourEndpointSize alpha hAlpha i)
          (fourEndpointSize alpha hAlpha j) -
        min (fourEndpointSize alpha hAlpha i)
          (fourEndpointSize alpha hAlpha j) =
        Nat.dist i.val j.val := by
    rw [hsize, hsize, Nat.dist_eq_max_sub_min]
    by_cases hij : i.val ≤ j.val
    · have hs : alpha - 2 - j.val ≤ alpha - 2 - i.val := by omega
      rw [max_eq_left hs, min_eq_right hs,
        max_eq_right hij, min_eq_left hij]
      omega
    · have hji : j.val ≤ i.val := by omega
      have hs : alpha - 2 - i.val ≤ alpha - 2 - j.val := by omega
      rw [max_eq_right hs, min_eq_left hs,
        max_eq_left hji, min_eq_right hji]
      omega
  unfold fourEndpointOverlapSize
  have hle :
      min (fourEndpointSize alpha hAlpha i)
          (fourEndpointSize alpha hAlpha j) ≤
        max (fourEndpointSize alpha hAlpha i)
          (fourEndpointSize alpha hAlpha j) :=
    min_le_max
  omega

private theorem scratch_fourEndpointPartialLocalFactor_mul_pow_eq_full_mul_near
    (n alpha : Nat) (hAlpha : 5 < alpha) (hHigh : 8 < alpha)
    (i j : Fin 4) (h : Nat)
    (hhalf :
      2 * h < fourEndpointOverlapSize alpha hAlpha i j) :
    (((((fourEndpointSize alpha hAlpha i).descFactorial
          (fourEndpointOverlapSize alpha hAlpha i j - h) : Nat) : ENNReal) *
        (((fourEndpointSize alpha hAlpha j).descFactorial
          (fourEndpointOverlapSize alpha hAlpha i j - h) : Nat) : ENNReal) /
        ((fourEndpointOverlapSize alpha hAlpha i j - h).factorial :
          ENNReal)) *
      (localSignRewardNat
        (fourEndpointOverlapSize alpha hAlpha i j - h) : ENNReal)) *
      (n : ENNReal) ^ h =
    fourEndpointLocalCellFactor alpha hAlpha i j *
      nearCellTerm n
        (fourEndpointOverlapSize alpha hAlpha i j)
        (Nat.dist i.val j.val) h := by
  have hlargest :
      7 ≤ fourEndpointLargestSize alpha hAlpha := by
    simp [fourEndpointLargestSize, fourEndpointOverlapSize,
      fourEndpointSize, fourEndpointCoordinate,
      fourDeficitCoordinate, fourDeficit]
    omega
  have hmhigh := fourEndpointOverlapSize_above_half_largest
    alpha hAlpha hHigh i j
  have hlarge :
      3 ≤ fourEndpointOverlapSize alpha hAlpha i j - h := by
    omega
  have hgeneric :=
    scratch_partialLocalFactor_mul_pow_eq_full_mul_near
      n (fourEndpointOverlapSize alpha hAlpha i j)
        (Nat.dist i.val j.val) h hhalf hlarge
  have hmax := scratch_fourEndpoint_max_eq_overlap_add_distance
    alpha hAlpha i j
  by_cases hij :
      fourEndpointSize alpha hAlpha i ≤
        fourEndpointSize alpha hAlpha j
  · have hi :
        fourEndpointSize alpha hAlpha i =
          fourEndpointOverlapSize alpha hAlpha i j := by
      simp [fourEndpointOverlapSize, min_eq_left hij]
    have hj :
        fourEndpointSize alpha hAlpha j =
          fourEndpointOverlapSize alpha hAlpha i j +
            Nat.dist i.val j.val := by
      simpa [max_eq_right hij] using hmax
    simpa [scratchPartialLocalFactor, fourEndpointLocalCellFactor,
      hi, hj] using hgeneric
  · have hji :
        fourEndpointSize alpha hAlpha j ≤
          fourEndpointSize alpha hAlpha i := by omega
    have hj :
        fourEndpointSize alpha hAlpha j =
          fourEndpointOverlapSize alpha hAlpha i j := by
      simp [fourEndpointOverlapSize, min_eq_right hji]
    have hi :
        fourEndpointSize alpha hAlpha i =
          fourEndpointOverlapSize alpha hAlpha i j +
            Nat.dist i.val j.val := by
      simpa [max_eq_left hji] using hmax
    simpa [scratchPartialLocalFactor, fourEndpointLocalCellFactor,
      hi, hj, mul_comm] using hgeneric

private noncomputable def scratchFourEndpointPartialLocalFactor
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)} {L : FourEndpointFullTable}
    (P : FourEndpointBlockPairing alpha hAlpha k L)
    (deficit : ∀ _e : ↥P.1.edges, Nat)
    (e : ↥P.1.edges) : ENNReal :=
  let x :=
    fourEndpointCellMultiplicityOfDeficit alpha hAlpha P deficit e
  ((((fourEndpointSize alpha hAlpha e.1.1.1).descFactorial x : Nat) :
        ENNReal) *
      (((fourEndpointSize alpha hAlpha e.1.2.1).descFactorial x : Nat) :
        ENNReal) /
      (x.factorial : ENNReal)) *
    (localSignRewardNat x : ENNReal)

private theorem scratch_fourEndpointPartialLocalFactor_edge_mul_pow_eq
    (n alpha : Nat) (hAlpha : 5 < alpha) (hHigh : 8 < alpha)
    {k : ColoringProfile (alpha + 1)} {L : FourEndpointFullTable}
    (P : FourEndpointBlockPairing alpha hAlpha k L)
    (deficit : ∀ _e : ↥P.1.edges, Nat)
    (e : ↥P.1.edges)
    (hhalf :
      2 * deficit e <
        fourEndpointCellFullMultiplicity alpha hAlpha P e) :
    scratchFourEndpointPartialLocalFactor alpha hAlpha P deficit e *
        (n : ENNReal) ^ deficit e =
      fourEndpointLocalCellFactor
          alpha hAlpha e.1.1.1 e.1.2.1 *
        nearCellTerm n
          (fourEndpointCellFullMultiplicity alpha hAlpha P e)
          (Nat.dist e.1.1.1.val e.1.2.1.val)
          (deficit e) := by
  simpa [scratchFourEndpointPartialLocalFactor,
    fourEndpointCellMultiplicityOfDeficit,
    fourEndpointCellFullMultiplicity] using
    scratch_fourEndpointPartialLocalFactor_mul_pow_eq_full_mul_near
      n alpha hAlpha hHigh e.1.1.1 e.1.2.1 (deficit e) hhalf

private theorem scratch_fourEndpointPartialLocalFactor_edge_mul_pow_eq_zero
    (n alpha : Nat) (hAlpha : 5 < alpha) (hHigh : 8 < alpha)
    {k : ColoringProfile (alpha + 1)} {L : FourEndpointFullTable}
    (P : FourEndpointBlockPairing alpha hAlpha k L)
    (deficit : ∀ _e : ↥P.1.edges, Nat)
    (e : ↥P.1.edges)
    (hhalf :
      2 * deficit e <
        fourEndpointCellFullMultiplicity alpha hAlpha P e) :
    scratchFourEndpointPartialLocalFactor alpha hAlpha P deficit e *
        (n : ENNReal) ^ deficit e =
      scratchFourEndpointPartialLocalFactor
          alpha hAlpha P (fun _ => 0) e *
        nearCellTerm n
          (fourEndpointCellFullMultiplicity alpha hAlpha P e)
          (Nat.dist e.1.1.1.val e.1.2.1.val)
          (deficit e) := by
  simpa [scratchFourEndpointPartialLocalFactor,
    fourEndpointCellMultiplicityOfDeficit,
    fourEndpointCellFullMultiplicity,
    fourEndpointLocalCellFactor] using
    scratch_fourEndpointPartialLocalFactor_edge_mul_pow_eq
      n alpha hAlpha hHigh P deficit e hhalf

private noncomputable def scratchRootFourEndpointPartialLocalFactor
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)} {L : FourEndpointFullTable}
    (P : FourEndpointBlockPairing alpha hAlpha k L)
    (deficit : ∀ _e : ↥P.1.edges, Nat)
    (e : ↥P.1.edges) : ENNReal :=
  (((fourEndpointSize alpha hAlpha e.1.1.1).descFactorial
        (fourEndpointCellMultiplicityOfDeficit
          alpha hAlpha P deficit e) *
      (fourEndpointSize alpha hAlpha e.1.2.1).descFactorial
        (fourEndpointCellMultiplicityOfDeficit
          alpha hAlpha P deficit e) : Nat) : ENNReal) /
    ((fourEndpointCellMultiplicityOfDeficit
      alpha hAlpha P deficit e).factorial : ENNReal) *
      (localSignRewardNat
        (fourEndpointCellMultiplicityOfDeficit
          alpha hAlpha P deficit e) : ENNReal)

private theorem scratch_rootFourEndpointPartialLocalFactor_edge_mul_pow_eq
    (n alpha : Nat) (hAlpha : 5 < alpha) (hHigh : 8 < alpha)
    {k : ColoringProfile (alpha + 1)} {L : FourEndpointFullTable}
    (P : FourEndpointBlockPairing alpha hAlpha k L)
    (deficit : ∀ _e : ↥P.1.edges, Nat)
    (e : ↥P.1.edges)
    (hhalf :
      2 * deficit e <
        fourEndpointCellFullMultiplicity alpha hAlpha P e) :
    scratchRootFourEndpointPartialLocalFactor
        alpha hAlpha P deficit e *
        (n : ENNReal) ^ deficit e =
      fourEndpointLocalCellFactor
          alpha hAlpha e.1.1.1 e.1.2.1 *
        nearCellTerm n
          (fourEndpointCellFullMultiplicity alpha hAlpha P e)
          (Nat.dist e.1.1.1.val e.1.2.1.val)
          (deficit e) := by
  simpa [scratchRootFourEndpointPartialLocalFactor,
    scratchFourEndpointPartialLocalFactor, Nat.cast_mul] using
    scratch_fourEndpointPartialLocalFactor_edge_mul_pow_eq
      n alpha hAlpha hHigh P deficit e hhalf

private noncomputable def fourEndpointPartialLocalFactor
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)} {L : FourEndpointFullTable}
    (P : FourEndpointBlockPairing alpha hAlpha k L)
    (deficit : ∀ _e : ↥P.1.edges, Nat)
    (e : ↥P.1.edges) : ENNReal :=
  (((fourEndpointSize alpha hAlpha e.1.1.1).descFactorial
        (fourEndpointCellMultiplicityOfDeficit
          alpha hAlpha P deficit e) *
      (fourEndpointSize alpha hAlpha e.1.2.1).descFactorial
        (fourEndpointCellMultiplicityOfDeficit
          alpha hAlpha P deficit e) : Nat) : ENNReal) /
    ((fourEndpointCellMultiplicityOfDeficit
      alpha hAlpha P deficit e).factorial : ENNReal) *
      (localSignRewardNat
        (fourEndpointCellMultiplicityOfDeficit
          alpha hAlpha P deficit e) : ENNReal)

private theorem fourEndpointPartialAggregateWeight_eq_prod_local_div
    (n alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)} {L : FourEndpointFullTable}
    (P : FourEndpointBlockPairing alpha hAlpha k L)
    (deficit : ∀ _e : ↥P.1.edges, Nat) :
    fourEndpointPartialAggregateWeight n alpha hAlpha P deficit =
      (∏ e : ↥P.1.edges,
        fourEndpointPartialLocalFactor alpha hAlpha P deficit e) /
        ((n.descFactorial
          (fourEndpointPartialTotalMultiplicity
            alpha hAlpha P deficit) : Nat) : ENNReal) := by
  classical
  have hfacNat :
      fourEndpointPartialCellFactorialProduct
        alpha hAlpha P deficit ≠ 0 :=
    fourEndpointPartialCellFactorialProduct_ne_zero
      alpha hAlpha P deficit
  have hfac0 :
      ((fourEndpointPartialCellFactorialProduct
        alpha hAlpha P deficit : Nat) : ENNReal) ≠ 0 := by
    exact_mod_cast hfacNat
  have hfacT :
      ((fourEndpointPartialCellFactorialProduct
        alpha hAlpha P deficit : Nat) : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hnum :
      ((fourEndpointPartialCellSelectionProduct
          alpha hAlpha P deficit : Nat) : ENNReal) /
          ((fourEndpointPartialCellFactorialProduct
            alpha hAlpha P deficit : Nat) : ENNReal) *
        fourEndpointPartialRewardProduct alpha hAlpha P deficit =
      ∏ e : ↥P.1.edges,
        fourEndpointPartialLocalFactor alpha hAlpha P deficit e := by
    rw [show
      ((fourEndpointPartialCellSelectionProduct
          alpha hAlpha P deficit : Nat) : ENNReal) /
          ((fourEndpointPartialCellFactorialProduct
            alpha hAlpha P deficit : Nat) : ENNReal) *
        fourEndpointPartialRewardProduct alpha hAlpha P deficit =
      (((fourEndpointPartialCellSelectionProduct
          alpha hAlpha P deficit : Nat) : ENNReal) *
        fourEndpointPartialRewardProduct alpha hAlpha P deficit) /
          ((fourEndpointPartialCellFactorialProduct
            alpha hAlpha P deficit : Nat) : ENNReal) by
      simp only [div_eq_mul_inv]
      ac_rfl]
    symm
    apply (ENNReal.eq_div_iff hfac0 hfacT).2
    unfold fourEndpointPartialCellFactorialProduct
      fourEndpointPartialCellSelectionProduct
      fourEndpointPartialRewardProduct
    rw [Nat.cast_prod, Nat.cast_prod]
    push_cast
    rw [← Finset.prod_mul_distrib]
    calc
      (∏ e : ↥P.1.edges,
          (((fourEndpointCellMultiplicityOfDeficit
            alpha hAlpha P deficit e).factorial : Nat) : ENNReal) *
            fourEndpointPartialLocalFactor alpha hAlpha P deficit e) =
          ∏ e : ↥P.1.edges,
            ((((fourEndpointSize alpha hAlpha e.1.1.1).descFactorial
                (fourEndpointCellMultiplicityOfDeficit
                  alpha hAlpha P deficit e) : Nat) : ENNReal) *
              (((fourEndpointSize alpha hAlpha e.1.2.1).descFactorial
                (fourEndpointCellMultiplicityOfDeficit
                  alpha hAlpha P deficit e) : Nat) : ENNReal)) *
                (localSignRewardNat
                  (fourEndpointCellMultiplicityOfDeficit
                    alpha hAlpha P deficit e) : ENNReal) := by
            apply Finset.prod_congr rfl
            intro e _he
            unfold fourEndpointPartialLocalFactor
            push_cast
            let a : ENNReal :=
              (((fourEndpointCellMultiplicityOfDeficit
                alpha hAlpha P deficit e).factorial : Nat) : ENNReal)
            let b : ENNReal :=
              (((fourEndpointSize alpha hAlpha e.1.1.1).descFactorial
                (fourEndpointCellMultiplicityOfDeficit
                  alpha hAlpha P deficit e) : Nat) : ENNReal) *
              (((fourEndpointSize alpha hAlpha e.1.2.1).descFactorial
                (fourEndpointCellMultiplicityOfDeficit
                  alpha hAlpha P deficit e) : Nat) : ENNReal)
            let c : ENNReal :=
              (localSignRewardNat
                (fourEndpointCellMultiplicityOfDeficit
                  alpha hAlpha P deficit e) : ENNReal)
            change a * ((b / a) * c) = b * c
            calc
              a * ((b / a) * c) = (a * (b / a)) * c := by
                rw [mul_assoc]
              _ = b * c := by
                rw [ENNReal.mul_div_cancel]
                · unfold a
                  exact_mod_cast Nat.factorial_ne_zero
                    (fourEndpointCellMultiplicityOfDeficit
                      alpha hAlpha P deficit e)
                · unfold a
                  exact ENNReal.natCast_ne_top _
      _ = (∏ e : ↥P.1.edges,
              (((fourEndpointSize alpha hAlpha e.1.1.1).descFactorial
                  (fourEndpointCellMultiplicityOfDeficit
                    alpha hAlpha P deficit e) : Nat) : ENNReal) *
                (((fourEndpointSize alpha hAlpha e.1.2.1).descFactorial
                  (fourEndpointCellMultiplicityOfDeficit
                    alpha hAlpha P deficit e) : Nat) : ENNReal)) *
            ∏ e : ↥P.1.edges,
              (localSignRewardNat
                (fourEndpointCellMultiplicityOfDeficit
                  alpha hAlpha P deficit e) : ENNReal) := by
            rw [Finset.prod_mul_distrib]
  unfold fourEndpointPartialAggregateWeight
    fourEndpointPartialAtomWeight
  rw [← mul_div_assoc, hnum]

private theorem fourEndpointDemandFullTotal_le_ambient
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (demand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha)) :
    fourEndpointPartialTotalMultiplicity alpha hAlpha
        (fourEndpointDemandBlockPairing
          alpha hAlpha k hcover slotIndex demand)
        (fun _ => 0) ≤
      Finset.univ.sum (profileBlockMargin k) := by
  classical
  let P := fourEndpointDemandBlockPairing
    alpha hAlpha k hcover slotIndex demand
  let f : ↥P.1.edges → ProfileBlockIndex k := fun e =>
    fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.1
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply P.1.leftUnique x.1 x.2 y.1 y.2
    exact fourEndpointActualBlockOfAtom_injective
      alpha hAlpha k slotIndex hxy
  have hcell (e : ↥P.1.edges) :
      fourEndpointCellFullMultiplicity alpha hAlpha P e ≤
        profileBlockMargin k (f e) := by
    rw [profileBlockMargin_fourEndpointActualBlockOfAtom]
    exact Nat.min_le_left _ _
  change
    (∑ e : ↥P.1.edges,
      fourEndpointCellFullMultiplicity alpha hAlpha P e - 0) ≤
      Finset.univ.sum (profileBlockMargin k)
  simp only [Nat.sub_zero]
  calc
    (∑ e : ↥P.1.edges,
        fourEndpointCellFullMultiplicity alpha hAlpha P e) ≤
        ∑ e : ↥P.1.edges, profileBlockMargin k (f e) := by
          exact Finset.sum_le_sum fun e _ => hcell e
    _ = ∑ a ∈ Finset.univ.image f, profileBlockMargin k a := by
      symm
      rw [Finset.sum_image]
      intro x _hx y _hy hxy
      exact hf hxy
    _ ≤ Finset.univ.sum (profileBlockMargin k) := by
      apply Finset.sum_le_sum_of_subset
      exact Finset.image_subset_iff.mpr fun _ _ => Finset.mem_univ _

private theorem prod_mul_pow_sum_eq_prod_mul_prod
    {E : Type*} [Fintype E]
    (n : Nat) (h : E → Nat) (A B C : E → ENNReal)
    (hlocal : ∀ e, A e * (n : ENNReal) ^ h e = B e * C e) :
    (∏ e, A e) * (n : ENNReal) ^ (∑ e, h e) =
      (∏ e, B e) * ∏ e, C e := by
  classical
  rw [← Finset.prod_pow_eq_pow_sum]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun e _ => hlocal e

private theorem fourEndpointDemandTotals_add_deficit
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (demand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha)) :
    fourEndpointPartialTotalMultiplicity alpha hAlpha
        (fourEndpointDemandBlockPairing
          alpha hAlpha k hcover slotIndex demand)
        (fourEndpointDemandDeficit
          alpha hAlpha k hcover slotIndex demand) +
      (∑ e : ↥(fourEndpointDemandBlockPairing
          alpha hAlpha k hcover slotIndex demand).1.edges,
        fourEndpointDemandDeficit
          alpha hAlpha k hcover slotIndex demand e) =
    fourEndpointPartialTotalMultiplicity alpha hAlpha
        (fourEndpointDemandBlockPairing
          alpha hAlpha k hcover slotIndex demand)
        (fun _ => 0) := by
  classical
  unfold fourEndpointPartialTotalMultiplicity
    fourEndpointCellMultiplicityOfDeficit
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _he
  have hhalf := fourEndpointDemandDeficit_twice_lt
    alpha hAlpha k hcover slotIndex demand e
  simp only [Nat.sub_zero]
  omega

private theorem aggregate_div_le_of_local_product
    (n J H M : Nat) (A B C : ENNReal)
    (hTotal : J + H = M) (hMn : M ≤ n)
    (hlocal : A * (n : ENNReal) ^ H = B * C) :
    A / ((n.descFactorial J : Nat) : ENNReal) ≤
      B / ((n.descFactorial M : Nat) : ENNReal) * C := by
  have hJn : J ≤ n := by omega
  have hdJNat : n.descFactorial J ≠ 0 :=
    (Nat.descFactorial_pos.mpr hJn).ne'
  have hdMNat : n.descFactorial M ≠ 0 :=
    (Nat.descFactorial_pos.mpr hMn).ne'
  have hdJ0 : ((n.descFactorial J : Nat) : ENNReal) ≠ 0 := by
    exact_mod_cast hdJNat
  have hdM0 : ((n.descFactorial M : Nat) : ENNReal) ≠ 0 := by
    exact_mod_cast hdMNat
  have hdJT : ((n.descFactorial J : Nat) : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hdMT : ((n.descFactorial M : Nat) : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hdescNat :
      n.descFactorial M =
        n.descFactorial J * (n - J).descFactorial H := by
    rw [← hTotal]
    simp only [Nat.descFactorial_eq_prod_range, Finset.prod_range_add]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [Nat.sub_sub]
  have hrestNat : (n - J).descFactorial H ≤ n ^ H := by
    exact (Nat.descFactorial_le_pow (n - J) H).trans
      (Nat.pow_le_pow_left (Nat.sub_le n J) H)
  have hdiv :
      A / ((n.descFactorial J : Nat) : ENNReal) ≤
        (A * (n : ENNReal) ^ H) /
          ((n.descFactorial M : Nat) : ENNReal) := by
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl hdM0) (Or.inl hdMT)).2
    rw [hdescNat]
    push_cast
    calc
      A / ((n.descFactorial J : Nat) : ENNReal) *
            (((n.descFactorial J : Nat) : ENNReal) *
              (((n - J).descFactorial H : Nat) : ENNReal)) =
          (((n.descFactorial J : Nat) : ENNReal) *
            (A / ((n.descFactorial J : Nat) : ENNReal))) *
              (((n - J).descFactorial H : Nat) : ENNReal) := by
                ac_rfl
      _ = A * (((n - J).descFactorial H : Nat) : ENNReal) := by
        rw [ENNReal.mul_div_cancel hdJ0 hdJT]
      _ ≤ A * (n : ENNReal) ^ H := by
        gcongr
        exact_mod_cast hrestNat
  calc
    A / ((n.descFactorial J : Nat) : ENNReal) ≤
        (A * (n : ENNReal) ^ H) /
          ((n.descFactorial M : Nat) : ENNReal) := hdiv
    _ = (B * C) / ((n.descFactorial M : Nat) : ENNReal) := by
      rw [hlocal]
    _ = B / ((n.descFactorial M : Nat) : ENNReal) * C := by
      simp only [div_eq_mul_inv]
      ac_rfl

private theorem fourEndpointPartialLocalFactor_edge_mul_pow_eq
    (n alpha : Nat) (hAlpha : 5 < alpha) (hHigh : 8 < alpha)
    {k : ColoringProfile (alpha + 1)} {L : FourEndpointFullTable}
    (P : FourEndpointBlockPairing alpha hAlpha k L)
    (deficit : ∀ _e : ↥P.1.edges, Nat)
    (e : ↥P.1.edges)
    (hhalf :
      2 * deficit e <
        fourEndpointCellFullMultiplicity alpha hAlpha P e) :
    fourEndpointPartialLocalFactor alpha hAlpha P deficit e *
        (n : ENNReal) ^ deficit e =
      fourEndpointPartialLocalFactor alpha hAlpha P (fun _ => 0) e *
        nearCellTerm n
          (fourEndpointCellFullMultiplicity alpha hAlpha P e)
          (Nat.dist e.1.1.1.val e.1.2.1.val)
          (deficit e) := by
  simpa [fourEndpointPartialLocalFactor,
    scratchRootFourEndpointPartialLocalFactor,
    fourEndpointCellMultiplicityOfDeficit,
    fourEndpointCellFullMultiplicity,
    fourEndpointLocalCellFactor, Nat.cast_mul] using
    scratch_rootFourEndpointPartialLocalFactor_edge_mul_pow_eq
      n alpha hAlpha hHigh P deficit e hhalf

/-- One attained high-skeleton weight is bounded by the zero-deficit full
reference on the same block support times the literal product of charged local
deficit factors. -/
theorem profileHighSkeletonWeight_le_fourEndpointFullReference_mul_deficitCharge
    (alpha : Nat) (hAlpha : 5 < alpha) (hHigh : 8 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (demand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha)) :
    profileHighSkeletonWeight k
        (fourEndpointLargestSize alpha hAlpha) demand ≤
      fourEndpointPartialAggregateWeight
          (Finset.univ.sum (profileBlockMargin k))
          alpha hAlpha
          (fourEndpointDemandBlockPairing
            alpha hAlpha k hcover slotIndex demand)
          (fun _ => 0) *
        ∏ e : ↥(fourEndpointDemandBlockPairing
            alpha hAlpha k hcover slotIndex demand).1.edges,
          nearCellTerm
            (Finset.univ.sum (profileBlockMargin k))
            (fourEndpointCellFullMultiplicity alpha hAlpha
              (fourEndpointDemandBlockPairing
                alpha hAlpha k hcover slotIndex demand) e)
            (Nat.dist e.1.1.1.val e.1.2.1.val)
            (fourEndpointDemandDeficit
              alpha hAlpha k hcover slotIndex demand e) := by
  classical
  let n := Finset.univ.sum (profileBlockMargin k)
  let P := fourEndpointDemandBlockPairing
    alpha hAlpha k hcover slotIndex demand
  let deficit := fourEndpointDemandDeficit
    alpha hAlpha k hcover slotIndex demand
  have hlocal (e : ↥P.1.edges) :
      fourEndpointPartialLocalFactor alpha hAlpha P deficit e *
          (n : ENNReal) ^ deficit e =
        fourEndpointPartialLocalFactor alpha hAlpha P (fun _ => 0) e *
          nearCellTerm n
            (fourEndpointCellFullMultiplicity alpha hAlpha P e)
            (Nat.dist e.1.1.1.val e.1.2.1.val)
            (deficit e) := by
    exact fourEndpointPartialLocalFactor_edge_mul_pow_eq
      n alpha hAlpha hHigh P deficit e
        (fourEndpointDemandDeficit_twice_lt
          alpha hAlpha k hcover slotIndex demand e)
  have hprod :
      (∏ e : ↥P.1.edges,
          fourEndpointPartialLocalFactor alpha hAlpha P deficit e) *
          (n : ENNReal) ^ (∑ e : ↥P.1.edges, deficit e) =
        (∏ e : ↥P.1.edges,
          fourEndpointPartialLocalFactor alpha hAlpha P (fun _ => 0) e) *
          ∏ e : ↥P.1.edges,
            nearCellTerm n
              (fourEndpointCellFullMultiplicity alpha hAlpha P e)
              (Nat.dist e.1.1.1.val e.1.2.1.val)
              (deficit e) :=
    prod_mul_pow_sum_eq_prod_mul_prod n deficit
      (fun e =>
        fourEndpointPartialLocalFactor alpha hAlpha P deficit e)
      (fun e =>
        fourEndpointPartialLocalFactor alpha hAlpha P (fun _ => 0) e)
      (fun e =>
        nearCellTerm n
          (fourEndpointCellFullMultiplicity alpha hAlpha P e)
          (Nat.dist e.1.1.1.val e.1.2.1.val)
          (deficit e))
      hlocal
  have htotal :
      fourEndpointPartialTotalMultiplicity alpha hAlpha P deficit +
          (∑ e : ↥P.1.edges, deficit e) =
        fourEndpointPartialTotalMultiplicity alpha hAlpha P
          (fun _ => 0) := by
    exact fourEndpointDemandTotals_add_deficit
      alpha hAlpha k hcover slotIndex demand
  have hfull :
      fourEndpointPartialTotalMultiplicity alpha hAlpha P
          (fun _ => 0) ≤ n := by
    exact fourEndpointDemandFullTotal_le_ambient
      alpha hAlpha k hcover slotIndex demand
  have hcompare := aggregate_div_le_of_local_product
    n
    (fourEndpointPartialTotalMultiplicity alpha hAlpha P deficit)
    (∑ e : ↥P.1.edges, deficit e)
    (fourEndpointPartialTotalMultiplicity alpha hAlpha P (fun _ => 0))
    (∏ e : ↥P.1.edges,
      fourEndpointPartialLocalFactor alpha hAlpha P deficit e)
    (∏ e : ↥P.1.edges,
      fourEndpointPartialLocalFactor alpha hAlpha P (fun _ => 0) e)
    (∏ e : ↥P.1.edges,
      nearCellTerm n
        (fourEndpointCellFullMultiplicity alpha hAlpha P e)
        (Nat.dist e.1.1.1.val e.1.2.1.val)
        (deficit e))
    htotal hfull hprod
  rw [profileHighSkeletonWeight_eq_fourEndpointPartialAggregateWeight
    alpha hAlpha k hcover slotIndex demand]
  rw [fourEndpointPartialAggregateWeight_eq_prod_local_div,
    fourEndpointPartialAggregateWeight_eq_prod_local_div]
  simpa [n, P, deficit] using hcompare

end

end Erdos625
