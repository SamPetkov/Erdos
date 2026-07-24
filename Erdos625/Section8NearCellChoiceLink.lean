import Erdos625.Section8NearSkeletonExpansion
import Mathlib.Tactic

/-!
# Section VIII: a literal one-cell near-skeleton specialization

The manuscript's local factor in (8.21) is embedded here in the repository's
actual `NearSkeletonChoice` / `nearSkeletonChoiceWeight` language.  A single
distinguishable endpoint cell has an optional deficit in the finite interval
`{1, ..., cut}`.  The first conjunct is the exact one-cell version of the
local product in (8.25a); the second is its division-free consecutive ratio.

This is deliberately only a local bridge.  It does not identify physical
unlabelled skeletons, prove the phase-uniform tail estimate (8.25), or sum
over endpoint tables.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- The bare local near-deficit factor from manuscript (8.21), after the
global denominator loss `n^e` has been charged. -/
def nearCellTerm (n m d e : Nat) : ENNReal :=
  ((n : ENNReal) ^ e * (Nat.choose m e : ENNReal) /
    ((∏ t ∈ Finset.Icc 1 e, (d + t) : Nat) : ENNReal)) *
      ((2 : ENNReal) ^ (e * m - e * (e + 1) / 2))⁻¹

/-- The literal finite deficit choices for one endpoint cell.  The ambient
finite type is `Fin (m+1)`; the filter records exactly the chosen near window.
-/
def nearCellAllowed (m cut : Nat) : Fin 1 → Finset (Fin (m + 1)) :=
  fun _ => Finset.univ.filter (fun e => e.1 ∈ Finset.Icc 1 cut)

/-- The Section VIII local weight, represented in the existing generic
near-skeleton expansion. -/
def nearCellWeight (n m d _cut : Nat) :
    Fin 1 → Fin (m + 1) → ENNReal :=
  fun _ e => nearCellTerm n m d e.1

/-- The single-cell choice which selects a specified deficit when it is in
the explicit near window, and otherwise selects no deficit. -/
def nearCellSelectedChoice (m cut : Nat) (e : Fin (m + 1)) :
    NearSkeletonChoice (Fin 1) (Fin (m + 1)) (nearCellAllowed m cut) :=
  fun _ => if h : e.1 ∈ Finset.Icc 1 cut then
    some ⟨e, by simpa [nearCellAllowed] using h⟩ else none

/-- Increment a deficit while retaining the original ambient finite type. -/
def nearCellSucc (m : Nat) (e : Fin (m + 1)) (he : e.1 < m) : Fin (m + 1) :=
  ⟨e.1 + 1, by omega⟩

private lemma nearCellChoiceExpansion_aux (n m d cut : Nat) :
    (∑ choice : NearSkeletonChoice (Fin 1) (Fin (m + 1))
        (nearCellAllowed m cut),
      nearSkeletonChoiceWeight (nearCellAllowed m cut)
        (nearCellWeight n m d cut) choice) =
      1 + ∑ q ∈ nearCellAllowed m cut 0, nearCellTerm n m d q.1 := by
  rw [ sum_nearSkeletonChoiceWeight_eq_product ];
  simp +decide [ nearCellWeight ]

private lemma nearCellExponent_succ (m k : Nat) (hk : k + 1 ≤ m) :
    (k + 1) * m - (k + 1) * (k + 1 + 1) / 2 =
      k * m - k * (k + 1) / 2 + (m - (k + 1)) := by
  rw [ tsub_eq_of_eq_add ];
  zify [ hk ];
  rw [ Nat.cast_sub ] <;> push_cast <;> repeat nlinarith [ Nat.div_mul_le_self ( k * ( k + 1 ) ) 2 ] ;
  grind

private lemma nearCellDenominator_succ (d k : Nat) :
    ∏ t ∈ Finset.Icc 1 (k + 1), (d + t) =
      (∏ t ∈ Finset.Icc 1 k, (d + t)) * (d + k + 1) := by
  have hset (a : Nat) : Finset.Icc 1 a = Finset.Ioc 0 a := by
    ext x
    simp
    omega
  rw [hset, hset, Finset.prod_Ioc_succ_top (Nat.zero_le k)]
  rw [add_assoc]

private lemma nearCellTerm_succ_cross_mul
    (n m d k : Nat) (hksucc : k + 1 ≤ m) :
    nearCellTerm n m d (k + 1) *
        (((k + 1) * (d + k + 1) : Nat) : ENNReal) * (2 : ENNReal) ^ m =
      nearCellTerm n m d k * ((n * (m - k) : Nat) : ENNReal) *
        (2 : ENNReal) ^ (k + 1) := by
  have h_choose : (Nat.choose m (k + 1) : ENNReal) * (k + 1) = (Nat.choose m k : ENNReal) * (m - k) := by
    norm_cast;
    rw [ Nat.choose_succ_right_eq, mul_comm ];
  unfold nearCellTerm
  rw [nearCellDenominator_succ d k]
  rw [nearCellExponent_succ m k hksucc]
  rw [ show ( 2 : ENNReal ) ^ m = ( 2 : ENNReal ) ^ ( k + 1 ) * ( 2 : ENNReal ) ^ ( m - ( k + 1 ) ) by rw [ ← pow_add, Nat.add_sub_of_le hksucc ] ];
  simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, pow_add ];
  simp_all +decide [ ← mul_assoc, ← h_choose ];
  simp +decide [ mul_assoc, mul_comm, mul_left_comm, ENNReal.mul_inv ];
  simp +decide [← mul_assoc, ENNReal.mul_inv_cancel]

private lemma nearCellSelectedChoiceWeight_eq
    (n m d cut : Nat) (q : Fin (m + 1))
    (hq : q.1 ∈ Finset.Icc 1 cut) :
    nearSkeletonChoiceWeight (nearCellAllowed m cut)
        (nearCellWeight n m d cut) (nearCellSelectedChoice m cut q) =
      nearCellTerm n m d q.1 := by
  unfold nearSkeletonChoiceWeight nearCellWeight nearCellSelectedChoice nearCellAllowed;
  aesop

private lemma nearCellChoiceSuccCrossMul_aux
    (n m d cut : Nat) (e : Fin (m + 1))
    (hcut : cut ≤ m) (hpos : 0 < e.1) (hsucc : e.1 + 1 ≤ cut) :
    nearSkeletonChoiceWeight (nearCellAllowed m cut)
        (nearCellWeight n m d cut)
        (nearCellSelectedChoice m cut (nearCellSucc m e (by omega))) *
      (((e.1 + 1) * (d + e.1 + 1) : Nat) : ENNReal) *
        (2 : ENNReal) ^ m =
      nearSkeletonChoiceWeight (nearCellAllowed m cut)
        (nearCellWeight n m d cut) (nearCellSelectedChoice m cut e) *
      ((n * (m - e.1) : Nat) : ENNReal) *
        (2 : ENNReal) ^ (e.1 + 1) := by
  rw [ nearCellSelectedChoiceWeight_eq, nearCellSelectedChoiceWeight_eq ];
  · simpa [nearCellSucc] using
      nearCellTerm_succ_cross_mul n m d e.val (by omega)
  · grind
  · unfold nearCellSucc
    aesop

/-- The exact Section VIII local bridge: the finite one-cell
`nearSkeletonChoiceWeight` expansion is the manuscript's `1 + sum_e` factor,
and the selected consecutive terms satisfy the division-free form of (8.23).

`hcut` merely ensures that the displayed finite choice window fits inside the
endpoint size.  The hypotheses `hpos` and `hsucc` ensure that both selected
deficits `e` and `e+1` genuinely belong to that window. -/
theorem nearCellChoiceExpansion_and_succ_cross_mul
    (n m d cut : Nat) (e : Fin (m + 1))
    (hcut : cut ≤ m) (hpos : 0 < e.1) (hsucc : e.1 + 1 ≤ cut) :
    (∑ choice : NearSkeletonChoice (Fin 1) (Fin (m + 1))
        (nearCellAllowed m cut),
      nearSkeletonChoiceWeight (nearCellAllowed m cut)
        (nearCellWeight n m d cut) choice) =
      1 + ∑ q ∈ nearCellAllowed m cut 0, nearCellTerm n m d q.1
    ∧
    nearSkeletonChoiceWeight (nearCellAllowed m cut)
        (nearCellWeight n m d cut)
        (nearCellSelectedChoice m cut (nearCellSucc m e (by omega))) *
      (((e.1 + 1) * (d + e.1 + 1) : Nat) : ENNReal) *
        (2 : ENNReal) ^ m =
      nearSkeletonChoiceWeight (nearCellAllowed m cut)
        (nearCellWeight n m d cut) (nearCellSelectedChoice m cut e) *
      ((n * (m - e.1) : Nat) : ENNReal) *
        (2 : ENNReal) ^ (e.1 + 1) := by
  exact ⟨nearCellChoiceExpansion_aux n m d cut,
    nearCellChoiceSuccCrossMul_aux n m d cut e hcut hpos hsucc⟩

#print axioms nearCellChoiceExpansion_and_succ_cross_mul

end

end Erdos625
