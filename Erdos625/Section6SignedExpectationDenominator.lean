import Erdos625.ProfileOverlapCanonicalTable
import Erdos625.SignedProfileWitness
import Mathlib.Tactic

/-!
# Section VI signed first-moment denominator

The normalized signed second-moment identity divides by the square of the
signed first moment.  This file records the exact feasibility facts which make
that division legitimate.  In particular, an ordered profile partition gives
an unordered profile partition through the already proved finite quotient
equivalence, so the signed first moment is strictly positive.  Finiteness is
proved directly from the exact finite first-moment formula.

The profile-block index can be empty in the genuine degenerate case `n = 0`
with no profile parts.  Its nonemptiness is therefore stated with the sharp
additional hypothesis `0 < n` (or, equivalently here, positive part count).
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- Feasibility of the ordered, block-labelled profile model supplies an
unordered profile partition of the same profile. -/
theorem profilePartition_nonempty_of_orderedProfilePartition
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) :
    Nonempty (ProfilePartition n k) := by
  let labelled : LabeledProfilePartition n k :=
    (labeledProfilePartitionEquivOrdered k).symm row₀
  exact ⟨labelled.1⟩

/-- The finite type of unordered profile partitions has positive cardinality
whenever an ordered profile partition is available. -/
theorem card_profilePartition_pos_of_orderedProfilePartition
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) :
    0 < Fintype.card (ProfilePartition n k) :=
  Fintype.card_pos_iff.mpr
    (profilePartition_nonempty_of_orderedProfilePartition row₀)

/-- Cardinality positivity in the `Nat.card` spelling used by the exact
first-moment formula. -/
theorem natCard_profilePartition_pos_of_orderedProfilePartition
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) :
    0 < Nat.card (ProfilePartition n k) := by
  rw [Nat.card_eq_fintype_card]
  exact card_profilePartition_pos_of_orderedProfilePartition row₀

/-- A positive profile part count makes the canonical block-slot type
nonempty. -/
theorem profileBlockIndex_nonempty_of_partCount_pos
    {b : ℕ} (k : ColoringProfile b)
    (hparts : 0 < ColoringProfile.partCount k) :
    Nonempty (ProfileBlockIndex k) := by
  apply Fintype.card_pos_iff.mp
  rw [card_profileBlockIndex]
  exact hparts

/-- The canonical block-slot type has positive finite cardinality exactly
when the profile has a positive number of parts. -/
theorem card_profileBlockIndex_pos_iff
    {b : ℕ} (k : ColoringProfile b) :
    0 < Fintype.card (ProfileBlockIndex k) ↔
      0 < ColoringProfile.partCount k := by
  rw [card_profileBlockIndex]

/-- A feasible ordered profile on a nonempty vertex set has at least one
profile part. -/
theorem partCount_pos_of_orderedProfilePartition_of_pos
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (hn : 0 < n) :
    0 < ColoringProfile.partCount k := by
  obtain ⟨P⟩ := profilePartition_nonempty_of_orderedProfilePartition row₀
  rw [← P.card_parts_eq]
  apply Finset.card_pos.mpr
  let v : Fin n := ⟨0, hn⟩
  exact ⟨P.1.part v, P.1.part_mem.mpr (Finset.mem_univ v)⟩

/-- On a nonempty vertex set, an ordered profile partition supplies a
nonempty canonical block-slot type. -/
theorem profileBlockIndex_nonempty_of_orderedProfilePartition_of_pos
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (hn : 0 < n) :
    Nonempty (ProfileBlockIndex k) :=
  profileBlockIndex_nonempty_of_partCount_pos k
    (partCount_pos_of_orderedProfilePartition_of_pos row₀ hn)

/-- On a nonempty vertex set, the canonical block-slot type has positive
finite cardinality. -/
theorem card_profileBlockIndex_pos_of_orderedProfilePartition_of_pos
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (hn : 0 < n) :
    0 < Fintype.card (ProfileBlockIndex k) :=
  Fintype.card_pos_iff.mpr
    (profileBlockIndex_nonempty_of_orderedProfilePartition_of_pos row₀ hn)

/-- This is the sharp unconditional form: a feasible ordered profile has a
nonempty block-slot type unless the ambient vertex set itself is empty. -/
theorem profileBlockIndex_nonempty_or_vertex_eq_zero_of_orderedProfilePartition
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) :
    Nonempty (ProfileBlockIndex k) ∨ n = 0 := by
  by_cases hn : n = 0
  · exact Or.inr hn
  · exact Or.inl
      (profileBlockIndex_nonempty_of_orderedProfilePartition_of_pos row₀
        (Nat.pos_of_ne_zero hn))

/-- The signed finite first moment is never infinite; this is independent
of feasibility because it is a finite sum over the finite graph space. -/
theorem signedProfileExpectation_ne_top
    {b : ℕ} (n : ℕ) (k : ColoringProfile b) :
    signedProfileExpectation n k ≠ ∞ := by
  rw [signedProfileExpectation_eq, profileColoringExpectation_eq_card_mul]
  apply ENNReal.mul_ne_top
  · exact ENNReal.pow_ne_top (by norm_num)
  · apply ENNReal.mul_ne_top
    · exact ENNReal.natCast_ne_top _
    · exact ENNReal.pow_ne_top (by norm_num)

/-- Feasibility of an ordered profile partition makes the signed first
moment strictly positive. -/
theorem signedProfileExpectation_pos_of_orderedProfilePartition
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) :
    0 < signedProfileExpectation n k := by
  have hcard : Nat.card (ProfilePartition n k) ≠ 0 :=
    (natCard_profilePartition_pos_of_orderedProfilePartition row₀).ne'
  rw [signedProfileExpectation_eq, profileColoringExpectation_eq_card_mul]
  apply ENNReal.mul_pos
  · exact ENNReal.pow_ne_zero (by norm_num) _
  · exact mul_ne_zero (Nat.cast_ne_zero.mpr hcard)
      (ENNReal.pow_ne_zero (by norm_num) _)

/-- The nonzero form of first-moment positivity, suitable for ENNReal
division lemmas. -/
theorem signedProfileExpectation_ne_zero_of_orderedProfilePartition
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) :
    signedProfileExpectation n k ≠ 0 :=
  (signedProfileExpectation_pos_of_orderedProfilePartition row₀).ne'

/-- The square of the signed first moment is nonzero under the same
feasibility hypothesis. -/
theorem signedProfileExpectation_sq_ne_zero_of_orderedProfilePartition
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) :
    signedProfileExpectation n k ^ 2 ≠ 0 :=
  ENNReal.pow_ne_zero
    (signedProfileExpectation_ne_zero_of_orderedProfilePartition row₀) 2

/-- The square of the signed first moment is finite. -/
theorem signedProfileExpectation_sq_ne_top
    {b : ℕ} (n : ℕ) (k : ColoringProfile b) :
    signedProfileExpectation n k ^ 2 ≠ ∞ :=
  ENNReal.pow_ne_top (signedProfileExpectation_ne_top n k)

/-- Safe self-cancellation of the signed first-moment square. -/
theorem signedProfileExpectation_sq_div_self_of_orderedProfilePartition
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) :
    signedProfileExpectation n k ^ 2 /
        signedProfileExpectation n k ^ 2 = 1 :=
  ENNReal.div_self
    (signedProfileExpectation_sq_ne_zero_of_orderedProfilePartition row₀)
    (signedProfileExpectation_sq_ne_top n k)

/-- Right cancellation after division by the signed first-moment square. -/
theorem div_signedProfileExpectation_sq_mul_of_orderedProfilePartition
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (x : ENNReal) :
    (x / signedProfileExpectation n k ^ 2) *
        signedProfileExpectation n k ^ 2 = x :=
  ENNReal.div_mul_cancel
    (signedProfileExpectation_sq_ne_zero_of_orderedProfilePartition row₀)
    (signedProfileExpectation_sq_ne_top n k)

/-- An ENNReal equality can be divided safely by the signed first-moment
square exactly when its denominator-free form has that square as a factor. -/
theorem div_signedProfileExpectation_sq_eq_iff_of_orderedProfilePartition
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (x y : ENNReal) :
    x / signedProfileExpectation n k ^ 2 = y ↔
      x = signedProfileExpectation n k ^ 2 * y := by
  let d : ENNReal := signedProfileExpectation n k ^ 2
  have hd0 : d ≠ 0 := by
    simpa only [d] using
      signedProfileExpectation_sq_ne_zero_of_orderedProfilePartition row₀
  have hdtop : d ≠ ∞ := by
    simpa only [d] using signedProfileExpectation_sq_ne_top n k
  constructor
  · intro h
    calc
      x = (x / d) * d := (ENNReal.div_mul_cancel hd0 hdtop).symm
      _ = y * d := by rw [h]
      _ = d * y := by ac_rfl
  · intro h
    change x / d = y
    rw [h, ENNReal.div_eq_inv_mul]
    calc
      d⁻¹ * (d * y) = (d⁻¹ * d) * y := by ac_rfl
      _ = y := by rw [ENNReal.inv_mul_cancel hd0 hdtop, one_mul]

/-- The forward direction most often used after a denominator-free
second-moment calculation. -/
theorem normalized_eq_of_eq_signedProfileExpectation_sq_mul
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) {secondMoment normalized : ENNReal}
    (h : secondMoment = signedProfileExpectation n k ^ 2 * normalized) :
    secondMoment / signedProfileExpectation n k ^ 2 = normalized :=
  (div_signedProfileExpectation_sq_eq_iff_of_orderedProfilePartition
    row₀ secondMoment normalized).mpr h

/-- The same normalization step when the denominator-free expression happens
to present the square factor on the right. -/
theorem normalized_eq_of_eq_mul_signedProfileExpectation_sq
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) {secondMoment normalized : ENNReal}
    (h : secondMoment = normalized * signedProfileExpectation n k ^ 2) :
    secondMoment / signedProfileExpectation n k ^ 2 = normalized :=
  normalized_eq_of_eq_signedProfileExpectation_sq_mul row₀
    (by simpa [mul_comm] using h)

/-- Conversely, a normalized equality may be multiplied back by the signed
first-moment square without losing information. -/
theorem eq_signedProfileExpectation_sq_mul_of_normalized_eq
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) {secondMoment normalized : ENNReal}
    (h : secondMoment / signedProfileExpectation n k ^ 2 = normalized) :
    secondMoment = signedProfileExpectation n k ^ 2 * normalized :=
  (div_signedProfileExpectation_sq_eq_iff_of_orderedProfilePartition
    row₀ secondMoment normalized).mp h

#print axioms profilePartition_nonempty_of_orderedProfilePartition
#print axioms signedProfileExpectation_ne_top
#print axioms signedProfileExpectation_pos_of_orderedProfilePartition
#print axioms div_signedProfileExpectation_sq_eq_iff_of_orderedProfilePartition

end

end Erdos625
