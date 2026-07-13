import Erdos625.ColoringProfileFirstMoment
import Mathlib.Data.Fintype.BigOperators

/-!
# Finite aggregation of bounded coloring profiles

The exact first-moment calculation in `ColoringProfileFirstMoment` concerns
one profile at a time.  This module supplies the finite aggregation layer
needed before the analytic estimate in manuscript Section 4.

A coordinate box makes the otherwise infinite type `Fin b → ℕ` finite.
Filtering that box by the mass and part-count equations loses no admissible
profile, because every coordinate of a mass-`n` profile is at most `n`.
The final theorem interchanges the two finite sums and identifies the
aggregate expectation with the sum of the already established per-profile
expectations.  No set-partition enumeration formula or asymptotic estimate is
used here.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-! ## A finite coordinate box -/

/-- All bounded profiles whose coordinates lie in `{0, …, n}`. -/
def coloringProfileBox (n b : ℕ) : Finset (ColoringProfile b) := by
  classical
  exact Fintype.piFinset fun _ : Fin b ↦ Finset.range (n + 1)

@[simp] theorem mem_coloringProfileBox {n b : ℕ}
    (k : ColoringProfile b) :
    k ∈ coloringProfileBox n b ↔ ∀ i, k i ≤ n := by
  classical
  simp [coloringProfileBox]

/-- Each coordinate is at most the total vertex mass, since its class size is
positive. -/
theorem ColoringProfile.coordinate_le_vertexMass {b : ℕ}
    (k : ColoringProfile b) (i : Fin b) :
    k i ≤ ColoringProfile.vertexMass k := by
  rw [ColoringProfile.vertexMass_eq_sum]
  have hTerm : k i ≤ (i.1 + 1) * k i := by
    rw [Nat.add_mul, one_mul]
    exact Nat.le_add_left _ _
  exact hTerm.trans
    (Finset.single_le_sum (fun j _ ↦ Nat.zero_le ((j.1 + 1) * k j))
      (Finset.mem_univ i))

/-- Every profile of mass `n` belongs to the coordinate box of side `n+1`. -/
theorem mem_coloringProfileBox_of_vertexMass_eq {n b : ℕ}
    {k : ColoringProfile b}
    (hmass : ColoringProfile.vertexMass k = n) :
    k ∈ coloringProfileBox n b := by
  rw [mem_coloringProfileBox]
  intro i
  rw [← hmass]
  exact k.coordinate_le_vertexMass i

/-- The coordinate box has exactly `(n+1)^b` elements. -/
theorem card_coloringProfileBox (n b : ℕ) :
    (coloringProfileBox n b).card = (n + 1) ^ b := by
  classical
  simp [coloringProfileBox]

/-! ## Mass-`n`, exactly-`k` profiles -/

/-- Profiles on class sizes `1, …, b` that cover exactly `n` vertices with
exactly `parts` nonempty classes. -/
def boundedColoringProfiles (n b parts : ℕ) :
    Finset (ColoringProfile b) := by
  classical
  exact (coloringProfileBox n b).filter fun k ↦
    ColoringProfile.vertexMass k = n ∧
      ColoringProfile.partCount k = parts

/-- Membership has exactly the two manuscript constraints; the coordinate-box
condition is automatic from the mass equation. -/
@[simp] theorem mem_boundedColoringProfiles {n b parts : ℕ}
    (k : ColoringProfile b) :
    k ∈ boundedColoringProfiles n b parts ↔
      ColoringProfile.vertexMass k = n ∧
        ColoringProfile.partCount k = parts := by
  classical
  rw [boundedColoringProfiles, Finset.mem_filter]
  constructor
  · exact fun h ↦ h.2
  · intro h
    exact ⟨mem_coloringProfileBox_of_vertexMass_eq h.1, h⟩

/-- Explicit coverage form: every profile satisfying the mass and part-count
constraints occurs in the filtered finite family. -/
theorem mem_boundedColoringProfiles_of_constraints {n b parts : ℕ}
    {k : ColoringProfile b}
    (hmass : ColoringProfile.vertexMass k = n)
    (hparts : ColoringProfile.partCount k = parts) :
    k ∈ boundedColoringProfiles n b parts :=
  (mem_boundedColoringProfiles k).2 ⟨hmass, hparts⟩

/-- There are at most `(n+1)^b` mass-`n`, exactly-`parts` bounded profiles. -/
theorem card_boundedColoringProfiles_le (n b parts : ℕ) :
    (boundedColoringProfiles n b parts).card ≤ (n + 1) ^ b := by
  classical
  calc
    (boundedColoringProfiles n b parts).card ≤
        (coloringProfileBox n b).card := by
      exact Finset.card_filter_le _ _
    _ = (n + 1) ^ b := card_coloringProfileBox n b

/-! ## Aggregate count and expectation -/

/-- Number of proper unordered colorings whose profile has class sizes at
most `b`, covers all `n` vertices, and has exactly `parts` nonempty classes. -/
def boundedProfileColoringCount {n : ℕ} (G : LabeledGraph n)
    (b parts : ℕ) : ℕ :=
  ∑ k ∈ boundedColoringProfiles n b parts, profileColoringCount G k

/-- Finite weighted-sum expectation of the aggregate bounded-profile coloring
count under `G(n,1/2)`. -/
def boundedProfileColoringExpectation (n b parts : ℕ) : ENNReal :=
  ∑ G : LabeledGraph n,
    (boundedProfileColoringCount G b parts : ENNReal) *
      randomGraphMeasure n {G}

/-- The aggregate expectation is exactly the sum of the per-profile
expectations.  This is only an interchange of two finite sums and is
independent of the separately proved decorated-partition enumeration
bijection. -/
theorem boundedProfileColoringExpectation_eq_sum (n b parts : ℕ) :
    boundedProfileColoringExpectation n b parts =
      ∑ k ∈ boundedColoringProfiles n b parts,
        profileColoringExpectation n k := by
  classical
  unfold boundedProfileColoringExpectation boundedProfileColoringCount
    profileColoringExpectation
  simp_rw [Nat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

end

end Erdos625
