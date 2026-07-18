import Erdos625.Section9FixedFFubiniBridge

/-!
# Section IX: zero-residual actual attachment

When the total row-stub mass is zero there are no realised residual pairs.
With an empty exposed skeleton, the literal even-edge family therefore consists
only of the empty edge set, and the exact Section IX numerator is one.

The empty-skeleton hypothesis is essential: in the present definition,
`actualResidualEvenEdgeSets` retains every even subset of the exposed skeleton
`M`, even if no residual pair is present.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- In the zero-total branch, and with no exposed skeleton edges, the literal
Section IX actual attachment numerator is exactly one. -/
theorem residualActualAttachmentNumerator_empty_eq_one_of_total_zero
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (R : ℕ) (row : A → ℕ) (col : B → ℕ)
    (htotal : Finset.univ.sum row = Finset.univ.sum col)
    (hrowTotal : Finset.univ.sum row = 0) :
    residualActualAttachmentNumerator (∅ : Finset (A × B)) R row col htotal = 1 := by
  classical
  have hrowzero : ∀ a : A, row a = 0 := by
    intro a
    exact (Finset.sum_eq_zero_iff.mp hrowTotal) a (Finset.mem_univ a)
  have hcellzero : ∀ (matching : ConfigurationMatching row col) (a : A) (b : B),
      configurationCellCount matching a b = 0 := by
    intro matching a b
    have hsum : (∑ b', configurationCellCount matching a b') = 0 := by
      rw [sum_configurationCellCount_row, hrowzero a]
    exact (Finset.sum_eq_zero_iff.mp hsum) b (Finset.mem_univ b)
  have hevent : ∀ matching : ConfigurationMatching row col,
      matching ∈ ResidualCapNoReturnEvent (∅ : Finset (A × B)) R row col := by
    intro matching
    constructor
    · intro a b
      simp [hcellzero matching a b]
    · simp
  have hfamily : ∀ matching : ConfigurationMatching row col,
      actualResidualEvenEdgeSets (∅ : Finset (A × B)) matching = {∅} := by
    intro matching
    ext F
    constructor
    · intro hF
      simp only [actualResidualEvenEdgeSets, Finset.mem_filter,
        bipartiteEvenEdgeSets, Finset.mem_univ, true_and] at hF
      have hFempty : F = ∅ := by
        by_contra hne
        obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        have hcondition := hF.2 e he
        simp [hcellzero matching e.1 e.2] at hcondition
      simp [hFempty]
    · intro hF
      have hFempty : F = ∅ := by
        simpa only [Finset.mem_singleton] using hF
      subst F
      simp only [actualResidualEvenEdgeSets, Finset.mem_filter]
      constructor
      · simp only [bipartiteEvenEdgeSets, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor <;> intro x <;> simp
      · simp
  unfold residualActualAttachmentNumerator
  simp_rw [hevent, if_pos, hfamily, hcellzero]
  simp [residualReward]
  simpa only [tsum_fintype] using
    (uniformConfigurationMatching row col htotal).tsum_coe

#print axioms residualActualAttachmentNumerator_empty_eq_one_of_total_zero

end

end Erdos625
