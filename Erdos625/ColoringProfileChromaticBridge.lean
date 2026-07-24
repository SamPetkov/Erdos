import Erdos625.ColoringPartitionBridge
import Erdos625.ColoringProfileExtraction

/-!
# From a chromatic bound to a positive bounded-profile count

This module joins the deterministic coloring-to-partition construction with
bounded-profile extraction.  If `G` is colorable with at most `k` colors,
`k ≤ n`, and every independent set has size at most `b`, then an exact
`k`-part proper partition extracted from a coloring witnesses positivity of
the bounded profile count.

No positivity assumption is imposed on `n`, `k`, or `b`.  In particular, the
proof includes the empty graph with `n = k = b = 0`.
-/

namespace Erdos625

noncomputable section

/-- A chromatic upper bound and an independence-number upper bound produce a
positive bounded-profile coloring count with exactly `k` nonempty parts. -/
theorem boundedProfileColoringCount_pos_of_chromaticNumberNat_le
    {n k b : ℕ} (G : LabeledGraph n)
    (hchi : chromaticNumberNat G ≤ k)
    (hkn : k ≤ n)
    (hindep : G.indepNum ≤ b) :
    0 < boundedProfileColoringCount G b k := by
  obtain ⟨P, hParts, hProper⟩ :=
    exists_exact_proper_partition_of_chromaticNumberNat_le G hchi hkn
  apply boundedProfileColoringCount_pos_of_partition G b k P
    hProper hParts
  intro B hB
  have hBIndep : G.IsIndepSet (B : Set (Fin n)) := hProper B hB
  exact hBIndep.card_le_indepNum.trans hindep

/-- Pointwise deterministic event containment: a graph satisfying the
chromatic bound either has a positive bounded-profile count, or its
independence number exceeds the permitted block size. -/
theorem chromaticNumberNat_le_set_subset_boundedProfileColoringCount_pos_union
    {n k b : ℕ} (hkn : k ≤ n) :
    {G : LabeledGraph n | chromaticNumberNat G ≤ k} ⊆
      {G : LabeledGraph n | 0 < boundedProfileColoringCount G b k} ∪
        independenceNumberExceedsEvent n b := by
  intro G hchi
  by_cases hindep : G.indepNum ≤ b
  · exact Or.inl
      (boundedProfileColoringCount_pos_of_chromaticNumberNat_le
        G hchi hkn hindep)
  · apply Or.inr
    change b < G.indepNum
    omega

end

end Erdos625
