import Erdos625.GraphModel
import Mathlib.Tactic

/-!
# Section 10: simultaneous greedy colouring

This is the deterministic recursion behind the last paragraph of Lemma 10.1.
The independent-set hypothesis is uniform over all sufficiently large vertex
sets, so the conclusion retains the required internal `∀ U`.
-/

namespace Erdos625

noncomputable section

/-- Ceiling division, used below only with a positive denominator. -/
def ceilDivNat (a b : ℕ) : ℕ :=
  (a + b - 1) / b

/-- If every vertex set of cardinality at least `cutoff` contains an
independent set of at least `block` vertices, then every induced subgraph is
colourable by greedily deleting such sets and colouring the final fewer-than-
`cutoff` vertices singly. -/
theorem simultaneous_induced_chromatic_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (cutoff block : ℕ) (hblock : 1 ≤ block)
    (hIndependent : ∀ S : Finset V, cutoff ≤ S.card →
      ∃ I : Finset V,
        I ⊆ S ∧ block ≤ I.card ∧ G.IsIndepSet (I : Set V)) :
    ∀ U : Finset V,
      chromaticNumberNat (G.induce (U : Set V)) ≤
        ceilDivNat U.card block + cutoff := by
  intro U
  induction' U using Finset.strongInduction with U ih
  by_cases hU : U.card < cutoff
  · have h_chromatic_le_card :
        ∀ H : SimpleGraph (↑U), chromaticNumberNat H ≤ U.card := by
      intro H
      have h_colorable : H.Colorable U.card := by
        convert H.colorable_of_fintype
        rw [Fintype.card_coe]
      exact Nat.cast_le.mp
        (le_trans
          (ENat.toNat_le_toNat
            (SimpleGraph.chromaticNumber_le_iff_colorable.mpr h_colorable)
            (by simp +decide))
          (by simp +decide))
    exact le_trans (h_chromatic_le_card _) (by linarith)
  · obtain ⟨I, hI₁, hI₂, hI₃⟩ :=
      hIndependent U (le_of_not_gt hU)
    simp_all +decide [SimpleGraph.induce]
    have h_coloring :
        ∃ f : (↑U) →
            Fin (ceilDivNat (U.card - I.card) block + cutoff + 1),
          ∀ u v : ↑U, u ≠ v → G.Adj u v → f u ≠ f v := by
      have h_coloring :
          ∃ f : (↑(U \ I)) →
              Fin (ceilDivNat (U.card - I.card) block + cutoff),
            ∀ u v : ↑(U \ I), u ≠ v → G.Adj u v → f u ≠ f v := by
        have h_coloring :
            chromaticNumberNat
                (SimpleGraph.comap
                  (⇑(Function.Embedding.subtype
                    fun x => x ∈ (↑(U \ I) : Set V))) G) ≤
              ceilDivNat (U.card - I.card) block + cutoff := by
          have hI_nonempty : I.Nonempty := by
            exact Finset.card_pos.mp (by omega)
          have hdiff : U \ I ⊂ U :=
            Finset.sdiff_ssubset hI₁ hI_nonempty
          convert ih (U \ I) hdiff using 1
          · congr 1
          · rw [Finset.card_sdiff_of_subset hI₁]
        have h_coloring :
            SimpleGraph.Colorable
                (SimpleGraph.comap
                  (⇑(Function.Embedding.subtype
                    fun x => x ∈ (↑(U \ I) : Set V))) G)
              (ceilDivNat (U.card - I.card) block + cutoff) := by
          refine' SimpleGraph.chromaticNumber_le_iff_colorable.mp _ |>
            fun h => h.mono h_coloring
          rw [chromaticNumberNat, ENat.coe_toNat]
          exact ne_of_lt
            (lt_of_le_of_lt
              (SimpleGraph.colorable_of_fintype _ |>
                SimpleGraph.Colorable.chromaticNumber_le)
              (WithTop.coe_lt_top _))
        obtain ⟨f, hf⟩ := h_coloring
        exact ⟨f, fun u v huv huv' => by simpa [huv] using hf huv'⟩
      obtain ⟨f, hf⟩ := h_coloring
      use fun u =>
        if hu : u.val ∈ I then Fin.last _
        else Fin.castSucc (f ⟨u.val, by aesop⟩)
      simp_all +decide [Fin.ext_iff]
      intro a ha b hb hab h
      split_ifs <;> simp_all +decide
      · exact hI₃ ‹_› ‹_› hab h
      · exact ne_of_gt (Fin.is_lt _)
      · exact ne_of_lt (Fin.is_lt _)
    have h_coloring :
        SimpleGraph.Colorable
            (SimpleGraph.comap
              (⇑(Function.Embedding.subtype fun x => x ∈ (↑U : Set V))) G)
          (ceilDivNat (U.card - I.card) block + cutoff + 1) := by
      obtain ⟨f, hf⟩ := h_coloring
      use fun u => f u
      aesop
    have h_coloring :
        chromaticNumberNat
            (SimpleGraph.comap
              (⇑(Function.Embedding.subtype fun x => x ∈ (↑U : Set V))) G) ≤
          ceilDivNat (U.card - I.card) block + cutoff + 1 := by
      convert h_coloring.chromaticNumber_le using 1
      rw [← ENat.coe_le_coe, chromaticNumberNat, ENat.coe_toNat]
      exact ne_of_lt
        (lt_of_le_of_lt
          (SimpleGraph.chromaticNumber_le_iff_colorable.mpr h_coloring)
          (WithTop.coe_lt_top _))
    refine' le_trans _ (h_coloring.trans _)
    · exact le_rfl
    · unfold ceilDivNat
      simp +arith +decide
      rw [Nat.div_lt_iff_lt_mul <| by positivity]
      rw [tsub_lt_iff_left]
      · linarith
          [Nat.div_add_mod (block + U.card - 1) block,
            Nat.mod_lt (block + U.card - 1) hblock,
            Nat.sub_add_cancel
              (show 1 ≤ block + U.card by linarith),
            Nat.sub_add_cancel
              (show I.card ≤ U.card from Finset.card_le_card hI₁)]
      · exact le_add_right hblock

#print axioms simultaneous_induced_chromatic_bound

end

end Erdos625
