import Erdos625.InducedCochromaticCapacity

/-!
# Section 8 (`cor:zeta-upper`): direct vertex-exposure amplification for `ζ` and `χ`

In the Heckel–Panagiotou route, amplification acts directly on the cochromatic
number `ζ(G)` and the chromatic number `χ(G)` rather than through an induced
capacity and greedy leftover colouring:
* changing the exposure block of one vertex changes `ζ(G)` by at most `1`, and
  changes `χ(G)` by at most `1`;
* the empty initial block `i = 0` contributes `0`, so both `ζ` and `χ` (and
  their negations) satisfy `HasBlockOscillation` with profile
  `noninitialUnitOscillation` and variance proxy `(n - 1) / 4`;
* if `P(F(G) ≤ k) > exp (-2 t² / (n - 1))` for `n ≥ 2` and `t > 0`, the lower
  tail forces `E[F(G)] ≤ k + t`, and the upper tail then gives
  `P(F(G) > k + 2 t) ≤ exp (-2 t² / (n - 1))`.
-/

namespace Erdos625HP

open Erdos625 MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

set_option autoImplicit false

/-- Negating a real-valued function preserves any block-oscillation bound. -/
theorem HasBlockOscillation.neg {n : ℕ} {Omega : Fin n → Type*}
    {f : (∀ i, Omega i) → ℝ} {c : Fin n → ℝ≥0}
    (hf : HasBlockOscillation f c) :
    HasBlockOscillation (fun x ↦ -f x) c := by
  intro i x y hxy
  rw [show -f x - -f y = -(f x - f y) by ring, abs_neg]
  exact hf i x y hxy

/-- An induced subgraph on at most one vertex (`{v | v ≠ i}ᶜ`) is properly
`1`-colourable. -/
theorem colorable_one_induce_compl_ne {n : ℕ} (G : LabeledGraph n) (i : Fin n) :
    (G.induce {v : Fin n | v ≠ i}ᶜ).Colorable 1 := by
  refine ⟨SimpleGraph.Coloring.mk (fun _ ↦ (0 : Fin 1)) ?_⟩
  intro x y hxy
  exfalso
  have hx : x.val = i := by
    by_contra hne
    exact x.property hne
  have hy : y.val = i := by
    by_contra hne
    exact y.property hne
  have hxy_eq : x = y := Subtype.ext (hx.trans hy.symm)
  exact ((G.induce {v : Fin n | v ≠ i}ᶜ).ne_of_adj hxy) hxy_eq

/-- Deleting one vertex and restoring it as a singleton class shows that
changing the edges at vertex `i` changes `ζ(G)` by at most `1`. -/
theorem cochromaticNumber_le_add_one_of_induce_away_eq {n : ℕ}
    {G H : LabeledGraph n} {i : Fin n}
    (hGH : G.induce {v | v ≠ i} = H.induce {v | v ≠ i}) :
    cochromaticNumber G ≤ cochromaticNumber H + 1 := by
  have hH : CoColorable (H.induce {v | v ≠ i}) (cochromaticNumber H) :=
    coColorable_induce_of_coColorable (coColorable_cochromaticNumber H)
  rw [← hGH] at hH
  have hG : CoColorable G (cochromaticNumber H + 1) :=
    coColorable_of_induce_and_colorable_compl {v | v ≠ i} hH
      (colorable_one_induce_compl_ne G i)
  exact cochromaticNumber_le_of_coColorable G hG

/-- `ζ(G)` has vertex-deletion oscillation `1`. -/
theorem cochromaticNumber_hasVertexDeletionOscillation (n : ℕ) :
    HasVertexDeletionOscillation
      (fun G : LabeledGraph n ↦ (cochromaticNumber G : ℝ))
      (fun _ ↦ (1 : ℝ≥0)) := by
  intro i G H hGH
  have h1 : (cochromaticNumber G : ℝ) ≤ (cochromaticNumber H : ℝ) + 1 := by
    exact_mod_cast cochromaticNumber_le_add_one_of_induce_away_eq hGH
  have h2 : (cochromaticNumber H : ℝ) ≤ (cochromaticNumber G : ℝ) + 1 := by
    exact_mod_cast cochromaticNumber_le_add_one_of_induce_away_eq hGH.symm
  change |(cochromaticNumber G : ℝ) - (cochromaticNumber H : ℝ)| ≤ 1
  rw [abs_le]
  constructor <;> linarith

/-- Restricting a proper colouring of `H` away from `i` and assigning a fresh
colour to `i` gives a `(k + 1)`-colouring of `G`. -/
theorem colorable_add_one_of_induce_away_eq {n k : ℕ}
    {G H : LabeledGraph n} {i : Fin n}
    (hGH : G.induce {v | v ≠ i} = H.induce {v | v ≠ i})
    (hCol : H.Colorable k) :
    G.Colorable (k + 1) := by
  classical
  rcases hCol with ⟨CH⟩
  let rawColor : Fin n → Fin (k + 1) := fun v ↦
    if v = i then Fin.last k else (CH v).castSucc
  have hvalid : ∀ {u v : Fin n}, G.Adj u v → rawColor u ≠ rawColor v := by
    intro u v huv
    by_cases hu : u = i <;> by_cases hv : v = i
    · exact (G.ne_of_adj huv (hu.trans hv.symm)).elim
    · simp only [rawColor, hu, hv, ↓reduceIte]
      exact (Fin.castSucc_lt_last (CH v)).ne'
    · simp only [rawColor, hu, hv, ↓reduceIte]
      exact (Fin.castSucc_lt_last (CH u)).ne
    · simp only [rawColor, hu, hv, ↓reduceIte, ne_eq, Fin.castSucc_inj]
      have hadjH : H.Adj u v := by
        change (H.induce {x | x ≠ i}).Adj ⟨u, hu⟩ ⟨v, hv⟩
        rw [← hGH]
        exact huv
      exact CH.valid hadjH
  exact ⟨SimpleGraph.Coloring.mk rawColor hvalid⟩

/-- Changing the edges at vertex `i` changes `χ(G)` by at most `1`. -/
theorem chromaticNumberNat_le_add_one_of_induce_away_eq {n : ℕ}
    {G H : LabeledGraph n} {i : Fin n}
    (hGH : G.induce {v | v ≠ i} = H.induce {v | v ≠ i}) :
    chromaticNumberNat G ≤ chromaticNumberNat H + 1 := by
  have hColG : G.Colorable (chromaticNumberNat H + 1) :=
    colorable_add_one_of_induce_away_eq hGH (colorable_chromaticNumberNat H)
  unfold chromaticNumberNat
  exact ENat.toNat_le_of_le_coe hColG.chromaticNumber_le

/-- `χ(G)` has vertex-deletion oscillation `1`. -/
theorem chromaticNumberNat_hasVertexDeletionOscillation (n : ℕ) :
    HasVertexDeletionOscillation
      (fun G : LabeledGraph n ↦ (chromaticNumberNat G : ℝ))
      (fun _ ↦ (1 : ℝ≥0)) := by
  intro i G H hGH
  have h1 : (chromaticNumberNat G : ℝ) ≤ (chromaticNumberNat H : ℝ) + 1 := by
    exact_mod_cast chromaticNumberNat_le_add_one_of_induce_away_eq hGH
  have h2 : (chromaticNumberNat H : ℝ) ≤ (chromaticNumberNat G : ℝ) + 1 := by
    exact_mod_cast chromaticNumberNat_le_add_one_of_induce_away_eq hGH.symm
  change |(chromaticNumberNat G : ℝ) - (chromaticNumberNat H : ℝ)| ≤ 1
  rw [abs_le]
  constructor <;> linarith

/-- Any statistic with unit vertex-deletion oscillation satisfies
`HasBlockOscillation` with `noninitialUnitOscillation` (zero at `i = 0`). -/
theorem hasBlockOscillation_noninitial_of_vertexDeletion {n : ℕ}
    {F : LabeledGraph n → ℝ}
    (hF : HasVertexDeletionOscillation F (fun _ ↦ (1 : ℝ≥0))) :
    HasBlockOscillation (fun x : VertexBlocks n ↦ F (blocksToGraph x))
      noninitialUnitOscillation := by
  intro i x y hxy
  by_cases hi : i.val = 0
  · have hxi : x i = y i := by
      funext u
      have hu : u.val < 0 := by simpa [hi] using u.isLt
      omega
    have hAll : x = y := by
      funext j
      by_cases hji : j = i
      · subst j; exact hxi
      · exact hxy j hji
    subst y
    simp [noninitialUnitOscillation, hi]
  · have h := hF.hasBlockOscillation i x y hxy
    simpa [noninitialUnitOscillation, hi] using h

/-- One-sided upper tail `P(F - E[F] ≥ t) ≤ exp (-2 t² / (n - 1))` for `n ≥ 2`. -/
theorem randomGraph_upperTail_noninitial {n : ℕ} (hn : 2 ≤ n)
    {F : LabeledGraph n → ℝ}
    (hF : HasVertexDeletionOscillation F (fun _ ↦ (1 : ℝ≥0)))
    {t : ℝ} (ht : 0 ≤ t) :
    (randomGraphMeasure n).real
        {G | t ≤ F G - ∫ H, F H ∂(randomGraphMeasure n)} ≤
      Real.exp (-2 * t ^ 2 / ((n - 1 : ℕ) : ℝ)) := by
  rw [integral_randomGraphMeasure_eq_randomGraphBlockExpectation]
  have hb := blockBoundedDifferences_upperTail
    (Omega := fun v : Fin n ↦ VertexBlock v)
    (hasBlockOscillation_noninitial_of_vertexDeletion hF) ht
  have hexp :
      -t ^ 2 / (2 * (blockVariance (noninitialUnitOscillation (n := n)) : ℝ)) =
        -2 * t ^ 2 / ((n - 1 : ℕ) : ℝ) := by
    rw [blockVariance_noninitialUnitOscillation]
    have hn1 : ((n - 1 : ℕ) : ℝ) ≠ 0 := by
      have : 1 ≤ n - 1 := by omega
      exact_mod_cast (by omega : n - 1 ≠ 0)
    field_simp [hn1]
    ring
  rw [hexp] at hb
  change (randomGraphMeasure n
    {G | t ≤ F G - randomGraphBlockExpectation F}).toReal ≤ _
  rw [← vertexBlockMeasure_preimage_eq_randomGraphMeasure]
  simpa only [Set.preimage_setOf_eq, randomGraphBlockExpectation,
    vertexBlockMeasure, Measure.real] using hb

/-- One-sided lower tail `P(E[F] - F ≥ t) ≤ exp (-2 t² / (n - 1))` for `n ≥ 2`. -/
theorem randomGraph_lowerTail_noninitial {n : ℕ} (hn : 2 ≤ n)
    {F : LabeledGraph n → ℝ}
    (hF : HasVertexDeletionOscillation F (fun _ ↦ (1 : ℝ≥0)))
    {t : ℝ} (ht : 0 ≤ t) :
    (randomGraphMeasure n).real
        {G | t ≤ ∫ H, F H ∂(randomGraphMeasure n) - F G} ≤
      Real.exp (-2 * t ^ 2 / ((n - 1 : ℕ) : ℝ)) := by
  have hIntNeg :
      ∫ H, (-F H) ∂(randomGraphMeasure n) = -∫ H, F H ∂(randomGraphMeasure n) :=
    integral_neg F
  have hNegOsc : HasBlockOscillation
      (fun x : VertexBlocks n ↦ -F (blocksToGraph x)) noninitialUnitOscillation :=
    HasBlockOscillation.neg (hasBlockOscillation_noninitial_of_vertexDeletion hF)
  have hb := blockBoundedDifferences_upperTail
    (Omega := fun v : Fin n ↦ VertexBlock v) hNegOsc ht
  have hexp :
      -t ^ 2 / (2 * (blockVariance (noninitialUnitOscillation (n := n)) : ℝ)) =
        -2 * t ^ 2 / ((n - 1 : ℕ) : ℝ) := by
    rw [blockVariance_noninitialUnitOscillation]
    have hn1 : ((n - 1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (by omega : n - 1 ≠ 0)
    field_simp [hn1]
    ring
  rw [hexp] at hb
  have hMeanNeg :
      blockExpectation (fun v : Fin n ↦ VertexBlock v)
          (fun x : VertexBlocks n ↦ -F (blocksToGraph x)) =
        -∫ H, F H ∂(randomGraphMeasure n) := by
    change randomGraphBlockExpectation (fun H ↦ -F H) = _
    rw [← integral_randomGraphMeasure_eq_randomGraphBlockExpectation, hIntNeg]
  rw [hMeanNeg] at hb
  have hSetEq :
      {G : LabeledGraph n | t ≤ ∫ H, F H ∂(randomGraphMeasure n) - F G} =
        {G : LabeledGraph n | t ≤ -F G - -∫ H, F H ∂(randomGraphMeasure n)} := by
    ext G
    simp only [Set.mem_setOf_eq, sub_neg_eq_add]
    constructor <;> intro h <;> linarith
  rw [hSetEq]
  change (randomGraphMeasure n _).toReal ≤ _
  rw [← vertexBlockMeasure_preimage_eq_randomGraphMeasure]
  simpa only [Set.preimage_setOf_eq, vertexBlockMeasure, Measure.real] using hb

/-- **Generic rare-seed amplification (Section 8 argument):** if `F` has unit
vertex-deletion oscillation and `P(F ≤ k) > exp (-2 t² / (n - 1))`, then
`E[F] ≤ k + t` and `P(F > k + 2 t) ≤ exp (-2 t² / (n - 1))`. -/
theorem randomGraph_amplification_of_seed {n : ℕ} (hn : 2 ≤ n)
    {F : LabeledGraph n → ℕ}
    (hF : HasVertexDeletionOscillation (fun G ↦ (F G : ℝ)) (fun _ ↦ (1 : ℝ≥0)))
    {k : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hSeed : Real.exp (-2 * t ^ 2 / ((n - 1 : ℕ) : ℝ)) <
      (randomGraphMeasure n).real {G | F G ≤ k}) :
    ∫ H, (F H : ℝ) ∂(randomGraphMeasure n) ≤ (k : ℝ) + t ∧
      (randomGraphMeasure n).real {G | (k : ℝ) + 2 * t < (F G : ℝ)} ≤
        Real.exp (-2 * t ^ 2 / ((n - 1 : ℕ) : ℝ)) := by
  have hExpLe : ∫ H, (F H : ℝ) ∂(randomGraphMeasure n) ≤ (k : ℝ) + t := by
    by_contra hgt_not
    have hgt : (k : ℝ) + t < ∫ H, (F H : ℝ) ∂(randomGraphMeasure n) :=
      not_le.mp hgt_not
    have hSub :
        {G : LabeledGraph n | F G ≤ k} ⊆
          {G : LabeledGraph n | t ≤ ∫ H, (F H : ℝ) ∂(randomGraphMeasure n) - (F G : ℝ)} := by
      intro G hG
      simp only [Set.mem_setOf_eq] at hG ⊢
      have hG' : (F G : ℝ) ≤ (k : ℝ) := by exact_mod_cast hG
      linarith
    have hMono :
        (randomGraphMeasure n).real {G | F G ≤ k} ≤
          (randomGraphMeasure n).real
            {G | t ≤ ∫ H, (F H : ℝ) ∂(randomGraphMeasure n) - (F G : ℝ)} :=
      measureReal_mono hSub
    have hLow := randomGraph_lowerTail_noninitial hn hF ht
    linarith
  refine ⟨hExpLe, ?_⟩
  have hSubUp :
      {G : LabeledGraph n | (k : ℝ) + 2 * t < (F G : ℝ)} ⊆
        {G : LabeledGraph n | t ≤ (F G : ℝ) - ∫ H, (F H : ℝ) ∂(randomGraphMeasure n)} := by
    intro G hG
    simp only [Set.mem_setOf_eq] at hG ⊢
    linarith
  exact le_trans (measureReal_mono hSubUp) (randomGraph_upperTail_noninitial hn hF ht)

/-- **Corollary 8.1 (`cor:zeta-upper`, cochromatic part):** once
`P(ζ(G_n) ≤ k_co) > exp (-2 t² / (n - 1))`, we have
`P(ζ(G_n) > k_co + 2 t) ≤ exp (-2 t² / (n - 1))`. -/
theorem cochromatic_upperTail_of_seed {n kCo : ℕ} (hn : 2 ≤ n)
    {t : ℝ} (ht : 0 ≤ t)
    (hSeed : Real.exp (-2 * t ^ 2 / ((n - 1 : ℕ) : ℝ)) <
      (randomGraphMeasure n).real {G | cochromaticNumber G ≤ kCo}) :
    (randomGraphMeasure n).real {G | (kCo : ℝ) + 2 * t < (cochromaticNumber G : ℝ)} ≤
      Real.exp (-2 * t ^ 2 / ((n - 1 : ℕ) : ℝ)) :=
  (randomGraph_amplification_of_seed hn
    (cochromaticNumber_hasVertexDeletionOscillation n) ht hSeed).2

/-- **Corollary 8.1 (`cor:zeta-upper`, chromatic part):** once
`P(χ(G_n) ≤ k_ch) > exp (-2 t² / (n - 1))`, we have
`P(χ(G_n) > k_ch + 2 t) ≤ exp (-2 t² / (n - 1))`. -/
theorem chromatic_upperTail_of_seed {n kCh : ℕ} (hn : 2 ≤ n)
    {t : ℝ} (ht : 0 ≤ t)
    (hSeed : Real.exp (-2 * t ^ 2 / ((n - 1 : ℕ) : ℝ)) <
      (randomGraphMeasure n).real {G | chromaticNumberNat G ≤ kCh}) :
    (randomGraphMeasure n).real {G | (kCh : ℝ) + 2 * t < (chromaticNumberNat G : ℝ)} ≤
      Real.exp (-2 * t ^ 2 / ((n - 1 : ℕ) : ℝ)) :=
  (randomGraph_amplification_of_seed hn
    (chromaticNumberNat_hasVertexDeletionOscillation n) ht hSeed).2

end

end Erdos625HP
