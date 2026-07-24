import Erdos625.Section8EndpointDecoratedBlockPairings

/-!
# Endpoint decorated block pairings to physical endpoint fibres

This is the statement-faithful inverse-map half of the endpoint fibre equivalence.
It reconstructs the physical stub edges selected by the literal decorations and
does not depend on the separately generated forward map.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

set_option autoImplicit false

theorem profileBlockMargin_fourEndpointActualBlockOfAtom (alpha : Nat)
    (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (a : Σ i : Fin 4, Fin (fourEndpointMultiplicity alpha hAlpha k i)) :
    profileBlockMargin k
        (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex a) =
      fourEndpointSize alpha hAlpha a.1 := by
  have hmem := (slotIndex a.1 a.2).2
  have hEq : profileBlockMargin k (slotIndex a.1 a.2).1 =
      fourEndpointSize alpha hAlpha a.1 := by
    simpa only [fourEndpointBlockSlots, Finset.mem_filter,
      Finset.mem_univ, true_and] using hmem
  exact hEq

theorem fourEndpointActualBlockOfAtom_injective (alpha : Nat)
    (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k) :
    Function.Injective
      (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ hab
  have hs : fourEndpointSize alpha hAlpha i =
      fourEndpointSize alpha hAlpha j := by
    rw [← profileBlockMargin_fourEndpointActualBlockOfAtom
      alpha hAlpha k slotIndex ⟨i, a⟩,
      ← profileBlockMargin_fourEndpointActualBlockOfAtom
      alpha hAlpha k slotIndex ⟨j, b⟩, hab]
  have hij : i = j := by
    have hi := (fourEndpoint_profile_indexing_facts alpha hAlpha k).1 i
    have hj := (fourEndpoint_profile_indexing_facts alpha hAlpha k).1 j
    rw [hi, hj] at hs
    apply Fin.ext
    omega
  subst j
  have hab' : slotIndex i a = slotIndex i b := by
    exact Subtype.ext hab
  have : a = b := (slotIndex i).injective hab'
  subst b
  rfl

noncomputable def fourEndpointPhysicalEdgeOfLocalEdge
    (alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (D : FourEndpointDecoratedBlockPairing alpha hAlpha k L)
    (e : ↥D.1.1.edges)
    (p : RowStub (fun _ : Unit => fourEndpointSize alpha hAlpha e.1.1.1) ×
      ColumnStub (fun _ : Unit => fourEndpointSize alpha hAlpha e.1.2.1)) :
    RowStub (profileBlockMargin k) × ColumnStub (profileBlockMargin k) :=
  let ha := profileBlockMargin_fourEndpointActualBlockOfAtom
    alpha hAlpha k slotIndex e.1.1
  let hb := profileBlockMargin_fourEndpointActualBlockOfAtom
    alpha hAlpha k slotIndex e.1.2
  (⟨fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.1,
      ⟨p.1.2.val, by rw [ha]; exact p.1.2.isLt⟩⟩,
   ⟨fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.2,
      ⟨p.2.2.val, by rw [hb]; exact p.2.2.isLt⟩⟩)

noncomputable def fourEndpointDecoratedPhysicalEdges
    (alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (D : FourEndpointDecoratedBlockPairing alpha hAlpha k L) :
    Finset (RowStub (profileBlockMargin k) × ColumnStub (profileBlockMargin k)) :=
  D.1.1.edges.attach.biUnion fun e =>
    (D.2 e).1.edges.image fun p =>
      fourEndpointPhysicalEdgeOfLocalEdge alpha hAlpha k L slotIndex D e p

noncomputable def fourEndpointDecoratedPhysicalSkeleton
    (alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (D : FourEndpointDecoratedBlockPairing alpha hAlpha k L) :
    UnlabelledTypedSkeleton (profileBlockMargin k) (profileBlockMargin k) where
  edges := fourEndpointDecoratedPhysicalEdges alpha hAlpha k L slotIndex D
  leftUnique := by
    intro x hx y hy hxy
    simp only [fourEndpointDecoratedPhysicalEdges, Finset.mem_biUnion,
      Finset.mem_attach, true_and, Finset.mem_image] at hx hy
    obtain ⟨ex, px, hpx, rfl⟩ := hx
    obtain ⟨ey, py, hpy, rfl⟩ := hy
    have heleft : ex.1.1 = ey.1.1 :=
      fourEndpointActualBlockOfAtom_injective alpha hAlpha k slotIndex
        (congrArg Sigma.fst hxy)
    have heval : ex.1 = ey.1 := D.1.1.leftUnique ex.1 ex.2 ey.1 ey.2
      heleft
    have he : ex = ey := Subtype.ext heval
    subst ey
    have hpl : px.1 = py.1 := by
      apply Sigma.ext (x := px.1) (y := py.1) rfl
      apply heq_of_eq
      apply Fin.ext
      simpa only [fourEndpointPhysicalEdgeOfLocalEdge] using
        congrArg (fun z => z.2.val) hxy
    have hp : px = py := (D.2 ex).1.leftUnique px hpx py hpy hpl
    subst py
    rfl
  rightUnique := by
    intro x hx y hy hxy
    simp only [fourEndpointDecoratedPhysicalEdges, Finset.mem_biUnion,
      Finset.mem_attach, true_and, Finset.mem_image] at hx hy
    obtain ⟨ex, px, hpx, rfl⟩ := hx
    obtain ⟨ey, py, hpy, rfl⟩ := hy
    have heright : ex.1.2 = ey.1.2 :=
      fourEndpointActualBlockOfAtom_injective alpha hAlpha k slotIndex
        (congrArg Sigma.fst hxy)
    have heval : ex.1 = ey.1 := D.1.1.rightUnique ex.1 ex.2 ey.1 ey.2
      heright
    have he : ex = ey := Subtype.ext heval
    subst ey
    have hpr : px.2 = py.2 := by
      apply Sigma.ext (x := px.2) (y := py.2) rfl
      apply heq_of_eq
      apply Fin.ext
      simpa only [fourEndpointPhysicalEdgeOfLocalEdge] using
        congrArg (fun z => z.2.val) hxy
    have hp : px = py := (D.2 ex).1.rightUnique px hpx py hpy hpr
    subst py
    rfl

theorem fourEndpointDecoratedPhysicalSkeleton_cellEdges_selected
    (alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (D : FourEndpointDecoratedBlockPairing alpha hAlpha k L)
    (e : ↥D.1.1.edges) :
    (fourEndpointDecoratedPhysicalSkeleton alpha hAlpha k L slotIndex D).edges.filter
        (fun z => z.1.1 = fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.1 ∧
          z.2.1 = fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.2) =
      (D.2 e).1.edges.image (fun p =>
        fourEndpointPhysicalEdgeOfLocalEdge alpha hAlpha k L slotIndex D e p) := by
  ext z
  constructor
  · intro hz
    rw [Finset.mem_filter] at hz
    rcases hz with ⟨hz, hztype⟩
    simp only [fourEndpointDecoratedPhysicalSkeleton,
      fourEndpointDecoratedPhysicalEdges, Finset.mem_biUnion,
      Finset.mem_attach, true_and, Finset.mem_image] at hz
    obtain ⟨e', p, hp, rfl⟩ := hz
    have hrow : e'.1.1 = e.1.1 :=
      fourEndpointActualBlockOfAtom_injective alpha hAlpha k slotIndex hztype.1
    have hcol : e'.1.2 = e.1.2 :=
      fourEndpointActualBlockOfAtom_injective alpha hAlpha k slotIndex hztype.2
    have heval : e'.1 = e.1 := Prod.ext hrow hcol
    have he : e' = e := Subtype.ext heval
    subst e'
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  · intro hz
    rw [Finset.mem_image] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    rw [Finset.mem_filter]
    constructor
    · simp only [fourEndpointDecoratedPhysicalSkeleton,
        fourEndpointDecoratedPhysicalEdges, Finset.mem_biUnion,
        Finset.mem_attach, true_and]
      exact ⟨e, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
    · simp [fourEndpointPhysicalEdgeOfLocalEdge]

theorem fourEndpointDecoratedPhysicalSkeleton_typeTable_selected
    (alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (D : FourEndpointDecoratedBlockPairing alpha hAlpha k L)
    (e : ↥D.1.1.edges) :
    (fourEndpointDecoratedPhysicalSkeleton alpha hAlpha k L slotIndex D).typeTable
        (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.1)
        (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.2) =
      fourEndpointOverlapSize alpha hAlpha e.1.1.1 e.1.2.1 := by
  unfold UnlabelledTypedSkeleton.typeTable
  rw [fourEndpointDecoratedPhysicalSkeleton_cellEdges_selected
    alpha hAlpha k L slotIndex D e]
  rw [Finset.card_image_of_injOn]
  · simpa [UnlabelledTypedSkeleton.typeTable] using (D.2 e).2
  · intro p hp q hq hpq
    have hl : p.1 = q.1 := by
      apply Sigma.ext (x := p.1) (y := q.1) rfl
      apply heq_of_eq
      apply Fin.ext
      simpa [fourEndpointPhysicalEdgeOfLocalEdge] using
        congrArg (fun z => z.1.2.val) hpq
    have hr : p.2 = q.2 := by
      apply Sigma.ext (x := p.2) (y := q.2) rfl
      apply heq_of_eq
      apply Fin.ext
      simpa [fourEndpointPhysicalEdgeOfLocalEdge] using
        congrArg (fun z => z.2.2.val) hpq
    exact Prod.ext hl hr

theorem fourEndpointDecoratedPhysicalSkeleton_endpointOnly
    (alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (D : FourEndpointDecoratedBlockPairing alpha hAlpha k L) :
    IsFourEndpointOnlyPhysicalSkeleton alpha hAlpha k
      (fourEndpointDecoratedPhysicalSkeleton alpha hAlpha k L slotIndex D) := by
  intro z hz
  simp only [fourEndpointDecoratedPhysicalSkeleton,
    fourEndpointDecoratedPhysicalEdges, Finset.mem_biUnion,
    Finset.mem_attach, true_and, Finset.mem_image] at hz
  obtain ⟨e, p, hp, rfl⟩ := hz
  refine ⟨e.1.1.1, e.1.2.1, ?_, ?_, ?_⟩
  · exact (slotIndex e.1.1.1 e.1.1.2).2
  · exact (slotIndex e.1.2.1 e.1.2.2).2
  · exact fourEndpointDecoratedPhysicalSkeleton_typeTable_selected
      alpha hAlpha k L slotIndex D e

theorem fourEndpointDecoratedPhysicalSkeleton_fullPairs_iff
    (alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (D : FourEndpointDecoratedBlockPairing alpha hAlpha k L)
    (a b : ProfileBlockIndex k) :
    (a, b) ∈ fourEndpointFullPairs alpha hAlpha k
        (fourEndpointDecoratedPhysicalSkeleton alpha hAlpha k L slotIndex D) ↔
      ∃ e : ↥D.1.1.edges,
        a = fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.1 ∧
        b = fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1.2 := by
  constructor
  · intro hab
    rw [fourEndpointFullPairs, Finset.mem_filter] at hab
    obtain ⟨_, i, j, hai, hbj, htable⟩ := hab
    have hpos : 0 < fourEndpointOverlapSize alpha hAlpha i j := by
      unfold fourEndpointOverlapSize
      have hi := (fourEndpoint_profile_indexing_facts alpha hAlpha k).1 i
      have hj := (fourEndpoint_profile_indexing_facts alpha hAlpha k).1 j
      rw [hi, hj]
      omega
    have hnz : (fourEndpointDecoratedPhysicalSkeleton alpha hAlpha k L slotIndex D).typeTable
        a b ≠ 0 := by
      rw [htable]
      omega
    rw [UnlabelledTypedSkeleton.typeTable_ne_zero_iff_exists_physical_edge] at hnz
    obtain ⟨z, hz, hza, hzb⟩ := hnz
    simp only [fourEndpointDecoratedPhysicalSkeleton,
      fourEndpointDecoratedPhysicalEdges, Finset.mem_biUnion,
      Finset.mem_attach, true_and, Finset.mem_image] at hz
    obtain ⟨e, p, hp, hzp⟩ := hz
    refine ⟨e, ?_, ?_⟩
    · rw [← hza, ← hzp]
      rfl
    · rw [← hzb, ← hzp]
      rfl
  · rintro ⟨e, rfl, rfl⟩
    rw [fourEndpointFullPairs, Finset.mem_filter]
    refine ⟨by simp, e.1.1.1, e.1.2.1,
      (slotIndex e.1.1.1 e.1.1.2).2,
      (slotIndex e.1.2.1 e.1.2.2).2, ?_⟩
    exact fourEndpointDecoratedPhysicalSkeleton_typeTable_selected
      alpha hAlpha k L slotIndex D e

theorem fourEndpointDecoratedPhysicalSkeleton_matching
    (alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (D : FourEndpointDecoratedBlockPairing alpha hAlpha k L) :
    FourEndpointFullPairsAreMatching alpha hAlpha k
      (fourEndpointDecoratedPhysicalSkeleton alpha hAlpha k L slotIndex D) := by
  constructor
  · intro a b₁ b₂ h₁ h₂
    rw [fourEndpointDecoratedPhysicalSkeleton_fullPairs_iff
      alpha hAlpha k L slotIndex D] at h₁ h₂
    obtain ⟨e₁, ha₁, hb₁⟩ := h₁
    obtain ⟨e₂, ha₂, hb₂⟩ := h₂
    have hleft : e₁.1.1 = e₂.1.1 :=
      fourEndpointActualBlockOfAtom_injective alpha hAlpha k slotIndex
        (ha₁.symm.trans ha₂)
    have he : e₁.1 = e₂.1 := D.1.1.leftUnique e₁.1 e₁.2 e₂.1 e₂.2 hleft
    exact hb₁.trans (congrArg (fun z =>
      fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex z.2) he) |>.trans hb₂.symm
  · intro a₁ a₂ b h₁ h₂
    rw [fourEndpointDecoratedPhysicalSkeleton_fullPairs_iff
      alpha hAlpha k L slotIndex D] at h₁ h₂
    obtain ⟨e₁, ha₁, hb₁⟩ := h₁
    obtain ⟨e₂, ha₂, hb₂⟩ := h₂
    have hright : e₁.1.2 = e₂.1.2 :=
      fourEndpointActualBlockOfAtom_injective alpha hAlpha k slotIndex
        (hb₁.symm.trans hb₂)
    have he : e₁.1 = e₂.1 := D.1.1.rightUnique e₁.1 e₁.2 e₂.1 e₂.2 hright
    exact ha₁.trans (congrArg (fun z =>
      fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex z.1) he) |>.trans ha₂.symm

theorem fourEndpointDecoratedPhysicalSkeleton_fullTable_cell
    (alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (D : FourEndpointDecoratedBlockPairing alpha hAlpha k L)
    (i j : Fin 4) :
    (((fourEndpointBlockSlots alpha hAlpha k i).product
      (fourEndpointBlockSlots alpha hAlpha k j)).filter
        (fun ab => (fourEndpointDecoratedPhysicalSkeleton alpha hAlpha k L slotIndex D).typeTable
          ab.1 ab.2 = fourEndpointOverlapSize alpha hAlpha i j)).card =
      D.1.1.typeTable i j := by
  let source := D.1.1.edges.filter (fun e => e.1.1 = i ∧ e.2.1 = j)
  let F := fun e : (Σ i : Fin 4, Fin (fourEndpointMultiplicity alpha hAlpha k i)) ×
      (Σ j : Fin 4, Fin (fourEndpointMultiplicity alpha hAlpha k j)) =>
    (fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1,
      fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.2)
  have hfin :
      ((fourEndpointBlockSlots alpha hAlpha k i).product
        (fourEndpointBlockSlots alpha hAlpha k j)).filter
          (fun ab => (fourEndpointDecoratedPhysicalSkeleton alpha hAlpha k L slotIndex D).typeTable
            ab.1 ab.2 = fourEndpointOverlapSize alpha hAlpha i j) =
        source.image F := by
    ext ab
    constructor
    · intro hab
      rw [Finset.mem_filter] at hab
      obtain ⟨hprod, htable⟩ := hab
      have hprod' := Finset.mem_product.mp hprod
      have hfull : ab ∈ fourEndpointFullPairs alpha hAlpha k
          (fourEndpointDecoratedPhysicalSkeleton alpha hAlpha k L slotIndex D) := by
        rw [fourEndpointFullPairs, Finset.mem_filter]
        exact ⟨by simp, i, j, hprod'.1, hprod'.2, htable⟩
      rw [fourEndpointDecoratedPhysicalSkeleton_fullPairs_iff
        alpha hAlpha k L slotIndex D] at hfull
      obtain ⟨e, ha, hb⟩ := hfull
      have hei : e.1.1.1 = i := by
        apply Fin.ext
        have hm := profileBlockMargin_fourEndpointActualBlockOfAtom
          alpha hAlpha k slotIndex e.1.1
        have hi := (slotIndex i).surjective ⟨ab.1, hprod'.1⟩
        obtain ⟨x, hx⟩ := hi
        have heq : e.1.1 = ⟨i, x⟩ :=
          fourEndpointActualBlockOfAtom_injective alpha hAlpha k slotIndex (by
            rw [← ha]
            exact congrArg Subtype.val hx.symm)
        exact congrArg (fun z => z.1.val) heq
      have hej : e.1.2.1 = j := by
        apply Fin.ext
        have hj := (slotIndex j).surjective ⟨ab.2, hprod'.2⟩
        obtain ⟨x, hx⟩ := hj
        have heq : e.1.2 = ⟨j, x⟩ :=
          fourEndpointActualBlockOfAtom_injective alpha hAlpha k slotIndex (by
            rw [← hb]
            exact congrArg Subtype.val hx.symm)
        exact congrArg (fun z => z.1.val) heq
      rw [Finset.mem_image]
      refine ⟨e.1, ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨e.2, hei, hej⟩
      · exact Prod.ext ha.symm hb.symm
    · intro hab
      rw [Finset.mem_image] at hab
      obtain ⟨e, he, rfl⟩ := hab
      rw [Finset.mem_filter] at he
      obtain ⟨hedge, hei, hej⟩ := he
      let es : ↥D.1.1.edges := ⟨e, hedge⟩
      rw [Finset.mem_filter]
      constructor
      · apply Finset.mem_product.mpr
        constructor
        · change fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.1 ∈
            fourEndpointBlockSlots alpha hAlpha k i
          simpa only [F, fourEndpointActualBlockOfAtom, hei] using
            (slotIndex e.1.1 e.1.2).2
        · change fourEndpointActualBlockOfAtom alpha hAlpha k slotIndex e.2 ∈
            fourEndpointBlockSlots alpha hAlpha k j
          simpa only [F, fourEndpointActualBlockOfAtom, hej] using
            (slotIndex e.2.1 e.2.2).2
      · simpa [F, es, hei, hej] using
          (fourEndpointDecoratedPhysicalSkeleton_typeTable_selected
            alpha hAlpha k L slotIndex D es)
  rw [hfin, Finset.card_image_of_injective]
  · rfl
  · intro e₁ e₂ he
    exact Prod.ext
      (fourEndpointActualBlockOfAtom_injective alpha hAlpha k slotIndex
        (congrArg Prod.fst he))
      (fourEndpointActualBlockOfAtom_injective alpha hAlpha k slotIndex
        (congrArg Prod.snd he))

noncomputable def fourEndpointDecoratedBlockPairingToPhysicalFibre
    (alpha : Nat) (hAlpha : 5 < alpha) (k : ColoringProfile (alpha + 1))
    (L : FourEndpointFullTable)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k) :
    FourEndpointDecoratedBlockPairing alpha hAlpha k L →
      FourEndpointPhysicalFibre alpha hAlpha k L := by
  intro D
  refine ⟨⟨fourEndpointDecoratedPhysicalSkeleton alpha hAlpha k L slotIndex D,
    fourEndpointDecoratedPhysicalSkeleton_endpointOnly alpha hAlpha k L slotIndex D,
    fourEndpointDecoratedPhysicalSkeleton_matching alpha hAlpha k L slotIndex D⟩, ?_⟩
  apply FourEndpointFullTable.ext
  funext i j
  change (((fourEndpointBlockSlots alpha hAlpha k i).product
      (fourEndpointBlockSlots alpha hAlpha k j)).filter
        (fun ab => (fourEndpointDecoratedPhysicalSkeleton alpha hAlpha k L slotIndex D).typeTable
          ab.1 ab.2 = fourEndpointOverlapSize alpha hAlpha i j)).card = L.toFun i j
  rw [fourEndpointDecoratedPhysicalSkeleton_fullTable_cell
    alpha hAlpha k L slotIndex D i j]
  exact congrFun (congrFun D.1.2 i) j

end

end Erdos625
