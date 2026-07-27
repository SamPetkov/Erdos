import Erdos625.Section8ProfileSkeletonWeight
import Erdos625.Section8EndpointSingleCellStubs
import Mathlib.Tactic

/-!
# Section VIII: exact local-cell fibre of a matching-supported demand

Let `demand : A → B → Nat` be a finite demand table whose positive support is a
bipartite matching.  A physical skeleton with this type table is then exactly a
product of independent one-cell partial stub matchings, one for every positive
cell.  This module proves that statement as a literal finite equivalence.

This is the aggregate physical-fibre theorem needed in place of an objectwise
"complete every cell and delete deficits" construction.  It introduces no
full-cell completion and no probability or asymptotic estimate.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- One independent literal partial stub matching in every positive demand
cell. -/
abbrev MatchingDemandCellDecoration
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → Nat) (row : A → Nat) (col : B → Nat) :=
  ∀ e : ↥(positiveDemandSupport demand),
    SingleCellStubMatching (row e.1.1) (col e.1.2)
      (demand e.1.1 e.1.2)

/-- Embed one local one-cell edge in the global typed stub spaces. -/
def matchingDemandPhysicalEdgeOfLocalEdge
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → Nat} {row : A → Nat} {col : B → Nat}
    (e : ↥(positiveDemandSupport demand))
    (p : RowStub (fun _ : Unit => row e.1.1) ×
      ColumnStub (fun _ : Unit => col e.1.2)) :
    RowStub row × ColumnStub col :=
  (⟨e.1.1, p.1.2⟩, ⟨e.1.2, p.2.2⟩)

/-- Union of the physical edges supplied by all positive demand cells. -/
def matchingDemandDecoratedPhysicalEdges
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → Nat} {row : A → Nat} {col : B → Nat}
    (D : MatchingDemandCellDecoration demand row col) :
    Finset (RowStub row × ColumnStub col) :=
  (positiveDemandSupport demand).attach.biUnion fun e =>
    (D e).1.edges.image fun p => matchingDemandPhysicalEdgeOfLocalEdge e p

/-- A matching-supported cell decoration gives one global physical skeleton. -/
def matchingDemandDecoratedPhysicalSkeleton
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → Nat} {row : A → Nat} {col : B → Nat}
    (hmatching : IsBipartiteMatching (positiveDemandSupport demand))
    (D : MatchingDemandCellDecoration demand row col) :
    UnlabelledTypedSkeleton row col where
  edges := matchingDemandDecoratedPhysicalEdges D
  leftUnique := by
    intro x hx y hy hxy
    simp only [matchingDemandDecoratedPhysicalEdges, Finset.mem_biUnion,
      Finset.mem_attach, true_and, Finset.mem_image] at hx hy
    obtain ⟨ex, px, hpx, rfl⟩ := hx
    obtain ⟨ey, py, hpy, rfl⟩ := hy
    have ha : ex.1.1 = ey.1.1 := (Sigma.mk.inj_iff.mp hxy).1
    have hb : ex.1.2 = ey.1.2 :=
      hmatching.1 ex.1.1 ex.1.2 ey.1.2 ex.2 (by simpa [ha] using ey.2)
    have heval : ex.1 = ey.1 := Prod.ext ha hb
    have he : ex = ey := Subtype.ext heval
    subst ey
    have hpl : px.1 = py.1 := by
      apply Sigma.ext rfl
      exact heq_of_eq (eq_of_heq (Sigma.mk.inj_iff.mp hxy).2)
    have hp : px = py := (D ex).1.leftUnique px hpx py hpy hpl
    subst py
    rfl
  rightUnique := by
    intro x hx y hy hxy
    simp only [matchingDemandDecoratedPhysicalEdges, Finset.mem_biUnion,
      Finset.mem_attach, true_and, Finset.mem_image] at hx hy
    obtain ⟨ex, px, hpx, rfl⟩ := hx
    obtain ⟨ey, py, hpy, rfl⟩ := hy
    have hb : ex.1.2 = ey.1.2 := (Sigma.mk.inj_iff.mp hxy).1
    have ha : ex.1.1 = ey.1.1 :=
      hmatching.2 ex.1.2 ex.1.1 ey.1.1 ex.2 (by simpa [hb] using ey.2)
    have heval : ex.1 = ey.1 := Prod.ext ha hb
    have he : ex = ey := Subtype.ext heval
    subst ey
    have hpr : px.2 = py.2 := by
      apply Sigma.ext rfl
      exact heq_of_eq (eq_of_heq (Sigma.mk.inj_iff.mp hxy).2)
    have hp : px = py := (D ex).1.rightUnique px hpx py hpy hpr
    subst py
    rfl

/-- In one selected positive cell, the global physical edge filter is exactly
the image of the corresponding local cell matching. -/
theorem matchingDemandDecoratedPhysicalSkeleton_cellEdges_selected
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → Nat} {row : A → Nat} {col : B → Nat}
    (hmatching : IsBipartiteMatching (positiveDemandSupport demand))
    (D : MatchingDemandCellDecoration demand row col)
    (e : ↥(positiveDemandSupport demand)) :
    (matchingDemandDecoratedPhysicalSkeleton hmatching D).edges.filter
        (fun z => z.1.1 = e.1.1 ∧ z.2.1 = e.1.2) =
      (D e).1.edges.image fun p => matchingDemandPhysicalEdgeOfLocalEdge e p := by
  ext z
  constructor
  · intro hz
    rw [Finset.mem_filter] at hz
    rcases hz with ⟨hz, hztype⟩
    simp only [matchingDemandDecoratedPhysicalSkeleton,
      matchingDemandDecoratedPhysicalEdges, Finset.mem_biUnion,
      Finset.mem_attach, true_and, Finset.mem_image] at hz
    obtain ⟨e', p, hp, rfl⟩ := hz
    have ha : e'.1.1 = e.1.1 := hztype.1
    have hb : e'.1.2 = e.1.2 := hztype.2
    have he : e' = e := Subtype.ext (Prod.ext ha hb)
    subst e'
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  · intro hz
    rw [Finset.mem_image] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    rw [Finset.mem_filter]
    constructor
    · simp only [matchingDemandDecoratedPhysicalSkeleton,
        matchingDemandDecoratedPhysicalEdges, Finset.mem_biUnion,
        Finset.mem_attach, true_and]
      exact ⟨e, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
    · rfl

/-- The global skeleton has the prescribed multiplicity in every selected
positive cell. -/
theorem matchingDemandDecoratedPhysicalSkeleton_typeTable_selected
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → Nat} {row : A → Nat} {col : B → Nat}
    (hmatching : IsBipartiteMatching (positiveDemandSupport demand))
    (D : MatchingDemandCellDecoration demand row col)
    (e : ↥(positiveDemandSupport demand)) :
    (matchingDemandDecoratedPhysicalSkeleton hmatching D).typeTable
        e.1.1 e.1.2 = demand e.1.1 e.1.2 := by
  unfold UnlabelledTypedSkeleton.typeTable
  rw [matchingDemandDecoratedPhysicalSkeleton_cellEdges_selected hmatching D e]
  rw [Finset.card_image_of_injOn]
  · simpa [UnlabelledTypedSkeleton.typeTable] using (D e).2
  · intro p hp q hq hpq
    apply Prod.ext
    · apply Sigma.ext rfl
      exact heq_of_eq (eq_of_heq (Sigma.mk.inj_iff.mp
        (congrArg Prod.fst hpq)).2)
    · apply Sigma.ext rfl
      exact heq_of_eq (eq_of_heq (Sigma.mk.inj_iff.mp
        (congrArg Prod.snd hpq)).2)

/-- No edge of the constructed skeleton lies in a zero demand cell. -/
theorem matchingDemandDecoratedPhysicalSkeleton_typeTable_zero
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → Nat} {row : A → Nat} {col : B → Nat}
    (hmatching : IsBipartiteMatching (positiveDemandSupport demand))
    (D : MatchingDemandCellDecoration demand row col)
    (a : A) (b : B) (hzero : demand a b = 0) :
    (matchingDemandDecoratedPhysicalSkeleton hmatching D).typeTable a b = 0 := by
  unfold UnlabelledTypedSkeleton.typeTable
  have hfilter :
      (matchingDemandDecoratedPhysicalSkeleton hmatching D).edges.filter
          (fun z => z.1.1 = a ∧ z.2.1 = b) = ∅ := by
    ext z
    constructor
    · intro hz
      rw [Finset.mem_filter] at hz
      rcases hz with ⟨hz, ha, hb⟩
      simp only [matchingDemandDecoratedPhysicalSkeleton,
        matchingDemandDecoratedPhysicalEdges, Finset.mem_biUnion,
        Finset.mem_attach, true_and, Finset.mem_image] at hz
      obtain ⟨e, p, hp, hzp⟩ := hz
      have hea : e.1.1 = a := by
        simpa [matchingDemandPhysicalEdgeOfLocalEdge] using
          congrArg (fun x => x.1.1) hzp
      have heb : e.1.2 = b := by
        simpa [matchingDemandPhysicalEdgeOfLocalEdge] using
          congrArg (fun x => x.2.1) hzp
      have : demand a b ≠ 0 := by
        simpa [positiveDemandSupport, hea, heb] using e.2
      exact (this hzero).elim
    · simp
  rw [hfilter]
  simp

/-- The physical skeleton assembled from local cell decorations has exactly the
original demand table. -/
theorem matchingDemandDecoratedPhysicalSkeleton_typeTable
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → Nat} {row : A → Nat} {col : B → Nat}
    (hmatching : IsBipartiteMatching (positiveDemandSupport demand))
    (D : MatchingDemandCellDecoration demand row col) :
    (matchingDemandDecoratedPhysicalSkeleton hmatching D).typeTable = demand := by
  funext a b
  by_cases hzero : demand a b = 0
  · exact matchingDemandDecoratedPhysicalSkeleton_typeTable_zero
      hmatching D a b hzero
  · let e : ↥(positiveDemandSupport demand) :=
      ⟨(a, b), by simp [positiveDemandSupport, hzero]⟩
    simpa [e] using
      matchingDemandDecoratedPhysicalSkeleton_typeTable_selected hmatching D e

/-- Forward map from local cell decorations to the exact global physical
skeleton fibre. -/
def matchingDemandCellDecorationToPhysicalFibre
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → Nat) (row : A → Nat) (col : B → Nat)
    (hmatching : IsBipartiteMatching (positiveDemandSupport demand)) :
    MatchingDemandCellDecoration demand row col →
      {S : UnlabelledTypedSkeleton row col // S.typeTable = demand} := fun D =>
  ⟨matchingDemandDecoratedPhysicalSkeleton hmatching D,
    matchingDemandDecoratedPhysicalSkeleton_typeTable hmatching D⟩

/-- The global physical skeleton determines every local one-cell decoration. -/
theorem matchingDemandCellDecorationToPhysicalFibre_injective
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → Nat) (row : A → Nat) (col : B → Nat)
    (hmatching : IsBipartiteMatching (positiveDemandSupport demand)) :
    Function.Injective
      (matchingDemandCellDecorationToPhysicalFibre demand row col hmatching) := by
  intro D₁ D₂ hPhysical
  have hSkeleton :
      matchingDemandDecoratedPhysicalSkeleton hmatching D₁ =
        matchingDemandDecoratedPhysicalSkeleton hmatching D₂ :=
    congrArg Subtype.val hPhysical
  funext e
  have hImage :
      (D₁ e).1.edges.image (fun p => matchingDemandPhysicalEdgeOfLocalEdge e p) =
        (D₂ e).1.edges.image (fun p => matchingDemandPhysicalEdgeOfLocalEdge e p) := by
    rw [← matchingDemandDecoratedPhysicalSkeleton_cellEdges_selected
      hmatching D₁ e]
    rw [← matchingDemandDecoratedPhysicalSkeleton_cellEdges_selected
      hmatching D₂ e]
    rw [hSkeleton]
  have hLocalEdges : (D₁ e).1.edges = (D₂ e).1.edges := by
    ext p
    constructor
    · intro hp
      have hpImage : matchingDemandPhysicalEdgeOfLocalEdge e p ∈
          (D₁ e).1.edges.image (fun q =>
            matchingDemandPhysicalEdgeOfLocalEdge e q) :=
        Finset.mem_image.mpr ⟨p, hp, rfl⟩
      rw [hImage] at hpImage
      obtain ⟨q, hq, hpq⟩ := Finset.mem_image.mp hpImage
      have : p = q := by
        apply Prod.ext
        · apply Sigma.ext rfl
          exact heq_of_eq (eq_of_heq (Sigma.mk.inj_iff.mp
            (congrArg Prod.fst hpq)).2)
        · apply Sigma.ext rfl
          exact heq_of_eq (eq_of_heq (Sigma.mk.inj_iff.mp
            (congrArg Prod.snd hpq)).2)
      simpa [this] using hq
    · intro hp
      have hpImage : matchingDemandPhysicalEdgeOfLocalEdge e p ∈
          (D₂ e).1.edges.image (fun q =>
            matchingDemandPhysicalEdgeOfLocalEdge e q) :=
        Finset.mem_image.mpr ⟨p, hp, rfl⟩
      rw [← hImage] at hpImage
      obtain ⟨q, hq, hpq⟩ := Finset.mem_image.mp hpImage
      have : p = q := by
        apply Prod.ext
        · apply Sigma.ext rfl
          exact heq_of_eq (eq_of_heq (Sigma.mk.inj_iff.mp
            (congrArg Prod.fst hpq)).2)
        · apply Sigma.ext rfl
          exact heq_of_eq (eq_of_heq (Sigma.mk.inj_iff.mp
            (congrArg Prod.snd hpq)).2)
      simpa [this] using hq
  exact Subtype.ext (UnlabelledTypedSkeleton.ext hLocalEdges)

/-- Pull one global physical cell edge into the corresponding unit-typed local
coordinates. -/
def matchingDemandPhysicalCellEdgeToLocal
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → Nat} {row : A → Nat} {col : B → Nat}
    (e : ↥(positiveDemandSupport demand)) :
    Fin (row e.1.1) × Fin (col e.1.2) →
      RowStub (fun _ : Unit => row e.1.1) ×
        ColumnStub (fun _ : Unit => col e.1.2) := fun p =>
  (⟨(), p.1⟩, ⟨(), p.2⟩)

/-- The pulled-back local edge map is injective. -/
theorem matchingDemandPhysicalCellEdgeToLocal_injective
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → Nat} {row : A → Nat} {col : B → Nat}
    (e : ↥(positiveDemandSupport demand)) :
    Function.Injective
      (matchingDemandPhysicalCellEdgeToLocal
        (demand := demand) (row := row) (col := col) e) := by
  intro p q hpq
  apply Prod.ext
  · exact eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.fst hpq)).2
  · exact eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.snd hpq)).2

/-- Local one-cell skeleton pulled back from a global physical skeleton fibre. -/
def matchingDemandPhysicalCellLocalSkeleton
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → Nat} {row : A → Nat} {col : B → Nat}
    (S : {S : UnlabelledTypedSkeleton row col // S.typeTable = demand})
    (e : ↥(positiveDemandSupport demand)) :
    UnlabelledTypedSkeleton (fun _ : Unit => row e.1.1)
      (fun _ : Unit => col e.1.2) where
  edges := (S.1.cellEdges e.1.1 e.1.2).image
    (matchingDemandPhysicalCellEdgeToLocal e)
  leftUnique := by
    intro x hx y hy hxy
    rw [Finset.mem_image] at hx hy
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨q, hq, rfl⟩ := hy
    have hpFirst : p.1 = q.1 :=
      eq_of_heq (Sigma.mk.inj_iff.mp hxy).2
    have hpEdge :
        ((⟨e.1.1, p.1⟩, ⟨e.1.2, p.2⟩) : RowStub row × ColumnStub col) ∈
          S.1.edges := by
      simpa [UnlabelledTypedSkeleton.cellEdges] using hp
    have hqEdge :
        ((⟨e.1.1, q.1⟩, ⟨e.1.2, q.2⟩) : RowStub row × ColumnStub col) ∈
          S.1.edges := by
      simpa [UnlabelledTypedSkeleton.cellEdges] using hq
    have hrow : (⟨e.1.1, p.1⟩ : RowStub row) = ⟨e.1.1, q.1⟩ :=
      Sigma.ext rfl (heq_of_eq hpFirst)
    have hglobal := S.1.leftUnique _ hpEdge _ hqEdge hrow
    have hpSecond : p.2 = q.2 :=
      eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.snd hglobal)).2
    exact congrArg (matchingDemandPhysicalCellEdgeToLocal e)
      (Prod.ext hpFirst hpSecond)
  rightUnique := by
    intro x hx y hy hxy
    rw [Finset.mem_image] at hx hy
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨q, hq, rfl⟩ := hy
    have hpSecond : p.2 = q.2 :=
      eq_of_heq (Sigma.mk.inj_iff.mp hxy).2
    have hpEdge :
        ((⟨e.1.1, p.1⟩, ⟨e.1.2, p.2⟩) : RowStub row × ColumnStub col) ∈
          S.1.edges := by
      simpa [UnlabelledTypedSkeleton.cellEdges] using hp
    have hqEdge :
        ((⟨e.1.1, q.1⟩, ⟨e.1.2, q.2⟩) : RowStub row × ColumnStub col) ∈
          S.1.edges := by
      simpa [UnlabelledTypedSkeleton.cellEdges] using hq
    have hcol : (⟨e.1.2, p.2⟩ : ColumnStub col) = ⟨e.1.2, q.2⟩ :=
      Sigma.ext rfl (heq_of_eq hpSecond)
    have hglobal := S.1.rightUnique _ hpEdge _ hqEdge hcol
    have hpFirst : p.1 = q.1 :=
      eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.fst hglobal)).2
    exact congrArg (matchingDemandPhysicalCellEdgeToLocal e)
      (Prod.ext hpFirst hpSecond)

/-- The pulled-back local skeleton has exactly the prescribed cell
multiplicity. -/
theorem matchingDemandPhysicalCellLocalSkeleton_typeTable
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → Nat} {row : A → Nat} {col : B → Nat}
    (S : {S : UnlabelledTypedSkeleton row col // S.typeTable = demand})
    (e : ↥(positiveDemandSupport demand)) :
    (matchingDemandPhysicalCellLocalSkeleton S e).typeTable () () =
      demand e.1.1 e.1.2 := by
  unfold UnlabelledTypedSkeleton.typeTable
  have hAll :
      (matchingDemandPhysicalCellLocalSkeleton S e).edges.filter
          (fun z => z.1.1 = () ∧ z.2.1 = ()) =
        (matchingDemandPhysicalCellLocalSkeleton S e).edges := by
    ext z
    simp
  rw [hAll]
  change ((S.1.cellEdges e.1.1 e.1.2).image
    (matchingDemandPhysicalCellEdgeToLocal e)).card = _
  rw [Finset.card_image_of_injective]
  · have hcell : (S.1.cellEdges e.1.1 e.1.2).card =
        S.1.typeTable e.1.1 e.1.2 := by
      unfold UnlabelledTypedSkeleton.cellEdges UnlabelledTypedSkeleton.typeTable
      refine Finset.card_bij
        (fun p _ => ((⟨e.1.1, p.1⟩, ⟨e.1.2, p.2⟩) :
          RowStub row × ColumnStub col)) ?_ ?_ ?_
      · intro p hp
        rw [Finset.mem_filter] at hp ⊢
        exact ⟨hp.2, rfl, rfl⟩
      · intro p₁ hp₁ p₂ hp₂ hEq
        exact Prod.ext
          (eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.fst hEq)).2)
          (eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.snd hEq)).2)
      · intro edge hedge
        rw [Finset.mem_filter] at hedge
        obtain ⟨hEdge, hA, hB⟩ := hedge
        obtain ⟨⟨a, r⟩, ⟨b, c⟩⟩ := edge
        simp only at hA hB
        subst a
        subst b
        exact ⟨(r, c), by simp [hEdge], rfl⟩
    rw [hcell]
    exact congrFun (congrFun S.2 e.1.1) e.1.2
  · exact matchingDemandPhysicalCellEdgeToLocal_injective e

/-- Reverse map from the exact physical fibre to the product of local one-cell
matchings. -/
def matchingDemandPhysicalFibreToCellDecoration
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → Nat) (row : A → Nat) (col : B → Nat) :
    {S : UnlabelledTypedSkeleton row col // S.typeTable = demand} →
      MatchingDemandCellDecoration demand row col := fun S e =>
  ⟨matchingDemandPhysicalCellLocalSkeleton S e,
    matchingDemandPhysicalCellLocalSkeleton_typeTable S e⟩

/-- Mapping a pulled-back local edge forward recovers the original physical
edge. -/
theorem matchingDemandPhysicalEdge_local_roundtrip
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → Nat} {row : A → Nat} {col : B → Nat}
    (S : {S : UnlabelledTypedSkeleton row col // S.typeTable = demand})
    (e : ↥(positiveDemandSupport demand))
    (p : Fin (row e.1.1) × Fin (col e.1.2)) :
    matchingDemandPhysicalEdgeOfLocalEdge e
        (matchingDemandPhysicalCellEdgeToLocal e p) =
      ((⟨e.1.1, p.1⟩, ⟨e.1.2, p.2⟩) :
        RowStub row × ColumnStub col) := by
  rfl

/-- Forward after reverse is the identity on the global physical skeleton
fibre. -/
theorem matchingDemandCellDecorationToPhysicalFibre_rightInverse
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → Nat) (row : A → Nat) (col : B → Nat)
    (hmatching : IsBipartiteMatching (positiveDemandSupport demand)) :
    Function.RightInverse
      (matchingDemandPhysicalFibreToCellDecoration demand row col)
      (matchingDemandCellDecorationToPhysicalFibre demand row col hmatching) := by
  intro S
  apply Subtype.ext
  apply UnlabelledTypedSkeleton.ext
  ext z
  constructor
  · intro hz
    simp only [matchingDemandCellDecorationToPhysicalFibre,
      matchingDemandDecoratedPhysicalSkeleton,
      matchingDemandDecoratedPhysicalEdges, Finset.mem_biUnion,
      Finset.mem_attach, true_and, Finset.mem_image] at hz
    obtain ⟨e, p, hp, rfl⟩ := hz
    change p ∈ (matchingDemandPhysicalCellLocalSkeleton S e).edges at hp
    rw [matchingDemandPhysicalCellLocalSkeleton, Finset.mem_image] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rw [matchingDemandPhysicalEdge_local_roundtrip]
    simpa [UnlabelledTypedSkeleton.cellEdges] using hq
  · intro hz
    rcases z with ⟨⟨a, r⟩, ⟨b, c⟩⟩
    have hcellpos : demand a b ≠ 0 := by
      have htypepos : S.1.typeTable a b ≠ 0 :=
        (S.1.typeTable_ne_zero_iff_exists_physical_edge a b).2
          ⟨((⟨a, r⟩, ⟨b, c⟩) : RowStub row × ColumnStub col), hz, rfl, rfl⟩
      simpa [S.2] using htypepos
    let e : ↥(positiveDemandSupport demand) :=
      ⟨(a, b), by simp [positiveDemandSupport, hcellpos]⟩
    let q : Fin (row a) × Fin (col b) := (r, c)
    have hq : q ∈ S.1.cellEdges a b := by
      simp [q, UnlabelledTypedSkeleton.cellEdges, hz]
    let p := matchingDemandPhysicalCellEdgeToLocal e q
    have hp : p ∈ (matchingDemandPhysicalCellLocalSkeleton S e).edges := by
      rw [matchingDemandPhysicalCellLocalSkeleton, Finset.mem_image]
      exact ⟨q, hq, rfl⟩
    simp only [matchingDemandCellDecorationToPhysicalFibre,
      matchingDemandDecoratedPhysicalSkeleton,
      matchingDemandDecoratedPhysicalEdges, Finset.mem_biUnion,
      Finset.mem_attach, true_and]
    refine ⟨e, Finset.mem_image.mpr ⟨p, hp, ?_⟩⟩
    rfl

/-- Reverse after forward is the identity on local cell decorations. -/
theorem matchingDemandCellDecorationToPhysicalFibre_leftInverse
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → Nat) (row : A → Nat) (col : B → Nat)
    (hmatching : IsBipartiteMatching (positiveDemandSupport demand)) :
    Function.LeftInverse
      (matchingDemandPhysicalFibreToCellDecoration demand row col)
      (matchingDemandCellDecorationToPhysicalFibre demand row col hmatching) := by
  intro D
  apply matchingDemandCellDecorationToPhysicalFibre_injective
    demand row col hmatching
  exact matchingDemandCellDecorationToPhysicalFibre_rightInverse
    demand row col hmatching
      (matchingDemandCellDecorationToPhysicalFibre demand row col hmatching D)

/-- Exact finite equivalence between the global physical skeleton fibre and the
product of its positive-cell partial matching fibres. -/
def matchingDemandCellDecorationEquivPhysicalFibre
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → Nat) (row : A → Nat) (col : B → Nat)
    (hmatching : IsBipartiteMatching (positiveDemandSupport demand)) :
    MatchingDemandCellDecoration demand row col ≃
      {S : UnlabelledTypedSkeleton row col // S.typeTable = demand} where
  toFun := matchingDemandCellDecorationToPhysicalFibre demand row col hmatching
  invFun := matchingDemandPhysicalFibreToCellDecoration demand row col
  left_inv := matchingDemandCellDecorationToPhysicalFibre_leftInverse
    demand row col hmatching
  right_inv := matchingDemandCellDecorationToPhysicalFibre_rightInverse
    demand row col hmatching

#print axioms matchingDemandDecoratedPhysicalSkeleton_typeTable
#print axioms matchingDemandCellDecorationToPhysicalFibre_injective
#print axioms matchingDemandPhysicalCellLocalSkeleton_typeTable
#print axioms matchingDemandCellDecorationToPhysicalFibre_rightInverse
#print axioms matchingDemandCellDecorationToPhysicalFibre_leftInverse

end

end Erdos625
