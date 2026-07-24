import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Graph invariants for Erdős Problem 625

This file defines cocolourings and the cochromatic number.  Empty colour
classes are permitted, so a cocolouring with `k` colours represents a
partition into at most `k` nonempty clique-or-independent parts.
-/

namespace Erdos625

universe u v

/-- A labelled simple graph on `n` vertices. -/
abbrev LabeledGraph (n : ℕ) := SimpleGraph (Fin n)

/-- The two allowed kinds of parts in a cocolouring. -/
inductive PartKind where
  | independent
  | clique
  deriving DecidableEq

/-- A colouring in which every colour class is independently declared to be
an independent set or a clique. -/
structure CoColoring {V : Type u} (G : SimpleGraph V) (κ : Type v) where
  color : V → κ
  kind : κ → PartKind
  valid : ∀ c,
    match kind c with
    | .independent => G.IsIndepSet {v | color v = c}
    | .clique => G.IsClique {v | color v = c}

namespace CoColoring

variable {V : Type u} {κ : Type v} {κ₂ : Type*} {G : SimpleGraph V}

/-- The vertices assigned a given cocolour. -/
def colorClass (C : CoColoring G κ) (c : κ) : Set V :=
  {v | C.color v = c}

theorem valid_independent (C : CoColoring G κ) {c : κ}
    (h : C.kind c = .independent) : G.IsIndepSet (C.colorClass c) := by
  simpa [colorClass, h] using C.valid c

theorem valid_clique (C : CoColoring G κ) {c : κ}
    (h : C.kind c = .clique) : G.IsClique (C.colorClass c) := by
  simpa [colorClass, h] using C.valid c

/-- Every proper colouring is a cocolouring whose parts are all independent. -/
def ofColoring (C : G.Coloring κ) : CoColoring G κ where
  color := fun v => C v
  kind := fun _ => .independent
  valid := fun c => by
    simpa [SimpleGraph.Coloring.colorClass] using C.isIndepSet_colorClass c

/-- Enlarge a palette by adding colours with empty (hence independent)
classes. -/
def addEmptyColors (C : CoColoring G κ) (κ₂ : Type*) :
    CoColoring G (Sum κ κ₂) where
  color := fun v => .inl (C.color v)
  kind := Sum.elim C.kind (fun _ => .independent)
  valid := by
    intro c
    cases c with
    | inl c => simpa using C.valid c
    | inr c => simp

/-- Rename the palette of a cocolouring along an equivalence. -/
noncomputable def relabel (C : CoColoring G κ) (e : κ ≃ κ₂) :
    CoColoring G κ₂ where
  color := fun v => e (C.color v)
  kind := fun c => C.kind (e.symm c)
  valid := by
    intro c
    cases hkind : C.kind (e.symm c) with
    | independent =>
        intro x hx y hy hxy
        have hx' : C.color x = e.symm c :=
          e.injective (by simpa using hx)
        have hy' : C.color y = e.symm c :=
          e.injective (by simpa using hy)
        exact (C.valid_independent hkind) hx' hy' hxy
    | clique =>
        intro x hx y hy hxy
        have hx' : C.color x = e.symm c :=
          e.injective (by simpa using hx)
        have hy' : C.color y = e.symm c :=
          e.injective (by simpa using hy)
        exact (C.valid_clique hkind) hx' hy' hxy

private noncomputable def sumInduceColor (W : Set V)
    (C₁ : CoColoring (G.induce W) κ)
    (C₂ : CoColoring (G.induce Wᶜ) κ₂) (v : V) : Sum κ κ₂ := by
  classical
  exact if hv : v ∈ W then .inl (C₁.color ⟨v, hv⟩)
  else .inr (C₂.color ⟨v, hv⟩)

/-- Glue cocolourings of a vertex set and its complement.  The two palettes
are kept disjoint, so no cross-edge condition is required. -/
noncomputable def sumInduce (W : Set V)
    (C₁ : CoColoring (G.induce W) κ)
    (C₂ : CoColoring (G.induce Wᶜ) κ₂) :
    CoColoring G (Sum κ κ₂) where
  color := sumInduceColor W C₁ C₂
  kind := Sum.elim C₁.kind C₂.kind
  valid := by
    intro c
    cases c with
    | inl c =>
        cases hkind : C₁.kind c with
        | independent =>
            simp only [Sum.elim_inl, hkind]
            intro x hx y hy hxy
            by_cases hxW : x ∈ W
            · by_cases hyW : y ∈ W
              · have hx' : C₁.color ⟨x, hxW⟩ = c := by
                  simpa [sumInduceColor, hxW] using hx
                have hy' : C₁.color ⟨y, hyW⟩ = c := by
                  simpa [sumInduceColor, hyW] using hy
                have hsub : (⟨x, hxW⟩ : W) ≠ ⟨y, hyW⟩ :=
                  fun h => hxy (congrArg Subtype.val h)
                exact (C₁.valid_independent hkind) hx' hy' hsub
              · simp [sumInduceColor, hyW] at hy
            · simp [sumInduceColor, hxW] at hx
        | clique =>
            simp only [Sum.elim_inl, hkind]
            intro x hx y hy hxy
            by_cases hxW : x ∈ W
            · by_cases hyW : y ∈ W
              · have hx' : C₁.color ⟨x, hxW⟩ = c := by
                  simpa [sumInduceColor, hxW] using hx
                have hy' : C₁.color ⟨y, hyW⟩ = c := by
                  simpa [sumInduceColor, hyW] using hy
                have hsub : (⟨x, hxW⟩ : W) ≠ ⟨y, hyW⟩ :=
                  fun h => hxy (congrArg Subtype.val h)
                exact (C₁.valid_clique hkind) hx' hy' hsub
              · simp [sumInduceColor, hyW] at hy
            · simp [sumInduceColor, hxW] at hx
    | inr c =>
        cases hkind : C₂.kind c with
        | independent =>
            simp only [Sum.elim_inr, hkind]
            intro x hx y hy hxy
            by_cases hxW : x ∈ W
            · simp [sumInduceColor, hxW] at hx
            · by_cases hyW : y ∈ W
              · simp [sumInduceColor, hyW] at hy
              · have hx' : C₂.color ⟨x, hxW⟩ = c := by
                  simpa [sumInduceColor, hxW] using hx
                have hy' : C₂.color ⟨y, hyW⟩ = c := by
                  simpa [sumInduceColor, hyW] using hy
                have hsub :
                    (⟨x, hxW⟩ : {v : V // v ∉ W}) ≠ ⟨y, hyW⟩ :=
                  fun h => hxy (congrArg Subtype.val h)
                exact (C₂.valid_independent hkind) hx' hy' hsub
        | clique =>
            simp only [Sum.elim_inr, hkind]
            intro x hx y hy hxy
            by_cases hxW : x ∈ W
            · simp [sumInduceColor, hxW] at hx
            · by_cases hyW : y ∈ W
              · simp [sumInduceColor, hyW] at hy
              · have hx' : C₂.color ⟨x, hxW⟩ = c := by
                  simpa [sumInduceColor, hxW] using hx
                have hy' : C₂.color ⟨y, hyW⟩ = c := by
                  simpa [sumInduceColor, hyW] using hy
                have hsub :
                    (⟨x, hxW⟩ : {v : V // v ∉ W}) ≠ ⟨y, hyW⟩ :=
                  fun h => hxy (congrArg Subtype.val h)
                exact (C₂.valid_clique hkind) hx' hy' hsub

end CoColoring

/-- A graph is cocolourable with at most `k` parts. -/
def CoColorable {V : Type u} (G : SimpleGraph V) (k : ℕ) : Prop :=
  Nonempty (CoColoring G (Fin k))

variable {V : Type u} {G : SimpleGraph V} {k : ℕ}

theorem coColorable_of_colorable (h : G.Colorable k) : CoColorable G k :=
  ⟨CoColoring.ofColoring h.some⟩

/-- Adding unused palette entries preserves cocolourability. -/
theorem coColorable_mono {ℓ : ℕ} (h : k ≤ ℓ) :
    CoColorable G k → CoColorable G ℓ := by
  rintro ⟨C⟩
  let e : Sum (Fin k) (Fin (ℓ - k)) ≃ Fin ℓ :=
    finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le h))
  exact ⟨CoColoring.relabel (C.addEmptyColors (Fin (ℓ - k))) e⟩

/-- Cocolourability concatenates across an induced set and its complement. -/
theorem coColorable_of_induce_and_compl {ℓ : ℕ} (W : Set V)
    (hW : CoColorable (G.induce W) k)
    (hWc : CoColorable (G.induce Wᶜ) ℓ) :
    CoColorable G (k + ℓ) :=
  ⟨CoColoring.relabel
    (CoColoring.sumInduce W hW.some hWc.some)
    finSumFinEquiv⟩

/-- A frequently used special case: the complement of the structured core
may be handled by an ordinary proper colouring. -/
theorem coColorable_of_induce_and_colorable_compl {ℓ : ℕ} (W : Set V)
    (hW : CoColorable (G.induce W) k)
    (hWc : (G.induce Wᶜ).Colorable ℓ) :
    CoColorable G (k + ℓ) :=
  coColorable_of_induce_and_compl W hW
    (coColorable_of_colorable hWc)

theorem coColorable_card [Fintype V] (G : SimpleGraph V) :
    CoColorable G (Fintype.card V) :=
  coColorable_of_colorable (SimpleGraph.colorable_of_fintype G)

theorem exists_coColorable [Fintype V] (G : SimpleGraph V) :
    ∃ k : ℕ, CoColorable G k :=
  ⟨Fintype.card V, coColorable_card G⟩

/-- The minimum number of clique-or-independent parts in a finite graph. -/
noncomputable def cochromaticNumber [Fintype V] (G : SimpleGraph V) : ℕ :=
  by
    classical
    exact Nat.find (exists_coColorable G)

theorem coColorable_cochromaticNumber [Fintype V] (G : SimpleGraph V) :
    CoColorable G (cochromaticNumber G) :=
  by
    classical
    exact Nat.find_spec (exists_coColorable G)

theorem cochromaticNumber_le_of_coColorable [Fintype V] (G : SimpleGraph V)
    (h : CoColorable G k) : cochromaticNumber G ≤ k :=
  by
    classical
    exact Nat.find_min' (exists_coColorable G) h

/-- Characterization of the minimum: `k` colours suffice exactly when the
cochromatic number is at most `k`. -/
theorem coColorable_iff_cochromaticNumber_le [Fintype V]
    (G : SimpleGraph V) :
    CoColorable G k ↔ cochromaticNumber G ≤ k := by
  constructor
  · exact cochromaticNumber_le_of_coColorable G
  · intro h
    exact coColorable_mono h (coColorable_cochromaticNumber G)

/-- The natural-valued chromatic number of a finite graph.  Mathlib's primary
definition takes values in `ℕ∞`; finite graphs are known to be colourable. -/
noncomputable def chromaticNumberNat [Fintype V] (G : SimpleGraph V) : ℕ :=
  ENat.toNat G.chromaticNumber

theorem colorable_chromaticNumberNat [Fintype V] (G : SimpleGraph V) :
    G.Colorable (chromaticNumberNat G) := by
  exact SimpleGraph.colorable_chromaticNumber_of_fintype G

/-- Every proper colouring is a cocolouring, hence `ζ(G) ≤ χ(G)`. -/
theorem cochromaticNumber_le_chromaticNumber [Fintype V] (G : SimpleGraph V) :
    cochromaticNumber G ≤ chromaticNumberNat G :=
  cochromaticNumber_le_of_coColorable G
    (coColorable_of_colorable (colorable_chromaticNumberNat G))

end Erdos625
