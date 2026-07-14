import Erdos625.StubAllocationTools

/-!
# Prescribed cells in a bipartite configuration model

This module formalizes the finite numerator count used in Lemma 6.2 and
equation (6.8).  It deliberately stops before introducing a probability
measure: the incidence of a fixed partial matching and the union-bound step
remain separate obligations.
-/

namespace Erdos625

open scoped BigOperators

/-- A witness for prescribed cell demands consists of disjoint row-stub
selections, disjoint column-stub selections, and a bijection pairing the two
selected sets inside every cell. -/
def PrescribedDemandWitness
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) :=
  Σ rowAllocation : ∀ a, StubAllocation (row a) (demand a),
    Σ colAllocation : ∀ b, StubAllocation (col b) (fun a ↦ demand a b),
      ∀ a b,
        (↑((rowAllocation a).1 b)) ≃ (↑((colAllocation b).1 a))

instance instFinitePrescribedDemandWitness
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) :
    Finite (PrescribedDemandWitness demand row col) := by
  unfold PrescribedDemandWitness
  infer_instance

noncomputable instance instFintypePrescribedDemandWitness
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) :
    Fintype (PrescribedDemandWitness demand row col) :=
  Fintype.ofFinite _

/-- Exact cross-multiplied numerator count from Lemma 6.2.  The theorem is
total: if a row or column demand is infeasible, the corresponding descending
factorial and the witness cardinal both vanish. -/
theorem card_prescribedDemandWitness_mul_factorials
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) :
    Fintype.card (PrescribedDemandWitness demand row col) *
        Finset.univ.prod
          (fun a ↦ Finset.univ.prod (fun b ↦ (demand a b).factorial)) =
      (Finset.univ.prod
          (fun a ↦ (row a).descFactorial (Finset.univ.sum (demand a)))) *
      (Finset.univ.prod
          (fun b ↦
            (col b).descFactorial
              (Finset.univ.sum (fun a ↦ demand a b)))) := by
  have hcard :
      ∀ (rowAllocation : ∀ a, StubAllocation (row a) (demand a))
        (colAllocation : ∀ b, StubAllocation (col b) (fun a ↦ demand a b)),
        Fintype.card
            (∀ a b,
              (↑((rowAllocation a).1 b)) ≃
                (↑((colAllocation b).1 a))) =
          Finset.univ.prod
            (fun a ↦ Finset.univ.prod (fun b ↦ (demand a b).factorial)) := by
    intro rowAllocation colAllocation
    rw [Fintype.card_pi]
    apply Finset.prod_congr rfl
    intro a _
    rw [Fintype.card_pi]
    apply Finset.prod_congr rfl
    intro b _
    let e : (↑((rowAllocation a).1 b)) ≃
        (↑((colAllocation b).1 a)) :=
      Fintype.equivOfCardEq (by
        simp [(rowAllocation a).2.1 b, (colAllocation b).2.1 a])
    rw [Fintype.card_equiv e]
    simp [(rowAllocation a).2.1 b]
  have hwitness :
      Fintype.card (PrescribedDemandWitness demand row col) =
        ∑ rowAllocation : (∀ a, StubAllocation (row a) (demand a)),
          ∑ colAllocation : (∀ b, StubAllocation (col b) (fun a ↦ demand a b)),
            Finset.univ.prod
              (fun a ↦ Finset.univ.prod
                (fun b ↦ (demand a b).factorial)) := by
    let E : PrescribedDemandWitness demand row col ≃
        (Σ rowAllocation : (∀ a, StubAllocation (row a) (demand a)),
          Σ colAllocation : (∀ b,
              StubAllocation (col b) (fun a ↦ demand a b)),
            ∀ a b,
              (↑((rowAllocation a).1 b)) ≃
                (↑((colAllocation b).1 a))) := Equiv.refl _
    rw [Fintype.card_congr E]
    rw [Fintype.card_sigma]
    apply Finset.sum_congr rfl
    intro rowAllocation _
    rw [Fintype.card_sigma]
    exact Finset.sum_congr rfl (fun colAllocation _ ↦
      hcard rowAllocation colAllocation)
  convert congr_arg₂ (· * ·)
      (Finset.prod_congr rfl (fun a _ ↦
        card_stubAllocation_mul_factorials (row a) (demand a)))
      (Finset.prod_congr rfl (fun b _ ↦
        card_stubAllocation_mul_factorials (col b) (fun a ↦ demand a b))) using 1
  rw [hwitness]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_pi, Finset.prod_mul_distrib]
  rw [Finset.prod_comm]
  ac_rfl

end Erdos625
