import Erdos625.Section9ActualResidualENNRealPolymerBridge
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-!
# Section IX: actual-residual `ENNReal` exponential endpoint

This isolated module turns the finite `ENNReal` polymer product into an
extended-real exponential bound.  Writing the exponent in `EReal` is
intentional: it remains meaningful when a finite polymer weight is `∞`.

It is a finite algebraic endpoint only.  It does not identify the conditioned
residual law, connect the weights to `residualQ`, encode cycles as walks, or
prove a Section IX probability estimate.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

local instance fintypeActualResidualEvenEdgeFamilyENNRealExp
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (cellCount : A → B → ℕ) (M : Finset (A × B)) :
    Fintype (ActualResidualEvenEdgeFamily cellCount
      (fun a b => (a, b) ∈ M)) := by
  letI : Finite (ActualResidualEvenEdgeFamily cellCount
      (fun a b => (a, b) ∈ M)) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _
/-- The elementary finite-or-infinite `ENNReal` exponential estimate. -/
theorem ennreal_one_add_le_ereal_exp (x : ENNReal) :
    1 + x ≤ EReal.exp (x : EReal) := by
  by_cases hx : x = ∞
  · simp [hx]
  calc
    1 + x = ENNReal.ofReal (1 + x.toReal) := by
      rw [ENNReal.ofReal_add zero_le_one ENNReal.toReal_nonneg,
        ENNReal.ofReal_one, ENNReal.ofReal_toReal hx]
    _ ≤ ENNReal.ofReal (Real.exp x.toReal) :=
      ENNReal.ofReal_le_ofReal
        (by simpa [add_comm] using Real.add_one_le_exp x.toReal)
    _ = EReal.exp (x : EReal) := by
      rw [← EReal.coe_ennreal_toReal hx, EReal.exp_coe]

/-- A finite `ENNReal` polymer product is bounded by the corresponding
extended-real exponential, including the case of an infinite weight. -/
theorem ennreal_polymer_product_le_ereal_exp_sum
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → ENNReal) :
    (∏ i ∈ s, (1 + w i)) ≤
      EReal.exp ((↑(∑ i ∈ s, w i) : ENNReal) : EReal) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        EReal.coe_ennreal_add, EReal.exp_add]
      exact mul_le_mul' (ennreal_one_add_le_ereal_exp (w a)) ih

/-- The actual residual even-edge family is bounded by the extended-real
exponential of the total finite polymer weight. -/
theorem sum_actualResidualEvenEdgeFamily_ennreal_weight_le_polymer_exp
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (cellCount : A → B → ℕ) (M : Finset (A × B))
    (q : A → B → ENNReal)
    (_hM : IsBipartiteMatching M) :
    (∑ F : ActualResidualEvenEdgeFamily cellCount
        (fun a b => (a, b) ∈ M),
      edgeWeightOutsideENN q M F.1) ≤
      EReal.exp ((↑(∑ C ∈ simpleBipartiteCycles A B,
        edgeWeightOutsideENN q M C) : ENNReal) : EReal) := by
  calc
    (∑ F : ActualResidualEvenEdgeFamily cellCount
        (fun a b => (a, b) ∈ M),
      edgeWeightOutsideENN q M F.1) ≤
        ∏ C ∈ simpleBipartiteCycles A B,
          (1 + edgeWeightOutsideENN q M C) :=
      sum_actualResidualEvenEdgeFamily_ennreal_weight_le_polymer_product
        cellCount M q _hM
    _ ≤ EReal.exp ((↑(∑ C ∈ simpleBipartiteCycles A B,
        edgeWeightOutsideENN q M C) : ENNReal) : EReal) :=
      ennreal_polymer_product_le_ereal_exp_sum
        (simpleBipartiteCycles A B)
        (fun C => edgeWeightOutsideENN q M C)

#print axioms ennreal_one_add_le_ereal_exp
#print axioms ennreal_polymer_product_le_ereal_exp_sum
#print axioms sum_actualResidualEvenEdgeFamily_ennreal_weight_le_polymer_exp

end

end Erdos625
