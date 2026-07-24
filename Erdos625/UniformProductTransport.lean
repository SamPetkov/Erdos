import Erdos625.UniformEquivTransport
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

/-!
# Uniform finite product projections

The uniform PMF on a nonempty finite Cartesian product has uniform coordinate
marginals.  This is a finite counting identity used to pass from an exact
uniform product representation to one standardized residual coordinate.
-/

namespace Erdos625

noncomputable section

/-- The second-coordinate marginal of the finite uniform PMF on a nonempty
product is the finite uniform PMF on that coordinate. -/
theorem uniformOfFintype_prod_map_snd
    {alpha beta : Type*}
    [Fintype alpha] [Fintype beta] [Nonempty alpha] [Nonempty beta] :
    (PMF.uniformOfFintype (alpha × beta)).map
        (fun p : alpha × beta => p.2) =
      PMF.uniformOfFintype beta := by
  classical
  ext b
  rw [PMF.map_apply, PMF.uniformOfFintype_apply, tsum_fintype]
  -- `rw` does not descend through the finite-sum binder, so expose the
  -- constant mass of the product uniform law explicitly before regrouping.
  simp_rw [PMF.uniformOfFintype_apply]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have halpha0 : (Fintype.card alpha : ENNReal) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have halphatop : (Fintype.card alpha : ENNReal) ≠ (⊤ : ENNReal) :=
    ENNReal.natCast_ne_top _
  rw [Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv (Or.inl halpha0) (Or.inl halphatop),
    ← mul_assoc, ENNReal.mul_inv_cancel halpha0 halphatop, one_mul]

#print axioms uniformOfFintype_prod_map_snd

end

end Erdos625
