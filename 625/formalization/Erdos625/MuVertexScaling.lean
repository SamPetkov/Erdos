import Erdos625.Phase

namespace Erdos625

noncomputable section

set_option autoImplicit false

/-!
# Finite vertex-count scaling for the first moment

This module isolates the finite binomial comparison needed before the
canonical full-corner activity can be estimated.  It supplies the decisive
power of the vertex-count ratio without importing any phase asymptotic,
midpoint rounding, partial-diagonal weight, or signed first-moment estimate.
-/

/-- Falling-factorial comparison: `(v)_s * n ^ s ≤ (n)_s * v ^ s` for `v ≤ n`,
proved factorwise from `(v - i) * n ≤ (n - i) * v`. -/
private lemma descFactorial_mul_pow_le_of_le {n v s : Nat} (hvn : v ≤ n) :
    v.descFactorial s * n ^ s ≤ n.descFactorial s * v ^ s := by
  have hpn : n ^ s = ∏ _i ∈ Finset.range s, n := by simp
  have hpv : v ^ s = ∏ _i ∈ Finset.range s, v := by simp
  rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range, hpn, hpv,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod' ?_
  intro i _
  have h1 : (v - i) * n = v * n - i * n := by rw [Nat.sub_mul]
  have h2 : (n - i) * v = v * n - i * v := by rw [Nat.sub_mul]; ring_nf
  rw [h1, h2]
  exact Nat.sub_le_sub_left (Nat.mul_le_mul (le_refl i) hvn) _

/-- The binomial form of the falling-factorial comparison, obtained by
cancelling the common factor `s !`. -/
private lemma choose_mul_pow_le_of_le {n v s : Nat} (_hsv : s ≤ v) (hvn : v ≤ n) :
    v.choose s * n ^ s ≤ n.choose s * v ^ s := by
  have h := descFactorial_mul_pow_le_of_le (s := s) hvn
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose] at h
  have h' : s.factorial * (v.choose s * n ^ s) ≤ s.factorial * (n.choose s * v ^ s) := by
    calc s.factorial * (v.choose s * n ^ s) = s.factorial * v.choose s * n ^ s := by ring
      _ ≤ s.factorial * n.choose s * v ^ s := h
      _ = s.factorial * (n.choose s * v ^ s) := by ring
  exact Nat.le_of_mul_le_mul_left h' (Nat.factorial_pos s)

/-- Shrinking the available vertex set from `n` to `v` costs at most the
`s`-th power of `v / n` in the independent-set first moment.

This is the finite falling-factorial comparison behind the manuscript's
full-corner activity estimate. -/
theorem mu_le_mu_mul_vertex_ratio_pow
    {n v s : Nat}
    (hn : 0 < n)
    (hsv : s ≤ v)
    (hvn : v ≤ n) :
    mu v s ≤
      mu n s * ((v : Real) / (n : Real)) ^ s := by
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hpow : (0 : Real) < (n : Real) ^ s := pow_pos hnR s
  have key : (v.choose s : Real) * (n : Real) ^ s ≤ (n.choose s : Real) * (v : Real) ^ s := by
    exact_mod_cast choose_mul_pow_le_of_le (s := s) hsv hvn
  have main : (v.choose s : Real) ≤ (n.choose s : Real) * ((v : Real) / (n : Real)) ^ s := by
    rw [div_pow, ← mul_div_assoc, le_div_iff₀ hpow]
    exact key
  have hc : (0 : Real) ≤ ((2 : Real) ^ (s.choose 2))⁻¹ := by positivity
  unfold mu
  calc (v.choose s : Real) * ((2 : Real) ^ (s.choose 2))⁻¹
      ≤ ((n.choose s : Real) * ((v : Real) / (n : Real)) ^ s) *
          ((2 : Real) ^ (s.choose 2))⁻¹ := mul_le_mul_of_nonneg_right main hc
    _ = (n.choose s : Real) * ((2 : Real) ^ (s.choose 2))⁻¹ *
          ((v : Real) / (n : Real)) ^ s := by ring

end

end Erdos625
