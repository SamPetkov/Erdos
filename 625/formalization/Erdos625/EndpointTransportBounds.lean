import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

/-!
# Finite endpoint-transport bounds

This module isolates the descending-factorial arithmetic used when two
endpoint margins are transported to their common minimum.  If `J` is below
both margins and their total excess over `J` is `gap`, then each remaining
descending-factorial tail is bounded by a power of the ambient size.

The main theorem is total: no hypotheses such as `mr ≤ n` or `mc ≤ n` are
needed.  Mathlib's descending-factorial factorization remains valid in the
infeasible cases, where the appropriate factors vanish.
-/

namespace Erdos625

/-- The two excesses above the common minimum add up to the natural-number
absolute difference. -/
theorem sub_min_add_sub_min_eq_dist (mr mc : ℕ) :
    (mr - min mr mc) + (mc - min mr mc) = Nat.dist mr mc := by
  rcases le_total mr mc with h | h
  · rw [min_eq_left h, Nat.dist_eq_sub_of_le h]
    omega
  · rw [min_eq_right h, Nat.dist_eq_sub_of_le_right h]
    omega

/-- A sum is twice its smaller endpoint plus the natural-number absolute
difference of the endpoints. -/
theorem add_eq_two_mul_min_add_dist (mr mc : ℕ) :
    mr + mc = 2 * min mr mc + Nat.dist mr mc := by
  rcases le_total mr mc with h | h
  · rw [min_eq_left h, Nat.dist_eq_sub_of_le h]
    omega
  · rw [min_eq_right h, Nat.dist_eq_sub_of_le_right h]
    omega

/-- Cross-multiplied endpoint transport for descending factorials.  This is
slightly stronger than the manuscript-facing form: the loss is `n ^ gap`
rather than `(n + 1) ^ gap`. -/
theorem descFactorial_endpoint_transport
    {n J mr mc gap : ℕ}
    (hJr : J ≤ mr) (hJc : J ≤ mc)
    (hsum : mr + mc = 2 * J + gap) :
    n.descFactorial mr * n.descFactorial mc ≤
      (n.descFactorial J) ^ 2 * n ^ gap := by
  have hgap : (mr - J) + (mc - J) = gap := by omega
  have hr :
      (n - J).descFactorial (mr - J) ≤ n ^ (mr - J) := by
    exact (Nat.descFactorial_le_pow (n - J) (mr - J)).trans
      (Nat.pow_le_pow_left (Nat.sub_le n J) _)
  have hc :
      (n - J).descFactorial (mc - J) ≤ n ^ (mc - J) := by
    exact (Nat.descFactorial_le_pow (n - J) (mc - J)).trans
      (Nat.pow_le_pow_left (Nat.sub_le n J) _)
  have htail :
      (n - J).descFactorial (mr - J) *
          (n - J).descFactorial (mc - J) ≤
        n ^ gap := by
    calc
      (n - J).descFactorial (mr - J) *
            (n - J).descFactorial (mc - J) ≤
          n ^ (mr - J) * n ^ (mc - J) := Nat.mul_le_mul hr hc
      _ = n ^ ((mr - J) + (mc - J)) := (pow_add _ _ _).symm
      _ = n ^ gap := by rw [hgap]
  calc
    n.descFactorial mr * n.descFactorial mc =
        (n.descFactorial J) ^ 2 *
          ((n - J).descFactorial (mr - J) *
            (n - J).descFactorial (mc - J)) := by
      rw [← Nat.descFactorial_mul_descFactorial hJr,
        ← Nat.descFactorial_mul_descFactorial hJc]
      simp only [pow_two]
      ac_rfl
    _ ≤ (n.descFactorial J) ^ 2 * n ^ gap :=
      Nat.mul_le_mul_left _ htail

/-- Manuscript-facing endpoint transport with the convenient base `n + 1`. -/
theorem descFactorial_endpoint_transport_succ
    {n J mr mc gap : ℕ}
    (hJr : J ≤ mr) (hJc : J ≤ mc)
    (hsum : mr + mc = 2 * J + gap) :
    n.descFactorial mr * n.descFactorial mc ≤
      (n.descFactorial J) ^ 2 * (n + 1) ^ gap := by
  calc
    n.descFactorial mr * n.descFactorial mc ≤
        (n.descFactorial J) ^ 2 * n ^ gap :=
      descFactorial_endpoint_transport hJr hJc hsum
    _ ≤ (n.descFactorial J) ^ 2 * (n + 1) ^ gap :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ n) _)

/-- Endpoint transport instantiated at the smaller margin; the exponent is
the exact natural-number absolute difference. -/
theorem descFactorial_min_transport
    (n mr mc : ℕ) :
    n.descFactorial mr * n.descFactorial mc ≤
      (n.descFactorial (min mr mc)) ^ 2 * n ^ (Nat.dist mr mc) := by
  apply descFactorial_endpoint_transport (J := min mr mc)
  · exact min_le_left _ _
  · exact min_le_right _ _
  · exact add_eq_two_mul_min_add_dist mr mc

/-- `n + 1` version of `descFactorial_min_transport`. -/
theorem descFactorial_min_transport_succ
    (n mr mc : ℕ) :
    n.descFactorial mr * n.descFactorial mc ≤
      (n.descFactorial (min mr mc)) ^ 2 *
        (n + 1) ^ (Nat.dist mr mc) := by
  apply descFactorial_endpoint_transport_succ (J := min mr mc)
  · exact min_le_left _ _
  · exact min_le_right _ _
  · exact add_eq_two_mul_min_add_dist mr mc

end Erdos625
