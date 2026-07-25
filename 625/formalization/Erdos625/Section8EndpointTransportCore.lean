import Erdos625.Section8EndpointGlobalTransport
import Erdos625.Section8EndpointLocalCellFactor
import Mathlib.Tactic

/-!
# Section VIII: square-root-free endpoint transportation core

This module isolates the exact finite algebra behind manuscript Lemma 8.1.
The displayed geometric-mean estimate contains square roots and several
factorial quotients.  Before introducing those divisions, its load-bearing
content can be written as a denominator-free squared inequality.

The module proves:

* the exact local cell identity relating one endpoint factor to the two
  diagonal endpoint factors;
* the corresponding product identity over an arbitrary four-type endpoint
  table;
* the global falling-factorial transport in `ENNReal`;
* their combined square-root-free transportation inequality.

No asymptotic estimate for `Q_ij`, margin summation, near-cell decoration, or
Section VIII skeleton bound is asserted here.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- The denominator-free local transport factor
`(t)_d 2^(d s + choose(d,2))` for an endpoint cell. -/
def fourEndpointLocalTransportDen
    (alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4) : ENNReal :=
  ((fourEndpointUpperSize alpha hAlpha i j).descFactorial
      (fourEndpointDistance i j) : ENNReal) *
    (2 : ENNReal) ^
      (fourEndpointDistance i j * fourEndpointLowerSize alpha hAlpha i j +
        (fourEndpointDistance i j).choose 2)

/-- The square of the local binomial choice in the endpoint comparison. -/
def fourEndpointLocalChooseSquare
    (alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4) : ENNReal :=
  (Nat.choose (fourEndpointUpperSize alpha hAlpha i j)
    (fourEndpointDistance i j) : ENNReal) ^ 2

/-- Product of the local transport denominators over a four-type table. -/
def fourEndpointLocalTransportDenProduct
    (alpha : Nat) (hAlpha : 5 < alpha) (L : FourEndpointFullTable) : ENNReal :=
  ∏ i, ∏ j, (fourEndpointLocalTransportDen alpha hAlpha i j) ^ L.toFun i j

/-- Product of the squared local binomial choices over a four-type table. -/
def fourEndpointLocalChooseSquareProduct
    (alpha : Nat) (hAlpha : 5 < alpha) (L : FourEndpointFullTable) : ENNReal :=
  ∏ i, ∏ j, (fourEndpointLocalChooseSquare alpha hAlpha i j) ^ L.toFun i j

/-- Exact square-root-free local identity behind the `Q_ij` factor in (8.8). -/
theorem fourEndpointLocalCellFactor_sq_mul_transportDen
    (alpha : Nat) (hAlpha : 5 < alpha) (hHigh : 8 < alpha)
    (i j : Fin 4) :
    fourEndpointLocalCellFactor alpha hAlpha i j ^ 2 *
        fourEndpointLocalTransportDen alpha hAlpha i j =
      fourEndpointSizeDiagonalFactor (fourEndpointSize alpha hAlpha i) *
        fourEndpointSizeDiagonalFactor (fourEndpointSize alpha hAlpha j) *
          fourEndpointLocalChooseSquare alpha hAlpha i j := by
  have hle (x y : Fin 4)
      (hxy : fourEndpointSize alpha hAlpha x ≤
        fourEndpointSize alpha hAlpha y) :
      fourEndpointLocalCellFactor alpha hAlpha x y ^ 2 *
          fourEndpointLocalTransportDen alpha hAlpha x y =
        fourEndpointSizeDiagonalFactor (fourEndpointSize alpha hAlpha x) *
          fourEndpointSizeDiagonalFactor (fourEndpointSize alpha hAlpha y) *
            fourEndpointLocalChooseSquare alpha hAlpha x y := by
    rw [fourEndpointLocalCellFactor_eq_lowerDiagonal_mul_choose]
    unfold fourEndpointLocalTransportDen fourEndpointLocalChooseSquare
      fourEndpointLowerSize fourEndpointUpperSize
    rw [min_eq_left hxy, max_eq_right hxy]
    rw [fourEndpointSizeDiagonalFactor_ratio alpha hAlpha hHigh x y hxy]
    ring
  by_cases hij : fourEndpointSize alpha hAlpha i ≤
      fourEndpointSize alpha hAlpha j
  · exact hle i j hij
  · have hji : fourEndpointSize alpha hAlpha j ≤
        fourEndpointSize alpha hAlpha i := le_of_not_ge hij
    have h := hle j i hji
    simpa [fourEndpointLocalCellFactor, fourEndpointOverlapSize,
      fourEndpointLocalTransportDen, fourEndpointLocalChooseSquare,
      fourEndpointLowerSize, fourEndpointUpperSize, fourEndpointDistance,
      Nat.dist_comm, min_comm, max_comm, mul_comm, mul_left_comm, mul_assoc] using h

/-- The local identities multiply exactly over every cell of a four-type
endpoint table.  The row and column diagonal products appear with the literal
endpoint margins. -/
theorem fourEndpointLocalProduct_sq_mul_transportDenProduct
    (alpha : Nat) (hAlpha : 5 < alpha) (hHigh : 8 < alpha)
    (L : FourEndpointFullTable) :
    fourEndpointLocalProduct alpha hAlpha L ^ 2 *
        fourEndpointLocalTransportDenProduct alpha hAlpha L =
      fourEndpointDiagonalLocalProduct alpha hAlpha
          (fun i => fourEndpointRowMargin L i) *
        fourEndpointDiagonalLocalProduct alpha hAlpha
          (fun j => fourEndpointColumnMargin L j) *
        fourEndpointLocalChooseSquareProduct alpha hAlpha L := by
  have hsq :
      (∏ i, ∏ j,
          (fourEndpointLocalCellFactor alpha hAlpha i j) ^ L.toFun i j) ^ 2 =
        ∏ i, ∏ j,
          ((fourEndpointLocalCellFactor alpha hAlpha i j) ^ 2) ^ L.toFun i j := by
    calc
      (∏ i, ∏ j,
          (fourEndpointLocalCellFactor alpha hAlpha i j) ^ L.toFun i j) ^ 2 =
        ∏ i, (∏ j,
          (fourEndpointLocalCellFactor alpha hAlpha i j) ^ L.toFun i j) ^ 2 :=
        Finset.prod_pow Finset.univ 2 (fun i =>
          ∏ j, (fourEndpointLocalCellFactor alpha hAlpha i j) ^ L.toFun i j)
      _ = ∏ i, ∏ j,
          ((fourEndpointLocalCellFactor alpha hAlpha i j) ^ L.toFun i j) ^ 2 := by
        apply Finset.prod_congr rfl
        intro i _
        exact Finset.prod_pow Finset.univ 2 (fun j =>
          (fourEndpointLocalCellFactor alpha hAlpha i j) ^ L.toFun i j)
      _ = ∏ i, ∏ j,
          ((fourEndpointLocalCellFactor alpha hAlpha i j) ^ 2) ^ L.toFun i j := by
        apply Finset.prod_congr rfl
        intro i _
        apply Finset.prod_congr rfl
        intro j _
        simp only [← pow_mul, Nat.mul_comm]
  have hrow :
      (∏ i, ∏ j,
          (fourEndpointSizeDiagonalFactor
            (fourEndpointSize alpha hAlpha i)) ^ L.toFun i j) =
        fourEndpointDiagonalLocalProduct alpha hAlpha
          (fun i => fourEndpointRowMargin L i) := by
    unfold fourEndpointDiagonalLocalProduct
    apply Finset.prod_congr rfl
    intro i _
    simpa [fourEndpointRowMargin, fourEndpointDiagonalLocalFactor,
      fourEndpointSizeDiagonalFactor] using
      (Finset.prod_pow_eq_pow_sum Finset.univ (L.toFun i)
        (fourEndpointSizeDiagonalFactor
          (fourEndpointSize alpha hAlpha i)))
  have hcol :
      (∏ i, ∏ j,
          (fourEndpointSizeDiagonalFactor
            (fourEndpointSize alpha hAlpha j)) ^ L.toFun i j) =
        fourEndpointDiagonalLocalProduct alpha hAlpha
          (fun j => fourEndpointColumnMargin L j) := by
    unfold fourEndpointDiagonalLocalProduct
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro j _
    simpa [fourEndpointColumnMargin, fourEndpointDiagonalLocalFactor,
      fourEndpointSizeDiagonalFactor] using
      (Finset.prod_pow_eq_pow_sum Finset.univ
        (fun i => L.toFun i j)
        (fourEndpointSizeDiagonalFactor
          (fourEndpointSize alpha hAlpha j)))
  unfold fourEndpointLocalProduct fourEndpointLocalTransportDenProduct
    fourEndpointLocalChooseSquareProduct
  calc
    (∏ i, ∏ j,
        (fourEndpointLocalCellFactor alpha hAlpha i j) ^ L.toFun i j) ^ 2 *
        (∏ i, ∏ j,
          (fourEndpointLocalTransportDen alpha hAlpha i j) ^ L.toFun i j) =
      ∏ i, ∏ j,
        ((fourEndpointLocalCellFactor alpha hAlpha i j) ^ 2 *
          fourEndpointLocalTransportDen alpha hAlpha i j) ^ L.toFun i j := by
        rw [hsq, ← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro i _
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro j _
        rw [mul_pow]
    _ = ∏ i, ∏ j,
        (fourEndpointSizeDiagonalFactor (fourEndpointSize alpha hAlpha i) *
          fourEndpointSizeDiagonalFactor (fourEndpointSize alpha hAlpha j) *
          fourEndpointLocalChooseSquare alpha hAlpha i j) ^ L.toFun i j := by
        apply Finset.prod_congr rfl
        intro i _
        apply Finset.prod_congr rfl
        intro j _
        rw [fourEndpointLocalCellFactor_sq_mul_transportDen
          alpha hAlpha hHigh i j]
    _ = (∏ i, ∏ j,
          (fourEndpointSizeDiagonalFactor
            (fourEndpointSize alpha hAlpha i)) ^ L.toFun i j) *
        (∏ i, ∏ j,
          (fourEndpointSizeDiagonalFactor
            (fourEndpointSize alpha hAlpha j)) ^ L.toFun i j) *
        (∏ i, ∏ j,
          (fourEndpointLocalChooseSquare alpha hAlpha i j) ^ L.toFun i j) := by
        simp only [mul_pow, Finset.prod_mul_distrib, mul_assoc]
    _ = fourEndpointDiagonalLocalProduct alpha hAlpha
          (fun i => fourEndpointRowMargin L i) *
        fourEndpointDiagonalLocalProduct alpha hAlpha
          (fun j => fourEndpointColumnMargin L j) *
        (∏ i, ∏ j,
          (fourEndpointLocalChooseSquare alpha hAlpha i j) ^ L.toFun i j) := by
        rw [hrow, hcol]

/-- `ENNReal` form of the global falling-factorial transport (8.12). -/
theorem fourEndpoint_global_transport_ennreal
    (n alpha : Nat) (hAlpha : 5 < alpha) (L : FourEndpointFullTable) :
    (n.descFactorial (fourEndpointRowMass alpha hAlpha L) : ENNReal) *
        (n.descFactorial (fourEndpointColumnMass alpha hAlpha L) : ENNReal) ≤
      ((n.descFactorial (fourEndpointJ alpha hAlpha L) : ENNReal) ^ 2) *
        (n + 1 : ENNReal) ^ fourEndpointDisplacement L := by
  exact_mod_cast fourEndpoint_global_transport n alpha hAlpha L

/-- Combined denominator-free squared form of the endpoint transportation
comparison.  This is the finite algebraic core of manuscript (8.8), before
introducing square roots or cancelling positive factorial denominators. -/
theorem fourEndpoint_squareFree_transport
    (n alpha : Nat) (hAlpha : 5 < alpha) (hHigh : 8 < alpha)
    (L : FourEndpointFullTable) :
    ((n.descFactorial (fourEndpointRowMass alpha hAlpha L) : ENNReal) *
      (n.descFactorial (fourEndpointColumnMass alpha hAlpha L) : ENNReal)) *
      (fourEndpointLocalProduct alpha hAlpha L ^ 2 *
        fourEndpointLocalTransportDenProduct alpha hAlpha L) ≤
    (((n.descFactorial (fourEndpointJ alpha hAlpha L) : ENNReal) ^ 2) *
      (n + 1 : ENNReal) ^ fourEndpointDisplacement L) *
      (fourEndpointDiagonalLocalProduct alpha hAlpha
          (fun i => fourEndpointRowMargin L i) *
        fourEndpointDiagonalLocalProduct alpha hAlpha
          (fun j => fourEndpointColumnMargin L j) *
        fourEndpointLocalChooseSquareProduct alpha hAlpha L) := by
  calc
    ((n.descFactorial (fourEndpointRowMass alpha hAlpha L) : ENNReal) *
        (n.descFactorial (fourEndpointColumnMass alpha hAlpha L) : ENNReal)) *
        (fourEndpointLocalProduct alpha hAlpha L ^ 2 *
          fourEndpointLocalTransportDenProduct alpha hAlpha L) ≤
      (((n.descFactorial (fourEndpointJ alpha hAlpha L) : ENNReal) ^ 2) *
        (n + 1 : ENNReal) ^ fourEndpointDisplacement L) *
        (fourEndpointLocalProduct alpha hAlpha L ^ 2 *
          fourEndpointLocalTransportDenProduct alpha hAlpha L) := by
      simpa [mul_comm] using
        (mul_le_mul_right
          (fourEndpoint_global_transport_ennreal n alpha hAlpha L)
          (fourEndpointLocalProduct alpha hAlpha L ^ 2 *
            fourEndpointLocalTransportDenProduct alpha hAlpha L))
    _ = (((n.descFactorial (fourEndpointJ alpha hAlpha L) : ENNReal) ^ 2) *
        (n + 1 : ENNReal) ^ fourEndpointDisplacement L) *
      (fourEndpointDiagonalLocalProduct alpha hAlpha
          (fun i => fourEndpointRowMargin L i) *
        fourEndpointDiagonalLocalProduct alpha hAlpha
          (fun j => fourEndpointColumnMargin L j) *
        fourEndpointLocalChooseSquareProduct alpha hAlpha L) := by
      rw [fourEndpointLocalProduct_sq_mul_transportDenProduct
        alpha hAlpha hHigh L]

#print axioms fourEndpointLocalCellFactor_sq_mul_transportDen
#print axioms fourEndpointLocalProduct_sq_mul_transportDenProduct
#print axioms fourEndpoint_global_transport_ennreal
#print axioms fourEndpoint_squareFree_transport

end

end Erdos625
