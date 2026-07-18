import Erdos625.PartialDiagonalWeights
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

/-!
# Finite partial-diagonal decay and reindexing

This file supplies the finite bookkeeping bridge behind the empty-corner
part of Section VII.  It deliberately contains no asymptotic statement.

For a finite type of block types, `partialSubprofileBox k` is exactly the
finite box of vectors `ell` with `ell i <= k i`.  A coordinatewise
factorial majorant reindexes exactly into a product of one-dimensional
truncated exponential sums.  The final theorem then applies that purely
finite reindexing to `partialDiagonalWeight` under a supplied pointwise
majorant.

The exact recurrence from `PartialDiagonalWeights` is also converted into
one explicit one-step decay inequality.  Its hypotheses retain the vertex
mass feasibility and the required lower bound on `mu`; no phase window or
limit estimate is assumed here.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The finite box of genuine subprofiles of `k`. -/
def partialSubprofileBox (k : I -> Nat) : Finset (I -> Nat) :=
  Fintype.piFinset fun i => Finset.range (k i + 1)

@[simp] theorem mem_partialSubprofileBox {k ell : I -> Nat} :
    ell ∈ partialSubprofileBox k ↔ IsPartialSubprofile k ell := by
  simp [partialSubprofileBox, IsPartialSubprofile]

/-- The exact number of coordinatewise subprofiles. -/
@[simp] theorem card_partialSubprofileBox (k : I -> Nat) :
    (partialSubprofileBox k).card = ∏ i, (k i + 1) := by
  simp [partialSubprofileBox]

/-- The product of the one-coordinate factorial decay majorants. -/
def partialDiagonalFactorialMajorant
    (xi : I -> Real) (ell : I -> Nat) : Real :=
  ∏ i, xi i ^ ell i / ((ell i).factorial : Real)

private theorem partialDiagonalFactorialMajorant_prod_update_mul
    {M : Type*} [CommMonoid M]
    (f : I -> M) (i : I) (b : M) :
    (∏ j, Function.update f i (f i * b) j) = (∏ j, f j) * b := by
  rw [Finset.prod_update_of_mem (Finset.mem_univ i)]
  have hold := Finset.prod_update_of_mem (Finset.mem_univ i) f (f i)
  have hself : Function.update f i (f i) = f := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]
  rw [hself] at hold
  rw [hold]
  ac_rfl

/-- Updating one coordinate of the factorial majorant has exactly the
factor expected from the formal exponential series. -/
theorem partialDiagonalFactorialMajorant_increment
    (xi : I -> Real) (ell : I -> Nat) (i : I) :
    partialDiagonalFactorialMajorant xi (incrementProfile ell i) =
      partialDiagonalFactorialMajorant xi ell *
        (xi i / (ell i + 1 : Real)) := by
  let f : I -> Real := fun j =>
    xi j ^ ell j / ((ell j).factorial : Real)
  have hlocal :
      xi i ^ (ell i + 1) / ((ell i + 1).factorial : Real) =
        f i * (xi i / (ell i + 1 : Real)) := by
    dsimp [f]
    rw [pow_succ, Nat.factorial_succ]
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hfactorial : ((ell i).factorial : Real) ≠ 0 := by positivity
    have hsucc : (ell i + 1 : Real) ≠ 0 := by positivity
    field_simp
  have hfun :
      (fun j => xi j ^ incrementProfile ell i j /
        ((incrementProfile ell i j).factorial : Real)) =
        Function.update f i (f i * (xi i / (ell i + 1 : Real))) := by
    funext j
    by_cases hji : j = i
    · subst j
      simpa [incrementProfile] using hlocal
    · simp [incrementProfile, f, hji]
  rw [partialDiagonalFactorialMajorant,
    partialDiagonalFactorialMajorant, hfun,
      partialDiagonalFactorialMajorant_prod_update_mul]

/-- Any nonnegative-coordinate one-step factorial decay certificate can be
iterated over the whole finite subprofile box.  This is a finite induction on
the number of selected blocks; it has no limiting or phase hypothesis. -/
theorem pointwise_le_factorialMajorant_of_increment_decay
    (k : I -> Nat) (xi : I -> Real) (w : (I -> Nat) -> Real)
    (hxi : ∀ i, 0 ≤ xi i)
    (hzero : w (fun _ => 0) ≤ 1)
    (hstep : ∀ ell i, IsPartialSubprofile k ell -> ell i < k i ->
      w (incrementProfile ell i) ≤ w ell *
        (xi i / (ell i + 1 : Real))) :
    ∀ ell, IsPartialSubprofile k ell ->
      w ell ≤ partialDiagonalFactorialMajorant xi ell := by
  have hinduction : ∀ q : Nat, ∀ ell : I -> Nat,
      selectedBlockCount ell = q -> IsPartialSubprofile k ell ->
        w ell ≤ partialDiagonalFactorialMajorant xi ell := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
      intro ell hcount hprofile
      by_cases hq : q = 0
      · have hsumzero : ∑ j, ell j = 0 := by
          simpa [selectedBlockCount, hq] using hcount
        have hcoordinatezero : ∀ j, ell j = 0 := by
          intro j
          exact (Finset.sum_eq_zero_iff_of_nonneg
            (fun a _ => Nat.zero_le (ell a))).mp hsumzero j (Finset.mem_univ j)
        have hellzero : ell = fun _ => 0 := by
          funext j
          exact hcoordinatezero j
        rw [hellzero]
        simpa [partialDiagonalFactorialMajorant] using hzero
      · have hsumne : (∑ j, ell j) ≠ 0 := by
          intro hsumzero
          apply hq
          calc
            q = selectedBlockCount ell := hcount.symm
            _ = ∑ j, ell j := rfl
            _ = 0 := hsumzero
        obtain ⟨i, -, hine⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumne
        have hipos : 0 < ell i := Nat.pos_of_ne_zero hine
        have hone : 1 ≤ ell i := hipos
        let ell' : I -> Nat := Function.update ell i (ell i - 1)
        have hcoordinate : ell' i + 1 = ell i := by
          have hcoordinateRaw : ell i - 1 + 1 = ell i :=
            Nat.sub_add_cancel hone
          simpa only [ell', Function.update_self] using
            hcoordinateRaw
        have hcoordinateReal : (ell' i + 1 : Real) = ell i := by
          exact_mod_cast hcoordinate
        have hincrement : incrementProfile ell' i = ell := by
          funext j
          by_cases hji : j = i
          · subst j
            simpa [incrementProfile] using hcoordinate
          · simp [incrementProfile, ell', hji]
        have hprofile' : IsPartialSubprofile k ell' := by
          intro j
          by_cases hji : j = i
          · subst j
            simpa only [ell', Function.update_self] using
              (Nat.sub_le _ _).trans (hprofile i)
          · simpa [ell', hji] using hprofile j
        have hi' : ell' i < k i := by
          have hle : ell i ≤ k i := hprofile i
          have hlt : ell i - 1 < k i := by omega
          simpa only [ell', Function.update_self] using hlt
        have hcountIncrement := selectedBlockCount_increment ell' i
        rw [hincrement] at hcountIncrement
        have hcount' : selectedBlockCount ell' < q := by
          omega
        have hinduction' :=
          ih (selectedBlockCount ell') hcount' ell' rfl hprofile'
        have hstep' := hstep ell' i hprofile' hi'
        rw [hincrement, hcoordinateReal] at hstep'
        have hmajorantIncrement :=
          partialDiagonalFactorialMajorant_increment xi ell' i
        rw [hincrement, hcoordinateReal] at hmajorantIncrement
        have hfactorNonneg : 0 ≤ xi i / (ell i : Real) := by
          exact div_nonneg (hxi i) (by positivity)
        calc
          w ell ≤ w ell' * (xi i / (ell i : Real)) := hstep'
          _ ≤ partialDiagonalFactorialMajorant xi ell' *
              (xi i / (ell i : Real)) :=
            mul_le_mul_of_nonneg_right hinduction' hfactorNonneg
          _ = partialDiagonalFactorialMajorant xi ell :=
            hmajorantIncrement.symm
  intro ell hprofile
  exact hinduction (selectedBlockCount ell) ell rfl hprofile

/-- The same finite iteration, restricted to any region closed under deleting
one selected block.  This is the form used for a finite empty-corner cutoff:
the predicate can be `selectedVertexMass u ell ≤ M`. -/
theorem pointwise_le_factorialMajorant_of_increment_decay_on
    (k : I -> Nat) (xi : I -> Real) (w : (I -> Nat) -> Real)
    (P : (I -> Nat) -> Prop)
    (hdown : ∀ ell i, P (incrementProfile ell i) -> P ell)
    (hxi : ∀ i, 0 ≤ xi i)
    (hzero : w (fun _ => 0) ≤ 1)
    (hstep : ∀ ell i, IsPartialSubprofile k ell -> ell i < k i ->
      P (incrementProfile ell i) ->
      w (incrementProfile ell i) ≤ w ell *
        (xi i / (ell i + 1 : Real))) :
    ∀ ell, P ell -> IsPartialSubprofile k ell ->
      w ell ≤ partialDiagonalFactorialMajorant xi ell := by
  have hinduction : ∀ q : Nat, ∀ ell : I -> Nat,
      selectedBlockCount ell = q -> P ell -> IsPartialSubprofile k ell ->
        w ell ≤ partialDiagonalFactorialMajorant xi ell := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
      intro ell hcount hregion hprofile
      by_cases hq : q = 0
      · have hsumzero : ∑ j, ell j = 0 := by
          simpa [selectedBlockCount, hq] using hcount
        have hcoordinatezero : ∀ j, ell j = 0 := by
          intro j
          exact (Finset.sum_eq_zero_iff_of_nonneg
            (fun a _ => Nat.zero_le (ell a))).mp hsumzero j (Finset.mem_univ j)
        have hellzero : ell = fun _ => 0 := by
          funext j
          exact hcoordinatezero j
        rw [hellzero]
        simpa [partialDiagonalFactorialMajorant] using hzero
      · have hsumne : (∑ j, ell j) ≠ 0 := by
          intro hsumzero
          apply hq
          calc
            q = selectedBlockCount ell := hcount.symm
            _ = ∑ j, ell j := rfl
            _ = 0 := hsumzero
        obtain ⟨i, -, hine⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumne
        have hipos : 0 < ell i := Nat.pos_of_ne_zero hine
        have hone : 1 ≤ ell i := hipos
        let ell' : I -> Nat := Function.update ell i (ell i - 1)
        have hcoordinate : ell' i + 1 = ell i := by
          have hcoordinateRaw : ell i - 1 + 1 = ell i :=
            Nat.sub_add_cancel hone
          simpa only [ell', Function.update_self] using hcoordinateRaw
        have hcoordinateReal : (ell' i + 1 : Real) = ell i := by
          exact_mod_cast hcoordinate
        have hincrement : incrementProfile ell' i = ell := by
          funext j
          by_cases hji : j = i
          · subst j
            simpa [incrementProfile] using hcoordinate
          · simp [incrementProfile, ell', hji]
        have hprofile' : IsPartialSubprofile k ell' := by
          intro j
          by_cases hji : j = i
          · subst j
            simpa only [ell', Function.update_self] using
              (Nat.sub_le _ _).trans (hprofile i)
          · simpa [ell', hji] using hprofile j
        have hi' : ell' i < k i := by
          have hle : ell i ≤ k i := hprofile i
          have hlt : ell i - 1 < k i := by omega
          simpa only [ell', Function.update_self] using hlt
        have hregion' : P ell' := by
          apply hdown ell' i
          rw [hincrement]
          exact hregion
        have hcountIncrement := selectedBlockCount_increment ell' i
        rw [hincrement] at hcountIncrement
        have hcount' : selectedBlockCount ell' < q := by
          omega
        have hinduction' :=
          ih (selectedBlockCount ell') hcount' ell' rfl hregion' hprofile'
        have hstep' := hstep ell' i hprofile' hi' (by
          rw [hincrement]
          exact hregion)
        rw [hincrement, hcoordinateReal] at hstep'
        have hmajorantIncrement :=
          partialDiagonalFactorialMajorant_increment xi ell' i
        rw [hincrement, hcoordinateReal] at hmajorantIncrement
        have hfactorNonneg : 0 ≤ xi i / (ell i : Real) := by
          exact div_nonneg (hxi i) (by positivity)
        calc
          w ell ≤ w ell' * (xi i / (ell i : Real)) := hstep'
          _ ≤ partialDiagonalFactorialMajorant xi ell' *
              (xi i / (ell i : Real)) :=
            mul_le_mul_of_nonneg_right hinduction' hfactorNonneg
          _ = partialDiagonalFactorialMajorant xi ell :=
            hmajorantIncrement.symm
  intro ell hregion hprofile
  exact hinduction (selectedBlockCount ell) ell rfl hregion hprofile

/-- Exact finite reindexing of the factorial majorant into one-dimensional
truncated exponential sums. -/
theorem sum_partialDiagonalFactorialMajorant_eq_product
    (k : I -> Nat) (xi : I -> Real) :
    ∑ ell ∈ partialSubprofileBox k,
      partialDiagonalFactorialMajorant xi ell =
      ∏ i, ∑ r ∈ Finset.range (k i + 1),
        xi i ^ r / (r.factorial : Real) := by
  simpa [partialSubprofileBox, partialDiagonalFactorialMajorant] using
    (Finset.prod_univ_sum
      (fun i => Finset.range (k i + 1))
      (fun i r => xi i ^ r / (r.factorial : Real))).symm

omit [DecidableEq I] in
/-- Nonnegativity of the factorial majorant follows coordinatewise from
nonnegative activities. -/
theorem partialDiagonalFactorialMajorant_nonneg
    (xi : I -> Real) (hxi : ∀ i, 0 ≤ xi i) (ell : I -> Nat) :
    0 ≤ partialDiagonalFactorialMajorant xi ell := by
  unfold partialDiagonalFactorialMajorant
  exact Finset.prod_nonneg fun i _ =>
    div_nonneg (pow_nonneg (hxi i) _) (by positivity)

/-- Reindex a factorial-majorized sum over any subprofile region into the
same full product of truncated exponential sums. -/
theorem sum_le_product_truncatedExp_of_partialDiagonal_majorant_on
    (k : I -> Nat) (xi : I -> Real) (w : (I -> Nat) -> Real)
    (P : (I -> Nat) -> Prop) [DecidablePred P] (hxi : ∀ i, 0 ≤ xi i)
    (hmajorant : ∀ ell, ell ∈ partialSubprofileBox k -> P ell ->
      w ell ≤ partialDiagonalFactorialMajorant xi ell) :
    ∑ ell ∈ (partialSubprofileBox k).filter P, w ell ≤
      ∏ i, ∑ r ∈ Finset.range (k i + 1),
        xi i ^ r / (r.factorial : Real) := by
  calc
    ∑ ell ∈ (partialSubprofileBox k).filter P, w ell ≤
        ∑ ell ∈ (partialSubprofileBox k).filter P,
          partialDiagonalFactorialMajorant xi ell := by
      exact Finset.sum_le_sum fun ell hell =>
        hmajorant ell (Finset.mem_filter.mp hell).1 (Finset.mem_filter.mp hell).2
    _ ≤ ∑ ell ∈ partialSubprofileBox k,
          partialDiagonalFactorialMajorant xi ell := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro ell hell _
      exact partialDiagonalFactorialMajorant_nonneg xi hxi ell
    _ = ∏ i, ∑ r ∈ Finset.range (k i + 1),
          xi i ^ r / (r.factorial : Real) :=
      sum_partialDiagonalFactorialMajorant_eq_product k xi

/-- A finite sum is controlled by a supplied factorial majorant, with the
right-hand side reindexed exactly as a product of truncated exponential sums. -/
theorem sum_le_product_truncatedExp_of_partialDiagonal_majorant
    (k : I -> Nat) (xi : I -> Real) (w : (I -> Nat) -> Real)
    (hmajorant : ∀ ell, ell ∈ partialSubprofileBox k ->
      w ell ≤ partialDiagonalFactorialMajorant xi ell) :
    ∑ ell ∈ partialSubprofileBox k, w ell ≤
      ∏ i, ∑ r ∈ Finset.range (k i + 1),
        xi i ^ r / (r.factorial : Real) := by
  calc
    ∑ ell ∈ partialSubprofileBox k, w ell ≤
        ∑ ell ∈ partialSubprofileBox k,
          partialDiagonalFactorialMajorant xi ell := by
      exact Finset.sum_le_sum fun ell hell => hmajorant ell hell
    _ = ∏ i, ∑ r ∈ Finset.range (k i + 1),
          xi i ^ r / (r.factorial : Real) :=
      sum_partialDiagonalFactorialMajorant_eq_product k xi

/-- The exact partial-diagonal ratio implies this one-step decay bound once
the displayed finite lower bound on `mu` is supplied. -/
theorem partialDiagonalWeight_increment_le_of_mu_activity
    (n : Nat) (u k ell : I -> Nat) (i : I) (xi : I -> Real)
    (hprofile : IsPartialSubprofile k ell)
    (hmass : selectedVertexMass u ell + u i ≤ n)
    (hactivity : ((k i - ell i : Nat) : Real) ^ 2 ≤
      2 * xi i * mu (n - selectedVertexMass u ell) (u i)) :
    partialDiagonalWeight n u k (incrementProfile ell i) ≤
      partialDiagonalWeight n u k ell * (xi i / (ell i + 1 : Real)) := by
  have hu : u i ≤ n - selectedVertexMass u ell :=
    Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hmass)
  have hmuPos : 0 < mu (n - selectedVertexMass u ell) (u i) := mu_pos hu
  have hdenPos : 0 < 2 * (ell i + 1 : Real) *
      mu (n - selectedVertexMass u ell) (u i) := by
    positivity
  have hratio :
      ((k i - ell i : Nat) : Real) ^ 2 /
          (2 * (ell i + 1 : Real) *
            mu (n - selectedVertexMass u ell) (u i)) ≤
        xi i / (ell i + 1 : Real) := by
    calc
      ((k i - ell i : Nat) : Real) ^ 2 /
          (2 * (ell i + 1 : Real) *
            mu (n - selectedVertexMass u ell) (u i)) ≤
          (2 * xi i * mu (n - selectedVertexMass u ell) (u i)) /
            (2 * (ell i + 1 : Real) *
              mu (n - selectedVertexMass u ell) (u i)) := by
        exact div_le_div_of_nonneg_right hactivity hdenPos.le
      _ = xi i / (ell i + 1 : Real) := by
        field_simp
  have hweightPos : 0 < partialDiagonalWeight n u k ell :=
    partialDiagonalWeight_pos n u k ell hprofile
  have hratioExact :=
    partialDiagonalWeight_increment_div n u k ell i hprofile hmass
  have hquotient :
      partialDiagonalWeight n u k (incrementProfile ell i) /
          partialDiagonalWeight n u k ell ≤
        xi i / (ell i + 1 : Real) := by
    rw [hratioExact]
    exact hratio
  have hmul := (div_le_iff₀ hweightPos).mp hquotient
  nlinarith

/-- A convenient coarser form of
`partialDiagonalWeight_increment_le_of_mu_activity`, replacing the exact
numerator by `k_i^2`. -/
theorem partialDiagonalWeight_increment_le_of_mu_lower
    (n : Nat) (u k ell : I -> Nat) (i : I) (xi : I -> Real)
    (hprofile : IsPartialSubprofile k ell)
    (hmass : selectedVertexMass u ell + u i ≤ n)
    (hmu : (k i : Real) ^ 2 ≤
      2 * xi i * mu (n - selectedVertexMass u ell) (u i)) :
    partialDiagonalWeight n u k (incrementProfile ell i) ≤
      partialDiagonalWeight n u k ell * (xi i / (ell i + 1 : Real)) := by
  have hsub : ((k i - ell i : Nat) : Real) ≤ k i := by
    exact_mod_cast Nat.sub_le (k i) (ell i)
  have hnum : ((k i - ell i : Nat) : Real) ^ 2 ≤ (k i : Real) ^ 2 := by
    nlinarith
  exact partialDiagonalWeight_increment_le_of_mu_activity
    n u k ell i xi hprofile hmass (hnum.trans hmu)

/-- Iterating any verified coordinate decay bound gives a pointwise
factorial majorant for every exact partial-diagonal weight. -/
theorem partialDiagonalWeight_le_factorialMajorant_of_increment_decay
    (n : Nat) (u k : I -> Nat) (xi : I -> Real)
    (hxi : ∀ i, 0 ≤ xi i)
    (hstep : ∀ ell i, IsPartialSubprofile k ell -> ell i < k i ->
      partialDiagonalWeight n u k (incrementProfile ell i) ≤
        partialDiagonalWeight n u k ell *
          (xi i / (ell i + 1 : Real))) :
    ∀ ell, IsPartialSubprofile k ell ->
      partialDiagonalWeight n u k ell ≤
        partialDiagonalFactorialMajorant xi ell := by
  apply pointwise_le_factorialMajorant_of_increment_decay k xi
    (partialDiagonalWeight n u k) hxi
  · simp
  · exact hstep

/-- A finite selected-mass cutoff is closed under deleting one block.  Under
the stated `mu` lower bound at every admissible last step, all weights in that
cutoff have the factorial majorant. -/
theorem partialDiagonalWeight_le_factorialMajorant_of_mu_lower_on_mass
    (n massCap : Nat) (u k : I -> Nat) (xi : I -> Real)
    (hxi : ∀ i, 0 ≤ xi i)
    (hmassCap : massCap ≤ n)
    (hmu : ∀ ell i, IsPartialSubprofile k ell -> ell i < k i ->
      selectedVertexMass u (incrementProfile ell i) ≤ massCap ->
      ((k i - ell i : Nat) : Real) ^ 2 ≤
        2 * xi i * mu (n - selectedVertexMass u ell) (u i)) :
    ∀ ell, selectedVertexMass u ell ≤ massCap ->
      IsPartialSubprofile k ell ->
        partialDiagonalWeight n u k ell ≤
          partialDiagonalFactorialMajorant xi ell := by
  apply pointwise_le_factorialMajorant_of_increment_decay_on k xi
    (partialDiagonalWeight n u k)
    (fun ell => selectedVertexMass u ell ≤ massCap)
  · intro ell i hregion
    rw [selectedVertexMass_increment] at hregion
    omega
  · exact hxi
  · simp
  · intro ell i hprofile hi hregion
    apply partialDiagonalWeight_increment_le_of_mu_activity n u k ell i xi hprofile
    · rw [selectedVertexMass_increment] at hregion
      omega
    · exact hmu ell i hprofile hi hregion

/-- Exact finite empty-corner bridge: a coordinatewise `mu` lower bound on
the selected-mass cutoff controls the entire cutoff sum by a product of
truncated exponential sums. -/
theorem sum_partialDiagonalWeight_le_product_truncatedExp_of_mu_lower_on_mass
    (n massCap : Nat) (u k : I -> Nat) (xi : I -> Real)
    (hxi : ∀ i, 0 ≤ xi i)
    (hmassCap : massCap ≤ n)
    (hmu : ∀ ell i, IsPartialSubprofile k ell -> ell i < k i ->
      selectedVertexMass u (incrementProfile ell i) ≤ massCap ->
      ((k i - ell i : Nat) : Real) ^ 2 ≤
        2 * xi i * mu (n - selectedVertexMass u ell) (u i)) :
    ∑ ell ∈ (partialSubprofileBox k).filter
        (fun ell => selectedVertexMass u ell ≤ massCap),
      partialDiagonalWeight n u k ell ≤
      ∏ i, ∑ r ∈ Finset.range (k i + 1),
        xi i ^ r / (r.factorial : Real) := by
  apply sum_le_product_truncatedExp_of_partialDiagonal_majorant_on k xi
    (partialDiagonalWeight n u k)
    (fun ell => selectedVertexMass u ell ≤ massCap) hxi
  intro ell hell hregion
  exact partialDiagonalWeight_le_factorialMajorant_of_mu_lower_on_mass
    n massCap u k xi hxi hmassCap hmu ell hregion
    (mem_partialSubprofileBox.mp hell)

/-- Each finite truncated exponential sum is bounded by the exact real
exponential at a nonnegative activity. -/
theorem truncatedExpSum_le_exp (x : Real) (bound : Nat) (hx : 0 ≤ x) :
    ∑ r ∈ Finset.range (bound + 1), x ^ r / (r.factorial : Real) ≤
      Real.exp x := by
  let f : Nat -> Real := fun r => x ^ r / (r.factorial : Real)
  have hsum : Summable f := by
    simpa [f] using NormedSpace.expSeries_div_summable x
  calc
    ∑ r ∈ Finset.range (bound + 1), x ^ r / (r.factorial : Real) =
        ∑ r ∈ Finset.range (bound + 1), f r := by rfl
    _ ≤ ∑' r, f r := by
      apply hsum.sum_le_tsum
      intro r hr
      exact div_nonneg (pow_nonneg hx _) (by positivity)
    _ = Real.exp x := by
      simpa [f, Real.exp_eq_exp_ℝ] using
        (NormedSpace.expSeries_div_hasSum_exp x).tsum_eq

omit [DecidableEq I] in
/-- The product of the finite one-dimensional majorants is at most the
exponential of the total activity. -/
theorem product_truncatedExp_le_exp_sum
    (k : I -> Nat) (xi : I -> Real) (hxi : ∀ i, 0 ≤ xi i) :
    (∏ i, ∑ r ∈ Finset.range (k i + 1),
      xi i ^ r / (r.factorial : Real)) ≤ Real.exp (∑ i, xi i) := by
  rw [Real.exp_sum]
  exact Finset.prod_le_prod
    (fun i _ => Finset.sum_nonneg fun r _ =>
      div_nonneg (pow_nonneg (hxi i) _) (by positivity))
    (fun i _ => truncatedExpSum_le_exp (xi i) (k i) (hxi i))

/-- The finite mass-cutoff bridge in a single exponential form.  This is an
ordinary inequality for the supplied finite data, not an asymptotic claim. -/
theorem sum_partialDiagonalWeight_le_exp_sum_of_mu_lower_on_mass
    (n massCap : Nat) (u k : I -> Nat) (xi : I -> Real)
    (hxi : ∀ i, 0 ≤ xi i)
    (hmassCap : massCap ≤ n)
    (hmu : ∀ ell i, IsPartialSubprofile k ell -> ell i < k i ->
      selectedVertexMass u (incrementProfile ell i) ≤ massCap ->
      ((k i - ell i : Nat) : Real) ^ 2 ≤
        2 * xi i * mu (n - selectedVertexMass u ell) (u i)) :
    ∑ ell ∈ (partialSubprofileBox k).filter
        (fun ell => selectedVertexMass u ell ≤ massCap),
      partialDiagonalWeight n u k ell ≤ Real.exp (∑ i, xi i) := by
  exact
    (sum_partialDiagonalWeight_le_product_truncatedExp_of_mu_lower_on_mass
      n massCap u k xi hxi hmassCap hmu).trans
      (product_truncatedExp_le_exp_sum k xi hxi)

/-- Apply the finite factorial-majorant reindexing directly to exact
partial-diagonal weights.  The hypothesis is intentionally pointwise: a
Section VII range argument may establish it by any finite recurrence path. -/
theorem sum_partialDiagonalWeight_le_product_truncatedExp
    (n : Nat) (u k : I -> Nat) (xi : I -> Real)
    (hmajorant : ∀ ell, IsPartialSubprofile k ell ->
      partialDiagonalWeight n u k ell ≤
        partialDiagonalFactorialMajorant xi ell) :
    ∑ ell ∈ partialSubprofileBox k, partialDiagonalWeight n u k ell ≤
      ∏ i, ∑ r ∈ Finset.range (k i + 1),
        xi i ^ r / (r.factorial : Real) := by
  apply sum_le_product_truncatedExp_of_partialDiagonal_majorant k xi
    (partialDiagonalWeight n u k)
  intro ell hell
  exact hmajorant ell (mem_partialSubprofileBox.mp hell)

end

end Erdos625
