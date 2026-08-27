import Erdos625.MidpointProfileRounding
import Erdos625.PartialDiagonalCentralLogEnvelope
import Erdos625.PartialDiagonalMidpointActivityBridge
import Erdos625.PartialDiagonalMuRatioBound
import Erdos625.PhaseConsequences

/-!
# Canonical midpoint partial-diagonal empty range

This module freezes the manuscript's empty-range predicate and the exact
uniform `Icc` endpoint for the corresponding finite partial-diagonal sum.
The theorem below gives the corresponding uniform finite asymptotic bound.
-/

namespace Erdos625

open scoped BigOperators Topology
open Filter Finset Set

noncomputable section

set_option autoImplicit false

/-- The manuscript cutoff `eta_n = log log n / (32 log n)`. -/
noncomputable def midpointPartialDiagonalEta (n : Nat) : Real :=
  logLogOrder n / (32 * logOrder n)

/-- A partial diagonal profile is in the empty range when its selected
vertex mass is at most `n * eta_n`, using the manuscript's real cutoff. -/
noncomputable def midpointPartialDiagonalEmptyRange
    (n : Nat) (ell : Fin 4 → Nat) : Prop :=
  (selectedVertexMass
      (midpointPartialDiagonalSize (phaseNat n)) ell : Real) ≤
    (n : Real) * midpointPartialDiagonalEta n

local instance (n : Nat) :
    DecidablePred (midpointPartialDiagonalEmptyRange n) :=
  fun _ => Classical.propDecidable _

/-! ### Local helpers for the empty-range endpoint -/

/-- One exact adjacent-size comparison for `mu`, obtained from the two-term
identity alone.  No global monotonicity of `s ↦ mu v s` is used. -/
private lemma aux_empty_mu_succ_le {v s : Nat} (hv : (v : Real) ≤ 2 ^ s) :
    mu v (s + 1) ≤ mu v s := by
  have hid := mu_succ_mul_identity v s
  have hpow : (0 : Real) < 2 ^ s := by positivity
  have hvs : ((v - s : Nat) : Real) ≤ (2 : Real) ^ s := by
    have h : ((v - s : Nat) : Real) ≤ (v : Real) := by
      exact_mod_cast Nat.sub_le v s
    linarith
  have hmus : 0 ≤ mu v s := mu_nonneg v s
  have hmus1 : 0 ≤ mu v (s + 1) := mu_nonneg v (s + 1)
  have hone : (1 : Real) ≤ ((s + 1 : Nat) : Real) := by
    have h : (1 : Nat) ≤ s + 1 := Nat.succ_le_succ (Nat.zero_le s)
    exact_mod_cast h
  have hle : mu v (s + 1) * 2 ^ s ≤ mu v s * 2 ^ s := by
    calc mu v (s + 1) * 2 ^ s
        ≤ mu v (s + 1) * ((s + 1 : Nat) : Real) * 2 ^ s := by
          have h0 : mu v (s + 1) * 1 ≤ mu v (s + 1) * ((s + 1 : Nat) : Real) :=
            mul_le_mul_of_nonneg_left hone hmus1
          have h1 := mul_le_mul_of_nonneg_right h0 hpow.le
          linarith
      _ = mu v s * ((v - s : Nat) : Real) := hid
      _ ≤ mu v s * 2 ^ s := mul_le_mul_of_nonneg_left hvs hmus
  exact le_of_mul_le_mul_right hle hpow

/-- Finitely many predecessor comparisons transport the `alpha - 2` first
moment to each of the four midpoint block sizes. -/
private lemma aux_empty_mu_size_ge {v alpha : Nat} (h5 : 5 < alpha)
    (hpow : (v : Real) ≤ 2 ^ (alpha - 5)) (i : Fin 4) :
    mu v (alpha - 2) ≤ mu v (midpointPartialDiagonalSize alpha i) := by
  have hstep : ∀ s : Nat, alpha - 5 ≤ s → mu v (s + 1) ≤ mu v s := by
    intro s hs
    refine aux_empty_mu_succ_le (hpow.trans ?_)
    exact pow_le_pow_right₀ (by norm_num) hs
  have h23 : mu v (alpha - 2) ≤ mu v (alpha - 3) := by
    have e : alpha - 2 = (alpha - 3) + 1 := by omega
    rw [e]
    exact hstep _ (by omega)
  have h34 : mu v (alpha - 3) ≤ mu v (alpha - 4) := by
    have e : alpha - 3 = (alpha - 4) + 1 := by omega
    rw [e]
    exact hstep _ (by omega)
  have h45 : mu v (alpha - 4) ≤ mu v (alpha - 5) := by
    have e : alpha - 4 = (alpha - 5) + 1 := by omega
    rw [e]
    exact hstep _ (by omega)
  have hsize : midpointPartialDiagonalSize alpha i = alpha - (i.1 + 2) := rfl
  have hi : i.1 = 0 ∨ i.1 = 1 ∨ i.1 = 2 ∨ i.1 = 3 := by omega
  rcases hi with h | h | h | h
  · have e : alpha - (i.1 + 2) = alpha - 2 := by omega
    rw [hsize, e]
  · have e : alpha - (i.1 + 2) = alpha - 3 := by omega
    rw [hsize, e]
    exact h23
  · have e : alpha - (i.1 + 2) = alpha - 4 := by omega
    rw [hsize, e]
    exact h23.trans h34
  · have e : alpha - (i.1 + 2) = alpha - 5 := by omega
    rw [hsize, e]
    exact h23.trans (h34.trans h45)

/-- `1 ≤ log log n` and `log log n ≤ log n` in the range used below. -/
private lemma aux_empty_logLog_bounds {n : Nat} (hL : (20 : Real) ≤ logOrder n) :
    (1 : Real) ≤ logLogOrder n ∧ logLogOrder n ≤ logOrder n := by
  have hllval : logLogOrder n = Real.log (logOrder n) := rfl
  have hLpos : (0 : Real) < logOrder n := by linarith
  constructor
  · rw [hllval]
    have h20 : (1 : Real) ≤ Real.log 20 :=
      (Real.le_log_iff_exp_le (by norm_num)).mpr (by linarith [Real.exp_one_lt_d9])
    have hmono : Real.log 20 ≤ Real.log (logOrder n) :=
      Real.log_le_log (by norm_num) hL
    linarith
  · rw [hllval]
    linarith [Real.log_le_sub_one_of_pos hLpos]

/-- The exact falling-factorial inflation factor of the empty range is at
most `sqrt (log n)`, written as `exp (log log n / 2)`. -/
private lemma aux_empty_pow_ratio_le {n m s : Nat}
    (hL : (20 : Real) ≤ logOrder n)
    (hn128 : 128 * logOrder n ^ 2 ≤ (n : Real))
    (hsm : s + m ≤ n)
    (hsL : (s : Real) ≤ 4 * logOrder n)
    (hmcut : (m : Real) ≤ (n : Real) * (logLogOrder n / (32 * logOrder n))) :
    ((n : Real) / ((n - m - s + 1 : Nat) : Real)) ^ s
      ≤ Real.exp (logLogOrder n / 2) := by
  obtain ⟨hll1, hllle⟩ := aux_empty_logLog_bounds hL
  have hLpos : (0 : Real) < logOrder n := by linarith
  have hnpos : (0 : Real) < (n : Real) := by nlinarith
  have hmsmall : (m : Real) ≤ (n : Real) / 32 := by
    have hfrac : logLogOrder n / (32 * logOrder n) ≤ 1 / 32 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have h := mul_le_mul_of_nonneg_left hfrac hnpos.le
    linarith
  have hssmall : (s : Real) ≤ (n : Real) / 640 := by
    nlinarith [mul_nonneg (show (0 : Real) ≤ logOrder n - 20 by linarith) hLpos.le]
  have hmn : m ≤ n := by omega
  have hsnm : s ≤ n - m := by omega
  have hDnat : ((n - m - s + 1 : Nat) : Real)
      = (n : Real) - (m : Real) - (s : Real) + 1 := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hsnm, Nat.cast_sub hmn]
  have hDpos : (0 : Real) < (n : Real) - (m : Real) - (s : Real) + 1 := by
    linarith
  have hexpstep : (n : Real) / ((n : Real) - m - s + 1) ≤
      Real.exp (((m : Real) + (s : Real)) / ((n : Real) - m - s + 1)) := by
    rw [div_le_iff₀ hDpos]
    have h := Real.add_one_le_exp
      (((m : Real) + (s : Real)) / ((n : Real) - m - s + 1))
    have hmul := mul_le_mul_of_nonneg_right h hDpos.le
    have heq : (((m : Real) + (s : Real)) / ((n : Real) - m - s + 1) + 1)
        * ((n : Real) - m - s + 1)
        = (m : Real) + (s : Real) + ((n : Real) - m - s + 1) := by
      field_simp
    linarith
  have h3 : (s : Real) *
      (((m : Real) + (s : Real)) / ((n : Real) - m - s + 1))
        ≤ logLogOrder n / 2 := by
    have hfrac : ((m : Real) + (s : Real)) / ((n : Real) - m - s + 1)
        ≤ 2 * ((m : Real) + (s : Real)) / (n : Real) := by
      rw [div_le_div_iff₀ hDpos hnpos]
      nlinarith [Nat.cast_nonneg (α := Real) m, Nat.cast_nonneg (α := Real) s]
    have hsnn : (0 : Real) ≤ (s : Real) := Nat.cast_nonneg s
    have hstep1 : (s : Real) *
        (((m : Real) + (s : Real)) / ((n : Real) - m - s + 1))
        ≤ (s : Real) * (2 * ((m : Real) + (s : Real)) / (n : Real)) :=
      mul_le_mul_of_nonneg_left hfrac hsnn
    have hsm2 : (s : Real) * (m : Real) ≤ (n : Real) * logLogOrder n / 8 := by
      have h4 : (s : Real) * (m : Real)
          ≤ (4 * logOrder n) * ((n : Real) * (logLogOrder n / (32 * logOrder n))) :=
        mul_le_mul hsL hmcut (Nat.cast_nonneg m) (by linarith)
      have heq : (4 * logOrder n) *
          ((n : Real) * (logLogOrder n / (32 * logOrder n)))
          = (n : Real) * logLogOrder n / 8 := by
        field_simp
        ring
      linarith
    have hss2 : (s : Real) ^ 2 ≤ 16 * logOrder n ^ 2 := by nlinarith
    have hfin : (s : Real) * (2 * ((m : Real) + (s : Real)) / (n : Real))
        ≤ logLogOrder n / 2 := by
      rw [mul_div_assoc', div_le_iff₀ hnpos]
      nlinarith [mul_nonneg hnpos.le (show (0 : Real) ≤ logLogOrder n - 1 by linarith)]
    linarith
  rw [hDnat]
  have hbase : (0 : Real) ≤ (n : Real) / ((n : Real) - m - s + 1) := by positivity
  have h1 : ((n : Real) / ((n : Real) - m - s + 1)) ^ s ≤
      (Real.exp (((m : Real) + (s : Real)) / ((n : Real) - m - s + 1))) ^ s :=
    pow_le_pow_left₀ hbase hexpstep s
  have h2 : (Real.exp (((m : Real) + (s : Real)) / ((n : Real) - m - s + 1))) ^ s
      = Real.exp ((s : Real) *
          (((m : Real) + (s : Real)) / ((n : Real) - m - s + 1))) :=
    (Real.exp_nat_mul _ s).symm
  rw [h2] at h1
  exact h1.trans (Real.exp_le_exp.mpr h3)

/-- The manuscript polylogarithmic first-moment bound, weakened to the
convenient `c n^2 / log n` form actually used in the empty range. -/
private lemma aux_empty_mu_base_lower {n s : Nat} {c : Real} (hc : 0 < c)
    (hL : (20 : Real) ≤ logOrder n)
    (hmu : c * (n : Real) ^ 2 * logOrder n ^ (2 / q - 5 / 2 : Real) ≤ mu n s) :
    c * (n : Real) ^ 2 / logOrder n ≤ mu n s := by
  have hqpos := q_pos
  have hq1 : q < 1 := by
    show Real.log 2 < 1
    linarith [Real.log_two_lt_d9]
  have h2q : (2 : Real) ≤ 2 / q := by
    rw [le_div_iff₀ hqpos]
    nlinarith
  have hexp : logOrder n ^ (-1 : Real) ≤ logOrder n ^ (2 / q - 5 / 2 : Real) := by
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    linarith
  have hcast : c * (n : Real) ^ 2 / logOrder n
      = c * (n : Real) ^ 2 * logOrder n ^ (-1 : Real) := by
    rw [Real.rpow_neg_one]
    ring
  rw [hcast]
  exact le_trans
    (mul_le_mul_of_nonneg_left hexp (mul_nonneg hc.le (sq_nonneg _))) hmu

/-- Transport of the first-moment lower bound from `n` to the residual
vertex count `n - m` on the whole empty range. -/
private lemma aux_empty_mu_shift_lower {n m s : Nat} {c : Real}
    (hc : 0 < c)
    (hL : (20 : Real) ≤ logOrder n)
    (hn128 : 128 * logOrder n ^ 2 ≤ (n : Real))
    (hsm : s + m ≤ n)
    (hsL : (s : Real) ≤ 4 * logOrder n)
    (hmcut : (m : Real) ≤ (n : Real) * (logLogOrder n / (32 * logOrder n)))
    (hmu : c * (n : Real) ^ 2 * logOrder n ^ (2 / q - 5 / 2 : Real) ≤ mu n s) :
    c * (n : Real) ^ 2 /
        (logOrder n * Real.exp (logLogOrder n / 2)) ≤ mu (n - m) s := by
  have hLpos : (0 : Real) < logOrder n := by linarith
  have hsnm : s ≤ n - m := by omega
  have hbase := aux_empty_mu_base_lower hc hL hmu
  have hratio := aux_empty_pow_ratio_le hL hn128 hsm hsL hmcut
  have hmupos : (0 : Real) < mu (n - m) s := mu_pos hsnm
  have hdiv := mu_div_mu_sub_le_pow (v := n) (s := s) (m := m) hsm
  have hchain : mu n s ≤ Real.exp (logLogOrder n / 2) * mu (n - m) s := by
    have h := (div_le_iff₀ hmupos).mp hdiv
    have h2 := mul_le_mul_of_nonneg_right hratio hmupos.le
    linarith
  have h1 : c * (n : Real) ^ 2
      ≤ (Real.exp (logLogOrder n / 2) * mu (n - m) s) * logOrder n :=
    (div_le_iff₀ hLpos).mp (hbase.trans hchain)
  rw [div_le_iff₀ (mul_pos hLpos (Real.exp_pos _))]
  linarith [h1]

private lemma aux_empty_multiplicity_le {n alpha K : Nat}
    (hadm : MidpointRoundingAdmissible n alpha K) (i : Fin 4) :
    midpointMultiplicity n alpha K i ≤ K := by
  have hsum := (midpointMultiplicity_count_deficit_intDisplacement n alpha K hadm).1
  calc midpointMultiplicity n alpha K i
      ≤ ∑ j : Fin 4, midpointMultiplicity n alpha K j :=
        Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    _ = K := hsum

/-- Split-module copy of the exact midpoint mass identity used by the
standalone proof.  The corresponding helper in the central-envelope module is
private, so it is not available across this module boundary. -/
private lemma aux_empty_full_mass (n alpha K : Nat)
    (hadm : MidpointRoundingAdmissible n alpha K) :
    selectedVertexMass (midpointPartialDiagonalSize alpha)
      (midpointMultiplicity n alpha K) = n := by
  have hcd := midpointMultiplicity_count_deficit_intDisplacement n alpha K hadm
  obtain ⟨halpha, hK, hnK, -, -⟩ := hadm
  have hsum := hcd.1
  have hmom := hcd.2.1
  rw [midpointDeficit] at hmom
  have hd : ∀ i : Fin 4, fourDeficit i ≤ alpha := by
    intro i
    have := i.isLt
    simp only [fourDeficit]
    omega
  have hsplit :
      (∑ i, midpointPartialDiagonalSize alpha i * midpointMultiplicity n alpha K i)
        + (∑ i, tangentDeficitNat i * midpointMultiplicity n alpha K i)
        = alpha * K := by
    have hstep :
        (∑ i, midpointPartialDiagonalSize alpha i * midpointMultiplicity n alpha K i)
          + (∑ i, tangentDeficitNat i * midpointMultiplicity n alpha K i)
          = ∑ i, alpha * midpointMultiplicity n alpha K i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have ht : tangentDeficitNat i = fourDeficit i := rfl
      simp only [midpointPartialDiagonalSize, ht, ← Nat.add_mul]
      rw [Nat.sub_add_cancel (hd i)]
    rw [hstep, ← Finset.mul_sum, hsum]
  unfold selectedVertexMass
  obtain ⟨P, hP⟩ : ∃ P, alpha * K = P := ⟨_, rfl⟩
  rw [hP] at hsplit hmom hnK
  omega

/-- Exact midpoint mass conservation forces the uniform `K = O(n / log n)`
bound used for the four activities. -/
private lemma aux_empty_K_mul_logOrder_le {n K : Nat}
    (hadm : MidpointRoundingAdmissible n (phaseNat n) K)
    (hL : (20 : Real) ≤ logOrder n)
    (hph2 : 2 * logOrder n ≤ (phaseNat n : Real)) :
    (K : Real) * logOrder n ≤ (n : Real) := by
  have h5 : 5 < phaseNat n := hadm.1
  have hsum :=
    (midpointMultiplicity_count_deficit_intDisplacement n (phaseNat n) K hadm).1
  have hfull : (∑ i : Fin 4, midpointPartialDiagonalSize (phaseNat n) i *
      midpointMultiplicity n (phaseNat n) K i) = n :=
    aux_empty_full_mass n (phaseNat n) K hadm
  have hsize : ∀ i : Fin 4,
      phaseNat n - 5 ≤ midpointPartialDiagonalSize (phaseNat n) i := by
    intro i
    have hi := i.isLt
    simp only [midpointPartialDiagonalSize, fourDeficit]
    omega
  have hmassge : (phaseNat n - 5) * K ≤ n := by
    calc (phaseNat n - 5) * K
        = ∑ i : Fin 4, (phaseNat n - 5) * midpointMultiplicity n (phaseNat n) K i := by
          rw [← Finset.mul_sum, hsum]
      _ ≤ ∑ i : Fin 4, midpointPartialDiagonalSize (phaseNat n) i *
            midpointMultiplicity n (phaseNat n) K i :=
          Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ (hsize i)
      _ = n := hfull
  have hcast : ((phaseNat n - 5 : Nat) : Real) * (K : Real) ≤ (n : Real) := by
    exact_mod_cast hmassge
  have hcast5 : ((phaseNat n - 5 : Nat) : Real) = (phaseNat n : Real) - 5 := by
    have h : (5 : Nat) ≤ phaseNat n := by omega
    rw [Nat.cast_sub h]
    norm_num
  rw [hcast5] at hcast
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := Real) K)
    (show (0 : Real) ≤ (phaseNat n : Real) - 5 - logOrder n by linarith)]

/-- At the phase scale the four block sizes are large enough that `2 ^ u_i`
dominates the vertex count. -/
private lemma aux_empty_two_pow_lower {n : Nat} (h5 : 5 < phaseNat n)
    (hL : (20 : Real) ≤ logOrder n)
    (hph2 : 2 * logOrder n ≤ (phaseNat n : Real)) :
    (n : Real) ≤ 2 ^ (phaseNat n - 5) := by
  have hLpos : (0 : Real) < logOrder n := by linarith
  have hnpos : (0 : Real) < (n : Real) := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      have hzero : logOrder 0 = 0 := by simp [logOrder]
      rw [h, hzero] at hL
      linarith
    · exact_mod_cast h
  have h5' : (5 : Nat) ≤ phaseNat n := le_of_lt h5
  have hcast5 : ((phaseNat n - 5 : Nat) : Real) = (phaseNat n : Real) - 5 := by
    rw [Nat.cast_sub h5']
    norm_num
  have hq2 : Real.log 2 = q := rfl
  have hqlow : (0.6931471803 : Real) < q := by
    rw [← hq2]
    exact Real.log_two_gt_d9
  have hlog : Real.log (n : Real) ≤ Real.log ((2 : Real) ^ (phaseNat n - 5)) := by
    rw [Real.log_pow, hcast5, hq2]
    have hLval : Real.log (n : Real) = logOrder n := rfl
    rw [hLval]
    have hh1 : (0 : Real) ≤ ((phaseNat n : Real) - 2 * logOrder n) * q :=
      mul_nonneg (by linarith) (le_of_lt q_pos)
    have hh2 : (2 * logOrder n - 5) * 0.6931471803 ≤ (2 * logOrder n - 5) * q :=
      mul_le_mul_of_nonneg_left (le_of_lt hqlow) (by linarith)
    nlinarith [hh1, hh2]
  exact (Real.log_le_log_iff hnpos (by positivity)).mp hlog

/-- The one-step decay input of the factorial majorant, uniformly over the
whole real empty range. -/
private lemma aux_empty_mu_step {n K massCap : Nat} {c X S : Real}
    (hcpos : 0 < c) (h5 : 5 < phaseNat n)
    (hL : (20 : Real) ≤ logOrder n)
    (hn128 : 128 * logOrder n ^ 2 ≤ (n : Real))
    (hph2 : 2 * logOrder n ≤ (phaseNat n : Real))
    (hph4 : (phaseNat n : Real) ≤ 4 * logOrder n)
    (hmu : c * (n : Real) ^ 2 * logOrder n ^ (2 / q - 5 / 2 : Real)
      ≤ mu n (phaseNat n - 2))
    (hSdef : S = Real.exp (logLogOrder n / 2))
    (hcapreal : (massCap : Real)
      ≤ (n : Real) * (logLogOrder n / (32 * logOrder n)))
    (hXnn : (0 : Real) ≤ X)
    (hKX : (K : Real) ^ 2 = 2 * X * (c * (n : Real) ^ 2 / (logOrder n * S)))
    (hkK : ∀ i : Fin 4, midpointMultiplicity n (phaseNat n) K i ≤ K) :
    ∀ (ell : Fin 4 → Nat) (i : Fin 4),
      IsPartialSubprofile (midpointMultiplicity n (phaseNat n) K) ell →
      ell i < midpointMultiplicity n (phaseNat n) K i →
      selectedVertexMass (midpointPartialDiagonalSize (phaseNat n))
        (incrementProfile ell i) ≤ massCap →
      ((midpointMultiplicity n (phaseNat n) K i - ell i : Nat) : Real) ^ 2 ≤
        2 * X * mu (n - selectedVertexMass
          (midpointPartialDiagonalSize (phaseNat n)) ell)
          (midpointPartialDiagonalSize (phaseNat n) i) := by
  obtain ⟨hll1, hllle⟩ := aux_empty_logLog_bounds hL
  have hLpos : (0 : Real) < logOrder n := by linarith
  have hnpos : (0 : Real) < (n : Real) := by nlinarith
  have hpown := aux_empty_two_pow_lower h5 hL hph2
  intro ell i hprof hlt hregion
  rw [selectedVertexMass_increment] at hregion
  have hmcap : selectedVertexMass
      (midpointPartialDiagonalSize (phaseNat n)) ell ≤ massCap := by omega
  have hmreal : ((selectedVertexMass
      (midpointPartialDiagonalSize (phaseNat n)) ell : Nat) : Real)
      ≤ (n : Real) * (logLogOrder n / (32 * logOrder n)) := by
    have h1 : ((selectedVertexMass
        (midpointPartialDiagonalSize (phaseNat n)) ell : Nat) : Real)
        ≤ (massCap : Real) := by exact_mod_cast hmcap
    linarith
  have hsL : ((phaseNat n - 2 : Nat) : Real) ≤ 4 * logOrder n := by
    have h1 : ((phaseNat n - 2 : Nat) : Real) ≤ (phaseNat n : Real) := by
      exact_mod_cast Nat.sub_le (phaseNat n) 2
    linarith
  have hsm : (phaseNat n - 2) + selectedVertexMass
      (midpointPartialDiagonalSize (phaseNat n)) ell ≤ n := by
    have hfrac : logLogOrder n / (32 * logOrder n) ≤ 1 / 32 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have hmn : ((selectedVertexMass
        (midpointPartialDiagonalSize (phaseNat n)) ell : Nat) : Real)
        ≤ (n : Real) / 32 := by
      have h := mul_le_mul_of_nonneg_left hfrac hnpos.le
      linarith
    have hsn : ((phaseNat n - 2 : Nat) : Real) ≤ (n : Real) / 640 := by
      nlinarith [mul_nonneg (show (0 : Real) ≤ logOrder n - 20 by linarith) hLpos.le]
    have hsum : ((phaseNat n - 2 : Nat) : Real) + ((selectedVertexMass
        (midpointPartialDiagonalSize (phaseNat n)) ell : Nat) : Real)
        ≤ (n : Real) := by linarith
    exact_mod_cast hsum
  have hlower := aux_empty_mu_shift_lower (n := n)
    (m := selectedVertexMass (midpointPartialDiagonalSize (phaseNat n)) ell)
    (s := phaseNat n - 2) hcpos hL hn128 hsm hsL hmreal hmu
  rw [← hSdef] at hlower
  have hpowv : ((n - selectedVertexMass
      (midpointPartialDiagonalSize (phaseNat n)) ell : Nat) : Real)
      ≤ 2 ^ (phaseNat n - 5) := by
    have h1 : ((n - selectedVertexMass
        (midpointPartialDiagonalSize (phaseNat n)) ell : Nat) : Real)
        ≤ (n : Real) := by
      exact_mod_cast Nat.sub_le n _
    linarith
  have hsize := aux_empty_mu_size_ge h5 hpowv i
  have hki : ((midpointMultiplicity n (phaseNat n) K i - ell i : Nat) : Real)
      ≤ (K : Real) := by
    have h1 : midpointMultiplicity n (phaseNat n) K i - ell i ≤ K :=
      le_trans (Nat.sub_le _ _) (hkK i)
    exact_mod_cast h1
  have hkinn : (0 : Real) ≤
      ((midpointMultiplicity n (phaseNat n) K i - ell i : Nat) : Real) :=
    Nat.cast_nonneg _
  calc ((midpointMultiplicity n (phaseNat n) K i - ell i : Nat) : Real) ^ 2
      ≤ (K : Real) ^ 2 := pow_le_pow_left₀ hkinn hki 2
    _ = 2 * X * (c * (n : Real) ^ 2 / (logOrder n * S)) := hKX
    _ ≤ 2 * X * mu (n - selectedVertexMass
          (midpointPartialDiagonalSize (phaseNat n)) ell) (phaseNat n - 2) :=
        mul_le_mul_of_nonneg_left hlower (by linarith)
    _ ≤ 2 * X * mu (n - selectedVertexMass
          (midpointPartialDiagonalSize (phaseNat n)) ell)
          (midpointPartialDiagonalSize (phaseNat n) i) :=
        mul_le_mul_of_nonneg_left hsize (by linarith)

/-- The zero profile lies in the empty range and has weight exactly one, so
the filtered sum is at least one. -/
private lemma aux_empty_one_le_sum {n K massCap : Nat} :
    (1 : Real) ≤ ∑ ell ∈ (partialSubprofileBox
        (midpointMultiplicity n (phaseNat n) K)).filter
        (fun ell => selectedVertexMass
          (midpointPartialDiagonalSize (phaseNat n)) ell ≤ massCap),
      partialDiagonalWeight n (midpointPartialDiagonalSize (phaseNat n))
        (midpointMultiplicity n (phaseNat n) K) ell := by
  have hzero : (fun _ => 0 : Fin 4 → Nat) ∈
      (partialSubprofileBox (midpointMultiplicity n (phaseNat n) K)).filter
        (fun ell => selectedVertexMass
          (midpointPartialDiagonalSize (phaseNat n)) ell ≤ massCap) := by
    refine Finset.mem_filter.mpr
      ⟨mem_partialSubprofileBox.mpr (fun i => Nat.zero_le _), ?_⟩
    have hz : selectedVertexMass
        (midpointPartialDiagonalSize (phaseNat n)) (fun _ => 0) = 0 := by
      simp [selectedVertexMass]
    rw [hz]
    exact Nat.zero_le _
  have hnn : ∀ ell ∈ (partialSubprofileBox
      (midpointMultiplicity n (phaseNat n) K)).filter
        (fun ell => selectedVertexMass
          (midpointPartialDiagonalSize (phaseNat n)) ell ≤ massCap),
      0 ≤ partialDiagonalWeight n (midpointPartialDiagonalSize (phaseNat n))
        (midpointMultiplicity n (phaseNat n) K) ell := by
    intro ell hell
    exact (partialDiagonalWeight_pos n _ _ ell
      (mem_partialSubprofileBox.mp (Finset.mem_filter.mp hell).1)).le
  have hsingle := Finset.single_le_sum hnn hzero
  rwa [partialDiagonalWeight_zero] at hsingle

/-- The total activity of the four coordinates is below `log (1 + epsilon)`. -/
private lemma aux_empty_activity_small {n K : Nat} {c X S epsilon : Real}
    (hcpos : 0 < c) (hepsilon : 0 < epsilon)
    (hL : (20 : Real) ≤ logOrder n)
    (hnpos : (0 : Real) < (n : Real))
    (hSdef : S = Real.exp (logLogOrder n / 2))
    (hS : 2 / (c * Real.log (1 + epsilon)) ≤ Real.exp (logLogOrder n / 2))
    (hXdef : X = (K : Real) ^ 2 * (logOrder n * S) / (2 * c * (n : Real) ^ 2))
    (hKL : (K : Real) * logOrder n ≤ (n : Real)) :
    4 * X ≤ Real.log (1 + epsilon) := by
  have hlogeps : (0 : Real) < Real.log (1 + epsilon) := Real.log_pos (by linarith)
  have hLpos : (0 : Real) < logOrder n := by linarith
  have hSpos : (0 : Real) < S := by
    rw [hSdef]
    exact Real.exp_pos _
  have hSS : S * S = logOrder n := by
    have hllval : logLogOrder n = Real.log (logOrder n) := rfl
    rw [hSdef, ← Real.exp_add]
    have hsum : logLogOrder n / 2 + logLogOrder n / 2 = Real.log (logOrder n) := by
      rw [← hllval]
      ring
    rw [hsum, Real.exp_log hLpos]
  have hKL2 : (K : Real) ^ 2 * logOrder n ^ 2 ≤ (n : Real) ^ 2 := by
    have hnn : (0 : Real) ≤ (K : Real) * logOrder n :=
      mul_nonneg (Nat.cast_nonneg K) hLpos.le
    have h := mul_self_le_mul_self hnn hKL
    nlinarith [h]
  have hcS : 2 / (c * S) ≤ Real.log (1 + epsilon) := by
    rw [div_le_iff₀ (mul_pos hcpos hSpos), ← hSdef] at *
    have h := (div_le_iff₀ (mul_pos hcpos hlogeps)).mp hS
    linarith
  have h4X : 4 * X ≤ 2 / (c * S) := by
    rw [hXdef, le_div_iff₀ (mul_pos hcpos hSpos)]
    have hexpand : 4 * ((K : Real) ^ 2 * (logOrder n * S) / (2 * c * (n : Real) ^ 2))
        * (c * S)
        = 2 * ((K : Real) ^ 2 * logOrder n * (S * S)) / ((n : Real) ^ 2) := by
      field_simp
      ring
    rw [hexpand, hSS, div_le_iff₀ (pow_pos hnpos 2)]
    linarith [hKL2]
  linarith

/-- Uniformly over every admissible midpoint rounding, the empty-range
partial-diagonal contribution lies between `1` and `1 + epsilon`. -/
theorem eventually_sum_midpointPartialDiagonal_empty_mem_Icc
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∀ᶠ n : Nat in atTop,
      ∀ K : Nat,
        MidpointRoundingAdmissible n (phaseNat n) K →
          (∑ ell ∈
              (partialSubprofileBox
                (midpointMultiplicity n (phaseNat n) K)).filter
                (fun ell => midpointPartialDiagonalEmptyRange n ell),
            partialDiagonalWeight n
              (midpointPartialDiagonalSize (phaseNat n))
              (midpointMultiplicity n (phaseNat n) K) ell) ∈
            Set.Icc (1 : Real) (1 + epsilon) := by
  obtain ⟨c, hcpos, hmuEv⟩ := exists_pos_eventually_mu_phaseNat_sub_two_lower_bound
  have hlogeps : (0 : Real) < Real.log (1 + epsilon) := Real.log_pos (by linarith)
  have hL20 : ∀ᶠ n : Nat in atTop, (20 : Real) ≤ logOrder n :=
    tendsto_logOrder_atTop.eventually_ge_atTop 20
  have hexpTend : Tendsto (fun n : Nat => Real.exp (logLogOrder n / 2)) atTop atTop :=
    Real.tendsto_exp_atTop.comp
      (tendsto_logLogOrder_atTop.atTop_div_const (by norm_num))
  have hSbig : ∀ᶠ n : Nat in atTop,
      2 / (c * Real.log (1 + epsilon)) ≤ Real.exp (logLogOrder n / 2) :=
    hexpTend.eventually_ge_atTop _
  have hn128Ev : ∀ᶠ n : Nat in atTop, 128 * logOrder n ^ 2 ≤ (n : Real) := by
    have hlittle :
        (fun n : Nat => logOrder n ^ 2) =o[atTop] (fun n : Nat => (n : Real)) := by
      simpa only [logOrder, Function.comp_def, id_eq] using
        (Real.isLittleO_pow_log_id_atTop (n := 2)).comp_tendsto
          (tendsto_natCast_atTop_atTop (R := Real))
    have hb := hlittle.bound (show (0 : Real) < 1 / 128 by norm_num)
    filter_upwards [hb] with n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (Nat.cast_nonneg n)] at hn
    linarith
  have hphase2Ev : ∀ᶠ n : Nat in atTop, 2 * logOrder n ≤ (phaseNat n : Real) := by
    have hb := phaseNat_isEquivalent_scaled_logOrder.isLittleO.bound
      (show (0 : Real) < 1 / 10 by norm_num)
    filter_upwards [hb, hL20] with n hn hL
    simp only [Pi.sub_apply] at hn
    have hLpos : (0 : Real) < logOrder n := by linarith
    have hqpos := q_pos
    have hq1 : q < 0.7 := by
      show Real.log 2 < 0.7
      linarith [Real.log_two_lt_d9]
    have hGpos : (0 : Real) < 2 / q * logOrder n :=
      mul_pos (div_pos (by norm_num) hqpos) hLpos
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hGpos.le] at hn
    have habs := abs_le.mp hn
    have h20q : (20 : Real) / 9 ≤ 2 / q := by
      rw [div_le_div_iff₀ (by norm_num) hqpos]
      nlinarith
    linarith [habs.1, mul_le_mul_of_nonneg_right h20q hLpos.le]
  filter_upwards [hL20, hSbig, hn128Ev, hphase2Ev,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
    hmuEv] with n hL hS hn128 hph2 hph4 hmu
  intro K hadm
  have h5 : 5 < phaseNat n := hadm.1
  have hLpos : (0 : Real) < logOrder n := by linarith
  have hnpos : (0 : Real) < (n : Real) := by nlinarith
  obtain ⟨hll1, hllle⟩ := aux_empty_logLog_bounds hL
  have hKL : (K : Real) * logOrder n ≤ (n : Real) :=
    aux_empty_K_mul_logOrder_le hadm hL hph2
  obtain ⟨S, hSdef⟩ : ∃ S : Real, S = Real.exp (logLogOrder n / 2) := ⟨_, rfl⟩
  have hSpos : (0 : Real) < S := by
    rw [hSdef]
    exact Real.exp_pos _
  have hetaval : midpointPartialDiagonalEta n
      = logLogOrder n / (32 * logOrder n) := rfl
  have hetaNonneg : (0 : Real) ≤ (n : Real) * midpointPartialDiagonalEta n := by
    have h : (0 : Real) ≤ midpointPartialDiagonalEta n := by
      rw [hetaval]
      exact div_nonneg (by linarith) (by linarith)
    exact mul_nonneg hnpos.le h
  obtain ⟨massCap, hcapdef⟩ :
      ∃ M : Nat, M = ⌊(n : Real) * midpointPartialDiagonalEta n⌋₊ := ⟨_, rfl⟩
  have hcapreal : (massCap : Real)
      ≤ (n : Real) * (logLogOrder n / (32 * logOrder n)) := by
    rw [hcapdef, ← hetaval]
    exact Nat.floor_le hetaNonneg
  have hcapn : massCap ≤ n := by
    have hle1 : logLogOrder n / (32 * logOrder n) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have h1 : (massCap : Real) ≤ (n : Real) := by
      nlinarith [hcapreal, hnpos]
    exact_mod_cast h1
  have hfiltereq :
      (partialSubprofileBox (midpointMultiplicity n (phaseNat n) K)).filter
          (fun ell => midpointPartialDiagonalEmptyRange n ell)
        = (partialSubprofileBox (midpointMultiplicity n (phaseNat n) K)).filter
          (fun ell => selectedVertexMass
            (midpointPartialDiagonalSize (phaseNat n)) ell ≤ massCap) := by
    apply Finset.filter_congr
    intro ell _
    simp only [midpointPartialDiagonalEmptyRange]
    constructor
    · intro hell
      rw [hcapdef]
      exact (Nat.le_floor_iff hetaNonneg).mpr hell
    · intro hell
      have h2 : ((selectedVertexMass
          (midpointPartialDiagonalSize (phaseNat n)) ell : Nat) : Real)
          ≤ (massCap : Real) := by exact_mod_cast hell
      rw [hetaval]
      linarith [hcapreal]
  rw [hfiltereq]
  refine Set.mem_Icc.mpr ⟨aux_empty_one_le_sum, ?_⟩
  obtain ⟨X, hXdef⟩ : ∃ X : Real,
      X = (K : Real) ^ 2 * (logOrder n * S) / (2 * c * (n : Real) ^ 2) := ⟨_, rfl⟩
  have h2cn : (0 : Real) < 2 * c * (n : Real) ^ 2 :=
    mul_pos (by linarith) (pow_pos hnpos 2)
  have hXnn : (0 : Real) ≤ X := by
    rw [hXdef]
    exact div_nonneg
      (mul_nonneg (sq_nonneg _) (mul_nonneg hLpos.le hSpos.le)) h2cn.le
  have hKX : (K : Real) ^ 2 = 2 * X * (c * (n : Real) ^ 2 / (logOrder n * S)) := by
    rw [hXdef]
    field_simp
  have hstep := sum_partialDiagonalWeight_le_exp_sum_of_mu_lower_on_mass
    n massCap (midpointPartialDiagonalSize (phaseNat n))
    (midpointMultiplicity n (phaseNat n) K) (fun _ => X)
    (fun _ => hXnn) hcapn
    (aux_empty_mu_step hcpos h5 hL hn128 hph2 hph4.2 hmu hSdef hcapreal hXnn hKX
      (fun i => aux_empty_multiplicity_le hadm i))
  have hsumxi : (∑ _i : Fin 4, X) = 4 * X := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  have h4X : 4 * X ≤ Real.log (1 + epsilon) :=
    aux_empty_activity_small hcpos hepsilon hL hnpos hSdef hS hXdef hKL
  calc (∑ ell ∈ (partialSubprofileBox
          (midpointMultiplicity n (phaseNat n) K)).filter
          (fun ell => selectedVertexMass
            (midpointPartialDiagonalSize (phaseNat n)) ell ≤ massCap),
        partialDiagonalWeight n (midpointPartialDiagonalSize (phaseNat n))
          (midpointMultiplicity n (phaseNat n) K) ell)
      ≤ Real.exp (∑ _i : Fin 4, X) := hstep
    _ = Real.exp (4 * X) := by rw [hsumxi]
    _ ≤ Real.exp (Real.log (1 + epsilon)) := Real.exp_le_exp.mpr h4X
    _ = 1 + epsilon := Real.exp_log (by linarith)

end

end Erdos625
