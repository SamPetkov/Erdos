import Erdos625.PhaseConsequences
import Erdos625HP.FullCornerSharp
import Erdos625HP.HomogeneousPackingAndBorelCantelli
import Erdos625HP.SelfContainedSecondMomentCore

/-!
# Stirling-free factorial/profile bounds, homogeneous-packing tails, and `L^p` convergence

This module kernel-checks the remaining analytic, combinatorial, and probabilistic
pillars of the 15-page v5 manuscript:

1. **Elementary Stirling-free factorial bounds (`eq:elem-fact`, `(1.1)`):**
   * `pow_mul_exp_neg_le_factorial`: `m^m * exp(-m) ≤ m!` for all `m : ℕ` (with `0^0 = 1`).
   * `factorial_le_exp_mul_succ_mul_pow_mul_exp_neg`: `m! ≤ e * (m + 1) * m^m * exp(-m)`
     for all `m : ℕ`.
   * `factorial_div_le_one_sub_rpow_mul_exp_neg`: for `0 ≤ s < n`,
     `n! / ((n - s)! * n^s) ≤ (1 - s / n) ^ (-(n - s + 1)) * exp(-s)`.

2. **Chromatic upper bound (`Main Theorem` proof, `0 ≤ ζ(G) ≤ χ(G) ≤ n`):**
   * `chromaticNumberNat_le_card`: `chromaticNumberNat G ≤ Fintype.card V` for every
     finite simple graph `G` (paired with `Erdos625.cochromaticNumber_le_chromaticNumber`).

3. **Stirling-free Section 4 first-moment bound & Appendix C `log W(ν)` bounds:**
   * `profileColoringExpectation_toReal_le_exp_mul_succ_mul_exp`: exact non-Stirling
     Section 4 bound `E[X̄_k] ≤ e * (n + 1) * exp(𝓛_k)` on `Erdos625.profileColoringExpectation`.
   * `log_partialDiagonalWeight_le` and `log_partialDiagonalWeight_self_ge`: exact finite
     non-Stirling upper bound (`+(2 * |I| + 1) * log(e * (n + 1))`) on `log W(ν)` and
     lower bound (`-log(e * (n + 1))`) on `log W(k)` for `Erdos625.partialDiagonalWeight`.

4. **Homogeneous-packing entropy bound & unconditional `G(n, 1/2)` tail bounds (`Proposition 4.1(ii)–(iii)`):**
   * `randomGraph_maxDisjointHomogeneousEq_ge_le_entropy`: exact finite entropy display
     bounding `P(H_u(G_n) ≥ m)` for `1 ≤ u`, `1 ≤ m`, and `m * u < n`.
   * `eventually_randomGraph_homogeneousPacking_alpha_tail`: unconditional `G(n, 1/2)`
     packing tail `P(H_α(G_n) ≥ ⌈8 n ℓ / L²⌉) ≤ exp(-200 n ℓ² / L²)` of Proposition 4.1(ii).
   * `eventually_randomGraph_homogeneousPacking_alpha_sub_one_tail`: unconditional
     phase-uniform `G(n, 1/2)` packing tail `P(H_{α-1}(G_n) ≥ ⌈θ̄ n / (α - 1)⌉) ≤ exp(-θ̄ γ n)`
     of Proposition 4.1(iii) when `δ_n ∈ [0, δ_*]` and `g(θ̄) + (log 2 / 2)(T_{δ_n} - 1) ≥ 2 γ`.

5. **Conditional `L^p` (`1 ≤ p < ∞`) and expectation convergence (`Main Theorem`):**
   * `tendsto_integral_abs_sub_rpow_normalizedGap_of_polylog_tail` and
     `tendsto_expected_normalizedGap_of_polylog_tail`: from the Main Theorem's
     `O_ε(n^{-3/2} (log n)^{β + 5/2})` single-`n` deviation tail, deduce `L^p` convergence
     to `1 / 4` for every `1 ≤ p < ∞` and `(log₂ n)³ / n · E[χ(G_n) - ζ(G_n)] → 1 / 4`.
-/

namespace Erdos625HP

open Erdos625 Erdos625.FiveSizeEntropyGap Filter Asymptotics MeasureTheory Set
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

noncomputable section

/-! ## 1. Elementary Stirling-free factorial bounds (`eq:elem-fact`, `(1.1)`) -/

private theorem pow_div_succ_pow_succ_le_exp_neg_one (m : ℕ) :
    ((m : ℝ) / ((m : ℝ) + 1)) ^ (m + 1) ≤ Real.exp (-1) := by
  have hm1_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have h1 : (m : ℝ) / ((m : ℝ) + 1) = -1 / ((m : ℝ) + 1) + 1 := by
    field_simp [hm1_pos.ne']
    ring
  have h2 : (m : ℝ) / ((m : ℝ) + 1) ≤ Real.exp (-1 / ((m : ℝ) + 1)) := by
    rw [h1]
    exact Real.add_one_le_exp (-1 / ((m : ℝ) + 1))
  calc ((m : ℝ) / ((m : ℝ) + 1)) ^ (m + 1)
      ≤ (Real.exp (-1 / ((m : ℝ) + 1))) ^ (m + 1) :=
        pow_le_pow_left₀ (by positivity) h2 (m + 1)
    _ = Real.exp (((m + 1 : ℕ) : ℝ) * (-1 / ((m : ℝ) + 1))) :=
        (Real.exp_nat_mul _ (m + 1)).symm
    _ = Real.exp (-1) := by
        congr 1
        push_cast
        field_simp [hm1_pos.ne']

/-- **First inequality of `(1.1)` (`eq:elem-fact`):**
for all `m : ℕ` (with `0 ^ 0 = 1`), `m ^ m * exp (-m) ≤ m!`. -/
theorem pow_mul_exp_neg_le_factorial (m : ℕ) :
    (m : ℝ) ^ m * Real.exp (-(m : ℝ)) ≤ (m.factorial : ℝ) := by
  induction m with
  | zero =>
    norm_num [Real.exp_zero]
  | succ m ih =>
    rcases eq_or_lt_of_le (Nat.zero_le m) with rfl | hm_pos
    · norm_num
    · have hmR_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
      have h1 : ((m : ℝ) + 1) / (m : ℝ) ≤ Real.exp (1 / (m : ℝ)) := by
        have heq : ((m : ℝ) + 1) / (m : ℝ) = 1 / (m : ℝ) + 1 := by
          field_simp [hmR_pos.ne']
          ring
        rw [heq]
        exact Real.add_one_le_exp (1 / (m : ℝ))
      have hpow : (((m : ℝ) + 1) / (m : ℝ)) ^ m ≤ Real.exp 1 := by
        calc (((m : ℝ) + 1) / (m : ℝ)) ^ m
            ≤ (Real.exp (1 / (m : ℝ))) ^ m :=
              pow_le_pow_left₀ (by positivity) h1 m
          _ = Real.exp ((m : ℝ) * (1 / (m : ℝ))) :=
              (Real.exp_nat_mul _ m).symm
          _ = Real.exp 1 := by
              congr 1
              field_simp [hmR_pos.ne']
      have hstep : ((m : ℝ) + 1) ^ m * Real.exp (-1) ≤ (m : ℝ) ^ m := by
        rw [div_pow, div_le_iff₀ (pow_pos hmR_pos m)] at hpow
        have hexp_mul : Real.exp 1 * Real.exp (-1) = 1 := by
          rw [← Real.exp_add]
          norm_num
        calc ((m : ℝ) + 1) ^ m * Real.exp (-1)
            ≤ (Real.exp 1 * (m : ℝ) ^ m) * Real.exp (-1) :=
              mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
          _ = (Real.exp 1 * Real.exp (-1)) * (m : ℝ) ^ m := by ring
          _ = (m : ℝ) ^ m := by rw [hexp_mul, one_mul]
      calc ((m + 1 : ℕ) : ℝ) ^ (m + 1) * Real.exp (-((m + 1 : ℕ) : ℝ))
          = ((m : ℝ) + 1) * (((m : ℝ) + 1) ^ m * Real.exp (-1)) *
              Real.exp (-(m : ℝ)) := by
            push_cast
            rw [pow_succ, show -((m : ℝ) + 1) = -(m : ℝ) + (-1 : ℝ) by ring,
              Real.exp_add]
            ring
        _ ≤ ((m : ℝ) + 1) * (m : ℝ) ^ m * Real.exp (-(m : ℝ)) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hstep (by positivity))
              (Real.exp_pos _).le
        _ = ((m : ℝ) + 1) * ((m : ℝ) ^ m * Real.exp (-(m : ℝ))) := by ring
        _ ≤ ((m : ℝ) + 1) * (m.factorial : ℝ) :=
            mul_le_mul_of_nonneg_left ih (by positivity)
        _ = ((m + 1).factorial : ℝ) := by
            rw [Nat.factorial_succ]
            push_cast
            ring

private theorem factorial_le_exp_mul_pow_succ_mul_exp_neg {m : ℕ} (hm : 1 ≤ m) :
    (m.factorial : ℝ) ≤ Real.exp 1 * (m : ℝ) ^ (m + 1) * Real.exp (-(m : ℝ)) := by
  induction m with
  | zero => omega
  | succ k ih =>
    rcases eq_or_lt_of_le (Nat.zero_le k) with rfl | hk_pos
    · norm_num
      rw [mul_comm, ← Real.exp_add]
      norm_num
    · have hk1 : 1 ≤ k := hk_pos
      have hk_ih := ih hk1
      have hpow_step : (k : ℝ) ^ (k + 1) ≤ ((k : ℝ) + 1) ^ (k + 1) * Real.exp (-1) := by
        have hdiv := pow_div_succ_pow_succ_le_exp_neg_one k
        have hk1_pos : (0 : ℝ) < ((k : ℝ) + 1) ^ (k + 1) := by positivity
        rwa [div_pow, div_le_iff₀ hk1_pos, mul_comm (Real.exp (-1))] at hdiv
      calc ((k + 1).factorial : ℝ)
          = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
            rw [Nat.factorial_succ]
            push_cast
            ring
        _ ≤ ((k : ℝ) + 1) * (Real.exp 1 * (k : ℝ) ^ (k + 1) * Real.exp (-(k : ℝ))) :=
            mul_le_mul_of_nonneg_left hk_ih (by positivity)
        _ = Real.exp 1 * ((k : ℝ) + 1) * (k : ℝ) ^ (k + 1) * Real.exp (-(k : ℝ)) := by
            ring
        _ ≤ Real.exp 1 * ((k : ℝ) + 1) *
              (((k : ℝ) + 1) ^ (k + 1) * Real.exp (-1)) * Real.exp (-(k : ℝ)) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpow_step (by positivity))
              (Real.exp_pos _).le
        _ = Real.exp 1 * ((k + 1 : ℕ) : ℝ) ^ (k + 2) *
              Real.exp (-((k + 1 : ℕ) : ℝ)) := by
            push_cast
            rw [pow_succ, show -((k : ℝ) + 1) = (-1 : ℝ) + -(k : ℝ) by ring,
              Real.exp_add]
            ring

/-- **Second inequality of `(1.1)` (`eq:elem-fact`):**
for all `m : ℕ`, `m! ≤ e * (m + 1) * m ^ m * exp (-m)`. -/
theorem factorial_le_exp_mul_succ_mul_pow_mul_exp_neg (m : ℕ) :
    (m.factorial : ℝ) ≤
      Real.exp 1 * ((m : ℝ) + 1) * (m : ℝ) ^ m * Real.exp (-(m : ℝ)) := by
  rcases eq_or_lt_of_le (Nat.zero_le m) with rfl | hm_pos
  · norm_num
  · calc (m.factorial : ℝ)
        ≤ Real.exp 1 * (m : ℝ) ^ (m + 1) * Real.exp (-(m : ℝ)) :=
          factorial_le_exp_mul_pow_succ_mul_exp_neg hm_pos
      _ = Real.exp 1 * (m : ℝ) * (m : ℝ) ^ m * Real.exp (-(m : ℝ)) := by
          rw [pow_succ]
          ring
      _ ≤ Real.exp 1 * ((m : ℝ) + 1) * (m : ℝ) ^ m * Real.exp (-(m : ℝ)) := by
          gcongr
          linarith

/-- **Third inequality of `(1.1)` (`eq:elem-fact`):**
for `0 ≤ s < n`, `n! / ((n - s)! * n ^ s) ≤ (1 - s / n) ^ (-(n - s + 1)) * exp (-s)`. -/
theorem factorial_div_le_one_sub_rpow_mul_exp_neg {n s : ℕ} (hsn : s < n) :
    (n.factorial : ℝ) / (((n - s).factorial : ℝ) * (n : ℝ) ^ s) ≤
      (1 - (s : ℝ) / (n : ℝ)) ^ (-((n - s + 1 : ℕ) : ℝ)) * Real.exp (-(s : ℝ)) := by
  induction s with
  | zero =>
    have hnf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    simp [div_self hnf]
  | succ s ih =>
    have hs_lt : s < n := by omega
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    let m : ℕ := n - (s + 1)
    have hm_pos : 1 ≤ m := by dsimp [m]; omega
    have hns_eq : n - s = m + 1 := by dsimp [m]; omega
    have h1ms_eq : 1 - (s : ℝ) / (n : ℝ) = ((m : ℝ) + 1) / (n : ℝ) := by
      have hcast : ((n - s : ℕ) : ℝ) = (m : ℝ) + 1 := by
        rw [hns_eq]
        push_cast
        rfl
      calc 1 - (s : ℝ) / (n : ℝ)
          = ((n : ℝ) - (s : ℝ)) / (n : ℝ) := by field_simp [hn_pos.ne']
        _ = ((n - s : ℕ) : ℝ) / (n : ℝ) := by rw [Nat.cast_sub hs_lt.le]
        _ = ((m : ℝ) + 1) / (n : ℝ) := by rw [hcast]
    have h1ms1_eq : 1 - ((s + 1 : ℕ) : ℝ) / (n : ℝ) = (m : ℝ) / (n : ℝ) := by
      have hcast : ((n - (s + 1) : ℕ) : ℝ) = (m : ℝ) := rfl
      calc 1 - ((s + 1 : ℕ) : ℝ) / (n : ℝ)
          = ((n : ℝ) - ((s + 1 : ℕ) : ℝ)) / (n : ℝ) := by field_simp [hn_pos.ne']
        _ = ((n - (s + 1) : ℕ) : ℝ) / (n : ℝ) := by rw [Nat.cast_sub hsn.le]
        _ = (m : ℝ) / (n : ℝ) := by rw [hcast]
    have ha_pos : 0 < 1 - (s : ℝ) / (n : ℝ) := by rw [h1ms_eq]; positivity
    have hb_pos : 0 < 1 - ((s + 1 : ℕ) : ℝ) / (n : ℝ) := by
      rw [h1ms1_eq]
      exact div_pos (by exact_mod_cast hm_pos) hn_pos
    have hlhs_step :
        (n.factorial : ℝ) / (((n - (s + 1)).factorial : ℝ) * (n : ℝ) ^ (s + 1)) =
          ((n.factorial : ℝ) / (((n - s).factorial : ℝ) * (n : ℝ) ^ s)) *
            (1 - (s : ℝ) / (n : ℝ)) := by
      have hfac : ((n - s).factorial : ℝ) =
          (((m : ℝ) + 1)) * ((n - (s + 1)).factorial : ℝ) := by
        change ((n - s).factorial : ℝ) = ((m : ℝ) + 1) * (m.factorial : ℝ)
        rw [hns_eq, Nat.factorial_succ]
        push_cast
        ring
      have hmf_ne : ((n - (s + 1)).factorial : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (n - (s + 1))
      have hm1_ne : (m : ℝ) + 1 ≠ 0 := by positivity
      rw [h1ms_eq, hfac, pow_succ]
      field_simp [hmf_ne, hm1_ne, hn_pos.ne']
    have hrpow_a :
        (1 - (s : ℝ) / (n : ℝ)) ^ (-((n - s + 1 : ℕ) : ℝ)) *
            (1 - (s : ℝ) / (n : ℝ)) =
          (((1 - (s : ℝ) / (n : ℝ)) ^ (m + 1))⁻¹) := by
      have hexp_eq : ((n - s + 1 : ℕ) : ℝ) = ((m + 2 : ℕ) : ℝ) := by
        congr 1; omega
      rw [hexp_eq, Real.rpow_neg ha_pos.le, Real.rpow_natCast, pow_succ, mul_inv_rev,
        mul_right_comm, inv_mul_cancel₀ ha_pos.ne', one_mul]
    have hrpow_b :
        (1 - ((s + 1 : ℕ) : ℝ) / (n : ℝ)) ^ (-((n - (s + 1) + 1 : ℕ) : ℝ)) =
          (((1 - ((s + 1 : ℕ) : ℝ) / (n : ℝ)) ^ (m + 1))⁻¹) := by
      have hexp_eq : ((n - (s + 1) + 1 : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) := rfl
      rw [hexp_eq, Real.rpow_neg hb_pos.le, Real.rpow_natCast]
    have hstep_inv :
        (((1 - (s : ℝ) / (n : ℝ)) ^ (m + 1))⁻¹) ≤
          (((1 - ((s + 1 : ℕ) : ℝ) / (n : ℝ)) ^ (m + 1))⁻¹) * Real.exp (-1) := by
      have hquot :
          (1 - ((s + 1 : ℕ) : ℝ) / (n : ℝ)) / (1 - (s : ℝ) / (n : ℝ)) =
            (m : ℝ) / ((m : ℝ) + 1) := by
        rw [h1ms1_eq, h1ms_eq]
        field_simp [hn_pos.ne', (show (m : ℝ) + 1 ≠ 0 by positivity)]
      have hpow_le :
          ((1 - ((s + 1 : ℕ) : ℝ) / (n : ℝ)) / (1 - (s : ℝ) / (n : ℝ))) ^ (m + 1) ≤
            Real.exp (-1) := by
        rw [hquot]
        exact pow_div_succ_pow_succ_le_exp_neg_one m
      have hapow_pos : 0 < (1 - (s : ℝ) / (n : ℝ)) ^ (m + 1) := pow_pos ha_pos (m + 1)
      have hbpow_pos : 0 < (1 - ((s + 1 : ℕ) : ℝ) / (n : ℝ)) ^ (m + 1) :=
        pow_pos hb_pos (m + 1)
      rw [div_pow, div_le_iff₀ hapow_pos] at hpow_le
      rw [inv_eq_one_div, inv_eq_one_div, one_div_mul_eq_div,
        div_le_div_iff₀ hapow_pos hbpow_pos]
      linarith
    calc (n.factorial : ℝ) / (((n - (s + 1)).factorial : ℝ) * (n : ℝ) ^ (s + 1))
        = ((n.factorial : ℝ) / (((n - s).factorial : ℝ) * (n : ℝ) ^ s)) *
            (1 - (s : ℝ) / (n : ℝ)) := hlhs_step
      _ ≤ ((1 - (s : ℝ) / (n : ℝ)) ^ (-((n - s + 1 : ℕ) : ℝ)) * Real.exp (-(s : ℝ))) *
            (1 - (s : ℝ) / (n : ℝ)) :=
          mul_le_mul_of_nonneg_right (ih hs_lt) ha_pos.le
      _ = (((1 - (s : ℝ) / (n : ℝ)) ^ (m + 1))⁻¹) * Real.exp (-(s : ℝ)) := by
          calc ((1 - (s : ℝ) / (n : ℝ)) ^ (-((n - s + 1 : ℕ) : ℝ)) * Real.exp (-(s : ℝ))) *
                (1 - (s : ℝ) / (n : ℝ))
              = ((1 - (s : ℝ) / (n : ℝ)) ^ (-((n - s + 1 : ℕ) : ℝ)) *
                  (1 - (s : ℝ) / (n : ℝ))) * Real.exp (-(s : ℝ)) := by ring
            _ = (((1 - (s : ℝ) / (n : ℝ)) ^ (m + 1))⁻¹) * Real.exp (-(s : ℝ)) := by
                rw [hrpow_a]
      _ ≤ ((((1 - ((s + 1 : ℕ) : ℝ) / (n : ℝ)) ^ (m + 1))⁻¹) * Real.exp (-1)) *
            Real.exp (-(s : ℝ)) :=
          mul_le_mul_of_nonneg_right hstep_inv (Real.exp_pos _).le
      _ = (1 - ((s + 1 : ℕ) : ℝ) / (n : ℝ)) ^ (-((n - (s + 1) + 1 : ℕ) : ℝ)) *
            Real.exp (-((s + 1 : ℕ) : ℝ)) := by
          rw [hrpow_b]
          push_cast
          rw [show -((s : ℝ) + 1) = (-1 : ℝ) + -(s : ℝ) by ring, Real.exp_add]
          ring

/-! ## 2. Chromatic upper bound `χ(G) ≤ |V|` -/

/-- For every finite simple graph `G`, `chromaticNumberNat G ≤ Fintype.card V`
(paired with `Erdos625.cochromaticNumber_le_chromaticNumber` to give `0 ≤ ζ(G) ≤ χ(G) ≤ n`). -/
theorem chromaticNumberNat_le_card {V : Type*} [Fintype V] (G : SimpleGraph V) :
    chromaticNumberNat G ≤ Fintype.card V :=
  ENat.toNat_le_of_le_coe G.chromaticNumber_le_card

/-! ## 3. Stirling-free Section 4 first-moment bound & Appendix C `log W(ν)` bounds -/

private theorem factorialEntropyMain_le_log_factorial_elem (m : ℕ) :
    factorialEntropyMain m ≤ Real.log (m.factorial : ℝ) := by
  rcases eq_or_lt_of_le (Nat.zero_le m) with rfl | hm_pos
  · simp [factorialEntropyMain]
  · have hmR_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
    have hlow := pow_mul_exp_neg_le_factorial m
    have hlhs_pos : 0 < (m : ℝ) ^ m * Real.exp (-(m : ℝ)) := by positivity
    have hlog := Real.log_le_log hlhs_pos hlow
    rw [Real.log_mul (pow_pos hmR_pos m).ne' (Real.exp_pos _).ne',
      Real.log_pow, Real.log_exp] at hlog
    rw [factorialEntropyMain_of_pos hm_pos]
    linarith

private theorem log_factorial_le_factorialEntropyMain_add_log_exp_mul_succ (m : ℕ) :
    Real.log (m.factorial : ℝ) ≤
      factorialEntropyMain m + Real.log (Real.exp 1 * ((m : ℝ) + 1)) := by
  have hmf_pos : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hup := factorial_le_exp_mul_succ_mul_pow_mul_exp_neg m
  rcases eq_or_lt_of_le (Nat.zero_le m) with rfl | hm_pos
  · simp only [Nat.factorial_zero, Nat.cast_one, Real.log_one,
      factorialEntropyMain_zero, Nat.cast_zero, zero_add, mul_one]
    exact Real.log_nonneg (Real.one_le_exp zero_le_one)
  · have hmR_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
    have he_pos : 0 < Real.exp 1 * ((m : ℝ) + 1) := by positivity
    have hpow_pos : 0 < (m : ℝ) ^ m := pow_pos hmR_pos m
    have hlog := Real.log_le_log hmf_pos hup
    rw [Real.log_mul (mul_pos he_pos hpow_pos).ne' (Real.exp_pos _).ne',
      Real.log_mul he_pos.ne' hpow_pos.ne', Real.log_pow, Real.log_exp] at hlog
    rw [factorialEntropyMain_of_pos hm_pos]
    linarith

private theorem factorialEntropyMain_eq_mul_div (m : ℕ) {K : ℝ} (hK : 0 < K) :
    factorialEntropyMain m =
      K * (((m : ℝ) / K) * Real.log K + ((m : ℝ) / K) * Real.log ((m : ℝ) / K) -
        (m : ℝ) / K) := by
  rcases eq_or_lt_of_le (Nat.zero_le m) with rfl | hm_pos
  · simp [factorialEntropyMain]
  · have hmR_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
    rw [factorialEntropyMain_of_pos hm_pos, Real.log_div hmR_pos.ne' hK.ne']
    field_simp [hK.ne']
    ring

/-- **Section 4 Stirling-free profile first-moment bound (`main.tex`, Section 4):**
for every coloring profile `k : ColoringProfile b` of vertex mass `n`,
`E[X̄_k] ≤ e * (n + 1) * exp(𝓛_k)` where `𝓛_k = profileStirlingUpperMain n k`. -/
theorem profileColoringExpectation_toReal_le_exp_mul_succ_mul_exp
    {b : ℕ} (n : ℕ) (k : ColoringProfile b)
    (hMass : ColoringProfile.vertexMass k = n) :
    (profileColoringExpectation n k).toReal ≤
      Real.exp 1 * ((n : ℝ) + 1) * Real.exp (profileStirlingUpperMain n k) := by
  have hpos : 0 < profileColoringExpectation n k :=
    profileColoringExpectation_pos n k hMass
  have htop : profileColoringExpectation n k ≠ ⊤ := by
    rw [profileColoringExpectation_eq_enumerativeCoefficient_mul_of n k
      (profileEnumerationStatement n k hMass)]
    finiteness
  have hrpos : 0 < (profileColoringExpectation n k).toReal :=
    ENNReal.toReal_pos hpos.ne' htop
  have hn_ub := log_factorial_le_factorialEntropyMain_add_log_exp_mul_succ n
  have hk_lb : profileFactorialEntropyMain k ≤ profileLogFactorialSum k :=
    Finset.sum_le_sum fun i _ ↦ factorialEntropyMain_le_log_factorial_elem (k i)
  have hlog : Real.log (profileColoringExpectation n k).toReal ≤
      Real.log (Real.exp 1 * ((n : ℝ) + 1)) + profileStirlingUpperMain n k := by
    rw [log_profileColoringExpectation_toReal_eq_profileLogWeight n k hMass]
    simp only [profileLogFactorialSum] at hk_lb
    unfold profileLogWeight profileStirlingUpperMain
    linarith
  have he_pos : 0 < Real.exp 1 * ((n : ℝ) + 1) := by positivity
  calc (profileColoringExpectation n k).toReal
      ≤ Real.exp (Real.log (Real.exp 1 * ((n : ℝ) + 1)) + profileStirlingUpperMain n k) :=
        (Real.log_le_iff_le_exp hrpos).mp hlog
    _ = Real.exp 1 * ((n : ℝ) + 1) * Real.exp (profileStirlingUpperMain n k) := by
        rw [Real.exp_add, Real.exp_log he_pos]

/-- **Appendix C Stirling-free upper bound on `log W(ν)` (`Lemma 6.1(i)` proof):**
for any finite index type `I`, `1 ≤ n`, class sizes `u i ≥ 1`, full profile `k` of
vertex mass `n`, and subprofile `ν ≤ k`, `log (partialDiagonalWeight n u k ν)` is
at most the exact finite entropy expression plus `(2 * |I| + 1) * log (e * (n + 1))`. -/
theorem log_partialDiagonalWeight_le {I : Type*} [Fintype I]
    {n : ℕ} {u k nu : I → ℕ}
    (hn : 1 ≤ n) (hu : ∀ i, 1 ≤ u i)
    (hMass : selectedVertexMass u k = n)
    (hnu : IsPartialSubprofile k nu) :
    let K : ℝ := (selectedBlockCount k : ℝ)
    let p : I → ℝ := fun i ↦ (k i : ℝ) / K
    let y : I → ℝ := fun i ↦ (nu i : ℝ) / K
    let z : I → ℝ := fun i ↦ ((k i - nu i : ℕ) : ℝ) / K
    let rho : ℝ := ((n - selectedVertexMass u nu : ℕ) : ℝ) / (n : ℝ)
    let E : I → ℝ := fun i ↦
      Real.log K + Real.log ((u i).factorial : ℝ) + (u i : ℝ) -
        (u i : ℝ) * Real.log (n : ℝ) + Real.log 2 * ((u i).choose 2 : ℝ) - Real.log 2
    Real.log (partialDiagonalWeight n u k nu) ≤
      (n : ℝ) * rho * Real.log rho +
        K * ∑ i : I,
          (2 * p i * Real.log (p i) - 2 * z i * Real.log (z i) -
            y i * Real.log (y i) - y i + y i * E i) +
        (2 * (Fintype.card I : ℝ) + 1) * Real.log (Real.exp 1 * ((n : ℝ) + 1)) := by
  intro K p y z rho E
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hK_nat_pos : 0 < selectedBlockCount k := by
    by_contra hK0
    have hall0 : ∀ i, k i = 0 := by
      have hsum0 : ∑ i : I, k i = 0 := Nat.eq_zero_of_not_pos hK0
      exact fun i ↦ Finset.sum_eq_zero_iff.mp hsum0 i (Finset.mem_univ i)
    have hM0 : selectedVertexMass u k = 0 := by
      unfold selectedVertexMass
      simp [hall0]
    omega
  have hK_pos : 0 < K := by dsimp [K]; exact_mod_cast hK_nat_pos
  have hm_le_n : selectedVertexMass u nu ≤ n := by
    rw [← hMass]
    unfold selectedVertexMass
    exact Finset.sum_le_sum fun i _ ↦ Nat.mul_le_mul_left (u i) (hnu i)
  have hki_le_n : ∀ i : I, k i ≤ n := by
    intro i
    calc k i = 1 * k i := (one_mul _).symm
      _ ≤ u i * k i := Nat.mul_le_mul_right (k i) (hu i)
      _ ≤ ∑ j : I, u j * k j :=
          Finset.single_le_sum (f := fun j ↦ u j * k j)
            (fun j _ ↦ Nat.zero_le _) (Finset.mem_univ i)
      _ = n := hMass
  -- Exact log decomposition of `W(ν) = partialDiagonalWeight n u k nu`
  have hmark_pos : 0 < (partialMarkingCount k nu : ℝ) := by
    exact_mod_cast partialMarkingCount_pos k nu hnu
  have hY_pos : 0 < partialSignedFirstMoment n u nu := partialSignedFirstMoment_pos n u nu
  have hlog_W :
      Real.log (partialDiagonalWeight n u k nu) =
        Real.log (((n - selectedVertexMass u nu).factorial : ℝ)) -
          Real.log (n.factorial : ℝ) +
          ∑ i : I,
            (2 * Real.log ((k i).factorial : ℝ) -
              2 * Real.log (((k i - nu i).factorial : ℝ)) -
              Real.log ((nu i).factorial : ℝ) +
              (nu i : ℝ) * Real.log ((u i).factorial : ℝ) +
              (nu i : ℝ) * (((u i).choose 2 : ℝ) * Real.log 2 - Real.log 2)) := by
    unfold partialDiagonalWeight
    rw [Real.log_div hmark_pos.ne' hY_pos.ne']
    unfold partialSignedFirstMoment partialMarkingCount
      partialProfileFactorialProduct selectedBlockCount selectedInternalEdgeCount
    have h2b_pos : (0 : ℝ) < (2 : ℝ) ^ (∑ i : I, nu i) := by positivity
    have hnf_pos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hnrem_pos : (0 : ℝ) < ((n - selectedVertexMass u nu).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    have hpf_pos : (0 : ℝ) < ((∏ i : I, (u i).factorial ^ nu i * (nu i).factorial : ℕ) : ℝ) := by
      exact_mod_cast Finset.prod_pos fun i _ ↦
        mul_pos (pow_pos (Nat.factorial_pos _) _) (Nat.factorial_pos _)
    have h2e_pos : (0 : ℝ) < (2 : ℝ) ^ (∑ i : I, (u i).choose 2 * nu i) := by positivity
    rw [Real.log_div (mul_pos h2b_pos hnf_pos).ne'
        (mul_pos (mul_pos hnrem_pos hpf_pos) h2e_pos).ne',
      Real.log_mul h2b_pos.ne' hnf_pos.ne',
      Real.log_mul (mul_pos hnrem_pos hpf_pos).ne' h2e_pos.ne',
      Real.log_mul hnrem_pos.ne' hpf_pos.ne',
      Real.log_pow, Real.log_pow]
    have hlog_mark :
        Real.log ((∏ i : I, (k i).choose (nu i) ^ 2 : ℕ) : ℝ) =
          ∑ i : I,
            (2 * Real.log ((k i).factorial : ℝ) -
              2 * Real.log ((nu i).factorial : ℝ) -
              2 * Real.log (((k i - nu i).factorial : ℝ))) := by
      rw [Nat.cast_prod, Real.log_prod (fun i _ ↦ by
        exact_mod_cast (pow_pos (Nat.choose_pos (hnu i)) 2).ne')]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hch_id : ((k i).choose (nu i) : ℝ) * ((nu i).factorial : ℝ) *
          (((k i - nu i).factorial : ℝ)) = ((k i).factorial : ℝ) := by
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial (hnu i)
      have hc_ne : ((k i).choose (nu i) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.choose_pos (hnu i)).ne'
      have hnuf_ne : ((nu i).factorial : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero _
      have hkf_ne : (((k i - nu i).factorial : ℝ)) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero _
      have hlog_id := congrArg Real.log hch_id
      rw [Real.log_mul (mul_ne_zero hc_ne hnuf_ne) hkf_ne,
        Real.log_mul hc_ne hnuf_ne] at hlog_id
      rw [Nat.cast_pow, Real.log_pow]
      push_cast
      linarith
    have hlog_pf :
        Real.log ((∏ i : I, (u i).factorial ^ nu i * (nu i).factorial : ℕ) : ℝ) =
          ∑ i : I, ((nu i : ℝ) * Real.log ((u i).factorial : ℝ) +
            Real.log ((nu i).factorial : ℝ)) := by
      rw [Nat.cast_prod, Real.log_prod (fun i _ ↦ by
        exact_mod_cast (mul_pos (pow_pos (Nat.factorial_pos _) _) (Nat.factorial_pos _)).ne')]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have h1 : (((u i).factorial ^ nu i : ℕ) : ℝ) ≠ 0 := by positivity
      have h2 : ((nu i).factorial : ℝ) ≠ 0 := by positivity
      rw [Nat.cast_mul, Real.log_mul h1 h2, Nat.cast_pow, Real.log_pow]
    rw [hlog_mark, hlog_pf, Nat.cast_sum, Finset.sum_mul, Nat.cast_sum, Finset.sum_mul]
    simp only [Nat.cast_mul]
    have hsum_rhs :
        ∑ i : I,
            (2 * Real.log ((k i).factorial : ℝ) -
              2 * Real.log (((k i - nu i).factorial : ℝ)) -
              Real.log ((nu i).factorial : ℝ) +
              (nu i : ℝ) * Real.log ((u i).factorial : ℝ) +
              (nu i : ℝ) * (((u i).choose 2 : ℝ) * Real.log 2 - Real.log 2)) =
          (∑ i : I,
              (2 * Real.log ((k i).factorial : ℝ) -
                2 * Real.log ((nu i).factorial : ℝ) -
                2 * Real.log (((k i - nu i).factorial : ℝ)))) -
            (∑ i : I, (nu i : ℝ) * Real.log 2) +
            (∑ i : I, ((nu i : ℝ) * Real.log ((u i).factorial : ℝ) +
              Real.log ((nu i).factorial : ℝ))) +
            (∑ i : I, ((u i).choose 2 : ℝ) * (nu i : ℝ) * Real.log 2) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hsum_rhs]
    ring
  -- Bound the vertex-factorial difference `log((n - m_ν)!) - log(n!)`
  have hrem_log_le :
      Real.log (((n - selectedVertexMass u nu).factorial : ℝ)) -
          Real.log (n.factorial : ℝ) ≤
        (n : ℝ) * rho * Real.log rho -
          (selectedVertexMass u nu : ℝ) * Real.log (n : ℝ) +
          (selectedVertexMass u nu : ℝ) +
          Real.log (Real.exp 1 * ((n : ℝ) + 1)) := by
    have hub := log_factorial_le_factorialEntropyMain_add_log_exp_mul_succ
      (n - selectedVertexMass u nu)
    have hlb := factorialEntropyMain_le_log_factorial_elem n
    have hlog_mono :
        Real.log (Real.exp 1 * (((n - selectedVertexMass u nu : ℕ) : ℝ) + 1)) ≤
          Real.log (Real.exp 1 * ((n : ℝ) + 1)) := by
      apply Real.log_le_log (by positivity)
      gcongr
      exact_mod_cast Nat.sub_le n (selectedVertexMass u nu)
    have hent_rem := factorialEntropyMain_eq_mul_div (n - selectedVertexMass u nu) hn_pos
    have hent_n := factorialEntropyMain_of_pos hn
    have hm_cast : ((n - selectedVertexMass u nu : ℕ) : ℝ) =
        (n : ℝ) - (selectedVertexMass u nu : ℝ) := Nat.cast_sub hm_le_n
    have hrho_def : ((n - selectedVertexMass u nu : ℕ) : ℝ) / (n : ℝ) = rho := rfl
    rw [hrho_def] at hent_rem
    have halg :
        (n : ℝ) * (rho * Real.log (n : ℝ) + rho * Real.log rho - rho) -
            ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ)) =
          (n : ℝ) * rho * Real.log rho -
            (selectedVertexMass u nu : ℝ) * Real.log (n : ℝ) +
            (selectedVertexMass u nu : ℝ) := by
      dsimp [rho]
      rw [hm_cast]
      field_simp [hn_pos.ne']
      ring
    linarith
  -- Bound each coordinate `i : I`
  have hcoord_le : ∀ i : I,
      2 * Real.log ((k i).factorial : ℝ) -
          2 * Real.log (((k i - nu i).factorial : ℝ)) -
          Real.log ((nu i).factorial : ℝ) +
          (nu i : ℝ) * Real.log ((u i).factorial : ℝ) +
          (nu i : ℝ) * (((u i).choose 2 : ℝ) * Real.log 2 - Real.log 2) -
          (u i : ℝ) * (nu i : ℝ) * Real.log (n : ℝ) +
          (u i : ℝ) * (nu i : ℝ) ≤
        K * (2 * p i * Real.log (p i) - 2 * z i * Real.log (z i) -
            y i * Real.log (y i) - y i + y i * E i) +
          2 * Real.log (Real.exp 1 * ((n : ℝ) + 1)) := by
    intro i
    have hki_ub := log_factorial_le_factorialEntropyMain_add_log_exp_mul_succ (k i)
    have hlog_ki : Real.log (Real.exp 1 * ((k i : ℝ) + 1)) ≤
        Real.log (Real.exp 1 * ((n : ℝ) + 1)) := by
      apply Real.log_le_log (by positivity)
      gcongr
      exact_mod_cast hki_le_n i
    have hzi_lb := factorialEntropyMain_le_log_factorial_elem (k i - nu i)
    have hyi_lb := factorialEntropyMain_le_log_factorial_elem (nu i)
    have hent_p := factorialEntropyMain_eq_mul_div (k i) hK_pos
    have hent_z := factorialEntropyMain_eq_mul_div (k i - nu i) hK_pos
    have hent_y := factorialEntropyMain_eq_mul_div (nu i) hK_pos
    have hsub_cast : ((k i - nu i : ℕ) : ℝ) = (k i : ℝ) - (nu i : ℝ) :=
      Nat.cast_sub (hnu i)
    have hpzy : z i = p i - y i := by
      dsimp [p, y, z]
      rw [hsub_cast]
      ring
    have hyK : K * y i = (nu i : ℝ) := by
      dsimp [y]
      field_simp [hK_pos.ne']
    have halg_coord :
        2 * factorialEntropyMain (k i) -
            2 * factorialEntropyMain (k i - nu i) -
            factorialEntropyMain (nu i) +
            (nu i : ℝ) * Real.log ((u i).factorial : ℝ) +
            (nu i : ℝ) * (((u i).choose 2 : ℝ) * Real.log 2 - Real.log 2) -
            (u i : ℝ) * (nu i : ℝ) * Real.log (n : ℝ) +
            (u i : ℝ) * (nu i : ℝ) =
          K * (2 * p i * Real.log (p i) - 2 * z i * Real.log (z i) -
              y i * Real.log (y i) - y i + y i * E i) := by
      rw [hent_p, hent_z, hent_y]
      change 2 * (K * (p i * Real.log K + p i * Real.log (p i) - p i)) -
          2 * (K * (z i * Real.log K + z i * Real.log (z i) - z i)) -
          K * (y i * Real.log K + y i * Real.log (y i) - y i) + _ + _ - _ + _ = _
      dsimp [E]
      rw [← hyK, hpzy]
      ring
    linarith
  -- Sum over `i : I` and combine with `hrem_log_le`
  have hsum_mass_log :
      (selectedVertexMass u nu : ℝ) * Real.log (n : ℝ) =
        ∑ i : I, (u i : ℝ) * (nu i : ℝ) * Real.log (n : ℝ) := by
    unfold selectedVertexMass
    rw [Nat.cast_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by push_cast; ring
  have hsum_mass :
      (selectedVertexMass u nu : ℝ) = ∑ i : I, (u i : ℝ) * (nu i : ℝ) := by
    unfold selectedVertexMass
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by push_cast; rfl
  have hsum_coord := Finset.sum_le_sum (s := Finset.univ) fun (i : I) _ ↦ hcoord_le i
  have hrhs_sum :
      ∑ i : I,
          (K * (2 * p i * Real.log (p i) - 2 * z i * Real.log (z i) -
              y i * Real.log (y i) - y i + y i * E i) +
            2 * Real.log (Real.exp 1 * ((n : ℝ) + 1))) =
        K * ∑ i : I,
            (2 * p i * Real.log (p i) - 2 * z i * Real.log (z i) -
              y i * Real.log (y i) - y i + y i * E i) +
          (Fintype.card I : ℝ) * (2 * Real.log (Real.exp 1 * ((n : ℝ) + 1))) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.mul_sum]
  have hsplit_lhs :
      ∑ i : I,
          (2 * Real.log ((k i).factorial : ℝ) -
            2 * Real.log (((k i - nu i).factorial : ℝ)) -
            Real.log ((nu i).factorial : ℝ) +
            (nu i : ℝ) * Real.log ((u i).factorial : ℝ) +
            (nu i : ℝ) * (((u i).choose 2 : ℝ) * Real.log 2 - Real.log 2) -
            (u i : ℝ) * (nu i : ℝ) * Real.log (n : ℝ) +
            (u i : ℝ) * (nu i : ℝ)) =
        (∑ i : I,
          (2 * Real.log ((k i).factorial : ℝ) -
            2 * Real.log (((k i - nu i).factorial : ℝ)) -
            Real.log ((nu i).factorial : ℝ) +
            (nu i : ℝ) * Real.log ((u i).factorial : ℝ) +
            (nu i : ℝ) * (((u i).choose 2 : ℝ) * Real.log 2 - Real.log 2))) -
          (selectedVertexMass u nu : ℝ) * Real.log (n : ℝ) +
          (selectedVertexMass u nu : ℝ) := by
    rw [hsum_mass_log, hsum_mass, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  rw [hsplit_lhs, hrhs_sum] at hsum_coord
  have herr_ring :
      (Fintype.card I : ℝ) * (2 * Real.log (Real.exp 1 * ((n : ℝ) + 1))) +
          Real.log (Real.exp 1 * ((n : ℝ) + 1)) =
        (2 * (Fintype.card I : ℝ) + 1) * Real.log (Real.exp 1 * ((n : ℝ) + 1)) := by ring
  rw [hlog_W]
  linarith

/-- **Appendix C Stirling-free lower bound on `log W(k)` (`Lemma 6.1(i)` proof):**
at the full profile `ν = k` (`W(k) = 1 / E[Z_k^mk]`), `log (partialDiagonalWeight n u k k)`
is at least `K * ∑ i, (p i * log (p i) - p i + p i * E i) - log (e * (n + 1))`. -/
theorem log_partialDiagonalWeight_self_ge {I : Type*} [Fintype I]
    {n : ℕ} {u k : I → ℕ}
    (hn : 1 ≤ n)
    (hMass : selectedVertexMass u k = n) :
    let K : ℝ := (selectedBlockCount k : ℝ)
    let p : I → ℝ := fun i ↦ (k i : ℝ) / K
    let E : I → ℝ := fun i ↦
      Real.log K + Real.log ((u i).factorial : ℝ) + (u i : ℝ) -
        (u i : ℝ) * Real.log (n : ℝ) + Real.log 2 * ((u i).choose 2 : ℝ) - Real.log 2
    K * ∑ i : I, (p i * Real.log (p i) - p i + p i * E i) -
        Real.log (Real.exp 1 * ((n : ℝ) + 1)) ≤
      Real.log (partialDiagonalWeight n u k k) := by
  intro K p E
  have hK_nat_pos : 0 < selectedBlockCount k := by
    by_contra hK0
    have hall0 : ∀ i, k i = 0 := by
      have hsum0 : ∑ i : I, k i = 0 := Nat.eq_zero_of_not_pos hK0
      exact fun i ↦ Finset.sum_eq_zero_iff.mp hsum0 i (Finset.mem_univ i)
    have hM0 : selectedVertexMass u k = 0 := by
      unfold selectedVertexMass
      simp [hall0]
    omega
  have hK_pos : 0 < K := by dsimp [K]; exact_mod_cast hK_nat_pos
  have hmark1 : (partialMarkingCount k k : ℝ) = 1 := by
    unfold partialMarkingCount
    simp
  have hlog_Wk :
      Real.log (partialDiagonalWeight n u k k) =
        -Real.log (n.factorial : ℝ) +
          ∑ i : I,
            (Real.log ((k i).factorial : ℝ) +
              (k i : ℝ) * Real.log ((u i).factorial : ℝ) +
              (k i : ℝ) * (((u i).choose 2 : ℝ) * Real.log 2 - Real.log 2)) := by
    unfold partialDiagonalWeight
    rw [hmark1, one_div, Real.log_inv]
    unfold partialSignedFirstMoment partialProfileFactorialProduct
      selectedBlockCount selectedInternalEdgeCount
    rw [hMass, Nat.sub_self, Nat.factorial_zero, Nat.cast_one, one_mul]
    have h2b_pos : (0 : ℝ) < (2 : ℝ) ^ (∑ i : I, k i) := by positivity
    have hnf_pos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hpf_pos : (0 : ℝ) < ((∏ i : I, (u i).factorial ^ k i * (k i).factorial : ℕ) : ℝ) := by
      exact_mod_cast Finset.prod_pos fun i _ ↦
        mul_pos (pow_pos (Nat.factorial_pos _) _) (Nat.factorial_pos _)
    have h2e_pos : (0 : ℝ) < (2 : ℝ) ^ (∑ i : I, (u i).choose 2 * k i) := by positivity
    rw [Real.log_div (mul_pos h2b_pos hnf_pos).ne' (mul_pos hpf_pos h2e_pos).ne',
      Real.log_mul h2b_pos.ne' hnf_pos.ne',
      Real.log_mul hpf_pos.ne' h2e_pos.ne',
      Real.log_pow, Real.log_pow, Nat.cast_prod,
      Real.log_prod (fun i _ ↦ by
        exact_mod_cast (mul_pos (pow_pos (Nat.factorial_pos _) _) (Nat.factorial_pos _)).ne')]
    have hlog_pf :
        ∑ i : I, Real.log ((((u i).factorial ^ k i * (k i).factorial : ℕ) : ℝ)) =
          ∑ i : I, ((k i : ℝ) * Real.log ((u i).factorial : ℝ) +
            Real.log ((k i).factorial : ℝ)) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have h1 : (((u i).factorial ^ k i : ℕ) : ℝ) ≠ 0 := by positivity
      have h2 : ((k i).factorial : ℝ) ≠ 0 := by positivity
      rw [Nat.cast_mul, Real.log_mul h1 h2, Nat.cast_pow, Real.log_pow]
    rw [hlog_pf, Nat.cast_sum, Finset.sum_mul, Nat.cast_sum, Finset.sum_mul]
    simp only [Nat.cast_mul]
    have hcombine :
        -(∑ i : I, (k i : ℝ) * Real.log 2 + Real.log (n.factorial : ℝ) -
            (∑ i : I, ((k i : ℝ) * Real.log ((u i).factorial : ℝ) +
                Real.log ((k i).factorial : ℝ)) +
              ∑ i : I, ((u i).choose 2 : ℝ) * (k i : ℝ) * Real.log 2)) =
          -Real.log (n.factorial : ℝ) +
            ((∑ i : I, ((k i : ℝ) * Real.log ((u i).factorial : ℝ) +
                Real.log ((k i).factorial : ℝ)) +
              ∑ i : I, ((u i).choose 2 : ℝ) * (k i : ℝ) * Real.log 2) -
              ∑ i : I, (k i : ℝ) * Real.log 2) := by ring
    rw [hcombine, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hn_ub := log_factorial_le_factorialEntropyMain_add_log_exp_mul_succ n
  rw [factorialEntropyMain_of_pos hn] at hn_ub
  have hcoord_ge : ∀ i : I,
      K * (p i * Real.log (p i) - p i + p i * E i) ≤
        Real.log ((k i).factorial : ℝ) +
          (k i : ℝ) * Real.log ((u i).factorial : ℝ) +
          (k i : ℝ) * (((u i).choose 2 : ℝ) * Real.log 2 - Real.log 2) -
          (u i : ℝ) * (k i : ℝ) * Real.log (n : ℝ) +
          (u i : ℝ) * (k i : ℝ) := by
    intro i
    have hki_lb := factorialEntropyMain_le_log_factorial_elem (k i)
    have hent_p := factorialEntropyMain_eq_mul_div (k i) hK_pos
    have hpK : K * p i = (k i : ℝ) := by
      dsimp [p]
      field_simp [hK_pos.ne']
    have halg :
        K * (p i * Real.log (p i) - p i + p i * E i) =
          factorialEntropyMain (k i) +
            (k i : ℝ) * Real.log ((u i).factorial : ℝ) +
            (k i : ℝ) * (((u i).choose 2 : ℝ) * Real.log 2 - Real.log 2) -
            (u i : ℝ) * (k i : ℝ) * Real.log (n : ℝ) +
            (u i : ℝ) * (k i : ℝ) := by
      rw [hent_p]
      change K * (p i * Real.log (p i) - p i + p i * E i) =
        K * (p i * Real.log K + p i * Real.log (p i) - p i) + _ + _ - _ + _
      dsimp [E]
      rw [← hpK]
      ring
    linarith
  have hsum_coord := Finset.sum_le_sum (s := Finset.univ) fun (i : I) _ ↦ hcoord_ge i
  rw [← Finset.mul_sum] at hsum_coord
  have hsum_mass_log :
      ∑ i : I, (u i : ℝ) * (k i : ℝ) * Real.log (n : ℝ) = (n : ℝ) * Real.log (n : ℝ) := by
    rw [← Finset.sum_mul, ← hMass]
    unfold selectedVertexMass
    congr 1
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by push_cast; rfl
  have hsum_mass : ∑ i : I, (u i : ℝ) * (k i : ℝ) = (n : ℝ) := by
    rw [← hMass]
    unfold selectedVertexMass
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by push_cast; rfl
  have hsplit_rhs :
      ∑ i : I,
          (Real.log ((k i).factorial : ℝ) +
            (k i : ℝ) * Real.log ((u i).factorial : ℝ) +
            (k i : ℝ) * (((u i).choose 2 : ℝ) * Real.log 2 - Real.log 2) -
            (u i : ℝ) * (k i : ℝ) * Real.log (n : ℝ) +
            (u i : ℝ) * (k i : ℝ)) =
        (∑ i : I,
          (Real.log ((k i).factorial : ℝ) +
            (k i : ℝ) * Real.log ((u i).factorial : ℝ) +
            (k i : ℝ) * (((u i).choose 2 : ℝ) * Real.log 2 - Real.log 2))) -
          (n : ℝ) * Real.log (n : ℝ) + (n : ℝ) := by
    rw [← hsum_mass_log, ← hsum_mass, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  rw [hsplit_rhs] at hsum_coord
  rw [hlog_Wk]
  linarith

/-! ## 4. Homogeneous-packing entropy bound & Proposition 4.1(ii)–(iii) `G(n, 1/2)` tails -/

/-- **Exact finite homogeneous-packing entropy bound (`Proposition 4.1(iii)` proof):**
for `1 ≤ u`, `1 ≤ m`, and `m * u < n`, writing `λ = m * u / n ∈ (0, 1)` and
`g(λ) = phiInfAux λ = ((1 - λ) / λ) log (1 - λ)`,
`P(H_u(G_n) ≥ m) ≤ (1 - λ)⁻¹ * (2 e² / λ * (e n / u * 2^(-u/2))^(u - 1))^m * exp(-λ n (1 + g(λ)))`. -/
theorem randomGraph_maxDisjointHomogeneousEq_ge_le_entropy
    {n u m : ℕ} (hu : 1 ≤ u) (hm : 1 ≤ m) (hmu : m * u < n) :
    let lam : ℝ := ((m * u : ℕ) : ℝ) / (n : ℝ)
    (randomGraphMeasure n).real {G | m ≤ maxDisjointHomogeneousEq G u} ≤
      (1 - lam)⁻¹ *
        (2 * Real.exp 1 ^ 2 / lam *
          (Real.exp 1 * (n : ℝ) / (u : ℝ) * (2 : ℝ) ^ (-(u : ℝ) / 2)) ^ (u - 1)) ^ m *
        Real.exp (-lam * (n : ℝ) * (1 + phiInfAux lam)) := by
  intro lam
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hu_pos : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmu_pos : 0 < m * u := Nat.mul_pos hm hu
  have hlam_pos : 0 < lam := by
    dsimp [lam]
    exact div_pos (by exact_mod_cast hmu_pos) hn_pos
  have hlam_lt_one : lam < 1 := by
    dsimp [lam]
    rw [div_lt_one hn_pos]
    exact_mod_cast hmu
  have h1mlam_pos : 0 < 1 - lam := sub_pos.mpr hlam_lt_one
  have hbase := randomGraph_maxDisjointHomogeneousEq_ge_le_factorial hmu.le
  have hfall := factorial_div_le_one_sub_rpow_mul_exp_neg hmu
  have hu_lb := pow_mul_exp_neg_le_factorial u
  have hm_lb := pow_mul_exp_neg_le_factorial m
  have hu_pow_lb :
      ((u : ℝ) ^ u * Real.exp (-(u : ℝ))) ^ m ≤ (u.factorial : ℝ) ^ m :=
    pow_le_pow_left₀ (by positivity) hu_lb m
  have hdenom_lb :
      ((u : ℝ) ^ u * Real.exp (-(u : ℝ))) ^ m *
          ((m : ℝ) ^ m * Real.exp (-(m : ℝ))) ≤
        (u.factorial : ℝ) ^ m * (m.factorial : ℝ) :=
    mul_le_mul hu_pow_lb hm_lb (by positivity) (by positivity)
  have hratio_le :
      (n.factorial : ℝ) /
          (((n - m * u).factorial : ℝ) * (u.factorial : ℝ) ^ m * (m.factorial : ℝ)) ≤
        (n : ℝ) ^ (m * u) *
          ((1 - lam) ^ (-((n - m * u + 1 : ℕ) : ℝ)) * Real.exp (-((m * u : ℕ) : ℝ))) /
          (((u : ℝ) ^ u * Real.exp (-(u : ℝ))) ^ m *
            ((m : ℝ) ^ m * Real.exp (-(m : ℝ)))) := by
    have hnf_pos : (0 : ℝ) < ((n - m * u).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    have hnpow_pos : (0 : ℝ) < (n : ℝ) ^ (m * u) := pow_pos hn_pos _
    have hfall' : (n.factorial : ℝ) / ((n - m * u).factorial : ℝ) ≤
        (n : ℝ) ^ (m * u) *
          ((1 - lam) ^ (-((n - m * u + 1 : ℕ) : ℝ)) * Real.exp (-((m * u : ℕ) : ℝ))) := by
      have hf := hfall
      change (n.factorial : ℝ) / (((n - m * u).factorial : ℝ) * (n : ℝ) ^ (m * u)) ≤
        (1 - lam) ^ (-((n - m * u + 1 : ℕ) : ℝ)) * Real.exp (-((m * u : ℕ) : ℝ)) at hf
      rw [div_mul_eq_div_div, div_le_iff₀ hnpow_pos] at hf
      linarith
    have hrew :
        (n.factorial : ℝ) /
            (((n - m * u).factorial : ℝ) * (u.factorial : ℝ) ^ m * (m.factorial : ℝ)) =
          ((n.factorial : ℝ) / ((n - m * u).factorial : ℝ)) /
            ((u.factorial : ℝ) ^ m * (m.factorial : ℝ)) := by ring
    rw [hrew]
    exact div_le_div₀ (by positivity) hfall' (by positivity) hdenom_lb
  -- Simplify the exponential/power factors into the exact manuscript display
  have hrpow_split :
      (1 - lam) ^ (-((n - m * u + 1 : ℕ) : ℝ)) * Real.exp (-((m * u : ℕ) : ℝ)) =
        (1 - lam)⁻¹ * Real.exp (-lam * (n : ℝ) * (1 + phiInfAux lam)) := by
    have hcast_exp : -((n - m * u + 1 : ℕ) : ℝ) = -1 + -(n : ℝ) * (1 - lam) := by
      have hsub : ((n - m * u + 1 : ℕ) : ℝ) = ((n - m * u : ℕ) : ℝ) + 1 := by push_cast; rfl
      rw [hsub, Nat.cast_sub hmu.le]
      dsimp [lam]
      field_simp [hn_pos.ne']
      ring
    have hmucast : -((m * u : ℕ) : ℝ) = -lam * (n : ℝ) := by
      dsimp [lam]
      field_simp [hn_pos.ne']
    rw [hcast_exp, Real.rpow_add h1mlam_pos, Real.rpow_neg_one,
      Real.rpow_def_of_pos h1mlam_pos, hmucast, mul_assoc, ← Real.exp_add]
    congr 2
    unfold phiInfAux
    field_simp [hlam_pos.ne']
    ring
  have h2choose :
      (((2 : ℝ) ^ (u.choose 2))⁻¹) = ((2 : ℝ) ^ (-(u : ℝ) / 2)) ^ (u - 1) := by
    have hch : (u.choose 2 : ℝ) = (u : ℝ) * ((u - 1 : ℕ) : ℝ) / 2 := by
      rw [Nat.cast_choose_two, Nat.cast_sub hu]
      push_cast
      rfl
    rw [← Real.rpow_natCast (2 : ℝ) (u.choose 2),
      ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), hch,
      ← Real.rpow_natCast _ (u - 1), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hfactor_m :
      (n : ℝ) ^ (m * u) /
          (((u : ℝ) ^ u * Real.exp (-(u : ℝ))) ^ m *
            ((m : ℝ) ^ m * Real.exp (-(m : ℝ)))) *
          (2 : ℝ) ^ m * (((2 : ℝ) ^ (u.choose 2))⁻¹) ^ m =
        (2 * Real.exp 1 ^ 2 / lam *
          (Real.exp 1 * (n : ℝ) / (u : ℝ) * (2 : ℝ) ^ (-(u : ℝ) / 2)) ^ (u - 1)) ^ m := by
    have hrm : (m : ℝ) ^ m * Real.exp (-(m : ℝ)) = ((m : ℝ) * Real.exp (-1)) ^ m := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      ring
    have hm_eq : (m : ℝ) = lam * (n : ℝ) / (u : ℝ) := by
      dsimp [lam]
      push_cast
      field_simp [hn_pos.ne', hu_pos.ne']
    have hu_split : ∀ x : ℝ, x ^ u = x * x ^ (u - 1) := by
      intro x
      conv_lhs => rw [← Nat.sub_add_cancel hu, pow_succ, mul_comm]
    have hexp_u : Real.exp (-(u : ℝ)) * Real.exp (-1) =
        (Real.exp 1 ^ 2)⁻¹ * (Real.exp 1 ^ (u - 1))⁻¹ := by
      have hu1 : ((u - 1 : ℕ) : ℝ) = (u : ℝ) - 1 := by
        rw [Nat.cast_sub hu]
        push_cast
        rfl
      rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_nat_mul, hu1,
        ← Real.exp_neg, ← Real.exp_neg, ← Real.exp_add]
      congr 1
      ring
    rw [hrm, h2choose, pow_mul' (n : ℝ) m u, ← mul_pow, ← div_pow, ← mul_pow, ← mul_pow]
    congr 1
    rw [hu_split (n : ℝ), hu_split (u : ℝ), hm_eq]
    have hexp_step :
        ((u : ℝ) * (u : ℝ) ^ (u - 1) * Real.exp (-(u : ℝ))) *
            (lam * (n : ℝ) / (u : ℝ) * Real.exp (-1)) =
          lam * (n : ℝ) * (u : ℝ) ^ (u - 1) *
            ((Real.exp 1 ^ 2)⁻¹ * (Real.exp 1 ^ (u - 1))⁻¹) := by
      calc ((u : ℝ) * (u : ℝ) ^ (u - 1) * Real.exp (-(u : ℝ))) *
              (lam * (n : ℝ) / (u : ℝ) * Real.exp (-1))
          = ((u : ℝ) * (lam * (n : ℝ) / (u : ℝ))) * (u : ℝ) ^ (u - 1) *
              (Real.exp (-(u : ℝ)) * Real.exp (-1)) := by ring
        _ = lam * (n : ℝ) * (u : ℝ) ^ (u - 1) *
              ((Real.exp 1 ^ 2)⁻¹ * (Real.exp 1 ^ (u - 1))⁻¹) := by
            rw [hexp_u]
            congr 2
            field_simp [hu_pos.ne']
    rw [hexp_step, mul_pow, div_pow, mul_pow]
    have he1_ne : Real.exp 1 ^ 2 ≠ 0 := by positivity
    have heu_ne : Real.exp 1 ^ (u - 1) ≠ 0 := by positivity
    have hu1_ne : (u : ℝ) ^ (u - 1) ≠ 0 := pow_ne_zero _ hu_pos.ne'
    field_simp [hlam_pos.ne', hn_pos.ne', he1_ne, heu_ne, hu1_ne]
  refine le_trans hbase ?_
  calc (n.factorial : ℝ) /
          (((n - m * u).factorial : ℝ) * (u.factorial : ℝ) ^ m * (m.factorial : ℝ)) *
          (2 : ℝ) ^ m * (((2 : ℝ) ^ (u.choose 2))⁻¹) ^ m
      ≤ ((n : ℝ) ^ (m * u) *
            ((1 - lam) ^ (-((n - m * u + 1 : ℕ) : ℝ)) * Real.exp (-((m * u : ℕ) : ℝ))) /
            (((u : ℝ) ^ u * Real.exp (-(u : ℝ))) ^ m *
              ((m : ℝ) ^ m * Real.exp (-(m : ℝ))))) *
          (2 : ℝ) ^ m * (((2 : ℝ) ^ (u.choose 2))⁻¹) ^ m := by
        gcongr
    _ = ((1 - lam) ^ (-((n - m * u + 1 : ℕ) : ℝ)) * Real.exp (-((m * u : ℕ) : ℝ))) *
          ((n : ℝ) ^ (m * u) /
            (((u : ℝ) ^ u * Real.exp (-(u : ℝ))) ^ m *
              ((m : ℝ) ^ m * Real.exp (-(m : ℝ)))) *
            (2 : ℝ) ^ m * (((2 : ℝ) ^ (u.choose 2))⁻¹) ^ m) := by
        ring
    _ = (1 - lam)⁻¹ *
          (2 * Real.exp 1 ^ 2 / lam *
            (Real.exp 1 * (n : ℝ) / (u : ℝ) * (2 : ℝ) ^ (-(u : ℝ) / 2)) ^ (u - 1)) ^ m *
          Real.exp (-lam * (n : ℝ) * (1 + phiInfAux lam)) := by
        rw [hrpow_split, hfactor_m]
        ring

/-- **Proposition 4.1(ii) unconditional `G(n, 1/2)` homogeneous-packing tail (`main.tex`):**
eventually along all integers `n`,
`P(H_α(G_n) ≥ ⌈8 n ℓ / L²⌉) ≤ exp(-200 n ℓ² / L²)`. -/
theorem eventually_randomGraph_homogeneousPacking_alpha_tail :
    ∀ᶠ n : ℕ in atTop,
      (randomGraphMeasure n).real
        {G | Nat.ceil (8 * (n : ℝ) * logLogOrder n / logOrder n ^ 2) ≤
          maxDisjointHomogeneousEq G (phaseNat n)} ≤
        Real.exp (-200 * (n : ℝ) * logLogOrder n ^ 2 / logOrder n ^ 2) := by
  obtain ⟨MK, hMK⟩ := exists_phaseK_abs_bound
  have h2q_lt3 : 2 / q < (29 / 10 : ℝ) := by
    have hq_lo : (56 / 81 : ℝ) < q := by
      unfold q
      linarith [Real.log_two_gt_d9]
    rw [div_lt_iff₀ q_pos]
    linarith
  have h2q_gt : (285 / 100 : ℝ) < 2 / q := by
    have hq_hi : q < (7 / 10 : ℝ) := by
      unfold q
      linarith [Real.log_two_lt_d9]
    rw [lt_div_iff₀ q_pos]
    linarith
  have hres_le : ∀ᶠ n : ℕ in atTop, phaseExpansionResidual n ≤ 1 :=
    phaseExpansionResidual_tendsto_zero.eventually (Iic_mem_nhds zero_lt_one)
  have hratio_alpha :
      Tendsto (fun n : ℕ ↦ (phaseNat n : ℝ) / logOrder n) atTop (nhds (2 / q)) := by
    have hScaleTop : Tendsto (fun n : ℕ ↦ (2 / q) * logOrder n) atTop atTop :=
      tendsto_logOrder_atTop.const_mul_atTop (div_pos (by norm_num) q_pos)
    have hDenom : ∀ᶠ n : ℕ in atTop, (2 / q) * logOrder n ≠ 0 :=
      hScaleTop.eventually_ne_atTop 0
    have hEq := (isEquivalent_iff_tendsto_one hDenom).mp phaseNat_isEquivalent_scaled_logOrder
    have hmul := hEq.const_mul (2 / q)
    rw [mul_one] at hmul
    refine hmul.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    have hL : logOrder n ≠ 0 := (Real.log_pos (by exact_mod_cast hn)).ne'
    simp only [Pi.div_apply]
    field_simp [hL, q_ne_zero]
  have halpha_lo : ∀ᶠ n : ℕ in atTop, (285 / 100 : ℝ) * logOrder n ≤ (phaseNat n : ℝ) := by
    filter_upwards [hratio_alpha.eventually (Ici_mem_nhds h2q_gt),
      eventually_gt_atTop (1 : ℕ)] with n hrat hn
    have hL : 0 < logOrder n := Real.log_pos (by exact_mod_cast hn)
    exact (le_div_iff₀ hL).mp hrat
  have halpha_hi : ∀ᶠ n : ℕ in atTop, (phaseNat n : ℝ) ≤ 3 * logOrder n := by
    have h2q_lt3' : 2 / q < (3 : ℝ) := lt_trans h2q_lt3 (by norm_num)
    filter_upwards [hratio_alpha.eventually (Iic_mem_nhds h2q_lt3'),
      eventually_gt_atTop (1 : ℕ)] with n hrat hn
    have hL : 0 < logOrder n := Real.log_pos (by exact_mod_cast hn)
    exact (div_le_iff₀ hL).mp hrat
  have hll_ge : ∀ᶠ n : ℕ in atTop,
      max (10 : ℝ) ((MK + 3) * 10) ≤ logLogOrder n :=
    tendsto_logLogOrder_atTop.eventually (eventually_ge_atTop _)
  have hll_le_L : ∀ᶠ n : ℕ in atTop, logLogOrder n ≤ logOrder n / 100 := by
    have hb := logLogOrder_isLittleO_logOrder.bound (by norm_num : (0 : ℝ) < 1 / 100)
    filter_upwards [hb, eventually_gt_atTop (1 : ℕ)] with n hbn hn
    have hL : 0 < logOrder n := Real.log_pos (by exact_mod_cast hn)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hL] at hbn
    linarith [le_abs_self (logLogOrder n)]
  have hLcube_le_n : ∀ᶠ n : ℕ in atTop, logOrder n ^ 3 ≤ (n : ℝ) := by
    have ho : (fun n : ℕ ↦ logOrder n ^ 3) =o[atTop] (fun n : ℕ ↦ (n : ℝ)) := by
      simpa only [logOrder, Function.comp_def, id_eq] using
        (Real.isLittleO_pow_log_id_atTop (n := 3)).comp_tendsto
          (tendsto_natCast_atTop_atTop (R := ℝ))
    filter_upwards [ho.bound (by norm_num : (0 : ℝ) < 1), eventually_gt_atTop (1 : ℕ)] with n hb hn
    have hL : 0 < logOrder n := Real.log_pos (by exact_mod_cast hn)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos hL 3),
      abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ)), one_mul] at hb
    exact hb
  filter_upwards [eventually_gt_atTop (2 : ℕ), eventually_two_le_phaseNat,
    hres_le, halpha_lo, halpha_hi, hll_ge, hll_le_L, hLcube_le_n] with
    n hn2 hu2 hres hulo huhi hll hllL hL3n
  let L : ℝ := logOrder n
  let ell : ℝ := logLogOrder n
  let u : ℕ := phaseNat n
  let x : ℝ := 8 * (n : ℝ) * ell / L ^ 2
  let m : ℕ := Nat.ceil x
  have hn1 : 1 ≤ n := by omega
  have hu1 : 1 ≤ u := by omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hell_ge10 : 10 ≤ ell := le_trans (le_max_left _ _) hll
  have hell_ge_MK : (MK + 3) * 10 ≤ ell := le_trans (le_max_right _ _) hll
  have hL_ge1000 : 1000 ≤ L := by change 1000 ≤ logOrder n; linarith
  have hL_pos : 0 < L := by linarith
  have hx_ge80 : 80 ≤ x := by
    dsimp [x]
    rw [le_div_iff₀ (sq_pos_of_pos hL_pos)]
    have hL2_le_L3 : L ^ 2 ≤ L ^ 3 := by
      calc L ^ 2 = 1 * L ^ 2 := (one_mul _).symm
        _ ≤ L * L ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg L)
        _ = L ^ 3 := by ring
    have h1 : 80 * L ^ 2 ≤ 8 * (L ^ 2) * ell := by
      calc 80 * L ^ 2 = L ^ 2 * 80 := by ring
        _ ≤ L ^ 2 * (8 * ell) := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg L)
        _ = 8 * (L ^ 2) * ell := by ring
    have h2 : 8 * (L ^ 2) * ell ≤ 8 * (L ^ 3) * ell :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL2_le_L3 (by norm_num)) (by linarith)
    have h3 : 8 * (L ^ 3) * ell ≤ 8 * (n : ℝ) * ell :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL3n (by norm_num)) (by linarith)
    linarith
  have hm_ge_x : x ≤ (m : ℝ) := Nat.le_ceil x
  have hm_le_x1 : (m : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hmu_le_n : m * u ≤ n := by
    suffices ((m * u : ℕ) : ℝ) ≤ (n : ℝ) from Nat.cast_le.mp this
    push_cast
    have hx_le : (m : ℝ) ≤ 9 * (n : ℝ) * ell / L ^ 2 := by
      have h1 : 1 ≤ (n : ℝ) * ell / L ^ 2 := by
        have hx80 := hx_ge80
        dsimp [x] at hx80
        have : 8 * ((n : ℝ) * ell / L ^ 2) = 8 * (n : ℝ) * ell / L ^ 2 := by ring
        linarith
      have h9 : x + 1 ≤ 9 * (n : ℝ) * ell / L ^ 2 := by
        dsimp [x]
        have : 9 * (n : ℝ) * ell / L ^ 2 = 8 * (n : ℝ) * ell / L ^ 2 + (n : ℝ) * ell / L ^ 2 := by
          ring
        linarith
      exact le_trans hm_le_x1 h9
    have huhi' : (u : ℝ) ≤ 3 * L := huhi
    calc (m : ℝ) * (u : ℝ)
        ≤ (9 * (n : ℝ) * ell / L ^ 2) * (3 * L) :=
          mul_le_mul hx_le huhi' (by positivity) (by positivity)
      _ = 27 * (n : ℝ) * (ell / L) := by field_simp [hL_pos.ne']; ring
      _ ≤ 27 * (n : ℝ) * (1 / 100) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_iff₀ hL_pos]
          change logLogOrder n ≤ 1 / 100 * logOrder n
          linarith
      _ ≤ (n : ℝ) := by linarith
  -- Bound `log (2 * e * mu n u)`
  have hu_le_n : u ≤ n := by
    have hm_pos_nat : 1 ≤ m := by
      have : (1 : ℝ) ≤ (m : ℝ) := by linarith
      exact_mod_cast this
    calc u = 1 * u := (one_mul u).symm
      _ ≤ m * u := Nat.mul_le_mul_right u hm_pos_nat
      _ ≤ n := hmu_le_n
  have hmu_pos : 0 < mu n u := mu_pos hu_le_n
  have hlog_2emu : Real.log (2 * Real.exp 1 * mu n u) ≤ L + (3 / 2 : ℝ) * ell := by
    have hK_le : phaseK (phaseDelta n) ≤ MK :=
      le_of_abs_le (hMK _ ⟨phaseDelta_nonneg n, (phaseDelta_lt_one n).le⟩)
    have hlog_mu : Real.log (mu n u) ≤
        L + (2 / q - 3 / 2) * ell + MK + 1 := by
      have hexp : Real.log (mu n u) = phaseExpansionMain n + phaseExpansionResidual n := by
        unfold phaseExpansionResidual
        ring
      have hd_le1 : phaseDelta n ≤ 1 := (phaseDelta_lt_one n).le
      have hL_sub_nn : 0 ≤ L - ell := by
        change 0 ≤ logOrder n - logLogOrder n
        linarith
      have hd_prod : phaseDelta n * (L - ell) ≤ 1 * (L - ell) :=
        mul_le_mul_of_nonneg_right hd_le1 hL_sub_nn
      rw [hexp]
      unfold phaseExpansionMain
      change phaseDelta n * (L - ell) + (2 / q - 1 / 2) * ell + phaseK (phaseDelta n) +
        phaseExpansionResidual n ≤ _
      linarith
    have hlog2_le1 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have h2q_ell : (2 / q - 3 / 2) * ell ≤ (29 / 10 - 3 / 2 : ℝ) * ell :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    rw [Real.log_mul (by positivity) hmu_pos.ne',
      Real.log_mul two_ne_zero (Real.exp_pos 1).ne', Real.log_exp]
    linarith
  -- Apply Lemma 1.2 (`randomGraph_maxDisjointHomogeneousEq_ge_le`) + `m^m e^{-m} ≤ m!`
  have hpack := randomGraph_maxDisjointHomogeneousEq_ge_le hn1 hu1 hmu_le_n
  have hm_fac := pow_mul_exp_neg_le_factorial m
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  have hquot_le :
      (2 * mu n u) ^ m / (m.factorial : ℝ) ≤
        (2 * Real.exp 1 * mu n u / (m : ℝ)) ^ m := by
    have hden_pos : 0 < (m : ℝ) ^ m * Real.exp (-(m : ℝ)) := by positivity
    calc (2 * mu n u) ^ m / (m.factorial : ℝ)
        ≤ (2 * mu n u) ^ m / ((m : ℝ) ^ m * Real.exp (-(m : ℝ))) :=
          div_le_div_of_nonneg_left (by positivity) hden_pos hm_fac
      _ = (2 * Real.exp 1 * mu n u / (m : ℝ)) ^ m := by
          have hexp_inv : (Real.exp (-(m : ℝ)))⁻¹ = (Real.exp 1) ^ m := by
            rw [← Real.exp_neg, neg_neg, ← Real.exp_nat_mul, mul_one]
          rw [div_mul_eq_div_div, div_eq_mul_inv (_ / _), hexp_inv,
            div_mul_eq_mul_div, ← mul_pow, ← div_pow]
          congr 2
          ring
  have hbase_log :
      Real.log (2 * Real.exp 1 * mu n u / (m : ℝ)) ≤ (7 / 2 : ℝ) * ell := by
    rw [Real.log_div (by positivity) hm_pos.ne']
    have hlog8_pos : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    have hlog_ell_pos : 0 ≤ Real.log ell := Real.log_nonneg (by linarith)
    have hlog_x_ge : L - 2 * ell ≤ Real.log (m : ℝ) := by
      have hx_pos : 0 < x := by linarith
      have hle_m : Real.log x ≤ Real.log (m : ℝ) := Real.log_le_log hx_pos hm_ge_x
      have hlog_x : Real.log x = Real.log 8 + L + Real.log ell - 2 * ell := by
        dsimp [x, L, ell, logOrder, logLogOrder]
        rw [Real.log_div (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by norm_num) hn_pos.ne', Real.log_pow]
        ring
      linarith
    linarith
  have hpow_exp :
      (2 * Real.exp 1 * mu n u / (m : ℝ)) ^ m ≤
        Real.exp ((7 / 2 : ℝ) * (m : ℝ) * ell) := by
    have hb_pos : 0 < 2 * Real.exp 1 * mu n u / (m : ℝ) := by positivity
    calc (2 * Real.exp 1 * mu n u / (m : ℝ)) ^ m
        = Real.exp ((m : ℝ) * Real.log (2 * Real.exp 1 * mu n u / (m : ℝ))) := by
          rw [Real.exp_nat_mul, Real.exp_log hb_pos]
      _ ≤ Real.exp ((7 / 2 : ℝ) * (m : ℝ) * ell) := by
          apply Real.exp_le_exp.mpr
          calc (m : ℝ) * Real.log (2 * Real.exp 1 * mu n u / (m : ℝ))
              ≤ (m : ℝ) * ((7 / 2 : ℝ) * ell) :=
                mul_le_mul_of_nonneg_left hbase_log (Nat.cast_nonneg m)
            _ = (7 / 2 : ℝ) * (m : ℝ) * ell := by ring
  have hquad_exp :
      -(u : ℝ) ^ 2 / (n : ℝ) * (m.choose 2 : ℝ) ≤ -30 * (m : ℝ) * ell := by
    have hu2_gt : 8 * L ^ 2 ≤ (u : ℝ) ^ 2 := by
      have hulo' : (285 / 100 : ℝ) * L ≤ (u : ℝ) := hulo
      have hsq : ((285 / 100 : ℝ) * L) ^ 2 ≤ (u : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hulo' 2
      have h8 : 8 * L ^ 2 ≤ ((285 / 100 : ℝ) * L) ^ 2 := by
        have : ((285 / 100 : ℝ) * L) ^ 2 - 8 * L ^ 2 = (49 / 400 : ℝ) * L ^ 2 := by ring
        have hnn : 0 ≤ (49 / 400 : ℝ) * L ^ 2 := by positivity
        linarith
      exact le_trans h8 hsq
    have hm1_ge : (79 / 80 : ℝ) * x ≤ (m : ℝ) - 1 := by linarith
    have hch : (m.choose 2 : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := Nat.cast_choose_two ℝ m
    rw [hch]
    have hprod_ge : 30 * ell ≤ (u : ℝ) ^ 2 / (n : ℝ) * (((m : ℝ) - 1) / 2) := by
      calc 30 * ell
          ≤ (8 * L ^ 2 / (n : ℝ)) * (((79 / 80 : ℝ) * (8 * (n : ℝ) * ell / L ^ 2)) / 2) := by
            field_simp [hn_pos.ne', hL_pos.ne']
            linarith
        _ ≤ ((u : ℝ) ^ 2 / (n : ℝ)) * (((m : ℝ) - 1) / 2) := by
            gcongr
    have hmprod : 30 * (m : ℝ) * ell ≤
        (m : ℝ) * ((u : ℝ) ^ 2 / (n : ℝ) * (((m : ℝ) - 1) / 2)) := by
      calc 30 * (m : ℝ) * ell = (m : ℝ) * (30 * ell) := by ring
        _ ≤ (m : ℝ) * ((u : ℝ) ^ 2 / (n : ℝ) * (((m : ℝ) - 1) / 2)) :=
          mul_le_mul_of_nonneg_left hprod_ge (Nat.cast_nonneg m)
    have hrew_q : -(u : ℝ) ^ 2 / (n : ℝ) * ((m : ℝ) * ((m : ℝ) - 1) / 2) =
        -((m : ℝ) * ((u : ℝ) ^ 2 / (n : ℝ) * (((m : ℝ) - 1) / 2))) := by ring
    linarith
  refine le_trans hpack ?_
  calc (2 * mu n u) ^ m / (m.factorial : ℝ) *
          Real.exp (-(u : ℝ) ^ 2 / (n : ℝ) * (m.choose 2 : ℝ))
      ≤ Real.exp ((7 / 2 : ℝ) * (m : ℝ) * ell) * Real.exp (-30 * (m : ℝ) * ell) := by
        exact mul_le_mul (le_trans hquot_le hpow_exp) (Real.exp_le_exp.mpr hquad_exp)
          (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (-(53 / 2 : ℝ) * ((m : ℝ) * ell)) := by
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (-200 * (n : ℝ) * ell ^ 2 / L ^ 2) := by
        apply Real.exp_le_exp.mpr
        have hm_ell : 8 * ((n : ℝ) * ell ^ 2 / L ^ 2) ≤ (m : ℝ) * ell := by
          calc 8 * ((n : ℝ) * ell ^ 2 / L ^ 2)
              = x * ell := by dsimp [x]; ring
            _ ≤ (m : ℝ) * ell := mul_le_mul_of_nonneg_right hm_ge_x (by linarith)
        have hnn : 0 ≤ (n : ℝ) * ell ^ 2 / L ^ 2 := by positivity
        calc -(53 / 2 : ℝ) * ((m : ℝ) * ell)
            ≤ -(53 / 2 : ℝ) * (8 * ((n : ℝ) * ell ^ 2 / L ^ 2)) :=
              mul_le_mul_of_nonpos_left hm_ell (by norm_num)
          _ = -212 * ((n : ℝ) * ell ^ 2 / L ^ 2) := by ring
          _ ≤ -200 * ((n : ℝ) * ell ^ 2 / L ^ 2) :=
              mul_le_mul_of_nonneg_right (by norm_num) hnn
          _ = -200 * (n : ℝ) * ell ^ 2 / L ^ 2 := by ring

/-- **Proposition 4.1(iii) unconditional phase-uniform `G(n, 1/2)` packing tail (`main.tex`):**
for fixed `θ̄ ∈ (0, 1 / 20]` and `γ > 0`, eventually uniformly over all `n` satisfying
`δ_n ∈ [0, δ_*]` and `g(θ̄) + (log 2 / 2)(T_{δ_n} - 1) ≥ 2 γ`,
`P(H_{α - 1}(G_n) ≥ ⌈θ̄ n / (α - 1)⌉) ≤ exp(-θ̄ γ n)`. -/
theorem eventually_randomGraph_homogeneousPacking_alpha_sub_one_tail
    {thetaBar gamma : ℝ}
    (htheta : thetaBar ∈ Set.Ioc (0 : ℝ) (1 / 20))
    (hgamma : 0 < gamma) :
    ∀ᶠ n : ℕ in atTop,
      phaseDelta n ∈ Set.Icc 0 deltaStar →
      2 * gamma ≤ phiInfAux thetaBar + Real.log 2 / 2 * (phaseTarget (phaseDelta n) - 1) →
      (randomGraphMeasure n).real
        {G | Nat.ceil (thetaBar * (n : ℝ) / ((phaseNat n - 1 : ℕ) : ℝ)) ≤
          maxDisjointHomogeneousEq G (phaseNat n - 1)} ≤
        Real.exp (-thetaBar * gamma * (n : ℝ)) := by
  obtain ⟨htheta_pos, htheta_hi⟩ := htheta
  have hratio_alpha :
      Tendsto (fun n : ℕ ↦ (phaseNat n : ℝ) / logOrder n) atTop (nhds (2 / q)) := by
    have hScaleTop : Tendsto (fun n : ℕ ↦ (2 / q) * logOrder n) atTop atTop :=
      tendsto_logOrder_atTop.const_mul_atTop (div_pos (by norm_num) q_pos)
    have hDenom : ∀ᶠ n : ℕ in atTop, (2 / q) * logOrder n ≠ 0 :=
      hScaleTop.eventually_ne_atTop 0
    have hEq := (isEquivalent_iff_tendsto_one hDenom).mp phaseNat_isEquivalent_scaled_logOrder
    have hmul := hEq.const_mul (2 / q)
    rw [mul_one] at hmul
    refine hmul.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    have hL : logOrder n ≠ 0 := (Real.log_pos (by exact_mod_cast hn)).ne'
    simp only [Pi.div_apply]
    field_simp [hL, q_ne_zero]
  have halpha_lo : ∀ᶠ n : ℕ in atTop, 2 * logOrder n ≤ (phaseNat n : ℝ) := by
    have h2_lt : (2 : ℝ) < 2 / q := by
      have hq_hi : q < 1 := by unfold q; linarith [Real.log_two_lt_d9]
      rw [lt_div_iff₀ q_pos]; linarith
    filter_upwards [hratio_alpha.eventually (Ici_mem_nhds h2_lt),
      eventually_gt_atTop (1 : ℕ)] with n hrat hn
    exact (le_div_iff₀ (Real.log_pos (by exact_mod_cast hn))).mp hrat
  have halpha_hi : ∀ᶠ n : ℕ in atTop, (phaseNat n : ℝ) ≤ 4 * logOrder n := by
    have h4_gt : 2 / q < (4 : ℝ) := by
      have hq_lo : (1 / 2 : ℝ) < q := by unfold q; linarith [Real.log_two_gt_d9]
      rw [div_lt_iff₀ q_pos]; linarith
    filter_upwards [hratio_alpha.eventually (Iic_mem_nhds h4_gt),
      eventually_gt_atTop (1 : ℕ)] with n hrat hn
    exact (div_le_iff₀ (Real.log_pos (by exact_mod_cast hn))).mp hrat
  -- Rate `logLogOrder n / logOrder n → 0` and `1 / logOrder n → 0` and `logOrder n / n → 0`
  let Cconst : ℝ := |Real.log (2 * Real.exp 1 ^ 2 / thetaBar)| +
    (2 / q) + (2 * |phaseC| / q) + 4
  have herr_small : ∀ᶠ n : ℕ in atTop,
      (Real.log 2) / (n : ℝ) +
        (1 / 10 : ℝ) * (Cconst * logLogOrder n / logOrder n) ≤
        thetaBar * gamma := by
    have h1 : Tendsto (fun n : ℕ ↦ (Real.log 2) / (n : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
    have h2 : Tendsto (fun n : ℕ ↦
        (1 / 10 : ℝ) * (Cconst * logLogOrder n / logOrder n)) atTop (nhds 0) := by
      have hll := logLogOrder_isLittleO_logOrder.tendsto_div_nhds_zero
      have hm := hll.const_mul ((1 / 10 : ℝ) * Cconst)
      rw [mul_zero] at hm
      exact hm.congr fun n ↦ by ring
    have hsum := h1.add h2
    rw [add_zero] at hsum
    exact hsum.eventually (Iic_mem_nhds (mul_pos htheta_pos hgamma))
  have hun_small : ∀ᶠ n : ℕ in atTop, 4 * logOrder n / (n : ℝ) ≤ 1 / 20 := by
    have ho := logOrder_isLittleO_natCast.tendsto_div_nhds_zero.const_mul 4
    rw [mul_zero] at ho
    refine (ho.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 20))).mono ?_
    intro n hn
    change 4 * (logOrder n / (n : ℝ)) ≤ 1 / 20 at hn
    rwa [mul_div_assoc]
  have hll_ge2 : ∀ᶠ n : ℕ in atTop, 2 ≤ logLogOrder n :=
    tendsto_logLogOrder_atTop.eventually (eventually_ge_atTop (2 : ℝ))
  have htn_gt : ∀ᶠ n : ℕ in atTop, 4 * logOrder n < thetaBar * (n : ℝ) := by
    have ho := logOrder_isLittleO_natCast.tendsto_div_nhds_zero.const_mul 4
    rw [mul_zero] at ho
    filter_upwards [ho.eventually (Iio_mem_nhds htheta_pos),
      eventually_gt_atTop (1 : ℕ)] with n hlt hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    change 4 * (logOrder n / (n : ℝ)) < thetaBar at hlt
    rw [← mul_div_assoc] at hlt
    exact (div_lt_iff₀ hn_pos).mp hlt
  filter_upwards [eventually_phaseRangeDomain, halpha_lo, halpha_hi,
    herr_small, hun_small, hll_ge2, htn_gt] with
    n hdom hulo huhi herr hun hll2 htn hdelta hphi_ge
  have hn1 : 1 < n := hdom.1
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hL_pos : 0 < logOrder n := Real.log_pos (by exact_mod_cast hn1)
  have hell_ge2 : 2 ≤ logLogOrder n := hll2
  have hL_ge4 : 4 ≤ logOrder n := by
    have := Real.exp_le_exp.mpr hell_ge2
    rw [logLogOrder, Real.exp_log hL_pos] at this
    have he2 : (4 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (1 : ℝ)
      have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) he1 2
        _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
    linarith
  let u : ℕ := phaseNat n - 1
  have hu_ge7 : 7 ≤ u := by
    have : (8 : ℝ) ≤ (phaseNat n : ℝ) := by linarith
    have h8 : 8 ≤ phaseNat n := by exact_mod_cast this
    dsimp [u]; omega
  have hu1 : 1 ≤ u := by omega
  have hu2 : 2 ≤ u := by omega
  have hu_pos : (0 : ℝ) < (u : ℝ) := by exact_mod_cast (show 0 < u by omega)
  have hu_ge_L : logOrder n ≤ (u : ℝ) := by
    have hu_cast : (u : ℝ) = (phaseNat n : ℝ) - 1 := by
      dsimp [u]; rw [Nat.cast_sub (by omega : 1 ≤ phaseNat n), Nat.cast_one]
    linarith
  have hu_le_4L : (u : ℝ) ≤ 4 * logOrder n := by
    have hu_cast : (u : ℝ) = (phaseNat n : ℝ) - 1 := by
      dsimp [u]; rw [Nat.cast_sub (by omega : 1 ≤ phaseNat n), Nat.cast_one]
    linarith
  set m : ℕ := Nat.ceil (thetaBar * (n : ℝ) / (u : ℝ))
  have hm_ge_rat : thetaBar * (n : ℝ) / (u : ℝ) ≤ (m : ℝ) := Nat.le_ceil _
  have hm_le_rat1 : (m : ℝ) ≤ thetaBar * (n : ℝ) / (u : ℝ) + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hm1 : 1 ≤ m := by
    have hgt1 : 1 < thetaBar * (n : ℝ) / (u : ℝ) := by
      rw [one_lt_div hu_pos]
      linarith
    have : (1 : ℝ) ≤ (m : ℝ) := by linarith
    exact_mod_cast this
  set lam : ℝ := ((m * u : ℕ) : ℝ) / (n : ℝ)
  have hlam_ge : thetaBar ≤ lam := by
    dsimp [lam]
    rw [Nat.cast_mul, le_div_iff₀ hn_pos]
    have := (div_le_iff₀ hu_pos).mp hm_ge_rat
    linarith
  have hlam_le : lam ≤ 1 / 10 := by
    dsimp [lam]
    rw [Nat.cast_mul]
    calc (m : ℝ) * (u : ℝ) / (n : ℝ)
        ≤ (thetaBar * (n : ℝ) / (u : ℝ) + 1) * (u : ℝ) / (n : ℝ) := by gcongr
      _ = thetaBar + (u : ℝ) / (n : ℝ) := by
          field_simp [hu_pos.ne', hn_pos.ne']
      _ ≤ 1 / 20 + 4 * logOrder n / (n : ℝ) := by
          have : (u : ℝ) / (n : ℝ) ≤ 4 * logOrder n / (n : ℝ) := by gcongr
          linarith
      _ ≤ 1 / 10 := by linarith
  have hmu_lt_n : m * u < n := by
    have hlt1 : lam < 1 := by linarith
    dsimp [lam] at hlt1
    exact_mod_cast (div_lt_one hn_pos).mp hlt1
  have hent := randomGraph_maxDisjointHomogeneousEq_ge_le_entropy hu1 hm1 hmu_lt_n
  change (randomGraphMeasure n).real {G | m ≤ maxDisjointHomogeneousEq G u} ≤
    (1 - lam)⁻¹ *
      (2 * Real.exp 1 ^ 2 / lam *
        (Real.exp 1 * (n : ℝ) / (u : ℝ) * (2 : ℝ) ^ (-(u : ℝ) / 2)) ^ (u - 1)) ^ m *
      Real.exp (-lam * (n : ℝ) * (1 + phiInfAux lam)) at hent
  -- Rewrite `e * n / u * 2 ^ (-u / 2)` via `two_rpow_neg_half_alphaZero_sub_one`
  have hcenter : Real.exp 1 * (n : ℝ) / (u : ℝ) * (2 : ℝ) ^ (-(u : ℝ) / 2) =
      (2 * logBaseTwo (n : ℝ) / (u : ℝ)) * (2 : ℝ) ^ (phaseDelta n / 2) := by
    have hu_eq : -(u : ℝ) / 2 = -(alphaZero n - 1) / 2 + phaseDelta n / 2 := by
      have ha0 := alphaZero_eq_phaseNat_add_delta hdom.phaseDomain
      have hu_cast : (u : ℝ) = (phaseNat n : ℝ) - 1 := by
        dsimp [u]; rw [Nat.cast_sub (by omega : 1 ≤ phaseNat n), Nat.cast_one]
      linarith
    rw [hu_eq, Real.rpow_add two_pos, two_rpow_neg_half_alphaZero_sub_one hn1]
    have he_ne : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
    field_simp [he_ne, hn_pos.ne', hu_pos.ne']
  rw [hcenter] at hent
  -- Bound the logarithm of the RHS of `hent`
  have h1mlam_inv_le : (1 - lam)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) two_pos]
    linarith
  have hlb2_pos : 0 < logBaseTwo (n : ℝ) := div_pos hL_pos q_pos
  have hu1_pos : (0 : ℝ) < ((u - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hu1, Nat.cast_one]
    have : (2 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu2
    linarith
  have hu_log_le :
      ((u - 1 : ℕ) : ℝ) * Real.log (2 * logBaseTwo (n : ℝ) / (u : ℝ)) ≤
        2 * logBaseTwo (n : ℝ) - (u : ℝ) + 1 := by
    have hle_u1 : 2 * logBaseTwo (n : ℝ) / (u : ℝ) ≤
        2 * logBaseTwo (n : ℝ) / ((u - 1 : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_left (by positivity) hu1_pos
      rw [Nat.cast_sub hu1, Nat.cast_one]
      linarith
    have hlog1 : Real.log (2 * logBaseTwo (n : ℝ) / (u : ℝ)) ≤
        Real.log (2 * logBaseTwo (n : ℝ) / ((u - 1 : ℕ) : ℝ)) :=
      Real.log_le_log (by positivity) hle_u1
    have hlog2 : Real.log (2 * logBaseTwo (n : ℝ) / ((u - 1 : ℕ) : ℝ)) ≤
        2 * logBaseTwo (n : ℝ) / ((u - 1 : ℕ) : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    calc ((u - 1 : ℕ) : ℝ) * Real.log (2 * logBaseTwo (n : ℝ) / (u : ℝ))
        ≤ ((u - 1 : ℕ) : ℝ) * (2 * logBaseTwo (n : ℝ) / ((u - 1 : ℕ) : ℝ) - 1) :=
          mul_le_mul_of_nonneg_left (le_trans hlog1 hlog2) hu1_pos.le
      _ = 2 * logBaseTwo (n : ℝ) - ((u - 1 : ℕ) : ℝ) := by
          field_simp [hu1_pos.ne']
      _ = 2 * logBaseTwo (n : ℝ) - (u : ℝ) + 1 := by
          rw [Nat.cast_sub hu1, Nat.cast_one]; ring
  have h2lb2_sub_u :
      2 * logBaseTwo (n : ℝ) - (u : ℝ) + 1 ≤
        (2 / q) * logLogOrder n + 2 * |phaseC| / q + 3 := by
    have ha0 := alphaZero_eq_two_phaseS_div_q_add_one hn1
    have ha_nat := alphaZero_eq_phaseNat_add_delta hdom.phaseDomain
    have hu_cast : (u : ℝ) = (phaseNat n : ℝ) - 1 := by
      dsimp [u]; rw [Nat.cast_sub (by omega : 1 ≤ phaseNat n), Nat.cast_one]
    have hd_lt1 : phaseDelta n ≤ 1 := (phaseDelta_lt_one n).le
    have hdiv_C : -2 * phaseC / q ≤ 2 * |phaseC| / q := by
      rw [div_le_div_iff_of_pos_right q_pos]
      linarith [neg_abs_le phaseC]
    have hid : 2 * logBaseTwo (n : ℝ) - (u : ℝ) + 1 =
        (2 / q) * logLogOrder n + (-2 * phaseC / q) + phaseDelta n + 1 := by
      have hlb2 : logBaseTwo (n : ℝ) = logOrder n / q := rfl
      unfold phaseS at ha0
      rw [hlb2, hu_cast]
      have : (phaseNat n : ℝ) = alphaZero n - phaseDelta n := by linarith
      rw [this, ha0]
      field_simp [q_ne_zero]
      ring
    linarith
  have hsingle_factor_log :
      Real.log (2 * Real.exp 1 ^ 2 / lam *
          ((2 * logBaseTwo (n : ℝ) / (u : ℝ)) * (2 : ℝ) ^ (phaseDelta n / 2)) ^ (u - 1)) ≤
        Cconst * logLogOrder n + ((u - 1 : ℕ) : ℝ) * (Real.log 2 / 2) * phaseDelta n := by
    have hlam_pos : 0 < lam := lt_of_lt_of_le htheta_pos hlam_ge
    have hq0 : 0 < q := q_pos
    have h2e_le : Real.log (2 * Real.exp 1 ^ 2 / lam) ≤
        |Real.log (2 * Real.exp 1 ^ 2 / thetaBar)| * logLogOrder n := by
      have h1 : Real.log (2 * Real.exp 1 ^ 2 / lam) ≤
          Real.log (2 * Real.exp 1 ^ 2 / thetaBar) := by
        apply Real.log_le_log (by positivity)
        exact div_le_div_of_nonneg_left (by positivity) htheta_pos hlam_ge
      have h2 : Real.log (2 * Real.exp 1 ^ 2 / thetaBar) ≤
          |Real.log (2 * Real.exp 1 ^ 2 / thetaBar)| := le_abs_self _
      have h3 : |Real.log (2 * Real.exp 1 ^ 2 / thetaBar)| * 1 ≤
          |Real.log (2 * Real.exp 1 ^ 2 / thetaBar)| * logLogOrder n :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      linarith
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_mul (by positivity) (by positivity),
      Real.log_rpow two_pos]
    have hC_expand :
        |Real.log (2 * Real.exp 1 ^ 2 / thetaBar)| * logLogOrder n +
          ((2 / q) * logLogOrder n + 2 * |phaseC| / q + 3) ≤
        Cconst * logLogOrder n := by
      have h1 : 2 * |phaseC| / q + 3 ≤ (2 * |phaseC| / q + 4) * logLogOrder n := by
        have hposC : 0 ≤ 2 * |phaseC| / q + 4 := by positivity
        have hm := mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ logLogOrder n) hposC
        linarith
      have hdist : Cconst * logLogOrder n =
          |Real.log (2 * Real.exp 1 ^ 2 / thetaBar)| * logLogOrder n +
            (2 / q) * logLogOrder n + (2 * |phaseC| / q + 4) * logLogOrder n := by
        dsimp [Cconst]
        ring
      linarith
    have hmul_expand :
        ((u - 1 : ℕ) : ℝ) *
            (Real.log (2 * logBaseTwo (n : ℝ) / (u : ℝ)) + phaseDelta n / 2 * Real.log 2) =
          ((u - 1 : ℕ) : ℝ) * Real.log (2 * logBaseTwo (n : ℝ) / (u : ℝ)) +
            ((u - 1 : ℕ) : ℝ) * (Real.log 2 / 2) * phaseDelta n := by ring
    rw [hmul_expand]
    linarith
  -- Multiply by `m` and combine with `-lam * n * (1 + phiInfAux lam)`
  have hm_factor_le :
      (2 * Real.exp 1 ^ 2 / lam *
          ((2 * logBaseTwo (n : ℝ) / (u : ℝ)) * (2 : ℝ) ^ (phaseDelta n / 2)) ^ (u - 1)) ^ m ≤
        Real.exp ((m : ℝ) * Cconst * logLogOrder n +
          lam * (n : ℝ) * (Real.log 2 / 2) * phaseDelta n) := by
    have hlam_pos : 0 < lam := lt_of_lt_of_le htheta_pos hlam_ge
    have hbase_pos : 0 < 2 * Real.exp 1 ^ 2 / lam *
        ((2 * logBaseTwo (n : ℝ) / (u : ℝ)) * (2 : ℝ) ^ (phaseDelta n / 2)) ^ (u - 1) := by
      positivity
    calc _ = Real.exp ((m : ℝ) * Real.log (2 * Real.exp 1 ^ 2 / lam *
            ((2 * logBaseTwo (n : ℝ) / (u : ℝ)) * (2 : ℝ) ^ (phaseDelta n / 2)) ^ (u - 1))) := by
          rw [Real.exp_nat_mul, Real.exp_log hbase_pos]
      _ ≤ Real.exp ((m : ℝ) * (Cconst * logLogOrder n +
            ((u - 1 : ℕ) : ℝ) * (Real.log 2 / 2) * phaseDelta n)) := by
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_left hsingle_factor_log (Nat.cast_nonneg m)
      _ ≤ Real.exp ((m : ℝ) * Cconst * logLogOrder n +
            lam * (n : ℝ) * (Real.log 2 / 2) * phaseDelta n) := by
          apply Real.exp_le_exp.mpr
          have hmu_eq : (m : ℝ) * (u : ℝ) = lam * (n : ℝ) := by
            dsimp [lam]; rw [Nat.cast_mul]; field_simp [hn_pos.ne']
          have hu1_le_u : ((u - 1 : ℕ) : ℝ) ≤ (u : ℝ) := by
            rw [Nat.cast_sub hu1, Nat.cast_one]; linarith
          have hd_nn : 0 ≤ (Real.log 2 / 2) * phaseDelta n :=
            mul_nonneg (by positivity) hdelta.1
          have hmul_u : (m : ℝ) * (((u - 1 : ℕ) : ℝ) * ((Real.log 2 / 2) * phaseDelta n)) ≤
              (m : ℝ) * ((u : ℝ) * ((Real.log 2 / 2) * phaseDelta n)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hu1_le_u hd_nn)
              (Nat.cast_nonneg m)
          calc (m : ℝ) * (Cconst * logLogOrder n +
                ((u - 1 : ℕ) : ℝ) * (Real.log 2 / 2) * phaseDelta n)
              = (m : ℝ) * Cconst * logLogOrder n +
                  (m : ℝ) * (((u - 1 : ℕ) : ℝ) * ((Real.log 2 / 2) * phaseDelta n)) := by ring
            _ ≤ (m : ℝ) * Cconst * logLogOrder n +
                  (m : ℝ) * ((u : ℝ) * ((Real.log 2 / 2) * phaseDelta n)) :=
                add_le_add_right hmul_u _
            _ = (m : ℝ) * Cconst * logLogOrder n +
                  ((m : ℝ) * (u : ℝ)) * (Real.log 2 / 2) * phaseDelta n := by ring
            _ = (m : ℝ) * Cconst * logLogOrder n +
                  lam * (n : ℝ) * (Real.log 2 / 2) * phaseDelta n := by rw [hmu_eq]
  have hm_over_n : (m : ℝ) ≤ (1 / 10 : ℝ) * (n : ℝ) / logOrder n := by
    have hlam_def : (m : ℝ) * (u : ℝ) ≤ (1 / 10 : ℝ) * (n : ℝ) := by
      have := (div_le_iff₀ hn_pos).mp hlam_le
      rwa [Nat.cast_mul] at this
    rw [le_div_iff₀ hL_pos]
    calc (m : ℝ) * logOrder n
        ≤ (m : ℝ) * (u : ℝ) := mul_le_mul_of_nonneg_left hu_ge_L (Nat.cast_nonneg m)
      _ ≤ (1 / 10 : ℝ) * (n : ℝ) := hlam_def
  have hphi_mono : phiInfAux thetaBar ≤ phiInfAux lam := by
    rcases eq_or_lt_of_le hlam_ge with heq | hlt
    · rw [heq]
    · exact (strictMonoOn_phiInfAux
        ⟨htheta_pos, lt_of_le_of_lt htheta_hi (by norm_num : (1 / 20 : ℝ) < 1)⟩
        ⟨lt_trans htheta_pos hlt, lt_of_le_of_lt hlam_le (by norm_num : (1 / 10 : ℝ) < 1)⟩ hlt).le
  have hrate_neg :
      lam * (n : ℝ) * (Real.log 2 / 2) * phaseDelta n +
          (-lam * (n : ℝ) * (1 + phiInfAux lam)) ≤
        -2 * thetaBar * gamma * (n : ℝ) := by
    have h1 : lam * (Real.log 2 / 2) * phaseDelta n - lam * (1 + phiInfAux lam) =
        -lam * (phiInfAux lam + Real.log 2 / 2 * (phaseTarget (phaseDelta n) - 1)) := by
      unfold phaseTarget
      field_simp [(Real.log_pos one_lt_two).ne']
      ring
    have h2 : 2 * gamma ≤ phiInfAux lam + Real.log 2 / 2 * (phaseTarget (phaseDelta n) - 1) :=
      le_trans hphi_ge (add_le_add_left hphi_mono _)
    have hlam_nn : 0 ≤ lam := le_trans htheta_pos.le hlam_ge
    have h3 : 2 * thetaBar * gamma ≤
        lam * (phiInfAux lam + Real.log 2 / 2 * (phaseTarget (phaseDelta n) - 1)) := by
      calc 2 * thetaBar * gamma
          = thetaBar * (2 * gamma) := by ring
        _ ≤ lam * (phiInfAux lam + Real.log 2 / 2 * (phaseTarget (phaseDelta n) - 1)) :=
          mul_le_mul hlam_ge h2 (by positivity) hlam_nn
    have h4 := mul_le_mul_of_nonneg_right h3 hn_pos.le
    calc lam * (n : ℝ) * (Real.log 2 / 2) * phaseDelta n +
            (-lam * (n : ℝ) * (1 + phiInfAux lam))
        = (lam * (Real.log 2 / 2) * phaseDelta n - lam * (1 + phiInfAux lam)) * (n : ℝ) := by
          ring
      _ = -(lam * (phiInfAux lam + Real.log 2 / 2 * (phaseTarget (phaseDelta n) - 1)) * (n : ℝ)) := by
          rw [h1]; ring
      _ ≤ -(2 * thetaBar * gamma * (n : ℝ)) := neg_le_neg h4
      _ = -2 * thetaBar * gamma * (n : ℝ) := by ring
  refine le_trans hent ?_
  calc (1 - lam)⁻¹ *
          (2 * Real.exp 1 ^ 2 / lam *
            ((2 * logBaseTwo (n : ℝ) / (u : ℝ)) * (2 : ℝ) ^ (phaseDelta n / 2)) ^ (u - 1)) ^ m *
          Real.exp (-lam * (n : ℝ) * (1 + phiInfAux lam))
      ≤ 2 * Real.exp ((m : ℝ) * Cconst * logLogOrder n +
          lam * (n : ℝ) * (Real.log 2 / 2) * phaseDelta n) *
          Real.exp (-lam * (n : ℝ) * (1 + phiInfAux lam)) := by
        exact mul_le_mul
          (mul_le_mul h1mlam_inv_le hm_factor_le (by positivity) zero_le_two)
          le_rfl (Real.exp_pos _).le (by positivity)
    _ = Real.exp (Real.log 2 + (m : ℝ) * Cconst * logLogOrder n +
          (lam * (n : ℝ) * (Real.log 2 / 2) * phaseDelta n +
            (-lam * (n : ℝ) * (1 + phiInfAux lam)))) := by
        have h2exp : (2 : ℝ) * Real.exp ((m : ℝ) * Cconst * logLogOrder n +
            lam * (n : ℝ) * (Real.log 2 / 2) * phaseDelta n) =
          Real.exp (Real.log 2) * Real.exp ((m : ℝ) * Cconst * logLogOrder n +
            lam * (n : ℝ) * (Real.log 2 / 2) * phaseDelta n) := by
          rw [Real.exp_log two_pos]
        rw [h2exp, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (-thetaBar * gamma * (n : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have _hq0 : 0 < q := q_pos
        have hC_nn : 0 ≤ Cconst := by
          dsimp [Cconst]
          positivity
        have hell_nn : 0 ≤ logLogOrder n := le_trans (by norm_num : (0 : ℝ) ≤ 2) hell_ge2
        have hmC : (m : ℝ) * Cconst * logLogOrder n ≤
            (n : ℝ) * ((1 / 10 : ℝ) * (Cconst * logLogOrder n / logOrder n)) := by
          calc (m : ℝ) * Cconst * logLogOrder n
              ≤ ((1 / 10 : ℝ) * (n : ℝ) / logOrder n) * Cconst * logLogOrder n :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hm_over_n hC_nn) hell_nn
            _ = (n : ℝ) * ((1 / 10 : ℝ) * (Cconst * logLogOrder n / logOrder n)) := by ring
        have herr_n : Real.log 2 +
            (n : ℝ) * ((1 / 10 : ℝ) * (Cconst * logLogOrder n / logOrder n)) ≤
            thetaBar * gamma * (n : ℝ) := by
          have hmul_err := mul_le_mul_of_nonneg_right herr hn_pos.le
          rwa [add_mul, div_mul_cancel₀ _ hn_pos.ne',
            mul_comm ((1 / 10 : ℝ) * (Cconst * logLogOrder n / logOrder n)) (n : ℝ)] at hmul_err
        calc Real.log 2 + (m : ℝ) * Cconst * logLogOrder n +
              (lam * (n : ℝ) * (Real.log 2 / 2) * phaseDelta n +
                (-lam * (n : ℝ) * (1 + phiInfAux lam)))
            ≤ (Real.log 2 + (n : ℝ) * ((1 / 10 : ℝ) * (Cconst * logLogOrder n / logOrder n))) +
                (-2 * thetaBar * gamma * (n : ℝ)) :=
              add_le_add (add_le_add_right hmC _) hrate_neg
          _ ≤ thetaBar * gamma * (n : ℝ) + (-2 * thetaBar * gamma * (n : ℝ)) :=
              add_le_add_left herr_n _
          _ = -thetaBar * gamma * (n : ℝ) := by ring

/-! ## 5. Conditional `L^p` (`1 ≤ p < ∞`) and expectation convergence (`Main Theorem`) -/

/-- **Conditional `L^p` convergence of the normalized `χ - ζ` gap (`Main Theorem`):**
if for every `ε > 0` the single-`n` deviation probability around `1 / 4` is
`O_ε(n^{-3/2} (log n)^{β + 5/2})` with `β = 2 / log 2 + 1 / 2`, then for every
`1 ≤ p < ∞`, `E[ |((log₂ n)³ / n)(χ(G_n) - ζ(G_n)) - 1 / 4|^p ] → 0`. -/
theorem tendsto_integral_abs_sub_rpow_normalizedGap_of_polylog_tail
    (htail : ∀ eps : ℝ, 0 < eps →
      (fun n : ℕ ↦ (randomGraphMeasure n).real
        {G : LabeledGraph n |
          eps < |(Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
            ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) - 1 / 4|})
        =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-(3 / 2 : ℝ)) *
        (Real.log (n : ℝ)) ^ ((2 / Real.log 2 + 1 / 2 : ℝ) + 5 / 2)))
    {p : ℝ} (hp : 1 ≤ p) :
    Tendsto (fun n : ℕ ↦
      ∫ G : LabeledGraph n,
        |(Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
          ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) - 1 / 4| ^ p
        ∂randomGraphMeasure n)
      atTop (nhds 0) := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let Y : ∀ n : ℕ, LabeledGraph n → ℝ := fun n G ↦
    (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
      ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
  -- For any fixed `eps > 0`, the tail contribution `((log₂ n)³ + 1/4)^p * P(|Y_n - 1/4| > eps) → 0`
  have htail_term_zero : ∀ eps : ℝ, 0 < eps →
      Tendsto (fun n : ℕ ↦
        ((Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4) ^ p *
          (randomGraphMeasure n).real {G : LabeledGraph n | eps < |Y n G - 1 / 4|})
        atTop (nhds 0) := by
    intro eps heps
    let beta : ℝ := 2 / Real.log 2 + 1 / 2
    let A : ℝ := 4 * p + (beta + 5 / 2)
    have hlog_bound : ∀ᶠ n : ℕ in atTop,
        ((Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4) ^ p ≤ (Real.log (n : ℝ)) ^ (4 * p) := by
      have hL9 : ∀ᶠ n : ℕ in atTop, 9 ≤ Real.log (n : ℝ) :=
        tendsto_logOrder_atTop.eventually (eventually_ge_atTop (9 : ℝ))
      filter_upwards [hL9] with n hL
      have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
      have hlb2_le : Real.logb 2 (n : ℝ) ≤ 2 * Real.log (n : ℝ) := by
        rw [Real.logb, div_le_iff₀ (Real.log_pos one_lt_two)]
        have hm := mul_le_mul_of_nonneg_left hlog2_gt.le
          (show (0 : ℝ) ≤ 2 * Real.log (n : ℝ) by linarith)
        linarith
      have hlb2_nn : 0 ≤ Real.logb 2 (n : ℝ) := by
        rw [Real.logb]
        exact div_nonneg (by linarith) (Real.log_pos one_lt_two).le
      have hcube_le : (Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4 ≤ (Real.log (n : ℝ)) ^ 4 := by
        have hc : (Real.logb 2 (n : ℝ)) ^ 3 ≤ 8 * (Real.log (n : ℝ)) ^ 3 := by
          calc (Real.logb 2 (n : ℝ)) ^ 3
              ≤ (2 * Real.log (n : ℝ)) ^ 3 := pow_le_pow_left₀ hlb2_nn hlb2_le 3
            _ = 8 * (Real.log (n : ℝ)) ^ 3 := by ring
        have h1_le_L3 : (1 : ℝ) ≤ (Real.log (n : ℝ)) ^ 3 := by
          calc (1 : ℝ) = 1 ^ 3 := by norm_num
            _ ≤ (Real.log (n : ℝ)) ^ 3 := pow_le_pow_left₀ zero_le_one (by linarith) 3
        have h9L3_le_L4 : 9 * (Real.log (n : ℝ)) ^ 3 ≤ (Real.log (n : ℝ)) ^ 4 := by
          calc 9 * (Real.log (n : ℝ)) ^ 3
              ≤ Real.log (n : ℝ) * (Real.log (n : ℝ)) ^ 3 :=
                mul_le_mul_of_nonneg_right hL (pow_nonneg (by linarith) 3)
            _ = (Real.log (n : ℝ)) ^ 4 := by ring
        linarith
      calc ((Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4) ^ p
          ≤ ((Real.log (n : ℝ)) ^ 4) ^ p :=
            Real.rpow_le_rpow (by positivity) hcube_le hp_pos.le
        _ = (Real.log (n : ℝ)) ^ (4 * p) := by
            rw [← Real.rpow_natCast (Real.log (n : ℝ)) 4,
              ← Real.rpow_mul (by linarith : 0 ≤ Real.log (n : ℝ))]
            norm_num
    obtain ⟨C, hC_pos, hC_ev⟩ := (htail eps heps).exists_pos
    rw [Asymptotics.IsBigOWith] at hC_ev
    have hdecay : Tendsto (fun n : ℕ ↦
        C * ((Real.log (n : ℝ)) ^ A * (n : ℝ) ^ (-(3 / 2 : ℝ)))) atTop (nhds 0) := by
      have ho : (fun x : ℝ ↦ (Real.log x) ^ A) =o[atTop] (fun x : ℝ ↦ x ^ (3 / 2 : ℝ)) :=
        isLittleO_log_rpow_rpow_atTop A (by norm_num : (0 : ℝ) < 3 / 2)
      have hdiv := (ho.tendsto_div_nhds_zero).comp (tendsto_natCast_atTop_atTop (R := ℝ))
      have hmul := hdiv.const_mul C
      rw [mul_zero] at hmul
      refine hmul.congr' ?_
      filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
      have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
      dsimp only [Function.comp_def]
      rw [Real.rpow_neg hn_pos.le, ← div_eq_mul_inv]
    refine squeeze_zero' ?_ ?_ hdecay
    · exact Filter.Eventually.of_forall fun n ↦
        mul_nonneg (Real.rpow_nonneg (by
          have hnn : 0 ≤ (Real.logb 2 (n : ℝ)) ^ 3 := by
            rcases eq_or_lt_of_le (Nat.zero_le n) with rfl | hpos
            · simp [Real.logb]
            · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpos
              exact pow_nonneg (div_nonneg (Real.log_nonneg h1) (Real.log_pos one_lt_two).le) 3
          linarith) p) measureReal_nonneg
    · filter_upwards [hlog_bound, hC_ev, eventually_gt_atTop (2 : ℕ)] with n hlb hCb hn2
      have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
      have hL_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      have hrhs_nn : 0 ≤ (n : ℝ) ^ (-(3 / 2 : ℝ)) * (Real.log (n : ℝ)) ^ (beta + 5 / 2) :=
        mul_nonneg (Real.rpow_nonneg hn_pos.le _) (Real.rpow_nonneg hL_pos.le _)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg,
        abs_of_nonneg hrhs_nn] at hCb
      calc ((Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4) ^ p *
              (randomGraphMeasure n).real {G | eps < |Y n G - 1 / 4|}
          ≤ (Real.log (n : ℝ)) ^ (4 * p) *
              (C * ((n : ℝ) ^ (-(3 / 2 : ℝ)) * (Real.log (n : ℝ)) ^ (beta + 5 / 2))) :=
            mul_le_mul hlb hCb measureReal_nonneg (Real.rpow_nonneg hL_pos.le _)
        _ = C * (((Real.log (n : ℝ)) ^ (4 * p) * (Real.log (n : ℝ)) ^ (beta + 5 / 2)) *
              (n : ℝ) ^ (-(3 / 2 : ℝ))) := by ring
        _ = C * ((Real.log (n : ℝ)) ^ A * (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
            rw [← Real.rpow_add hL_pos]
  -- Epsilon-delta squeeze on `∫ |Y_n - 1/4|^p`
  rw [Metric.tendsto_nhds]
  intro delta hdelta
  have hd2_pos : 0 < delta / 2 := half_pos hdelta
  let eps : ℝ := (delta / 2) ^ (1 / p)
  have heps_pos : 0 < eps := Real.rpow_pos_of_pos hd2_pos _
  have heps_pow : eps ^ p = delta / 2 := by
    dsimp [eps]
    rw [← Real.rpow_mul hd2_pos.le, one_div_mul_cancel hp_pos.ne', Real.rpow_one]
  have htail_lt : ∀ᶠ n : ℕ in atTop,
      ((Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4) ^ p *
        (randomGraphMeasure n).real {G | eps < |Y n G - 1 / 4|} < delta / 2 :=
    (htail_term_zero eps heps_pos).eventually (gt_mem_nhds hd2_pos)
  filter_upwards [eventually_ge_atTop (2 : ℕ), htail_lt] with n hn2 htl
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hlb2_nn : 0 ≤ Real.logb 2 (n : ℝ) := by
    rw [Real.logb]
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))
      (Real.log_pos one_lt_two).le
  have hint_nn : 0 ≤ ∫ G : LabeledGraph n, |Y n G - 1 / 4| ^ p ∂randomGraphMeasure n :=
    integral_nonneg fun G ↦ Real.rpow_nonneg (abs_nonneg _) p
  let Eset : Set (LabeledGraph n) := {G | eps < |Y n G - 1 / 4|}
  have hpointwise : ∀ G : LabeledGraph n,
      |Y n G - 1 / 4| ^ p ≤
        eps ^ p + Eset.indicator
          (fun _ ↦ ((Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4) ^ p) G := by
    intro G
    by_cases hG : G ∈ Eset
    · rw [Set.indicator_of_mem hG]
      have hdiff_nn : 0 ≤ (chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ) := by
        exact sub_nonneg.mpr (by exact_mod_cast cochromaticNumber_le_chromaticNumber G)
      have hdiff_le : (chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ) ≤ (n : ℝ) := by
        have hchi_le : chromaticNumberNat G ≤ n := by
          simpa [Fintype.card_fin] using chromaticNumberNat_le_card G
        have hchi_R : (chromaticNumberNat G : ℝ) ≤ (n : ℝ) := by exact_mod_cast hchi_le
        have hzeta_nn : (0 : ℝ) ≤ (cochromaticNumber G : ℝ) := Nat.cast_nonneg _
        linarith
      have hY_nn : 0 ≤ Y n G := by
        dsimp [Y]; positivity
      have hY_le : Y n G ≤ (Real.logb 2 (n : ℝ)) ^ 3 := by
        dsimp [Y]
        calc (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
                ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
            ≤ (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) * (n : ℝ) :=
              mul_le_mul_of_nonneg_left hdiff_le (by positivity)
          _ = (Real.logb 2 (n : ℝ)) ^ 3 := div_mul_cancel₀ _ hn_pos.ne'
      have habs_le : |Y n G - 1 / 4| ≤ (Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4 := by
        rw [abs_le]
        exact ⟨by linarith, by linarith⟩
      have hrpow_le : |Y n G - 1 / 4| ^ p ≤ ((Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4) ^ p :=
        Real.rpow_le_rpow (abs_nonneg _) habs_le hp_pos.le
      linarith [Real.rpow_nonneg heps_pos.le p]
    · rw [Set.indicator_of_notMem hG, add_zero]
      have hle : |Y n G - 1 / 4| ≤ eps := not_lt.mp hG
      exact Real.rpow_le_rpow (abs_nonneg _) hle hp_pos.le
  have hint_le :
      ∫ G : LabeledGraph n, |Y n G - 1 / 4| ^ p ∂randomGraphMeasure n ≤
        eps ^ p + ((Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4) ^ p *
          (randomGraphMeasure n).real Eset := by
    calc ∫ G : LabeledGraph n, |Y n G - 1 / 4| ^ p ∂randomGraphMeasure n
        ≤ ∫ G : LabeledGraph n,
            (eps ^ p + Eset.indicator
              (fun _ ↦ ((Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4) ^ p) G)
            ∂randomGraphMeasure n :=
          integral_mono (Integrable.of_finite) (Integrable.of_finite) hpointwise
      _ = (∫ _G : LabeledGraph n, eps ^ p ∂randomGraphMeasure n) +
            ∫ G : LabeledGraph n,
              Eset.indicator (fun _ ↦ ((Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4) ^ p) G
              ∂randomGraphMeasure n :=
          integral_add (Integrable.of_finite) (Integrable.of_finite)
      _ = eps ^ p + ((Real.logb 2 (n : ℝ)) ^ 3 + 1 / 4) ^ p *
            (randomGraphMeasure n).real Eset := by
          rw [integral_const, probReal_univ, one_smul,
            integral_indicator_const _ (Set.toFinite Eset).measurableSet,
            smul_eq_mul, mul_comm]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hint_nn]
  linarith

/-- **Conditional expectation asymptotic for `χ(G_n) - ζ(G_n)` (`Main Theorem`):**
under the Main Theorem's `O_ε(n^{-3/2} (log n)^{β + 5/2})` deviation tail,
`((log₂ n)³ / n) * E[χ(G_n) - ζ(G_n)] → 1 / 4`. -/
theorem tendsto_expected_normalizedGap_of_polylog_tail
    (htail : ∀ eps : ℝ, 0 < eps →
      (fun n : ℕ ↦ (randomGraphMeasure n).real
        {G : LabeledGraph n |
          eps < |(Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
            ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) - 1 / 4|})
        =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-(3 / 2 : ℝ)) *
        (Real.log (n : ℝ)) ^ ((2 / Real.log 2 + 1 / 2 : ℝ) + 5 / 2))) :
    Tendsto (fun n : ℕ ↦
      (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
        ∫ G : LabeledGraph n,
          ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
          ∂randomGraphMeasure n)
      atTop (nhds (1 / 4 : ℝ)) := by
  have hL1 := tendsto_integral_abs_sub_rpow_normalizedGap_of_polylog_tail htail le_rfl
  rw [Metric.tendsto_nhds] at hL1 ⊢
  intro delta hdelta
  filter_upwards [hL1 delta hdelta] with n hn
  rw [Real.dist_eq, sub_zero] at hn
  rw [Real.dist_eq]
  have heq :
      (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
          (∫ G : LabeledGraph n,
            ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
            ∂randomGraphMeasure n) - 1 / 4 =
        ∫ G : LabeledGraph n,
          ((Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
            ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) - 1 / 4)
          ∂randomGraphMeasure n := by
    symm
    rw [integral_sub (Integrable.of_finite) (Integrable.of_finite),
      integral_const_mul, integral_const, probReal_univ, one_smul]
  have habs_int :
      |∫ G : LabeledGraph n,
          ((Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
            ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) - 1 / 4)
          ∂randomGraphMeasure n| ≤
        ∫ G : LabeledGraph n,
          |(Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
            ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) - 1 / 4| ^ (1 : ℝ)
          ∂randomGraphMeasure n := by
    calc |∫ G : LabeledGraph n, _ ∂randomGraphMeasure n|
        ≤ ∫ G : LabeledGraph n,
            |(Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
              ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) - 1 / 4|
            ∂randomGraphMeasure n := abs_integral_le_integral_abs
      _ = ∫ G : LabeledGraph n,
            |(Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
              ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) - 1 / 4| ^ (1 : ℝ)
            ∂randomGraphMeasure n := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun G ↦ ?_)
          exact (Real.rpow_one _).symm
  have hint_nn : 0 ≤ ∫ G : LabeledGraph n,
      |(Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
        ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) - 1 / 4| ^ (1 : ℝ)
      ∂randomGraphMeasure n :=
    integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _
  rw [abs_of_nonneg hint_nn] at hn
  rw [heq]
  exact lt_of_le_of_lt habs_int hn

end

end Erdos625HP
