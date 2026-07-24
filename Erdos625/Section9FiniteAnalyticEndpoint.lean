import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Finite analytic endpoint estimate for Section IX

This module proves the finite version of manuscript (9.7)--(9.9).  It keeps
the exact local reward, its increments, the truncated sum through
`R = floor(U / 2)`, the cell parameter bound, and the finite exponential form
of `U ≤ 3 log_2 m`.  The conclusion asserts one absolute constant, uniform in
all finite parameters.  It does not supply the upstream probabilistic event
or identify these finite parameters with a random residual table.
-/

namespace Erdos625

open scoped BigOperators

/-- Local signed reward `g` from manuscript (6.5). -/
def endpointRewardNat (x : ℕ) : ℕ :=
  if 3 ≤ x then 2 ^ (x.choose 2 - 1) else 1

/-- Real increment `Delta_x = g(x) - g(x-1)` from (9.5). -/
def endpointIncrement (x : ℕ) : ℝ :=
  (endpointRewardNat x : ℝ) - (endpointRewardNat (x - 1) : ℝ)

/-- Truncated local correction `lambda` from (9.6). -/
noncomputable def endpointLambda (R : ℕ) (theta : ℝ) : ℝ :=
  ∑ x ∈ Finset.Icc 3 R,
    endpointIncrement x * theta ^ x / (x.factorial : ℝ)

/-- Quadratic-plus-higher local correction `q` from (9.6). -/
noncomputable def endpointQ (R : ℕ) (theta : ℝ) : ℝ :=
  theta ^ 2 / 2 + endpointLambda R theta

lemma monotoneRatio_le_endpoint
    (R x : ℕ) (a q : ℕ → ℝ)
    (hx3 : 3 ≤ x) (hxR : x ≤ R)
    (ha : ∀ n, 3 ≤ n → n ≤ R → 0 ≤ a n)
    (hq : ∀ i j, 3 ≤ i → i ≤ j → j < R → q i ≤ q j)
    (hrec : ∀ n, 3 ≤ n → n < R → a (n + 1) = a n * q n) :
    a x ≤ max (a 3) (a R) := by
  -- If there exists an index $i$ ($3 \leq i \leq x-1$) with $q_i > 1$, then pick the first such $i$.
  by_cases h_exists_i : ∃ i, 3 ≤ i ∧ i < x ∧ q i > 1;
  · -- Let $i$ be the smallest index such that $q_i > 1$.
    obtain ⟨i, hi₁, hi₂, hi₃⟩ : ∃ i, 3 ≤ i ∧ i < x ∧ q i > 1 ∧ ∀ j, 3 ≤ j → j < i → q j ≤ 1 := by
      exact ⟨ Nat.find h_exists_i, Nat.find_spec h_exists_i |>.1, Nat.find_spec h_exists_i |>.2.1, Nat.find_spec h_exists_i |>.2.2, fun j hj₁ hj₂ => not_lt.1 fun hj₃ => Nat.find_min h_exists_i hj₂ ⟨ hj₁, by linarith [ Nat.find_spec h_exists_i |>.2.1 ], hj₃ ⟩ ⟩;
    -- Since $q_i > 1$, we have $a_{i+1} \geq a_i$.
    have h_inc : ∀ j, i ≤ j → j < R → a (j + 1) ≥ a j := by
      exact fun j hj₁ hj₂ => by rw [ hrec j ( by linarith ) hj₂ ] ; nlinarith [ ha j ( by linarith ) ( by linarith ), hq i j hi₁ hj₁ hj₂ ] ;
    -- Since $a_{i+1} \geq a_i$, we have $a_x \leq a_R$.
    have h_le_R : a x ≤ a R := by
      have h_le_R : ∀ j, x ≤ j → j ≤ R → a x ≤ a j := by
        intro j hj₁ hj₂; induction hj₁ <;> norm_num at *;
        exact le_trans ( by solve_by_elim [ Nat.le_of_lt ] ) ( h_inc _ ( by linarith ) hj₂ );
      exact h_le_R R hxR le_rfl;
    exact le_trans h_le_R ( le_max_right _ _ );
  · -- Since there's no i with q i > 1, the sequence a n is non-increasing from 3 to x.
    have h_noninc : ∀ n, 3 ≤ n → n ≤ x → a n ≤ a 3 := by
      intro n hn hn'; induction hn <;> simp_all +decide ;
      exact hrec _ ‹_› ( by linarith ) ▸ le_trans ( mul_le_of_le_one_right ( ha _ ‹_› ( by linarith ) ) ( h_exists_i _ ‹_› hn' ) ) ( by solve_by_elim [ Nat.le_of_lt ] );
    exact le_max_of_le_left ( h_noninc x hx3 le_rfl )

lemma sum_before_half_crossing
    (R i : ℕ) (a q : ℕ → ℝ)
    (hi : 3 ≤ i) (hiR : i ≤ R)
    (ha : ∀ n, 3 ≤ n → n ≤ R → 0 ≤ a n)
    (hrec : ∀ n, 3 ≤ n → n < R → a (n + 1) = a n * q n)
    (hhalf : ∀ n, 3 ≤ n → n < i → q n ≤ (1/2 : ℝ)) :
    ∑ n ∈ Finset.Ico 3 i, a n ≤ 2 * a 3 := by
  -- By induction, we show that $a_n \leq a_3 \cdot 2^{-(n-3)}$ for all $n$ such that $3 \leq n < i$.
  have h_ind : ∀ n, 3 ≤ n → n < i → a n ≤ a 3 * (1 / 2) ^ (n - 3) := by
    intro n hn hn'; induction hn <;> norm_num at *;
    rename_i k hk ih; rw [ hrec k hk ( by linarith ) ] ; rw [ Nat.succ_sub ( by linarith ) ] ; norm_num [ pow_succ' ] at * ; nlinarith [ ih ( by linarith ), hhalf k hk ( by linarith ), ha k hk ( by linarith ) ] ;
  refine' le_trans ( Finset.sum_le_sum fun n hn => h_ind n ( Finset.mem_Ico.mp hn |>.1 ) ( Finset.mem_Ico.mp hn |>.2 ) ) _;
  erw [ Finset.sum_Ico_eq_sum_range ] ; norm_num [ mul_comm, ← Finset.mul_sum _ _ _, geom_sum_eq ] ; ring_nf;
  exact sub_le_self _ ( mul_nonneg ( mul_nonneg ( ha 3 ( by norm_num ) ( by linarith ) ) ( pow_nonneg ( by norm_num ) _ ) ) ( by norm_num ) )

lemma sum_after_double_crossing
    (R i : ℕ) (a q : ℕ → ℝ)
    (hi : 3 ≤ i) (hiR : i ≤ R)
    (ha : ∀ n, 3 ≤ n → n ≤ R → 0 ≤ a n)
    (hrec : ∀ n, 3 ≤ n → n < R → a (n + 1) = a n * q n)
    (hdouble : ∀ n, i ≤ n → n < R → (2 : ℝ) ≤ q n) :
    ∑ n ∈ Finset.Icc i R, a n ≤ 2 * a R := by
  -- By induction on $j$ from $i$ to $R$, we show that $a_j \leq a_R (1/2)^{R-j}$.
  have h_ind : ∀ j, i ≤ j ∧ j ≤ R → a j ≤ a R * (1 / 2) ^ (R - j) := by
    intro j hj;
    -- By induction on $j$ from $i$ to $R$, we show that $a_j \leq a_{j+1} / 2$.
    have h_ind_step : ∀ j, i ≤ j ∧ j < R → a j ≤ a (j + 1) / 2 := by
      exact fun n hn => by rw [ hrec n ( by linarith ) hn.2 ] ; nlinarith [ hdouble n hn.1 hn.2, ha n ( by linarith ) ( by linarith ) ] ;
    -- By induction on $R - j$, we show that $a_j \leq a_R / 2^{R-j}$.
    have h_induction : ∀ k, 0 ≤ k → k ≤ R - i → ∀ j, i ≤ j ∧ j + k ≤ R → a j ≤ a (j + k) / 2 ^ k := by
      intro k hk hk' j hj; induction' k with k ih generalizing j <;> norm_num [ Nat.pow_succ', ← div_div ] at *;
      convert le_trans ( ih ( Nat.le_of_lt hk' ) j hj.1 ( by linarith ) ) ( div_le_div_of_nonneg_right ( h_ind_step ( j + k ) ( by linarith ) ( by linarith ) ) ( by positivity ) ) using 1 <;> first | rfl | ring
    convert h_induction ( R - j ) ( Nat.zero_le _ ) ( Nat.sub_le_sub_left hj.1 _ ) j ⟨ hj.1, by omega ⟩ using 1 ; norm_num [ Nat.add_sub_of_le hj.2 ];
    ring;
    norm_num;
  refine' le_trans ( Finset.sum_le_sum fun x hx => h_ind x <| Finset.mem_Icc.mp hx ) _;
  erw [ Finset.sum_Ico_eq_sum_range ];
  rw [ ← Finset.mul_sum _ _ _, ← Finset.sum_range_reflect ];
  rw [ mul_comm ] ; gcongr;
  · grind;
  · rw [ Finset.sum_congr rfl fun x hx => by rw [ show R - ( i + ( R + 1 - i - 1 - x ) ) = x by norm_num at *; omega ] ] ; rw [ geom_sum_eq ] <;> ring <;> norm_num

lemma ratio_transition_length
    (R i j : ℕ) (q : ℕ → ℝ)
    (_hi : 3 ≤ i) (hij : i ≤ j) (_hjR : j < R)
    (_hpos : ∀ n, i ≤ n → n ≤ j → 0 ≤ q n)
    (hgrow : ∀ n, i ≤ n → n < j → 3 * q n ≤ 2 * q (n + 1))
    (hlo : (1/2 : ℝ) < q i) (hhi : q j < 2) :
    j - i ≤ 4 := by
  by_contra h_contra;
  -- Since $j - i > 4$, we have $q_j \geq (3/2)^{j-i} q_i$.
  have h_qj_ge : q j ≥ (3 / 2 : ℝ) ^ (j - i) * q i := by
    have h_qj_ge : ∀ n, i ≤ n → n ≤ j → q n ≥ (3 / 2 : ℝ) ^ (n - i) * q i := by
      intro n hn hn'; induction hn <;> norm_num at *;
      rename_i k hk₁ hk₂; rw [ Nat.succ_sub ( by linarith ) ] ; rw [ pow_succ' ] ; nlinarith [ hk₂ ( by linarith ), hgrow k ( by linarith ) ( by linarith ), pow_pos ( by norm_num : ( 0 : ℝ ) < 3 / 2 ) ( k - i ) ] ;
    exact h_qj_ge j hij le_rfl;
  nlinarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 3 / 2 ) ( not_le.mp h_contra ) ]


lemma geometricRatioEndpointBound
    (R : ℕ) (a q : ℕ → ℝ)
    (ha : ∀ x, 0 ≤ a x)
    (hq : ∀ x, 3 ≤ x → x < R → 0 ≤ q x)
    (hrec : ∀ x, 3 ≤ x → x < R → a (x + 1) = a x * q x)
    (hgrow : ∀ x, 3 ≤ x → x + 1 < R → 3 * q x ≤ 2 * q (x + 1)) :
    ∑ x ∈ Finset.Icc 3 R, a x ≤ 10 * (a 3 + a R) := by
  by_cases hR : 3 ≤ R
  · have hmono : ∀ x y, 3 ≤ x → x ≤ y → y < R → q x ≤ q y := by
      intro x y hx hxy hyR
      induction hxy <;> norm_num at *
      grind
    by_cases hall : ∀ x, 3 ≤ x → x < R → q x ≤ (1 / 2 : ℝ)
    · have hh := sum_before_half_crossing R R a q hR le_rfl (fun x _ _ => ha x) hrec hall
      change (∑ x ∈ Finset.Ico 3 (R+1), a x) ≤ _
      rw [Finset.sum_Ico_succ_top hR]
      have h3 := ha 3
      have hlast := ha R
      nlinarith
    · push Not at hall
      obtain ⟨i, hi3, hiR, hiq⟩ := hall
      let i₀ := Nat.find (show ∃ i, 3 ≤ i ∧ i < R ∧ (1 / 2 : ℝ) < q i from ⟨i, hi3, hiR, hiq⟩)
      have hi₀ := Nat.find_spec (show ∃ i, 3 ≤ i ∧ i < R ∧ (1 / 2 : ℝ) < q i from ⟨i, hi3, hiR, hiq⟩)
      have hbefore : ∀ n, 3 ≤ n → n < i₀ → q n ≤ (1 / 2 : ℝ) := by
        intro n hn hni
        exact le_of_not_gt (fun hh => Nat.find_min (show ∃ i, 3 ≤ i ∧ i < R ∧ (1 / 2 : ℝ) < q i from ⟨i, hi3, hiR, hiq⟩) hni ⟨hn, by omega, hh⟩)
      have hhead := sum_before_half_crossing R i₀ a q hi₀.1 hi₀.2.1.le (fun x _ _ => ha x) hrec hbefore
      by_cases htail : ∀ x, i₀ ≤ x → x < R → (2 : ℝ) ≤ q x
      · have ht := sum_after_double_crossing R i₀ a q hi₀.1 hi₀.2.1.le (fun x _ _ => ha x) hrec htail
        have hsplit : ∑ x ∈ Finset.Icc 3 R, a x =
            ∑ x ∈ Finset.Ico 3 i₀, a x + ∑ x ∈ Finset.Icc i₀ R, a x := by
          have hwhole : (∑ x ∈ Finset.Icc 3 R, a x) = ∑ x ∈ Finset.Ico 3 (R+1), a x := by rfl
          have hright : (∑ x ∈ Finset.Icc i₀ R, a x) = ∑ x ∈ Finset.Ico i₀ (R+1), a x := by rfl
          rw [hwhole, hright]
          exact (Finset.sum_Ico_consecutive a hi₀.1 (by omega)).symm
        rw [hsplit]
        have h3 := ha 3
        have hlast := ha R
        nlinarith
      · push Not at htail
        obtain ⟨j, hij, hjR, hjq⟩ := htail
        let j₀ := Finset.max' (Finset.filter (fun x => q x < 2) (Finset.Ico i₀ R))
          ⟨j, by simp [hij, hjR, hjq]⟩
        have hjmem : j₀ ∈ Finset.filter (fun x => q x < 2) (Finset.Ico i₀ R) :=
          Finset.max'_mem _ _
        have hjprops : i₀ ≤ j₀ ∧ j₀ < R ∧ q j₀ < 2 := by
          have hp := (Finset.mem_filter.mp hjmem)
          have hiR : i₀ ≤ j₀ ∧ j₀ < R := (Finset.mem_Ico.mp hp.1)
          exact ⟨hiR.1, hiR.2, hp.2⟩
        have hafter : ∀ n, j₀ < n → n < R → (2 : ℝ) ≤ q n := by
          intro n hjn hnR
          exact le_of_not_gt (fun hnq => by
            have hnmem : n ∈ Finset.filter (fun x => q x < 2) (Finset.Ico i₀ R) := by
              simp only [Finset.mem_filter, Finset.mem_Ico]
              exact ⟨⟨by omega, hnR⟩, hnq⟩
            have := Finset.le_max' _ n hnmem
            omega)
        have htail' := sum_after_double_crossing R (j₀ + 1) a q (by omega)
          (by omega) (fun x _ _ => ha x) hrec (by intro n hn hnR; exact hafter n (by omega) hnR)
        have hlen : j₀ - i₀ ≤ 4 := ratio_transition_length R i₀ j₀ q hi₀.1 hjprops.1 hjprops.2.1
          (by intro n hn hnj; exact hq n (hi₀.1.trans hn) (hnj.trans_lt hjprops.2.1))
          (by intro n hn hnj; exact hgrow n (hi₀.1.trans hn) (by omega)) hi₀.2.2 hjprops.2.2
        have hmiddle_point : ∀ x ∈ Finset.Icc i₀ j₀, a x ≤ max (a 3) (a R) := by
          intro x hx
          rw [Finset.mem_Icc] at hx
          exact monotoneRatio_le_endpoint R x a q (hi₀.1.trans hx.1)
            (hx.2.trans hjprops.2.1.le) (fun x _ _ => ha x) hmono hrec
        have hmiddle : ∑ x ∈ Finset.Icc i₀ j₀, a x ≤ 5 * max (a 3) (a R) := by
          calc
            _ ≤ ∑ _x ∈ Finset.Icc i₀ j₀, max (a 3) (a R) := Finset.sum_le_sum hmiddle_point
            _ = ((j₀ + 1 - i₀ : ℕ) : ℝ) * max (a 3) (a R) := by
              rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
            _ ≤ 5 * max (a 3) (a R) := by
              have hm : 0 ≤ max (a 3) (a R) := le_max_of_le_left (ha 3)
              have hc : ((j₀ + 1 - i₀ : ℕ) : ℝ) ≤ 5 := by exact_mod_cast (by omega : j₀ + 1 - i₀ ≤ 5)
              nlinarith
        have hsplit : ∑ x ∈ Finset.Icc 3 R, a x =
            ∑ x ∈ Finset.Ico 3 i₀, a x + ∑ x ∈ Finset.Icc i₀ j₀, a x +
              ∑ x ∈ Finset.Icc (j₀ + 1) R, a x := by
          have hwhole : (∑ x ∈ Finset.Icc 3 R, a x) = ∑ x ∈ Finset.Ico 3 (R+1), a x := by rfl
          have hmid : (∑ x ∈ Finset.Icc i₀ j₀, a x) = ∑ x ∈ Finset.Ico i₀ (j₀+1), a x := by rfl
          have hright : (∑ x ∈ Finset.Icc (j₀+1) R, a x) = ∑ x ∈ Finset.Ico (j₀+1) (R+1), a x := by rfl
          rw [hwhole, hmid, hright]
          rw [Finset.sum_Ico_consecutive a hi₀.1 (by omega)]
          rw [Finset.sum_Ico_consecutive a (by omega : 3 ≤ j₀ + 1) (by omega)]
        rw [hsplit]
        have h3 := ha 3
        have hlast := ha R
        have hm1 : max (a 3) (a R) ≤ a 3 + a R := max_le (le_add_of_nonneg_right hlast) (le_add_of_nonneg_left h3)
        nlinarith
  · have : Finset.Icc 3 R = ∅ := by ext x; simp; omega
    rw [this]
    simp
    nlinarith [ha 3, ha R]

lemma dyadic_logconvex_sum_bound (R : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ∑ x ∈ Finset.Icc 3 R,
      (2 : ℝ) ^ (x.choose 2 - 1) * t ^ x / (x.factorial : ℝ)
      ≤ 10 * ((2 : ℝ) ^ (Nat.choose 3 2 - 1) * t ^ 3 / (Nat.factorial 3 : ℝ) +
        (2 : ℝ) ^ (R.choose 2 - 1) * t ^ R / (R.factorial : ℝ)) := by
  apply geometricRatioEndpointBound R (fun x => 2 ^ (x.choose 2 - 1) * t ^ x / (x.factorial : ℝ)) (fun x => 2^x * t / (x + 1));
  · exact fun x => by positivity;
  · exact fun _ _ _ => by positivity;
  · intro x hx₁ hx₂; rw [ Nat.choose_succ_succ ] ; ring;
    norm_num [ Nat.add_comm 1, Nat.factorial_succ ] ; ring;
    rw [ show x + x.choose 2 - 1 = x + ( x.choose 2 - 1 ) by rw [ Nat.add_sub_assoc ( Nat.choose_pos ( by linarith ) ) ] ] ; ring;
  · intro x hx₁ hx₂; rw [ mul_div, mul_div, div_le_div_iff₀ ] <;> try positivity;
    norm_num [ pow_succ' ] ; nlinarith [ show ( x : ℝ ) ≥ 3 by norm_cast, show ( 2 : ℝ ) ^ x * t ≥ 0 by positivity ]


lemma exp_poly_le_dyadic_eventually24 :
    ∀ U : ℕ, 2000 ≤ U →
      Real.exp 1 * (U : ℝ) ^ 2 ≤ (2 : ℝ) ^ (U / 24) := by
  intro U hU
  by_cases hU_le_2048 : U ≤ 2048
  · have h := Real.exp_one_lt_d9.le
    exact le_trans (mul_le_mul_of_nonneg_right h (sq_nonneg _)) (by interval_cases U <;> norm_num)
  · induction' U using Nat.strong_induction_on with U ih
    by_cases hU_le_2072 : U ≤ 2072
    · have h := Real.exp_one_lt_d9.le
      norm_num1 at *
      interval_cases U <;> norm_num at * <;> linarith
    · have h_ind : Real.exp 1 * (U - 24 : ℝ) ^ 2 ≤ 2 ^ ((U - 24) / 24) := by
        convert ih (U - 24) (Nat.sub_lt (by linarith) (by linarith))
          (Nat.le_sub_of_add_le (by linarith)) (by omega) using 1
        rw [Nat.cast_sub (by linarith)]
        push_cast
        ring
      have h_ineq : 2 * (U - 24 : ℝ) ^ 2 ≥ U ^ 2 := by
        nlinarith only [show (U : ℝ) ≥ 2073 by norm_cast; linarith]
      rw [show U / 24 = (U - 24) / 24 + 1 by omega]
      norm_num [pow_add]
      nlinarith [Real.exp_pos 1]

lemma dyadic_upper_endpoint_large (U : ℕ) (hU : 2000 ≤ U) :
      (2 : ℝ) ^ ((U / 2).choose 2 - 1) /
          ((U / 2).factorial : ℝ) *
        (Real.exp 1 * (U : ℝ) ^ 2 / (2 : ℝ) ^ (U / 3)) ^ (U / 2 - 3) ≤ 1 := by
  -- Use the inequality $eU^2/2^{U/3} \le 2^{U/24-U/3}$ to bound $T$.
  have hT_bound : (Real.exp 1 * U ^ 2 / 2 ^ (U / 3)) ^ ((U / 2 - 3) : ℕ) ≤ (1 / 2 ^ ((U / 3 - U / 24) : ℕ)) ^ ((U / 2 - 3) : ℕ) := by
    have hT_bound : Real.exp 1 * (U : ℝ) ^ 2 ≤ (2 : ℝ) ^ (U / 24) := by
      convert exp_poly_le_dyadic_eventually24 U hU using 1;
    refine' pow_le_pow_left₀ ( by positivity ) _ _;
    convert div_le_div_of_nonneg_right hT_bound ( by positivity : ( 0 : ℝ ) ≤ 2 ^ ( U / 3 ) ) using 1 ; rw [ div_eq_div_iff ] <;> first | positivity | ring;
    rw [ ← pow_add, Nat.add_sub_of_le ( by omega ) ];
  refine le_trans ( mul_le_mul_of_nonneg_left hT_bound ( by positivity ) ) ?_;
  rw [ div_pow, mul_div, div_le_one ];
  · rw [ ← pow_mul, mul_comm ];
    refine' le_trans ( mul_le_mul_of_nonneg_left ( div_le_self ( by positivity ) ( mod_cast Nat.factorial_pos _ ) ) ( by positivity ) ) _;
    norm_num [ Nat.choose_two_right ];
    gcongr <;> norm_num;
    rw [ Nat.div_le_iff_le_mul_add_pred ] <;> norm_num;
    zify;
    rw [ Nat.cast_sub, Nat.cast_sub, Nat.cast_sub ] <;> push_cast <;> repeat omega;
    nlinarith [ Nat.div_mul_le_self U 2, Nat.div_mul_le_self U 3, Nat.div_mul_le_self U 24, Nat.div_add_mod U 2, Nat.mod_lt U two_pos, Nat.div_add_mod U 3, Nat.mod_lt U three_pos, Nat.div_add_mod U 24, Nat.mod_lt U ( by decide : 0 < 24 ) ];
  · positivity

lemma dyadic_upper_endpoint_uniform :
    ∃ K : ℝ, 0 < K ∧ ∀ U : ℕ,
      (2 : ℝ) ^ ((U / 2).choose 2 - 1) /
          ((U / 2).factorial : ℝ) *
        (Real.exp 1 * (U : ℝ) ^ 2 / (2 : ℝ) ^ (U / 3)) ^ (U / 2 - 3) ≤ K := by
  -- Let's choose any $K > 0$ and show that the inequality holds for all $U$.
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ U : ℕ, U < 2000 → (2 : ℝ) ^ ((U / 2).choose 2 - 1) / ((U / 2).factorial : ℝ) * (Real.exp 1 * (U : ℝ) ^ 2 / (2 : ℝ) ^ (U / 3)) ^ (U / 2 - 3) ≤ K := by
    have h_finite : Set.Finite (Set.image (fun U : ℕ => (2 : ℝ) ^ ((U / 2).choose 2 - 1) / ((U / 2).factorial : ℝ) * (Real.exp 1 * (U : ℝ) ^ 2 / (2 : ℝ) ^ (U / 3)) ^ (U / 2 - 3)) (Set.Iio 2000)) := by
      exact Set.Finite.image _ <| Set.finite_Iio _;
    exact ⟨ h_finite.bddAbove.choose, fun U hU => h_finite.bddAbove.choose_spec <| Set.mem_image_of_mem _ hU ⟩;
  refine' ⟨ Max.max K 1, by positivity, fun U => _ ⟩ ; cases lt_or_ge U 2000 <;> simp_all +decide;
  exact Or.inr ( dyadic_upper_endpoint_large U ‹_› )



lemma endpointIncrement_le_majorant (x : ℕ) (hx : 3 ≤ x) :
    endpointIncrement x ≤ (2 : ℝ) ^ (x.choose 2 - 1) := by
  unfold endpointIncrement endpointRewardNat
  rw [if_pos hx]
  push_cast
  exact sub_le_self ((2 : ℝ) ^ (x.choose 2 - 1)) (by positivity)

lemma cell_size_dyadic_lower (U m : ℕ) (hm : (2 : ℕ)^U ≤ m^3) :
    (2 : ℕ)^(U/3) ≤ m := by
  by_contra h
  have hlt : m < 2^(U/3) := Nat.lt_of_not_ge h
  have hc := Nat.pow_lt_pow_left hlt (by omega : 3 ≠ 0)
  rw [← pow_mul] at hc
  have he : U / 3 * 3 ≤ U := Nat.div_mul_le_self U 3
  have hp : (2 : ℕ)^(U/3*3) ≤ 2^U := Nat.pow_le_pow_right (by omega) he
  exact (Nat.not_lt_of_ge hm) (hc.trans_le hp)

lemma theta_cap_uniform :
    ∃ B : ℝ, 0 < B ∧ ∀ U : ℕ,
      Real.exp 1 * (U : ℝ)^2 / (2 : ℝ)^(U/3) ≤ B := by
  let f : ℕ → ℝ := fun U => Real.exp 1 * (U : ℝ)^2 / (2 : ℝ)^(U/3)
  let S := Set.image f (Set.Iio 2000)
  have hfin : S.Finite := Set.Finite.image _ (Set.finite_Iio 2000)
  let B := max 1 hfin.bddAbove.choose
  refine ⟨B, by positivity, ?_⟩
  intro U
  by_cases hU : U < 2000
  · exact le_trans (hfin.bddAbove.choose_spec (Set.mem_image_of_mem f hU)) (le_max_right _ _)
  · have he := exp_poly_le_dyadic_eventually24 U (by omega)
    have hle : f U ≤ 1 := by
      dsimp [f]
      calc
        _ ≤ (2 : ℝ)^(U/24) / (2 : ℝ)^(U/3) := div_le_div_of_nonneg_right he (by positivity)
        _ ≤ 1 := by
          rw [div_le_one (by positivity)]
          exact pow_le_pow_right₀ (by norm_num) (by omega)
    exact hle.trans (le_max_left _ _)

/-- Finite uniform analytic endpoint theorem.

The natural inequality `2^U ≤ m^3` is an exact finite replacement for
`U ≤ 3 log_2 m` when `m > 0`.  The witness `C` is quantified before every
cell parameter, so it is genuinely absolute. -/
theorem existsAbsoluteFiniteEndpointConstant :
    ∃ C : ℝ, 0 < C ∧
      ∀ (U m R : ℕ) (theta : ℝ),
        0 < m →
        R = U / 2 →
        0 ≤ theta →
        theta ≤ Real.exp 1 * (U : ℝ) ^ 2 / (m : ℝ) →
        (2 : ℕ) ^ U ≤ m ^ 3 →
        endpointLambda R theta ≤ C * theta ^ 3 ∧
          endpointQ R theta ≤ C * theta ^ 2 := by
  obtain ⟨K, hKpos, hK⟩ := dyadic_upper_endpoint_uniform
  obtain ⟨B, hBpos, hB⟩ := theta_cap_uniform
  let A : ℝ := 10 * (1 + K)
  let C : ℝ := 1 + A + A * B
  refine ⟨C, by dsimp [C, A]; positivity, ?_⟩
  intro U m R theta hm hR htheta htheta_m hpow
  have hm_lower_nat := cell_size_dyadic_lower U m hpow
  have hm_lower : (2 : ℝ) ^ (U / 3) ≤ (m : ℝ) := by exact_mod_cast hm_lower_nat
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hT : theta ≤ Real.exp 1 * (U : ℝ)^2 / (2 : ℝ)^(U/3) := by
    exact htheta_m.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hm_lower)
  have hthetaB : theta ≤ B := hT.trans (hB U)
  have hlambda : endpointLambda R theta ≤ A * theta^3 := by
    rw [hR]
    by_cases hsmall : U / 2 < 3
    · unfold endpointLambda
      have hzero : Finset.Icc 3 (U/2) = ∅ := by ext x; simp; omega
      simp [hzero]
      dsimp [A]
      positivity
    · unfold endpointLambda
      calc
        _ ≤ ∑ x ∈ Finset.Icc 3 (U / 2),
            (2 : ℝ)^(x.choose 2 - 1) * theta^x / (x.factorial : ℝ) := by
          apply Finset.sum_le_sum
          intro x hx
          rw [Finset.mem_Icc] at hx
          have hi := endpointIncrement_le_majorant x hx.1
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hi (pow_nonneg htheta x)) (by positivity)
        _ ≤ 10 * ((2 : ℝ)^(Nat.choose 3 2 - 1) * theta^3 /
              (Nat.factorial 3 : ℝ) +
            (2 : ℝ)^((U/2).choose 2 - 1) * theta^(U/2) /
              ((U/2).factorial : ℝ)) := dyadic_logconvex_sum_bound (U/2) theta htheta
        _ ≤ A * theta^3 := by
          have hpow_split : theta^(U/2) = theta^3 * theta^(U/2-3) := by
            rw [← pow_add, Nat.add_sub_of_le (by omega)]
          have htail :
              (2 : ℝ)^((U/2).choose 2 - 1) / ((U/2).factorial : ℝ) *
                theta^(U/2-3) ≤ K := by
            refine le_trans ?_ (hK U)
            gcongr
          have htail' :
              (2 : ℝ)^((U/2).choose 2 - 1) * theta^(U/2) /
                ((U/2).factorial : ℝ) ≤ K * theta^3 := by
            rw [hpow_split]
            calc
              _ = ((2 : ℝ)^((U/2).choose 2 - 1) / ((U/2).factorial : ℝ) *
                    theta^(U/2-3)) * theta^3 := by ring
              _ ≤ K * theta^3 := mul_le_mul_of_nonneg_right htail (pow_nonneg htheta 3)
          norm_num [A, Nat.choose]
          nlinarith [htail', hKpos, pow_nonneg htheta 3]

  constructor
  · have hA : 0 ≤ A := by dsimp [A]; positivity
    have hAC : A ≤ C := by dsimp [C]; nlinarith [hBpos]
    exact hlambda.trans (mul_le_mul_of_nonneg_right hAC (pow_nonneg htheta 3))
  · unfold endpointQ
    have hc : 1 / 2 + A * theta ≤ C := by
      have hab : A * theta ≤ A * B := mul_le_mul_of_nonneg_left hthetaB (by dsimp [A]; positivity)
      dsimp [C]
      linarith [show 0 ≤ A by dsimp [A]; positivity]
    calc
      theta^2 / 2 + endpointLambda R theta ≤ theta^2 / 2 + A * theta^3 := add_le_add_right hlambda _
      _ = (1/2 + A * theta) * theta^2 := by ring
      _ ≤ C * theta^2 := mul_le_mul_of_nonneg_right hc (sq_nonneg theta)

#print axioms existsAbsoluteFiniteEndpointConstant

end Erdos625
