import Erdos625.PhaseEstimates
import Mathlib.Tactic

namespace Erdos625

set_option autoImplicit false

/--
Three errors bounded by one sixteenth of the positive `q`-quadratic scale
leave at least one quarter of that quadratic scale in the main term.
-/
theorem quadraticMain_sub_three_errors_ge_quarter
    {a selected centerLog factorialError : ℝ}
    (ha : 0 ≤ a)
    (hselected : |selected| ≤ q / 16 * a ^ 2)
    (hcenterLog : |centerLog| ≤ q / 16 * a ^ 2)
    (hfactorialNonneg : 0 ≤ factorialError)
    (hfactorial : factorialError ≤ q / 16 * a ^ 2) :
    q / 4 * a ^ 2 ≤
      q / 2 * a ^ 2 + a + selected - centerLog - factorialError := by
  have hsel := (abs_le.mp hselected).1
  have hcen := (abs_le.mp hcenterLog).2
  nlinarith [q_pos, ha, hsel, hcen, hfactorialNonneg, hfactorial, sq_nonneg a,
    mul_nonneg q_pos.le (sq_nonneg a)]

end Erdos625

