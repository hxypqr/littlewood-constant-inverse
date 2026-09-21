import LittlewoodInverse.OuterAlgebra

open scoped BigOperators

namespace LittlewoodInverse
namespace SharpLogBounds

theorem log_nine_upper : Real.log 9 < (2197224577336219383 / 10^18 : ℝ) := by
  have h : (9 : ℝ) < ∑ j ∈ Finset.range 34,
      (2197224577336219383 / 10^18 : ℝ)^j / (j.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ]
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 9)).mpr
  exact h.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 34)

theorem log_ten_upper : Real.log 10 < (2302585092994045685 / 10^18 : ℝ) := by
  have h : (10 : ℝ) < ∑ j ∈ Finset.range 34,
      (2302585092994045685 / 10^18 : ℝ)^j / (j.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ]
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 10)).mpr
  exact h.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 34)

theorem endpoint_sharp_upper :
    -(9 / 10 : ℝ)^2 - 2 * (9 / 10 : ℝ) + 2 * Real.log 10 -
      (11 / 8 : ℝ) * (4 * (9 / 10 : ℝ)^3 - (9 / 10 : ℝ)^4) <
        (-11121923140 / 10^10 : ℝ) := by
  have h := log_ten_upper
  linarith

theorem coefficient_gt_sharp_decimal (E : ℝ) (hE0 : 0 ≤ E)
    (hE : E ≤ (479084457020255861 / 10^18 : ℝ)) :
    (2459209213577253 / 10^16 : ℝ) <
      (9 / (10 * Real.log 9)) * (1 - Real.sqrt (E / 3)) := by
  have hlog0 : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have hs0 : 0 ≤ Real.sqrt (E / 3) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (E / 3)^2 = E / 3 := Real.sq_sqrt (by positivity)
  have hs : Real.sqrt (E / 3) < (399618341679598027014498 / 10^24 : ℝ) := by
    nlinarith
  have hlog := log_nine_upper
  have hdiv : (2459209213577253 / 10^16 : ℝ) * (10 * Real.log 9) <
      9 * (1 - Real.sqrt (E / 3)) := by nlinarith
  have h := (lt_div_iff₀ (show 0 < 10 * Real.log 9 by positivity)).mpr hdiv
  simpa only [div_mul_eq_mul_div] using h

end SharpLogBounds
end LittlewoodInverse
