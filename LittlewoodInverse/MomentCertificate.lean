import LittlewoodInverse.CoefficientBounds

open scoped BigOperators
namespace LittlewoodInverse.MomentCertificate
open SincFormula
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem finite_error_bound :
    (55 : ℝ) * (9 / 10)^2 / 108 + (1 / 9 : ℝ) *
      ((2 / 3 : ℝ) * (5 * (9 / 10)^4 / 6 - 2 * (9 / 10)^3 / 3) +
       2 * (∑ j ∈ Finset.range 156, (9 / 10 : ℝ)^(j + 5) / ((j : ℝ) + 5) *
         (coefficientBound j : ℝ)) +
       2 * (9 / 10 : ℝ)^161 / (161 * (1 - (9 / 10 : ℝ)))) ≤
      (479084457020255861 : ℝ) / 10^18 := by
  norm_num [Finset.sum_range_succ, coefficientBound]

end LittlewoodInverse.MomentCertificate
