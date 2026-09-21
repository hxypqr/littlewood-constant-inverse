import LittlewoodInverse.MomentCertificate
import LittlewoodInverse.SeriesCertificate
import LittlewoodInverse.SharpLogBounds

open scoped BigOperators

namespace LittlewoodInverse
namespace NumericalConstant

open SeriesCertificate

/-- The actual infinite series error satisfies the manuscript's rational
upper enclosure.  Every finite comparison and the infinite tail have
independent Lean proofs. -/
theorem tailError_upper : tailError ≤ (479084457020255861 : ℝ) / 10^18 := by
  have htail := momentSeries_le_finite 156 (a := (9 / 10 : ℝ)) (by norm_num) (by norm_num)
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at htail
  have hfinite :
      (∑ j ∈ Finset.range 156, (9 / 10 : ℝ)^(j + 5) / ((j : ℝ) + 5) * momentCoefficient (j + 5)) ≤
        ∑ j ∈ Finset.range 156, (9 / 10 : ℝ)^(j + 5) / ((j : ℝ) + 5) *
          (MomentCertificate.coefficientBound j : ℝ) := by
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left
      (MomentCertificate.coefficientBound_valid j (Finset.mem_range.mp hj)) (by positivity)
  have hcertificate := MomentCertificate.finite_error_bound
  rw [tailError_eq_momentSeries]
  linarith

/-- The advertised decimal is now proved for the actual constant defined
from the sinc-moment series, without a numerical-bound hypothesis. -/
theorem littlewoodCoefficient_gt_decimal :
    (2459209 / 10000000 : ℝ) < littlewoodCoefficient := by
  unfold littlewoodCoefficient
  apply OuterAlgebra.coefficient_gt_decimal tailError tailError_nonneg
  convert tailError_upper using 1; norm_num

/-- The stronger decimal enclosure recorded in Appendix A. -/
theorem littlewoodCoefficient_gt_sharp_decimal :
    (2459209213577253 / 10^16 : ℝ) < littlewoodCoefficient := by
  exact SharpLogBounds.coefficient_gt_sharp_decimal tailError tailError_nonneg tailError_upper

end NumericalConstant
end LittlewoodInverse
