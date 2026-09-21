import LittlewoodInverse.QuantitativeAsymptotic
import LittlewoodInverse.NumericalConstant

namespace LittlewoodInverse

/-- Theorem 1.1 of the manuscript: the advertised decimal and the full
uniform asymptotic lower bound, for actual finite sets of integers. -/
theorem quantitative_theorem : QuantitativeTheorem :=
  ⟨NumericalConstant.littlewoodCoefficient_gt_decimal, littlewood_asymptotic⟩

end LittlewoodInverse
