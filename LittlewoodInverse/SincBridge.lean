import LittlewoodInverse.SincMoments
import LittlewoodInverse.DirichletKernel

open scoped BigOperators
open MeasureTheory

namespace LittlewoodInverse

/-- Exact Haar-integral and change-of-variable bridge to the rescaled sinc kernel. -/
theorem normalized_interval_moment_eq_scaledSinc (n k : ℕ) (hn : 0 < n) :
    (n : ℝ) * (∫ t, (‖fourierPolynomial (Finset.Ico (0 : ℤ) n) t‖ / n) ^ (k + 2)
      ∂circleMeasure) =
      ∫ x : ℝ, |SincMoments.scaledSincKernel n x| ^ (k + 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let f : Circle → ℝ := fun t => (‖fourierPolynomial (Finset.Ico (0 : ℤ) n) t‖ / n) ^ (k + 2)
  have hind : (fun x : ℝ => |SincMoments.scaledSincKernel n x| ^ (k + 2)) =
      (Set.Icc (-(n : ℝ) / 2) ((n : ℝ) / 2)).indicator
        (fun x => f ((x / n : ℝ) : Circle)) := by
    funext x
    by_cases hx : |x| ≤ (n : ℝ) / 2
    · have hxmem : x ∈ Set.Icc (-(n : ℝ) / 2) ((n : ℝ) / 2) := by
        simpa only [Set.mem_Icc, neg_div] using abs_le.mp hx
      rw [Set.indicator_of_mem hxmem]
      simp only [SincMoments.scaledSincKernel, if_pos hx, f,
        normalized_intervalPolynomial_eq_sinc n hn x hx]
    · have hxmem : x ∉ Set.Icc (-(n : ℝ) / 2) ((n : ℝ) / 2) := by
        simpa only [Set.mem_Icc, neg_div, ← abs_le] using hx
      simp only [Set.indicator_of_notMem hxmem, SincMoments.scaledSincKernel,
        if_neg hx, abs_zero, zero_pow (by omega : k + 2 ≠ 0)]
  rw [hind, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -(n : ℝ) / 2 ≤ (n : ℝ) / 2)]
  have hchange := intervalIntegral.integral_comp_div (fun x : ℝ => f (x : Circle))
    (a := -(n : ℝ) / 2) (b := (n : ℝ) / 2) hnR.ne'
  have ha : -(n : ℝ) / 2 / n = -(1 / 2 : ℝ) := by field_simp
  have hb : (n : ℝ) / 2 / n = (1 / 2 : ℝ) := by field_simp
  rw [ha, hb, smul_eq_mul] at hchange
  rw [hchange]
  congr 1
  have hhaar : (∫ t, f t ∂circleMeasure) = ∫ t : Circle, f t := by
    simp only [circleMeasure, AddCircle.integral_haarAddCircle, inv_one, one_smul]
  rw [hhaar]
  have hp := AddCircle.intervalIntegral_preimage (1 : ℝ) (-(1 / 2 : ℝ)) f
  norm_num at hp
  exact hp.symm

end LittlewoodInverse
