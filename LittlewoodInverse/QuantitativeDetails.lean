import LittlewoodInverse.UniformMoments
import LittlewoodInverse.LandauAsymptotic

open MeasureTheory

namespace LittlewoodInverse

/-- The strict positivity used in the introduction follows from the
actual continuous sinc integrand, whose value at zero is one. -/
theorem sincMoment_nat_pos (k : ℕ) (hk : 2 ≤ k) : 0 < sincMoment (k : ℝ) := by
  have he : k - 2 + 2 = k := by omega
  have hc : Continuous (fun x : ℝ => |Real.sinc (Real.pi * x)| ^ k) := by fun_prop
  unfold sincMoment
  simp only [Real.rpow_natCast]
  apply integral_pos_of_integrable_nonneg_nonzero hc
    (by simpa only [he] using SincMoments.integrable_sinc_power (k - 2))
    (fun x => pow_nonneg (abs_nonneg _) _) (x := 0)
  simp

theorem momentCoefficient_pos (k : ℕ) (hk : 2 ≤ k) : 0 < momentCoefficient k := by
  unfold momentCoefficient
  split_ifs with h
  · exact sincMoment_nat_pos k hk
  · apply Real.sqrt_pos.mpr
    apply mul_pos
    · apply sincMoment_nat_pos
      have hne : k ≠ 2 := by intro he; subst k; norm_num at h
      omega
    · exact sincMoment_nat_pos _ (by omega)

/-- Explicit pointwise form of the coefficient asymptotic used in
Appendix B; the proof needs no separate Stirling theorem. -/
theorem Landau.b_sq_asymptotic_error (n : ℕ) (hn : 0 < n) :
    |b n ^ 2 - 1 / (Real.pi * n)| ≤ 1 / ((n : ℝ)^2) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlo := b_sq_lower n
  have hhi := b_sq_upper n hn
  rw [abs_of_nonpos (sub_nonpos.mpr hhi)]
  have hdiff : 1 / (Real.pi * (n : ℝ)) - 1 / (Real.pi * ((n : ℝ) + 1)) =
      1 / (Real.pi * n * ((n : ℝ) + 1)) := by field_simp; ring
  have hden : (n : ℝ)^2 ≤ Real.pi * n * ((n : ℝ) + 1) := by
    have hp : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    calc
      _ ≤ (n : ℝ) * ((n : ℝ) + 1) := by nlinarith
      _ ≤ Real.pi * n * ((n : ℝ) + 1) := by
        gcongr
        exact le_mul_of_one_le_left hnR.le hp
  have hfrac := one_div_le_one_div_of_le (by positivity : 0 < (n : ℝ)^2) hden
  linarith

end LittlewoodInverse
