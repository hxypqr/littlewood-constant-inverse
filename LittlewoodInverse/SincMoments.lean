import LittlewoodInverse.IntervalEnergy
import LittlewoodInverse.Statements

open scoped BigOperators Topology
open MeasureTheory Filter

namespace LittlewoodInverse
namespace SincMoments

/-- The rescaled Dirichlet quotient, extended by zero outside its fundamental interval. -/
noncomputable def scaledSincKernel (n : ℕ) (x : ℝ) : ℝ :=
  if |x| ≤ (n : ℝ) / 2 then
    Real.sinc (Real.pi * x) / Real.sinc (Real.pi * x / n)
  else 0

theorem abs_sinc_ge_two_div_pi {y : ℝ} (hy : |y| ≤ Real.pi / 2) :
    2 / Real.pi ≤ |Real.sinc y| := by
  by_cases h0 : y = 0
  · simp only [h0, Real.sinc_zero, abs_one]
    exact (div_le_one Real.pi_pos).mpr Real.two_le_pi
  · rw [Real.sinc_of_ne_zero h0, abs_div]
    exact (le_div_iff₀ (abs_pos.mpr h0)).mpr (Real.mul_abs_le_abs_sin hy)

theorem abs_mul_abs_sinc_le (x : ℝ) :
    |x| * |Real.sinc (Real.pi * x)| ≤ 1 / Real.pi := by
  by_cases hx : x = 0
  · simp [hx, le_of_lt Real.pi_pos]
  · rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hx), abs_div,
      abs_mul, abs_of_pos Real.pi_pos]
    have hxp : 0 < |x| := abs_pos.mpr hx
    apply (le_div_iff₀ Real.pi_pos).mpr
    calc
      |x| * (|Real.sin (Real.pi * x)| / (Real.pi * |x|)) * Real.pi =
          |Real.sin (Real.pi * x)| := by field_simp
      _ ≤ 1 := Real.abs_sin_le_one _

theorem scaledSincKernel_bounds (n : ℕ) (hn : 0 < n) (x : ℝ) :
    |scaledSincKernel n x| ≤ 2 ∧ |x| * |scaledSincKernel n x| ≤ 1 := by
  unfold scaledSincKernel
  split_ifs with hx
  · have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hy : |Real.pi * x / n| ≤ Real.pi / 2 := by
      rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hnR]
      apply (div_le_iff₀ hnR).mpr
      nlinarith [Real.pi_pos]
    have hd := abs_sinc_ge_two_div_pi hy
    have hdpos : 0 < |Real.sinc (Real.pi * x / n)| :=
      lt_of_lt_of_le (by positivity) hd
    rw [abs_div]
    constructor
    · apply (div_le_iff₀ hdpos).mpr
      have hp : (1 : ℝ) / 2 ≤ 2 / Real.pi := by
        apply (le_div_iff₀ Real.pi_pos).mpr
        linarith [Real.pi_lt_four]
      nlinarith [Real.abs_sinc_le_one (Real.pi * x)]
    · rw [← mul_div_assoc]
      apply (div_le_iff₀ hdpos).mpr
      have hp : (1 : ℝ) / Real.pi ≤ 2 / Real.pi := by
        exact div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le
      simpa only [one_mul] using (abs_mul_abs_sinc_le x).trans (hp.trans hd)
  · simp

theorem scaledSincKernel_power_bound (n k : ℕ) (hn : 0 < n) (x : ℝ) :
    |scaledSincKernel n x| ^ (k + 2) ≤
      (5 * 2 ^ k : ℝ) * (1 + x ^ 2)⁻¹ := by
  rcases scaledSincKernel_bounds n hn x with ⟨hb, hxb⟩
  have hb0 := abs_nonneg (scaledSincKernel n x)
  have hpow := pow_le_pow_left₀ hb0 hb k
  have hsq : |scaledSincKernel n x| ^ 2 * (1 + x ^ 2) ≤ 5 := by
    have h1 : |scaledSincKernel n x| ^ 2 ≤ 4 := by nlinarith
    have h2 : (|x| * |scaledSincKernel n x|)^2 ≤ 1 := by
      nlinarith [mul_nonneg (abs_nonneg x) hb0]
    rw [mul_pow, sq_abs] at h2
    nlinarith
  apply (le_mul_inv_iff₀ (by positivity : 0 < 1 + x ^ 2)).mpr
  rw [pow_add]
  calc
    |scaledSincKernel n x| ^ k * |scaledSincKernel n x| ^ 2 * (1 + x ^ 2) =
        |scaledSincKernel n x| ^ k * (|scaledSincKernel n x| ^ 2 * (1 + x ^ 2)) := by ring
    _ ≤ (2 : ℝ)^k * 5 := mul_le_mul hpow hsq (by positivity) (by positivity)
    _ = _ := by ring

theorem scaledSincKernel_measurable (n : ℕ) : Measurable (scaledSincKernel n) := by
  unfold scaledSincKernel
  apply Measurable.ite (measurableSet_le measurable_abs measurable_const)
  · exact (Real.continuous_sinc.measurable.comp (measurable_const.mul measurable_id)).div
      (Real.continuous_sinc.measurable.comp
        ((measurable_const.mul measurable_id).div_const _))
  · exact measurable_const

theorem tendsto_scaledSincKernel (x : ℝ) :
    Tendsto (fun n : ℕ => scaledSincKernel n x) atTop (𝓝 (Real.sinc (Real.pi * x))) := by
  have harg : Tendsto (fun n : ℕ => Real.pi * x / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hden : Tendsto (fun n : ℕ => Real.sinc (Real.pi * x / n)) atTop (𝓝 1) := by
    simpa only [Real.sinc_zero, Function.comp_def] using
      Real.continuous_sinc.continuousAt.tendsto.comp harg
  have hquot := (tendsto_const_nhds (x := Real.sinc (Real.pi * x))).div hden
    (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at hquot
  apply hquot.congr'
  have hn : ∀ᶠ n : ℕ in atTop, 2 * |x| ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hn] with n hn
  simp [scaledSincKernel, show |x| ≤ (n : ℝ) / 2 by linarith]

theorem sinc_power_bound (k : ℕ) (x : ℝ) :
    |Real.sinc (Real.pi * x)| ^ (k + 2) ≤
      (5 * 2 ^ k : ℝ) * (1 + x ^ 2)⁻¹ := by
  apply le_of_tendsto ((tendsto_scaledSincKernel x).abs.pow (k + 2))
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact scaledSincKernel_power_bound n k (by omega) x

theorem integrable_sinc_power (k : ℕ) :
    Integrable (fun x : ℝ => |Real.sinc (Real.pi * x)| ^ (k + 2)) := by
  apply (integrable_inv_one_add_sq.const_mul (5 * (2 : ℝ)^k)).mono'
  · exact ((Real.continuous_sinc.comp (continuous_const.mul continuous_id)).abs.pow
      _).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, abs_pow, abs_abs] using sinc_power_bound k x

/-- Actual dominated convergence, with an explicit integrable majorant. -/
theorem tendsto_integral_scaledSincKernel (k : ℕ) :
    Tendsto (fun n : ℕ => ∫ x : ℝ, |scaledSincKernel n x| ^ (k + 2))
      atTop (𝓝 (sincMoment (k + 2 : ℕ))) := by
  have h := tendsto_integral_filter_of_dominated_convergence
      (fun x : ℝ => (5 * 2 ^ k : ℝ) * (1 + x ^ 2)⁻¹)
      (Filter.Eventually.of_forall fun n =>
        ((scaledSincKernel_measurable n).abs.pow_const (k + 2)).aestronglyMeasurable)
      (by
        filter_upwards [eventually_ge_atTop 1] with n hn
        exact Filter.Eventually.of_forall fun x => by
          simpa only [Real.norm_eq_abs, abs_pow, abs_abs] using
            scaledSincKernel_power_bound n k (by omega) x)
      (integrable_inv_one_add_sq.const_mul (5 * (2 : ℝ)^k))
      (Filter.Eventually.of_forall fun x => (tendsto_scaledSincKernel x).abs.pow (k + 2))
  simpa only [sincMoment, Real.rpow_natCast] using h

end SincMoments
end LittlewoodInverse
