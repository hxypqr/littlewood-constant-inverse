import LittlewoodInverse.DirichletKernel
import LittlewoodInverse.BlockBoundaryIntegral

open MeasureTheory
open scoped Interval

namespace LittlewoodInverse

theorem littlewoodNorm_eq_two_half (A : Finset ℤ) :
    littlewoodNorm A = 2 * ∫ x : ℝ in 0..(1 / 2 : ℝ),
      ‖fourierPolynomial A (x : Circle)‖ := by
  let f : ℝ → ℝ := fun x => ‖fourierPolynomial A (x : Circle)‖
  have hf : Continuous f :=
    ((fourierPolynomial_continuous A).comp (AddCircle.continuous_mk' 1)).norm
  have he (x : ℝ) : f (-x) = f x := by
    dsimp only [f]
    rw [show ((-x : ℝ) : Circle) = -(x : Circle) from rfl,
      fourierPolynomial_neg_argument, Complex.norm_conj]
  have hneg := intervalIntegral.integral_comp_neg (f := f) (a := 0) (b := (1 / 2 : ℝ))
  simp only [he, neg_zero] at hneg
  rw [littlewoodNorm_eq_interval A (-(1 / 2 : ℝ))]
  have hb : -(1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
  rw [hb]
  change (∫ x in -(1 / 2 : ℝ)..(1 / 2 : ℝ), f x) = 2 * ∫ x in 0..(1 / 2 : ℝ), f x
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (-(1 / 2 : ℝ)) 0) (hf.intervalIntegrable 0 (1 / 2 : ℝ)), ← hneg]
  ring

theorem intervalPolynomial_norm_le_inv (n : ℕ) {x : ℝ} (hx : 0 < x) (hx' : x ≤ 1 / 2) :
    ‖fourierPolynomial (Finset.Ico (0 : ℤ) n) (x : Circle)‖ ≤ 1 / (2 * x) := by
  have harg : |Real.pi * x| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hx]
    nlinarith [Real.pi_pos]
  have hs := Real.mul_abs_le_abs_sin harg
  have hsin : 2 * x ≤ |Real.sin (Real.pi * x)| := by
    have he : 2 / Real.pi * |Real.pi * x| = 2 * x := by
      rw [abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hx]
      field_simp
    rwa [he] at hs
  apply (le_div_iff₀ (by positivity : 0 < 2 * x)).mpr
  have hm := mul_le_mul_of_nonneg_left hsin
    (norm_nonneg (fourierPolynomial (Finset.Ico (0 : ℤ) n) (x : Circle)))
  rw [intervalPolynomial_norm_mul_sin] at hm
  exact hm.trans (Real.abs_sin_le_one _)

/-- An elementary logarithmic bound for every genuine integer interval. -/
theorem interval_littlewoodNorm_le_log (n : ℕ) (hn : 0 < n) :
    littlewoodNorm (Finset.Ico (0 : ℤ) n) ≤ 1 + Real.log n := by
  let f : ℝ → ℝ := fun x => ‖fourierPolynomial (Finset.Ico (0 : ℤ) n) (x : Circle)‖
  let δ : ℝ := 1 / (2 * (n : ℝ))
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδhalf : δ ≤ (1 / 2 : ℝ) := by
    dsimp [δ]
    apply (div_le_iff₀ (by positivity : 0 < 2 * (n : ℝ))).mpr
    linarith
  have hf : Continuous f :=
    ((fourierPolynomial_continuous _).comp (AddCircle.continuous_mk' 1)).norm
  have hs : (∫ x in 0..δ, f x) ≤ 1 / 2 := by
    have h := intervalIntegral.integral_mono_on hδ.le (hf.intervalIntegrable _ _)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (n : ℝ)) volume 0 δ)
      (fun x _ => show f x ≤ n from by
        simpa [f] using fourierPolynomial_norm_le_card (Finset.Ico (0 : ℤ) n) (x : Circle))
    have he : (∫ _x : ℝ in 0..δ, (n : ℝ)) = 1 / 2 := by
      rw [intervalIntegral.integral_const]
      dsimp [δ]
      field_simp
      ring
    rwa [he] at h
  have hgi : IntervalIntegrable (fun x : ℝ => 1 / (2 * x)) volume δ (1 / 2) := by
    apply intervalIntegral.intervalIntegrable_one_div
    · intro x hx
      rw [Set.uIcc_of_le hδhalf] at hx
      exact mul_ne_zero (by norm_num) (ne_of_gt (hδ.trans_le hx.1))
    · fun_prop
  have hl : (∫ x in δ..(1 / 2 : ℝ), f x) ≤ Real.log n / 2 := by
    have h := intervalIntegral.integral_mono_on hδhalf (hf.intervalIntegrable _ _) hgi
      (fun x hx => intervalPolynomial_norm_le_inv n (hδ.trans_le hx.1) hx.2)
    have he : (∫ x : ℝ in δ..(1 / 2 : ℝ), 1 / (2 * x)) = Real.log n / 2 := by
      have hi (x : ℝ) : 1 / (2 * x) = x⁻¹ / 2 := by simp [div_eq_mul_inv]
      simp_rw [hi]
      rw [intervalIntegral.integral_div, integral_inv_of_pos hδ (by norm_num)]
      congr 2
      dsimp [δ]
      field_simp
    rwa [he] at h
  rw [littlewoodNorm_eq_two_half]
  change 2 * (∫ x in 0..(1 / 2 : ℝ), f x) ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable 0 δ) (hf.intervalIntegrable δ (1 / 2))]
  linarith

end LittlewoodInverse
