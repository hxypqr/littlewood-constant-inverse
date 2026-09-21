import LittlewoodInverse.PolynomialTransport

open scoped BigOperators

namespace LittlewoodInverse

theorem fourier_nat_pow (n : ℕ) (t : Circle) :
    fourier (n : ℤ) t = fourier 1 t ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [Nat.cast_add, ih, pow_succ]

theorem intervalPolynomial_eq_geom_sum (n : ℕ) (t : Circle) :
    fourierPolynomial (Finset.Ico (0 : ℤ) n) t =
      ∑ k ∈ Finset.range n, fourier 1 t ^ k := by
  unfold fourierPolynomial
  symm
  apply Finset.sum_bij (fun (k : ℕ) _ => (k : ℤ))
  · intro k hk
    simp only [Finset.mem_range] at hk
    exact Finset.mem_Ico.mpr ⟨Int.natCast_nonneg _, by exact_mod_cast hk⟩
  · intro k _ l _ hkl
    exact_mod_cast hkl
  · intro z hz
    obtain ⟨hz0, hzn⟩ := Finset.mem_Ico.mp hz
    refine ⟨z.toNat, Finset.mem_range.mpr ?_, Int.toNat_of_nonneg hz0⟩
    exact_mod_cast (show (z.toNat : ℤ) < n by simpa [Int.toNat_of_nonneg hz0] using hzn)
  · intro k _
    exact (fourier_nat_pow k t).symm

theorem norm_fourier_sub_one (n : ℤ) (x : ℝ) :
    ‖fourier n (x : Circle) - 1‖ = 2 * |Real.sin (Real.pi * n * x)| := by
  rw [fourier_coe_apply]
  simp only [Complex.ofReal_one]
  have harg : (2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ) / (1 : ℂ)) =
      Complex.I * ((2 * (Real.pi * (n : ℝ) * x) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hhalf : 2 * (Real.pi * (n : ℝ) * x) / 2 = Real.pi * n * x := by ring
  rw [hhalf, Real.norm_eq_abs, abs_mul]
  norm_num

/-- The denominator-free Dirichlet-kernel identity, valid also at integer points. -/
theorem intervalPolynomial_norm_mul_sin (n : ℕ) (x : ℝ) :
    ‖fourierPolynomial (Finset.Ico (0 : ℤ) n) (x : Circle)‖ * |Real.sin (Real.pi * x)| =
      |Real.sin (Real.pi * n * x)| := by
  have h := geom_sum_mul (fourier 1 (x : Circle)) n
  rw [← intervalPolynomial_eq_geom_sum, ← fourier_nat_pow] at h
  have hn := congrArg norm h
  rw [norm_mul, norm_fourier_sub_one, norm_fourier_sub_one] at hn
  norm_cast at hn
  simp only [mul_one] at hn
  nlinarith

theorem intervalPolynomial_norm_eq_sin_div (n : ℕ) (x : ℝ)
    (hx : Real.sin (Real.pi * x) ≠ 0) :
    ‖fourierPolynomial (Finset.Ico (0 : ℤ) n) (x : Circle)‖ =
      |Real.sin (Real.pi * n * x) / Real.sin (Real.pi * x)| := by
  rw [abs_div]
  exact (eq_div_iff (abs_ne_zero.mpr hx)).mpr (intervalPolynomial_norm_mul_sin n x)

/-- The rescaled kernel, including its removable value at the origin. -/
theorem normalized_intervalPolynomial_eq_sinc (n : ℕ) (hn : 0 < n) (x : ℝ)
    (hx : |x| ≤ (n : ℝ) / 2) :
    ‖fourierPolynomial (Finset.Ico (0 : ℤ) n) ((x / n : ℝ) : Circle)‖ / n =
      |Real.sinc (Real.pi * x) / Real.sinc (Real.pi * x / n)| := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hx0 : x = 0
  · subst x
    simp [fourierPolynomial, hn.ne']
  have hy : |Real.pi * x / n| ≤ Real.pi / 2 := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hnR]
    apply (div_le_iff₀ hnR).mpr
    nlinarith [Real.pi_pos]
  have hy0 : Real.pi * x / n ≠ 0 := div_ne_zero (mul_ne_zero Real.pi_ne_zero hx0) hnR.ne'
  have hsin : Real.sin (Real.pi * (x / n)) ≠ 0 := by
    rw [← mul_div_assoc]
    intro hs
    apply hy0
    exact (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [(abs_le.mp hy).1, Real.pi_pos])
      (by linarith [(abs_le.mp hy).2, Real.pi_pos])).mp hs
  rw [intervalPolynomial_norm_eq_sin_div n (x / n) hsin]
  have hnum : Real.pi * (n : ℝ) * (x / n) = Real.pi * x := by field_simp
  rw [hnum, ← mul_div_assoc]
  have hquot : Real.sinc (Real.pi * x) / Real.sinc (Real.pi * x / n) =
      (Real.sin (Real.pi * x) / Real.sin (Real.pi * x / n)) / n := by
    rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hx0), Real.sinc_of_ne_zero hy0]
    field_simp
  simp only [hquot, abs_div, abs_of_pos hnR]

end LittlewoodInverse
