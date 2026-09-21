import Mathlib

/-!
# Scalar estimates for the constant-one Sidon argument

This file proves the algebraic estimates in manuscript lines 1491–1521.
It does not assume or assert the Fourier moment identities: the norm lower
bounds resulting from those identities are explicit hypotheses below.
-/

namespace LittlewoodInverse

/-- The pointwise excess estimate, valid also on the real axis. -/
theorem complex_pointwise_excess (z : ℂ) :
    z.im ^ 2 / (2 * (1 + ‖z‖)) ≤ ‖(1 : ℂ) + z‖ - 1 - z.re := by
  have hre : 1 + z.re ≤ ‖(1 : ℂ) + z‖ := by
    simpa using Complex.re_le_norm ((1 : ℂ) + z)
  have htriangle : ‖(1 : ℂ) + z‖ ≤ 1 + ‖z‖ := by
    simpa using norm_add_le (1 : ℂ) z
  have hzre : z.re ≤ ‖z‖ := Complex.re_le_norm z
  have hsquare : ‖(1 : ℂ) + z‖ ^ 2 = (1 + z.re) ^ 2 + z.im ^ 2 := by
    have hsq := Complex.sq_norm_sub_sq_re ((1 : ℂ) + z)
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
      zero_add] at hsq
    linarith
  have hden : 0 < 2 * (1 + ‖z‖) := by positivity
  apply (div_le_iff₀ hden).2
  have hprod := mul_nonneg (show 0 ≤ ‖(1 : ℂ) + z‖ - 1 - z.re by linarith)
    (show 0 ≤ 2 * (1 + ‖z‖) - (‖(1 : ℂ) + z‖ + 1 + z.re) by linarith)
  nlinarith

/-- Bernoulli's inequality in the precise normalization needed here. -/
theorem sidon_bernoulli_twenty {t : ℝ} (ht : 0 ≤ t) :
    1 + t ≤ (1 + t / 20) ^ 20 := by
  have h := one_add_mul_le_pow (show -(2 : ℝ) ≤ t / 20 by linarith) 20
  norm_num at h ⊢
  nlinarith [h]

/-- In the small variance range, the rational lower bound is at least
`1 + t / 20`. -/
theorem sidon_small_denominator {t : ℝ} (ht : 0 ≤ t) (htwo : t ≤ 2) :
    1 + t / 20 ≤ 1 + t / (4 + 8 * Real.sqrt (2 * t)) := by
  have hsqrt : Real.sqrt (2 * t) ≤ 2 := by
    apply (Real.sqrt_le_iff).2
    constructor <;> nlinarith
  have hden : 0 < 4 + 8 * Real.sqrt (2 * t) := by positivity
  have hd : 4 + 8 * Real.sqrt (2 * t) ≤ 20 := by linarith
  have hfrac : t / 20 ≤ t / (4 + 8 * Real.sqrt (2 * t)) :=
    div_le_div_of_nonneg_left ht hden hd
  linarith

/-- The small-variance conclusion written with an integer power, so no
real-power convention is needed. -/
theorem sidon_small_variance {t L : ℝ} (ht : 0 ≤ t) (htwo : t ≤ 2)
    (hL : 1 + t / (4 + 8 * Real.sqrt (2 * t)) ≤ L) :
    1 + t ≤ L ^ 20 := by
  have hlower := (sidon_small_denominator ht htwo).trans hL
  exact (sidon_bernoulli_twenty ht).trans
    (pow_le_pow_left₀ (by positivity) hlower 20)

/-- The large-variance interpolation bound implies the same twentieth-power
conclusion. Its interpolation premise is stated as a square inequality. -/
theorem sidon_large_variance {t L : ℝ} (ht : 2 ≤ t)
    (hL : (1 + t) / 2 ≤ L ^ 2) : 1 + t ≤ L ^ 20 := by
  have hu : 3 ≤ 1 + t := by linarith
  have hp : (3 : ℝ) ^ 9 ≤ (1 + t) ^ 9 := pow_le_pow_left₀ (by norm_num) hu 9
  have hbase : 0 ≤ (1 + t) / 2 := by linarith
  have hpow := pow_le_pow_left₀ hbase hL 10
  have h9 : (2 : ℝ) ^ 10 ≤ (1 + t) ^ 9 := by norm_num at hp ⊢; linarith
  have hmul := mul_le_mul_of_nonneg_left h9 (show 0 ≤ 1 + t by linarith)
  have hfirst : 1 + t ≤ ((1 + t) / 2) ^ 10 := by
    rw [div_pow]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2 ^ 10)).2
    convert hmul using 1; ring
  calc
    1 + t ≤ ((1 + t) / 2) ^ 10 := hfirst
    _ ≤ (L ^ 2) ^ 10 := hpow
    _ = L ^ 20 := by rw [← pow_mul]

/-- The manuscript's square-root form of the large-variance premise. -/
theorem sidon_large_variance_sqrt {t L : ℝ} (ht : 2 ≤ t)
    (hL : Real.sqrt ((1 + t) / 2) ≤ L) : 1 + t ≤ L ^ 20 := by
  apply sidon_large_variance ht
  have hbase : 0 ≤ (1 + t) / 2 := by linarith
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg ((1 + t) / 2)) hL 2
  simpa only [Real.sq_sqrt hbase] using hsq

/-- Combining the two scalar lower bounds yields the twentieth-power
estimate for every nonnegative variance. -/
theorem sidon_twentieth_from_scalar_bounds {t L : ℝ} (ht : 0 ≤ t)
    (hsmall : 1 + t / (4 + 8 * Real.sqrt (2 * t)) ≤ L)
    (hlarge : Real.sqrt ((1 + t) / 2) ≤ L) : 1 + t ≤ L ^ 20 := by
  rcases le_total t 2 with h | h
  · exact sidon_small_variance ht h hsmall
  · exact sidon_large_variance_sqrt h hlarge

/-- A coefficient of modulus at most one has twentieth power at most its
square. -/
theorem coefficient_twentieth_le_square {a : ℝ} (ha : 0 ≤ a) (haone : a ≤ 1) :
    a ^ 20 ≤ a ^ 2 := by
  have hp : a ^ 18 ≤ 1 := pow_le_one₀ ha haone
  calc
    a ^ 20 = a ^ 2 * a ^ 18 := by ring
    _ ≤ a ^ 2 * 1 := mul_le_mul_of_nonneg_left hp (sq_nonneg a)
    _ = a ^ 2 := mul_one _

end LittlewoodInverse
