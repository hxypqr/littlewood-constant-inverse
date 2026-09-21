import LittlewoodInverse.Basic
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

open scoped BigOperators Interval
open MeasureTheory AddCircle Complex

namespace LittlewoodInverse

noncomputable def periodicSine : C(Circle, ℂ) :=
  ⟨AddCircle.liftIco 1 0 (fun x : ℝ => (Real.sin (Real.pi * x) : ℂ)),
    AddCircle.liftIco_zero_continuous (by simp) (by fun_prop)⟩

theorem sine_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => (Real.sin (Real.pi * y) : ℂ))
      ((Real.pi : ℂ) * (Real.cos (Real.pi * x) : ℂ)) x := by
  simpa only [Function.comp_def, mul_one, Complex.ofReal_mul, mul_comm] using
    (((Real.hasDerivAt_sin (Real.pi * x)).comp x
      ((hasDerivAt_id x).const_mul Real.pi)).ofReal_comp)

theorem cosine_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => (Real.cos (Real.pi * y) : ℂ))
      (-(Real.pi : ℂ) * (Real.sin (Real.pi * x) : ℂ)) x := by
  simpa only [Function.comp_def, mul_one, Complex.ofReal_mul, Complex.ofReal_neg,
    neg_mul, mul_neg, mul_comm] using
    (((Real.hasDerivAt_cos (Real.pi * x)).comp x
      ((hasDerivAt_id x).const_mul Real.pi)).ofReal_comp)

theorem fourierCoeffOn_sine (n : ℤ) :
    fourierCoeffOn (show (0 : ℝ) < 1 by norm_num)
      (fun x : ℝ => (Real.sin (Real.pi * x) : ℂ)) n =
      -2 / ((Real.pi : ℂ) * (4 * (n : ℂ) ^ 2 - 1)) := by
  by_cases hn : n = 0
  · subst n
    rw [fourierCoeffOn_eq_integral]
    simp only [sub_zero, one_div_one, one_smul, neg_zero, fourier_zero, one_mul,
      smul_eq_mul]
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := 1)
      (fun x _ => (cosine_hasDerivAt x).div_const (-(Real.pi : ℂ)))
      (show IntervalIntegrable (fun x : ℝ => -(Real.pi : ℂ) *
        (Real.sin (Real.pi * x) : ℂ) / -(Real.pi : ℂ))
        volume 0 1 from (by fun_prop : Continuous _).intervalIntegrable _ _)
    have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    simp only [neg_mul, neg_div_neg_eq, mul_div_cancel_left₀ _ hp] at hi
    convert hi using 1
    simp
    field_simp
    ring
  · have hs := fourierCoeffOn_of_hasDerivAt (show (0 : ℝ) < 1 by norm_num) hn
      (fun x _ => sine_hasDerivAt x)
      (show IntervalIntegrable
        (fun x : ℝ => (Real.pi : ℂ) * (Real.cos (Real.pi * x) : ℂ)) volume 0 1
        from (by fun_prop : Continuous _).intervalIntegrable _ _)
    have hc := fourierCoeffOn_of_hasDerivAt (show (0 : ℝ) < 1 by norm_num) hn
      (fun x _ => cosine_hasDerivAt x)
      (show IntervalIntegrable
        (fun x : ℝ => -(Real.pi : ℂ) * (Real.sin (Real.pi * x) : ℂ)) volume 0 1
        from (by fun_prop : Continuous _).intervalIntegrable _ _)
    simp only [mul_zero, Real.sin_zero, Real.cos_zero, mul_one, Real.sin_pi,
      Real.cos_pi, ofReal_zero, ofReal_one, ofReal_neg, sub_self,
      sub_zero, one_mul, zero_sub,
      fourierCoeffOn.const_mul] at hs hc
    simp only [AddCircle.coe_zero, fourier_eval_zero, one_mul] at hc
    have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hnC : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
    have hdenR : 4 * (n : ℝ) ^ 2 - 1 ≠ 0 := by
      have hn1 : 1 ≤ |n| := Int.one_le_abs hn
      have hn1R : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast hn1
      nlinarith [sq_abs (n : ℝ)]
    have hden : 4 * (n : ℂ) ^ 2 - 1 ≠ 0 := by exact_mod_cast hdenR
    field_simp [hp, hnC, Complex.I_ne_zero] at hs hc
    apply (eq_div_iff (mul_ne_zero hp hden)).mpr
    linear_combination (norm := ring_nf) -hs * (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) - hc
    simp [Complex.I_sq]

theorem fourierCoeff_periodicSine (n : ℤ) :
    fourierCoeff periodicSine n =
      -2 / ((Real.pi : ℂ) * (4 * (n : ℂ) ^ 2 - 1)) := by
  change fourierCoeff (AddCircle.liftIco 1 0 _) n = _
  rw [fourierCoeff_liftIco_eq]
  simpa only [zero_add] using fourierCoeffOn_sine n

noncomputable def sineWeight (k : ℕ) : ℝ := 1 / (4 * (k + 1 : ℝ) ^ 2 - 1)

theorem sineWeight_nonneg (k : ℕ) : 0 ≤ sineWeight k := by
  unfold sineWeight
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  apply one_div_nonneg.mpr
  nlinarith

theorem sineWeight_telescope (k : ℕ) :
    sineWeight k = (1 / (2 * (k : ℝ) + 1) - 1 / (2 * (k : ℝ) + 3)) / 2 := by
  unfold sineWeight
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have h1 : 2 * (k : ℝ) + 1 ≠ 0 := by positivity
  have h3 : 2 * (k : ℝ) + 3 ≠ 0 := by positivity
  have hd : 4 * (k + 1 : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  field_simp
  ring

theorem sum_sineWeight (h N : ℕ) :
    (∑ k ∈ Finset.range N, sineWeight (k + h)) =
      (1 / (2 * (h : ℝ) + 1) - 1 / (2 * (h + N : ℝ) + 1)) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, sineWeight_telescope]
      push_cast
      ring_nf

theorem hasSum_sineWeight_tail (h : ℕ) :
    HasSum (fun k => sineWeight (k + h)) (1 / (2 * (2 * (h : ℝ) + 1))) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun k => sineWeight_nonneg _) _).mpr
  simp only [sum_sineWeight]
  have ht : Filter.Tendsto (fun N : ℕ => (2 : ℝ) * (h + N : ℝ) + 1)
      Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono (f := fun N : ℕ => (N : ℝ))
    · intro N
      have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
      have hh : 0 ≤ (h : ℝ) := Nat.cast_nonneg _
      linarith
    · exact tendsto_natCast_atTop_atTop (R := ℝ)
  have hz := (tendsto_inv_atTop_zero.comp ht)
  have hc : Filter.Tendsto (fun _ : ℕ => 1 / (2 * (h : ℝ) + 1)) Filter.atTop
      (nhds (1 / (2 * (h : ℝ) + 1))) := tendsto_const_nhds
  simpa only [one_div, Function.comp_def, sub_zero, div_eq_mul_inv, mul_inv_rev, one_mul] using
    (hc.sub hz).div_const 2

theorem summable_fourierCoeff_periodicSine : Summable (fourierCoeff periodicSine) := by
  have hw : Summable (fun k : ℕ => (sineWeight k : ℂ)) := by
    exact Complex.summable_ofReal.mpr (by simpa using (hasSum_sineWeight_tail 0).summable)
  have hpos : Summable (fun k : ℕ => fourierCoeff periodicSine ((k + 1 : ℕ) : ℤ)) := by
    apply (hw.mul_left (-2 / (Real.pi : ℂ))).congr
    intro k
    simp only [fourierCoeff_periodicSine, sineWeight, ofReal_div, ofReal_one,
      ofReal_sub, ofReal_mul, ofReal_ofNat, ofReal_pow, ofReal_add, ofReal_natCast,
      Nat.cast_add, Nat.cast_one]
    push_cast
    rw [div_mul_div_comm]
    congr 2
    ring
  apply Summable.of_nat_of_neg_add_one
  · exact (summable_nat_add_iff 1).mp hpos
  · apply hpos.congr
    intro k
    simp only [fourierCoeff_periodicSine, Int.cast_neg, Int.cast_add, Int.cast_natCast,
      Int.cast_one, Nat.cast_add, Nat.cast_one, neg_sq]

theorem fourier_real_part (n : ℤ) (x : ℝ) :
    (fourier n (x : Circle)).re = Real.cos (2 * Real.pi * (n : ℝ) * x) := by
  simp [Complex.exp_re, Complex.mul_re, Complex.mul_im]

theorem sine_fourier_term_real (n : ℤ) (x : ℝ) :
    (fourierCoeff periodicSine n • fourier n (x : Circle)).re =
      -2 / (Real.pi * (4 * (n : ℝ) ^ 2 - 1)) *
        Real.cos (2 * Real.pi * (n : ℝ) * x) := by
  have hc : fourierCoeff periodicSine n =
      ((-2 / (Real.pi * (4 * (n : ℝ) ^ 2 - 1)) : ℝ) : ℂ) := by
    rw [fourierCoeff_periodicSine]
    push_cast
    rfl
  rw [hc, smul_eq_mul, Complex.re_ofReal_mul, fourier_real_part]

/-- The cosine expansion of sine on its nonnegative half-wave, obtained
from Fourier reconstruction and the internally computed coefficients. -/
theorem hasSum_sine_cosine {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    HasSum (fun k : ℕ => -4 / Real.pi * sineWeight k *
      Real.cos (2 * Real.pi * (k + 1 : ℝ) * x))
      (Real.sin (Real.pi * x) - 2 / Real.pi) := by
  have hs := (has_pointwise_sum_fourier_series_of_summable
    summable_fourierCoeff_periodicSine (x : Circle)).nat_add_neg
  have hf : (periodicSine (x : Circle)).re = Real.sin (Real.pi * x) := by
    change (AddCircle.liftIco 1 0 (fun y : ℝ => (Real.sin (Real.pi * y) : ℂ))
      (x : Circle)).re = _
    rw [AddCircle.liftIco_zero_coe_apply hx]
    rfl
  have ht := (hasSum_nat_add_iff' 1).mpr (Complex.hasSum_re hs)
  simp only [Finset.sum_range_one, Nat.cast_zero, neg_zero, Complex.add_re,
    sine_fourier_term_real, hf] at ht
  norm_num at ht
  have hterm (k : ℕ) :
      -2 / (Real.pi * (4 * (k + 1 : ℝ) ^ 2 - 1)) *
        Real.cos (2 * Real.pi * (k + 1 : ℝ) * x) +
      -2 / (Real.pi * (4 * (-1 + -(k : ℝ)) ^ 2 - 1)) *
        Real.cos (2 * Real.pi * (-1 + -(k : ℝ)) * x) =
      -4 / Real.pi * sineWeight k * Real.cos (2 * Real.pi * (k + 1 : ℝ) * x) := by
    rw [show -1 + -(k : ℝ) = -(k + 1) by ring]
    simp only [sineWeight, neg_sq, mul_neg, Real.cos_neg, neg_mul,
      div_eq_mul_inv, mul_inv_rev]
    ring
  simp_rw [hterm] at ht
  exact ht

theorem sine_cosine_truncation_error (h : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    |Real.sin (Real.pi * x) - (2 / Real.pi +
      ∑ k ∈ Finset.range h, -4 / Real.pi * sineWeight k *
        Real.cos (2 * Real.pi * (k + 1 : ℝ) * x))| ≤
      2 / (Real.pi * (2 * (h : ℝ) + 1)) := by
  have hs := (hasSum_nat_add_iff' h).mpr (hasSum_sine_cosine hx)
  have hb := (hasSum_sineWeight_tail h).mul_left (4 / Real.pi)
  have hm := hs.norm_le_of_bounded hb (fun k => by
    simp only [Real.norm_eq_abs, abs_mul, abs_div, abs_neg,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
      abs_of_pos Real.pi_pos, abs_of_nonneg (sineWeight_nonneg _)]
    exact mul_le_of_le_one_right
      (mul_nonneg (div_nonneg (by norm_num) Real.pi_pos.le) (sineWeight_nonneg _))
      (Real.abs_cos_le_one _))
  convert hm using 1
  · rw [Real.norm_eq_abs]
    congr 1
    ring
  · field_simp
    ring

end LittlewoodInverse
