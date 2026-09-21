import LittlewoodInverse.SpectralEnergy
import LittlewoodInverse.SidonAlgebra

/-!
# Analytic part of the constant-one Sidon inequality

Moment hypotheses are explicit. In particular, the large-variance result
requires the fourth-moment estimate for the *whole* polynomial `1 + g`;
it is not inferred from the second and fourth moments of `g` alone.
-/

open MeasureTheory

namespace LittlewoodInverse

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
  [CompactSpace α] [BorelSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

private theorem cint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : α → E} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Pointwise Gram positivity underlying the weighted excess estimate. -/
theorem sidon_excess_gram (z : ℂ) (r : ℝ) :
    0 ≤ (‖(1 : ℂ) + z‖ - 1 - z.re) * (r * r) +
      (-2 * z.im ^ 2) * r + 2 * z.im ^ 2 * (1 + ‖z‖) := by
  have hd : 0 < 2 * (1 + ‖z‖) := by positivity
  have he := (div_le_iff₀ hd).1 (complex_pointwise_excess z)
  have hpos := add_nonneg
    (mul_nonneg (sq_nonneg r) (sub_nonneg.mpr he))
    (mul_nonneg (sq_nonneg z.im) (sq_nonneg (r - 2 * (1 + ‖z‖))))
  apply nonneg_of_mul_nonneg_left (b := 2 * (1 + ‖z‖)) _ hd
  nlinarith

/-- Vanishing of the complex second moment makes the real and imaginary
quadratic masses equal. -/
theorem sidon_imaginary_second_moment {g : α → ℂ} (hg : Continuous g) {t : ℝ}
    (hg2 : (∫ x, g x ^ 2 ∂μ) = 0) (ht : (∫ x, ‖g x‖ ^ 2 ∂μ) = t) :
    (∫ x, (g x).im ^ 2 ∂μ) = t / 2 := by
  have hre : (∫ x, (g x ^ 2).re ∂μ) = 0 := by
    have h := integral_re (cint (μ := μ) (f := fun x => g x ^ 2) (by fun_prop))
    simpa only [RCLike.re_eq_complex_re, hg2, Complex.zero_re] using h
  have hpoint : (fun x => 2 * (g x).im ^ 2) =
      (fun x => ‖g x‖ ^ 2 - (g x ^ 2).re) := by
    funext x
    have hnorm := Complex.sq_norm_sub_sq_re (g x)
    simp only [pow_two, Complex.mul_re] at *
    nlinarith
  have hint := congrArg (fun f : α → ℝ => ∫ x, f x ∂μ) hpoint
  rw [integral_const_mul, integral_sub
    (cint (μ := μ) (f := fun x => ‖g x‖ ^ 2) (by fun_prop))
    (cint (μ := μ) (f := fun x => (g x ^ 2).re) (by fun_prop)),
    ht, hre] at hint
  linarith

/-- The second/fourth moment bound controls the third norm moment. -/
theorem sidon_third_moment {g : α → ℂ} (hg : Continuous g) {t : ℝ}
    (ht : (∫ x, ‖g x‖ ^ 2 ∂μ) = t)
    (hfour : (∫ x, ‖g x‖ ^ 4 ∂μ) ≤ 2 * t ^ 2) :
    (∫ x, ‖g x‖ ^ 3 ∂μ) ≤ t * Real.sqrt (2 * t) := by
  have ht0 : 0 ≤ t := ht ▸ integral_nonneg (fun x => sq_nonneg ‖g x‖)
  have hcs := integral_cauchy_schwarz_sq (f := fun x => ‖g x‖) (g := fun x => ‖g x‖ ^ 2)
    (cint (μ := μ) (hg.norm.pow 2))
    (cint (μ := μ) (hg.norm.mul (hg.norm.pow 2))) (cint (μ := μ) ((hg.norm.pow 2).pow 2))
  have hprod : (fun x => ‖g x‖ * ‖g x‖ ^ 2) = (fun x => ‖g x‖ ^ 3) := by
    funext x; ring
  simp only [hprod, ← pow_mul, ht] at hcs
  apply (sq_le_sq₀ (integral_nonneg (fun x => pow_nonneg (norm_nonneg _) _))
    (mul_nonneg ht0 (Real.sqrt_nonneg _))).1
  calc
    (∫ x, ‖g x‖ ^ 3 ∂μ) ^ 2 ≤ t * (∫ x, ‖g x‖ ^ 4 ∂μ) := hcs
    _ ≤ t * (2 * t ^ 2) := mul_le_mul_of_nonneg_left hfour ht0
    _ = (t * Real.sqrt (2 * t)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * t)]
      ring

/-- Actual integrated small-variance estimate (the estimate itself holds
for all nonnegative variances). -/
theorem sidon_small_t_analytic {g : α → ℂ} (hg : Continuous g) {t : ℝ}
    (hg0 : (∫ x, g x ∂μ) = 0)
    (hg2 : (∫ x, g x ^ 2 ∂μ) = 0)
    (ht : (∫ x, ‖g x‖ ^ 2 ∂μ) = t)
    (hfour : (∫ x, ‖g x‖ ^ 4 ∂μ) ≤ 2 * t ^ 2) :
    1 + t / (4 + 8 * Real.sqrt (2 * t)) ≤ ∫ x, ‖(1 : ℂ) + g x‖ ∂μ := by
  have ht0 : 0 ≤ t := ht ▸ integral_nonneg (fun x => sq_nonneg ‖g x‖)
  have hRe : (∫ x, (g x).re ∂μ) = 0 := by
    have h := integral_re (cint (μ := μ) hg)
    simpa only [RCLike.re_eq_complex_re, hg0, Complex.zero_re] using h
  have hnorm : Continuous (fun x => ‖(1 : ℂ) + g x‖) := continuous_const.add hg |>.norm
  have hex : Continuous (fun x => ‖(1 : ℂ) + g x‖ - 1 - (g x).re) := by fun_prop
  have hexint : (∫ x, ‖(1 : ℂ) + g x‖ - 1 - (g x).re ∂μ) =
      (∫ x, ‖(1 : ℂ) + g x‖ ∂μ) - 1 := by
    rw [integral_sub
      (cint (μ := μ) (f := fun x => ‖(1 : ℂ) + g x‖ - 1) (by fun_prop))
      (cint (μ := μ) (f := fun x => (g x).re) (by fun_prop)),
      integral_sub (cint hnorm) (integrable_const _), hRe]
    simp
  have hex0 : 0 ≤ (∫ x, ‖(1 : ℂ) + g x‖ ∂μ) - 1 := by
    rw [← hexint]
    apply integral_nonneg
    intro x
    change 0 ≤ ‖(1 : ℂ) + g x‖ - 1 - (g x).re
    have h := Complex.re_le_norm ((1 : ℂ) + g x)
    simp only [Complex.add_re, Complex.one_re] at h
    linarith
  have him := sidon_imaginary_second_moment hg hg2 ht
  have hthird := sidon_third_moment hg ht hfour
  have hmix : (∫ x, (g x).im ^ 2 * ‖g x‖ ∂μ) ≤ t * Real.sqrt (2 * t) := by
    apply le_trans (integral_mono (cint (μ := μ) (((Complex.continuous_im.comp hg).pow 2).mul hg.norm))
      (cint (μ := μ) (hg.norm.pow 3)) ?_) hthird
    intro x
    change (g x).im ^ 2 * ‖g x‖ ≤ ‖g x‖ ^ 3
    have hnormsq := Complex.sq_norm_sub_sq_re (g x)
    have hmul := mul_le_mul_of_nonneg_right
      (show (g x).im ^ 2 ≤ ‖g x‖ ^ 2 by nlinarith [sq_nonneg (g x).re])
      (norm_nonneg (g x))
    nlinarith
  have hcint : (∫ x, 2 * (g x).im ^ 2 * (1 + ‖g x‖) ∂μ) =
      t + 2 * (∫ x, (g x).im ^ 2 * ‖g x‖ ∂μ) := by
    have hfun : (fun x => 2 * (g x).im ^ 2 * (1 + ‖g x‖)) =
        (fun x => 2 * (g x).im ^ 2 + 2 * ((g x).im ^ 2 * ‖g x‖)) := by
      funext x; ring
    rw [hfun, integral_add
      (cint (μ := μ) (f := fun x => 2 * (g x).im ^ 2) (by fun_prop))
      (cint (μ := μ) (f := fun x => 2 * ((g x).im ^ 2 * ‖g x‖)) (by fun_prop)),
      integral_const_mul, integral_const_mul, him]
    ring
  have hgram := integral_gram_sq_le
    (a := fun x => ‖(1 : ℂ) + g x‖ - 1 - (g x).re)
    (b := fun x => (g x).im ^ 2)
    (c := fun x => 2 * (g x).im ^ 2 * (1 + ‖g x‖))
    (cint (μ := μ) hex) (cint (μ := μ) ((Complex.continuous_im.comp hg).pow 2))
    (cint (μ := μ) (by fun_prop : Continuous (fun x => 2 * (g x).im ^ 2 * (1 + ‖g x‖))))
    (fun x r => sidon_excess_gram (g x) r)
  rw [him, hexint, hcint] at hgram
  have hupper := mul_le_mul_of_nonneg_left
    (show t + 2 * (∫ x, (g x).im ^ 2 * ‖g x‖ ∂μ) ≤
      t + 2 * (t * Real.sqrt (2 * t)) by linarith) hex0
  have hbound := hgram.trans hupper
  rcases ht0.eq_or_lt with hz | hp
  · rw [← hz]
    simp only [zero_div, add_zero]
    linarith
  · have hcancel : t ≤ ((∫ x, ‖(1 : ℂ) + g x‖ ∂μ) - 1) *
        (4 + 8 * Real.sqrt (2 * t)) := by
      apply (mul_le_mul_iff_right₀ hp).1
      nlinarith [hbound]
    have hd : 0 < 4 + 8 * Real.sqrt (2 * t) := by positivity
    have hdiv := (div_le_iff₀ hd).2 hcancel
    linarith

/-- Actual `L¹`–`L²`–`L⁴` interpolation in the form used for the large
variance range. Both Cauchy–Schwarz steps are proved above from integrals. -/
theorem integral_L1_sq_ge_half_L2 {w : α → ℝ} (hw : Continuous w)
    (hw0 : ∀ x, 0 ≤ w x)
    (hfour : (∫ x, w x ^ 4 ∂μ) ≤ 2 * (∫ x, w x ^ 2 ∂μ) ^ 2) :
    (∫ x, w x ^ 2 ∂μ) / 2 ≤ (∫ x, w x ∂μ) ^ 2 := by
  have hmul2 : (fun x => w x * w x) = (fun x => w x ^ 2) := by funext x; ring
  have hmul3 : (fun x => w x * w x ^ 2) = (fun x => w x ^ 3) := by funext x; ring
  have hwcs := integral_weighted_cauchy_schwarz_sq (w := w) (g := w) hw0
    (cint (μ := μ) hw) (cint (μ := μ) (hw.mul hw))
    (cint (μ := μ) (hw.mul (hw.pow 2)))
  rw [hmul2, hmul3] at hwcs
  have hcs := integral_cauchy_schwarz_sq (f := w) (g := fun x => w x ^ 2)
    (cint (μ := μ) (hw.pow 2)) (cint (μ := μ) (hw.mul (hw.pow 2)))
    (cint (μ := μ) ((hw.pow 2).pow 2))
  simp only [hmul3, ← pow_mul] at hcs
  have hm2 : 0 ≤ (∫ x, w x ^ 2 ∂μ) := integral_nonneg (fun x => sq_nonneg _)
  have hsq := pow_le_pow_left₀ (sq_nonneg _) hwcs 2
  have hlast := hcs.trans (mul_le_mul_of_nonneg_left hfour hm2)
  have hmul := mul_le_mul_of_nonneg_left hlast (sq_nonneg (∫ x, w x ∂μ))
  have hfinal : (∫ x, w x ^ 2 ∂μ) ^ 4 ≤
      (2 * (∫ x, w x ∂μ) ^ 2) * (∫ x, w x ^ 2 ∂μ) ^ 3 := by
    nlinarith [hsq, hmul]
  rcases hm2.eq_or_lt with hz | hp
  · rw [← hz]
    simpa only [zero_div] using sq_nonneg (∫ x, w x ∂μ)
  · have hcancel : (∫ x, w x ^ 2 ∂μ) ≤ 2 * (∫ x, w x ∂μ) ^ 2 := by
      apply (mul_le_mul_iff_left₀ (pow_pos hp 3)).1
      nlinarith [hfinal]
    linarith

/-- Centering converts the second norm moment of `g` to that of `1 + g`. -/
theorem sidon_shifted_second_moment {g : α → ℂ} (hg : Continuous g) {t : ℝ}
    (hg0 : (∫ x, g x ∂μ) = 0) (ht : (∫ x, ‖g x‖ ^ 2 ∂μ) = t) :
    (∫ x, ‖(1 : ℂ) + g x‖ ^ 2 ∂μ) = 1 + t := by
  have hre : (∫ x, (g x).re ∂μ) = 0 := by
    have h := integral_re (cint (μ := μ) hg)
    simpa only [RCLike.re_eq_complex_re, hg0, Complex.zero_re] using h
  have hfun : (fun x => ‖(1 : ℂ) + g x‖ ^ 2) =
      (fun x => (1 + 2 * (g x).re) + ‖g x‖ ^ 2) := by
    funext x
    have h1 := Complex.sq_norm_sub_sq_re ((1 : ℂ) + g x)
    have h2 := Complex.sq_norm_sub_sq_re (g x)
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
      zero_add] at h1
    nlinarith
  rw [hfun, integral_add
    (cint (μ := μ) (f := fun x => 1 + 2 * (g x).re) (by fun_prop))
    (cint (μ := μ) (f := fun x => ‖g x‖ ^ 2) (by fun_prop)),
    integral_add (integrable_const 1)
      (cint (μ := μ) (f := fun x => 2 * (g x).re) (by fun_prop)),
    integral_const_mul, hre, ht]
  simp

/-- The analytic and scalar parts of the Sidon twentieth-power estimate.
All moment premises are stated explicitly; the fourth moment of the whole
polynomial is the input normally supplied by Sidon orthogonality. -/
theorem sidon_twentieth_analytic {g : α → ℂ} (hg : Continuous g) {t : ℝ}
    (hg0 : (∫ x, g x ∂μ) = 0)
    (hg2 : (∫ x, g x ^ 2 ∂μ) = 0)
    (ht : (∫ x, ‖g x‖ ^ 2 ∂μ) = t)
    (hfour : (∫ x, ‖g x‖ ^ 4 ∂μ) ≤ 2 * t ^ 2)
    (hwhole : (∫ x, ‖(1 : ℂ) + g x‖ ^ 4 ∂μ) ≤ 2 * (1 + t) ^ 2) :
    1 + t ≤ (∫ x, ‖(1 : ℂ) + g x‖ ∂μ) ^ 20 := by
  have ht0 : 0 ≤ t := ht ▸ integral_nonneg (fun x => sq_nonneg ‖g x‖)
  rcases le_total t 2 with hsmall | hlarge
  · exact sidon_small_variance ht0 hsmall (sidon_small_t_analytic hg hg0 hg2 ht hfour)
  · have htwo := sidon_shifted_second_moment hg hg0 ht
    have hi := integral_L1_sq_ge_half_L2 (μ := μ)
      (w := fun x => ‖(1 : ℂ) + g x‖) (by fun_prop)
      (fun x => norm_nonneg _) (by simpa only [htwo] using hwhole)
    rw [htwo] at hi
    exact sidon_large_variance hlarge hi

end LittlewoodInverse
