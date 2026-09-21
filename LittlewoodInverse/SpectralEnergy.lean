import Mathlib
import LittlewoodInverse.Fourier

/-!
# The analytic hereditary-energy estimate

The weighted Cauchy–Schwarz argument of manuscript lines 885–908 is proved
here for complex functions on any measure space. All analytic inequalities
are derived from nonnegative integrals; the required integrability hypotheses
are explicit. No Fourier identity is assumed in the analytic theorem.
-/

open MeasureTheory

namespace LittlewoodInverse

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Integrating a pointwise nonnegative quadratic preserves its
nonpositive discriminant. -/
theorem integral_gram_sq_le {a b c : α → ℝ}
    (ha : Integrable a μ) (hb : Integrable b μ) (hc : Integrable c μ)
    (hpoint : ∀ x t, 0 ≤ a x * (t * t) + (-2 * b x) * t + c x) :
    (∫ x, b x ∂μ) ^ 2 ≤ (∫ x, a x ∂μ) * (∫ x, c x ∂μ) := by
  have hquad : ∀ t : ℝ,
      0 ≤ (∫ x, a x ∂μ) * (t * t) + (-2 * ∫ x, b x ∂μ) * t + ∫ x, c x ∂μ := by
    intro t
    have hnonneg : (0 : ℝ) ≤ ∫ x, a x * (t * t) + (-2 * b x) * t + c x ∂μ :=
      integral_nonneg (fun x => hpoint x t)
    have hab : Integrable (fun x => a x * (t * t) + (-2 * b x) * t) μ :=
      (ha.mul_const (t * t)).add ((hb.const_mul (-2)).mul_const t)
    rw [integral_add hab hc,
      integral_add (ha.mul_const (t * t)) ((hb.const_mul (-2)).mul_const t),
      integral_mul_const, integral_mul_const, integral_const_mul] at hnonneg
    exact hnonneg
  have hd := discrim_le_zero hquad
  simp only [discrim] at hd
  nlinarith

/-- Cauchy–Schwarz for real functions, with integrability stated directly
for the three products that occur. -/
theorem integral_cauchy_schwarz_sq {f g : α → ℝ}
    (hff : Integrable (fun x => f x ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ)
    (hgg : Integrable (fun x => g x ^ 2) μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  apply integral_gram_sq_le hff hfg hgg
  intro x t
  nlinarith [sq_nonneg (f x * t - g x)]

/-- The weighted Cauchy–Schwarz step uses the original nonnegative weight
throughout, including when that weight vanishes. -/
theorem integral_weighted_cauchy_schwarz_sq {w g : α → ℝ}
    (hw : ∀ x, 0 ≤ w x)
    (hwint : Integrable w μ)
    (hwg : Integrable (fun x => w x * g x) μ)
    (hwgg : Integrable (fun x => w x * g x ^ 2) μ) :
    (∫ x, w x * g x ∂μ) ^ 2 ≤ (∫ x, w x ∂μ) * (∫ x, w x * g x ^ 2 ∂μ) := by
  apply integral_gram_sq_le hwint hwg hwgg
  intro x t
  nlinarith [mul_nonneg (hw x) (sq_nonneg (t - g x))]

/-- The fourth power of a complex pairing is controlled by the square of
the original target's `L¹` norm, its second moment, and the other function's
fourth moment. This is the full two-step analytic estimate. -/
theorem complex_pairing_fourth_le
    (f g : α → ℂ)
    (hf : Integrable (fun x => ‖f x‖) μ)
    (hfg : Integrable (fun x => ‖f x‖ * ‖g x‖) μ)
    (hfgg : Integrable (fun x => ‖f x‖ * ‖g x‖ ^ 2) μ)
    (hff : Integrable (fun x => ‖f x‖ ^ 2) μ)
    (hgggg : Integrable (fun x => ‖g x‖ ^ 4) μ) :
    ‖∫ x, f x * star (g x) ∂μ‖ ^ 4 ≤
      (∫ x, ‖f x‖ ∂μ) ^ 2 * (∫ x, ‖f x‖ ^ 2 ∂μ) * (∫ x, ‖g x‖ ^ 4 ∂μ) := by
  have hpair : ‖∫ x, f x * star (g x) ∂μ‖ ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by
    simpa only [norm_mul, norm_star] using
      (norm_integral_le_integral_norm (fun x => f x * star (g x)) (μ := μ))
  have hweighted := integral_weighted_cauchy_schwarz_sq (fun x => norm_nonneg (f x))
    hf hfg hfgg
  have hlast : (∫ x, ‖f x‖ * ‖g x‖ ^ 2 ∂μ) ^ 2 ≤
      (∫ x, ‖f x‖ ^ 2 ∂μ) * (∫ x, ‖g x‖ ^ 4 ∂μ) := by
    simpa only [← pow_mul] using integral_cauchy_schwarz_sq hff hfgg
      (show Integrable (fun x => (‖g x‖ ^ 2) ^ 2) μ by
        simpa only [← pow_mul] using hgggg)
  have hpairsq := pow_le_pow_left₀ (norm_nonneg _) hpair 2
  have hfirst := hpairsq.trans hweighted
  have hnext := pow_le_pow_left₀ (sq_nonneg _) hfirst 2
  have hmul := mul_le_mul_of_nonneg_left hlast
    (sq_nonneg (∫ x, ‖f x‖ ∂μ))
  calc
    ‖∫ x, f x * star (g x) ∂μ‖ ^ 4 ≤
        ((∫ x, ‖f x‖ ∂μ) * (∫ x, ‖f x‖ * ‖g x‖ ^ 2 ∂μ)) ^ 2 := by
      simpa only [← pow_mul] using hnext
    _ = (∫ x, ‖f x‖ ∂μ) ^ 2 * (∫ x, ‖f x‖ * ‖g x‖ ^ 2 ∂μ) ^ 2 := mul_pow _ _ _
    _ ≤ (∫ x, ‖f x‖ ∂μ) ^ 2 * ((∫ x, ‖f x‖ ^ 2 ∂μ) * (∫ x, ‖g x‖ ^ 4 ∂μ)) := hmul
    _ = _ := by ring

/-- The divided hereditary-energy estimate. A zero denominator is handled
using Lean's division convention and the nonnegativity of the fourth moment. -/
theorem complex_spectral_hereditary
    (f g : α → ℂ)
    (hf : Integrable (fun x => ‖f x‖) μ)
    (hfg : Integrable (fun x => ‖f x‖ * ‖g x‖) μ)
    (hfgg : Integrable (fun x => ‖f x‖ * ‖g x‖ ^ 2) μ)
    (hff : Integrable (fun x => ‖f x‖ ^ 2) μ)
    (hgggg : Integrable (fun x => ‖g x‖ ^ 4) μ) :
    ‖∫ x, f x * star (g x) ∂μ‖ ^ 4 /
        ((∫ x, ‖f x‖ ∂μ) ^ 2 * (∫ x, ‖f x‖ ^ 2 ∂μ)) ≤
      ∫ x, ‖g x‖ ^ 4 ∂μ := by
  have hd : 0 ≤ (∫ x, ‖f x‖ ∂μ) ^ 2 * (∫ x, ‖f x‖ ^ 2 ∂μ) := by
    exact mul_nonneg (sq_nonneg _) (integral_nonneg fun x => sq_nonneg _)
  rcases hd.eq_or_lt with hz | hp
  · rw [← hz, div_zero]
    exact integral_nonneg fun x => pow_nonneg (norm_nonneg _) _
  · apply (div_le_iff₀ hp).2
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      complex_pairing_fourth_le f g hf hfg hfgg hff hgggg

/-- Manuscript Lemma 5.2 for actual finite integer sets. The target remains
the original set `X`; only the second Fourier polynomial is replaced by the
subset `Y`. Empty sets are covered by the same statement. -/
theorem spectral_hereditary_energy {Y X : Finset ℤ} (hYX : Y ⊆ X) :
    (Y.card : ℝ) ^ 4 / (littlewoodNorm X ^ 2 * (X.card : ℝ)) ≤
      (additiveEnergy Y : ℝ) := by
  have hX := fourierPolynomial_continuous X
  have hY := fourierPolynomial_continuous Y
  have hmain := complex_spectral_hereditary (μ := circleMeasure)
    (fourierPolynomial X) (fourierPolynomial Y)
    (continuous_circle_integrable hX.norm)
    (continuous_circle_integrable (hX.norm.mul hY.norm))
    (continuous_circle_integrable (hX.norm.mul (hY.norm.pow 2)))
    (continuous_circle_integrable (hX.norm.pow 2))
    (continuous_circle_integrable (hY.norm.pow 4))
  have hpair : ‖∫ t, fourierPolynomial X t * star (fourierPolynomial Y t) ∂circleMeasure‖ =
      (Y.card : ℝ) := by
    change ‖circlePairing (fourierPolynomial X) (fourierPolynomial Y)‖ = (Y.card : ℝ)
    rw [circlePairing_fourierPolynomial_of_subset hYX]
    simp
  rw [hpair, integral_norm_sq_fourierPolynomial,
    integral_norm_pow_four_fourierPolynomial] at hmain
  exact hmain

/-- Division-free form of the same concrete hereditary inequality. -/
theorem card_fourth_le_norm_sq_card_energy {Y X : Finset ℤ} (hYX : Y ⊆ X) :
    (Y.card : ℝ) ^ 4 ≤ littlewoodNorm X ^ 2 * (X.card : ℝ) *
      (additiveEnergy Y : ℝ) := by
  have hX := fourierPolynomial_continuous X
  have hY := fourierPolynomial_continuous Y
  have hmain := complex_pairing_fourth_le (μ := circleMeasure)
    (fourierPolynomial X) (fourierPolynomial Y)
    (continuous_circle_integrable hX.norm)
    (continuous_circle_integrable (hX.norm.mul hY.norm))
    (continuous_circle_integrable (hX.norm.mul (hY.norm.pow 2)))
    (continuous_circle_integrable (hX.norm.pow 2))
    (continuous_circle_integrable (hY.norm.pow 4))
  have hpair : ‖∫ t, fourierPolynomial X t * star (fourierPolynomial Y t) ∂circleMeasure‖ =
      (Y.card : ℝ) := by
    change ‖circlePairing (fourierPolynomial X) (fourierPolynomial Y)‖ = (Y.card : ℝ)
    rw [circlePairing_fourierPolynomial_of_subset hYX]
    simp
  rw [hpair, integral_norm_sq_fourierPolynomial,
    integral_norm_pow_four_fourierPolynomial] at hmain
  exact hmain

end LittlewoodInverse
