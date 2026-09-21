import LittlewoodInverse.FreimanMoments

open scoped BigOperators
open MeasureTheory

namespace LittlewoodInverse

attribute [local fun_prop] fourierPolynomial_continuous

theorem fourierPolynomial_norm_le_card (C : Finset ℤ) (t : Circle) :
    ‖fourierPolynomial C t‖ ≤ (C.card : ℝ) := by
  unfold fourierPolynomial
  calc
    _ ≤ ∑ i ∈ C, ‖fourier i t‖ := norm_sum_le _ _
    _ = _ := by simp [fourier_apply]

/-- Integrating an even polynomial only uses the finite list of preserved moments. -/
theorem freiman_even_polynomial_integral {h : ℕ} {A : Finset ℤ} {B : Set ℤ} {f : ℤ → ℤ}
    (hf : IsAddFreimanIso h (A : Set ℤ) B f) {C : Finset ℤ} (hCA : C ⊆ A)
    (a : Fin (h + 1) → ℝ) (m : ℝ) :
    (∫ t, ∑ i, a i * (‖fourierPolynomial C t‖ / m) ^ (2 * i.val) ∂circleMeasure) =
      ∫ t, ∑ i, a i * (‖fourierPolynomial (C.image f) t‖ / m) ^ (2 * i.val)
        ∂circleMeasure := by
  rw [integral_finsetSum _ (fun _ _ => continuous_circle_integrable (by fun_prop)),
    integral_finsetSum _ (fun _ _ => continuous_circle_integrable (by fun_prop))]
  apply Finset.sum_congr rfl
  intro i _
  simp only [div_pow, integral_const_mul, integral_div,
    freiman_integral_even_moment hf (Nat.le_of_lt_succ i.isLt) hCA]

/-- The analytic reduction in Lemma 9.2.  A concrete approximation must still be supplied. -/
theorem freiman_norm_transport_of_approximation {h : ℕ} {A : Finset ℤ} {B : Set ℤ}
    {f : ℤ → ℤ} (hf : IsAddFreimanIso h (A : Set ℤ) B f)
    {C : Finset ℤ} (hCA : C ⊆ A) (a : Fin (h + 1) → ℝ) {δ : ℝ}
    (happrox : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      |x - ∑ i, a i * x ^ (2 * i.val)| ≤ δ) :
    |littlewoodNorm C - littlewoodNorm (C.image f)| ≤ 2 * (C.card : ℝ) * δ := by
  classical
  by_cases hC : C = ∅
  · simp [hC]
  have hm : (0 : ℝ) < C.card := Nat.cast_pos.mpr (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hC))
  have hcard : (C.image f).card = C.card := Finset.card_image_of_injOn
    (fun x hx y hy hxy => hf.bijOn.injOn (hCA hx) (hCA hy) hxy)
  let m : ℝ := C.card
  let p (X : Finset ℤ) (t : Circle) := ∑ i, a i * (‖fourierPolynomial X t‖ / m) ^ (2 * i.val)
  have heq : (∫ t, p C t ∂circleMeasure) = ∫ t, p (C.image f) t ∂circleMeasure :=
    freiman_even_polynomial_integral hf hCA a m
  have herr (X : Finset ℤ) (hX : X.card = C.card) :
      |littlewoodNorm X / m - ∫ t, p X t ∂circleMeasure| ≤ δ := by
    have hc : Continuous (fun t => ‖fourierPolynomial X t‖ / m - p X t) := by
      dsimp [p]
      fun_prop
    calc
      _ = |∫ t, (‖fourierPolynomial X t‖ / m - p X t) ∂circleMeasure| := by
        rw [integral_sub (continuous_circle_integrable (by fun_prop))
          (continuous_circle_integrable (by dsimp [p]; fun_prop)), integral_div]
        rfl
      _ ≤ ∫ t, |‖fourierPolynomial X t‖ / m - p X t| ∂circleMeasure :=
        abs_integral_le_integral_abs
      _ ≤ ∫ _ : Circle, δ ∂circleMeasure := by
        apply integral_mono (continuous_circle_integrable hc.abs)
          (continuous_circle_integrable continuous_const)
        intro t
        apply happrox _ (div_nonneg (norm_nonneg _) hm.le)
        apply (div_le_one hm).mpr
        simpa [m, hX] using fourierPolynomial_norm_le_card X t
      _ = δ := by simp
  have h1 := herr C rfl
  have h2 := herr (C.image f) hcard
  rw [← heq] at h2
  have he : |littlewoodNorm C / m - littlewoodNorm (C.image f) / m| ≤ 2 * δ := by
    calc
      _ ≤ |littlewoodNorm C / m - ∫ t, p C t ∂circleMeasure| +
        |littlewoodNorm (C.image f) / m - ∫ t, p C t ∂circleMeasure| := by
          simpa only [abs_sub_comm (∫ t, p C t ∂circleMeasure)] using
            abs_sub_le (littlewoodNorm C / m) (∫ t, p C t ∂circleMeasure)
              (littlewoodNorm (C.image f) / m)
      _ ≤ 2 * δ := by linarith
  rw [← sub_div, abs_div, abs_of_pos hm] at he
  have he' := (div_le_iff₀ hm).mp he
  nlinarith

end LittlewoodInverse
