import LittlewoodInverse.Basic

open scoped BigOperators Pointwise ComplexConjugate
open MeasureTheory

namespace LittlewoodInverse

theorem continuous_circle_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Circle → E} (hf : Continuous f) : Integrable f circleMeasure :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integral_fourier (n : ℤ) :
    (∫ t : Circle, fourier n t ∂circleMeasure) = if n = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) n) 0
  simpa [fourierCoeff, circleMeasure, Pi.single_apply, eq_comm] using h

theorem integral_fourier_mul_conj (a b : ℤ) :
    (∫ t : Circle, fourier a t * conj (fourier b t) ∂circleMeasure) =
      if a = b then 1 else 0 := by
  simp_rw [← fourier_neg, ← fourier_add]
  simpa [add_neg_eq_zero] using integral_fourier (a + -b)

theorem circlePairing_fourierPolynomial (X Y : Finset ℤ) :
    circlePairing (fourierPolynomial X) (fourierPolynomial Y) = ((Y ∩ X).card : ℂ) := by
  unfold circlePairing fourierPolynomial
  simp_rw [star_sum, Finset.mul_sum, Finset.sum_mul]
  rw [integral_finsetSum]
  · have hi (b : ℤ) :
        (∫ t : Circle, ∑ a ∈ X, fourier a t * star (fourier b t) ∂circleMeasure) =
          ∑ a ∈ X, ∫ t : Circle, fourier a t * star (fourier b t) ∂circleMeasure :=
        integral_finsetSum X (fun _ _ ↦ continuous_circle_integrable (by fun_prop))
    simp_rw [hi, Complex.star_def, integral_fourier_mul_conj]
    simp [Finset.sum_ite_eq']
  · intro i hi
    exact continuous_circle_integrable (by fun_prop)

theorem circlePairing_fourierPolynomial_of_subset {Y X : Finset ℤ} (h : Y ⊆ X) :
    circlePairing (fourierPolynomial X) (fourierPolynomial Y) = (Y.card : ℂ) := by
  unfold circlePairing fourierPolynomial
  simp_rw [star_sum, Finset.mul_sum, Finset.sum_mul]
  rw [integral_finsetSum]
  · have hi (b : ℤ) :
        (∫ t : Circle, ∑ a ∈ X, fourier a t * star (fourier b t) ∂circleMeasure) =
          ∑ a ∈ X, ∫ t : Circle, fourier a t * star (fourier b t) ∂circleMeasure :=
        integral_finsetSum X (fun _ _ ↦ continuous_circle_integrable (by fun_prop))
    simp_rw [hi, Complex.star_def, integral_fourier_mul_conj]
    simp [Finset.sum_ite_eq', Finset.inter_eq_left.mpr h]
  · intro i hi
    exact continuous_circle_integrable (by fun_prop)

theorem integral_norm_sq_fourierPolynomial (A : Finset ℤ) :
    (∫ t, ‖fourierPolynomial A t‖ ^ 2 ∂circleMeasure) = (A.card : ℝ) := by
  have h := circlePairing_fourierPolynomial_of_subset (X := A) (Y := A) Finset.Subset.rfl
  simp only [circlePairing, Complex.star_def, Complex.mul_conj',
    ← Complex.ofReal_pow] at h
  exact_mod_cast h

private theorem norm_pow_four_eq_sum_fourier (A : Finset ℤ) (t : Circle) :
    (‖fourierPolynomial A t‖ ^ 4 : ℂ) =
      ∑ x ∈ ((A ×ˢ A) ×ˢ A ×ˢ A),
        fourier (x.1.1 + x.2.1 - (x.1.2 + x.2.2)) t := by
  have hp : (conj (fourierPolynomial A t) * fourierPolynomial A t) ^ 2 =
      (‖fourierPolynomial A t‖ ^ 4 : ℂ) := by
    rw [mul_comm (conj _), Complex.mul_conj']
    ring
  rw [← hp]
  simp only [Finset.sum_product, sub_eq_add_neg, fourier_add, fourier_neg, map_mul]
  simp only [Finset.mul_sum, Finset.sum_mul, fourierPolynomial, map_sum, pow_two]
  congr 1
  ext a
  congr 1
  ext b
  congr 1
  ext c
  congr 1
  ext d
  ring

theorem integral_norm_pow_four_fourierPolynomial (A : Finset ℤ) :
    (∫ t, ‖fourierPolynomial A t‖ ^ 4 ∂circleMeasure) = (additiveEnergy A : ℝ) := by
  have hi :
      (∫ t : Circle, ∑ x ∈ ((A ×ˢ A) ×ˢ A ×ˢ A),
        fourier (x.1.1 + x.2.1 - (x.1.2 + x.2.2)) t ∂circleMeasure) =
        ∑ x ∈ ((A ×ˢ A) ×ˢ A ×ˢ A),
          ∫ t : Circle, fourier (x.1.1 + x.2.1 - (x.1.2 + x.2.2)) t ∂circleMeasure :=
    integral_finsetSum _ (fun _ _ ↦ continuous_circle_integrable (by fun_prop))
  have h : (∫ t, (‖fourierPolynomial A t‖ ^ 4 : ℂ) ∂circleMeasure) =
      (additiveEnergy A : ℂ) := by
    simp_rw [norm_pow_four_eq_sum_fourier]
    rw [hi]
    simp_rw [integral_fourier, sub_eq_zero]
    simp only [additiveEnergy, Finset.addEnergy, Finset.card_filter,
      Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  exact_mod_cast h

end LittlewoodInverse
