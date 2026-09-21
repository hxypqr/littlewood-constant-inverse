import LittlewoodInverse.SpectralEnergy

open scoped BigOperators Pointwise ComplexConjugate symmDiff
open MeasureTheory

namespace LittlewoodInverse

theorem one_le_littlewoodNorm {A : Finset ℤ} (hA : A.Nonempty) :
    1 ≤ littlewoodNorm A := by
  obtain ⟨a, ha⟩ := hA
  have hp := circlePairing_fourierPolynomial_of_subset
    (X := A) (Y := {a}) (by simpa using ha)
  have hn (t : Circle) : ‖fourierPolynomial {a} t‖ = 1 := by
    simp [fourierPolynomial, fourier_apply]
  calc
    1 = ‖circlePairing (fourierPolynomial A) (fourierPolynomial {a})‖ := by simp [hp]
    _ ≤ ∫ t, ‖fourierPolynomial A t * star (fourierPolynomial {a} t)‖ ∂circleMeasure :=
      norm_integral_le_integral_norm _
    _ = littlewoodNorm A := by simp only [norm_mul, norm_star, hn, mul_one, littlewoodNorm]

theorem integral_norm_le_sqrt_integral_norm_sq {f : Circle → ℂ} (hf : Continuous f) :
    (∫ t, ‖f t‖ ∂circleMeasure) ≤ Real.sqrt (∫ t, ‖f t‖ ^ 2 ∂circleMeasure) := by
  have hcs := integral_cauchy_schwarz_sq
    (μ := circleMeasure) (f := fun t ↦ ‖f t‖) (g := fun _ ↦ (1 : ℝ))
    (continuous_circle_integrable (hf.norm.pow 2))
    (continuous_circle_integrable (hf.norm.mul continuous_const))
    (continuous_circle_integrable continuous_const)
  simp only [mul_one, one_pow, integral_const, probReal_univ, smul_eq_mul] at hcs
  exact (Real.le_sqrt (integral_nonneg fun _ ↦ norm_nonneg _)
    (integral_nonneg fun _ ↦ sq_nonneg _)).mpr hcs

theorem littlewoodNorm_le_sqrt_card (A : Finset ℤ) :
    littlewoodNorm A ≤ Real.sqrt (A.card : ℝ) := by
  simpa only [littlewoodNorm, integral_norm_sq_fourierPolynomial] using
    integral_norm_le_sqrt_integral_norm_sq (fourierPolynomial_continuous A)

theorem integral_norm_sq_fourierPolynomial_sub (A B : Finset ℤ) :
    (∫ t, ‖fourierPolynomial A t - fourierPolynomial B t‖ ^ 2 ∂circleMeasure) =
      ((A ∆ B).card : ℝ) := by
  have hc (X Y : Finset ℤ) :
      Integrable (fun t ↦ fourierPolynomial X t * star (fourierPolynomial Y t)) circleMeasure :=
    continuous_circle_integrable ((fourierPolynomial_continuous X).mul
      (fourierPolynomial_continuous Y).star)
  have hp : (∫ t, (fourierPolynomial A t - fourierPolynomial B t) *
      star (fourierPolynomial A t - fourierPolynomial B t) ∂circleMeasure) =
      circlePairing (fourierPolynomial A) (fourierPolynomial A) -
      circlePairing (fourierPolynomial A) (fourierPolynomial B) -
      circlePairing (fourierPolynomial B) (fourierPolynomial A) +
      circlePairing (fourierPolynomial B) (fourierPolynomial B) := by
    calc
      _ = ∫ t, (fourierPolynomial A t * star (fourierPolynomial A t) -
          fourierPolynomial A t * star (fourierPolynomial B t)) -
          fourierPolynomial B t * star (fourierPolynomial A t) +
          fourierPolynomial B t * star (fourierPolynomial B t) ∂circleMeasure := by
        apply integral_congr_ae
        filter_upwards [] with t
        rw [star_sub]
        ring
      _ = _ := by
        have hab : Integrable (fun t ↦ fourierPolynomial A t * star (fourierPolynomial A t) -
            fourierPolynomial A t * star (fourierPolynomial B t)) circleMeasure :=
          (hc A A).sub (hc A B)
        have habc : Integrable (fun t ↦ (fourierPolynomial A t * star (fourierPolynomial A t) -
            fourierPolynomial A t * star (fourierPolynomial B t)) -
            fourierPolynomial B t * star (fourierPolynomial A t)) circleMeasure :=
          hab.sub (hc B A)
        rw [integral_add habc (hc B B), integral_sub hab (hc B A),
          integral_sub (hc A A) (hc A B)]
        rfl
  simp only [circlePairing_fourierPolynomial, Finset.inter_self, Finset.inter_comm B A] at hp
  simp only [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow] at hp
  have hcard : ((A ∆ B).card : ℂ) =
      (A.card : ℂ) - ((A ∩ B).card : ℂ) - ((A ∩ B).card : ℂ) + (B.card : ℂ) := by
    have hd : Disjoint (A \ B) (B \ A) := by
      exact Finset.disjoint_left.mpr fun x hx hy ↦
        (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
    rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hd, Nat.cast_add]
    have ha : ((A \ B).card : ℂ) + ((A ∩ B).card : ℂ) = (A.card : ℂ) := by
      exact_mod_cast Finset.card_sdiff_add_card_inter A B
    have hb : ((B \ A).card : ℂ) + ((A ∩ B).card : ℂ) = (B.card : ℂ) := by
      exact_mod_cast (by simpa only [Finset.inter_comm] using
        Finset.card_sdiff_add_card_inter B A)
    linear_combination ha + hb
  rw [← hcard] at hp
  exact_mod_cast hp

/-- Changing `s` frequencies changes the indicator Fourier `L¹` norm by at most `√s`. -/
theorem littlewoodNorm_sub_le_sqrt_symmDiff (A B : Finset ℤ) :
    |littlewoodNorm A - littlewoodNorm B| ≤ Real.sqrt ((A ∆ B).card : ℝ) := by
  have ha := fourierPolynomial_continuous A
  have hb := fourierPolynomial_continuous B
  calc
    |littlewoodNorm A - littlewoodNorm B| =
        |∫ t, ‖fourierPolynomial A t‖ - ‖fourierPolynomial B t‖ ∂circleMeasure| := by
      rw [integral_sub (continuous_circle_integrable ha.norm) (continuous_circle_integrable hb.norm)]
      rfl
    _ ≤ ∫ t, |‖fourierPolynomial A t‖ - ‖fourierPolynomial B t‖| ∂circleMeasure :=
      abs_integral_le_integral_abs
    _ ≤ ∫ t, ‖fourierPolynomial A t - fourierPolynomial B t‖ ∂circleMeasure := by
      apply integral_mono (continuous_circle_integrable (ha.norm.sub hb.norm).abs)
        (continuous_circle_integrable (ha.sub hb).norm)
      intro t
      exact abs_norm_sub_norm_le _ _
    _ ≤ Real.sqrt (∫ t, ‖fourierPolynomial A t - fourierPolynomial B t‖ ^ 2 ∂circleMeasure) :=
      integral_norm_le_sqrt_integral_norm_sq (ha.sub hb)
    _ = _ := by rw [integral_norm_sq_fourierPolynomial_sub]

theorem fourierPolynomial_translate (A : Finset ℤ) (u : ℤ) (t : Circle) :
    fourierPolynomial (A.image (fun a ↦ u + a)) t = fourier u t * fourierPolynomial A t := by
  rw [fourierPolynomial, Finset.sum_image]
  · simp only [fourier_add, fourierPolynomial, Finset.mul_sum]
  · intro a _ b _ hab
    exact add_left_cancel hab

theorem littlewoodNorm_translate (A : Finset ℤ) (u : ℤ) :
    littlewoodNorm (A.image (fun a ↦ u + a)) = littlewoodNorm A := by
  unfold littlewoodNorm
  simp only [fourierPolynomial_translate, norm_mul, fourier_apply, Circle.norm_coe, one_mul]

theorem fourierPolynomial_dilate (A : Finset ℤ) {v : ℤ} (hv : v ≠ 0) (t : Circle) :
    fourierPolynomial (A.image (fun a ↦ v * a)) t = fourierPolynomial A (v • t) := by
  rw [fourierPolynomial, Finset.sum_image]
  · unfold fourierPolynomial
    apply Finset.sum_congr rfl
    intro a _
    simp only [fourier_apply, mul_smul, smul_comm v a]
  · intro a _ b _ hab
    exact (mul_left_cancel₀ hv) hab

theorem littlewoodNorm_dilate (A : Finset ℤ) {v : ℤ} (hv : v ≠ 0) :
    littlewoodNorm (A.image (fun a ↦ v * a)) = littlewoodNorm A := by
  unfold littlewoodNorm
  simp only [fourierPolynomial_dilate A hv]
  have hp : MeasurePreserving (fun t : Circle ↦ v • t) circleMeasure circleMeasure := by
    unfold circleMeasure
    exact MeasureTheory.Measure.measurePreserving_zsmul _ hv
  have hm := integral_map (μ := circleMeasure) hp.measurable.aemeasurable
    (fourierPolynomial_continuous A).norm.aestronglyMeasurable
  rw [hp.map_eq] at hm
  exact hm.symm

theorem littlewoodNorm_affine (A : Finset ℤ) (u : ℤ) {v : ℤ} (hv : v ≠ 0) :
    littlewoodNorm (A.image (fun a ↦ u + v * a)) = littlewoodNorm A := by
  have hi : A.image (fun a ↦ u + v * a) =
      (A.image (fun a ↦ v * a)).image (fun a ↦ u + a) := by
    simp only [Finset.image_image, Function.comp_def]
  rw [hi, littlewoodNorm_translate, littlewoodNorm_dilate A hv]

end LittlewoodInverse
