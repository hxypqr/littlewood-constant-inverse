import LittlewoodInverse.NormBounds
import LittlewoodInverse.PrefixCount

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LittlewoodInverse

/-- Every ambient frequency below a retained frequency is retained. -/
def IsInitialSegment (B A : Finset ℤ) : Prop :=
  B ⊆ A ∧ ∀ a ∈ A, ∀ b ∈ B, a ≤ b → a ∈ B

/-- The actual Fourier coefficients vanish at all positive frequencies. -/
def NonpositiveFourierSupport (P : Circle → ℂ) : Prop :=
  ∀ n : ℤ, 0 < n → circleFourierCoeff P n = 0

noncomputable def indexedFourierSum {ι : Type*} (S : Finset ι) (n : ι → ℤ)
    (t : Circle) : ℂ := ∑ j ∈ S, fourier (n j) t

theorem indexedFourierSum_continuous {ι : Type*} (S : Finset ι) (n : ι → ℤ) :
    Continuous (indexedFourierSum S n) := by unfold indexedFourierSum; fun_prop

theorem indexedFourierSum_second_moment {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (n : ι → ℤ) :
    (∫ t, ‖indexedFourierSum S n t‖ ^ 2 ∂circleMeasure) =
      (((S ×ˢ S).filter (fun x ↦ n x.1 = n x.2)).card : ℝ) := by
  have hi (j : ι) :
      (∫ t : Circle, ∑ i ∈ S, fourier (n i) t * conj (fourier (n j) t) ∂circleMeasure) =
        ∑ i ∈ S, ∫ t : Circle, fourier (n i) t * conj (fourier (n j) t) ∂circleMeasure :=
    integral_finsetSum _ (fun _ _ ↦ continuous_circle_integrable (by fun_prop))
  have he : (∫ t, (‖indexedFourierSum S n t‖ ^ 2 : ℂ) ∂circleMeasure) =
      (((S ×ˢ S).filter (fun x ↦ n x.1 = n x.2)).card : ℂ) := by
    simp_rw [← Complex.mul_conj', indexedFourierSum, map_sum, Finset.mul_sum, Finset.sum_mul]
    rw [integral_finsetSum]
    · simp_rw [hi, integral_fourier_mul_conj]
      simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
        Nat.cast_zero, Finset.sum_product]
      exact Finset.sum_comm
    · intro i hi
      exact continuous_circle_integrable (by fun_prop)
  exact_mod_cast he

theorem integrable_mul_fourier {P : Circle → ℂ} (hP : Integrable P circleMeasure) (n : ℤ) :
    Integrable (fun t ↦ P t * fourier n t) circleMeasure := by
  have hi := MeasureTheory.Integrable.fourier_smul
    (show Integrable P AddCircle.haarAddCircle from hP) n
  simpa only [circleMeasure, smul_eq_mul, mul_comm] using hi

theorem circlePairing_fourier_mul (P : Circle → ℂ) (a b : ℤ) :
    circlePairing (fourier a) (fun t ↦ fourier b t * P t) =
      conj (circleFourierCoeff P (a - b)) := by
  unfold circlePairing circleFourierCoeff
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [Complex.star_def, map_mul, ← fourier_neg, neg_neg]
  rw [sub_eq_add_neg, fourier_add]
  ring

theorem circlePairing_fourierPolynomial_mul {P : Circle → ℂ}
    (hP : Integrable P circleMeasure) (A B : Finset ℤ) :
    circlePairing (fourierPolynomial A) (fun t ↦ fourierPolynomial B t * P t) =
      ∑ b ∈ B, ∑ a ∈ A, conj (circleFourierCoeff P (a - b)) := by
  have hi (a b : ℤ) :
      Integrable (fun t ↦ fourier a t * star (fourier b t * P t)) circleMeasure := by
    have he (t : Circle) : fourier a t * star (fourier b t * P t) =
        conj (P t * fourier (-(a - b)) t) := by
      simp only [Complex.star_def, map_mul, ← fourier_neg, neg_neg]
      rw [sub_eq_add_neg, fourier_add]
      ring
    simp_rw [he]
    exact Complex.conjCLE.integrable_comp_iff.mpr (integrable_mul_fourier hP (-(a - b)))
  unfold circlePairing fourierPolynomial
  simp_rw [Finset.sum_mul, star_sum, Finset.mul_sum]
  have hsum (t : Circle) :
      (∑ a ∈ A, ∑ b ∈ B, fourier a t * star (fourier b t * P t)) =
        ∑ b ∈ B, ∑ a ∈ A, fourier a t * star (fourier b t * P t) := Finset.sum_comm
  simp_rw [hsum]
  rw [integral_finsetSum]
  · have hj (b : ℤ) :
        (∫ t : Circle, ∑ a ∈ A, fourier a t * star (fourier b t * P t) ∂circleMeasure) =
          ∑ a ∈ A, ∫ t : Circle, fourier a t * star (fourier b t * P t) ∂circleMeasure :=
      integral_finsetSum _ (fun _ _ ↦ hi _ _)
    simp_rw [hj]
    exact Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun a _ ↦
      circlePairing_fourier_mul P a b
  · intro b _
    exact integrable_finsetSum _ (fun a _ ↦ hi a b)

/-- Exact frequency localization preceding the quantitative prefix bound. -/
theorem initial_segment_pairing_localization {A B : Finset ℤ}
    (hB : IsInitialSegment B A) {P : Circle → ℂ}
    (hP : Integrable P circleMeasure) (hsupp : NonpositiveFourierSupport P) :
    circlePairing (fourierPolynomial A) (fun t ↦ fourierPolynomial B t * P t) =
      circlePairing (fourierPolynomial B) (fun t ↦ fourierPolynomial B t * P t) := by
  rw [circlePairing_fourierPolynomial_mul hP, circlePairing_fourierPolynomial_mul hP]
  apply Finset.sum_congr rfl
  intro b hb
  symm
  apply Finset.sum_subset hB.1
  intro a ha hnot
  have hlt : b < a := lt_of_not_ge (fun hle ↦ hnot (hB.2 a ha b hb hle))
  simp only [hsupp (a - b) (sub_pos.mpr hlt), map_zero]

noncomputable def prefixKernel (B : Finset ℤ) : Circle → ℂ :=
  indexedFourierSum (PrefixCounting.orderedPairs B) (fun p ↦ p.1 - p.2)

theorem prefixKernel_continuous (B : Finset ℤ) : Continuous (prefixKernel B) :=
  indexedFourierSum_continuous _ _

theorem prefixKernel_second_moment (B : Finset ℤ) :
    (∫ t, ‖prefixKernel B t‖ ^ 2 ∂circleMeasure) =
      ((additiveEnergy B : ℝ) + (B.card : ℝ)^2) / 2 := by
  have hcount : (2 : ℝ) * (PrefixCounting.orderedCollisionCount B : ℝ) =
      (additiveEnergy B : ℝ) + (B.card : ℝ)^2 := by
    exact_mod_cast PrefixCounting.ordered_collision_identity B
  rw [prefixKernel, indexedFourierSum_second_moment]
  change (PrefixCounting.orderedCollisionCount B : ℝ) = _
  linarith

theorem integrable_fourier_mul_star {P : Circle → ℂ}
    (hP : Integrable P circleMeasure) (a : ℤ) :
    Integrable (fun t ↦ fourier a t * star (P t)) circleMeasure := by
  have hi := Complex.conjCLE.integrable_comp_iff.mpr (integrable_mul_fourier hP (-a))
  have he (t : Circle) : conj (P t * fourier (-a) t) = fourier a t * star (P t) := by
    simp only [map_mul, ← fourier_neg, neg_neg, Complex.star_def, mul_comm]
  simpa only [Complex.conjCLE_apply, he] using hi

theorem circlePairing_indexedFourierSum {ι : Type*} (S : Finset ι) (n : ι → ℤ)
    {P : Circle → ℂ} (hP : Integrable P circleMeasure) :
    circlePairing (indexedFourierSum S n) P = ∑ j ∈ S, conj (circleFourierCoeff P (n j)) := by
  unfold circlePairing indexedFourierSum
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ (fun j _ ↦ integrable_fourier_mul_star hP (n j))]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [fourier_zero, one_mul, sub_zero, circlePairing] using circlePairing_fourier_mul P (n j) 0

/-- All positive differences disappear against the prescribed Fourier support. -/
theorem pairing_eq_prefixKernel (B : Finset ℤ) {P : Circle → ℂ}
    (hP : Integrable P circleMeasure) (hsupp : NonpositiveFourierSupport P) :
    circlePairing (fourierPolynomial B) (fun t ↦ fourierPolynomial B t * P t) =
      circlePairing (prefixKernel B) P := by
  rw [circlePairing_fourierPolynomial_mul hP]
  unfold prefixKernel
  rw [circlePairing_indexedFourierSum _ _ hP]
  rw [Finset.sum_comm]
  change (∑ a ∈ B, ∑ b ∈ B, conj (circleFourierCoeff P (a - b))) = _
  rw [← Finset.sum_product (f := fun p : ℤ × ℤ ↦ conj (circleFourierCoeff P (p.1 - p.2)))]
  unfold PrefixCounting.orderedPairs
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hle : p.1 ≤ p.2
  · simp only [hle, if_true]
  · simp only [hle, if_false, hsupp (p.1 - p.2) (by omega), map_zero]

theorem prefixKernel_integral (B : Finset ℤ) :
    (∫ t, prefixKernel B t ∂circleMeasure) = (B.card : ℂ) := by
  have hsupp : NonpositiveFourierSupport (fun _ : Circle ↦ (1 : ℂ)) := by
    intro n hn
    simp only [circleFourierCoeff, one_mul, integral_fourier,
      neg_eq_zero, ne_of_gt hn, if_false]
  have he := pairing_eq_prefixKernel B (integrable_const 1) hsupp
  simp only [mul_one] at he
  simpa only [mul_one, circlePairing, star_one] using
    he.symm.trans (circlePairing_fourierPolynomial_of_subset (X := B) (Y := B) Finset.Subset.rfl)

theorem circlePairing_cauchy_schwarz_sq {f g : Circle → ℂ}
    (hf : MemLp f 2 circleMeasure) (hg : MemLp g 2 circleMeasure) :
    ‖circlePairing f g‖ ^ 2 ≤
      (∫ t, ‖f t‖ ^ 2 ∂circleMeasure) * (∫ t, ‖g t‖ ^ 2 ∂circleMeasure) := by
  have hi : Integrable (fun t ↦ ‖f t‖ * ‖g t‖) circleMeasure := hf.norm.integrable_mul hg.norm
  have hcs := integral_cauchy_schwarz_sq hf.norm.integrable_sq hi hg.norm.integrable_sq
  have hp : ‖circlePairing f g‖ ≤ ∫ t, ‖f t‖ * ‖g t‖ ∂circleMeasure := by
    simpa only [circlePairing, norm_mul, norm_star] using
      norm_integral_le_integral_norm (fun t ↦ f t * star (g t)) (μ := circleMeasure)
  exact (pow_le_pow_left₀ (norm_nonneg _) hp 2).trans hcs

theorem prefix_pairing_error_identity {A B : Finset ℤ} (hB : IsInitialSegment B A)
    {P : Circle → ℂ} (hP : Integrable P circleMeasure) (hsupp : NonpositiveFourierSupport P) :
    circlePairing (fourierPolynomial A) (fun t ↦ fourierPolynomial B t * P t) - (B.card : ℂ) =
      circlePairing (prefixKernel B) (fun t ↦ P t - 1) := by
  rw [initial_segment_pairing_localization hB hP hsupp, pairing_eq_prefixKernel B hP hsupp]
  have hi : Integrable (fun t ↦ prefixKernel B t * star (P t)) circleMeasure := by
    simp only [prefixKernel, indexedFourierSum, Finset.sum_mul]
    exact integrable_finsetSum _ (fun p _ ↦ integrable_fourier_mul_star hP (p.1 - p.2))
  unfold circlePairing
  simp only [star_sub, star_one, mul_sub, mul_one]
  rw [integral_sub hi (continuous_circle_integrable (prefixKernel_continuous B)), prefixKernel_integral]

/-- The unnormalized form, for every genuine `L²` multiplier. -/
theorem initial_segment_pairing_error_sq {A B : Finset ℤ} (hB : IsInitialSegment B A)
    {P : Circle → ℂ} (hP : MemLp P 2 circleMeasure) (hsupp : NonpositiveFourierSupport P) :
    ‖circlePairing (fourierPolynomial A) (fun t ↦ fourierPolynomial B t * P t) - (B.card : ℂ)‖ ^ 2 ≤
      (((additiveEnergy B : ℝ) + (B.card : ℝ)^2) / 2) *
        (∫ t, ‖P t - 1‖ ^ 2 ∂circleMeasure) := by
  have hQ : MemLp (fun t ↦ P t - 1) 2 circleMeasure := hP.sub (memLp_const 1)
  have hH : MemLp (prefixKernel B) 2 circleMeasure :=
    (memLp_two_iff_integrable_sq_norm (prefixKernel_continuous B).aestronglyMeasurable).mpr
      (continuous_circle_integrable ((prefixKernel_continuous B).norm.pow 2))
  rw [prefix_pairing_error_identity hB (hP.integrable (by norm_num)) hsupp]
  have hcs := circlePairing_cauchy_schwarz_sq hH hQ
  simpa only [prefixKernel_second_moment] using hcs

theorem circlePairing_div_nat_right (f g : Circle → ℂ) (n : ℕ) :
    circlePairing f (fun t ↦ g t / (n : ℂ)) = circlePairing f g / (n : ℂ) := by
  simp only [circlePairing, star_div₀, star_natCast, ← mul_div_assoc, integral_div]

/-- Lemma 4.2 of the manuscript, including its exact one-sided constant.

`P` is an arbitrary `L²` function; no continuity or boundedness is assumed.
-/
theorem initial_segment_pairing_error {A B : Finset ℤ} (hB : IsInitialSegment B A)
    (hBn : B.Nonempty) {P : Circle → ℂ} (hP : MemLp P 2 circleMeasure)
    (hsupp : NonpositiveFourierSupport P) :
    ‖circlePairing (fourierPolynomial A)
        (fun t ↦ (fourierPolynomial B t / (B.card : ℂ)) * P t) - 1‖ ≤
      Real.sqrt (((additiveEnergy B : ℝ) + (B.card : ℝ)^2) / (2 * (B.card : ℝ)^2)) *
        Real.sqrt (∫ t, ‖P t - 1‖ ^ 2 ∂circleMeasure) := by
  have hn : 0 < (B.card : ℝ) := by exact_mod_cast hBn.card_pos
  have hnc : (B.card : ℂ) ≠ 0 := by exact_mod_cast hBn.card_pos.ne'
  have hnorm : circlePairing (fourierPolynomial A)
        (fun t ↦ (fourierPolynomial B t / (B.card : ℂ)) * P t) - 1 =
      (circlePairing (fourierPolynomial A) (fun t ↦ fourierPolynomial B t * P t) -
        (B.card : ℂ)) / (B.card : ℂ) := by
    simp_rw [div_mul_eq_mul_div]
    rw [circlePairing_div_nat_right]
    field_simp
  rw [hnorm, norm_div, Complex.norm_natCast]
  have hcs := initial_segment_pairing_error_sq hB hP hsupp
  have hmoment : 0 ≤ ∫ t, ‖P t - 1‖ ^ 2 ∂circleMeasure :=
    integral_nonneg fun _ ↦ sq_nonneg _
  have henergy : 0 ≤ ((additiveEnergy B : ℝ) + (B.card : ℝ)^2) / (2 * (B.card : ℝ)^2) :=
    by positivity
  apply (sq_le_sq₀ (div_nonneg (norm_nonneg _) hn.le)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [div_pow, mul_pow, Real.sq_sqrt henergy, Real.sq_sqrt hmoment]
  apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
  calc
    _ ≤ (((additiveEnergy B : ℝ) + (B.card : ℝ)^2) / 2) *
        (∫ t, ‖P t - 1‖ ^ 2 ∂circleMeasure) := hcs
    _ = _ := by field_simp

end LittlewoodInverse
