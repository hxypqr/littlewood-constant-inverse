import LittlewoodInverse.LandauCoefficients
import LittlewoodInverse.MajorityPhase

/-! # Landau's bound for the actual one-sided Fourier class -/

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LittlewoodInverse
namespace Landau

noncomputable def polynomial (N : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range N, Polynomial.monomial k (b k : ℂ)

theorem polynomial_coeff (N k : ℕ) :
    (polynomial N).coeff k = if k < N then (b k : ℂ) else 0 := by
  simp [polynomial, Polynomial.coeff_monomial, Finset.mem_range]

theorem polynomial_square_coeff (N k : ℕ) (hk : k < N) :
    (polynomial N * polynomial N).coeff k = 1 := by
  rw [Polynomial.coeff_mul]
  have hterm (ij : ℕ × ℕ) (hij : ij ∈ Finset.HasAntidiagonal.antidiagonal k) :
      (polynomial N).coeff ij.1 * (polynomial N).coeff ij.2 =
        ((b ij.1 * b ij.2 : ℝ) : ℂ) := by
    have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    rw [polynomial_coeff, polynomial_coeff, if_pos (by omega), if_pos (by omega)]
    push_cast
    rfl
  rw [Finset.sum_congr rfl hterm, ← Complex.ofReal_sum, coefficient_convolution,
    Complex.ofReal_one]

noncomputable def evalCircle (P : Polynomial ℂ) (t : Circle) : ℂ := P.eval (fourier 1 t)

theorem evalCircle_expansion (P : Polynomial ℂ) (t : Circle) :
    evalCircle P t = ∑ k ∈ P.support, P.coeff k * fourier (k : ℤ) t := by
  simp only [evalCircle, Polynomial.eval_eq_sum, Polynomial.sum,
    Majority.fourier_pow_nat, mul_one]

theorem evalCircle_continuous (P : Polynomial ℂ) : Continuous (evalCircle P) := by
  unfold evalCircle
  exact P.continuous.comp (fourier 1).continuous

theorem circlePairing_evalCircle (P : Polynomial ℂ) {G : Circle → ℂ}
    (hG : Integrable G circleMeasure) :
    circlePairing (evalCircle P) G =
      ∑ k ∈ P.support, P.coeff k * conj (circleFourierCoeff G (k : ℤ)) := by
  unfold circlePairing
  simp only [evalCircle_expansion, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum P.support (fun k _ ↦
    (integrable_fourier_mul_star hG (k : ℤ)).const_mul (P.coeff k))]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_const_mul]
  congr 1
  have hh := circlePairing_indexedFourierSum {k} (fun n : ℕ ↦ (n : ℤ)) hG
  simpa only [indexedFourierSum, Finset.sum_singleton, circlePairing] using hh

theorem circleFourierCoeff_evalCircle (P : Polynomial ℂ) (n : ℕ) :
    circleFourierCoeff (evalCircle P) (n : ℤ) = P.coeff n := by
  unfold circleFourierCoeff
  simp only [evalCircle_expansion, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun _ _ ↦ continuous_circle_integrable (by fun_prop))]
  simp only [integral_const_mul, ← fourier_add, integral_fourier]
  have he (k : ℕ) : (k : ℤ) + -(n : ℤ) = 0 ↔ k = n := by omega
  simp only [he]
  by_cases hn : n ∈ P.support
  · simp [hn]
  · simp only [Polynomial.mem_support_iff, not_not] at hn
    simp [hn]

theorem integral_norm_sq_evalCircle (P : Polynomial ℂ) :
    (∫ t, ‖evalCircle P t‖ ^ 2 ∂circleMeasure) =
      ∑ k ∈ P.support, ‖P.coeff k‖ ^ 2 := by
  have hh := circlePairing_evalCircle P (continuous_circle_integrable (evalCircle_continuous P))
  simp only [circleFourierCoeff_evalCircle, Complex.mul_conj'] at hh
  unfold circlePairing at hh
  simp only [Complex.star_def, Complex.mul_conj'] at hh
  exact_mod_cast hh

theorem integral_norm_sq_polynomial (N : ℕ) :
    (∫ t, ‖evalCircle (polynomial N) t‖ ^ 2 ∂circleMeasure) =
      ∑ k ∈ Finset.range N, b k ^ 2 := by
  rw [integral_norm_sq_evalCircle]
  have hs : (polynomial N).support = Finset.range N := by
    ext k
    simp only [Polynomial.mem_support_iff, polynomial_coeff, Finset.mem_range]
    split_ifs with hk
    · simp [hk, (b_pos k).ne']
    · simp [hk]
  rw [hs]
  apply Finset.sum_congr rfl
  intro k hk
  rw [polynomial_coeff, if_pos (Finset.mem_range.mp hk), Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (b_pos k)]

noncomputable def dirichlet (N : ℕ) (t : Circle) : ℂ :=
  ∑ k ∈ Finset.range N, fourier (k : ℤ) t

theorem pairing_square_eq_dirichlet (N : ℕ) {G : Circle → ℂ}
    (hG : Integrable G circleMeasure)
    (hsupport : ∀ n : ℤ, (N : ℤ) ≤ n → circleFourierCoeff G n = 0) :
    circlePairing (evalCircle (polynomial N * polynomial N)) G =
      circlePairing (dirichlet N) G := by
  rw [circlePairing_evalCircle _ hG]
  have hs : Finset.range N ⊆ (polynomial N * polynomial N).support := by
    intro n hn
    rw [Polynomial.mem_support_iff, polynomial_square_coeff N n (Finset.mem_range.mp hn)]
    exact one_ne_zero
  have hz (n : ℕ) (_hn : n ∈ (polynomial N * polynomial N).support)
      (hnN : n ∉ Finset.range N) :
      (polynomial N * polynomial N).coeff n * conj (circleFourierCoeff G (n : ℤ)) = 0 := by
    have hn : N ≤ n := by simpa only [Finset.mem_range, not_lt] using hnN
    rw [hsupport n (by exact_mod_cast hn), map_zero, mul_zero]
  rw [← Finset.sum_subset hs hz]
  calc
    _ = ∑ n ∈ Finset.range N, conj (circleFourierCoeff G (n : ℤ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [polynomial_square_coeff N n (Finset.mem_range.mp hn), one_mul]
    _ = _ := (circlePairing_indexedFourierSum (Finset.range N) (fun n : ℕ ↦ (n : ℤ)) hG).symm

/-- Landau's exact inequality. The support condition is imposed on the
actual Fourier coefficients of the measurable bounded test. -/
theorem spectral_bound (N : ℕ) {G : Circle → ℂ}
    (hG : AEStronglyMeasurable G circleMeasure)
    (hGbound : ∀ᵐ t ∂circleMeasure, ‖G t‖ ≤ 1)
    (hsupport : ∀ n : ℤ, (N : ℤ) ≤ n → circleFourierCoeff G n = 0) :
    ‖circlePairing (dirichlet N) G‖ ≤ ∑ k ∈ Finset.range N, b k ^ 2 := by
  have hGi := (memLp_top_of_bound hG 1 hGbound).integrable le_top
  rw [← pairing_square_eq_dirichlet N hGi hsupport]
  have he (t : Circle) : evalCircle (polynomial N * polynomial N) t =
      evalCircle (polynomial N) t ^ 2 := by simp [evalCircle, pow_two]
  have hi : Integrable (fun t ↦ evalCircle (polynomial N) t ^ 2 * star (G t)) circleMeasure := by
    apply (continuous_circle_integrable ((evalCircle_continuous _).pow 2)).mul_bdd
      (Complex.continuous_conj.comp_aestronglyMeasurable hG)
    simpa only [Complex.star_def, Complex.norm_conj] using hGbound
  calc
    _ ≤ ∫ t, ‖evalCircle (polynomial N) t ^ 2 * star (G t)‖ ∂circleMeasure := by
      simpa only [circlePairing, he] using norm_integral_le_integral_norm
        (fun t ↦ evalCircle (polynomial N) t ^ 2 * star (G t)) (μ := circleMeasure)
    _ ≤ ∫ t, ‖evalCircle (polynomial N) t‖ ^ 2 ∂circleMeasure := by
      apply integral_mono_ae hi.norm
        (continuous_circle_integrable ((evalCircle_continuous _).norm.pow 2))
      filter_upwards [hGbound] with t ht
      rw [norm_mul, norm_star, norm_pow]
      exact mul_le_of_le_one_right (by positivity) ht
    _ = _ := integral_norm_sq_polynomial N

end Landau
end LittlewoodInverse
