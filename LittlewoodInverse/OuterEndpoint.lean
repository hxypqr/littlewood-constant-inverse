import LittlewoodInverse.DampedTest
import LittlewoodInverse.PacketSupport
import LittlewoodInverse.LandauSpectral
import LittlewoodInverse.OuterFamily
import LittlewoodInverse.LandauAsymptotic

open scoped BigOperators
open MeasureTheory

namespace LittlewoodInverse

def UpperSpectrum (f : Circle → ℂ) (H : ℤ) : Prop :=
  ∀ n : ℤ, H < n → circleFourierCoeff f n = 0

theorem normalizedPolynomial_upperSpectrum (A : Finset ℤ) (H : ℤ)
    (hA : ∀ k ∈ A, k ≤ H) :
    UpperSpectrum (fun t => fourierPolynomial A t / (A.card : ℂ)) H := by
  intro n hn
  unfold circleFourierCoeff fourierPolynomial
  simp_rw [div_mul_eq_mul_div, Finset.sum_mul]
  rw [integral_div, integral_finsetSum]
  · have hz (k : ℤ) (hk : k ∈ A) :
        (∫ t : Circle, fourier k t * fourier (-n) t ∂circleMeasure) = 0 := by
      simp only [← fourier_add]
      rw [integral_fourier]
      simp [show k + -n ≠ 0 by have := hA k hk; omega]
    simp only [Finset.sum_congr rfl hz, Finset.sum_const_zero, zero_div]
  · intro k _
    exact continuous_circle_integrable (by fun_prop)

theorem interval_subset_upperSpectrum (N : ℕ) (B : Finset ℤ)
    (hB : B ⊆ Finset.Ico (0 : ℤ) N) :
    UpperSpectrum (fun t => fourierPolynomial B t / (B.card : ℂ)) ((N : ℤ)-1) := by
  apply normalizedPolynomial_upperSpectrum
  intro k hk
  have := (Finset.mem_Ico.mp (hB hk)).2
  omega

theorem upperSpectrum_mul {f P : Circle → ℂ} {H : ℤ}
    (hf : MemLp f 2 circleMeasure) (hP : MemLp P 2 circleMeasure)
    (hsf : UpperSpectrum f H) (hsP : NonpositiveFourierSupport P) :
    UpperSpectrum (fun t => f t * P t) H := by
  intro k hk
  rw [circleFourierCoeff_mul_eq_tsum hf hP]
  have hz (n : ℤ) : circleFourierCoeff f (-n) * circleFourierCoeff P (n+k) = 0 := by
    by_cases hn : H < -n
    · rw [hsf (-n) hn,zero_mul]
    · rw [hsP (n+k) (by omega),mul_zero]
  simp only [hz,tsum_zero]

theorem dampedTest_upperSpectrum {n : ℕ} (a : ℝ) (f M : Fin n → Circle → ℂ) (H : ℤ)
    (hf : ∀ i, MemLp (f i) ⊤ circleMeasure) (hM : ∀ i, MemLp (M i) ⊤ circleMeasure)
    (hsf : ∀ i, UpperSpectrum (f i) H)
    (hsM : ∀ i, NonpositiveFourierSupport (M i)) : UpperSpectrum (dampedTest a f M) H := by
  intro k hk
  have hprod (i : Fin n) : MemLp (fun t => f i t * dampingTail M i t) ⊤ circleMeasure :=
    (dampingTail_memLp M hM i).mul' (hf i)
  have hs (i : Fin n) := upperSpectrum_mul ((hf i).mono_exponent le_top)
    ((dampingTail_memLp M hM i).mono_exponent le_top) (hsf i) (dampingTail_support M hM hsM i) k hk
  unfold circleFourierCoeff dampedTest
  simp only [Finset.sum_mul,mul_assoc]
  rw [integral_finsetSum]
  · have he (i : Fin n) :
        (∫ t, (a : ℂ)*(f i t*(dampingTail M i t*fourier (-k) t)) ∂circleMeasure) = 0 := by
      rw [integral_const_mul]
      have hh : (∫ t, f i t*(dampingTail M i t*fourier (-k) t) ∂circleMeasure) = 0 := by
        simpa only [circleFourierCoeff,mul_assoc] using hs i
      rw [hh,mul_zero]
    simp only [he,Finset.sum_const_zero]
  · intro i _
    simpa only [mul_assoc] using
      (integrable_mul_fourier ((hprod i).integrable le_top) (-k)).const_mul (a : ℂ)

/-- Every interval test produced by the outer recursion remains in the
Landau spectral class. The endpoint bound therefore applies to the actual
finite sum of damped sources. -/
theorem damped_interval_endpoint {n : ℕ} (N : ℕ) {a : ℝ} (ha : 0 ≤ a)
    (f M : Fin n → Circle → ℂ)
    (hf : ∀ i, MemLp (f i) ⊤ circleMeasure) (hM : ∀ i, MemLp (M i) ⊤ circleMeasure)
    (hsf : ∀ i, UpperSpectrum (f i) ((N : ℤ)-1))
    (hsM : ∀ i, NonpositiveFourierSupport (M i))
    (hm : ∀ i, ∀ᵐ t ∂circleMeasure, ‖M i t‖ = 1-a*‖f i t‖) :
    ‖circlePairing (Landau.dirichlet N) (dampedTest a f M)‖ ≤
      ∑ k ∈ Finset.range N, Landau.b k^2 := by
  apply Landau.spectral_bound
  · have ht : MemLp (dampedTest a f M) ⊤ circleMeasure := by
      apply memLp_finsetSum
      intro i _
      exact ((dampingTail_memLp M hM i).mul' (hf i) : MemLp _ ⊤ circleMeasure).const_mul (a : ℂ)
    exact ht.1
  · have hall := ae_all_iff.mpr hm
    filter_upwards [hall] with t ht
    exact dampedTest_norm_le ha f M t ht
  · intro k hk
    exact dampedTest_upperSpectrum a f M _ hf hM hsf hsM k (by omega)

/-- The sources may be the actual normalized initial prefixes, or any
subsets of the interval: no spectral hypothesis is left to the caller. -/
theorem outer_interval_endpoint {n : ℕ} (N : ℕ) {a : ℝ} (ha : 0 ≤ a)
    (B : Fin n → Finset ℤ) (hB : ∀ i, B i ⊆ Finset.Ico (0 : ℤ) N)
    (M : ∀ i, DampingData a (B i)) :
    ‖circlePairing (Landau.dirichlet N)
      (dampedTest a (fun i t => fourierPolynomial (B i) t / ((B i).card : ℂ))
        (fun i => (M i).multiplier))‖ ≤ ∑ k ∈ Finset.range N, Landau.b k^2 := by
  apply damped_interval_endpoint N ha
  · intro i
    exact ((fourierPolynomial_continuous (B i)).div_const _).memLp_top_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) circleMeasure
  · exact fun i => (M i).memLp
  · exact fun i => interval_subset_upperSpectrum N (B i) (hB i)
  · exact fun i => (M i).support
  · intro i
    simpa only [norm_div,Complex.norm_natCast] using (M i).modulus

theorem outer_interval_log_endpoint {n : ℕ} (N : ℕ) (hN : 0 < N)
    {a : ℝ} (ha : 0 ≤ a) (B : Fin n → Finset ℤ)
    (hB : ∀ i, B i ⊆ Finset.Ico (0 : ℤ) N) (M : ∀ i, DampingData a (B i)) :
    ‖circlePairing (Landau.dirichlet N)
      (dampedTest a (fun i t => fourierPolynomial (B i) t / ((B i).card : ℂ))
        (fun i => (M i).multiplier))‖ ≤ Real.log N / Real.pi+2 := by
  have hh := (abs_le.mp (Landau.sum_b_sq_log_error N hN)).2
  exact (outer_interval_endpoint N ha B hB M).trans (by linarith)

end LittlewoodInverse
