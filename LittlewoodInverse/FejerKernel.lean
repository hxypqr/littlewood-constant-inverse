import LittlewoodInverse.OuterDamping
import Mathlib.Data.Int.Interval

/-! # Explicit Fejér and de la Vallée Poussin kernels -/

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LittlewoodInverse

noncomputable def fejerInterval (D : ℕ) : Finset ℤ := Finset.Ico 0 (D : ℤ)

noncomputable def intervalDifferenceCount (D : ℕ) (n : ℤ) : ℕ :=
  (((fejerInterval D) ×ˢ (fejerInterval D)).filter (fun p ↦ p.1 - p.2 = n)).card

theorem intervalDifferenceCount_eq (D : ℕ) (n : ℤ) :
    intervalDifferenceCount D n = ((D : ℤ) - |n|).toNat := by
  have hc : intervalDifferenceCount D n =
      (Finset.Ico (max 0 (-n)) (min (D : ℤ) ((D : ℤ) - n))).card := by
    unfold intervalDifferenceCount
    apply Finset.card_bij (fun p _ ↦ p.2)
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, fejerInterval,
        Finset.mem_Ico] at hp
      simp only [Finset.mem_Ico, max_le_iff, lt_min_iff]
      omega
    · intro p hp q hq he
      simp only [Finset.mem_filter] at hp hq
      ext <;> omega
    · intro b hb
      refine ⟨(b + n, b), ?_, rfl⟩
      simp only [Finset.mem_Ico, max_le_iff, lt_min_iff] at hb
      simp only [Finset.mem_filter, Finset.mem_product, fejerInterval, Finset.mem_Ico]
      omega
  rw [hc, Int.card_Ico]
  congr 1
  rcases le_or_gt 0 n with hn | hn
  · rw [abs_of_nonneg hn, max_eq_left (by omega), min_eq_right (by omega)]
    omega
  · rw [abs_of_neg hn, max_eq_right (by omega), min_eq_left (by omega)]

noncomputable def fejerKernel (D : ℕ) (t : Circle) : ℝ :=
  ‖fourierPolynomial (fejerInterval D) t‖ ^ 2 / (D : ℝ)

theorem fejerKernel_continuous (D : ℕ) : Continuous (fejerKernel D) := by
  exact ((fourierPolynomial_continuous _).norm.pow 2).div_const _

theorem fejerKernel_nonneg (D : ℕ) (t : Circle) : 0 ≤ fejerKernel D t := by
  unfold fejerKernel
  positivity

theorem integral_fejerKernel {D : ℕ} (hD : 0 < D) :
    (∫ t, fejerKernel D t ∂circleMeasure) = 1 := by
  simp only [fejerKernel]
  rw [integral_div, integral_norm_sq_fourierPolynomial]
  simp only [fejerInterval, Int.card_Ico, sub_zero, Int.toNat_natCast]
  exact div_self (by exact_mod_cast hD.ne')

theorem norm_sq_fourierPolynomial_eq_indexed (A : Finset ℤ) (t : Circle) :
    (‖fourierPolynomial A t‖ ^ 2 : ℂ) =
      indexedFourierSum (A ×ˢ A) (fun p ↦ p.1 - p.2) t := by
  simp only [← Complex.mul_conj', fourierPolynomial, indexedFourierSum,
    map_sum, Finset.sum_product, Finset.sum_mul, Finset.mul_sum, ← fourier_neg,
    sub_eq_add_neg, fourier_add]
  exact Finset.sum_comm

theorem circleFourierCoeff_indexedFourierSum {ι : Type*} (S : Finset ι)
    (n : ι → ℤ) (k : ℤ) :
    circleFourierCoeff (indexedFourierSum S n) k = ((S.filter (fun i ↦ n i = k)).card : ℂ) := by
  classical
  unfold circleFourierCoeff indexedFourierSum
  simp only [Finset.sum_mul, ← fourier_add]
  rw [integral_finsetSum]
  · simp only [integral_fourier, add_neg_eq_zero, Finset.card_filter,
      Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  · intro i hi
    exact continuous_circle_integrable (fourier _).continuous

theorem circleFourierCoeff_fejerKernel (D : ℕ) (n : ℤ) :
    circleFourierCoeff (fun t ↦ (fejerKernel D t : ℂ)) n =
      (((D : ℤ) - |n|).toNat : ℂ) / (D : ℂ) := by
  have he (t : Circle) : (fejerKernel D t : ℂ) =
      indexedFourierSum ((fejerInterval D) ×ˢ (fejerInterval D))
        (fun p ↦ p.1 - p.2) t / (D : ℂ) := by
    simp only [fejerKernel, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast]
    rw [norm_sq_fourierPolynomial_eq_indexed]
  simp only [circleFourierCoeff, he, div_mul_eq_mul_div, integral_div]
  change circleFourierCoeff (indexedFourierSum _ _) n / (D : ℂ) = _
  rw [circleFourierCoeff_indexedFourierSum]
  change (intervalDifferenceCount D n : ℂ) / (D : ℂ) = _
  rw [intervalDifferenceCount_eq]

theorem circleFourierCoeff_const_mul (c : ℂ) (f : Circle → ℂ) (n : ℤ) :
    circleFourierCoeff (fun t ↦ c * f t) n = c * circleFourierCoeff f n := by
  simp only [circleFourierCoeff, mul_assoc, integral_const_mul]

theorem circleFourierCoeff_sub {f g : Circle → ℂ}
    (hf : Integrable f circleMeasure) (hg : Integrable g circleMeasure) (n : ℤ) :
    circleFourierCoeff (fun t ↦ f t - g t) n =
      circleFourierCoeff f n - circleFourierCoeff g n := by
  simp only [circleFourierCoeff, sub_mul]
  exact integral_sub (integrable_mul_fourier hf _) (integrable_mul_fourier hg _)

noncomputable def valleePoussinKernel (D : ℕ) (t : Circle) : ℝ :=
  2 * fejerKernel (2 * D) t - fejerKernel D t

theorem valleePoussinKernel_continuous (D : ℕ) : Continuous (valleePoussinKernel D) :=
  (continuous_const.mul (fejerKernel_continuous _)).sub (fejerKernel_continuous _)

theorem circleFourierCoeff_valleePoussinKernel (D : ℕ) (n : ℤ) :
    circleFourierCoeff (fun t ↦ (valleePoussinKernel D t : ℂ)) n =
      2 * ((((2 * D : ℕ) : ℤ) - |n|).toNat : ℂ) / ((2 * D : ℕ) : ℂ) -
        (((D : ℤ) - |n|).toNat : ℂ) / (D : ℂ) := by
  have h2 : Integrable (fun t ↦ (2 : ℂ) * (fejerKernel (2 * D) t : ℂ)) circleMeasure :=
    continuous_circle_integrable (continuous_const.mul
      (Complex.continuous_ofReal.comp (fejerKernel_continuous _)))
  have h1 : Integrable (fun t ↦ (fejerKernel D t : ℂ)) circleMeasure :=
    continuous_circle_integrable (Complex.continuous_ofReal.comp (fejerKernel_continuous _))
  simp only [valleePoussinKernel, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  rw [circleFourierCoeff_sub h2 h1, circleFourierCoeff_const_mul,
    circleFourierCoeff_fejerKernel, circleFourierCoeff_fejerKernel]
  ring

theorem valleePoussinKernel_reproduces {D : ℕ} (hD : 0 < D) {n : ℤ}
    (hn : |n| ≤ (D : ℤ)) :
    circleFourierCoeff (fun t ↦ (valleePoussinKernel D t : ℂ)) n = 1 := by
  have hn1 : 0 ≤ (D : ℤ) - |n| := by omega
  have hn2 : 0 ≤ ((2 * D : ℕ) : ℤ) - |n| := by omega
  have hcast1 : (((D : ℤ) - |n|).toNat : ℂ) = (D : ℂ) - (|n| : ℤ) := by
    exact_mod_cast Int.toNat_of_nonneg hn1
  have hcast2 : (((((2 * D : ℕ) : ℤ) - |n|).toNat) : ℂ) =
      (2 * (D : ℂ)) - (|n| : ℤ) := by
    exact_mod_cast Int.toNat_of_nonneg hn2
  rw [circleFourierCoeff_valleePoussinKernel, hcast1, hcast2]
  push_cast
  have hd : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  field_simp
  ring

theorem valleePoussinKernel_support {D : ℕ} {n : ℤ} (hn : (2 * D : ℤ) ≤ |n|) :
    circleFourierCoeff (fun t ↦ (valleePoussinKernel D t : ℂ)) n = 0 := by
  rw [circleFourierCoeff_valleePoussinKernel]
  have h1 : ((D : ℤ) - |n|).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
  have h2 : ((((2 * D : ℕ) : ℤ) - |n|).toNat) = 0 := Int.toNat_eq_zero.mpr (by omega)
  rw [h1, h2]
  norm_num

theorem integral_norm_valleePoussinKernel_le {D : ℕ} (hD : 0 < D) :
    (∫ t, ‖valleePoussinKernel D t‖ ∂circleMeasure) ≤ 3 := by
  have hb (t : Circle) : ‖valleePoussinKernel D t‖ ≤
      2 * fejerKernel (2 * D) t + fejerKernel D t := by
    calc
      ‖valleePoussinKernel D t‖ ≤ ‖2 * fejerKernel (2 * D) t‖ + ‖fejerKernel D t‖ :=
        norm_sub_le _ _
      _ = _ := by simp [norm_mul, Real.norm_eq_abs, abs_of_nonneg (fejerKernel_nonneg _ _)]
  have h1 := continuous_circle_integrable (fejerKernel_continuous D)
  have h2 := continuous_circle_integrable (fejerKernel_continuous (2 * D))
  calc
    _ ≤ ∫ t, 2 * fejerKernel (2 * D) t + fejerKernel D t ∂circleMeasure :=
      integral_mono (continuous_circle_integrable (valleePoussinKernel_continuous D).norm)
        ((h2.const_mul 2).add h1) hb
    _ = 3 := by
      rw [integral_add (h2.const_mul 2) h1, integral_const_mul,
        integral_fejerKernel (by omega : 0 < 2 * D), integral_fejerKernel hD]
      norm_num

end LittlewoodInverse
