import LittlewoodInverse.OuterFamily
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators
open MeasureTheory
set_option maxHeartbeats 800000

namespace LittlewoodInverse

noncomputable def dampingTail {n : ℕ} (M : Fin n → Circle → ℂ)
    (i : Fin n) (t : Circle) : ℂ := ∏ j ∈ Finset.univ.filter (i < ·), M j t

noncomputable def dampedTest {n : ℕ} (a : ℝ) (f M : Fin n → Circle → ℂ)
    (t : Circle) : ℂ := ∑ i, (a : ℂ) * (f i t * dampingTail M i t)

theorem dampedTest_norm_le {n : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (f M : Fin n → Circle → ℂ) (t : Circle)
    (hm : ∀ i, ‖M i t‖ = 1 - a * ‖f i t‖) : ‖dampedTest a f M t‖ ≤ 1 := by
  have ht : (∏ i : Fin n, (1 - a * ‖f i t‖)) =
      1 - ∑ i : Fin n, a * ‖f i t‖ *
        ∏ j ∈ Finset.univ.filter (i < ·), (1 - a * ‖f j t‖) := by
    exact @Finset.prod_one_sub_ordered (OrderDual (Fin n)) ℝ _ _
      Finset.univ (fun i => a * ‖f i t‖)
  have hp : 0 ≤ ∏ i : Fin n, (1 - a * ‖f i t‖) := by
    apply Finset.prod_nonneg
    intro i _
    rw [← hm]
    exact norm_nonneg _
  calc
    _ ≤ ∑ i : Fin n, ‖(a : ℂ) * (f i t * dampingTail M i t)‖ := norm_sum_le _ _
    _ = ∑ i : Fin n, a * ‖f i t‖ *
        ∏ j ∈ Finset.univ.filter (i < ·), (1 - a * ‖f j t‖) := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha,
        dampingTail, norm_prod, hm, mul_assoc]
    _ ≤ 1 := by linarith

theorem dampingTail_memLp {n : ℕ} (M : Fin n → Circle → ℂ)
    (hM : ∀ i, MemLp (M i) ⊤ circleMeasure) (i : Fin n) :
    MemLp (dampingTail M i) ⊤ circleMeasure :=
  memLp_finset_prod_top _ (fun j _ => hM j)

theorem dampingTail_support {n : ℕ} (M : Fin n → Circle → ℂ)
    (hM : ∀ i, MemLp (M i) ⊤ circleMeasure)
    (hs : ∀ i, NonpositiveFourierSupport (M i)) (i : Fin n) :
    NonpositiveFourierSupport (dampingTail M i) :=
  (finite_product_nonpositive_support_mean _ (fun j _ => hM j) (fun j _ => hs j)).1

theorem circlePairing_norm_le_littlewoodNorm (A : Finset ℤ) {G : Circle → ℂ}
    (hG : MemLp G ⊤ circleMeasure) (hbound : ∀ᵐ t ∂circleMeasure, ‖G t‖ ≤ 1) :
    ‖circlePairing (fourierPolynomial A) G‖ ≤ littlewoodNorm A := by
  have hF : MemLp (fourierPolynomial A) ⊤ circleMeasure :=
    (fourierPolynomial_continuous A).memLp_top_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) circleMeasure
  have hi : Integrable (fun t => ‖fourierPolynomial A t‖ * ‖G t‖) circleMeasure :=
    (hG.norm.mul' hF.norm : MemLp _ ⊤ circleMeasure).integrable le_top
  calc
    _ ≤ ∫ t, ‖fourierPolynomial A t‖ * ‖G t‖ ∂circleMeasure := by
      simpa only [circlePairing, norm_mul, norm_star] using
        norm_integral_le_integral_norm (fun t => fourierPolynomial A t * star (G t))
          (μ := circleMeasure)
    _ ≤ littlewoodNorm A := by
      apply integral_mono_ae hi (fourierPolynomial_integrable A).norm
      filter_upwards [hbound] with t ht
      simpa only [mul_one] using mul_le_mul_of_nonneg_left ht (norm_nonneg _)

/-- The bounded-test construction with every tail pairing exposed. -/
theorem dampedTest_lower_bound {n : ℕ} {a c : ℝ} (ha : 0 ≤ a)
    (A : Finset ℤ) (f M : Fin n → Circle → ℂ)
    (hf : ∀ i, MemLp (f i) ⊤ circleMeasure)
    (hM : ∀ i, MemLp (M i) ⊤ circleMeasure)
    (hm : ∀ i, ∀ᵐ t ∂circleMeasure, ‖M i t‖ = 1 - a * ‖f i t‖)
    (hc : ∀ i, c ≤ (circlePairing (fourierPolynomial A)
      (fun t => f i t * dampingTail M i t)).re) :
    a * (n : ℝ) * c ≤ littlewoodNorm A := by
  have hterm (i : Fin n) : MemLp (fun t => f i t * dampingTail M i t) ⊤ circleMeasure :=
    (dampingTail_memLp M hM i).mul' (hf i)
  have htest : MemLp (dampedTest a f M) ⊤ circleMeasure := by
    apply memLp_finsetSum
    intro i _
    exact (hterm i).const_mul (a : ℂ)
  have hb : ∀ᵐ t ∂circleMeasure, ‖dampedTest a f M t‖ ≤ 1 := by
    have hall := (ae_all_iff.mpr hm)
    filter_upwards [hall] with t ht
    exact dampedTest_norm_le ha f M t ht
  have hFi : MemLp (fourierPolynomial A) ⊤ circleMeasure :=
    (fourierPolynomial_continuous A).memLp_top_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) circleMeasure
  have he : circlePairing (fourierPolynomial A) (dampedTest a f M) =
      (a : ℂ) * ∑ i, circlePairing (fourierPolynomial A)
        (fun t => f i t * dampingTail M i t) := by
    have hpoint (i : Fin n) (t : Circle) :
        fourierPolynomial A t * star ((a : ℂ) * (f i t * dampingTail M i t)) =
        (a : ℂ) * (fourierPolynomial A t * star (f i t * dampingTail M i t)) := by
      simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
      ring
    unfold circlePairing dampedTest
    simp only [star_sum, Finset.mul_sum, hpoint]
    rw [integral_finsetSum]
    · simp only [integral_const_mul]
    · intro i _
      exact (((hterm i).star.mul' hFi : MemLp _ ⊤ circleMeasure).const_mul
        (a : ℂ)).integrable le_top
  calc
    _ = a * ∑ _i : Fin n, c := by simp; ring
    _ ≤ a * ∑ i, (circlePairing (fourierPolynomial A)
        (fun t => f i t * dampingTail M i t)).re :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hc i) ha
    _ = (circlePairing (fourierPolynomial A) (dampedTest a f M)).re := by
      rw [he]; simp
    _ ≤ ‖circlePairing (fourierPolynomial A) (dampedTest a f M)‖ := Complex.re_le_norm _
    _ ≤ _ := circlePairing_norm_le_littlewoodNorm A htest hb

end LittlewoodInverse
