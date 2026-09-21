import LittlewoodInverse.WholeProduct
import LittlewoodInverse.OuterDamping

open scoped BigOperators
open MeasureTheory

namespace LittlewoodInverse

theorem integral_mul_le_sqrt_moments (f g : Circle → ℝ) (hf : Continuous f) (hg : Continuous g) :
    (∫ t, f t * g t ∂circleMeasure) ≤
      Real.sqrt (∫ t, f t ^ 2 ∂circleMeasure) * Real.sqrt (∫ t, g t ^ 2 ∂circleMeasure) := by
  have hc := integral_cauchy_schwarz_sq
    (continuous_circle_integrable (hf.pow 2)) (continuous_circle_integrable (hf.mul hg))
    (continuous_circle_integrable (hg.pow 2))
  have hF : 0 ≤ ∫ t, f t ^ 2 ∂circleMeasure := integral_nonneg fun _ => sq_nonneg _
  have hG : 0 ≤ ∫ t, g t ^ 2 ∂circleMeasure := integral_nonneg fun _ => sq_nonneg _
  have hs : (Real.sqrt (∫ t, f t ^ 2 ∂circleMeasure) *
      Real.sqrt (∫ t, g t ^ 2 ∂circleMeasure)) ^ 2 =
      (∫ t, f t ^ 2 ∂circleMeasure) * (∫ t, g t ^ 2 ∂circleMeasure) := by
    rw [mul_pow, Real.sq_sqrt hF, Real.sq_sqrt hG]
  nlinarith [mul_nonneg (Real.sqrt_nonneg (∫ t, f t ^ 2 ∂circleMeasure))
    (Real.sqrt_nonneg (∫ t, g t ^ 2 ∂circleMeasure))]

theorem integral_sum_sq_le {n : ℕ} (f : Fin n → Circle → ℝ) (hf : ∀ i, Continuous (f i)) :
    (∫ t, (∑ i, f i t) ^ 2 ∂circleMeasure) ≤
      (∑ i, Real.sqrt (∫ t, f i t ^ 2 ∂circleMeasure)) ^ 2 := by
  have hexp (t : Circle) : (∑ i, f i t)^2 = ∑ i, ∑ j, f i t * f j t := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun i _ => continuous_circle_integrable (by fun_prop))]
  have hi (i : Fin n) : (∫ t, ∑ j, f i t * f j t ∂circleMeasure) =
      ∑ j, ∫ t, f i t * f j t ∂circleMeasure :=
    integral_finsetSum _ (fun j _ => continuous_circle_integrable ((hf i).mul (hf j)))
  simp_rw [hi]
  rw [pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    integral_mul_le_sqrt_moments (f i) (f j) (hf i) (hf j)

theorem integral_crossTerm_le {n : ℕ} (a : ℝ) (u : Fin n → Circle → ℝ)
    (hu : ∀ i, Continuous (u i)) :
    (∫ t, WholeProduct.crossTerm a u t ∂circleMeasure) ≤
      ((∑ i, Real.sqrt (∫ t, OuterAlgebra.q a (u i t)^2 ∂circleMeasure))^2 -
        ∑ i, ∫ t, OuterAlgebra.q a (u i t)^2 ∂circleMeasure) / 2 := by
  have hq (i : Fin n) : Continuous (fun t => OuterAlgebra.q a (u i t)) := by
    unfold OuterAlgebra.q
    fun_prop
  unfold WholeProduct.crossTerm
  rw [integral_div, integral_sub (continuous_circle_integrable (by fun_prop))
    (continuous_circle_integrable (by fun_prop)),
    integral_finsetSum _ (fun i _ => continuous_circle_integrable (by fun_prop))]
  have hs := integral_sum_sq_le (fun i t => OuterAlgebra.q a (u i t)) hq
  linarith

/-- The full analytic coupling (4.16), with continuous modulus data and an
actual L² product. The modulus and mean are supplied by outer multipliers. -/
theorem coupled_whole_product {n : ℕ} {a V : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (P : Circle → ℂ) (hP : MemLp P 2 circleMeasure)
    (u : Fin n → Circle → ℝ) (hu : ∀ i, Continuous (u i))
    (hui : ∀ i t, 0 ≤ u i t ∧ u i t ≤ 1)
    (v : Fin n → ℝ) (hv : ∀ i, 0 < v i) (hV : ∑ i, v i ≤ V)
    (hmod : ∀ᵐ t ∂circleMeasure, ‖P t‖^2 = ∏ i, (1 - OuterAlgebra.q a (u i t)))
    (hmean : (∫ t, P t ∂circleMeasure) =
      (Real.exp (∑ i, ∫ t, Real.log (1 - a * u i t) ∂circleMeasure) : ℂ)) :
    (∫ t, ‖P t - 1‖^2 ∂circleMeasure) ≤
      ∑ i, ∫ t, ScalarCoupling.h a (u i t) +
        ((V / v i - 1) / 2) * OuterAlgebra.q a (u i t)^2 ∂circleMeasure := by
  have hq (i : Fin n) : Continuous (fun t => OuterAlgebra.q a (u i t)) := by
    unfold OuterAlgebra.q
    fun_prop
  have hlog (i : Fin n) : Continuous (fun t => Real.log (1 - a * u i t)) := by
    apply Continuous.log (by fun_prop)
    intro t
    have hx := hui i t
    nlinarith
  have hh (i : Fin n) : Continuous (fun t => ScalarCoupling.h a (u i t)) := by
    unfold ScalarCoupling.h
    fun_prop
  have hcross : Continuous (WholeProduct.crossTerm a u) := by
    unfold WholeProduct.crossTerm
    fun_prop
  have hest := WholeProduct.estimate ha0 ha1.le P u
    (Filter.Eventually.of_forall (fun t i => hui i t))
    (hP.integrable (by norm_num)) hP.integrable_norm_pow'
    (fun i => continuous_circle_integrable (hq i))
    (fun i => continuous_circle_integrable (hlog i))
    (continuous_circle_integrable hcross) hmod hmean
  have hc := OuterAlgebra.coupled_tail Finset.univ (fun _ : Fin n => (1 : ℝ)) v
    (fun i => ∫ t, ScalarCoupling.h a (u i t) ∂circleMeasure)
    (fun i => ∫ t, OuterAlgebra.q a (u i t)^2 ∂circleMeasure) V
    (fun i _ => hv i) (fun i _ => integral_nonneg fun _ => sq_nonneg _) hV
  simp only [one_pow, one_mul] at hc
  have hcrossbound := integral_crossTerm_le a u hu
  calc
    _ ≤ (∑ i, ∫ t, ScalarCoupling.h a (u i t) ∂circleMeasure) +
        (((∑ i, Real.sqrt (∫ t, OuterAlgebra.q a (u i t)^2 ∂circleMeasure))^2 -
          ∑ i, ∫ t, OuterAlgebra.q a (u i t)^2 ∂circleMeasure) / 2) := by linarith
    _ ≤ ∑ i, ((∫ t, ScalarCoupling.h a (u i t) ∂circleMeasure) +
        ((V / v i - 1) / 2) * (∫ t, OuterAlgebra.q a (u i t)^2 ∂circleMeasure)) := hc
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_add (continuous_circle_integrable (hh i))
        (continuous_circle_integrable (by fun_prop)), integral_const_mul]

/-- Specialization to an actual finite family of outer multipliers: their
product modulus, mean, and integrability are all discharged here. -/
theorem outer_product_coupled {n : ℕ} {a V : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (u : Fin n → Circle → ℝ) (hu : ∀ i, Continuous (u i))
    (hui : ∀ i t, 0 ≤ u i t ∧ u i t ≤ 1)
    (M : Fin n → Circle → ℂ) (hM : ∀ i, MemLp (M i) ⊤ circleMeasure)
    (hS : ∀ i, NonpositiveFourierSupport (M i))
    (hmod : ∀ i, ∀ᵐ t ∂circleMeasure, ‖M i t‖ = 1 - a * u i t)
    (hzero : ∀ i, circleFourierCoeff (M i) 0 =
      (Real.exp (∫ t, Real.log (1 - a * u i t) ∂circleMeasure) : ℂ))
    (v : Fin n → ℝ) (hv : ∀ i, 0 < v i) (hV : ∑ i, v i ≤ V) :
    (∫ t, ‖(∏ i, M i t) - 1‖^2 ∂circleMeasure) ≤
      ∑ i, ∫ t, ScalarCoupling.h a (u i t) +
        ((V / v i - 1) / 2) * OuterAlgebra.q a (u i t)^2 ∂circleMeasure := by
  apply coupled_whole_product ha0 ha1 (fun t => ∏ i, M i t)
    ((memLp_finset_prod_top Finset.univ (fun i _ => hM i)).mono_exponent le_top)
    u hu hui v hv hV
  · have hall : ∀ᵐ t ∂circleMeasure, ∀ i, ‖M i t‖ = 1 - a * u i t :=
      (ae_all_iff).mpr hmod
    filter_upwards [hall] with t ht
    rw [norm_prod, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    rw [ht, OuterAlgebra.q_eq_one_sub_sq]
    ring
  · rw [finite_product_mean_eq_prod_zeroCoeff Finset.univ (fun i _ => hM i) (fun i _ => hS i)]
    simp_rw [hzero]
    rw [← Complex.ofReal_prod, ← Real.exp_sum]

end LittlewoodInverse
