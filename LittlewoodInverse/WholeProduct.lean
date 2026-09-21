import LittlewoodInverse.ScalarCoupling

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LittlewoodInverse
namespace WholeProduct

variable {α : Type*}

noncomputable def crossTerm {n : ℕ} (a : ℝ) (u : Fin n → α → ℝ) (x : α) : ℝ :=
  ((∑ j, OuterAlgebra.q a (u j x))^2 - ∑ j, OuterAlgebra.q a (u j x)^2) / 2

theorem pointwise_bonferroni {n : ℕ} {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (u : Fin n → α → ℝ) (x : α) (hu : ∀ j, 0 ≤ u j x ∧ u j x ≤ 1) :
    (∏ j, (1 - OuterAlgebra.q a (u j x))) ≤
      1 - (∑ j, OuterAlgebra.q a (u j x)) + crossTerm a u x := by
  have h := OuterAlgebra.bonferroni_two (List.ofFn (fun j => OuterAlgebra.q a (u j x))) (by
    intro q hq
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
    exact OuterAlgebra.q_mem_Icc ha0 ha1 (hu j).1 (hu j).2)
  simpa [OuterAlgebra.pairProducts_eq_half, List.map_ofFn, List.sum_ofFn,
    List.prod_ofFn, crossTerm] using h

theorem product_modulus {n : ℕ} (a : ℝ) (M : Fin n → α → ℂ) (u : Fin n → α → ℝ)
    (hmod : ∀ j x, ‖M j x‖ = 1 - a * u j x) (x : α) :
    ‖∏ j, M j x‖^2 = ∏ j, (1 - OuterAlgebra.q a (u j x)) := by
  rw [norm_prod, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro j _
  rw [hmod, OuterAlgebra.q_eq_one_sub_sq]
  ring

theorem norm_sub_one_sq (z : ℂ) : ‖z - 1‖^2 = ‖z‖^2 + 1 - 2 * z.re := by
  have hz := Complex.sq_norm_sub_sq_re z
  have hw := Complex.sq_norm_sub_sq_re (z - 1)
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at hw
  nlinarith

variable [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

theorem integral_error_identity (P : α → ℂ) (hp : Integrable P μ)
    (hpsq : Integrable (fun x => ‖P x‖^2) μ) :
    (∫ x, ‖P x - 1‖^2 ∂μ) = (∫ x, ‖P x‖^2 ∂μ) + 1 - 2 * (∫ x, P x ∂μ).re := by
  simp_rw [norm_sub_one_sq]
  have hadd : Integrable (fun x => ‖P x‖^2 + 1) μ := hpsq.add (integrable_const 1)
  have hre : Integrable (fun x => 2 * (P x).re) μ := hp.re.const_mul 2
  have hr : (∫ x, (P x).re ∂μ) = (∫ x, P x ∂μ).re := by
    simpa only [RCLike.re_eq_complex_re] using integral_re hp
  rw [integral_sub hadd hre, integral_add hpsq (integrable_const 1),
    integral_const_mul, hr]
  simp

/-- Whole-product estimate using exactly the modulus and mean supplied by outer
multipliers. Integrability assumptions state the analytic domain explicitly;
the resulting L2 error estimate is proved, not an input. The cross term is the
sum over unordered distinct pairs, written by the equivalent square identity. -/
theorem estimate {n : ℕ} {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (P : α → ℂ) (u : Fin n → α → ℝ)
    (hu : ∀ᵐ x ∂μ, ∀ j, 0 ≤ u j x ∧ u j x ≤ 1)
    (hp : Integrable P μ) (hpsq : Integrable (fun x => ‖P x‖^2) μ)
    (hq : ∀ j, Integrable (fun x => OuterAlgebra.q a (u j x)) μ)
    (hlog : ∀ j, Integrable (fun x => Real.log (1 - a * u j x)) μ)
    (hcross : Integrable (crossTerm a u) μ)
    (hmod : ∀ᵐ x ∂μ, ‖P x‖^2 = ∏ j, (1 - OuterAlgebra.q a (u j x)))
    (hmean : (∫ x, P x ∂μ) =
      (Real.exp (∑ j, ∫ x, Real.log (1 - a * u j x) ∂μ) : ℂ)) :
    (∫ x, ‖P x - 1‖^2 ∂μ) ≤
      (∑ j, ∫ x, ScalarCoupling.h a (u j x) ∂μ) + ∫ x, crossTerm a u x ∂μ := by
  have hqsum : Integrable (fun x => ∑ j, OuterAlgebra.q a (u j x)) μ :=
    integrable_finsetSum _ (fun j _ => hq j)
  have hright : Integrable (fun x => 1 - (∑ j, OuterAlgebra.q a (u j x)) +
      crossTerm a u x) μ := ((integrable_const 1).sub hqsum).add hcross
  have hbon := integral_mono_ae hpsq hright (by
    filter_upwards [hu, hmod] with x hux hmx
    rw [hmx]
    exact pointwise_bonferroni ha0 ha1 u x hux)
  have hsub : Integrable (fun x => 1 - ∑ j, OuterAlgebra.q a (u j x)) μ :=
    (integrable_const 1).sub hqsum
  rw [integral_add hsub hcross,
    integral_sub (integrable_const 1) hqsum,
    integral_finsetSum _ (fun j _ => hq j)] at hbon
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hbon
  rw [integral_error_identity P hp hpsq, hmean, Complex.ofReal_re]
  have hred := OuterAlgebra.whole_product_reduction (∫ x, ‖P x‖^2 ∂μ)
    (-(∑ j, ∫ x, Real.log (1 - a * u j x) ∂μ))
    (∑ j, ∫ x, OuterAlgebra.q a (u j x) ∂μ) (∫ x, crossTerm a u x ∂μ) hbon
  simp only [neg_neg] at hred
  calc
    _ ≤ 2 * (-(∑ j, ∫ x, Real.log (1 - a * u j x) ∂μ)) -
        (∑ j, ∫ x, OuterAlgebra.q a (u j x) ∂μ) + ∫ x, crossTerm a u x ∂μ := hred
    _ = _ := by
      have hh (j : Fin n) : (∫ x, ScalarCoupling.h a (u j x) ∂μ) =
          -(∫ x, OuterAlgebra.q a (u j x) ∂μ) -
            2 * (∫ x, Real.log (1 - a * u j x) ∂μ) := by
        have heq : (fun x => ScalarCoupling.h a (u j x)) =
            (fun x => -OuterAlgebra.q a (u j x) - 2 * Real.log (1 - a * u j x)) := by
          funext x
          unfold ScalarCoupling.h OuterAlgebra.q
          ring
        have hiq : Integrable (fun x => -OuterAlgebra.q a (u j x)) μ := (hq j).neg
        have hil : Integrable (fun x => 2 * Real.log (1 - a * u j x)) μ := (hlog j).const_mul 2
        rw [heq, integral_sub hiq hil,
          integral_neg, integral_const_mul]
      simp_rw [hh]
      rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
      ring

end WholeProduct
end LittlewoodInverse
