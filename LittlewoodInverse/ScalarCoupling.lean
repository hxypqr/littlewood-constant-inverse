import LittlewoodInverse.OuterAlgebra
import LittlewoodInverse.Fourier

open scoped BigOperators
open MeasureTheory

namespace LittlewoodInverse
namespace ScalarCoupling

/-!
The scalar inequality is proved directly from the logarithmic power series.
Its cubic-tail comparison is equivalent to the endpoint chord bound for the
convex function in the manuscript, but avoids division by a variable at zero.
-/

noncomputable def logRemainder (y : ℝ) : ℝ :=
  -Real.log (1 - y) - y - y ^ 2 / 2

theorem hasSum_logRemainder {y : ℝ} (hy : |y| < 1) :
    HasSum (fun n : ℕ => y ^ (n + 3) / ((n : ℝ) + 3)) (logRemainder y) := by
  have htail := (hasSum_nat_add_iff' 2).mpr
    (Real.hasSum_pow_div_log_of_abs_lt_one hy)
  have htail' : HasSum (fun n : ℕ => y ^ (n + 3) / ((n : ℝ) + 3))
      (-Real.log (1 - y) - ∑ i ∈ Finset.range 2, y ^ (i + 1) / ((i : ℝ) + 1)) := by
    apply htail.congr_fun
    intro n
    simp only [Nat.cast_add, Nat.cast_ofNat, Nat.add_assoc]
    ring_nf
  have htotal : (-Real.log (1 - y) -
      ∑ i ∈ Finset.range 2, y ^ (i + 1) / ((i : ℝ) + 1)) = logRemainder y := by
    norm_num [logRemainder, Finset.sum_range_succ]
    ring
  rw [htotal] at htail'
  exact htail'

/-- The tail of the logarithmic series after its linear and quadratic
terms contracts cubically on the unit interval. -/
theorem logRemainder_mul_le {a x : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    logRemainder (a * x) ≤ x ^ 3 * logRemainder a := by
  have hax0 : 0 ≤ a * x := mul_nonneg ha0 hx0
  have haxa : a * x ≤ a := by nlinarith
  have hax1 : |a * x| < 1 := by rw [abs_of_nonneg hax0]; exact haxa.trans_lt ha1
  have haabs : |a| < 1 := by rwa [abs_of_nonneg ha0]
  apply hasSum_le _ (hasSum_logRemainder hax1)
    ((hasSum_logRemainder haabs).mul_left (x ^ 3))
  intro n
  have hpow : x ^ (n + 3) ≤ x ^ 3 :=
    pow_le_pow_of_le_one hx0 hx1 (by omega)
  rw [mul_pow]
  calc
    _ ≤ a ^ (n + 3) * x ^ 3 / ((n : ℝ) + 3) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hpow (pow_nonneg ha0 _)
    _ = x ^ 3 * (a ^ (n + 3) / ((n : ℝ) + 3)) := by ring

/-- The scalar function h from (4.8). -/
noncomputable def h (a x : ℝ) : ℝ :=
  a ^ 2 * x ^ 2 - 2 * a * x - 2 * Real.log (1 - a * x)

theorem h_eq_remainder (a x : ℝ) :
    h a x = 2 * a ^ 2 * x ^ 2 + 2 * logRemainder (a * x) := by
  unfold h logRemainder
  ring

theorem h_cubic_majorant {a x : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    h a x ≤ 2 * a ^ 2 * x ^ 2 + 2 * logRemainder a * x ^ 3 := by
  rw [h_eq_remainder]
  have htail := logRemainder_mul_le ha0 ha1 hx0 hx1
  nlinarith

/-- The full pointwise large-weight scalar inequality used to prove
Lemma 4.4, including its logarithmic term and the endpoint x = 0. -/
theorem scalar_large_b_pointwise (b x : ℝ) (hb : (11 / 8 : ℝ) ≤ b)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    h (9 / 10) x + b * OuterAlgebra.q (9 / 10) x ^ 2 ≤
      (2 + 4 * b) * (9 / 10 : ℝ) ^ 2 * x ^ 2 := by
  have hb0 : 0 ≤ b := by linarith
  have hh := h_cubic_majorant (by norm_num : (0 : ℝ) ≤ 9 / 10)
    (by norm_num : (9 / 10 : ℝ) < 1) hx0 hx1
  have hend := OuterAlgebra.scalar_endpoint_negative b hb
  have hend' : 2 * logRemainder (9 / 10) -
      b * (4 * (9 / 10 : ℝ) ^ 3 - (9 / 10 : ℝ) ^ 4) ≤ 0 := by
    unfold logRemainder
    nlinarith
  have hxpow : x ^ 4 ≤ x ^ 3 := pow_le_pow_of_le_one hx0 hx1 (by omega)
  have hfour := mul_le_mul_of_nonneg_left hxpow
    (mul_nonneg hb0 (pow_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 10) 4))
  have hthree := mul_nonpos_of_nonpos_of_nonneg hend' (pow_nonneg hx0 3)
  unfold OuterAlgebra.q
  nlinarith

/-- The normalized absolute exponential sum used in the manuscript. -/
noncomputable def normalizedMagnitude (A : Finset ℤ) (t : Circle) : ℝ :=
  ‖fourierPolynomial A t‖ / (A.card : ℝ)

theorem normalizedMagnitude_continuous (A : Finset ℤ) :
    Continuous (normalizedMagnitude A) :=
  (fourierPolynomial_continuous A).norm.div_const _

theorem normalizedMagnitude_nonneg (A : Finset ℤ) (t : Circle) :
    0 ≤ normalizedMagnitude A t := by
  unfold normalizedMagnitude
  positivity

theorem normalizedMagnitude_le_one (A : Finset ℤ) (hA : A.Nonempty) (t : Circle) :
    normalizedMagnitude A t ≤ 1 := by
  have hn : (0 : ℝ) < A.card := Nat.cast_pos.mpr hA.card_pos
  apply (div_le_iff₀ hn).mpr
  calc
    ‖fourierPolynomial A t‖ ≤ ∑ a ∈ A, ‖fourier a t‖ := norm_sum_le ..
    _ = 1 * (A.card : ℝ) := by simp [fourier_apply]

theorem normalized_second_moment (A : Finset ℤ) (hA : A.Nonempty) :
    (A.card : ℝ) * (∫ t, normalizedMagnitude A t ^ 2 ∂circleMeasure) = 1 := by
  have hn : (A.card : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hA.card_pos)
  unfold normalizedMagnitude
  simp_rw [div_pow]
  rw [integral_div, integral_norm_sq_fourierPolynomial]
  field_simp

/-- The finite, uniform part of the normalized moment comparison: every
integer moment of order at least two has normalized integral at most one. -/
theorem normalized_moment_le_one (A : Finset ℤ) (hA : A.Nonempty)
    (k : ℕ) (hk : 2 ≤ k) :
    (A.card : ℝ) * (∫ t, normalizedMagnitude A t ^ k ∂circleMeasure) ≤ 1 := by
  have hu := normalizedMagnitude_continuous A
  have hi := integral_mono (continuous_circle_integrable (hu.pow k))
    (continuous_circle_integrable (hu.pow 2)) (fun t =>
      pow_le_pow_of_le_one (normalizedMagnitude_nonneg A t)
        (normalizedMagnitude_le_one A hA t) hk)
  calc
    _ ≤ (A.card : ℝ) * (∫ t, normalizedMagnitude A t ^ 2 ∂circleMeasure) :=
      mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg _)
    _ = 1 := normalized_second_moment A hA

/-- The large-weight half of the manuscript's scalar coupling lemma,
for the actual exponential sum of every nonempty finite integer set. -/
theorem scalar_large_b_integral (A : Finset ℤ) (hA : A.Nonempty)
    (b : ℝ) (hb : (11 / 8 : ℝ) ≤ b) :
    (A.card : ℝ) * (∫ t, h (9 / 10) (normalizedMagnitude A t) +
      b * OuterAlgebra.q (9 / 10) (normalizedMagnitude A t) ^ 2 ∂circleMeasure) ≤
        (2 + 4 * b) * (9 / 10 : ℝ) ^ 2 := by
  have hu := normalizedMagnitude_continuous A
  have hlog : Continuous (fun t => Real.log (1 - (9 / 10 : ℝ) * normalizedMagnitude A t)) := by
    apply (continuous_const.sub (continuous_const.mul hu)).log
    intro t
    have hule := normalizedMagnitude_le_one A hA t
    have hpos : (0 : ℝ) < 1 - (9 / 10 : ℝ) * normalizedMagnitude A t := by linarith
    exact ne_of_gt hpos
  have hleft : Continuous (fun t => h (9 / 10) (normalizedMagnitude A t) +
      b * OuterAlgebra.q (9 / 10) (normalizedMagnitude A t) ^ 2) := by
    unfold h OuterAlgebra.q
    fun_prop
  have hright : Continuous (fun t =>
      ((2 + 4 * b) * (9 / 10 : ℝ) ^ 2) * normalizedMagnitude A t ^ 2) := by fun_prop
  have hi := integral_mono (continuous_circle_integrable hleft)
    (continuous_circle_integrable hright) (fun t =>
      scalar_large_b_pointwise b (normalizedMagnitude A t) hb
        (normalizedMagnitude_nonneg A t) (normalizedMagnitude_le_one A hA t))
  calc
    _ ≤ (A.card : ℝ) * (∫ t,
        ((2 + 4 * b) * (9 / 10 : ℝ) ^ 2) * normalizedMagnitude A t ^ 2 ∂circleMeasure) :=
      mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg _)
    _ = ((2 + 4 * b) * (9 / 10 : ℝ) ^ 2) *
        ((A.card : ℝ) * ∫ t, normalizedMagnitude A t ^ 2 ∂circleMeasure) := by
      rw [integral_const_mul]
      ring
    _ = _ := by rw [normalized_second_moment A hA, mul_one]

/-- The logarithmic series tail beginning at exponent five. -/
noncomputable def tailFromFive (y : ℝ) : ℝ :=
  -Real.log (1 - y) - y - y ^ 2 / 2 - y ^ 3 / 3 - y ^ 4 / 4

theorem hasSum_tailFromFive {y : ℝ} (hy : |y| < 1) :
    HasSum (fun n : ℕ => y ^ (n + 5) / ((n : ℝ) + 5)) (tailFromFive y) := by
  have htail := (hasSum_nat_add_iff' 4).mpr
    (Real.hasSum_pow_div_log_of_abs_lt_one hy)
  have htail' : HasSum (fun n : ℕ => y ^ (n + 5) / ((n : ℝ) + 5))
      (-Real.log (1 - y) - ∑ i ∈ Finset.range 4, y ^ (i + 1) / ((i : ℝ) + 1)) := by
    apply htail.congr_fun
    intro n
    simp only [Nat.cast_add, Nat.cast_ofNat, Nat.add_assoc]
    ring_nf
  have htotal : (-Real.log (1 - y) -
      ∑ i ∈ Finset.range 4, y ^ (i + 1) / ((i : ℝ) + 1)) = tailFromFive y := by
    norm_num [tailFromFive, Finset.sum_range_succ]
    ring
  rw [htotal] at htail'
  exact htail'

theorem tailFromFive_eq_tsum {y : ℝ} (hy : |y| < 1) :
    tailFromFive y = ∑' n : ℕ, y ^ (n + 5) / ((n : ℝ) + 5) :=
  (hasSum_tailFromFive hy).tsum_eq.symm

/-- Exact first-level scalar expansion before estimating its moments. -/
theorem first_level_exact (a x : ℝ) :
    h a x + (1 / 3 : ℝ) * OuterAlgebra.q a x ^ 2 =
      (10 * a ^ 2 / 3) * x ^ 2 - (2 * a ^ 3 / 3) * x ^ 3 +
        (5 * a ^ 4 / 6) * x ^ 4 + 2 * tailFromFive (a * x) := by
  unfold h OuterAlgebra.q tailFromFive
  ring

theorem first_level_pointwise_tail {a x : ℝ} (ha0 : 0 ≤ a)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    h a x + (1 / 3 : ℝ) * OuterAlgebra.q a x ^ 2 ≤
      (10 * a ^ 2 / 3) * x ^ 2 + (5 * a ^ 4 / 6 - 2 * a ^ 3 / 3) * x ^ 4 +
        2 * tailFromFive (a * x) := by
  rw [first_level_exact]
  have hxpow : x ^ 4 ≤ x ^ 3 := pow_le_pow_of_le_one hx0 hx1 (by omega)
  have hmul := mul_le_mul_of_nonneg_left hxpow (pow_nonneg ha0 3)
  nlinarith

/-- The nonconstant first-level majorant, with the genuine convergent
logarithmic tail.  The interval-moment asymptotic is not assumed here. -/
theorem first_level_pointwise {a x : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    h a x + (1 / 3 : ℝ) * OuterAlgebra.q a x ^ 2 ≤
      (10 * a ^ 2 / 3) * x ^ 2 + (5 * a ^ 4 / 6 - 2 * a ^ 3 / 3) * x ^ 4 +
        2 * ∑' n : ℕ, (a * x) ^ (n + 5) / ((n : ℝ) + 5) := by
  have haxa : a * x ≤ a := by nlinarith
  have hax0 : 0 ≤ a * x := mul_nonneg ha0 hx0
  have hax1 : |a * x| < 1 := by rw [abs_of_nonneg hax0]; exact haxa.trans_lt ha1
  rw [← tailFromFive_eq_tsum hax1]
  exact first_level_pointwise_tail ha0 hx0 hx1

/-- Integration of the actual first-level infinite series is justified
by a summable constant majorant on the probability circle. -/
theorem hasSum_integral_tail (A : Finset ℤ) (hA : A.Nonempty)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    HasSum (fun n : ℕ => a ^ (n + 5) / ((n : ℝ) + 5) *
      (∫ t, normalizedMagnitude A t ^ (n + 5) ∂circleMeasure))
      (∫ t, tailFromFive (a * normalizedMagnitude A t) ∂circleMeasure) := by
  have hu := normalizedMagnitude_continuous A
  have haabs : |a| < 1 := by rwa [abs_of_nonneg ha0]
  have hnorm (n : ℕ) (t : Circle) :
      ‖(a * normalizedMagnitude A t) ^ (n + 5) / ((n : ℝ) + 5)‖ ≤
        a ^ (n + 5) / ((n : ℝ) + 5) := by
    have hu0 := normalizedMagnitude_nonneg A t
    have hu1 := normalizedMagnitude_le_one A hA t
    have hax0 : 0 ≤ a * normalizedMagnitude A t := mul_nonneg ha0 hu0
    have haxa : a * normalizedMagnitude A t ≤ a := by nlinarith
    rw [Real.norm_of_nonneg (by positivity)]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hax0 haxa _) (by positivity)
  have hlim (t : Circle) : HasSum (fun n : ℕ =>
      (a * normalizedMagnitude A t) ^ (n + 5) / ((n : ℝ) + 5))
      (tailFromFive (a * normalizedMagnitude A t)) := by
    apply hasSum_tailFromFive
    have hu0 := normalizedMagnitude_nonneg A t
    have hu1 := normalizedMagnitude_le_one A hA t
    rw [abs_of_nonneg (mul_nonneg ha0 hu0)]
    nlinarith
  have hint := hasSum_integral_of_dominated_convergence
    (μ := circleMeasure)
    (fun (n : ℕ) (_ : Circle) => a ^ (n + 5) / ((n : ℝ) + 5))
    (fun n => (show Continuous (fun t : Circle =>
      (a * normalizedMagnitude A t) ^ (n + 5) / ((n : ℝ) + 5)) by fun_prop).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall (hnorm n))
    (Filter.Eventually.of_forall (fun _ => (hasSum_tailFromFive haabs).summable))
    (integrable_const _)
    (Filter.Eventually.of_forall hlim)
  apply hint.congr_fun
  intro n
  simp_rw [mul_pow]
  rw [integral_div, integral_const_mul]
  ring_nf

theorem normalized_integral_tail_eq_tsum (A : Finset ℤ) (hA : A.Nonempty)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    (A.card : ℝ) * (∫ t, tailFromFive (a * normalizedMagnitude A t) ∂circleMeasure) =
      ∑' n : ℕ, a ^ (n + 5) / ((n : ℝ) + 5) *
        ((A.card : ℝ) * ∫ t, normalizedMagnitude A t ^ (n + 5) ∂circleMeasure) := by
  have hint := (hasSum_integral_tail A hA ha0 ha1).mul_left (A.card : ℝ)
  have hint' : HasSum (fun n : ℕ => a ^ (n + 5) / ((n : ℝ) + 5) *
      ((A.card : ℝ) * ∫ t, normalizedMagnitude A t ^ (n + 5) ∂circleMeasure))
      ((A.card : ℝ) * ∫ t, tailFromFive (a * normalizedMagnitude A t) ∂circleMeasure) := by
    apply hint.congr_fun
    intro n
    ring_nf
  exact hint'.tsum_eq.symm

/-- The fully integrated first-level scalar majorant, in terms of actual
moments of the finite exponential sum.  Replacing these moments by the
asymptotic interval constants is a separate, still required theorem. -/
theorem first_level_integral (A : Finset ℤ) (hA : A.Nonempty)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    (A.card : ℝ) * (∫ t, h a (normalizedMagnitude A t) +
      (1 / 3 : ℝ) * OuterAlgebra.q a (normalizedMagnitude A t) ^ 2 ∂circleMeasure) ≤
        10 * a ^ 2 / 3 + (5 * a ^ 4 / 6 - 2 * a ^ 3 / 3) *
          ((A.card : ℝ) * ∫ t, normalizedMagnitude A t ^ 4 ∂circleMeasure) +
        2 * ∑' n : ℕ, a ^ (n + 5) / ((n : ℝ) + 5) *
          ((A.card : ℝ) * ∫ t, normalizedMagnitude A t ^ (n + 5) ∂circleMeasure) := by
  have hu := normalizedMagnitude_continuous A
  have hlog : Continuous (fun t => Real.log (1 - a * normalizedMagnitude A t)) := by
    apply (continuous_const.sub (continuous_const.mul hu)).log
    intro t
    have hu1 := normalizedMagnitude_le_one A hA t
    have haxa : a * normalizedMagnitude A t ≤ a := by nlinarith
    have hpos : 0 < 1 - a * normalizedMagnitude A t := by linarith
    exact ne_of_gt hpos
  have htail : Continuous (fun t => tailFromFive (a * normalizedMagnitude A t)) := by
    unfold tailFromFive
    fun_prop
  have hleft : Continuous (fun t => h a (normalizedMagnitude A t) +
      (1 / 3 : ℝ) * OuterAlgebra.q a (normalizedMagnitude A t) ^ 2) := by
    unfold h OuterAlgebra.q
    fun_prop
  have hint2 := (continuous_circle_integrable (hu.pow 2)).const_mul (10 * a ^ 2 / 3)
  have hint4 := (continuous_circle_integrable (hu.pow 4)).const_mul
    (5 * a ^ 4 / 6 - 2 * a ^ 3 / 3)
  have hinttail := (continuous_circle_integrable htail).const_mul 2
  have hi := integral_mono (continuous_circle_integrable hleft)
    ((hint2.add hint4).add hinttail) (fun t =>
      first_level_pointwise_tail ha0 (normalizedMagnitude_nonneg A t)
        (normalizedMagnitude_le_one A hA t))
  simp only [Pi.add_apply, Pi.pow_apply] at hi hint2 hint4
  have hint24 : Integrable (fun t => (10 * a ^ 2 / 3) * normalizedMagnitude A t ^ 2 +
      (5 * a ^ 4 / 6 - 2 * a ^ 3 / 3) * normalizedMagnitude A t ^ 4) circleMeasure :=
    hint2.add hint4
  rw [integral_add hint24 hinttail, integral_add hint2 hint4,
    integral_const_mul, integral_const_mul, integral_const_mul] at hi
  have hscaled := mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg A.card : (0 : ℝ) ≤ A.card)
  have hmoment := normalized_second_moment A hA
  rw [← normalized_integral_tail_eq_tsum A hA ha0 ha1]
  nlinarith

end ScalarCoupling
end LittlewoodInverse
