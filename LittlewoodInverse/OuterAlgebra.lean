import Mathlib

/-!
# Finite algebra for the outer-multiplier argument

This file proves the finite algebra and a conditional numerical conclusion in
Sections 4 and Appendix A.  In particular it does **not** assert that the
manuscript's infinite moment series satisfies its proposed upper bound.
-/

namespace LittlewoodInverse
namespace OuterAlgebra

/-- Sum of the products at two distinct positions in a list. -/
def pairProducts : List ℝ → ℝ
  | [] => 0
  | x :: xs => x * xs.sum + pairProducts xs

theorem pairProducts_nonneg (xs : List ℝ)
    (h : ∀ x ∈ xs, 0 ≤ x) : 0 ≤ pairProducts xs := by
  induction xs with
  | nil => simp [pairProducts]
  | cons x xs ih =>
    have hx : 0 ≤ x := h x (by simp)
    have hxs : ∀ y ∈ xs, 0 ≤ y := fun y hy => h y (by simp [hy])
    have hs : 0 ≤ xs.sum := List.sum_nonneg hxs
    exact add_nonneg (mul_nonneg hx hs) (ih hxs)

theorem pairProducts_eq_half (xs : List ℝ) :
    pairProducts xs = (xs.sum ^ 2 - (xs.map (fun x => x ^ 2)).sum) / 2 := by
  induction xs with
  | nil => simp [pairProducts]
  | cons x xs ih =>
    simp only [pairProducts, List.sum_cons, List.map_cons]
    rw [ih]
    ring

/-- The second Bonferroni inequality used in (4.11), for a finite list. -/
theorem bonferroni_two (qs : List ℝ)
    (h : ∀ q ∈ qs, 0 ≤ q ∧ q ≤ 1) :
    (qs.map (fun q => 1 - q)).prod ≤ 1 - qs.sum + pairProducts qs := by
  induction qs with
  | nil => simp [pairProducts]
  | cons q qs ih =>
    have hq : 0 ≤ q ∧ q ≤ 1 := h q (by simp)
    have hqs : ∀ r ∈ qs, 0 ≤ r ∧ r ≤ 1 := fun r hr => h r (by simp [hr])
    have hmul := mul_le_mul_of_nonneg_left (ih hqs) (sub_nonneg.mpr hq.2)
    have hp := pairProducts_nonneg qs (fun r hr => (hqs r hr).1)
    have hqp := mul_nonneg hq.1 hp
    simp only [List.map_cons, List.prod_cons, List.sum_cons, pairProducts]
    nlinarith

/-- The quadratic loss of squared modulus in (4.8). -/
def q (a x : ℝ) : ℝ := 2 * a * x - a ^ 2 * x ^ 2

theorem q_eq_one_sub_sq (a x : ℝ) : q a x = 1 - (1 - a * x) ^ 2 := by
  unfold q
  ring

theorem q_mem_Icc {a x : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ q a x ∧ q a x ≤ 1 := by
  have hax0 : 0 ≤ a * x := mul_nonneg ha0 hx0
  have hax1 : a * x ≤ 1 := by nlinarith [mul_nonneg ha0 (sub_nonneg.mpr hx1)]
  rw [q_eq_one_sub_sq]
  constructor <;> nlinarith [sq_nonneg (1 - a * x)]

/-- The exact pointwise update budget (4.4).  The existence and Fourier
support of the multiplier are independent analytic obligations. -/
theorem outer_update_bound (g m source : ℂ) (a : ℝ) (ha : 0 ≤ a)
    (hg : ‖g‖ ≤ 1) (hm : ‖m‖ = 1 - a * ‖source‖) :
    ‖g * m + (a : ℂ) * source‖ ≤ 1 := by
  calc
    _ ≤ ‖g * m‖ + ‖(a : ℂ) * source‖ := norm_add_le _ _
    _ = ‖g‖ * ‖m‖ + a * ‖source‖ := by
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
    _ ≤ ‖m‖ + a * ‖source‖ := by nlinarith [norm_nonneg m]
    _ = 1 := by rw [hm]; ring

/-- The only exponential inequality needed for the whole-product reduction. -/
theorem one_sub_exp_neg_le (s : ℝ) : 1 - Real.exp (-s) ≤ s := by
  have h := Real.add_one_le_exp (-s)
  linarith

/-- The algebraic reduction from the exact product identity (4.10) and
the integrated Bonferroni estimate to (4.9).  Its hypotheses retain the
analytic obligations rather than assuming their conclusion as an axiom. -/
theorem whole_product_reduction (modulusIntegral logLoss quadSum pairSum : ℝ)
    (hBonferroni : modulusIntegral ≤ 1 - quadSum + pairSum) :
    modulusIntegral + 1 - 2 * Real.exp (-logLoss) ≤
      2 * logLoss - quadSum + pairSum := by
  have h := one_sub_exp_neg_le logLoss
  linarith

/-- Weighted Cauchy--Schwarz with unused positive weights retained in the
total budget, exactly as in (4.15). -/
theorem weighted_cauchy {ι : Type*} (s : Finset ι) (w v Q : ι → ℝ) (V : ℝ)
    (hv : ∀ i ∈ s, 0 < v i) (hQ : ∀ i ∈ s, 0 ≤ Q i)
    (hV : ∑ i ∈ s, v i ≤ V) :
    (∑ i ∈ s, w i * Real.sqrt (Q i)) ^ 2 ≤
      V * ∑ i ∈ s, w i ^ 2 * Q i / v i := by
  have hg : ∀ i ∈ s, 0 ≤ w i ^ 2 * Q i / v i := by
    intro i hi
    exact div_nonneg (mul_nonneg (sq_nonneg _) (hQ i hi)) (hv i hi).le
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (fun i hi => (hv i hi).le) hg
    (r := fun i => w i * Real.sqrt (Q i)) (by
      intro i hi
      rw [mul_pow, Real.sq_sqrt (hQ i hi)]
      exact le_of_eq (by field_simp [ne_of_gt (hv i hi)]))
  exact hcs.trans (mul_le_mul_of_nonneg_right hV (Finset.sum_nonneg hg))

/-- The finite weighted coupling step (4.16), with the off-diagonal sum
written using the square of the full sum. -/
theorem coupled_tail {ι : Type*} (s : Finset ι) (w v D Q : ι → ℝ) (V : ℝ)
    (hv : ∀ i ∈ s, 0 < v i) (hQ : ∀ i ∈ s, 0 ≤ Q i)
    (hV : ∑ i ∈ s, v i ≤ V) :
    (∑ i ∈ s, w i ^ 2 * D i) +
        ((∑ i ∈ s, w i * Real.sqrt (Q i)) ^ 2 - ∑ i ∈ s, w i ^ 2 * Q i) / 2 ≤
      ∑ i ∈ s, w i ^ 2 * (D i + (V / v i - 1) / 2 * Q i) := by
  have hcs := weighted_cauchy s w v Q V hv hQ hV
  calc
    _ ≤ (∑ i ∈ s, w i ^ 2 * D i) +
        (V * (∑ i ∈ s, w i ^ 2 * Q i / v i) - ∑ i ∈ s, w i ^ 2 * Q i) / 2 := by
      linarith
    _ = _ := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- The expansion of the first-level polynomial part of the scalar majorant. -/
theorem first_level_expansion (a x : ℝ) :
    2 * a ^ 2 + 2 * a ^ 3 * x / 3 + a ^ 4 * x ^ 2 / 2 +
        (1 / 3 : ℝ) * (2 * a - a ^ 2 * x) ^ 2 =
      10 * a ^ 2 / 3 - 2 * a ^ 3 * x / 3 + 5 * a ^ 4 * x ^ 2 / 6 := by
  ring

/-- The replacement of the negative linear term by a negative quadratic
term in the scalar majorant, valid throughout the entire unit interval. -/
theorem first_level_polynomial_majorant {a x : ℝ} (ha : 0 ≤ a)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    10 * a ^ 2 / 3 - 2 * a ^ 3 * x / 3 + 5 * a ^ 4 * x ^ 2 / 6 ≤
      10 * a ^ 2 / 3 + (5 * a ^ 4 / 6 - 2 * a ^ 3 / 3) * x ^ 2 := by
  have hxx : 0 ≤ x - x ^ 2 := by nlinarith
  have h := mul_nonneg (pow_nonneg ha 3) hxx
  nlinarith

theorem first_level_coefficient_pos :
    0 < 5 * (9 / 10 : ℝ) ^ 4 / 6 - 2 * (9 / 10 : ℝ) ^ 3 / 3 := by
  norm_num

theorem first_tail_weight :
    (1 / 2 : ℝ) * ((5 / 12) / (1 / 4) - 1) = 1 / 3 := by
  norm_num

theorem second_tail_weight :
    (1 / 2 : ℝ) * ((5 / 12) / (1 / 9) - 1) = 11 / 8 := by
  norm_num

theorem tail_constant_algebra (a : ℝ) :
    2 * a ^ 2 * (5 / 12) * (4 / 9 + 1 / 6) = 55 * a ^ 2 / 108 := by
  ring

/-- The geometric tail of the positive weights starts at level two. -/
theorem finite_geometric_weights (n : ℕ) :
    (∑ r ∈ Finset.range n, (1 / 3 : ℝ) ^ (r + 2)) =
      (1 / 6 : ℝ) * (1 - (1 / 3 : ℝ) ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_add, pow_succ]
    ring

theorem finite_weight_budget (n : ℕ) :
    (1 / 4 : ℝ) + (∑ r ∈ Finset.range n, (1 / 3 : ℝ) ^ (r + 2)) ≤ 5 / 12 := by
  rw [finite_geometric_weights]
  have h := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3) n
  linarith

theorem higher_tail_weight_lower (r : ℕ) (hr : 2 ≤ r) :
    (11 / 8 : ℝ) ≤ ((5 / 12 : ℝ) / (1 / 3 : ℝ) ^ r - 1) / 2 := by
  have hv0 : (0 : ℝ) < (1 / 3 : ℝ) ^ r := by positivity
  have hv := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (by norm_num : (1 / 3 : ℝ) ≤ 1) hr
  norm_num at hv
  have hdiv : (15 / 4 : ℝ) ≤ (5 / 12 : ℝ) / (1 / 3 : ℝ) ^ r := by
    apply (le_div_iff₀ hv0).mpr
    nlinarith
  linarith

/-- Convexity converts the endpoint comparison to a uniform scalar bound.
The caller must still establish convexity of its particular function. -/
theorem convex_endpoint_majorant (f : ℝ → ℝ)
    (hf : ConvexOn ℝ (Set.Icc 0 1) f) (hends : f 1 ≤ f 0)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : f x ≤ f 0 := by
  have h := hf.2 (by simp : (0 : ℝ) ∈ Set.Icc 0 1)
    (by simp : (1 : ℝ) ∈ Set.Icc 0 1) (sub_nonneg.mpr hx1) hx0
    (by ring : (1 - x) + x = 1)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add] at h
  nlinarith

theorem log_ten_lt_five_halves : Real.log 10 < (5 / 2 : ℝ) := by
  have htaylor : (10 : ℝ) <
      ∑ i ∈ Finset.range 5, (5 / 2 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 10)).mpr
  exact lt_of_lt_of_le htaylor (Real.sum_le_exp_of_nonneg (by norm_num) 5)

/-- The endpoint comparison in (4.19) is strictly negative on the entire
range of higher-level weights. -/
theorem scalar_endpoint_negative (b : ℝ) (hb : (11 / 8 : ℝ) ≤ b) :
    -(9 / 10 : ℝ) ^ 2 - 2 * (9 / 10 : ℝ) - 2 * Real.log (1 - (9 / 10 : ℝ)) -
      b * (4 * (9 / 10 : ℝ) ^ 3 - (9 / 10 : ℝ) ^ 4) < 0 := by
  have hlog := log_ten_lt_five_halves
  have hinv : (1 - (9 / 10 : ℝ)) = (10 : ℝ)⁻¹ := by norm_num
  rw [hinv, Real.log_inv]
  norm_num at *
  linarith

/-- An explicit rational upper bound for log 9, proved using sixteen
nonnegative terms of the exponential Taylor series. -/
theorem log_nine_upper : Real.log 9 < (219722458 / 100000000 : ℝ) := by
  have htaylor : (9 : ℝ) <
      ∑ i ∈ Finset.range 16, (219722458 / 100000000 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 9)).mpr
  exact lt_of_lt_of_le htaylor (Real.sum_le_exp_of_nonneg (by norm_num) 16)

/-- Appendix A's advertised coefficient follows from the stated bound on
the series error.  The series-error bound is an explicit hypothesis here. -/
theorem coefficient_gt_decimal (error : ℝ) (herror0 : 0 ≤ error)
    (herror : error ≤ (479084457020255861 / 1000000000000000000 : ℝ)) :
    (2459209 / 10000000 : ℝ) <
      (9 / (10 * Real.log 9)) * (1 - Real.sqrt (error / 3)) := by
  have hlog0 : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have hs0 : 0 ≤ Real.sqrt (error / 3) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (error / 3) ^ 2 = error / 3 :=
    Real.sq_sqrt (by positivity)
  have hs : Real.sqrt (error / 3) < (39961835 / 100000000 : ℝ) := by
    nlinarith
  have hlog := log_nine_upper
  have hdiv :
      (2459209 / 10000000 : ℝ) * (10 * Real.log 9) <
        9 * (1 - Real.sqrt (error / 3)) := by
    nlinarith
  have hresult := (lt_div_iff₀ (show 0 < 10 * Real.log 9 by positivity)).mpr hdiv
  simpa only [div_mul_eq_mul_div] using hresult

end OuterAlgebra
end LittlewoodInverse
