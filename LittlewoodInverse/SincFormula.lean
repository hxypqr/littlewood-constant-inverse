import LittlewoodInverse.BoundedCompositions
import LittlewoodInverse.BinomialLimit

open scoped BigOperators Topology
open MeasureTheory Filter

namespace LittlewoodInverse
namespace SincFormula

open IntervalMoments UniformMoments ScalarCoupling

theorem normalizedMoment_interval_eq_relationCount (n r : ℕ) (hn : 0 < n) (hr : 0 < r) :
    normalizedMoment (integerInterval n) (2 * r) =
      (MomentCounting.relationCount (integerInterval n) r : ℝ) / (n : ℝ) ^ (2 * r - 1) := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold normalizedMoment normalizedMagnitude
  rw [card_integerInterval]
  simp_rw [div_pow]
  rw [integral_div, MomentCounting.integral_even_moment]
  have hp : 2 * r = (2 * r - 1) + 1 := by omega
  rw [hp, pow_succ]
  field_simp
  simp

theorem normalizedMoment_interval_binomial (n r : ℕ) (hr : 0 < r) (hn : r ≤ n) :
    normalizedMoment (integerInterval n) (2 * r) =
      ∑ j ∈ Finset.range r, (-1 : ℝ)^j * ((2 * r).choose j : ℝ) *
        ((((r - j) * n + (r - 1)).choose (2 * r - 1) : ℝ) / (n : ℝ)^(2 * r - 1)) := by
  rw [normalizedMoment_interval_eq_relationCount n r (by omega) hr]
  have hc : (MomentCounting.relationCount (integerInterval n) r : ℝ) =
      ∑ j ∈ Finset.range r, (-1 : ℝ)^j * ((2 * r).choose j : ℝ) *
        (((r - j) * n + r - 1).choose (2 * r - 1) : ℝ) := by
    exact_mod_cast BoundedCompositions.interval_relationCount_binomial n r hr hn
  rw [hc, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have htop : (r - j) * n + r - 1 = (r - j) * n + (r - 1) := by omega
  rw [htop]
  ring

/-- The exact rational even-sinc formula, obtained from the actual
interval moment count and its proved analytic limit. -/
theorem sincMoment_even_eq_sum (r : ℕ) (hr : 0 < r) :
    sincMoment (2 * r : ℕ) =
      (∑ j ∈ Finset.range r, (-1 : ℝ)^j * ((2 * r).choose j : ℝ) *
        ((r - j : ℕ) : ℝ) ^ (2 * r - 1)) / ((2 * r - 1).factorial : ℝ) := by
  have hlim : Tendsto (fun n : ℕ =>
      ∑ j ∈ Finset.range r, (-1 : ℝ)^j * ((2 * r).choose j : ℝ) *
        ((((r - j) * n + (r - 1)).choose (2 * r - 1) : ℝ) / (n : ℝ)^(2 * r - 1)))
      atTop (𝓝 (∑ j ∈ Finset.range r, (-1 : ℝ)^j * ((2 * r).choose j : ℝ) *
        (((r - j : ℕ) : ℝ)^(2 * r - 1) / ((2 * r - 1).factorial : ℝ)))) := by
    apply tendsto_finsetSum
    intro j hj
    exact (BinomialLimit.tendsto_choose_affine_div_pow (r - j) (r - 1)
      (2 * r - 1) (by have := Finset.mem_range.mp hj; omega)).const_mul _
  have hactual := tendsto_normalizedMoment_interval_even r (by omega)
  have heq : (fun n : ℕ => normalizedMoment (integerInterval n) (2 * r)) =ᶠ[atTop]
      (fun n : ℕ => ∑ j ∈ Finset.range r, (-1 : ℝ)^j * ((2 * r).choose j : ℝ) *
        ((((r - j) * n + (r - 1)).choose (2 * r - 1) : ℝ) / (n : ℝ)^(2 * r - 1))) := by
    filter_upwards [eventually_ge_atTop r] with n hn
    exact normalizedMoment_interval_binomial n r hr hn
  have hsame := tendsto_nhds_unique (hactual.congr' heq) hlim
  rw [hsame, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Manuscript form, with the vanishing final `j = r` summand included. -/
theorem sincMoment_even_formula (r : ℕ) (hr : 0 < r) :
    sincMoment (2 * r : ℕ) =
      (∑ j ∈ Finset.range (r + 1), (-1 : ℝ)^j * ((2 * r).choose j : ℝ) *
        ((r - j : ℕ) : ℝ) ^ (2 * r - 1)) / ((2 * r - 1).factorial : ℝ) := by
  rw [Finset.sum_range_succ]
  simp only [Nat.sub_self, Nat.cast_zero, zero_pow (by omega : 2 * r - 1 ≠ 0), mul_zero, add_zero]
  exact sincMoment_even_eq_sum r hr

/-- A computable rational expression for the proved even sinc moment. -/
def evenMomentRat (r : ℕ) : ℚ :=
  (∑ j ∈ Finset.range r, (-1 : ℚ)^j * ((2 * r).choose j : ℚ) *
    ((r - j : ℕ) : ℚ) ^ (2 * r - 1)) / ((2 * r - 1).factorial : ℚ)

theorem sincMoment_even_eq_rat (r : ℕ) (hr : 0 < r) :
    sincMoment (2 * r : ℕ) = (evenMomentRat r : ℝ) := by
  rw [sincMoment_even_eq_sum r hr]
  unfold evenMomentRat
  norm_cast

end SincFormula
end LittlewoodInverse
