import LittlewoodInverse.FirstLevelUniform

open scoped BigOperators
open MeasureTheory

namespace LittlewoodInverse
namespace SeriesCertificate

open ScalarCoupling UniformMoments

noncomputable def momentSeries (a : ℝ) : ℝ :=
  ∑' j : ℕ, a ^ (j + 5) / ((j : ℝ) + 5) * momentCoefficient (j + 5)

theorem summable_momentSeries {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Summable (fun j : ℕ => a ^ (j + 5) / ((j : ℝ) + 5) * momentCoefficient (j + 5)) := by
  apply (hasSum_tailFromFive (by rwa [abs_of_nonneg ha0] : |a| < 1)).summable.of_norm_bounded
  intro j
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (momentCoefficient_nonneg _))]
  exact mul_le_of_le_one_right (by positivity) (momentCoefficient_le_one _ (by omega))

/-- Uniform geometric bound for the omitted sinc-moment series. -/
theorem momentSeries_le_finite (L : ℕ) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    momentSeries a ≤
      (∑ j ∈ Finset.range L, a ^ (j + 5) / ((j : ℝ) + 5) * momentCoefficient (j + 5)) +
        a ^ (L + 5) / (((L : ℝ) + 5) * (1 - a)) := by
  let f : ℕ → ℝ := fun j => a ^ (j + 5) / ((j : ℝ) + 5) * momentCoefficient (j + 5)
  have hf : Summable f := summable_momentSeries ha0 ha1
  have htail : Summable (fun j => f (j + L)) := (summable_nat_add_iff L).mpr hf
  have hgeom : Summable (fun j : ℕ => (a ^ (L + 5) / ((L : ℝ) + 5)) * a ^ j) :=
    (summable_geometric_of_lt_one ha0 ha1).mul_left _
  have hpoint (j : ℕ) : f (j + L) ≤ (a ^ (L + 5) / ((L : ℝ) + 5)) * a ^ j := by
    dsimp only [f]
    calc
      _ ≤ a ^ (j + L + 5) / (((j + L : ℕ) : ℝ) + 5) :=
        mul_le_of_le_one_right (by positivity) (momentCoefficient_le_one _ (by omega))
      _ ≤ a ^ (j + L + 5) / ((L : ℝ) + 5) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) j])
      _ = _ := by rw [Nat.add_assoc, pow_add]; ring
  have htsum := Summable.tsum_le_tsum hpoint htail hgeom
  rw [tsum_mul_left, tsum_geometric_of_lt_one ha0 ha1] at htsum
  have he : a ^ (L + 5) / ((L : ℝ) + 5) * (1 - a)⁻¹ =
      a ^ (L + 5) / (((L : ℝ) + 5) * (1 - a)) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he] at htsum
  rw [momentSeries, ← Summable.sum_add_tsum_nat_add L hf]
  exact add_le_add le_rfl htsum

theorem tailError_eq_momentSeries :
    tailError = 55 * (9 / 10 : ℝ)^2 / 108 + (1 / 9 : ℝ) *
      ((2 / 3 : ℝ) * (5 * (9 / 10 : ℝ)^4 / 6 - 2 * (9 / 10 : ℝ)^3 / 3) +
        2 * momentSeries (9 / 10)) := by
  have hs : (∑' j : ℕ, momentCoefficient (j + 5) * (9 / 10 : ℝ) ^ (j + 5) / (j + 5 : ℕ)) =
      ∑' j : ℕ, (9 / 10 : ℝ) ^ (j + 5) / ((j : ℝ) + 5) * momentCoefficient (j + 5) := by
    apply tsum_congr
    intro j
    push_cast
    ring
  dsimp only [tailError, momentSeries]
  rw [hs]

theorem tailError_eq_delta :
    tailError = 55 * (9 / 10 : ℝ)^2 / 108 + FirstLevelUniform.delta (9 / 10) / 9 := by
  rw [tailError_eq_momentSeries]
  unfold FirstLevelUniform.delta momentSeries
  ring

theorem tailError_nonneg : 0 ≤ tailError := by
  rw [tailError_eq_momentSeries]
  have hs : 0 ≤ momentSeries (9 / 10) := by
    apply tsum_nonneg
    intro j
    exact mul_nonneg (by positivity) (momentCoefficient_nonneg _)
  have hc : (0 : ℝ) ≤ 5 * (9 / 10 : ℝ)^4 / 6 - 2 * (9 / 10 : ℝ)^3 / 3 := by norm_num
  positivity

end SeriesCertificate
end LittlewoodInverse
