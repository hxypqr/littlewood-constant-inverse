import LittlewoodInverse.BoundaryAsymptotic
import LittlewoodInverse.SidonFibreExamples

open scoped BigOperators Interval
open MeasureTheory

namespace LittlewoodInverse

theorem boundaryNorm_single_cell :
    boundaryNorm 1 ({(0, 0)} : Finset (ZMod 1 × ℤ)) = 4 / Real.pi := by
  rw [← integral_boundaryW_zero]
  simp_rw [boundaryW_zero, boundaryPolynomial_difference]
  simp only [Finset.sum_singleton, cyclicCharacter_zero, fourier_zero, one_mul, mul_one,
    integral_const, probReal_univ, smul_eq_mul]
  rw [circle_integral_eq_unit_interval]
  simp only [norm_one_sub_fourier_one]
  have habs : (∫ x in (0 : ℝ)..1, 2 * |Real.sin (Real.pi * x)|) =
      ∫ x in (0 : ℝ)..1, 2 * Real.sin (Real.pi * x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
      (mul_nonneg Real.pi_pos.le hx.1) (by nlinarith [Real.pi_pos, hx.2]))]
  rw [habs, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left Real.sin Real.pi_ne_zero]
  norm_num [integral_sin]
  ring

/-- The classical arithmetic-progression logarithmic asymptotic follows
internally from the manuscript's proved boundary asymptotic. -/
theorem interval_littlewoodNorm_asymptotic :
    (fun M : ℕ => littlewoodNorm (Finset.Ico (0 : ℤ) M) -
      (4 / Real.pi ^ 2) * Real.log (M : ℝ)) =O[Filter.atTop] (fun _ : ℕ => (1 : ℝ)) := by
  have h := boundary_norm_asymptotic 1 ({(0, 0)} : Finset (ZMod 1 × ℤ))
  simpa only [interval_as_blockInflation, IntervalMoments.integerInterval,
    boundaryNorm_single_cell, div_div, ← pow_two] using h

/-- Bounded-error form for every positive integer, derived without any
external Dirichlet-kernel asymptotic. -/
theorem dirichlet_l1_asymptotic : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 0 < N →
    |littlewoodNorm (Finset.Ico (0 : ℤ) N) - 4 / Real.pi ^ 2 * Real.log N| ≤ C := by
  let B : ℝ := 2 + Real.pi * Real.sqrt
    (boundaryMass ({(0, 0)} : Finset (ZMod 1 × ℤ)) : ℝ) +
    Real.pi ^ 2 * (4 / Real.pi) + (2 + Real.log 2) * (4 / Real.pi) / Real.pi
  refine ⟨max B (littlewoodNorm (Finset.Ico (0 : ℤ) 1)),
    (littlewoodNorm_nonneg _).trans (le_max_right _ _), ?_⟩
  intro N hN
  by_cases hN2 : 2 ≤ N
  · have h := boundary_asymptotic_explicit 1 hN2
      ({(0, 0)} : Finset (ZMod 1 × ℤ))
    have hh : |littlewoodNorm (Finset.Ico (0 : ℤ) N) -
        4 / Real.pi ^ 2 * Real.log N| ≤ B := by
      simpa only [interval_as_blockInflation, IntervalMoments.integerInterval,
        boundaryNorm_single_cell, Finset.card_singleton, Nat.cast_one,
        mul_one, div_div, ← pow_two] using h
    exact hh.trans (le_max_left _ _)
  · have he : N = 1 := by omega
    subst N
    simpa only [Nat.cast_one, Real.log_one, mul_zero, sub_zero,
      abs_of_nonneg (littlewoodNorm_nonneg _)] using le_max_right B
        (littlewoodNorm (Finset.Ico (0 : ℤ) 1))

end LittlewoodInverse
