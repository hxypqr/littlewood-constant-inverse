import LittlewoodInverse.FirstLevelUniform

open scoped BigOperators

namespace LittlewoodInverse
namespace TailWeights

noncomputable def v (r : ℕ) : ℝ := if r = 0 then 1 / 4 else (1 / 3) ^ (r + 1)
noncomputable def b (r : ℕ) : ℝ := ((5 / 12) / v r - 1) / 2
noncomputable def w (r : ℕ) : ℝ := (1 / 9) ^ (r + 1)

theorem v_pos (r : ℕ) : 0 < v r := by unfold v; split_ifs <;> positivity

theorem b_zero : b 0 = 1 / 3 := by norm_num [b, v]

theorem b_ge (r : ℕ) (hr : 0 < r) : (11 / 8 : ℝ) ≤ b r := by
  simpa only [b, v, if_neg (Nat.ne_of_gt hr)] using
    OuterAlgebra.higher_tail_weight_lower (r + 1) (by omega)

theorem v_sum (n : ℕ) : (∑ r ∈ Finset.range n, v r) ≤ 5 / 12 := by
  cases n with
  | zero => norm_num
  | succ n =>
    rw [Finset.sum_range_succ']
    have h := OuterAlgebra.finite_weight_budget n
    rw [add_comm] at h
    simpa [v, Nat.add_assoc] using h

theorem weighted_constant (r : ℕ) : w r * (2 + 4 * b r) =
    if r = 0 then 10 / 27 else (5 / 6) * (1 / 3 : ℝ) ^ (r + 1) := by
  by_cases hr : r = 0
  · subst r
    norm_num [w, b, v]
  · rw [if_neg hr]
    unfold b v w
    rw [if_neg hr]
    have hv0 : (1 / 3 : ℝ) ^ (r + 1) ≠ 0 := by positivity
    have hratio : ((1 / 9 : ℝ) ^ (r + 1)) / ((1 / 3 : ℝ) ^ (r + 1)) =
        (1 / 3 : ℝ) ^ (r + 1) := by rw [← div_pow]; norm_num
    calc
      _ = (5 / 6) * ((1 / 9 : ℝ) ^ (r + 1) / (1 / 3 : ℝ) ^ (r + 1)) := by field_simp; ring
      _ = _ := by rw [hratio]

theorem constant_sum (n : ℕ) :
    (∑ r ∈ Finset.range n, w r * (2 + 4 * b r)) ≤ 55 / 108 := by
  cases n with
  | zero => norm_num
  | succ n =>
    simp_rw [weighted_constant]
    rw [Finset.sum_range_succ']
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, ite_true]
    rw [← Finset.mul_sum]
    have hg := OuterAlgebra.finite_geometric_weights n
    have hp : 0 ≤ (1 / 3 : ℝ)^n := by positivity
    have hs : (∑ r ∈ Finset.range n, (1 / 3 : ℝ) ^ (r + 1 + 1)) ≤ 1 / 6 := by
      simpa only [Nat.add_assoc] using (show
        (∑ r ∈ Finset.range n, (1 / 3 : ℝ) ^ (r + 2)) ≤ 1 / 6 by linarith)
    linarith

theorem delta_nonneg : 0 ≤ FirstLevelUniform.delta (9 / 10) := by
  unfold FirstLevelUniform.delta
  have hsum : 0 ≤ ∑' j : ℕ, (9 / 10 : ℝ) ^ (j + 5) / ((j : ℝ) + 5) *
      momentCoefficient (j + 5) := tsum_nonneg fun j =>
    mul_nonneg (by positivity) (UniformMoments.momentCoefficient_nonneg _)
  norm_num
  linarith

theorem tailError_eq : tailError = 55 * (9 / 10 : ℝ)^2 / 108 +
    FirstLevelUniform.delta (9 / 10) / 9 := by
  dsimp only [tailError, FirstLevelUniform.delta]
  have hs : (∑' j : ℕ, momentCoefficient (j + 5) * (9 / 10 : ℝ)^(j + 5) / (j + 5 : ℕ)) =
      ∑' j : ℕ, (9 / 10 : ℝ)^(j + 5) / ((j : ℝ) + 5) * momentCoefficient (j + 5) := by
    apply tsum_congr
    intro j
    push_cast
    ring
  rw [hs]
  ring

theorem finite_budget (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    (∑ r ∈ Finset.range n, w r * ((2 + 4 * b r) * (9 / 10 : ℝ)^2 +
      if r = 0 then FirstLevelUniform.delta (9 / 10) + ε else 0)) ≤ tailError + ε := by
  have hconst := mul_le_mul_of_nonneg_right (constant_sum n) (sq_nonneg (9 / 10 : ℝ))
  rw [Finset.sum_mul] at hconst
  have hcorr : (∑ r ∈ Finset.range n, w r *
      (if r = 0 then FirstLevelUniform.delta (9 / 10) + ε else 0)) ≤
        (FirstLevelUniform.delta (9 / 10) + ε) / 9 := by
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq']
    split_ifs <;> norm_num [w] <;> nlinarith [delta_nonneg]
  simp_rw [mul_add, Finset.sum_add_distrib, ← mul_assoc]
  rw [tailError_eq]
  nlinarith

end TailWeights
end LittlewoodInverse
