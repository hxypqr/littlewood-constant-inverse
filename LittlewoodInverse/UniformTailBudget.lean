import LittlewoodInverse.TailWeights
import LittlewoodInverse.TailCoupling
import LittlewoodInverse.OuterFamily

open scoped BigOperators
open MeasureTheory
open LittlewoodInverse.ScalarCoupling

namespace LittlewoodInverse

/-- Proposition 4.5: the tail error bound is uniform in its length and in
the actual integer sets. The outer multipliers are the data proved to exist. -/
theorem uniform_outer_tail_budget (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ (base len : ℕ), N ≤ base →
      ∀ A : Fin len → Finset ℤ,
      (∀ i, (A i).card = base * 9 ^ (i.val + 1)) →
      ∀ M : ∀ i, DampingData (9 / 10) (A i),
      (base : ℝ) * (∫ t, ‖(∏ i, (M i).multiplier t) - 1‖ ^ 2 ∂circleMeasure) ≤
        tailError + ε := by
  obtain ⟨N, hN⟩ := FirstLevelUniform.first_level_uniform ε hε
  refine ⟨max N 1, by omega, ?_⟩
  intro base len hbase A hcard M
  have hb : 0 < base := by omega
  have hbR : (0 : ℝ) < base := by exact_mod_cast hb
  have hbig (i : Fin len) : base ≤ (A i).card := by
    rw [hcard]
    exact Nat.le_mul_of_pos_right base (by positivity)
  have hne (i : Fin len) : (A i).Nonempty := Finset.card_pos.mp (hb.trans_le (hbig i))
  let u := fun i => ScalarCoupling.normalizedMagnitude (A i)
  let I := fun i : Fin len => ∫ t, ScalarCoupling.h (9 / 10) (u i t) +
    TailWeights.b i.val * OuterAlgebra.q (9 / 10) (u i t)^2 ∂circleMeasure
  have hscalar (i : Fin len) : ((A i).card : ℝ) * I i ≤
      (2 + 4 * TailWeights.b i.val) * (9 / 10 : ℝ)^2 +
        if i.val = 0 then FirstLevelUniform.delta (9 / 10) + ε else 0 := by
    by_cases hi : i.val = 0
    · have hs := hN (A i) ((by omega : N ≤ base).trans (hbig i))
      simp only [I, u, hi, TailWeights.b_zero, ite_true]
      convert hs using 1; ring
    · have hs := scalar_large_b_integral (A i) (hne i) (TailWeights.b i.val)
        (TailWeights.b_ge i.val (by omega))
      simpa only [I, u, if_neg hi, add_zero] using hs
  have hscaled (i : Fin len) : (base : ℝ) * I i ≤ TailWeights.w i.val *
      ((2 + 4 * TailWeights.b i.val) * (9 / 10 : ℝ)^2 +
        if i.val = 0 then FirstLevelUniform.delta (9 / 10) + ε else 0) := by
    have hs := mul_le_mul_of_nonneg_left (hscalar i)
      (show 0 ≤ TailWeights.w i.val by unfold TailWeights.w; positivity)
    have hw : TailWeights.w i.val * ((A i).card : ℝ) = base := by
      rw [hcard]
      push_cast
      unfold TailWeights.w
      calc
        _ = (base : ℝ) * ((1 / 9 : ℝ) * 9) ^ (i.val + 1) := by rw [mul_pow]; ring
        _ = _ := by norm_num
    simpa only [← mul_assoc, hw] using hs
  have hweight : (∑ i : Fin len, TailWeights.v i.val) ≤ 5 / 12 := by
    simpa only [Fin.sum_univ_eq_sum_range] using TailWeights.v_sum len
  have he := outer_product_coupled (by norm_num : (0 : ℝ) ≤ 9 / 10)
    (by norm_num : (9 / 10 : ℝ) < 1) u
    (fun i => normalizedMagnitude_continuous (A i))
    (fun i t => ⟨normalizedMagnitude_nonneg (A i) t, normalizedMagnitude_le_one (A i) (hne i) t⟩)
    (fun i => (M i).multiplier) (fun i => (M i).memLp) (fun i => (M i).support)
    (fun i => (M i).modulus) (fun i => (M i).zeroCoeff)
    (fun i => TailWeights.v i.val) (fun i => TailWeights.v_pos i.val) hweight
  change _ ≤ ∑ i, I i at he
  calc
    _ ≤ (base : ℝ) * ∑ i, I i := mul_le_mul_of_nonneg_left he hbR.le
    _ = ∑ i, (base : ℝ) * I i := Finset.mul_sum _ _ _
    _ ≤ ∑ i : Fin len, TailWeights.w i.val *
        ((2 + 4 * TailWeights.b i.val) * (9 / 10 : ℝ)^2 +
          if i.val = 0 then FirstLevelUniform.delta (9 / 10) + ε else 0) :=
      Finset.sum_le_sum fun i _ => hscaled i
    _ ≤ _ := by
      simpa only [← Fin.sum_univ_eq_sum_range] using TailWeights.finite_budget len hε.le

end LittlewoodInverse
