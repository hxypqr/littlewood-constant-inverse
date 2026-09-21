import LittlewoodInverse.IntervalMoments
import LittlewoodInverse.ScalarCoupling

open scoped BigOperators Pointwise
open MeasureTheory

namespace LittlewoodInverse
namespace IntervalEnergy

open IntervalMoments

noncomputable def pairSumCount (n : ℕ) (s : ℤ) : ℕ :=
  (((integerInterval n) ×ˢ (integerInterval n)).filter (fun p => p.1 + p.2 = s)).card

theorem pairSumCount_eq_interval (n : ℕ) (s : ℤ) :
    pairSumCount n s = (Finset.Ico (max 0 (s - (n : ℤ) + 1)) (min (n : ℤ) (s + 1))).card := by
  unfold pairSumCount
  apply Finset.card_bij (fun p _ => p.1)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, integerInterval, Finset.mem_Ico] at hp ⊢
    omega
  · intro p hp q hq hpq
    simp only [Finset.mem_filter, Finset.mem_product, integerInterval, Finset.mem_Ico] at hp hq
    apply Prod.ext hpq
    omega
  · intro z hz
    simp only [Finset.mem_Ico] at hz
    refine ⟨(z, s - z), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product, integerInterval, Finset.mem_Ico]
    omega

theorem pairSumCount_lower (n k : ℕ) (hk : k < n) :
    pairSumCount n (k : ℤ) = k + 1 := by
  rw [pairSumCount_eq_interval, Int.card_Ico]
  omega

theorem pairSumCount_upper (n k : ℕ) (hk : k < n) :
    pairSumCount n ((n : ℤ) + (k : ℤ)) = n - (k + 1) := by
  rw [pairSumCount_eq_interval, Int.card_Ico]
  omega

theorem sum_integerInterval (n : ℕ) (f : ℤ → ℕ) :
    (∑ z ∈ integerInterval n, f z) = ∑ k ∈ Finset.range n, f (k : ℤ) := by
  simp [integerInterval, Int.Ico_eq_finset_map]

theorem energy_eq_sum_pairSumCount (n : ℕ) :
    additiveEnergy (integerInterval n) = ∑ k ∈ Finset.range (n + n), pairSumCount n (k : ℤ) ^ 2 := by
  unfold additiveEnergy
  rw [Finset.addEnergy_eq_sum_sq']
  change (∑ s ∈ integerInterval n + integerInterval n, pairSumCount n s ^ 2) = _
  rw [← sum_integerInterval (n + n) (fun s => pairSumCount n s ^ 2)]
  apply Finset.sum_subset
  · intro s hs
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hs
    simp only [integerInterval, Finset.mem_Ico] at hx hy ⊢
    push_cast
    omega
  · intro s hs hsnot
    have hzero : pairSumCount n s = 0 := by
      unfold pairSumCount
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro p hp hsum
      apply hsnot
      rw [← hsum]
      exact Finset.add_mem_add (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hp).2
    simp [hzero]

theorem energy_eq_two_square_sums (n : ℕ) :
    additiveEnergy (integerInterval n) =
      (∑ k ∈ Finset.range n, (k + 1) ^ 2) + ∑ k ∈ Finset.range n, (n - (k + 1)) ^ 2 := by
  rw [energy_eq_sum_pairSumCount, Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    rw [pairSumCount_lower n k (Finset.mem_range.mp hk)]
  · apply Finset.sum_congr rfl
    intro k hk
    push_cast
    rw [pairSumCount_upper n k (Finset.mem_range.mp hk)]

theorem energy_eq_square_sum (n : ℕ) :
    additiveEnergy (integerInterval n) = n ^ 2 + 2 * ∑ k ∈ Finset.range n, k ^ 2 := by
  rw [energy_eq_two_square_sums]
  have hfirst : (∑ k ∈ Finset.range n, (k + 1) ^ 2) =
      (∑ k ∈ Finset.range n, k ^ 2) + n ^ 2 := by
    have h := Finset.sum_range_succ' (fun k : ℕ => k ^ 2) n
    rw [Finset.sum_range_succ] at h
    simpa using h.symm
  have hsecond : (∑ k ∈ Finset.range n, (n - (k + 1)) ^ 2) =
      ∑ k ∈ Finset.range n, k ^ 2 := by
    simpa [Nat.sub_sub, Nat.add_comm] using Finset.sum_range_reflect (fun k : ℕ => k ^ 2) n
  rw [hfirst, hsecond]
  omega

theorem square_sum_identity (n : ℕ) :
    3 * (n ^ 2 + 2 * ∑ k ∈ Finset.range n, k ^ 2) = 2 * n ^ 3 + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    nlinarith

/-- Exact interval energy, stated without natural-number division. -/
theorem three_mul_interval_energy (n : ℕ) :
    3 * additiveEnergy (integerInterval n) = 2 * n ^ 3 + n := by
  rw [energy_eq_square_sum]
  exact square_sum_identity n

theorem interval_energy_real (n : ℕ) :
    (additiveEnergy (integerInterval n) : ℝ) = (2 * (n : ℝ) ^ 3 + n) / 3 := by
  have h : (3 : ℝ) * additiveEnergy (integerInterval n) = 2 * (n : ℝ) ^ 3 + n := by
    exact_mod_cast three_mul_interval_energy n
  linarith

theorem additiveEnergy_le_interval (B : Finset ℤ) :
    additiveEnergy B ≤ additiveEnergy (integerInterval B.card) := by
  have h := even_moment_le_interval B 2
  norm_num only at h
  rw [integral_norm_pow_four_fourierPolynomial, integral_norm_pow_four_fourierPolynomial] at h
  exact_mod_cast h

/-- The sharp finite energy bound (3.2), with denominators cleared. -/
theorem three_mul_energy_le (B : Finset ℤ) :
    3 * additiveEnergy B ≤ 2 * B.card ^ 3 + B.card := by
  calc
    _ ≤ 3 * additiveEnergy (integerInterval B.card) :=
      Nat.mul_le_mul_left 3 (additiveEnergy_le_interval B)
    _ = _ := three_mul_interval_energy B.card

theorem energy_max_real (B : Finset ℤ) :
    (additiveEnergy B : ℝ) ≤ (2 * (B.card : ℝ) ^ 3 + B.card) / 3 := by
  have h : (3 : ℝ) * additiveEnergy B ≤ 2 * (B.card : ℝ) ^ 3 + B.card := by
    exact_mod_cast three_mul_energy_le B
  linarith

theorem normalized_fourth_moment_eq (B : Finset ℤ) (hB : B.Nonempty) :
    (B.card : ℝ) * (∫ t, ScalarCoupling.normalizedMagnitude B t ^ 4 ∂circleMeasure) =
      (additiveEnergy B : ℝ) / (B.card : ℝ) ^ 3 := by
  have hn : (B.card : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hB.card_pos)
  unfold ScalarCoupling.normalizedMagnitude
  simp_rw [div_pow]
  rw [integral_div, integral_norm_pow_four_fourierPolynomial]
  field_simp

/-- An explicit uniform error term for the normalized fourth moment. -/
theorem normalized_fourth_moment_le (B : Finset ℤ) (hB : B.Nonempty) :
    (B.card : ℝ) * (∫ t, ScalarCoupling.normalizedMagnitude B t ^ 4 ∂circleMeasure) ≤
      (2 / 3 : ℝ) + 1 / (3 * (B.card : ℝ) ^ 2) := by
  have hn : (B.card : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hB.card_pos)
  rw [normalized_fourth_moment_eq B hB]
  calc
    _ ≤ ((2 * (B.card : ℝ) ^ 3 + B.card) / 3) / (B.card : ℝ) ^ 3 :=
      div_le_div_of_nonneg_right (energy_max_real B) (by positivity)
    _ = _ := by field_simp

/-- The fourth-moment asymptotic upper bound is uniform over all integer
sets of a given cardinality, with no restriction on their diameter. -/
theorem normalized_fourth_moment_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ B : Finset ℤ, N ≤ B.card →
      (B.card : ℝ) * (∫ t, ScalarCoupling.normalizedMagnitude B t ^ 4 ∂circleMeasure) ≤
        (2 / 3 : ℝ) + ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (1 : ℝ) (1 / ε))
  refine ⟨N, ?_⟩
  intro B hBN
  have hNc : (N : ℝ) ≤ B.card := by exact_mod_cast hBN
  have hn1 : (1 : ℝ) < B.card := lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hN) hNc
  have hn0 : (0 : ℝ) < B.card := by linarith
  have hB : B.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hn0)
  have hinv : 1 / ε < (B.card : ℝ) := lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hN) hNc
  have hmul : (1 : ℝ) < (B.card : ℝ) * ε := (div_lt_iff₀ hε).mp hinv
  have hn2 : (B.card : ℝ) ≤ (B.card : ℝ) ^ 2 := by nlinarith
  have hmul2 := mul_le_mul_of_nonneg_right hn2 hε.le
  have hsmall : 1 / (3 * (B.card : ℝ) ^ 2) ≤ ε := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 3 * (B.card : ℝ) ^ 2)).mpr
    nlinarith
  exact (normalized_fourth_moment_le B hB).trans (add_le_add le_rfl hsmall)

end IntervalEnergy
end LittlewoodInverse
