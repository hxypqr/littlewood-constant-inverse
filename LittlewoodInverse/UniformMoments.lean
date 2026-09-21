import LittlewoodInverse.SincMoments
import LittlewoodInverse.SincBridge
import LittlewoodInverse.SpectralEnergy

open scoped BigOperators Topology
open MeasureTheory Filter

namespace LittlewoodInverse
namespace UniformMoments

open ScalarCoupling IntervalMoments

noncomputable def normalizedMoment (B : Finset ℤ) (k : ℕ) : ℝ :=
  (B.card : ℝ) * ∫ t, normalizedMagnitude B t ^ k ∂circleMeasure

theorem normalizedMoment_nonneg (B : Finset ℤ) (k : ℕ) :
    0 ≤ normalizedMoment B k :=
  mul_nonneg (Nat.cast_nonneg _) (integral_nonneg fun t =>
    pow_nonneg (normalizedMagnitude_nonneg B t) _)

@[simp] theorem card_integerInterval (n : ℕ) : (integerInterval n).card = n := by
  simp [integerInterval, Int.card_Ico]

theorem normalizedMoment_even_le_interval (B : Finset ℤ) (r : ℕ) :
    normalizedMoment B (2 * r) ≤ normalizedMoment (integerInterval B.card) (2 * r) := by
  unfold normalizedMoment normalizedMagnitude
  simp_rw [card_integerInterval, div_pow]
  rw [integral_div, integral_div]
  exact mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (even_moment_le_interval B r) (by positivity))
    (Nat.cast_nonneg _)

/-- Cauchy--Schwarz between the two neighboring even moments, for the
actual normalized exponential sum. -/
theorem normalizedMoment_odd_sq_le (B : Finset ℤ) (r : ℕ) :
    normalizedMoment B (2 * r + 1) ^ 2 ≤
      normalizedMoment B (2 * r) * normalizedMoment B (2 * r + 2) := by
  have hc := normalizedMagnitude_continuous B
  have hcs := integral_cauchy_schwarz_sq
    (μ := circleMeasure) (f := fun t => normalizedMagnitude B t ^ r)
    (g := fun t => normalizedMagnitude B t ^ (r + 1))
    (continuous_circle_integrable ((hc.pow r).pow 2))
    (continuous_circle_integrable ((hc.pow r).mul (hc.pow (r + 1))))
    (continuous_circle_integrable ((hc.pow (r + 1)).pow 2))
  have h1 : r + (r + 1) = 2 * r + 1 := by omega
  have h2 : r * 2 = 2 * r := by omega
  have h3 : (r + 1) * 2 = 2 * r + 2 := by omega
  simp_rw [← pow_add, ← pow_mul, h1, h2, h3] at hcs
  have h := mul_le_mul_of_nonneg_left hcs (sq_nonneg (B.card : ℝ))
  unfold normalizedMoment
  nlinarith only [h]

theorem normalizedMoment_odd_le_sqrt (B : Finset ℤ) (r : ℕ) :
    normalizedMoment B (2 * r + 1) ≤
      Real.sqrt (normalizedMoment B (2 * r) * normalizedMoment B (2 * r + 2)) := by
  apply (Real.le_sqrt (normalizedMoment_nonneg B _) (mul_nonneg
    (normalizedMoment_nonneg B _) (normalizedMoment_nonneg B _))).mpr
  exact normalizedMoment_odd_sq_le B r

theorem tendsto_normalizedMoment_interval (k : ℕ) :
    Tendsto (fun n : ℕ => normalizedMoment (integerInterval n) (k + 2))
      atTop (𝓝 (sincMoment (k + 2 : ℕ))) := by
  apply (SincMoments.tendsto_integral_scaledSincKernel k).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  symm
  unfold normalizedMoment normalizedMagnitude
  rw [card_integerInterval]
  exact normalized_interval_moment_eq_scaledSinc n k (by omega)

theorem tendsto_normalizedMoment_interval_even (r : ℕ) (hr : 1 ≤ r) :
    Tendsto (fun n : ℕ => normalizedMoment (integerInterval n) (2 * r))
      atTop (𝓝 (sincMoment (2 * r : ℕ))) := by
  have he : 2 * r - 2 + 2 = 2 * r := by omega
  simpa only [he] using tendsto_normalizedMoment_interval (2 * r - 2)

/-- The even-moment asymptotic is uniform over all finite integer sets,
including sets with arbitrarily large diameter. -/
theorem normalizedMoment_even_uniform (r : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ B : Finset ℤ, N ≤ B.card →
      normalizedMoment B (2 * r) ≤ sincMoment (2 * r : ℕ) + ε := by
  have hev := (tendsto_normalizedMoment_interval_even r hr).eventually
    (gt_mem_nhds (show sincMoment (2 * r : ℕ) < sincMoment (2 * r : ℕ) + ε by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun B hB => ?_⟩
  exact (normalizedMoment_even_le_interval B r).trans (hN B.card hB).le

theorem normalizedMoment_odd_le_interval_sqrt (B : Finset ℤ) (r : ℕ) :
    normalizedMoment B (2 * r + 1) ≤
      Real.sqrt (normalizedMoment (integerInterval B.card) (2 * r) *
        normalizedMoment (integerInterval B.card) (2 * r + 2)) := by
  apply (normalizedMoment_odd_le_sqrt B r).trans
  apply Real.sqrt_le_sqrt
  have hn := normalizedMoment_even_le_interval B (r + 1)
  have he : 2 * (r + 1) = 2 * r + 2 := by omega
  rw [he] at hn
  exact mul_le_mul (normalizedMoment_even_le_interval B r) hn
    (normalizedMoment_nonneg B _) (normalizedMoment_nonneg _ _)

/-- The odd-moment constant is the geometric mean of the neighboring
even sinc moments, as in the manuscript. -/
theorem normalizedMoment_odd_uniform (r : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ B : Finset ℤ, N ≤ B.card →
      normalizedMoment B (2 * r + 1) ≤
        Real.sqrt (sincMoment (2 * r : ℕ) * sincMoment (2 * r + 2 : ℕ)) + ε := by
  have he : 2 * (r + 1) = 2 * r + 2 := by omega
  have hnext := tendsto_normalizedMoment_interval_even (r + 1) (by omega)
  rw [he] at hnext
  have hlim := ((tendsto_normalizedMoment_interval_even r hr).mul hnext).sqrt
  have hev := hlim.eventually (gt_mem_nhds (show
    Real.sqrt (sincMoment (2 * r : ℕ) * sincMoment (2 * r + 2 : ℕ)) <
      Real.sqrt (sincMoment (2 * r : ℕ) * sincMoment (2 * r + 2 : ℕ)) + ε by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun B hB => ?_⟩
  exact (normalizedMoment_odd_le_interval_sqrt B r).trans (hN B.card hB).le

theorem normalizedMoment_uniform (k : ℕ) (hk : 2 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ B : Finset ℤ, N ≤ B.card →
      normalizedMoment B k ≤ momentCoefficient k + ε := by
  rcases Nat.even_or_odd k with he | ho
  · obtain ⟨r, hr⟩ := he
    have hr' : k = 2 * r := by omega
    rw [hr'] at hk ⊢
    have hev : Even (2 * r) := ⟨r, by omega⟩
    simpa only [momentCoefficient, if_pos hev] using
      normalizedMoment_even_uniform r (by omega) ε hε
  · obtain ⟨r, hr⟩ := ho
    have hr' : k = 2 * r + 1 := by omega
    rw [hr'] at hk ⊢
    have hev : ¬Even (2 * r + 1) := by rintro ⟨s, hs⟩; omega
    have hsub : 2 * r + 1 - 1 = 2 * r := by omega
    have hadd : 2 * r + 1 + 1 = 2 * r + 2 := by omega
    simpa only [momentCoefficient, if_neg hev, hsub, hadd] using
      normalizedMoment_odd_uniform r (by omega) ε hε

theorem sincMoment_nat_nonneg (k : ℕ) : 0 ≤ sincMoment (k : ℝ) := by
  apply integral_nonneg
  intro x
  exact Real.rpow_nonneg (abs_nonneg _) _

theorem sincMoment_nat_le_one (k : ℕ) (hk : 2 ≤ k) : sincMoment (k : ℝ) ≤ 1 := by
  have he : k - 2 + 2 = k := by omega
  have hlim := tendsto_normalizedMoment_interval (k - 2)
  rw [he] at hlim
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hB : (integerInterval n).Nonempty :=
    Finset.card_pos.mp (by rw [card_integerInterval]; omega)
  exact normalized_moment_le_one _ hB k hk

theorem sincMoment_two : sincMoment 2 = 1 := by
  have hlim := tendsto_normalizedMoment_interval 0
  norm_num only [zero_add, Nat.cast_ofNat] at hlim
  have heq : (fun n : ℕ => normalizedMoment (integerInterval n) 2) =ᶠ[atTop]
      fun _ => (1 : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hB : (integerInterval n).Nonempty :=
      Finset.card_pos.mp (by rw [card_integerInterval]; omega)
    exact normalized_second_moment _ hB
  exact tendsto_nhds_unique (hlim.congr' heq) tendsto_const_nhds

theorem normalizedMoment_interval_four (n : ℕ) (hn : 0 < n) :
    normalizedMoment (integerInterval n) 4 =
      (2 / 3 : ℝ) + (1 / 3 : ℝ) * (1 / (n : ℝ)) ^ 2 := by
  have hB : (integerInterval n).Nonempty :=
    Finset.card_pos.mp (by simpa only [card_integerInterval] using hn)
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold normalizedMoment
  rw [IntervalEnergy.normalized_fourth_moment_eq _ hB, card_integerInterval,
    IntervalEnergy.interval_energy_real]
  field_simp

theorem sincMoment_four : sincMoment 4 = 2 / 3 := by
  have hlim := tendsto_normalizedMoment_interval 2
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hlim
  have hsmall : Tendsto (fun n : ℕ => (2 / 3 : ℝ) + (1 / 3 : ℝ) *
      (1 / (n : ℝ)) ^ 2) atTop (𝓝 (2 / 3)) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using
      (tendsto_const_nhds (x := (2 / 3 : ℝ))).add
        (((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2).const_mul (1 / 3 : ℝ))
  have heq : (fun n : ℕ => normalizedMoment (integerInterval n) 4) =ᶠ[atTop]
      (fun n : ℕ => (2 / 3 : ℝ) + (1 / 3 : ℝ) * (1 / (n : ℝ)) ^ 2) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact normalizedMoment_interval_four n (by omega)
  exact tendsto_nhds_unique (hlim.congr' heq) hsmall

theorem momentCoefficient_nonneg (k : ℕ) : 0 ≤ momentCoefficient k := by
  unfold momentCoefficient
  split_ifs
  · exact sincMoment_nat_nonneg _
  · exact Real.sqrt_nonneg _

theorem momentCoefficient_le_one (k : ℕ) (hk : 2 ≤ k) : momentCoefficient k ≤ 1 := by
  unfold momentCoefficient
  split_ifs with he
  · exact sincMoment_nat_le_one k hk
  · have hk3 : 3 ≤ k := by
      by_contra! h
      have hk2 : k = 2 := by omega
      subst k
      exact he (by decide)
    have hm := sincMoment_nat_le_one (k - 1) (by omega)
    have hp := sincMoment_nat_le_one (k + 1) (by omega)
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by norm_num, ?_⟩
    have hmul := mul_le_mul hm hp (sincMoment_nat_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    simpa using hmul

end UniformMoments
end LittlewoodInverse
