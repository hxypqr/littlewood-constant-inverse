import LittlewoodInverse.UniformMoments

open scoped BigOperators Topology
open MeasureTheory Filter

namespace LittlewoodInverse
namespace FirstLevelUniform

open ScalarCoupling IntervalMoments UniformMoments

/-- A common finite-cardinality upper bound for all integer sets. -/
noncomputable def momentEnvelope (n k : ℕ) : ℝ :=
  if Even k then normalizedMoment (integerInterval n) k
  else Real.sqrt (normalizedMoment (integerInterval n) (k - 1) *
    normalizedMoment (integerInterval n) (k + 1))

theorem momentEnvelope_nonneg (n k : ℕ) : 0 ≤ momentEnvelope n k := by
  unfold momentEnvelope
  split_ifs
  · exact normalizedMoment_nonneg _ _
  · exact Real.sqrt_nonneg _

theorem normalizedMoment_le_envelope (B : Finset ℤ) (k : ℕ) :
    normalizedMoment B k ≤ momentEnvelope B.card k := by
  unfold momentEnvelope
  split_ifs with he
  · obtain ⟨r, hr⟩ := he
    have hk : k = 2 * r := by omega
    rw [hk]
    exact normalizedMoment_even_le_interval B r
  · have ho := (Nat.even_or_odd k).resolve_left he
    obtain ⟨r, hr⟩ := ho
    have hk : k = 2 * r + 1 := by omega
    rw [hk]
    have hm : 2 * r + 1 - 1 = 2 * r := by omega
    have hp : 2 * r + 1 + 1 = 2 * r + 2 := by omega
    rw [hm, hp]
    exact normalizedMoment_odd_le_interval_sqrt B r

theorem momentEnvelope_le_one (n k : ℕ) (hn : 0 < n) (hk : 2 ≤ k) :
    momentEnvelope n k ≤ 1 := by
  have hB : (integerInterval n).Nonempty :=
    Finset.card_pos.mp (by rwa [card_integerInterval])
  unfold momentEnvelope
  split_ifs with he
  · exact normalized_moment_le_one _ hB k hk
  · have hk3 : 3 ≤ k := by
      by_contra! h
      have hk2 : k = 2 := by omega
      subst k
      exact he (by decide)
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by norm_num, ?_⟩
    have hmul := mul_le_mul
      (normalized_moment_le_one _ hB (k - 1) (by omega))
      (normalized_moment_le_one _ hB (k + 1) (by omega))
      (normalizedMoment_nonneg _ _) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul, one_pow, normalizedMoment] using hmul

theorem tendsto_momentEnvelope (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun n : ℕ => momentEnvelope n k) atTop (𝓝 (momentCoefficient k)) := by
  have hlim (j : ℕ) (hj : 2 ≤ j) :
      Tendsto (fun n : ℕ => normalizedMoment (integerInterval n) j)
        atTop (𝓝 (sincMoment (j : ℝ))) := by
    have he : j - 2 + 2 = j := by omega
    simpa only [he] using tendsto_normalizedMoment_interval (j - 2)
  unfold momentEnvelope momentCoefficient
  split_ifs with he
  · exact hlim k hk
  · have hk3 : 3 ≤ k := by
      by_contra! h
      have hk2 : k = 2 := by omega
      subst k
      exact he (by decide)
    exact ((hlim (k - 1) (by omega)).mul (hlim (k + 1) (by omega))).sqrt

theorem summable_weighted_envelope (n : ℕ) (hn : 0 < n)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Summable (fun j : ℕ => a ^ (j + 5) / ((j : ℝ) + 5) * momentEnvelope n (j + 5)) := by
  apply (hasSum_tailFromFive (by rwa [abs_of_nonneg ha0] : |a| < 1)).summable.of_norm_bounded
  intro j
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (momentEnvelope_nonneg n _))]
  exact mul_le_of_le_one_right (by positivity) (momentEnvelope_le_one n _ hn (by omega))

theorem tendsto_weighted_envelope {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Tendsto (fun n : ℕ => ∑' j : ℕ, a ^ (j + 5) / ((j : ℝ) + 5) * momentEnvelope n (j + 5))
      atTop (𝓝 (∑' j : ℕ, a ^ (j + 5) / ((j : ℝ) + 5) * momentCoefficient (j + 5))) := by
  apply tendsto_tsum_of_dominated_convergence
    (hasSum_tailFromFive (by rwa [abs_of_nonneg ha0] : |a| < 1)).summable
  · intro j
    exact (tendsto_momentEnvelope (j + 5) (by omega)).const_mul _
  · filter_upwards [eventually_ge_atTop 1] with n hn j
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (momentEnvelope_nonneg n _))]
    exact mul_le_of_le_one_right (by positivity) (momentEnvelope_le_one n _ (by omega) (by omega))

theorem normalized_series_le_envelope (B : Finset ℤ) (hB : B.Nonempty)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    (∑' j : ℕ, a ^ (j + 5) / ((j : ℝ) + 5) * normalizedMoment B (j + 5)) ≤
      ∑' j : ℕ, a ^ (j + 5) / ((j : ℝ) + 5) * momentEnvelope B.card (j + 5) := by
  have hs : Summable (fun j : ℕ => a ^ (j + 5) / ((j : ℝ) + 5) *
      normalizedMoment B (j + 5)) := by
    apply (hasSum_tailFromFive (by rwa [abs_of_nonneg ha0] : |a| < 1)).summable.of_norm_bounded
    intro j
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (normalizedMoment_nonneg B _))]
    exact mul_le_of_le_one_right (by positivity) (normalized_moment_le_one B hB _ (by omega))
  exact Summable.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left
    (normalizedMoment_le_envelope B _) (by positivity)) hs
      (summable_weighted_envelope B.card hB.card_pos ha0 ha1)

noncomputable def delta (a : ℝ) : ℝ :=
  (2 / 3 : ℝ) * (5 * a ^ 4 / 6 - 2 * a ^ 3 / 3) +
    2 * ∑' j : ℕ, a ^ (j + 5) / ((j : ℝ) + 5) * momentCoefficient (j + 5)

/-- The previously proved exact scalar expansion now has the actual
uniform asymptotic constants.  The infinite series is handled by Tannery's
theorem with a summable bound independent of the set. -/
theorem first_level_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ B : Finset ℤ, N ≤ B.card →
      (B.card : ℝ) * (∫ t, h (9 / 10) (normalizedMagnitude B t) +
        (1 / 3 : ℝ) * OuterAlgebra.q (9 / 10) (normalizedMagnitude B t) ^ 2 ∂circleMeasure) ≤
      10 * (9 / 10 : ℝ)^2 / 3 + delta (9 / 10) + ε := by
  let c : ℝ := 5 * (9 / 10 : ℝ)^4 / 6 - 2 * (9 / 10 : ℝ)^3 / 3
  have hc : 0 ≤ c := by norm_num [c]
  let G : ℕ → ℝ := fun n => 10 * (9 / 10 : ℝ)^2 / 3 +
    c * normalizedMoment (integerInterval n) 4 +
    2 * ∑' j : ℕ, (9 / 10 : ℝ) ^ (j + 5) / ((j : ℝ) + 5) * momentEnvelope n (j + 5)
  have hfour := tendsto_normalizedMoment_interval 2
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hfour
  rw [sincMoment_four] at hfour
  have hlim : Tendsto G atTop (𝓝 (10 * (9 / 10 : ℝ)^2 / 3 + delta (9 / 10))) := by
    have ht := ((tendsto_const_nhds (x := 10 * (9 / 10 : ℝ)^2 / 3)).add (hfour.const_mul c)).add
      ((tendsto_weighted_envelope (by norm_num : (0 : ℝ) ≤ 9 / 10)
        (by norm_num : (9 / 10 : ℝ) < 1)).const_mul 2)
    have hval : 10 * (9 / 10 : ℝ)^2 / 3 + c * (2 / 3) +
        2 * (∑' j : ℕ, (9 / 10 : ℝ) ^ (j + 5) / ((j : ℝ) + 5) *
          momentCoefficient (j + 5)) = 10 * (9 / 10 : ℝ)^2 / 3 + delta (9 / 10) := by
      dsimp only [delta, c]
      ring
    rw [hval] at ht
    exact ht
  have hev := hlim.eventually (gt_mem_nhds (show
    10 * (9 / 10 : ℝ)^2 / 3 + delta (9 / 10) <
      10 * (9 / 10 : ℝ)^2 / 3 + delta (9 / 10) + ε by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨max N 1, ?_⟩
  intro B hBN
  have hB : B.Nonempty := Finset.card_pos.mp (by omega)
  have hbase := first_level_integral B hB (a := (9 / 10 : ℝ)) (by norm_num) (by norm_num)
  have hfourB := mul_le_mul_of_nonneg_left (normalizedMoment_even_le_interval B 2) hc
  norm_num only [Nat.reduceMul] at hfourB
  have hseries := normalized_series_le_envelope B hB (a := (9 / 10 : ℝ))
    (by norm_num) (by norm_num)
  have hGb : G B.card < 10 * (9 / 10 : ℝ)^2 / 3 + delta (9 / 10) + ε :=
    hN B.card (by omega)
  change _ ≤ 10 * (9 / 10 : ℝ)^2 / 3 + c * normalizedMoment B 4 +
    2 * (∑' j : ℕ, (9 / 10 : ℝ) ^ (j + 5) / ((j : ℝ) + 5) * normalizedMoment B (j + 5)) at hbase
  dsimp only [G] at hGb
  linarith

end FirstLevelUniform
end LittlewoodInverse
