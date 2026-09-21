import LittlewoodInverse.PeriodicBounds

open scoped BigOperators Interval
open MeasureTheory intervalIntegral

namespace LittlewoodInverse

theorem periodic_harmonic_upper {f : ℝ → ℝ} (hf : Continuous f)
    (hp : Function.Periodic f 1) (h0 : ∀ x, 0 ≤ f x) {X : ℝ} (hX : 1 ≤ X) :
    (∫ x in (1 : ℝ)..X, f x / x) ≤
      (∫ x in (0 : ℝ)..1, f x) * (Real.log X + 1) := by
  let S : ℝ := ∫ x in (0 : ℝ)..1, f x
  let n := Nat.floor X
  have hn : 1 ≤ n := (Nat.one_le_floor_iff X).mpr hX
  have hnX : (n : ℝ) ≤ X := Nat.floor_le (zero_le_one.trans hX)
  have hXn : X ≤ (n + 1 : ℕ) := by
    exact_mod_cast (Nat.lt_floor_add_one X).le
  have hS : 0 ≤ S := integral_nonneg_of_forall (by norm_num) h0
  have hlocal (j : ℕ) (hj : 1 ≤ j) :
      (∫ x in (j : ℝ)..(j + 1 : ℝ), f x / x) ≤ S / (j : ℝ) := by
    have hjR : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hmean : (∫ x in (j : ℝ)..(j + 1 : ℝ), f x) = S := by
      simpa [S] using hp.intervalIntegral_add_eq (j : ℝ) 0
    rw [← hmean, ← intervalIntegral.integral_div]
    apply integral_mono_on (by linarith)
      (continuous_intervalIntegrable_div_id hf hjR (by linarith))
      ((hf.div_const _).intervalIntegrable _ _)
    intro x hx
    exact div_le_div_of_nonneg_left (h0 x) hjR hx.1
  have hsum : (∫ x in (1 : ℝ)..(n + 1 : ℕ), f x / x) ≤ S * (harmonic n : ℝ) := by
    have hh := Finset.sum_le_sum (fun j (hj : j ∈ Finset.Ico 1 (n + 1)) =>
      hlocal j (Finset.mem_Ico.mp hj).1)
    have hleft : (∑ j ∈ Finset.Ico 1 (n + 1),
        ∫ x in (j : ℝ)..(j + 1 : ℝ), f x / x) =
        ∫ x in (1 : ℝ)..(n + 1 : ℕ), f x / x := by
      convert sum_integral_adjacent_intervals_Ico (a := fun j : ℕ => (j : ℝ))
        (show 1 ≤ n + 1 by omega)
        (fun j hj => continuous_intervalIntegrable_div_id hf
          (by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hj.1))
          (by norm_num)) using 1 <;> simp
    rw [hleft] at hh
    have hright : (∑ j ∈ Finset.Ico 1 (n + 1), S / (j : ℝ)) = S * (harmonic n : ℝ) := by
      rw [harmonic_eq_sum_Icc, Finset.Ico_add_one_right_eq_Icc]
      simp [div_eq_mul_inv, Finset.mul_sum]
    rwa [hright] at hh
  calc
    _ ≤ ∫ x in (1 : ℝ)..(n + 1 : ℕ), f x / x := by
      apply integral_mono_interval le_rfl hX hXn _
        (continuous_intervalIntegrable_div_id hf zero_lt_one (hX.trans hXn))
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact div_nonneg (h0 x) (by linarith [hx.1])
    _ ≤ S * (harmonic n : ℝ) := hsum
    _ ≤ S * (Real.log X + 1) := by
      apply mul_le_mul_of_nonneg_left _ hS
      have hh := harmonic_floor_le_one_add_log X hX
      linarith

theorem periodic_harmonic_error {f : ℝ → ℝ} (hf : Continuous f)
    (hp : Function.Periodic f 1) (h0 : ∀ x, 0 ≤ f x) {X : ℝ} (hX : 1 ≤ X) :
    |(∫ x in (1 : ℝ)..X, f x / x) -
      (∫ x in (0 : ℝ)..1, f x) * Real.log X| ≤ 2 * ∫ x in (0 : ℝ)..1, f x := by
  have hl := periodic_harmonic_lower hf hp h0 hX
  have hu := periodic_harmonic_upper hf hp h0 hX
  have hS : 0 ≤ ∫ x in (0 : ℝ)..1, f x := integral_nonneg_of_forall (by norm_num) h0
  rw [abs_le]
  constructor <;> nlinarith

end LittlewoodInverse
