import Mathlib

open scoped BigOperators Interval
open MeasureTheory intervalIntegral

namespace LittlewoodInverse

theorem continuous_intervalIntegrable_div_id {f : ℝ → ℝ} (hf : Continuous f)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun x => f x / x) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  exact hf.continuousOn.div continuousOn_id (fun x hx => (ha.trans_le hx.1).ne')

theorem periodic_integral_upto_le {f : ℝ → ℝ} (hf : Continuous f)
    (hp : Function.Periodic f 1) (h0 : ∀ x, 0 ≤ f x) {X : ℝ} (hX : 0 ≤ X) :
    (∫ x in 0..X, f x) ≤ (X + 1) * ∫ x in (0 : ℝ)..1, f x := by
  have hS : 0 ≤ ∫ x in (0 : ℝ)..1, f x := integral_nonneg_of_forall (by norm_num) h0
  let n := Nat.floor X + 1
  have hnX : X ≤ (n : ℝ) := by simpa [n] using (Nat.lt_floor_add_one X).le
  have hXn : (n : ℝ) ≤ X + 1 := by
    dsimp [n]
    push_cast
    linarith [Nat.floor_le hX]
  have hni : (∫ x in (0 : ℝ)..(n : ℝ), f x) =
      (n : ℝ) * ∫ x in (0 : ℝ)..1, f x := by
    simpa only [zero_add, zsmul_eq_mul, Int.cast_natCast, mul_one] using
      hp.intervalIntegral_add_zsmul_eq (n : ℤ) 0 hf.intervalIntegrable
  calc
    _ ≤ ∫ x in (0 : ℝ)..(n : ℝ), f x :=
      integral_mono_interval le_rfl hX hnX (Filter.Eventually.of_forall h0)
        (hf.intervalIntegrable _ _)
    _ = _ := hni
    _ ≤ _ := mul_le_mul_of_nonneg_right hXn hS

/-- A full-period harmonic lower bound; no integrability at zero is
required because the first unit interval is discarded. -/
theorem periodic_harmonic_lower {f : ℝ → ℝ} (hf : Continuous f)
    (hp : Function.Periodic f 1) (h0 : ∀ x, 0 ≤ f x) {X : ℝ} (hX : 1 ≤ X) :
    (∫ x in (0 : ℝ)..1, f x) * (Real.log X - 2) ≤ ∫ x in (1 : ℝ)..X, f x / x := by
  let S : ℝ := ∫ x in (0 : ℝ)..1, f x
  let n := Nat.floor X
  have hn : 1 ≤ n := (Nat.one_le_floor_iff X).mpr hX
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnX : (n : ℝ) ≤ X := Nat.floor_le (zero_le_one.trans hX)
  have hS : 0 ≤ S := integral_nonneg_of_forall (by norm_num) h0
  have hlocal (j : ℕ) (hj : 1 ≤ j) :
      S / (j + 1 : ℝ) ≤ ∫ x in (j : ℝ)..(j + 1 : ℝ), f x / x := by
    have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have hmean : (∫ x in (j : ℝ)..(j + 1 : ℝ), f x) = S := by
      simpa [S] using hp.intervalIntegral_add_eq (j : ℝ) 0
    rw [← hmean, ← intervalIntegral.integral_div]
    apply integral_mono_on (by linarith) ((hf.div_const _).intervalIntegrable _ _)
      (continuous_intervalIntegrable_div_id hf (by linarith) (by linarith))
    intro x hx
    exact div_le_div_of_nonneg_left (h0 x) (by linarith [hx.1]) hx.2
  have hsum : S * ((harmonic n : ℝ) - 1) ≤ ∫ x in (1 : ℝ)..(n : ℝ), f x / x := by
    have hh := Finset.sum_le_sum (fun j (hj : j ∈ Finset.Ico 1 n) =>
      hlocal j (Finset.mem_Ico.mp hj).1)
    have hright : (∑ j ∈ Finset.Ico 1 n,
        ∫ x in (j : ℝ)..(j + 1 : ℝ), f x / x) =
        ∫ x in (1 : ℝ)..(n : ℝ), f x / x := by
      convert sum_integral_adjacent_intervals_Ico (a := fun j : ℕ => (j : ℝ)) hn
        (fun j hj => continuous_intervalIntegrable_div_id hf
          (by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hj.1))
          (by norm_num)) using 1 <;> simp
    rw [hright] at hh
    have hleft : (∑ j ∈ Finset.Ico 1 n, S / (j + 1 : ℝ)) = S * ((harmonic n : ℝ) - 1) := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.mul_sum, Finset.sum_Ico_eq_sub _ hn]
      congr 1
      simp [harmonic]
    rwa [hleft] at hh
  have hlog : Real.log X ≤ (harmonic n : ℝ) := by
    have hxlt : X < (n : ℝ) + 1 := Nat.lt_floor_add_one X
    exact (Real.log_le_log (zero_lt_one.trans_le hX) hxlt.le).trans
      (by exact_mod_cast log_add_one_le_harmonic n)
  calc
    S * (Real.log X - 2) ≤ S * ((harmonic n : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hS
    _ ≤ ∫ x in (1 : ℝ)..(n : ℝ), f x / x := hsum
    _ ≤ ∫ x in (1 : ℝ)..X, f x / x := by
      apply integral_mono_interval le_rfl hnR hnX _
        (continuous_intervalIntegrable_div_id hf zero_lt_one hX)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact div_nonneg (h0 x) (by linarith [hx.1])

theorem integral_scaled_div_id (f : ℝ → ℝ) {m : ℝ} (hm : m ≠ 0) (a b : ℝ) :
    (∫ x in a..b, f (m * x) / x) = ∫ u in (m * a)..(m * b), f u / u := by
  have he (x : ℝ) : f (m * x) / x = m * (f (m * x) / (m * x)) := by
    rw [div_mul_eq_div_div, ← mul_div_assoc, mul_div_cancel₀ _ hm]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  simpa only [smul_eq_mul] using
    intervalIntegral.smul_integral_comp_mul_left (fun u => f u / u) (a := a) (b := b) m

theorem periodic_scaled_integral_le {f : ℝ → ℝ} (hf : Continuous f)
    (hp : Function.Periodic f 1) (h0 : ∀ x, 0 ≤ f x)
    {m a : ℝ} (hm : 0 < m) (ha : 0 ≤ a) :
    (∫ x in (0 : ℝ)..a, f (m * x)) ≤
      (a + 1 / m) * ∫ x in (0 : ℝ)..1, f x := by
  rw [intervalIntegral.integral_comp_mul_left f hm.ne', mul_zero, smul_eq_mul]
  have hi := periodic_integral_upto_le hf hp h0 (mul_nonneg hm.le ha)
  have hh := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hm.le)
  calc
    _ ≤ m⁻¹ * ((m * a + 1) * ∫ x in (0 : ℝ)..1, f x) := hh
    _ = _ := by
      rw [← mul_assoc, mul_add, ← mul_assoc, inv_mul_cancel₀ hm.ne', one_mul, mul_one,
        one_div]

end LittlewoodInverse
