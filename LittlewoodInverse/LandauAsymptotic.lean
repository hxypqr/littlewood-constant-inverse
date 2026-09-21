import LittlewoodInverse.LandauCoefficients
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds

open scoped BigOperators

namespace LittlewoodInverse
namespace Landau

/-- The finite Wallis identity gives the needed asymptotic without a
separate Stirling assumption. -/
theorem b_sq_wallis (n : ℕ) : b n ^ 2 * Real.Wallis.W n * (2 * (n : ℝ) + 1) = 1 := by
  induction n with
  | zero => simp [Real.Wallis.W]
  | succ n ih =>
    have hb : b (n + 1) = (((n : ℝ) + 1 / 2) * b n) / ((n : ℝ) + 1) :=
      (eq_div_iff (by positivity)).mpr (by simpa only [mul_comm] using b_recurrence n)
    rw [hb, Real.Wallis.W_succ]
    push_cast
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have hn2 : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
    have hn3 : 2 * (n : ℝ) + 3 ≠ 0 := by positivity
    field_simp
    nlinarith [ih]

theorem b_sq_eq_wallis_inv (n : ℕ) :
    b n ^ 2 = 1 / (Real.Wallis.W n * (2 * (n : ℝ) + 1)) := by
  apply (eq_div_iff (mul_ne_zero (Real.Wallis.W_pos n).ne'
    (by positivity : 2 * (n : ℝ) + 1 ≠ 0))).mpr
  simpa only [mul_assoc] using b_sq_wallis n

theorem b_sq_lower (n : ℕ) : 1 / (Real.pi * ((n : ℝ) + 1)) ≤ b n ^ 2 := by
  rw [b_sq_eq_wallis_inv]
  apply one_div_le_one_div_of_le
  · exact mul_pos (Real.Wallis.W_pos n) (by positivity)
  · have hw := Real.Wallis.W_le n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hw (show 0 ≤ 2 * (n : ℝ) + 1 by positivity),
      Real.pi_pos]

theorem b_sq_upper (n : ℕ) (hn : 0 < n) : b n ^ 2 ≤ 1 / (Real.pi * n) := by
  rw [b_sq_eq_wallis_inv]
  apply one_div_le_one_div_of_le (mul_pos Real.pi_pos (Nat.cast_pos.mpr hn))
  have hw := Real.Wallis.le_W n
  have hp : 0 < 2 * (n : ℝ) + 2 := by positivity
  have he : (2 * (n : ℝ) + 1) * Real.pi ≤
      2 * (2 * (n : ℝ) + 2) * Real.Wallis.W n := by
    have h := mul_le_mul_of_nonneg_right hw hp.le
    field_simp at h
    nlinarith
  have hm := mul_le_mul_of_nonneg_right he (show 0 ≤ 2 * (n : ℝ) + 1 by positivity)
  have hh : 0 < (n : ℝ) + 1 := by positivity
  nlinarith [Real.pi_pos]

theorem sum_b_sq_lower (N : ℕ) :
    (harmonic N : ℝ) / Real.pi ≤ ∑ k ∈ Finset.range N, b k ^ 2 := by
  calc
    _ = ∑ k ∈ Finset.range N, 1 / (Real.pi * ((k : ℝ) + 1)) := by
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv,
        Nat.cast_add, Nat.cast_one, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      simp [div_eq_mul_inv, mul_comm]
    _ ≤ _ := Finset.sum_le_sum fun k _ => b_sq_lower k

theorem sum_b_sq_upper_succ (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), b k ^ 2) ≤ 1 + (harmonic N : ℝ) / Real.pi := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hb := b_sq_upper (N + 1) (by omega)
    rw [harmonic_succ]
    push_cast
    push_cast at hb
    calc
      _ ≤ (1 + (harmonic N : ℝ) / Real.pi) + 1 / (Real.pi * ((N : ℝ) + 1)) :=
        add_le_add ih hb
      _ = _ := by simp [div_eq_mul_inv]; ring

theorem sum_b_sq_upper (N : ℕ) :
    (∑ k ∈ Finset.range N, b k ^ 2) ≤ 1 + (harmonic N : ℝ) / Real.pi := by
  have hh := sum_b_sq_upper_succ N
  rw [Finset.sum_range_succ] at hh
  linarith [sq_nonneg (b N)]

/-- A fully explicit bounded-error form of the Landau constant asymptotic. -/
theorem sum_b_sq_log_error (N : ℕ) (hN : 0 < N) :
    |(∑ k ∈ Finset.range N, b k ^ 2) - Real.log N / Real.pi| ≤ 2 := by
  have hlo : Real.log (N : ℝ) ≤ (harmonic N : ℝ) := by
    have hl := log_add_one_le_harmonic N
    have hh : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 1) :=
      Real.log_le_log (Nat.cast_pos.mpr hN) (by linarith)
    exact hh.trans (by exact_mod_cast hl)
  have hhi : (harmonic N : ℝ) ≤ 1 + Real.log (N : ℝ) := harmonic_le_one_add_log N
  have hl := (div_le_div_of_nonneg_right hlo Real.pi_pos.le).trans (sum_b_sq_lower N)
  have hu := (sum_b_sq_upper N).trans
    (add_le_add (le_refl (1 : ℝ)) (div_le_div_of_nonneg_right hhi Real.pi_pos.le))
  have hpi : 1 / Real.pi ≤ 1 := (div_le_one Real.pi_pos).mpr (by linarith [Real.pi_gt_three])
  rw [add_div] at hu
  apply abs_le.mpr
  constructor <;> linarith

theorem b_le_inv_sqrt (n : ℕ) (hn : 0 < n) : b n ≤ 1 / Real.sqrt n := by
  have hbound : b n ^ 2 ≤ 1 / (n : ℝ) :=
    (b_sq_upper n hn).trans (one_div_le_one_div_of_le (Nat.cast_pos.mpr hn)
      (by nlinarith [Real.pi_gt_three, (show (0 : ℝ) < n from Nat.cast_pos.mpr hn)]))
  calc
    _ ≤ Real.sqrt (1 / (n : ℝ)) :=
      (Real.le_sqrt (b_pos n).le (by positivity)).mpr hbound
    _ = _ := by rw [Real.sqrt_div zero_le_one, Real.sqrt_one]

end Landau
end LittlewoodInverse
