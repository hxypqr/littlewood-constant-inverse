import LittlewoodInverse.FiniteBand
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Nat.Choose.Central

/-! # The exact square-root coefficients in Landau's bound -/

open scoped BigOperators PowerSeries

namespace LittlewoodInverse
namespace Landau

noncomputable def b (n : ℕ) : ℝ := (Nat.centralBinom n : ℝ) / (4 : ℝ) ^ n

@[simp] theorem b_zero : b 0 = 1 := by simp [b]

theorem b_pos (n : ℕ) : 0 < b n := by
  unfold b
  exact div_pos (Nat.cast_pos.mpr (Nat.centralBinom_pos n)) (by positivity)

theorem b_recurrence (n : ℕ) :
    ((n : ℝ) + 1) * b (n + 1) = ((n : ℝ) + 1 / 2) * b n := by
  have hh : ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ) =
      2 * (2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  unfold b
  rw [pow_succ]
  field_simp
  nlinarith

theorem b_succ_lt (n : ℕ) : b (n + 1) < b n := by
  have hh := b_recurrence n
  have hp := b_pos n
  nlinarith

theorem b_antitone : Antitone b := antitone_nat_of_succ_le (fun n ↦ (b_succ_lt n).le)

noncomputable def series : PowerSeries ℝ := PowerSeries.mk b

@[simp] theorem coeff_series (n : ℕ) : PowerSeries.coeff n series = b n :=
  PowerSeries.coeff_mk n b

theorem series_differential :
    (1 - PowerSeries.X) * (PowerSeries.derivative ℝ series) = PowerSeries.C (1 / 2) * series := by
  ext n
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_C_mul]
  cases n with
  | zero =>
    simp only [PowerSeries.coeff_derivative, coeff_series, zero_add, Nat.cast_zero, mul_one]
    simp only [PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
      PowerSeries.constantCoeff_X, zero_mul]
    have hh := b_recurrence 0
    norm_num at hh ⊢
    linarith
  | succ n =>
    rw [PowerSeries.coeff_succ_X_mul]
    simp only [PowerSeries.coeff_derivative, coeff_series]
    have hh := b_recurrence (n + 1)
    push_cast at hh ⊢
    linarith

theorem square_series_differential :
    (1 - PowerSeries.X) * (PowerSeries.derivative ℝ (series * series)) = series * series := by
  rw [(PowerSeries.derivative ℝ).leibniz]
  simp only [smul_eq_mul]
  calc
    _ = (PowerSeries.C (2 : ℝ) * series) *
        ((1 - PowerSeries.X) * (PowerSeries.derivative ℝ series)) := by
      simp only [map_ofNat]
      ring
    _ = (PowerSeries.C (2 : ℝ) * series) * (PowerSeries.C (1 / 2) * series) := by
      rw [series_differential]
    _ = series * series := by
      rw [mul_mul_mul_comm, ← map_mul]
      norm_num

theorem coeff_square_series (n : ℕ) : PowerSeries.coeff n (series * series) = 1 := by
  induction n with
  | zero =>
    simp only [PowerSeries.coeff_zero_eq_constantCoeff, map_mul]
    change b 0 * b 0 = 1
    simp
  | succ n ih =>
    have hh := congrArg (PowerSeries.coeff n) square_series_differential
    rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_derivative] at hh
    cases n with
    | zero =>
      simp only [PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
        PowerSeries.constantCoeff_X, zero_mul, sub_zero, zero_add, Nat.cast_zero,
        mul_one] at hh
      exact hh.trans (by simpa only [PowerSeries.coeff_zero_eq_constantCoeff, map_mul] using ih)
    | succ n =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, ih] at hh
      push_cast at hh
      have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      nlinarith

theorem coefficient_convolution (n : ℕ) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, b ij.1 * b ij.2) = 1 := by
  have hh := coeff_square_series n
  simpa only [PowerSeries.coeff_mul, coeff_series] using hh

end Landau
end LittlewoodInverse
