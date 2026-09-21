import LittlewoodInverse.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace LittlewoodInverse

/-- A uniform bound at geometric scales gives its precise logarithmic slope. -/
theorem geometric_bounds_to_logarithmic {c : ℝ} (hc : 0 ≤ c) {base : ℕ}
    (hb : 0 < base)
    (hscale : ∀ (J : ℕ) (A : Finset ℤ), base * 9^J ≤ A.card →
      c * J ≤ littlewoodNorm A) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ A : Finset ℤ, N ≤ A.card →
      (c / Real.log 9 - δ) * Real.log (A.card : ℝ) ≤ littlewoodNorm A := by
  have hlog : 0 < Real.log 9 := Real.log_pos (by norm_num)
  let R : ℝ := c * (Real.log (base : ℝ) / Real.log 9 + 1)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (base : ℝ) (Real.exp (R/δ)))
  refine ⟨N, ?_⟩
  intro A hNA
  have hncast : (N : ℝ) ≤ A.card := by exact_mod_cast hNA
  have hbcast : (0 : ℝ) < base := by exact_mod_cast hb
  have hba : base ≤ A.card := by
    exact_mod_cast (le_max_left (base : ℝ) _).trans (hN.le.trans hncast)
  have ha : 0 < A.card := hb.trans_le hba
  have hacast : (0 : ℝ) < A.card := by exact_mod_cast ha
  let J := Nat.log 9 (A.card / base)
  have hdiv : A.card / base ≠ 0 := Nat.ne_of_gt (Nat.div_pos hba hb)
  have hj : base * 9^J ≤ A.card := by
    calc
      _ ≤ base * (A.card / base) := Nat.mul_le_mul_left _ (Nat.pow_log_le_self 9 hdiv)
      _ ≤ A.card := Nat.mul_div_le _ _
  have hu : A.card < base * 9^(J+1) := by
    have hh := (Nat.div_lt_iff_lt_mul hb).mp
      (Nat.lt_pow_succ_log_self (by norm_num : 1 < 9) (A.card / base))
    simpa only [J, Nat.succ_eq_add_one, Nat.mul_comm] using hh
  have hlu : Real.log (A.card : ℝ) ≤ Real.log (base : ℝ) +
      ((J : ℝ)+1)*Real.log 9 := by
    have hh : (A.card : ℝ) ≤ (base : ℝ) * (9 : ℝ)^(J+1) := by exact_mod_cast hu.le
    have hl := Real.log_le_log hacast hh
    rw [Real.log_mul hbcast.ne' (by positivity), Real.log_pow] at hl
    push_cast at hl
    exact hl
  have hJlower : Real.log (A.card : ℝ) / Real.log 9 -
      (Real.log (base : ℝ) / Real.log 9 + 1) ≤ J := by
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hlog).mpr
    have he : ((J : ℝ) + (Real.log (base : ℝ) / Real.log 9 + 1)) * Real.log 9 =
        Real.log (base : ℝ) + ((J : ℝ)+1)*Real.log 9 := by field_simp; ring
    rw [he]
    exact hlu
  have hr : R ≤ δ * Real.log (A.card : ℝ) := by
    have hexp : Real.exp (R/δ) ≤ (A.card : ℝ) :=
      (le_max_right _ _).trans (hN.le.trans hncast)
    have hl := (Real.le_log_iff_exp_le hacast).mpr hexp
    have := (div_le_iff₀ hδ).mp hl
    nlinarith
  calc
    _ ≤ c * (Real.log (A.card : ℝ) / Real.log 9 -
        (Real.log (base : ℝ) / Real.log 9 + 1)) := by
      convert sub_le_sub_left hr (c * (Real.log (A.card : ℝ) / Real.log 9)) using 1 <;>
        (try unfold R) <;> ring
    _ ≤ c * J := mul_le_mul_of_nonneg_left hJlower hc
    _ ≤ _ := hscale J A hj

end LittlewoodInverse
