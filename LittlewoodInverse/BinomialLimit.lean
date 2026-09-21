import Mathlib

open scoped BigOperators Topology
open Filter

namespace LittlewoodInverse
namespace BinomialLimit

theorem cast_choose_eq_prod (t m : ℕ) (hm : m ≤ t) :
    (t.choose m : ℝ) = (∏ i ∈ Finset.range m, ((t : ℝ) - i)) / (m.factorial : ℝ) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose t m
  rw [Nat.descFactorial_eq_prod_range] at h
  have hR : (∏ i ∈ Finset.range m, ((t - i : ℕ) : ℝ)) =
      (m.factorial : ℝ) * (t.choose m : ℝ) := by exact_mod_cast h
  have he : (∏ i ∈ Finset.range m, ((t - i : ℕ) : ℝ)) =
      ∏ i ∈ Finset.range m, ((t : ℝ) - i) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact Nat.cast_sub (le_trans (Finset.mem_range.mp hi).le hm)
  rw [he] at hR
  apply (eq_div_iff (Nat.cast_ne_zero.mpr m.factorial_ne_zero)).mpr
  nlinarith only [hR]

theorem tendsto_choose_affine_div_pow (a b m : ℕ) (ha : 0 < a) :
    Tendsto (fun n : ℕ => ((a * n + b).choose m : ℝ) / (n : ℝ)^m)
      atTop (𝓝 ((a : ℝ)^m / (m.factorial : ℝ))) := by
  have hterm (i : ℕ) : Tendsto (fun n : ℕ =>
      ((a : ℝ) * n + b - i) / n) atTop (𝓝 (a : ℝ)) := by
    have h := (tendsto_const_nhds (x := (a : ℝ))).add
      (tendsto_const_div_atTop_nhds_zero_nat ((b : ℝ) - i))
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
    ring
  have hp := tendsto_finsetProd (Finset.range m) (fun i _ => hterm i)
  simp only [Finset.prod_const, Finset.card_range] at hp
  have hfinal := hp.div_const (m.factorial : ℝ)
  apply hfinal.congr'
  filter_upwards [eventually_ge_atTop (max m 1)] with n hn
  have hn0 : 0 < n := by omega
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have ham : m ≤ a * n + b := by
    have h := Nat.mul_le_mul_right n ha
    omega
  rw [cast_choose_eq_prod _ _ ham]
  simp only [Nat.cast_add, Nat.cast_mul]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_range]
  ring

end BinomialLimit
end LittlewoodInverse
