import LittlewoodInverse.MajorityCounting

open scoped BigOperators

namespace LittlewoodInverse
namespace MajorityCounting

theorem factorial_ratio_ge_exp_neg (k : ℕ) (hk : 0 < k) :
    Real.exp (-(k : ℝ)) ≤ (k.factorial : ℝ) / (k : ℝ)^k := by
  have hfact : (0 : ℝ) < k.factorial := Nat.cast_pos.mpr k.factorial_pos
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have h := (div_le_iff₀ hfact).mp (Real.pow_div_factorial_le_exp (k : ℝ) hkR.le k)
  have hmul := mul_le_mul_of_nonneg_left h (Real.exp_pos (-(k : ℝ))).le
  have hexp : Real.exp (-(k : ℝ)) * Real.exp k = 1 := by
    rw [← Real.exp_add]
    simp
  apply (le_div_iff₀ (pow_pos hkR k)).mpr
  calc
    _ ≤ Real.exp (-(k : ℝ)) * (Real.exp k * (k.factorial : ℝ)) := hmul
    _ = _ := by rw [← mul_assoc, hexp, one_mul]

/-- The loss from sampling distinct ordered entries is at most `exp(k)`,
even when the ambient cardinality equals the tuple length. -/
theorem descFactorial_ge_exp_neg (r k : ℕ) (hk : k ≤ r) :
    Real.exp (-(k : ℝ)) * (r : ℝ)^k ≤ (r.descFactorial k : ℝ) := by
  by_cases hk0 : k = 0
  · simp [hk0]
  have hkpos : 0 < k := by omega
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hkpos
  have hrR : (0 : ℝ) < r := Nat.cast_pos.mpr (by omega)
  have hterm (i : ℕ) (hi : i ∈ Finset.range k) :
      ((k - i : ℕ) : ℝ) / k ≤ ((r - i : ℕ) : ℝ) / r := by
    have hik : i ≤ k := (Finset.mem_range.mp hi).le
    have hir : i ≤ r := hik.trans hk
    rw [Nat.cast_sub hik, Nat.cast_sub hir]
    apply (div_le_div_iff₀ hkR hrR).mpr
    have hkr : (k : ℝ) ≤ r := by exact_mod_cast hk
    nlinarith [Nat.cast_nonneg (α := ℝ) i]
  have hp := Finset.prod_le_prod (s := Finset.range k)
    (fun i _ => by positivity : ∀ i ∈ Finset.range k, (0 : ℝ) ≤ ((k - i : ℕ) : ℝ) / k) hterm
  simp only [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range,
    ← Nat.cast_prod, ← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self] at hp
  have hbound := (factorial_ratio_ge_exp_neg k hkpos).trans hp
  exact (le_div_iff₀ (pow_pos hrR k)).mp hbound

theorem split_factorial_ge (s t : ℕ) :
    ((s + t).factorial : ℝ) / (2 : ℝ)^(s + t) ≤ (s.factorial : ℝ) * t.factorial := by
  have hchoose := Nat.choose_le_two_pow (s + t) s
  have hmul := Nat.mul_le_mul_right (s.factorial * t.factorial) hchoose
  have he := Nat.choose_mul_factorial_mul_factorial (n := s + t) (k := s) (by omega)
  simp only [Nat.add_sub_cancel_left] at he
  have hle : (s + t).factorial ≤ 2^(s+t) * (s.factorial * t.factorial) := by
    rw [← he]
    nlinarith only [hmul]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2^(s+t))).mpr
  exact_mod_cast (by nlinarith only [hle] : (s+t).factorial ≤ s.factorial * t.factorial * 2^(s+t))

/-- Combine subset density, orientation permutations, and the loss from
distinct sampling into the ordered-tuple lower bound. -/
theorem ordered_density_lower (r s t : ℕ) (hk : s + t ≤ r)
    (D G Q : ℝ) (hD : 0 < D)
    (hG : (r.choose (s + t) : ℝ) / D ≤ G)
    (hQ : G * (s.factorial : ℝ) * (t.factorial : ℝ) ≤ Q) :
    Real.exp (-((s + t : ℕ) : ℝ)) * (r : ℝ)^(s + t) /
      (D * (2 : ℝ)^(s + t)) ≤ Q := by
  have hs := split_factorial_ge s t
  have hchoose : (0 : ℝ) ≤ r.choose (s + t) := Nat.cast_nonneg _
  have hprod := mul_le_mul_of_nonneg_left hs (div_nonneg hchoose hD.le)
  have hcount := mul_le_mul_of_nonneg_right hG
    (show (0 : ℝ) ≤ (s.factorial : ℝ) * (t.factorial : ℝ) by positivity)
  have hid : (r.choose (s + t) : ℝ) / D *
      ((s + t).factorial : ℝ) / (2 : ℝ)^(s + t) =
      (r.descFactorial (s + t) : ℝ) / (D * (2 : ℝ)^(s + t)) := by
    have he : (r.descFactorial (s + t) : ℝ) =
        ((s + t).factorial : ℝ) * (r.choose (s + t) : ℝ) := by
      exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose r (s + t)
    rw [he]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hbound : (r.descFactorial (s + t) : ℝ) /
      (D * (2 : ℝ)^(s + t)) ≤ Q := by
    rw [← hid]
    have hp : (r.choose (s + t) : ℝ) / D *
        ((s + t).factorial : ℝ) / (2 : ℝ)^(s + t) ≤
        (r.choose (s + t) : ℝ) / D * ((s.factorial : ℝ) * (t.factorial : ℝ)) := by
      simpa only [div_eq_mul_inv, mul_assoc] using hprod
    nlinarith only [hp, hcount, hQ]
  exact (div_le_div_of_nonneg_right (descFactorial_ge_exp_neg r (s + t) hk)
    (by positivity)).trans hbound

end MajorityCounting
end LittlewoodInverse
