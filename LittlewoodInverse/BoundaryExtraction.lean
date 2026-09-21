import LittlewoodInverse.BlockBoundaryIntegral

open scoped BigOperators

namespace LittlewoodInverse

variable (q : ℕ) [NeZero q]

/-- The uniform boundary extraction inequality of Section 7. Its boundary
norm and mass are computed from the actual integer-valued jump function. -/
theorem uniform_boundary_extraction {M : ℕ} (hM : 0 < M)
    {C : Finset (ZMod q × ℤ)} (hC : C.Nonempty) :
    boundaryNorm q C / Real.pi *
        Real.log ((M : ℝ) * boundaryNorm q C / Real.sqrt (boundaryMass C : ℝ)) -
      4 * boundaryNorm q C ≤ littlewoodNorm (blockInflation q M C) := by
  let S := boundaryNorm q C
  let H := Real.sqrt (boundaryMass C : ℝ)
  have hs1 : 1 ≤ S := one_le_boundaryNorm q hC
  have hs : 0 < S := lt_of_lt_of_le zero_lt_one hs1
  have hH : 0 < H := Real.sqrt_pos.mpr (by exact_mod_cast boundaryMass_pos hC)
  have hsH : S ≤ H := boundaryNorm_le_sqrt_mass q C
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hratio : 0 < (M : ℝ) * S / H := by positivity
  have hlog4 : Real.log 4 ≤ 3 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hpi : 3 < Real.pi := Real.pi_gt_three
  by_cases hl : 4 ≤ (M : ℝ) * S / H
  · let a := S / (4 * H)
    have ha0 : 0 < a := by positivity
    have ha4 : a ≤ 1 / 4 := by
      apply (div_le_iff₀ (by positivity : 0 < 4 * H)).mpr
      nlinarith
    have hMa : 1 ≤ (M : ℝ) * a := by
      dsimp [a]
      rw [← mul_div_assoc]
      apply (le_div_iff₀ (by positivity : 0 < 4 * H)).mpr
      have hh := (le_div_iff₀ hH).mp hl
      nlinarith
    have hi := boundary_arc_lower q hM C (show a ≤ 1 / 2 by linarith) hMa
    have hia : 1 / (M : ℝ) ≤ a := (div_le_iff₀ hm).mpr (by nlinarith)
    have herr : 2 * (a + 1 / (M : ℝ)) * H ≤ S := by
      have hae : 4 * a * H = S := by dsimp [a]; field_simp
      nlinarith
    have he : (M : ℝ) * a = ((M : ℝ) * S / H) / 4 := by dsimp [a]; ring
    have hlog : Real.log ((M : ℝ) * a) =
        Real.log ((M : ℝ) * S / H) - Real.log 4 := by
      rw [he, Real.log_div hratio.ne' (by norm_num)]
    change S / Real.pi * (Real.log ((M : ℝ) * a) - 2) -
      2 * (a + 1 / (M : ℝ)) * H ≤ _ at hi
    rw [hlog] at hi
    have hsdiv : 0 < S / Real.pi := div_pos hs Real.pi_pos
    have hconst : S / Real.pi * (Real.log 4 + 2) + S ≤ 4 * S := by
      have hbase : Real.log 4 + 2 ≤ 3 * Real.pi := by linarith
      have hx := mul_le_mul_of_nonneg_left hbase hsdiv.le
      have heq : S / Real.pi * (3 * Real.pi) = 3 * S := by field_simp
      rw [heq] at hx
      linarith
    change S / Real.pi * Real.log ((M : ℝ) * S / H) - 4 * S ≤ _
    nlinarith
  · have hlog := Real.log_le_log hratio (le_of_lt (lt_of_not_ge hl))
    have hlogpi : Real.log ((M : ℝ) * S / H) ≤ 4 * Real.pi := by linarith
    have hx := mul_le_mul_of_nonneg_left hlogpi (div_nonneg hs.le Real.pi_pos.le)
    have heq : S / Real.pi * (4 * Real.pi) = 4 * S := by field_simp
    rw [heq] at hx
    exact (sub_nonpos.mpr hx).trans (littlewoodNorm_nonneg _)

theorem boundary_log_ratio_lower {M : ℕ}
    {C : Finset (ZMod q × ℤ)} (hC : C.Nonempty) (hMC : C.card ≤ M) :
    (Real.log (M : ℝ) - 1) / 2 ≤
      Real.log ((M : ℝ) * boundaryNorm q C / Real.sqrt (boundaryMass C : ℝ)) := by
  have hm : (0 : ℝ) < M := by exact_mod_cast (C.card_pos.mpr hC).trans_le hMC
  have hs1 := one_le_boundaryNorm q hC
  have hs : 0 < boundaryNorm q C := by linarith
  have hh : (0 : ℝ) < boundaryMass C := by exact_mod_cast boundaryMass_pos hC
  have hH : 0 < Real.sqrt (boundaryMass C : ℝ) := Real.sqrt_pos.mpr hh
  have hmass : (boundaryMass C : ℝ) ≤ 2 * M := by
    exact_mod_cast (boundaryMass_le C).trans (Nat.mul_le_mul_left 2 hMC)
  have hlogmass := Real.log_le_log hh hmass
  rw [Real.log_mul (by norm_num) hm.ne'] at hlogmass
  have hlog2 : Real.log 2 ≤ 1 := by
    have hi := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  rw [Real.log_div (mul_pos hm hs).ne' hH.ne', Real.log_mul hm.ne' hs.ne',
    Real.log_sqrt hh.le]
  have hlogs := Real.log_nonneg hs1
  linarith

/-- A concrete absolute constant in the long-block boundary budget. -/
theorem constant_boundary_budget_of_log {M : ℕ}
    {C : Finset (ZMod q × ℤ)} (hC : C.Nonempty) (hMC : C.card ≤ M)
    {K : ℝ} (hK : 0 ≤ K) (hlarge : 16 * Real.pi + 2 ≤ Real.log (M : ℝ))
    (hnorm : littlewoodNorm (blockInflation q M C) ≤
      K * Real.log ((M : ℝ) * C.card)) : boundaryNorm q C ≤ 8 * Real.pi * K := by
  have hM : 0 < M := (C.card_pos.mpr hC).trans_le hMC
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hV : (0 : ℝ) < C.card := by exact_mod_cast C.card_pos.mpr hC
  have hvm : (C.card : ℝ) ≤ M := by exact_mod_cast hMC
  have hlm : 0 < Real.log (M : ℝ) := by linarith [Real.pi_pos]
  have hex := uniform_boundary_extraction q hM hC
  have hratio := boundary_log_ratio_lower q hC hMC
  have hs := (one_le_boundaryNorm q hC).trans' zero_le_one
  have hsc : 0 ≤ boundaryNorm q C / Real.pi := div_nonneg hs Real.pi_pos.le
  have hx := mul_le_mul_of_nonneg_left hratio hsc
  have hlogV := Real.log_le_log hV hvm
  rw [Real.log_mul hm.ne' hV.ne'] at hnorm
  have hu : littlewoodNorm (blockInflation q M C) ≤ 2 * K * Real.log (M : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hlogV hK
    nlinarith
  have hlow : boundaryNorm q C / (4 * Real.pi) * Real.log (M : ℝ) ≤
      littlewoodNorm (blockInflation q M C) := by
    have hh := mul_le_mul_of_nonneg_left hlarge hsc
    have he : boundaryNorm q C / Real.pi * (16 * Real.pi + 2) =
        16 * boundaryNorm q C + 2 * (boundaryNorm q C / Real.pi) := by field_simp
    rw [he] at hh
    have hr : boundaryNorm q C / (4 * Real.pi) = (boundaryNorm q C / Real.pi) / 4 := by ring
    rw [hr]
    nlinarith
  have hc : boundaryNorm q C / (4 * Real.pi) ≤ 2 * K := by
    exact (mul_le_mul_iff_left₀ hlm).mp (hlow.trans hu)
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * Real.pi)).mp hc |>.trans_eq (by ring)

/-- The threshold is absolute and is stated directly in terms of the actual
inflated set cardinality. -/
theorem constant_boundary_budget {M : ℕ}
    {C : Finset (ZMod q × ℤ)} (hC : C.Nonempty) (hMC : C.card ≤ M)
    {K : ℝ} (hK : 0 ≤ K)
    (hlarge : Real.exp (32 * Real.pi + 4) ≤ ((blockInflation q M C).card : ℝ))
    (hnorm : littlewoodNorm (blockInflation q M C) ≤
      K * Real.log ((blockInflation q M C).card : ℝ)) :
      boundaryNorm q C ≤ 8 * Real.pi * K := by
  have hM : 0 < M := (C.card_pos.mpr hC).trans_le hMC
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hv : (0 : ℝ) < C.card := by exact_mod_cast C.card_pos.mpr hC
  rw [blockInflation_card q hM C, Nat.cast_mul] at hlarge hnorm
  apply constant_boundary_budget_of_log q hC hMC hK _ hnorm
  have hlog := Real.log_le_log (Real.exp_pos _) hlarge
  rw [Real.log_exp, Real.log_mul hm.ne' hv.ne'] at hlog
  have hvlog := Real.log_le_log hv (show (C.card : ℝ) ≤ M by exact_mod_cast hMC)
  linarith

end LittlewoodInverse
