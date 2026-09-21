import LittlewoodInverse.BoundaryExtraction

namespace LittlewoodInverse

theorem aspect_log_gain {m v σ : ℝ} (hm : 0 < m) (hv : 1 ≤ v)
    (hσ : 0 < σ) (hσ' : σ ≤ 1 / 2) (haspect : v ^ (1 / 2 + σ) ≤ m) :
    σ / 2 * Real.log (m * v) ≤ Real.log m - Real.log v / 2 := by
  have hv0 : 0 < v := lt_of_lt_of_le zero_lt_one hv
  have hl := Real.log_le_log (Real.rpow_pos_of_pos hv0 _) haspect
  rw [Real.log_rpow hv0] at hl
  rw [Real.log_mul hm.ne' hv0.ne']
  have hvlog := Real.log_nonneg hv
  have hh := mul_le_mul_of_nonneg_left hl (show 0 ≤ 1 - σ / 2 by linarith)
  have hs : 0 ≤ σ * (1 / 2 - σ) := mul_nonneg hσ.le (by linarith)
  nlinarith [mul_nonneg hs hvlog]

variable (q : ℕ) [NeZero q]

theorem boundary_log_ratio_aspect {M : ℕ} {C : Finset (ZMod q × ℤ)}
    (hC : C.Nonempty) {σ : ℝ} (hσ : 0 < σ) (hσ' : σ ≤ 1 / 2)
    (haspect : (C.card : ℝ) ^ (1 / 2 + σ) ≤ M) :
    σ / 2 * Real.log ((M : ℝ) * C.card) - 1 / 2 ≤
      Real.log ((M : ℝ) * boundaryNorm q C / Real.sqrt (boundaryMass C : ℝ)) := by
  have hv : (1 : ℝ) ≤ C.card := by exact_mod_cast C.card_pos.mpr hC
  have hv0 : (0 : ℝ) < C.card := lt_of_lt_of_le zero_lt_one hv
  have hm : (0 : ℝ) < M := (Real.rpow_pos_of_pos hv0 _).trans_le haspect
  have hs1 := one_le_boundaryNorm q hC
  have hs : 0 < boundaryNorm q C := lt_of_lt_of_le zero_lt_one hs1
  have hmass : (0 : ℝ) < boundaryMass C := by exact_mod_cast boundaryMass_pos hC
  have hH : 0 < Real.sqrt (boundaryMass C : ℝ) := Real.sqrt_pos.mpr hmass
  have hmassle : (boundaryMass C : ℝ) ≤ 2 * C.card := by exact_mod_cast boundaryMass_le C
  have hlmass := Real.log_le_log hmass hmassle
  rw [Real.log_mul (by norm_num) hv0.ne'] at hlmass
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hgain := aspect_log_gain hm hv hσ hσ' haspect
  rw [Real.log_div (mul_pos hm hs).ne' hH.ne', Real.log_mul hm.ne' hs.ne',
    Real.log_sqrt hmass.le]
  have hlogs := Real.log_nonneg hs1
  linarith

/-- Corollary 7.2 for every positive aspect exponent up to one half.
The threshold depends only on that exponent. -/
theorem aspect_boundary_budget {M : ℕ} {C : Finset (ZMod q × ℤ)}
    (hC : C.Nonempty) {σ : ℝ} (hσ : 0 < σ) (hσ' : σ ≤ 1 / 2)
    (haspect : (C.card : ℝ) ^ (1 / 2 + σ) ≤ M) {K : ℝ}
    (hlarge : Real.exp ((16 * Real.pi + 2) / σ) ≤ ((blockInflation q M C).card : ℝ))
    (hnorm : littlewoodNorm (blockInflation q M C) ≤
      K * Real.log ((blockInflation q M C).card : ℝ)) :
    boundaryNorm q C ≤ 4 * Real.pi * K / σ := by
  have hv : (0 : ℝ) < C.card := by exact_mod_cast C.card_pos.mpr hC
  have hm : (0 : ℝ) < M := (Real.rpow_pos_of_pos hv _).trans_le haspect
  have hM : 0 < M := by exact_mod_cast hm
  rw [blockInflation_card q hM C, Nat.cast_mul] at hlarge hnorm
  let L := Real.log ((M : ℝ) * C.card)
  let S := boundaryNorm q C
  have hlog := Real.log_le_log (Real.exp_pos _) hlarge
  rw [Real.log_exp] at hlog
  have hlower : 16 * Real.pi + 2 ≤ σ * L := by
    have h := (div_le_iff₀ hσ).mp hlog
    simpa only [mul_comm] using h
  have hL : 0 < L := by nlinarith [Real.pi_pos]
  have hs0 : 0 ≤ S := boundaryNorm_nonneg q C
  have hc : 0 ≤ S / Real.pi := div_nonneg hs0 Real.pi_pos.le
  have hex := uniform_boundary_extraction q hM hC
  have hratio := boundary_log_ratio_aspect q hC hσ hσ' haspect
  have hscaled := mul_le_mul_of_nonneg_left hratio hc
  have hsize := mul_le_mul_of_nonneg_left hlower hc
  have hSpi : S / Real.pi * Real.pi = S := by field_simp
  have hlow : S / Real.pi * σ / 4 * L ≤ littlewoodNorm (blockInflation q M C) := by
    change S / Real.pi * Real.log ((M : ℝ) * S / Real.sqrt (boundaryMass C : ℝ)) -
      4 * S ≤ _ at hex
    change S / Real.pi * (σ / 2 * L - 1 / 2) ≤ _ at hscaled
    nlinarith
  have hcoef : S / Real.pi * σ / 4 ≤ K :=
    (mul_le_mul_iff_left₀ hL).mp (hlow.trans hnorm)
  apply (le_div_iff₀ hσ).mpr
  have h := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ 4 * Real.pi by positivity)
  change S * σ ≤ 4 * Real.pi * K
  calc
    _ = (S / Real.pi * σ / 4) * (4 * Real.pi) := by field_simp
    _ ≤ K * (4 * Real.pi) := h
    _ = _ := by ring

end LittlewoodInverse
