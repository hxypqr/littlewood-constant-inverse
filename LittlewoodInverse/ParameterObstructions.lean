import LittlewoodInverse.SidonFibreExamples
import LittlewoodInverse.IntervalNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter
open scoped Topology

namespace LittlewoodInverse

/-- The normalized additive energy, with value zero for the empty set. -/
noncomputable def energyRatio (Y : Finset ℤ) : ℝ :=
  (additiveEnergy Y : ℝ) / (Y.card : ℝ) ^ 3

theorem interlacedSet_energy_size_cost {R M : ℕ} (hR : 0 < R) {Y : Finset ℤ}
    (hY : Y ⊆ interlacedSet R M) :
    (Y.card : ℝ) * energyRatio Y ≤ 2 * (interlacedSet R M).card / R := by
  rw [interlacedSet_card]
  push_cast
  have hR0 : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
  have he : (additiveEnergy Y : ℝ) ≤ 2 * (M : ℝ) * (Y.card : ℝ) ^ 2 := by
    exact_mod_cast interlacedSet_energy R M hY
  by_cases hy : Y.card = 0
  · simp only [hy, Nat.cast_zero, zero_mul]
    positivity
  · have hy0 : (0 : ℝ) < Y.card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hy)
    have hnorm : (Y.card : ℝ) * energyRatio Y ≤ 2 * M := by
      unfold energyRatio
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (pow_pos hy0 3)).mpr
      have hh := mul_le_mul_of_nonneg_left he hy0.le
      nlinarith
    convert hnorm using 1; field_simp

/-- Membership in the assembly class alone cannot give uniformly bounded
doubling for positive-density pieces as the number of fibres grows. -/
theorem interlacedSet_doubling_cost {R M : ℕ} (hR : 0 < R) (hM : 0 < M)
    {Y : Finset ℤ} (hY : Y ⊆ interlacedSet R M) {c Q : ℝ}
    (hc : 0 < c) (hQ : 0 ≤ Q)
    (hdensity : c * (interlacedSet R M).card ≤ Y.card)
    (hdouble : ((sumset Y).card : ℝ) ≤ Q * Y.card) : c * R / 2 ≤ Q := by
  rw [interlacedSet_card, Nat.cast_mul] at hdensity
  have hRr : (0 : ℝ) < R := Nat.cast_pos.mpr hR
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hy : (0 : ℝ) < Y.card :=
    (mul_pos hc (mul_pos hRr hMr)).trans_le hdensity
  have hlower : (Y.card : ℝ) ^ 4 ≤ (sumset Y).card * (additiveEnergy Y : ℝ) := by
    exact_mod_cast card_pow_four_le_sumset_mul_energy Y
  have hupper : (additiveEnergy Y : ℝ) ≤ 2 * (M : ℝ) * (Y.card : ℝ) ^ 2 := by
    exact_mod_cast interlacedSet_energy R M hY
  have hprod := mul_le_mul hdouble hupper (Nat.cast_nonneg (additiveEnergy Y))
    (mul_nonneg hQ hy.le)
  have hcard : (Y.card : ℝ) ≤ 2 * M * Q := by
    by_contra h
    have hp := mul_pos (pow_pos hy 3) (sub_pos.mpr (lt_of_not_ge h))
    nlinarith
  have hcancel : c * R ≤ 2 * Q := by
    by_contra h
    have hp := mul_pos hMr (sub_pos.mpr (lt_of_not_ge h))
    nlinarith
  linarith

theorem interlacedSet_low_norm {R M : ℕ} (hR : 0 < R) (hM : 0 < M)
    (hlogM : 1 ≤ Real.log (M : ℝ)) :
    littlewoodNorm (interlacedSet R M) ≤
      (2 * Real.sqrt (R : ℝ)) * Real.log ((interlacedSet R M).card : ℝ) := by
  have hRr : (0 : ℝ) < R := Nat.cast_pos.mpr hR
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hlogR : 0 ≤ Real.log (R : ℝ) := Real.log_nonneg (by exact_mod_cast hR)
  have hb := interval_littlewoodNorm_le_log M hM
  have hh := (interlacedSet_norm R M).trans
    (mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _))
  rw [interlacedSet_card, Nat.cast_mul, Real.log_mul hRr.ne' hMr.ne']
  have hs := Real.sqrt_nonneg (R : ℝ)
  nlinarith

theorem prefix_coefficient_obstruction {p c : ℝ} (hp : p < 2) (hc : 0 < c) :
    ∀ᶠ R : ℕ in atTop, 0 < R ∧
      16 / (R : ℝ) < c / (2 * Real.sqrt (R : ℝ)) ^ p := by
  have hlim : Tendsto (fun R : ℕ => (16 * (2 : ℝ) ^ p) * (R : ℝ) ^ (p / 2 - 1))
      atTop (𝓝 0) := by
    have ht := (tendsto_rpow_neg_atTop (show 0 < 1 - p / 2 by linarith)).comp
      tendsto_natCast_atTop_atTop
    have he : -(1 - p / 2) = p / 2 - 1 := by ring
    simpa only [he, mul_zero, Function.comp_def] using ht.const_mul (16 * (2 : ℝ) ^ p)
  have hsmall := hlim.eventually (gt_mem_nhds hc)
  filter_upwards [hsmall, eventually_gt_atTop 0] with R hsmall hR
  refine ⟨hR, ?_⟩
  have hRr : (0 : ℝ) < R := Nat.cast_pos.mpr hR
  have he : (16 * (2 : ℝ) ^ p) * (R : ℝ) ^ (p / 2 - 1) =
      16 / (R : ℝ) * (2 * Real.sqrt (R : ℝ)) ^ p := by
    rw [Real.mul_rpow (by norm_num) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
      ← Real.rpow_mul hRr.le, Real.rpow_sub_one hRr.ne']
    rw [show (1 / 2 : ℝ) * p = p / 2 by ring]
    ring
  rw [he] at hsmall
  exact (lt_div_iff₀ (Real.rpow_pos_of_pos (by positivity) _)).mpr hsmall

/-- For every exponent below two and every positive coefficient, all
sufficiently many-fibre examples defeat that stronger prefix estimate. -/
theorem initial_segment_parameter_obstruction {p c : ℝ} (hp : p < 2) (hc : 0 < c) :
    ∀ᶠ R : ℕ in atTop, 0 < R ∧ ∀ M : ℕ, 0 < M → 1 ≤ Real.log (M : ℝ) →
      littlewoodNorm (interlacedSet R M) ≤
        (2 * Real.sqrt (R : ℝ)) * Real.log ((interlacedSet R M).card : ℝ) ∧
      ∀ P : Finset ℤ, IsInitialSegment P (interlacedSet R M) → R ≤ P.card →
        (additiveEnergy P : ℝ) <
          c / (2 * Real.sqrt (R : ℝ)) ^ p * (P.card : ℝ) ^ 3 := by
  filter_upwards [prefix_coefficient_obstruction hp hc] with R hR
  refine ⟨hR.1, fun M hM hlogM => ⟨interlacedSet_low_norm hR.1 hM hlogM, ?_⟩⟩
  intro P hP hsize
  have hPpos : (0 : ℝ) < P.card := by exact_mod_cast hR.1.trans_le hsize
  have h := mul_lt_mul_of_pos_right hR.2 (pow_pos hPpos 3)
  exact (interlacedSet_prefix_energy hR.1 hP hsize).trans_lt (by
    simpa only [div_mul_eq_mul_div] using h)

/-- The size qualification in the prose obstruction requires exponent
`1-δ` to be positive. In particular it applies to the intended `0<δ<1`. -/
theorem prefix_threshold_eventually_ge_fibres {R : ℕ} (hR : 0 < R)
    {γ δ : ℝ} (hγ : 0 < γ) (hδ : δ < 1) :
    ∀ᶠ M : ℕ in atTop, ∀ P : Finset ℤ,
      γ * ((interlacedSet R M).card : ℝ) ^ (1 - δ) ≤ P.card → R ≤ P.card := by
  have hRr : (0 : ℝ) < R := Nat.cast_pos.mpr hR
  have hprod : Tendsto (fun M : ℕ => (R : ℝ) * M) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hRr
  have hp := (tendsto_rpow_atTop (show 0 < 1 - δ by linarith)).comp hprod
  have ht := hp.const_mul_atTop hγ
  filter_upwards [ht.eventually (eventually_ge_atTop (R : ℝ))] with M hM
  intro P hP
  rw [interlacedSet_card, Nat.cast_mul] at hP
  exact_mod_cast hM.trans hP

end LittlewoodInverse
