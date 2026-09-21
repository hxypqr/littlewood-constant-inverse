import LittlewoodInverse.Basic
import Mathlib

open scoped ComplexConjugate
open MeasureTheory

namespace LittlewoodInverse
namespace PhaseNormalization

/-- Complex phase with the value zero at zero. -/
noncomputable def phase (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

@[simp] theorem phase_zero : phase 0 = 0 := by simp [phase]

theorem norm_phase_le_one (z : ℂ) : ‖phase z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [hz]
  · simp [phase, norm_ne_zero_iff.mpr hz]

theorem norm_phase_eq_one {z : ℂ} (hz : z ≠ 0) : ‖phase z‖ = 1 := by
  simp [phase, norm_ne_zero_iff.mpr hz]

theorem norm_mul_phase (z : ℂ) : (‖z‖ : ℂ) * phase z = z := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [phase, mul_div_cancel₀ _ (by exact_mod_cast norm_ne_zero_iff.mpr hz)]

theorem phase_perturbation_weighted (x y : ℂ) :
    ‖y‖ * ‖phase x - phase y‖ ≤ 2 * ‖x - y‖ := by
  have he : (‖y‖ : ℂ) * (phase x - phase y) =
      ((‖y‖ - ‖x‖ : ℝ) : ℂ) * phase x + (x - y) := by
    push_cast
    rw [sub_mul, mul_sub, norm_mul_phase, norm_mul_phase]
    ring
  have hn := norm_add_le (((‖y‖ - ‖x‖ : ℝ) : ℂ) * phase x) (x - y)
  rw [← he] at hn
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm] at hn
  have hb := mul_le_mul_of_nonneg_left (norm_phase_le_one x) (abs_nonneg (‖y‖ - ‖x‖))
  have hr := abs_norm_sub_norm_le y x
  rw [norm_sub_rev] at hr
  nlinarith

/-- The normalization estimate remains valid when the first input is zero. -/
theorem phase_perturbation (x : ℂ) {y : ℂ} (hy : y ≠ 0) :
    ‖phase x - phase y‖ ≤ 2 * ‖x - y‖ / ‖y‖ := by
  apply (le_div_iff₀ (norm_pos_iff.mpr hy)).mpr
  simpa only [mul_comm] using phase_perturbation_weighted x y

theorem phase_difference_le_two (x y : ℂ) : ‖phase x - phase y‖ ≤ 2 := by
  have := norm_sub_le (phase x) (phase y)
  linarith [norm_phase_le_one x, norm_phase_le_one y]

theorem self_pair (z : ℂ) : z * conj (phase z) = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [hz]
  · simp only [phase, map_div₀, Complex.conj_ofReal]
    rw [← mul_div_assoc, Complex.mul_conj']
    have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
    field_simp

theorem pairing_loss_le (z w : ℂ) :
    ‖z‖ - (z * conj (phase w)).re ≤ ‖z‖ * ‖phase z - phase w‖ := by
  have he : ‖z‖ - (z * conj (phase w)).re =
      (z * conj (phase z - phase w)).re := by
    rw [map_sub, mul_sub, Complex.sub_re, self_pair, Complex.ofReal_re]
  rw [he]
  exact (Complex.re_le_norm _).trans_eq (by rw [norm_mul, RCLike.norm_conj])

theorem phase_aestronglyMeasurable {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℂ} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => phase (f x)) μ := by
  exact hf.div₀ (Complex.continuous_ofReal.comp_aestronglyMeasurable hf.norm)

theorem phase_pair_integrable {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℂ} (hf : Integrable f μ)
    (hg : AEStronglyMeasurable g μ) :
    Integrable (fun x => f x * conj (phase (g x))) μ := by
  apply hf.mul_bdd (Complex.continuous_conj.comp_aestronglyMeasurable
    (phase_aestronglyMeasurable hg))
  filter_upwards [] with x
  simpa only [RCLike.norm_conj] using norm_phase_le_one (g x)

theorem weighted_phase_error_integrable {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℂ} (hf : Integrable f μ)
    (hg : AEStronglyMeasurable g μ) :
    Integrable (fun x => ‖f x‖ * ‖phase (f x) - phase (g x)‖) μ := by
  apply hf.norm.mul_bdd ((phase_aestronglyMeasurable hf.aestronglyMeasurable).sub
    (phase_aestronglyMeasurable hg)).norm
  filter_upwards [] with x
  simpa only [norm_norm, Pi.sub_apply] using phase_difference_le_two (f x) (g x)

/-- Exact weighted correlation-loss inequality, with all integrability
conditions discharged by the unit bound on normalized phases. -/
theorem integral_pairing_loss_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℂ} (hf : Integrable f μ)
    (hg : AEStronglyMeasurable g μ) :
    (∫ x, ‖f x‖ ∂μ) - (∫ x, f x * conj (phase (g x)) ∂μ).re ≤
      ∫ x, ‖f x‖ * ‖phase (f x) - phase (g x)‖ ∂μ := by
  have hp := phase_pair_integrable hf hg
  calc
    _ = ∫ x, (‖f x‖ - (f x * conj (phase (g x))).re) ∂μ := by
      have hre : (∫ x, (f x * conj (phase (g x))).re ∂μ) =
          (∫ x, f x * conj (phase (g x)) ∂μ).re := integral_re hp
      rw [← hre]
      exact (integral_sub hf.norm hp.re).symm
    _ ≤ _ := integral_mono (hf.norm.sub hp.re) (weighted_phase_error_integrable hf hg)
      (fun x => pairing_loss_le (f x) (g x))

theorem phase_positive_mul (r : ℝ) (hr : 0 < r) (z : ℂ) :
    phase ((r : ℂ) * z) = phase z := by
  by_cases hz : z = 0
  · simp [hz]
  · have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    simp only [phase, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      Complex.ofReal_mul]
    field_simp

/-- Pointwise model-phase control used outside the short exceptional arcs. -/
theorem pairing_loss_le_model (z x y : ℂ) (hy : y ≠ 0) (hphase : phase y = phase z) :
    ‖z‖ - (z * conj (phase x)).re ≤ 2 * ‖z‖ * ‖x - y‖ / ‖y‖ := by
  have hp := phase_perturbation x hy
  rw [hphase, norm_sub_rev] at hp
  calc
    _ ≤ ‖z‖ * ‖phase z - phase x‖ := pairing_loss_le z x
    _ ≤ ‖z‖ * (2 * ‖x - y‖ / ‖y‖) := mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ = _ := by ring

theorem quotient_conj_eq_phase_sq (z : ℂ) : z / conj z = phase z ^ 2 := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [phase, div_pow, show (‖z‖ : ℂ) ^ 2 = z * conj z from (Complex.mul_conj' z).symm]
    have hz' : conj z ≠ 0 := by simpa using hz
    field_simp

theorem quotient_conj_norm_le (z : ℂ) : ‖z / conj z‖ ≤ 1 := by
  rw [quotient_conj_eq_phase_sq, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (norm_phase_le_one _)

theorem quotient_conj_perturbation (x : ℂ) {y : ℂ} (hy : y ≠ 0) :
    ‖x / conj x - y / conj y‖ ≤ 4 * ‖x - y‖ / ‖y‖ := by
  rw [quotient_conj_eq_phase_sq, quotient_conj_eq_phase_sq]
  have hs : ‖phase x + phase y‖ ≤ 2 :=
    (norm_add_le _ _).trans (by linarith [norm_phase_le_one x, norm_phase_le_one y])
  calc
    _ = ‖(phase x - phase y) * (phase x + phase y)‖ := congrArg norm (by ring)
    _ ≤ ‖phase x - phase y‖ * 2 := by rw [norm_mul]; exact mul_le_mul_of_nonneg_left hs (norm_nonneg _)
    _ ≤ (2 * ‖x - y‖ / ‖y‖) * 2 :=
      mul_le_mul_of_nonneg_right (phase_perturbation x hy) (by norm_num)
    _ = _ := by ring

theorem small_arc_integral (C N : ℝ) (hN : 0 < N) :
    (∫ _s in Set.Ioc (0 : ℝ) N⁻¹, C * N) = C := by
  rw [setIntegral_const, Measure.real, Real.volume_Ioc,
    ENNReal.toReal_ofReal (show 0 ≤ N⁻¹ - 0 by simpa using (inv_pos.mpr hN).le)]
  simp only [sub_zero, smul_eq_mul]
  field_simp

theorem large_arc_integrable (C N : ℝ) (hN : 0 < N) :
    IntegrableOn (fun s : ℝ => C * N ^ (- (1 / 2 : ℝ)) * s ^ (- (3 / 2 : ℝ)))
      (Set.Ioi N⁻¹) :=
  (integrableOn_Ioi_rpow_of_lt (by norm_num) (inv_pos.mpr hN)).const_mul _

theorem large_arc_integral (C N : ℝ) (hN : 0 < N) :
    (∫ s in Set.Ioi N⁻¹, C * N ^ (- (1 / 2 : ℝ)) * s ^ (- (3 / 2 : ℝ))) = 2 * C := by
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) (inv_pos.mpr hN)]
  norm_num only [show -(3 / 2 : ℝ) + 1 = -(1 / 2 : ℝ) by norm_num]
  rw [Real.inv_rpow hN.le, Real.rpow_neg hN.le]
  have hn : N ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hN _).ne'
  field_simp

/-- The `1/N` cut-off gives a uniform constant, with the tail integrated all
the way to infinity. This also bounds every finite terminal arc. -/
theorem two_arc_error_bound (C N : ℝ) (hN : 0 < N) {f : ℝ → ℝ}
    (hf : IntegrableOn f (Set.Ioi 0))
    (hsmall : ∀ s ∈ Set.Ioc (0 : ℝ) N⁻¹, f s ≤ C * N)
    (hlarge : ∀ s ∈ Set.Ioi N⁻¹,
      f s ≤ C * N ^ (- (1 / 2 : ℝ)) * s ^ (- (3 / 2 : ℝ))) :
    (∫ s in Set.Ioi (0 : ℝ), f s) ≤ 3 * C := by
  have ha : 0 < N⁻¹ := inv_pos.mpr hN
  have hs : Set.Ioc (0 : ℝ) N⁻¹ ⊆ Set.Ioi 0 := fun _ h => h.1
  have hl : Set.Ioi N⁻¹ ⊆ Set.Ioi 0 := fun _ h => ha.trans h
  have hd : Disjoint (Set.Ioc (0 : ℝ) N⁻¹) (Set.Ioi N⁻¹) :=
    Set.disjoint_left.mpr (fun _ h h' => (not_lt_of_ge h.2) h')
  have hu : Set.Ioc (0 : ℝ) N⁻¹ ∪ Set.Ioi N⁻¹ = Set.Ioi 0 := by
    ext s
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact ha.trans h
    · intro h
      rcases le_or_gt s N⁻¹ with hle | hlt
      · exact Or.inl ⟨h, hle⟩
      · exact Or.inr hlt
  have hsi : IntegrableOn (fun _ : ℝ => C * N) (Set.Ioc (0 : ℝ) N⁻¹) :=
    integrableOn_const (by simp)
  calc
    _ = (∫ s in Set.Ioc (0 : ℝ) N⁻¹, f s) + (∫ s in Set.Ioi N⁻¹, f s) := by
      rw [← hu, setIntegral_union hd measurableSet_Ioi (hf.mono_set hs) (hf.mono_set hl)]
    _ ≤ (∫ s in Set.Ioc (0 : ℝ) N⁻¹, C * N) +
        (∫ s in Set.Ioi N⁻¹, C * N ^ (- (1 / 2 : ℝ)) * s ^ (- (3 / 2 : ℝ))) :=
      add_le_add (setIntegral_mono_on (hf.mono_set hs) hsi measurableSet_Ioc hsmall)
        (setIntegral_mono_on (hf.mono_set hl) (large_arc_integrable C N hN)
          measurableSet_Ioi hlarge)
    _ = _ := by rw [small_arc_integral C N hN, large_arc_integral C N hN]; ring

theorem finite_two_arc_error_bound (C N B : ℝ) (hC : 0 ≤ C) (hN : 0 < N)
    {f : ℝ → ℝ} (hf : IntegrableOn f (Set.Ioc 0 B))
    (hsmall : ∀ s ∈ Set.Ioc (0 : ℝ) B, s ≤ N⁻¹ → f s ≤ C * N)
    (hlarge : ∀ s ∈ Set.Ioc (0 : ℝ) B, N⁻¹ < s →
      f s ≤ C * N ^ (- (1 / 2 : ℝ)) * s ^ (- (3 / 2 : ℝ))) :
    (∫ s in Set.Ioc (0 : ℝ) B, f s) ≤ 3 * C := by
  let g := (Set.Ioc (0 : ℝ) B).indicator f
  have hg : IntegrableOn g (Set.Ioi 0) :=
    (hf.integrable_indicator measurableSet_Ioc).integrableOn
  have hs (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) N⁻¹) : g s ≤ C * N := by
    by_cases h : s ∈ Set.Ioc (0 : ℝ) B
    · simpa only [g, Set.indicator_of_mem h] using hsmall s h hs.2
    · simp only [g, Set.indicator_of_notMem h]
      exact mul_nonneg hC hN.le
  have hl (s : ℝ) (hs : s ∈ Set.Ioi N⁻¹) :
      g s ≤ C * N ^ (- (1 / 2 : ℝ)) * s ^ (- (3 / 2 : ℝ)) := by
    by_cases h : s ∈ Set.Ioc (0 : ℝ) B
    · simpa only [g, Set.indicator_of_mem h] using hlarge s h hs
    · simp only [g, Set.indicator_of_notMem h]
      exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hN.le _))
        (Real.rpow_nonneg (le_of_lt ((inv_pos.mpr hN).trans hs)) _)
  have h := two_arc_error_bound C N hN hg hs hl
  have he : Set.Ioi (0 : ℝ) ∩ Set.Ioc 0 B = Set.Ioc 0 B :=
    Set.inter_eq_right.mpr (fun _ h => h.1)
  simpa only [g, setIntegral_indicator measurableSet_Ioc, he] using h

end PhaseNormalization
end LittlewoodInverse
