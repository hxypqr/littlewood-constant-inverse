import LittlewoodInverse.LandauBoundary
import LittlewoodInverse.LandauSharpness
import LittlewoodInverse.LandauModel
import LittlewoodInverse.LandauAsymptotic

/-! # The actual two-sided completion for intervals -/

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LittlewoodInverse
namespace Landau

noncomputable def twoSidedSum (N : ℕ) (t : Circle) : ℂ :=
  extremizer N t + fourier ((N - 1 : ℕ) : ℤ) t * conj (extremizer N t)

noncomputable def completion (N : ℕ) (t : Circle) : ℂ :=
  PhaseNormalization.phase (twoSidedSum N t)

theorem completion_norm_le (N : ℕ) (t : Circle) : ‖completion N t‖ ≤ 1 :=
  PhaseNormalization.norm_phase_le_one _

theorem twoSidedSum_continuous {N : ℕ} (hN : 0 < N) : Continuous (twoSidedSum N) :=
  (extremizer_continuous hN).add ((fourier _).continuous.mul
    (Complex.continuous_conj.comp (extremizer_continuous hN)))

theorem dirichlet_continuous (N : ℕ) : Continuous (dirichlet N) := by
  unfold dirichlet
  fun_prop

theorem dirichlet_norm_le (N : ℕ) (t : Circle) : ‖dirichlet N t‖ ≤ N := by
  calc
    _ ≤ ∑ k ∈ Finset.range N, ‖fourier (k : ℤ) t‖ := norm_sum_le _ _
    _ = _ := by simp [fourier_apply]

noncomputable def completionError (N : ℕ) (t : Circle) : ℝ :=
  ‖dirichlet N t‖ * ‖PhaseNormalization.phase (dirichlet N t) - completion N t‖

theorem completionError_integrable {N : ℕ} (hN : 0 < N) :
    Integrable (completionError N) circleMeasure :=
  PhaseNormalization.weighted_phase_error_integrable
    (continuous_circle_integrable (dirichlet_continuous N))
    (twoSidedSum_continuous hN).aestronglyMeasurable

theorem completionError_small (N : ℕ) (t : Circle) : completionError N t ≤ 2 * N := by
  have hh := PhaseNormalization.phase_difference_le_two (dirichlet N t) (twoSidedSum N t)
  calc
    _ ≤ ‖dirichlet N t‖ * 2 := mul_le_mul_of_nonneg_left hh (norm_nonneg _)
    _ ≤ _ := by nlinarith [dirichlet_norm_le N t]

theorem twoSidedSum_model_error {N : ℕ} (hN : 0 < N) (t : Circle)
    (ht : fourier 1 t ≠ 1) :
    ‖twoSidedSum N t - (‖1 - fourier 1 t‖ : ℂ) * dirichlet N t‖ ≤
      16 * b N / Real.sqrt ‖1 - fourier 1 t‖ := by
  have hz : ‖fourier 1 t‖ = 1 := by simp [fourier_apply]
  have hmodel := model_identity hN hz ht
  have he : (∑ k ∈ Finset.range N, fourier 1 t ^ k) = dirichlet N t := by
    simp only [dirichlet, fourier_nat_pow]
  rw [he, ← fourier_nat_pow] at hmodel
  have hu := quotient_phase_error N hz ht
  change ‖extremizer N t - model (fourier 1 t)‖ ≤ _ at hu
  rw [← hmodel]
  have hdiff : twoSidedSum N t -
      (model (fourier 1 t) + fourier ((N - 1 : ℕ) : ℤ) t * conj (model (fourier 1 t))) =
      (extremizer N t - model (fourier 1 t)) + fourier ((N - 1 : ℕ) : ℤ) t *
        conj (extremizer N t - model (fourier 1 t)) := by
    unfold twoSidedSum
    rw [map_sub]
    ring
  rw [hdiff]
  calc
    _ ≤ ‖extremizer N t - model (fourier 1 t)‖ +
        ‖fourier ((N - 1 : ℕ) : ℤ) t * conj (extremizer N t - model (fourier 1 t))‖ := norm_add_le _ _
    _ = 2 * ‖extremizer N t - model (fourier 1 t)‖ := by
      simp only [norm_mul, Complex.norm_conj, fourier_apply, Circle.norm_coe, one_mul]
      ring
    _ ≤ _ := by
      calc
        _ ≤ 2 * (8 * b N / Real.sqrt ‖1 - fourier 1 t‖) := by linarith
        _ = _ := by ring

theorem completionError_large {N : ℕ} (hN : 0 < N) (t : Circle)
    (ht : fourier 1 t ≠ 1) :
    completionError N t ≤ 32 * b N /
      (‖1 - fourier 1 t‖ * Real.sqrt ‖1 - fourier 1 t‖) := by
  have hd : 0 < ‖1 - fourier 1 t‖ := norm_pos_iff.mpr (sub_ne_zero.mpr ht.symm)
  have hh := PhaseNormalization.phase_perturbation_weighted (twoSidedSum N t)
    ((‖1 - fourier 1 t‖ : ℂ) * dirichlet N t)
  rw [PhaseNormalization.phase_positive_mul _ hd] at hh
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), norm_sub_rev] at hh
  have hmodel := twoSidedSum_model_error hN t ht
  apply (le_div_iff₀ (mul_pos hd (Real.sqrt_pos.mpr hd))).mpr
  change (‖dirichlet N t‖ * ‖PhaseNormalization.phase (dirichlet N t) -
    PhaseNormalization.phase (twoSidedSum N t)‖) *
      (‖1 - fourier 1 t‖ * Real.sqrt ‖1 - fourier 1 t‖) ≤ _
  have hbound : ‖1 - fourier 1 t‖ *
      (‖dirichlet N t‖ * ‖PhaseNormalization.phase (dirichlet N t) -
        PhaseNormalization.phase (twoSidedSum N t)‖) ≤
      32 * b N / Real.sqrt ‖1 - fourier 1 t‖ := by
    calc
      _ ≤ 2 * ‖twoSidedSum N t - (‖1 - fourier 1 t‖ : ℂ) * dirichlet N t‖ := by
        simpa only [mul_assoc] using hh
      _ ≤ 2 * (16 * b N / Real.sqrt ‖1 - fourier 1 t‖) := by linarith
      _ = _ := by ring
  have hmul := (le_div_iff₀ (Real.sqrt_pos.mpr hd)).mp hbound
  calc
    _ = ‖1 - fourier 1 t‖ *
      (‖dirichlet N t‖ * ‖PhaseNormalization.phase (dirichlet N t) -
        PhaseNormalization.phase (twoSidedSum N t)‖) * Real.sqrt ‖1 - fourier 1 t‖ := by ring
    _ ≤ _ := hmul

theorem completionError_real_bound {N : ℕ} (hN : 0 < N) {x : ℝ}
    (hx : 0 < |x|) (hxhalf : |x| ≤ 1 / 2) :
    completionError N (x : Circle) ≤
      32 * (N : ℝ) ^ (-(1 / 2 : ℝ)) * |x| ^ (-(3 / 2 : ℝ)) := by
  have hdist := fourier_distance_lower x hxhalf
  have hxd : |x| ≤ ‖1 - fourier 1 (x : Circle)‖ := by linarith
  have hd : 0 < ‖1 - fourier 1 (x : Circle)‖ := hx.trans_le hxd
  have ht : fourier 1 (x : Circle) ≠ 1 := by
    intro hh
    simp only [hh, sub_self, norm_zero] at hd
    exact hd.false
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    _ ≤ 32 * b N / (‖1 - fourier 1 (x : Circle)‖ *
        Real.sqrt ‖1 - fourier 1 (x : Circle)‖) := completionError_large hN _ ht
    _ ≤ 32 * (1 / Real.sqrt (N : ℝ)) / (|x| * Real.sqrt |x|) := by
      gcongr
      exact b_le_inv_sqrt N hN
    _ = _ := by
      rw [Real.rpow_neg hNr.le, Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow,
        show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx,
        Real.rpow_one, ← Real.sqrt_eq_rpow]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem fourier_neg_argument (n : ℤ) (t : Circle) :
    fourier n (-t) = conj (fourier n t) := by
  rw [← fourier_neg]
  simp [fourier_apply, smul_neg, neg_smul]

theorem dirichlet_neg_argument (N : ℕ) (t : Circle) :
    dirichlet N (-t) = conj (dirichlet N t) := by
  simp only [dirichlet, fourier_neg_argument, map_sum]

theorem polynomial_neg_argument (N : ℕ) (t : Circle) :
    evalCircle (polynomial N) (-t) = conj (evalCircle (polynomial N) t) := by
  simp only [evalCircle, ← partialSum_eq_eval, partialSum, map_sum, map_mul,
    map_pow, Complex.conj_ofReal, fourier_neg_argument]

theorem extremizer_neg_argument (N : ℕ) (t : Circle) :
    extremizer N (-t) = conj (extremizer N t) := by
  simp only [extremizer, polynomial_neg_argument, map_div₀]

theorem twoSidedSum_neg_argument (N : ℕ) (t : Circle) :
    twoSidedSum N (-t) = conj (twoSidedSum N t) := by
  simp only [twoSidedSum, extremizer_neg_argument, fourier_neg_argument, map_add, map_mul]

theorem phase_conj (z : ℂ) : PhaseNormalization.phase (conj z) =
    conj (PhaseNormalization.phase z) := by
  simp only [PhaseNormalization.phase, map_div₀, Complex.conj_ofReal, Complex.norm_conj]

theorem completionError_even (N : ℕ) (t : Circle) :
    completionError N (-t) = completionError N t := by
  simp only [completionError, completion, dirichlet_neg_argument,
    twoSidedSum_neg_argument, phase_conj, ← map_sub, Complex.norm_conj]

theorem completionError_half_integrable {N : ℕ} (hN : 0 < N) :
    IntegrableOn (fun x : ℝ => completionError N (x : Circle)) (Set.Ioc 0 (1/2)) := by
  have hm : (volume : Measure Circle) = circleMeasure := by
    simpa [circleMeasure] using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
  have hv : Integrable (completionError N) volume := by
    rw [hm]
    exact completionError_integrable hN
  have hp := (AddCircle.measurePreserving_mk (1 : ℝ) 0).integrable_comp_of_integrable hv
  have hi : IntegrableOn (fun x : ℝ => completionError N (x : Circle)) (Set.Ioc 0 1) := by
    simpa only [IntegrableOn, Function.comp_def, zero_add] using hp
  exact hi.mono_set (by intro x hx; exact ⟨hx.1, by linarith [hx.2]⟩)

/-- The two-sided completion has a uniform integrable phase error. -/
theorem completionError_integral_le {N : ℕ} (hN : 0 < N) :
    (∫ t, completionError N t ∂circleMeasure) ≤ 192 := by
  have hh := PhaseNormalization.finite_two_arc_error_bound 32 (N : ℝ) (1/2)
    (by norm_num) (by exact_mod_cast hN) (completionError_half_integrable hN)
    (fun s _ _ => (completionError_small N (s : Circle)).trans (by linarith [Nat.cast_nonneg (α := ℝ) N]))
    (fun s hs _ => by
      simpa only [abs_of_pos hs.1] using
        completionError_real_bound hN (x := s) (by simpa only [abs_of_pos hs.1] using hs.1)
          (by simpa only [abs_of_pos hs.1] using hs.2))
  rw [circle_even_integral _ (completionError_integrable hN) (completionError_even N)]
  linarith

/-- Appendix B's actual explicit two-sided test loses at most an absolute
constant from the full Dirichlet-kernel norm. -/
theorem completion_pairing_lower {N : ℕ} (hN : 0 < N) :
    (∫ t, ‖dirichlet N t‖ ∂circleMeasure) - 192 ≤
      (circlePairing (dirichlet N) (completion N)).re := by
  have hh := PhaseNormalization.integral_pairing_loss_le
    (continuous_circle_integrable (dirichlet_continuous N))
    (twoSidedSum_continuous hN).aestronglyMeasurable
  change (∫ t, ‖dirichlet N t‖ ∂circleMeasure) -
    (circlePairing (dirichlet N) (completion N)).re ≤
      ∫ t, completionError N t ∂circleMeasure at hh
  linarith [completionError_integral_le hN]

end Landau
end LittlewoodInverse

