import LittlewoodInverse.LandauCompletion
import LittlewoodInverse.IntervalAsymptotic

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LittlewoodInverse.Landau

theorem dirichlet_eq_fourierPolynomial (N : ℕ) :
    dirichlet N = fourierPolynomial (Finset.Ico (0 : ℤ) N) := by
  funext t
  simp only [dirichlet, intervalPolynomial_eq_geom_sum, fourier_nat_pow]

theorem completion_pairing_upper (N : ℕ) (hN : 0 < N) :
    (circlePairing (dirichlet N) (completion N)).re ≤
      littlewoodNorm (Finset.Ico (0 : ℤ) N) := by
  have hf := continuous_circle_integrable (dirichlet_continuous N)
  have hp := PhaseNormalization.phase_pair_integrable hf
    (twoSidedSum_continuous hN).aestronglyMeasurable
  calc
    _ = ∫ t, (dirichlet N t * conj (completion N t)).re ∂circleMeasure :=
      (integral_re hp).symm
    _ ≤ ∫ t, ‖dirichlet N t‖ ∂circleMeasure := by
      apply integral_mono hp.re hf.norm
      intro t
      calc
        _ ≤ ‖dirichlet N t * conj (completion N t)‖ := Complex.re_le_norm _
        _ ≤ _ := by
          rw [norm_mul, Complex.norm_conj]
          exact mul_le_of_le_one_right (norm_nonneg _) (completion_norm_le N t)
    _ = _ := by rw [dirichlet_eq_fourierPolynomial]; rfl

theorem completion_pairing_lower_norm (N : ℕ) (hN : 0 < N) :
    littlewoodNorm (Finset.Ico (0 : ℤ) N) - 192 ≤
      (circlePairing (dirichlet N) (completion N)).re := by
  simpa only [dirichlet_eq_fourierPolynomial, littlewoodNorm] using completion_pairing_lower hN

/-- Full bounded-error asymptotic for the explicit two-sided completion.
Both the Dirichlet norm asymptotic and the uniform comparison with that
norm are proved internally. -/
theorem completion_log_asymptotic : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 0 < N →
    |(circlePairing (dirichlet N) (completion N)).re -
      4 / Real.pi ^ 2 * Real.log N| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := LittlewoodInverse.dirichlet_l1_asymptotic
  refine ⟨C + 192, by linarith, fun N hN => ?_⟩
  have hl := completion_pairing_lower_norm N hN
  have hu := completion_pairing_upper N hN
  have hb := abs_le.mp (hbound N hN)
  exact abs_le.mpr ⟨by linarith [hb.1], by linarith [hb.2]⟩

end LittlewoodInverse.Landau
