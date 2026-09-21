import LittlewoodInverse.PrefixChain
import LittlewoodInverse.GeometricAsymptotic

open scoped Topology

namespace LittlewoodInverse

/-- The full uniform asymptotic assertion in Theorem 1.1, with the actual
sinc-moment constant and without any numerical or analytic extra premise. -/
theorem littlewood_asymptotic (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ A : Finset ℤ, N ≤ A.card →
      (littlewoodCoefficient - ε) * Real.log (A.card : ℝ) ≤ littlewoodNorm A := by
  by_cases hpos : 0 < littlewoodCoefficient - ε
  · let c : ℝ → ℝ := fun η => (9/10 : ℝ) *
      (1 - Real.sqrt ((1/3+η)*(tailError+η)))
    let f : ℝ → ℝ := fun η => c η / Real.log 9
    have hcont : Continuous f := by unfold f c; fun_prop
    have hf0 : f 0 = littlewoodCoefficient := by
      dsimp only [f, c, littlewoodCoefficient]
      simp only [add_zero]
      rw [show (1/3 : ℝ) * tailError = tailError/3 by ring]
      ring
    obtain ⟨d, hd, hclose⟩ := Metric.continuousAt_iff.mp hcont.continuousAt
      (ε/2) (by linarith)
    let η := d/2
    have hη : 0 < η := by dsimp only [η]; positivity
    have hnear : dist η 0 < d := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hη]
      dsimp only [η]
      linarith
    have hfη := hclose hnear
    rw [Real.dist_eq, hf0] at hfη
    have hslope : littlewoodCoefficient - ε/2 < f η := by
      have := (abs_lt.mp hfη).1
      linarith
    have hfpos : 0 < f η := by linarith
    have hlog : 0 < Real.log 9 := Real.log_pos (by norm_num)
    have hcpos : 0 < c η := (div_pos_iff_of_pos_right hlog).mp hfpos
    obtain ⟨base, hb, hscale⟩ := geometric_prefix_lower_bound η hη
    have hscale' : ∀ (J : ℕ) (A : Finset ℤ), base * 9^J ≤ A.card →
        c η * J ≤ littlewoodNorm A := by
      intro J A hJ
      convert hscale J A hJ using 1
      dsimp only [c]
      ring
    obtain ⟨N, hN⟩ := geometric_bounds_to_logarithmic hcpos.le hb hscale'
      (ε/2) (by linarith)
    refine ⟨N, ?_⟩
    intro A hA
    calc
      _ ≤ (f η - ε/2) * Real.log (A.card : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.log_natCast_nonneg _)
      _ ≤ _ := hN A hA
  · refine ⟨0, ?_⟩
    intro A _
    exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hpos)
      (Real.log_natCast_nonneg _)).trans (littlewoodNorm_nonneg A)

end LittlewoodInverse
