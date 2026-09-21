import LittlewoodInverse.AssemblyReduction
import LittlewoodInverse.CoverFreiman
import LittlewoodInverse.ChebyshevTransport

namespace LittlewoodInverse

/-- Once the two terminal geometry theorems are proved, the assembled and
high-order-model versions of the manuscript's inverse theorem follow. -/
theorem structural_inverse_of_terminal
    (ht : ∀ β Δ : ℝ, 0 < β → β ≤ 1 → 1 ≤ Δ → UniformTerminalCover β Δ) :
    StructuralInverseTheorem := by
  intro K ε β Δ hK hε hε1 hβ hβ1 hΔ
  obtain ⟨N, c, C, hN, hc, hC, hcover⟩ := assembly_inverse_of_terminal
    (ht β Δ hβ hβ1 hΔ) (K + 1) ε (by linarith) hε (by linarith)
  refine ⟨N, c, C, hN, hc, hC, ?_⟩
  intro A hAN hmodel hnorm
  have hA2 : 2 ≤ A.card := hN.trans hAN
  rcases hmodel with hgeom | ⟨A', f, hf, hgeom⟩
  · apply hcover A hAN hgeom
    have hlog : 0 ≤ Real.log (A.card : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ A.card by omega))
    nlinarith
  · have himage : A.image f = A' := by
      apply Finset.coe_injective
      simpa only [Finset.coe_image] using hf.bijOn.image_eq
    have hcard : A'.card = A.card := by
      rw [← himage]
      exact Finset.card_image_of_injOn hf.bijOn.injOn
    have hmodelnorm := freiman_model_logarithmic_bound hf hA2 hnorm
    rw [himage] at hmodelnorm
    have hA'cover := hcover A' (by simpa only [hcard] using hAN) hgeom hmodelnorm
    exact (almostCover_freiman_iff (hf.mono (hmn := hA2))).mpr hA'cover

end LittlewoodInverse
