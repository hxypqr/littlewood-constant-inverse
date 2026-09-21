import LittlewoodInverse.OuterDamping

open MeasureTheory

namespace LittlewoodInverse

/-- Data actually constructed by Lemma 4.1 for one finite Fourier sum. -/
structure DampingData (a : ℝ) (A : Finset ℤ) where
  multiplier : Circle → ℂ
  memLp : MemLp multiplier ⊤ circleMeasure
  support : NonpositiveFourierSupport multiplier
  modulus : ∀ᵐ t ∂circleMeasure, ‖multiplier t‖ = 1 - a * (‖fourierPolynomial A t‖ / A.card)
  zeroCoeff : circleFourierCoeff multiplier 0 =
    (Real.exp (∫ t, Real.log (1 - a * (‖fourierPolynomial A t‖ / A.card)) ∂circleMeasure) : ℂ)

theorem exists_dampingData {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (A : Finset ℤ) (hA : A.Nonempty) : Nonempty (DampingData a A) := by
  obtain ⟨M, hm, hs, hmod, hz, _⟩ := outer_damping_fourierPolynomial ha0 ha1 A hA
  exact ⟨⟨M, hm, hs, hmod, hz⟩⟩

end LittlewoodInverse
