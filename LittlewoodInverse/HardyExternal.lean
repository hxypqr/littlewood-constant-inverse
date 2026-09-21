import LittlewoodInverse.Basic
import Mathlib.Analysis.Complex.Poisson
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Standard Hardy-space boundary inputs

These are external theorems, not manuscript conclusions.  The Schwarz integral
below is explicit; the two statements apply to arbitrary bounded real boundary
data and arbitrary bounded holomorphic disk functions, respectively.

References and normalization are recorded in `verification/EXTERNAL_INPUTS.md`.
The Poisson facts are the disk case of Axler–Bourdon–Ramey, *Harmonic Function
Theory*, Proposition 1.20 and Theorem 6.39.  The Hardy boundary/Cauchy facts are
standard Duren inputs, also stated in Auberson–Epele–Mahoux–Simão (1975),
Appendix A, Theorems A.1, A.5 and A.6.
-/

open scoped ComplexConjugate Topology
open MeasureTheory Filter

namespace LittlewoodInverse

/-- The actual Schwarz integral, with normalized Haar measure on `ℝ/ℤ`. -/
noncomputable def schwarzIntegral (ell : Circle → ℝ) (z : ℂ) : ℂ :=
  ∫ t, ((fourier 1 t + z) / (fourier 1 t - z)) * (ell t : ℂ) ∂circleMeasure

noncomputable def radialPoint (r : ℝ) (t : Circle) : ℂ := (r : ℂ) * fourier 1 t

namespace HardyExternal

/-- Schwarz–Poisson boundary theorem for arbitrary essentially bounded real data.
The real-part inequalities are the positivity and unit-mass consequence of the
Poisson kernel, and the radial limit is the radial specialization of Fatou's
Poisson-integral theorem. -/
axiom schwarz_integral_boundary (ell : Circle → ℝ)
    (hell : MemLp ell ⊤ circleMeasure) (L U : ℝ)
    (hbound : ∀ᵐ t ∂circleMeasure, L ≤ ell t ∧ ell t ≤ U) :
    DifferentiableOn ℂ (schwarzIntegral ell) (Metric.ball 0 1) ∧
      (∀ z : ℂ, ‖z‖ < 1 → L ≤ (schwarzIntegral ell z).re ∧
        (schwarzIntegral ell z).re ≤ U) ∧
      ∀ᵐ t ∂circleMeasure,
        Tendsto (fun r : ℝ ↦ (schwarzIntegral ell (radialPoint r t)).re)
          (𝓝[Set.Iio 1] 1) (𝓝 (ell t))

/-- Fatou's bounded-holomorphic boundary theorem, with the standard Cauchy/Fourier
identification of the boundary coefficients.  The support has the usual analytic
(nonnegative) orientation; no reflected or damping function is assumed. -/
axiom bounded_holomorphic_radial_boundary (f : ℂ → ℂ) (C : ℝ)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hbound : ∀ z : ℂ, ‖z‖ < 1 → ‖f z‖ ≤ C) :
    ∃ g : Circle → ℂ, MemLp g ⊤ circleMeasure ∧
      (∀ᵐ t ∂circleMeasure, ‖g t‖ ≤ C) ∧
      (∀ᵐ t ∂circleMeasure,
        Tendsto (fun r : ℝ ↦ f (radialPoint r t)) (𝓝[Set.Iio 1] 1) (𝓝 (g t))) ∧
      (∀ n : ℤ, n < 0 → circleFourierCoeff g n = 0) ∧
      circleFourierCoeff g 0 = f 0

end HardyExternal
end LittlewoodInverse
