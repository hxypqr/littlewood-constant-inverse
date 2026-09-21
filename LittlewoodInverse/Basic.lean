import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Concrete objects for the Littlewood manuscript

All circle integrals use probability Haar measure. Additive energy is the
actual finite count provided by mathlib, not a parameter satisfying axioms.
-/

open scoped BigOperators Pointwise
open MeasureTheory

namespace LittlewoodInverse

abbrev Circle := AddCircle (1 : ℝ)

noncomputable def circleMeasure : Measure Circle := AddCircle.haarAddCircle

instance : IsProbabilityMeasure circleMeasure := by
  unfold circleMeasure
  infer_instance

/-- The exponential sum with coefficient one at every element of `A`. -/
noncomputable def fourierPolynomial (A : Finset ℤ) (t : Circle) : ℂ :=
  ∑ a ∈ A, fourier a t

/-- The Fourier `L¹` norm of the indicator of an integer set. -/
noncomputable def littlewoodNorm (A : Finset ℤ) : ℝ :=
  ∫ t, ‖fourierPolynomial A t‖ ∂circleMeasure

/-- An exponential sum indexed in increasing frequency order. -/
noncomputable def weightedFourierPolynomial {m : ℕ}
    (n : Fin m → ℤ) (u : Fin m → ℂ) (t : Circle) : ℂ :=
  ∑ j, u j * fourier (n j) t

/-- The number of ordered quadruples in `A⁴` with equal pair sums. -/
def additiveEnergy {G : Type*} [Add G] [DecidableEq G] (A : Finset G) : ℕ :=
  Finset.addEnergy A A

/-- The sumset, with repeated representations counted only once. -/
def sumset {G : Type*} [Add G] [DecidableEq G] (A : Finset G) : Finset G :=
  A + A

/-- Pairings are linear in the first argument. -/
noncomputable def circlePairing (f g : Circle → ℂ) : ℂ :=
  ∫ t, f t * star (g t) ∂circleMeasure

/-- Fourier coefficients with the manuscript's `e(-nt)` convention. -/
noncomputable def circleFourierCoeff (f : Circle → ℂ) (n : ℤ) : ℂ :=
  ∫ t, f t * fourier (-n) t ∂circleMeasure

theorem fourierPolynomial_continuous (A : Finset ℤ) : Continuous (fourierPolynomial A) := by
  unfold fourierPolynomial
  fun_prop

theorem fourierPolynomial_integrable (A : Finset ℤ) :
    Integrable (fourierPolynomial A) circleMeasure :=
  (fourierPolynomial_continuous A).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem littlewoodNorm_nonneg (A : Finset ℤ) : 0 ≤ littlewoodNorm A :=
  integral_nonneg fun _ ↦ norm_nonneg _

@[simp] theorem littlewoodNorm_empty : littlewoodNorm ∅ = 0 := by
  simp [littlewoodNorm, fourierPolynomial]

@[simp] theorem littlewoodNorm_singleton (a : ℤ) : littlewoodNorm {a} = 1 := by
  simp [littlewoodNorm, fourierPolynomial, fourier_apply]

theorem additiveEnergy_pos {G : Type*} [Add G] [DecidableEq G]
    {A : Finset G} (hA : A.Nonempty) : 0 < additiveEnergy A :=
  Finset.addEnergy_self_pos hA

/-- The counting Cauchy--Schwarz bound, without division by a possibly empty sumset. -/
theorem card_pow_four_le_sumset_mul_energy {G : Type*} [Add G] [DecidableEq G]
    (A : Finset G) : A.card ^ 4 ≤ (sumset A).card * additiveEnergy A := by
  simpa [sumset, additiveEnergy, ← pow_add] using Finset.le_card_add_mul_addEnergy A A

end LittlewoodInverse
