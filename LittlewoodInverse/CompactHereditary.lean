import LittlewoodInverse.CompactCharacters
import LittlewoodInverse.DiscreteCharacters
import LittlewoodInverse.SpectralEnergy

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LittlewoodInverse

section Compact

variable {Γ G : Type*} [AddCommGroup Γ] [DecidableEq Γ] [CommGroup G]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [IsProbabilityMeasure μ] [Measure.IsMulLeftInvariant μ]
  (χ : Γ →+ Additive (PontryaginDual G)) (hχ : Function.Injective χ)

noncomputable def compactLittlewoodNorm (X : Finset Γ) : ℝ :=
  ∫ x, ‖compactPolynomial χ X (fun _ => 1) x‖ ∂μ

include hχ

theorem integral_compactSet_norm_four (X : Finset Γ) :
    (∫ x, ‖compactPolynomial χ X (fun _ => 1) x‖ ^ 4 ∂μ) =
      (additiveEnergy X : ℝ) := by
  rw [integral_compactPolynomial_norm_four μ χ hχ]
  simp only [one_mul, map_one, Complex.one_re, Complex.zero_re, apply_ite,
    additiveEnergy, Finset.addEnergy, Finset.card_filter,
    Nat.cast_sum, Nat.cast_one, Nat.cast_zero, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]

/-- Lemma 5.2 for any faithful family of characters on a compact abelian
group with probability Haar measure. The moment identities are proved
from character orthogonality, not supplied as hypotheses. -/
theorem compact_spectral_hereditary_energy {Y X : Finset Γ} (hYX : Y ⊆ X) :
    (Y.card : ℝ) ^ 4 / (compactLittlewoodNorm μ χ X ^ 2 * (X.card : ℝ)) ≤
      (additiveEnergy Y : ℝ) := by
  have hmain := complex_spectral_hereditary (μ := μ)
    (compactPolynomial χ X (fun _ => 1)) (compactPolynomial χ Y (fun _ => 1))
    (compact_integrable (by fun_prop)) (compact_integrable (by fun_prop))
    (compact_integrable (by fun_prop)) (compact_integrable (by fun_prop))
    (compact_integrable (by fun_prop))
  have hpair : ‖∫ x, compactPolynomial χ X (fun _ => 1) x *
      star (compactPolynomial χ Y (fun _ => 1) x) ∂μ‖ = (Y.card : ℝ) := by
    rw [Complex.star_def, integral_compactPolynomial_pair μ χ hχ]
    simp [Finset.inter_eq_right.mpr hYX]
  have hsq : (∫ x, ‖compactPolynomial χ X (fun _ => 1) x‖ ^ 2 ∂μ) =
      (X.card : ℝ) := by simp [integral_compactPolynomial_norm_sq μ χ hχ]
  rw [hpair, hsq, integral_compactSet_norm_four μ χ hχ] at hmain
  exact hmain

end Compact

section DiscreteDual

variable (Γ : Type*) [AddCommGroup Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]

noncomputable local instance dualMeasurableSpace :
    MeasurableSpace (PontryaginDual (Multiplicative Γ)) := borel _
local instance dualBorelSpace : BorelSpace (PontryaginDual (Multiplicative Γ)) := ⟨rfl⟩

/-- The actual Haar measure on the compact dual of a discrete abelian
group, normalized on the entire compact group. -/
noncomputable def discreteDualMeasure : Measure (PontryaginDual (Multiplicative Γ)) :=
  Measure.haarMeasure ⊤

instance discreteDualMeasure_probability : IsProbabilityMeasure (discreteDualMeasure Γ) := by
  constructor
  exact Measure.haarMeasure_self

instance discreteDualMeasure_leftInvariant : Measure.IsMulLeftInvariant (discreteDualMeasure Γ) :=
  inferInstanceAs (Measure.IsMulLeftInvariant (Measure.haarMeasure ⊤))

noncomputable def discreteLittlewoodNorm (X : Finset Γ) : ℝ :=
  compactLittlewoodNorm (discreteDualMeasure Γ) (discreteEvaluation Γ) X

/-- Full arbitrary-discrete-abelian-group form of Lemma 5.2. The dual,
evaluation characters, their injectivity, and normalized Haar measure
are all concrete; no compact Fourier model is assumed. -/
theorem discrete_spectral_hereditary_energy [DecidableEq Γ]
    {Y X : Finset Γ} (hYX : Y ⊆ X) :
    (Y.card : ℝ) ^ 4 / (discreteLittlewoodNorm Γ X ^ 2 * (X.card : ℝ)) ≤
      (additiveEnergy Y : ℝ) :=
  compact_spectral_hereditary_energy (discreteDualMeasure Γ) (discreteEvaluation Γ)
    (discreteEvaluation_injective Γ) hYX

end DiscreteDual
end LittlewoodInverse
