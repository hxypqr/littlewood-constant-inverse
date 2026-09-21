import LittlewoodInverse.CyclicSidon
import LittlewoodInverse.SpectralEnergy

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LittlewoodInverse

variable (q : ℕ) [NeZero q]

noncomputable def cyclicLittlewoodNorm (A : Finset (ZMod q)) : ℝ :=
  ∫ j, ‖cyclicPolynomial q A (fun _ => 1) j‖ ∂cyclicMeasure q

theorem integral_cyclicSet_norm_four (A : Finset (ZMod q)) :
    (∫ j, ‖cyclicPolynomial q A (fun _ => 1) j‖ ^ 4 ∂cyclicMeasure q) =
      (additiveEnergy A : ℝ) := by
  rw [integral_cyclicPolynomial_norm_four]
  simp only [one_mul, map_one, Complex.one_re, Complex.zero_re, apply_ite,
    additiveEnergy, Finset.addEnergy, Finset.card_filter,
    Nat.cast_sum, Nat.cast_one, Nat.cast_zero, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]

/-- Lemma 5.2 on the actual finite cyclic dual group, with probability measure. -/
theorem cyclic_spectral_hereditary_energy {Y X : Finset (ZMod q)} (hYX : Y ⊆ X) :
    (Y.card : ℝ) ^ 4 / (cyclicLittlewoodNorm q X ^ 2 * (X.card : ℝ)) ≤
      (additiveEnergy Y : ℝ) := by
  have hmain := complex_spectral_hereditary (μ := cyclicMeasure q)
    (cyclicPolynomial q X (fun _ => 1)) (cyclicPolynomial q Y (fun _ => 1))
    (cyclic_integrable q _) (cyclic_integrable q _) (cyclic_integrable q _)
    (cyclic_integrable q _) (cyclic_integrable q _)
  have hpair : ‖∫ j, cyclicPolynomial q X (fun _ => 1) j *
      star (cyclicPolynomial q Y (fun _ => 1) j) ∂cyclicMeasure q‖ = (Y.card : ℝ) := by
    rw [Complex.star_def, integral_cyclicPolynomial_pair]
    simp [Finset.inter_eq_right.mpr hYX]
  have hsq : (∫ j, ‖cyclicPolynomial q X (fun _ => 1) j‖ ^ 2 ∂cyclicMeasure q) =
      (X.card : ℝ) := by simp [integral_cyclicPolynomial_norm_sq]
  rw [hpair, hsq, integral_cyclicSet_norm_four] at hmain
  exact hmain

theorem cyclicCoefficient_norm_le_integral {R : Finset (ZMod q)} (a : ZMod q → ℂ)
    {r : ZMod q} (hr : r ∈ R) :
    ‖a r‖ ≤ ∫ j, ‖cyclicPolynomial q R a j‖ ∂cyclicMeasure q := by
  have hp : (∫ j, cyclicPolynomial q R a j * conj (cyclicCharacter q r j)
      ∂cyclicMeasure q) = a r := by
    have h := integral_cyclicPolynomial_pair q R {r} a (fun _ => 1)
    simpa [cyclicPolynomial, hr] using h
  calc
    ‖a r‖ = ‖∫ j, cyclicPolynomial q R a j * conj (cyclicCharacter q r j)
      ∂cyclicMeasure q‖ := congrArg norm hp.symm
    _ ≤ ∫ j, ‖cyclicPolynomial q R a j * conj (cyclicCharacter q r j)‖
      ∂cyclicMeasure q := norm_integral_le_integral_norm _
    _ = _ := by simp

theorem one_le_cyclicLittlewoodNorm {A : Finset (ZMod q)} (hA : A.Nonempty) :
    1 ≤ cyclicLittlewoodNorm q A := by
  obtain ⟨a, ha⟩ := hA
  simpa [cyclicLittlewoodNorm] using cyclicCoefficient_norm_le_integral q (fun _ => 1) ha

theorem cyclicLittlewoodNorm_nonneg (A : Finset (ZMod q)) :
    0 ≤ cyclicLittlewoodNorm q A := integral_nonneg fun _ => norm_nonneg _

theorem cyclicLittlewoodNorm_le_sqrt_card (A : Finset (ZMod q)) :
    cyclicLittlewoodNorm q A ≤ Real.sqrt (A.card : ℝ) := by
  have hs := integral_cauchy_schwarz_sq (μ := cyclicMeasure q)
    (f := fun j => ‖cyclicPolynomial q A (fun _ => 1) j‖) (g := fun _ => (1 : ℝ))
    (cyclic_integrable q _) (cyclic_integrable q _) (cyclic_integrable q _)
  simp only [mul_one, one_pow, integral_const, probReal_univ, smul_eq_mul,
    integral_cyclicPolynomial_norm_sq, norm_one, Finset.sum_const, nsmul_eq_mul] at hs
  exact (Real.le_sqrt (cyclicLittlewoodNorm_nonneg q A) (Nat.cast_nonneg _)).mpr hs

end LittlewoodInverse
