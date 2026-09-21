import LittlewoodInverse.FiniteBand
import LittlewoodInverse.PacketGeometry

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LittlewoodInverse

theorem circleFourierCoeff_modulate (f : Circle → ℂ) (b n : ℤ) :
    circleFourierCoeff (fun t => fourier b t * f t) n = circleFourierCoeff f (n - b) := by
  unfold circleFourierCoeff
  apply integral_congr_ae
  filter_upwards [] with t
  have he : -(n - b) = b + -n := by ring
  rw [he, fourier_add]
  ring

namespace DenseBlocks

noncomputable def certificate {β Δ : ℝ} {A : Finset ℤ} (data : DenseBlocks β Δ A)
    (i : Fin data.count) (t : Circle) : ℂ :=
  fourier (data.centre i) t * finiteBandCertificate data.radius (data.block i) t

theorem certificate_continuous {β Δ : ℝ} {A : Finset ℤ} (data : DenseBlocks β Δ A)
    (i : Fin data.count) : Continuous (data.certificate i) :=
  (fourier _).continuous.mul (finiteBandCertificate_continuous _ _)

theorem certificate_norm_le {β Δ : ℝ} {A : Finset ℤ} (data : DenseBlocks β Δ A)
    (i : Fin data.count) (t : Circle) : ‖data.certificate i t‖ ≤ 1 := by
  simpa [certificate, norm_mul, fourier_apply] using
    norm_finiteBandCertificate_le_one data.radius_pos (data.block i) t

theorem certificate_coeff {β Δ : ℝ} {A : Finset ℤ} (data : DenseBlocks β Δ A)
    (i : Fin data.count) (n : ℤ) :
    circleFourierCoeff (data.certificate i) n =
      circleFourierCoeff (finiteBandCertificate data.radius (data.block i)) (n - data.centre i) :=
  circleFourierCoeff_modulate _ _ _

theorem other_block_coeff_zero {β Δ : ℝ} {A : Finset ℤ} (data : DenseBlocks β Δ A)
    (i j : Fin data.count) (hij : i ≠ j) {x : ℤ} (hx : x ∈ data.block j) :
    circleFourierCoeff (data.certificate i) (data.centre j + x) = 0 := by
  rw [data.certificate_coeff]
  apply finiteBandCertificate_support
  by_contra h
  have hbound := abs_le.mp (le_of_not_gt h)
  have hxb := data.block_mem j x hx
  have hc : |data.centre i - data.centre j| ≤ 3 * (data.radius : ℤ) := by
    apply abs_le.mpr
    constructor <;> omega
  have hs := data.separated i j hij
  omega

/-- The certificates pair with the full original target, not a deleted union. -/
theorem certificate_pairing {β Δ : ℝ} {A : Finset ℤ} (data : DenseBlocks β Δ A)
    (i : Fin data.count) :
    circlePairing (fourierPolynomial A) (data.certificate i) =
      ((littlewoodNorm (data.block i) / 3 : ℝ) : ℂ) := by
  classical
  have hi := continuous_circle_integrable (data.certificate_continuous i)
  change circlePairing (indexedFourierSum A id) _ = _
  rw [circlePairing_indexedFourierSum _ _ hi]
  simp only [id_eq]
  have hsum := congrArg (fun S : Finset ℤ =>
    ∑ n ∈ S, conj (circleFourierCoeff (data.certificate i) n)) data.exact_union
  rw [hsum, Finset.sum_biUnion
    (fun j _ k _ hjk => data.translated_disjoint j k hjk)]
  have hinner (j : Fin data.count) :
      (∑ n ∈ affineImage (data.centre j) 1 (data.block j),
        conj (circleFourierCoeff (data.certificate i) n)) =
      if j = i then circlePairing (fourierPolynomial (data.block i))
        (finiteBandCertificate data.radius (data.block i)) else 0 := by
    unfold affineImage
    rw [Finset.sum_image (fun x _ y _ h => affine_injective _ 1 (by norm_num) h)]
    simp only [one_mul]
    by_cases hji : j = i
    · subst j
      rw [if_pos rfl]
      change _ = circlePairing (indexedFourierSum (data.block i) id) _
      rw [circlePairing_indexedFourierSum _ _
        (continuous_circle_integrable (finiteBandCertificate_continuous _ _))]
      apply Finset.sum_congr rfl
      intro x hx
      rw [data.certificate_coeff]
      simp
    · rw [if_neg hji]
      apply Finset.sum_eq_zero
      intro x hx
      rw [data.other_block_coeff_zero i j (Ne.symm hji) hx, map_zero]
  simp_rw [hinner]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ i)]
  exact circlePairing_finiteBandCertificate data.radius_pos (data.block i)
    (fun x hx => abs_le.mpr (data.block_mem i x hx))

end DenseBlocks
end LittlewoodInverse
