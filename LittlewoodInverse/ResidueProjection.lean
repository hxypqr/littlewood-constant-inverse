import LittlewoodInverse.FibreBudget
import LittlewoodInverse.CyclicSpectral
import LittlewoodInverse.NormBounds

open scoped BigOperators
open MeasureTheory

namespace LittlewoodInverse

variable (q : ℕ) [NeZero q]

/-- A single residue projection is contractive, without a Sidon hypothesis. -/
theorem fibre_norm_le (R : Finset (ZMod q)) (child : ZMod q → Finset ℤ)
    {r : ZMod q} (hr : r ∈ R) :
    littlewoodNorm (child r) ≤ littlewoodNorm (fibreUnion q R child) := by
  have hpoint (t : Circle) : ‖fourierPolynomial (child r) ((q : ℤ) • t)‖ ≤
      ∫ j, ‖fourierPolynomial (fibreUnion q R child) (t + ZMod.toAddCircle j)‖
        ∂cyclicMeasure q := by
    have h := cyclicCoefficient_norm_le_integral q
      (fun s => fourier (s.val : ℤ) t * fourierPolynomial (child s) ((q : ℤ) • t)) hr
    simp only [← fibre_cyclic_expansion q R child t] at h
    simpa [norm_mul, fourier_apply] using h
  calc
    littlewoodNorm (child r) =
        ∫ t, ‖fourierPolynomial (child r) ((q : ℤ) • t)‖ ∂circleMeasure :=
      (circle_integral_zsmul q _ (fourierPolynomial_continuous (child r)).norm).symm
    _ ≤ ∫ t, (∫ j, ‖fourierPolynomial (fibreUnion q R child)
          (t + ZMod.toAddCircle j)‖ ∂cyclicMeasure q) ∂circleMeasure := by
      apply integral_mono _ (continuous_circle_integrable (cyclicTranslate_average_continuous q _)) hpoint
      exact continuous_circle_integrable
        (((fourierPolynomial_continuous (child r)).comp (continuous_zsmul (q : ℤ))).norm)
    _ = _ := cyclicTranslate_average_integral q _

def residueChild (A : Finset ℤ) (r : ZMod q) : Finset ℤ :=
  (A.filter (fun z : ℤ => (z : ZMod q) = r)).image (fun z => z / (q : ℤ))

theorem residue_reconstruction (z : ℤ) :
    (((z : ZMod q).val : ℕ) : ℤ) + (q : ℤ) * (z / (q : ℤ)) = z := by
  rw [ZMod.val_intCast]
  exact Int.emod_add_mul_ediv z q

theorem affineImage_residueChild (A : Finset ℤ) (r : ZMod q) :
    affineImage (r.val : ℤ) q (residueChild q A r) = A.filter (fun z : ℤ => (z : ZMod q) = r) := by
  classical
  ext z
  simp only [affineImage, residueChild, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨u, ⟨x, ⟨hx, hxr⟩, rfl⟩, hzu⟩
    have he : (r.val : ℤ) + (q : ℤ) * (x / (q : ℤ)) = x := by
      simpa only [hxr] using residue_reconstruction q x
    rw [he] at hzu
    subst z
    exact ⟨hx, hxr⟩
  · rintro ⟨hz, hzr⟩
    exact ⟨z / (q : ℤ), ⟨z, ⟨hz, hzr⟩, rfl⟩, by
      simpa only [hzr] using residue_reconstruction q z⟩

theorem fibreUnion_residueChild (A : Finset ℤ) :
    fibreUnion q Finset.univ (residueChild q A) = A := by
  classical
  ext z
  simp only [fibreUnion, Finset.mem_biUnion, affineImage_residueChild,
    Finset.mem_univ, Finset.mem_filter, true_and]
  aesop

/-- Lemma 2.3: deleting all but one complete residue fibre is contractive. -/
theorem residue_projection_norm_le (A : Finset ℤ) (r : ZMod q) :
    littlewoodNorm (A.filter (fun z : ℤ => (z : ZMod q) = r)) ≤ littlewoodNorm A := by
  rw [← affineImage_residueChild]
  change littlewoodNorm ((residueChild q A r).image (fun z => (r.val : ℤ) + (q : ℤ) * z)) ≤ _
  rw [littlewoodNorm_affine _ _ (by exact_mod_cast NeZero.ne q)]
  have h := fibre_norm_le q Finset.univ (residueChild q A) (Finset.mem_univ r)
  simpa only [fibreUnion_residueChild] using h

end LittlewoodInverse
