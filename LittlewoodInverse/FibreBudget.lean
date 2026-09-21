import LittlewoodInverse.CyclicSidon
import LittlewoodInverse.CarryLift

open scoped BigOperators Pointwise ENNReal
open MeasureTheory

namespace LittlewoodInverse

variable (q : ℕ) [NeZero q]

private instance circleMeasure_isAddHaar : circleMeasure.IsAddHaarMeasure := by
  unfold circleMeasure
  infer_instance

noncomputable def fibreUnion (R : Finset (ZMod q)) (child : ZMod q → Finset ℤ) : Finset ℤ :=
  R.biUnion fun r => affineImage (r.val : ℤ) q (child r)

theorem fibre_disjoint (child : ZMod q → Finset ℤ) {r s : ZMod q} (hrs : r ≠ s) :
    Disjoint (affineImage (r.val : ℤ) q (child r)) (affineImage (s.val : ℤ) q (child s)) := by
  apply Finset.disjoint_left.mpr
  intro z hz hs
  obtain ⟨u, hu, hzu⟩ := Finset.mem_image.mp hz
  obtain ⟨v, hv, hzv⟩ := Finset.mem_image.mp hs
  have he : residueHeight q (r, u) = residueHeight q (s, v) := hzu.trans hzv.symm
  exact hrs (congrArg Prod.fst (residueHeight_injective q he))

theorem fourier_character_add (n : ℤ) (t s : Circle) :
    fourier n (t + s) = fourier n t * fourier n s := by
  simp [fourier_apply, AddCircle.toCircle_add]

theorem fourier_mul_index (n m : ℤ) (t : Circle) :
    fourier (n * m) t = fourier m (n • t) := by
  simp only [fourier_apply, smul_smul, mul_comm]

theorem fourierPolynomial_affine (u : ℤ) (C : Finset ℤ) (t : Circle) :
    fourierPolynomial (affineImage u q C) t =
      fourier u t * fourierPolynomial C ((q : ℤ) • t) := by
  unfold fourierPolynomial affineImage
  rw [Finset.sum_image (fun x _ y _ h => affine_injective u q
    (by exact_mod_cast (NeZero.ne q)) h), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [fourier_add, fourier_mul_index]

theorem fourierPolynomial_fibreUnion (R : Finset (ZMod q)) (child : ZMod q → Finset ℤ)
    (t : Circle) :
    fourierPolynomial (fibreUnion q R child) t =
      ∑ r ∈ R, fourier (r.val : ℤ) t * fourierPolynomial (child r) ((q : ℤ) • t) := by
  unfold fibreUnion fourierPolynomial
  rw [Finset.sum_biUnion (fun r _ s _ hrs => fibre_disjoint q child hrs)]
  apply Finset.sum_congr rfl
  intro r hr
  exact fourierPolynomial_affine q (r.val : ℤ) (child r) t

theorem q_smul_cyclicShift (j : ZMod q) : (q : ℤ) • ZMod.toAddCircle j = 0 := by
  rw [← map_zsmul]
  simp [zsmul_eq_mul]

theorem fourier_cyclicShift (r j : ZMod q) :
    fourier (r.val : ℤ) (ZMod.toAddCircle j) = cyclicCharacter q r j := by
  rw [fourier_apply, ← map_zsmul]
  simp only [zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  rfl

/-- Exact fibre expansion under a torsion translation of the circle. -/
theorem fibre_cyclic_expansion (R : Finset (ZMod q)) (child : ZMod q → Finset ℤ)
    (t : Circle) (j : ZMod q) :
    fourierPolynomial (fibreUnion q R child) (t + ZMod.toAddCircle j) =
      cyclicPolynomial q R (fun r =>
        fourier (r.val : ℤ) t * fourierPolynomial (child r) ((q : ℤ) • t)) j := by
  rw [fourierPolynomial_fibreUnion]
  unfold cyclicPolynomial
  apply Finset.sum_congr rfl
  intro r hr
  rw [fourier_character_add, fourier_cyclicShift, smul_add, q_smul_cyclicShift, add_zero]
  ring

theorem circle_integral_zsmul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : Circle → E) (hf : Continuous f) :
    (∫ t, f ((q : ℤ) • t) ∂circleMeasure) = ∫ t, f t ∂circleMeasure := by
  have hmp := Measure.measurePreserving_zsmul circleMeasure
    (show (q : ℤ) ≠ 0 by exact_mod_cast (NeZero.ne q))
  calc
    (∫ t, f ((q : ℤ) • t) ∂circleMeasure) =
        ∫ t, f t ∂Measure.map (fun t : Circle => (q : ℤ) • t) circleMeasure :=
      (integral_map hmp.measurable.aemeasurable hf.aestronglyMeasurable).symm
    _ = _ := by rw [hmp.map_eq]

private instance twenty_ge_one : Fact ((1 : ℝ≥0∞) ≤ 20) := ⟨by norm_num⟩

omit [NeZero q] in
theorem pilp_norm_twentieth {ι : Type*} [Fintype ι]
    (v : PiLp (20 : ℝ≥0∞) (fun _ : ι => ℝ)) : ‖v‖ ^ 20 = ∑ i, ‖v i‖ ^ 20 := by
  rw [PiLp.norm_eq_of_nat (p := (20 : ℝ≥0∞)) 20 (by norm_num) v]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Finset.sum_nonneg fun i _ => by positivity)]
  norm_num

noncomputable def fibreNormVector (R : Finset (ZMod q)) (child : ZMod q → Finset ℤ)
    (t : Circle) : PiLp (20 : ℝ≥0∞) (fun _ : R => ℝ) :=
  WithLp.toLp 20 (fun r => ‖fourierPolynomial (child r) ((q : ℤ) • t)‖)

omit [NeZero q] in
theorem fibreNormVector_continuous (R : Finset (ZMod q)) (child : ZMod q → Finset ℤ) :
    Continuous (fibreNormVector q R child) := by
  apply (PiLp.continuous_toLp 20 (fun _ : R => ℝ)).comp
  apply continuous_pi
  intro r
  exact ((fourierPolynomial_continuous (child r)).comp (continuous_zsmul (q : ℤ))).norm

theorem fibreNormVector_pointwise (R : Finset (ZMod q)) (hR : AdditiveSidon R)
    (child : ZMod q → Finset ℤ) (t : Circle) :
    ‖fibreNormVector q R child t‖ ≤
      ∫ j, ‖fourierPolynomial (fibreUnion q R child) (t + ZMod.toAddCircle j)‖ ∂cyclicMeasure q := by
  have h := cyclic_sidon_twentieth q hR
    (fun r => fourier (r.val : ℤ) t * fourierPolynomial (child r) ((q : ℤ) • t))
  have hv : ‖fibreNormVector q R child t‖ ^ 20 =
      ∑ r ∈ R, ‖fourierPolynomial (child r) ((q : ℤ) • t)‖ ^ 20 := by
    rw [pilp_norm_twentieth]
    simp only [fibreNormVector, PiLp.toLp_apply, Real.norm_eq_abs, abs_norm]
    exact Finset.sum_coe_sort R (fun r => ‖fourierPolynomial (child r) ((q : ℤ) • t)‖ ^ 20)
  have hpoint (j : ZMod q) := fibre_cyclic_expansion q R child t j
  have hcoeff (r : ZMod q) :
      ‖fourier (r.val : ℤ) t * fourierPolynomial (child r) ((q : ℤ) • t)‖ =
      ‖fourierPolynomial (child r) ((q : ℤ) • t)‖ := by simp [fourier_apply]
  simp only [hcoeff, ← hpoint] at h
  rw [← hv] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (integral_nonneg fun j => norm_nonneg _) (by decide : 20 ≠ 0)).1 h

theorem fibreNormVector_integral_coordinate (R : Finset (ZMod q))
    (child : ZMod q → Finset ℤ) (r : R) :
    (∫ t, fibreNormVector q R child t ∂circleMeasure) r = littlewoodNorm (child r) := by
  have hi := (PiLp.proj (𝕜 := ℝ) (20 : ℝ≥0∞) (fun _ : R => ℝ) r).integral_comp_comm
    (continuous_circle_integrable (fibreNormVector_continuous q R child))
  have he : (∫ t, ‖fourierPolynomial (child r) ((q : ℤ) • t)‖ ∂circleMeasure) =
      (∫ t, fibreNormVector q R child t ∂circleMeasure) r := hi
  rw [← he]
  exact circle_integral_zsmul q _ (fourierPolynomial_continuous (child r)).norm

theorem cyclicTranslate_average_continuous (A : Finset ℤ) :
    Continuous (fun t : Circle =>
      ∫ j, ‖fourierPolynomial A (t + ZMod.toAddCircle j)‖ ∂cyclicMeasure q) := by
  simp_rw [integral_cyclicMeasure, smul_eq_mul]
  apply continuous_const.mul
  apply continuous_finsetSum
  intro j hj
  exact ((fourierPolynomial_continuous A).comp (continuous_id.add continuous_const)).norm

/-- Averaging over all torsion translates preserves the original target's
Fourier norm. No norm of a deleted-frequency subset is introduced. -/
theorem cyclicTranslate_average_integral (A : Finset ℤ) :
    (∫ t : Circle, (∫ j, ‖fourierPolynomial A (t + ZMod.toAddCircle j)‖ ∂cyclicMeasure q)
      ∂circleMeasure) = littlewoodNorm A := by
  simp_rw [integral_cyclicMeasure, smul_eq_mul]
  have hj (j : ZMod q) : Integrable
      (fun t : Circle => ‖fourierPolynomial A (t + ZMod.toAddCircle j)‖) circleMeasure :=
    continuous_circle_integrable
      (((fourierPolynomial_continuous A).comp (continuous_id.add continuous_const)).norm)
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun j _ => hj j)]
  have htrans (j : ZMod q) :
      (∫ t : Circle, ‖fourierPolynomial A (t + ZMod.toAddCircle j)‖ ∂circleMeasure) =
        littlewoodNorm A := by
    exact integral_add_right_eq_self (μ := circleMeasure)
      (fun t : Circle => ‖fourierPolynomial A t‖) (ZMod.toAddCircle j)
  simp_rw [htrans]
  simp [ZMod.card, NeZero.ne q]

/-- The actual fibre budget in Proposition 8.2. Arbitrary empty fibres are
also allowed; cyclic Sidon support and nonzero modulus are sufficient. -/
theorem actual_fibre_twentieth_budget (R : Finset (ZMod q)) (hR : AdditiveSidon R)
    (child : ZMod q → Finset ℤ) :
    (∑ r ∈ R, littlewoodNorm (child r) ^ 20) ≤ littlewoodNorm (fibreUnion q R child) ^ 20 := by
  have hvec := fibreNormVector_continuous q R child
  have hpoint := fibreNormVector_pointwise q R hR child
  have hinter : ‖∫ t, fibreNormVector q R child t ∂circleMeasure‖ ≤
      littlewoodNorm (fibreUnion q R child) := by
    calc
      ‖∫ t, fibreNormVector q R child t ∂circleMeasure‖ ≤
          ∫ t, ‖fibreNormVector q R child t‖ ∂circleMeasure := norm_integral_le_integral_norm _
      _ ≤ ∫ t : Circle, (∫ j, ‖fourierPolynomial (fibreUnion q R child)
            (t + ZMod.toAddCircle j)‖ ∂cyclicMeasure q) ∂circleMeasure :=
        integral_mono (continuous_circle_integrable hvec.norm)
          (continuous_circle_integrable (cyclicTranslate_average_continuous q _)) hpoint
      _ = _ := cyclicTranslate_average_integral q _
  have hpow := pow_le_pow_left₀ (norm_nonneg _) hinter 20
  rw [pilp_norm_twentieth] at hpow
  simp_rw [fibreNormVector_integral_coordinate, Real.norm_eq_abs,
    abs_of_nonneg (littlewoodNorm_nonneg _)] at hpow
  have hsum : (∑ r : R, littlewoodNorm (child r) ^ 20) =
      ∑ r ∈ R, littlewoodNorm (child r) ^ 20 :=
    Finset.sum_coe_sort R (fun r : ZMod q => littlewoodNorm (child r) ^ 20)
  rw [hsum] at hpow
  exact hpow

end LittlewoodInverse
