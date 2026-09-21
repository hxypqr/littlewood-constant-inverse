import LittlewoodInverse.CompactCharacters

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LittlewoodInverse

variable {Γ G : Type*} [AddCommGroup Γ] [DecidableEq Γ] [CommGroup G]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [IsProbabilityMeasure μ] [Measure.IsMulLeftInvariant μ]
  (χ : Γ →+ Additive (PontryaginDual G)) (hχ : Function.Injective χ)

include hχ
omit hχ [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [IsProbabilityMeasure μ] [Measure.IsMulLeftInvariant μ] in
/-- A Sidon relation contributes only one of the two trivial pairings. -/
theorem compact_sidon_fourth_term_le {R : Finset (Γ)} (hR : AdditiveSidon R)
    (a : Γ → ℂ) {r s u v : Γ}
    (hr : r ∈ R) (hs : s ∈ R) (hu : u ∈ R) (hv : v ∈ R) :
    (if r + s = u + v then (a r * a s) * conj (a u * a v) else 0).re ≤
      (if r = u ∧ s = v then ‖a r‖ ^ 2 * ‖a s‖ ^ 2 else 0) +
      (if r = v ∧ s = u then ‖a r‖ ^ 2 * ‖a s‖ ^ 2 else 0) := by
  by_cases he : r + s = u + v
  · rcases hR r hr s hs u hu v hv he with ⟨hru, hsv⟩ | ⟨hrv, hsu⟩
    · subst u; subst v
      simp only [ite_true, and_self, Complex.mul_conj', ← Complex.ofReal_pow,
        Complex.ofReal_re, norm_mul, mul_pow]
      split_ifs <;> nlinarith [mul_nonneg (sq_nonneg ‖a r‖) (sq_nonneg ‖a s‖)]
    · subst v; subst u
      rw [if_pos he]
      have hc : (a r * a s) * conj (a s * a r) = (a r * a s) * conj (a r * a s) := by
        rw [mul_comm (a s) (a r)]
      rw [hc, Complex.mul_conj']
      simp only [← Complex.ofReal_pow, Complex.ofReal_re, norm_mul, mul_pow, and_self, ite_true]
      split_ifs <;> nlinarith [mul_nonneg (sq_nonneg ‖a r‖) (sq_nonneg ‖a s‖)]
  · rw [if_neg he]
    simp only [Complex.zero_re]
    split_ifs <;> positivity

/-- The genuine compact Sidon fourth-moment bound, with arbitrary complex
coefficients and probability Haar measure. -/
theorem compact_sidon_fourth_moment {R : Finset (Γ)} (hR : AdditiveSidon R)
    (a : Γ → ℂ) :
    (∫ j, ‖compactPolynomial χ R a j‖ ^ 4 ∂μ) ≤
      2 * (∑ r ∈ R, ‖a r‖ ^ 2) ^ 2 := by
  rw [integral_compactPolynomial_norm_four μ χ hχ]
  simp only [Finset.sum_product]
  calc
    _ ≤ ∑ r ∈ R, ∑ s ∈ R, ∑ u ∈ R, ∑ v ∈ R,
        ((if r = u ∧ s = v then ‖a r‖ ^ 2 * ‖a s‖ ^ 2 else 0) +
        (if r = v ∧ s = u then ‖a r‖ ^ 2 * ‖a s‖ ^ 2 else 0)) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro s hs
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      exact compact_sidon_fourth_term_le hR a hr hs hu hv
    _ = ∑ r ∈ R, ∑ s ∈ R, 2 * (‖a r‖ ^ 2 * ‖a s‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro s hs
      simp [Finset.sum_add_distrib, ite_and, hr, hs, two_mul]
    _ = 2 * (∑ r ∈ R, ‖a r‖ ^ 2) ^ 2 := by
      simp_rw [← Finset.mul_sum]
      simp_rw [← Finset.sum_mul]
      ring

omit hχ [DecidableEq Γ] [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [IsProbabilityMeasure μ] [Measure.IsMulLeftInvariant μ] in
/-- If zero is in a Sidon support, no two nonzero labels sum to zero. -/
theorem compact_sidon_zero_sum {R : Finset (Γ)} (hR : AdditiveSidon R) (hzero : 0 ∈ R)
    {r s : Γ} (hr : r ∈ R) (hs : s ∈ R) (h : r + s = 0) : r = 0 ∧ s = 0 := by
  have hp := hR r hr s hs 0 hzero 0 hzero (by simpa using h)
  simpa using hp

/-- Vanishing square moment for an actual Sidon polynomial whose constant
coefficient is zero. -/
theorem compact_sidon_square_moment_zero {R : Finset (Γ)} (hR : AdditiveSidon R)
    (hzero : 0 ∈ R) (a : Γ → ℂ) (ha0 : a 0 = 0) :
    (∫ j, compactPolynomial χ R a j ^ 2 ∂μ) = 0 := by
  simp_rw [compactPolynomial_sq]
  rw [integral_finsetSum (R ×ˢ R) (fun _ _ => compact_integrable (by fun_prop))]
  simp_rw [integral_const_mul, integral_compactCharacter μ χ hχ]
  apply Finset.sum_eq_zero
  intro p hp
  rcases Finset.mem_product.mp hp with ⟨hr, hs⟩
  by_cases he : p.1 + p.2 = 0
  · have hz := compact_sidon_zero_sum hR hzero hr hs he
    simp [hz.1, ha0]
  · simp [he]

/-- Delete the distinguished constant coefficient, keeping the same
concrete compact frequency support. -/
noncomputable def compactRemainderCoefficients (a : Γ → ℂ) (r : Γ) : ℂ :=
  if r = 0 then 0 else a r

omit hχ [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [IsProbabilityMeasure μ] [Measure.IsMulLeftInvariant μ] in
theorem compactPolynomial_split_constant {R : Finset (Γ)} (hzero : 0 ∈ R)
    (a : Γ → ℂ) (ha0 : a 0 = 1) (j : G) :
    compactPolynomial χ R a j =
      1 + compactPolynomial χ R (compactRemainderCoefficients a) j := by
  unfold compactPolynomial
  calc
    ∑ r ∈ R, a r * compactCharacter χ r j =
        ∑ r ∈ R, ((if r = 0 then 1 else 0) +
          compactRemainderCoefficients a r * compactCharacter χ r j) := by
      apply Finset.sum_congr rfl
      intro r hr
      by_cases h : r = 0
      · simp [h, ha0, compactRemainderCoefficients]
      · simp [h, compactRemainderCoefficients]
    _ = _ := by rw [Finset.sum_add_distrib]; simp [hzero]

omit hχ [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [IsProbabilityMeasure μ] [Measure.IsMulLeftInvariant μ] in
theorem compact_coefficient_second_split {R : Finset (Γ)} (hzero : 0 ∈ R)
    (a : Γ → ℂ) (ha0 : a 0 = 1) :
    (∑ r ∈ R, ‖a r‖ ^ 2) =
      1 + ∑ r ∈ R, ‖compactRemainderCoefficients a r‖ ^ 2 := by
  calc
    ∑ r ∈ R, ‖a r‖ ^ 2 =
        ∑ r ∈ R, ((if r = 0 then 1 else 0) + ‖compactRemainderCoefficients a r‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro r hr
      by_cases h : r = 0
      · simp [h, ha0, compactRemainderCoefficients]
      · simp [h, compactRemainderCoefficients]
    _ = _ := by rw [Finset.sum_add_distrib]; simp [hzero]

/-- The actual compact coefficient inequality in the normalization where
the largest coefficient occurs at zero and equals one. -/
theorem compact_sidon_normalized_twentieth {R : Finset (Γ)} (hR : AdditiveSidon R)
    (hzero : 0 ∈ R) (a : Γ → ℂ) (ha0 : a 0 = 1)
    (ha : ∀ r ∈ R, ‖a r‖ ≤ 1) :
    (∑ r ∈ R, ‖a r‖ ^ 20) ≤ (∫ j, ‖compactPolynomial χ R a j‖ ∂μ) ^ 20 := by
  let b := compactRemainderCoefficients a
  let t : ℝ := ∑ r ∈ R, ‖b r‖ ^ 2
  let g := compactPolynomial χ R b
  have hb0 : b 0 = 0 := by simp [b, compactRemainderCoefficients]
  have hg0 : (∫ j, g j ∂μ) = 0 := by
    dsimp [g]
    rw [integral_compactPolynomial μ χ hχ, if_pos hzero, hb0]
  have hg2 : (∫ j, g j ^ 2 ∂μ) = 0 :=
    compact_sidon_square_moment_zero μ χ hχ hR hzero b hb0
  have ht : (∫ j, ‖g j‖ ^ 2 ∂μ) = t :=
    integral_compactPolynomial_norm_sq μ χ hχ R b
  have hfour : (∫ j, ‖g j‖ ^ 4 ∂μ) ≤ 2 * t ^ 2 :=
    compact_sidon_fourth_moment μ χ hχ hR b
  have hsplit : (fun j => (1 : ℂ) + g j) = compactPolynomial χ R a := by
    funext j
    exact (compactPolynomial_split_constant χ hzero a ha0 j).symm
  have hsplitpoint (j : G) : (1 : ℂ) + g j = compactPolynomial χ R a j :=
    congrFun hsplit j
  have hmass : (∑ r ∈ R, ‖a r‖ ^ 2) = 1 + t :=
    compact_coefficient_second_split hzero a ha0
  have hwhole : (∫ j, ‖(1 : ℂ) + g j‖ ^ 4 ∂μ) ≤ 2 * (1 + t) ^ 2 := by
    simpa only [hsplitpoint, hmass] using compact_sidon_fourth_moment μ χ hχ hR a
  have hanalytic := sidon_twentieth_analytic
    (continuous_compactPolynomial χ R b) hg0 hg2 ht hfour hwhole
  change 1 + t ≤ (∫ j, ‖(1 : ℂ) + g j‖ ∂μ) ^ 20 at hanalytic
  have hsum : (∑ r ∈ R, ‖a r‖ ^ 20) ≤ 1 + t := by
    rw [← hmass]
    exact Finset.sum_le_sum fun r hr => coefficient_twentieth_le_square (norm_nonneg _) (ha r hr)
  simpa only [hsplitpoint] using hsum.trans hanalytic

omit hχ [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [IsProbabilityMeasure μ] [Measure.IsMulLeftInvariant μ] in
theorem compact_additiveSidon_image_sub {R : Finset (Γ)} (hR : AdditiveSidon R) (u : Γ) :
    AdditiveSidon (R.image fun r => r - u) := by
  intro a ha b hb c hc d hd he
  obtain ⟨ra, hra, hae⟩ := Finset.mem_image.mp ha
  obtain ⟨rb, hrb, hbe⟩ := Finset.mem_image.mp hb
  obtain ⟨rc, hrc, hce⟩ := Finset.mem_image.mp hc
  obtain ⟨rd, hrd, hde⟩ := Finset.mem_image.mp hd
  subst a; subst b; subst c; subst d
  have hsum : ra + rb = rc + rd := by
    exact sub_left_injective (by simpa only [sub_add_sub_comm] using he)
  rcases hR ra hra rb hrb rc hrc rd hrd hsum with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-- The full constant-one compact Sidon coefficient inequality, expressed
without a real twentieth root. There are no moment assumptions here. -/
theorem compact_sidon_twentieth {R : Finset (Γ)} (hR : AdditiveSidon R)
    (a : Γ → ℂ) :
    (∑ r ∈ R, ‖a r‖ ^ 20) ≤ (∫ j, ‖compactPolynomial χ R a j‖ ∂μ) ^ 20 := by
  classical
  by_cases hall : ∀ r ∈ R, a r = 0
  · have hz : (∑ r ∈ R, ‖a r‖ ^ 20) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      simp [hall r hr]
    rw [hz]
    positivity
  push Not at hall
  obtain ⟨r, hr, har⟩ := hall
  obtain ⟨u, hu, hmax⟩ := Finset.exists_max_image R (fun r => ‖a r‖) ⟨r, hr⟩
  have hau : a u ≠ 0 := by
    intro hz
    have hm := hmax r hr
    rw [hz, norm_zero] at hm
    exact har (norm_eq_zero.mp (le_antisymm hm (norm_nonneg _)))
  have hnormu : 0 < ‖a u‖ := norm_pos_iff.mpr hau
  let S := R.image fun r => r - u
  let b : Γ → ℂ := fun s => a (s + u) / a u
  have hS : AdditiveSidon S := compact_additiveSidon_image_sub hR u
  have hzero : (0 : Γ) ∈ S := by
    exact Finset.mem_image.mpr ⟨u, hu, sub_self u⟩
  have hb0 : b 0 = 1 := by simp [b, hau]
  have hb : ∀ s ∈ S, ‖b s‖ ≤ 1 := by
    intro s hs
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
    dsimp [b]
    rw [sub_add_cancel, norm_div]
    exact (div_le_one hnormu).2 (hmax r hr)
  have hnormalized := compact_sidon_normalized_twentieth μ χ hχ hS hzero b hb0 hb
  have hcoeff : (∑ s ∈ S, ‖b s‖ ^ 20) = (∑ r ∈ R, ‖a r‖ ^ 20) / ‖a u‖ ^ 20 := by
    dsimp [S, b]
    rw [Finset.sum_image (fun r _ s _ h => sub_left_injective h)]
    simp only [sub_add_cancel, norm_div, div_pow, Finset.sum_div]
  have hpoly (j : G) : compactPolynomial χ S b j =
      (compactCharacter χ (-u) j / a u) * compactPolynomial χ R a j := by
    unfold compactPolynomial
    dsimp [S, b]
    rw [Finset.sum_image (fun r _ s _ h => sub_left_injective h), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [sub_add_cancel]
    simp only [sub_eq_add_neg, compactCharacter_add]
    ring
  have hnorm (j : G) : ‖compactPolynomial χ S b j‖ = ‖compactPolynomial χ R a j‖ / ‖a u‖ := by
    rw [hpoly, norm_mul, norm_div, norm_compactCharacter]
    ring
  have hint : (∫ j, ‖compactPolynomial χ S b j‖ ∂μ) =
      (∫ j, ‖compactPolynomial χ R a j‖ ∂μ) / ‖a u‖ := by
    simp_rw [hnorm]
    exact integral_div _ _
  rw [hcoeff, hint, div_pow] at hnormalized
  exact (div_le_div_iff_of_pos_right (pow_pos hnormu 20)).1 hnormalized

/-- The original twentieth-root form, for any injectively labelled family
of genuine continuous characters on a compact abelian group. -/
theorem compact_sidon_constant_one {R : Finset Γ} (hR : AdditiveSidon R)
    (a : Γ → ℂ) :
    (∑ r ∈ R, ‖a r‖ ^ 20) ^ (1 / 20 : ℝ) ≤
      ∫ x, ‖compactPolynomial χ R a x‖ ∂μ := by
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg (fun r _ => pow_nonneg (norm_nonneg (a r)) 20))
    (compact_sidon_twentieth μ χ hχ hR a) (by norm_num : 0 ≤ (20 : ℝ)⁻¹)
  have he := Real.pow_rpow_inv_natCast
    (x := ∫ x, ‖compactPolynomial χ R a x‖ ∂μ)
    (integral_nonneg (fun x => norm_nonneg _)) (by decide : (20 : ℕ) ≠ 0)
  norm_num only [Nat.cast_ofNat] at he
  simp only [one_div] at he
  rw [he] at h
  simpa only [one_div] using h

omit hχ [AddCommGroup Γ] [DecidableEq Γ] in
/-- Manuscript Lemma 8.1 in its full stated generality: the labels are
elements of the dual of an arbitrary compact abelian group, and the
measure is normalized Haar. No moment identities are hypotheses. -/
theorem compact_dual_sidon_constant_one
    {R : Finset (Additive (PontryaginDual G))} (hR : AdditiveSidon R)
    (a : Additive (PontryaginDual G) → ℂ) :
    (∑ r ∈ R, ‖a r‖ ^ 20) ^ (1 / 20 : ℝ) ≤
      ∫ x, ‖∑ r ∈ R, a r * ((Additive.toMul r) x : ℂ)‖ ∂μ := by
  classical
  simpa only [compactPolynomial, compactCharacter, AddMonoidHom.id_apply] using
    compact_sidon_constant_one μ (AddMonoidHom.id (Additive (PontryaginDual G)))
      (fun _ _ h => h) hR a


end LittlewoodInverse
