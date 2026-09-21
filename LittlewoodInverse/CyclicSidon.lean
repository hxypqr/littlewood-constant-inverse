import LittlewoodInverse.Geometry
import LittlewoodInverse.SidonAnalytic
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Topology.Instances.ZMod

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace LittlewoodInverse

variable (q : ℕ) [NeZero q]

/-- Probability counting measure on the actual cyclic residue group. -/
noncomputable def cyclicMeasure : Measure (ZMod q) := (q : ℝ≥0∞)⁻¹ • Measure.count

instance cyclicMeasure_isProbability : IsProbabilityMeasure (cyclicMeasure q) := by
  constructor
  simp only [cyclicMeasure, Measure.smul_apply, Measure.count_univ,
    ENat.card_eq_coe_fintype_card, ZMod.card, ENat.toENNReal_coe, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by simp [NeZero.ne q]) (by simp)

theorem integral_cyclicMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ZMod q → E) : (∫ j, f j ∂cyclicMeasure q) = (q : ℝ)⁻¹ • ∑ j, f j := by
  simp [cyclicMeasure, integral_smul_measure]

/-- The standard cyclic characters used in the fibre inequality. -/
noncomputable def cyclicCharacter (r j : ZMod q) : ℂ := ZMod.stdAddChar (r * j)

@[simp] theorem cyclicCharacter_zero (j : ZMod q) : cyclicCharacter q 0 j = 1 := by
  simp [cyclicCharacter]

@[simp] theorem norm_cyclicCharacter (r j : ZMod q) : ‖cyclicCharacter q r j‖ = 1 := by
  simp [cyclicCharacter, ZMod.stdAddChar_apply]

theorem cyclicCharacter_add (a b j : ZMod q) :
    cyclicCharacter q (a + b) j = cyclicCharacter q a j * cyclicCharacter q b j := by
  simp [cyclicCharacter, add_mul, AddChar.map_add_eq_mul]

theorem integral_cyclicCharacter (r : ZMod q) :
    (∫ j, cyclicCharacter q r j ∂cyclicMeasure q) = if r = 0 then 1 else 0 := by
  rw [integral_cyclicMeasure]
  by_cases hr : r = 0
  · simp [hr, ZMod.card, NeZero.ne q]
  · have hsum : ∑ j : ZMod q, ZMod.stdAddChar (r * j) = 0 :=
      AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q hr)
    simp [cyclicCharacter, hsum, hr]

theorem cyclic_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ZMod q → E) : Integrable f (cyclicMeasure q) :=
  (continuous_of_discreteTopology : Continuous f).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem cyclicCharacter_neg (r j : ZMod q) :
    cyclicCharacter q (-r) j = conj (cyclicCharacter q r j) := by
  simp [cyclicCharacter, ZMod.stdAddChar_apply, neg_mul, AddChar.map_neg_eq_inv,
    ← Circle.coe_inv, Circle.coe_inv_eq_conj]

theorem integral_cyclicCharacter_mul_conj (r s : ZMod q) :
    (∫ j, cyclicCharacter q r j * conj (cyclicCharacter q s j) ∂cyclicMeasure q) =
      if r = s then 1 else 0 := by
  simp_rw [← cyclicCharacter_neg, ← cyclicCharacter_add]
  simpa only [add_neg_eq_zero] using integral_cyclicCharacter q (r + -s)

noncomputable def cyclicPolynomial (R : Finset (ZMod q)) (a : ZMod q → ℂ) (j : ZMod q) : ℂ :=
  ∑ r ∈ R, a r * cyclicCharacter q r j

theorem integral_cyclicPolynomial (R : Finset (ZMod q)) (a : ZMod q → ℂ) :
    (∫ j, cyclicPolynomial q R a j ∂cyclicMeasure q) = if 0 ∈ R then a 0 else 0 := by
  unfold cyclicPolynomial
  rw [integral_finsetSum R (fun _ _ => cyclic_integrable q _)]
  simp_rw [integral_const_mul, integral_cyclicCharacter]
  simp [Finset.sum_ite_eq']

theorem integral_cyclic_term_pair (r s : ZMod q) (a b : ℂ) :
    (∫ j, (a * cyclicCharacter q r j) * conj (b * cyclicCharacter q s j) ∂cyclicMeasure q) =
      if r = s then a * conj b else 0 := by
  have hfun : (fun j => (a * cyclicCharacter q r j) * conj (b * cyclicCharacter q s j)) =
      (fun j => (a * conj b) * (cyclicCharacter q r j * conj (cyclicCharacter q s j))) := by
    funext j
    simp only [map_mul]
    ring
  rw [hfun, integral_const_mul, integral_cyclicCharacter_mul_conj]
  split_ifs <;> simp

theorem integral_cyclicPolynomial_pair (R S : Finset (ZMod q)) (a b : ZMod q → ℂ) :
    (∫ j, cyclicPolynomial q R a j * conj (cyclicPolynomial q S b j) ∂cyclicMeasure q) =
      ∑ r ∈ R ∩ S, a r * conj (b r) := by
  unfold cyclicPolynomial
  simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum R (fun _ _ => cyclic_integrable q _)]
  simp_rw [integral_finsetSum S (fun _ _ => cyclic_integrable q _), integral_cyclic_term_pair]
  simp

theorem integral_cyclicPolynomial_norm_sq (R : Finset (ZMod q)) (a : ZMod q → ℂ) :
    (∫ j, ‖cyclicPolynomial q R a j‖ ^ 2 ∂cyclicMeasure q) = ∑ r ∈ R, ‖a r‖ ^ 2 := by
  have h := integral_cyclicPolynomial_pair q R R a a
  simp only [Finset.inter_self, Complex.mul_conj', ← Complex.ofReal_pow] at h
  exact_mod_cast h

/-- Orthogonality with an arbitrary finite indexing set, allowing repeated
frequencies. This is needed for the pair-sum expansion of the fourth moment. -/
theorem integral_cyclic_indexed_norm_sq {ι : Type*} (I : Finset ι)
    (n : ι → ZMod q) (a : ι → ℂ) :
    (∫ j, ‖∑ r ∈ I, a r * cyclicCharacter q (n r) j‖ ^ 2 ∂cyclicMeasure q) =
      (∑ r ∈ I, ∑ s ∈ I, if n r = n s then a r * conj (a s) else 0).re := by
  classical
  have h : (∫ j, (∑ r ∈ I, a r * cyclicCharacter q (n r) j) *
      conj (∑ s ∈ I, a s * cyclicCharacter q (n s) j) ∂cyclicMeasure q) =
      ∑ r ∈ I, ∑ s ∈ I, if n r = n s then a r * conj (a s) else 0 := by
    simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum]
    rw [integral_finsetSum I (fun _ _ => cyclic_integrable q _)]
    simp_rw [integral_finsetSum I (fun _ _ => cyclic_integrable q _), integral_cyclic_term_pair]
  simp only [Complex.mul_conj', ← Complex.ofReal_pow, integral_complex_ofReal] at h
  simpa only [Complex.ofReal_re] using congrArg Complex.re h

theorem cyclicPolynomial_sq (R : Finset (ZMod q)) (a : ZMod q → ℂ) (j : ZMod q) :
    cyclicPolynomial q R a j ^ 2 =
      ∑ p ∈ R ×ˢ R, (a p.1 * a p.2) * cyclicCharacter q (p.1 + p.2) j := by
  simp only [cyclicPolynomial, pow_two, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_product, cyclicCharacter_add]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  ring

/-- Exact fourth-moment expansion of an actual finite cyclic polynomial. -/
theorem integral_cyclicPolynomial_norm_four (R : Finset (ZMod q)) (a : ZMod q → ℂ) :
    (∫ j, ‖cyclicPolynomial q R a j‖ ^ 4 ∂cyclicMeasure q) =
      ∑ p ∈ R ×ˢ R, ∑ v ∈ R ×ˢ R,
        (if p.1 + p.2 = v.1 + v.2 then
          (a p.1 * a p.2) * conj (a v.1 * a v.2) else 0).re := by
  have h := integral_cyclic_indexed_norm_sq q (R ×ˢ R)
    (fun p => p.1 + p.2) (fun p => a p.1 * a p.2)
  simp only [Complex.re_sum] at h
  rw [← h]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun j => by
    change ‖cyclicPolynomial q R a j‖ ^ 4 =
      ‖∑ r ∈ R ×ˢ R, a r.1 * a r.2 * cyclicCharacter q (r.1 + r.2) j‖ ^ 2
    rw [← cyclicPolynomial_sq]
    simp [norm_pow, ← pow_mul]

omit [NeZero q] in
/-- A Sidon relation contributes only one of the two trivial pairings. -/
theorem sidon_fourth_term_le {R : Finset (ZMod q)} (hR : AdditiveSidon R)
    (a : ZMod q → ℂ) {r s u v : ZMod q}
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

/-- The genuine cyclic Sidon fourth-moment bound, with arbitrary complex
coefficients and normalized counting measure. -/
theorem cyclic_sidon_fourth_moment {R : Finset (ZMod q)} (hR : AdditiveSidon R)
    (a : ZMod q → ℂ) :
    (∫ j, ‖cyclicPolynomial q R a j‖ ^ 4 ∂cyclicMeasure q) ≤
      2 * (∑ r ∈ R, ‖a r‖ ^ 2) ^ 2 := by
  rw [integral_cyclicPolynomial_norm_four]
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
      exact sidon_fourth_term_le q hR a hr hs hu hv
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

omit [NeZero q] in
/-- If zero is in a Sidon support, no two nonzero labels sum to zero. -/
theorem sidon_zero_sum {R : Finset (ZMod q)} (hR : AdditiveSidon R) (hzero : 0 ∈ R)
    {r s : ZMod q} (hr : r ∈ R) (hs : s ∈ R) (h : r + s = 0) : r = 0 ∧ s = 0 := by
  have hp := hR r hr s hs 0 hzero 0 hzero (by simpa using h)
  simpa using hp

/-- Vanishing square moment for an actual Sidon polynomial whose constant
coefficient is zero. -/
theorem cyclic_sidon_square_moment_zero {R : Finset (ZMod q)} (hR : AdditiveSidon R)
    (hzero : 0 ∈ R) (a : ZMod q → ℂ) (ha0 : a 0 = 0) :
    (∫ j, cyclicPolynomial q R a j ^ 2 ∂cyclicMeasure q) = 0 := by
  simp_rw [cyclicPolynomial_sq]
  rw [integral_finsetSum (R ×ˢ R) (fun _ _ => cyclic_integrable q _)]
  simp_rw [integral_const_mul, integral_cyclicCharacter]
  apply Finset.sum_eq_zero
  intro p hp
  rcases Finset.mem_product.mp hp with ⟨hr, hs⟩
  by_cases he : p.1 + p.2 = 0
  · have hz := sidon_zero_sum q hR hzero hr hs he
    simp [hz.1, ha0]
  · simp [he]

/-- Delete the distinguished constant coefficient, keeping the same
concrete cyclic frequency support. -/
noncomputable def cyclicRemainderCoefficients (a : ZMod q → ℂ) (r : ZMod q) : ℂ :=
  if r = 0 then 0 else a r

theorem cyclicPolynomial_split_constant {R : Finset (ZMod q)} (hzero : 0 ∈ R)
    (a : ZMod q → ℂ) (ha0 : a 0 = 1) (j : ZMod q) :
    cyclicPolynomial q R a j =
      1 + cyclicPolynomial q R (cyclicRemainderCoefficients q a) j := by
  unfold cyclicPolynomial
  calc
    ∑ r ∈ R, a r * cyclicCharacter q r j =
        ∑ r ∈ R, ((if r = 0 then 1 else 0) +
          cyclicRemainderCoefficients q a r * cyclicCharacter q r j) := by
      apply Finset.sum_congr rfl
      intro r hr
      by_cases h : r = 0
      · simp [h, ha0, cyclicRemainderCoefficients]
      · simp [h, cyclicRemainderCoefficients]
    _ = _ := by rw [Finset.sum_add_distrib]; simp [hzero]

omit [NeZero q] in
theorem cyclic_coefficient_second_split {R : Finset (ZMod q)} (hzero : 0 ∈ R)
    (a : ZMod q → ℂ) (ha0 : a 0 = 1) :
    (∑ r ∈ R, ‖a r‖ ^ 2) =
      1 + ∑ r ∈ R, ‖cyclicRemainderCoefficients q a r‖ ^ 2 := by
  calc
    ∑ r ∈ R, ‖a r‖ ^ 2 =
        ∑ r ∈ R, ((if r = 0 then 1 else 0) + ‖cyclicRemainderCoefficients q a r‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro r hr
      by_cases h : r = 0
      · simp [h, ha0, cyclicRemainderCoefficients]
      · simp [h, cyclicRemainderCoefficients]
    _ = _ := by rw [Finset.sum_add_distrib]; simp [hzero]

/-- The actual cyclic coefficient inequality in the normalization where
the largest coefficient occurs at zero and equals one. -/
theorem cyclic_sidon_normalized_twentieth {R : Finset (ZMod q)} (hR : AdditiveSidon R)
    (hzero : 0 ∈ R) (a : ZMod q → ℂ) (ha0 : a 0 = 1)
    (ha : ∀ r ∈ R, ‖a r‖ ≤ 1) :
    (∑ r ∈ R, ‖a r‖ ^ 20) ≤ (∫ j, ‖cyclicPolynomial q R a j‖ ∂cyclicMeasure q) ^ 20 := by
  let b := cyclicRemainderCoefficients q a
  let t : ℝ := ∑ r ∈ R, ‖b r‖ ^ 2
  let g := cyclicPolynomial q R b
  have hb0 : b 0 = 0 := by simp [b, cyclicRemainderCoefficients]
  have hg0 : (∫ j, g j ∂cyclicMeasure q) = 0 := by
    dsimp [g]
    rw [integral_cyclicPolynomial, if_pos hzero, hb0]
  have hg2 : (∫ j, g j ^ 2 ∂cyclicMeasure q) = 0 :=
    cyclic_sidon_square_moment_zero q hR hzero b hb0
  have ht : (∫ j, ‖g j‖ ^ 2 ∂cyclicMeasure q) = t :=
    integral_cyclicPolynomial_norm_sq q R b
  have hfour : (∫ j, ‖g j‖ ^ 4 ∂cyclicMeasure q) ≤ 2 * t ^ 2 :=
    cyclic_sidon_fourth_moment q hR b
  have hsplit : (fun j => (1 : ℂ) + g j) = cyclicPolynomial q R a := by
    funext j
    exact (cyclicPolynomial_split_constant q hzero a ha0 j).symm
  have hsplitpoint (j : ZMod q) : (1 : ℂ) + g j = cyclicPolynomial q R a j :=
    congrFun hsplit j
  have hmass : (∑ r ∈ R, ‖a r‖ ^ 2) = 1 + t :=
    cyclic_coefficient_second_split q hzero a ha0
  have hwhole : (∫ j, ‖(1 : ℂ) + g j‖ ^ 4 ∂cyclicMeasure q) ≤ 2 * (1 + t) ^ 2 := by
    simpa only [hsplitpoint, hmass] using cyclic_sidon_fourth_moment q hR a
  have hanalytic := sidon_twentieth_analytic
    (continuous_of_discreteTopology : Continuous g) hg0 hg2 ht hfour hwhole
  have hsum : (∑ r ∈ R, ‖a r‖ ^ 20) ≤ 1 + t := by
    rw [← hmass]
    exact Finset.sum_le_sum fun r hr => coefficient_twentieth_le_square (norm_nonneg _) (ha r hr)
  simpa only [hsplitpoint] using hsum.trans hanalytic

omit [NeZero q] in
theorem additiveSidon_image_sub {R : Finset (ZMod q)} (hR : AdditiveSidon R) (u : ZMod q) :
    AdditiveSidon (R.image fun r => r - u) := by
  intro a ha b hb c hc d hd he
  obtain ⟨ra, hra, hae⟩ := Finset.mem_image.mp ha
  obtain ⟨rb, hrb, hbe⟩ := Finset.mem_image.mp hb
  obtain ⟨rc, hrc, hce⟩ := Finset.mem_image.mp hc
  obtain ⟨rd, hrd, hde⟩ := Finset.mem_image.mp hd
  subst a; subst b; subst c; subst d
  have hsum : ra + rb = rc + rd := by linear_combination he
  rcases hR ra hra rb hrb rc hrc rd hrd hsum with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-- The full constant-one cyclic Sidon coefficient inequality, expressed
without a real twentieth root. There are no moment assumptions here. -/
theorem cyclic_sidon_twentieth {R : Finset (ZMod q)} (hR : AdditiveSidon R)
    (a : ZMod q → ℂ) :
    (∑ r ∈ R, ‖a r‖ ^ 20) ≤ (∫ j, ‖cyclicPolynomial q R a j‖ ∂cyclicMeasure q) ^ 20 := by
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
  let b : ZMod q → ℂ := fun s => a (s + u) / a u
  have hS : AdditiveSidon S := additiveSidon_image_sub q hR u
  have hzero : (0 : ZMod q) ∈ S := by
    exact Finset.mem_image.mpr ⟨u, hu, sub_self u⟩
  have hb0 : b 0 = 1 := by simp [b, hau]
  have hb : ∀ s ∈ S, ‖b s‖ ≤ 1 := by
    intro s hs
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
    dsimp [b]
    rw [sub_add_cancel, norm_div]
    exact (div_le_one hnormu).2 (hmax r hr)
  have hnormalized := cyclic_sidon_normalized_twentieth q hS hzero b hb0 hb
  have hcoeff : (∑ s ∈ S, ‖b s‖ ^ 20) = (∑ r ∈ R, ‖a r‖ ^ 20) / ‖a u‖ ^ 20 := by
    dsimp [S, b]
    rw [Finset.sum_image (fun r _ s _ h => sub_left_injective h)]
    simp only [sub_add_cancel, norm_div, div_pow, Finset.sum_div]
  have hpoly (j : ZMod q) : cyclicPolynomial q S b j =
      (cyclicCharacter q (-u) j / a u) * cyclicPolynomial q R a j := by
    unfold cyclicPolynomial
    dsimp [S, b]
    rw [Finset.sum_image (fun r _ s _ h => sub_left_injective h), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [sub_add_cancel]
    simp only [sub_eq_add_neg, cyclicCharacter_add]
    ring
  have hnorm (j : ZMod q) : ‖cyclicPolynomial q S b j‖ = ‖cyclicPolynomial q R a j‖ / ‖a u‖ := by
    rw [hpoly, norm_mul, norm_div, norm_cyclicCharacter]
    ring
  have hint : (∫ j, ‖cyclicPolynomial q S b j‖ ∂cyclicMeasure q) =
      (∫ j, ‖cyclicPolynomial q R a j‖ ∂cyclicMeasure q) / ‖a u‖ := by
    simp_rw [hnorm]
    exact integral_div _ _
  rw [hcoeff, hint, div_pow] at hnormalized
  exact (div_le_div_iff_of_pos_right (pow_pos hnormu 20)).1 hnormalized

end LittlewoodInverse
