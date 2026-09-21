import LittlewoodInverse.Geometry
import LittlewoodInverse.SidonAnalytic
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.MeasureTheory.Group.Integral

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LittlewoodInverse

variable {Γ G : Type*} [AddCommGroup Γ] [CommGroup G]
  [TopologicalSpace G]

/-- An actual family of continuous unitary characters, with additive labels. -/
noncomputable def compactCharacter (χ : Γ →+ Additive (PontryaginDual G))
    (r : Γ) (x : G) : ℂ := ((Additive.toMul (χ r)) x : ℂ)

@[simp] theorem compactCharacter_zero (χ : Γ →+ Additive (PontryaginDual G)) (x : G) :
    compactCharacter χ 0 x = 1 := by simp [compactCharacter]

@[simp] theorem norm_compactCharacter (χ : Γ →+ Additive (PontryaginDual G)) (r : Γ) (x : G) :
    ‖compactCharacter χ r x‖ = 1 := by simp [compactCharacter]

@[fun_prop] theorem continuous_compactCharacter
    (χ : Γ →+ Additive (PontryaginDual G)) (r : Γ) : Continuous (compactCharacter χ r) := by
  exact continuous_subtype_val.comp (map_continuous (Additive.toMul (χ r)))

theorem compactCharacter_add (χ : Γ →+ Additive (PontryaginDual G)) (r s : Γ) (x : G) :
    compactCharacter χ (r + s) x = compactCharacter χ r x * compactCharacter χ s x := by
  simp only [compactCharacter, map_add]
  rfl

theorem compactCharacter_neg (χ : Γ →+ Additive (PontryaginDual G)) (r : Γ) (x : G) :
    compactCharacter χ (-r) x = conj (compactCharacter χ r x) := by
  simp only [compactCharacter, map_neg]
  change (((Additive.toMul (χ r)) x : _root_.Circle)⁻¹ : ℂ) = _
  exact _root_.Circle.coe_inv_eq_conj _

theorem compactCharacter_mul (χ : Γ →+ Additive (PontryaginDual G)) (r : Γ) (x y : G) :
    compactCharacter χ r (x * y) = compactCharacter χ r x * compactCharacter χ r y := by
  simp [compactCharacter, map_mul]

variable [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

omit [CommGroup G] [IsTopologicalGroup G] in
theorem compact_integrable {μ : Measure G} [IsProbabilityMeasure μ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : G → E} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

variable (μ : Measure G) [IsProbabilityMeasure μ] [Measure.IsMulLeftInvariant μ]
  [DecidableEq Γ] (χ : Γ →+ Additive (PontryaginDual G)) (hχ : Function.Injective χ)

include hχ

omit [CompactSpace G] in
/-- Haar orthogonality follows from translating the actual character;
it is not an assumption about the moments of a polynomial. -/
theorem integral_compactCharacter (r : Γ) :
    (∫ x, compactCharacter χ r x ∂μ) = if r = 0 then 1 else 0 := by
  classical
  by_cases hr : r = 0
  · simp [hr]
  · rw [if_neg hr]
    have hx : ∃ x : G, compactCharacter χ r x ≠ 1 := by
      by_contra hn
      push Not at hn
      have he : χ r = χ 0 := by
        apply Additive.toMul.injective
        apply PontryaginDual.ext
        intro x
        apply Subtype.ext
        simpa [compactCharacter] using hn x
      exact hr (hχ he)
    obtain ⟨x, hx⟩ := hx
    have hi := integral_mul_left_eq_self (μ := μ) (compactCharacter χ r) x
    simp_rw [compactCharacter_mul, integral_const_mul] at hi
    have hz : (compactCharacter χ r x - 1) * (∫ y, compactCharacter χ r y ∂μ) = 0 := by
      linear_combination hi
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hx)

omit [CompactSpace G] in
theorem integral_compactCharacter_mul_conj (r s : Γ) :
    (∫ x, compactCharacter χ r x * conj (compactCharacter χ s x) ∂μ) =
      if r = s then 1 else 0 := by
  simp_rw [← compactCharacter_neg, ← compactCharacter_add]
  simpa only [add_neg_eq_zero] using integral_compactCharacter μ χ hχ (r + -s)

noncomputable def compactPolynomial (R : Finset (Γ)) (a : Γ → ℂ) (j : G) : ℂ :=
  ∑ r ∈ R, a r * compactCharacter χ r j

omit hχ [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [DecidableEq Γ] [IsProbabilityMeasure μ] [Measure.IsMulLeftInvariant μ] in
@[fun_prop] theorem continuous_compactPolynomial (R : Finset Γ) (a : Γ → ℂ) :
    Continuous (compactPolynomial χ R a) := by unfold compactPolynomial; fun_prop

theorem integral_compactPolynomial (R : Finset (Γ)) (a : Γ → ℂ) :
    (∫ j, compactPolynomial χ R a j ∂μ) = if 0 ∈ R then a 0 else 0 := by
  unfold compactPolynomial
  rw [integral_finsetSum R (fun _ _ => compact_integrable (by fun_prop))]
  simp_rw [integral_const_mul, integral_compactCharacter μ χ hχ]
  simp [Finset.sum_ite_eq']

omit [CompactSpace G] in
theorem integral_compact_term_pair (r s : Γ) (a b : ℂ) :
    (∫ j, (a * compactCharacter χ r j) * conj (b * compactCharacter χ s j) ∂μ) =
      if r = s then a * conj b else 0 := by
  have hfun : (fun j => (a * compactCharacter χ r j) * conj (b * compactCharacter χ s j)) =
      (fun j => (a * conj b) * (compactCharacter χ r j * conj (compactCharacter χ s j))) := by
    funext j
    simp only [map_mul]
    ring
  rw [hfun, integral_const_mul, integral_compactCharacter_mul_conj μ χ hχ]
  split_ifs <;> simp

theorem integral_compactPolynomial_pair (R S : Finset (Γ)) (a b : Γ → ℂ) :
    (∫ j, compactPolynomial χ R a j * conj (compactPolynomial χ S b j) ∂μ) =
      ∑ r ∈ R ∩ S, a r * conj (b r) := by
  have hinner (r : Γ) : (∫ j, ∑ s ∈ S,
      (a r * compactCharacter χ r j) * conj (b s * compactCharacter χ s j) ∂μ) =
      ∑ s ∈ S, if r = s then a r * conj (b s) else 0 := by
    rw [integral_finsetSum S (fun _ _ => compact_integrable (by fun_prop))]
    simp_rw [integral_compact_term_pair μ χ hχ]
  unfold compactPolynomial
  simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum R (fun _ _ => compact_integrable (by fun_prop))]
  simp_rw [hinner]
  simp

theorem integral_compactPolynomial_norm_sq (R : Finset (Γ)) (a : Γ → ℂ) :
    (∫ j, ‖compactPolynomial χ R a j‖ ^ 2 ∂μ) = ∑ r ∈ R, ‖a r‖ ^ 2 := by
  have h := integral_compactPolynomial_pair μ χ hχ R R a a
  simp only [Finset.inter_self, Complex.mul_conj', ← Complex.ofReal_pow] at h
  exact_mod_cast h

/-- Orthogonality with an arbitrary finite indexing set, allowing repeated
frequencies. This is needed for the pair-sum expansion of the fourth moment. -/
theorem integral_compact_indexed_norm_sq {ι : Type*} (I : Finset ι)
    (n : ι → Γ) (a : ι → ℂ) :
    (∫ j, ‖∑ r ∈ I, a r * compactCharacter χ (n r) j‖ ^ 2 ∂μ) =
      (∑ r ∈ I, ∑ s ∈ I, if n r = n s then a r * conj (a s) else 0).re := by
  classical
  have hinner (r : ι) : (∫ j, ∑ s ∈ I,
      (a r * compactCharacter χ (n r) j) * conj (a s * compactCharacter χ (n s) j) ∂μ) =
      ∑ s ∈ I, if n r = n s then a r * conj (a s) else 0 := by
    rw [integral_finsetSum I (fun _ _ => compact_integrable (by fun_prop))]
    simp_rw [integral_compact_term_pair μ χ hχ]
  have h : (∫ j, (∑ r ∈ I, a r * compactCharacter χ (n r) j) *
      conj (∑ s ∈ I, a s * compactCharacter χ (n s) j) ∂μ) =
      ∑ r ∈ I, ∑ s ∈ I, if n r = n s then a r * conj (a s) else 0 := by
    simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum]
    rw [integral_finsetSum I (fun _ _ => compact_integrable (by fun_prop))]
    simp_rw [hinner]
  simp only [Complex.mul_conj', ← Complex.ofReal_pow, integral_complex_ofReal] at h
  simpa only [Complex.ofReal_re] using congrArg Complex.re h

omit hχ [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [DecidableEq Γ] [IsProbabilityMeasure μ] [Measure.IsMulLeftInvariant μ] in
theorem compactPolynomial_sq (R : Finset (Γ)) (a : Γ → ℂ) (j : G) :
    compactPolynomial χ R a j ^ 2 =
      ∑ p ∈ R ×ˢ R, (a p.1 * a p.2) * compactCharacter χ (p.1 + p.2) j := by
  simp only [compactPolynomial, pow_two, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_product, compactCharacter_add]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  ring

/-- Exact fourth-moment expansion of an actual finite character polynomial. -/
theorem integral_compactPolynomial_norm_four (R : Finset (Γ)) (a : Γ → ℂ) :
    (∫ j, ‖compactPolynomial χ R a j‖ ^ 4 ∂μ) =
      ∑ p ∈ R ×ˢ R, ∑ v ∈ R ×ˢ R,
        (if p.1 + p.2 = v.1 + v.2 then
          (a p.1 * a p.2) * conj (a v.1 * a v.2) else 0).re := by
  have h := integral_compact_indexed_norm_sq μ χ hχ (R ×ˢ R)
    (fun p => p.1 + p.2) (fun p => a p.1 * a p.2)
  simp only [Complex.re_sum] at h
  rw [← h]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun j => by
    change ‖compactPolynomial χ R a j‖ ^ 4 =
      ‖∑ r ∈ R ×ˢ R, a r.1 * a r.2 * compactCharacter χ (r.1 + r.2) j‖ ^ 2
    rw [← compactPolynomial_sq]
    simp [norm_pow, ← pow_mul]


end LittlewoodInverse
