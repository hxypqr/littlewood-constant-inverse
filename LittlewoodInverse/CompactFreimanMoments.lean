import LittlewoodInverse.CompactCharacters
import LittlewoodInverse.FreimanMoments

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LittlewoodInverse

def compactTuples {Γ : Type*} [DecidableEq Γ] (C : Finset Γ) (j : ℕ) :
    Finset (Fin j → Γ) := Fintype.piFinset (fun _ => C)

def compactRelationCount {Γ : Type*} [AddCommGroup Γ] [DecidableEq Γ]
    (C : Finset Γ) (j : ℕ) : ℕ :=
  ((compactTuples C j ×ˢ compactTuples C j).filter
    (fun p => (∑ i, p.1 i) = ∑ i, p.2 i)).card

section Compact
variable {Γ G : Type*} [AddCommGroup Γ] [DecidableEq Γ] [CommGroup G]
  [TopologicalSpace G]
  (χ : Γ →+ Additive (PontryaginDual G))

omit [DecidableEq Γ] in
theorem compactCharacter_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → Γ) (x : G) :
    compactCharacter χ (∑ i ∈ s, f i) x = ∏ i ∈ s, compactCharacter χ (f i) x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, compactCharacter_add]

theorem compactSet_polynomial_pow (C : Finset Γ) (j : ℕ) (x : G) :
    compactPolynomial χ C (fun _ => 1) x ^ j =
      ∑ p ∈ compactTuples C j, compactCharacter χ (∑ i, p i) x := by
  simp only [compactPolynomial, one_mul]
  rw [Finset.sum_pow']
  apply Finset.sum_congr rfl
  intro p _
  exact (compactCharacter_sum χ Finset.univ p x).symm

theorem compactSet_norm_even_pow_expansion (C : Finset Γ) (j : ℕ) (x : G) :
    (‖compactPolynomial χ C (fun _ => 1) x‖ ^ (2 * j) : ℂ) =
      ∑ p ∈ compactTuples C j ×ˢ compactTuples C j,
        compactCharacter χ ((∑ i, p.1 i) - ∑ i, p.2 i) x := by
  have hpow : (‖compactPolynomial χ C (fun _ => 1) x‖ ^ (2 * j) : ℂ) =
      compactPolynomial χ C (fun _ => 1) x ^ j *
        conj (compactPolynomial χ C (fun _ => 1) x ^ j) := by
    rw [Complex.mul_conj', norm_pow, Complex.ofReal_pow, ← pow_mul]
    rw [Nat.mul_comm 2 j]
  rw [hpow, compactSet_polynomial_pow]
  simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_product,
    sub_eq_add_neg, compactCharacter_add, compactCharacter_neg]

variable [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [IsProbabilityMeasure μ] [Measure.IsMulLeftInvariant μ]

/-- Every even moment of the actual compact-group Fourier polynomial
counts additive relations in its frequency set. -/
theorem integral_compactSet_even_moment (hχ : Function.Injective χ)
    (C : Finset Γ) (j : ℕ) :
    (∫ x, ‖compactPolynomial χ C (fun _ => 1) x‖ ^ (2 * j) ∂μ) =
      (compactRelationCount C j : ℝ) := by
  have h : (∫ x, (‖compactPolynomial χ C (fun _ => 1) x‖ ^ (2 * j) : ℂ) ∂μ) =
      (compactRelationCount C j : ℂ) := by
    simp_rw [compactSet_norm_even_pow_expansion]
    rw [integral_finsetSum _ (fun _ _ => compact_integrable (by fun_prop))]
    simp_rw [integral_compactCharacter μ χ hχ, sub_eq_zero]
    simp [compactRelationCount, Finset.sum_boole]
  exact_mod_cast h

end Compact

/-- Relation-count invariance for Freiman isomorphisms between arbitrary
abelian groups, with no order or torsion assumption. -/
theorem compact_freiman_relationCount {Γ Λ : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
    [DecidableEq Γ] [DecidableEq Λ] {h j : ℕ} {A : Finset Γ} {B : Set Λ} {f : Γ → Λ}
    (hf : IsAddFreimanIso h (A : Set Γ) B f) (hj : j ≤ h)
    {C : Finset Γ} (hCA : C ⊆ A) :
    compactRelationCount C j = compactRelationCount (C.image f) j := by
  classical
  unfold compactRelationCount
  apply Finset.card_nbij (fun p : (Fin j → Γ) × (Fin j → Γ) =>
    ((fun i => f (p.1 i)), fun i => f (p.2 i)))
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
      compactTuples, Fintype.mem_piFinset] at hp ⊢
    refine ⟨⟨fun i => Finset.mem_image_of_mem f (hp.1.1 i),
      fun i => Finset.mem_image_of_mem f (hp.1.2 i)⟩, ?_⟩
    exact (freiman_fin_sum_iff hf hj p.1 p.2
      (fun i => hCA (hp.1.1 i)) (fun i => hCA (hp.1.2 i))).mpr hp.2
  · intro p hp q hq heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
      compactTuples, Fintype.mem_piFinset] at hp hq
    apply Prod.ext
    · funext i
      exact hf.bijOn.injOn (hCA (hp.1.1 i)) (hCA (hq.1.1 i))
        (congrFun (congrArg Prod.fst heq) i)
    · funext i
      exact hf.bijOn.injOn (hCA (hp.1.2 i)) (hCA (hq.1.2 i))
        (congrFun (congrArg Prod.snd heq) i)
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
      compactTuples, Fintype.mem_piFinset] at hp
    have h1 : ∀ i, ∃ x ∈ C, f x = p.1 i := fun i => Finset.mem_image.mp (hp.1.1 i)
    have h2 : ∀ i, ∃ x ∈ C, f x = p.2 i := fun i => Finset.mem_image.mp (hp.1.2 i)
    choose u hu huf using h1
    choose v hv hvf using h2
    refine ⟨(u, v), ?_, ?_⟩
    · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        compactTuples, Fintype.mem_piFinset]
      refine ⟨⟨hu, hv⟩, ?_⟩
      apply (freiman_fin_sum_iff hf hj u v (fun i => hCA (hu i))
        (fun i => hCA (hv i))).mp
      simpa only [huf, hvf] using hp.2
    · exact Prod.ext (funext huf) (funext hvf)

/-- The moment bridge between two actual compact character models. -/
theorem compact_freiman_integral_even_moment
    {Γ Λ G H : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
    [DecidableEq Γ] [DecidableEq Λ]
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G]
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : Measure G) (ν : Measure H) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [Measure.IsMulLeftInvariant μ] [Measure.IsMulLeftInvariant ν]
    (χ : Γ →+ Additive (PontryaginDual G)) (ψ : Λ →+ Additive (PontryaginDual H))
    (hχ : Function.Injective χ) (hψ : Function.Injective ψ)
    {h j : ℕ} {A : Finset Γ} {B : Set Λ} {f : Γ → Λ}
    (hf : IsAddFreimanIso h (A : Set Γ) B f) (hj : j ≤ h)
    {C : Finset Γ} (hCA : C ⊆ A) :
    (∫ x, ‖compactPolynomial χ C (fun _ => 1) x‖ ^ (2 * j) ∂μ) =
      ∫ y, ‖compactPolynomial ψ (C.image f) (fun _ => 1) y‖ ^ (2 * j) ∂ν := by
  rw [integral_compactSet_even_moment χ μ hχ,
    integral_compactSet_even_moment ψ ν hψ, compact_freiman_relationCount hf hj hCA]

end LittlewoodInverse
