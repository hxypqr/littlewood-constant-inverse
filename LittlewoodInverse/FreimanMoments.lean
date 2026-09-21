import LittlewoodInverse.MomentCounting
import LittlewoodInverse.FreimanFinite

open scoped BigOperators
open MeasureTheory

namespace LittlewoodInverse

theorem freiman_fin_sum_iff {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    {h j : ℕ} {A : Set G} {B : Set H} {f : G → H}
    (hf : IsAddFreimanIso h A B f) (hj : j ≤ h)
    (u v : Fin j → G) (hu : ∀ i, u i ∈ A) (hv : ∀ i, v i ∈ A) :
    (∑ i, f (u i)) = (∑ i, f (v i)) ↔ (∑ i, u i) = ∑ i, v i := by
  have hf' := hf.mono (hmn := hj)
  have hs := hf'.map_sum_eq_map_sum
    (s := Finset.univ.val.map u) (t := Finset.univ.val.map v)
    (by simpa using hu) (by simpa using hv) (by simp) (by simp)
  simpa [Multiset.map_map, Function.comp_def, List.sum_ofFn] using hs

/-- Freiman isomorphisms preserve each actual relation count up to their order. -/
theorem freiman_relationCount {h j : ℕ} {A : Finset ℤ} {B : Set ℤ} {f : ℤ → ℤ}
    (hf : IsAddFreimanIso h (A : Set ℤ) B f) (hj : j ≤ h)
    {C : Finset ℤ} (hCA : C ⊆ A) :
    MomentCounting.relationCount C j = MomentCounting.relationCount (C.image f) j := by
  classical
  unfold MomentCounting.relationCount
  apply Finset.card_nbij (fun p : (Fin j → ℤ) × (Fin j → ℤ) =>
    ((fun i => f (p.1 i)), fun i => f (p.2 i)))
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
      MomentCounting.tuples, Fintype.mem_piFinset] at hp ⊢
    refine ⟨⟨fun i => Finset.mem_image_of_mem f (hp.1.1 i),
      fun i => Finset.mem_image_of_mem f (hp.1.2 i)⟩, ?_⟩
    exact (freiman_fin_sum_iff hf hj p.1 p.2
      (fun i => hCA (hp.1.1 i)) (fun i => hCA (hp.1.2 i))).mpr hp.2
  · intro p hp q hq heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
      MomentCounting.tuples, Fintype.mem_piFinset] at hp hq
    apply Prod.ext
    · funext i
      exact hf.bijOn.injOn (hCA (hp.1.1 i)) (hCA (hq.1.1 i))
        (congrFun (congrArg Prod.fst heq) i)
    · funext i
      exact hf.bijOn.injOn (hCA (hp.1.2 i)) (hCA (hq.1.2 i))
        (congrFun (congrArg Prod.snd heq) i)
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
      MomentCounting.tuples, Fintype.mem_piFinset] at hp
    have h1 : ∀ i, ∃ x ∈ C, f x = p.1 i := fun i => Finset.mem_image.mp (hp.1.1 i)
    have h2 : ∀ i, ∃ x ∈ C, f x = p.2 i := fun i => Finset.mem_image.mp (hp.1.2 i)
    choose u hu huf using h1
    choose v hv hvf using h2
    refine ⟨(u, v), ?_, ?_⟩
    · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        MomentCounting.tuples, Fintype.mem_piFinset]
      refine ⟨⟨hu, hv⟩, ?_⟩
      apply (freiman_fin_sum_iff hf hj u v (fun i => hCA (hu i))
        (fun i => hCA (hv i))).mp
      simpa only [huf, hvf] using hp.2
    · exact Prod.ext (funext huf) (funext hvf)

/-- The moment identities in the proof of Lemma 9.2, for every subset at once. -/
theorem freiman_integral_even_moment {h j : ℕ} {A : Finset ℤ} {B : Set ℤ} {f : ℤ → ℤ}
    (hf : IsAddFreimanIso h (A : Set ℤ) B f) (hj : j ≤ h)
    {C : Finset ℤ} (hCA : C ⊆ A) :
    (∫ t, ‖fourierPolynomial C t‖ ^ (2 * j) ∂circleMeasure) =
      ∫ t, ‖fourierPolynomial (C.image f) t‖ ^ (2 * j) ∂circleMeasure := by
  simp only [MomentCounting.integral_even_moment, freiman_relationCount hf hj hCA]

end LittlewoodInverse
