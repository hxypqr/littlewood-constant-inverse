import LittlewoodInverse.CompactTransport
import LittlewoodInverse.CompactHereditary
import LittlewoodInverse.FreimanFinite

open scoped Pointwise

namespace LittlewoodInverse

section Pair

variable {Γ Λ : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [TopologicalSpace Γ] [DiscreteTopology Γ] [TopologicalSpace Λ] [DiscreteTopology Λ]
  [DecidableEq Γ] [DecidableEq Λ]

/-- Lemma 9.2 for arbitrary discrete abelian groups and their actual
compact Pontryagin duals, with canonical probability Haar measures. -/
theorem discrete_freiman_norm_transport {h : ℕ} {A : Finset Γ} {B : Set Λ}
    {f : Γ → Λ} (hf : IsAddFreimanIso h (A : Set Γ) B f)
    {C : Finset Γ} (hCA : C ⊆ A) :
    |discreteLittlewoodNorm Γ C - discreteLittlewoodNorm Λ (C.image f)| ≤
      4 * (C.card : ℝ) / (Real.pi * (2 * (h : ℝ) + 1)) := by
  letI : MeasurableSpace (PontryaginDual (Multiplicative Γ)) := borel _
  letI : BorelSpace (PontryaginDual (Multiplicative Γ)) := ⟨rfl⟩
  letI : MeasurableSpace (PontryaginDual (Multiplicative Λ)) := borel _
  letI : BorelSpace (PontryaginDual (Multiplicative Λ)) := ⟨rfl⟩
  exact compact_freiman_norm_transport (discreteDualMeasure Γ) (discreteDualMeasure Λ)
    (discreteEvaluation Γ) (discreteEvaluation Λ) (discreteEvaluation_injective Γ)
    (discreteEvaluation_injective Λ) hf hCA

/-- The norm, energy, and doubling conclusions of the full cross-group
transport lemma collected in a single statement. -/
theorem discrete_freiman_transport {h : ℕ} (hh : 2 ≤ h)
    {A : Finset Γ} {B : Set Λ} {f : Γ → Λ}
    (hf : IsAddFreimanIso h (A : Set Γ) B f) {C : Finset Γ} (hCA : C ⊆ A) :
    |discreteLittlewoodNorm Γ C - discreteLittlewoodNorm Λ (C.image f)| ≤
      4 * (C.card : ℝ) / (Real.pi * (2 * (h : ℝ) + 1)) ∧
    additiveEnergy C = additiveEnergy (C.image f) ∧
    (sumset C).card = (sumset (C.image f)).card := by
  obtain ⟨_, hE, hS⟩ := high_order_freiman_exact hh hf hCA
  exact ⟨discrete_freiman_norm_transport hf hCA, hE, hS⟩

theorem discrete_freiman_cardinality_order_norm_transport
    {A : Finset Γ} {B : Set Λ} {f : Γ → Λ}
    (hf : IsAddFreimanIso A.card (A : Set Γ) B f)
    {C : Finset Γ} (hCA : C ⊆ A) :
    |discreteLittlewoodNorm Γ C - discreteLittlewoodNorm Λ (C.image f)| < 2 / Real.pi := by
  apply (discrete_freiman_norm_transport hf hCA).trans_lt
  have hsize : (C.card : ℝ) ≤ A.card := by exact_mod_cast Finset.card_le_card hCA
  have hd : 0 < Real.pi * (2 * (A.card : ℝ) + 1) := by positivity
  apply (div_lt_div_iff₀ hd Real.pi_pos).mpr
  have hm := mul_le_mul_of_nonneg_right hsize Real.pi_pos.le
  nlinarith [Real.pi_pos]

end Pair

section ModelFamily

variable {ι Γ₀ : Type*} {Γ : ι → Type*}
  [AddCommGroup Γ₀] [TopologicalSpace Γ₀] [DiscreteTopology Γ₀] [DecidableEq Γ₀]
  [∀ i, AddCommGroup (Γ i)] [∀ i, TopologicalSpace (Γ i)]
  [∀ i, DiscreteTopology (Γ i)] [∀ i, DecidableEq (Γ i)]

omit [TopologicalSpace Γ₀] [DiscreteTopology Γ₀] [DecidableEq Γ₀] in
/-- The budget is not paid once per model change. Any two members of an
arbitrarily large family in the same order-cardinality relation class are
compared directly, even when their ambient discrete groups differ. -/
theorem discrete_model_family_norm_transport (A : Finset Γ₀)
    (B : ∀ i, Finset (Γ i)) (f : ∀ i, Γ₀ → Γ i)
    (hf : ∀ i, IsAddFreimanIso A.card (A : Set Γ₀) (B i : Set (Γ i)) (f i))
    (i j : ι) {C : Finset Γ₀} (hCA : C ⊆ A) :
    |discreteLittlewoodNorm (Γ i) (C.image (f i)) -
      discreteLittlewoodNorm (Γ j) (C.image (f j))| < 2 / Real.pi := by
  classical
  let g := f j ∘ Function.invFunOn (f i) (A : Set Γ₀)
  have him : A.image (f i) = B i := by
    apply Finset.coe_injective
    simpa only [Finset.coe_image] using (hf i).bijOn.image_eq
  have hcard : (B i).card = A.card := by
    rw [← him]
    exact Finset.card_image_of_injOn (hf i).bijOn.injOn
  have hbridge : IsAddFreimanIso (B i).card (B i : Set (Γ i)) (B j : Set (Γ j)) g := by
    rw [hcard]
    exact (hf j).comp (hf i).invFunOn
  have hsub : C.image (f i) ⊆ B i := by
    rw [← him]
    exact Finset.image_subset_image hCA
  have he : (C.image (f i)).image g = C.image (f j) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro x hx
    dsimp only [g, Function.comp_def]
    rw [(hf i).bijOn.injOn.leftInvOn_invFunOn (hCA hx)]
  simpa only [he] using discrete_freiman_cardinality_order_norm_transport hbridge hsub

end ModelFamily
end LittlewoodInverse
