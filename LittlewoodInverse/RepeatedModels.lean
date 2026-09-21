import LittlewoodInverse.ChebyshevTransport

namespace LittlewoodInverse

/-- The actual composite map through an arbitrarily long sequence of models. -/
def modelMap (f : ℕ → ℤ → ℤ) : ℕ → ℤ → ℤ
  | 0 => id
  | n + 1 => f n ∘ modelMap f n

theorem modelMap_freiman (A : ℕ → Finset ℤ) (f : ℕ → ℤ → ℤ)
    (hf : ∀ n, IsAddFreimanIso (A 0).card (A n : Set ℤ) (A (n + 1) : Set ℤ) (f n))
    (n : ℕ) : IsAddFreimanIso (A 0).card (A 0 : Set ℤ) (A n : Set ℤ) (modelMap f n) := by
  induction n with
  | zero => exact isAddFreimanIso_id
  | succ n ih => exact (hf n).comp ih

theorem modelMap_image (A : ℕ → Finset ℤ) (f : ℕ → ℤ → ℤ)
    (hf : ∀ n, IsAddFreimanIso (A 0).card (A n : Set ℤ) (A (n + 1) : Set ℤ) (f n))
    (n : ℕ) : (A 0).image (modelMap f n) = A n := by
  apply Finset.coe_injective
  simpa only [Finset.coe_image] using (modelMap_freiman A f hf n).bijOn.image_eq

theorem models_card (A : ℕ → Finset ℤ) (f : ℕ → ℤ → ℤ)
    (hf : ∀ n, IsAddFreimanIso (A 0).card (A n : Set ℤ) (A (n + 1) : Set ℤ) (f n))
    (n : ℕ) : (A n).card = (A 0).card := by
  rw [← modelMap_image A f hf n]
  exact Finset.card_image_of_injOn (modelMap_freiman A f hf n).bijOn.injOn

/-- Any two stages are compared directly inside the same relation class.
There is no accumulation of error with the number of model changes. -/
theorem repeated_model_norm_transport (A : ℕ → Finset ℤ) (f : ℕ → ℤ → ℤ)
    (hf : ∀ n, IsAddFreimanIso (A 0).card (A n : Set ℤ) (A (n + 1) : Set ℤ) (f n))
    (i j : ℕ) {C : Finset ℤ} (hCA : C ⊆ A 0) :
    |littlewoodNorm (C.image (modelMap f i)) - littlewoodNorm (C.image (modelMap f j))| <
      2 / Real.pi := by
  let g := modelMap f j ∘ Function.invFunOn (modelMap f i) (A 0 : Set ℤ)
  have hi := modelMap_freiman A f hf i
  have hj := modelMap_freiman A f hf j
  have hbridge : IsAddFreimanIso (A i).card (A i : Set ℤ) (A j : Set ℤ) g := by
    rw [models_card A f hf i]
    exact hj.comp hi.invFunOn
  have hsub : C.image (modelMap f i) ⊆ A i := by
    rw [← modelMap_image A f hf i]
    exact Finset.image_subset_image hCA
  have he : (C.image (modelMap f i)).image g = C.image (modelMap f j) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro x hx
    dsimp only [g, Function.comp_def]
    rw [hi.bijOn.injOn.leftInvOn_invFunOn (hCA hx)]
  have h := freiman_cardinality_order_norm_transport hbridge hsub
  simpa only [he] using h

end LittlewoodInverse
