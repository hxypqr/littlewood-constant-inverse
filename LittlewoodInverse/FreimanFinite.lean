import Mathlib

/-!
# Exact finite consequences of Freiman modelling

The cardinality, energy, and sumset assertions in Lemma 9.2.  The analytic
Fourier-norm transport estimate is not asserted in this file.
-/

open scoped Pointwise

namespace LittlewoodInverse

private theorem card_image_eq_of_same_fibres {α β γ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (f : α → β) (g : α → γ)
    (h : ∀ x ∈ s, ∀ y ∈ s, f x = f y ↔ g x = g y) :
    (s.image f).card = (s.image g).card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have h' := ih (fun x hx y hy => h x (Finset.mem_insert_of_mem hx)
      y (Finset.mem_insert_of_mem hy))
    have hm : f a ∈ s.image f ↔ g a ∈ s.image g := by
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨x, hx, heq⟩
        exact ⟨x, hx, (h x (Finset.mem_insert_of_mem hx) a (Finset.mem_insert_self _ _)).mp heq⟩
      · rintro ⟨x, hx, heq⟩
        exact ⟨x, hx, (h x (Finset.mem_insert_of_mem hx) a (Finset.mem_insert_self _ _)).mpr heq⟩
    simp only [Finset.image_insert]
    by_cases hf : f a ∈ s.image f
    · simpa only [Finset.card_insert_of_mem hf, Finset.card_insert_of_mem (hm.mp hf)] using h'
    · simpa only [Finset.card_insert_of_notMem hf,
        Finset.card_insert_of_notMem (fun hg => hf (hm.mpr hg))] using congrArg Nat.succ h'

theorem freiman_sumset_card {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [DecidableEq G] [DecidableEq H] {A : Finset G} {B : Set H} {f : G → H}
    (hf : IsAddFreimanIso 2 (A : Set G) B f) {C : Finset G} (hCA : C ⊆ A) :
    (C + C).card = (C.image f + C.image f).card := by
  have h1 : C + C = (C ×ˢ C).image (fun x : G × G => x.1 + x.2) := by
    ext x
    simp [Finset.mem_add, Finset.mem_image, Finset.mem_product]
    aesop
  have h2 : C.image f + C.image f =
      (C ×ˢ C).image (fun x : G × G => f x.1 + f x.2) := by
    ext x
    simp only [Finset.mem_add, Finset.mem_image, Finset.mem_product, Prod.exists]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨a, b, ⟨ha, hb⟩, rfl⟩
    · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩
      exact ⟨f a, ⟨a, ha, rfl⟩, f b, ⟨b, hb, rfl⟩, rfl⟩
  rw [h1, h2]
  apply card_image_eq_of_same_fibres
  intro x hx y hy
  rcases Finset.mem_product.mp hx with ⟨hx1, hx2⟩
  rcases Finset.mem_product.mp hy with ⟨hy1, hy2⟩
  exact (hf.add_eq_add (hCA hx1) (hCA hx2) (hCA hy1) (hCA hy2)).symm

theorem freiman_energy {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [DecidableEq G] [DecidableEq H] {A : Finset G} {B : Set H} {f : G → H}
    (hf : IsAddFreimanIso 2 (A : Set G) B f) {C : Finset G} (hCA : C ⊆ A) :
    Finset.addEnergy C C = Finset.addEnergy (C.image f) (C.image f) := by
  classical
  unfold Finset.addEnergy
  apply Finset.card_nbij (fun x : (G × G) × G × G =>
    ((f x.1.1, f x.1.2), f x.2.1, f x.2.2))
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hx ⊢
    refine ⟨⟨⟨Finset.mem_image_of_mem f hx.1.1.1, Finset.mem_image_of_mem f hx.1.1.2⟩,
      Finset.mem_image_of_mem f hx.1.2.1, Finset.mem_image_of_mem f hx.1.2.2⟩, ?_⟩
    exact (hf.add_eq_add (hCA hx.1.1.1) (hCA hx.1.2.1)
      (hCA hx.1.1.2) (hCA hx.1.2.2)).mpr hx.2
  · intro x hx y hy heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hx hy
    simp only [Prod.mk.injEq] at heq
    apply Prod.ext
    · exact Prod.ext (hf.bijOn.injOn (hCA hx.1.1.1) (hCA hy.1.1.1) heq.1.1)
        (hf.bijOn.injOn (hCA hx.1.1.2) (hCA hy.1.1.2) heq.1.2)
    · exact Prod.ext (hf.bijOn.injOn (hCA hx.1.2.1) (hCA hy.1.2.1) heq.2.1)
        (hf.bijOn.injOn (hCA hx.1.2.2) (hCA hy.1.2.2) heq.2.2)
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hy
    obtain ⟨a, ha, ha'⟩ := Finset.mem_image.mp hy.1.1.1
    obtain ⟨b, hb, hb'⟩ := Finset.mem_image.mp hy.1.1.2
    obtain ⟨c, hc, hc'⟩ := Finset.mem_image.mp hy.1.2.1
    obtain ⟨d, hd, hd'⟩ := Finset.mem_image.mp hy.1.2.2
    refine ⟨((a,b),c,d), ?_, ?_⟩
    · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨⟨ha, hb⟩, hc, hd⟩, ?_⟩
      apply (hf.add_eq_add (hCA ha) (hCA hc) (hCA hb) (hCA hd)).mp
      simpa only [ha', hb', hc', hd'] using hy.2
    · exact Prod.ext (Prod.ext ha' hb') (Prod.ext hc' hd')

theorem high_order_freiman_exact {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [DecidableEq G] [DecidableEq H] {A : Finset G} {B : Set H} {f : G → H}
    {h : ℕ} (hh : 2 ≤ h) (hf : IsAddFreimanIso h (A : Set G) B f)
    {C : Finset G} (hCA : C ⊆ A) :
    C.card = (C.image f).card ∧
    Finset.addEnergy C C = Finset.addEnergy (C.image f) (C.image f) ∧
    (C + C).card = (C.image f + C.image f).card := by
  have hf2 : IsAddFreimanIso 2 (A : Set G) B f := hf.mono (hmn := hh)
  refine ⟨(Finset.card_image_of_injOn ?_).symm, freiman_energy hf2 hCA,
    freiman_sumset_card hf2 hCA⟩
  intro x hx y hy heq
  exact hf.bijOn.injOn (hCA hx) (hCA hy) heq

end LittlewoodInverse
