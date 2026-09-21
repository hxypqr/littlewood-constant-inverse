import LittlewoodInverse.Basic
import Mathlib

namespace LittlewoodInverse.PrefixCounting

def orderedPairs (B : Finset ℤ) : Finset (ℤ × ℤ) :=
  (B ×ˢ B).filter (fun p => p.1 ≤ p.2)

def differenceRelations (B : Finset ℤ) : Finset ((ℤ × ℤ) × ℤ × ℤ) :=
  ((B ×ˢ B) ×ˢ (B ×ˢ B)).filter (fun x => x.1.1 - x.1.2 = x.2.1 - x.2.2)

def orderedCollisionCount (B : Finset ℤ) : ℕ :=
  ((orderedPairs B ×ˢ orderedPairs B).filter
    (fun x => x.1.1 - x.1.2 = x.2.1 - x.2.2)).card

theorem relation_card (B : Finset ℤ) : (differenceRelations B).card = additiveEnergy B := by
  unfold differenceRelations additiveEnergy Finset.addEnergy
  apply Finset.card_nbij' (fun x => (x.1, x.2.2, x.2.1))
    (fun x => (x.1, x.2.2, x.2.1))
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hx ⊢
    exact ⟨⟨hx.1.1, hx.1.2.2, hx.1.2.1⟩, by omega⟩
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hx ⊢
    exact ⟨⟨hx.1.1, hx.1.2.2, hx.1.2.1⟩, by omega⟩
  · intro x _
    rfl
  · intro x _
    rfl

theorem ordered_count_filter (B : Finset ℤ) :
    orderedCollisionCount B = ((differenceRelations B).filter (fun x => x.1.1 ≤ x.1.2)).card := by
  unfold orderedCollisionCount
  congr 1
  ext x
  simp only [orderedPairs, differenceRelations, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨⟨ha, hb⟩, ⟨hc, hd⟩⟩, heq⟩
    exact ⟨⟨⟨ha, hc⟩, heq⟩, hb⟩
  · rintro ⟨⟨⟨ha, hc⟩, heq⟩, hb⟩
    exact ⟨⟨⟨ha, hb⟩, ⟨hc, by omega⟩⟩, heq⟩

theorem reflected_count (B : Finset ℤ) :
    ((differenceRelations B).filter (fun x => x.1.1 ≤ x.1.2)).card =
      ((differenceRelations B).filter (fun x => x.1.2 ≤ x.1.1)).card := by
  apply Finset.card_nbij' (fun x => ((x.1.2, x.1.1), x.2.2, x.2.1))
    (fun x => ((x.1.2, x.1.1), x.2.2, x.2.1))
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, differenceRelations, Finset.mem_product] at hx ⊢
    exact ⟨⟨⟨⟨hx.1.1.1.2, hx.1.1.1.1⟩, hx.1.1.2.2, hx.1.1.2.1⟩, by omega⟩, hx.2⟩
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, differenceRelations, Finset.mem_product] at hx ⊢
    exact ⟨⟨⟨⟨hx.1.1.1.2, hx.1.1.1.1⟩, hx.1.1.2.2, hx.1.1.2.1⟩, by omega⟩, hx.2⟩
  · intro x _
    rfl
  · intro x _
    rfl

theorem diagonal_count (B : Finset ℤ) :
    ((differenceRelations B).filter (fun x => x.1.1 = x.1.2)).card = B.card ^ 2 := by
  rw [pow_two, ← Finset.card_product]
  apply Finset.card_nbij' (fun x => (x.1.1, x.2.1)) (fun p => ((p.1, p.1), p.2, p.2))
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, differenceRelations, Finset.mem_product] at hx ⊢
    exact ⟨hx.1.1.1.1, hx.1.1.2.1⟩
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, differenceRelations, Finset.mem_product] at hp ⊢
    exact ⟨⟨⟨⟨hp.1, hp.1⟩, hp.2, hp.2⟩, by omega⟩, trivial⟩
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, differenceRelations, Finset.mem_product] at hx
    apply Prod.ext
    · exact Prod.ext rfl hx.2
    · exact Prod.ext rfl (by change x.2.1 = x.2.2; omega)
  · intro p _
    rfl

/-- The exact factor one-half in the manuscript's initial-segment pairing. -/
theorem ordered_collision_identity (B : Finset ℤ) :
    2 * orderedCollisionCount B = additiveEnergy B + B.card ^ 2 := by
  let R := differenceRelations B
  let S := R.filter (fun x => x.1.1 ≤ x.1.2)
  let T := R.filter (fun x => x.1.2 ≤ x.1.1)
  have hunion : S ∪ T = R := by
    ext x
    simp only [S, T, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      rcases le_total x.1.1 x.1.2 with hle | hle
      · exact Or.inl ⟨h, hle⟩
      · exact Or.inr ⟨h, hle⟩
  have hinter : S ∩ T = R.filter (fun x => x.1.1 = x.1.2) := by
    ext x
    simp only [S, T, Finset.mem_inter, Finset.mem_filter]
    constructor
    · rintro ⟨⟨h, h1⟩, _, h2⟩
      exact ⟨h, le_antisymm h1 h2⟩
    · rintro ⟨h, heq⟩
      exact ⟨⟨h, heq.le⟩, h, heq.ge⟩
  have h := Finset.card_union_add_card_inter S T
  rw [hunion, hinter, relation_card, diagonal_count] at h
  have heq : S.card = T.card := reflected_count B
  have hS : S.card = orderedCollisionCount B := (ordered_count_filter B).symm
  omega

end LittlewoodInverse.PrefixCounting
