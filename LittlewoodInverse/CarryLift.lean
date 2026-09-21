import LittlewoodInverse.Basic
import Mathlib

/-! # Exact carry counting for Lemma 7.4 -/

open scoped Pointwise

namespace LittlewoodInverse

def residueHeight (q : ℕ) (x : ZMod q × ℤ) : ℤ := (x.1.val : ℤ) + (q : ℤ) * x.2

noncomputable def arithmeticSlab (q : ℕ) (X : Finset (ZMod q)) (a : ℤ) (L : ℕ) : Finset ℤ :=
  (X ×ˢ Finset.Ico a (a + L)).image (residueHeight q)

theorem residueHeight_injective (q : ℕ) [NeZero q] :
    Function.Injective (residueHeight q) := by
  rintro ⟨x, u⟩ ⟨y, v⟩ h
  have hxy : x = y := by
    have hh := congrArg (fun z : ℤ => (z : ZMod q)) h
    simpa [residueHeight, ZMod.natCast_zmod_val] using hh
  subst y
  have huv : u = v := by
    apply mul_left_cancel₀ (show (q : ℤ) ≠ 0 by exact_mod_cast (NeZero.ne q))
    exact add_left_cancel h
  subst v
  rfl

theorem arithmeticSlab_card (q : ℕ) [NeZero q] (X : Finset (ZMod q))
    (a : ℤ) (L : ℕ) : (arithmeticSlab q X a L).card = X.card * L := by
  rw [arithmeticSlab, Finset.card_image_of_injective _ (residueHeight_injective q)]
  simp

theorem arithmeticSlab_sum_subset (q : ℕ) [NeZero q] (X : Finset (ZMod q))
    (a : ℤ) (L : ℕ) :
    arithmeticSlab q X a L + arithmeticSlab q X a L ⊆
      arithmeticSlab q (X + X) (2 * a) (2 * L) := by
  intro z hz
  obtain ⟨p, hp, p', hp', rfl⟩ := Finset.mem_add.mp hz
  obtain ⟨⟨x, u⟩, hxu, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨⟨y, v⟩, hyv, rfl⟩ := Finset.mem_image.mp hp'
  rcases Finset.mem_product.mp hxu with ⟨hx, hu⟩
  rcases Finset.mem_product.mp hyv with ⟨hy, hv⟩
  rcases Finset.mem_Ico.mp hu with ⟨hu0, hu1⟩
  rcases Finset.mem_Ico.mp hv with ⟨hv0, hv1⟩
  have hxy : x + y ∈ X + X := Finset.add_mem_add hx hy
  by_cases hcarry : x.val + y.val < q
  · have hval : ((x + y).val : ℤ) = (x.val : ℤ) + (y.val : ℤ) := by
      exact_mod_cast ZMod.val_add_of_lt hcarry
    apply Finset.mem_image.mpr
    refine ⟨(x + y, u + v), Finset.mem_product.mpr ⟨hxy, ?_⟩, ?_⟩
    · apply Finset.mem_Ico.mpr
      push_cast
      omega
    · simp only [residueHeight, hval]
      ring
  · have hval : (x.val : ℤ) + (y.val : ℤ) = ((x + y).val : ℤ) + (q : ℤ) := by
      exact_mod_cast ZMod.val_add_val_of_le (le_of_not_gt hcarry)
    apply Finset.mem_image.mpr
    refine ⟨(x + y, u + v + 1), Finset.mem_product.mpr ⟨hxy, ?_⟩, ?_⟩
    · apply Finset.mem_Ico.mpr
      push_cast
      omega
    · simp only [residueHeight]
      linear_combination -hval

/-- Cardinality form retaining both possible carries; valid also for `L = 0`. -/
theorem carry_sumset_card (q : ℕ) [NeZero q] (X : Finset (ZMod q))
    (a : ℤ) (L : ℕ) :
    (sumset (arithmeticSlab q X a L)).card ≤ (2 * L) * (sumset X).card := by
  calc
    _ ≤ (arithmeticSlab q (X + X) (2 * a) (2 * L)).card :=
      Finset.card_le_card (arithmeticSlab_sum_subset q X a L)
    _ = (2 * L) * (sumset X).card := by rw [arithmeticSlab_card]; simp [sumset, mul_comm]

/-- Lemma 7.4: bounded cyclic doubling lifts with a factor of at most two. -/
theorem carry_doubling (q : ℕ) [NeZero q] (X : Finset (ZMod q))
    (a : ℤ) (L : ℕ) (Q : ℝ)
    (hQ : ((sumset X).card : ℝ) ≤ Q * (X.card : ℝ)) :
    ((sumset (arithmeticSlab q X a L)).card : ℝ) ≤
      2 * Q * ((arithmeticSlab q X a L).card : ℝ) := by
  have hcard : ((sumset (arithmeticSlab q X a L)).card : ℝ) ≤
      (2 * L : ℝ) * ((sumset X).card : ℝ) := by
    exact_mod_cast carry_sumset_card q X a L
  rw [arithmeticSlab_card]
  push_cast
  have hmul := mul_le_mul_of_nonneg_left hQ (show 0 ≤ (2 * L : ℝ) by positivity)
  nlinarith

end LittlewoodInverse
