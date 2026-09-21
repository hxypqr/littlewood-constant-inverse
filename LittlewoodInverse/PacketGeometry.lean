import LittlewoodInverse.Geometry

/-! # Cardinality and disjointness for dense separated blocks -/

open scoped BigOperators Pointwise

namespace LittlewoodInverse
namespace DenseBlocks

theorem translated_disjoint {β Δ : ℝ} {A : Finset ℤ} (data : DenseBlocks β Δ A)
    (i j : Fin data.count) (hij : i ≠ j) :
    Disjoint (affineImage (data.centre i) 1 (data.block i))
      (affineImage (data.centre j) 1 (data.block j)) := by
  apply Finset.disjoint_left.mpr
  intro z hi hj
  obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hi
  obtain ⟨y, hy, hyeq⟩ := Finset.mem_image.mp hj
  have hxb := data.block_mem i x hx
  have hyb := data.block_mem j y hy
  have hsep := data.separated i j hij
  have heq : data.centre i + x = data.centre j + y := by
    simpa using hxeq.trans hyeq.symm
  have habs : |data.centre i - data.centre j| ≤ 2 * (data.radius : ℤ) := by
    apply abs_le.mpr
    constructor <;> omega
  omega

theorem card_eq_sum {β Δ : ℝ} {A : Finset ℤ} (data : DenseBlocks β Δ A) :
    A.card = ∑ i, (data.block i).card := by
  calc
    A.card = (Finset.univ.biUnion
        (fun i => affineImage (data.centre i) 1 (data.block i))).card :=
      congrArg Finset.card data.exact_union
    _ = ∑ i, (data.block i).card := by
      rw [Finset.card_biUnion]
      · apply Finset.sum_congr rfl
        intro i _
        exact affine_card (data.block i) (data.centre i) 1 (by norm_num)
      · intro i _ j _ hij
        exact data.translated_disjoint i j hij

theorem block_card_upper {β Δ : ℝ} {A : Finset ℤ} (data : DenseBlocks β Δ A)
    (i : Fin data.count) : (data.block i).card ≤ 2 * data.radius + 1 := by
  have hsub : data.block i ⊆ Finset.Icc (-(data.radius : ℤ)) (data.radius : ℤ) := by
    intro x hx
    exact Finset.mem_Icc.mpr (data.block_mem i x hx)
  have h := Finset.card_le_card hsub
  simp only [Int.card_Icc] at h
  omega

theorem card_lower {β Δ : ℝ} {A : Finset ℤ} (data : DenseBlocks β Δ A) :
    data.count * data.minSize ≤ A.card := by
  rw [data.card_eq_sum]
  calc
    data.count * data.minSize = ∑ _ : Fin data.count, data.minSize := by simp
    _ ≤ ∑ i, (data.block i).card := Finset.sum_le_sum (fun i _ => data.block_size i)

theorem card_upper {β Δ : ℝ} {A : Finset ℤ} (data : DenseBlocks β Δ A) :
    A.card ≤ data.count * (2 * data.radius + 1) := by
  rw [data.card_eq_sum]
  calc
    ∑ i, (data.block i).card ≤ ∑ _ : Fin data.count, (2 * data.radius + 1) :=
      Finset.sum_le_sum (fun i _ => data.block_card_upper i)
    _ = _ := by simp

theorem card_upper_density {β Δ : ℝ} {A : Finset ℤ} (data : DenseBlocks β Δ A) :
    (A.card : ℝ) ≤ 3 * Δ * (data.minSize : ℝ) * (data.count : ℝ) := by
  have hD : 1 ≤ (data.radius : ℝ) := by exact_mod_cast data.radius_pos
  have hlocal : 2 * (data.radius : ℝ) + 1 ≤ 3 * Δ * (data.minSize : ℝ) := by
    nlinarith [data.diameter]
  have hcard : (A.card : ℝ) ≤ (data.count : ℝ) * (2 * (data.radius : ℝ) + 1) := by
    exact_mod_cast data.card_upper
  have hm := mul_le_mul_of_nonneg_left hlocal (show 0 ≤ (data.count : ℝ) by positivity)
  nlinarith

end DenseBlocks
end LittlewoodInverse
