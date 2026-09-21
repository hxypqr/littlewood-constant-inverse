import LittlewoodInverse.LabelGeometry
import LittlewoodInverse.Statements

open scoped BigOperators Pointwise

namespace LittlewoodInverse
namespace DenseBlocks

noncomputable def labels {β Δ : ℝ} {A : Finset ℤ} (data : DenseBlocks β Δ A) : Finset ℤ :=
  Finset.univ.image data.label

def indexSet {β Δ : ℝ} {A : Finset ℤ} (data : DenseBlocks β Δ A) (S : Finset ℤ) :
    Finset (Fin data.count) := Finset.univ.filter (fun i => data.label i ∈ S)

def labelLift {β Δ : ℝ} {A : Finset ℤ} (data : DenseBlocks β Δ A) (S : Finset ℤ) : Finset ℤ :=
  (data.indexSet S).biUnion (fun i => affineImage (data.centre i) 1 (data.block i))

theorem labels_card {β Δ : ℝ} {A : Finset ℤ} (data : DenseBlocks β Δ A) :
    data.labels.card = data.count := by
  rw [labels, Finset.card_image_of_injective _ data.label_injective]
  simp

theorem label_image_indexSet {β Δ : ℝ} {A : Finset ℤ} (data : DenseBlocks β Δ A)
    {S : Finset ℤ} (hS : S ⊆ data.labels) : (data.indexSet S).image data.label = S := by
  ext x
  simp only [Finset.mem_image, indexSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact hi
  · intro hx
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (hS hx)
    exact ⟨i, hi ▸ hx, hi⟩

theorem indexSet_card {β Δ : ℝ} {A : Finset ℤ} (data : DenseBlocks β Δ A)
    {S : Finset ℤ} (hS : S ⊆ data.labels) : (data.indexSet S).card = S.card := by
  have hh := congrArg Finset.card (data.label_image_indexSet hS)
  simpa only [Finset.card_image_of_injective _ data.label_injective] using hh

theorem labelLift_card_eq {β Δ : ℝ} {A : Finset ℤ} (data : DenseBlocks β Δ A) (S : Finset ℤ) :
    (data.labelLift S).card = ∑ i ∈ data.indexSet S, (data.block i).card := by
  unfold labelLift
  rw [Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun i _ => affine_card _ _ 1 (by norm_num)
  · intro i _ j _ hij
    exact data.translated_disjoint i j hij

theorem labelLift_card_lower {β Δ : ℝ} {A : Finset ℤ} (data : DenseBlocks β Δ A)
    {S : Finset ℤ} (hS : S ⊆ data.labels) : data.minSize * S.card ≤ (data.labelLift S).card := by
  rw [data.labelLift_card_eq]
  calc
    _ = ∑ _i ∈ data.indexSet S, data.minSize := by simp [data.indexSet_card hS, Nat.mul_comm]
    _ ≤ _ := Finset.sum_le_sum fun i _ => data.block_size i

theorem labelLift_card_upper {β Δ : ℝ} {A : Finset ℤ} (data : DenseBlocks β Δ A)
    {S : Finset ℤ} (hS : S ⊆ data.labels) :
    (data.labelLift S).card ≤ (2*data.radius+1)*S.card := by
  rw [data.labelLift_card_eq]
  calc
    _ ≤ ∑ _i ∈ data.indexSet S, (2*data.radius+1) :=
      Finset.sum_le_sum fun i _ => data.block_card_upper i
    _ = _ := by simp [data.indexSet_card hS, Nat.mul_comm]

theorem labelLift_subset {β Δ : ℝ} {A : Finset ℤ} (data : DenseBlocks β Δ A)
    (S : Finset ℤ) : data.labelLift S ⊆ A := by
  intro x hx
  obtain ⟨i, _, hx⟩ := Finset.mem_biUnion.mp hx
  rw [data.exact_union]
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩

theorem labelLift_disjoint {β Δ : ℝ} {A : Finset ℤ} (data : DenseBlocks β Δ A)
    {S T : Finset ℤ} (hST : Disjoint S T) : Disjoint (data.labelLift S) (data.labelLift T) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i, hi, hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨j, hj, hy⟩ := Finset.mem_biUnion.mp hy
  have hij : i = j := by
    by_contra h
    exact Finset.disjoint_left.mp (data.translated_disjoint i j h) hx hy
  subst j
  exact Finset.disjoint_left.mp hST (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

/-- A point in a selected original block has a bounded remainder relative
to its integer floor label. -/
theorem labelLift_representation {β Δ : ℝ} {A : Finset ℤ} (data : DenseBlocks β Δ A)
    {S : Finset ℤ} {x : ℤ} (hx : x ∈ data.labelLift S) :
    ∃ l ∈ S, ∃ u ∈ Finset.Icc (-(data.radius : ℤ)) (2*data.radius),
      x = (data.radius : ℤ)*l+u := by
  obtain ⟨i, hi, hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  have hb := data.block_mem i y hy
  have hD : (0 : ℤ) < data.radius := by exact_mod_cast data.radius_pos
  have h0 := Int.emod_nonneg (data.centre i) hD.ne'
  have hlt := Int.emod_lt_of_pos (data.centre i) hD
  have he := Int.emod_add_mul_ediv (data.centre i) data.radius
  refine ⟨data.label i, (Finset.mem_filter.mp hi).2,
    data.centre i % data.radius + y, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
  unfold label
  linear_combination -he

theorem labelLift_sumset_card {β Δ : ℝ} {A : Finset ℤ} (data : DenseBlocks β Δ A)
    (S : Finset ℤ) :
    (sumset (data.labelLift S)).card ≤ (6*data.radius+1)*(sumset S).card := by
  let V := Finset.Icc (-(2*data.radius : ℤ)) (4*data.radius)
  have hsub : sumset (data.labelLift S) ⊆
      ((sumset S) ×ˢ V).image (fun p => (data.radius : ℤ)*p.1+p.2) := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨l, hl, u, hu, rfl⟩ := data.labelLift_representation hx
    obtain ⟨m, hm, v, hv, rfl⟩ := data.labelLift_representation hy
    have hu' := Finset.mem_Icc.mp hu
    have hv' := Finset.mem_Icc.mp hv
    refine Finset.mem_image.mpr ⟨(l+m,u+v), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_add.mpr ⟨l, hl, m, hm, rfl⟩
    · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · dsimp only; ring
  have hV : V.card = 6*data.radius+1 := by
    dsimp only [V]
    rw [Int.card_Icc]
    omega
  calc
    _ ≤ (((sumset S) ×ˢ V).image (fun p => (data.radius : ℤ)*p.1+p.2)).card :=
      Finset.card_le_card hsub
    _ ≤ ((sumset S) ×ˢ V).card := Finset.card_image_le
    _ = _ := by rw [Finset.card_product, hV]; ring

theorem mem_labelLift {β Δ : ℝ} {A : Finset ℤ} (data : DenseBlocks β Δ A)
    (S : Finset ℤ) (x : ℤ) : x ∈ data.labelLift S ↔
      ∃ i : Fin data.count, data.label i ∈ S ∧
        x ∈ affineImage (data.centre i) 1 (data.block i) := by
  simp only [labelLift, Finset.mem_biUnion, indexSet, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem labelLift_labels {β Δ : ℝ} {A : Finset ℤ} (data : DenseBlocks β Δ A) :
    data.labelLift data.labels = A := by
  have hidx : data.indexSet data.labels = Finset.univ := by
    ext i
    simp only [indexSet, Finset.mem_filter, Finset.mem_univ, true_and,
      iff_true]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  rw [labelLift, hidx, ← data.exact_union]

theorem labelLift_sdiff {β Δ : ℝ} {A : Finset ℤ} (data : DenseBlocks β Δ A)
    (S T : Finset ℤ) : data.labelLift (S \ T) = data.labelLift S \ data.labelLift T := by
  ext x
  rw [data.mem_labelLift, Finset.mem_sdiff, data.mem_labelLift, data.mem_labelLift]
  constructor
  · rintro ⟨i, hi, hx⟩
    refine ⟨⟨i, (Finset.mem_sdiff.mp hi).1, hx⟩, ?_⟩
    rintro ⟨j, hj, hy⟩
    by_cases hij : i=j
    · subst j
      exact (Finset.mem_sdiff.mp hi).2 hj
    · exact Finset.disjoint_left.mp (data.translated_disjoint i j hij) hx hy
  · rintro ⟨⟨i, hi, hx⟩, hn⟩
    exact ⟨i, Finset.mem_sdiff.mpr ⟨hi, fun ht => hn ⟨i, ht, hx⟩⟩, hx⟩

theorem labelLift_biUnion {β Δ : ℝ} {A : Finset ℤ} (data : DenseBlocks β Δ A)
    (blocks : Finset (Finset ℤ)) :
    data.labelLift (blocks.biUnion id) = (blocks.image data.labelLift).biUnion id := by
  ext x
  simp only [data.mem_labelLift, Finset.mem_biUnion, Finset.mem_image, id_eq]
  constructor
  · rintro ⟨i, ⟨S, hS, hi⟩, hx⟩
    exact ⟨data.labelLift S, ⟨S,hS,rfl⟩, (data.mem_labelLift S x).mpr ⟨i,hi,hx⟩⟩
  · rintro ⟨_, ⟨S, hS, rfl⟩, hx⟩
    obtain ⟨i, hi, hx⟩ := (data.mem_labelLift S x).mp hx
    exact ⟨i, ⟨S,hS,hi⟩, hx⟩

/-- Every label almost-cover lifts to the actual integer blocks, with the
size, doubling, disjointness, count and omitted mass all controlled. -/
theorem almostCover_of_labels {β Δ ε c C : ℝ} {A : Finset ℤ}
    (data : DenseBlocks β Δ A) (hΔ : 1 ≤ Δ) (hε : 0 ≤ ε) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hcover : AlmostCover data.labels ε c C) :
    AlmostCover A (3*Δ*ε) (c/(3*Δ)) (max C (7*Δ*C)) := by
  classical
  obtain ⟨blocks,hblocks,hdis,hrem,hcount⟩ := hcover
  have hD : 1 ≤ (data.radius : ℝ) := by exact_mod_cast data.radius_pos
  have hDp : (0 : ℝ) < 3*Δ := by positivity
  have hM : 0 ≤ (data.minSize : ℝ) := Nat.cast_nonneg _
  have hL : 0 ≤ (data.count : ℝ) := Nat.cast_nonneg _
  have hlocal : 2*(data.radius : ℝ)+1 ≤ 3*Δ*data.minSize := by
    nlinarith [data.diameter]
  have hlocal7 : 6*(data.radius : ℝ)+1 ≤ 7*Δ*data.minSize := by
    nlinarith [data.diameter]
  refine ⟨blocks.image data.labelLift, ?_, ?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨hsub,hne,hsize,hdouble⟩ := hblocks S hS
    have hlow : (data.minSize : ℝ)*S.card ≤ (data.labelLift S).card := by
      exact_mod_cast data.labelLift_card_lower hsub
    have hneLift : (data.labelLift S).Nonempty := by
      apply Finset.card_pos.mp
      exact (Nat.mul_pos data.minSize_pos hne.card_pos).trans_le (data.labelLift_card_lower hsub)
    refine ⟨data.labelLift_subset S,hneLift,?_,?_⟩
    · rw [data.labels_card] at hsize
      calc
        _ ≤ c/(3*Δ)*(3*Δ*data.minSize*data.count) :=
          mul_le_mul_of_nonneg_left data.card_upper_density (div_nonneg hc hDp.le)
        _ = (data.minSize : ℝ)*(c*data.count) := by field_simp
        _ ≤ (data.minSize : ℝ)*S.card := mul_le_mul_of_nonneg_left hsize hM
        _ ≤ _ := hlow
    · have hh : ((sumset (data.labelLift S)).card : ℝ) ≤
          (6*(data.radius : ℝ)+1)*(sumset S).card := by
        exact_mod_cast data.labelLift_sumset_card S
      calc
        _ ≤ (6*(data.radius : ℝ)+1)*(sumset S).card := hh
        _ ≤ (7*Δ*data.minSize)*(C*S.card) :=
          mul_le_mul hlocal7 hdouble (Nat.cast_nonneg _) (by positivity)
        _ = (7*Δ*C)*((data.minSize : ℝ)*S.card) := by ring
        _ ≤ (7*Δ*C)*(data.labelLift S).card :=
          mul_le_mul_of_nonneg_left hlow (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg _)
  · intro B hB D hD hBD
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hD
    apply data.labelLift_disjoint
    exact hdis S hS T hT (fun he => hBD (congrArg data.labelLift he))
  · have he : A \ (blocks.image data.labelLift).biUnion id =
        data.labelLift (data.labels \ blocks.biUnion id) := by
      rw [data.labelLift_sdiff, data.labelLift_labels, data.labelLift_biUnion]
    rw [he]
    have hu : ((data.labelLift (data.labels \ blocks.biUnion id)).card : ℝ) ≤
        (2*(data.radius : ℝ)+1)*((data.labels \ blocks.biUnion id).card : ℝ) := by
      exact_mod_cast data.labelLift_card_upper Finset.sdiff_subset
    rw [data.labels_card] at hrem
    have hn : (data.minSize : ℝ)*data.count ≤ A.card := by
      exact_mod_cast (by simpa only [Nat.mul_comm] using data.card_lower)
    calc
      _ ≤ (2*(data.radius : ℝ)+1)*((data.labels \ blocks.biUnion id).card : ℝ) := hu
      _ ≤ (3*Δ*data.minSize)*(ε*data.count) :=
        mul_le_mul hlocal hrem (Nat.cast_nonneg _) (by positivity)
      _ = (3*Δ*ε)*((data.minSize : ℝ)*data.count) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hn (by positivity)
  · have hh : ((blocks.image data.labelLift).card : ℝ) ≤ blocks.card := by
      exact_mod_cast Finset.card_image_le
    exact (hh.trans hcount).trans (le_max_left _ _)

end DenseBlocks
end LittlewoodInverse
