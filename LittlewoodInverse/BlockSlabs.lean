import LittlewoodInverse.BoundaryExtraction
import LittlewoodInverse.CarryLift

open scoped BigOperators

namespace LittlewoodInverse

variable {q : ℕ}

def cellResidues (C : Finset (ZMod q × ℤ)) (u : ℤ) : Finset (ZMod q) :=
  (C.filter (fun p => p.2 = u)).image Prod.fst

@[simp] theorem mem_cellResidues (C : Finset (ZMod q × ℤ)) (b : ZMod q) (u : ℤ) :
    b ∈ cellResidues C u ↔ (b, u) ∈ C := by
  simp only [cellResidues, Finset.mem_image, Finset.mem_filter, Prod.exists]
  aesop

theorem cell_membership_constant (C : Finset (ZMod q × ℤ)) (b : ZMod q)
    {a u : ℤ} (hau : a ≤ u)
    (hgap : ∀ v : ℤ, a < v → v ≤ u → boundaryValue C (b, v) = 0) :
    (b, u) ∈ C ↔ (b, a) ∈ C := by
  have hind : ∀ v : ℤ, a ≤ v → v ≤ u → ((b, v) ∈ C ↔ (b, a) ∈ C) := by
    intro v hv
    induction v, hv using Int.leInduction with
    | base => simp
    | succ v hav ih =>
      intro hvu
      have h := hgap (v + 1) (by omega) hvu
      rw [boundaryValue_formula] at h
      have hvu' : v ≤ u := by omega
      have he : v + 1 - 1 = v := by omega
      rw [he] at h
      have hstep : (b, v + 1) ∈ C ↔ (b, v) ∈ C := by
        split_ifs at h <;> simp_all
      exact hstep.trans (ih hvu')
  exact hind u hau le_rfl

theorem boundary_heights_bracket (C : Finset (ZMod q × ℤ))
    (U : Finset ℤ) (hU : ∀ b u, boundaryValue C (b, u) ≠ 0 → u ∈ U)
    {b : ZMod q} {u : ℤ} (hbu : (b, u) ∈ C) :
    (∃ a ∈ U, a ≤ u) ∧ (∃ v ∈ U, u < v) := by
  classical
  let R := (C.filter (fun p => p.1 = b)).image Prod.snd
  have hRmem (v : ℤ) : v ∈ R ↔ (b, v) ∈ C := by
    simp only [R, Finset.mem_image, Finset.mem_filter, Prod.exists]
    aesop
  have hR : R.Nonempty := ⟨u, (hRmem u).mpr hbu⟩
  have hlo := Finset.min'_mem R hR
  have hhi := Finset.max'_mem R hR
  have hlnot : (b, R.min' hR - 1) ∉ C := by
    intro h
    have hh := Finset.min'_le R _ ((hRmem _).mpr h)
    omega
  have hhnot : (b, R.max' hR + 1) ∉ C := by
    intro h
    have hh := Finset.le_max' R _ ((hRmem _).mpr h)
    omega
  constructor
  · refine ⟨R.min' hR, hU b _ ?_, Finset.min'_le R _ ((hRmem u).mpr hbu)⟩
    rw [boundaryValue_formula]
    simp [hlnot, (hRmem _).mp hlo]
  · refine ⟨R.max' hR + 1, hU b _ ?_, ?_⟩
    · rw [boundaryValue_formula]
      simp [hhnot, (hRmem _).mp hhi]
    · have hh := Finset.le_max' R u ((hRmem u).mpr hbu)
      omega

noncomputable def nextSlabHeight (U : Finset ℤ) (a : ℤ) : ℤ :=
  if h : (U.filter (a < ·)).Nonempty then (U.filter (a < ·)).min' h else a

theorem le_nextSlabHeight (U : Finset ℤ) (a : ℤ) : a ≤ nextSlabHeight U a := by
  classical
  unfold nextSlabHeight
  split_ifs with h
  · have hh := Finset.mem_filter.mp (Finset.min'_mem (U.filter (a < ·)) h)
    exact hh.2.le
  · rfl

theorem nextSlabHeight_le_of_mem (U : Finset ℤ) {a b : ℤ} (hb : b ∈ U) (hab : a < b) :
    nextSlabHeight U a ≤ b := by
  classical
  have h : (U.filter (a < ·)).Nonempty := ⟨b, Finset.mem_filter.mpr ⟨hb, hab⟩⟩
  rw [nextSlabHeight, dif_pos h]
  exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hb, hab⟩)

theorem nextSlabHeight_no_between (U : Finset ℤ) {a v : ℤ}
    (hav : a < v) (hv : v < nextSlabHeight U a) : v ∉ U := by
  intro h
  exact (not_lt_of_ge (nextSlabHeight_le_of_mem U h hav)) hv

noncomputable def cellSlab (C : Finset (ZMod q × ℤ)) (U : Finset ℤ) (a : ℤ) :
    Finset (ZMod q × ℤ) := cellResidues C a ×ˢ Finset.Ico a (nextSlabHeight U a)

theorem cellSlab_subset (C : Finset (ZMod q × ℤ)) (U : Finset ℤ)
    (hU : ∀ b u, boundaryValue C (b, u) ≠ 0 → u ∈ U) (a : ℤ) :
    cellSlab C U a ⊆ C := by
  rintro ⟨b, u⟩ h
  obtain ⟨hb, hu⟩ := Finset.mem_product.mp h
  obtain ⟨hau, hun⟩ := Finset.mem_Ico.mp hu
  apply (cell_membership_constant C b hau ?_).mpr ((mem_cellResidues C b a).mp hb)
  intro v hav hvu
  by_contra h
  exact nextSlabHeight_no_between U hav (hvu.trans_lt hun) (hU b v h)

theorem cellSlab_disjoint (C : Finset (ZMod q × ℤ)) (U : Finset ℤ)
    {a b : ℤ} (ha : a ∈ U) (hb : b ∈ U) (hab : a ≠ b) :
    Disjoint (cellSlab C U a) (cellSlab C U b) := by
  apply Finset.disjoint_left.mpr
  intro p hpa hpb
  have haI := Finset.mem_Ico.mp (Finset.mem_product.mp hpa).2
  have hbI := Finset.mem_Ico.mp (Finset.mem_product.mp hpb).2
  rcases lt_or_gt_of_ne hab with hab | hba
  · have hh := nextSlabHeight_le_of_mem U hb hab
    omega
  · have hh := nextSlabHeight_le_of_mem U ha hba
    omega

/-- Every finite cell set is partitioned by the slabs between its shared
boundary heights. Empty slabs are harmless and are retained in the indexing. -/
theorem cellSlabs_cover (C : Finset (ZMod q × ℤ)) (U : Finset ℤ)
    (hU : ∀ b u, boundaryValue C (b, u) ≠ 0 → u ∈ U) :
    U.biUnion (cellSlab C U) = C := by
  classical
  apply Finset.Subset.antisymm
  · exact Finset.biUnion_subset.mpr (fun a _ => cellSlab_subset C U hU a)
  · rintro ⟨b, u⟩ hbu
    obtain ⟨⟨a₀, ha₀, ha₀u⟩, ⟨v₀, hv₀, huv₀⟩⟩ := boundary_heights_bracket C U hU hbu
    let L := U.filter (· ≤ u)
    have hL : L.Nonempty := ⟨a₀, Finset.mem_filter.mpr ⟨ha₀, ha₀u⟩⟩
    let a := L.max' hL
    have haL : a ∈ L := Finset.max'_mem L hL
    have haU : a ∈ U := (Finset.mem_filter.mp haL).1
    have hau : a ≤ u := (Finset.mem_filter.mp haL).2
    have hn : (U.filter (a < ·)).Nonempty :=
      ⟨v₀, Finset.mem_filter.mpr ⟨hv₀, hau.trans_lt huv₀⟩⟩
    have hun : u < nextSlabHeight U a := by
      rw [nextSlabHeight, dif_pos hn]
      apply (Finset.lt_min'_iff _ _).mpr
      intro v hv
      obtain ⟨hvU, hav⟩ := Finset.mem_filter.mp hv
      by_contra h
      have hvL : v ∈ L := Finset.mem_filter.mpr ⟨hvU, le_of_not_gt h⟩
      have hh := Finset.le_max' L v hvL
      exact (not_lt_of_ge hh) hav
    have hba : (b, a) ∈ C := (cell_membership_constant C b hau (by
      intro v hav hvu
      by_contra h
      exact nextSlabHeight_no_between U hav (hvu.trans_lt hun) (hU b v h))).mp hbu
    apply Finset.mem_biUnion.mpr
    exact ⟨a, haU, Finset.mem_product.mpr
      ⟨(mem_cellResidues C b a).mpr hba, Finset.mem_Ico.mpr ⟨hau, hun⟩⟩⟩

theorem blockInflation_biUnion (M : ℕ) {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (C : ι → Finset (ZMod q × ℤ)) :
    blockInflation q M (I.biUnion C) = I.biUnion (fun i => blockInflation q M (C i)) := by
  classical
  unfold blockInflation
  ext x
  simp only [Finset.mem_biUnion]
  aesop

theorem blockInflation_disjoint [NeZero q] {M : ℕ} (hM : 0 < M)
    {C D : Finset (ZMod q × ℤ)} (hCD : Disjoint C D) :
    Disjoint (blockInflation q M C) (blockInflation q M D) := by
  rw [blockInflation_eq_image, blockInflation_eq_image]
  apply Finset.disjoint_left.mpr
  intro z hzC hzD
  obtain ⟨p, hp, hpz⟩ := Finset.mem_image.mp hzC
  obtain ⟨r, hr, hrz⟩ := Finset.mem_image.mp hzD
  have hpr := blockCellIndex_injective q hM
    (Finset.mem_range.mp (Finset.mem_product.mp hp).2)
    (Finset.mem_range.mp (Finset.mem_product.mp hr).2) (hpz.trans hrz.symm)
  subst r
  exact Finset.disjoint_left.mp hCD (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hr).1

theorem blockInflation_product_interval (M : ℕ) (hM : 0 < M)
    (X : Finset (ZMod q)) (a b : ℤ) (hab : a ≤ b) :
    blockInflation q M (X ×ˢ Finset.Ico a b) =
      arithmeticSlab q X ((M : ℤ) * a) (M * (b - a).toNat) := by
  have hm : (0 : ℤ) < M := by exact_mod_cast hM
  have hlen : ((M * (b - a).toNat : ℕ) : ℤ) = (M : ℤ) * (b - a) := by
    rw [Nat.cast_mul, Int.toNat_of_nonneg (sub_nonneg.mpr hab)]
  ext z
  constructor
  · intro hz
    obtain ⟨⟨x, u⟩, hxu, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hx, hu⟩ := Finset.mem_product.mp hxu
    obtain ⟨hua, hub⟩ := Finset.mem_Ico.mp hu
    have hr0 : (0 : ℤ) ≤ r := by positivity
    have hrM : (r : ℤ) < M := by exact_mod_cast Finset.mem_range.mp hr
    apply Finset.mem_image.mpr
    refine ⟨(x, (M : ℤ) * u + r), Finset.mem_product.mpr ⟨hx, ?_⟩, rfl⟩
    apply Finset.mem_Ico.mpr
    rw [hlen]
    constructor <;> nlinarith
  · intro hz
    obtain ⟨⟨x, t⟩, hxt, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hx, ht⟩ := Finset.mem_product.mp hxt
    obtain ⟨hta, htb⟩ := Finset.mem_Ico.mp ht
    rw [hlen] at htb
    have hua : a ≤ t / (M : ℤ) := (Int.le_ediv_iff_mul_le hm).mpr (by nlinarith)
    have hub : t / (M : ℤ) < b := (Int.ediv_lt_iff_lt_mul hm).mpr (by nlinarith)
    have hr0 := Int.emod_nonneg t hm.ne'
    have hrM := Int.emod_lt_of_pos t hm
    apply Finset.mem_biUnion.mpr
    refine ⟨(x, t / (M : ℤ)), Finset.mem_product.mpr ⟨hx, Finset.mem_Ico.mpr ⟨hua, hub⟩⟩, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨(t % (M : ℤ)).toNat, ?_, ?_⟩
    · apply Finset.mem_range.mpr
      exact_mod_cast (show ((t % (M : ℤ)).toNat : ℤ) < M by
        rw [Int.toNat_of_nonneg hr0]; exact hrM)
    · rw [Int.toNat_of_nonneg hr0]
      dsimp [residueHeight]
      congr 2
      exact Int.mul_ediv_add_emod t M

theorem inflated_cellSlab (M : ℕ) (hM : 0 < M)
    (C : Finset (ZMod q × ℤ)) (U : Finset ℤ) (a : ℤ) :
    blockInflation q M (cellSlab C U a) =
      arithmeticSlab q (cellResidues C a) ((M : ℤ) * a)
        (M * (nextSlabHeight U a - a).toNat) :=
  blockInflation_product_interval M hM _ _ _ (le_nextSlabHeight U a)

end LittlewoodInverse
