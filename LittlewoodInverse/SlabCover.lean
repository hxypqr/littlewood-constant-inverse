import LittlewoodInverse.BlockSlabs
import LittlewoodInverse.Peeling
import LittlewoodInverse.Statements

open scoped BigOperators

namespace LittlewoodInverse

/-- Hereditary spectral energy and BSG peeling give uniform covers of all
finite cyclic sets whose algebra norm is bounded by `B`. -/
theorem cyclic_spectral_almost_cover (B δ : ℝ) (hB : 1 ≤ B)
    (hδ : 0 < δ) (hδ1 : δ < 1) : ∃ c D : ℝ, 0 < c ∧ 0 < D ∧
    ∀ (q : ℕ) [NeZero q] (X : Finset (ZMod q)), X.Nonempty →
      cyclicLittlewoodNorm q X ≤ B →
      ∃ blocks : Finset (Finset (ZMod q)),
        (∀ Y ∈ blocks, Y ⊆ X ∧ Y.Nonempty ∧
          c * (X.card : ℝ) ≤ (Y.card : ℝ) ∧
          ((sumset Y).card : ℝ) ≤ D * (Y.card : ℝ)) ∧
        (∀ Y ∈ blocks, ∀ Z ∈ blocks, Y ≠ Z → Disjoint Y Z) ∧
        ((X \ blocks.biUnion id).card : ℝ) ≤ δ * (X.card : ℝ) ∧
        (blocks.card : ℝ) ≤ D := by
  obtain ⟨c₀, C₀, hc₀, hC₀, hpeel⟩ := hereditary_energy_cover
  let η : ℝ := (B ^ 2)⁻¹
  have hBp : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := by
    dsimp [η]
    apply (inv_le_one₀ (sq_pos_of_pos hBp)).mpr
    nlinarith
  let c := c₀ * (η * δ) ^ C₀ * δ
  have hc : 0 < c := by dsimp [c]; positivity
  let D := max (C₀ * (η * δ) ^ (-C₀)) c⁻¹
  have hD : 0 < D := lt_of_lt_of_le (inv_pos.mpr hc) (le_max_right _ _)
  refine ⟨c, D, hc, hD, ?_⟩
  intro q _ X hX hnorm
  have hx : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hn : 0 < cyclicLittlewoodNorm q X :=
    zero_lt_one.trans_le (one_le_cyclicLittlewoodNorm q hX)
  have hhered (Y : Finset (ZMod q)) (hYX : Y ⊆ X) (_hY : Y.Nonempty) :
      η * (Y.card : ℝ) ^ 4 / X.card ≤ (additiveEnergy Y : ℝ) := by
    calc
      _ = (Y.card : ℝ) ^ 4 / (B ^ 2 * X.card) := by dsimp [η]; ring
      _ ≤ (Y.card : ℝ) ^ 4 / (cyclicLittlewoodNorm q X ^ 2 * X.card) := by
        apply div_le_div_of_nonneg_left (by positivity) (mul_pos (sq_pos_of_pos hn) hx)
        gcongr
      _ ≤ _ := cyclic_spectral_hereditary_energy q hYX
  obtain ⟨blocks, hb, hd, hr, hncount⟩ := hpeel X hX η δ hη hη1 hδ hδ1 hhered
  refine ⟨blocks, ?_, hd, hr.le, ?_⟩
  · intro Y hY
    obtain ⟨hYX, hYe, hsize, hdouble⟩ := hb Y hY
    exact ⟨hYX, hYe, hsize,
      hdouble.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))⟩
  · have hcount : (blocks.card : ℝ) ≤ c⁻¹ := by
      rw [← one_div]
      apply (le_div_iff₀ hc).mpr
      exact hncount
    exact hcount.trans (le_max_right _ _)

variable (q : ℕ) [NeZero q]

@[simp] theorem mem_arithmeticSlab_residueHeight (X : Finset (ZMod q))
    (a : ℤ) (L : ℕ) (p : ZMod q × ℤ) :
    residueHeight q p ∈ arithmeticSlab q X a L ↔
      p.1 ∈ X ∧ a ≤ p.2 ∧ p.2 < a + L := by
  rw [arithmeticSlab, Finset.mem_image]
  constructor
  · rintro ⟨r, hr, he⟩
    obtain rfl := residueHeight_injective q he
    simpa only [Finset.mem_product, Finset.mem_Ico] using hr
  · intro h
    exact ⟨p, by simpa only [Finset.mem_product, Finset.mem_Ico] using h, rfl⟩

omit [NeZero q] in
theorem arithmeticSlab_subset {X Y : Finset (ZMod q)} (hXY : X ⊆ Y)
    (a : ℤ) (L : ℕ) : arithmeticSlab q X a L ⊆ arithmeticSlab q Y a L :=
  Finset.image_subset_image (Finset.product_subset_product_left hXY)

theorem arithmeticSlab_nonempty {X : Finset (ZMod q)} (hX : X.Nonempty)
    (a : ℤ) {L : ℕ} (hL : 0 < L) : (arithmeticSlab q X a L).Nonempty := by
  obtain ⟨x, hx⟩ := hX
  refine ⟨residueHeight q (x, a), ?_⟩
  rw [mem_arithmeticSlab_residueHeight]
  exact ⟨hx, le_rfl, by exact_mod_cast (show a < a + (L : ℤ) by omega)⟩

theorem arithmeticSlab_disjoint {X Y : Finset (ZMod q)} (hXY : Disjoint X Y)
    (a : ℤ) (L : ℕ) : Disjoint (arithmeticSlab q X a L) (arithmeticSlab q Y a L) := by
  apply Finset.disjoint_left.mpr
  intro z hx hy
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  have hy' := (mem_arithmeticSlab_residueHeight q Y a L p).mp hy
  exact Finset.disjoint_left.mp hXY (Finset.mem_product.mp hp).1 hy'.1

theorem arithmeticSlab_sdiff_union (X : Finset (ZMod q))
    (blocks : Finset (Finset (ZMod q))) (a : ℤ) (L : ℕ) :
    arithmeticSlab q X a L \ (blocks.image (fun Y => arithmeticSlab q Y a L)).biUnion id =
      arithmeticSlab q (X \ blocks.biUnion id) a L := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨hx, hn⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    have hpX := Finset.mem_product.mp hp
    rw [mem_arithmeticSlab_residueHeight]
    refine ⟨Finset.mem_sdiff.mpr ⟨hpX.1, ?_⟩, Finset.mem_Ico.mp hpX.2⟩
    intro h
    obtain ⟨Y, hY, hpY⟩ := Finset.mem_biUnion.mp h
    apply hn
    refine Finset.mem_biUnion.mpr ⟨arithmeticSlab q Y a L,
      Finset.mem_image.mpr ⟨Y, hY, rfl⟩, ?_⟩
    dsimp only [id_eq]
    rw [mem_arithmeticSlab_residueHeight]
    exact ⟨hpY, Finset.mem_Ico.mp hpX.2⟩
  · intro hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hpX, hpI⟩ := Finset.mem_product.mp hp
    obtain ⟨hpX, hn⟩ := Finset.mem_sdiff.mp hpX
    apply Finset.mem_sdiff.mpr
    refine ⟨(mem_arithmeticSlab_residueHeight q X a L p).mpr
      ⟨hpX, Finset.mem_Ico.mp hpI⟩, ?_⟩
    intro h
    obtain ⟨Z, hZ, hpZ⟩ := Finset.mem_biUnion.mp h
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hZ
    exact hn (Finset.mem_biUnion.mpr
      ⟨Y, hY, ((mem_arithmeticSlab_residueHeight q Y a L p).mp hpZ).1⟩)

/-- Lifting a finite cyclic cover along a whole arithmetic slab preserves
relative size and omitted proportion; carries cost a factor of two in doubling. -/
theorem arithmeticSlab_almost_cover {X : Finset (ZMod q)}
    (a : ℤ) {L : ℕ} (hL : 0 < L) {δ c D : ℝ} (hD : 0 ≤ D)
    (blocks : Finset (Finset (ZMod q)))
    (hb : ∀ Y ∈ blocks, Y ⊆ X ∧ Y.Nonempty ∧
      c * (X.card : ℝ) ≤ (Y.card : ℝ) ∧ ((sumset Y).card : ℝ) ≤ D * Y.card)
    (hd : ∀ Y ∈ blocks, ∀ Z ∈ blocks, Y ≠ Z → Disjoint Y Z)
    (hr : ((X \ blocks.biUnion id).card : ℝ) ≤ δ * X.card)
    (hn : (blocks.card : ℝ) ≤ D) : AlmostCover (arithmeticSlab q X a L) δ c (2 * D) := by
  classical
  let lift := fun Y => arithmeticSlab q Y a L
  refine ⟨blocks.image lift, ?_, ?_, ?_, ?_⟩
  · intro Z hZ
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hZ
    obtain ⟨hYX, hYe, hsize, hdouble⟩ := hb Y hY
    refine ⟨arithmeticSlab_subset q hYX a L, arithmeticSlab_nonempty q hYe a hL, ?_,
      carry_doubling q Y a L D hdouble⟩
    simp only [lift, arithmeticSlab_card, Nat.cast_mul]
    nlinarith [mul_le_mul_of_nonneg_right hsize (Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  · intro Y hY Z hZ hYZ
    obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hY
    obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hZ
    exact arithmeticSlab_disjoint q (hd U hU V hV (fun h => hYZ (congrArg lift h))) a L
  · rw [arithmeticSlab_sdiff_union, arithmeticSlab_card, arithmeticSlab_card,
      Nat.cast_mul, Nat.cast_mul]
    nlinarith [mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  · have hcount : ((blocks.image lift).card : ℝ) ≤ blocks.card := by
      exact_mod_cast Finset.card_image_le
    linarith

theorem uniform_slab_cover (B δ : ℝ) (hB : 1 ≤ B) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ c D : ℝ, 0 < c ∧ 0 < D ∧
      ∀ (q : ℕ) [NeZero q] (X : Finset (ZMod q)) (a : ℤ) (L : ℕ),
        X.Nonempty → 0 < L → cyclicLittlewoodNorm q X ≤ B →
          AlmostCover (arithmeticSlab q X a L) δ c D := by
  obtain ⟨c, D, hc, hD, hcover⟩ := cyclic_spectral_almost_cover B δ hB hδ hδ1
  refine ⟨c, 2 * D, hc, by positivity, ?_⟩
  intro q _ X a L hX hL hnorm
  obtain ⟨blocks, hb, hd, hr, hn⟩ := hcover q X hX hnorm
  exact arithmeticSlab_almost_cover q a hL hD.le blocks hb hd hr hn

end LittlewoodInverse
