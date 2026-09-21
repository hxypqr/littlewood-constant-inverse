import LittlewoodInverse.SignedProgressions
import LittlewoodInverse.GreenSandersProgressions
import LittlewoodInverse.LongBlockCover

open scoped BigOperators

namespace LittlewoodInverse

theorem signed_slab_of_spectral_budget (S : ℝ) (hS : 0 ≤ S) :
    ∃ B : ℝ, 0 < B ∧ ∀ (q : ℕ) [NeZero q] (X : Finset (ZMod q)),
      cyclicLittlewoodNorm q X ≤ S → ∀ (a : ℤ) (L : ℕ),
      ∃ D : SignedProgressionData (arithmeticSlab q X a L),
        (Fintype.card D.Index : ℝ) ≤ B := by
  classical
  obtain ⟨B,hB,hGS⟩ := BackgroundExternal.green_sanders_cyclic S hS
  refine ⟨B,hB,fun q _ X hX a L => ?_⟩
  obtain ⟨n,c,d,r,hc,hd,he,hn⟩ := hGS q X hX
  have hInd (Y : Finset (ZMod q)) (x : ZMod q) :
      BackgroundExternal.setIndicator Y x = (if x ∈ Y then 1 else 0 : ℤ) := by
    by_cases hx : x ∈ Y <;> simp [BackgroundExternal.setIndicator,hx]
  simp_rw [hInd] at he
  let D : SignedProgressionData (arithmeticSlab q X a L) := {
    Index := Fin n
    sign := c
    start := fun i => r i+(q : ℤ)*a
    step := d
    length := fun i => (q/d i)*L
    sign_one := hc
    step_pos := fun i => (hd i).1
    identity := fun z => signed_progression_lift q X d r c
      (fun i => (hd i).1) (fun i => (hd i).2.1) (fun i => (hd i).2.2)
      he a L z }
  exact ⟨D,by simpa [D] using hn⟩

/-- The stronger representation in the remark after Theorem 7.5:
uniformly boundedly many signed arithmetic progressions, with no assertion
that individual progression lengths are bounded by the target cardinality. -/
theorem long_block_signed_progressions (K : ℝ) (hK : 1 ≤ K) :
    ∃ (N₀ : ℕ) (B : ℝ), 0 < B ∧
      ∀ (q : ℕ) [NeZero q] (M : ℕ), 0 < M →
        ∀ C : Finset (ZMod q × ℤ), C.Nonempty → C.card ≤ M →
          N₀ ≤ (blockInflation q M C).card →
          littlewoodNorm (blockInflation q M C) ≤
            K*Real.log ((blockInflation q M C).card : ℝ) →
          ∃ D : SignedProgressionData (blockInflation q M C),
            (Fintype.card D.Index : ℝ) ≤ B := by
  obtain ⟨k,hk,hheight⟩ := exists_boundary_height_bound
  let S := 8*Real.pi*K
  let v := Real.exp (k*S)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hv : 0 < v := Real.exp_pos _
  obtain ⟨B,hB,hGS⟩ := signed_slab_of_spectral_budget (v*S) (mul_nonneg hv.le hS)
  obtain ⟨N₀,hN₀⟩ := exists_nat_ge (Real.exp (32*Real.pi+4))
  refine ⟨N₀,v*B,mul_pos hv hB,fun q _ M hM C hC hMC hlarge hnorm => ?_⟩
  have hcard : Real.exp (32*Real.pi+4) ≤ ((blockInflation q M C).card : ℝ) :=
    hN₀.trans (by exact_mod_cast hlarge)
  have hbudget : boundaryNorm q C ≤ S :=
    constant_boundary_budget q hC hMC (by linarith) hcard hnorm
  have hvcount : ((boundaryHeights C).card : ℝ) ≤ v := by
    exact (hheight q C).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hbudget hk.le))
  let P := inflatedSlabPartition q M hM C (boundaryHeights C)
    (fun b u hu => (mem_boundaryHeights C u).mpr ⟨b,hu⟩)
  apply signed_progression_glue_bound P v B hB.le
    (by simpa [P,inflatedSlabPartition] using hvcount)
  intro i
  change ∃ D : SignedProgressionData (blockInflation q M (cellSlab C (boundaryHeights C) i.val)),
    (Fintype.card D.Index : ℝ) ≤ B
  rw [inflated_cellSlab M hM]
  apply hGS q (cellResidues C i.val)
  exact (cellResidues_norm_le_boundary q C i.val).trans
    (mul_le_mul hvcount hbudget (boundaryNorm_nonneg q C) hv.le)

end LittlewoodInverse
