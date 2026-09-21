import LittlewoodInverse.DenseCover
import LittlewoodInverse.LongBlockCover
import LittlewoodInverse.ModelReduction

namespace LittlewoodInverse

/-- Both concrete terminal geometries, uniformly over all their data and
all nonzero affine normalizations. -/
theorem uniform_terminal_cover (β Δ : ℝ) (hβ : 0 < β) (hΔ : 1 ≤ Δ) :
    UniformTerminalCover β Δ := by
  intro K ε hK hε hε1
  obtain ⟨cd,Cd,hcd,hCd,hdense⟩ := dense_blocks_cover K ε β Δ hβ hΔ hε hε1
  obtain ⟨N,cl,Cl,hcl,hCl,hlong⟩ := long_block_almost_cover K ε hK hε hε1
  refine ⟨max 2 N,min cd cl,max Cd Cl,lt_min hcd hcl,
    lt_of_lt_of_le hCd (le_max_left _ _),?_⟩
  intro A hAN hterm hnorm
  cases hterm with
  | singleton a => simp only [Finset.card_singleton] at hAN; omega
  | @dense B data u v hv =>
    rw [affine_card B u v hv] at hAN
    have he : littlewoodNorm (affineImage u v B) = littlewoodNorm B :=
      littlewoodNorm_affine B u hv
    rw [he,affine_card B u v hv] at hnorm
    have hc := hdense B data (by omega) hnorm
    exact almostCover_mono (almostCover_freiman_map (affine_freiman_two B u v hv) hc)
      le_rfl (min_le_left _ _) (le_max_left _ _)
  | inflation q M hq hM C hC hlongC u v hv =>
    letI : NeZero q := ⟨hq.ne'⟩
    rw [affine_card _ u v hv] at hAN
    have he : littlewoodNorm (affineImage u v (blockInflation q M C)) =
        littlewoodNorm (blockInflation q M C) := littlewoodNorm_affine _ u hv
    rw [he,affine_card _ u v hv] at hnorm
    have hc := hlong q M hM C hC hlongC (by omega) hnorm
    exact almostCover_mono (almostCover_freiman_map (affine_freiman_two _ u v hv) hc)
      le_rfl (min_le_right _ _) (le_max_right _ _)

/-- Theorem 1.5: the complete structural inverse theorem, including the
order-cardinality Freiman modelling alternative. -/
theorem structural_inverse_theorem : StructuralInverseTheorem :=
  structural_inverse_of_terminal (fun β Δ hβ _ hΔ => uniform_terminal_cover β Δ hβ hΔ)

end LittlewoodInverse
