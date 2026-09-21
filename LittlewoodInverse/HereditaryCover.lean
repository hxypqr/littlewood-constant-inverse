import LittlewoodInverse.Peeling
import LittlewoodInverse.Statements

namespace LittlewoodInverse

/-- Uniform covering constants obtained from the hereditary fourth-power
energy hypothesis. They are selected before the finite target set. -/
theorem almostCover_of_hereditary (η δ : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : Finset ℤ, X.Nonempty →
      (∀ Y ⊆ X, Y.Nonempty → η*(Y.card : ℝ)^4/(X.card : ℝ) ≤ additiveEnergy Y) →
      AlmostCover X δ c C := by
  obtain ⟨c₀,C₀,hc₀,hC₀,hcover⟩ := hereditary_energy_cover
  let c := c₀*(η*δ)^C₀*δ
  let C := max (C₀*(η*δ)^(-C₀)) (1/c)
  have hc : 0 < c := by dsimp only [c]; positivity
  have hC : 0 < C := lt_of_lt_of_le (by positivity : 0 < 1/c) (le_max_right _ _)
  refine ⟨c,C,hc,hC,?_⟩
  intro X hX henergy
  obtain ⟨blocks,hblocks,hdis,hrem,hcount⟩ := hcover X hX η δ hη hη1 hδ hδ1 henergy
  refine ⟨blocks,?_,hdis,hrem.le,?_⟩
  · intro B hB
    obtain ⟨hs,hn,hsize,hd⟩ := hblocks B hB
    refine ⟨hs,hn,hsize,?_⟩
    exact hd.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
  · have hh : (blocks.card : ℝ) ≤ 1/c := (le_div_iff₀ hc).mpr hcount
    exact hh.trans (le_max_right _ _)

end LittlewoodInverse
