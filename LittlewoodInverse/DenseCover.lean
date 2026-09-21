import LittlewoodInverse.PacketRelations
import LittlewoodInverse.PacketBudget
import LittlewoodInverse.HereditaryCover

namespace LittlewoodInverse

/-- Theorem 6.4: the complete uniform almost-covering theorem for actual
dense separated integer blocks. -/
theorem dense_blocks_cover (K ε β Δ : ℝ) (hβ : 0 < β) (hΔ : 1 ≤ Δ)
    (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (A : Finset ℤ) (_data : DenseBlocks β Δ A),
      2 ≤ A.card → littlewoodNorm A ≤ K*Real.log (A.card : ℝ) → AlmostCover A ε c C := by
  let T := DenseBlocks.certificateBudget K β
  let η := Real.exp (-2000*T^2)
  let δ := ε/(3*Δ)
  have hη : 0 < η := Real.exp_pos _
  have hη1 : η ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg T])
  have hden : (0 : ℝ) < 3*Δ := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hδ1 : δ < 1 := by dsimp only [δ]; rw [div_lt_one hden]; linarith
  obtain ⟨c,C,hc,hC,hcover⟩ := almostCover_of_hereditary η δ hη hη1 hδ hδ1
  refine ⟨c/(3*Δ),max C (7*Δ*C),by positivity,lt_of_lt_of_le hC (le_max_left _ _),?_⟩
  intro A data hA hnorm
  obtain ⟨κ,hκ,hlin,hL⟩ := data.uniform_certificate_budget hβ hA hnorm
  have hlabels : data.labels.Nonempty := by
    obtain ⟨x,hx⟩ := data.nonempty
    rw [data.exact_union] at hx
    obtain ⟨i,_,_⟩ := Finset.mem_biUnion.mp hx
    exact ⟨data.label i,Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have hlpos : (0 : ℝ) < data.labels.card := by exact_mod_cast hlabels.card_pos
  have hcov : AlmostCover data.labels δ c C := hcover data.labels hlabels (by
    intro S hS hSne
    apply (div_le_iff₀ hlpos).mpr
    exact data.label_hereditary_energy hκ (DenseBlocks.certificateBudget_ge_one K β)
      hlin hL S hS hSne)
  have hh := data.almostCover_of_labels hΔ hδ.le hc.le hC.le hcov
  have he : 3*Δ*δ = ε := by dsimp only [δ]; field_simp
  simpa only [he] using hh

end LittlewoodInverse
