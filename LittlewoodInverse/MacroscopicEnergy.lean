import LittlewoodInverse.CoverEnergy
import LittlewoodInverse.Statements

namespace LittlewoodInverse

/-- Corollary 1.6, with constants selected before the ambient and hereditary
sets. The main inverse theorem is its sole structural premise. -/
theorem macroscopic_hereditary_energy (hinverse : StructuralInverseTheorem)
    (K β Δ δ : ℝ) (hK : 1 ≤ K) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hΔ : 1 ≤ Δ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ (N₀ : ℕ) (ρ : ℝ), 2 ≤ N₀ ∧ 0 < ρ ∧
      ∀ A : Finset ℤ, N₀ ≤ A.card → AdmitsAssemblyModel β Δ A →
        littlewoodNorm A ≤ K*Real.log (A.card : ℝ) →
        ∀ Y ⊆ A, δ*(A.card : ℝ) ≤ (Y.card : ℝ) →
          ρ*(Y.card : ℝ)^3 ≤ additiveEnergy Y := by
  obtain ⟨N,c,C,hN,hc,hC,hcover⟩ := hinverse K (δ/4) β Δ hK
    (by positivity) (by linarith) hβ hβ1 hΔ
  refine ⟨N,δ^4/(16*C^5),hN,by positivity,?_⟩
  intro A hAN hgeom hnorm Y hYA hYlarge
  obtain ⟨blocks,hblocks,hdis,hrem,hcount⟩ := hcover A hAN hgeom hnorm
  have hA : A.Nonempty := Finset.card_pos.mp (by omega)
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hblocksne : blocks.Nonempty := by
    by_contra hh
    have he : blocks = ∅ := Finset.not_nonempty_iff_eq_empty.mp hh
    rw [he] at hrem
    simp only [Finset.biUnion_empty, Finset.sdiff_empty] at hrem
    have hm := mul_le_mul_of_nonneg_right hδ1 hApos.le
    nlinarith
  have he := energy_from_cover A Y blocks δ C hYA hA hblocksne hδ.le hC.le
    (fun B hB => (hblocks B hB).1) (fun B hB => (hblocks B hB).2.2.2)
    hYlarge (by nlinarith)
  have hpow : (blocks.card : ℝ)^4 ≤ C^4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcount 4
  have hmul := mul_le_mul_of_nonneg_right hpow
    (show 0 ≤ 16*C*(additiveEnergy Y : ℝ) by positivity)
  have he' : δ^4*(Y.card : ℝ)^3 ≤ 16*C^5*(additiveEnergy Y : ℝ) := by nlinarith
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0 < 16*C^5)).mpr
  nlinarith

end LittlewoodInverse
