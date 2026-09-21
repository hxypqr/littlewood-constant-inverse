import LittlewoodInverse.TerminalCover
import LittlewoodInverse.MacroscopicEnergy
import LittlewoodInverse.PerturbationAsymptotic

open scoped symmDiff

namespace LittlewoodInverse

/-- Corollary 1.6 with the structural theorem premise fully discharged. -/
theorem macroscopic_energy_corollary (K β Δ δ : ℝ) (hK : 1 ≤ K)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hΔ : 1 ≤ Δ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ (N₀ : ℕ) (ρ : ℝ), 2 ≤ N₀ ∧ 0 < ρ ∧
      ∀ A : Finset ℤ, N₀ ≤ A.card → AdmitsAssemblyModel β Δ A →
        littlewoodNorm A ≤ K*Real.log (A.card : ℝ) →
        ∀ Y ⊆ A, δ*(A.card : ℝ) ≤ (Y.card : ℝ) →
          ρ*(Y.card : ℝ)^3 ≤ additiveEnergy Y :=
  macroscopic_hereditary_energy structural_inverse_theorem K β Δ δ hK hβ hβ1 hΔ hδ hδ1

/-- Corollary 9.3 with the structural theorem premise fully discharged. -/
theorem exceptional_perturbation_corollary (K ε β Δ H : ℝ)
    (hK : 1 ≤ K) (hε : 0 < ε) (hε1 : ε < 1/2)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hΔ : 1 ≤ Δ) (hH : 0 ≤ H) :
    ∃ (N₀ : ℕ) (c C : ℝ), 2 ≤ N₀ ∧ 0 < c ∧ 0 < C ∧
      ∀ A B : Finset ℤ, N₀ ≤ A.card →
        littlewoodNorm A ≤ K*Real.log (A.card : ℝ) →
        AdmitsAssemblyModel β Δ B →
        ((A ∆ B).card : ℝ) ≤ H*(Real.log (A.card : ℝ))^2 →
        AlmostCover A ε c C :=
  exceptional_perturbation_inverse structural_inverse_theorem K ε β Δ H hK hε hε1 hβ hβ1 hΔ hH

end LittlewoodInverse
