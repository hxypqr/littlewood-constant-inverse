import LittlewoodInverse.PerturbationCover
import LittlewoodInverse.AssemblyReduction

open scoped Topology symmDiff
open Filter Asymptotics

namespace LittlewoodInverse

theorem eventually_log_square_small (H : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℝ in atTop, H*(Real.log N)^2 ≤ δ*N := by
  have hl : (fun x : ℝ => (Real.log x)^2) =o[atTop] (fun x => x) := by
    have hh := isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1)
    simpa only [Real.rpow_two, Real.rpow_one] using hh
  filter_upwards [(hl.const_mul_left H).bound hδ, eventually_ge_atTop (0 : ℝ)] with N hn hN
  have hh : |H*(Real.log N)^2| ≤ δ*N := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hN] using hn
  exact (le_abs_self _).trans hh

/-- Corollary 9.3, including all uniform quantifiers. Its only premise is
the main structural inverse theorem, not any perturbative covering input. -/
theorem exceptional_perturbation_inverse (hinverse : StructuralInverseTheorem)
    (K ε β Δ H : ℝ) (hK : 1 ≤ K) (hε : 0 < ε) (hε1 : ε < 1/2)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hΔ : 1 ≤ Δ) (hH : 0 ≤ H) :
    ∃ (N₀ : ℕ) (c C : ℝ), 2 ≤ N₀ ∧ 0 < c ∧ 0 < C ∧
      ∀ A B : Finset ℤ, N₀ ≤ A.card →
        littlewoodNorm A ≤ K*Real.log (A.card : ℝ) →
        AdmitsAssemblyModel β Δ B →
        ((A ∆ B).card : ℝ) ≤ H*(Real.log (A.card : ℝ))^2 →
        AlmostCover A ε c C := by
  have hK' : 1 ≤ 2*(K+Real.sqrt H) := by nlinarith [Real.sqrt_nonneg H]
  obtain ⟨Nt,c,C,hNt,hc,hC,hcover⟩ := hinverse (2*(K+Real.sqrt H)) (ε/4) β Δ
    hK' (by positivity) (by linarith) hβ hβ1 hΔ
  let δ := min (1/2 : ℝ) (min (c/4) (ε/2))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδhalf : δ ≤ 1/2 := min_le_left _ _
  have hδc : δ ≤ c/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδε : δ ≤ ε/2 := (min_le_right _ _).trans (min_le_right _ _)
  have hnatevent := (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually (eventually_log_square_small H hδ)
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp hnatevent
  refine ⟨max N (max 4 (2*Nt)), c/4, 2*C, by omega, by positivity, by positivity, ?_⟩
  intro A B hAN hnorm hmodel hdiff
  have hA4 : (4 : ℝ) ≤ A.card := by exact_mod_cast (show 4 ≤ A.card by omega)
  have hApos : (0 : ℝ) < A.card := by linarith
  have hlogA : 0 ≤ Real.log (A.card : ℝ) := Real.log_natCast_nonneg _
  have hsmall : ((A ∆ B).card : ℝ) ≤ δ*A.card := hdiff.trans (hN A.card (by omega))
  have hAB : (A.card : ℝ) ≤ (B.card : ℝ)+(A ∆ B).card := by
    exact_mod_cast card_le_card_add_symmDiff A B
  have hBA : (B.card : ℝ) ≤ (A.card : ℝ)+(A ∆ B).card := by
    have hh := card_le_card_add_symmDiff B A
    rw [symmDiff_comm B A] at hh
    exact_mod_cast hh
  have hhalf := mul_le_mul_of_nonneg_right hδhalf (Nat.cast_nonneg A.card : (0 : ℝ) ≤ A.card)
  have hBhalf : (A.card : ℝ)/2 ≤ B.card := by linarith
  have hBupper : (B.card : ℝ) ≤ 2*A.card := by linarith
  have hBpos : (0 : ℝ) < B.card := by linarith
  have hBN : Nt ≤ B.card := by
    have hh : (2*Nt : ℝ) ≤ A.card := by exact_mod_cast (show 2*Nt ≤ A.card by omega)
    have : (Nt : ℝ) ≤ B.card := by linarith
    exact_mod_cast this
  have hlog : Real.log (A.card : ℝ) ≤ 2*Real.log (B.card : ℝ) := by
    have hsq : (A.card : ℝ) ≤ (B.card : ℝ)^2 := by nlinarith
    have hh := Real.log_le_log hApos hsq
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hnormB : littlewoodNorm B ≤ 2*(K+Real.sqrt H)*Real.log (B.card : ℝ) := by
    have hdist := littlewoodNorm_sub_le_sqrt_symmDiff A B
    have hsqrt : Real.sqrt ((A ∆ B).card : ℝ) ≤ Real.sqrt H*Real.log (A.card : ℝ) := by
      calc
        _ ≤ Real.sqrt (H*(Real.log (A.card : ℝ))^2) := Real.sqrt_le_sqrt hdiff
        _ = _ := by rw [Real.sqrt_mul hH, Real.sqrt_sq_eq_abs, abs_of_nonneg hlogA]
    have hh := (abs_le.mp hdist).1
    have hlogmul := mul_le_mul_of_nonneg_left hlog
      (show 0 ≤ K+Real.sqrt H by nlinarith [Real.sqrt_nonneg H])
    nlinarith
  have hcov := hcover B hBN hmodel hnormB
  apply almostCover_intersect (Finset.card_pos.mp (Nat.cast_pos.mp hBpos)) hc hC.le hcov
    (by linarith)
  · have hmc := mul_le_mul_of_nonneg_right hδc (Nat.cast_nonneg A.card : (0 : ℝ) ≤ A.card)
    have hm := mul_le_mul_of_nonneg_left hBhalf hc.le
    nlinarith
  · have hme := mul_le_mul_of_nonneg_right hδε (Nat.cast_nonneg A.card : (0 : ℝ) ≤ A.card)
    have hm := mul_le_mul_of_nonneg_left hBupper hε.le
    nlinarith

end LittlewoodInverse
