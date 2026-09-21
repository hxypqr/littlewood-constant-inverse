import LittlewoodInverse.MajorityBlocks
import LittlewoodInverse.MajorityCounting
import LittlewoodInverse.MajorityOrdered
import LittlewoodInverse.MajorityFactorial

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LittlewoodInverse
namespace Majority

theorem GoodSet.mono {α : Type*} [DecidableEq α] {F : Circle → ℂ}
    {Φ : α → Circle → ℂ} {η η' : ℝ} {S : Finset α}
    (h : GoodSet F Φ η S) (hle : η' ≤ η) : GoodSet F Φ η' S := by
  obtain ⟨hodd, h3, U, hUS, hbal, hpair⟩ := h
  exact ⟨hodd, h3, U, hUS, hbal, hle.trans hpair⟩

/-- The density version of majority amplification at the level of unordered
supports, with an actual balanced orientation for every counted support. -/
theorem dense_good_sets {α : Type*} [DecidableEq α]
    {F : Circle → ℂ} (hF : Integrable F circleMeasure)
    (Φ : α → Circle → ℂ)
    (hΦ : ∀ i, AEStronglyMeasurable (Φ i) circleMeasure)
    (hΦbound : ∀ i, ∀ᵐ x ∂circleMeasure, ‖Φ i x‖ ≤ 1)
    {κ T : ℝ} (hκ : 0 < κ) (hT : 1 ≤ T)
    (hlin : ∀ i, κ ≤ (circlePairing F (Φ i)).re)
    (hL : (∫ x, ‖F x‖ ∂circleMeasure) ≤ T * κ)
    (V : Finset α) (hm : majorityDegree T ≤ V.card) :
    ∃ k, Odd k ∧ 3 ≤ k ∧ k ≤ majorityDegree T ∧
      (V.card.choose k : ℝ) /
        (((majorityDegree T : ℝ) + 1) * (2 : ℝ) ^ majorityDegree T) ≤
        MajorityCounting.goodCount V (GoodSet F Φ (Real.exp (-300 * T ^ 2) * κ)) k := by
  apply MajorityCounting.exists_dense_good_size V
    (GoodSet F Φ (Real.exp (-300 * T ^ 2) * κ)) (majorityDegree T) hm
  · intro S hS
    exact ⟨hS.1, hS.2.1⟩
  · intro B hB
    obtain ⟨S, hSB, hgood⟩ := every_block_contains_good_set (majorityHalfDegree T)
      hF Φ hΦ hΦbound hκ hT hlin hL
      (by simpa only [majorityDegree, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_one] using majorityDegree_lower T)
      B (Finset.mem_powersetCard.mp hB).2
    exact ⟨S, hSB, hgood.mono (majority_correlation_threshold hT hκ.le)⟩

def BalancedCorrelation {α : Type*} [DecidableEq α]
    (F : Circle → ℂ) (Φ : α → Circle → ℂ) (η : ℝ) (U V : Finset α) : Prop :=
  η ≤ ‖circlePairing F (fun x ↦ (∏ i ∈ U, Φ i x) * ∏ i ∈ V, conj (Φ i x))‖

/-- Lemma 6.1. An ordered pair of tuples of lengths `s,t` is an ordered
`s+t` tuple via `Fin.append`; `orderedPairs` enforces distinctness of every
entry. The first length is one greater than the second, preserving balance. -/
theorem dense_mixed_correlations {α : Type*} [Fintype α] [DecidableEq α]
    {F : Circle → ℂ} (hF : Integrable F circleMeasure)
    (Φ : α → Circle → ℂ)
    (hΦ : ∀ i, AEStronglyMeasurable (Φ i) circleMeasure)
    (hΦbound : ∀ i, ∀ᵐ x ∂circleMeasure, ‖Φ i x‖ ≤ 1)
    {κ T : ℝ} (hκ : 0 < κ) (hT : 1 ≤ T)
    (hlin : ∀ i, κ ≤ (circlePairing F (Φ i)).re)
    (hL : (∫ x, ‖F x‖ ∂circleMeasure) ≤ T * κ)
    (hm : majorityDegree T ≤ Fintype.card α) :
    ∃ t : ℕ, 1 ≤ t ∧ 2 * t + 1 ≤ majorityDegree T ∧
      Real.exp (-300 * T ^ 2) * (Fintype.card α : ℝ) ^ (2 * t + 1) ≤
        ((MajorityCounting.orderedPairs (t + 1) t
          (BalancedCorrelation F Φ (Real.exp (-300 * T ^ 2) * κ))).card : ℝ) := by
  classical
  obtain ⟨k, hodd, h3, hkm, hdensity⟩ := dense_good_sets hF Φ hΦ hΦbound hκ hT hlin hL
    (Finset.univ : Finset α) (by simpa using hm)
  obtain ⟨t, rfl⟩ := hodd
  let η := Real.exp (-300 * T ^ 2) * κ
  let H := ((Finset.univ : Finset α).powersetCard (2 * t + 1)).filter (GoodSet F Φ η)
  let P := BalancedCorrelation F Φ η
  have hH (S : Finset α) (hS : S ∈ H) : S.card = (t + 1) + t ∧
      ∃ U ⊆ S, U.card = t + 1 ∧ P U (S \ U) := by
    obtain ⟨hSk, hgood⟩ := Finset.mem_filter.mp hS
    have hcard := (Finset.mem_powersetCard.mp hSk).2
    obtain ⟨_, _, U, hUS, hbal, hpair⟩ := hgood
    refine ⟨by omega, U, hUS, by omega, ?_⟩
    exact hpair
  have hcount := MajorityCounting.orderedPairs_card_lower H (t + 1) t P hH
  have hcountR : (H.card : ℝ) * ((t + 1).factorial : ℝ) * (t.factorial : ℝ) ≤
      ((MajorityCounting.orderedPairs (t + 1) t P).card : ℝ) := by exact_mod_cast hcount
  let D : ℝ := ((majorityDegree T : ℝ) + 1) * (2 : ℝ) ^ majorityDegree T
  have hG : (Nat.choose (Fintype.card α) ((t + 1) + t) : ℝ) / D ≤ H.card := by
    simpa [MajorityCounting.goodCount, H, η, D, show (t + 1) + t = 2 * t + 1 by omega]
      using hdensity
  have hordered := MajorityCounting.ordered_density_lower (Fintype.card α) (t + 1) t
    (by omega) D (H.card : ℝ) ((MajorityCounting.orderedPairs (t + 1) t P).card : ℝ)
    (by dsimp [D]; positivity) hG hcountR
  have hden := majority_density_denominator hT hkm
  have hscalar : Real.exp (-300 * T ^ 2) ≤
      Real.exp (-((2 * t + 1 : ℕ) : ℝ)) / (D * (2 : ℝ) ^ (2 * t + 1)) := by
    have hi := one_div_le_one_div_of_le
      (by positivity : (0 : ℝ) < (majorityDegree T + 1 : ℝ) *
        (2 : ℝ) ^ (majorityDegree T + (2 * t + 1)) * Real.exp (2 * t + 1 : ℕ)) hden
    rw [show -300 * T ^ 2 = -(300 * T ^ 2) by ring, Real.exp_neg, ← one_div]
    calc
      _ ≤ 1 / ((majorityDegree T + 1 : ℝ) *
          (2 : ℝ) ^ (majorityDegree T + (2 * t + 1)) * Real.exp (2 * t + 1 : ℕ)) := hi
      _ = _ := by
        rw [Real.exp_neg]
        dsimp [D]
        rw [pow_add]
        field_simp
  refine ⟨t, by omega, hkm, ?_⟩
  have hscaled := mul_le_mul_of_nonneg_right hscalar
    (by positivity : (0 : ℝ) ≤ (Fintype.card α : ℝ) ^ (2 * t + 1))
  have he : (t + 1) + t = 2 * t + 1 := by omega
  rw [he] at hordered
  apply le_trans _ hordered
  simpa only [div_mul_eq_mul_div] using hscaled

end Majority
end LittlewoodInverse
