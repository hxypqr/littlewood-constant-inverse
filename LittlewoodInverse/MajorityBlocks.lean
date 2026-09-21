import LittlewoodInverse.MajorityPhase
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Order.Floor.Ring

/-! # Arbitrary blocks and the quantitative majority degree -/

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LittlewoodInverse
namespace Majority

theorem mixedMonomial_map {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (e : ι ↪ α) (S U : Finset ι) (z : α → ℂ) :
    mixedMonomial (S.map e) (U.map e) z = mixedMonomial S U (fun i ↦ z (e i)) := by
  unfold mixedMonomial
  rw [← Finset.map_sdiff]
  simp only [Finset.prod_map]

/-- The genuine large balanced-correlation property of a finite set of test indices. -/
def GoodSet {α : Type*} [DecidableEq α] (F : Circle → ℂ)
    (Φ : α → Circle → ℂ) (η : ℝ) (S : Finset α) : Prop :=
  Odd S.card ∧ 3 ≤ S.card ∧ ∃ U ⊆ S, 2 * U.card = S.card + 1 ∧
    η ≤ ‖circlePairing F (fun x ↦ mixedMonomial S U (fun i ↦ Φ i x))‖

theorem every_block_contains_good_set {α : Type*} [DecidableEq α]
    (q : ℕ) {F : Circle → ℂ} (hF : Integrable F circleMeasure)
    (Φ : α → Circle → ℂ)
    (hΦ : ∀ i, AEStronglyMeasurable (Φ i) circleMeasure)
    (hΦbound : ∀ i, ∀ᵐ x ∂circleMeasure, ‖Φ i x‖ ≤ 1)
    {κ T : ℝ} (hκ : 0 < κ) (hT : 1 ≤ T)
    (hlin : ∀ i, κ ≤ (circlePairing F (Φ i)).re)
    (hL : (∫ x, ‖F x‖ ∂circleMeasure) ≤ T * κ)
    (hm : 64 * T ^ 2 ≤ 2 * (q : ℝ) + 1)
    (B : Finset α) (hB : B.card = 2 * q + 1) :
    ∃ S ⊆ B, GoodSet F Φ (κ / (4 * (2 : ℝ) ^ (2 * q + 1))) S := by
  classical
  let e : Fin (2 * q + 1) ↪ α :=
    (B.equivFinOfCardEq hB).symm.toEmbedding.trans (Function.Embedding.subtype (· ∈ B))
  obtain ⟨S, U, hUS, hodd, h3, hbal, hpair⟩ := exists_balanced_higher_monomial_of_ratio q hF
    (fun i ↦ Φ (e i)) (fun i ↦ hΦ (e i)) (fun i ↦ hΦbound (e i)) hκ hT
    (fun i ↦ hlin (e i)) hL hm
  refine ⟨S.map e, ?_, ?_⟩
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp ha
    exact ((B.equivFinOfCardEq hB).symm i).property
  · refine ⟨by simpa using hodd, by simpa using h3, U.map e,
      Finset.map_subset_map.mpr hUS, by simpa using hbal, ?_⟩
    simpa only [mixedMonomial_map] using hpair

noncomputable def majorityHalfDegree (T : ℝ) : ℕ := ⌈(64 * T ^ 2 - 1) / 2⌉₊

noncomputable def majorityDegree (T : ℝ) : ℕ := 2 * majorityHalfDegree T + 1

theorem majorityDegree_odd (T : ℝ) : Odd (majorityDegree T) :=
  ⟨majorityHalfDegree T, rfl⟩

theorem majorityDegree_lower (T : ℝ) : 64 * T ^ 2 ≤ (majorityDegree T : ℝ) := by
  have hh := Nat.le_ceil ((64 * T ^ 2 - 1) / 2)
  unfold majorityDegree majorityHalfDegree
  push_cast
  linarith

theorem majorityDegree_upper {T : ℝ} (hT : 1 ≤ T) :
    (majorityDegree T : ℝ) < 64 * T ^ 2 + 2 := by
  have ht : 0 ≤ (64 * T ^ 2 - 1) / 2 := by nlinarith
  have hh := Nat.ceil_lt_add_one ht
  unfold majorityDegree majorityHalfDegree
  push_cast
  linarith

theorem majorityDegree_le_sixty_six {T : ℝ} (hT : 1 ≤ T) :
    (majorityDegree T : ℝ) ≤ 66 * T ^ 2 := by
  have hh := majorityDegree_upper hT
  nlinarith

theorem majorityDegree_minimal (T : ℝ) (n : ℕ) (hn : Odd n)
    (hsize : 64 * T ^ 2 ≤ (n : ℝ)) : majorityDegree T ≤ n := by
  obtain ⟨q, rfl⟩ := hn
  have hq : (64 * T ^ 2 - 1) / 2 ≤ (q : ℝ) := by
    push_cast at hsize
    linarith
  have hc : majorityHalfDegree T ≤ q := Nat.ceil_le.mpr hq
  unfold majorityDegree
  omega

theorem majority_correlation_threshold {T κ : ℝ} (hT : 1 ≤ T) (hκ : 0 ≤ κ) :
    Real.exp (-300 * T ^ 2) * κ ≤ κ / (4 * (2 : ℝ) ^ majorityDegree T) := by
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hlog4 : Real.log 4 ≤ 3 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    norm_num at hh ⊢
    exact hh
  have hlog : Real.log (4 * (2 : ℝ) ^ majorityDegree T) ≤ 300 * T ^ 2 := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have hm := majorityDegree_le_sixty_six hT
    have hh := mul_le_mul_of_nonneg_left hlog2
      (Nat.cast_nonneg (majorityDegree T) : (0 : ℝ) ≤ majorityDegree T)
    nlinarith
  have he := Real.le_exp_of_log_le hlog
  have hi : Real.exp (-300 * T ^ 2) ≤ 1 / (4 * (2 : ℝ) ^ majorityDegree T) := by
    rw [show -300 * T ^ 2 = -(300 * T ^ 2) by ring, Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) he
  have hh := mul_le_mul_of_nonneg_right hi hκ
  simpa only [one_div_mul_eq_div] using hh

/-- The exponential denominator needed when converting good subsets with one
balanced orientation into ordered tuples. -/
theorem majority_density_denominator {T : ℝ} (hT : 1 ≤ T)
    {k : ℕ} (hk : k ≤ majorityDegree T) :
    (majorityDegree T + 1 : ℝ) * (2 : ℝ) ^ (majorityDegree T + k) *
      Real.exp (k : ℝ) ≤ Real.exp (300 * T ^ 2) := by
  apply Real.le_exp_of_log_le
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp,
    Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hlogm := Real.log_le_sub_one_of_pos
    (by positivity : (0 : ℝ) < majorityDegree T + 1)
  have hm := majorityDegree_le_sixty_six hT
  have hk' : (k : ℝ) ≤ majorityDegree T := by exact_mod_cast hk
  have hh := mul_le_mul_of_nonneg_left hlog2
    (by positivity : (0 : ℝ) ≤ majorityDegree T + k)
  push_cast at hh ⊢
  nlinarith

theorem norm_circlePairing_le_integral_norm {F Φ : Circle → ℂ}
    (hF : Integrable F circleMeasure)
    (hΦ : AEStronglyMeasurable Φ circleMeasure)
    (hΦbound : ∀ᵐ x ∂circleMeasure, ‖Φ x‖ ≤ 1) :
    ‖circlePairing F Φ‖ ≤ ∫ x, ‖F x‖ ∂circleMeasure := by
  have hi : Integrable (fun x ↦ F x * conj (Φ x)) circleMeasure := by
    apply hF.mul_bdd (Complex.continuous_conj.comp_aestronglyMeasurable hΦ)
    simpa only [Complex.norm_conj] using hΦbound
  calc
    _ ≤ ∫ x, ‖F x * conj (Φ x)‖ ∂circleMeasure := norm_integral_le_integral_norm _
    _ ≤ _ := by
      apply integral_mono_ae hi.norm hF.norm
      filter_upwards [hΦbound] with x hx
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_of_le_one_right (norm_nonneg _) hx

theorem correlation_ratio_ge_one {F Φ : Circle → ℂ}
    (hF : Integrable F circleMeasure)
    (hΦ : AEStronglyMeasurable Φ circleMeasure)
    (hΦbound : ∀ᵐ x ∂circleMeasure, ‖Φ x‖ ≤ 1)
    {κ : ℝ} (hκ : 0 < κ) (hlin : κ ≤ (circlePairing F Φ).re) :
    1 ≤ (∫ x, ‖F x‖ ∂circleMeasure) / κ := by
  rw [le_div_iff₀ hκ, one_mul]
  exact hlin.trans ((Complex.re_le_norm _).trans
    (norm_circlePairing_le_integral_norm hF hΦ hΦbound))

end Majority
end LittlewoodInverse
