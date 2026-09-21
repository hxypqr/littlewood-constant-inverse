import LittlewoodInverse.BooleanMajority

/-! # Nonlinear correlation extraction from the actual Boolean majority polynomial -/

open scoped BigOperators
open MeasureTheory

namespace LittlewoodInverse
namespace Majority

theorem sum_singleton_coefficients (q : ℕ) (J : Finset (Fin (2 * q + 1)) → ℝ) :
    (∑ S ∈ (Finset.univ : Finset (Finset (Fin (2 * q + 1)))).filter (fun S ↦ S.card = 1),
      coefficient S * J S) =
        ((Nat.centralBinom q : ℝ) / (4 : ℝ) ^ q) * ∑ i, J {i} := by
  have he : (Finset.univ : Finset (Finset (Fin (2 * q + 1)))).filter (fun S ↦ S.card = 1) =
      (Finset.univ : Finset (Fin (2 * q + 1))).powersetCard 1 := by
    ext S
    simp
  rw [he, Finset.powersetCard_one, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, coefficient_singleton, Finset.mul_sum]

/-- Pure finite-dimensional extraction: if the actual majority polynomial has
a small total correlation but all linear correlations are positive, then a
genuine odd higher-degree monomial has large correlation. -/
theorem exists_higher_correlation (q : ℕ) (J : Finset (Fin (2 * q + 1)) → ℝ)
    {κ L : ℝ} (hκ : 0 < κ)
    (hlin : ∀ i, κ ≤ J {i})
    (htotal : |∑ S : Finset (Fin (2 * q + 1)), coefficient S * J S| ≤ L)
    (hbudget : L + 2 * κ ≤ (2 * (q : ℝ) + 1) *
      ((Nat.centralBinom q : ℝ) / (4 : ℝ) ^ q) * κ) :
    ∃ S : Finset (Fin (2 * q + 1)), Odd S.card ∧ 3 ≤ S.card ∧
      κ / (2 : ℝ) ^ (2 * q + 1) ≤ |J S| := by
  classical
  by_contra hnone
  push Not at hnone
  let a : ℝ := (Nat.centralBinom q : ℝ) / (4 : ℝ) ^ q
  let δ : ℝ := κ / (2 : ℝ) ^ (2 * q + 1)
  let R : Finset (Finset (Fin (2 * q + 1))) := Finset.univ.filter (fun S ↦ S.card ≠ 1)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hm : Odd (2 * q + 1) := ⟨q, by omega⟩
  have hterm (S : Finset (Fin (2 * q + 1))) (hS : S ∈ R) :
      |coefficient S * J S| ≤ |coefficient S| * δ := by
    by_cases heven : Even S.card
    · rw [coefficient_even_eq_zero hm S heven]
      simp
    · have hodd : Odd S.card := Nat.not_even_iff_odd.mp heven
      have hne : S.card ≠ 1 := (Finset.mem_filter.mp hS).2
      have hthree : 3 ≤ S.card := by obtain ⟨k, hk⟩ := hodd; omega
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hnone S hodd hthree).le (abs_nonneg _)
  have hhigh : |∑ S ∈ R, coefficient S * J S| ≤ κ := by
    calc
      _ ≤ ∑ S ∈ R, |coefficient S * J S| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ S ∈ R, |coefficient S| * δ := Finset.sum_le_sum hterm
      _ ≤ ∑ S : Finset (Fin (2 * q + 1)), |coefficient S| * δ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun S _ _ ↦ mul_nonneg (abs_nonneg _) hδ)
      _ = (∑ S : Finset (Fin (2 * q + 1)), |coefficient S|) * δ :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ (2 : ℝ) ^ (2 * q + 1) * δ := mul_le_mul_of_nonneg_right coefficient_mass_le hδ
      _ = κ := by dsimp [δ]; field_simp
  have hlinear : (2 * (q : ℝ) + 1) * a * κ ≤ a * ∑ i, J {i} := by
    have hs : (2 * (q : ℝ) + 1) * κ ≤ ∑ i : Fin (2 * q + 1), J {i} := by
      calc
        _ = ∑ _i : Fin (2 * q + 1), κ := by simp
        _ ≤ _ := Finset.sum_le_sum (fun i _ ↦ hlin i)
    have ha : 0 ≤ a := by dsimp [a]; positivity
    nlinarith [mul_le_mul_of_nonneg_left hs ha]
  have hsplit : (∑ S : Finset (Fin (2 * q + 1)), coefficient S * J S) =
      a * (∑ i, J {i}) + ∑ S ∈ R, coefficient S * J S := by
    have hh := Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset (Finset (Fin (2 * q + 1))))
      (fun S ↦ S.card = 1) (fun S ↦ coefficient S * J S)
    rw [sum_singleton_coefficients] at hh
    exact hh.symm
  rw [hsplit] at htotal
  have h1 := (abs_le.mp htotal).2
  have h2 := (abs_le.mp hhigh).1
  change L + 2 * κ ≤ (2 * (q : ℝ) + 1) * a * κ at hbudget
  linarith

theorem abs_finset_prod_le_one {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, |f i| ≤ 1) : |∏ i ∈ S, f i| ≤ 1 := by
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ _i ∈ S, (1 : ℝ) :=
      Finset.prod_le_prod (fun i _ ↦ abs_nonneg (f i)) hf
    _ = 1 := by simp

theorem exists_higher_integral {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (q : ℕ) (H : α → ℝ) (hH : Integrable H μ) (ψ : Fin (2 * q + 1) → α → ℝ)
    (hψ : ∀ i, AEStronglyMeasurable (ψ i) μ)
    (hψbound : ∀ᵐ x ∂μ, ∀ i, |ψ i x| ≤ 1)
    {κ : ℝ} (hκ : 0 < κ) (hlin : ∀ i, κ ≤ ∫ x, H x * ψ i x ∂μ)
    (hbudget : (∫ x, |H x| ∂μ) + 2 * κ ≤ (2 * (q : ℝ) + 1) *
      ((Nat.centralBinom q : ℝ) / (4 : ℝ) ^ q) * κ) :
    ∃ S : Finset (Fin (2 * q + 1)), Odd S.card ∧ 3 ≤ S.card ∧
      κ / (2 : ℝ) ^ (2 * q + 1) ≤ |∫ x, H x * ∏ i ∈ S, ψ i x ∂μ| := by
  let J : Finset (Fin (2 * q + 1)) → ℝ := fun S ↦ ∫ x, H x * ∏ i ∈ S, ψ i x ∂μ
  have hmon (S : Finset (Fin (2 * q + 1))) :
      Integrable (fun x ↦ H x * ∏ i ∈ S, ψ i x) μ := by
    apply hH.mul_bdd (S.aestronglyMeasurable_fun_prod (fun i _ ↦ hψ i))
    filter_upwards [hψbound] with x hx
    exact abs_finset_prod_le_one S (fun i ↦ ψ i x) (fun i _ ↦ hx i)
  have hpolymeas : AEStronglyMeasurable (fun x ↦ polynomial (fun i ↦ ψ i x)) μ := by
    unfold polynomial
    apply Finset.aestronglyMeasurable_fun_sum
    intro S hS
    exact (S.aestronglyMeasurable_fun_prod (fun i _ ↦ hψ i)).const_mul _
  have hpolybound : ∀ᵐ x ∂μ, |polynomial (fun i ↦ ψ i x)| ≤ 1 :=
    hψbound.mono fun x hx ↦ polynomial_abs_le_one hx
  have hpoly : Integrable (fun x ↦ H x * polynomial (fun i ↦ ψ i x)) μ :=
    hH.mul_bdd hpolymeas hpolybound
  have he : (∑ S : Finset (Fin (2 * q + 1)), coefficient S * J S) =
      ∫ x, H x * polynomial (fun i ↦ ψ i x) ∂μ := by
    unfold polynomial
    simp only [Finset.mul_sum]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro S hS
      have hp (x : α) : H x * (coefficient S * ∏ i ∈ S, ψ i x) =
          coefficient S * (H x * ∏ i ∈ S, ψ i x) := by ring
      simp only [hp, integral_const_mul, J]
    · intro S hS
      convert (hmon S).const_mul (coefficient S) using 1
      ext x
      ring
  refine exists_higher_correlation q J hκ ?_ ?_ hbudget
  · intro i
    simpa only [J, Finset.prod_singleton] using hlin i
  · rw [he]
    calc
      _ ≤ ∫ x, |H x * polynomial (fun i ↦ ψ i x)| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, |H x| ∂μ := by
        apply integral_mono_ae hpoly.abs hH.abs
        filter_upwards [hpolybound] with x hx
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) hx

end Majority
end LittlewoodInverse
