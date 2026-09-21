import LittlewoodInverse.External
import Mathlib

open scoped BigOperators
open MeasureTheory

namespace LittlewoodInverse

theorem weightedPolynomial_sorted_ones (C : Finset ℤ) (t : Circle) :
    weightedFourierPolynomial (C.orderEmbOfFin rfl) (fun _ => 1) t =
      fourierPolynomial C t := by
  classical
  unfold weightedFourierPolynomial fourierPolynomial
  simp only [one_mul]
  apply Finset.sum_bij (fun i _ => C.orderEmbOfFin rfl i)
  · intro i _
    exact C.orderEmbOfFin_mem rfl i
  · intro i _ j _ hij
    exact (C.orderEmbOfFin rfl).injective hij
  · intro x hx
    obtain ⟨i, hi⟩ := (C.orderIsoOfFin rfl).surjective ⟨x, hx⟩
    exact ⟨i, Finset.mem_univ _, congrArg Subtype.val hi⟩
  · intro i _
    rfl

theorem sum_fin_reciprocal_eq_harmonic (m : ℕ) :
    (∑ j : Fin m, (1 : ℝ) / ((j.val : ℝ) + 1)) = (harmonic m : ℝ) := by
  simp [harmonic, ← Fin.sum_univ_eq_sum_range]

/-- The logarithmic set bound derived from the correctly weighted external MPS theorem. -/
theorem mps_logarithmic : ∃ c : ℝ, 0 < c ∧
    ∀ C : Finset ℤ, c * Real.log ((C.card : ℝ) + 1) ≤ littlewoodNorm C := by
  obtain ⟨c, hc, hmps⟩ := External.mps_weighted
  refine ⟨c, hc, fun C => ?_⟩
  have hp := hmps C.card (C.orderEmbOfFin rfl) (C.orderEmbOfFin rfl).strictMono
    (fun _ => 1)
  simp only [norm_one, sum_fin_reciprocal_eq_harmonic, weightedPolynomial_sorted_ones] at hp
  exact (mul_le_mul_of_nonneg_left (by exact_mod_cast log_add_one_le_harmonic C.card) hc.le).trans hp

noncomputable def mpsConstant : ℝ := mps_logarithmic.choose

theorem mpsConstant_pos : 0 < mpsConstant := mps_logarithmic.choose_spec.1

theorem mpsConstant_log_le (C : Finset ℤ) :
    mpsConstant * Real.log ((C.card : ℝ) + 1) ≤ littlewoodNorm C :=
  mps_logarithmic.choose_spec.2 C

end LittlewoodInverse
