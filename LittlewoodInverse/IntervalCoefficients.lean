import LittlewoodInverse.BoundedCompositions

open scoped BigOperators

namespace LittlewoodInverse
namespace IntervalCoefficients

open IntervalMoments

theorem geometric_power_coefficient (n d s : ℕ) :
    Polynomial.coeff ((∑ i ∈ Finset.range n, (Polynomial.X : Polynomial ℕ) ^ i) ^ d) s =
      (Finset.univ.filter (fun x : Fin d → Fin n => ∑ i, (x i).val = s)).card := by
  rw [← Fin.sum_univ_eq_sum_range, Fintype.sum_pow]
  simp_rw [Finset.prod_pow_eq_pow_sum, Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow]
  simp only [Finset.sum_boole, Nat.cast_id]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_comm]

/-- The precise generating-polynomial coefficient in Proposition 3.2. -/
theorem interval_relationCount_eq_coefficient (n r : ℕ) :
    MomentCounting.relationCount (integerInterval n) r =
      Polynomial.coeff ((∑ i ∈ Finset.range n, (Polynomial.X : Polynomial ℕ) ^ i) ^ (2 * r))
        (r * (n - 1)) := by
  rw [geometric_power_coefficient, interval_relationCount_eq_middle]
  rw [show 2 * r = r + r by omega]

theorem relationCount_le_coefficient (B : Finset ℤ) (r : ℕ) :
    MomentCounting.relationCount B r ≤
      Polynomial.coeff ((∑ i ∈ Finset.range B.card, (Polynomial.X : Polynomial ℕ) ^ i) ^ (2 * r))
        (r * (B.card - 1)) := by
  rw [← interval_relationCount_eq_coefficient]
  exact relationCount_le_interval B r

end IntervalCoefficients
end LittlewoodInverse
