import LittlewoodInverse.AssemblyBudget

open scoped BigOperators

namespace LittlewoodInverse

/-- The two-stage deletion in Section 8, stated for the actual disjoint leaves. -/
theorem assembly_retained_leaves {β Δ : ℝ} {A : Finset ℤ}
    (L : AssemblyLeafFamily β Δ A) [DecidableEq L.Index] {K θ δ : ℝ}
    (hθ : 0 < θ) (hδ : 0 ≤ δ) (hN : 1 < (A.card : ℝ))
    (hnorm : littlewoodNorm A ≤ K * Real.log (A.card : ℝ)) :
    ∃ s : Finset L.Index,
      (∀ i ∈ s, δ * (A.card : ℝ) ≤ ((L.leaf i).card : ℝ)) ∧
      (s.card : ℝ) ≤ (K / (mpsConstant * θ)) ^ 20 ∧
      (∑ i ∈ Finset.univ \ s, ((L.leaf i).card : ℝ)) ≤
        (A.card : ℝ) ^ θ * (K * Real.log (A.card : ℝ)) ^ 20 +
          δ * (A.card : ℝ) * (K / (mpsConstant * θ)) ^ 20 := by
  classical
  let w (i : L.Index) : ℝ := (L.leaf i).card
  let big := Finset.univ.filter (fun i => (A.card : ℝ) ^ θ ≤ w i)
  let small := Finset.univ.filter (fun i => w i < (A.card : ℝ) ^ θ)
  let medium := big.filter (fun i => w i < δ * (A.card : ℝ))
  let s := big.filter (fun i => δ * (A.card : ℝ) ≤ w i)
  have hbig : (big.card : ℝ) ≤ (K / (mpsConstant * θ)) ^ 20 :=
    L.large_leaf_count_le hθ hN hnorm big (fun i hi => (Finset.mem_filter.mp hi).2)
  have hs : s ⊆ big := Finset.filter_subset _ _
  refine ⟨s, fun i hi => (Finset.mem_filter.mp hi).2,
    (Nat.cast_le.mpr (Finset.card_le_card hs)).trans hbig, ?_⟩
  have heq : Finset.univ \ s = small ∪ medium := by
    ext i
    simp only [s, small, medium, big, Finset.mem_sdiff, Finset.mem_univ,
      Finset.mem_filter, Finset.mem_union, true_and]
    by_cases h1 : (A.card : ℝ) ^ θ ≤ w i <;>
      by_cases h2 : δ * (A.card : ℝ) ≤ w i <;> simp_all
  have hdisj : Disjoint small medium := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hlt := (Finset.mem_filter.mp hi).2
    have hge := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
    exact not_lt_of_ge hge hlt
  have hsmall : (∑ i ∈ small, w i) ≤
      (A.card : ℝ) ^ θ * (K * Real.log (A.card : ℝ)) ^ 20 :=
    L.small_leaf_mass_log_bound hnorm small (fun i hi => (Finset.mem_filter.mp hi).2)
  have hmedium : (∑ i ∈ medium, w i) ≤
      δ * (A.card : ℝ) * (K / (mpsConstant * θ)) ^ 20 := by
    calc
      _ ≤ ∑ _i ∈ medium, δ * (A.card : ℝ) :=
        Finset.sum_le_sum fun i hi => (Finset.mem_filter.mp hi).2.le
      _ = δ * (A.card : ℝ) * medium.card := by simp [mul_comm]
      _ ≤ δ * (A.card : ℝ) * big.card := mul_le_mul_of_nonneg_left
        (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hbig (by positivity)
  rw [heq, Finset.sum_union hdisj]
  exact add_le_add hsmall hmedium

end LittlewoodInverse
