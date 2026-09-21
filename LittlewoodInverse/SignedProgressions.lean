import LittlewoodInverse.CosetLift
import LittlewoodInverse.FiniteCoverGluing

open scoped BigOperators

namespace LittlewoodInverse

/-- An exact signed progression representation. The lengths may be large,
and cancellation between different progressions is explicitly allowed. -/
structure SignedProgressionData (A : Finset ℤ) where
  Index : Type
  [indexFintype : Fintype Index]
  sign : Index → ℤ
  start : Index → ℤ
  step : Index → ℕ
  length : Index → ℕ
  sign_one : ∀ i, sign i = 1 ∨ sign i = -1
  step_pos : ∀ i, 0 < step i
  identity : ∀ z : ℤ, (if z ∈ A then 1 else 0 : ℤ) =
    ∑ i, sign i*(if z ∈ integerProgression (start i) (step i) (length i) then 1 else 0)

attribute [instance] SignedProgressionData.indexFintype

theorem FiniteSetPartition.sum_indicator {A : Finset ℤ} (P : FiniteSetPartition A) (z : ℤ) :
    (∑ i, if z ∈ P.part i then 1 else 0 : ℤ) = if z ∈ A then 1 else 0 := by
  classical
  by_cases hz : z ∈ A
  · obtain ⟨i,hi⟩ := (P.covers z).mp hz
    rw [if_pos hz, Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hji
      have hj : z ∉ P.part j := fun hj => Finset.disjoint_left.mp (P.disjoint hji) hj hi
      simp [hj]
    · simp
  · have hi (i : P.Index) : z ∉ P.part i := fun hi => hz (P.part_subset i hi)
    simp [hz,hi]

/-- Disjoint slab representations combine without changing their signs. -/
noncomputable def SignedProgressionData.glue {A : Finset ℤ} (P : FiniteSetPartition A)
    (D : ∀ i, SignedProgressionData (P.part i)) : SignedProgressionData A where
  Index := (i : P.Index) × (D i).Index
  sign i := (D i.1).sign i.2
  start i := (D i.1).start i.2
  step i := (D i.1).step i.2
  length i := (D i.1).length i.2
  sign_one i := (D i.1).sign_one i.2
  step_pos i := (D i.1).step_pos i.2
  identity z := by
    classical
    rw [Fintype.sum_sigma]
    simp_rw [← SignedProgressionData.identity]
    exact (P.sum_indicator z).symm

theorem signed_progression_glue_bound {A : Finset ℤ} (P : FiniteSetPartition A)
    (v B : ℝ) (hB : 0 ≤ B) (hv : (Fintype.card P.Index : ℝ) ≤ v)
    (hparts : ∀ i, ∃ D : SignedProgressionData (P.part i), (Fintype.card D.Index : ℝ) ≤ B) :
    ∃ D : SignedProgressionData A, (Fintype.card D.Index : ℝ) ≤ v*B := by
  classical
  choose D hD using hparts
  refine ⟨SignedProgressionData.glue P D, ?_⟩
  change ((Fintype.card ((i : P.Index) × (D i).Index)) : ℝ) ≤ _
  rw [Fintype.card_sigma, Nat.cast_sum]
  calc
    _ ≤ ∑ _i : P.Index, B := Finset.sum_le_sum fun i _ => hD i
    _ = (Fintype.card P.Index : ℝ)*B := by simp
    _ ≤ v*B := mul_le_mul_of_nonneg_right hv hB

end LittlewoodInverse
