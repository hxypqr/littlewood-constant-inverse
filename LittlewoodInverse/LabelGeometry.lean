import LittlewoodInverse.PacketGeometry

open scoped BigOperators

namespace LittlewoodInverse

namespace DenseBlocks

def label {β Δ : ℝ} {A : Finset ℤ} (data : DenseBlocks β Δ A)
    (i : Fin data.count) : ℤ := data.centre i / data.radius

theorem label_injective {β Δ : ℝ} {A : Finset ℤ} (data : DenseBlocks β Δ A) :
    Function.Injective data.label := by
  intro i j hij
  by_contra hne
  have hD : (0 : ℤ) < data.radius := by exact_mod_cast data.radius_pos
  have hi := Int.emod_add_mul_ediv (data.centre i) data.radius
  have hj := Int.emod_add_mul_ediv (data.centre j) data.radius
  have hi0 := Int.emod_nonneg (data.centre i) hD.ne'
  have hj0 := Int.emod_nonneg (data.centre j) hD.ne'
  have hiD := Int.emod_lt_of_pos (data.centre i) hD
  have hjD := Int.emod_lt_of_pos (data.centre j) hD
  change data.centre i / data.radius = data.centre j / data.radius at hij
  rw [hij] at hi
  have hc : |data.centre i - data.centre j| ≤ data.radius := by
    apply abs_le.mpr
    constructor <;> omega
  have hs := data.separated i j hne
  omega

end DenseBlocks

theorem list_floor_error (D : ℤ) (hD : 0 < D) (xs : List ℤ) :
    0 ≤ xs.sum - D * (xs.map (fun x => x / D)).sum ∧
      xs.sum - D * (xs.map (fun x => x / D)).sum ≤ (xs.length : ℤ) * D := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have he := Int.emod_add_mul_ediv x D
    have h0 := Int.emod_nonneg x hD.ne'
    have hlt := Int.emod_lt_of_pos x hD
    simp only [List.sum_cons, List.map_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    constructor <;> nlinarith

/-- The bounded carry in Section 6: floor labels preserve an approximate
balanced relation up to an explicitly bounded integer error. -/
theorem bounded_floor_carry (D : ℤ) (hD : 0 < D) (p m : List ℤ) (b : ℤ)
    (k : ℕ) (hk : 2 ≤ k) (hlen : p.length + m.length = k)
    (hclose : |p.sum - m.sum - b| ≤ (2 * (k : ℤ) + 1) * D) :
    |(p.map (fun x => x / D)).sum - (m.map (fun x => x / D)).sum - b / D| ≤ 4 * (k : ℤ) := by
  have hp := list_floor_error D hD p
  have hm := list_floor_error D hD m
  have hb := Int.emod_add_mul_ediv b D
  have hb0 := Int.emod_nonneg b hD.ne'
  have hbD := Int.emod_lt_of_pos b hD
  have hl : (p.length : ℤ) + (m.length : ℤ) = k := by exact_mod_cast hlen
  have hkl : (2 : ℤ) ≤ k := by exact_mod_cast hk
  have hp0 : (0 : ℤ) ≤ p.length := Int.natCast_nonneg _
  have hm0 : (0 : ℤ) ≤ m.length := Int.natCast_nonneg _
  have hsmall : (3 * (k : ℤ) + 2) * D ≤ 4 * (k : ℤ) * D := by nlinarith
  apply abs_le.mpr
  constructor
  · apply (mul_le_mul_iff_of_pos_left hD).mp
    have hbound := (abs_le.mp hclose).1
    nlinarith [mul_nonneg hp0 hD.le, mul_nonneg hm0 hD.le]
  · apply (mul_le_mul_iff_of_pos_left hD).mp
    have hbound := (abs_le.mp hclose).2
    nlinarith [mul_nonneg hp0 hD.le, mul_nonneg hm0 hD.le]

end LittlewoodInverse
