import LittlewoodInverse.BackgroundExternal
import LittlewoodInverse.CyclicSpectral

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LittlewoodInverse.BackgroundExternal

theorem zmodAddEquiv_apply_eq (q : ℕ) [NeZero q] (r x : ZMod q) :
    AddChar.zmodAddEquiv r x = cyclicCharacter q r x := by
  rfl

theorem finiteAlgebraNorm_indicator (q : ℕ) [NeZero q] (X : Finset (ZMod q)) :
    finiteAlgebraNorm (setIndicator X) = cyclicLittlewoodNorm q X := by
  classical
  unfold finiteAlgebraNorm
  rw [← (AddChar.zmodAddEquiv (n := q)).toEquiv.sum_comp]
  simp only [norm_mul, norm_inv, Complex.norm_natCast, ZMod.card]
  rw [← Finset.mul_sum]
  unfold cyclicLittlewoodNorm
  rw [integral_cyclicMeasure]
  simp only [smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  change ‖∑ x : ZMod q, (setIndicator X x : ℂ) * conj (cyclicCharacter q r x)‖ = _
  have he : (∑ x : ZMod q, (setIndicator X x : ℂ) * conj (cyclicCharacter q r x)) =
      conj (cyclicPolynomial q X (fun _ => 1) r) := by
    simp only [cyclicPolynomial, map_sum, one_mul]
    simp only [setIndicator, Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
    apply Finset.sum_congr rfl
    intro x _
    simp only [cyclicCharacter, mul_comm]
  rw [he, Complex.norm_conj]

/-- The actual cyclic spectral norm supplies the hypothesis of the general
Green--Sanders theorem, uniformly in the modulus. -/
theorem green_sanders_cyclic_cosets (M : ℝ) (hM : 0 ≤ M) :
    ∃ B : ℝ, 0 < B ∧ ∀ (q : ℕ) [NeZero q] (X : Finset (ZMod q)),
      cyclicLittlewoodNorm q X ≤ M →
      ∃ (L : ℕ) (sign : Fin L → ℤ) (a : Fin L → ZMod q)
        (H : Fin L → AddSubgroup (ZMod q)),
        (∀ j, sign j = 1 ∨ sign j = -1) ∧
        (∀ x, setIndicator X x = ∑ j, sign j * cosetIndicator (H j) (a j) x) ∧
        (L : ℝ) ≤ B := by
  obtain ⟨C, _, hGS⟩ := green_sanders
  refine ⟨Real.exp (Real.exp (C * M ^ 4)), Real.exp_pos _, fun q _ X hX => ?_⟩
  obtain ⟨L, sign, a, H, hs, he, hL, _⟩ := hGS (setIndicator X) M hM
    (by simpa only [finiteAlgebraNorm_indicator] using hX)
  exact ⟨L, sign, a, H, hs, he, hL⟩

end LittlewoodInverse.BackgroundExternal
