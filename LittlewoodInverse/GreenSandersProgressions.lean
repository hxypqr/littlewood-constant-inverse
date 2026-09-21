import LittlewoodInverse.GreenSandersCyclic
import LittlewoodInverse.CyclicCosetNormalForm

open scoped BigOperators

namespace LittlewoodInverse.BackgroundExternal

/-- The precise cyclic specialization used in the manuscript's terminal
remark. The Fourier-norm identification and canonical coset form are
proved internally, so this depends only on the general Green--Sanders
external theorem. -/
theorem green_sanders_cyclic (M : ℝ) (hM : 0 ≤ M) :
    ∃ B : ℝ, 0 < B ∧ ∀ (q : ℕ) [NeZero q] (X : Finset (ZMod q)),
      cyclicLittlewoodNorm q X ≤ M →
      ∃ (L : ℕ) (sign : Fin L → ℤ) (d r : Fin L → ℕ),
        (∀ j, sign j = 1 ∨ sign j = -1) ∧
        (∀ j, 0 < d j ∧ d j ∣ q ∧ r j < d j) ∧
        (∀ x, setIndicator X x =
          ∑ j, sign j * setIndicator (cyclicProgressionCoset q (d j) (r j)) x) ∧
        (L : ℝ) ≤ B := by
  classical
  obtain ⟨B, hB, hGS⟩ := green_sanders_cyclic_cosets M hM
  refine ⟨B, hB, fun q _ X hX => ?_⟩
  obtain ⟨L, sign, a, H, hs, he, hL⟩ := hGS q X hX
  choose d r hd hdq hr hcos using fun j => cyclic_coset_normal_form q (H j) (a j)
  refine ⟨L, sign, d, r, hs, fun j => ⟨hd j, hdq j, hr j⟩, ?_, hL⟩
  intro x
  rw [he]
  apply Finset.sum_congr rfl
  intro j _
  rw [hcos j x]

end LittlewoodInverse.BackgroundExternal
