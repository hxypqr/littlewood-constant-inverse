import LittlewoodInverse.PacketCertificates
import LittlewoodInverse.MPSConsequences

open MeasureTheory

namespace LittlewoodInverse
namespace DenseBlocks

noncomputable def certificateBudget (K β : ℝ) : ℝ := max 1 (3*K/(mpsConstant*β))

theorem certificateBudget_ge_one (K β : ℝ) : 1 ≤ certificateBudget K β := le_max_left _ _

/-- The low norm hypothesis gives a fixed majority-amplification budget,
uniform over the number, diameter, and positions of the actual blocks. -/
theorem uniform_certificate_budget {β Δ K : ℝ} {A : Finset ℤ}
    (data : DenseBlocks β Δ A) (hβ : 0 < β) (hA : 2 ≤ A.card)
    (hnorm : littlewoodNorm A ≤ K*Real.log (A.card : ℝ)) :
    ∃ κ : ℝ, 0 < κ ∧
      (∀ i, κ ≤ (circlePairing (fourierPolynomial A) (data.certificate i)).re) ∧
      littlewoodNorm A ≤ certificateBudget K β * κ := by
  have hN : (1 : ℝ) < A.card := by exact_mod_cast hA
  have hN0 : (0 : ℝ) < A.card := by linarith
  have hlog : 0 < Real.log (A.card : ℝ) := Real.log_pos hN
  let κ := mpsConstant*β*Real.log (A.card : ℝ)/3
  have hκ : 0 < κ := by dsimp only [κ]; positivity [mpsConstant_pos]
  refine ⟨κ,hκ,?_,?_⟩
  · intro i
    have hsize : (A.card : ℝ)^β ≤ ((data.block i).card : ℝ)+1 := by
      have hh : (data.minSize : ℝ) ≤ (data.block i).card := by
        exact_mod_cast data.block_size i
      linarith [data.density]
    have hl := Real.log_le_log (Real.rpow_pos_of_pos hN0 β) hsize
    rw [Real.log_rpow hN0] at hl
    have hm := (mul_le_mul_of_nonneg_left hl mpsConstant_pos.le).trans
      (mpsConstant_log_le (data.block i))
    rw [data.certificate_pairing, Complex.ofReal_re]
    dsimp only [κ]
    nlinarith
  · calc
      _ ≤ K*Real.log (A.card : ℝ) := hnorm
      _ = (3*K/(mpsConstant*β))*κ := by
        dsimp only [κ]
        field_simp [mpsConstant_pos.ne', hβ.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hκ.le

end DenseBlocks
end LittlewoodInverse
