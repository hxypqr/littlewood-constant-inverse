import LittlewoodInverse.Basic
import Mathlib

/-! # Almost-covering implies macroscopic hereditary energy

This is the finite argument in the proof of Corollary 1.6.  The covering
is an explicit input; no main inverse theorem is asserted here.
-/

open scoped BigOperators Pointwise

namespace LittlewoodInverse

theorem covering_intersection {G : Type*} [DecidableEq G]
    (A Y : Finset G) (blocks : Finset (Finset G)) (d : ℝ)
    (hYA : Y ⊆ A) (hblocks : blocks.Nonempty)
    (hmass : d * (A.card : ℝ) ≤ (Y.card : ℝ))
    (hrem : ((A \ blocks.biUnion id).card : ℝ) ≤ d * (A.card : ℝ) / 2) :
    ∃ B ∈ blocks, d * (A.card : ℝ) / (2 * (blocks.card : ℝ)) ≤
      ((Y ∩ B).card : ℝ) := by
  classical
  have hj : 0 < (blocks.card : ℝ) := by exact_mod_cast hblocks.card_pos
  have hdel : ((Y \ blocks.biUnion id).card : ℝ) ≤
      ((A \ blocks.biUnion id).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (show Y \ blocks.biUnion id ⊆ A \ blocks.biUnion id from
      fun x hx => Finset.mem_sdiff.mpr ⟨hYA (Finset.mem_sdiff.mp hx).1,
        (Finset.mem_sdiff.mp hx).2⟩)
  have hsplit : ((Y \ blocks.biUnion id).card : ℝ) +
      ((Y ∩ blocks.biUnion id).card : ℝ) = (Y.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_inter Y (blocks.biUnion id)
  have hsum : ((Y ∩ blocks.biUnion id).card : ℝ) ≤
      ∑ B ∈ blocks, ((Y ∩ B).card : ℝ) := by
    rw [Finset.inter_biUnion]
    exact_mod_cast (Finset.card_biUnion_le :
      (blocks.biUnion (fun B => Y ∩ B)).card ≤ ∑ B ∈ blocks, (Y ∩ B).card)
  apply Finset.exists_le_of_sum_le hblocks
  calc
    (∑ _ ∈ blocks, d * (A.card : ℝ) / (2 * (blocks.card : ℝ))) =
        d * (A.card : ℝ) / 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      field_simp
    _ ≤ ∑ B ∈ blocks, ((Y ∩ B).card : ℝ) := by linarith

/-- Concrete energy consequence of a covering by `J` sets with doubling `Q`.
The bound is stated without division, so all normalization factors are visible. -/
theorem energy_from_cover {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A Y : Finset G) (blocks : Finset (Finset G)) (d Q : ℝ)
    (hYA : Y ⊆ A) (hA : A.Nonempty) (hblocks : blocks.Nonempty)
    (hd : 0 ≤ d) (hQ : 0 ≤ Q)
    (hsub : ∀ B ∈ blocks, B ⊆ A)
    (hdouble : ∀ B ∈ blocks, ((sumset B).card : ℝ) ≤ Q * (B.card : ℝ))
    (hmass : d * (A.card : ℝ) ≤ (Y.card : ℝ))
    (hrem : ((A \ blocks.biUnion id).card : ℝ) ≤ d * (A.card : ℝ) / 2) :
    d^4 * (Y.card : ℝ)^3 ≤
      16 * Q * (blocks.card : ℝ)^4 * (additiveEnergy Y : ℝ) := by
  classical
  obtain ⟨B, hB, hlarge⟩ := covering_intersection A Y blocks d hYA hblocks hmass hrem
  have hn : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hj : 0 < (blocks.card : ℝ) := by exact_mod_cast hblocks.card_pos
  have hsumsub : sumset (Y ∩ B) ⊆ sumset B :=
    Finset.add_subset_add Finset.inter_subset_right Finset.inter_subset_right
  have hcardB : (B.card : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast Finset.card_le_card (hsub B hB)
  have hs : ((sumset (Y ∩ B)).card : ℝ) ≤ Q * (A.card : ℝ) := by
    calc
      _ ≤ ((sumset B).card : ℝ) := by exact_mod_cast Finset.card_le_card hsumsub
      _ ≤ Q * (B.card : ℝ) := hdouble B hB
      _ ≤ Q * (A.card : ℝ) := mul_le_mul_of_nonneg_left hcardB hQ
  have he : (additiveEnergy (Y ∩ B) : ℝ) ≤ (additiveEnergy Y : ℝ) := by
    exact_mod_cast Finset.addEnergy_mono Finset.inter_subset_left Finset.inter_subset_left
  have henergy : ((Y ∩ B).card : ℝ)^4 ≤ Q * (A.card : ℝ) * (additiveEnergy Y : ℝ) := by
    have hc : ((Y ∩ B).card : ℝ)^4 ≤
        ((sumset (Y ∩ B)).card : ℝ) * (additiveEnergy (Y ∩ B) : ℝ) := by
      exact_mod_cast card_pow_four_le_sumset_mul_energy (Y ∩ B)
    exact hc.trans (mul_le_mul hs he (by positivity) (mul_nonneg hQ hn.le))
  have hscaled : d * (A.card : ℝ) ≤
      2 * (blocks.card : ℝ) * ((Y ∩ B).card : ℝ) := by
    have := (div_le_iff₀ (show 0 < 2 * (blocks.card : ℝ) by positivity)).mp hlarge
    nlinarith
  have hp : (d * (A.card : ℝ))^4 ≤
      (2 * (blocks.card : ℝ) * ((Y ∩ B).card : ℝ))^4 := by gcongr
  have hp' : d^4 * (A.card : ℝ)^4 ≤
      16 * (blocks.card : ℝ)^4 * (Q * (A.card : ℝ) * (additiveEnergy Y : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left henergy
      (show 0 ≤ 16 * (blocks.card : ℝ)^4 by positivity)
    nlinarith [hp]
  have hbase : d^4 * (A.card : ℝ)^3 ≤
      16 * Q * (blocks.card : ℝ)^4 * (additiveEnergy Y : ℝ) := by
    apply (mul_le_mul_iff_left₀ hn).mp
    nlinarith [hp']
  have hYcard : (Y.card : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast Finset.card_le_card hYA
  calc
    _ ≤ d^4 * (A.card : ℝ)^3 := by gcongr
    _ ≤ _ := hbase

end LittlewoodInverse
