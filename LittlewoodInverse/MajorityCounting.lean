import Mathlib

open scoped BigOperators

namespace LittlewoodInverse
namespace MajorityCounting

/-- The elementary binomial pigeonhole step in majority amplification. -/
theorem density_of_incidence (r m : ℕ) (g : ℕ → ℕ) (hm : m ≤ r)
    (hinc : r.choose m ≤ ∑ k ∈ Finset.range (m + 1), g k * (r - k).choose (m - k)) :
    ∃ k ≤ m, r.choose k ≤ ((m + 1) * 2 ^ m) * g k := by
  by_contra! h
  have hpoint (k : ℕ) (hk : k ∈ Finset.range (m + 1)) :
      ((m + 1) * 2 ^ m) * (g k * (r - k).choose (m - k)) < r.choose m * 2 ^ m := by
    have hkm : k ≤ m := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
    have hc : 0 < (r - k).choose (m - k) := Nat.choose_pos (by omega)
    have hmul := Nat.mul_lt_mul_of_pos_right (h k hkm) hc
    have he := Nat.choose_mul (n := r) (k := m) (s := k) hkm
    have hu := Nat.mul_le_mul_left (r.choose m) (Nat.choose_le_two_pow m k)
    rw [he] at hu
    calc
      _ = (((m + 1) * 2 ^ m) * g k) * (r - k).choose (m - k) := by ring
      _ < r.choose k * (r - k).choose (m - k) := hmul
      _ ≤ _ := hu
  have hsum := Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (by omega)) hpoint
  rw [← Finset.mul_sum] at hsum
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hsum
  have hlo := Nat.mul_le_mul_left ((m + 1) * 2 ^ m) hinc
  have he : (m + 1) * (r.choose m * 2 ^ m) = ((m + 1) * 2 ^ m) * r.choose m := by ring
  rw [he] at hsum
  exact (not_lt_of_ge hlo) hsum

variable {α : Type*} [DecidableEq α]

attribute [local instance] Classical.propDecidable

noncomputable def goodFamily (V : Finset α) (Good : Finset α → Prop) (m : ℕ) : Finset (Finset α) :=
  V.powerset.filter (fun S => Good S ∧ S.card ≤ m)

noncomputable def goodCount (V : Finset α) (Good : Finset α → Prop) (k : ℕ) : ℕ :=
  ((V.powersetCard k).filter Good).card

omit [DecidableEq α] in
theorem goodFamily_fiber (V : Finset α) (Good : Finset α → Prop) (m k : ℕ) (hk : k ≤ m) :
    (goodFamily V Good m).filter (fun S => S.card = k) = (V.powersetCard k).filter Good := by
  classical
  ext S
  simp only [goodFamily, Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨hSV, hG, hSm⟩, hSk⟩
    exact ⟨⟨hSV, hSk⟩, hG⟩
  · rintro ⟨⟨hSV, hSk⟩, hG⟩
    exact ⟨⟨hSV, hG, by omega⟩, hSk⟩

/-- Count incidences between all `m`-subsets and their good witnesses. -/
theorem good_incidence_lower (V : Finset α) (Good : Finset α → Prop) (m : ℕ)
    (hcover : ∀ B ∈ V.powersetCard m, ∃ S ⊆ B, Good S) :
    V.card.choose m ≤ ∑ k ∈ Finset.range (m + 1),
      goodCount V Good k * (V.card - k).choose (m - k) := by
  classical
  let H := goodFamily V Good m
  let C : Finset α → Finset (Finset α) := fun S => (V.powersetCard m).filter (S ⊆ ·)
  have hcover' : V.powersetCard m ⊆ H.biUnion C := by
    intro B hB
    obtain ⟨S, hSB, hGood⟩ := hcover B hB
    rcases Finset.mem_powersetCard.mp hB with ⟨hBV, hcard⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨S, ?_, ?_⟩
    · simp only [H, goodFamily, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hSB.trans hBV, hGood, hcard ▸ Finset.card_le_card hSB⟩
    · exact Finset.mem_filter.mpr ⟨hB, hSB⟩
  have hcount : V.card.choose m ≤ ∑ S ∈ H, (C S).card := by
    calc
      _ = (V.powersetCard m).card := (Finset.card_powersetCard _ _).symm
      _ ≤ (H.biUnion C).card := Finset.card_le_card hcover'
      _ ≤ _ := Finset.card_biUnion_le
  have hC (S : Finset α) (hS : S ∈ H) : (C S).card =
      (V.card - S.card).choose (m - S.card) := by
    rcases Finset.mem_filter.mp hS with ⟨hSV, hG, hSm⟩
    exact Finset.card_filter_powersetCard_subset S V m (Finset.mem_powerset.mp hSV) hSm
  simp_rw [Finset.sum_congr rfl hC] at hcount
  have hmap : ∀ S ∈ H, S.card ∈ Finset.range (m + 1) := by
    intro S hS
    have hs := (Finset.mem_filter.mp hS).2.2
    exact Finset.mem_range.mpr (by omega)
  have hgroup := Finset.sum_fiberwise_of_maps_to' hmap
    (fun k => (V.card - k).choose (m - k))
  rw [← hgroup] at hcount
  have heq : (∑ k ∈ Finset.range (m + 1),
      ∑ S ∈ H with S.card = k, (V.card - k).choose (m - k)) =
      ∑ k ∈ Finset.range (m + 1), goodCount V Good k * (V.card - k).choose (m - k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_const, smul_eq_mul]
    congr 1
    exact congrArg Finset.card (goodFamily_fiber V Good m k (by
      simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk))
  rw [heq] at hcount
  exact hcount

/-- A common odd subset size occurs with an exponential-in-`m` density,
uniformly in the size of the ambient set. -/
theorem exists_dense_good_size (V : Finset α) (Good : Finset α → Prop) (m : ℕ)
    (hm : m ≤ V.card) (hshape : ∀ S, Good S → Odd S.card ∧ 3 ≤ S.card)
    (hcover : ∀ B ∈ V.powersetCard m, ∃ S ⊆ B, Good S) :
    ∃ k, Odd k ∧ 3 ≤ k ∧ k ≤ m ∧
      (V.card.choose k : ℝ) / (((m : ℝ) + 1) * (2 : ℝ)^m) ≤ goodCount V Good k := by
  obtain ⟨k, hkm, hdensity⟩ := density_of_incidence V.card m (goodCount V Good) hm
    (good_incidence_lower V Good m hcover)
  have hpos : 0 < goodCount V Good k := by
    have hp := Nat.choose_pos (show k ≤ V.card by omega)
    by_contra! hzero
    rw [show goodCount V Good k = 0 by omega] at hdensity
    omega
  obtain ⟨S, hS⟩ := Finset.card_pos.mp hpos
  rcases Finset.mem_filter.mp hS with ⟨hSk, hGood⟩
  have hcard := (Finset.mem_powersetCard.mp hSk).2
  have hshapeS := hshape S hGood
  refine ⟨k, hcard ▸ hshapeS.1, hcard ▸ hshapeS.2, hkm, ?_⟩
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((m : ℝ) + 1) * (2 : ℝ)^m)).mpr
  have hR : (V.card.choose k : ℝ) ≤ (((m : ℝ) + 1) * (2 : ℝ)^m) * goodCount V Good k := by
    exact_mod_cast hdensity
  simpa only [mul_comm] using hR

end MajorityCounting
end LittlewoodInverse
