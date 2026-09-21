import LittlewoodInverse.CarryLift
import LittlewoodInverse.ResidueProjection

open scoped BigOperators

namespace LittlewoodInverse

noncomputable def integerProgression (a d : ℤ) (L : ℕ) : Finset ℤ :=
  (Finset.range L).image (fun k : ℕ => a+d*(k : ℤ))

noncomputable def canonicalResidueCoset (d s r : ℕ) : Finset (ZMod (d*s)) :=
  (Finset.range s).image (fun k => ((r+d*k : ℕ) : ZMod (d*s)))

noncomputable def cyclicProgressionCoset (q d r : ℕ) : Finset (ZMod q) :=
  (Finset.range (q/d)).image (fun k => ((r+d*k : ℕ) : ZMod q))

/-- Lifting one full cyclic coset through a consecutive vertical interval
is exactly one integer arithmetic progression. -/
theorem canonical_coset_lift (d s r : ℕ) (hd : 0 < d) (hs : 0 < s)
    (hr : r < d) (a : ℤ) (L : ℕ) :
    arithmeticSlab (d*s) (canonicalResidueCoset d s r) a L =
      integerProgression (r+(d*s : ℕ)*a) d (s*L) := by
  classical
  have hq : 0 < d*s := Nat.mul_pos hd hs
  letI : NeZero (d*s) := ⟨Nat.ne_of_gt hq⟩
  have hv (k : ℕ) (hk : k < s) :
      (((r+d*k : ℕ) : ZMod (d*s)).val : ℤ) = (r : ℤ)+(d : ℤ)*k := by
    have ht : r+d*k < d*s := by nlinarith
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt ht]
    push_cast
    rfl
  ext z
  constructor
  · intro hz
    obtain ⟨⟨x,u⟩,hxu,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hx,hu⟩ := Finset.mem_product.mp hxu
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
    have hk' := Finset.mem_range.mp hk
    obtain ⟨hu0,hu1⟩ := Finset.mem_Ico.mp hu
    have huNat : ((u-a).toNat : ℤ) = u-a := Int.toNat_of_nonneg (by omega)
    apply Finset.mem_image.mpr
    refine ⟨k+s*(u-a).toNat, Finset.mem_range.mpr ?_, ?_⟩
    · have hsub : (u-a).toNat < L := by omega
      nlinarith
    · simp only [residueHeight, hv k hk']
      push_cast
      rw [huNat]
      ring
  · intro hz
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hz
    have hm' := Finset.mem_range.mp hm
    have hmod := Nat.mod_lt m hs
    have hdiv : m/s < L := (Nat.div_lt_iff_lt_mul hs).mpr (by simpa [mul_comm] using hm')
    apply Finset.mem_image.mpr
    refine ⟨(((r+d*(m%s) : ℕ) : ZMod (d*s)),a+(m/s : ℕ)), ?_, ?_⟩
    · apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_image.mpr ⟨m%s,Finset.mem_range.mpr hmod,rfl⟩
      · apply Finset.mem_Ico.mpr
        constructor
        · have : (0 : ℤ) ≤ (m/s : ℕ) := by positivity
          linarith
        · have ht : ((m/s : ℕ) : ℤ) < (L : ℤ) := by exact_mod_cast hdiv
          dsimp only
          omega
    · simp only [residueHeight,hv (m%s) hmod]
      have hdecomp : (m : ℤ) = (m%s : ℕ)+(s : ℤ)*(m/s : ℕ) := by
        exact_mod_cast (Nat.mod_add_div m s).symm
      simp only [Nat.cast_mul]
      linear_combination -(d : ℤ)*hdecomp

theorem cyclic_coset_lift (q d r : ℕ) (hq : 0 < q) (hd : 0 < d)
    (hdq : d ∣ q) (hr : r < d) (a : ℤ) (L : ℕ) :
    arithmeticSlab q (cyclicProgressionCoset q d r) a L =
      integerProgression (r+(q : ℤ)*a) d ((q/d)*L) := by
  obtain ⟨s,rfl⟩ := hdq
  have hs : 0 < s := Nat.pos_of_mul_pos_left hq
  simpa only [cyclicProgressionCoset, canonicalResidueCoset,
    Nat.mul_div_cancel_left s hd] using canonical_coset_lift d s r hd hs hr a L

theorem mem_arithmeticSlab_iff (q : ℕ) [NeZero q] (X : Finset (ZMod q))
    (a : ℤ) (L : ℕ) (z : ℤ) :
    z ∈ arithmeticSlab q X a L ↔ (z : ZMod q) ∈ X ∧ z/(q : ℤ) ∈ Finset.Ico a (a+L) := by
  have hr : residueHeight q ((z : ZMod q), z/(q : ℤ)) = z := residue_reconstruction q z
  constructor
  · intro hz
    obtain ⟨p,hp,hpz⟩ := Finset.mem_image.mp hz
    have he := residueHeight_injective q (hpz.trans hr.symm)
    subst p
    exact Finset.mem_product.mp hp
  · intro hz
    exact Finset.mem_image.mpr ⟨((z : ZMod q), z/(q : ℤ)),Finset.mem_product.mpr hz,hr⟩

/-- Signed identities of residue indicators lift linearly, with exactly
the same number of terms and exactly the same signs. -/
theorem signed_indicator_lift (q : ℕ) [NeZero q] {n : ℕ}
    (X : Finset (ZMod q)) (Y : Fin n → Finset (ZMod q)) (c : Fin n → ℤ)
    (h : ∀ x, (if x ∈ X then 1 else 0 : ℤ) =
      ∑ i, c i*(if x ∈ Y i then 1 else 0)) (a : ℤ) (L : ℕ) (z : ℤ) :
    (if z ∈ arithmeticSlab q X a L then 1 else 0 : ℤ) =
      ∑ i, c i*(if z ∈ arithmeticSlab q (Y i) a L then 1 else 0) := by
  simp only [mem_arithmeticSlab_iff]
  by_cases hz : z/(q : ℤ) ∈ Finset.Ico a (a+L)
  · simpa only [hz,and_true] using h (z : ZMod q)
  · simp [hz]

theorem signed_progression_lift (q : ℕ) [NeZero q] {n : ℕ}
    (X : Finset (ZMod q)) (d r : Fin n → ℕ) (c : Fin n → ℤ)
    (hd : ∀ i, 0 < d i) (hdq : ∀ i, d i ∣ q) (hr : ∀ i, r i < d i)
    (h : ∀ x, (if x ∈ X then 1 else 0 : ℤ) =
      ∑ i, c i*(if x ∈ cyclicProgressionCoset q (d i) (r i) then 1 else 0))
    (a : ℤ) (L : ℕ) (z : ℤ) :
    (if z ∈ arithmeticSlab q X a L then 1 else 0 : ℤ) =
      ∑ i, c i*(if z ∈ integerProgression (r i+(q : ℤ)*a) (d i) ((q/d i)*L)
        then 1 else 0) := by
  have hh := signed_indicator_lift q X (fun i => cyclicProgressionCoset q (d i) (r i)) c h a L z
  simpa only [cyclic_coset_lift q _ _ (Nat.pos_of_ne_zero (NeZero.ne q))
    (hd _) (hdq _) (hr _)] using hh

end LittlewoodInverse
