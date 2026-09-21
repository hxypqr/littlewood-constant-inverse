import LittlewoodInverse.CosetLift
import LittlewoodInverse.BackgroundExternal
import Mathlib.GroupTheory.Archimedean

namespace LittlewoodInverse

theorem mem_cyclicProgressionCoset (q d r : ℕ) [NeZero q] (hd : 0 < d)
    (hdq : d ∣ q) (hr : r < d) (x : ZMod q) :
    x ∈ cyclicProgressionCoset q d r ↔ x.val % d = r := by
  classical
  have hmul : d * (q / d) = q := Nat.mul_div_cancel' hdq
  constructor
  · rintro hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    have hk' : k < q / d := Finset.mem_range.mp hk
    have hlt : r + d * k < q := by nlinarith
    rw [ZMod.val_natCast_of_lt hlt]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hr]
  · intro hx
    apply Finset.mem_image.mpr
    refine ⟨x.val / d, Finset.mem_range.mpr ?_, ?_⟩
    · apply (Nat.div_lt_iff_lt_mul hd).mpr
      simpa only [Nat.div_mul_cancel hdq] using ZMod.val_lt x
    · have he : r + d * (x.val / d) = x.val := by
        simpa only [hx] using Nat.mod_add_div x.val d
      rw [he, ZMod.natCast_zmod_val]

/-- Every additive subgroup of a finite cyclic group is given by one
positive divisor, as proved by lifting it to an integer subgroup. -/
theorem cyclic_subgroup_modulus (q : ℕ) [NeZero q] (H : AddSubgroup (ZMod q)) :
    ∃ d : ℕ, 0 < d ∧ d ∣ q ∧ ∀ a x : ZMod q,
      x - a ∈ H ↔ x.val % d = a.val % d := by
  let K := H.comap (Int.castAddHom (ZMod q))
  obtain ⟨z, hz⟩ := Int.subgroup_cyclic K
  rw [← AddSubgroup.zmultiples_eq_closure, ← Int.zmultiples_natAbs z] at hz
  let d := z.natAbs
  have hmem (t : ℤ) : (t : ZMod q) ∈ H ↔ (d : ℤ) ∣ t := by
    change t ∈ K ↔ _
    rw [hz, Int.mem_zmultiples_iff]
  have hqd : (d : ℤ) ∣ (q : ℤ) := (hmem q).mp (by simp)
  have hdq : d ∣ q := by exact_mod_cast hqd
  have hd : 0 < d := Nat.pos_of_dvd_of_pos hdq (Nat.pos_of_ne_zero (NeZero.ne q))
  refine ⟨d, hd, hdq, fun a x => ?_⟩
  have h := hmem ((x.val : ℤ) - (a.val : ℤ))
  simp only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val] at h
  rw [h, ← Nat.modEq_iff_dvd]
  exact eq_comm

/-- Canonical finite representatives of any coset, with exactly the
divisor and remainder conditions needed by `cyclic_coset_lift`. -/
theorem cyclic_coset_normal_form (q : ℕ) [NeZero q]
    (H : AddSubgroup (ZMod q)) (a : ZMod q) :
    ∃ d r : ℕ, 0 < d ∧ d ∣ q ∧ r < d ∧ ∀ x : ZMod q,
      BackgroundExternal.cosetIndicator H a x =
        BackgroundExternal.setIndicator (cyclicProgressionCoset q d r) x := by
  obtain ⟨d, hd, hdq, hmem⟩ := cyclic_subgroup_modulus q H
  refine ⟨d, a.val % d, hd, hdq, Nat.mod_lt _ hd, fun x => ?_⟩
  have he : x - a ∈ H ↔ x ∈ cyclicProgressionCoset q d (a.val % d) :=
    (hmem a x).trans (mem_cyclicProgressionCoset q d (a.val % d) hd hdq
      (Nat.mod_lt _ hd) x).symm
  simp only [BackgroundExternal.cosetIndicator, BackgroundExternal.setIndicator, he]
  split_ifs <;> rfl

end LittlewoodInverse
