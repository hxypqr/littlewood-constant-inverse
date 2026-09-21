import LittlewoodInverse.UniformMoments

open scoped BigOperators

namespace LittlewoodInverse
namespace BoundedCompositions

abbrev Composition (d s : ℕ) := {x : Fin d → ℕ // ∑ i, x i = s}

noncomputable instance (d s : ℕ) : Fintype (Composition d s) :=
  Fintype.ofEquiv (Sym (Fin d) s) (Sym.equivNatSumOfFintype (Fin d) s)

theorem card_composition (d s : ℕ) (hd : 0 < d) :
    Fintype.card (Composition d s) = (s + d - 1).choose (d - 1) := by
  rw [← Fintype.card_congr (Sym.equivNatSumOfFintype (Fin d) s), Sym.card_sym_eq_choose]
  simp only [Fintype.card_fin]
  have hs : s ≤ d + s - 1 := by omega
  rw [← Nat.choose_symm hs]
  congr 1 <;> omega

def threshold {d : ℕ} (t : Finset (Fin d)) (n : ℕ) (i : Fin d) : ℕ :=
  if i ∈ t then n else 0

theorem sum_threshold {d : ℕ} (t : Finset (Fin d)) (n : ℕ) :
    ∑ i, threshold t n i = t.card * n := by
  simp [threshold]

theorem threshold_le_iff {d : ℕ} (t : Finset (Fin d)) (n : ℕ) (x : Fin d → ℕ) :
    (∀ i, threshold t n i ≤ x i) ↔ ∀ i ∈ t, n ≤ x i := by
  constructor
  · intro h i hi
    simpa [threshold, hi] using h i
  · intro h i
    by_cases hi : i ∈ t
    · simpa [threshold, hi] using h i hi
    · simp [threshold, hi]

theorem threshold_sum_le {d s : ℕ} (t : Finset (Fin d)) (n : ℕ)
    (x : Composition d s) (hx : ∀ i ∈ t, n ≤ x.val i) : t.card * n ≤ s := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (threshold_le_iff t n x.val).mpr hx i)
  simpa only [sum_threshold, x.property] using h

noncomputable def subtractThresholdEquiv {d s : ℕ} (t : Finset (Fin d)) (n : ℕ)
    (hs : t.card * n ≤ s) :
    {x : Composition d s // ∀ i ∈ t, n ≤ x.val i} ≃ Composition d (s - t.card * n) where
  toFun x := ⟨fun i => x.val.val i - threshold t n i, by
    have hpoint (i : Fin d) : x.val.val i - threshold t n i + threshold t n i = x.val.val i :=
      Nat.sub_add_cancel ((threshold_le_iff t n x.val.val).mpr x.property i)
    have heq : (∑ i, (x.val.val i - threshold t n i)) + t.card * n = s := by
      rw [← sum_threshold t n, ← Finset.sum_add_distrib]
      simp only [hpoint, x.val.property]
    simpa only using Nat.eq_sub_of_add_eq heq⟩
  invFun y := ⟨⟨fun i => y.val i + threshold t n i, by
    rw [Finset.sum_add_distrib, y.property, sum_threshold]
    omega⟩, by
      intro i hi
      simp only [threshold, if_pos hi]
      omega⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact Nat.sub_add_cancel ((threshold_le_iff t n x.val.val).mpr x.property i)
  right_inv y := by
    apply Subtype.ext
    funext i
    exact Nat.add_sub_cancel _ _

noncomputable def bad (d s n : ℕ) (i : Fin d) : Finset (Composition d s) :=
  Finset.univ.filter (fun x => n ≤ x.val i)

noncomputable def bounded (d s n : ℕ) : Finset (Composition d s) :=
  Finset.univ.filter (fun x => ∀ i, x.val i < n)

theorem bounded_eq_inf_compl (d s n : ℕ) :
    bounded d s n = Finset.univ.inf (fun i => (bad d s n i)ᶜ) := by
  ext x
  simp [bounded, bad, Finset.mem_inf]

theorem mem_inf_bad {d s n : ℕ} (t : Finset (Fin d)) (x : Composition d s) :
    x ∈ t.inf (bad d s n) ↔ ∀ i ∈ t, n ≤ x.val i := by
  simp [Finset.mem_inf, bad]

theorem card_inf_bad_of_le {d s n : ℕ} (t : Finset (Fin d))
    (hd : 0 < d) (hs : t.card * n ≤ s) :
    (t.inf (bad d s n)).card = (s - t.card * n + d - 1).choose (d - 1) := by
  rw [← Fintype.card_coe]
  have e : (t.inf (bad d s n) : Finset (Composition d s)) ≃
      {x : Composition d s // ∀ i ∈ t, n ≤ x.val i} :=
    Equiv.subtypeEquivRight (fun x => mem_inf_bad t x)
  rw [Fintype.card_congr (e.trans (subtractThresholdEquiv t n hs)), card_composition _ _ hd]

theorem card_inf_bad_of_gt {d s n : ℕ} (t : Finset (Fin d)) (hs : s < t.card * n) :
    (t.inf (bad d s n)).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have h := threshold_sum_le t n x ((mem_inf_bad t x).mp hx)
  omega

/-- Exact inclusion-exclusion count for bounded weak compositions. -/
theorem bounded_card_inclusion_exclusion (d s n : ℕ) (hd : 0 < d) :
    ((bounded d s n).card : ℤ) =
      ∑ t ∈ (Finset.univ : Finset (Fin d)).powerset, (-1 : ℤ) ^ t.card *
        (if t.card * n ≤ s then ((s - t.card * n + d - 1).choose (d - 1) : ℤ) else 0) := by
  rw [bounded_eq_inf_compl, Finset.inclusion_exclusion_card_inf_compl]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hs : t.card * n ≤ s
  · rw [if_pos hs, card_inf_bad_of_le t hd hs]
  · rw [if_neg hs, card_inf_bad_of_gt t (by omega)]
    simp

theorem bounded_card_binomial_sum (d s n : ℕ) (hd : 0 < d) :
    ((bounded d s n).card : ℤ) =
      ∑ j ∈ Finset.range (d + 1), (d.choose j : ℤ) * (-1 : ℤ) ^ j *
        (if j * n ≤ s then ((s - j * n + d - 1).choose (d - 1) : ℤ) else 0) := by
  rw [bounded_card_inclusion_exclusion d s n hd, Finset.sum_powerset]
  simp only [Finset.card_univ, Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_powersetCard j Finset.univ (fun q : ℕ => (-1 : ℤ) ^ q *
    (if q * n ≤ s then ((s - q * n + d - 1).choose (d - 1) : ℤ) else 0))]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem bounded_card_eq_grid (d s n : ℕ) :
    (bounded d s n).card =
      (Finset.univ.filter (fun x : Fin d → Fin n => ∑ i, (x i).val = s)).card := by
  classical
  symm
  apply Finset.card_bij (fun x hx => (⟨fun i => (x i).val,
    (Finset.mem_filter.mp hx).2⟩ : Composition d s))
  · intro x hx
    simp only [bounded, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun i => (x i).isLt
  · intro x hx y hy hxy
    funext i
    apply Fin.ext
    exact congrFun (congrArg Subtype.val hxy) i
  · intro x hx
    have hbound : ∀ i, x.val i < n := (Finset.mem_filter.mp hx).2
    refine ⟨fun i => ⟨x.val i, hbound i⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact x.property
    · exact Subtype.ext rfl

theorem interval_relationCount_eq_bounded (n r : ℕ) :
    MomentCounting.relationCount (IntervalMoments.integerInterval n) r =
      (bounded (r + r) (r * (n - 1)) n).card := by
  rw [IntervalMoments.interval_relationCount_eq_middle, bounded_card_eq_grid]

/-- The interval moment count as the exact alternating binomial sum.
The hypothesis `r ≤ n` ensures the displayed top entries have their
ordinary polynomial form, which suffices for taking `n → ∞`. -/
theorem interval_relationCount_binomial (n r : ℕ) (hr : 0 < r) (hn : r ≤ n) :
    (MomentCounting.relationCount (IntervalMoments.integerInterval n) r : ℤ) =
      ∑ j ∈ Finset.range r, (-1 : ℤ)^j * ((2 * r).choose j : ℤ) *
        (((r - j) * n + r - 1).choose (2 * r - 1) : ℤ) := by
  rw [interval_relationCount_eq_bounded,
    bounded_card_binomial_sum (r + r) (r * (n - 1)) n (by omega)]
  have hn0 : 0 < n := lt_of_lt_of_le hr hn
  have htot : r * (n - 1) = r * n - r := by
    have hne : n - 1 + 1 = n := by omega
    have hmul := congrArg (fun q : ℕ => r * q) hne
    simp only [Nat.mul_add, Nat.mul_one] at hmul
    omega
  have hsmall (j : ℕ) (hj : j < r) : j * n ≤ r * (n - 1) := by
    have h := Nat.mul_le_mul_right n (show j + 1 ≤ r by omega)
    simp only [Nat.add_mul, one_mul] at h
    omega
  have hlarge (j : ℕ) (hj : r ≤ j) : ¬j * n ≤ r * (n - 1) := by
    have h := Nat.mul_le_mul_right n hj
    have hp : 0 < r * n := Nat.mul_pos hr hn0
    omega
  have htop (j : ℕ) (hj : j < r) :
      r * (n - 1) - j * n + (r + r) - 1 = (r - j) * n + r - 1 := by
    have hd : (r - j) * n + j * n = r * n := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hj.le]
    have hs := hsmall j hj
    have hx : r * (n - 1) - j * n + j * n = r * (n - 1) := Nat.sub_add_cancel hs
    have hy : r * (n - 1) + r = r * n := by
      rw [htot, Nat.sub_add_cancel (Nat.le_mul_of_pos_right r hn0)]
    have heq : r * (n - 1) - j * n + (r + r) = (r - j) * n + r := by
      omega
    exact congrArg (fun q : ℕ => q - 1) heq
  calc
    _ = ∑ j ∈ Finset.range r, ((r + r).choose j : ℤ) * (-1 : ℤ)^j *
        (if j * n ≤ r * (n - 1) then
          ((r * (n - 1) - j * n + (r + r) - 1).choose (r + r - 1) : ℤ) else 0) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (show r ≤ r + r + 1 by omega))
      intro j hj hjnot
      rw [if_neg (hlarge j (by simpa only [Finset.mem_range, not_lt] using hjnot)), mul_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [if_pos (hsmall j hj'), htop j hj']
      have he : r + r = 2 * r := by omega
      rw [he]
      ring

end BoundedCompositions
end LittlewoodInverse
