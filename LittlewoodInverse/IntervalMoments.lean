import LittlewoodInverse.SymmetricChains
import LittlewoodInverse.MomentCounting

open scoped BigOperators
open MeasureTheory

namespace LittlewoodInverse
namespace IntervalMoments

def signedCoordinate {n : ℕ} (b : Fin n → ℤ) (r : ℕ) (i : Fin (r + r)) (j : Fin n) : ℤ :=
  Fin.addCases (fun _ : Fin r => b j) (fun _ : Fin r => -b j.rev) i

def signedSum {n : ℕ} (b : Fin n → ℤ) (r : ℕ) (x : Fin (r + r) → Fin n) : ℤ :=
  ∑ i, signedCoordinate b r i (x i)

def gridDecode {n : ℕ} (b : Fin n → ℤ) (r : ℕ) (x : Fin (r + r) → Fin n) :
    (Fin r → ℤ) × (Fin r → ℤ) :=
  (fun i => b (x (Fin.castAdd r i)), fun i => b (x (Fin.natAdd r i)).rev)

theorem signedSum_eq {n : ℕ} (b : Fin n → ℤ) (r : ℕ) (x : Fin (r + r) → Fin n) :
    signedSum b r x = (∑ i, (gridDecode b r x).1 i) - ∑ i, (gridDecode b r x).2 i := by
  unfold signedSum
  rw [Fin.sum_univ_add]
  simp only [signedCoordinate, gridDecode, Fin.addCases_left, Fin.addCases_right,
    Finset.sum_neg_distrib, sub_eq_add_neg]

theorem signedCoordinate_strictMono {n : ℕ} (b : Fin n → ℤ) (hb : StrictMono b)
    (r : ℕ) (i : Fin (r + r)) : StrictMono (signedCoordinate b r i) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · intro k l hkl
    simpa only [signedCoordinate, Fin.addCases_left] using hb hkl
  · intro k l hkl
    simp only [signedCoordinate, Fin.addCases_right]
    exact neg_lt_neg (hb (Fin.rev_lt_rev.mpr hkl))

theorem signedSum_strictMono {n : ℕ} (b : Fin n → ℤ) (hb : StrictMono b) (r : ℕ) :
    StrictMono (signedSum b r) := by
  intro x y hxy
  have hex : ∃ i, x i < y i := by
    by_contra h
    push Not at h
    exact (not_le_of_gt hxy) h
  obtain ⟨i, hi⟩ := hex
  exact Finset.sum_lt_sum (fun j hj => (signedCoordinate_strictMono b hb r j).monotone (hxy.le j))
    ⟨i, Finset.mem_univ _, signedCoordinate_strictMono b hb r i hi⟩

theorem gridDecode_injective {n : ℕ} (b : Fin n → ℤ) (hb : Function.Injective b) (r : ℕ) :
    Function.Injective (gridDecode b r) := by
  intro x y hxy
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · exact hb (congrArg (fun p => p.1 j) hxy)
  · have hrev := hb (congrArg (fun p => p.2 j) hxy)
    simpa only [Fin.rev_rev] using congrArg Fin.rev hrev

/-- Reversing the second group of sorted indices turns equal-sum tuples
into the zero level of a function that strictly increases in the product order. -/
theorem relationCount_eq_zero_fiber (B : Finset ℤ) (r n : ℕ) (b : Fin n → ℤ)
    (hb : Function.Injective b) (hmem : ∀ i, b i ∈ B)
    (hsurj : ∀ z ∈ B, ∃ i, b i = z) :
    MomentCounting.relationCount B r =
      (Finset.univ.filter (fun x : Fin (r + r) → Fin n => signedSum b r x = 0)).card := by
  classical
  unfold MomentCounting.relationCount
  symm
  apply Finset.card_bij (fun x _ => gridDecode b r x)
  · intro x hx
    have hz := (Finset.mem_filter.mp hx).2
    rw [signedSum_eq, sub_eq_zero] at hz
    simp only [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨?_, ?_⟩, hz⟩
    · simp only [MomentCounting.tuples, Fintype.mem_piFinset]
      intro i
      exact hmem _
    · simp only [MomentCounting.tuples, Fintype.mem_piFinset]
      intro i
      exact hmem _
  · intro x hx y hy hxy
    exact gridDecode_injective b hb r hxy
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hp1 := (Finset.mem_product.mp hp'.1).1
    have hp2 := (Finset.mem_product.mp hp'.1).2
    simp only [MomentCounting.tuples, Fintype.mem_piFinset] at hp1 hp2
    choose f hf using fun i => hsurj (p.1 i) (hp1 i)
    choose g hg using fun i => hsurj (p.2 i) (hp2 i)
    let x : Fin (r + r) → Fin n := Fin.append f (fun i => (g i).rev)
    have hx : gridDecode b r x = p := by
      apply Prod.ext <;> funext i
      · simpa only [x, gridDecode, Fin.append_left] using hf i
      · simpa only [x, gridDecode, Fin.append_right, Fin.rev_rev] using hg i
    refine ⟨x, ?_, hx⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [signedSum_eq, hx, hp'.2]
    omega

theorem relationCount_le_middle (B : Finset ℤ) (hB : B.Nonempty) (r : ℕ) :
    MomentCounting.relationCount B r ≤
      (Finset.univ.filter (fun x : Fin (r + r) → Fin B.card =>
        (∑ i, (x i).val) = r * (B.card - 1))).card := by
  let b := B.orderEmbOfFin rfl
  have hb : StrictMono b := b.strictMono
  have heq := relationCount_eq_zero_fiber B r B.card b hb.injective
    (fun i => B.orderEmbOfFin_mem rfl i) (by
      intro z hz
      obtain ⟨i, hi⟩ := (B.orderIsoOfFin rfl).surjective ⟨z, hz⟩
      exact ⟨i, congrArg Subtype.val hi⟩)
  rw [heq]
  have hanti : IsAntichain (· ≤ ·)
      ((Finset.univ.filter (fun x : Fin (r + r) → Fin B.card => signedSum b r x = 0)) :
        Set (Fin (r + r) → Fin B.card)) := by
    intro x hx y hy hne hle
    have hx0 := (Finset.mem_filter.mp hx).2
    have hy0 := (Finset.mem_filter.mp hy).2
    have hlt := signedSum_strictMono b hb r (lt_of_le_of_ne hle hne)
    omega
  have hbound := SymmetricChains.nonempty_grid_antichain_card_le_middle
    (r + r) B.card hB.card_pos _ hanti
  have hmid : (r + r) * (B.card - 1) / 2 = r * (B.card - 1) := by
    rw [Nat.add_mul]
    omega
  simpa only [hmid] using hbound

noncomputable def integerInterval (n : ℕ) : Finset ℤ := Finset.Ico 0 (n : ℤ)

theorem interval_signedSum (n r : ℕ) (x : Fin (r + r) → Fin n) :
    signedSum (fun j : Fin n => (j.val : ℤ)) r x =
      (∑ i, ((x i).val : ℤ)) - (r : ℤ) * ((n - 1 : ℕ) : ℤ) := by
  have hrev (j : Fin n) : (j.rev.val : ℤ) = ((n - 1 : ℕ) : ℤ) - (j.val : ℤ) := by
    rw [Fin.val_rev]
    have := j.isLt
    omega
  rw [signedSum_eq]
  simp only [gridDecode]
  simp_rw [hrev]
  rw [Finset.sum_sub_distrib, Fin.sum_univ_add]
  simp
  ring

theorem interval_signedSum_zero_iff (n r : ℕ) (x : Fin (r + r) → Fin n) :
    signedSum (fun j : Fin n => (j.val : ℤ)) r x = 0 ↔
      (∑ i, (x i).val) = r * (n - 1) := by
  rw [interval_signedSum, sub_eq_zero]
  norm_cast

theorem interval_relationCount_eq_middle (n r : ℕ) :
    MomentCounting.relationCount (integerInterval n) r =
      (Finset.univ.filter (fun x : Fin (r + r) → Fin n =>
        (∑ i, (x i).val) = r * (n - 1))).card := by
  have heq := relationCount_eq_zero_fiber (integerInterval n) r n
    (fun j : Fin n => (j.val : ℤ))
    (by intro i j hij; apply Fin.ext; dsimp at hij; exact_mod_cast hij)
    (by intro i; simp only [integerInterval, Finset.mem_Ico]; have := i.isLt; omega)
    (by
      intro z hz
      simp only [integerInterval, Finset.mem_Ico] at hz
      exact ⟨⟨z.toNat, by omega⟩, by dsimp; omega⟩)
  rw [heq]
  congr 1
  apply Finset.filter_congr
  intro x hx
  exact interval_signedSum_zero_iff n r x

/-- The exact counting inequality behind all even Fourier moments. -/
theorem relationCount_le_interval (B : Finset ℤ) (r : ℕ) :
    MomentCounting.relationCount B r ≤ MomentCounting.relationCount (integerInterval B.card) r := by
  by_cases hB : B.Nonempty
  · rw [interval_relationCount_eq_middle]
    exact relationCount_le_middle B hB r
  · have hB0 : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    subst B
    simp [integerInterval]

/-- Proposition 3.2: among all integer sets of a given size, the interval
maximizes every even Fourier moment.  This includes the empty-set and
zero-exponent cases under Lean's usual convention for the zeroth power. -/
theorem even_moment_le_interval (B : Finset ℤ) (r : ℕ) :
    (∫ t, ‖fourierPolynomial B t‖ ^ (2 * r) ∂circleMeasure) ≤
      ∫ t, ‖fourierPolynomial (integerInterval B.card) t‖ ^ (2 * r) ∂circleMeasure := by
  rw [MomentCounting.integral_even_moment, MomentCounting.integral_even_moment]
  exact_mod_cast relationCount_le_interval B r

end IntervalMoments
end LittlewoodInverse
