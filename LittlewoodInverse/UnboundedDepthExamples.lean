import LittlewoodInverse.SidonFibreExamples
import LittlewoodInverse.IntervalNorm

open scoped BigOperators
open MeasureTheory
open Filter

namespace LittlewoodInverse

def ternaryExceptions (h : ℕ) : Finset ℤ :=
  (Finset.range h).image (fun j => (3 : ℤ) ^ j)

noncomputable def unbalancedSet (h M : ℕ) : Finset ℤ :=
  affineImage 0 ((3 : ℤ) ^ h) (IntervalMoments.integerInterval M) ∪ ternaryExceptions h

theorem ternaryExceptions_card (h : ℕ) : (ternaryExceptions h).card = h := by
  rw [ternaryExceptions, Finset.card_image_of_injective, Finset.card_range]
  intro i j hij
  apply ternary_power_strictMono.injective
  dsimp only at hij ⊢
  exact_mod_cast hij

theorem unbalancedSet_disjoint (h M : ℕ) :
    Disjoint (affineImage 0 ((3 : ℤ) ^ h) (IntervalMoments.integerInterval M))
      (ternaryExceptions h) := by
  apply Finset.disjoint_left.mpr
  intro z hz hj
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hj
  obtain ⟨hu0, _huM⟩ := Finset.mem_Ico.mp hu
  have hjh : (3 : ℤ) ^ j < 3 ^ h := by
    exact_mod_cast ternary_pow_lt (Finset.mem_range.mp hj)
  have hp : (0 : ℤ) < 3 ^ j := by positivity
  have hh : (0 : ℤ) < 3 ^ h := by positivity
  by_cases huZ : u = 0
  · subst u
    simp only [mul_zero, add_zero] at he
    omega
  · have hu1 : 1 ≤ u := by omega
    nlinarith

theorem unbalancedSet_card (h M : ℕ) : (unbalancedSet h M).card = M + h := by
  rw [unbalancedSet, Finset.card_union_of_disjoint (unbalancedSet_disjoint h M),
    affine_card _ _ _ (by positivity), integerInterval_card, ternaryExceptions_card]

theorem littlewoodNorm_disjoint_union {A B : Finset ℤ} (hAB : Disjoint A B) :
    littlewoodNorm (A ∪ B) ≤ littlewoodNorm A + littlewoodNorm B := by
  have hp (t : Circle) : fourierPolynomial (A ∪ B) t = fourierPolynomial A t + fourierPolynomial B t :=
    Finset.sum_union hAB
  calc
    _ ≤ ∫ t, (‖fourierPolynomial A t‖ + ‖fourierPolynomial B t‖) ∂circleMeasure := by
      apply integral_mono (continuous_circle_integrable (fourierPolynomial_continuous _).norm)
        (continuous_circle_integrable ((fourierPolynomial_continuous A).norm.add
          (fourierPolynomial_continuous B).norm))
      intro t
      dsimp only
      rw [hp]
      exact norm_add_le _ _
    _ = _ := integral_add (continuous_circle_integrable (fourierPolynomial_continuous A).norm)
      (continuous_circle_integrable (fourierPolynomial_continuous B).norm)

theorem unbalancedSet_norm (h M : ℕ) :
    littlewoodNorm (unbalancedSet h M) ≤
      littlewoodNorm (IntervalMoments.integerInterval M) + Real.sqrt (h : ℝ) := by
  have hh := littlewoodNorm_disjoint_union (unbalancedSet_disjoint h M)
  have he := littlewoodNorm_le_sqrt_card (ternaryExceptions h)
  rw [ternaryExceptions_card] at he
  simp only [affineImage, littlewoodNorm_affine _ _ (by positivity : (3 : ℤ) ^ h ≠ 0)] at hh
  change littlewoodNorm (unbalancedSet h M) ≤ _ at hh
  linarith

theorem ternaryExceptions_succ (h : ℕ) :
    ternaryExceptions (h + 1) = insert 1 (affineImage 0 3 (ternaryExceptions h)) := by
  ext z
  constructor
  · intro hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
    rcases j with _ | j
    · simp
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      refine ⟨(3 : ℤ) ^ j, Finset.mem_image.mpr ⟨j, ?_, rfl⟩, ?_⟩
      · apply Finset.mem_range.mpr
        have hh := Finset.mem_range.mp hj
        omega
      · simp only [zero_add, pow_succ]
        ring
  · intro hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), by simp⟩
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hu
      refine Finset.mem_image.mpr ⟨j + 1, ?_, ?_⟩
      · exact Finset.mem_range.mpr (Nat.add_lt_add_right (Finset.mem_range.mp hj) 1)
      · simp only [zero_add, pow_succ]
        ring

theorem unbalancedSet_zero (M : ℕ) : unbalancedSet 0 M = IntervalMoments.integerInterval M := by
  simp [unbalancedSet, ternaryExceptions, affineImage]

theorem unbalancedSet_succ (h M : ℕ) :
    unbalancedSet (h + 1) M = affineImage 0 3 (unbalancedSet h M) ∪ {1} := by
  rw [unbalancedSet, ternaryExceptions_succ, unbalancedSet]
  simp only [affineImage, Finset.image_union, Finset.image_image, Function.comp_def]
  have he : (fun x : ℤ => 0 + 3 * (0 + 3 ^ h * x)) =
      (fun x : ℤ => 0 + 3 ^ (h + 1) * x) := by
    funext x
    rw [pow_succ]
    ring
  rw [he]
  ext x
  simp

theorem zero_one_sidon : AdditiveSidon ({0, 1} : Finset (ZMod 3)) := by
  unfold AdditiveSidon
  decide

theorem zero_one_fibre_union (A B : Finset ℤ) :
    fibreUnion 3 {0, 1} (fun r => if r = 0 then A else B) =
      affineImage 0 3 A ∪ affineImage 1 3 B := by
  norm_num [fibreUnion, ZMod.val]
  rfl

theorem unbalancedSet_fibre_recursion (h M : ℕ) :
    unbalancedSet (h + 1) M =
      fibreUnion 3 {0, 1} (fun r => if r = 0 then unbalancedSet h M else {0}) := by
  rw [zero_one_fibre_union, unbalancedSet_succ]
  simp [affineImage]

theorem unbalancedSet_nonempty (h : ℕ) {M : ℕ} (hM : 0 < M) :
    (unbalancedSet h M).Nonempty := by
  apply Finset.card_pos.mp
  rw [unbalancedSet_card]
  omega

/-- At every recursive step the residue support is exactly {0,1}, the
continuing child is the preceding set, and the other child is a singleton. -/
theorem unbalancedSet_assembly (β Δ : ℝ) (h : ℕ) {M : ℕ} (hM : 0 < M) :
    Assembly β Δ (unbalancedSet h M) := by
  induction h with
  | zero => rw [unbalancedSet_zero]; exact Assembly.terminal (interval_terminal β Δ hM)
  | succ h ih =>
    rw [unbalancedSet_fibre_recursion]
    apply Assembly.node 3 (by norm_num) {0, 1} (by simp) zero_one_sidon
    · intro r _hr
      split_ifs
      · exact ih
      · exact Assembly.terminal (Terminal.singleton 0)
    · intro r _hr
      split_ifs
      · exact unbalancedSet_nonempty h hM
      · simp

noncomputable def ternaryDigitSet : ℕ → Finset ℤ
  | 0 => {0}
  | h + 1 => fibreUnion 3 {0, 1} (fun _ => ternaryDigitSet h)

theorem ternaryDigitSet_card (h : ℕ) : (ternaryDigitSet h).card = 2 ^ h := by
  induction h with
  | zero => simp [ternaryDigitSet]
  | succ h ih =>
    rw [ternaryDigitSet, uniform_fibre_card, ih]
    norm_num
    ring

theorem ternaryDigitSet_assembly (β Δ : ℝ) (h : ℕ) : Assembly β Δ (ternaryDigitSet h) := by
  induction h with
  | zero => exact Assembly.terminal (Terminal.singleton 0)
  | succ h ih =>
    apply Assembly.node 3 (by norm_num) {0, 1} (by simp) zero_one_sidon
    · intro _ _; exact ih
    · intro _ _
      apply Finset.card_pos.mp
      rw [ternaryDigitSet_card]
      positivity

theorem ternaryDigitSet_norm_twentieth (h : ℕ) :
    ((ternaryDigitSet h).card : ℝ) ≤ littlewoodNorm (ternaryDigitSet h) ^ 20 := by
  induction h with
  | zero => simp [ternaryDigitSet, littlewoodNorm, fourierPolynomial]
  | succ h ih =>
    have hb := actual_fibre_twentieth_budget 3 ({0, 1} : Finset (ZMod 3)) zero_one_sidon
      (fun _ => ternaryDigitSet h)
    norm_num only [Finset.sum_insert, Finset.mem_singleton, zero_ne_one, not_false_eq_true,
      Finset.sum_singleton] at hb
    rw [ternaryDigitSet_card, pow_succ, Nat.cast_mul, Nat.cast_ofNat]
    rw [ternaryDigitSet_card] at ih
    change littlewoodNorm (ternaryDigitSet h) ^ 20 + littlewoodNorm (ternaryDigitSet h) ^ 20 ≤
      littlewoodNorm (ternaryDigitSet (h + 1)) ^ 20 at hb
    nlinarith

def ternaryDigitValue {h : ℕ} (ε : Fin h → Fin 2) : ℤ :=
  ∑ i, (ε i).val * (3 : ℤ) ^ i.val

theorem ternaryDigitValue_cons {h : ℕ} (b : Fin 2) (ε : Fin h → Fin 2) :
    ternaryDigitValue (Fin.cons b ε) = (b.val : ℤ) + 3 * ternaryDigitValue ε := by
  rw [ternaryDigitValue, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.val_zero, pow_zero, mul_one, Fin.cons_succ, Fin.val_succ,
    pow_succ, ternaryDigitValue, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem ternaryDigitSet_mem (h : ℕ) (z : ℤ) :
    z ∈ ternaryDigitSet h ↔ ∃ ε : Fin h → Fin 2, ternaryDigitValue ε = z := by
  induction h generalizing z with
  | zero => simp [ternaryDigitSet, ternaryDigitValue, eq_comm]
  | succ h ih =>
    have he : ternaryDigitSet (h + 1) = affineImage 0 3 (ternaryDigitSet h) ∪
        affineImage 1 3 (ternaryDigitSet h) := by
      simpa [ternaryDigitSet] using zero_one_fibre_union (ternaryDigitSet h) (ternaryDigitSet h)
    rw [he]
    constructor
    · intro hz
      rcases Finset.mem_union.mp hz with hz | hz
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨ε, rfl⟩ := (ih u).mp hu
        exact ⟨Fin.cons 0 ε, by rw [ternaryDigitValue_cons]; rfl⟩
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨ε, rfl⟩ := (ih u).mp hu
        exact ⟨Fin.cons 1 ε, by rw [ternaryDigitValue_cons]; rfl⟩
    · rintro ⟨ε, rfl⟩
      let tail : Fin h → Fin 2 := fun i => ε i.succ
      have heps : ε = Fin.cons (ε 0) tail := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      have ht : ternaryDigitValue tail ∈ ternaryDigitSet h := (ih _).mpr ⟨tail, rfl⟩
      rw [heps, ternaryDigitValue_cons]
      have he0 := (ε 0).isLt
      rcases (show (ε 0).val = 0 ∨ (ε 0).val = 1 by omega) with h0 | h1
      · apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨ternaryDigitValue tail, ht, by simp [h0]⟩
      · apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨ternaryDigitValue tail, ht, by simp [h1]⟩

/-- The fully branching example is exactly the set of base-three expansions
with digits zero or one, with no hidden model replacement. -/
theorem ternaryDigitSet_eq (h : ℕ) :
    ternaryDigitSet h = Finset.univ.image (fun ε : Fin h → Fin 2 => ternaryDigitValue ε) := by
  ext z
  simp [ternaryDigitSet_mem]

theorem ternaryDigitSet_norm_lower (h : ℕ) :
    ((ternaryDigitSet h).card : ℝ) ^ (1 / 20 : ℝ) ≤ littlewoodNorm (ternaryDigitSet h) := by
  have hh := ternaryDigitSet_norm_twentieth h
  have hp := Real.rpow_le_rpow (Nat.cast_nonneg _) hh (by norm_num : (0 : ℝ) ≤ 1 / 20)
  have hn := littlewoodNorm_nonneg (ternaryDigitSet h)
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn] at hp
  norm_num at hp
  exact hp

noncomputable def logarithmicChainDepth (M : ℕ) : ℕ := Nat.floor (Real.log (M : ℝ) ^ 2)

theorem logarithmicChainDepth_sqrt {M : ℕ} (hM : 1 ≤ M) :
    Real.sqrt (logarithmicChainDepth M : ℝ) ≤ Real.log (M : ℝ) := by
  have hl : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hM)
  apply (Real.sqrt_le_left hl).mpr
  exact Nat.floor_le (sq_nonneg _)

theorem logarithmic_chain_norm {M : ℕ} (hM : 1 ≤ M) :
    littlewoodNorm (unbalancedSet (logarithmicChainDepth M) M) ≤
      littlewoodNorm (IntervalMoments.integerInterval M) + Real.log (M : ℝ) :=
  (unbalancedSet_norm _ _).trans (by linarith [logarithmicChainDepth_sqrt hM])

theorem logarithmicChainDepth_tendsto : Tendsto logarithmicChainDepth atTop atTop := by
  apply tendsto_nat_floor_atTop.comp
  exact (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

theorem logarithmic_chain_low_norm {M : ℕ} (hM : 1 ≤ M) :
    littlewoodNorm (unbalancedSet (logarithmicChainDepth M) M) ≤
      1 + 2 * Real.log ((unbalancedSet (logarithmicChainDepth M) M).card : ℝ) := by
  have hi := interval_littlewoodNorm_le_log M (show 0 < M by omega)
  have hc := logarithmic_chain_norm hM
  have hm : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hcard : (M : ℝ) ≤ (unbalancedSet (logarithmicChainDepth M) M).card := by
    rw [unbalancedSet_card]
    exact_mod_cast Nat.le_add_right M (logarithmicChainDepth M)
  have hl := Real.log_le_log hm hcard
  change littlewoodNorm (IntervalMoments.integerInterval M) ≤ _ at hi
  linarith

theorem ternaryDigitSet_eventually_not_low_norm (K : ℝ) :
    ∀ᶠ h : ℕ in atTop,
      K * Real.log ((ternaryDigitSet h).card : ℝ) < littlewoodNorm (ternaryDigitSet h) := by
  have hsmall := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).const_mul_left K).bound
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hpow : Tendsto (fun h : ℕ => ((ternaryDigitSet h).card : ℝ)) atTop atTop := by
    simp only [ternaryDigitSet_card, Nat.cast_pow, Nat.cast_ofNat]
    exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
  filter_upwards [hpow.eventually hsmall] with h hh
  have hN : (0 : ℝ) < (ternaryDigitSet h).card := by
    rw [ternaryDigitSet_card]
    positivity
  have hr : 0 < ((ternaryDigitSet h).card : ℝ) ^ (1 / 20 : ℝ) :=
    Real.rpow_pos_of_pos hN _
  have hlow := ternaryDigitSet_norm_lower h
  simp only [Real.norm_eq_abs, abs_of_pos hr] at hh
  have hx := le_abs_self (K * Real.log ((ternaryDigitSet h).card : ℝ))
  linarith

end LittlewoodInverse
