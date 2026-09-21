import LittlewoodInverse.BlockBoundary
import LittlewoodInverse.MPSConsequences
import LittlewoodInverse.BlockSlabs

open scoped BigOperators ComplexConjugate symmDiff
open MeasureTheory

namespace LittlewoodInverse

variable {q : ℕ}

/-- The actual vertical support of the discrete boundary. -/
def boundaryHeights (C : Finset (ZMod q × ℤ)) : Finset ℤ :=
  (C ∆ boundaryTranslate C).image Prod.snd

theorem mem_boundaryHeights (C : Finset (ZMod q × ℤ)) (u : ℤ) :
    u ∈ boundaryHeights C ↔ ∃ b, boundaryValue C (b, u) ≠ 0 := by
  simp only [boundaryHeights, Finset.mem_image, Prod.exists,
    ← boundaryValue_ne_zero_iff]
  aesop

theorem boundaryValue_zero_of_height_not_mem (C : Finset (ZMod q × ℤ))
    {u : ℤ} (hu : u ∉ boundaryHeights C) (b : ZMod q) :
    boundaryValue C (b, u) = 0 := by
  by_contra h
  exact hu ((mem_boundaryHeights C u).mpr ⟨b, h⟩)

theorem boundaryValue_zero_of_not_mem_carrier (C : Finset (ZMod q × ℤ))
    {p : ZMod q × ℤ} (hp : p ∉ boundaryCarrier C) : boundaryValue C p = 0 := by
  by_contra h
  exact hp (Finset.symmDiff_subset_union ((boundaryValue_ne_zero_iff C p).mp h))

variable (q) [NeZero q]

noncomputable def boundaryRow (C : Finset (ZMod q × ℤ)) (u : ℤ) (j : ZMod q) : ℂ :=
  cyclicPolynomial q Finset.univ (fun b => (boundaryValue C (b, u) : ℂ)) j

noncomputable def boundaryRowNorm (C : Finset (ZMod q × ℤ)) (u : ℤ) : ℝ :=
  ∫ j, ‖boundaryRow q C u j‖ ∂cyclicMeasure q

theorem boundaryRowNorm_nonneg (C : Finset (ZMod q × ℤ)) (u : ℤ) :
    0 ≤ boundaryRowNorm q C u := integral_nonneg fun _ => norm_nonneg _

theorem boundaryRow_zero_of_not_mem (C : Finset (ZMod q × ℤ)) {u : ℤ}
    (hu : u ∉ boundaryHeights C) (j : ZMod q) : boundaryRow q C u j = 0 := by
  simp [boundaryRow, cyclicPolynomial, boundaryValue_zero_of_height_not_mem C hu]

theorem boundary_sum_rows (C : Finset (ZMod q × ℤ)) (f : ZMod q × ℤ → ℂ) :
    (∑ p ∈ boundaryCarrier C, (boundaryValue C p : ℂ) * f p) =
      ∑ u ∈ boundaryHeights C, ∑ b : ZMod q, (boundaryValue C (b, u) : ℂ) * f (b, u) := by
  classical
  rw [Finset.sum_comm]
  rw [← Finset.sum_product (f := fun p : ZMod q × ℤ => (boundaryValue C p : ℂ) * f p)]
  apply Finset.sum_congr_of_eq_on_inter
  · intro p _ hp
    have hu : p.2 ∉ boundaryHeights C := by simpa only [Finset.mem_product,
      Finset.mem_univ, true_and] using hp
    have hz := boundaryValue_zero_of_height_not_mem C hu p.1
    simp only [Prod.mk.eta] at hz
    simp [hz]
  · intro p _ hp
    simp [boundaryValue_zero_of_not_mem_carrier C hp]
  · intro p _ _
    rfl

theorem boundaryPolynomial_eq_rows (C : Finset (ZMod q × ℤ)) (j : ZMod q)
    (s : Circle) :
    boundaryPolynomial q C j s =
      ∑ u ∈ boundaryHeights C, boundaryRow q C u j * fourier u s := by
  classical
  unfold boundaryPolynomial boundaryRow cyclicPolynomial
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [← Finset.sum_product (f := fun p : ZMod q × ℤ =>
    (boundaryValue C p : ℂ) * cyclicCharacter q p.1 j * fourier p.2 s)]
  apply Finset.sum_congr_of_eq_on_inter
  · intro p _ hp
    have hu : p.2 ∉ boundaryHeights C := by simpa only [Finset.mem_product,
      Finset.mem_univ, true_and] using hp
    have hz := boundaryValue_zero_of_height_not_mem C hu p.1
    simp only [Prod.mk.eta] at hz
    simp [hz]
  · intro p _ hp
    simp [boundaryValue_zero_of_not_mem_carrier C hp]
  · intro p _ _
    ring

theorem boundaryRow_eq_coefficient (C : Finset (ZMod q × ℤ)) (u : ℤ) (j : ZMod q) :
    boundaryRow q C u j =
      ∫ s, boundaryPolynomial q C j s * conj (fourier u s) ∂circleMeasure := by
  classical
  simp_rw [boundaryPolynomial_eq_rows, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun _ _ => continuous_circle_integrable (by fun_prop))]
  simp_rw [integral_const_mul, integral_fourier_mul_conj]
  by_cases hu : u ∈ boundaryHeights C
  · simp [hu]
  · simp [hu, boundaryRow_zero_of_not_mem q C hu]

theorem boundaryRow_norm_le_circleIntegral (C : Finset (ZMod q × ℤ))
    (u : ℤ) (j : ZMod q) :
    ‖boundaryRow q C u j‖ ≤ ∫ s, ‖boundaryPolynomial q C j s‖ ∂circleMeasure := by
  rw [boundaryRow_eq_coefficient]
  calc
    _ ≤ ∫ s, ‖boundaryPolynomial q C j s * conj (fourier u s)‖ ∂circleMeasure :=
      norm_integral_le_integral_norm _
    _ = _ := by simp

theorem boundaryNorm_eq_iterated (C : Finset (ZMod q × ℤ)) :
    boundaryNorm q C =
      ∫ j, ∫ s, ‖boundaryPolynomial q C j s‖ ∂circleMeasure ∂cyclicMeasure q := by
  unfold boundaryNorm boundaryDualMeasure
  apply integral_prod_symm
  apply boundary_dual_integrable q
  simp_rw [boundaryPolynomial_eq_mixed]
  fun_prop

theorem boundaryRowNorm_le (C : Finset (ZMod q × ℤ)) (u : ℤ) :
    boundaryRowNorm q C u ≤ boundaryNorm q C := by
  rw [boundaryNorm_eq_iterated]
  exact integral_mono (cyclic_integrable q _) (cyclic_integrable q _)
    (boundaryRow_norm_le_circleIntegral q C u)

theorem one_le_boundaryRowNorm (C : Finset (ZMod q × ℤ)) {u : ℤ}
    (hu : u ∈ boundaryHeights C) : 1 ≤ boundaryRowNorm q C u := by
  obtain ⟨b, hb⟩ := (mem_boundaryHeights C u).mp hu
  have h := cyclicCoefficient_norm_le_integral q
    (fun b => (boundaryValue C (b, u) : ℂ)) (Finset.mem_univ b)
  have hn : ‖(boundaryValue C (b, u) : ℂ)‖ = 1 := by
    rcases boundaryValue_cases C (b, u) with he | he | he <;> simp_all
  simpa only [hn, boundaryRowNorm, boundaryRow] using h

theorem boundaryPolynomial_eq_sorted (C : Finset (ZMod q × ℤ)) (j : ZMod q)
    (s : Circle) :
    weightedFourierPolynomial ((boundaryHeights C).orderEmbOfFin rfl)
      (fun i => boundaryRow q C ((boundaryHeights C).orderEmbOfFin rfl i) j) s =
      boundaryPolynomial q C j s := by
  rw [boundaryPolynomial_eq_rows]
  unfold weightedFourierPolynomial
  apply Finset.sum_bij (fun i _ => (boundaryHeights C).orderEmbOfFin rfl i)
  · intro i _
    exact (boundaryHeights C).orderEmbOfFin_mem rfl i
  · intro i _ k _ h
    exact ((boundaryHeights C).orderEmbOfFin rfl).injective h
  · intro u hu
    obtain ⟨i, hi⟩ := ((boundaryHeights C).orderIsoOfFin rfl).surjective ⟨u, hu⟩
    exact ⟨i, Finset.mem_univ _, congrArg Subtype.val hi⟩
  · intro i _
    rfl

/-- The MPS weights retain their original indices, even when a row happens
to vanish at a particular dual-group point. -/
theorem exists_boundary_log_bound : ∃ c : ℝ, 0 < c ∧
    ∀ (q : ℕ) [NeZero q] (C : Finset (ZMod q × ℤ)),
      c * Real.log ((boundaryHeights C).card + 1) ≤ boundaryNorm q C := by
  obtain ⟨c, hc, hmps⟩ := External.mps_weighted
  refine ⟨c, hc, fun q _ C => ?_⟩
  let U := boundaryHeights C
  let n := U.orderEmbOfFin rfl
  have hp (j : ZMod q) :
      c * (∑ i : Fin U.card, ‖boundaryRow q C (n i) j‖ / ((i.val : ℝ) + 1)) ≤
        ∫ s, ‖boundaryPolynomial q C j s‖ ∂circleMeasure := by
    simpa only [n, U, boundaryPolynomial_eq_sorted] using
      hmps U.card n n.strictMono (fun i => boundaryRow q C (n i) j)
  have havg := integral_mono (cyclic_integrable q _) (cyclic_integrable q _) hp
  rw [integral_const_mul, integral_finsetSum _ (fun _ _ => cyclic_integrable q _)] at havg
  simp_rw [div_eq_mul_inv, integral_mul_const] at havg
  rw [← boundaryNorm_eq_iterated] at havg
  have hs : (∑ i : Fin U.card, (1 : ℝ) / ((i.val : ℝ) + 1)) ≤
      ∑ i : Fin U.card, boundaryRowNorm q C (n i) / ((i.val : ℝ) + 1) := by
    apply Finset.sum_le_sum
    intro i _
    exact div_le_div_of_nonneg_right
      (one_le_boundaryRowNorm q C (U.orderEmbOfFin_mem rfl i)) (by positivity)
  rw [sum_fin_reciprocal_eq_harmonic] at hs
  have hl : Real.log ((U.card : ℝ) + 1) ≤ (harmonic U.card : ℝ) := by
    exact_mod_cast log_add_one_le_harmonic U.card
  exact (mul_le_mul_of_nonneg_left (hl.trans hs) hc.le).trans havg

/-- A uniform exponential bound for the number of actual boundary heights. -/
theorem exists_boundary_height_bound : ∃ K : ℝ, 0 < K ∧
    ∀ (q : ℕ) [NeZero q] (C : Finset (ZMod q × ℤ)),
      ((boundaryHeights C).card : ℝ) ≤ Real.exp (K * boundaryNorm q C) := by
  obtain ⟨c, hc, hlog⟩ := exists_boundary_log_bound
  refine ⟨c⁻¹, inv_pos.mpr hc, fun q _ C => ?_⟩
  have hl : Real.log ((boundaryHeights C).card + 1) ≤
      c⁻¹ * boundaryNorm q C := by
    have h := (le_div_iff₀ hc).mpr (show
      Real.log ((boundaryHeights C).card + 1) * c ≤ boundaryNorm q C by
        simpa only [mul_comm] using hlog q C)
    simpa only [div_eq_mul_inv, mul_comm] using h
  have he : ((boundaryHeights C).card : ℝ) + 1 ≤
      Real.exp (c⁻¹ * boundaryNorm q C) :=
    (Real.log_le_iff_le_exp (by positivity)).mp hl
  linarith

theorem cyclicPolynomial_cellResidues (C : Finset (ZMod q × ℤ)) (u : ℤ)
    (j : ZMod q) :
    cyclicPolynomial q (cellResidues C u) (fun _ => 1) j =
      ∑ p ∈ C, if p.2 = u then cyclicCharacter q p.1 j else 0 := by
  classical
  unfold cyclicPolynomial cellResidues
  rw [Finset.sum_image]
  · simp only [one_mul, Finset.sum_filter]
  · intro p hp r hr he
    exact Prod.ext he ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hr).2.symm)

/-- Discrete telescoping over all boundary heights below a given slice. -/
theorem boundaryRow_sum_telescope (C : Finset (ZMod q × ℤ)) (u : ℤ) (j : ZMod q) :
    (∑ v ∈ boundaryHeights C, if v ≤ u then boundaryRow q C v j else 0) =
      cyclicPolynomial q (cellResidues C u) (fun _ => 1) j := by
  classical
  have hs := boundary_sum C (fun p => if p.2 ≤ u then cyclicCharacter q p.1 j else 0)
  rw [boundary_sum_rows q] at hs
  simp only [mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero] at hs
  rw [cyclicPolynomial_cellResidues]
  calc
    _ = ∑ p ∈ C, ((if p.2 ≤ u then cyclicCharacter q p.1 j else 0) -
      (if p.2 + 1 ≤ u then cyclicCharacter q p.1 j else 0)) := hs
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      rcases lt_trichotomy p.2 u with h | h | h
      · have hle : p.2 ≤ u := by omega
        have hsle : p.2 + 1 ≤ u := by omega
        simp [hle, hsle, ne_of_lt h]
      · simp [h]
      · have hle : ¬ p.2 ≤ u := by omega
        have hsle : ¬ p.2 + 1 ≤ u := by omega
        simp [hle, hsle, ne_of_gt h]

/-- Every actual horizontal slice has cyclic spectral norm at most v S. -/
theorem cellResidues_norm_le_boundary (C : Finset (ZMod q × ℤ)) (u : ℤ) :
    cyclicLittlewoodNorm q (cellResidues C u) ≤
      (boundaryHeights C).card * boundaryNorm q C := by
  classical
  have hp (j : ZMod q) :
      ‖cyclicPolynomial q (cellResidues C u) (fun _ => 1) j‖ ≤
        ∑ v ∈ boundaryHeights C, ‖boundaryRow q C v j‖ := by
    rw [← boundaryRow_sum_telescope]
    calc
      _ ≤ ∑ v ∈ boundaryHeights C, ‖if v ≤ u then boundaryRow q C v j else 0‖ :=
        norm_sum_le _ _
      _ ≤ _ := Finset.sum_le_sum fun v _ => by split_ifs <;> simp
  have havg := integral_mono (cyclic_integrable q _) (cyclic_integrable q _) hp
  rw [integral_finsetSum _ (fun _ _ => cyclic_integrable q _)] at havg
  calc
    _ ≤ ∑ v ∈ boundaryHeights C, boundaryRowNorm q C v := havg
    _ ≤ ∑ _v ∈ boundaryHeights C, boundaryNorm q C :=
      Finset.sum_le_sum fun v _ => boundaryRowNorm_le q C v
    _ = _ := by simp

end LittlewoodInverse
