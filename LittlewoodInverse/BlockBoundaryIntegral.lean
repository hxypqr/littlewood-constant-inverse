import LittlewoodInverse.BlockBoundary
import LittlewoodInverse.PeriodicBounds

open scoped BigOperators Interval ComplexConjugate
open MeasureTheory

namespace LittlewoodInverse

variable (q : ℕ) [NeZero q]

theorem sum_zmod_eq_sum_range {E : Type*} [AddCommMonoid E] (f : ZMod q → E) :
    (∑ j : ZMod q, f j) = ∑ r ∈ Finset.range q, f (r : ZMod q) := by
  classical
  symm
  apply Finset.sum_bij (fun (r : ℕ) _ => (r : ZMod q))
  · intro _ _; exact Finset.mem_univ _
  · intro r hr s hs h
    have he := congrArg ZMod.val h
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hr),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hs)] using he
  · intro j _
    exact ⟨j.val, Finset.mem_range.mpr (ZMod.val_lt j), ZMod.natCast_zmod_val j⟩
  · intro _ _; rfl

noncomputable def residueNormAverage (A : Finset ℤ) (t : ℝ) : ℝ :=
  ∫ j, ‖fourierPolynomial A (((t / q : ℝ) : Circle) + ZMod.toAddCircle j)‖
    ∂cyclicMeasure q

theorem residueNormAverage_nonneg (A : Finset ℤ) (t : ℝ) :
    0 ≤ residueNormAverage q A t := integral_nonneg fun _ => norm_nonneg _

@[fun_prop] theorem residueNormAverage_continuous (A : Finset ℤ) :
    Continuous (residueNormAverage q A) := by
  unfold residueNormAverage
  simp_rw [integral_cyclicMeasure, smul_eq_mul]
  apply continuous_const.mul
  apply continuous_finsetSum
  intro j _
  exact ((fourierPolynomial_continuous A).comp
    (((AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_id.div_const (q : ℝ))).add
      continuous_const)).norm

theorem littlewoodNorm_eq_interval (A : Finset ℤ) (a : ℝ) :
    littlewoodNorm A = ∫ t in a..a + 1, ‖fourierPolynomial A (t : Circle)‖ := by
  unfold littlewoodNorm circleMeasure
  rw [AddCircle.integral_haarAddCircle]
  simpa using (AddCircle.intervalIntegral_preimage (1 : ℝ) a
    (fun t : Circle => ‖fourierPolynomial A t‖)).symm

/-- Integrating the average over the `q` residue arcs exactly recovers the
original circle norm. -/
theorem residueNormAverage_integral (A : Finset ℤ) (a : ℝ) :
    (∫ t in a..a + 1, residueNormAverage q A t) = littlewoodNorm A := by
  let f : ℝ → ℝ := fun x => ‖fourierPolynomial A (x : Circle)‖
  have hf : Continuous f :=
    ((fourierPolynomial_continuous A).comp (AddCircle.continuous_mk' (1 : ℝ))).norm
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hexp (t : ℝ) : residueNormAverage q A t =
      (q : ℝ)⁻¹ * ∑ r ∈ Finset.range q, f ((r : ℝ) / q + t / q) := by
    simp only [residueNormAverage, integral_cyclicMeasure, sum_zmod_eq_sum_range,
      smul_eq_mul, ZMod.toAddCircle_natCast]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    congr 2
    rw [← QuotientAddGroup.mk_add]
    congr 1
    ring
  simp_rw [hexp]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_comp_add_div f hq, smul_eq_mul]
    rw [← Finset.mul_sum, inv_mul_cancel_left₀ hq]
    have he (r : ℕ) : (r : ℝ) / q + (a + 1) / q =
        ((r + 1 : ℕ) : ℝ) / (q : ℝ) + a / q := by push_cast; ring
    simp_rw [he]
    rw [intervalIntegral.sum_integral_adjacent_intervals
      (fun k _ => hf.intervalIntegrable _ _)]
    simp only [Nat.cast_zero, zero_div, zero_add, div_self hq]
    rw [add_comm 1]
    exact (littlewoodNorm_eq_interval A (a / q)).symm
  · intro r _
    exact ((hf.comp ((continuous_const.add (continuous_id.div_const (q : ℝ)))))).intervalIntegrable _ _

theorem fourierPolynomial_neg_argument (A : Finset ℤ) (t : Circle) :
    fourierPolynomial A (-t) = conj (fourierPolynomial A t) := by
  unfold fourierPolynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [← fourier_neg]
  simp [fourier_apply, smul_neg, neg_smul]

theorem residueNormAverage_even (A : Finset ℤ) (t : ℝ) :
    residueNormAverage q A (-t) = residueNormAverage q A t := by
  unfold residueNormAverage
  simp only [integral_cyclicMeasure, smul_eq_mul]
  congr 1
  have hp (j : ZMod q) : ‖fourierPolynomial A
      (((-t / q : ℝ) : Circle) + ZMod.toAddCircle j)‖ =
      ‖fourierPolynomial A (((t / q : ℝ) : Circle) + ZMod.toAddCircle (-j))‖ := by
    have he : (((-t / q : ℝ) : Circle) + ZMod.toAddCircle j) =
        -(((t / q : ℝ) : Circle) + ZMod.toAddCircle (-j)) := by
      simp [neg_div, map_neg, add_comm]
    rw [he, fourierPolynomial_neg_argument, Complex.norm_conj]
  simp_rw [hp]
  exact (Equiv.neg (ZMod q)).sum_comp Finset.univ
    (fun j => ‖fourierPolynomial A (((t / q : ℝ) : Circle) + ZMod.toAddCircle j)‖)
    (by simp)

theorem residueNormAverage_half_integral (A : Finset ℤ) :
    2 * (∫ t in (0 : ℝ)..(1 / 2 : ℝ), residueNormAverage q A t) = littlewoodNorm A := by
  have hc := residueNormAverage_continuous q A
  have hleft : (∫ t in (-1 / 2 : ℝ)..(0 : ℝ), residueNormAverage q A t) =
      ∫ t in (0 : ℝ)..(1 / 2 : ℝ), residueNormAverage q A t := by
    have h := intervalIntegral.integral_comp_neg (residueNormAverage q A)
      (a := (0 : ℝ)) (b := (1 / 2 : ℝ))
    simpa only [residueNormAverage_even, neg_zero, neg_div] using h.symm
  have hsum := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable (-1 / 2) 0) (hc.intervalIntegrable 0 (1 / 2))
  rw [hleft] at hsum
  have hfull := residueNormAverage_integral q A (-1 / 2)
  norm_num at hfull
  linarith

theorem two_mul_integral_residue_le (A : Finset ℤ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 2) :
    2 * (∫ t in a..b, residueNormAverage q A t) ≤ littlewoodNorm A := by
  have hi := intervalIntegral.integral_mono_interval (μ := volume) ha hab hb
    (Filter.Eventually.of_forall (residueNormAverage_nonneg q A))
    ((residueNormAverage_continuous q A).intervalIntegrable 0 (1 / 2))
  have he := residueNormAverage_half_integral q A
  linarith

@[fun_prop] theorem boundaryW_continuous_s (C : Finset (ZMod q × ℤ)) (t : ℝ) :
    Continuous (boundaryW q C t) := by
  unfold boundaryW
  simp_rw [integral_cyclicMeasure, smul_eq_mul]
  apply continuous_const.mul
  apply continuous_finsetSum
  intro j _
  unfold cyclicPolynomial
  fun_prop

theorem boundary_pointwise_lower {M : ℕ} (hM : 0 < M)
    (C : Finset (ZMod q × ℤ)) {t : ℝ} (ht : 0 < t) :
    boundaryW q C 0 (((M : ℝ) * t : ℝ) : Circle) / (Real.pi * t) -
      2 * boundaryQ q C (((M : ℝ) * t : ℝ) : Circle) ≤
        2 * residueNormAverage q (blockInflation q M C) t := by
  have hf := (abs_le.mp (boundary_freezing q C t (((M : ℝ) * t : ℝ) : Circle))).1
  rw [abs_of_pos ht, boundaryW_inflation_identity q hM] at hf
  have hphase : ‖1 - fourier 1 (t : Circle)‖ ≤ 2 * Real.pi * t := by
    rw [norm_one_sub_fourier_one]
    have hs := Real.abs_sin_le_abs (x := Real.pi * t)
    rw [abs_of_pos (mul_pos Real.pi_pos ht)] at hs
    linarith
  have hm := mul_le_mul_of_nonneg_right hphase
    (residueNormAverage_nonneg q (blockInflation q M C) t)
  have hdiv : boundaryW q C 0 (((M : ℝ) * t : ℝ) : Circle) / (Real.pi * t) ≤
      2 * residueNormAverage q (blockInflation q M C) t +
        2 * boundaryQ q C (((M : ℝ) * t : ℝ) : Circle) := by
    apply (div_le_iff₀ (mul_pos Real.pi_pos ht)).mpr
    change -(2 * Real.pi * t * boundaryQ q C _) ≤
      ‖1 - fourier 1 (t : Circle)‖ * residueNormAverage q (blockInflation q M C) t -
        boundaryW q C 0 _ at hf
    nlinarith
  linarith

theorem circle_integral_eq_unit_interval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Circle → E) : (∫ x, f x ∂circleMeasure) = ∫ x in (0 : ℝ)..1, f (x : Circle) := by
  unfold circleMeasure
  rw [AddCircle.integral_haarAddCircle]
  simpa using (AddCircle.intervalIntegral_preimage (1 : ℝ) 0 f).symm

theorem boundaryW_zero_periodic (C : Finset (ZMod q × ℤ)) :
    Function.Periodic (fun x : ℝ => boundaryW q C 0 (x : Circle)) 1 := by
  intro x
  dsimp only
  rw [AddCircle.coe_add_period]

theorem boundaryQ_periodic (C : Finset (ZMod q × ℤ)) :
    Function.Periodic (fun x : ℝ => boundaryQ q C (x : Circle)) 1 := by
  intro x
  dsimp only
  rw [AddCircle.coe_add_period]

theorem boundary_arc_lower {M : ℕ} (hM : 0 < M)
    (C : Finset (ZMod q × ℤ)) {a : ℝ} (ha : a ≤ 1 / 2)
    (hMa : 1 ≤ (M : ℝ) * a) :
    boundaryNorm q C / Real.pi * (Real.log ((M : ℝ) * a) - 2) -
      2 * (a + 1 / M) * Real.sqrt (boundaryMass C : ℝ) ≤
        littlewoodNorm (blockInflation q M C) := by
  let f : ℝ → ℝ := fun x => boundaryW q C 0 (x : Circle)
  let g : ℝ → ℝ := fun x => boundaryQ q C (x : Circle)
  have hf : Continuous f := (boundaryW_continuous_s q C 0).comp
    (AddCircle.continuous_mk' (1 : ℝ))
  have hg : Continuous g := (boundaryQ_continuous q C).comp
    (AddCircle.continuous_mk' (1 : ℝ))
  have hf0 : ∀ x, 0 ≤ f x := fun x => boundaryW_nonneg q C 0 (x : Circle)
  have hg0 : ∀ x, 0 ≤ g x := fun x => boundaryQ_nonneg q C (x : Circle)
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hia : 1 / (M : ℝ) ≤ a := (div_le_iff₀ hm).mpr (by nlinarith)
  have hi0 : 0 < 1 / (M : ℝ) := by positivity
  have ha0 : 0 ≤ a := hi0.le.trans hia
  have hfi : IntervalIntegrable (fun t => f ((M : ℝ) * t) / t)
      volume (1 / (M : ℝ)) a :=
    continuous_intervalIntegrable_div_id (hf.comp (continuous_const.mul continuous_id)) hi0 hia
  have hgi : IntervalIntegrable (fun t => g ((M : ℝ) * t))
      volume (1 / (M : ℝ)) a :=
    (hg.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hpoint : (∫ t in (1 / (M : ℝ))..a,
      (Real.pi)⁻¹ * (f ((M : ℝ) * t) / t) - 2 * g ((M : ℝ) * t)) ≤
      ∫ t in (1 / (M : ℝ))..a, 2 * residueNormAverage q (blockInflation q M C) t := by
    apply intervalIntegral.integral_mono_on hia
      ((hfi.const_mul _).sub (hgi.const_mul _))
      (((residueNormAverage_continuous q _).const_mul 2).intervalIntegrable _ _)
    intro t ht
    convert boundary_pointwise_lower q hM C (hi0.trans_le ht.1) using 1
    dsimp only [f, g]
    ring
  rw [intervalIntegral.integral_sub (hfi.const_mul _) (hgi.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_scaled_div_id f hm.ne',
    mul_one_div_cancel hm.ne'] at hpoint
  have hres := two_mul_integral_residue_le q (blockInflation q M C) hi0.le hia ha
  have hmeanf : (∫ x in (0 : ℝ)..1, f x) = boundaryNorm q C := by
    rw [← circle_integral_eq_unit_interval]
    exact integral_boundaryW_zero q C
  have hmeang : (∫ x in (0 : ℝ)..1, g x) ≤ Real.sqrt (boundaryMass C : ℝ) := by
    rw [← circle_integral_eq_unit_interval]
    exact integral_boundaryQ_le q C
  have hh := periodic_harmonic_lower hf (boundaryW_zero_periodic q C) hf0 hMa
  rw [hmeanf] at hh
  have hqint : (∫ t in (1 / (M : ℝ))..a, g ((M : ℝ) * t)) ≤
      (a + 1 / M) * Real.sqrt (boundaryMass C : ℝ) := by
    calc
      _ ≤ ∫ t in (0 : ℝ)..a, g ((M : ℝ) * t) :=
        intervalIntegral.integral_mono_interval hi0.le hia le_rfl
          (Filter.Eventually.of_forall (fun t => hg0 ((M : ℝ) * t)))
          ((hg.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)
      _ ≤ (a + 1 / M) * ∫ x in (0 : ℝ)..1, g x :=
        periodic_scaled_integral_le hg (boundaryQ_periodic q C) hg0 hm ha0
      _ ≤ _ := mul_le_mul_of_nonneg_left hmeang (by positivity)
  have hh' := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr Real.pi_pos.le)
  simp only [div_eq_mul_inv] at *
  nlinarith

end LittlewoodInverse
