import LittlewoodInverse.BoundaryExtraction
import LittlewoodInverse.PeriodicHarmonic
import LittlewoodInverse.IntervalNorm

open scoped BigOperators Interval
open MeasureTheory

namespace LittlewoodInverse

theorem sine_reciprocal_error {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 1 / 2) :
    0 ≤ 1 / Real.sin (Real.pi * t) - 1 / (Real.pi * t) ∧
    1 / Real.sin (Real.pi * t) - 1 / (Real.pi * t) ≤ Real.pi ^ 2 := by
  have hx : 0 < Real.pi * t := mul_pos Real.pi_pos ht
  have hslow : 2 * t ≤ Real.sin (Real.pi * t) := by
    have h := Real.mul_le_sin hx.le (by nlinarith [Real.pi_pos])
    have he : 2 / Real.pi * (Real.pi * t) = 2 * t := by field_simp
    rwa [he] at h
  have hs : 0 < Real.sin (Real.pi * t) := by linarith
  have hsupper : Real.sin (Real.pi * t) ≤ Real.pi * t := Real.sin_le hx.le
  constructor
  · exact sub_nonneg.mpr (one_div_le_one_div_of_le hs hsupper)
  · have he : 1 / Real.sin (Real.pi * t) - 1 / (Real.pi * t) =
        (Real.pi * t - Real.sin (Real.pi * t)) /
          (Real.sin (Real.pi * t) * (Real.pi * t)) := by field_simp
    rw [he]
    apply (div_le_iff₀ (mul_pos hs hx)).mpr
    have hc := Real.sin_ge_sub_cube hx.le
    have hm := mul_le_mul_of_nonneg_right hslow
      (show 0 ≤ Real.pi ^ 2 * (Real.pi * t) by positivity)
    have hp := mul_nonneg (show 0 ≤ Real.pi ^ 3 * t ^ 2 by positivity)
      (show 0 ≤ 12 - t by linarith)
    nlinarith

variable (q : ℕ) [NeZero q]

theorem boundary_pointwise_asymptotic_error {M : ℕ} (hM : 0 < M)
    (C : Finset (ZMod q × ℤ)) {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 1 / 2) :
    |2 * residueNormAverage q (blockInflation q M C) t -
        boundaryW q C 0 (((M : ℝ) * t : ℝ) : Circle) / (Real.pi * t)| ≤
      Real.pi * boundaryQ q C (((M : ℝ) * t : ℝ) : Circle) +
        Real.pi ^ 2 * boundaryW q C 0 (((M : ℝ) * t : ℝ) : Circle) := by
  let s : Circle := (((M : ℝ) * t : ℝ) : Circle)
  have hslow : 2 * t ≤ Real.sin (Real.pi * t) := by
    have h := Real.mul_le_sin (mul_pos Real.pi_pos ht).le (by nlinarith [Real.pi_pos])
    have he : 2 / Real.pi * (Real.pi * t) = 2 * t := by field_simp
    rwa [he] at h
  have hs : 0 < Real.sin (Real.pi * t) := by linarith
  have hid := boundaryW_inflation_identity q hM C t
  rw [norm_one_sub_fourier_one, abs_of_pos hs] at hid
  have hdiv : 2 * residueNormAverage q (blockInflation q M C) t =
      boundaryW q C t s / Real.sin (Real.pi * t) := by
    apply (eq_div_iff hs.ne').mpr
    dsimp only [s]
    change boundaryW q C t _ = 2 * Real.sin (Real.pi * t) * residueNormAverage q _ t at hid
    nlinarith
  rw [hdiv]
  have hsplit : boundaryW q C t s / Real.sin (Real.pi * t) -
      boundaryW q C 0 s / (Real.pi * t) =
      (boundaryW q C t s - boundaryW q C 0 s) / Real.sin (Real.pi * t) +
      boundaryW q C 0 s * (1 / Real.sin (Real.pi * t) - 1 / (Real.pi * t)) := by ring
  change |boundaryW q C t s / _ - boundaryW q C 0 s / _| ≤ _
  rw [hsplit]
  have hfreeze := boundary_freezing q C t s
  rw [abs_of_pos ht] at hfreeze
  have hfirst : |(boundaryW q C t s - boundaryW q C 0 s) / Real.sin (Real.pi * t)| ≤
      Real.pi * boundaryQ q C s := by
    rw [abs_div, abs_of_pos hs]
    apply (div_le_iff₀ hs).mpr
    have hm := mul_le_mul_of_nonneg_left hslow
      (mul_nonneg Real.pi_pos.le (boundaryQ_nonneg q C s))
    nlinarith
  have hkernel := sine_reciprocal_error ht ht2
  have hsecond : |boundaryW q C 0 s *
      (1 / Real.sin (Real.pi * t) - 1 / (Real.pi * t))| ≤ Real.pi ^ 2 * boundaryW q C 0 s := by
    rw [abs_of_nonneg (mul_nonneg (boundaryW_nonneg q C 0 s) hkernel.1)]
    nlinarith [mul_le_mul_of_nonneg_left hkernel.2 (boundaryW_nonneg q C 0 s)]
  exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)

theorem residueNormAverage_le_card (A : Finset ℤ) (t : ℝ) :
    residueNormAverage q A t ≤ (A.card : ℝ) := by
  calc
    _ ≤ ∫ _j : ZMod q, (A.card : ℝ) ∂cyclicMeasure q := by
      apply integral_mono (cyclic_integrable q _) (integrable_const _)
      intro j
      calc
        _ ≤ ∑ a ∈ A, ‖fourier a _‖ := norm_sum_le _ _
        _ = _ := by simp [fourier_apply]
    _ = _ := by simp

theorem boundary_asymptotic_cut_error {M : ℕ} (hM : 2 ≤ M)
    (C : Finset (ZMod q × ℤ)) :
    |littlewoodNorm (blockInflation q M C) - (Real.pi)⁻¹ *
      (∫ u in (1 : ℝ)..((M : ℝ) / 2), boundaryW q C 0 (u : Circle) / u)| ≤
      2 * (C.card : ℝ) + Real.pi * Real.sqrt (boundaryMass C : ℝ) +
        Real.pi ^ 2 * boundaryNorm q C := by
  let f : ℝ → ℝ := fun x => boundaryW q C 0 (x : Circle)
  let g : ℝ → ℝ := fun x => boundaryQ q C (x : Circle)
  let A := blockInflation q M C
  let G := residueNormAverage q A
  have hm : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hm2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have ha : (0 : ℝ) < 1 / M := by positivity
  have hab : 1 / (M : ℝ) ≤ 1 / 2 := by apply (div_le_div_iff₀ hm (by norm_num)).mpr; linarith
  have hf : Continuous f := (boundaryW_continuous_s q C 0).comp (AddCircle.continuous_mk' (1 : ℝ))
  have hg : Continuous g := (boundaryQ_continuous q C).comp (AddCircle.continuous_mk' (1 : ℝ))
  have hG : Continuous G := residueNormAverage_continuous q A
  have hfM : Continuous (fun t => f ((M : ℝ) * t)) := hf.comp (continuous_const.mul continuous_id)
  have hgM : Continuous (fun t => g ((M : ℝ) * t)) := hg.comp (continuous_const.mul continuous_id)
  have hfi := continuous_intervalIntegrable_div_id hfM ha hab
  have hgi := hgM.intervalIntegrable (μ := volume) (1 / (M : ℝ)) (1 / 2)
  have hwi := hfM.intervalIntegrable (μ := volume) (1 / (M : ℝ)) (1 / 2)
  have hGi := hG.intervalIntegrable (μ := volume) (1 / (M : ℝ)) (1 / 2)
  have hdiff : |2 * (∫ t in (1 / (M : ℝ))..(1 / 2 : ℝ), G t) -
      Real.pi⁻¹ * (∫ t in (1 / (M : ℝ))..(1 / 2 : ℝ), f ((M : ℝ) * t) / t)| ≤
      Real.pi * (∫ t in (1 / (M : ℝ))..(1 / 2 : ℝ), g ((M : ℝ) * t)) +
      Real.pi ^ 2 * (∫ t in (1 / (M : ℝ))..(1 / 2 : ℝ), f ((M : ℝ) * t)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hGi.const_mul _) (hfi.const_mul _)]
    calc
      _ ≤ ∫ t in (1 / (M : ℝ))..(1 / 2 : ℝ),
          |2 * G t - Real.pi⁻¹ * (f ((M : ℝ) * t) / t)| :=
        intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ t in (1 / (M : ℝ))..(1 / 2 : ℝ),
          (Real.pi * g ((M : ℝ) * t) + Real.pi ^ 2 * f ((M : ℝ) * t)) := by
        apply intervalIntegral.integral_mono_on hab
          (((hGi.const_mul _).sub (hfi.const_mul _)).abs)
          ((hgi.const_mul _).add (hwi.const_mul _))
        intro t ht
        convert boundary_pointwise_asymptotic_error q (show 0 < M by omega) C
          (ha.trans_le ht.1) ht.2 using 1
        dsimp only [G, A, f, g]
        congr 1
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add (hgi.const_mul _) (hwi.const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hscaled {w : ℝ → ℝ} (hw : Continuous w) (hp : Function.Periodic w 1)
      (h0 : ∀ x, 0 ≤ w x) :
      (∫ t in (1 / (M : ℝ))..(1 / 2 : ℝ), w ((M : ℝ) * t)) ≤
        ∫ x in (0 : ℝ)..1, w x := by
    have hmean : 0 ≤ ∫ x in (0 : ℝ)..1, w x :=
      intervalIntegral.integral_nonneg_of_forall (by norm_num) h0
    calc
      _ ≤ ∫ t in (0 : ℝ)..(1 / 2 : ℝ), w ((M : ℝ) * t) :=
        intervalIntegral.integral_mono_interval ha.le hab le_rfl
          (Filter.Eventually.of_forall (fun t => h0 ((M : ℝ) * t)))
          ((hw.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)
      _ ≤ (1 / 2 + 1 / (M : ℝ)) * ∫ x in (0 : ℝ)..1, w x :=
        periodic_scaled_integral_le hw hp h0 hm (by norm_num)
      _ ≤ _ := mul_le_of_le_one_left hmean (by linarith)
  have hsf := hscaled hf (boundaryW_zero_periodic q C) (fun x => boundaryW_nonneg q C 0 _)
  have hsg := hscaled hg (boundaryQ_periodic q C) (fun x => boundaryQ_nonneg q C _)
  have hmeanf : (∫ x in (0 : ℝ)..1, f x) = boundaryNorm q C := by
    rw [← circle_integral_eq_unit_interval]
    exact integral_boundaryW_zero q C
  have hmeang : (∫ x in (0 : ℝ)..1, g x) ≤ Real.sqrt (boundaryMass C : ℝ) := by
    rw [← circle_integral_eq_unit_interval]
    exact integral_boundaryQ_le q C
  rw [hmeanf] at hsf
  rw [integral_scaled_div_id f hm.ne', mul_one_div_cancel hm.ne', mul_one_div] at hdiff
  have hsg' := hsg.trans hmeang
  have hzero : 0 ≤ 2 * ∫ t in (0 : ℝ)..(1 / (M : ℝ)), G t := by
    apply mul_nonneg (by norm_num)
    exact intervalIntegral.integral_nonneg_of_forall ha.le (residueNormAverage_nonneg q A)
  have hsmall : 2 * (∫ t in (0 : ℝ)..(1 / (M : ℝ)), G t) ≤ 2 * C.card := by
    have hh : (∫ t in (0 : ℝ)..(1 / (M : ℝ)), G t) ≤ (1 / (M : ℝ)) * A.card := by
      have hi := intervalIntegral.integral_mono_on (μ := volume) ha.le (hG.intervalIntegrable _ _)
        (intervalIntegrable_const (c := (A.card : ℝ)))
        (fun t _ => residueNormAverage_le_card q A t)
      simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using hi
    have hc : (A.card : ℝ) = (M : ℝ) * C.card := by
      dsimp only [A]
      rw [blockInflation_card q (show 0 < M by omega) C, Nat.cast_mul]
    rw [hc] at hh
    have he : (1 / (M : ℝ)) * ((M : ℝ) * C.card) = C.card := by field_simp
    rw [he] at hh
    linarith
  have hfull := residueNormAverage_half_integral q A
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hG.intervalIntegrable 0 (1 / (M : ℝ))) (hG.intervalIntegrable (1 / (M : ℝ)) (1 / 2))
  change (∫ t in (0 : ℝ)..(1 / (M : ℝ)), G t) +
    (∫ t in (1 / (M : ℝ))..(1 / 2 : ℝ), G t) = ∫ t in (0 : ℝ)..(1 / 2 : ℝ), G t at hadd
  change 2 * (∫ t in (0 : ℝ)..(1 / 2 : ℝ), G t) = littlewoodNorm A at hfull
  change |littlewoodNorm A - Real.pi⁻¹ * (∫ u in (1 : ℝ)..((M : ℝ) / 2), f u / u)| ≤ _
  rw [abs_le] at hdiff ⊢
  have hfbound := mul_le_mul_of_nonneg_left hsf (sq_nonneg Real.pi)
  have hgbound := mul_le_mul_of_nonneg_left hsg' Real.pi_pos.le
  constructor <;> linarith

theorem boundary_asymptotic_explicit {M : ℕ} (hM : 2 ≤ M)
    (C : Finset (ZMod q × ℤ)) :
    |littlewoodNorm (blockInflation q M C) -
      boundaryNorm q C / Real.pi * Real.log (M : ℝ)| ≤
      2 * (C.card : ℝ) + Real.pi * Real.sqrt (boundaryMass C : ℝ) +
        Real.pi ^ 2 * boundaryNorm q C + (2 + Real.log 2) * boundaryNorm q C / Real.pi := by
  have hcut := boundary_asymptotic_cut_error q hM C
  have hX : 1 ≤ (M : ℝ) / 2 := by
    have hh : (2 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hf : Continuous (fun x : ℝ => boundaryW q C 0 (x : Circle)) :=
    (boundaryW_continuous_s q C 0).comp (AddCircle.continuous_mk' (1 : ℝ))
  have hh := periodic_harmonic_error hf (boundaryW_zero_periodic q C)
    (fun x => boundaryW_nonneg q C 0 _) hX
  have hmean : (∫ x in (0 : ℝ)..1, boundaryW q C 0 (x : Circle)) = boundaryNorm q C := by
    rw [← circle_integral_eq_unit_interval]
    exact integral_boundaryW_zero q C
  rw [hmean] at hh
  have hm : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  rw [Real.log_div hm.ne' (by norm_num)] at hh
  rw [abs_le] at hcut hh ⊢
  have hlo := mul_le_mul_of_nonneg_left hh.1 (inv_nonneg.mpr Real.pi_pos.le)
  have hhi := mul_le_mul_of_nonneg_left hh.2 (inv_nonneg.mpr Real.pi_pos.le)
  have hpos : 0 ≤ boundaryNorm q C * Real.log 2 * Real.pi⁻¹ := by
    exact mul_nonneg (mul_nonneg (boundaryNorm_nonneg q C) (Real.log_nonneg (by norm_num)))
      (inv_nonneg.mpr Real.pi_pos.le)
  simp only [div_eq_mul_inv] at *
  constructor <;> nlinarith

/-- The second assertion of the uniform boundary proposition: with the
actual cell set fixed, the additive error is bounded independently of `M`. -/
theorem boundary_norm_asymptotic (C : Finset (ZMod q × ℤ)) :
    (fun M : ℕ => littlewoodNorm (blockInflation q M C) -
      boundaryNorm q C / Real.pi * Real.log (M : ℝ)) =O[Filter.atTop] (fun _ : ℕ => (1 : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound
    (2 * (C.card : ℝ) + Real.pi * Real.sqrt (boundaryMass C : ℝ) +
      Real.pi ^ 2 * boundaryNorm q C + (2 + Real.log 2) * boundaryNorm q C / Real.pi) ?_
  filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with M hM
  simpa only [Real.norm_eq_abs, abs_one, mul_one] using boundary_asymptotic_explicit q hM C

end LittlewoodInverse
