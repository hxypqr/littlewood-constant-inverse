import LittlewoodInverse.LandauSpectral
import LittlewoodInverse.DirichletKernel

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LittlewoodInverse
namespace Landau

theorem circle_even_integral (f : Circle → ℝ) (hf : Integrable f circleMeasure)
    (he : ∀ t, f (-t) = f t) :
    (∫ t, f t ∂circleMeasure) = 2 * ∫ x : ℝ in Set.Ioc 0 (1/2), f (x : Circle) := by
  have hm : (volume : Measure Circle) = circleMeasure := by
    simpa [circleMeasure] using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
  have hv : Integrable f volume := by rwa [hm]
  have hp := (AddCircle.measurePreserving_mk (1 : ℝ) (-(1/2 : ℝ))).integrable_comp_of_integrable hv
  have hi : IntervalIntegrable (fun x : ℝ => f (x : Circle)) volume (-(1/2 : ℝ)) (1/2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    simpa only [show -(1/2 : ℝ)+1 = 1/2 by norm_num, IntegrableOn,
      Function.comp_def] using hp
  have hn := intervalIntegral.integral_comp_neg (f := fun x : ℝ => f (x : Circle))
    (a := 0) (b := (1/2 : ℝ))
  simp only [show ∀ x : ℝ, ((-x : ℝ) : Circle) = -(x : Circle) from fun _ => rfl,
    he, neg_zero] at hn
  have hl : IntervalIntegrable (fun x : ℝ => f (x : Circle)) volume (-(1/2 : ℝ)) 0 :=
    hi.mono_set (by norm_num [Set.uIcc_of_le]; intro x hx; constructor <;> linarith [hx.1,hx.2])
  have hr : IntervalIntegrable (fun x : ℝ => f (x : Circle)) volume 0 (1/2 : ℝ) :=
    hi.mono_set (by norm_num [Set.uIcc_of_le]; intro x hx; constructor <;> linarith [hx.1,hx.2])
  have hs := intervalIntegral.integral_add_adjacent_intervals hl hr
  have hb := AddCircle.intervalIntegral_preimage (1 : ℝ) (-(1/2 : ℝ)) f
  norm_num at hb
  rw [hm] at hb
  rw [← hb, ← hs, ← hn, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1/2)]
  ring

noncomputable def model (z : ℂ) : ℂ := (‖1-z‖ : ℂ)/(1-z)

theorem model_norm {z : ℂ} (hz : z ≠ 1) : ‖model z‖ = 1 := by
  have hd : 1-z ≠ 0 := sub_ne_zero.mpr hz.symm
  simp only [model,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _),div_self (norm_ne_zero_iff.mpr hd)]

theorem conj_model {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    conj (model z) = -z*model z := by
  have hd : 1-z ≠ 0 := sub_ne_zero.mpr hz1.symm
  have hdc : 1-conj z ≠ 0 := by
    have hh := (map_ne_zero (starRingEnd ℂ)).mpr hd
    simpa only [map_sub,map_one] using hh
  have hmul : z*conj z = 1 := by rw [Complex.mul_conj',hz]; norm_num
  unfold model
  simp only [map_div₀,map_sub,map_one,Complex.conj_ofReal]
  field_simp
  linear_combination -(‖1-z‖ : ℂ)*hmul

/-- The exact two-sided model phase identity, expressed without a choice
of square-root branch. -/
theorem model_identity {N : ℕ} (hN : 0 < N) {z : ℂ}
    (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    model z+z^(N-1)*conj (model z) =
      (‖1-z‖ : ℂ)*(∑ k ∈ Finset.range N, z^k) := by
  have hd : 1-z ≠ 0 := sub_ne_zero.mpr hz1.symm
  have hp : z^(N-1)*z=z^N := by rw [← pow_succ,Nat.sub_add_cancel (by omega)]
  have hg := geom_sum_mul z N
  rw [conj_model hz hz1]
  have he : model z+z^(N-1)*(-z*model z) = (1-z^N)*model z := by
    calc
      _ = (1-z^(N-1)*z)*model z := by ring
      _ = _ := by rw [hp]
  rw [he,model]
  rw [← mul_div_assoc]
  apply (div_eq_iff hd).mpr
  linear_combination (‖1-z‖ : ℂ)*hg

theorem fourier_distance_lower (x : ℝ) (hx : |x| ≤ 1/2) :
    4*|x| ≤ ‖1-fourier 1 (x : Circle)‖ := by
  rw [norm_sub_rev,norm_fourier_sub_one]
  norm_num only [Int.cast_one,mul_one]
  have hh : |Real.pi*x| ≤ Real.pi/2 := by
    rw [abs_mul,abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hs := Real.mul_abs_le_abs_sin hh
  rw [abs_mul,abs_of_pos Real.pi_pos] at hs
  have he : (2/Real.pi)*(Real.pi*|x|) = 2*|x| := by field_simp
  rw [he] at hs
  linarith

end Landau
end LittlewoodInverse

