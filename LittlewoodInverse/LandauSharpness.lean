import LittlewoodInverse.LandauSpectral
import LittlewoodInverse.HardyExternal
import LittlewoodInverse.PacketCertificates

open scoped BigOperators ComplexConjugate Topology
open MeasureTheory

namespace LittlewoodInverse
namespace Landau

theorem polynomial_eval (N : ℕ) (z : ℂ) :
    (polynomial N).eval z = ∑ k ∈ Finset.range N, (b k : ℂ)*z^k := by
  simp only [polynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

theorem polynomial_eval_succ (n : ℕ) (z : ℂ) :
    (polynomial (n+1)).eval z = (polynomial n).eval z + (b n : ℂ)*z^n := by
  simp only [polynomial_eval, Finset.sum_range_succ]

theorem polynomial_boundary_identity (n : ℕ) (z : ℂ) :
    (1-z)*(polynomial (n+1)).eval z =
      1-(∑ k ∈ Finset.range n, ((b k-b (k+1) : ℝ) : ℂ)*z^(k+1))-
        (b n : ℂ)*z^(n+1) := by
  induction n with
  | zero => simp [polynomial_eval]
  | succ n ih =>
    rw [polynomial_eval_succ (n+1), Finset.sum_range_succ]
    rw [mul_add, ih]
    push_cast
    simp only [pow_succ]
    ring

theorem polynomial_boundary_weights (n : ℕ) :
    (∑ k ∈ Finset.range n, (b k-b (k+1)))+b n = 1 := by
  have hh := congrArg Complex.re (polynomial_boundary_identity n 1)
  simp only [sub_self, zero_mul, one_pow, mul_one, Complex.sub_re,
    Complex.one_re, Complex.zero_re, Complex.re_sum, Complex.ofReal_re] at hh
  linarith

theorem re_lt_one_of_norm_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) (hne : z ≠ 1) : z.re < 1 := by
  have hre : z.re ≤ 1 := (Complex.re_le_norm _).trans hz
  by_contra hh
  have he : z.re = 1 := le_antisymm hre (le_of_not_gt hh)
  have hsq := Complex.normSq_apply z
  have hnorm : ‖z‖^2 ≤ 1 := by nlinarith [norm_nonneg z]
  have hi : z.im = 0 := by
    rw [Complex.normSq_eq_norm_sq] at hsq
    rw [he] at hsq
    nlinarith [sq_nonneg z.im]
  apply hne
  apply Complex.ext <;> simp [he,hi]

/-- The truncated inverse-square-root polynomial has no zeros in the
closed unit disk. This proves the zero-free assertion inside Appendix B. -/
theorem polynomial_ne_zero_closedDisk {N : ℕ} (hN : 0 < N)
    (z : ℂ) (hz : ‖z‖ ≤ 1) : (polynomial N).eval z ≠ 0 := by
  cases N with
  | zero => omega
  | succ n =>
    by_cases hz1 : z=1
    · subst z
      intro he
      have hr := congrArg Complex.re he
      rw [polynomial_eval] at hr
      simp only [one_pow,mul_one,Complex.re_sum,Complex.ofReal_re,Complex.zero_re] at hr
      have hp : 0 < ∑ k ∈ Finset.range (n+1), b k :=
        Finset.sum_pos (fun k _ => b_pos k) (Finset.nonempty_range_iff.mpr (by omega))
      linarith
    · cases n with
      | zero => simp [polynomial_eval]
      | succ n =>
        intro hzero
        have hr := congrArg Complex.re (polynomial_boundary_identity (n+1) z)
        rw [hzero,mul_zero] at hr
        simp only [Complex.zero_re,Complex.sub_re,Complex.one_re,Complex.re_sum,
          Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hr
        have hpow (k : ℕ) : (z^k).re ≤ 1 := by
          calc
            _ ≤ ‖z^k‖ := Complex.re_le_norm _
            _ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hz
        have hpoint (k : ℕ) : (b k-b (k+1))*(z^(k+1)).re ≤ b k-b (k+1) := by
          exact mul_le_of_le_one_right (sub_nonneg.mpr (b_succ_lt k).le) (hpow _)
        have hstrict : (b 0-b 1)*(z^(0+1)).re < b 0-b 1 := by
          simpa only [Nat.zero_add,pow_one,mul_one] using
            mul_lt_mul_of_pos_left (re_lt_one_of_norm_le_one hz hz1) (sub_pos.mpr (b_succ_lt 0))
        have hsum : (∑ k ∈ Finset.range (n+1), (b k-b (k+1))*(z^(k+1)).re) <
            ∑ k ∈ Finset.range (n+1), (b k-b (k+1)) :=
          Finset.sum_lt_sum (fun k _ => hpoint k) ⟨0,Finset.mem_range.mpr (by omega),hstrict⟩
        have hlast := mul_le_of_le_one_right (b_pos (n+1)).le (hpow (n+1+1))
        have hw := polynomial_boundary_weights (n+1)
        linarith

/-- A rational function whose polynomial denominator is zero-free on the
closed disk has the usual analytic Fourier support on the circle. -/
theorem polynomial_quotient_spectrum (P Q : Polynomial ℂ)
    (hQ : ∀ z : ℂ, ‖z‖ ≤ 1 → Q.eval z ≠ 0) (n : ℤ) (hn : n < 0) :
    circleFourierCoeff (fun t => evalCircle P t / evalCircle Q t) n = 0 := by
  let F : ℂ → ℂ := fun z => P.eval z / Q.eval z
  have hcont (z : ℂ) (hz : ‖z‖ ≤ 1) : ContinuousAt F z :=
    P.continuous.continuousAt.div Q.continuous.continuousAt (hQ z hz)
  have hcontOn : ContinuousOn F (Metric.closedBall 0 1) := by
    intro z hz
    exact (hcont z (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz)).continuousWithinAt
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0 : ℂ) 1).bddAbove_image hcontOn.norm
  have hdiff : DifferentiableOn ℂ F (Metric.ball 0 1) := by
    intro z hz
    have hz' : ‖z‖ ≤ 1 := le_of_lt (by simpa only [Metric.mem_ball,dist_zero_right] using hz)
    exact (P.differentiableAt.div Q.differentiableAt (hQ z hz')).differentiableWithinAt
  have hbound (z : ℂ) (hz : ‖z‖ < 1) : ‖F z‖ ≤ B :=
    hB (Set.mem_image_of_mem _ (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz.le))
  obtain ⟨g,_,_,hlim,hs,_⟩ := HardyExternal.bounded_holomorphic_radial_boundary F B hdiff hbound
  have hae : (fun t => evalCircle P t / evalCircle Q t) =ᵐ[circleMeasure] g := by
    filter_upwards [hlim] with t ht
    have hz : ‖fourier (T := (1 : ℝ)) 1 t‖ ≤ 1 := by simp [fourier_apply]
    have hr : Continuous (fun r : ℝ => radialPoint r t) := by unfold radialPoint; fun_prop
    have hr1 : Filter.Tendsto (fun r : ℝ => radialPoint r t)
        (𝓝 (1 : ℝ)) (𝓝 (radialPoint 1 t)) := hr.continuousAt.tendsto
    have hrad : Filter.Tendsto (fun r : ℝ => radialPoint r t)
        (𝓝[Set.Iio 1] 1) (𝓝 (fourier 1 t)) := by
      simpa only [radialPoint,Nat.cast_one,Complex.ofReal_one,one_mul] using
        (hr1.mono_left nhdsWithin_le_nhds)
    exact tendsto_nhds_unique ((hcont _ hz).tendsto.comp hrad) ht
  have he : circleFourierCoeff (fun t => evalCircle P t / evalCircle Q t) n =
      circleFourierCoeff g n := by
    unfold circleFourierCoeff
    apply integral_congr_ae
    filter_upwards [hae] with t ht
    rw [ht]
  rw [he,hs n hn]

noncomputable def reversePolynomial (N : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range N, Polynomial.monomial (N-1-k) (b k : ℂ)

theorem reversePolynomial_evalCircle (N : ℕ) (t : Circle) :
    evalCircle (reversePolynomial N) t =
      fourier (N-1 : ℕ) t * conj (evalCircle (polynomial N) t) := by
  unfold evalCircle reversePolynomial
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial, polynomial_eval,
    map_sum, map_mul, Complex.conj_ofReal, ← fourier_neg,
    Majority.fourier_pow_nat, mul_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ N-1 := by have := Finset.mem_range.mp hk; omega
  rw [mul_left_comm, ← fourier_add]
  congr 2
  congr 1
  omega

noncomputable def extremizer (N : ℕ) (t : Circle) : ℂ :=
  evalCircle (polynomial N) t / conj (evalCircle (polynomial N) t)

theorem evalCircle_polynomial_ne_zero {N : ℕ} (hN : 0 < N) (t : Circle) :
    evalCircle (polynomial N) t ≠ 0 :=
  polynomial_ne_zero_closedDisk hN _ (by simp [fourier_apply])

theorem extremizer_continuous {N : ℕ} (hN : 0 < N) : Continuous (extremizer N) :=
  (evalCircle_continuous _).div
    (Complex.continuous_conj.comp (evalCircle_continuous _))
    (fun t => by simpa only [map_ne_zero] using evalCircle_polynomial_ne_zero hN t)

theorem extremizer_norm {N : ℕ} (hN : 0 < N) (t : Circle) : ‖extremizer N t‖ = 1 := by
  rw [extremizer,norm_div,Complex.norm_conj,div_self (norm_ne_zero_iff.mpr
    (evalCircle_polynomial_ne_zero hN t))]

theorem extremizer_support {N : ℕ} (hN : 0 < N) (n : ℤ) (hn : (N : ℤ) ≤ n) :
    circleFourierCoeff (extremizer N) n = 0 := by
  let m : ℤ := N-1
  have hH := polynomial_quotient_spectrum (reversePolynomial N) (polynomial N)
    (polynomial_ne_zero_closedDisk hN) (m-n) (by dsimp only [m]; omega)
  have hid : (fun t => evalCircle (reversePolynomial N) t / evalCircle (polynomial N) t) =
      (fun t => fourier m t * conj (extremizer N t)) := by
    funext t
    rw [reversePolynomial_evalCircle]
    have hm : ((N-1 : ℕ) : ℤ) = m := by dsimp only [m]; omega
    simp only [hm,extremizer,map_div₀,Complex.conj_conj,mul_div_assoc]
  rw [hid,circleFourierCoeff_modulate,circleFourierCoeff_conj] at hH
  have he : -(m-n-m) = n := by ring
  rw [he] at hH
  have hh := congrArg conj hH
  simpa only [Complex.conj_conj,map_zero] using hh

/-- The explicit test Q/conj(Q) attains Landau's bound, proving sharpness
inside exactly the spectral class used in the manuscript. -/
theorem extremizer_attains {N : ℕ} (hN : 0 < N) :
    circlePairing (dirichlet N) (extremizer N) =
      ((∑ k ∈ Finset.range N, b k^2 : ℝ) : ℂ) := by
  rw [← pairing_square_eq_dirichlet N
    (continuous_circle_integrable (extremizer_continuous hN)) (extremizer_support hN)]
  have hp (t : Circle) : evalCircle (polynomial N*polynomial N) t * star (extremizer N t) =
      ((‖evalCircle (polynomial N) t‖^2 : ℝ) : ℂ) := by
    have hn := evalCircle_polynomial_ne_zero hN t
    simp only [evalCircle,Polynomial.eval_mul,extremizer,Complex.star_def,
      map_div₀,Complex.conj_conj]
    change _ = ((‖(polynomial N).eval (fourier 1 t)‖^2 : ℝ) : ℂ)
    rw [Complex.ofReal_pow,← Complex.mul_conj']
    field_simp [show (polynomial N).eval (fourier 1 t) ≠ 0 from hn]
  unfold circlePairing
  simp only [hp]
  rw [integral_complex_ofReal,integral_norm_sq_polynomial]

end Landau
end LittlewoodInverse
