import LittlewoodInverse.LandauSpectral
import Mathlib.Analysis.Complex.AbelLimit
import LittlewoodInverse.PhaseNormalization

/-! # Boundary convergence and Abel remainder for the Landau square root -/

open scoped BigOperators Topology ComplexConjugate
open Filter

namespace LittlewoodInverse
namespace Landau

theorem b_sq_mul_le_one (n : ℕ) : ((n : ℝ) + 1) * b n ^ 2 ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hr := b_recurrence n
    have hs := congrArg (fun x : ℝ ↦ x ^ 2) hr
    have hn : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
    have hmul : ((n : ℝ) + 1) ^ 2 * (((n : ℝ) + 2) * b (n + 1) ^ 2) ≤
        ((n : ℝ) + 1) ^ 2 := by
      have hh := mul_le_mul_of_nonneg_left ih (sq_nonneg ((n : ℝ) + 1))
      have hdiff : ((n : ℝ) + 2) * ((n : ℝ) + 1 / 2) ^ 2 ≤ ((n : ℝ) + 1) ^ 3 := by
        nlinarith
      have hx := mul_le_mul_of_nonneg_right hdiff (sq_nonneg (b n))
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 2)
        (sq_nonneg (b (n + 1)))]
    have hh := (mul_le_mul_iff_right₀ hn).mp
      (show ((n : ℝ) + 1) ^ 2 * (((n : ℝ) + 2) * b (n + 1) ^ 2) ≤
        ((n : ℝ) + 1) ^ 2 * 1 by simpa only [mul_one] using hmul)
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, show (1 : ℝ) + 1 = 2 by norm_num] using hh

theorem b_le_inv_sqrt_succ (n : ℕ) : b n ≤ 1 / Real.sqrt ((n : ℝ) + 1) := by
  have hs := b_sq_mul_le_one n
  have hn : (0 : ℝ) < Real.sqrt ((n : ℝ) + 1) := by positivity
  rw [le_div_iff₀ hn]
  have he := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
  nlinarith [mul_nonneg (b_pos n).le hn.le]

theorem b_tendsto_zero : Tendsto b atTop (𝓝 0) := by
  have hh : Tendsto (fun n : ℕ ↦ (1 : ℝ) / Real.sqrt ((n : ℝ) + 1)) atTop (𝓝 0) := by
    apply tendsto_const_nhds.div_atTop
    exact Real.tendsto_sqrt_atTop.comp
      (Tendsto.atTop_add tendsto_natCast_atTop_atTop tendsto_const_nhds)
  exact squeeze_zero (fun n ↦ (b_pos n).le) b_le_inv_sqrt_succ hh

theorem norm_weighted_sum_le (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hanti : Antitone c)
    (g : ℕ → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hg : ∀ n, ‖∑ i ∈ Finset.range n, g i‖ ≤ M) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, (c i : ℂ) * g i‖ ≤ c 0 * M := by
  by_cases hn : n = 0
  · simp only [hn, Finset.range_zero, Finset.sum_empty, norm_zero]
    exact mul_nonneg (hc 0) hM
  have hpos : 0 < n := Nat.pos_of_ne_zero hn
  have he := Finset.sum_range_by_parts c g n
  simp only [Complex.real_smul] at he
  rw [he]
  calc
    _ ≤ ‖(c (n - 1) : ℂ) * ∑ i ∈ Finset.range n, g i‖ +
        ‖∑ i ∈ Finset.range (n - 1), ((c (i + 1) - c i : ℝ) : ℂ) *
          ∑ j ∈ Finset.range (i + 1), g j‖ := norm_sub_le _ _
    _ ≤ c (n - 1) * M + ∑ i ∈ Finset.range (n - 1), (c i - c (i + 1)) * M := by
      apply add_le_add
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc _)]
        exact mul_le_mul_of_nonneg_left (hg n) (hc _)
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonpos (sub_nonpos.mpr (hanti (Nat.le_succ i))), neg_sub]
        exact mul_le_mul_of_nonneg_left (hg (i + 1)) (sub_nonneg.mpr (hanti (Nat.le_succ i)))
    _ = c 0 * M := by
      rw [← Finset.sum_mul, Finset.sum_range_sub']
      ring

theorem geometric_sum_bound {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, z ^ i‖ ≤ 2 / ‖1 - z‖ := by
  rw [geom_sum_eq hz1, norm_div]
  have hden : ‖z - 1‖ = ‖1 - z‖ := norm_sub_rev _ _
  rw [hden]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [norm_pow, hz]

noncomputable def partialSum (N : ℕ) (z : ℂ) : ℂ := ∑ k ∈ Finset.range N, (b k : ℂ) * z ^ k

theorem partialSum_eq_eval (N : ℕ) (z : ℂ) : partialSum N z = (polynomial N).eval z := by
  simp [partialSum, polynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

theorem partial_converges {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    ∃ B : ℂ, Tendsto (fun N ↦ partialSum N z) atTop (𝓝 B) := by
  have hh := b_antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded
    b_tendsto_zero (geometric_sum_bound hz hz1)
  simpa only [Complex.real_smul, partialSum] using cauchySeq_tendsto_of_complete hh

theorem partialSum_tail (N k : ℕ) (z : ℂ) :
    partialSum (N + k) z - partialSum N z =
      z ^ N * ∑ i ∈ Finset.range k, (b (N + i) : ℂ) * z ^ i := by
  unfold partialSum
  rw [Finset.sum_range_add, add_sub_cancel_left, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [pow_add]
  ring

theorem norm_partialSum_tail (N k : ℕ) {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    ‖partialSum (N + k) z - partialSum N z‖ ≤ 2 * b N / ‖1 - z‖ := by
  rw [partialSum_tail, norm_mul, norm_pow, hz, one_pow, one_mul]
  have hh := norm_weighted_sum_le (fun i ↦ b (N + i)) (fun i ↦ (b_pos _).le)
    (fun i j hij ↦ b_antitone (Nat.add_le_add_left hij N)) (fun i ↦ z ^ i)
    (by positivity : 0 ≤ 2 / ‖1 - z‖) (geometric_sum_bound hz hz1) k
  calc
    _ ≤ b N * (2 / ‖1 - z‖) := by simpa only [Nat.add_zero] using hh
    _ = _ := by ring

theorem boundary_tail_bound {z B : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1)
    (hB : Tendsto (fun N ↦ partialSum N z) atTop (𝓝 B)) (N : ℕ) :
    ‖B - partialSum N z‖ ≤ 2 * b N / ‖1 - z‖ := by
  have hh : Tendsto (fun k ↦ partialSum (N + k) z - partialSum N z) atTop
      (𝓝 (B - partialSum N z)) := by
    have hh := (hB.comp (tendsto_add_atTop_nat N)).sub_const (partialSum N z)
    simpa only [Function.comp_def, Nat.add_comm] using hh
  exact le_of_tendsto hh.norm (Filter.Eventually.of_forall (norm_partialSum_tail N · hz hz1))

noncomputable def powerSum (z : ℂ) : ℂ := ∑' n : ℕ, (b n : ℂ) * z ^ n

theorem summable_norm_powerSum {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ ↦ ‖(b n : ℂ) * z ^ n‖) := by
  apply (summable_geometric_of_lt_one (norm_nonneg z) hz).of_nonneg_of_le
    (fun n ↦ norm_nonneg _)
  intro n
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (b_pos n), norm_pow]
  have hb : b n ≤ 1 := by simpa using b_antitone (Nat.zero_le n)
  exact mul_le_of_le_one_left (by positivity) hb

theorem powerSum_square {z : ℂ} (hz : ‖z‖ < 1) : powerSum z ^ 2 = (1 - z)⁻¹ := by
  unfold powerSum
  rw [pow_two, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (summable_norm_powerSum hz) (summable_norm_powerSum hz)]
  have he (n : ℕ) : (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
      ((b ij.1 : ℂ) * z ^ ij.1) * ((b ij.2 : ℂ) * z ^ ij.2)) = z ^ n := by
    calc
      _ = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
          ((b ij.1 * b ij.2 : ℝ) : ℂ) * z ^ n := by
        apply Finset.sum_congr rfl
        intro ij hij
        have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
        rw [← hsum, pow_add]
        push_cast
        ring
      _ = _ := by
        rw [← Finset.sum_mul, ← Complex.ofReal_sum, coefficient_convolution]
        simp
  simp only [he]
  exact tsum_geometric_of_norm_lt_one hz

theorem boundary_square {z B : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1)
    (hB : Tendsto (fun N ↦ partialSum N z) atTop (𝓝 B)) : B ^ 2 = (1 - z)⁻¹ := by
  have hab := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hB
  have hr : Tendsto (fun r : ℝ ↦ powerSum ((r : ℂ) * z)) (𝓝[<] 1) (𝓝 B) := by
    have hh := hab.comp (tendsto_map : Tendsto Complex.ofReal (𝓝[<] (1 : ℝ))
      ((𝓝[<] (1 : ℝ)).map Complex.ofReal))
    convert hh using 1
    ext r
    unfold powerSum
    apply tsum_congr
    intro n
    rw [mul_pow]
    ring
  have hne : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  have hri : Tendsto (fun r : ℝ ↦ (1 - (r : ℂ) * z)⁻¹) (𝓝[<] 1) (𝓝 ((1 - z)⁻¹)) := by
    have hh := ((Complex.continuous_ofReal.tendsto 1).mul_const z).const_sub 1
    simpa only [Complex.ofReal_one, one_mul] using
      (hh.inv₀ (by simpa only [Complex.ofReal_one, one_mul] using hne)).mono_left nhdsWithin_le_nhds
  have he : (fun r : ℝ ↦ powerSum ((r : ℂ) * z) ^ 2) =ᶠ[𝓝[<] 1]
      (fun r ↦ (1 - (r : ℂ) * z)⁻¹) := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    apply powerSum_square
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1, hz, mul_one]
    exact hr.2
  exact tendsto_nhds_unique (hr.pow 2) (hri.congr' he.symm)

theorem boundary_norm {z B : ℂ} (hz1 : z ≠ 1) (hB : B ^ 2 = (1 - z)⁻¹) :
    ‖B‖ = 1 / Real.sqrt ‖1 - z‖ := by
  have hd : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz1))
  have hh := congrArg norm hB
  rw [norm_pow, norm_inv] at hh
  have hs := Real.sq_sqrt hd.le
  have hspos : 0 < Real.sqrt ‖1 - z‖ := Real.sqrt_pos.mpr hd
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [div_pow, one_pow, hs]
  simpa only [one_div] using hh

theorem boundary_ratio {z B : ℂ} (hz1 : z ≠ 1) (hB : B ^ 2 = (1 - z)⁻¹) :
    B / conj B = (‖1 - z‖ : ℂ) / (1 - z) := by
  have hd : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz1))
  have hn := congrArg norm hB
  rw [norm_pow, norm_inv] at hn
  have hB0 : B ≠ 0 := by
    intro hh
    simp [hh] at hB
    exact hz1 ((sub_eq_zero.mp hB.symm).symm)
  have hBc : conj B ≠ 0 := by simpa using hB0
  have hdC : (‖1 - z‖ : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have he : B / conj B = B ^ 2 / (‖B‖ ^ 2 : ℂ) := by
    rw [← Complex.mul_conj']
    field_simp
  rw [he, hB]
  have hnC : (‖B‖ ^ 2 : ℂ) = (‖1 - z‖ : ℂ)⁻¹ := by exact_mod_cast hn
  rw [hnC]
  field_simp

/-- The Abel remainder controls the exact quotient phase, with no choice
of a complex square-root branch. -/
theorem quotient_phase_error (N : ℕ) {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    ‖(polynomial N).eval z / conj ((polynomial N).eval z) -
      (‖1 - z‖ : ℂ) / (1 - z)‖ ≤ 8 * b N / Real.sqrt ‖1 - z‖ := by
  obtain ⟨B, hconv⟩ := partial_converges hz hz1
  have hB := boundary_square hz hz1 hconv
  have hd : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz1))
  have hB0 : B ≠ 0 := by
    have hn := boundary_norm hz1 hB
    have hh : 0 < ‖B‖ := by rw [hn]; positivity
    exact norm_ne_zero_iff.mp hh.ne'
  have htail := boundary_tail_bound hz hz1 hconv N
  rw [norm_sub_rev, partialSum_eq_eval] at htail
  have hp := PhaseNormalization.quotient_conj_perturbation ((polynomial N).eval z) hB0
  rw [boundary_ratio hz1 hB, boundary_norm hz1 hB] at hp
  have hs := Real.sq_sqrt hd.le
  calc
    _ ≤ 4 * ‖(polynomial N).eval z - B‖ / (1 / Real.sqrt ‖1 - z‖) := hp
    _ ≤ 4 * (2 * b N / ‖1 - z‖) / (1 / Real.sqrt ‖1 - z‖) := by gcongr
    _ = _ := by
      have hs0 : Real.sqrt ‖1 - z‖ ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
      field_simp
      linear_combination 8 * b N * hs

end Landau
end LittlewoodInverse
