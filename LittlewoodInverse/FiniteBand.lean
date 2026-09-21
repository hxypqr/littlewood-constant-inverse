import LittlewoodInverse.FejerKernel
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # The finite-band certificate (Lemma 6.2) -/

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LittlewoodInverse

noncomputable def finiteFourierSum (S : Finset ℤ) (c : ℤ → ℂ) (t : Circle) : ℂ :=
  ∑ n ∈ S, c n * fourier n t

theorem finiteFourierSum_continuous (S : Finset ℤ) (c : ℤ → ℂ) :
    Continuous (finiteFourierSum S c) := by
  unfold finiteFourierSum
  fun_prop

theorem circleFourierCoeff_finiteFourierSum (S : Finset ℤ) (c : ℤ → ℂ) (k : ℤ) :
    circleFourierCoeff (finiteFourierSum S c) k = if k ∈ S then c k else 0 := by
  classical
  unfold circleFourierCoeff finiteFourierSum
  simp only [Finset.sum_mul, mul_assoc, ← fourier_add]
  rw [integral_finsetSum]
  · simp only [integral_const_mul, integral_fourier, add_neg_eq_zero,
      mul_ite, mul_one, mul_zero]
    exact Finset.sum_ite_eq' _ _ _
  · intro n hn
    exact continuous_circle_integrable (continuous_const.mul (fourier _).continuous)

theorem continuous_eq_of_circleFourierCoeff_eq {f g : Circle → ℂ}
    (hf : Continuous f) (hg : Continuous g)
    (hc : ∀ n, circleFourierCoeff f n = circleFourierCoeff g n) : f = g := by
  have hfl : MemLp f 2 AddCircle.haarAddCircle :=
    hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hgl : MemLp g 2 AddCircle.haarAddCircle :=
    hg.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he : hfl.toLp f = hgl.toLp g := by
    apply (fourierBasis (T := (1 : ℝ))).repr.injective
    ext n
    rw [fourierBasis_repr, fourierBasis_repr,
      fourierCoeff_congr_ae hfl.coeFn_toLp, fourierCoeff_congr_ae hgl.coeFn_toLp]
    simpa only [circleFourierCoeff_eq_fourierCoeff] using hc n
  exact MeasureTheory.Measure.eq_of_ae_eq ((hfl.toLp_eq_toLp_iff hgl).mp he) hf hg

noncomputable def frequencyBand (D : ℕ) : Finset ℤ :=
  Finset.Icc (-(2 * D : ℤ)) (2 * D : ℤ)

theorem valleePoussinKernel_eq_finiteFourierSum (D : ℕ) :
    (fun t ↦ (valleePoussinKernel D t : ℂ)) =
      finiteFourierSum (frequencyBand D)
        (circleFourierCoeff (fun t ↦ (valleePoussinKernel D t : ℂ))) := by
  apply continuous_eq_of_circleFourierCoeff_eq
    (Complex.continuous_ofReal.comp (valleePoussinKernel_continuous D))
    (finiteFourierSum_continuous _ _)
  intro n
  rw [circleFourierCoeff_finiteFourierSum]
  split_ifs with hn
  · rfl
  · apply valleePoussinKernel_support
    simp only [frequencyBand, Finset.mem_Icc, not_and_or, not_le] at hn
    rcases hn with hn | hn
    · have h := le_abs_self n
      have h' := neg_le_abs n
      omega
    · exact le_trans hn.le (le_abs_self n)

theorem fourier_eval_sub (n : ℤ) (t s : Circle) :
    fourier n (t - s) = fourier n t * fourier (-n) s := by
  simp only [fourier_apply, sub_eq_add_neg, smul_add, smul_neg,
    AddCircle.toCircle_add, Circle.coe_mul, neg_smul]

theorem integral_finiteFourierSum_sub_mul (S : Finset ℤ) (c : ℤ → ℂ)
    {g : Circle → ℂ} (hg : Integrable g circleMeasure) (t : Circle) :
    (∫ s, finiteFourierSum S c (t - s) * g s ∂circleMeasure) =
      finiteFourierSum S (fun n ↦ c n * circleFourierCoeff g n) t := by
  have he (n : ℤ) (s : Circle) :
      c n * fourier n (t - s) * g s =
        (c n * fourier n t) * (g s * fourier (-n) s) := by
    rw [fourier_eval_sub]
    ring
  unfold finiteFourierSum
  simp only [Finset.sum_mul, he]
  rw [integral_finsetSum]
  · simp only [integral_const_mul, circleFourierCoeff]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  · intro n hn
    exact (integrable_mul_fourier hg _).const_mul _

noncomputable def fourierPhase (B : Finset ℤ) (t : Circle) : ℂ :=
  fourierPolynomial B t / (‖fourierPolynomial B t‖ : ℂ)

theorem fourierPhase_measurable (B : Finset ℤ) : Measurable (fourierPhase B) :=
  (fourierPolynomial_continuous B).measurable.div
    (Complex.continuous_ofReal.comp (fourierPolynomial_continuous B).norm).measurable

theorem norm_fourierPhase_le_one (B : Finset ℤ) (t : Circle) :
    ‖fourierPhase B t‖ ≤ 1 := by
  by_cases hz : fourierPolynomial B t = 0
  · simp [fourierPhase, hz]
  · simp [fourierPhase, norm_ne_zero_iff.mpr hz]

theorem fourierPhase_memLp_top (B : Finset ℤ) :
    MemLp (fourierPhase B) ⊤ circleMeasure :=
  memLp_top_of_bound (fourierPhase_measurable B).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (norm_fourierPhase_le_one B))

theorem fourierPhase_integrable (B : Finset ℤ) : Integrable (fourierPhase B) circleMeasure :=
  (fourierPhase_memLp_top B).integrable le_top

theorem fourierPolynomial_mul_star_phase (B : Finset ℤ) (t : Circle) :
    fourierPolynomial B t * star (fourierPhase B t) = (‖fourierPolynomial B t‖ : ℂ) := by
  by_cases hz : fourierPolynomial B t = 0
  · simp [fourierPhase, hz]
  · have hn : (‖fourierPolynomial B t‖ : ℂ) ≠ 0 := by
      exact_mod_cast norm_ne_zero_iff.mpr hz
    change fourierPolynomial B t * conj
      (fourierPolynomial B t / (‖fourierPolynomial B t‖ : ℂ)) = _
    rw [map_div₀, Complex.conj_ofReal, ← mul_div_assoc, Complex.mul_conj']
    field_simp

theorem circlePairing_fourierPhase (B : Finset ℤ) :
    circlePairing (fourierPolynomial B) (fourierPhase B) = (littlewoodNorm B : ℂ) := by
  unfold circlePairing littlewoodNorm
  simp only [fourierPolynomial_mul_star_phase]
  exact integral_complex_ofReal

noncomputable def finiteBandCertificate (D : ℕ) (B : Finset ℤ) : Circle → ℂ :=
  finiteFourierSum (frequencyBand D) (fun n ↦
    circleFourierCoeff (fun t ↦ (valleePoussinKernel D t : ℂ)) n *
      circleFourierCoeff (fourierPhase B) n / 3)

theorem finiteBandCertificate_continuous (D : ℕ) (B : Finset ℤ) :
    Continuous (finiteBandCertificate D B) := finiteFourierSum_continuous _ _

theorem finiteBandCertificate_eq_convolution (D : ℕ) (B : Finset ℤ) (t : Circle) :
    finiteBandCertificate D B t =
      (∫ s, (valleePoussinKernel D (t - s) : ℂ) * fourierPhase B s ∂circleMeasure) / 3 := by
  have hv (s : Circle) : (valleePoussinKernel D (t - s) : ℂ) =
      finiteFourierSum (frequencyBand D)
        (circleFourierCoeff (fun t ↦ (valleePoussinKernel D t : ℂ))) (t - s) :=
    congrFun (valleePoussinKernel_eq_finiteFourierSum D) (t - s)
  simp_rw [hv]
  rw [integral_finiteFourierSum_sub_mul _ _ (fourierPhase_integrable B)]
  simp only [finiteBandCertificate, finiteFourierSum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem norm_finiteBandCertificate_le_one {D : ℕ} (hD : 0 < D)
    (B : Finset ℤ) (t : Circle) : ‖finiteBandCertificate D B t‖ ≤ 1 := by
  have hc : Continuous (fun s ↦ (valleePoussinKernel D (t - s) : ℂ)) :=
    (Complex.continuous_ofReal.comp (valleePoussinKernel_continuous D)).comp
      (continuous_const.sub continuous_id)
  have hk : MemLp (fun s ↦ (valleePoussinKernel D (t - s) : ℂ)) ⊤ circleMeasure :=
    hc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi : Integrable
      (fun s ↦ (valleePoussinKernel D (t - s) : ℂ) * fourierPhase B s) circleMeasure :=
    ((fourierPhase_memLp_top B).mul' hk : MemLp _ ⊤ circleMeasure).integrable le_top
  have hm : (∫ s, ‖(valleePoussinKernel D (t - s) : ℂ) * fourierPhase B s‖
      ∂circleMeasure) ≤ ∫ s, ‖(valleePoussinKernel D (t - s) : ℂ)‖ ∂circleMeasure := by
    apply integral_mono hi.norm (continuous_circle_integrable hc.norm)
    intro s
    change ‖(valleePoussinKernel D (t - s) : ℂ) * fourierPhase B s‖ ≤
      ‖(valleePoussinKernel D (t - s) : ℂ)‖
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_fourierPhase_le_one B s)
  have hs : (∫ s, ‖(valleePoussinKernel D (t - s) : ℂ)‖ ∂circleMeasure) =
      ∫ s, ‖valleePoussinKernel D s‖ ∂circleMeasure := by
    simp only [Complex.norm_real]
    letI : circleMeasure.IsAddHaarMeasure := by
      unfold circleMeasure
      infer_instance
    exact integral_sub_left_eq_self (fun s : Circle ↦ ‖valleePoussinKernel D s‖)
      circleMeasure t
  have hn := norm_integral_le_integral_norm
    (fun s ↦ (valleePoussinKernel D (t - s) : ℂ) * fourierPhase B s) (μ := circleMeasure)
  rw [hs] at hm
  have h3 := integral_norm_valleePoussinKernel_le hD
  rw [finiteBandCertificate_eq_convolution, norm_div]
  norm_num
  linarith

theorem finiteBandCertificate_support (D : ℕ) (B : Finset ℤ) {n : ℤ}
    (hn : (2 * D : ℤ) < |n|) : circleFourierCoeff (finiteBandCertificate D B) n = 0 := by
  rw [finiteBandCertificate, circleFourierCoeff_finiteFourierSum]
  have hnot : n ∉ frequencyBand D := by
    simp only [frequencyBand, Finset.mem_Icc]
    intro h
    have hle : |n| ≤ (2 * D : ℤ) := abs_le.mpr h
    omega
  simp only [hnot, if_false]

theorem circlePairing_finiteBandCertificate {D : ℕ} (hD : 0 < D)
    (B : Finset ℤ) (hB : ∀ n ∈ B, |n| ≤ (D : ℤ)) :
    circlePairing (fourierPolynomial B) (finiteBandCertificate D B) =
      ((littlewoodNorm B / 3 : ℝ) : ℂ) := by
  have hcoeff (n : ℤ) (hn : n ∈ B) :
      circleFourierCoeff (finiteBandCertificate D B) n =
        circleFourierCoeff (fourierPhase B) n / 3 := by
    rw [finiteBandCertificate, circleFourierCoeff_finiteFourierSum]
    have hnb : n ∈ frequencyBand D := by
      simp only [frequencyBand, Finset.mem_Icc]
      have habs := abs_le.mp (hB n hn)
      constructor <;> omega
    rw [if_pos hnb, valleePoussinKernel_reproduces hD (hB n hn), one_mul]
  change circlePairing (indexedFourierSum B id) _ = _
  rw [circlePairing_indexedFourierSum _ _
    (continuous_circle_integrable (finiteBandCertificate_continuous D B))]
  simp only [id_eq]
  have he : (∑ n ∈ B, conj (circleFourierCoeff (finiteBandCertificate D B) n)) =
      (∑ n ∈ B, conj (circleFourierCoeff (fourierPhase B) n)) / 3 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hcoeff n hn, map_div₀]
    rw [show conj (3 : ℂ) = 3 from Complex.conj_ofReal (3 : ℝ)]
  rw [he]
  have hp := circlePairing_indexedFourierSum B id (fourierPhase_integrable B)
  simp only [id_eq] at hp
  rw [← hp]
  change circlePairing (fourierPolynomial B) (fourierPhase B) / 3 = _
  rw [circlePairing_fourierPhase]
  push_cast
  rfl

/-- Lemma 6.2: an actual trigonometric polynomial with frequency band
`[-2D,2D]`, pointwise norm at most one and exact correlation `La(B)/3`.
The statement includes the empty-set case. -/
theorem finite_band_certificate {D : ℕ} (hD : 0 < D)
    (B : Finset ℤ) (hB : ∀ n ∈ B, -(D : ℤ) ≤ n ∧ n ≤ (D : ℤ)) :
    ∃ ψ : Circle → ℂ,
      (∃ c : ℤ → ℂ, ψ = finiteFourierSum (frequencyBand D) c) ∧
      (∀ t, ‖ψ t‖ ≤ 1) ∧
      (∀ n : ℤ, (2 * D : ℤ) < |n| → circleFourierCoeff ψ n = 0) ∧
      circlePairing (fourierPolynomial B) ψ = ((littlewoodNorm B / 3 : ℝ) : ℂ) := by
  refine ⟨finiteBandCertificate D B, ⟨_, rfl⟩,
    norm_finiteBandCertificate_le_one hD B, ?_, ?_⟩
  · intro n hn
    exact finiteBandCertificate_support D B hn
  · exact circlePairing_finiteBandCertificate hD B (fun n hn ↦ abs_le.mpr (hB n hn))

end LittlewoodInverse
