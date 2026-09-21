import LittlewoodInverse.PrefixPairing
import LittlewoodInverse.HardyExternal
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Nonpositive Fourier support and means of products

The product-mean part of Lemma 4.1 is proved from actual Fourier support.
The construction uses the explicit Schwarz integral and the standard external
Schwarz–Poisson and Hardy boundary theorems in `HardyExternal`.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace Topology
open MeasureTheory Filter

namespace LittlewoodInverse

theorem circleFourierCoeff_eq_fourierCoeff (f : Circle → ℂ) (n : ℤ) :
    circleFourierCoeff f n = fourierCoeff f n := by
  simp only [circleFourierCoeff, fourierCoeff, smul_eq_mul, circleMeasure, mul_comm]

theorem circleFourierCoeff_conj (f : Circle → ℂ) (n : ℤ) :
    circleFourierCoeff (fun t ↦ conj (f t)) n = conj (circleFourierCoeff f (-n)) := by
  simp only [circleFourierCoeff, neg_neg, ← integral_conj, map_mul, ← fourier_neg]

theorem hasSum_conj_circleFourierCoeff_mul {f g : Circle → ℂ}
    (hf : MemLp f 2 circleMeasure) (hg : MemLp g 2 circleMeasure) :
    HasSum (fun n : ℤ ↦ conj (circleFourierCoeff f n) * circleFourierCoeff g n)
      (∫ t, conj (f t) * g t ∂circleMeasure) := by
  let hf' : MemLp f 2 AddCircle.haarAddCircle := hf
  let hg' : MemLp g 2 AddCircle.haarAddCircle := hg
  have hc (n : ℤ) :
      inner ℂ (hf'.toLp f) (fourierBasis n) * inner ℂ (fourierBasis n) (hg'.toLp g) =
        conj (circleFourierCoeff f n) * circleFourierCoeff g n := by
    rw [← inner_conj_symm (hf'.toLp f) (fourierBasis n)]
    rw [← fourierBasis.repr_apply_apply, ← fourierBasis.repr_apply_apply]
    rw [fourierBasis_repr, fourierBasis_repr]
    rw [fourierCoeff_congr_ae hf'.coeFn_toLp, fourierCoeff_congr_ae hg'.coeFn_toLp]
    rw [circleFourierCoeff_eq_fourierCoeff, circleFourierCoeff_eq_fourierCoeff]
  have hi : inner ℂ (hf'.toLp f) (hg'.toLp g) =
      ∫ t, conj (f t) * g t ∂circleMeasure := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf'.coeFn_toLp, hg'.coeFn_toLp] with t ht ht'
    simp only [RCLike.inner_apply', ht, ht']
  have hh := (fourierBasis (T := (1 : ℝ))).hasSum_inner_mul_inner (hf'.toLp f) (hg'.toLp g)
  simpa only [hc, hi] using hh

theorem circleFourierCoeff_zero (f : Circle → ℂ) :
    circleFourierCoeff f 0 = ∫ t, f t ∂circleMeasure := by
  simp only [circleFourierCoeff, neg_zero, fourier_zero, mul_one]

/-- The mean of a product of two `L²` functions with nonpositive spectrum. -/
theorem integral_mul_of_nonpositive_support {f g : Circle → ℂ}
    (hf : MemLp f 2 circleMeasure) (hg : MemLp g 2 circleMeasure)
    (hsf : NonpositiveFourierSupport f) (hsg : NonpositiveFourierSupport g) :
    (∫ t, f t * g t ∂circleMeasure) =
      (∫ t, f t ∂circleMeasure) * (∫ t, g t ∂circleMeasure) := by
  have hfc : MemLp (fun t ↦ conj (f t)) 2 circleMeasure :=
    hf.continuousLinearMap_comp Complex.conjCLE.toContinuousLinearMap
  have hh := hasSum_conj_circleFourierCoeff_mul hfc hg
  simp only [circleFourierCoeff_conj] at hh
  simp only [Complex.conj_conj] at hh
  have hs : (∑' n : ℤ, circleFourierCoeff f (-n) * circleFourierCoeff g n) =
      circleFourierCoeff f 0 * circleFourierCoeff g 0 := by
    rw [tsum_eq_single 0]
    · simp only [neg_zero]
    · intro n hn
      rcases lt_or_gt_of_ne hn with hneg | hpos
      · rw [hsf (-n) (neg_pos.mpr hneg), zero_mul]
      · rw [hsg n hpos, mul_zero]
  rw [← hh.tsum_eq, hs, circleFourierCoeff_zero, circleFourierCoeff_zero]

theorem circleFourierCoeff_mul_fourier (f : Circle → ℂ) (k n : ℤ) :
    circleFourierCoeff (fun t ↦ f t * fourier k t) n = circleFourierCoeff f (n - k) := by
  unfold circleFourierCoeff
  apply integral_congr_ae
  filter_upwards [] with t
  rw [mul_assoc, ← fourier_add]
  congr 2
  congr 1
  omega

theorem memLp_mul_fourier {f : Circle → ℂ} {p : ENNReal}
    (hf : MemLp f p circleMeasure) (k : ℤ) :
    MemLp (fun t ↦ f t * fourier k t) p circleMeasure := by
  apply hf.congr_norm (hf.1.mul (fourier k).continuous.aestronglyMeasurable)
  filter_upwards [] with t
  change ‖f t‖ = ‖f t * fourier k t‖
  simp only [norm_mul, fourier_apply, Circle.norm_coe, mul_one]

/-- Multiplication preserves the nonpositive Fourier support condition. -/
theorem nonpositive_support_mul {f g : Circle → ℂ}
    (hf : MemLp f 2 circleMeasure) (hg : MemLp g 2 circleMeasure)
    (hsf : NonpositiveFourierSupport f) (hsg : NonpositiveFourierSupport g) :
    NonpositiveFourierSupport (fun t ↦ f t * g t) := by
  intro n hn
  have hs : NonpositiveFourierSupport (fun t ↦ g t * fourier (-n) t) := by
    intro k hk
    rw [circleFourierCoeff_mul_fourier]
    exact hsg (k - -n) (by omega)
  have hh := integral_mul_of_nonpositive_support hf (memLp_mul_fourier hg (-n)) hsf hs
  rw [← circleFourierCoeff_zero (fun t ↦ g t * fourier (-n) t),
    circleFourierCoeff_mul_fourier, zero_sub, neg_neg, hsg n hn, mul_zero] at hh
  simpa only [circleFourierCoeff, mul_assoc] using hh

theorem memLp_finset_prod_top {ι : Type*} (S : Finset ι) {f : ι → Circle → ℂ}
    (hf : ∀ i ∈ S, MemLp (f i) ⊤ circleMeasure) :
    MemLp (fun t ↦ ∏ i ∈ S, f i t) ⊤ circleMeasure := by
  simpa using MemLp.prod' hf

/-- Any finite product of bounded functions with nonpositive spectrum has
nonpositive spectrum and its mean is the product of its means. -/
theorem finite_product_nonpositive_support_mean {ι : Type*} (S : Finset ι)
    {f : ι → Circle → ℂ} (hf : ∀ i ∈ S, MemLp (f i) ⊤ circleMeasure)
    (hs : ∀ i ∈ S, NonpositiveFourierSupport (f i)) :
    NonpositiveFourierSupport (fun t ↦ ∏ i ∈ S, f i t) ∧
      (∫ t, ∏ i ∈ S, f i t ∂circleMeasure) =
        ∏ i ∈ S, (∫ t, f i t ∂circleMeasure) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    constructor
    · intro n hn
      simp only [Finset.prod_empty, circleFourierCoeff, one_mul, integral_fourier]
      simp [ne_of_lt (neg_neg_of_pos hn)]
    · simp
  | @insert i S hi ih =>
    have hmem : ∀ j ∈ S, MemLp (f j) ⊤ circleMeasure :=
      fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)
    have hsupport : ∀ j ∈ S, NonpositiveFourierSupport (f j) :=
      fun j hj ↦ hs j (Finset.mem_insert_of_mem hj)
    have hrec := ih hmem hsupport
    have hfi : MemLp (f i) 2 circleMeasure :=
      (hf i (Finset.mem_insert_self i S)).mono_exponent le_top
    have hprod : MemLp (fun t ↦ ∏ j ∈ S, f j t) 2 circleMeasure :=
      (memLp_finset_prod_top S hmem).mono_exponent le_top
    simp only [Finset.prod_insert hi]
    constructor
    · exact nonpositive_support_mul hfi hprod
        (hs i (Finset.mem_insert_self i S)) hrec.1
    · rw [integral_mul_of_nonpositive_support hfi hprod
        (hs i (Finset.mem_insert_self i S)) hrec.1, hrec.2]

theorem schwarzIntegral_zero (ell : Circle → ℝ) :
    schwarzIntegral ell 0 = ((∫ t, ell t ∂circleMeasure : ℝ) : ℂ) := by
  have hn (t : Circle) : fourier (T := (1 : ℝ)) 1 t ≠ 0 := by
    simp [fourier_apply]
  simp only [schwarzIntegral, add_zero, sub_zero, div_self (hn _), one_mul]
  exact integral_complex_ofReal

/-- Exponentiation of the explicit Schwarz integral followed by conjugation of
its radial boundary.  This is the internal construction, for arbitrary bounded
nonpositive real logarithmic data. -/
theorem exists_nonpositive_outer_of_log (ell : Circle → ℝ)
    (hell : MemLp ell ⊤ circleMeasure) (L : ℝ)
    (hbound : ∀ᵐ t ∂circleMeasure, L ≤ ell t ∧ ell t ≤ 0) :
    ∃ M : Circle → ℂ, MemLp M ⊤ circleMeasure ∧
      NonpositiveFourierSupport M ∧
      (∀ᵐ t ∂circleMeasure, ‖M t‖ = Real.exp (ell t)) ∧
      circleFourierCoeff M 0 = (Real.exp (∫ t, ell t ∂circleMeasure) : ℂ) := by
  obtain ⟨hhol, hrange, hreal⟩ :=
    HardyExternal.schwarz_integral_boundary ell hell L 0 hbound
  let F : ℂ → ℂ := fun z ↦ Complex.exp (schwarzIntegral ell z)
  have hFhol : DifferentiableOn ℂ F (Metric.ball 0 1) := hhol.cexp
  have hFbound : ∀ z : ℂ, ‖z‖ < 1 → ‖F z‖ ≤ 1 := by
    intro z hz
    change ‖Complex.exp (schwarzIntegral ell z)‖ ≤ 1
    rw [Complex.norm_exp]
    exact Real.exp_le_one_iff.mpr (hrange z hz).2
  obtain ⟨g, hgLp, _, hgrad, hgsupp, hgzero⟩ :=
    HardyExternal.bounded_holomorphic_radial_boundary F 1 hFhol hFbound
  refine ⟨fun t ↦ conj (g t),
    hgLp.continuousLinearMap_comp Complex.conjCLE.toContinuousLinearMap, ?_, ?_, ?_⟩
  · intro n hn
    rw [circleFourierCoeff_conj, hgsupp (-n) (neg_neg_of_pos hn), map_zero]
  · filter_upwards [hreal, hgrad] with t htReal htG
    have hnorm := htG.norm
    have hexp := Real.continuous_exp.continuousAt.tendsto.comp htReal
    simp only [F, Complex.norm_exp] at hnorm
    simpa only [Complex.norm_conj] using tendsto_nhds_unique hnorm hexp
  · rw [circleFourierCoeff_conj, neg_zero, hgzero]
    simp only [F, schwarzIntegral_zero, ← Complex.ofReal_exp, Complex.conj_ofReal]

/-- Lemma 4.1 (outer damping), including actual `L∞` membership, nonpositive
Fourier support, exact almost-everywhere modulus and positive real mean. -/
theorem outer_damping {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (u : Circle → ℝ) (hu : Measurable u)
    (huIcc : ∀ᵐ t ∂circleMeasure, 0 ≤ u t ∧ u t ≤ 1) :
    ∃ M : Circle → ℂ, MemLp M ⊤ circleMeasure ∧
      NonpositiveFourierSupport M ∧
      (∀ᵐ t ∂circleMeasure, ‖M t‖ = 1 - a * u t) ∧
      circleFourierCoeff M 0 =
        (Real.exp (∫ t, Real.log (1 - a * u t) ∂circleMeasure) : ℂ) ∧
      0 < Real.exp (∫ t, Real.log (1 - a * u t) ∂circleMeasure) := by
  let ell : Circle → ℝ := fun t ↦ Real.log (1 - a * u t)
  have hpos : ∀ᵐ t ∂circleMeasure, 0 < 1 - a * u t := by
    filter_upwards [huIcc] with t ht
    nlinarith
  have hrange : ∀ᵐ t ∂circleMeasure, Real.log (1 - a) ≤ ell t ∧ ell t ≤ 0 := by
    filter_upwards [huIcc, hpos] with t ht hpt
    constructor
    · exact Real.log_le_log (by linarith) (by nlinarith)
    · exact Real.log_nonpos (le_of_lt hpt) (by nlinarith)
  have hmeas : Measurable ell := (measurable_const.sub (measurable_const.mul hu)).log
  have hell : MemLp ell ⊤ circleMeasure :=
    memLp_of_bounded hrange hmeas.aestronglyMeasurable ⊤
  obtain ⟨M, hM, hs, hnorm, hzero⟩ :=
    exists_nonpositive_outer_of_log ell hell (Real.log (1 - a)) hrange
  refine ⟨M, hM, hs, ?_, hzero, Real.exp_pos _⟩
  filter_upwards [hnorm, hpos] with t ht hpt
  rw [ht]
  exact Real.exp_log hpt

/-- The exact product-mean formula in the notation of Lemma 4.1. -/
theorem finite_product_mean_eq_prod_zeroCoeff {ι : Type*} (S : Finset ι)
    {f : ι → Circle → ℂ} (hf : ∀ i ∈ S, MemLp (f i) ⊤ circleMeasure)
    (hs : ∀ i ∈ S, NonpositiveFourierSupport (f i)) :
    (∫ t, ∏ i ∈ S, f i t ∂circleMeasure) = ∏ i ∈ S, circleFourierCoeff (f i) 0 := by
  simpa only [circleFourierCoeff_zero] using
    (finite_product_nonpositive_support_mean S hf hs).2

theorem norm_fourierPolynomial_le_card (A : Finset ℤ) (t : Circle) :
    ‖fourierPolynomial A t‖ ≤ (A.card : ℝ) := by
  calc
    ‖fourierPolynomial A t‖ ≤ ∑ a ∈ A, ‖fourier a t‖ := norm_sum_le _ _
    _ = (A.card : ℝ) := by simp [fourier_apply]

/-- The multiplier `M_{a,A}` used immediately after Lemma 4.1 exists with the
normalized Fourier polynomial as its actual modulus data. -/
theorem outer_damping_fourierPolynomial {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (A : Finset ℤ) (hA : A.Nonempty) :
    ∃ M : Circle → ℂ, MemLp M ⊤ circleMeasure ∧
      NonpositiveFourierSupport M ∧
      (∀ᵐ t ∂circleMeasure, ‖M t‖ = 1 - a * (‖fourierPolynomial A t‖ / A.card)) ∧
      circleFourierCoeff M 0 =
        (Real.exp (∫ t, Real.log (1 - a * (‖fourierPolynomial A t‖ / A.card))
          ∂circleMeasure) : ℂ) ∧
      0 < Real.exp (∫ t, Real.log (1 - a * (‖fourierPolynomial A t‖ / A.card))
        ∂circleMeasure) := by
  apply outer_damping ha0 ha1 _
    ((fourierPolynomial_continuous A).norm.div_const _).measurable
  filter_upwards [] with t
  have hn : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  exact ⟨div_nonneg (norm_nonneg _) hn.le,
    (div_le_one hn).mpr (norm_fourierPolynomial_le_card A t)⟩

/-- The exact pointwise modulus budget after Lemma 4.1 preserves the unit ball. -/
theorem outer_update_bound {G M q : ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hG : ‖G‖ ≤ 1) (hM : ‖M‖ = 1 - a * ‖q‖) :
    ‖G * M + (a : ℂ) * q‖ ≤ 1 := by
  calc
    ‖G * M + (a : ℂ) * q‖ ≤ ‖G * M‖ + ‖(a : ℂ) * q‖ := norm_add_le _ _
    _ = ‖G‖ * ‖M‖ + a * ‖q‖ := by simp [abs_of_nonneg ha]
    _ ≤ 1 * ‖M‖ + a * ‖q‖ := by gcongr
    _ = 1 := by rw [hM]; ring

end LittlewoodInverse
