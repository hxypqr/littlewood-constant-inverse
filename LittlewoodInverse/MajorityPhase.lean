import LittlewoodInverse.MajorityAmplification
import Mathlib.MeasureTheory.Integral.Prod

/-! # Exact phase selection for balanced mixed monomials -/

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LittlewoodInverse
namespace Majority

noncomputable def mixedMonomial {ι : Type*} [DecidableEq ι]
    (S U : Finset ι) (z : ι → ℂ) : ℂ :=
  (∏ i ∈ U, z i) * ∏ i ∈ S \ U, conj (z i)

theorem fourier_pow_nat (n : ℤ) (k : ℕ) (t : Circle) :
    fourier n t ^ k = fourier ((k : ℤ) * n) t := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, Nat.cast_add, Nat.cast_one, add_mul, one_mul, fourier_add]

theorem phase_product_expansion {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (z : ι → ℂ) (t : Circle) :
    (∏ i ∈ S, (((fourier 1 t * z i).re : ℝ) : ℂ)) =
      (∑ U ∈ S.powerset,
        fourier (2 * (U.card : ℤ) - (S.card : ℤ)) t * mixedMonomial S U z) /
          (2 : ℂ) ^ S.card := by
  simp only [Complex.re_eq_add_conj, map_mul, ← fourier_neg,
    Finset.prod_div_distrib, Finset.prod_const]
  rw [Finset.prod_add]
  congr 1
  apply Finset.sum_congr rfl
  intro U hU
  have hUS : U ⊆ S := Finset.mem_powerset.mp hU
  have hcard : (U.card : ℤ) - ((S \ U).card : ℤ) =
      2 * (U.card : ℤ) - (S.card : ℤ) := by
    have hh := Finset.card_sdiff_add_card_eq_card hUS
    omega
  simp only [Finset.prod_mul_distrib, Finset.prod_const, fourier_pow_nat,
    mul_one, mul_neg_one, mixedMonomial]
  have hh : fourier (U.card : ℤ) t * fourier (-((S \ U).card : ℤ)) t =
      fourier (2 * (U.card : ℤ) - (S.card : ℤ)) t := by
    rw [← fourier_add, ← sub_eq_add_neg, hcard]
  calc
    _ = (fourier (U.card : ℤ) t * fourier (-((S \ U).card : ℤ)) t) *
        ((∏ i ∈ U, z i) * ∏ i ∈ S \ U, conj (z i)) := by ring
    _ = _ := by rw [hh]

theorem phase_lift_expansion {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (z : ι → ℂ) (F : ℂ) (t : Circle) :
    ((2 * (fourier 1 t * F).re : ℝ) : ℂ) *
        (∏ i ∈ S, (((fourier 1 t * z i).re : ℝ) : ℂ)) =
      (∑ U ∈ S.powerset,
        ((F * mixedMonomial S U z) * fourier (1 + 2 * (U.card : ℤ) - (S.card : ℤ)) t +
        (conj F * mixedMonomial S U z) * fourier (-1 + 2 * (U.card : ℤ) - (S.card : ℤ)) t)) /
          (2 : ℂ) ^ S.card := by
  rw [← Complex.add_conj, phase_product_expansion, ← mul_div_assoc, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro U hU
  rw [map_mul, ← fourier_neg]
  have h1 : 1 + 2 * (U.card : ℤ) - (S.card : ℤ) =
      1 + (2 * (U.card : ℤ) - (S.card : ℤ)) := by ring
  have h2 : -1 + 2 * (U.card : ℤ) - (S.card : ℤ) =
      -1 + (2 * (U.card : ℤ) - (S.card : ℤ)) := by ring
  rw [h1, h2, fourier_add, fourier_add]
  ring

theorem integral_phase_lift_expansion {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (z : ι → ℂ) (F : ℂ) :
    (∫ t : Circle, ((2 * (fourier 1 t * F).re : ℝ) : ℂ) *
        (∏ i ∈ S, (((fourier 1 t * z i).re : ℝ) : ℂ)) ∂circleMeasure) =
      (∑ U ∈ S.powerset,
        ((if 1 + 2 * (U.card : ℤ) - (S.card : ℤ) = 0 then F * mixedMonomial S U z else 0) +
        (if -1 + 2 * (U.card : ℤ) - (S.card : ℤ) = 0 then conj F * mixedMonomial S U z else 0))) /
          (2 : ℂ) ^ S.card := by
  simp only [phase_lift_expansion, integral_div]
  rw [integral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro U hU
    rw [integral_add (continuous_circle_integrable (by fun_prop))
      (continuous_circle_integrable (by fun_prop))]
    simp only [integral_const_mul, integral_fourier, mul_ite, mul_one, mul_zero]
  · intro U hU
    exact continuous_circle_integrable (by fun_prop)

theorem mixedMonomial_complement {ι : Type*} [DecidableEq ι]
    {S U : Finset ι} (hU : U ⊆ S) (z : ι → ℂ) :
    mixedMonomial S (S \ U) z = conj (mixedMonomial S U z) := by
  simp only [mixedMonomial, Finset.sdiff_sdiff_eq_self hU, map_mul, map_prod,
    Complex.conj_conj]
  ring

theorem phase_selected_sums_conjugate {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (z : ι → ℂ) (F : ℂ) :
    (∑ U ∈ S.powerset,
      if 1 + 2 * (U.card : ℤ) - (S.card : ℤ) = 0 then F * mixedMonomial S U z else 0) =
    ∑ U ∈ S.powerset,
      if -1 + 2 * (U.card : ℤ) - (S.card : ℤ) = 0 then F * conj (mixedMonomial S U z) else 0 := by
  apply Finset.sum_bij (fun U _ ↦ S \ U)
  · intro U hU
    exact Finset.mem_powerset.mpr Finset.sdiff_subset
  · intro U hU V hV he
    have he' := congrArg (fun W ↦ S \ W) he
    simpa only [Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hU),
      Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hV)] using he'
  · intro U hU
    refine ⟨S \ U, Finset.mem_powerset.mpr Finset.sdiff_subset,
      Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hU)⟩
  · intro U hU
    have hUS := Finset.mem_powerset.mp hU
    have hc := Finset.card_sdiff_add_card_eq_card hUS
    rw [mixedMonomial_complement hUS, Complex.conj_conj]
    have hiff : (1 + 2 * (U.card : ℤ) - (S.card : ℤ) = 0) ↔
        (-1 + 2 * ((S \ U).card : ℤ) - (S.card : ℤ) = 0) := by omega
    simp only [hiff]

/-- Exact balanced identity in subset notation, prior to the outer `x` integral.
The condition selects exactly one more unconjugated than conjugated factor. -/
theorem integral_phase_balanced_identity {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (z : ι → ℂ) (F : ℂ) :
    (∫ t : Circle, ((2 * (fourier 1 t * F).re : ℝ) : ℂ) *
        (∏ i ∈ S, (((fourier 1 t * z i).re : ℝ) : ℂ)) ∂circleMeasure) =
      (2 : ℂ) / (2 : ℂ) ^ S.card *
        ((∑ U ∈ S.powerset,
          if 2 * U.card = S.card + 1 then (F * conj (mixedMonomial S U z)).re else 0 : ℝ) : ℂ) := by
  rw [integral_phase_lift_expansion, Finset.sum_add_distrib,
    phase_selected_sums_conjugate]
  have he (U : Finset ι) :
      (if -1 + 2 * (U.card : ℤ) - (S.card : ℤ) = 0 then F * conj (mixedMonomial S U z) else 0) +
      (if -1 + 2 * (U.card : ℤ) - (S.card : ℤ) = 0 then conj F * mixedMonomial S U z else 0) =
        2 * ((if 2 * U.card = S.card + 1 then
          (F * conj (mixedMonomial S U z)).re else 0 : ℝ) : ℂ) := by
    have hiff : (-1 + 2 * (U.card : ℤ) - (S.card : ℤ) = 0) ↔
        2 * U.card = S.card + 1 := by omega
    by_cases h : 2 * U.card = S.card + 1
    · rw [if_pos (hiff.mpr h), if_pos (hiff.mpr h), if_pos h]
      have hc : conj F * mixedMonomial S U z = conj (F * conj (mixedMonomial S U z)) := by
        simp only [map_mul, Complex.conj_conj]
      rw [hc, Complex.add_conj]
      push_cast
      rfl
    · rw [if_neg (mt hiff.mp h), if_neg (mt hiff.mp h), if_neg h]
      norm_num
  rw [← Finset.sum_add_distrib]
  simp only [he, ← Finset.mul_sum, ← Complex.ofReal_sum]
  ring

theorem integral_phase_pairing (F z : ℂ) :
    (∫ t : Circle, 2 * (fourier 1 t * F).re * (fourier 1 t * z).re ∂circleMeasure) =
      (F * conj z).re := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have hh := integral_phase_balanced_identity ({()} : Finset Unit) (fun _ ↦ z) F
  have hp : ({()} : Finset Unit).powerset = {∅, {()}} := by decide
  simpa [hp, mixedMonomial] using hh

noncomputable def phaseTarget (F : Circle → ℂ) (p : Circle × Circle) : ℝ :=
  2 * (fourier 1 p.2 * F p.1).re

noncomputable def phaseTest (Φ : Circle → ℂ) (p : Circle × Circle) : ℝ :=
  (fourier 1 p.2 * Φ p.1).re

theorem phaseTest_aestronglyMeasurable {Φ : Circle → ℂ}
    (hΦ : AEStronglyMeasurable Φ circleMeasure) :
    AEStronglyMeasurable (phaseTest Φ) (circleMeasure.prod circleMeasure) := by
  exact Complex.continuous_re.comp_aestronglyMeasurable
    (((fourier 1).continuous.aestronglyMeasurable.comp_snd).mul hΦ.comp_fst)

theorem phaseTarget_integrable {F : Circle → ℂ} (hF : Integrable F circleMeasure) :
    Integrable (phaseTarget F) (circleMeasure.prod circleMeasure) := by
  have hc : Integrable (fun p : Circle × Circle ↦ fourier 1 p.2 * F p.1)
      (circleMeasure.prod circleMeasure) := by
    apply (hF.comp_fst circleMeasure).bdd_mul
      ((fourier 1).continuous.aestronglyMeasurable.comp_snd)
    filter_upwards [] with p
    simp only [fourier_apply, Circle.norm_coe]
    exact le_rfl
  exact hc.re.const_mul 2

theorem abs_phaseTest_le (Φ : Circle → ℂ) (p : Circle × Circle) :
    |phaseTest Φ p| ≤ ‖Φ p.1‖ := by
  calc
    _ ≤ ‖fourier 1 p.2 * Φ p.1‖ := Complex.abs_re_le_norm _
    _ = _ := by simp [fourier_apply]

theorem abs_phaseTarget_le (F : Circle → ℂ) (p : Circle × Circle) :
    |phaseTarget F p| ≤ 2 * ‖F p.1‖ := by
  unfold phaseTarget
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact mul_le_mul_of_nonneg_left (abs_phaseTest_le F p) (by norm_num)

theorem integral_abs_phaseTarget_le {F : Circle → ℂ} (hF : Integrable F circleMeasure) :
    (∫ p, |phaseTarget F p| ∂circleMeasure.prod circleMeasure) ≤
      2 * ∫ x, ‖F x‖ ∂circleMeasure := by
  calc
    _ ≤ ∫ p : Circle × Circle, 2 * ‖F p.1‖ ∂circleMeasure.prod circleMeasure :=
      integral_mono (phaseTarget_integrable hF).abs
        ((hF.norm.comp_fst circleMeasure).const_mul 2) (abs_phaseTarget_le F)
    _ = _ := by
      rw [integral_const_mul, integral_prod _ (hF.norm.comp_fst circleMeasure)]
      simp

theorem phaseTest_ae_bound {Φ : Circle → ℂ}
    (hΦ : ∀ᵐ x ∂circleMeasure, ‖Φ x‖ ≤ 1) :
    ∀ᵐ p ∂circleMeasure.prod circleMeasure, |phaseTest Φ p| ≤ 1 := by
  have hh := (Measure.quasiMeasurePreserving_fst (μ := circleMeasure) (ν := circleMeasure)).ae hΦ
  filter_upwards [hh] with p hp
  exact (abs_phaseTest_le Φ p).trans hp

theorem integral_phaseTarget_mul_phaseTest {F Φ : Circle → ℂ}
    (hF : Integrable F circleMeasure) (hΦ : AEStronglyMeasurable Φ circleMeasure)
    (hΦbound : ∀ᵐ x ∂circleMeasure, ‖Φ x‖ ≤ 1) :
    (∫ p, phaseTarget F p * phaseTest Φ p ∂circleMeasure.prod circleMeasure) =
      (circlePairing F Φ).re := by
  have hi : Integrable (fun p ↦ phaseTarget F p * phaseTest Φ p)
      (circleMeasure.prod circleMeasure) :=
    (phaseTarget_integrable hF).mul_bdd (phaseTest_aestronglyMeasurable hΦ)
      (phaseTest_ae_bound hΦbound)
  have hpair : Integrable (fun x ↦ F x * conj (Φ x)) circleMeasure := by
    apply hF.mul_bdd (Complex.continuous_conj.comp_aestronglyMeasurable hΦ)
    simpa only [Complex.norm_conj] using hΦbound
  rw [integral_prod _ hi]
  simp only [phaseTarget, phaseTest, integral_phase_pairing, circlePairing, Complex.star_def]
  exact integral_re hpair

theorem integral_phase_balanced_identity_real {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (z : ι → ℂ) (F : ℂ) :
    (∫ t : Circle, 2 * (fourier 1 t * F).re *
        (∏ i ∈ S, (fourier 1 t * z i).re) ∂circleMeasure) =
      (2 : ℝ) / (2 : ℝ) ^ S.card *
        (∑ U ∈ S.powerset,
          if 2 * U.card = S.card + 1 then (F * conj (mixedMonomial S U z)).re else 0) := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_prod,
    Complex.ofReal_div, Complex.ofReal_pow] using integral_phase_balanced_identity S z F

theorem mixedMonomial_aestronglyMeasurable {ι : Type*} [DecidableEq ι]
    (S U : Finset ι) (Φ : ι → Circle → ℂ)
    (hΦ : ∀ i, AEStronglyMeasurable (Φ i) circleMeasure) :
    AEStronglyMeasurable (fun x ↦ mixedMonomial S U (fun i ↦ Φ i x)) circleMeasure := by
  exact (U.aestronglyMeasurable_fun_prod (fun i _ ↦ hΦ i)).mul
    ((S \ U).aestronglyMeasurable_fun_prod
      (fun i _ ↦ Complex.continuous_conj.comp_aestronglyMeasurable (hΦ i)))

theorem norm_mixedMonomial_le_one {ι : Type*} [DecidableEq ι]
    (S U : Finset ι) (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    ‖mixedMonomial S U z‖ ≤ 1 := by
  unfold mixedMonomial
  rw [norm_mul, norm_prod, norm_prod]
  have hh (V : Finset ι) : (∏ i ∈ V, ‖z i‖) ≤ 1 := by
    calc
      _ ≤ ∏ _i ∈ V, (1 : ℝ) := Finset.prod_le_prod (fun i _ ↦ norm_nonneg _) (fun i _ ↦ hz i)
      _ = _ := by simp
  simp only [Complex.norm_conj]
  exact mul_le_one₀ (hh U) (Finset.prod_nonneg (fun i _ ↦ norm_nonneg _)) (hh (S \ U))

theorem mixedMonomial_ae_bound {ι : Type*} [Countable ι] [DecidableEq ι]
    (S U : Finset ι) (Φ : ι → Circle → ℂ)
    (hΦ : ∀ i, ∀ᵐ x ∂circleMeasure, ‖Φ i x‖ ≤ 1) :
    ∀ᵐ x ∂circleMeasure, ‖mixedMonomial S U (fun i ↦ Φ i x)‖ ≤ 1 := by
  have hh : ∀ᵐ x ∂circleMeasure, ∀ i, ‖Φ i x‖ ≤ 1 := ae_all_iff.mpr hΦ
  exact hh.mono fun x hx ↦ norm_mixedMonomial_le_one S U _ hx

theorem mixed_pair_integrable {ι : Type*} [Countable ι] [DecidableEq ι]
    {F : Circle → ℂ} (hF : Integrable F circleMeasure)
    (S U : Finset ι) (Φ : ι → Circle → ℂ)
    (hΦ : ∀ i, AEStronglyMeasurable (Φ i) circleMeasure)
    (hΦbound : ∀ i, ∀ᵐ x ∂circleMeasure, ‖Φ i x‖ ≤ 1) :
    Integrable (fun x ↦ F x * conj (mixedMonomial S U (fun i ↦ Φ i x))) circleMeasure := by
  apply hF.mul_bdd
    (Complex.continuous_conj.comp_aestronglyMeasurable
      (mixedMonomial_aestronglyMeasurable S U Φ hΦ))
  simpa only [Complex.norm_conj] using mixedMonomial_ae_bound S U Φ hΦbound

theorem integral_phase_balanced_pairings {ι : Type*} [Countable ι] [DecidableEq ι]
    {F : Circle → ℂ} (hF : Integrable F circleMeasure)
    (S : Finset ι) (Φ : ι → Circle → ℂ)
    (hΦ : ∀ i, AEStronglyMeasurable (Φ i) circleMeasure)
    (hΦbound : ∀ i, ∀ᵐ x ∂circleMeasure, ‖Φ i x‖ ≤ 1) :
    (∫ p, phaseTarget F p * ∏ i ∈ S, phaseTest (Φ i) p
      ∂circleMeasure.prod circleMeasure) =
      (2 : ℝ) / (2 : ℝ) ^ S.card * ∑ U ∈ S.powerset,
        if 2 * U.card = S.card + 1 then
          (circlePairing F (fun x ↦ mixedMonomial S U (fun i ↦ Φ i x))).re else 0 := by
  have htest : ∀ᵐ p ∂circleMeasure.prod circleMeasure, ∀ i, |phaseTest (Φ i) p| ≤ 1 :=
    ae_all_iff.mpr fun i ↦ phaseTest_ae_bound (hΦbound i)
  have hi : Integrable (fun p ↦ phaseTarget F p * ∏ i ∈ S, phaseTest (Φ i) p)
      (circleMeasure.prod circleMeasure) := by
    apply (phaseTarget_integrable hF).mul_bdd
      (S.aestronglyMeasurable_fun_prod (fun i _ ↦ phaseTest_aestronglyMeasurable (hΦ i)))
    exact htest.mono fun p hp ↦ abs_finset_prod_le_one S _ (fun i _ ↦ hp i)
  rw [integral_prod _ hi]
  simp only [phaseTarget, phaseTest, integral_phase_balanced_identity_real]
  rw [integral_const_mul, integral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro U hU
    split_ifs with hc
    · exact integral_re (mixed_pair_integrable hF S U Φ hΦ hΦbound)
    · simp
  · intro U hU
    split_ifs
    · exact (mixed_pair_integrable hF S U Φ hΦ hΦbound).re
    · exact integrable_zero Circle ℝ circleMeasure

theorem exists_balanced_pairing {ι : Type*} [Countable ι] [DecidableEq ι]
    {F : Circle → ℂ} (hF : Integrable F circleMeasure)
    (S : Finset ι) (Φ : ι → Circle → ℂ)
    (hΦ : ∀ i, AEStronglyMeasurable (Φ i) circleMeasure)
    (hΦbound : ∀ i, ∀ᵐ x ∂circleMeasure, ‖Φ i x‖ ≤ 1)
    {η : ℝ} (hη : 0 < η)
    (hlarge : η ≤ |∫ p, phaseTarget F p * ∏ i ∈ S, phaseTest (Φ i) p
      ∂circleMeasure.prod circleMeasure|) :
    ∃ U ⊆ S, 2 * U.card = S.card + 1 ∧ η / 4 ≤
      ‖circlePairing F (fun x ↦ mixedMonomial S U (fun i ↦ Φ i x))‖ := by
  by_contra hn
  push Not at hn
  rw [integral_phase_balanced_pairings hF S Φ hΦ hΦbound, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) / 2 ^ S.card)] at hlarge
  have hs : |∑ U ∈ S.powerset, if 2 * U.card = S.card + 1 then
      (circlePairing F (fun x ↦ mixedMonomial S U (fun i ↦ Φ i x))).re else 0| ≤
      (2 : ℝ) ^ S.card * (η / 4) := by
    calc
      _ ≤ ∑ U ∈ S.powerset, |if 2 * U.card = S.card + 1 then
          (circlePairing F (fun x ↦ mixedMonomial S U (fun i ↦ Φ i x))).re else 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _U ∈ S.powerset, η / 4 := by
        apply Finset.sum_le_sum
        intro U hU
        split_ifs with hc
        · exact (Complex.abs_re_le_norm _).trans (hn U (Finset.mem_powerset.mp hU) hc).le
        · simpa only [abs_zero] using (by positivity : (0 : ℝ) ≤ η / 4)
      _ = _ := by simp
  have hh := mul_le_mul_of_nonneg_left hs
    (by positivity : 0 ≤ (2 : ℝ) / 2 ^ S.card)
  have he : (2 : ℝ) / 2 ^ S.card * (2 ^ S.card * (η / 4)) = η / 2 := by
    field_simp
    ring
  rw [he] at hh
  linarith

/-- A block of `2q+1` positively correlated bounded complex tests contains a
balanced higher monomial. The lower bound depends exponentially only on the block size. -/
theorem exists_balanced_higher_monomial (q : ℕ) {F : Circle → ℂ}
    (hF : Integrable F circleMeasure) (Φ : Fin (2 * q + 1) → Circle → ℂ)
    (hΦ : ∀ i, AEStronglyMeasurable (Φ i) circleMeasure)
    (hΦbound : ∀ i, ∀ᵐ x ∂circleMeasure, ‖Φ i x‖ ≤ 1)
    {κ : ℝ} (hκ : 0 < κ)
    (hlin : ∀ i, κ ≤ (circlePairing F (Φ i)).re)
    (hbudget : 2 * (∫ x, ‖F x‖ ∂circleMeasure) + 2 * κ ≤
      (2 * (q : ℝ) + 1) * ((Nat.centralBinom q : ℝ) / (4 : ℝ) ^ q) * κ) :
    ∃ S U : Finset (Fin (2 * q + 1)), U ⊆ S ∧ Odd S.card ∧ 3 ≤ S.card ∧
      2 * U.card = S.card + 1 ∧ κ / (4 * (2 : ℝ) ^ (2 * q + 1)) ≤
        ‖circlePairing F (fun x ↦ mixedMonomial S U (fun i ↦ Φ i x))‖ := by
  obtain ⟨S, hodd, h3, hlarge⟩ := exists_higher_integral
    (circleMeasure.prod circleMeasure) q (phaseTarget F) (phaseTarget_integrable hF)
    (fun i ↦ phaseTest (Φ i))
    (fun i ↦ phaseTest_aestronglyMeasurable (hΦ i))
    (ae_all_iff.mpr fun i ↦ phaseTest_ae_bound (hΦbound i)) hκ
    (fun i ↦ by rw [integral_phaseTarget_mul_phaseTest hF (hΦ i) (hΦbound i)]; exact hlin i)
    (by linarith [integral_abs_phaseTarget_le hF])
  obtain ⟨U, hUS, hbal, hpair⟩ := exists_balanced_pairing hF S Φ hΦ hΦbound
    (by positivity : 0 < κ / (2 : ℝ) ^ (2 * q + 1)) hlarge
  refine ⟨S, U, hUS, hodd, h3, hbal, ?_⟩
  convert hpair using 1
  ring

theorem exists_balanced_higher_monomial_of_ratio (q : ℕ) {F : Circle → ℂ}
    (hF : Integrable F circleMeasure) (Φ : Fin (2 * q + 1) → Circle → ℂ)
    (hΦ : ∀ i, AEStronglyMeasurable (Φ i) circleMeasure)
    (hΦbound : ∀ i, ∀ᵐ x ∂circleMeasure, ‖Φ i x‖ ≤ 1)
    {κ T : ℝ} (hκ : 0 < κ) (hT : 1 ≤ T)
    (hlin : ∀ i, κ ≤ (circlePairing F (Φ i)).re)
    (hL : (∫ x, ‖F x‖ ∂circleMeasure) ≤ T * κ)
    (hm : 64 * T ^ 2 ≤ 2 * (q : ℝ) + 1) :
    ∃ S U : Finset (Fin (2 * q + 1)), U ⊆ S ∧ Odd S.card ∧ 3 ≤ S.card ∧
      2 * U.card = S.card + 1 ∧ κ / (4 * (2 : ℝ) ^ (2 * q + 1)) ≤
        ‖circlePairing F (fun x ↦ mixedMonomial S U (fun i ↦ Φ i x))‖ := by
  apply exists_balanced_higher_monomial q hF Φ hΦ hΦbound hκ hlin
  have ha := mul_le_mul_of_nonneg_right
    (linear_amplitude_ge_four_mul (by linarith : 0 ≤ T) hm) hκ.le
  nlinarith [mul_le_mul_of_nonneg_right hT hκ.le]

end Majority
end LittlewoodInverse
