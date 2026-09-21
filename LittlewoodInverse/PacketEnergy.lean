import LittlewoodInverse.SpectralEnergy
import LittlewoodInverse.PrefixPairing
import LittlewoodInverse.OuterDamping
import LittlewoodInverse.MomentCounting
import LittlewoodInverse.MajorityBlocks

/-! # High-order packet relations reduce to fourth-order energy -/

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LittlewoodInverse
namespace PacketEnergy

/-- Hölder with exponents `4/3,4`, proved by two applications of the already
proved integral Cauchy--Schwarz inequality. -/
theorem integral_cube_mul_fourth_le (f g : Circle → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    (∫ x, f x ^ 3 * g x ∂circleMeasure) ^ 4 ≤
      (∫ x, f x ^ 4 ∂circleMeasure) ^ 3 * (∫ x, g x ^ 4 ∂circleMeasure) := by
  have hc1 := integral_cauchy_schwarz_sq
    (f := fun x ↦ f x ^ 2) (g := fun x ↦ f x * g x)
    (continuous_circle_integrable (by fun_prop))
    (continuous_circle_integrable (by fun_prop))
    (continuous_circle_integrable (by fun_prop))
  have hc2 := integral_cauchy_schwarz_sq
    (f := fun x ↦ f x ^ 2) (g := fun x ↦ g x ^ 2)
    (continuous_circle_integrable (by fun_prop))
    (continuous_circle_integrable (by fun_prop))
    (continuous_circle_integrable (by fun_prop))
  have h1 (x : Circle) : f x ^ 2 * (f x * g x) = f x ^ 3 * g x := by ring
  have h2 (x : Circle) : (f x * g x) ^ 2 = f x ^ 2 * g x ^ 2 := by ring
  simp only [h1, h2, ← pow_mul] at hc1 hc2
  norm_num at hc1 hc2
  have hnon : 0 ≤ (∫ x, f x ^ 4 ∂circleMeasure) *
      (∫ x, f x ^ 2 * g x ^ 2 ∂circleMeasure) :=
    mul_nonneg (integral_nonneg fun x ↦ by positivity)
      (integral_nonneg fun x ↦ by positivity)
  have hh : (∫ x, f x ^ 3 * g x ∂circleMeasure) ^ 4 ≤
      ((∫ x, f x ^ 4 ∂circleMeasure) *
        (∫ x, f x ^ 2 * g x ^ 2 ∂circleMeasure)) ^ 2 := by
    nlinarith [sq_nonneg ((∫ x, f x ^ 3 * g x ∂circleMeasure) ^ 2 -
      (∫ x, f x ^ 4 ∂circleMeasure) *
        (∫ x, f x ^ 2 * g x ^ 2 ∂circleMeasure))]
  have hh2 := mul_le_mul_of_nonneg_left hc2
    (sq_nonneg (∫ x, f x ^ 4 ∂circleMeasure))
  nlinarith

theorem fourier_cube_mul_fourth_le (S A : Finset ℤ) :
    (∫ x, ‖fourierPolynomial S x‖ ^ 3 * ‖fourierPolynomial A x‖ ∂circleMeasure) ^ 4 ≤
      (additiveEnergy S : ℝ) ^ 3 * (additiveEnergy A : ℝ) := by
  have hh := integral_cube_mul_fourth_le (fun x ↦ ‖fourierPolynomial S x‖)
    (fun x ↦ ‖fourierPolynomial A x‖)
    (fourierPolynomial_continuous S).norm (fourierPolynomial_continuous A).norm
  simpa only [integral_norm_pow_four_fourierPolynomial] using hh

theorem highmoment_le (S A : Finset ℤ) (k : ℕ) (hk : 3 ≤ k) :
    (∫ x, ‖fourierPolynomial S x‖ ^ k * ‖fourierPolynomial A x‖ ∂circleMeasure) ≤
      (S.card : ℝ) ^ (k - 3) *
        (∫ x, ‖fourierPolynomial S x‖ ^ 3 * ‖fourierPolynomial A x‖ ∂circleMeasure) := by
  rw [← integral_const_mul]
  apply integral_mono
    (continuous_circle_integrable (((fourierPolynomial_continuous S).norm.pow k).mul
      (fourierPolynomial_continuous A).norm))
    (continuous_circle_integrable ((((fourierPolynomial_continuous S).norm.pow 3).mul
      (fourierPolynomial_continuous A).norm).const_mul _))
  intro x
  change ‖fourierPolynomial S x‖ ^ k * ‖fourierPolynomial A x‖ ≤ _
  have hp : ‖fourierPolynomial S x‖ ^ k =
      ‖fourierPolynomial S x‖ ^ (k - 3) * ‖fourierPolynomial S x‖ ^ 3 := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  rw [hp, mul_assoc]
  dsimp only
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (norm_fourierPolynomial_le_card S x) (k - 3))
    (by positivity)

theorem highmoment_fourth_le (S A : Finset ℤ) (k : ℕ) (hk : 3 ≤ k) :
    (∫ x, ‖fourierPolynomial S x‖ ^ k * ‖fourierPolynomial A x‖ ∂circleMeasure) ^ 4 ≤
      (S.card : ℝ) ^ (4 * (k - 3)) * (additiveEnergy S : ℝ) ^ 3 *
        (additiveEnergy A : ℝ) := by
  have hh := highmoment_le S A k hk
  have hpos : 0 ≤ ∫ x, ‖fourierPolynomial S x‖ ^ k * ‖fourierPolynomial A x‖
      ∂circleMeasure := integral_nonneg fun x ↦ by positivity
  calc
    _ ≤ ((S.card : ℝ) ^ (k - 3) *
        (∫ x, ‖fourierPolynomial S x‖ ^ 3 * ‖fourierPolynomial A x‖ ∂circleMeasure)) ^ 4 := by
      gcongr
    _ = (S.card : ℝ) ^ (4 * (k - 3)) *
        (∫ x, ‖fourierPolynomial S x‖ ^ 3 * ‖fourierPolynomial A x‖ ∂circleMeasure) ^ 4 := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm]
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (fourier_cube_mul_fourth_le S A) (by positivity)

def shiftedRelationCount (S A : Finset ℤ) (p q : ℕ) (t : ℤ) : ℕ :=
  (((MomentCounting.tuples S p ×ˢ MomentCounting.tuples S q) ×ˢ A).filter
    (fun v ↦ (∑ i, v.1.1 i) = (∑ i, v.1.2 i) + v.2 + t)).card

theorem shifted_relation_integral (S A : Finset ℤ) (p q : ℕ) (t : ℤ) :
    (shiftedRelationCount S A p q t : ℂ) =
      ∫ x, fourierPolynomial S x ^ p *
        conj (fourierPolynomial S x ^ q * fourierPolynomial A x) * fourier (-t) x
        ∂circleMeasure := by
  have he (x : Circle) : fourierPolynomial S x ^ p *
      conj (fourierPolynomial S x ^ q * fourierPolynomial A x) * fourier (-t) x =
      ∑ v ∈ (MomentCounting.tuples S p ×ˢ MomentCounting.tuples S q) ×ˢ A,
        fourier ((∑ i, v.1.1 i) - (∑ i, v.1.2 i) - v.2 - t) x := by
    rw [MomentCounting.polynomial_pow, MomentCounting.polynomial_pow]
    unfold fourierPolynomial
    simp only [map_mul, map_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_product,
      sub_eq_add_neg, fourier_add, fourier_neg]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := A) (t := MomentCounting.tuples S p)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun _ _ ↦ continuous_circle_integrable (by fun_prop))]
  simp only [integral_fourier]
  unfold shiftedRelationCount
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro v hv
  have hh : (∑ i, v.1.1 i) - (∑ i, v.1.2 i) - v.2 - t = 0 ↔
      (∑ i, v.1.1 i) = (∑ i, v.1.2 i) + v.2 + t := by omega
  simp only [hh]

theorem shifted_relation_le_highmoment (S A : Finset ℤ) (p q : ℕ) (t : ℤ) :
    (shiftedRelationCount S A p q t : ℝ) ≤
      ∫ x, ‖fourierPolynomial S x‖ ^ (p + q) * ‖fourierPolynomial A x‖ ∂circleMeasure := by
  have hh := norm_integral_le_integral_norm
    (fun x ↦ fourierPolynomial S x ^ p *
      conj (fourierPolynomial S x ^ q * fourierPolynomial A x) * fourier (-t) x)
    (μ := circleMeasure)
  rw [← shifted_relation_integral] at hh
  simpa only [norm_mul, Complex.norm_conj, norm_pow, fourier_apply, Circle.norm_coe,
    mul_one, ← mul_assoc, ← pow_add, Complex.norm_natCast] using hh

theorem shifted_relation_energy_bound (S A : Finset ℤ) (p q : ℕ) (t : ℤ)
    (hk : 3 ≤ p + q) :
    (shiftedRelationCount S A p q t : ℝ) ^ 4 ≤
      (S.card : ℝ) ^ (4 * (p + q - 3)) * (additiveEnergy S : ℝ) ^ 3 *
        (A.card : ℝ) ^ 3 := by
  have henergy : (additiveEnergy A : ℝ) ≤ (A.card : ℝ) ^ 3 := by
    exact_mod_cast additiveEnergy_le_card_cube A
  calc
    _ ≤ (∫ x, ‖fourierPolynomial S x‖ ^ (p + q) *
        ‖fourierPolynomial A x‖ ∂circleMeasure) ^ 4 := by
      gcongr
      exact shifted_relation_le_highmoment S A p q t
    _ ≤ (S.card : ℝ) ^ (4 * (p + q - 3)) * (additiveEnergy S : ℝ) ^ 3 *
        (additiveEnergy A : ℝ) := highmoment_fourth_le S A (p + q) hk
    _ ≤ _ := by gcongr

theorem shifted_relations_fourth_bound (S A : Finset ℤ) (J : Finset ℤ)
    (p q : ℕ) (hk : 3 ≤ p + q) :
    (∑ t ∈ J, (shiftedRelationCount S A p q t : ℝ)) ^ 4 ≤
      (J.card : ℝ) ^ 4 * (S.card : ℝ) ^ (4 * (p + q - 3)) *
        (additiveEnergy S : ℝ) ^ 3 * (A.card : ℝ) ^ 3 := by
  have hs : (∑ t ∈ J, (shiftedRelationCount S A p q t : ℝ)) ≤
      (J.card : ℝ) * (∫ x, ‖fourierPolynomial S x‖ ^ (p + q) *
        ‖fourierPolynomial A x‖ ∂circleMeasure) := by
    calc
      _ ≤ ∑ _t ∈ J, (∫ x, ‖fourierPolynomial S x‖ ^ (p + q) *
          ‖fourierPolynomial A x‖ ∂circleMeasure) :=
        Finset.sum_le_sum (fun t _ ↦ shifted_relation_le_highmoment S A p q t)
      _ = _ := by simp
  have henergy : (additiveEnergy A : ℝ) ≤ (A.card : ℝ) ^ 3 := by
    exact_mod_cast additiveEnergy_le_card_cube A
  calc
    _ ≤ ((J.card : ℝ) * (∫ x, ‖fourierPolynomial S x‖ ^ (p + q) *
        ‖fourierPolynomial A x‖ ∂circleMeasure)) ^ 4 := by gcongr
    _ = (J.card : ℝ) ^ 4 * (∫ x, ‖fourierPolynomial S x‖ ^ (p + q) *
        ‖fourierPolynomial A x‖ ∂circleMeasure) ^ 4 := mul_pow _ _ _
    _ ≤ (J.card : ℝ) ^ 4 * ((S.card : ℝ) ^ (4 * (p + q - 3)) *
        (additiveEnergy S : ℝ) ^ 3 * (additiveEnergy A : ℝ)) := by
      gcongr
      exact highmoment_fourth_le S A (p + q) hk
    _ ≤ _ := by
      simp only [← mul_assoc]
      gcongr

/-- Quantitative energy extraction from actual shifted relation counts.
The hypothesis on `η,δ` accounts only for the finite number of allowed carries. -/
theorem energy_from_shifted_relations (S A : Finset ℤ) (J : Finset ℤ)
    (hS : S.Nonempty) (hJ : J.Nonempty) (p q : ℕ) (hk : 3 ≤ p + q)
    {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hdensity : δ * (S.card : ℝ) ^ (p + q) ≤
      ∑ t ∈ J, (shiftedRelationCount S A p q t : ℝ))
    (hcarry : η ^ 3 * (J.card : ℝ) ^ 4 ≤ δ ^ 4) :
    η * (S.card : ℝ) ^ 4 ≤ (additiveEnergy S : ℝ) * (A.card : ℝ) := by
  have hr : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hj : (0 : ℝ) < J.card := by exact_mod_cast hJ.card_pos
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ δ * (S.card : ℝ) ^ (p + q))
    hdensity 4
  have hbound := shifted_relations_fourth_bound S A J p q hk
  have he : (S.card : ℝ) ^ (4 * (p + q)) =
      (S.card : ℝ) ^ (4 * (p + q - 3)) * (S.card : ℝ) ^ 12 := by
    rw [← pow_add]
    congr 1
    omega
  rw [mul_pow, ← pow_mul, Nat.mul_comm (p + q) 4, he] at hpow
  have hcancel : δ ^ 4 * (S.card : ℝ) ^ 12 ≤
      (J.card : ℝ) ^ 4 * (additiveEnergy S : ℝ) ^ 3 * (A.card : ℝ) ^ 3 := by
    apply (mul_le_mul_iff_right₀ (pow_pos hr (4 * (p + q - 3)))).mp
    calc
      _ = δ ^ 4 * ((S.card : ℝ) ^ (4 * (p + q - 3)) * (S.card : ℝ) ^ 12) := by ring
      _ ≤ _ := hpow.trans hbound
      _ = _ := by ring
  have hc := mul_le_mul_of_nonneg_right hcarry (by positivity : 0 ≤ (S.card : ℝ) ^ 12)
  have hfinal : (η * (S.card : ℝ) ^ 4) ^ 3 ≤
      ((additiveEnergy S : ℝ) * (A.card : ℝ)) ^ 3 := by
    apply (mul_le_mul_iff_right₀ (pow_pos hj 4)).mp
    calc
      _ = (η ^ 3 * (J.card : ℝ) ^ 4) * (S.card : ℝ) ^ 12 := by ring
      _ ≤ _ := hc.trans hcancel
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : 3 ≠ 0)).mp hfinal

noncomputable def carryRange (k : ℕ) : Finset ℤ := Finset.Icc (-4 * (k : ℤ)) (4 * (k : ℤ))

theorem carryRange_nonempty (k : ℕ) : (carryRange k).Nonempty := by
  refine ⟨0, ?_⟩
  simp only [carryRange, Finset.mem_Icc]
  constructor <;> omega

theorem carryRange_card (k : ℕ) : (carryRange k).card = 8 * k + 1 := by
  simp only [carryRange, Int.card_Icc]
  omega

theorem exponential_carry_bound {T : ℝ} (hT : 1 ≤ T) {k : ℕ}
    (hk : k ≤ Majority.majorityDegree T) :
    Real.exp (-2000 * T ^ 2) ^ 3 * ((carryRange k).card : ℝ) ^ 4 ≤
      Real.exp (-300 * T ^ 2) ^ 4 := by
  rw [carryRange_card]
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_exp, Real.log_pow, Real.log_exp]
  push_cast
  have hlog := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 8 * k + 1)
  have hm := Majority.majorityDegree_le_sixty_six hT
  have hk' : (k : ℝ) ≤ Majority.majorityDegree T := by exact_mod_cast hk
  nlinarith

theorem exponential_energy_from_relations (S A : Finset ℤ) (hS : S.Nonempty)
    (p q : ℕ) (hk : 3 ≤ p + q) {T : ℝ} (hT : 1 ≤ T)
    (hm : p + q ≤ Majority.majorityDegree T)
    (hdensity : Real.exp (-300 * T ^ 2) * (S.card : ℝ) ^ (p + q) ≤
      ∑ t ∈ carryRange (p + q), (shiftedRelationCount S A p q t : ℝ)) :
    Real.exp (-2000 * T ^ 2) * (S.card : ℝ) ^ 4 ≤
      (additiveEnergy S : ℝ) * (A.card : ℝ) :=
  energy_from_shifted_relations S A (carryRange (p + q)) hS (carryRange_nonempty _)
    p q hk (Real.exp_pos _).le (Real.exp_pos _).le hdensity (exponential_carry_bound hT hm)

theorem exponential_energy_small_set (S A : Finset ℤ) (hSA : S ⊆ A)
    {T : ℝ} (hT : 1 ≤ T) (hsmall : S.card < Majority.majorityDegree T) :
    Real.exp (-2000 * T ^ 2) * (S.card : ℝ) ^ 4 ≤
      (additiveEnergy S : ℝ) * (A.card : ℝ) := by
  have hrA : (S.card : ℝ) ≤ A.card := by exact_mod_cast Finset.card_le_card hSA
  have hrm : (S.card : ℝ) ≤ Majority.majorityDegree T := by exact_mod_cast hsmall.le
  have hm := Majority.majorityDegree_le_sixty_six hT
  have hexp : (S.card : ℝ) ≤ Real.exp (2000 * T ^ 2) := by
    have hh := Real.add_one_le_exp (2000 * T ^ 2)
    linarith
  have hcoef : Real.exp (-2000 * T ^ 2) * (S.card : ℝ) ≤ 1 := by
    rw [show -2000 * T ^ 2 = -(2000 * T ^ 2) by ring, Real.exp_neg]
    exact (inv_mul_le_one₀ (Real.exp_pos _)).mpr hexp
  have henergy : (S.card : ℝ) ^ 2 ≤ (additiveEnergy S : ℝ) := by
    exact_mod_cast (Finset.le_addEnergy_self (s := S))
  calc
    _ = (Real.exp (-2000 * T ^ 2) * (S.card : ℝ)) * (S.card : ℝ) ^ 3 := by ring
    _ ≤ 1 * (S.card : ℝ) ^ 3 := mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = (S.card : ℝ) ^ 2 * (S.card : ℝ) := by ring
    _ ≤ _ := mul_le_mul henergy hrA (by positivity) (by positivity)

end PacketEnergy
end LittlewoodInverse
