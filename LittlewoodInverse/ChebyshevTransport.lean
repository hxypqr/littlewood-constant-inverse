import LittlewoodInverse.SineFourier
import LittlewoodInverse.PolynomialTransport
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

open scoped BigOperators
open Polynomial

namespace LittlewoodInverse

/-- Written as a polynomial in `x²`, the truncated Chebyshev expansion. -/
noncomputable def absoluteValueApproximant (h : ℕ) : Polynomial ℝ :=
  C (2 / Real.pi) + ∑ k ∈ Finset.range h,
    C (-4 / Real.pi * sineWeight k) *
      (Polynomial.Chebyshev.T ℝ (k + 1)).comp (C 1 - C 2 * X)

theorem absoluteValueApproximant_degree (h : ℕ) :
    (absoluteValueApproximant h).natDegree ≤ h := by
  have hlin : (C 1 - C 2 * X : Polynomial ℝ).natDegree ≤ 1 := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · simp
    · exact (natDegree_C_mul_le _ _).trans natDegree_X_le
  unfold absoluteValueApproximant
  apply (natDegree_add_le _ _).trans
  apply max_le
  · simp
  · apply natDegree_sum_le_of_forall_le
    intro k hk
    apply (natDegree_C_mul_le _ _).trans
    apply natDegree_comp_le.trans
    rw [Polynomial.Chebyshev.natDegree_T]
    rw [show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by simp, Int.natAbs_natCast]
    have hk' : k + 1 ≤ h := Nat.succ_le_of_lt (Finset.mem_range.mp hk)
    simpa using (Nat.mul_le_mul_left (k + 1) hlin).trans (by simpa using hk')

theorem absoluteValueApproximant_error (h : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |x - (absoluteValueApproximant h).eval (x ^ 2)| ≤
      2 / (Real.pi * (2 * (h : ℝ) + 1)) := by
  let t : ℝ := Real.arcsin x / Real.pi
  have ht : t ∈ Set.Ico (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (Real.arcsin_nonneg.mpr hx0) Real.pi_pos.le
    · apply (div_lt_one Real.pi_pos).mpr
      linarith [Real.arcsin_le_pi_div_two x, Real.pi_pos]
  have hsin : Real.sin (Real.pi * t) = x := by
    dsimp [t]
    rw [mul_div_cancel₀ _ Real.pi_ne_zero]
    exact Real.sin_arcsin (by linarith) hx1
  have hcos : Real.cos (2 * Real.pi * t) = 1 - 2 * x ^ 2 := by
    rw [mul_assoc, Real.cos_two_mul]
    have hsq := Real.sin_sq_add_cos_sq (Real.pi * t)
    rw [hsin] at hsq
    nlinarith
  have heval : (absoluteValueApproximant h).eval (x ^ 2) =
      2 / Real.pi + ∑ k ∈ Finset.range h, -4 / Real.pi * sineWeight k *
        Real.cos (2 * Real.pi * (k + 1 : ℝ) * t) := by
    simp only [absoluteValueApproximant, eval_add, eval_C, eval_finsetSum,
      eval_mul, eval_comp, eval_sub, eval_X]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [← hcos, Polynomial.Chebyshev.T_real_cos]
    congr 2
    push_cast
    ring
  rw [heval, ← hsin]
  exact sine_cosine_truncation_error h ht

/-- Explicit even polynomial coefficients with the exact truncation error. -/
theorem exists_even_absoluteValue_approximation (h : ℕ) :
    ∃ a : Fin (h + 1) → ℝ, ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      |x - ∑ i, a i * x ^ (2 * i.val)| ≤
        2 / (Real.pi * (2 * (h : ℝ) + 1)) := by
  refine ⟨fun i => (absoluteValueApproximant h).coeff i.val, ?_⟩
  intro x hx0 hx1
  have heval := Polynomial.eval_eq_sum_range'
    (Nat.lt_succ_of_le (absoluteValueApproximant_degree h)) (x ^ 2)
  rw [← Fin.sum_univ_eq_sum_range] at heval
  simp only [← pow_mul] at heval
  rw [← heval]
  exact absoluteValueApproximant_error h hx0 hx1

/-- The exact norm-transport bound in Lemma 9.2, with the approximation
and all Fourier moments proved internally. -/
theorem freiman_norm_transport {h : ℕ} {A : Finset ℤ} {B : Set ℤ} {f : ℤ → ℤ}
    (hf : IsAddFreimanIso h (A : Set ℤ) B f) {C : Finset ℤ} (hCA : C ⊆ A) :
    |littlewoodNorm C - littlewoodNorm (C.image f)| ≤
      4 * (C.card : ℝ) / (Real.pi * (2 * (h : ℝ) + 1)) := by
  obtain ⟨a, ha⟩ := exists_even_absoluteValue_approximation h
  have ht := freiman_norm_transport_of_approximation hf hCA a ha
  convert ht using 1
  ring

/-- Every corresponding subset has distortion less than `2/π` in a
model of order equal to the original set's cardinality. -/
theorem freiman_cardinality_order_norm_transport {A : Finset ℤ} {B : Set ℤ}
    {f : ℤ → ℤ} (hf : IsAddFreimanIso A.card (A : Set ℤ) B f)
    {C : Finset ℤ} (hCA : C ⊆ A) :
    |littlewoodNorm C - littlewoodNorm (C.image f)| < 2 / Real.pi := by
  apply (freiman_norm_transport hf hCA).trans_lt
  have hsize : (C.card : ℝ) ≤ A.card := by exact_mod_cast Finset.card_le_card hCA
  have hd : 0 < Real.pi * (2 * (A.card : ℝ) + 1) := by positivity
  apply (div_lt_div_iff₀ hd Real.pi_pos).mpr
  have hm := mul_le_mul_of_nonneg_right hsize Real.pi_pos.le
  nlinarith [Real.pi_pos]

/-- The norm parameter increases from `K` to `K+1` in an order-cardinality
integer model, as used in the completion of the inverse theorem. -/
theorem freiman_model_logarithmic_bound {A : Finset ℤ} {B : Set ℤ}
    {f : ℤ → ℤ} (hf : IsAddFreimanIso A.card (A : Set ℤ) B f)
    (hN : 2 ≤ A.card) {K : ℝ}
    (hK : littlewoodNorm A ≤ K * Real.log (A.card : ℝ)) :
    littlewoodNorm (A.image f) ≤ (K + 1) * Real.log ((A.image f).card : ℝ) := by
  have hcard : (A.image f).card = A.card :=
    Finset.card_image_of_injOn hf.bijOn.injOn
  rw [hcard]
  have ht := (abs_lt.mp (freiman_cardinality_order_norm_transport hf
    (Finset.Subset.refl A))).1
  have htwo : 2 / Real.pi < Real.log 2 := by
    have hsmall : 2 / Real.pi < (2 : ℝ) / 3 :=
      div_lt_div_of_pos_left (by norm_num) (by norm_num) Real.pi_gt_three
    exact hsmall.trans (by linarith [Real.log_two_gt_d9])
  have hlog : Real.log 2 ≤ Real.log (A.card : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  nlinarith

end LittlewoodInverse
