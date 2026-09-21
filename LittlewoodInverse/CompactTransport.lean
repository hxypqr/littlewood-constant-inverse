import LittlewoodInverse.CompactHereditary
import LittlewoodInverse.ChebyshevTransport
import LittlewoodInverse.CompactFreimanMoments

open scoped BigOperators
open MeasureTheory

namespace LittlewoodInverse

section Analytic

variable {α β : Type*}
  [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α] [BorelSpace α]
  [TopologicalSpace β] [CompactSpace β] [MeasurableSpace β] [BorelSpace β]

theorem norm_polynomial_approximation_integral (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → ℂ} (hf : Continuous f) {m : ℝ} (hm : 0 < m)
    (hbound : ∀ x, ‖f x‖ ≤ m) {h : ℕ} (a : Fin (h + 1) → ℝ) {δ : ℝ}
    (happrox : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      |x - ∑ i, a i * x ^ (2 * i.val)| ≤ δ) :
    |(∫ x, ‖f x‖ ∂μ) / m -
      ∫ x, ∑ i, a i * (‖f x‖ / m) ^ (2 * i.val) ∂μ| ≤ δ := by
  let p (x : α) := ∑ i, a i * (‖f x‖ / m) ^ (2 * i.val)
  have hp : Continuous p := by dsimp [p]; fun_prop
  calc
    _ = |∫ x, (‖f x‖ / m - p x) ∂μ| := by
      rw [integral_sub (compact_integrable (by fun_prop)) (compact_integrable hp), integral_div]
    _ ≤ ∫ x, |‖f x‖ / m - p x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _ : α, δ ∂μ := by
      apply integral_mono (compact_integrable (by fun_prop)) (integrable_const _)
      intro x
      exact happrox _ (div_nonneg (norm_nonneg _) hm.le) ((div_le_one hm).mpr (hbound x))
    _ = δ := by simp

/-- The approximation step works on two different compact probability
spaces. The actual character moments are supplied by the next theorem. -/
theorem integral_norm_transport_of_moments
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [IsProbabilityMeasure ν]
    {f : α → ℂ} {g : β → ℂ} (hf : Continuous f) (hg : Continuous g)
    {m : ℝ} (hm : 0 < m) (hfbound : ∀ x, ‖f x‖ ≤ m) (hgbound : ∀ y, ‖g y‖ ≤ m)
    {h : ℕ} (hmom : ∀ j ≤ h,
      (∫ x, ‖f x‖ ^ (2 * j) ∂μ) = ∫ y, ‖g y‖ ^ (2 * j) ∂ν)
    (a : Fin (h + 1) → ℝ) {δ : ℝ}
    (happrox : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      |x - ∑ i, a i * x ^ (2 * i.val)| ≤ δ) :
    |(∫ x, ‖f x‖ ∂μ) - ∫ y, ‖g y‖ ∂ν| ≤ 2 * m * δ := by
  have heq : (∫ x, ∑ i, a i * (‖f x‖ / m) ^ (2 * i.val) ∂μ) =
      ∫ y, ∑ i, a i * (‖g y‖ / m) ^ (2 * i.val) ∂ν := by
    rw [integral_finsetSum _ (fun _ _ => compact_integrable (by fun_prop)),
      integral_finsetSum _ (fun _ _ => compact_integrable (by fun_prop))]
    apply Finset.sum_congr rfl
    intro i _
    simp only [div_pow, integral_const_mul, integral_div,
      hmom i.val (Nat.le_of_lt_succ i.isLt)]
  have h1 := norm_polynomial_approximation_integral μ hf hm hfbound a happrox
  have h2 := norm_polynomial_approximation_integral ν hg hm hgbound a happrox
  rw [← heq] at h2
  have he : |(∫ x, ‖f x‖ ∂μ) / m - (∫ y, ‖g y‖ ∂ν) / m| ≤ 2 * δ := by
    calc
      _ ≤ |(∫ x, ‖f x‖ ∂μ) / m -
          ∫ x, ∑ i, a i * (‖f x‖ / m) ^ (2 * i.val) ∂μ| +
        |(∫ y, ‖g y‖ ∂ν) / m -
          ∫ x, ∑ i, a i * (‖f x‖ / m) ^ (2 * i.val) ∂μ| := by
        simpa only [abs_sub_comm (∫ x, ∑ i, a i * (‖f x‖ / m) ^ (2 * i.val) ∂μ)] using
          abs_sub_le ((∫ x, ‖f x‖ ∂μ) / m)
            (∫ x, ∑ i, a i * (‖f x‖ / m) ^ (2 * i.val) ∂μ)
            ((∫ y, ‖g y‖ ∂ν) / m)
      _ ≤ 2 * δ := by linarith
  rw [← sub_div, abs_div, abs_of_pos hm] at he
  have he' := (div_le_iff₀ hm).mp he
  nlinarith

end Analytic

theorem compactSet_norm_le_card {Γ G : Type*} [AddCommGroup Γ] [CommGroup G]
    [TopologicalSpace G] (χ : Γ →+ Additive (PontryaginDual G))
    (C : Finset Γ) (x : G) : ‖compactPolynomial χ C (fun _ => 1) x‖ ≤ (C.card : ℝ) := by
  unfold compactPolynomial
  calc
    _ ≤ ∑ r ∈ C, ‖(1 : ℂ) * compactCharacter χ r x‖ := norm_sum_le _ _
    _ = _ := by simp

section Compact

variable {Γ Λ G H : Type*} [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup Λ] [DecidableEq Λ] [CommGroup G] [CommGroup H]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]
  [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [MeasurableSpace H] [BorelSpace H]
  (μ : Measure G) [IsProbabilityMeasure μ] [Measure.IsMulLeftInvariant μ]
  (ν : Measure H) [IsProbabilityMeasure ν] [Measure.IsMulLeftInvariant ν]
  (χ : Γ →+ Additive (PontryaginDual G))
  (ψ : Λ →+ Additive (PontryaginDual H))
  (hχ : Function.Injective χ) (hψ : Function.Injective ψ)

include hχ hψ

/-- Full cross-group norm transport for faithful compact character models.
Both actual moment identities and the Chebyshev approximation are proved
internally. There is no assumed moment-preservation or approximation input. -/
theorem compact_freiman_norm_transport {h : ℕ} {A : Finset Γ} {B : Set Λ}
    {f : Γ → Λ} (hf : IsAddFreimanIso h (A : Set Γ) B f)
    {C : Finset Γ} (hCA : C ⊆ A) :
    |compactLittlewoodNorm μ χ C - compactLittlewoodNorm ν ψ (C.image f)| ≤
      4 * (C.card : ℝ) / (Real.pi * (2 * (h : ℝ) + 1)) := by
  by_cases hC : C = ∅
  · simp [hC, compactLittlewoodNorm, compactPolynomial]
  have hm : (0 : ℝ) < C.card :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hC))
  have hcard : (C.image f).card = C.card := Finset.card_image_of_injOn
    (fun x hx y hy hxy => hf.bijOn.injOn (hCA hx) (hCA hy) hxy)
  obtain ⟨a, ha⟩ := exists_even_absoluteValue_approximation h
  have ht := integral_norm_transport_of_moments μ ν
    (continuous_compactPolynomial χ C (fun _ => 1))
    (continuous_compactPolynomial ψ (C.image f) (fun _ => 1)) hm
    (compactSet_norm_le_card χ C)
    (fun y => by simpa only [hcard] using compactSet_norm_le_card ψ (C.image f) y)
    (fun j hj => compact_freiman_integral_even_moment μ ν χ ψ hχ hψ hf hj hCA) a ha
  change |(∫ x, ‖compactPolynomial χ C (fun _ => 1) x‖ ∂μ) -
    ∫ y, ‖compactPolynomial ψ (C.image f) (fun _ => 1) y‖ ∂ν| ≤ _
  convert ht using 1
  ring

/-- The same uniform subset error is below `2/π` at order equal to the
original cardinality, independently of the source and target groups. -/
theorem compact_freiman_cardinality_order_norm_transport
    {A : Finset Γ} {B : Set Λ} {f : Γ → Λ}
    (hf : IsAddFreimanIso A.card (A : Set Γ) B f) {C : Finset Γ} (hCA : C ⊆ A) :
    |compactLittlewoodNorm μ χ C - compactLittlewoodNorm ν ψ (C.image f)| < 2 / Real.pi := by
  apply (compact_freiman_norm_transport μ ν χ ψ hχ hψ hf hCA).trans_lt
  have hsize : (C.card : ℝ) ≤ A.card := by exact_mod_cast Finset.card_le_card hCA
  have hd : 0 < Real.pi * (2 * (A.card : ℝ) + 1) := by positivity
  apply (div_lt_div_iff₀ hd Real.pi_pos).mpr
  have hm := mul_le_mul_of_nonneg_right hsize Real.pi_pos.le
  nlinarith [Real.pi_pos]

end Compact

end LittlewoodInverse
