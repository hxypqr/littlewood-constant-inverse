import LittlewoodInverse.ResidueProjection
import LittlewoodInverse.CyclicSpectral

open scoped BigOperators Pointwise ComplexConjugate symmDiff
open MeasureTheory

namespace LittlewoodInverse

variable {q : ℕ}

def boundaryShift (p : ZMod q × ℤ) : ZMod q × ℤ := (p.1, p.2 + 1)

theorem boundaryShift_injective : Function.Injective (boundaryShift (q := q)) := by
  rintro ⟨b, u⟩ ⟨c, v⟩ h
  simp only [boundaryShift, Prod.mk.injEq] at h
  exact Prod.ext h.1 (add_right_cancel h.2)

def boundaryTranslate (C : Finset (ZMod q × ℤ)) : Finset (ZMod q × ℤ) :=
  C.image boundaryShift

def boundaryCarrier (C : Finset (ZMod q × ℤ)) : Finset (ZMod q × ℤ) :=
  C ∪ boundaryTranslate C

def boundaryValue (C : Finset (ZMod q × ℤ)) (p : ZMod q × ℤ) : ℤ :=
  (if p ∈ C then 1 else 0) - (if p ∈ boundaryTranslate C then 1 else 0)

def boundaryMass (C : Finset (ZMod q × ℤ)) : ℕ :=
  (C ∆ boundaryTranslate C).card

theorem mem_boundaryTranslate (C : Finset (ZMod q × ℤ)) (p : ZMod q × ℤ) :
    p ∈ boundaryTranslate C ↔ (p.1, p.2 - 1) ∈ C := by
  rcases p with ⟨b, u⟩
  simp only [boundaryTranslate, Finset.mem_image, boundaryShift, Prod.exists,
    Prod.mk.injEq]
  constructor
  · rintro ⟨c, v, h, rfl, hv⟩
    have he : v = u - 1 := by omega
    simpa only [← he] using h
  · intro h
    exact ⟨b, u - 1, h, rfl, by omega⟩

theorem boundaryValue_formula (C : Finset (ZMod q × ℤ)) (b : ZMod q) (u : ℤ) :
    boundaryValue C (b, u) = (if (b, u) ∈ C then 1 else 0) -
      (if (b, u - 1) ∈ C then 1 else 0) := by
  simp only [boundaryValue, mem_boundaryTranslate]

theorem boundaryValue_cases (C : Finset (ZMod q × ℤ)) (p : ZMod q × ℤ) :
    boundaryValue C p = -1 ∨ boundaryValue C p = 0 ∨ boundaryValue C p = 1 := by
  unfold boundaryValue
  split_ifs <;> norm_num

theorem boundaryValue_ne_zero_iff (C : Finset (ZMod q × ℤ)) (p : ZMod q × ℤ) :
    boundaryValue C p ≠ 0 ↔ p ∈ C ∆ boundaryTranslate C := by
  simp only [boundaryValue, Finset.mem_symmDiff]
  split_ifs <;> simp_all

theorem boundaryMass_le (C : Finset (ZMod q × ℤ)) : boundaryMass C ≤ 2 * C.card := by
  have hsub : C ∆ boundaryTranslate C ⊆ C ∪ boundaryTranslate C :=
    Finset.symmDiff_subset_union
  calc
    _ ≤ (C ∪ boundaryTranslate C).card := Finset.card_le_card hsub
    _ ≤ C.card + (boundaryTranslate C).card := Finset.card_union_le _ _
    _ = _ := by
      rw [boundaryTranslate, Finset.card_image_of_injective _ boundaryShift_injective]
      omega

theorem boundary_nonzero {C : Finset (ZMod q × ℤ)} (hC : C.Nonempty) :
    ∃ p, boundaryValue C p ≠ 0 := by
  classical
  let U := C.image Prod.snd
  have hU : U.Nonempty := hC.image _
  have hm : U.max' hU ∈ U := Finset.max'_mem _ _
  obtain ⟨⟨b, u⟩, hbu, hu⟩ := Finset.mem_image.mp hm
  have hnot : (b, u + 1) ∉ C := by
    intro h
    have hm' := Finset.le_max' U (u + 1) (Finset.mem_image.mpr ⟨(b, u + 1), h, rfl⟩)
    dsimp only at hu
    omega
  refine ⟨(b, u + 1), ?_⟩
  rw [boundaryValue_formula]
  simp [hnot, hbu]

theorem boundaryMass_pos {C : Finset (ZMod q × ℤ)} (hC : C.Nonempty) :
    0 < boundaryMass C := by
  obtain ⟨p, hp⟩ := boundary_nonzero hC
  exact Finset.card_pos.mpr ⟨p, (boundaryValue_ne_zero_iff C p).mp hp⟩

theorem boundary_sum (C : Finset (ZMod q × ℤ)) (f : ZMod q × ℤ → ℂ) :
    (∑ p ∈ boundaryCarrier C, (boundaryValue C p : ℂ) * f p) =
      ∑ p ∈ C, (f p - f (boundaryShift p)) := by
  simp only [boundaryValue, Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero,
    sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib,
    Finset.sum_ite_mem, boundaryCarrier, Finset.union_inter_cancel_left,
    Finset.union_inter_cancel_right]
  rw [boundaryTranslate, Finset.sum_image]
  intro p _ r _ h
  exact boundaryShift_injective h

theorem boundaryMass_eq_sum_sq (C : Finset (ZMod q × ℤ)) :
    (boundaryMass C : ℝ) =
      ∑ p ∈ boundaryCarrier C, (boundaryValue C p : ℝ) ^ 2 := by
  classical
  have hf : C ∆ boundaryTranslate C =
      (boundaryCarrier C).filter (fun p => boundaryValue C p ≠ 0) := by
    ext p
    simp only [Finset.mem_filter, ← boundaryValue_ne_zero_iff]
    constructor
    · intro hp
      refine ⟨?_, hp⟩
      exact Finset.symmDiff_subset_union ((boundaryValue_ne_zero_iff C p).mp hp)
    · exact And.right
  change (((C ∆ boundaryTranslate C).card : ℕ) : ℝ) = _
  rw [hf, Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro p _
  rcases boundaryValue_cases C p with h | h | h <;> simp [h]

variable (q) [NeZero q]

noncomputable def boundaryPolynomial (C : Finset (ZMod q × ℤ))
    (j : ZMod q) (s : Circle) : ℂ :=
  ∑ p ∈ boundaryCarrier C,
    (boundaryValue C p : ℂ) * (cyclicCharacter q p.1 j * fourier p.2 s)

theorem boundaryPolynomial_continuous (C : Finset (ZMod q × ℤ)) (j : ZMod q) :
    Continuous (boundaryPolynomial q C j) := by
  unfold boundaryPolynomial
  fun_prop

theorem boundaryPolynomial_difference (C : Finset (ZMod q × ℤ))
    (j : ZMod q) (s : Circle) :
    boundaryPolynomial q C j s = (1 - fourier 1 s) *
      ∑ p ∈ C, cyclicCharacter q p.1 j * fourier p.2 s := by
  rw [boundaryPolynomial, boundary_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp only [boundaryShift, fourier_add]
  ring

theorem boundaryPolynomial_zero (C : Finset (ZMod q × ℤ)) (j : ZMod q) :
    boundaryPolynomial q C j 0 = 0 := by
  simp [boundaryPolynomial_difference]

def blockCellIndex (M : ℕ) (p : (ZMod q × ℤ) × ℕ) : ℤ :=
  (p.1.1.val : ℤ) + (q : ℤ) * ((M : ℤ) * p.1.2 + (p.2 : ℤ))

theorem blockCellIndex_injective {M : ℕ} (hM : 0 < M)
    {p r : (ZMod q × ℤ) × ℕ} (hp : p.2 < M) (hr : r.2 < M)
    (he : blockCellIndex q M p = blockCellIndex q M r) : p = r := by
  have he' : residueHeight q (p.1.1, (M : ℤ) * p.1.2 + p.2) =
      residueHeight q (r.1.1, (M : ℤ) * r.1.2 + r.2) := he
  have hx := residueHeight_injective q he'
  have hb := congrArg Prod.fst hx
  have hu := congrArg Prod.snd hx
  dsimp only at hb hu
  have hMp : (0 : ℤ) < M := by exact_mod_cast hM
  have hp' : (0 : ℤ) ≤ p.2 ∧ (p.2 : ℤ) < M := by exact_mod_cast (show 0 ≤ p.2 ∧ p.2 < M by omega)
  have hr' : (0 : ℤ) ≤ r.2 ∧ (r.2 : ℤ) < M := by exact_mod_cast (show 0 ≤ r.2 ∧ r.2 < M by omega)
  have huu : p.1.2 = r.1.2 := by
    rcases lt_trichotomy p.1.2 r.1.2 with h | h | h
    · have hh : p.1.2 + 1 ≤ r.1.2 := by omega
      have hm := mul_le_mul_of_nonneg_left hh hMp.le
      nlinarith
    · exact h
    · have hh : r.1.2 + 1 ≤ p.1.2 := by omega
      have hm := mul_le_mul_of_nonneg_left hh hMp.le
      nlinarith
  have hpr : p.2 = r.2 := by
    rw [huu] at hu
    exact_mod_cast add_left_cancel hu
  exact Prod.ext (Prod.ext hb huu) hpr

theorem blockInflation_eq_image (M : ℕ) (C : Finset (ZMod q × ℤ)) :
    blockInflation q M C = (C ×ˢ Finset.range M).image (blockCellIndex q M) := by
  ext x
  simp only [blockInflation, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product,
    Prod.exists, blockCellIndex]
  aesop

theorem blockInflation_card {M : ℕ} (hM : 0 < M) (C : Finset (ZMod q × ℤ)) :
    (blockInflation q M C).card = M * C.card := by
  rw [blockInflation_eq_image, Finset.card_image_of_injOn]
  · simp [mul_comm]
  · intro p hp r hr he
    exact blockCellIndex_injective q hM (Finset.mem_range.mp (Finset.mem_product.mp hp).2)
      (Finset.mem_range.mp (Finset.mem_product.mp hr).2) he

theorem fourier_nat_mul (n : ℤ) (r : ℕ) (t : Circle) :
    fourier (n * r) t = fourier n t ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, fourier_add, ih, pow_succ]

theorem blockInflation_fourier {M : ℕ} (hM : 0 < M)
    (C : Finset (ZMod q × ℤ)) (t : Circle) :
    fourierPolynomial (blockInflation q M C) t =
      ∑ p ∈ C, fourier ((p.1.val : ℤ) + (q : ℤ) * M * p.2) t *
        ∑ r ∈ Finset.range M, fourier (q : ℤ) t ^ r := by
  rw [blockInflation_eq_image, fourierPolynomial, Finset.sum_image]
  · simp only [Finset.sum_product, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro r _
    rw [← fourier_nat_mul, ← fourier_add]
    apply congrArg (fun n : ℤ => fourier n t)
    dsimp [blockCellIndex]
    ring
  · intro p hp r hr he
    exact blockCellIndex_injective q hM (Finset.mem_range.mp (Finset.mem_product.mp hp).2)
      (Finset.mem_range.mp (Finset.mem_product.mp hr).2) he

/-- The exact finite-cell boundary identity, before dividing by a sine. -/
theorem block_boundary_identity {M : ℕ} (hM : 0 < M)
    (C : Finset (ZMod q × ℤ)) (t : Circle) :
    (1 - fourier (q : ℤ) t) * fourierPolynomial (blockInflation q M C) t =
      ∑ p ∈ boundaryCarrier C, (boundaryValue C p : ℂ) *
        fourier ((p.1.val : ℤ) + (q : ℤ) * M * p.2) t := by
  rw [blockInflation_fourier q hM, boundary_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [show (1 - fourier (q : ℤ) t) *
      (fourier ((p.1.val : ℤ) + (q : ℤ) * M * p.2) t *
        ∑ r ∈ Finset.range M, fourier (q : ℤ) t ^ r) =
      fourier ((p.1.val : ℤ) + (q : ℤ) * M * p.2) t *
        ((1 - fourier (q : ℤ) t) * ∑ r ∈ Finset.range M, fourier (q : ℤ) t ^ r) by ring]
  rw [mul_neg_geom_sum, ← fourier_nat_mul, mul_sub, mul_one, ← fourier_add]
  apply congrArg (fun n : ℤ =>
    fourier ((p.1.val : ℤ) + (q : ℤ) * M * p.2) t - fourier n t)
  dsimp [boundaryShift]
  ring

noncomputable def boundaryDualMeasure : Measure (Circle × ZMod q) :=
  circleMeasure.prod (cyclicMeasure q)

instance boundaryDualMeasure_probability : IsProbabilityMeasure (boundaryDualMeasure q) := by
  unfold boundaryDualMeasure
  infer_instance

theorem boundary_dual_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Circle × ZMod q → E} (hf : Continuous f) :
    Integrable f (boundaryDualMeasure q) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

noncomputable def mixedCharacter (p : ZMod q × ℤ) (z : Circle × ZMod q) : ℂ :=
  fourier p.2 z.1 * cyclicCharacter q p.1 z.2

@[fun_prop] theorem mixedCharacter_continuous (p : ZMod q × ℤ) :
    Continuous (mixedCharacter q p) := by
  unfold mixedCharacter
  exact ((map_continuous (fourier p.2)).comp continuous_fst).mul
    ((continuous_of_discreteTopology : Continuous (cyclicCharacter q p.1)).comp continuous_snd)

@[simp] theorem mixedCharacter_norm (p : ZMod q × ℤ) (z : Circle × ZMod q) :
    ‖mixedCharacter q p z‖ = 1 := by
  simp [mixedCharacter, fourier_apply]

theorem integral_mixedCharacter_pair (p r : ZMod q × ℤ) :
    (∫ z, mixedCharacter q p z * conj (mixedCharacter q r z) ∂boundaryDualMeasure q) =
      if p = r then 1 else 0 := by
  rw [boundaryDualMeasure, integral_prod _ (boundary_dual_integrable q (by fun_prop))]
  simp only [mixedCharacter, integral_cyclic_term_pair]
  by_cases hb : p.1 = r.1
  · simp only [hb, ite_true]
    rw [integral_fourier_mul_conj]
    simp only [Prod.ext_iff, hb, true_and]
  · simp only [hb, ite_false, integral_zero]
    rw [if_neg (fun h => hb (congrArg Prod.fst h))]

theorem integral_mixed_term_pair (p r : ZMod q × ℤ) (a b : ℂ) :
    (∫ z, (a * mixedCharacter q p z) * conj (b * mixedCharacter q r z)
      ∂boundaryDualMeasure q) = if p = r then a * conj b else 0 := by
  have he : (fun z => (a * mixedCharacter q p z) * conj (b * mixedCharacter q r z)) =
      (fun z => (a * conj b) * (mixedCharacter q p z * conj (mixedCharacter q r z))) := by
    funext z
    simp only [map_mul]
    ring
  rw [he, integral_const_mul, integral_mixedCharacter_pair]
  split_ifs <;> simp

noncomputable def mixedPolynomial (I : Finset (ZMod q × ℤ)) (a : ZMod q × ℤ → ℂ)
    (z : Circle × ZMod q) : ℂ := ∑ p ∈ I, a p * mixedCharacter q p z

@[fun_prop] theorem mixedPolynomial_continuous (I : Finset (ZMod q × ℤ))
    (a : ZMod q × ℤ → ℂ) : Continuous (mixedPolynomial q I a) := by
  unfold mixedPolynomial
  fun_prop

theorem mixedPolynomial_pair (I J : Finset (ZMod q × ℤ)) (a b : ZMod q × ℤ → ℂ) :
    (∫ z, mixedPolynomial q I a z * conj (mixedPolynomial q J b z)
      ∂boundaryDualMeasure q) = ∑ p ∈ I ∩ J, a p * conj (b p) := by
  unfold mixedPolynomial
  simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum I (fun _ _ => boundary_dual_integrable q (by fun_prop))]
  have hi (p : ZMod q × ℤ) :
      (∫ z, ∑ r ∈ J, (a p * mixedCharacter q p z) * conj (b r * mixedCharacter q r z)
        ∂boundaryDualMeasure q) =
      ∑ r ∈ J, ∫ z, (a p * mixedCharacter q p z) * conj (b r * mixedCharacter q r z)
        ∂boundaryDualMeasure q :=
    integral_finsetSum J (fun _ _ => boundary_dual_integrable q (by fun_prop))
  simp_rw [hi, integral_mixed_term_pair]
  simp

theorem mixedPolynomial_second_moment (I : Finset (ZMod q × ℤ))
    (a : ZMod q × ℤ → ℂ) :
    (∫ z, ‖mixedPolynomial q I a z‖ ^ 2 ∂boundaryDualMeasure q) =
      ∑ p ∈ I, ‖a p‖ ^ 2 := by
  have hp := mixedPolynomial_pair q I I a a
  simp only [Finset.inter_self, Complex.mul_conj', ← Complex.ofReal_pow] at hp
  exact_mod_cast hp

theorem boundaryPolynomial_eq_mixed (C : Finset (ZMod q × ℤ))
    (z : Circle × ZMod q) :
    boundaryPolynomial q C z.2 z.1 =
      mixedPolynomial q (boundaryCarrier C) (fun p => (boundaryValue C p : ℂ)) z := by
  simp only [boundaryPolynomial, mixedPolynomial, mixedCharacter, mul_comm]

noncomputable def boundaryNorm (C : Finset (ZMod q × ℤ)) : ℝ :=
  ∫ z, ‖boundaryPolynomial q C z.2 z.1‖ ∂boundaryDualMeasure q

theorem boundaryNorm_nonneg (C : Finset (ZMod q × ℤ)) : 0 ≤ boundaryNorm q C :=
  integral_nonneg fun _ => norm_nonneg _

theorem boundary_second_moment (C : Finset (ZMod q × ℤ)) :
    (∫ z, ‖boundaryPolynomial q C z.2 z.1‖ ^ 2 ∂boundaryDualMeasure q) =
      (boundaryMass C : ℝ) := by
  simp_rw [boundaryPolynomial_eq_mixed]
  rw [mixedPolynomial_second_moment, boundaryMass_eq_sum_sq]
  apply Finset.sum_congr rfl
  intro p _
  simp [Complex.norm_intCast, sq_abs]

theorem boundaryNorm_le_sqrt_mass (C : Finset (ZMod q × ℤ)) :
    boundaryNorm q C ≤ Real.sqrt (boundaryMass C : ℝ) := by
  have hc : Continuous (fun z : Circle × ZMod q => boundaryPolynomial q C z.2 z.1) := by
    simp_rw [boundaryPolynomial_eq_mixed]
    fun_prop
  have hh := integral_cauchy_schwarz_sq (μ := boundaryDualMeasure q)
    (f := fun z => ‖boundaryPolynomial q C z.2 z.1‖) (g := fun _ => (1 : ℝ))
    (boundary_dual_integrable q (by fun_prop))
    (boundary_dual_integrable q (by fun_prop))
    (boundary_dual_integrable q (by fun_prop))
  simp only [mul_one, one_pow, integral_const, probReal_univ, smul_eq_mul,
    boundary_second_moment] at hh
  exact (Real.le_sqrt (boundaryNorm_nonneg q C) (Nat.cast_nonneg _)).mpr hh

theorem mixedCoefficient_norm_le (I : Finset (ZMod q × ℤ)) (a : ZMod q × ℤ → ℂ)
    {p : ZMod q × ℤ} (hp : p ∈ I) :
    ‖a p‖ ≤ ∫ z, ‖mixedPolynomial q I a z‖ ∂boundaryDualMeasure q := by
  have hh := mixedPolynomial_pair q I {p} a (fun _ => 1)
  simp only [mixedPolynomial, Finset.sum_singleton, one_mul] at hh
  have he : (∫ z, mixedPolynomial q I a z * conj (mixedCharacter q p z)
      ∂boundaryDualMeasure q) = a p := by
    simpa [mixedPolynomial, hp] using hh
  calc
    ‖a p‖ = ‖∫ z, mixedPolynomial q I a z * conj (mixedCharacter q p z)
        ∂boundaryDualMeasure q‖ := congrArg norm he.symm
    _ ≤ ∫ z, ‖mixedPolynomial q I a z * conj (mixedCharacter q p z)‖
        ∂boundaryDualMeasure q := norm_integral_le_integral_norm _
    _ = _ := by simp

theorem one_le_boundaryNorm {C : Finset (ZMod q × ℤ)} (hC : C.Nonempty) :
    1 ≤ boundaryNorm q C := by
  obtain ⟨p, hp⟩ := boundary_nonzero hC
  have hmem : p ∈ boundaryCarrier C :=
    Finset.symmDiff_subset_union ((boundaryValue_ne_zero_iff C p).mp hp)
  have hh := mixedCoefficient_norm_le q (boundaryCarrier C)
    (fun p => (boundaryValue C p : ℂ)) hmem
  have habs : ‖(boundaryValue C p : ℂ)‖ = 1 := by
    rcases boundaryValue_cases C p with h | h | h <;> simp_all
  simpa only [habs, boundaryNorm, ← boundaryPolynomial_eq_mixed] using hh

noncomputable def boundaryVertical (C : Finset (ZMod q × ℤ)) (b : ZMod q)
    (s : Circle) : ℂ :=
  ∑ p ∈ boundaryCarrier C,
    if p.1 = b then (boundaryValue C p : ℂ) * fourier p.2 s else 0

omit [NeZero q] in
@[fun_prop] theorem boundaryVertical_continuous (C : Finset (ZMod q × ℤ)) (b : ZMod q) :
    Continuous (boundaryVertical q C b) := by
  unfold boundaryVertical
  apply continuous_finsetSum
  intro p _
  split_ifs <;> fun_prop

theorem boundaryPolynomial_cyclic (C : Finset (ZMod q × ℤ)) (j : ZMod q) (s : Circle) :
    cyclicPolynomial q Finset.univ (fun b => boundaryVertical q C b s) j =
      boundaryPolynomial q C j s := by
  unfold cyclicPolynomial boundaryVertical boundaryPolynomial
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

noncomputable def boundaryQ (C : Finset (ZMod q × ℤ)) (s : Circle) : ℝ :=
  Real.sqrt (∑ b : ZMod q, ‖boundaryVertical q C b s‖ ^ 2)

@[fun_prop] theorem boundaryQ_continuous (C : Finset (ZMod q × ℤ)) :
    Continuous (boundaryQ q C) := by unfold boundaryQ; fun_prop

theorem boundaryQ_nonneg (C : Finset (ZMod q × ℤ)) (s : Circle) :
    0 ≤ boundaryQ q C s := Real.sqrt_nonneg _

theorem boundaryQ_sq (C : Finset (ZMod q × ℤ)) (s : Circle) :
    boundaryQ q C s ^ 2 =
      ∫ j, ‖boundaryPolynomial q C j s‖ ^ 2 ∂cyclicMeasure q := by
  simp_rw [← boundaryPolynomial_cyclic, integral_cyclicPolynomial_norm_sq]
  exact Real.sq_sqrt (Finset.sum_nonneg fun b _ => sq_nonneg _)

theorem integral_boundaryQ_sq (C : Finset (ZMod q × ℤ)) :
    (∫ s, boundaryQ q C s ^ 2 ∂circleMeasure) = (boundaryMass C : ℝ) := by
  simp_rw [boundaryQ_sq]
  rw [← integral_prod (fun z : Circle × ZMod q => ‖boundaryPolynomial q C z.2 z.1‖ ^ 2)]
  · exact boundary_second_moment q C
  · apply boundary_dual_integrable q
    simp_rw [boundaryPolynomial_eq_mixed]
    fun_prop

theorem integral_boundaryQ_le (C : Finset (ZMod q × ℤ)) :
    (∫ s, boundaryQ q C s ∂circleMeasure) ≤ Real.sqrt (boundaryMass C : ℝ) := by
  have hh := integral_cauchy_schwarz_sq (μ := circleMeasure)
    (f := boundaryQ q C) (g := fun _ => (1 : ℝ))
    (continuous_circle_integrable (by fun_prop))
    (continuous_circle_integrable (by fun_prop))
    (continuous_circle_integrable (by fun_prop))
  simp only [mul_one, one_pow, integral_const, probReal_univ, smul_eq_mul,
    integral_boundaryQ_sq] at hh
  exact (Real.le_sqrt (integral_nonneg (boundaryQ_nonneg q C)) (Nat.cast_nonneg _)).mpr hh

noncomputable def boundaryPhase (b : ZMod q) (t : ℝ) : ℂ :=
  fourier (b.val : ℤ) ((t / q : ℝ) : Circle)

theorem boundaryPhase_sub_one_le (b : ZMod q) (t : ℝ) :
    ‖boundaryPhase q b t - 1‖ ≤ 2 * Real.pi * |t| := by
  have hq : (0 : ℝ) < q := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q))
  have hb : (b.val : ℝ) ≤ q := by exact_mod_cast (ZMod.val_lt b).le
  have he : boundaryPhase q b t =
      Complex.exp (Complex.I * ((2 * Real.pi * (b.val : ℝ) * (t / q) : ℝ) : ℂ)) := by
    simp only [boundaryPhase, fourier_coe_apply, Complex.ofReal_one, div_one]
    congr 1
    push_cast
    ring
  rw [he]
  apply Real.norm_exp_I_mul_ofReal_sub_one_le.trans
  simp only [Real.norm_eq_abs, abs_mul, abs_div,
    abs_of_pos Real.pi_pos, abs_of_nonneg (show (0 : ℝ) ≤ b.val from Nat.cast_nonneg _),
    abs_of_pos hq, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hratio : (b.val : ℝ) / q ≤ 1 := (div_le_one hq).mpr hb
  have hp : 0 ≤ 2 * Real.pi * |t| := by positivity
  calc
    _ = (2 * Real.pi * |t|) * ((b.val : ℝ) / q) := by ring
    _ ≤ _ := mul_le_of_le_one_right hp hratio

theorem cyclicPolynomial_integral_norm_le (R : Finset (ZMod q)) (a : ZMod q → ℂ) :
    (∫ j, ‖cyclicPolynomial q R a j‖ ∂cyclicMeasure q) ≤
      Real.sqrt (∑ r ∈ R, ‖a r‖ ^ 2) := by
  have hh := integral_cauchy_schwarz_sq (μ := cyclicMeasure q)
    (f := fun j => ‖cyclicPolynomial q R a j‖) (g := fun _ => (1 : ℝ))
    (cyclic_integrable q _) (cyclic_integrable q _) (cyclic_integrable q _)
  simp only [mul_one, one_pow, integral_const, probReal_univ, smul_eq_mul,
    integral_cyclicPolynomial_norm_sq] at hh
  exact (Real.le_sqrt (integral_nonneg fun _ => norm_nonneg _)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)).mpr hh

noncomputable def boundaryW (C : Finset (ZMod q × ℤ)) (t : ℝ) (s : Circle) : ℝ :=
  ∫ j, ‖cyclicPolynomial q Finset.univ
    (fun b => boundaryPhase q b t * boundaryVertical q C b s) j‖ ∂cyclicMeasure q

theorem boundaryW_zero (C : Finset (ZMod q × ℤ)) (s : Circle) :
    boundaryW q C 0 s = ∫ j, ‖boundaryPolynomial q C j s‖ ∂cyclicMeasure q := by
  simp [boundaryW, boundaryPhase, boundaryPolynomial_cyclic]

theorem integral_boundaryW_zero (C : Finset (ZMod q × ℤ)) :
    (∫ s, boundaryW q C 0 s ∂circleMeasure) = boundaryNorm q C := by
  simp_rw [boundaryW_zero]
  rw [← integral_prod (fun z : Circle × ZMod q => ‖boundaryPolynomial q C z.2 z.1‖)]
  · rfl
  · apply boundary_dual_integrable q
    simp_rw [boundaryPolynomial_eq_mixed]
    fun_prop

/-- Freezing the residue phases costs a cyclic `L²` norm, independently
of the modulus or the number of nonzero residues. -/
theorem boundary_freezing (C : Finset (ZMod q × ℤ)) (t : ℝ) (s : Circle) :
    |boundaryW q C t s - boundaryW q C 0 s| ≤
      2 * Real.pi * |t| * boundaryQ q C s := by
  let a : ZMod q → ℂ := fun b => boundaryPhase q b t * boundaryVertical q C b s
  let b : ZMod q → ℂ := fun b => boundaryVertical q C b s
  let d : ZMod q → ℂ := fun r => (boundaryPhase q r t - 1) * b r
  have hdiff (j : ZMod q) :
      cyclicPolynomial q Finset.univ a j - cyclicPolynomial q Finset.univ b j =
        cyclicPolynomial q Finset.univ d j := by
    simp only [cyclicPolynomial, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    dsimp [a, b, d]
    ring
  have hzero : boundaryW q C 0 s = ∫ j, ‖cyclicPolynomial q Finset.univ b j‖
      ∂cyclicMeasure q := by simp [boundaryW, boundaryPhase, b]
  rw [hzero]
  change |(∫ j, ‖cyclicPolynomial q Finset.univ a j‖ ∂cyclicMeasure q) - _| ≤ _
  rw [← integral_sub (cyclic_integrable q _) (cyclic_integrable q _)]
  calc
    _ ≤ ∫ j, |‖cyclicPolynomial q Finset.univ a j‖ -
        ‖cyclicPolynomial q Finset.univ b j‖| ∂cyclicMeasure q :=
      abs_integral_le_integral_abs
    _ ≤ ∫ j, ‖cyclicPolynomial q Finset.univ d j‖ ∂cyclicMeasure q := by
      apply integral_mono (cyclic_integrable q _) (cyclic_integrable q _)
      intro j
      dsimp only
      rw [← hdiff]
      exact abs_norm_sub_norm_le _ _
    _ ≤ Real.sqrt (∑ r : ZMod q, ‖d r‖ ^ 2) := cyclicPolynomial_integral_norm_le q _ _
    _ ≤ _ := by
      apply (Real.sqrt_le_left (mul_nonneg (by positivity) (boundaryQ_nonneg q C s))).mpr
      rw [mul_pow, boundaryQ, Real.sq_sqrt (Finset.sum_nonneg fun r _ => sq_nonneg _),
        Finset.mul_sum]
      apply Finset.sum_le_sum
      intro r _
      dsimp [d, b]
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (boundaryPhase_sub_one_le q r t) 2) (sq_nonneg _)

theorem boundaryW_nonneg (C : Finset (ZMod q × ℤ)) (t : ℝ) (s : Circle) :
    0 ≤ boundaryW q C t s := integral_nonneg fun _ => norm_nonneg _

theorem boundaryW_expansion (C : Finset (ZMod q × ℤ)) (t : ℝ) (s : Circle) (j : ZMod q) :
    cyclicPolynomial q Finset.univ
      (fun b => boundaryPhase q b t * boundaryVertical q C b s) j =
      ∑ p ∈ boundaryCarrier C, (boundaryValue C p : ℂ) *
        (boundaryPhase q p.1 t * cyclicCharacter q p.1 j * fourier p.2 s) := by
  unfold cyclicPolynomial boundaryVertical
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  ring

theorem q_smul_div_shift (t : ℝ) (j : ZMod q) :
    (q : ℤ) • (((t / q : ℝ) : Circle) + ZMod.toAddCircle j) = (t : Circle) := by
  rw [smul_add, q_smul_cyclicShift, add_zero, ← QuotientAddGroup.mk_zsmul]
  congr 1
  simp only [zsmul_eq_mul, Int.cast_natCast]
  exact mul_div_cancel₀ t (show (q : ℝ) ≠ 0 by exact_mod_cast NeZero.ne q)

theorem boundary_frequency_div_shift (M : ℕ) (p : ZMod q × ℤ) (t : ℝ) (j : ZMod q) :
    fourier ((p.1.val : ℤ) + (q : ℤ) * M * p.2)
      (((t / q : ℝ) : Circle) + ZMod.toAddCircle j) =
      boundaryPhase q p.1 t * cyclicCharacter q p.1 j *
        fourier p.2 (((M : ℝ) * t : ℝ) : Circle) := by
  rw [fourier_add, fourier_character_add, fourier_cyclicShift]
  rw [mul_assoc (q : ℤ) (M : ℤ) p.2, fourier_mul_index, q_smul_div_shift,
    fourier_mul_index]
  have he : (M : ℤ) • (t : Circle) = (((M : ℝ) * t : ℝ) : Circle) := by
    rw [← QuotientAddGroup.mk_zsmul]
    congr 1
    simp [zsmul_eq_mul]
  rw [he]
  rfl

theorem boundaryW_inflation_identity {M : ℕ} (hM : 0 < M)
    (C : Finset (ZMod q × ℤ)) (t : ℝ) :
    boundaryW q C t (((M : ℝ) * t : ℝ) : Circle) =
      ‖1 - fourier 1 (t : Circle)‖ *
        ∫ j, ‖fourierPolynomial (blockInflation q M C)
          (((t / q : ℝ) : Circle) + ZMod.toAddCircle j)‖ ∂cyclicMeasure q := by
  unfold boundaryW
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun j => by
    dsimp only
    rw [boundaryW_expansion]
    have hi := block_boundary_identity q hM C
      (((t / q : ℝ) : Circle) + ZMod.toAddCircle j)
    simp_rw [boundary_frequency_div_shift] at hi
    have he : fourier (q : ℤ) (((t / q : ℝ) : Circle) + ZMod.toAddCircle j) =
        fourier 1 (t : Circle) := by
      simpa only [mul_one] using
        (fourier_mul_index (q : ℤ) 1 (((t / q : ℝ) : Circle) + ZMod.toAddCircle j)).trans
          (congrArg (fun z : Circle => fourier 1 z) (q_smul_div_shift q t j))
    rw [he] at hi
    rw [← hi, norm_mul]

theorem norm_one_sub_fourier_one (t : ℝ) :
    ‖1 - fourier 1 (t : Circle)‖ = 2 * |Real.sin (Real.pi * t)| := by
  have he : fourier 1 (t : Circle) =
      Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)) := by
    simp only [fourier_coe_apply, Int.cast_one, Complex.ofReal_one, div_one, mul_one]
    congr 1
    push_cast
    ring
  rw [norm_sub_rev, he, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show 2 * Real.pi * t / 2 = Real.pi * t by ring]
  simp [Real.norm_eq_abs]

end LittlewoodInverse
