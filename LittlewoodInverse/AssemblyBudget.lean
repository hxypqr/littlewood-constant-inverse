import LittlewoodInverse.FibreBudget
import LittlewoodInverse.NormBounds
import LittlewoodInverse.MPSConsequences

open scoped BigOperators Pointwise

namespace LittlewoodInverse

theorem affineImage_comp (A : Finset ℤ) (u v w z : ℤ) :
    affineImage u v (affineImage w z A) = affineImage (u + v * w) (v * z) A := by
  unfold affineImage
  rw [Finset.image_image]
  congr 1
  funext x
  simp only [Function.comp_apply]
  ring

theorem terminal_affine {β Δ : ℝ} {A : Finset ℤ} (h : Terminal β Δ A)
    (u v : ℤ) (hv : v ≠ 0) : Terminal β Δ (affineImage u v A) := by
  cases h with
  | singleton a =>
      simpa [affineImage] using (Terminal.singleton (β := β) (Δ := Δ) (u + v * a))
  | dense data w z hz =>
      rw [affineImage_comp]
      exact Terminal.dense data _ _ (mul_ne_zero hv hz)
  | inflation q M hq hM C hC hlong w z hz =>
      rw [affineImage_comp]
      exact Terminal.inflation q M hq hM C hC hlong _ _ (mul_ne_zero hv hz)

theorem terminal_nonempty {β Δ : ℝ} {A : Finset ℤ} (h : Terminal β Δ A) : A.Nonempty := by
  cases h with
  | singleton a => simp
  | dense data u v hv => exact affine_nonempty data.nonempty u v
  | inflation q M hq hM C hC hlong u v hv =>
      apply affine_nonempty
      obtain ⟨bu, hbu⟩ := hC
      apply Finset.biUnion_nonempty.mpr
      refine ⟨bu, hbu, ?_⟩
      exact (show (Finset.range M).Nonempty from ⟨0, Finset.mem_range.mpr hM⟩).image _

/-- Actual terminal leaves embedded into the root integer set. The
index type records all leaves, while disjointness rules out duplicate sets. -/
structure AssemblyLeafFamily (β Δ : ℝ) (A : Finset ℤ) where
  Index : Type
  [indexFintype : Fintype Index]
  leaf : Index → Finset ℤ
  terminal : ∀ i, Terminal β Δ (leaf i)
  disjoint : Pairwise (fun i j => Disjoint (leaf i) (leaf j))
  covers : ∀ x, x ∈ A ↔ ∃ i, x ∈ leaf i
  budget : (∑ i, littlewoodNorm (leaf i) ^ 20) ≤ littlewoodNorm A ^ 20

attribute [instance] AssemblyLeafFamily.indexFintype

namespace AssemblyLeafFamily

variable {β Δ : ℝ} {A : Finset ℤ}

theorem leaf_subset (L : AssemblyLeafFamily β Δ A) (i : L.Index) : L.leaf i ⊆ A := by
  intro x hx
  exact (L.covers x).2 ⟨i, hx⟩

theorem leaf_nonempty (L : AssemblyLeafFamily β Δ A) (i : L.Index) : (L.leaf i).Nonempty :=
  terminal_nonempty (L.terminal i)

noncomputable def ofTerminal (h : Terminal β Δ A) : AssemblyLeafFamily β Δ A where
  Index := PUnit
  leaf := fun _ => A
  terminal := fun _ => h
  disjoint := by intro i j hij; exact (hij (Subsingleton.elim _ _)).elim
  covers := by intro x; simp
  budget := by simp

noncomputable def affine (L : AssemblyLeafFamily β Δ A) (u v : ℤ) (hv : v ≠ 0) :
    AssemblyLeafFamily β Δ (affineImage u v A) where
  Index := L.Index
  leaf := fun i => affineImage u v (L.leaf i)
  terminal := fun i => terminal_affine (L.terminal i) u v hv
  disjoint := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hi hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨b, hb, he⟩ := Finset.mem_image.mp hj
    have heq : b = a := affine_injective u v hv he
    subst b
    exact Finset.disjoint_left.mp (L.disjoint hij) ha hb
  covers := by
    intro x
    constructor
    · rintro hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨i, hi⟩ := (L.covers a).1 ha
      exact ⟨i, Finset.mem_image.mpr ⟨a, hi, rfl⟩⟩
    · rintro ⟨i, hi⟩
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_image.mpr ⟨a, (L.covers a).2 ⟨i, ha⟩, rfl⟩
  budget := by
    simpa only [affineImage, littlewoodNorm_affine _ _ hv] using L.budget

noncomputable def node (q : ℕ) [NeZero q] (R : Finset (ZMod q))
    (hR : AdditiveSidon R) (child : ZMod q → Finset ℤ)
    (L : ∀ r : R, AssemblyLeafFamily β Δ (child r)) :
    AssemblyLeafFamily β Δ (fibreUnion q R child) where
  Index := Σ r : R, (L r).Index
  leaf := fun i => affineImage (i.1.val.val : ℤ) q ((L i.1).leaf i.2)
  terminal := fun i => terminal_affine ((L i.1).terminal i.2) _ _
    (by exact_mod_cast (NeZero.ne q))
  disjoint := by
    rintro ⟨r, i⟩ ⟨s, j⟩ hne
    by_cases hrs : r = s
    · subst s
      have hij : i ≠ j := by intro h; subst j; exact hne rfl
      exact ((L r).affine (r.val.val : ℤ) q (by exact_mod_cast (NeZero.ne q))).disjoint hij
    · apply Finset.disjoint_of_subset_left
        (Finset.image_subset_image ((L r).leaf_subset i))
      apply Finset.disjoint_of_subset_right
        (Finset.image_subset_image ((L s).leaf_subset j))
      exact fibre_disjoint q child (fun h => hrs (Subtype.ext h))
  covers := by
    intro x
    constructor
    · intro hx
      obtain ⟨r, hr, hx⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨i, hi⟩ := ((L ⟨r, hr⟩).covers a).1 ha
      exact ⟨⟨⟨r, hr⟩, i⟩, Finset.mem_image.mpr ⟨a, hi, rfl⟩⟩
    · rintro ⟨⟨r, i⟩, hx⟩
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      apply Finset.mem_biUnion.mpr
      exact ⟨r.val, r.property, Finset.mem_image.mpr
        ⟨a, ((L r).covers a).2 ⟨i, ha⟩, rfl⟩⟩
  budget := by
    simp only [Fintype.sum_sigma]
    simp only [affineImage, littlewoodNorm_affine _ _ (show (q : ℤ) ≠ 0 by exact_mod_cast (NeZero.ne q))]
    have hsum := Finset.sum_le_sum (fun r (_ : r ∈ (Finset.univ : Finset R)) => (L r).budget)
    have hroot := actual_fibre_twentieth_budget q R hR child
    have heq : (∑ r : R, littlewoodNorm (child r) ^ 20) =
        ∑ r ∈ R, littlewoodNorm (child r) ^ 20 :=
      Finset.sum_coe_sort R (fun r : ZMod q => littlewoodNorm (child r) ^ 20)
    exact hsum.trans (heq ▸ hroot)

/-- The leaf images partition the root, so their actual cardinalities add
to the cardinality of the original integer set. -/
theorem sum_card (L : AssemblyLeafFamily β Δ A) : (∑ i, (L.leaf i).card) = A.card := by
  classical
  have hcover : Finset.univ.biUnion L.leaf = A := by
    ext x
    simpa using (L.covers x).symm
  calc
    _ = (Finset.univ.biUnion L.leaf).card := by
      rw [Finset.card_biUnion]
      intro i hi j hj hij
      exact L.disjoint hij
    _ = _ := congrArg Finset.card hcover

/-- Each leaf uses part of the root norm budget. -/
theorem leaf_norm_le (L : AssemblyLeafFamily β Δ A) (i : L.Index) :
    littlewoodNorm (L.leaf i) ≤ littlewoodNorm A := by
  have hp : littlewoodNorm (L.leaf i) ^ 20 ≤ littlewoodNorm A ^ 20 :=
    (Finset.single_le_sum (fun j _ => pow_nonneg (littlewoodNorm_nonneg _) 20)
      (Finset.mem_univ i)).trans L.budget
  exact (pow_le_pow_iff_left₀ (littlewoodNorm_nonneg _) (littlewoodNorm_nonneg _)
    (by norm_num : (20 : ℕ) ≠ 0)).mp hp

/-- The number of actual leaves is bounded independently of tree depth. -/
theorem leaf_count_le (L : AssemblyLeafFamily β Δ A) :
    (Fintype.card L.Index : ℝ) ≤ littlewoodNorm A ^ 20 := by
  calc
    _ = ∑ _ : L.Index, (1 : ℝ) := by simp
    _ ≤ ∑ i, littlewoodNorm (L.leaf i) ^ 20 := by
      apply Finset.sum_le_sum
      intro i _
      exact one_le_pow₀ (one_le_littlewoodNorm (L.leaf_nonempty i))
    _ ≤ _ := L.budget

/-- A threshold lower bound for a subfamily's norms bounds its cardinality. -/
theorem threshold_count_mul_pow_le (L : AssemblyLeafFamily β Δ A)
    (s : Finset L.Index) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ i ∈ s, b ≤ littlewoodNorm (L.leaf i)) :
    (s.card : ℝ) * b ^ 20 ≤ littlewoodNorm A ^ 20 := by
  calc
    _ = ∑ _i ∈ s, b ^ 20 := by simp
    _ ≤ ∑ i ∈ s, littlewoodNorm (L.leaf i) ^ 20 := by
      exact Finset.sum_le_sum fun i hi => pow_le_pow_left₀ hb (h i hi) 20
    _ ≤ ∑ i, littlewoodNorm (L.leaf i) ^ 20 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
        intro i _ _
        exact pow_nonneg (littlewoodNorm_nonneg _) 20)
    _ ≤ _ := L.budget

/-- Total actual mass of leaves smaller than a real threshold. -/
theorem small_leaf_mass_le (L : AssemblyLeafFamily β Δ A)
    (s : Finset L.Index) {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ i ∈ s, ((L.leaf i).card : ℝ) ≤ a) :
    (∑ i ∈ s, ((L.leaf i).card : ℝ)) ≤ a * littlewoodNorm A ^ 20 := by
  calc
    _ ≤ ∑ _i ∈ s, a := Finset.sum_le_sum h
    _ = a * s.card := by simp [mul_comm]
    _ ≤ a * Fintype.card L.Index := mul_le_mul_of_nonneg_left
      (by exact_mod_cast (Finset.card_le_univ s)) ha
    _ ≤ _ := mul_le_mul_of_nonneg_left L.leaf_count_le ha

/-- The MPS lower bound gives a uniform number of polynomially large leaves. -/
theorem large_leaf_count_le (L : AssemblyLeafFamily β Δ A)
    {K θ : ℝ} (hθ : 0 < θ) (hN : 1 < (A.card : ℝ))
    (hnorm : littlewoodNorm A ≤ K * Real.log (A.card : ℝ))
    (s : Finset L.Index)
    (hs : ∀ i ∈ s, (A.card : ℝ) ^ θ ≤ ((L.leaf i).card : ℝ)) :
    (s.card : ℝ) ≤ (K / (mpsConstant * θ)) ^ 20 := by
  have hN0 : 0 < (A.card : ℝ) := lt_trans zero_lt_one hN
  have hlog : 0 < Real.log (A.card : ℝ) := Real.log_pos hN
  have hb : 0 < mpsConstant * θ * Real.log (A.card : ℝ) := by
    exact mul_pos (mul_pos mpsConstant_pos hθ) hlog
  have hbound := L.threshold_count_mul_pow_le s hb.le (fun i hi => by
    have hi' : (A.card : ℝ) ^ θ ≤ ((L.leaf i).card : ℝ) + 1 :=
      (hs i hi).trans (by linarith)
    have hlogi := Real.log_le_log (Real.rpow_pos_of_pos hN0 θ) hi'
    rw [Real.log_rpow hN0] at hlogi
    have hm : mpsConstant * θ * Real.log (A.card : ℝ) ≤
        mpsConstant * Real.log (((L.leaf i).card : ℝ) + 1) := by
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left hlogi mpsConstant_pos.le)
    exact hm.trans (mpsConstant_log_le (L.leaf i)))
  calc
    (s.card : ℝ) ≤ littlewoodNorm A ^ 20 /
        (mpsConstant * θ * Real.log (A.card : ℝ)) ^ 20 :=
      (le_div_iff₀ (pow_pos hb 20)).mpr hbound
    _ ≤ (K * Real.log (A.card : ℝ)) ^ 20 /
        (mpsConstant * θ * Real.log (A.card : ℝ)) ^ 20 :=
      div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (littlewoodNorm_nonneg _) hnorm 20) (pow_pos hb 20).le
    _ = (K / (mpsConstant * θ)) ^ 20 := by
      rw [← div_pow]
      congr 1
      exact mul_div_mul_right K (mpsConstant * θ) hlog.ne'

/-- The finite small-leaf estimate with the manuscript's norm hypothesis. -/
theorem small_leaf_mass_log_bound (L : AssemblyLeafFamily β Δ A)
    {K θ : ℝ} (hnorm : littlewoodNorm A ≤ K * Real.log (A.card : ℝ))
    (s : Finset L.Index)
    (hs : ∀ i ∈ s, ((L.leaf i).card : ℝ) < (A.card : ℝ) ^ θ) :
    (∑ i ∈ s, ((L.leaf i).card : ℝ)) ≤
      (A.card : ℝ) ^ θ * (K * Real.log (A.card : ℝ)) ^ 20 := by
  have hp : 0 ≤ (A.card : ℝ) ^ θ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  exact (L.small_leaf_mass_le s hp (fun i hi => (hs i hi).le)).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (littlewoodNorm_nonneg _) hnorm 20) hp)

end AssemblyLeafFamily

/-- Every concrete assembly admits an actual disjoint family of terminal
leaves with the depth-independent norm budget. -/
theorem assembly_has_terminal_leaves {β Δ : ℝ} {A : Finset ℤ} (hA : Assembly β Δ A) :
    Nonempty (AssemblyLeafFamily β Δ A) := by
  induction hA with
  | terminal h => exact ⟨AssemblyLeafFamily.ofTerminal h⟩
  | affine h u v hv ih => exact ⟨(Classical.choice ih).affine u v hv⟩
  | node q hq R hR hSidon child hchild hne ih =>
      haveI : NeZero q := ⟨by omega⟩
      let L : ∀ r : R, AssemblyLeafFamily β Δ (child r) :=
        fun r => Classical.choice (ih r.val r.property)
      exact ⟨AssemblyLeafFamily.node q R hSidon child L⟩

open Filter Asymptotics

/-- The small-leaf mass envelope is negligible compared with the root size. -/
theorem small_leaf_envelope_isLittleO (K : ℝ) {θ : ℝ} (hθ : θ < 1) :
    (fun N : ℝ => N ^ θ * (K * Real.log N) ^ 20) =o[atTop] (fun N => N) := by
  have hlog : (fun x : ℝ => Real.log x ^ 20) =o[atTop]
      (fun x => x ^ (1 - θ)) := by
    have heq : (fun x : ℝ => Real.log x ^ (20 : ℝ)) =
        (fun x : ℝ => Real.log x ^ (20 : ℕ)) := by
      funext x
      exact Real.rpow_natCast (Real.log x) 20
    rw [← heq]
    exact isLittleO_log_rpow_rpow_atTop (20 : ℝ) (sub_pos.mpr hθ)
  have hmul := (isBigO_refl (fun x : ℝ => x ^ θ) atTop).mul_isLittleO
    (hlog.const_mul_left (K ^ 20))
  apply hmul.congr'
  · exact Eventually.of_forall (fun x => by simp only [mul_pow])
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [← Real.rpow_add hx, add_sub_cancel, Real.rpow_one]

/-- A uniform size threshold for the exceptional mass in Proposition 8.2. -/
theorem eventually_small_leaf_envelope (K : ℝ) {θ ε : ℝ}
    (hθ : θ < 1) (hε : 0 < ε) :
    ∀ᶠ N : ℝ in atTop, N ^ θ * (K * Real.log N) ^ 20 ≤ ε * N := by
  filter_upwards [(small_leaf_envelope_isLittleO K hθ).bound hε,
    eventually_ge_atTop (0 : ℝ)] with N hN hpos
  have habs : |N ^ θ * (K * Real.log N) ^ 20| ≤ ε * N := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hpos] using hN
  exact (le_abs_self _).trans habs

end LittlewoodInverse
