import LittlewoodInverse.LongBlockCover
import LittlewoodInverse.InitialPrefixes
import LittlewoodInverse.IntervalMoments
import LittlewoodInverse.IntervalEnergy

open scoped BigOperators
open MeasureTheory

namespace LittlewoodInverse

/-- Counting one of the two possible residue pairings and then choosing the
third entry proves the Sidon fibre energy estimate without analytic losses. -/
theorem sidon_fibre_energy_bound {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [DecidableEq G] [DecidableEq H] (φ : G →+ H) (Y : Finset G)
    (R : Finset H) (hR : AdditiveSidon R) (hYR : ∀ y ∈ Y, φ y ∈ R)
    (M : ℕ) (hfibre : ∀ r : H, (Y.filter (fun y => φ y = r)).card ≤ M) :
    additiveEnergy Y ≤ 2 * M * Y.card ^ 2 := by
  classical
  let Q := ((Y ×ˢ Y) ×ˢ (Y ×ˢ Y)).filter (fun x => x.1.1 + x.1.2 = x.2.1 + x.2.2)
  let T (p : G × G) :=
    ((Y.filter (fun y => φ y = φ p.1)) ∪ (Y.filter (fun y => φ y = φ p.2))).image
      (fun y => (p, y))
  have hmap : Set.MapsTo (fun x : (G × G) × (G × G) => (x.1, x.2.1))
      Q ((Y ×ˢ Y).biUnion T) := by
    intro x hx
    obtain ⟨hx, he⟩ := Finset.mem_filter.mp hx
    obtain ⟨hab, hcd⟩ := Finset.mem_product.mp hx
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    obtain ⟨hc, hd⟩ := Finset.mem_product.mp hcd
    have hr := hR _ (hYR _ ha) _ (hYR _ hb) _ (hYR _ hc) _ (hYR _ hd)
      (by simpa only [map_add] using congrArg φ he)
    apply Finset.mem_biUnion.mpr
    refine ⟨x.1, hab, Finset.mem_image.mpr ⟨x.2.1, ?_, rfl⟩⟩
    rcases hr with ⟨h, _⟩ | ⟨_, h⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hc, h.symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hc, h.symm⟩)
  have hinj : Set.InjOn (fun x : (G × G) × (G × G) => (x.1, x.2.1)) Q := by
    intro x hx y hy h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    dsimp only at h1 h2
    have hx := (Finset.mem_filter.mp hx).2
    have hy := (Finset.mem_filter.mp hy).2
    have h3 : x.2.2 = y.2.2 := by
      apply add_left_cancel (a := x.2.1)
      rw [← hx, h1, hy, h2]
    exact Prod.ext h1 (Prod.ext h2 h3)
  have hT (p : G × G) : (T p).card ≤ 2 * M := by
    calc
      _ ≤ ((Y.filter (fun y => φ y = φ p.1)) ∪
        (Y.filter (fun y => φ y = φ p.2))).card := Finset.card_image_le
      _ ≤ (Y.filter (fun y => φ y = φ p.1)).card +
        (Y.filter (fun y => φ y = φ p.2)).card := Finset.card_union_le _ _
      _ ≤ _ := by linarith [hfibre (φ p.1), hfibre (φ p.2)]
  calc
    additiveEnergy Y = Q.card := Finset.addEnergy_eq_card_filter Y Y
    _ ≤ ((Y ×ˢ Y).biUnion T).card := Finset.card_le_card_of_injOn _ hmap hinj
    _ ≤ ∑ p ∈ Y ×ˢ Y, (T p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ Y ×ˢ Y, 2 * M := Finset.sum_le_sum (fun p _ => hT p)
    _ = _ := by simp; ring

theorem ternary_power_strictMono : StrictMono (fun n : ℕ => (3 : ℕ) ^ n) := by
  intro a b hab
  exact pow_lt_pow_right₀ (by norm_num) hab

theorem ternary_sum_sorted {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d)
    (he : 3 ^ a + 3 ^ b = 3 ^ c + 3 ^ d) : a = c ∧ b = d := by
  have hbd : b = d := by
    rcases lt_trichotomy b d with h | h | h
    · have ha := ternary_power_strictMono.monotone hab
      have hd := ternary_power_strictMono.monotone (show b + 1 ≤ d by omega)
      rw [pow_succ] at hd
      have hp := pow_pos (by norm_num : 0 < (3 : ℕ)) b
      nlinarith [Nat.zero_le ((3 : ℕ) ^ c)]
    · exact h
    · have hc := ternary_power_strictMono.monotone hcd
      have hb := ternary_power_strictMono.monotone (show d + 1 ≤ b by omega)
      rw [pow_succ] at hb
      have hp := pow_pos (by norm_num : 0 < (3 : ℕ)) d
      nlinarith [Nat.zero_le ((3 : ℕ) ^ a)]
  subst d
  exact ⟨ternary_power_strictMono.injective (Nat.add_right_cancel he), rfl⟩

theorem ternary_powers_sidon (R : ℕ) :
    AdditiveSidon ((Finset.range R).image (fun n => (3 : ℕ) ^ n)) := by
  intro a ha b hb c hc d hd he
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hd
  by_cases hij : i ≤ j <;> by_cases hkl : k ≤ l
  · obtain ⟨rfl, rfl⟩ := ternary_sum_sorted hij hkl he
    exact Or.inl ⟨rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := ternary_sum_sorted hij (le_of_not_ge hkl) (by omega)
    exact Or.inr ⟨rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := ternary_sum_sorted (le_of_not_ge hij) hkl (by omega)
    exact Or.inr ⟨rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := ternary_sum_sorted (le_of_not_ge hij) (le_of_not_ge hkl) (by omega)
    exact Or.inl ⟨rfl, rfl⟩

def ternaryResidues (R : ℕ) : Finset (ZMod (3 ^ R)) :=
  (Finset.range R).image (fun n => ((3 ^ n : ℕ) : ZMod (3 ^ R)))

theorem ternary_pow_lt {i R : ℕ} (hi : i < R) : 3 ^ i < 3 ^ R :=
  ternary_power_strictMono hi

theorem ternary_pair_sum_lt {i j R : ℕ} (hi : i < R) (hj : j < R) :
    3 ^ i + 3 ^ j < 3 ^ R := by
  let m := max i j
  have hmi : 3 ^ i ≤ (3 : ℕ) ^ m := ternary_power_strictMono.monotone (le_max_left _ _)
  have hmj : 3 ^ j ≤ (3 : ℕ) ^ m := ternary_power_strictMono.monotone (le_max_right _ _)
  have hmr : m + 1 ≤ R := by dsimp [m]; omega
  have hp := ternary_power_strictMono.monotone hmr
  rw [pow_succ] at hp
  have hpos : 0 < (3 : ℕ) ^ m := by positivity
  nlinarith

theorem ternaryResidues_card (R : ℕ) : (ternaryResidues R).card = R := by
  rw [ternaryResidues, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj he
  apply ternary_power_strictMono.injective
  have hval := congrArg ZMod.val he
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (ternary_pow_lt (Finset.mem_range.mp hi)),
    Nat.mod_eq_of_lt (ternary_pow_lt (Finset.mem_range.mp hj))] using hval

theorem ternaryResidues_sidon (R : ℕ) : AdditiveSidon (ternaryResidues R) := by
  intro a ha b hb c hc d hd he
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hd
  have heval := congrArg ZMod.val he
  simp only [← Nat.cast_add, ZMod.val_natCast,
    Nat.mod_eq_of_lt (ternary_pair_sum_lt (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)),
    Nat.mod_eq_of_lt (ternary_pair_sum_lt (Finset.mem_range.mp hk) (Finset.mem_range.mp hl))] at heval
  have hsidon := ternary_powers_sidon R _ (Finset.mem_image_of_mem _ hi)
    _ (Finset.mem_image_of_mem _ hj) _ (Finset.mem_image_of_mem _ hk)
    _ (Finset.mem_image_of_mem _ hl) heval
  rcases hsidon with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨congrArg Nat.cast h1, congrArg Nat.cast h2⟩
  · exact Or.inr ⟨congrArg Nat.cast h1, congrArg Nat.cast h2⟩

theorem uniform_fibre_norm_upper (q : ℕ) [NeZero q] (R : Finset (ZMod q)) (I : Finset ℤ) :
    littlewoodNorm (fibreUnion q R (fun _ => I)) ≤ Real.sqrt (R.card : ℝ) * littlewoodNorm I := by
  have hpoint (t : Circle) :
      (∫ j, ‖fourierPolynomial (fibreUnion q R (fun _ => I))
        (t + ZMod.toAddCircle j)‖ ∂cyclicMeasure q) ≤
        Real.sqrt (R.card : ℝ) * ‖fourierPolynomial I ((q : ℤ) • t)‖ := by
    simp_rw [fibre_cyclic_expansion]
    have hs := cyclicPolynomial_integral_norm_le q R
      (fun r => fourier (r.val : ℤ) t * fourierPolynomial I ((q : ℤ) • t))
    have hn (r : ZMod q) :
        ‖fourier (r.val : ℤ) t * fourierPolynomial I ((q : ℤ) • t)‖ =
          ‖fourierPolynomial I ((q : ℤ) • t)‖ := by simp [fourier_apply]
    simp only [hn] at hs
    simpa only [Finset.sum_const, nsmul_eq_mul, Real.sqrt_mul (Nat.cast_nonneg _),
      Real.sqrt_sq_eq_abs, abs_norm] using hs
  rw [← cyclicTranslate_average_integral q]
  calc
    _ ≤ ∫ t, Real.sqrt (R.card : ℝ) * ‖fourierPolynomial I ((q : ℤ) • t)‖ ∂circleMeasure := by
      apply integral_mono
        (continuous_circle_integrable (cyclicTranslate_average_continuous q _))
        (continuous_circle_integrable (continuous_const.mul
          (((fourierPolynomial_continuous I).comp (continuous_zsmul (q : ℤ))).norm))) hpoint
    _ = _ := by
      rw [integral_const_mul, circle_integral_zsmul q _ (fourierPolynomial_continuous I).norm]
      rfl

noncomputable def interlacedSet (R M : ℕ) : Finset ℤ :=
  fibreUnion (3 ^ R) (ternaryResidues R) (fun _ => IntervalMoments.integerInterval M)

theorem uniform_fibre_card (q : ℕ) [NeZero q] (R : Finset (ZMod q)) (I : Finset ℤ) :
    (fibreUnion q R (fun _ => I)).card = R.card * I.card := by
  classical
  rw [fibreUnion, Finset.card_biUnion]
  · simp [affine_card _ _ _ (show (q : ℤ) ≠ 0 by exact_mod_cast NeZero.ne q)]
  · intro r hr s hs hrs
    exact fibre_disjoint q (fun _ => I) hrs

theorem interlacedSet_card (R M : ℕ) : (interlacedSet R M).card = R * M := by
  rw [interlacedSet, uniform_fibre_card, ternaryResidues_card]
  simp [IntervalMoments.integerInterval]

theorem integerInterval_card (M : ℕ) : (IntervalMoments.integerInterval M).card = M := by
  simp [IntervalMoments.integerInterval]

theorem interlacedSet_norm (R M : ℕ) :
    littlewoodNorm (interlacedSet R M) ≤ Real.sqrt (R : ℝ) * littlewoodNorm (IntervalMoments.integerInterval M) := by
  simpa only [interlacedSet, ternaryResidues_card] using
    uniform_fibre_norm_upper (3 ^ R) (ternaryResidues R) (IntervalMoments.integerInterval M)

theorem uniform_fibre_energy (q : ℕ) [NeZero q] (R : Finset (ZMod q))
    (hR : AdditiveSidon R) (I : Finset ℤ) {Y : Finset ℤ}
    (hY : Y ⊆ fibreUnion q R (fun _ => I)) :
    additiveEnergy Y ≤ 2 * I.card * Y.card ^ 2 := by
  let φ : ℤ →+ ZMod q := Int.castAddHom (ZMod q)
  have hdecomp {y : ℤ} (hy : y ∈ Y) :
      ∃ r ∈ R, ∃ u ∈ I, y = (r.val : ℤ) + (q : ℤ) * u := by
    obtain ⟨r, hr, hu⟩ := Finset.mem_biUnion.mp (hY hy)
    obtain ⟨u, hu, h⟩ := Finset.mem_image.mp hu
    exact ⟨r, hr, u, hu, h.symm⟩
  apply sidon_fibre_energy_bound φ Y R hR
  · intro y hy
    obtain ⟨r, hr, u, hu, rfl⟩ := hdecomp hy
    simpa [φ] using hr
  · intro r
    have hsub : Y.filter (fun y => φ y = r) ⊆ affineImage (r.val : ℤ) q I := by
      intro y hy
      obtain ⟨hy, hr⟩ := Finset.mem_filter.mp hy
      obtain ⟨s, hs, u, hu, rfl⟩ := hdecomp hy
      have hsr : s = r := by simpa [φ] using hr
      subst s
      exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
    exact (Finset.card_le_card hsub).trans_eq
      (affine_card I _ _ (by exact_mod_cast NeZero.ne q))

theorem interlacedSet_energy (R M : ℕ) {Y : Finset ℤ} (hY : Y ⊆ interlacedSet R M) :
    additiveEnergy Y ≤ 2 * M * Y.card ^ 2 := by
  have h := uniform_fibre_energy (3 ^ R) (ternaryResidues R) (ternaryResidues_sidon R)
    (IntervalMoments.integerInterval M) hY
  simpa [IntervalMoments.integerInterval] using h

theorem interval_as_blockInflation (M : ℕ) :
    blockInflation 1 M {(0, 0)} = IntervalMoments.integerInterval M := by
  ext z
  simp only [blockInflation, Finset.singleton_biUnion, ZMod.val_zero,
    Nat.cast_zero, Nat.cast_one, mul_zero, zero_add, one_mul,
    IntervalMoments.integerInterval, Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨by positivity, by exact_mod_cast hr⟩
  · rintro ⟨h0, hM⟩
    exact ⟨z.toNat, by exact_mod_cast (show (z.toNat : ℤ) < M by
      rw [Int.toNat_of_nonneg h0]; exact hM), Int.toNat_of_nonneg h0⟩

theorem interval_terminal (β Δ : ℝ) {M : ℕ} (hM : 0 < M) :
    Terminal β Δ (IntervalMoments.integerInterval M) := by
  have ht := Terminal.inflation (β := β) (Δ := Δ) 1 M (by norm_num) hM
    ({(0, 0)} : Finset (ZMod 1 × ℤ)) (Finset.singleton_nonempty _) (by simpa using (show 1 ≤ M by omega))
    0 1 (by norm_num)
  simpa [affineImage, interval_as_blockInflation] using ht

theorem interlacedSet_assembly (β Δ : ℝ) {R M : ℕ} (hR : 0 < R) (hM : 0 < M) :
    Assembly β Δ (interlacedSet R M) := by
  have hq : 2 ≤ 3 ^ R := by
    have hh := ternary_power_strictMono.monotone (show 1 ≤ R from hR)
    norm_num at hh
    omega
  apply Assembly.node (3 ^ R) hq (ternaryResidues R)
    (Finset.card_pos.mp (by rw [ternaryResidues_card]; exact hR)) (ternaryResidues_sidon R)
    (fun _ => IntervalMoments.integerInterval M)
  · intro _ _
    exact Assembly.terminal (interval_terminal β Δ hM)
  · intro _ _
    refine ⟨0, Finset.mem_Ico.mpr ⟨le_rfl, ?_⟩⟩
    exact_mod_cast hM

theorem uniform_fibre_prefix_layers (q : ℕ) [NeZero q] (R : Finset (ZMod q))
    (hR : R.Nonempty) (M : ℕ) {P : Finset ℤ}
    (hP : IsInitialSegment P (fibreUnion q R (fun _ => IntervalMoments.integerInterval M))) :
    P ⊆ fibreUnion q R (fun _ => IntervalMoments.integerInterval (P.card / R.card + 1)) := by
  intro y hy
  obtain ⟨r, hr, hu⟩ := Finset.mem_biUnion.mp (hP.1 hy)
  obtain ⟨u, hu, huy⟩ := Finset.mem_image.mp hu
  obtain ⟨hu0, huM⟩ := Finset.mem_Ico.mp hu
  have hucast : (u.toNat : ℤ) = u := Int.toNat_of_nonneg hu0
  have hlow : fibreUnion q R (fun _ => IntervalMoments.integerInterval u.toNat) ⊆ P := by
    intro z hz
    obtain ⟨s, hs, hv⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨v, hv, hvz⟩ := Finset.mem_image.mp hv
    obtain ⟨hv0, hvu⟩ := Finset.mem_Ico.mp hv
    rw [hucast] at hvu
    apply hP.2 z ?_ y hy ?_
    · apply Finset.mem_biUnion.mpr
      refine ⟨s, hs, Finset.mem_image.mpr ⟨v, ?_, hvz⟩⟩
      exact Finset.mem_Ico.mpr ⟨hv0, hvu.trans huM⟩
    · have hq : (0 : ℤ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
      have hsv : (s.val : ℤ) < q := by exact_mod_cast ZMod.val_lt s
      have hrv : (0 : ℤ) ≤ r.val := by positivity
      rw [← hvz, ← huy]
      have hvu' : v + 1 ≤ u := by omega
      have hh := mul_le_mul_of_nonneg_left hvu' hq.le
      nlinarith
  have hcard : R.card * u.toNat ≤ P.card := by
    have h := Finset.card_le_card hlow
    rw [uniform_fibre_card] at h
    simpa only [integerInterval_card] using h
  have hlevel : u.toNat ≤ P.card / R.card :=
    (Nat.le_div_iff_mul_le hR.card_pos).mpr (by nlinarith)
  apply Finset.mem_biUnion.mpr
  refine ⟨r, hr, Finset.mem_image.mpr ⟨u, ?_, huy⟩⟩
  apply Finset.mem_Ico.mpr
  refine ⟨hu0, ?_⟩
  have hh : (u.toNat : ℤ) ≤ (P.card / R.card : ℕ) := by exact_mod_cast hlevel
  rw [hucast] at hh
  push_cast
  omega

/-- The layer argument in fact gives the stronger constant 4 for initial
segments, while the manuscript only needs 16. -/
theorem uniform_fibre_prefix_energy (q : ℕ) [NeZero q] (R : Finset (ZMod q))
    (hR : R.Nonempty) (hSidon : AdditiveSidon R) (M : ℕ) {P : Finset ℤ}
    (hP : IsInitialSegment P (fibreUnion q R (fun _ => IntervalMoments.integerInterval M)))
    (hn : R.card ≤ P.card) : R.card * additiveEnergy P ≤ 4 * P.card ^ 3 := by
  have hsub := uniform_fibre_prefix_layers q R hR M hP
  have he := uniform_fibre_energy q R hSidon
    (IntervalMoments.integerInterval (P.card / R.card + 1)) hsub
  have he' : additiveEnergy P ≤ 2 * (P.card / R.card + 1) * P.card ^ 2 := by
    simpa only [integerInterval_card] using he
  have hl : R.card * (P.card / R.card + 1) ≤ 2 * P.card := by
    have hh := Nat.mul_div_le P.card R.card
    nlinarith
  have hmul := Nat.mul_le_mul_left R.card he'
  have hmul' := Nat.mul_le_mul_right (2 * P.card ^ 2) hl
  nlinarith

theorem interlacedSet_prefix_energy {R M : ℕ} (hR : 0 < R) {P : Finset ℤ}
    (hP : IsInitialSegment P (interlacedSet R M)) (hn : R ≤ P.card) :
    (additiveEnergy P : ℝ) ≤ 16 * (P.card : ℝ) ^ 3 / R := by
  have hRn : (ternaryResidues R).Nonempty :=
    Finset.card_pos.mp (by rw [ternaryResidues_card]; exact hR)
  have he := uniform_fibre_prefix_energy (3 ^ R) (ternaryResidues R) hRn
    (ternaryResidues_sidon R) M hP (by simpa only [ternaryResidues_card] using hn)
  rw [ternaryResidues_card] at he
  apply (le_div_iff₀ (by exact_mod_cast hR : (0 : ℝ) < R)).mpr
  have heR : (R : ℝ) * additiveEnergy P ≤ 4 * (P.card : ℝ) ^ 3 := by exact_mod_cast he
  nlinarith [pow_nonneg (Nat.cast_nonneg P.card : (0 : ℝ) ≤ P.card) 3]

/-- Proposition 10.1, including its explicit construction, every-subset
energy bound, initial-segment obstruction, and actual assembly certificate. -/
theorem sidon_fibres {R M : ℕ} (hR : 0 < R) (hM : 0 < M) :
    ∃ A : Finset ℤ, A.card = R * M ∧
      littlewoodNorm A ≤ Real.sqrt (R : ℝ) * littlewoodNorm (IntervalMoments.integerInterval M) ∧
      (∀ Y ⊆ A, additiveEnergy Y ≤ 2 * M * Y.card ^ 2) ∧
      (∀ P : Finset ℤ, IsInitialSegment P A → R ≤ P.card →
        (additiveEnergy P : ℝ) ≤ 16 * (P.card : ℝ) ^ 3 / R) ∧
      (∀ β Δ : ℝ, Assembly β Δ A) :=
  ⟨interlacedSet R M, interlacedSet_card R M, interlacedSet_norm R M,
    fun _ hY => interlacedSet_energy R M hY,
    fun _ hP hn => interlacedSet_prefix_energy hR hP hn,
    fun β Δ => interlacedSet_assembly β Δ hR hM⟩

/-- Each individual arithmetic-progression fibre is an actual subset of
the example, with exactly the cardinality and energy stated in Section 10. -/
theorem interlacedSet_individual_fibre (R M : ℕ) {r : ZMod (3 ^ R)}
    (hr : r ∈ ternaryResidues R) :
    let B := affineImage (r.val : ℤ) (3 ^ R) (IntervalMoments.integerInterval M)
    B ⊆ interlacedSet R M ∧ B.card = M ∧
      (additiveEnergy B : ℝ) = (2 * (M : ℝ) ^ 3 + M) / 3 := by
  dsimp only
  have hv : (3 : ℤ) ^ R ≠ 0 := pow_ne_zero _ (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · change affineImage (r.val : ℤ) ((3 ^ R : ℕ) : ℤ)
        (IntervalMoments.integerInterval M) ⊆ _
    exact Finset.subset_biUnion_of_mem
      (fun s => affineImage (s.val : ℤ) ((3 ^ R : ℕ) : ℤ)
        (IntervalMoments.integerInterval M)) hr
  · rw [affine_card _ _ _ hv, integerInterval_card]
  · rw [affine_energy _ _ _ hv]
    exact IntervalEnergy.interval_energy_real M

end LittlewoodInverse
