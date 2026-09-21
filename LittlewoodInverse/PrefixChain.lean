import LittlewoodInverse.DampedTest
import LittlewoodInverse.InitialPrefixes
import LittlewoodInverse.UniformTailBudget

open scoped BigOperators
open MeasureTheory

namespace LittlewoodInverse

theorem dampingTail_eq_reindexed {n : ℕ} (M : Fin n → Circle → ℂ)
    (i : Fin n) (t : Circle) : dampingTail M i t =
      ∏ r : Fin (n - (i.val + 1)), M ⟨i.val + 1 + r.val, by omega⟩ t := by
  classical
  symm
  apply Finset.prod_bij (fun r _ => (⟨i.val + 1 + r.val, by omega⟩ : Fin n))
  · intro r _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
    omega
  · intro r _ s _ h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp only at this
    omega
  · intro j hj
    have hlt : i.val < j.val := (Finset.mem_filter.mp hj).2
    refine ⟨⟨j.val - (i.val + 1), by omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    dsimp only
    omega
  · intros; rfl

theorem initial_segment_pairing_uniform {A B : Finset ℤ}
    (hB : IsInitialSegment B A) (hBn : B.Nonempty) {P : Circle → ℂ}
    (hP : MemLp P 2 circleMeasure) (hs : NonpositiveFourierSupport P)
    {η E : ℝ} (hη : 0 ≤ η) (hE : 0 ≤ E + η)
    (hsize : 1 ≤ η * (B.card : ℝ))
    (htail : (B.card : ℝ) * (∫ t, ‖P t - 1‖^2 ∂circleMeasure) ≤ E + η) :
    1 - Real.sqrt ((1 / 3 + η) * (E + η)) ≤
      (circlePairing (fourierPolynomial A)
        (fun t => (fourierPolynomial B t / (B.card : ℂ)) * P t)).re := by
  let N : ℝ := B.card
  let I : ℝ := ∫ t, ‖P t - 1‖^2 ∂circleMeasure
  have hN : 1 ≤ N := by
    change (1 : ℝ) ≤ (B.card : ℝ)
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hBn.card_pos.ne')
  have hN0 : 0 < N := by linarith
  have hI : 0 ≤ I := integral_nonneg fun _ => sq_nonneg _
  have hfac : ((additiveEnergy B : ℝ) + N^2) / (2*N^2) ≤ N * (1/3+η) := by
    apply (div_le_iff₀ (by positivity : 0 < 2*N^2)).mpr
    have he := IntervalEnergy.energy_max_real B
    change (additiveEnergy B : ℝ) ≤ (2*N^3+N)/3 at he
    have hsq : N ≤ N^2 := by nlinarith
    have hηN : N^2 ≤ η*N^3 := by
      have hh := mul_le_mul_of_nonneg_right hsize (sq_nonneg N)
      dsimp only [N] at *
      nlinarith
    nlinarith
  have hz := initial_segment_pairing_error hB hBn hP hs
  have hfac0 : 0 ≤ ((additiveEnergy B : ℝ) + N^2) / (2*N^2) := by positivity
  have herr : ‖circlePairing (fourierPolynomial A)
      (fun t => (fourierPolynomial B t / (B.card : ℂ)) * P t) - 1‖ ≤
        Real.sqrt ((1 / 3 + η) * (E + η)) := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (mul_nonneg (by linarith) hE)]
    calc
      _ ≤ (Real.sqrt (((additiveEnergy B : ℝ) + N^2) / (2*N^2)) * Real.sqrt I)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) hz 2
      _ = (((additiveEnergy B : ℝ) + N^2) / (2*N^2)) * I := by
        rw [mul_pow, Real.sq_sqrt hfac0, Real.sq_sqrt hI]
      _ ≤ (N * (1/3+η)) * I := mul_le_mul_of_nonneg_right hfac hI
      _ = (1/3+η) * (N*I) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left htail (by linarith)
  have hre := Complex.re_le_norm (-(circlePairing (fourierPolynomial A)
    (fun t => (fourierPolynomial B t / (B.card : ℂ)) * P t) - 1))
  simp only [Complex.neg_re, norm_neg, Complex.sub_re, Complex.one_re] at hre
  linarith

/-- The quantitative test at any finite number of geometric prefix scales. -/
theorem geometric_prefix_lower_bound (η : ℝ) (hη : 0 < η) :
    ∃ base : ℕ, 0 < base ∧ ∀ (J : ℕ) (A : Finset ℤ),
      base * 9^J ≤ A.card →
      (9/10 : ℝ) * J * (1 - Real.sqrt ((1/3+η)*(tailError+η))) ≤ littlewoodNorm A := by
  classical
  obtain ⟨N, hNpos, hN⟩ := uniform_outer_tail_budget η hη
  obtain ⟨b, hb⟩ := exists_nat_gt (1/η)
  let base := max N b
  have hbpos : 0 < base := lt_of_lt_of_le hNpos (le_max_left _ _)
  have hbη : 1 ≤ η * (base : ℝ) := by
    have hcast : (b : ℝ) ≤ base := by exact_mod_cast le_max_right N b
    have hh := (div_lt_iff₀ hη).mp hb
    nlinarith
  refine ⟨base, hbpos, ?_⟩
  intro J A hAJ
  have hle (i : Fin J) : base * 9^i.val ≤ A.card :=
    (Nat.mul_le_mul_left base (Nat.pow_le_pow_right (by norm_num) i.isLt.le)).trans hAJ
  let B : Fin J → Finset ℤ := fun i => initialPrefix A (base * 9^i.val) (hle i)
  have hcard (i : Fin J) : (B i).card = base * 9^i.val := initialPrefix_card _ _ _
  have hbase (i : Fin J) : base ≤ (B i).card := by
    rw [hcard]
    exact Nat.le_mul_of_pos_right _ (by positivity)
  have hne (i : Fin J) : (B i).Nonempty := Finset.card_pos.mp (hbpos.trans_le (hbase i))
  let M : ∀ i, DampingData (9/10) (B i) := fun i =>
    Classical.choice (exists_dampingData (by norm_num) (by norm_num) (B i) (hne i))
  let f : Fin J → Circle → ℂ := fun i t => fourierPolynomial (B i) t / ((B i).card : ℂ)
  have hf (i : Fin J) : MemLp (f i) ⊤ circleMeasure :=
    (((fourierPolynomial_continuous (B i)).div_const _).memLp_top_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) circleMeasure)
  have hm (i : Fin J) : ∀ᵐ t ∂circleMeasure,
      ‖(M i).multiplier t‖ = 1 - (9/10 : ℝ) * ‖f i t‖ := by
    simpa only [f, norm_div, Complex.norm_natCast] using (M i).modulus
  apply dampedTest_lower_bound (by norm_num) A f (fun i => (M i).multiplier)
    hf (fun i => (M i).memLp) hm
  intro i
  apply initial_segment_pairing_uniform (initialPrefix_isInitialSegment _ _ _) (hne i)
    ((dampingTail_memLp _ (fun j => (M j).memLp) i).mono_exponent le_top)
    (dampingTail_support _ (fun j => (M j).memLp) (fun j => (M j).support) i) hη.le
  · have he : 0 ≤ tailError := by
      rw [TailWeights.tailError_eq]
      positivity [TailWeights.delta_nonneg]
    linarith
  · have hcast : (base : ℝ) ≤ (B i).card := by exact_mod_cast hbase i
    nlinarith
  · let idx : Fin (J-(i.val+1)) → Fin J := fun r => ⟨i.val+1+r.val, by omega⟩
    have hsizes (r : Fin (J-(i.val+1))) :
        (B (idx r)).card = (B i).card * 9^(r.val+1) := by
      simp only [hcard, idx]
      rw [Nat.mul_assoc, ← pow_add]
      congr 2
      omega
    have ht := hN (B i).card (J-(i.val+1))
      ((le_max_left N b).trans (hbase i)) (fun r => B (idx r)) hsizes
      (fun r => M (idx r))
    simpa only [dampingTail_eq_reindexed, idx] using ht

end LittlewoodInverse
