import LittlewoodInverse.Peeling

namespace LittlewoodInverse

/-- The literal polynomial parameter bounds of Lemma 5.1. Both constants
are chosen before the ambient group and all set and error parameters. -/
theorem hereditary_energy_cover_polynomial : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ {G : Type} [AddCommGroup G] [DecidableEq G]
      (X : Finset G), X.Nonempty → ∀ η δ : ℝ,
      0 < η → η ≤ 1 → 0 < δ → δ < 1 →
      (∀ Y ⊆ X, Y.Nonempty → η * (Y.card : ℝ)^4 / (X.card : ℝ) ≤
        (additiveEnergy Y : ℝ)) →
      ∃ blocks : Finset (Finset G),
        (∀ Z ∈ blocks, Z ⊆ X ∧ Z.Nonempty ∧
          c * η^C * δ^C * (X.card : ℝ) ≤ (Z.card : ℝ) ∧
          ((sumset Z).card : ℝ) ≤ C * η^(-C) * δ^(-C) * (Z.card : ℝ)) ∧
        (∀ U ∈ blocks, ∀ V ∈ blocks, U ≠ V → Disjoint U V) ∧
        ((X \ blocks.biUnion id).card : ℝ) < δ * (X.card : ℝ) ∧
        (blocks.card : ℝ) ≤ C * η^(-C) * δ^(-C) := by
  obtain ⟨c, C₀, hc, hC₀, hcover⟩ := hereditary_energy_cover
  let C := C₀ + 1 + 1 / c
  have hinv : 0 < 1 / c := by positivity
  have hC : 0 < C := by dsimp [C]; linarith
  have hC₀C : C₀ ≤ C := by dsimp [C]; linarith
  have hCC : C₀ + 1 ≤ C := by dsimp [C]; linarith
  have hcC : 1 / c ≤ C := by dsimp [C]; linarith
  refine ⟨c, C, hc, hC, ?_⟩
  intro G _ _ X hX η δ hη hη1 hδ hδ1 henergy
  obtain ⟨blocks, hblocks, hdis, hrem, hcount⟩ :=
    hcover X hX η δ hη hη1 hδ hδ1 henergy
  have ht : 0 < η * δ := mul_pos hη hδ
  have ht1 : η * δ ≤ 1 := by nlinarith
  have hs : (η * δ)^C ≤ (η * δ)^C₀ * δ := by
    calc
      _ ≤ (η * δ)^(C₀ + 1) :=
        Real.rpow_le_rpow_of_exponent_ge ht ht1 hCC
      _ = (η * δ)^C₀ * (η * δ) := by rw [Real.rpow_add ht, Real.rpow_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have hn : (η * δ)^(-C₀) ≤ (η * δ)^(-C) :=
    Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
  have he (a : ℝ) : η^a * δ^a = (η * δ)^a := (Real.mul_rpow hη.le hδ.le).symm
  refine ⟨blocks, ?_, hdis, hrem, ?_⟩
  · intro Z hZ
    obtain ⟨hZX, hZn, hsize, hd⟩ := hblocks Z hZ
    refine ⟨hZX, hZn, ?_, ?_⟩
    · calc
        _ = c * (η * δ)^C * (X.card : ℝ) := by rw [mul_assoc c, he C]
        _ ≤ c * ((η * δ)^C₀ * δ) * (X.card : ℝ) := by gcongr
        _ = c * (η * δ)^C₀ * δ * (X.card : ℝ) := by ring
        _ ≤ _ := hsize
    · apply hd.trans
      calc
        _ ≤ C * (η * δ)^(-C) * (Z.card : ℝ) := by gcongr
        _ = _ := by rw [← he (-C)]; ring
  · have hsmall : (blocks.card : ℝ) * (c * (η * δ)^C) ≤ 1 := by
      apply le_trans _ hcount
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs hc.le
    have hdiv := (le_div_iff₀ (show 0 < c * (η * δ)^C by positivity)).mpr hsmall
    calc
      _ ≤ 1 / (c * (η * δ)^C) := hdiv
      _ = (1 / c) * (η * δ)^(-C) := by rw [Real.rpow_neg ht.le]; field_simp
      _ ≤ C * (η * δ)^(-C) := mul_le_mul_of_nonneg_right hcC (by positivity)
      _ = _ := by rw [mul_assoc C, he (-C)]

end LittlewoodInverse
