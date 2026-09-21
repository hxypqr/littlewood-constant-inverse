import LittlewoodInverse.Peeling
import LittlewoodInverse.CoverEnergy
import LittlewoodInverse.Statements

namespace LittlewoodInverse

/-- Uniform almost-covering, allowing a size threshold for every accuracy. -/
def UniformAlmostCovers (F : Finset ℤ → Prop) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ (N : ℕ) (c C : ℝ), 0 < c ∧ 0 < C ∧
    ∀ A : Finset ℤ, F A → N ≤ A.card → A.Nonempty → AlmostCover A ε c C

/-- A uniform positive energy density at each fixed positive size density. -/
def UniformMacroscopicEnergy (F : Finset ℤ → Prop) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ (N : ℕ) (η : ℝ), 0 < η ∧
    ∀ A : Finset ℤ, F A → N ≤ A.card → A.Nonempty →
      ∀ Y ⊆ A, δ * (A.card : ℝ) ≤ Y.card → η * (Y.card : ℝ)^3 ≤ additiveEnergy Y

theorem almostCover_of_macroscopic_energy (η δ : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hδ : 0 < δ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ A : Finset ℤ, A.Nonempty →
      (∀ Y ⊆ A, δ * (A.card : ℝ) ≤ Y.card → η * (Y.card : ℝ)^3 ≤ additiveEnergy Y) →
      AlmostCover A δ c C := by
  obtain ⟨c₀, C₀, hc₀, hC₀, hBSG⟩ := External.polynomial_bsg
  let c := c₀ * η^C₀ * δ
  let C := max (C₀ * η^(-C₀)) (1 / c)
  have hc : 0 < c := by dsimp [c]; positivity
  have hC : 0 < C := (by positivity : (0 : ℝ) < 1 / c).trans_le (le_max_right _ _)
  refine ⟨c, C, hc, hC, fun A hA henergy => ?_⟩
  have hAn : (0 : ℝ) < A.card := Nat.cast_pos.mpr hA.card_pos
  obtain ⟨blocks, hb, hd, hr⟩ := finite_peeling A
    (fun Z => ((sumset Z).card : ℝ) ≤ C₀ * η^(-C₀) * Z.card)
    (c * (A.card : ℝ)) (δ * (A.card : ℝ)) (mul_pos hc hAn) (by
      intro Y hYA hYlarge
      have hYn : (0 : ℝ) < Y.card := (mul_pos hδ hAn).trans_le hYlarge
      have hY : Y.Nonempty := Finset.card_pos.mp (by exact_mod_cast hYn)
      obtain ⟨Z, hZY, hZ, hsize, hdouble⟩ := hBSG Y hY η hη hη1 (henergy Y hYA hYlarge)
      refine ⟨Z, hZY, ?_, hdouble⟩
      have hh := mul_le_mul_of_nonneg_left hYlarge
        (show 0 ≤ c₀ * η^C₀ by positivity)
      calc
        c * (A.card : ℝ) ≤ c₀ * η^C₀ * Y.card := by simpa only [c, mul_assoc] using hh
        _ ≤ Z.card := hsize)
  have hcount := disjoint_block_count A blocks (c * (A.card : ℝ))
    (fun B hB => (hb B hB).1) (fun B hB => (hb B hB).2.1) hd
  refine ⟨blocks, ?_, hd, hr.le, ?_⟩
  · intro B hB
    obtain ⟨hBA, hsize, hdouble⟩ := hb B hB
    have hBne : B.Nonempty := Finset.card_pos.mp (by
      exact_mod_cast (mul_pos hc hAn).trans_le hsize)
    exact ⟨hBA, hBne, hsize, hdouble.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))⟩
  · have hn : (blocks.card : ℝ) * c ≤ 1 := by
      have hh : ((blocks.card : ℝ) * c) * A.card ≤ 1 * (A.card : ℝ) := by
        simpa only [mul_assoc, one_mul] using hcount
      exact (mul_le_mul_iff_left₀ hAn).mp hh
    exact ((le_div_iff₀ hc).mpr hn).trans (le_max_right _ _)

theorem uniformAlmostCovers_implies_energy {F : Finset ℤ → Prop}
    (hF : UniformAlmostCovers F) : UniformMacroscopicEnergy F := by
  intro δ hδ hδ1
  obtain ⟨N, c, C, hc, hC, hcover⟩ := hF (δ / 4) (by positivity) (by linarith)
  refine ⟨N, δ^4 / (16 * C^5), by positivity, ?_⟩
  intro A hFA hN hA Y hYA hlarge
  obtain ⟨blocks, hb, hd, hr, hcount⟩ := hcover A hFA hN hA
  have hAn : (0 : ℝ) < A.card := Nat.cast_pos.mpr hA.card_pos
  have hbn : blocks.Nonempty := by
    by_contra h
    have he : blocks = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [he] at hr
    simp only [Finset.biUnion_empty, Finset.sdiff_empty] at hr
    nlinarith
  have he := energy_from_cover A Y blocks δ C hYA hA hbn hδ.le hC.le
    (fun B hB => (hb B hB).1) (fun B hB => (hb B hB).2.2.2) hlarge (by nlinarith)
  have hp : (blocks.card : ℝ)^4 ≤ C^4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcount 4
  have hm := mul_le_mul_of_nonneg_right hp
    (show 0 ≤ 16 * C * (additiveEnergy Y : ℝ) by positivity)
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0 < 16 * C^5)).mpr
  nlinarith

theorem uniformMacroscopicEnergy_implies_cover {F : Finset ℤ → Prop}
    (hF : UniformMacroscopicEnergy F) : UniformAlmostCovers F := by
  intro ε hε hε1
  obtain ⟨N, η, hη, henergy⟩ := hF ε hε hε1
  obtain ⟨c, C, hc, hC, hcover⟩ := almostCover_of_macroscopic_energy (min η 1) ε
    (lt_min hη zero_lt_one) (min_le_right _ _) hε
  refine ⟨N, c, C, hc, hC, fun A hFA hN hA => hcover A hA ?_⟩
  intro Y hYA hlarge
  exact (mul_le_mul_of_nonneg_right (min_le_left η 1) (by positivity)).trans
    (henergy A hFA hN hA Y hYA hlarge)

/-- The qualitative equivalence asserted in the hereditary-energy remark.
Both sides retain uniform constants and permit parameter-dependent thresholds. -/
theorem uniform_cover_iff_macroscopic_energy (F : Finset ℤ → Prop) :
    UniformAlmostCovers F ↔ UniformMacroscopicEnergy F :=
  ⟨uniformAlmostCovers_implies_energy, uniformMacroscopicEnergy_implies_cover⟩

end LittlewoodInverse
