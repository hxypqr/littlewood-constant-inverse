import LittlewoodInverse.RetainedLeaves
import LittlewoodInverse.CoverGluing

open scoped BigOperators Topology
open Filter

namespace LittlewoodInverse

/-- The two terminal geometry theorems must establish this property. -/
def UniformTerminalCover (β Δ : ℝ) : Prop :=
  ∀ K ε : ℝ, 1 ≤ K → 0 < ε → ε < 1 →
    ∃ (N₀ : ℕ) (c C : ℝ), 0 < c ∧ 0 < C ∧
      ∀ A : Finset ℤ, N₀ ≤ A.card → Terminal β Δ A →
        littlewoodNorm A ≤ K * Real.log (A.card : ℝ) → AlmostCover A ε c C

theorem eventually_log_le_two_log_mul {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℝ in atTop, Real.log N ≤ 2 * Real.log (δ * N) := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (-2 * Real.log δ)),
    eventually_gt_atTop (0 : ℝ)] with N hlog hN
  rw [Real.log_mul hδ.ne' hN.ne']
  linarith

/-- The complete assembly step in Section 8. The terminal covering input is
explicit: this reduction does not assert either missing terminal geometry theorem. -/
theorem assembly_inverse_of_terminal {β Δ : ℝ} (ht : UniformTerminalCover β Δ)
    (K ε : ℝ) (hK : 1 ≤ K) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ (N₀ : ℕ) (c C : ℝ), 2 ≤ N₀ ∧ 0 < c ∧ 0 < C ∧
      ∀ A : Finset ℤ, N₀ ≤ A.card → Assembly β Δ A →
        littlewoodNorm A ≤ K * Real.log (A.card : ℝ) → AlmostCover A ε c C := by
  classical
  obtain ⟨Nt, c, C, hc, hC, hterm⟩ := ht (2 * K) (ε / 2) (by linarith)
    (by positivity) (by linarith)
  let B : ℝ := max 1 ((K / (mpsConstant * (1 / 2))) ^ 20)
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let δ : ℝ := ε / (4 * B)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hB)
  have hδB : δ * B = ε / 4 := by dsimp [δ]; field_simp
  have hevent : ∀ᶠ N : ℝ in atTop,
      (Nt : ℝ) / δ ≤ N ∧ Real.log N ≤ 2 * Real.log (δ * N) ∧
        N ^ (1 / 2 : ℝ) * (K * Real.log N) ^ 20 ≤ (ε / 4) * N := by
    filter_upwards [eventually_ge_atTop ((Nt : ℝ) / δ),
      eventually_log_le_two_log_mul hδ,
      eventually_small_leaf_envelope K (θ := 1 / 2) (by norm_num) (by positivity : 0 < ε / 4)]
      with N hn hl he
    exact ⟨hn, hl, he⟩
  have hnatevent := (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually hevent
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hnatevent
  refine ⟨max 2 N₁, c * δ, max C (B * C), le_max_left _ _, mul_pos hc hδ,
    lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
  intro A hA hgeom hnorm
  have hN2 : 2 ≤ A.card := (le_max_left _ _).trans hA
  have hN : 1 < (A.card : ℝ) := by exact_mod_cast (show 1 < A.card by omega)
  have hNpos : (0 : ℝ) < A.card := lt_trans zero_lt_one hN
  obtain ⟨hNt, hlog, hsmall⟩ := hN₁ A.card ((le_max_right _ _).trans hA)
  obtain ⟨L⟩ := assembly_has_terminal_leaves hgeom
  obtain ⟨s, hsize, hcount, hdiscard⟩ := assembly_retained_leaves L
    (θ := 1 / 2) (by norm_num) hδ.le hN hnorm
  have hsB : (s.card : ℝ) ≤ B := hcount.trans (le_max_right _ _)
  have hrem : (∑ i ∈ Finset.univ \ s, ((L.leaf i).card : ℝ)) ≤ (ε / 2) * A.card := by
    have haux : δ * (A.card : ℝ) * (K / (mpsConstant * (1 / 2))) ^ 20 ≤
        (ε / 4) * A.card := by
      calc
        _ ≤ δ * (A.card : ℝ) * B := mul_le_mul_of_nonneg_left (le_max_right _ _)
          (mul_nonneg hδ.le hNpos.le)
        _ = _ := by nlinarith [hδB]
    linarith
  have hlocal : ∀ i ∈ s, AlmostCover (L.leaf i) (ε / 2) c C := by
    intro i hi
    have hiSize := hsize i hi
    have hNt' : (Nt : ℝ) ≤ δ * (A.card : ℝ) := by
      nlinarith [(div_le_iff₀ hδ).mp hNt]
    have hnleaf : Nt ≤ (L.leaf i).card := by exact_mod_cast hNt'.trans hiSize
    apply hterm (L.leaf i) hnleaf (L.terminal i)
    have hilog := Real.log_le_log (mul_pos hδ hNpos) hiSize
    have hlogleaf : Real.log (A.card : ℝ) ≤ 2 * Real.log ((L.leaf i).card : ℝ) := by linarith
    calc
      littlewoodNorm (L.leaf i) ≤ littlewoodNorm A := L.leaf_norm_le i
      _ ≤ K * Real.log (A.card : ℝ) := hnorm
      _ ≤ (2 * K) * Real.log ((L.leaf i).card : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_left hlogleaf (by linarith : 0 ≤ K)]
  have hglue := assembly_glue_covers L s (by positivity : 0 ≤ ε / 2) hc.le hsize hrem hlocal
  exact almostCover_mono hglue (by linarith) le_rfl
    (max_le_max le_rfl (mul_le_mul_of_nonneg_right hsB hC.le))

end LittlewoodInverse
