import LittlewoodInverse.Geometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Exact main-theorem specifications

These definitions specify the goals without adding axioms. The proofs
are `quantitative_theorem` in `QuantitativeTheorem.lean` and
`structural_inverse_theorem` in `TerminalCover.lean`.
-/

open scoped BigOperators
open MeasureTheory

namespace LittlewoodInverse

noncomputable def sincMoment (p : ℝ) : ℝ :=
  ∫ x : ℝ, |Real.sinc (Real.pi * x)| ^ p

noncomputable def momentCoefficient (k : ℕ) : ℝ :=
  if Even k then sincMoment (k : ℝ)
  else Real.sqrt (sincMoment ((k - 1 : ℕ) : ℝ) * sincMoment ((k + 1 : ℕ) : ℝ))

noncomputable def tailError : ℝ :=
  let a : ℝ := 9 / 10
  55 * a^2 / 108 + (1 / 9) *
    ((2 / 3) * (5 * a^4 / 6 - 2 * a^3 / 3) +
      2 * ∑' j : ℕ, momentCoefficient (j + 5) * a^(j + 5) / (j + 5 : ℕ))

noncomputable def littlewoodCoefficient : ℝ :=
  9 / (10 * Real.log 9) * (1 - Real.sqrt (tailError / 3))

/-- Theorem 1.1: a uniform asymptotic lower bound and the explicit decimal. -/
def QuantitativeTheorem : Prop :=
  (2459209 / 10000000 : ℝ) < littlewoodCoefficient ∧
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ A : Finset ℤ, N₀ ≤ A.card →
    (littlewoodCoefficient - ε) * Real.log (A.card : ℝ) ≤ littlewoodNorm A

/-- The complete almost-covering conclusion, including all four bounds. -/
def AlmostCover (A : Finset ℤ) (ε c C : ℝ) : Prop :=
  ∃ blocks : Finset (Finset ℤ),
    (∀ B ∈ blocks, B ⊆ A ∧ B.Nonempty ∧
      c * (A.card : ℝ) ≤ (B.card : ℝ) ∧
      ((sumset B).card : ℝ) ≤ C * (B.card : ℝ)) ∧
    (∀ U ∈ blocks, ∀ V ∈ blocks, U ≠ V → Disjoint U V) ∧
    ((A \ blocks.biUnion id).card : ℝ) ≤ ε * (A.card : ℝ) ∧
    (blocks.card : ℝ) ≤ C

/-- Exact geometric or order-cardinality modelling assumption in Theorem 1.5. -/
def AdmitsAssemblyModel (β Δ : ℝ) (A : Finset ℤ) : Prop :=
  Assembly β Δ A ∨ ∃ (A' : Finset ℤ) (f : ℤ → ℤ),
    IsAddFreimanIso A.card (A : Set ℤ) (A' : Set ℤ) f ∧ Assembly β Δ A'

/-- Theorem 1.5, with constants chosen before the set and its decomposition. -/
def StructuralInverseTheorem : Prop :=
  ∀ K ε β Δ : ℝ, 1 ≤ K → 0 < ε → ε < 1 / 2 →
    0 < β → β ≤ 1 → 1 ≤ Δ →
    ∃ (N₀ : ℕ) (c C : ℝ), 2 ≤ N₀ ∧ 0 < c ∧ 0 < C ∧
      ∀ A : Finset ℤ, N₀ ≤ A.card → AdmitsAssemblyModel β Δ A →
        littlewoodNorm A ≤ K * Real.log (A.card : ℝ) → AlmostCover A ε c C

end LittlewoodInverse
