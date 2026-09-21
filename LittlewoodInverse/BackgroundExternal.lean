import LittlewoodInverse.PrefixPairing

/-! # Cited background theorems

These are precise external statements, not internal manuscript lemmas.
They are kept separate from the four inputs to the two main theorems.
-/

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LittlewoodInverse.BackgroundExternal

noncomputable def setIndicator {G : Type*} (X : Finset G) (x : G) : ℤ := by
  classical
  exact if x ∈ X then 1 else 0

/-- The actual Fourier algebra norm: normalized counting on the group,
and unnormalized counting on its character group. -/
noncomputable def finiteAlgebraNorm {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℤ) : ℝ :=
  ∑ χ : AddChar G ℂ,
    ‖(Fintype.card G : ℂ)⁻¹ * ∑ x : G, (f x : ℂ) * conj (χ x)‖

noncomputable def cosetIndicator {G : Type*} [AddCommGroup G]
    (H : AddSubgroup G) (a x : G) : ℤ := by
  classical
  exact if x - a ∈ H then 1 else 0

/-- Green--Sanders, Annals of Mathematics 168 (2008), Theorem 1.3,
pp. 1026--1028, with their exact double-exponential bound and optional
bound on the number of distinct subgroups.
Source: https://annals.math.princeton.edu/wp-content/uploads/annals-v168-n3-p09.pdf
-/
axiom green_sanders : ∃ C : ℝ, 0 < C ∧
  ∀ {G : Type} [AddCommGroup G] [Fintype G] (f : G → ℤ) (M : ℝ),
    0 ≤ M → finiteAlgebraNorm f ≤ M →
    ∃ (L : ℕ) (sign : Fin L → ℤ) (a : Fin L → G) (H : Fin L → AddSubgroup G),
      (∀ j, sign j = 1 ∨ sign j = -1) ∧
      (∀ x, f x = ∑ j, sign j * cosetIndicator (H j) (a j) x) ∧
      (L : ℝ) ≤ Real.exp (Real.exp (C * M ^ 4)) ∧
      ((Set.range H).ncard : ℝ) ≤ M + 1 / 100

/-- Bloom--Green, Theorem 1.2 and the sentence immediately following it.
The constants are absolute, and the subset is a genuine initial segment.
This unrestricted inverse theorem is a comparison result, not an input
to this project's structural theorem.
Source: https://arxiv.org/html/2602.16482v2
-/
axiom bloom_green_inverse : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
  ∃ N₀ : ℕ, ∀ (A : Finset ℤ), N₀ ≤ A.card → ∀ K δ : ℝ,
    0 < K → 0 < δ → δ ≤ 1 / 2 →
    littlewoodNorm A ≤ K * Real.log A.card →
    ∃ B : Finset ℤ, IsInitialSegment B A ∧
      c₁ * (A.card : ℝ) ^ (1 - δ) ≤ (B.card : ℝ) ∧
      c₂ * (δ / K) ^ 2 * (B.card : ℝ) ^ 3 ≤ (additiveEnergy B : ℝ)

/-- The exact parameter expression behind the rounded decimal reported
by Bloom--Green; no rounded decimal is treated as an exact constant. -/
noncomputable def bloomGreenCoefficient (b lam : ℝ) : ℝ :=
  (1 - Real.exp (-b)) / Real.log lam *
    (1 - Real.sqrt (2 / 3) * b / (Real.sqrt lam - 1))

/-- Bloom--Green, Section 4, proof of Theorem 1.5. The positive error
parameter spells out the uniform `o(1)` statement for integer sets.
Source: https://arxiv.org/html/2602.16482v2
-/
axiom bloom_green_constant : ∀ b lam : ℝ, 0 < b → 2 ≤ lam →
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ A : Finset ℤ, N₀ ≤ A.card →
    (bloomGreenCoefficient b lam - ε) * Real.log A.card ≤ littlewoodNorm A

end LittlewoodInverse.BackgroundExternal

