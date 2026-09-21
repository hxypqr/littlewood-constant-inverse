import LittlewoodInverse.Basic

/-!
# Explicit external inputs

Only established external theorems are axiomatized in this file. None of the
manuscript's internal lemmas or main theorems is included here.
-/

open scoped BigOperators Pointwise
open MeasureTheory

namespace LittlewoodInverse.External

/-- McGehee--Pigno--Smith's weighted Littlewood inequality.

Source: McGehee, Pigno and Smith, Ann. of Math. 113 (1981), 613--618,
DOI 10.2307/2007000. This exact complex-coefficient formulation is also
Theorem 1.1 of Hanson, https://arxiv.org/html/2003.01561v2.
`Fin m` is indexed from zero, hence the denominator is `j.val + 1`.
-/
axiom mps_weighted : ∃ c : ℝ, 0 < c ∧
  ∀ (m : ℕ) (n : Fin m → ℤ), StrictMono n → ∀ (u : Fin m → ℂ),
    c * (∑ j, ‖u j‖ / ((j.val : ℝ) + 1)) ≤
      ∫ t, ‖weightedFourierPolynomial n u t‖ ∂circleMeasure

/-- The polynomial Balog--Szemerédi--Gowers theorem in sumset form.

Sources: Tao--Vu, *Additive Combinatorics*, Theorem 2.31;
Reiher--Schoen, https://arxiv.org/abs/2308.10245v2, followed by the standard
sum--difference inequality. Constants are absolute: they are chosen before
the ambient abelian group, its finite subset, and the energy parameter.
No finiteness or topology is assumed on the ambient group.
-/
axiom polynomial_bsg : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
  ∀ {G : Type} [AddCommGroup G] [DecidableEq G]
    (Y : Finset G), Y.Nonempty → ∀ (γ : ℝ), 0 < γ → γ ≤ 1 →
    γ * (Y.card : ℝ) ^ 3 ≤ (additiveEnergy Y : ℝ) →
    ∃ Z : Finset G, Z ⊆ Y ∧ Z.Nonempty ∧
      c * γ ^ C * (Y.card : ℝ) ≤ (Z.card : ℝ) ∧
      ((sumset Z).card : ℝ) ≤ C * γ ^ (-C) * (Z.card : ℝ)

end LittlewoodInverse.External
