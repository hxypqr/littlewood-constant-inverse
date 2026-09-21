import LittlewoodInverse.Fourier
import Mathlib

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LittlewoodInverse
namespace MomentCounting

def tuples (B : Finset ℤ) (r : ℕ) : Finset (Fin r → ℤ) := Fintype.piFinset (fun _ => B)

def relationCount (B : Finset ℤ) (r : ℕ) : ℕ :=
  ((tuples B r ×ˢ tuples B r).filter (fun p => (∑ i, p.1 i) = ∑ i, p.2 i)).card

theorem fourier_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℤ) (t : Circle) :
    fourier (∑ i ∈ s, f i) t = ∏ i ∈ s, fourier (f i) t := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

theorem polynomial_pow (B : Finset ℤ) (r : ℕ) (t : Circle) :
    fourierPolynomial B t ^ r = ∑ p ∈ tuples B r, fourier (∑ i, p i) t := by
  unfold fourierPolynomial
  rw [Finset.sum_pow']
  apply Finset.sum_congr rfl
  intro p _
  exact (fourier_sum Finset.univ p t).symm

theorem norm_even_pow_expansion (B : Finset ℤ) (r : ℕ) (t : Circle) :
    (‖fourierPolynomial B t‖ ^ (2 * r) : ℂ) =
      ∑ p ∈ tuples B r ×ˢ tuples B r, fourier ((∑ i, p.1 i) - ∑ i, p.2 i) t := by
  have hpow : (‖fourierPolynomial B t‖ ^ (2 * r) : ℂ) =
      fourierPolynomial B t ^ r * conj (fourierPolynomial B t ^ r) := by
    rw [Complex.mul_conj', norm_pow, Complex.ofReal_pow, ← pow_mul]
    rw [Nat.mul_comm 2 r]
  rw [hpow, polynomial_pow]
  simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_product,
    sub_eq_add_neg, fourier_add, fourier_neg]

/-- Actual even Fourier moments equal the count of equal sums of r terms. -/
theorem integral_even_moment (B : Finset ℤ) (r : ℕ) :
    (∫ t, ‖fourierPolynomial B t‖ ^ (2 * r) ∂circleMeasure) = (relationCount B r : ℝ) := by
  have h : (∫ t, (‖fourierPolynomial B t‖ ^ (2 * r) : ℂ) ∂circleMeasure) =
      (relationCount B r : ℂ) := by
    simp_rw [norm_even_pow_expansion]
    rw [integral_finsetSum _ (fun _ _ => continuous_circle_integrable (by fun_prop))]
    simp_rw [integral_fourier, sub_eq_zero]
    simp [relationCount, Finset.sum_boole]
  exact_mod_cast h

end MomentCounting

/-- The elementary energy upper bound used in the label-counting argument. -/
theorem additiveEnergy_le_card_cube {G : Type*} [AddCommGroup G] [DecidableEq G]
    (B : Finset G) : additiveEnergy B ≤ B.card ^ 3 := by
  unfold additiveEnergy Finset.addEnergy
  have h :
      ({x ∈ ((B ×ˢ B) ×ˢ B ×ˢ B) | x.1.1 + x.2.1 = x.1.2 + x.2.2}).card ≤
        (B ×ˢ B ×ˢ B).card := by
    apply Finset.card_le_card_of_injOn (fun x => (x.1.1, x.1.2, x.2.1))
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hx ⊢
      exact ⟨hx.1.1.1, hx.1.1.2, hx.1.2.1⟩
    · intro x hx y hy heq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hx hy
      simp only [Prod.mk.injEq] at heq
      have hlast : x.2.2 = y.2.2 := by
        apply add_left_cancel (a := x.1.2)
        rw [← hx.2, heq.1, heq.2.2, hy.2, heq.2.1]
      exact Prod.ext (Prod.ext heq.1 heq.2.1) (Prod.ext heq.2.2 hlast)
  simpa [Finset.card_product, pow_succ, pow_two, Nat.mul_assoc] using h

end LittlewoodInverse
