import LittlewoodInverse.Basic
import LittlewoodInverse.FreimanFinite
import Mathlib

/-!
# The precise structural class in Definitions 1.2--1.4

All members are concrete finite integer sets. An assembly certificate carries
the stated terminal geometries and the complete cyclic Sidon residue support.
-/

open scoped BigOperators Pointwise

namespace LittlewoodInverse

def affineImage (u v : ℤ) (A : Finset ℤ) : Finset ℤ :=
  A.image (fun x => u + v * x)

def AdditiveSidon {G : Type*} [Add G] (R : Finset G) : Prop :=
  ∀ a ∈ R, ∀ b ∈ R, ∀ c ∈ R, ∀ d ∈ R,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- The separated block hypothesis includes density of every individual block. -/
structure DenseBlocks (β Δ : ℝ) (A : Finset ℤ) where
  count : ℕ
  radius : ℕ
  minSize : ℕ
  radius_pos : 0 < radius
  minSize_pos : 0 < minSize
  centre : Fin count → ℤ
  block : Fin count → Finset ℤ
  block_mem : ∀ i, ∀ x ∈ block i, -(radius : ℤ) ≤ x ∧ x ≤ (radius : ℤ)
  block_size : ∀ i, minSize ≤ (block i).card
  density : (A.card : ℝ) ^ β ≤ (minSize : ℝ)
  diameter : (radius : ℝ) ≤ Δ * minSize
  separated : ∀ i j, i ≠ j → (4 * radius : ℤ) < |centre i - centre j|
  exact_union : A = Finset.univ.biUnion (fun i => affineImage (centre i) 1 (block i))
  nonempty : A.Nonempty

/-- The integer realization retains both a residue and an integer height. -/
def blockInflation (q M : ℕ) (C : Finset (ZMod q × ℤ)) : Finset ℤ :=
  C.biUnion fun bu => (Finset.range M).image fun (r : ℕ) =>
    (bu.1.val : ℤ) + (q : ℤ) * ((M : ℤ) * bu.2 + (r : ℤ))

inductive Terminal (β Δ : ℝ) : Finset ℤ → Prop
  | singleton (a : ℤ) : Terminal β Δ {a}
  | dense {A : Finset ℤ} (data : DenseBlocks β Δ A) (u v : ℤ) (hv : v ≠ 0) :
      Terminal β Δ (affineImage u v A)
  | inflation (q M : ℕ) (hq : 0 < q) (hM : 0 < M)
      (C : Finset (ZMod q × ℤ)) (hC : C.Nonempty) (hlong : C.card ≤ M)
      (u v : ℤ) (hv : v ≠ 0) :
      Terminal β Δ (affineImage u v (blockInflation q M C))

/-- Inductive finite-tree realization of the manuscript's assembly class.
Affine normalization is allowed at every node. There are no bounds on depth,
branching, modulus, or integer diameter. -/
inductive Assembly (β Δ : ℝ) : Finset ℤ → Prop
  | terminal {A : Finset ℤ} (h : Terminal β Δ A) : Assembly β Δ A
  | affine {A : Finset ℤ} (h : Assembly β Δ A) (u v : ℤ) (hv : v ≠ 0) :
      Assembly β Δ (affineImage u v A)
  | node (q : ℕ) (hq : 2 ≤ q) (R : Finset (ZMod q)) (hR : R.Nonempty)
      (hSidon : AdditiveSidon R) (child : ZMod q → Finset ℤ)
      (hchild : ∀ r ∈ R, Assembly β Δ (child r))
      (hne : ∀ r ∈ R, (child r).Nonempty) :
      Assembly β Δ (R.biUnion fun r => affineImage (r.val : ℤ) q (child r))

theorem affine_injective (u v : ℤ) (hv : v ≠ 0) :
    Function.Injective (fun x : ℤ => u + v * x) := by
  intro x y h
  exact mul_left_cancel₀ hv (add_left_cancel h)

theorem affine_card (A : Finset ℤ) (u v : ℤ) (hv : v ≠ 0) :
    (affineImage u v A).card = A.card := by
  exact Finset.card_image_of_injective A (affine_injective u v hv)

theorem affine_nonempty {A : Finset ℤ} (hA : A.Nonempty) (u v : ℤ) :
    (affineImage u v A).Nonempty := hA.image _

theorem affine_freiman_two (A : Finset ℤ) (u v : ℤ) (hv : v ≠ 0) :
    IsAddFreimanIso 2 (A : Set ℤ) (affineImage u v A : Set ℤ)
      (fun x => u + v * x) := by
  apply isAddFreimanIso_two.mpr
  constructor
  · refine ⟨?_, (affine_injective u v hv).injOn, ?_⟩
    · intro x hx
      exact Finset.mem_image_of_mem _ hx
    · intro y hy
      exact Finset.mem_image.mp hy
  · intro a _ b _ c _ d _
    constructor
    · intro h
      apply mul_left_cancel₀ hv
      linear_combination h
    · intro h
      linear_combination v * h

theorem affine_energy (A : Finset ℤ) (u v : ℤ) (hv : v ≠ 0) :
    additiveEnergy (affineImage u v A) = additiveEnergy A := by
  exact (freiman_energy (affine_freiman_two A u v hv) (Finset.Subset.refl A)).symm

theorem affine_sumset_card (A : Finset ℤ) (u v : ℤ) (hv : v ≠ 0) :
    (sumset (affineImage u v A)).card = (sumset A).card := by
  exact (freiman_sumset_card (affine_freiman_two A u v hv) (Finset.Subset.refl A)).symm

end LittlewoodInverse
