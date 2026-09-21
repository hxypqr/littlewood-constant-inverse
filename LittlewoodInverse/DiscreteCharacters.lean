import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Tactic

/-! Character separation and the canonical evaluation embedding of a discrete
abelian group. The separation proof uses the existing algebraic character
module over ℚ/ℤ, whose inclusion in ℝ/ℤ is proved here. -/

noncomputable section
namespace LittlewoodInverse

def rationalCircleCast : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.lift (AddSubgroup.zmultiples (1 : ℚ))
    ((QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).comp
      (Rat.castHom ℝ).toAddMonoidHom) (by
        intro x hx
        obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
        change (((n • (1 : ℚ) : ℚ) : ℝ) : AddCircle (1 : ℝ)) = 0
        rw [AddCircle.coe_eq_zero_iff]
        exact ⟨n, by simp⟩)

@[simp] theorem rationalCircleCast_coe (x : ℚ) :
    rationalCircleCast (x : AddCircle (1 : ℚ)) =
      ((x : ℝ) : AddCircle (1 : ℝ)) := rfl

theorem rationalCircleCast_injective : Function.Injective rationalCircleCast := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  induction x using QuotientAddGroup.induction_on with
  | H x =>
    rw [rationalCircleCast_coe, AddCircle.coe_eq_zero_iff] at hx
    obtain ⟨n, hn⟩ := hx
    rw [AddCircle.coe_eq_zero_iff]
    refine ⟨n, ?_⟩
    simp only [zsmul_one] at hn ⊢
    exact_mod_cast hn

variable (Γ : Type*) [AddCommGroup Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]

/-- An algebraic rational-circle character gives a continuous character on a
discrete group. -/
def characterModuleToDual (c : CharacterModule Γ) : PontryaginDual (Multiplicative Γ) where
  toFun a := AddCircle.toCircle (rationalCircleCast (c a.toAdd))
  map_one' := by simp
  map_mul' a b := by simp [map_add, AddCircle.toCircle_add]
  continuous_toFun := continuous_of_discreteTopology

theorem discrete_characters_separate {a : Γ} (ha : a ≠ 0) :
    ∃ χ : PontryaginDual (Multiplicative Γ), χ (Multiplicative.ofAdd a) ≠ 1 := by
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero ha
  refine ⟨characterModuleToDual Γ c, fun h => hc ?_⟩
  apply rationalCircleCast_injective
  apply AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0)
  change AddCircle.toCircle (rationalCircleCast (c a)) = 1 at h
  simpa using h

/-- The canonical evaluation homomorphism into the double Pontryagin dual. -/
def discreteEvaluation : Γ →+ Additive (PontryaginDual (PontryaginDual (Multiplicative Γ))) where
  toFun a := Additive.ofMul
    ({ toFun := fun χ => χ (Multiplicative.ofAdd a)
       map_one' := rfl
       map_mul' := fun _ _ => rfl
       continuous_toFun := by
         change Continuous (fun χ : Multiplicative Γ →ₜ* _root_.Circle =>
           χ (Multiplicative.ofAdd a))
         exact continuous_eval_const _ } :
      PontryaginDual (PontryaginDual (Multiplicative Γ)))
  map_zero' := by
    apply PontryaginDual.ext
    intro χ
    exact map_one χ
  map_add' a b := by
    apply PontryaginDual.ext
    intro χ
    exact map_mul χ (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)

omit [DiscreteTopology Γ] in
@[simp] theorem discreteEvaluation_apply (a : Γ)
    (χ : PontryaginDual (Multiplicative Γ)) :
    Additive.toMul (discreteEvaluation Γ a) χ = χ (Multiplicative.ofAdd a) := rfl

theorem discreteEvaluation_injective : Function.Injective (discreteEvaluation Γ) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  by_contra hne
  obtain ⟨χ, hχ⟩ := discrete_characters_separate Γ hne
  apply hχ
  have h := congrArg (fun z : Additive (PontryaginDual (PontryaginDual (Multiplicative Γ))) =>
    Additive.toMul z χ) ha
  simpa using h

end LittlewoodInverse
