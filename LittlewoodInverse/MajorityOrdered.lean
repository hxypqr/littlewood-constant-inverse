import LittlewoodInverse.MajorityCounting

open scoped BigOperators

namespace LittlewoodInverse
namespace MajorityCounting

variable {α : Type*} [DecidableEq α]

def tupleSupport {k : ℕ} (x : Fin k → α) : Finset α := Finset.univ.image x

theorem tupleSupport_equiv {k : ℕ} (U : Finset α) (e : Fin k ≃ U) :
    tupleSupport (fun i => (e i).val) = U := by
  ext a
  simp only [tupleSupport, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact (e i).property
  · intro ha
    exact ⟨e.symm ⟨a, ha⟩, by simp⟩

def ValidOrderedPair {s t : ℕ} (P : Finset α → Finset α → Prop)
    (p : (Fin s → α) × (Fin t → α)) : Prop :=
  Function.Injective p.1 ∧ Function.Injective p.2 ∧
    Disjoint (tupleSupport p.1) (tupleSupport p.2) ∧ P (tupleSupport p.1) (tupleSupport p.2)

attribute [local instance] Classical.propDecidable

noncomputable def orderedPairs [Fintype α] (s t : ℕ) (P : Finset α → Finset α → Prop) :
    Finset ((Fin s → α) × (Fin t → α)) := Finset.univ.filter (ValidOrderedPair P)

theorem validOrderedPair_append_injective {s t : ℕ} {P : Finset α → Finset α → Prop}
    {p : (Fin s → α) × (Fin t → α)} (hp : ValidOrderedPair P p) :
    Function.Injective (Fin.append p.1 p.2) := by
  intro i j hij
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [Fin.append_left] at hij
      exact congrArg (Fin.castAdd t) (hp.1 hij)
    | right j =>
      simp only [Fin.append_left, Fin.append_right] at hij
      exfalso
      exact Finset.disjoint_left.mp hp.2.2.1
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
        (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hij.symm⟩)
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [Fin.append_left, Fin.append_right] at hij
      exfalso
      exact Finset.disjoint_left.mp hp.2.2.1
        (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hij.symm⟩)
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    | right j =>
      simp only [Fin.append_right] at hij
      exact congrArg (Fin.natAdd s) (hp.2.1 hij)

/-- Each good support with one admissible balanced orientation supplies
`s! t!` distinct ordered tuples. Tuples from different supports are
disjoint because their union of coordinates recovers the support. -/
theorem orderedPairs_card_lower [Fintype α] (H : Finset (Finset α)) (s t : ℕ)
    (P : Finset α → Finset α → Prop)
    (hH : ∀ S ∈ H, S.card = s + t ∧ ∃ U ⊆ S, U.card = s ∧ P U (S \ U)) :
    H.card * s.factorial * t.factorial ≤ (orderedPairs s t P).card := by
  classical
  choose U hUS hUcard hP using fun S : H => (hH S.val S.property).2
  have hWcard (S : H) : (S.val \ U S).card = t := by
    rw [Finset.card_sdiff_of_subset (hUS S), (hH S.val S.property).1, hUcard S]
    omega
  let Choices (S : H) := (Fin s ≃ U S) × (Fin t ≃ ↥(S.val \ U S))
  let encode : (Σ S : H, Choices S) → ((Fin s → α) × (Fin t → α)) :=
    fun z => (fun i => (z.2.1 i).val, fun i => (z.2.2 i).val)
  have hsup1 (z : Σ S : H, Choices S) : tupleSupport (encode z).1 = U z.1 :=
    tupleSupport_equiv _ z.2.1
  have hsup2 (z : Σ S : H, Choices S) : tupleSupport (encode z).2 = z.1.val \ U z.1 :=
    tupleSupport_equiv _ z.2.2
  have hsup (z : Σ S : H, Choices S) :
      tupleSupport (encode z).1 ∪ tupleSupport (encode z).2 = z.1.val := by
    rw [hsup1, hsup2]
    exact Finset.union_sdiff_of_subset (hUS z.1)
  have hgood (z : Σ S : H, Choices S) : ValidOrderedPair P (encode z) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i j hij
      exact z.2.1.injective (Subtype.ext hij)
    · intro i j hij
      exact z.2.2.injective (Subtype.ext hij)
    · rw [hsup1, hsup2]
      apply Finset.disjoint_left.mpr
      intro a ha hbad
      exact (Finset.mem_sdiff.mp hbad).2 ha
    · rw [hsup1, hsup2]
      exact hP z.1
  have hinj : Function.Injective encode := by
    intro z w he
    have hS : z.1 = w.1 := by
      apply Subtype.ext
      rw [← hsup z, ← hsup w, he]
    rcases z with ⟨S, e, f⟩
    rcases w with ⟨T, g, h⟩
    dsimp only at hS
    subst T
    apply congrArg (fun p : Choices S => (⟨S, p⟩ : Σ S : H, Choices S))
    apply Prod.ext
    · apply Equiv.ext
      intro i
      exact Subtype.ext (congrFun (congrArg Prod.fst he) i)
    · apply Equiv.ext
      intro i
      exact Subtype.ext (congrFun (congrArg Prod.snd he) i)
  let embedding : (Σ S : H, Choices S) ↪ orderedPairs s t P :=
    ⟨fun z => ⟨encode z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgood z⟩⟩,
      fun z w h => hinj (congrArg Subtype.val h)⟩
  have hcard (S : H) : Fintype.card (Choices S) = s.factorial * t.factorial := by
    let e : Fin s ≃ U S := Fintype.equivOfCardEq (by
      simp only [Fintype.card_fin, Fintype.card_coe, hUcard S])
    let f : Fin t ≃ ↥(S.val \ U S) := Fintype.equivOfCardEq (by
      simp only [Fintype.card_fin, Fintype.card_coe, hWcard S])
    simp only [Choices, Fintype.card_prod, Fintype.card_equiv e, Fintype.card_equiv f,
      Fintype.card_fin]
  have hc := Fintype.card_le_of_embedding embedding
  rw [Fintype.card_sigma] at hc
  simp only [hcard, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
    smul_eq_mul] at hc
  nlinarith only [hc]

end MajorityCounting
end LittlewoodInverse
