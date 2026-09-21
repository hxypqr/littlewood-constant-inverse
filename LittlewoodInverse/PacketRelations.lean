import LittlewoodInverse.PacketEnergy
import LittlewoodInverse.PacketSupport
import LittlewoodInverse.PacketLift
import LittlewoodInverse.DenseMajority

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LittlewoodInverse
namespace PacketEnergy

def shiftedRelations (S A J : Finset ℤ) (p q : ℕ) :=
  (J ×ˢ ((MomentCounting.tuples S p ×ˢ MomentCounting.tuples S q) ×ˢ A)).filter
    (fun v ↦ (∑ i, v.2.1.1 i) = (∑ i, v.2.1.2 i) + v.2.2 + v.1)

theorem shiftedRelations_card (S A J : Finset ℤ) (p q : ℕ) :
    (shiftedRelations S A J p q).card = ∑ t ∈ J, shiftedRelationCount S A p q t := by
  simp only [shiftedRelations, shiftedRelationCount, Finset.card_filter, Finset.sum_product]

/-- Witness choices preserve all ordered tuple information. No multiplicity
is lost when a bounded carry and an ambient label are adjoined. -/
theorem ordered_count_le_relations {α : Type*} [DecidableEq α]
    (S A : Finset ℤ) (p q : ℕ) (l : α → ℤ) (hl : Function.Injective l)
    (hmem : ∀ i, l i ∈ S)
    (Q : Finset ((Fin p → α) × (Fin q → α)))
    (hw : ∀ v ∈ Q, ∃ a ∈ A,
      |(∑ i, l (v.1 i)) - (∑ i, l (v.2 i)) - a| ≤ 4 * ((p + q : ℕ) : ℤ)) :
    Q.card ≤ ∑ t ∈ carryRange (p + q), shiftedRelationCount S A p q t := by
  classical
  have hex : ∀ v : (Fin p → α) × (Fin q → α), ∃ a : ℤ, v ∈ Q →
      a ∈ A ∧ |(∑ i, l (v.1 i)) - (∑ i, l (v.2 i)) - a| ≤
        4 * ((p + q : ℕ) : ℤ) := by
    intro v
    by_cases hv : v ∈ Q
    · obtain ⟨a, ha, hb⟩ := hw v hv
      exact ⟨a, fun _ ↦ ⟨ha, hb⟩⟩
    · exact ⟨0, fun hh ↦ (hv hh).elim⟩
  choose a ha using hex
  let f := fun v : (Fin p → α) × (Fin q → α) ↦
    ((∑ i, l (v.1 i)) - (∑ i, l (v.2 i)) - a v,
      ((fun i ↦ l (v.1 i)), (fun i ↦ l (v.2 i))), a v)
  rw [← shiftedRelations_card]
  apply Finset.card_le_card_of_injOn f
  · intro v hv
    rcases ha v hv with ⟨haA, hab⟩
    simp only [shiftedRelations, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
      carryRange, Finset.mem_Icc, MomentCounting.tuples, Fintype.mem_piFinset, f]
    refine ⟨⟨?_, ⟨⟨fun i ↦ hmem _, fun i ↦ hmem _⟩, haA⟩⟩, ?_⟩
    · exact abs_le.mp hab
    · ring
  · intro v hv w hw he
    have hp := congrArg (fun z => z.2.1.1) he
    have hq := congrArg (fun z => z.2.1.2) he
    apply Prod.ext
    · funext i
      exact hl (congrFun hp i)
    · funext i
      exact hl (congrFun hq i)

end PacketEnergy

namespace DenseBlocks

theorem balanced_pairing_label_witness_reindex {β Δ : ℝ} {A : Finset ℤ}
    (data : DenseBlocks β Δ A) {α : Type*} [DecidableEq α]
    (e : α ↪ Fin data.count) (U V : Finset α) (hk : 2 ≤ U.card + V.card)
    (hne : circlePairing (fourierPolynomial A)
      (fun x ↦ (∏ i ∈ U, data.certificate (e i) x) *
        ∏ i ∈ V, conj (data.certificate (e i) x)) ≠ 0) :
    ∃ j : Fin data.count,
      |(∑ i ∈ U, data.label (e i)) - (∑ i ∈ V, data.label (e i)) - data.label j| ≤
        4 * ((U.card : ℤ) + V.card) := by
  have hp : circlePairing (fourierPolynomial A)
      (data.balancedCertificate (U.map e) (V.map e)) ≠ 0 := by
    change circlePairing (fourierPolynomial A)
      (fun x ↦ (∏ i ∈ U.map e, data.certificate i x) *
        ∏ i ∈ V.map e, conj (data.certificate i x)) ≠ 0
    simpa only [Finset.prod_map] using hne
  obtain ⟨j, hj⟩ := data.balanced_pairing_label_witness (U.map e) (V.map e)
    (by simpa using hk) hp
  exact ⟨j, by simpa only [Finset.sum_map, Finset.card_map] using hj⟩

/-- Hereditary label energy for every subset, with the original full target
and one fixed certificate budget. This is Proposition 6.3 of the manuscript. -/
theorem label_hereditary_energy {β Δ : ℝ} {A : Finset ℤ}
    (data : DenseBlocks β Δ A) {κ T : ℝ} (hκ : 0 < κ) (hT : 1 ≤ T)
    (hlin : ∀ i, κ ≤ (circlePairing (fourierPolynomial A) (data.certificate i)).re)
    (hL : littlewoodNorm A ≤ T * κ)
    (S : Finset ℤ) (hS : S ⊆ data.labels) (hSne : S.Nonempty) :
    Real.exp (-2000 * T ^ 2) * (S.card : ℝ) ^ 4 ≤
      (additiveEnergy S : ℝ) * (data.labels.card : ℝ) := by
  classical
  by_cases hsmall : S.card < Majority.majorityDegree T
  · exact PacketEnergy.exponential_energy_small_set S data.labels hS hT hsmall
  let I := data.indexSet S
  let e : I ↪ Fin data.count := Function.Embedding.subtype (· ∈ I)
  let Φ : I → Circle → ℂ := fun i ↦ data.certificate (e i)
  have hcard : Fintype.card I = S.card := by
    rw [Fintype.card_coe]
    exact data.indexSet_card hS
  obtain ⟨t, ht, htm, hmany⟩ := Majority.dense_mixed_correlations
    (fourierPolynomial_integrable A) Φ
    (fun i ↦ (data.certificate_continuous (e i)).aestronglyMeasurable)
    (fun i ↦ Filter.Eventually.of_forall (data.certificate_norm_le (e i)))
    hκ hT (fun i ↦ hlin (e i)) hL
    (by rw [hcard]; omega)
  let η := Real.exp (-300 * T ^ 2) * κ
  let Q := MajorityCounting.orderedPairs (t + 1) t
    (Majority.BalancedCorrelation (fourierPolynomial A) Φ η)
  have hQ : (Q.card : ℝ) ≤ ∑ n ∈ PacketEnergy.carryRange ((t + 1) + t),
      (PacketEnergy.shiftedRelationCount S data.labels (t + 1) t n : ℝ) := by
    have hc := PacketEnergy.ordered_count_le_relations S data.labels (t + 1) t
      (fun i : I ↦ data.label (e i))
      (fun i j hij ↦ e.injective (data.label_injective hij))
      (fun i ↦ (Finset.mem_filter.mp i.property).2) Q ?_
    · exact_mod_cast hc
    · intro v hv
      have hv' : MajorityCounting.ValidOrderedPair
          (Majority.BalancedCorrelation (fourierPolynomial A) Φ η) v :=
        (Finset.mem_filter.mp hv).2
      have hp : (MajorityCounting.tupleSupport v.1).card = t + 1 := by
        simp [MajorityCounting.tupleSupport, Finset.card_image_of_injective _ hv'.1]
      have hm : (MajorityCounting.tupleSupport v.2).card = t := by
        simp [MajorityCounting.tupleSupport, Finset.card_image_of_injective _ hv'.2.1]
      have hcorr := hv'.2.2.2
      have hne : circlePairing (fourierPolynomial A)
          (fun x ↦ (∏ i ∈ MajorityCounting.tupleSupport v.1, data.certificate (e i) x) *
            ∏ i ∈ MajorityCounting.tupleSupport v.2, conj (data.certificate (e i) x)) ≠ 0 := by
        apply norm_ne_zero_iff.mp
        have hη : 0 < η := by dsimp [η]; positivity
        exact ne_of_gt (hη.trans_le hcorr)
      obtain ⟨j, hj⟩ := data.balanced_pairing_label_witness_reindex e
        (MajorityCounting.tupleSupport v.1) (MajorityCounting.tupleSupport v.2)
        (by rw [hp, hm]; omega) hne
      refine ⟨data.label j, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
      rw [hp, hm] at hj
      have hsum1 : (∑ i ∈ MajorityCounting.tupleSupport v.1, data.label (e i)) =
          ∑ i, data.label (e (v.1 i)) := by
        exact Finset.sum_image (fun i _ j _ hij ↦ hv'.1 hij)
      have hsum2 : (∑ i ∈ MajorityCounting.tupleSupport v.2, data.label (e i)) =
          ∑ i, data.label (e (v.2 i)) := by
        exact Finset.sum_image (fun i _ j _ hij ↦ hv'.2.1 hij)
      rw [hsum1, hsum2] at hj
      simpa only [Nat.cast_add] using hj
  apply PacketEnergy.exponential_energy_from_relations S data.labels hSne
    (t + 1) t (by omega) hT (by omega)
  have he : (t + 1) + t = 2 * t + 1 := by omega
  rw [he] at hQ ⊢
  rw [hcard] at hmany
  exact hmany.trans hQ

end DenseBlocks
end LittlewoodInverse
