import LittlewoodInverse.PacketCertificates
import LittlewoodInverse.LabelGeometry
import LittlewoodInverse.OuterDamping

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LittlewoodInverse

/-- A concrete Fourier support interval, described by centre and radius. -/
def SpectrumIn (f : Circle → ℂ) (c R : ℤ) : Prop :=
  ∀ n : ℤ, R < |n-c| → circleFourierCoeff f n = 0

theorem circleFourierCoeff_mul_eq_tsum {f g : Circle → ℂ}
    (hf : MemLp f 2 circleMeasure) (hg : MemLp g 2 circleMeasure) (k : ℤ) :
    circleFourierCoeff (fun t => f t * g t) k =
      ∑' n : ℤ, circleFourierCoeff f (-n) * circleFourierCoeff g (n+k) := by
  have hc : MemLp (fun t => conj (f t)) 2 circleMeasure :=
    hf.continuousLinearMap_comp Complex.conjCLE.toContinuousLinearMap
  have hh := hasSum_conj_circleFourierCoeff_mul hc (memLp_mul_fourier hg (-k))
  simp only [circleFourierCoeff_conj, Complex.conj_conj,
    circleFourierCoeff_mul_fourier, sub_neg_eq_add] at hh
  simpa only [circleFourierCoeff, mul_assoc] using hh.tsum_eq.symm

theorem spectrumIn_mul {f g : Circle → ℂ} {c d R S : ℤ}
    (hf : MemLp f 2 circleMeasure) (hg : MemLp g 2 circleMeasure)
    (hfs : SpectrumIn f c R) (hgs : SpectrumIn g d S) :
    SpectrumIn (fun t => f t * g t) (c+d) (R+S) := by
  intro k hk
  rw [circleFourierCoeff_mul_eq_tsum hf hg]
  have hz (n : ℤ) : circleFourierCoeff f (-n) * circleFourierCoeff g (n+k) = 0 := by
    by_cases hfr : R < |-n-c|
    · rw [hfs (-n) hfr, zero_mul]
    · have hgr : S < |(n+k)-d| := by
        by_contra hh
        have hf' := le_of_not_gt hfr
        have hg' := le_of_not_gt hh
        have htri := abs_add_le (-n-c) ((n+k)-d)
        have he : -n-c+((n+k)-d) = k-(c+d) := by ring
        rw [he] at htri
        omega
      rw [hgs (n+k) hgr, mul_zero]
  simp only [hz, tsum_zero]

theorem spectrumIn_conj {f : Circle → ℂ} {c R : ℤ} (hf : SpectrumIn f c R) :
    SpectrumIn (fun t => conj (f t)) (-c) R := by
  intro n hn
  rw [circleFourierCoeff_conj, hf (-n), map_zero]
  have he : -n-c = -(n- -c) := by ring
  simpa only [he, abs_neg] using hn

theorem spectrumIn_one : SpectrumIn (fun _ : Circle => (1 : ℂ)) 0 0 := by
  intro n hn
  have hn0 : n ≠ 0 := by intro h; simp [h] at hn
  simp only [circleFourierCoeff, one_mul, integral_fourier,
    neg_eq_zero, hn0, if_false]

theorem spectrumIn_prod {ι : Type*} (I : Finset ι) (f : ι → Circle → ℂ)
    (c R : ι → ℤ) (hm : ∀ i ∈ I, MemLp (f i) ⊤ circleMeasure)
    (hs : ∀ i ∈ I, SpectrumIn (f i) (c i) (R i)) :
    SpectrumIn (fun t => ∏ i ∈ I, f i t) (∑ i ∈ I, c i) (∑ i ∈ I, R i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, Finset.sum_empty] using spectrumIn_one
  | @insert i I hi ih =>
    have hm' := fun j hj => hm j (Finset.mem_insert_of_mem hj)
    have hs' := fun j hj => hs j (Finset.mem_insert_of_mem hj)
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    exact spectrumIn_mul ((hm i (Finset.mem_insert_self i I)).mono_exponent le_top)
      ((memLp_finset_prod_top I hm').mono_exponent le_top)
      (hs i (Finset.mem_insert_self i I)) (ih hm' hs')

theorem finset_floor_error {ι : Type*} (D : ℤ) (hD : 0 < D) (s : Finset ι) (b : ι → ℤ) :
    0 ≤ (∑ i ∈ s, b i) - D * (∑ i ∈ s, b i / D) ∧
      (∑ i ∈ s, b i) - D * (∑ i ∈ s, b i / D) ≤ (s.card : ℤ) * D := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have he := Int.emod_add_mul_ediv (b i) D
    have h0 := Int.emod_nonneg (b i) hD.ne'
    have hlt := Int.emod_lt_of_pos (b i) hD
    simp only [Finset.sum_insert hi, Finset.card_insert_of_notMem hi,
      Nat.cast_add, Nat.cast_one]
    constructor <;> nlinarith

theorem bounded_finset_floor_carry {ι : Type*} (D : ℤ) (hD : 0 < D)
    (p m : Finset ι) (b : ι → ℤ) (c : ℤ) (hk : 2 ≤ p.card + m.card)
    (hclose : |(∑ i ∈ p, b i) - (∑ i ∈ m, b i) - c| ≤
      (2*((p.card : ℤ)+m.card)+1)*D) :
    |(∑ i ∈ p, b i / D) - (∑ i ∈ m, b i / D) - c/D| ≤
      4*((p.card : ℤ)+m.card) := by
  have hp := finset_floor_error D hD p b
  have hm := finset_floor_error D hD m b
  have hc := Int.emod_add_mul_ediv c D
  have hc0 := Int.emod_nonneg c hD.ne'
  have hcD := Int.emod_lt_of_pos c hD
  have hkl : (2 : ℤ) ≤ (p.card : ℤ)+m.card := by exact_mod_cast hk
  have hp0 : (0 : ℤ) ≤ p.card := Int.natCast_nonneg _
  have hm0 : (0 : ℤ) ≤ m.card := Int.natCast_nonneg _
  have hsmall : (3*((p.card : ℤ)+m.card)+2)*D ≤ 4*((p.card : ℤ)+m.card)*D := by
    nlinarith
  apply abs_le.mpr
  constructor
  · apply (mul_le_mul_iff_of_pos_left hD).mp
    have hb := (abs_le.mp hclose).1
    nlinarith [mul_nonneg hp0 hD.le, mul_nonneg hm0 hD.le]
  · apply (mul_le_mul_iff_of_pos_left hD).mp
    have hb := (abs_le.mp hclose).2
    nlinarith [mul_nonneg hp0 hD.le, mul_nonneg hm0 hD.le]

namespace DenseBlocks

theorem certificate_spectrum {β Δ : ℝ} {A : Finset ℤ} (data : DenseBlocks β Δ A)
    (i : Fin data.count) : SpectrumIn (data.certificate i) (data.centre i) (2*data.radius) := by
  intro n hn
  rw [data.certificate_coeff]
  exact finiteBandCertificate_support _ _ hn

theorem certificate_memLp {β Δ : ℝ} {A : Finset ℤ} (data : DenseBlocks β Δ A)
    (i : Fin data.count) : MemLp (data.certificate i) ⊤ circleMeasure :=
  (data.certificate_continuous i).memLp_top_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) circleMeasure

noncomputable def balancedCertificate {β Δ : ℝ} {A : Finset ℤ}
    (data : DenseBlocks β Δ A) (p m : Finset (Fin data.count)) (t : Circle) : ℂ :=
  (∏ i ∈ p, data.certificate i t) * ∏ i ∈ m, conj (data.certificate i t)

theorem balancedCertificate_continuous {β Δ : ℝ} {A : Finset ℤ}
    (data : DenseBlocks β Δ A) (p m : Finset (Fin data.count)) :
    Continuous (data.balancedCertificate p m) := by
  unfold balancedCertificate
  apply Continuous.mul
  · exact continuous_finsetProd _ (fun i _ => data.certificate_continuous i)
  · exact continuous_finsetProd _ (fun i _ =>
      Complex.continuous_conj.comp (data.certificate_continuous i))

theorem balancedCertificate_spectrum {β Δ : ℝ} {A : Finset ℤ}
    (data : DenseBlocks β Δ A) (p m : Finset (Fin data.count)) :
    SpectrumIn (data.balancedCertificate p m)
      ((∑ i ∈ p, data.centre i) - ∑ i ∈ m, data.centre i)
      (2*((p.card : ℤ)+m.card)*data.radius) := by
  have hp := spectrumIn_prod p data.certificate data.centre (fun _ => 2*data.radius)
    (fun i _ => data.certificate_memLp i) (fun i _ => data.certificate_spectrum i)
  have hm := spectrumIn_prod m (fun i t => conj (data.certificate i t))
    (fun i => -data.centre i) (fun _ => 2*data.radius)
    (fun i _ => (data.certificate_memLp i).continuousLinearMap_comp
      Complex.conjCLE.toContinuousLinearMap)
    (fun i _ => spectrumIn_conj (data.certificate_spectrum i))
  have hpLp := memLp_finset_prod_top p (fun i _ => data.certificate_memLp i)
  have hmLp := memLp_finset_prod_top m (fun i _ =>
    (data.certificate_memLp i).continuousLinearMap_comp Complex.conjCLE.toContinuousLinearMap)
  have hh := spectrumIn_mul (hpLp.mono_exponent le_top) (hmLp.mono_exponent le_top) hp hm
  simp only [Finset.sum_neg_distrib, Finset.sum_const, nsmul_eq_mul] at hh
  convert hh using 1
  · rfl
  · ring
  · ring

/-- The witness comes from the full target, including blocks outside the
chosen index set. No Fourier support assumption is left to the caller. -/
theorem balanced_pairing_witness {β Δ : ℝ} {A : Finset ℤ}
    (data : DenseBlocks β Δ A) (p m : Finset (Fin data.count))
    (hne : circlePairing (fourierPolynomial A) (data.balancedCertificate p m) ≠ 0) :
    ∃ j : Fin data.count,
      |(∑ i ∈ p, data.centre i) - (∑ i ∈ m, data.centre i) - data.centre j| ≤
        (2*((p.card : ℤ)+m.card)+1)*data.radius := by
  have hi := continuous_circle_integrable (data.balancedCertificate_continuous p m)
  have hp := circlePairing_indexedFourierSum A id hi
  change circlePairing (fourierPolynomial A) _ = _ at hp
  rw [hp] at hne
  obtain ⟨x, hx, hcoeff⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hcoeff' : circleFourierCoeff (data.balancedCertificate p m) x ≠ 0 := by
    simpa only [id_eq, map_ne_zero] using hcoeff
  have hfreq : |x - ((∑ i ∈ p, data.centre i) - ∑ i ∈ m, data.centre i)| ≤
      2*((p.card : ℤ)+m.card)*data.radius := by
    by_contra hh
    exact hcoeff' (data.balancedCertificate_spectrum p m x (lt_of_not_ge hh))
  rw [data.exact_union] at hx
  obtain ⟨j, _, hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
  simp only [one_mul] at he
  have hyb := data.block_mem j y hy
  have hxf : |((∑ i ∈ p, data.centre i) - ∑ i ∈ m, data.centre i)-x| ≤
      2*((p.card : ℤ)+m.card)*data.radius := by rwa [abs_sub_comm]
  refine ⟨j, ?_⟩
  have htri := abs_add_le
    (((∑ i ∈ p, data.centre i) - ∑ i ∈ m, data.centre i)-x) (x-data.centre j)
  have hxy : |x-data.centre j| ≤ data.radius := by
    rw [← he]
    simpa only [add_sub_cancel_left] using (abs_le.mpr hyb)
  have heq : ((∑ i ∈ p, data.centre i) - ∑ i ∈ m, data.centre i)-x+
      (x-data.centre j) = (∑ i ∈ p, data.centre i) -
        (∑ i ∈ m, data.centre i)-data.centre j := by ring
  rw [heq] at htri
  nlinarith

theorem balanced_pairing_label_witness {β Δ : ℝ} {A : Finset ℤ}
    (data : DenseBlocks β Δ A) (p m : Finset (Fin data.count))
    (hk : 2 ≤ p.card+m.card)
    (hne : circlePairing (fourierPolynomial A) (data.balancedCertificate p m) ≠ 0) :
    ∃ j : Fin data.count,
      |(∑ i ∈ p, data.label i) - (∑ i ∈ m, data.label i) - data.label j| ≤
        4*((p.card : ℤ)+m.card) := by
  obtain ⟨j, hj⟩ := data.balanced_pairing_witness p m hne
  exact ⟨j, bounded_finset_floor_carry data.radius
    (by exact_mod_cast data.radius_pos) p m data.centre (data.centre j) hk hj⟩

end DenseBlocks
end LittlewoodInverse
