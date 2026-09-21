import LittlewoodInverse.FiniteBand
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # The bounded Boolean majority polynomial used in Lemma 6.1 -/

open scoped BigOperators

namespace LittlewoodInverse
namespace Majority

noncomputable def sign {m : ℕ} (P : Finset (Fin m)) (i : Fin m) : ℝ :=
  if i ∈ P then 1 else -1

noncomputable def majority {m : ℕ} (P : Finset (Fin m)) : ℝ :=
  if m < 2 * P.card then 1 else -1

noncomputable def walsh {m : ℕ} (S P : Finset (Fin m)) : ℝ :=
  ∏ i ∈ S, sign P i

noncomputable def coefficient {m : ℕ} (S : Finset (Fin m)) : ℝ :=
  (∑ P : Finset (Fin m), majority P * walsh S P) / (2 : ℝ) ^ m

noncomputable def polynomial {m : ℕ} (t : Fin m → ℝ) : ℝ :=
  ∑ S : Finset (Fin m), coefficient S * ∏ i ∈ S, t i

noncomputable def bernoulliWeight {m : ℕ} (t : Fin m → ℝ) (P : Finset (Fin m)) : ℝ :=
  (∏ i ∈ P, (1 + t i) / 2) * ∏ i ∈ Pᶜ, (1 - t i) / 2

theorem abs_majority {m : ℕ} (P : Finset (Fin m)) : |majority P| = 1 := by
  unfold majority
  split_ifs <;> norm_num

theorem abs_sign {m : ℕ} (P : Finset (Fin m)) (i : Fin m) : |sign P i| = 1 := by
  unfold sign
  split_ifs <;> norm_num

theorem abs_walsh {m : ℕ} (S P : Finset (Fin m)) : |walsh S P| = 1 := by
  simp only [walsh, Finset.abs_prod, abs_sign, Finset.prod_const_one]

theorem bernoulliWeight_nonneg {m : ℕ} {t : Fin m → ℝ}
    (ht : ∀ i, |t i| ≤ 1) (P : Finset (Fin m)) : 0 ≤ bernoulliWeight t P := by
  unfold bernoulliWeight
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro i hi
    have := abs_le.mp (ht i)
    exact div_nonneg (by linarith) (by norm_num)
  · apply Finset.prod_nonneg
    intro i hi
    have := abs_le.mp (ht i)
    exact div_nonneg (by linarith) (by norm_num)

theorem sum_bernoulliWeight {m : ℕ} (t : Fin m → ℝ) :
    (∑ P : Finset (Fin m), bernoulliWeight t P) = 1 := by
  unfold bernoulliWeight
  rw [← Fintype.prod_add]
  have h (i : Fin m) : (1 + t i) / 2 + (1 - t i) / 2 = 1 := by ring
  simp only [h, Finset.prod_const_one]

theorem bernoulliWeight_eq_product {m : ℕ} (t : Fin m → ℝ) (P : Finset (Fin m)) :
    bernoulliWeight t P = (∏ i, (1 + sign P i * t i)) / (2 : ℝ) ^ m := by
  have he : (∏ i, (1 + sign P i * t i)) =
      (∏ i ∈ P, (1 + t i)) * ∏ i ∈ Pᶜ, (1 - t i) := by
    rw [← Finset.prod_mul_prod_compl P]
    congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      simp only [sign, hi, if_true, one_mul]
    · apply Finset.prod_congr rfl
      intro i hi
      have hni : i ∉ P := Finset.mem_compl.mp hi
      simp only [sign, hni, if_false, neg_one_mul, sub_eq_add_neg]
  unfold bernoulliWeight
  rw [he]
  simp only [Finset.prod_div_distrib, Finset.prod_const, ← mul_div_mul_comm,
    ← pow_add, Finset.card_add_card_compl, Fintype.card_fin]

theorem polynomial_eq_expectation {m : ℕ} (t : Fin m → ℝ) :
    polynomial t = ∑ P : Finset (Fin m), majority P * bernoulliWeight t P := by
  have hp (P : Finset (Fin m)) : (∏ i, (1 + sign P i * t i)) =
      ∑ S : Finset (Fin m), walsh S P * ∏ i ∈ S, t i := by
    simp_rw [add_comm (1 : ℝ), Fintype.prod_add]
    simp only [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, walsh]
  simp_rw [bernoulliWeight_eq_product, hp, Finset.sum_div, Finset.mul_sum]
  unfold polynomial coefficient
  simp only [div_mul_eq_mul_div, Finset.sum_mul, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P hP
  apply Finset.sum_congr rfl
  intro S hS
  ring

theorem polynomial_abs_le_one {m : ℕ} {t : Fin m → ℝ}
    (ht : ∀ i, |t i| ≤ 1) : |polynomial t| ≤ 1 := by
  rw [polynomial_eq_expectation]
  calc
    _ ≤ ∑ P : Finset (Fin m), |majority P * bernoulliWeight t P| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ P : Finset (Fin m), bernoulliWeight t P := by
      apply Finset.sum_congr rfl
      intro P hP
      rw [abs_mul, abs_majority, one_mul, abs_of_nonneg (bernoulliWeight_nonneg ht P)]
    _ = 1 := sum_bernoulliWeight t

def complementEquiv (m : ℕ) : Equiv.Perm (Finset (Fin m)) where
  toFun := fun P ↦ Pᶜ
  invFun := fun P ↦ Pᶜ
  left_inv := compl_compl
  right_inv := compl_compl

theorem majority_compl {m : ℕ} (hm : Odd m) (P : Finset (Fin m)) :
    majority Pᶜ = -majority P := by
  have hp : P.card ≤ m := (Finset.card_le_univ P).trans_eq (Fintype.card_fin m)
  obtain ⟨q, hq⟩ := hm
  simp only [majority, Finset.card_compl, Fintype.card_fin]
  split_ifs <;> norm_num <;> omega

theorem sign_compl {m : ℕ} (P : Finset (Fin m)) (i : Fin m) :
    sign Pᶜ i = -sign P i := by
  simp only [sign, Finset.mem_compl]
  split_ifs <;> norm_num

theorem walsh_compl {m : ℕ} (S P : Finset (Fin m)) :
    walsh S Pᶜ = (-1 : ℝ) ^ S.card * walsh S P := by
  simp only [walsh, sign_compl, Finset.prod_neg]

theorem coefficient_even_eq_zero {m : ℕ} (hm : Odd m) (S : Finset (Fin m))
    (hS : Even S.card) : coefficient S = 0 := by
  have he := Equiv.sum_comp (complementEquiv m) (fun P ↦ majority P * walsh S P)
  change (∑ P : Finset (Fin m), majority Pᶜ * walsh S Pᶜ) = _ at he
  simp only [majority_compl hm, walsh_compl, hS.neg_one_pow, one_mul,
    neg_mul, Finset.sum_neg_distrib] at he
  have hz : (∑ P : Finset (Fin m), majority P * walsh S P) = 0 := by linarith
  simp only [coefficient, hz, zero_div]

theorem abs_coefficient_le_one {m : ℕ} (S : Finset (Fin m)) : |coefficient S| ≤ 1 := by
  have hd : (0 : ℝ) < 2 ^ m := by positivity
  rw [coefficient, abs_div, abs_of_pos hd, div_le_one hd]
  calc
    _ ≤ ∑ P : Finset (Fin m), |majority P * walsh S P| := Finset.abs_sum_le_sum_abs _ _
    _ = (2 : ℝ) ^ m := by simp [abs_mul, abs_majority, abs_walsh]

/-- An exponential Walsh mass bound sufficient for the quantitative lemma.
The sharper Parseval estimate is not needed for the unspecified absolute constant. -/
theorem coefficient_mass_le {m : ℕ} :
    (∑ S : Finset (Fin m), |coefficient S|) ≤ (2 : ℝ) ^ m := by
  calc
    _ ≤ ∑ _S : Finset (Fin m), (1 : ℝ) :=
      Finset.sum_le_sum (fun S _ ↦ abs_coefficient_le_one S)
    _ = _ := by simp

theorem coefficient_singleton (q : ℕ) (j : Fin (2 * q + 1)) :
    coefficient ({j} : Finset (Fin (2 * q + 1))) =
      (Nat.centralBinom q : ℝ) / (4 : ℝ) ^ q := by
  let U : Finset (Fin (2 * q + 1)) := Finset.univ.erase j
  have hjU : j ∉ U := Finset.notMem_erase j Finset.univ
  have hU : U.card = 2 * q := by
    simp [U]
  have hsplit : (∑ P : Finset (Fin (2 * q + 1)), majority P * walsh {j} P) =
      ∑ P ∈ U.powerset,
        (majority P * walsh {j} P + majority (insert j P) * walsh {j} (insert j P)) := by
    rw [Finset.sum_add_distrib]
    rw [← Finset.sum_powerset_insert hjU]
    simp [U]
  have hp (P : Finset (Fin (2 * q + 1))) (hP : P ∈ U.powerset) :
      majority P * walsh {j} P + majority (insert j P) * walsh {j} (insert j P) =
        if P.card = q then 2 else 0 := by
    have hjP : j ∉ P := fun hj ↦ hjU (Finset.mem_powerset.mp hP hj)
    simp only [walsh, Finset.prod_singleton, sign, hjP, if_false,
      Finset.mem_insert_self, if_true, mul_neg_one, mul_one, majority,
      Finset.card_insert_of_notMem hjP]
    split_ifs <;> norm_num <;> omega
  have hcard : (U.powerset.filter (fun P ↦ P.card = q)).card = Nat.centralBinom q := by
    rw [← Finset.powersetCard_eq_filter, Finset.card_powersetCard, hU]
    rfl
  have hsum : (∑ P : Finset (Fin (2 * q + 1)), majority P * walsh {j} P) =
      2 * (Nat.centralBinom q : ℝ) := by
    rw [hsplit]
    calc
      _ = ∑ P ∈ U.powerset, if P.card = q then (2 : ℝ) else 0 :=
        Finset.sum_congr rfl hp
      _ = 2 * (Nat.centralBinom q : ℝ) := by
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul, hcard]
        ring
  rw [coefficient, hsum, pow_add, pow_mul]
  norm_num
  ring

/-- An elementary squared central-binomial bound, proved from the exact
successor recurrence. It implies the lower bound used in the manuscript. -/
theorem centralBinom_squared_lower (q : ℕ) :
    (16 : ℝ) ^ q ≤ (4 * (q : ℝ) + 1) * (Nat.centralBinom q : ℝ) ^ 2 := by
  induction q with
  | zero => norm_num
  | succ q ih =>
    have hc : ((q : ℝ) + 1) * (Nat.centralBinom (q + 1) : ℝ) =
        2 * (2 * (q : ℝ) + 1) * (Nat.centralBinom q : ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ q
    have hs := congrArg (fun x : ℝ ↦ x ^ 2) hc
    have hmul : ((q : ℝ) + 1) ^ 2 * (16 : ℝ) ^ (q + 1) ≤
        ((q : ℝ) + 1) ^ 2 *
          ((4 * ((q : ℝ) + 1) + 1) * (Nat.centralBinom (q + 1) : ℝ) ^ 2) := by
      calc
        _ = (16 * ((q : ℝ) + 1) ^ 2) * (16 : ℝ) ^ q := by rw [pow_succ]; ring
        _ ≤ (16 * ((q : ℝ) + 1) ^ 2) *
            ((4 * (q : ℝ) + 1) * (Nat.centralBinom q : ℝ) ^ 2) := by gcongr
        _ ≤ (4 * (2 * (q : ℝ) + 1) ^ 2) *
            (4 * ((q : ℝ) + 1) + 1) * (Nat.centralBinom q : ℝ) ^ 2 := by
          nlinarith [sq_nonneg (Nat.centralBinom q : ℝ)]
        _ = _ := by linear_combination -(4 * ((q : ℝ) + 1) + 1) * hs
    have hq : 0 < ((q : ℝ) + 1) ^ 2 := by positivity
    exact_mod_cast (mul_le_mul_iff_right₀ hq).mp hmul

theorem normalized_centralBinom_squared_lower (q : ℕ) :
    1 ≤ (4 * (q : ℝ) + 1) * ((Nat.centralBinom q : ℝ) / (4 : ℝ) ^ q) ^ 2 := by
  have hd : (0 : ℝ) < ((4 : ℝ) ^ q) ^ 2 := by positivity
  rw [div_pow, ← mul_div_assoc, le_div_iff₀ hd, one_mul]
  have he : ((4 : ℝ) ^ q) ^ 2 = (16 : ℝ) ^ q := by
    rw [← pow_mul, mul_comm q 2, pow_mul]
    norm_num
  rw [he]
  exact centralBinom_squared_lower q

theorem linear_amplitude_nonneg (q : ℕ) :
    0 ≤ (2 * (q : ℝ) + 1) * ((Nat.centralBinom q : ℝ) / (4 : ℝ) ^ q) := by positivity

theorem linear_amplitude_squared_lower (q : ℕ) :
    (2 * (q : ℝ) + 1) / 2 ≤
      ((2 * (q : ℝ) + 1) * ((Nat.centralBinom q : ℝ) / (4 : ℝ) ^ q)) ^ 2 := by
  have hh := normalized_centralBinom_squared_lower q
  have hm := mul_le_mul_of_nonneg_left hh
    (by positivity : 0 ≤ (2 * (q : ℝ) + 1) / 2)
  nlinarith [sq_nonneg ((Nat.centralBinom q : ℝ) / (4 : ℝ) ^ q),
    mul_nonneg (show 0 ≤ (q : ℝ) by positivity)
      (sq_nonneg ((Nat.centralBinom q : ℝ) / (4 : ℝ) ^ q))]

theorem linear_amplitude_ge_four_mul {q : ℕ} {T : ℝ}
    (hT : 0 ≤ T) (hm : 64 * T ^ 2 ≤ 2 * (q : ℝ) + 1) :
    4 * T ≤ (2 * (q : ℝ) + 1) * ((Nat.centralBinom q : ℝ) / (4 : ℝ) ^ q) := by
  have h1 := linear_amplitude_squared_lower q
  have h2 := linear_amplitude_nonneg q
  nlinarith

end Majority
end LittlewoodInverse
