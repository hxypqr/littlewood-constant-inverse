import Mathlib

/-!
# Constructive symmetric chains

The rectangle construction in Lemma 3.1 of the manuscript is encoded by
an explicit equivalence.  Chain coordinates increase the ordinary rank
by exactly one at every step.
-/

namespace LittlewoodInverse
namespace SymmetricChains

open scoped BigOperators

/-- A partition into monotone saturated chains with symmetric endpoints.
The equivalence records disjointness and complete coverage, and `rank_eq`
records that every intermediate rank occurs exactly once in each chain. -/
structure Decomposition (α : Type) [Preorder α] (rank : α → ℕ) (R : ℕ) where
  Index : Type
  finiteIndex : Fintype Index
  start : Index → ℕ
  length : Index → ℕ
  equiv : ((i : Index) × Fin (length i + 1)) ≃ α
  symmetric : ∀ i, 2 * start i + length i = R
  rank_eq : ∀ i k, rank (equiv ⟨i, k⟩) = start i + k.val
  monotone : ∀ i, Monotone (fun k => equiv ⟨i, k⟩)

abbrev Rectangle (p q : ℕ) := Fin (p + 1) × Fin (q + 1)
abbrev WideChains (p q : ℕ) := (j : Fin (q + 1)) × Fin (p + q - 2 * j.val + 1)

def wideEncode (p q : ℕ) (z : Rectangle p q) : WideChains p q :=
  ⟨⟨min z.2.val (p - z.1.val), by have := z.2.isLt; omega⟩,
    ⟨z.1.val + z.2.val - min z.2.val (p - z.1.val), by
      have := z.1.isLt
      have := z.2.isLt
      dsimp only
      omega⟩⟩

def wideDecode (p q : ℕ) (hpq : q ≤ p) (z : WideChains p q) : Rectangle p q :=
  (⟨min z.2.val (p - z.1.val), by omega⟩,
    ⟨z.1.val + (z.2.val - (p - z.1.val)), by
      have := z.1.isLt
      have := z.2.isLt
      omega⟩)

theorem wideDecode_rank (p q : ℕ) (hpq : q ≤ p) (z : WideChains p q) :
    (wideDecode p q hpq z).1.val + (wideDecode p q hpq z).2.val =
      z.1.val + z.2.val := by
  dsimp [wideDecode]
  omega

theorem wideDecode_index (p q : ℕ) (hpq : q ≤ p) (z : WideChains p q) :
    min (wideDecode p q hpq z).2.val (p - (wideDecode p q hpq z).1.val) = z.1.val := by
  dsimp [wideDecode]
  have := z.1.isLt
  omega

theorem wideDecode_encode (p q : ℕ) (hpq : q ≤ p) (z : Rectangle p q) :
    wideDecode p q hpq (wideEncode p q z) = z := by
  apply Prod.ext <;> apply Fin.ext <;> dsimp [wideDecode, wideEncode]
  all_goals have := z.1.isLt; have := z.2.isLt; omega

theorem wideEncode_decode (p q : ℕ) (hpq : q ≤ p) (z : WideChains p q) :
    wideEncode p q (wideDecode p q hpq z) = z := by
  have hj : (wideEncode p q (wideDecode p q hpq z)).1 = z.1 := by
    apply Fin.ext
    exact wideDecode_index p q hpq z
  apply Sigma.ext hj
  apply (Fin.heq_ext_iff (congrArg (fun j : Fin (q + 1) => p + q - 2 * j.val + 1) hj)).mpr
  change (wideDecode p q hpq z).1.val + (wideDecode p q hpq z).2.val -
    min (wideDecode p q hpq z).2.val (p - (wideDecode p q hpq z).1.val) = z.2.val
  rw [wideDecode_rank, wideDecode_index]
  omega

def wideEquiv (p q : ℕ) (hpq : q ≤ p) : Rectangle p q ≃ WideChains p q where
  toFun := wideEncode p q
  invFun := wideDecode p q hpq
  left_inv := wideDecode_encode p q hpq
  right_inv := wideEncode_decode p q hpq

theorem wideDecode_monotone (p q : ℕ) (hpq : q ≤ p) (j : Fin (q + 1)) :
    Monotone (fun k : Fin (p + q - 2 * j.val + 1) => wideDecode p q hpq ⟨j, k⟩) := by
  intro k l hkl
  constructor
  · change min k.val (p - j.val) ≤ min l.val (p - j.val)
    exact min_le_min_right _ hkl
  · change j.val + (k.val - (p - j.val)) ≤ j.val + (l.val - (p - j.val))
    exact Nat.add_le_add_left (Nat.sub_le_sub_right hkl _) _

def rectangleDecomposition (p q : ℕ) :
    Decomposition (Rectangle p q) (fun z => z.1.val + z.2.val) (p + q) := by
  by_cases hpq : q ≤ p
  · exact {
      Index := Fin (q + 1)
      finiteIndex := inferInstance
      start := Fin.val
      length := fun j => p + q - 2 * j.val
      equiv := (wideEquiv p q hpq).symm
      symmetric := fun j => by have := j.isLt; omega
      rank_eq := fun j k => wideDecode_rank p q hpq ⟨j, k⟩
      monotone := wideDecode_monotone p q hpq }
  · have hqp : p ≤ q := by omega
    exact {
      Index := Fin (p + 1)
      finiteIndex := inferInstance
      start := Fin.val
      length := fun j => q + p - 2 * j.val
      equiv := (wideEquiv q p hqp).symm.trans (Equiv.prodComm _ _)
      symmetric := fun j => by have := j.isLt; omega
      rank_eq := fun j k => by
        have h := wideDecode_rank q p hqp ⟨j, k⟩
        dsimp only at h
        change (wideDecode q p hqp ⟨j, k⟩).2.val +
          (wideDecode q p hqp ⟨j, k⟩).1.val = j.val + k.val
        omega
      monotone := fun j k l hkl => by
        have h := wideDecode_monotone q p hqp j hkl
        exact ⟨h.2, h.1⟩ }

def Decomposition.prodChain {α : Type} [Preorder α] {rank : α → ℕ} {R : ℕ}
    (D : Decomposition α rank R) (q : ℕ) :
    Decomposition (α × Fin (q + 1)) (fun z => rank z.1 + z.2.val) (R + q) := by
  let E := fun i : D.Index => rectangleDecomposition (D.length i) q
  letI := D.finiteIndex
  letI : (i : D.Index) → Fintype (E i).Index := fun i => (E i).finiteIndex
  let e := (Equiv.sigmaAssoc (fun i j => Fin ((E i).length j + 1))).trans
    ((Equiv.sigmaCongrRight (fun i => (E i).equiv)).trans
      ((Equiv.sigmaProdDistrib (fun i => Fin (D.length i + 1)) (Fin (q + 1))).symm.trans
        (Equiv.prodCongr D.equiv (Equiv.refl _))))
  exact {
    Index := (i : D.Index) × (E i).Index
    finiteIndex := inferInstance
    start := fun ij => D.start ij.1 + (E ij.1).start ij.2
    length := fun ij => (E ij.1).length ij.2
    equiv := e
    symmetric := fun ⟨i, j⟩ => by
      have hD := D.symmetric i
      have hE := (E i).symmetric j
      dsimp only
      omega
    rank_eq := fun ⟨i, j⟩ k => by
      change rank (D.equiv ⟨i, ((E i).equiv ⟨j, k⟩).1⟩) +
        ((E i).equiv ⟨j, k⟩).2.val = D.start i + (E i).start j + k.val
      rw [D.rank_eq]
      have hE := (E i).rank_eq j k
      omega
    monotone := fun ⟨i, j⟩ k l hkl => by
      have hE := (E i).monotone j hkl
      exact ⟨D.monotone i hE.1, hE.2⟩ }

def Decomposition.map {α β : Type} [Preorder α] [Preorder β]
    {rankA : α → ℕ} {rankB : β → ℕ} {R : ℕ}
    (D : Decomposition α rankA R) (e : α ≃ β) (he : Monotone e)
    (hrank : ∀ x, rankB (e x) = rankA x) : Decomposition β rankB R where
  Index := D.Index
  finiteIndex := D.finiteIndex
  start := D.start
  length := D.length
  equiv := D.equiv.trans e
  symmetric := D.symmetric
  rank_eq := by intro i k; exact (hrank _).trans (D.rank_eq i k)
  monotone := fun i => he.comp (D.monotone i)

def gridRank {d n : ℕ} (x : Fin d → Fin (n + 1)) : ℕ := ∑ i, (x i).val

theorem gridRank_strictMono (d n : ℕ) : StrictMono (@gridRank d n) := by
  intro x y hxy
  have hex : ∃ i, x i < y i := by
    by_contra h
    push Not at h
    exact (not_le_of_gt hxy) h
  obtain ⟨i, hi⟩ := hex
  exact Finset.sum_lt_sum (fun j hj => hxy.le j) ⟨i, Finset.mem_univ i, hi⟩

/-- Every product of equal finite chains has a symmetric saturated-chain
decomposition.  The value parameter `n` means the grid `{0,...,n}^d`. -/
def gridDecomposition (d n : ℕ) :
    Decomposition (Fin d → Fin (n + 1)) gridRank (d * n) := by
  induction d with
  | zero =>
    let e0 : ((i : Unit) × Fin 1) ≃ (Fin 0 → Fin (n + 1)) := {
      toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => ⟨(), 0⟩
      left_inv := by rintro ⟨⟨⟩, k⟩; have hk := Fin.eq_zero k; subst k; rfl
      right_inv := by intro x; funext i; exact Fin.elim0 i }
    exact {
      Index := Unit
      finiteIndex := inferInstance
      start := fun _ => 0
      length := fun _ => 0
      equiv := e0
      symmetric := by simp
      rank_eq := fun i k => by
        simp [gridRank]
      monotone := fun i k l hkl j => Fin.elim0 j }
  | succ d ih =>
    let e : ((Fin d → Fin (n + 1)) × Fin (n + 1)) ≃ (Fin (d + 1) → Fin (n + 1)) :=
      (Equiv.prodComm _ _).trans (Fin.consEquiv (fun _ => Fin (n + 1)))
    have he : Monotone e := by
      intro x y hxy i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hxy.2
      · exact hxy.1 j
    have hrank : ∀ x, gridRank (e x) = gridRank x.1 + x.2.val := by
      intro x
      simp [gridRank, e, Fin.sum_univ_succ, Fin.consEquiv, Nat.add_comm]
    simpa only [Nat.succ_mul] using (ih.prodChain n).map e he hrank

def Decomposition.middlePosition {α : Type} [Preorder α] {rank : α → ℕ} {R : ℕ}
    (D : Decomposition α rank R) (i : D.Index) : Fin (D.length i + 1) :=
  ⟨R / 2 - D.start i, by have := D.symmetric i; omega⟩

def Decomposition.middlePoint {α : Type} [Preorder α] {rank : α → ℕ} {R : ℕ}
    (D : Decomposition α rank R) (i : D.Index) : α :=
  D.equiv ⟨i, D.middlePosition i⟩

theorem Decomposition.middlePoint_rank {α : Type} [Preorder α]
    {rank : α → ℕ} {R : ℕ} (D : Decomposition α rank R) (i : D.Index) :
    rank (D.middlePoint i) = R / 2 := by
  unfold Decomposition.middlePoint
  rw [D.rank_eq]
  dsimp [Decomposition.middlePosition]
  have := D.symmetric i
  omega

theorem Decomposition.comparable_of_same_index {α : Type} [Preorder α]
    {rank : α → ℕ} {R : ℕ} (D : Decomposition α rank R) {x y : α}
    (h : (D.equiv.symm x).1 = (D.equiv.symm y).1) : x ≤ y ∨ y ≤ x := by
  obtain ⟨⟨i, k⟩, rfl⟩ := D.equiv.surjective x
  obtain ⟨⟨j, l⟩, rfl⟩ := D.equiv.surjective y
  simp only [Equiv.symm_apply_apply] at h
  subst j
  rcases le_total k l with hkl | hlk
  · exact Or.inl (D.monotone i hkl)
  · exact Or.inr (D.monotone i hlk)

/-- Every antichain injects into the middle rank by sending an element
to the unique middle point of its chain. -/
theorem Decomposition.antichain_card_le_middle {α : Type} [Preorder α]
    [Fintype α] [DecidableEq α] {rank : α → ℕ} {R : ℕ}
    (D : Decomposition α rank R) (s : Finset α)
    (hs : IsAntichain (· ≤ ·) (s : Set α)) :
    s.card ≤ (Finset.univ.filter (fun x => rank x = R / 2)).card := by
  let f := fun x : α => D.middlePoint (D.equiv.symm x).1
  apply Finset.card_le_card_of_injOn f
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, D.middlePoint_rank _⟩
  · intro x hx y hy hxy
    have hidx : (D.equiv.symm x).1 = (D.equiv.symm y).1 := by
      change D.equiv ⟨(D.equiv.symm x).1, D.middlePosition _⟩ =
        D.equiv ⟨(D.equiv.symm y).1, D.middlePosition _⟩ at hxy
      have hpair := D.equiv.injective hxy
      have hfst := congrArg Sigma.fst hpair
      exact hfst
    rcases D.comparable_of_same_index hidx with h | h
    · exact hs.eq hx hy h
    · exact hs.eq' hx hy h

theorem grid_antichain_card_le_middle (d n : ℕ)
    (s : Finset (Fin d → Fin (n + 1)))
    (hs : IsAntichain (· ≤ ·) (s : Set (Fin d → Fin (n + 1)))) :
    s.card ≤ (Finset.univ.filter (fun x : Fin d → Fin (n + 1) =>
      (∑ i, (x i).val) = d * n / 2)).card :=
  (gridDecomposition d n).antichain_card_le_middle s hs

/-- The same constructive decomposition in the manuscript's `{0,...,n-1}`
notation, for positive side length `n`. -/
def nonemptyGridDecomposition (d n : ℕ) (hn : 0 < n) :
    Decomposition (Fin d → Fin n) (fun x => ∑ i, (x i).val) (d * (n - 1)) := by
  cases n with
  | zero => omega
  | succ n => exact gridDecomposition d n

theorem nonempty_grid_antichain_card_le_middle (d n : ℕ) (hn : 0 < n)
    (s : Finset (Fin d → Fin n))
    (hs : IsAntichain (· ≤ ·) (s : Set (Fin d → Fin n))) :
    s.card ≤ (Finset.univ.filter (fun x : Fin d → Fin n =>
      (∑ i, (x i).val) = d * (n - 1) / 2)).card :=
  (nonemptyGridDecomposition d n hn).antichain_card_le_middle s hs

/-- With a strictly increasing rank, consecutive entries of any of our
chains are adjacent in the ambient order, so the chains are saturated. -/
theorem Decomposition.covBy_of_adjacent {α : Type} [PartialOrder α]
    {rank : α → ℕ} {R : ℕ} (D : Decomposition α rank R) (hrank : StrictMono rank)
    (i : D.Index) (k l : Fin (D.length i + 1)) (hkl : k.val + 1 = l.val) :
    D.equiv ⟨i, k⟩ ⋖ D.equiv ⟨i, l⟩ := by
  have hle : D.equiv ⟨i, k⟩ ≤ D.equiv ⟨i, l⟩ := D.monotone i (by omega)
  have hne : D.equiv ⟨i, k⟩ ≠ D.equiv ⟨i, l⟩ := by
    intro heq
    have h := congrArg rank heq
    rw [D.rank_eq, D.rank_eq] at h
    omega
  refine ⟨lt_of_le_of_ne hle hne, ?_⟩
  intro z hxz hzy
  have hxrank := hrank hxz
  have hyrank := hrank hzy
  rw [D.rank_eq] at hxrank hyrank
  omega

theorem grid_chains_saturated (d n : ℕ) (i : (gridDecomposition d n).Index)
    (k l : Fin ((gridDecomposition d n).length i + 1)) (hkl : k.val + 1 = l.val) :
    (gridDecomposition d n).equiv ⟨i, k⟩ ⋖ (gridDecomposition d n).equiv ⟨i, l⟩ :=
  (gridDecomposition d n).covBy_of_adjacent (gridRank_strictMono d n) i k l hkl

/-- Every rank level is an antichain, so the central level really is a
largest rank level, as asserted in the last sentence of Lemma 3.1. -/
theorem grid_rank_card_le_middle (d n r : ℕ) :
    (Finset.univ.filter (fun x : Fin d → Fin (n + 1) => gridRank x = r)).card ≤
      (Finset.univ.filter (fun x : Fin d → Fin (n + 1) => gridRank x = d * n / 2)).card := by
  apply (gridDecomposition d n).antichain_card_le_middle
  intro x hx y hy hne hle
  have hxrank : gridRank x = r := (Finset.mem_filter.mp hx).2
  have hyrank : gridRank y = r := (Finset.mem_filter.mp hy).2
  have hlt := gridRank_strictMono d n (lt_of_le_of_ne hle hne)
  omega

end SymmetricChains
end LittlewoodInverse
