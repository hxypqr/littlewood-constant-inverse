import Mathlib

/-!
# Abstract finite-tree budget

This is the combinatorial induction at manuscript lines 1561–1571.
The analytic inequality at a vertex is an explicit premise. In particular,
this file does not claim to prove the Fourier fibre inequality.
-/

namespace LittlewoodInverse

/-- A finite rooted tree with a real budget at every vertex. The arity of
each vertex is finite but is not bounded uniformly across trees. -/
inductive BudgetTree where
  | leaf (budget : ℝ)
  | node (budget : ℝ) (arity : ℕ) (children : Fin arity → BudgetTree)

namespace BudgetTree

def rootBudget : BudgetTree → ℝ
  | leaf b => b
  | node b _ _ => b

def leafPowerSum (p : ℕ) : BudgetTree → ℝ
  | leaf b => b ^ p
  | node _ _ children => ∑ i, leafPowerSum p (children i)

def leafCount : BudgetTree → ℕ
  | leaf _ => 1
  | node _ _ children => ∑ i, leafCount (children i)

/-- Every local budget bounds the sum of the child budgets to power `p`. -/
def HasLocalPowerBound (p : ℕ) : BudgetTree → Prop
  | leaf _ => True
  | node b _ children =>
      (∑ i, (children i).rootBudget ^ p) ≤ b ^ p ∧
        ∀ i, HasLocalPowerBound p (children i)

def LeavesAtLeastOne : BudgetTree → Prop
  | leaf b => 1 ≤ b
  | node _ _ children => ∀ i, LeavesAtLeastOne (children i)

/-- Iterating a local power budget introduces no factor depending on the
depth or branching of the tree. -/
theorem leafPowerSum_le_rootBudget (p : ℕ) (tree : BudgetTree)
    (h : tree.HasLocalPowerBound p) : tree.leafPowerSum p ≤ tree.rootBudget ^ p := by
  induction tree with
  | leaf b => exact le_rfl
  | node b n children ih =>
      change (∑ i, leafPowerSum p (children i)) ≤ b ^ p
      exact (Finset.sum_le_sum fun i _ => ih i (h.2 i)).trans h.1

/-- The leaf-count consequence only uses the lower budget one at each leaf. -/
theorem leafCount_le_leafPowerSum (p : ℕ) (tree : BudgetTree)
    (h : tree.LeavesAtLeastOne) : (tree.leafCount : ℝ) ≤ tree.leafPowerSum p := by
  induction tree with
  | leaf b =>
      simpa [leafCount, leafPowerSum] using
        (one_le_pow₀ (show (1 : ℝ) ≤ b from h) : (1 : ℝ) ≤ b ^ p)
  | node b n children ih =>
      change ((∑ i, leafCount (children i) : ℕ) : ℝ) ≤ ∑ i, leafPowerSum p (children i)
      push_cast
      exact Finset.sum_le_sum fun i _ => ih i (h i)

/-- Abstract form of the manuscript's twentieth-power leaf budget. -/
theorem leaf_twentieth_budget (tree : BudgetTree)
    (h : tree.HasLocalPowerBound 20) : tree.leafPowerSum 20 ≤ tree.rootBudget ^ 20 :=
  leafPowerSum_le_rootBudget 20 tree h

/-- Abstract leaf-count bound, independent of the tree's depth. -/
theorem leafCount_le_rootBudget (p : ℕ) (tree : BudgetTree)
    (h : tree.HasLocalPowerBound p) (hleaf : tree.LeavesAtLeastOne) :
    (tree.leafCount : ℝ) ≤ tree.rootBudget ^ p :=
  (leafCount_le_leafPowerSum p tree hleaf).trans (leafPowerSum_le_rootBudget p tree h)

end BudgetTree
end LittlewoodInverse
