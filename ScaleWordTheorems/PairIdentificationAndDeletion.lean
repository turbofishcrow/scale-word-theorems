-- Properties of ternary scales related to projection and step deletion
-- including MOS substitution scales
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import ScaleWordTheorems.Basic

namespace Necklace

/-- A necklace over any alphabet has the MOS property if it uses at least 2 distinct
    values and has ≤ 2 distinct k-step multisets for all valid k. -/
def hasMOSProperty [NeZero n] [DecidableEq α] (w : Necklace α n) : Prop :=
  (∃ a b : α, a ≠ b ∧ (∃ i : ZMod n, w i = a) ∧ (∃ i : ZMod n, w i = b)) ∧
  (∀ k : ℕ, 0 < k → k < n →
    (Necklace.allKStepMultisets w k).toFinset.card ≤ 2)

end Necklace

/-- A list, read as a circular word, has the MOS property:
    length ≥ 2, uses ≥ 2 distinct values, and ≤ 2 distinct k-step multisets. -/
def circularHasMOSProperty [DecidableEq α] [Inhabited α] (l : List α) : Prop :=
  l.length ≥ 2 ∧ l.toFinset.card ≥ 2 ∧
  ∀ k : ℕ, 0 < k → k < l.length →
    ((List.range l.length).map (fun i =>
      Multiset.ofList ((List.range k).map (fun j => l[(i + j) % l.length]!))
    )).toFinset.card ≤ 2

namespace TernaryNecklace

variable {n : ℕ}

/-- Read a necklace in order (positions 0, 1, ..., n-1),
    deleting all occurrences of step size x. -/
def orderedDeletion [NeZero n] (w : TernaryNecklace n) (x : StepSize) : List StepSize :=
  ((List.range n).map (fun i => w (i : ZMod n))).filter (· ≠ x)

/-! ### Pairwise-MOS

A ternary necklace is called *pairwise-MOS* if it satisfies all
three *partial pairwise-MOS properties*, i.e. it becomes a MOS under all three
of the identifications L = m, m = s, and L = s. -/

/-- Partial pairwise-MOS: identifying step sizes x and y gives a MOS. -/
def isPartialPairwiseMOS [NeZero n] (w : TernaryNecklace n) (x y : StepSize) : Prop :=
  Necklace.hasMOSProperty (w.identifyPair x y)

/-- Pairwise-MOS: all three pair identifications give a MOS. -/
def isPairwiseMOS [NeZero n] (w : TernaryNecklace n) : Prop :=
  w.isPartialPairwiseMOS StepSize.L StepSize.m ∧
  w.isPartialPairwiseMOS StepSize.m StepSize.s ∧
  w.isPartialPairwiseMOS StepSize.L StepSize.s

/-! ### Deletion-MOS

A ternary necklace is called *deletion-MOS* if it satisfies all three *partial
deletion-MOS properties*, i.e. it becomes a MOS when you delete any of the three
step sizes, L, m, and s. -/

/-- Partial deletion-MOS: deleting step size x and reading the result
    as a circular word gives a MOS. -/
def isPartialDeletionMOS [NeZero n] (w : TernaryNecklace n) (x : StepSize) : Prop :=
  circularHasMOSProperty (w.orderedDeletion x)

/-- Deletion-MOS: deleting any of the three step sizes gives a MOS. -/
def isDeletionMOS [NeZero n] (w : TernaryNecklace n) : Prop :=
  w.isPartialDeletionMOS StepSize.L ∧
  w.isPartialDeletionMOS StepSize.m ∧
  w.isPartialDeletionMOS StepSize.s

/-! ### MOS substitution

A ternary necklace is a *MOS substitution necklace* if it becomes a
MOS (called the *template MOS*) under identifying two of the step sizes
and becomes a MOS (called the *filling MOS*) after deleting the third
step size. -/

/-- MOS substitution necklace: there exist three pairwise-distinct step sizes
    x, y, z such that identifying x with y gives a MOS (template)
    and deleting z gives a MOS (filling). -/
def isMOSSubstitution [NeZero n] (w : TernaryNecklace n) : Prop :=
  ∃ (x y z : StepSize), x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
    w.isPartialPairwiseMOS x y ∧ w.isPartialDeletionMOS z

end TernaryNecklace
