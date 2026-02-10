import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Multiset.Basic

/-!
# Basic Definitions for Ternary Scale Theory

This file contains the basic definitions for working with ternary scales,
which are necklaces (circular words) over an alphabet of three step sizes.

## Main Definitions

* `Necklace α n`: A circular word of length `n` over alphabet `α`,
  indexed by `ZMod n`
* `TernaryNecklace`: A circular word over three step sizes (typically L, M, s)
* Projections and other basic operations on scale words

## References

Based on "ternary-scale-theorems" document

-/



/-! ## Vectors

A vector is a function from the alphabet to ℤ, representing a formal integer
linear combination of step sizes. This allows us to express the generator
condition: g is a generator if every vector in the scale is of the form jg + kp
for some j, k ∈ ℤ, where p is the period vector.
-/

/-- A vector over alphabet α is a function to ℤ.
    This represents a formal ℤ-linear combination of letters.
    Named ZVector to avoid conflict with Mathlib's Vector. -/
def ZVector (α : Type*) := α → ℤ

namespace ZVector

variable {α : Type*}

instance : Zero (ZVector α) := ⟨fun _ => 0⟩
instance : Add (ZVector α) := ⟨fun v w a => v a + w a⟩
instance : Neg (ZVector α) := ⟨fun v a => -v a⟩
instance : Sub (ZVector α) := ⟨fun v w a => v a - w a⟩

/-- Scalar multiplication by an integer -/
instance : SMul ℤ (ZVector α) := ⟨fun n v a => n * v a⟩

@[simp] lemma zero_apply (a : α) : (0 : ZVector α) a = 0 := rfl
@[simp] lemma add_apply (v w : ZVector α) (a : α) : (v + w) a = v a + w a := rfl
@[simp] lemma neg_apply (v : ZVector α) (a : α) : (-v) a = -v a := rfl
@[simp] lemma sub_apply (v w : ZVector α) (a : α) : (v - w) a = v a - w a := rfl
@[simp] lemma smul_apply (n : ℤ) (v : ZVector α) (a : α) : (n • v) a = n * v a := rfl

/-- Convert a list to a vector by counting occurrences -/
def ofList [DecidableEq α] (l : List α) : ZVector α :=
  fun a => (l.filter (· == a)).length

/-- Convert a multiset to a vector -/
def ofMultiset [DecidableEq α] (m : Multiset α) : ZVector α :=
  fun a => Multiset.count a m

end ZVector

/-- A circular word of length `n` over alphabet `α`.
    Indices are elements of `ZMod n`, making the word circular. -/
def Necklace (α : Type*) (n : ℕ) := ZMod n → α

namespace Necklace

variable {α : Type*} {n : ℕ} [NeZero n]

/-- The length of a circular word -/
def length (_w : Necklace α n) : ℕ := n

/-- Get the element at a given index (using 0-based indexing internally) -/
def get (w : Necklace α n) (i : ZMod n) : α := w i

/-- Count occurrences of a letter in a circular word -/
def count [NeZero n] [DecidableEq α] (w : Necklace α n) (a : α) : ℕ :=
  Finset.card (Finset.filter (fun i => w i = a) Finset.univ)

/-- A subword (or slice) from index i to index j.
    Note: This returns a list, not a circular word -/
def slice [NeZero n] (w : Necklace α n) (i j : ℕ) : List α :=
  List.map w (List.map (fun k => ((i + k) : ZMod n)) (List.range (j - i))) -- 0..=(j - i - 1)

/-- Get all elements that actually occur in a necklace -/
def distinctElements [NeZero n] [DecidableEq α] [Fintype α] (w: Necklace α n) : (Finset α) :=
  (slice w 0 n).toFinset

/-- A necklace is a d-fold repetition if w(i) = w(i + n/d) for all i -/
def isRepetition [NeZero n] (w : Necklace α n) (d : ℕ) : Prop :=
  d ∣ n ∧ d > 0 ∧ ∀ i : ZMod n, w i = w (i + (n / d : ℕ))

/-- The length of a slice is j - i -/
lemma slice_length (w : Necklace α n) (i j : ℕ) :
    (slice w i j).length = j - i := by
  unfold slice
  simp only [bind_pure_comp, Functor.map, List.length_map, List.length_range]

/-- Check if a circular word is the repetition of a given pattern -/
def isRepetitionOf [NeZero n] [DecidableEq α] (w : Necklace α n) (pfx : List α) : Bool :=
  if pfx.length = 0 then
    false
  else if n % pfx.length ≠ 0 then
    false
  else
    List.range n |>.all fun i =>
      some (w (i : ZMod n)) = pfx[i % pfx.length]?

/-- The minimal-length subword p such that the circular word is a power of p -/
def period [NeZero n] [DecidableEq α] (w : Necklace α n) : List α :=
  (List.range n).tail
    |>.map (slice w 0 ·)
    |>.find? (isRepetitionOf w)
    |>.getD (slice w 0 n)

/-- A scale is primitive if its period equals its length -/
def isPrimitive [NeZero n] [DecidableEq α] (w : Necklace α n) : Prop :=
  (Necklace.period w).length = n

/-- Get all k-step subwords of a circular word as a list of lists -/
def allKStepSubwords [NeZero n] [DecidableEq α] (w : Necklace α n) (k : ℕ) : List (List α) :=
  List.ofFn fun (i : Fin n) => Necklace.slice w i.val (i.val + k)

/-- Convert a k-step subword to its abelianized form (multiset of letters).
    This captures the counts of each letter, ignoring order. -/
def abelianize [DecidableEq α] (subword : List α) : Multiset α  :=
  Multiset.ofList subword

/-- Get all multisets (abelianized subwords) corresponding to k-step subwords -/
def allKStepMultisets [NeZero n] [DecidableEq α] (w : Necklace α n) (k : ℕ) : List (Multiset α) :=
  List.map Necklace.abelianize (allKStepSubwords w k)

/-- The period vector: abelianization of the period word as an integer vector -/
def periodVector [NeZero n] [DecidableEq α] (w : Necklace α n) : ZVector α :=
  ZVector.ofList (Necklace.period w)

/-- Convert a k-step subword to its vector form -/
def kStepVector [NeZero n] [DecidableEq α] (w : Necklace α n) (i k : ℕ) : ZVector α :=
  ZVector.ofList (Necklace.slice w i (i + k))

/-- All k-step vectors of a necklace -/
def allKStepVectors [NeZero n] [DecidableEq α] (w : Necklace α n) (k : ℕ) : List (ZVector α) :=
  List.map (fun i => kStepVector w i k) (List.range n)

/-- Convert a list into a necklace -/
def toNecklace [Inhabited α] [DecidableEq α] (l : List α) : Necklace α (l.length) :=
  fun (i : ZMod l.length) => l[i.val]!

/-- Whether a necklace is balanced:
Let *a* be a letter in a word or necklace *s*. Define

`\mathsf{block\_balance}(s, a) := \max \big\{ \big| |w|_{a} - |w'|_{a} \big| : |w| =  |w'| \big\}.`

Then *s* is *balanced* if:

`\max \big\{ \mathsf{block\_balance}(s, a) : a \text{ is a letter of }s \big\} \leq 1.`
-/
def isBalanced [NeZero n] [DecidableEq α] (w : Necklace α n) : Prop :=
  (∀ k : ℕ, 0 < k → k < n → ∀ (w1 w2 : List α), ∀ a : α, w1 ∈ allKStepSubwords w k → w2 ∈ allKStepSubwords w k →
    Int.natAbs ((w1.count a : ℤ) - (w2.count a : ℤ)) ≤ 1)

/-! ## Technical Lemmas
-/
/-- Helper lemma: A singleton necklace has only one distinct element.
-/
lemma singletonNecklaceIsUnary [DecidableEq α] [Fintype α] (w : Necklace α 1) :
    ((distinctElements w).card = 1) := by
  unfold distinctElements slice
  simp only [tsub_zero, List.range_one, bind_pure_comp]
  rfl

end Necklace

/-- The alphabet for ternary scales: three step sizes L, M, s -/
inductive StepSize where
  | L : StepSize  -- Large step
  | m : StepSize  -- Medium step
  | s : StepSize  -- small step
  deriving DecidableEq, Repr, Inhabited

instance : Fintype StepSize where
  elems := {StepSize.L, StepSize.m, StepSize.s}
  complete := fun x => by cases x <;> simp

/-- A ternary scale word is a circular word over the three step sizes -/
def TernaryNecklace (n : ℕ) := Necklace StepSize n

namespace TernaryNecklace

variable {n : ℕ}

/-- Pair identification: identify two step sizes.
    This models setting two step sizes equal (e.g., L = M) -/
def identifyPair (w : TernaryNecklace n) (x y : StepSize) : Necklace StepSize n :=
  fun i => if w i = x then y else w i

/-- Check if a scale is ternary (uses all three step sizes) -/
def isTernary (w : TernaryNecklace n) : Prop :=
  (∃ i, w i = StepSize.L) ∧
  (∃ i, w i = StepSize.m) ∧
  (∃ i, w i = StepSize.s)

/-- Delete all instances of a step size from a scale word.
    This operation is denoted E_X(s) in the document.
    Returns a list since the result is not necessarily circular. -/
noncomputable def delete [NeZero n] (w : TernaryNecklace n) (x : StepSize) : List StepSize :=
  List.filter (· ≠ x) (Finset.univ.val.map w).toList

/-- A scale word represented as a list for easier pattern matching -/
noncomputable def toList [NeZero n] (w : TernaryNecklace n) : List StepSize :=
  (Finset.univ.val.map w).toList

/-- A ternary scale word is MV3 (maximum variety 3) if for every k
    between 1 and n-1, there are at most 3 distinct k-step vectors -/
def isMV3 [NeZero n] (w : TernaryNecklace n) : Prop :=
  (TernaryNecklace.isTernary w) ∧ (∀ k : ℕ, 0 < k → k < n →
    (Necklace.allKStepMultisets w k).toFinset.card ≤ 3)

end TernaryNecklace

/-! ## Examples -/

/-- Example: Create a small circular word -/
example : Necklace ℕ 5 := fun i => i.val

/-- Example: A scale word can be defined by cases -/
def zarlino : TernaryNecklace 7 := fun i =>
  match i.val with
  | 0 => StepSize.L
  | 1 => StepSize.m
  | 2 => StepSize.s
  | 3 => StepSize.L
  | 4 => StepSize.m
  | 5 => StepSize.L
  | 6 => StepSize.s
  | _ => StepSize.s  -- unreachable due to ZMod 7
