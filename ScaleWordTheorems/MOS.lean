import Mathlib.Data.Multiset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import ScaleWordTheorems.Basic

/-!
# MOS (Moment of Symmetry) Scales

This file defines MOS scales, which are binary scale words where every k-step subword,
when abelianized (i.e., considering only letter counts, not order), comes in at most
two distinct multisets.

In the mathematical literature, these are also called "balanced" binary words.

## Main Definitions

* `isMOS`: A scale word is a MOS if for every k, all k-step subwords come in
  at most two abelianized forms

## References

Based on the ternary-scale-theorems document and the property that MOS scales
are balanced.

-/

/-- A binary step size alphabet
    We won't be using the size order most of the time though -/
inductive BinaryStep where
  | L : BinaryStep  -- Large step
  | s : BinaryStep  -- small step
  deriving DecidableEq, Repr, Inhabited

namespace BinaryStep

instance : Fintype BinaryStep where
  elems := {L, s}
  complete := fun x => by cases x <;> simp

def otherStep (x : BinaryStep) : BinaryStep :=
  match x with
    | L => s
    | s => L

end BinaryStep

/-- A binary scale word (MOS candidate) -/
def BinaryNecklace (n : ℕ) := Necklace BinaryStep n

namespace BinaryNecklace

variable {n : ℕ} [NeZero n]

/-- Check if a scale is binary (uses both step sizes) -/
def isBinary (w : BinaryNecklace n) : Prop :=
  (∃ i, w i = BinaryStep.L) ∧
  (∃ i, w i = BinaryStep.s)

/-- A binary scale word is a MOS if for every k between 1 and n-1,
    there are at most 2 distinct k-step vectors -/
def isMOS (w : BinaryNecklace n) : Prop :=
  (BinaryNecklace.isBinary w) ∧ (∀ k : ℕ, 0 < k → k < n →
    (Necklace.allKStepMultisets w k).toFinset.card ≤ 2)

/-- The step signature of a binary scale: (number of L's, number of s's) -/
def stepSignature [NeZero n] (w : BinaryNecklace n) : ℕ × ℕ :=
  let numL := Necklace.count w BinaryStep.L
  let nums := Necklace.count w BinaryStep.s
  (numL, nums)

/-- A MOS with step signature aL bs is often written as "aL bs" -/
def hasStepSignature [NeZero n] (w : BinaryNecklace n) (a b : ℕ) : Prop :=
  stepSignature w = (a, b)

end BinaryNecklace

/-! ## Examples -/

/-- Example: The 5L 2s scale (diatonic scale pattern) -/
def diatonic : BinaryNecklace 7 := fun i =>
  match i.val with
  | 0 => BinaryStep.L
  | 1 => BinaryStep.L
  | 2 => BinaryStep.s
  | 3 => BinaryStep.L
  | 4 => BinaryStep.L
  | 5 => BinaryStep.L
  | 6 => BinaryStep.s
  | _ => BinaryStep.s  -- unreachable

/-- Examples: The 5L 3s (oneirotonic) scale -/
def oneirotonic : BinaryNecklace 8 := fun i =>
  match i.val with
  | 0 => BinaryStep.L
  | 1 => BinaryStep.s
  | 2 => BinaryStep.L
  | 3 => BinaryStep.s
  | 4 => BinaryStep.L
  | 5 => BinaryStep.L
  | 6 => BinaryStep.s
  | 7 => BinaryStep.L
  | _ => BinaryStep.L -- unreachable

/-- Example: 2L 3s (pentatonic pattern) -/
def pentatonic : BinaryNecklace 5 := fun i =>
  match i.val with
  | 0 => BinaryStep.s
  | 1 => BinaryStep.s
  | 2 => BinaryStep.L
  | 3 => BinaryStep.s
  | 4 => BinaryStep.L
  | _ => BinaryStep.s  -- unreachable

/-! ## Generators -/

/-- Decidable equality for ZVector over a finite decidable type -/
instance [DecidableEq α] [Fintype α] : DecidableEq (ZVector α) :=
  fun v w => decidable_of_iff (∀ a, v a = w a) ⟨fun h => funext h, fun h _ => congrFun h _⟩

/-- A generator g is a period-reduced vector such that there exists a rotation of w where the
    prefix vectors {w'[0:1], w'[0:2], ..., w'[0:|p|]} correspond bijectively to
    {0·g, 1·g, ..., (|p|-1)·g} modulo the period lattice.

    More precisely: g is a generator for scale w if:
    1. g actually appears as some k-step vector in w (period-reduced), and
    2. there exists a rotation r such that the prefix vectors at that rotation
       cover all residue classes {j·g + k·p : 0 ≤ j < |p|, k ∈ ℤ}. -/
def IsGenerator [NeZero n] [DecidableEq α] (w : Necklace α n) (g : ZVector α) : Prop :=
  let per := Necklace.period w
  let pLen := per.length
  let p := ZVector.ofList per
  -- g is period-reduced: it actually appears as a k-step vector with k < period length
  (∃ k : ℕ, k < pLen ∧ ∃ i : Fin n, Necklace.kStepVector w i.val k = g) ∧
  -- There exists a rotation where prefixes correspond to {j·g + k·p}
  ∃ r : ZMod n, -- there is a rotation s.t.
    let w' := fun i => w (i + r) -- let w' be the rotated word
    -- Every prefix is of the form j·g + k·p for some j < |p|:
    (∀ i : Fin pLen, -- for every prefix length
      ∃ j : Fin pLen, ∃ k : ℤ, -- there's a stack of generators and periods s.t.
        ∀ a : α, -- the prefix vector and the stack of gens and pers have equal components, AND
          (Necklace.kStepVector w' 0 (i.val + 1)) a = j.val * g a + k * p a) ∧
    -- Every j < |p| is realized by some prefix (surjectivity implies bijectivity):
    (∀ j : Fin pLen, -- for every number of stacked generators in 0..pLen
      ∃ i : Fin pLen, ∃ k : ℤ, -- there's a prefix and a stack of periods s.t.
        ∀ a : α, -- the prefix vector and the stack of gens and pers have equal components
          (Necklace.kStepVector w' 0 (i.val + 1)) a = j.val * g a + k * p a)

/-- Check if vector v can be written as j·g + k·p for some j ∈ {0,...,pLen-1} and k ∈ ℤ.
    Returns the j value if found, or none if not expressible in this form.
    For binary alphabet, this solves a 2x2 linear system. -/
def findGeneratorCoeff (v g p : ZVector BinaryStep) (pLen : ℕ) : Option (Fin pLen) :=
  -- For binary alphabet, we solve:
  -- j * g(L) + k * p(L) = v(L)
  -- j * g(s) + k * p(s) = v(s)
  -- Determinant: det = g(L)\*p(s) - g(s)\*p(L)
  let gL := g BinaryStep.L
  let gs := g BinaryStep.s
  let pL := p BinaryStep.L
  let ps := p BinaryStep.s
  let vL := v BinaryStep.L
  let vs := v BinaryStep.s
  let det := gL * ps - gs * pL
  if det = 0 then
    -- g and p are parallel; check if v is a multiple of g (with k=0)
    if gL ≠ 0 then
      let j := vL / gL
      if hj : j * gL = vL ∧ j * gs = vs ∧ 0 ≤ j ∧ j < pLen then
        some ⟨j.toNat, by
          have h1 : 0 ≤ j := hj.2.2.1
          have h2 : j < pLen := hj.2.2.2
          omega⟩
      else none
    else if gs ≠ 0 then
      let j := vs / gs
      if hj : j * gL = vL ∧ j * gs = vs ∧ 0 ≤ j ∧ j < pLen then
        some ⟨j.toNat, by
          have h1 : 0 ≤ j := hj.2.2.1
          have h2 : j < pLen := hj.2.2.2
          omega⟩
      else none
    else none  -- g is zero vector
  else
    -- Solve using Cramer's rule
    -- k * det = vL * gs - vs * gL
    let kNumer := vL * gs - vs * gL
    if kNumer % det ≠ 0 then none  -- k is not an integer
    else
      let k := kNumer / det
      -- j * det = vL * ps - vs * pL - k * (pL * ps - ps * pL) = vL * ps - vs * pL
      -- Actually: j = (vL - k * pL) / gL or j = (vs - k * ps) / gs
      let jNumer := if gL ≠ 0 then vL - k * pL else vs - k * ps
      let gComp := if gL ≠ 0 then gL else gs
      if gComp = 0 then none
      else if jNumer % gComp ≠ 0 then none  -- j is not an integer
      else
        let j := jNumer / gComp
        if hj : 0 ≤ j ∧ j < pLen then
          some ⟨j.toNat, by
            have h1 : 0 ≤ j := hj.1
            have h2 : j < pLen := hj.2
            omega⟩
        else none

/-- Boolean check for generator (computable version). -/
def isGenerator [NeZero n] (w : BinaryNecklace n) (g : ZVector BinaryStep) : Bool :=
  let per := Necklace.period w
  let pLen := per.length
  let p := ZVector.ofList per
  -- Check 1: g is period-reduced (appears as some k-step vector)
  let isPeriodReduced := (List.range n).any fun k =>
    (List.range n).any fun i => decide (Necklace.kStepVector w i k = g)
  -- Check 2: There exists a rotation where prefix property holds
  let hasGoodRotation := (List.range n).any fun r =>
    let w' := fun i => w (i + (r : ZMod n))
    -- Forward: every prefix is j·g + k·p for some j
    let fwdOk := (List.range pLen).all fun i =>
      let v := Necklace.kStepVector w' 0 (i + 1)
      (findGeneratorCoeff v g p pLen).isSome
    -- Backward: every j is realized by some prefix
    let bwdOk := (List.range pLen).all fun j =>
      (List.range pLen).any fun i =>
        let v := Necklace.kStepVector w' 0 (i + 1)
        match findGeneratorCoeff v g p pLen with
        | some j' => decide (j'.val = j)
        | none => false
    fwdOk && bwdOk
  isPeriodReduced && hasGoodRotation

/-- A scale has a generator if there exists some vector g that is a generator -/
def HasGenerator [NeZero n] [DecidableEq α] (w : Necklace α n) : Prop :=
  ∃ g : ZVector α, IsGenerator w g

/-- Count how many positions (out of all n) have a given k-step vector -/
def countKStepVector [NeZero n] [DecidableEq α] [Fintype α] (w : Necklace α n) (k : ℕ) (g : ZVector α) : ℕ :=
  (List.range n).countP fun i => decide (Necklace.kStepVector w i k = g)

/-- Count how many positions within one period have a given k-step vector.
    This counts only within positions 0..(period length - 1). -/
def countKStepVectorPerPeriod [NeZero n] [DecidableEq α] [Fintype α] (w : Necklace α n) (k : ℕ) (g : ZVector α) : ℕ :=
  let p := (Necklace.period w).length
  (List.range p).countP fun i => decide (Necklace.kStepVector w i k = g)

/-- The set of distinct k-step vectors in a necklace -/
def distinctKStepVectors [NeZero n] [DecidableEq α] [Fintype α] (w : Necklace α n) (k : ℕ) : Finset (ZVector α) :=
  (Necklace.allKStepVectors w k).toFinset

/-! ## Generator Occurrence Theorems

The following theorems characterize generators in terms of their occurrence count:
a generator occurs at exactly n-1 positions per period, and conversely, any k-step
vector that occurs at exactly n-1 positions per period is a generator.
-/

/-- Helper: Counting L's in a cons list -/
lemma countL_cons (a : BinaryStep) (l : List BinaryStep) :
    let countL := fun l : List BinaryStep => (l.filter (· == BinaryStep.L)).length
    countL (a :: l) = (if a = BinaryStep.L then 1 else 0) + countL l := by
  simp only [List.filter_cons]
  cases a <;> simp [Nat.add_comm]

/-- Helper: Counting L's after appending a single element -/
lemma countL_append_singleton (l : List BinaryStep) (a : BinaryStep) :
    let countL := fun l : List BinaryStep => (l.filter (· == BinaryStep.L)).length
    countL (l ++ [a]) = countL l + (if a = BinaryStep.L then 1 else 0) := by
  simp only [List.filter_append, List.length_append, List.filter_cons, List.filter_nil]
  cases a <;> simp

/-- ZVector.ofMultiset is injective for finite types -/
lemma ZVector.ofMultiset_injective [DecidableEq α] [Fintype α] :
    Function.Injective (ZVector.ofMultiset : Multiset α → ZVector α) := by
  intro m1 m2 h
  apply Multiset.ext.mpr
  intro a
  have : ZVector.ofMultiset m1 a = ZVector.ofMultiset m2 a := congrFun h a
  simp only [ZVector.ofMultiset] at this
  exact_mod_cast this

/-- Necklace.kStepVector equals ZVector.ofMultiset of the abelianized slice -/
lemma kStepVector_eq_ofMultiset [NeZero n] [DecidableEq α] (w : Necklace α n) (i k : ℕ) :
    Necklace.kStepVector w i k = ZVector.ofMultiset (Necklace.abelianize (Necklace.slice w i (i + k))) := by
  unfold Necklace.kStepVector Necklace.abelianize
  funext a
  simp only [ZVector.ofList, ZVector.ofMultiset]
  rw [Multiset.coe_count, List.count_eq_countP]
  congr 1
  induction (Necklace.slice w i (i + k)) with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.filter_cons, List.countP_cons]
    by_cases h : hd = a
    · simp [h, ih]
    · simp [ih, beq_eq_false_iff_ne.mpr h]

/-- Mapping an injective function preserves toFinset cardinality -/
lemma List.toFinset_card_map_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (l : List α) :
    (l.map f).toFinset.card = l.toFinset.card := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.toFinset_cons]
    by_cases hmem : hd ∈ tl
    · -- hd already in tl, so f hd already in (map f tl)
      have hfmem : f hd ∈ (tl.map f).toFinset := by
        simp only [List.mem_toFinset, List.mem_map]
        exact ⟨hd, hmem, rfl⟩
      rw [Finset.insert_eq_of_mem hfmem, Finset.insert_eq_of_mem (List.mem_toFinset.mpr hmem), ih]
    · -- hd not in tl, so f hd not in (map f tl) by injectivity
      have hfnmem : f hd ∉ (tl.map f).toFinset := by
        simp only [List.mem_toFinset, List.mem_map, not_exists, not_and]
        intro x hx heq
        exact hmem (hf heq ▸ hx)
      rw [Finset.card_insert_eq_ite, Finset.card_insert_eq_ite, if_neg hfnmem,
          if_neg (List.mem_toFinset.not.mpr hmem), ih]

/-- The set of distinct k-step ZVectors has same cardinality as the set of distinct Multisets -/
lemma distinctKStepVectors_card_eq [NeZero n] [DecidableEq α] [Fintype α] (w : Necklace α n) (k : ℕ) :
    (distinctKStepVectors w k).card = (Necklace.allKStepMultisets w k).toFinset.card := by
  unfold distinctKStepVectors Necklace.allKStepVectors Necklace.allKStepMultisets Necklace.allKStepSubwords
  -- Show LHS = image of RHS under ZVector.ofMultiset, then use injectivity
  have h_eq : (List.map (fun i => Necklace.kStepVector w i k) (List.range n)).toFinset =
      (List.map Necklace.abelianize (List.ofFn fun i : Fin n => Necklace.slice w i.val (i.val + k))).toFinset.image ZVector.ofMultiset := by
    ext v
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]
    constructor
    · intro ⟨i, hi, hv⟩
      rw [List.mem_range] at hi
      refine ⟨Necklace.abelianize (Necklace.slice w i (i + k)), ?_, ?_⟩
      · -- Show the abelianized slice is in the list
        use Necklace.slice w i (i + k)
        constructor
        · rw [List.mem_ofFn]
          exact ⟨⟨i, hi⟩, rfl⟩
        · rfl
      · rw [← hv, kStepVector_eq_ofMultiset]
    · intro ⟨m, hm, hv⟩
      obtain ⟨slice, hslice_mem, hslice_eq⟩ := hm
      rw [List.mem_ofFn] at hslice_mem
      obtain ⟨⟨i, hi⟩, rfl⟩ := hslice_mem
      refine ⟨i, List.mem_range.mpr hi, ?_⟩
      rw [← hv, ← hslice_eq, kStepVector_eq_ofMultiset]
  rw [h_eq, Finset.card_image_of_injective _ ZVector.ofMultiset_injective]

/-- The period length is at most n (since period divides the necklace) -/
lemma Necklace.period_length_le_n [NeZero n] [DecidableEq α] (w : Necklace α n) :
    (Necklace.period w).length ≤ n := by
  unfold Necklace.period
  cases h : (List.range n).tail.map (Necklace.slice w 0) |>.find? (Necklace.isRepetitionOf w) with
  | none =>
    -- Default case: slice w 0 n, which has length n - 0 = n
    simp only [Option.getD, Necklace.slice_length]
    omega
  | some pfx =>
    -- Found case: pfx is in the mapped list, so pfx = slice w 0 k for some k ∈ (List.range n).tail
    simp only [Option.getD]
    have hmem := List.mem_of_find?_eq_some h
    rw [List.mem_map] at hmem
    obtain ⟨k, hk_mem, hk_eq⟩ := hmem
    rw [← hk_eq, Necklace.slice_length]
    -- k ∈ (List.range n).tail means k < n
    have hk_lt : k < n := by
      have : k ∈ List.range n := List.mem_of_mem_tail hk_mem
      exact List.mem_range.mp this
    omega

/-- In a MOS scale, for any step size k with 0 < k < period length, there are at most 2
    distinct k-step vectors. -/
lemma mos_at_most_two_varieties [NeZero n]
    (w : BinaryNecklace n) (hw : BinaryNecklace.isMOS w)
    (k : ℕ) (hk_pos : 0 < k) (hk_bound : k < (Necklace.period w).length) :
    (distinctKStepVectors w k).card ≤ 2 := by
  -- Use the cardinality equality
  rw [distinctKStepVectors_card_eq]
  -- period.length ≤ n, so k < n
  have hkn : k < n := by
    calc k < (Necklace.period w).length := hk_bound
      _ ≤ n := Necklace.period_length_le_n w
  -- Apply the MOS property
  exact hw.2 k hk_pos hkn

/-- Necklace.kStepVector depends only on the starting index modulo n -/
lemma kStepVector_mod_n [NeZero n] [DecidableEq α] (w : Necklace α n) (m k : ℕ) :
    Necklace.kStepVector w (m % n) k = Necklace.kStepVector w m k := by
  -- Each element in slice is w((m % n + l) : ZMod n) = w((m + l) : ZMod n)
  -- because (m % n : ZMod n) = (m : ZMod n)
  unfold Necklace.kStepVector Necklace.slice
  -- Simplify (m % n + k) - (m % n) = k and (m + k) - m = k
  simp only [Nat.add_sub_cancel_left]
  -- Now the ranges are the same (both List.range k)
  -- Need to show the mapped functions give the same result
  congr 1
  ext l
  -- Show (m % n + l : ZMod n) = (m + l : ZMod n)
  -- This follows from (m % n : ZMod n) = (m : ZMod n)
  simp only [ZMod.natCast_mod]

/-- Necklace.kStepVector is periodic with respect to the necklace's period length.

    This states that Necklace.kStepVector has period equal to the necklace's minimal period.
    The proof requires showing that the necklace's period property (captured by
    isRepetitionOf) implies pointwise periodicity: w(j) = w(j % pLen) for all j,
    which then extends to slices and thus to Necklace.kStepVector.
-/
lemma kStepVector_mod_period [NeZero n] [DecidableEq α]
    (w : Necklace α n) (m k : ℕ) (_ : k ≤ (Necklace.period w).length) :
    Necklace.kStepVector w (m % (Necklace.period w).length) k = Necklace.kStepVector w m k := by
  let pLen := (Necklace.period w).length

  have hpLen_pos : 0 < pLen := by
    show 0 < (Necklace.period w).length
    unfold Necklace.period
    cases hfind : ((List.range n).tail.map (Necklace.slice w 0)).find?
        (Necklace.isRepetitionOf w) with
    | none =>
      simp only [Option.getD_none]
      rw [Necklace.slice_length]
      exact NeZero.pos n
    | some pfx =>
      simp only [Option.getD_some]
      have hmem := List.mem_of_find?_eq_some hfind
      rw [List.mem_map] at hmem
      obtain ⟨k', hk_mem, hk_eq⟩ := hmem
      rw [← hk_eq, Necklace.slice_length]
      simp only [List.tail_range, List.mem_range'] at hk_mem
      omega

  -- Extract pLen | n from isRepetitionOf property
  have hpLen_dvd_n : pLen ∣ n := by
    have hRep : Necklace.isRepetitionOf w (Necklace.period w) = true := by
      unfold Necklace.period
      cases hfind : ((List.range n).tail.map (Necklace.slice w 0)).find?
          (Necklace.isRepetitionOf w) with
      | some pfx => simp only [Option.getD_some]; exact List.find?_some hfind
      | none =>
        simp only [Option.getD_none]
        unfold Necklace.isRepetitionOf
        simp only [Necklace.slice_length, Nat.sub_zero, ne_eq,
          Nat.pos_iff_ne_zero.mp (NeZero.pos n), ↓reduceIte,
          Nat.mod_self, not_true_eq_false]
        rw [List.all_eq_true]
        intro i hi
        rw [List.mem_range] at hi
        rw [decide_eq_true_eq, Nat.mod_eq_of_lt hi]
        unfold Necklace.slice
        simp only [bind_pure_comp, Functor.map, Nat.sub_zero, Nat.cast_zero, zero_add,
              List.map_map, Function.comp, List.getElem?_map, List.getElem?_range hi,
              Option.map]
    unfold Necklace.isRepetitionOf at hRep
    simp only [ne_eq] at hRep
    split at hRep
    · exact absurd hRep Bool.false_ne_true
    · split at hRep
      · exact absurd hRep Bool.false_ne_true
      · rename_i _ h2
        push_neg at h2
        exact Nat.dvd_of_mod_eq_zero h2

  -- Pointwise periodicity: w(j) = w(j % pLen)
  have hperiodic : ∀ j : ℕ, w ((j : ℕ) : ZMod n) = w ((j % pLen : ℕ) : ZMod n) := by
    intro j
    have hj_mod_n := Nat.mod_lt j (NeZero.pos n)
    have hj_mod_pLen := Nat.mod_lt j hpLen_pos
    conv_lhs => rw [show ((j : ℕ) : ZMod n) = ((j % n : ℕ) : ZMod n) from by simp []]
    -- Use isRepetitionOf to show matching
    have hRep : Necklace.isRepetitionOf w (Necklace.period w) = true := by
      unfold Necklace.period
      cases hfind : ((List.range n).tail.map (Necklace.slice w 0)).find?
          (Necklace.isRepetitionOf w) with
      | some pfx => simp only [Option.getD_some]; exact List.find?_some hfind
      | none =>
        simp only [Option.getD_none]
        unfold Necklace.isRepetitionOf
        simp only [Necklace.slice_length, Nat.sub_zero, ne_eq,
          Nat.pos_iff_ne_zero.mp (NeZero.pos n), ↓reduceIte,
          Nat.mod_self, not_true_eq_false]
        rw [List.all_eq_true]
        intro i hi
        rw [List.mem_range] at hi
        rw [decide_eq_true_eq, Nat.mod_eq_of_lt hi]
        unfold Necklace.slice
        simp only [bind_pure_comp, Functor.map, Nat.sub_zero, Nat.cast_zero, zero_add,
              List.map_map, Function.comp, List.getElem?_map, List.getElem?_range hi,
              Option.map]
    -- Extract matching from isRepetitionOf
    have hperiod_match : ∀ i, i < n →
        some (w ((i : ℕ) : ZMod n)) = (Necklace.period w)[i % pLen]? := by
      intro i hi
      unfold Necklace.isRepetitionOf at hRep
      simp only [ne_eq] at hRep
      split at hRep
      · exact absurd hRep Bool.false_ne_true
      · split at hRep
        · exact absurd hRep Bool.false_ne_true
        · rw [List.all_eq_true] at hRep
          have := hRep i (List.mem_range.mpr hi)
          rwa [decide_eq_true_eq] at this
    -- Extract period elements
    have hperiod_is_slice : Necklace.period w = Necklace.slice w 0 pLen := by
      have ⟨l, hl⟩ : ∃ l, Necklace.period w = Necklace.slice w 0 l := by
        unfold Necklace.period
        cases hfind : ((List.range n).tail.map (Necklace.slice w 0)).find?
            (Necklace.isRepetitionOf w) with
        | some pfx =>
          simp only [Option.getD_some]
          have hmem := List.mem_of_find?_eq_some hfind
          rw [List.mem_map] at hmem
          obtain ⟨l, _, rfl⟩ := hmem
          exact ⟨l, rfl⟩
        | none =>
          simp only [Option.getD_none]
          exact ⟨n, rfl⟩
      rw [hl]; congr 1
      have : pLen = l := by
        show (Necklace.period w).length = l
        rw [hl, Necklace.slice_length]; omega
      omega
    have hperiod_elem : ∀ j, j < pLen →
        (Necklace.period w)[j]? = some (w ((j : ℕ) : ZMod n)) := by
      intro j hj
      rw [hperiod_is_slice]
      unfold Necklace.slice
      simp only [bind_pure_comp, Functor.map, Nat.sub_zero, Nat.cast_zero, zero_add,
            List.map_map, Function.comp, List.getElem?_map, List.getElem?_range hj,
            Option.map]
    -- Combine to get periodicity
    have h1 := hperiod_match (j % n) hj_mod_n
    rw [Nat.mod_mod_of_dvd j hpLen_dvd_n] at h1
    have h2 := hperiod_elem (j % pLen) hj_mod_pLen
    rw [h2] at h1
    exact Option.some_injective _ h1

  -- Use pointwise periodicity to show Necklace.kStepVector equality
  unfold Necklace.kStepVector
  congr 1
  -- Necklace.slice w (m % pLen) (m % pLen + k) = Necklace.slice w m (m + k)
  unfold Necklace.slice
  simp only [Nat.add_sub_cancel_left, bind_pure_comp, Functor.map, List.map_map]
  congr 1
  ext i
  simp only [Function.comp_apply, ← Nat.cast_add]
  rw [hperiodic (m % pLen + i), hperiodic (m + i)]
  congr 2
  rw [Nat.add_mod, Nat.mod_eq_of_lt (Nat.mod_lt m hpLen_pos), ← Nat.add_mod]

/-- The counts of all distinct k-step vectors sum to the period length -/
lemma counts_sum_to_period [NeZero n] [DecidableEq α] [Fintype α]
    (w : Necklace α n) (k : ℕ) :
    (distinctKStepVectors w k).sum (countKStepVectorPerPeriod w k) = (Necklace.period w).length := by
  -- Each position in [0, p) contributes exactly once to some k-step vector's count
  -- The sum counts each position exactly once
  -- Key idea: sum over distinct vectors of (count of positions with that vector) = total positions
  -- This is essentially ∑_{v ∈ S} |{i : f(i) = v}| = |domain| where S = image of f
  let p := (Necklace.period w).length
  -- Define f : [0, p) → distinctKStepVectors mapping i to its k-step vector
  -- The sum equals ∑_{g ∈ image(f)} |f⁻¹(g)| = |domain| = p

  -- The sum counts each position i ∈ [0, p) exactly once
  -- because countKStepVectorPerPeriod w k g = |{i < p : Necklace.kStepVector w i k = g}|
  -- and each i is counted in exactly one term (for g = Necklace.kStepVector w i k)

  -- Expand the definitions
  unfold countKStepVectorPerPeriod distinctKStepVectors Necklace.allKStepVectors
  -- Goal: sum over toFinset of (List.range p).countP (Necklace.kStepVector w · k = g) = p
  -- This follows from: each i ∈ [0, p) satisfies the predicate for exactly one g
  -- namely g = Necklace.kStepVector w i k, and that g is in the toFinset

  -- Use that summing countP over all values in the image equals the domain size
  have h_partition : ∀ i : ℕ, i < p →
      (List.map (fun j => Necklace.kStepVector w j k) (List.range n)).toFinset.sum
        (fun g => if Necklace.kStepVector w i k = g then 1 else 0) = 1 := by
    intro i _
    -- Necklace.kStepVector w i k is in the toFinset
    have hmem : Necklace.kStepVector w i k ∈ (List.map (fun j => Necklace.kStepVector w j k) (List.range n)).toFinset := by
      rw [List.mem_toFinset, List.mem_map]
      use i % n
      constructor
      · exact List.mem_range.mpr (Nat.mod_lt i (NeZero.pos n))
      · exact kStepVector_mod_n w i k
    -- The sum has exactly one nonzero term
    rw [Finset.sum_eq_single (Necklace.kStepVector w i k)]
    · simp only [↓reduceIte]
    · intro g _ hne
      simp only [hne.symm, ↓reduceIte]
    · intro h
      exact absurd hmem h

  -- Now use h_partition to prove the main result
  -- The idea: each i ∈ [0, p) is counted exactly once in the sum
  -- We use that ∑_g countP(pred_g, range p) = p when pred_g partitions range p

  -- Rewrite countP as length of filter
  conv_lhs =>
    congr
    · skip
    · ext g
      rw [List.countP_eq_length_filter]

  -- Now goal: ∑_g (filter (Necklace.kStepVector w · k = g) (range p)).length = p
  -- This follows from: the filters partition (range p)

  -- Key fact: each i < p belongs to exactly one filter
  have h_unique : ∀ i, i < p →
      ∃! g ∈ (List.map (fun j => Necklace.kStepVector w j k) (List.range n)).toFinset,
        i ∈ List.filter (fun j => decide (Necklace.kStepVector w j k = g)) (List.range p) := by
    intro i hi
    use Necklace.kStepVector w i k
    constructor
    · -- Necklace.kStepVector w i k is in the toFinset
      constructor
      · rw [List.mem_toFinset, List.mem_map]
        use i % n
        exact ⟨List.mem_range.mpr (Nat.mod_lt i (NeZero.pos n)), kStepVector_mod_n w i k⟩
      · rw [List.mem_filter, List.mem_range]
        exact ⟨hi, by simp⟩
    · -- Uniqueness: any g with i in its filter must equal Necklace.kStepVector w i k
      intro g ⟨_, hg_filter⟩
      rw [List.mem_filter] at hg_filter
      simp only [decide_eq_true_eq] at hg_filter
      exact hg_filter.2.symm

  -- Use the partition lemma: sum of cardinalities of disjoint sets = total
  -- Since each i is in exactly one filter, the sum of filter lengths = p

  -- Convert to Finset for easier manipulation
  let S := (List.map (fun j => Necklace.kStepVector w j k) (List.range n)).toFinset
  let f := fun g => (List.filter (fun j => decide (Necklace.kStepVector w j k = g)) (List.range p)).toFinset

  -- The filters are pairwise disjoint
  have h_disj : (S : Set _).PairwiseDisjoint f := by
    intro g1 _ g2 _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro i hi1 hi2
    rw [List.mem_toFinset, List.mem_filter] at hi1 hi2
    simp only [decide_eq_true_eq] at hi1 hi2
    exact hne (hi1.2.symm.trans hi2.2)

  -- The union of filters covers range p
  have h_cover : ∀ i, i < p → ∃ g ∈ S, i ∈ f g := by
    intro i hi
    use Necklace.kStepVector w i k
    constructor
    · rw [List.mem_toFinset, List.mem_map]
      use i % n
      exact ⟨List.mem_range.mpr (Nat.mod_lt i (NeZero.pos n)), kStepVector_mod_n w i k⟩
    · rw [List.mem_toFinset, List.mem_filter, List.mem_range]
      exact ⟨hi, by simp⟩

  -- Convert the sum
  have hsum_eq : S.sum (fun g => (f g).card) = (Finset.range p).card := by
    rw [← Finset.card_biUnion h_disj]
    congr 1
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_range]
    constructor
    · intro ⟨g, _, hi_fg⟩
      rw [List.mem_toFinset, List.mem_filter, List.mem_range] at hi_fg
      exact hi_fg.1
    · intro hi
      exact h_cover i hi

  simp only [Finset.card_range] at hsum_eq
  convert hsum_eq using 1
  apply Finset.sum_congr rfl
  intro g _
  -- Need: (List.filter pred (List.range p)).length = (f g).card
  -- f g = (List.filter pred (List.range p)).toFinset
  -- For a nodup list, toFinset.card = length
  rw [List.toFinset_card_of_nodup]
  exact List.Nodup.filter _ List.nodup_range

/-- In a binary scale with exactly 2 distinct k-step vectors, if the counts are c1 and c2,
    then c1 + c2 = period length -/
lemma two_varieties_counts_sum [NeZero n]
    (w : BinaryNecklace n) (k : ℕ) (v1 v2 : ZVector BinaryStep)
    (hv1 : v1 ∈ distinctKStepVectors w k) (hv2 : v2 ∈ distinctKStepVectors w k) (hne : v1 ≠ v2)
    (hcard : (distinctKStepVectors w k).card = 2) :
    countKStepVectorPerPeriod w k v1 + countKStepVectorPerPeriod w k v2 = (Necklace.period w).length := by
  -- Since there are exactly 2 distinct vectors, and v1, v2 are the two distinct ones
  have hfinset : distinctKStepVectors w k = {v1, v2} := by
    ext v
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hv
      -- v is in a set of cardinality 2 that contains v1 and v2
      -- Since card = 2 and {v1, v2} ⊆ distinctKStepVectors, they must be equal
      by_cases h1 : v = v1
      · left; exact h1
      · by_cases h2 : v = v2
        · right; exact h2
        · -- v is in the set but is neither v1 nor v2
          -- This contradicts card = 2
          exfalso
          have hcard' : (distinctKStepVectors w k).card ≥ 3 := by
            have : {v1, v2, v} ⊆ distinctKStepVectors w k := by
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl | rfl
              · exact hv1
              · exact hv2
              · exact hv
            calc (distinctKStepVectors w k).card
              ≥ ({v1, v2, v} : Finset _).card := Finset.card_le_card this
              _ = 3 := by
                have hv_ne_v2 : v ≠ v2 := h2
                have hv_ne_v1 : v ≠ v1 := h1
                have hv1_ne_v2 : v1 ≠ v2 := hne
                have hv2_ne_v : v2 ≠ v := hv_ne_v2.symm
                have hv1_ne_v : v1 ≠ v := hv_ne_v1.symm
                simp only [Finset.card_insert_eq_ite, Finset.mem_insert, Finset.mem_singleton,
                           Finset.card_singleton, hv1_ne_v, hv2_ne_v, hv1_ne_v2, or_self,
                           ite_false]
          omega
    · intro hv
      rcases hv with rfl | rfl
      · exact hv1
      · exact hv2
  calc countKStepVectorPerPeriod w k v1 + countKStepVectorPerPeriod w k v2
    = ({v1, v2} : Finset _).sum (countKStepVectorPerPeriod w k) := by
        rw [Finset.sum_insert (by simp [hne]), Finset.sum_singleton]
    _ = (distinctKStepVectors w k).sum (countKStepVectorPerPeriod w k) := by rw [hfinset]
    _ = (Necklace.period w).length := counts_sum_to_period w k

/-- The period of a binary necklace (containing both L and s) has length ≥ 2.
    If period.length ≤ 1, the necklace would be constant, contradicting binary. -/
lemma period_length_ge_two_of_binary [NeZero n] (w : BinaryNecklace n)
    (hbinary : BinaryNecklace.isBinary w) : (Necklace.period w).length ≥ 2 := by
  -- The period is computed as the shortest prefix that generates w by repetition
  -- If a word contains both L and s, any generating prefix must also contain both
  -- Therefore the period has at least 2 elements
  obtain ⟨iL, hiL⟩ := hbinary.1
  obtain ⟨is, his⟩ := hbinary.2
  -- w(iL) = L and w(is) = s with iL ≠ is
  have hne : iL ≠ is := by
    intro heq
    rw [heq, his] at hiL
    cases hiL
  -- First, n ≥ 2 since we have two distinct indices
  have hn_ge_2 : n ≥ 2 := by
    by_contra hlt
    push_neg at hlt
    have hn_le_1 : n ≤ 1 := Nat.lt_succ_iff.mp hlt
    have hn_pos : n > 0 := NeZero.pos n
    have hn_eq_1 : n = 1 := Nat.le_antisymm hn_le_1 hn_pos
    -- n = 1, so ZMod 1 is a subsingleton, meaning iL = is
    subst hn_eq_1
    have : iL = is := Subsingleton.elim iL is
    exact hne this
  -- The period has length ≥ 1 (since it's a slice of positive length)
  have hperiod_pos : (Necklace.period w).length ≥ 1 := by
    unfold Necklace.period
    -- Case split on whether find? returns some or none
    cases hfind : ((List.range n).tail.map (Necklace.slice w 0)).find? (Necklace.isRepetitionOf w) with
    | none =>
      -- Fallback: slice w 0 n has length n ≥ 1
      simp only [Option.getD_none]
      rw [Necklace.slice_length]
      exact NeZero.pos n
    | some p =>
      -- Found: p is in the mapped list, so p = slice w 0 k for some k in tail
      simp only [Option.getD_some]
      have hmem : p ∈ (List.range n).tail.map (Necklace.slice w 0) :=
        List.mem_of_find?_eq_some hfind
      rw [List.mem_map] at hmem
      have ⟨k, hk_mem, hk_eq⟩ := hmem
      rw [← hk_eq, Necklace.slice_length]
      -- k is in (List.range n).tail = [1, 2, ..., n-1]
      simp only [List.tail_range, List.mem_range'] at hk_mem
      omega
  -- If period.length < 2, then period.length = 1 (since ≥ 1)
  -- A period of length 1 means w is constant, contradicting hbinary
  by_contra hlt
  push_neg at hlt
  have hperiod_one : (Necklace.period w).length = 1 := by omega
  -- A period of length 1 means w is the repetition of a single letter
  -- So w(iL) = w(is), but w(iL) = L ≠ s = w(is)
  have hconst : w iL = w is := by
    -- If period = [a] for some a, then all elements of w equal a
    -- First, analyze the period structure
    unfold Necklace.period at hperiod_one
    cases hfind : ((List.range n).tail.map (Necklace.slice w 0)).find? (Necklace.isRepetitionOf w) with
    | none =>
      -- Fallback case: period = slice w 0 n, so n = 1
      simp only [hfind, Option.getD_none, Necklace.slice_length] at hperiod_one
      -- But n ≥ 2, contradiction
      omega
    | some p =>
      -- Found case: p is a valid period with length 1
      simp only [hfind, Option.getD_some] at hperiod_one
      -- p satisfies isRepetitionOf w p
      have hrep := List.find?_some hfind
      -- p = [a] for some a (since p.length = 1)
      match p, hperiod_one with
      | [a], _ =>
        -- isRepetitionOf w [a] means all elements equal a
        unfold Necklace.isRepetitionOf at hrep
        simp only [List.length_singleton, one_ne_zero, ↓reduceIte, ne_eq, not_true_eq_false,
                   Nat.mod_one, List.getElem?_singleton, List.all_eq_true, List.mem_range,
                   decide_eq_true_eq, Option.some.injEq] at hrep
        have hiL_eq : w iL = a := by
          have := hrep iL.val (ZMod.val_lt iL)
          simp only [ZMod.natCast_zmod_val] at this
          exact this
        have his_eq : w is = a := by
          have := hrep is.val (ZMod.val_lt is)
          simp only [ZMod.natCast_zmod_val] at this
          exact this
        rw [hiL_eq, his_eq]
  rw [hiL, his] at hconst
  cases hconst

/-- For any list of BinarySteps, the count of L's plus the count of s's equals the length. -/
lemma binaryStep_count_sum (l : List BinaryStep) :
    l.count BinaryStep.L + l.count BinaryStep.s = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.count_cons, List.length_cons]
    cases x with
    | L =>
      -- (L == L) = true, (L == s) = false
      simp only [show (BinaryStep.L == BinaryStep.L) = true from rfl,
                 show (BinaryStep.L == BinaryStep.s) = false from rfl]
      simp only [ite_true, Bool.false_eq_true, ite_false]
      omega
    | s =>
      -- (s == L) = false, (s == s) = true
      simp only [show (BinaryStep.s == BinaryStep.L) = false from rfl,
                 show (BinaryStep.s == BinaryStep.s) = true from rfl]
      simp only [ite_true, Bool.false_eq_true, ite_false]
      omega

/-- The total count of a k-step vector equals k: g(L) + g(s) = k. -/
lemma kStepVector_total_count [NeZero n] (w : BinaryNecklace n) (i k : ℕ) :
    (Necklace.kStepVector w i k) BinaryStep.L + (Necklace.kStepVector w i k) BinaryStep.s = k := by
  unfold Necklace.kStepVector ZVector.ofList
  -- The slice has length k, and every element is L or s
  have hlen : (Necklace.slice w i (i + k)).length = k := by
    rw [Necklace.slice_length]; omega
  have hsum := binaryStep_count_sum (Necklace.slice w i (i + k))
  simp only [List.count_eq_countP, List.countP_eq_length_filter] at hsum
  rw [hlen] at hsum
  exact_mod_cast hsum

/-- The difference of consecutive prefix vectors equals the indicator for the letter at that position.
    That is, `Necklace.kStepVector w 0 (m+1) b - Necklace.kStepVector w 0 m b = if w(m) = b then 1 else 0`. -/
lemma kStepVector_succ_sub [NeZero n] [DecidableEq α]
    (w : Necklace α n) (m : ℕ) (b : α) :
    Necklace.kStepVector w 0 (m + 1) b - Necklace.kStepVector w 0 m b =
    if w (↑m : ZMod n) = b then 1 else 0 := by
  unfold Necklace.kStepVector ZVector.ofList Necklace.slice
  simp only [Nat.sub_zero, bind_pure_comp, Functor.map,
             Nat.cast_zero, zero_add, List.map_map,
             List.range_succ, List.map_append, List.map_singleton,
             List.filter_append, List.length_append, Nat.cast_add,
             add_sub_cancel_left]
  -- Goal: ↑(List.length (List.filter (· == b) [w ↑m])) = if w ↑m = b then 1 else 0
  split_ifs with h
  · simp [h]
  · simp [show (w (↑m : ZMod n) == b) = false from beq_eq_false_iff_ne.mpr h]

/-- For a list, the count of elements equal to `a` (via BEq filter) equals
    the sum of Prop-equality indicators cast to ℤ. -/
private lemma list_filter_beq_length_eq_map_ite_sum {α : Type*} [DecidableEq α]
    (l : List α) (a : α) :
    ((l.filter (· == a)).length : ℤ) =
    (l.map (fun x => if x = a then (1 : ℤ) else 0)).sum := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    by_cases h : hd = a
    · simp [h, ih]; omega
    · simp [show (hd == a) = false from beq_eq_false_iff_ne.mpr h, h, ih]

/-- Convert `(List.range n |>.map f).sum` to `∑ i ∈ Finset.range n, f i`. -/
private lemma list_range_map_sum_eq_finset {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (m : ℕ) :
    ((List.range m).map f).sum = ∑ i ∈ Finset.range m, f i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton, ih, Finset.sum_range_succ]

/-- Sum of k-step vector L-counts over one period = k × (L-count in period).
    Each letter in [0, p) appears in exactly k of the p k-step vectors. -/
lemma kStepVector_lettercount_sum_over_period [NeZero n] (w : BinaryNecklace n)
    (k : ℕ) (hk_pos : 0 < k) (hk_bound : k < (Necklace.period w).length)
    (a : BinaryStep) :
    ((List.range (Necklace.period w).length).map
      (fun i => (Necklace.kStepVector w i k) a)).sum =
    k * (ZVector.ofList (Necklace.period w)) a := by
  -- The k-step starting at i contains k consecutive positions: i, i+1, ..., i+k-1 (mod n)
  -- Key: Σᵢ Σₘ [w[i+m] = a] = Σₘ Σᵢ [w[i+m] = a] = Σₘ (count of a) = k × count
  let pLen := (Necklace.period w).length

  -- Step 1: Express each k-step vector count as sum over consecutive offsets
  -- Use ↑(i + m) rather than ↑i + ↑m to keep m : ℕ and avoid list coercion
  have h_expand : ∀ i, i < pLen →
    (Necklace.kStepVector w i k) a = ((List.range k).map (fun m =>
      if w (((i + m : ℕ) : ZMod n)) = a then (1 : ℤ) else 0)).sum := by
    intro i _hi
    -- Unfold to expose filter-count on the slice
    unfold Necklace.kStepVector ZVector.ofList Necklace.slice
    -- Use rw (not simp) to avoid Nat.cast_add decomposing ↑(i+m) into ↑i + ↑m
    rw [show i + k - i = k from by omega, List.map_map,
        list_filter_beq_length_eq_map_ite_sum, List.map_map]
    simp [pure, bind, Nat.cast_add, List.flatMap]
    congr 1
    ext m
    simp [Function.comp]

  -- Step 2: Rewrite LHS using h_expand
  have h_lhs_expand : ((List.range pLen).map (fun i => (Necklace.kStepVector w i k) a)).sum =
    ((List.range pLen).map (fun i =>
      ((List.range k).map (fun m =>
        if w (((i + m : ℕ) : ZMod n)) = a then (1 : ℤ) else 0)).sum)).sum := by
    congr 1
    apply List.map_congr_left
    intro i hi
    exact h_expand i (List.mem_range.mp hi)

  rw [h_lhs_expand]

  -- Step 3: Convert to Finset sums and exchange order
  simp_rw [list_range_map_sum_eq_finset]
  rw [Finset.sum_comm]

  -- Step 4: Each inner sum counts letter a in a shifted period = count(a)
  -- After exchange: ∑ m < k, (∑ i < pLen, [w(i+m)=a]) = k * count(a)
  have hpLen_pos : 0 < pLen := by omega

  -- period w is always of the form (slice w 0 k), and pLen = k
  have hperiod_is_slice : Necklace.period w = Necklace.slice w 0 pLen := by
    have ⟨l, hl⟩ : ∃ l, Necklace.period w = Necklace.slice w 0 l := by
      unfold Necklace.period
      cases hfind : ((List.range n).tail.map (Necklace.slice w 0)).find?
          (Necklace.isRepetitionOf w) with
      | some pfx =>
        simp only [Option.getD_some]
        have hmem := List.mem_of_find?_eq_some hfind
        rw [List.mem_map] at hmem
        obtain ⟨l, _, rfl⟩ := hmem
        exact ⟨l, rfl⟩
      | none =>
        simp only [Option.getD_none]
        exact ⟨n, rfl⟩
    rw [hl]; congr 1
    have : pLen = l := by
      show (Necklace.period w).length = l
      rw [hl, Necklace.slice_length]; omega
    omega

  -- isRepetitionOf w (period w) = true
  have hRep : Necklace.isRepetitionOf w (Necklace.period w) = true := by
    unfold Necklace.period
    cases hfind : ((List.range n).tail.map (Necklace.slice w 0)).find?
        (Necklace.isRepetitionOf w) with
    | some pfx => simp only [Option.getD_some]; exact List.find?_some hfind
    | none =>
      simp only [Option.getD_none]
      -- isRepetitionOf w (slice w 0 n) = true: every word is a repetition of itself
      unfold Necklace.isRepetitionOf
      simp only [Necklace.slice_length, Nat.sub_zero, ne_eq,
        Nat.pos_iff_ne_zero.mp (NeZero.pos n), ↓reduceIte,
        Nat.mod_self, not_true_eq_false]
      rw [List.all_eq_true]
      intro i hi
      rw [List.mem_range] at hi
      rw [decide_eq_true_eq, Nat.mod_eq_of_lt hi]
      -- Goal: some (w ↑i) = (slice w 0 n)[i]?
      -- slice w 0 n = List.map w (... (List.range n))
      -- so (slice w 0 n)[i]? = some (w ↑i)
      unfold Necklace.slice
      simp only [bind_pure_comp, Functor.map, Nat.sub_zero, Nat.cast_zero, zero_add,
            List.map_map, Function.comp, List.getElem?_map, List.getElem?_range hi,
            Option.map]

  -- Extract pLen | n from isRepetitionOf
  have hpLen_dvd_n : pLen ∣ n := by
    unfold Necklace.isRepetitionOf at hRep
    simp only [ne_eq] at hRep
    split at hRep
    · exact absurd hRep Bool.false_ne_true
    · split at hRep
      · exact absurd hRep Bool.false_ne_true
      · rename_i _ h2
        push_neg at h2
        exact Nat.dvd_of_mod_eq_zero h2

  -- period[j] = w(j : ZMod n) for j < pLen (since period = slice w 0 pLen)
  have hperiod_elem : ∀ j, j < pLen →
      (Necklace.period w)[j]? = some (w ((j : ℕ) : ZMod n)) := by
    intro j hj
    rw [hperiod_is_slice]
    unfold Necklace.slice
    simp only [bind_pure_comp, Functor.map, Nat.sub_zero, Nat.cast_zero, zero_add,
          List.map_map, Function.comp, List.getElem?_map, List.getElem?_range hj,
          Option.map]

  -- Extract pointwise matching from isRepetitionOf
  have hperiod_match : ∀ i, i < n →
      some (w ((i : ℕ) : ZMod n)) = (Necklace.period w)[i % pLen]? := by
    intro i hi
    unfold Necklace.isRepetitionOf at hRep
    simp only [ne_eq] at hRep
    split at hRep
    · exact absurd hRep Bool.false_ne_true
    · split at hRep
      · exact absurd hRep Bool.false_ne_true
      · rw [List.all_eq_true] at hRep
        have := hRep i (List.mem_range.mpr hi)
        rwa [decide_eq_true_eq] at this

  -- Pointwise periodicity: w(j : ZMod n) = w((j % pLen : ℕ) : ZMod n)
  have hperiodic : ∀ j : ℕ, w ((j : ℕ) : ZMod n) = w ((j % pLen : ℕ) : ZMod n) := by
    intro j
    have hj_mod_n := Nat.mod_lt j (NeZero.pos n)
    have hj_mod_pLen := Nat.mod_lt j hpLen_pos
    conv_lhs => rw [show ((j : ℕ) : ZMod n) = ((j % n : ℕ) : ZMod n) from by
      simp []]
    have h1 := hperiod_match (j % n) hj_mod_n
    rw [Nat.mod_mod_of_dvd j hpLen_dvd_n] at h1
    have h2 := hperiod_elem (j % pLen) hj_mod_pLen
    rw [h2] at h1
    exact Option.some_injective _ h1

  have h_shift : ∀ m : ℕ, ∑ i ∈ Finset.range pLen,
      (if w (((i + m : ℕ) : ZMod n)) = a then (1 : ℤ) else 0) =
      (ZVector.ofList (Necklace.period w)) a := by
    intro m
    induction m with
    | zero =>
      simp only [Nat.add_zero]
      -- period w = slice w 0 pLen, convert both sides to same sum
      unfold ZVector.ofList
      rw [list_filter_beq_length_eq_map_ite_sum, hperiod_is_slice]
      unfold Necklace.slice
      simp only [bind_pure_comp, Functor.map, Nat.sub_zero, Nat.cast_zero, zero_add,
            List.map_map, Function.comp, list_range_map_sum_eq_finset]
    | succ m ih =>
      rw [← ih]
      simp_rw [show ∀ i : ℕ, i + (m + 1) = (i + 1) + m from fun i => by omega]
      set g : ℕ → ℤ := fun j => if w (((j + m : ℕ) : ZMod n)) = a then 1 else 0 with hg_def
      -- g(pLen) = g(0) by periodicity
      have hgperiod : g pLen = g 0 := by
        simp only [hg_def, Nat.zero_add]
        congr 1
        rw [hperiodic (pLen + m), hperiodic m]
        congr 1
        rw [Nat.add_comm pLen m, Nat.add_mod_right]
      have h1 := Finset.sum_range_succ' g pLen
      have h2 := Finset.sum_range_succ g pLen
      linarith
  have h_const_sum : ∑ m ∈ Finset.range k,
      (∑ i ∈ Finset.range pLen,
        (if w (((i + m : ℕ) : ZMod n)) = a then (1 : ℤ) else 0)) =
      ∑ _m ∈ Finset.range k, (ZVector.ofList (Necklace.period w)) a :=
    Finset.sum_congr rfl (fun m _ => h_shift m)
  rw [h_const_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Discrete IVT: If f(0) and f(t) differ by more than 1, and each step changes by at most 1,
    then there's an intermediate value. -/
lemma discrete_ivt (f : ℕ → ℤ) (t : ℕ) (_ht : t > 0)
    (hstep : ∀ s < t, |f (s + 1) - f s| ≤ 1)
    (hdiff : f 0 - f t > 1 ∨ f t - f 0 > 1) :
    ∃ s, s < t ∧ min (f 0) (f t) < f s ∧ f s < max (f 0) (f t) := by
  -- In each case, find the smallest s where f crosses the threshold.
  -- The step bound |f(s+1) - f(s)| ≤ 1 forces an intermediate value at that crossing.
  rcases hdiff with hcase | hcase
  · -- Case: f 0 - f t > 1, so f 0 > f t + 1
    have hft : f t < f 0 := by omega
    -- Find smallest s with f(s) < f(0)
    have hex : ∃ s, f s < f 0 := ⟨t, hft⟩
    set s₁ := Nat.find hex
    have hspec : f s₁ < f 0 := Nat.find_spec hex
    have hle_t : s₁ ≤ t := Nat.find_min' hex hft
    have hpos : 0 < s₁ := by
      by_contra h; push_neg at h
      have : s₁ = 0 := by omega
      rw [this] at hspec; omega
    have hprev : ¬ f (s₁ - 1) < f 0 := Nat.find_min hex (by omega)
    -- |f(s₁) - f(s₁-1)| ≤ 1
    have hpred_eq : s₁ - 1 + 1 = s₁ := by omega
    have hstep' : |f s₁ - f (s₁ - 1)| ≤ 1 := by
      have := hstep (s₁ - 1) (by omega); rwa [hpred_eq] at this
    have hbounds := abs_le.mp hstep'
    -- f(s₁-1) ≥ f(0) (from hprev) and |f(s₁) - f(s₁-1)| ≤ 1 and f(s₁) < f(0)
    -- So f(s₁) = f(0) - 1
    have heq : f s₁ = f 0 - 1 := by omega
    -- s₁ < t (if s₁ = t, then f(t) = f(0)-1, contradicting f(0) - f(t) > 1)
    have hlt : s₁ < t := by
      by_contra h; push_neg at h
      have : s₁ = t := by omega
      rw [this] at heq; omega
    refine ⟨s₁, hlt, ?_, ?_⟩
    · rw [min_eq_right (le_of_lt hft)]; omega
    · rw [max_eq_left (le_of_lt hft)]; omega
  · -- Case: f t - f 0 > 1, so f t > f 0 + 1
    have hft : f 0 < f t := by omega
    -- Find smallest s with f(s) > f(0)
    have hex : ∃ s, f 0 < f s := ⟨t, hft⟩
    set s₁ := Nat.find hex
    have hspec : f 0 < f s₁ := Nat.find_spec hex
    have hle_t : s₁ ≤ t := Nat.find_min' hex hft
    have hpos : 0 < s₁ := by
      by_contra h; push_neg at h
      have : s₁ = 0 := by omega
      rw [this] at hspec; omega
    have hprev : ¬ f 0 < f (s₁ - 1) := Nat.find_min hex (by omega)
    -- |f(s₁) - f(s₁-1)| ≤ 1
    have hpred_eq : s₁ - 1 + 1 = s₁ := by omega
    have hstep' : |f s₁ - f (s₁ - 1)| ≤ 1 := by
      have := hstep (s₁ - 1) (by omega); rwa [hpred_eq] at this
    have hbounds := abs_le.mp hstep'
    -- f(s₁-1) ≤ f(0) (from hprev) and |f(s₁) - f(s₁-1)| ≤ 1 and f(s₁) > f(0)
    -- So f(s₁) = f(0) + 1
    have heq : f s₁ = f 0 + 1 := by omega
    -- s₁ < t (if s₁ = t, then f(t) = f(0)+1, contradicting f(t) - f(0) > 1)
    have hlt : s₁ < t := by
      by_contra h; push_neg at h
      have : s₁ = t := by omega
      rw [this] at heq; omega
    refine ⟨s₁, hlt, ?_, ?_⟩
    · rw [min_eq_left (le_of_lt hft)]; omega
    · rw [max_eq_right (le_of_lt hft)]; omega

/-- The slice depends only on the index modulo n (in terms of ZMod n casting).
    This follows from the definition of slice using ZMod n. -/
lemma slice_index_add_n [NeZero n] (w : Necklace α n) (i k : ℕ) :
    Necklace.slice w (i + n) (i + n + k) = Necklace.slice w i (i + k) := by
  unfold Necklace.slice
  -- Both sides have List.range k (after simplifying j - i)
  have h1 : i + n + k - (i + n) = k := by omega
  have h2 : i + k - i = k := by omega
  rw [h1, h2]
  -- Now show the inner maps are equal
  congr 1
  apply List.map_congr_left
  intro l _
  -- Goal: ↑(i + n) + l = ↑i + l (in ZMod n)
  simp only [Nat.cast_add, ZMod.natCast_self, add_zero]

/-- Necklace.kStepVector is periodic in the starting index with period n -/
lemma kStepVector_add_n [NeZero n] [DecidableEq α] (w : Necklace α n) (i k : ℕ) :
    Necklace.kStepVector w (i + n) k = Necklace.kStepVector w i k := by
  unfold Necklace.kStepVector
  congr 1
  exact slice_index_add_n w i k

/-- Helper: slice relationship when shifting start by 1.
    slice w i (i+k) = w[i] :: slice w (i+1) (i+k) for k > 0.
    Proof: LHS = [w[i], w[i+1], ..., w[i+k-1]], RHS = w[i] :: [w[i+1], ..., w[i+k-1]]. -/
lemma slice_shift_decompose [NeZero n] (w : Necklace α n) (i k : ℕ) (hk : k > 0) :
    Necklace.slice w i (i + k) = w (i : ZMod n) :: Necklace.slice w (i + 1) (i + k) := by
  unfold Necklace.slice
  have hlen1 : i + k - i = k := by omega
  have hlen2 : i + k - (i + 1) = k - 1 := by omega
  simp only [hlen1, hlen2, bind_pure_comp, Functor.map]
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp only [add_tsub_cancel_right, List.range_succ_eq_map, List.map_cons, List.map_map,
             Function.comp_def]
  -- Goal: w (↑i + ↑0) :: List.map (fun x => w ↑(i + (x + 1))) (List.range k')
  --     = w ↑i :: List.map (fun x => w ↑(i + 1 + x)) (List.range k')
  simp only [Nat.cast_zero, add_zero]
  congr 1
  ext1 x
  congr 1
  push_cast
  ring_nf

/-- Helper: extending a slice by one element at the end.
    slice w i (i+k+1) = slice w i (i+k) ++ [w[i+k]]. -/
lemma slice_extend_end [NeZero n] (w : Necklace α n) (i k : ℕ) :
    Necklace.slice w i (i + k + 1) = Necklace.slice w i (i + k) ++ [w ((i + k) : ZMod n)] := by
  unfold Necklace.slice
  have hlen1 : i + k + 1 - i = k + 1 := by omega
  have hlen2 : i + k - i = k := by omega
  simp only [hlen1, hlen2, bind_pure_comp, Functor.map]
  rw [List.range_succ]
  simp only [List.map_append, List.map_singleton]

/-- Helper: The L-count in slice [i+1, i+k+1) equals L-count in [i, i+k) minus (w[i]=L) plus (w[i+k]=L) -/
lemma slice_L_count_shift [NeZero n] (w : BinaryNecklace n) (i k : ℕ) :
    let slice1 := Necklace.slice w i (i + k)
    let slice2 := Necklace.slice w (i + 1) (i + 1 + k)
    let countL := fun l : List BinaryStep => (l.filter (· == BinaryStep.L)).length
    let delta_out : ℤ := if w (i : ZMod n) = BinaryStep.L then 1 else 0
    let delta_in : ℤ := if w ((i + k) : ZMod n) = BinaryStep.L then 1 else 0
    (countL slice2 : ℤ) = countL slice1 - delta_out + delta_in := by
  -- slice1 = [w[i], w[i+1], ..., w[i+k-1]]
  -- slice2 = [w[i+1], w[i+2], ..., w[i+k]]
  -- slice2 removes w[i] from front and adds w[i+k] to back
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · -- k = 0 case: both slices are empty
    simp only [add_zero, Necklace.slice, Nat.sub_self, List.range_zero, Nat.cast_zero]
    split_ifs <;> simp
  -- k > 0 case: use the decomposition lemmas
  have h1 : Necklace.slice w i (i + k) = w (i : ZMod n) :: Necklace.slice w (i + 1) (i + k) :=
    slice_shift_decompose w i k hk_pos
  have h2 : Necklace.slice w (i + 1) (i + 1 + k) =
            Necklace.slice w (i + 1) (i + k) ++ [w ((i + k) : ZMod n)] := by
    -- Rewrite to match slice_extend_end pattern: slice i (i + k + 1) = slice i (i + k) ++ [w (i+k)]
    -- Here i' = i + 1, k' = k - 1, so i' + k' = i + k and i' + k' + 1 = i + 1 + k
    have hend : i + 1 + k = (i + 1) + (k - 1) + 1 := by omega
    have hmid : (i + 1) + (k - 1) = i + k := by omega
    conv_lhs => rw [hend]
    rw [slice_extend_end, hmid]
    -- Goal: ... ++ [w (↑(i + 1) + ↑(k - 1))] = ... ++ [w (↑i + ↑k)]
    congr 2
    -- Show: (i + 1 : ZMod n) + (k - 1 : ZMod n) = (i : ZMod n) + (k : ZMod n)
    simp only [← Nat.cast_add, hmid]
  -- Now compute the L-counts using countL_cons and countL_append_singleton
  simp only [h1, h2, countL_cons, countL_append_singleton]
  -- The middle part (Necklace.slice w (i+1) (i+k)) appears in both expressions
  -- slice1 count = (if w[i]=L then 1 else 0) + middle_count
  -- slice2 count = middle_count + (if w[i+k]=L then 1 else 0)
  -- So slice2 count = slice1 count - delta_out + delta_in
  split_ifs with h1' h2' <;> simp

/-- Scooting a k-step vector by one position changes the L-count by at most 1.
    The new vector at position i+1 is obtained by removing w[i] and adding w[i+k]. -/
lemma kStepVector_scoot_L_count_diff [NeZero n] (w : BinaryNecklace n) (i k : ℕ) :
    let v1 := Necklace.kStepVector w i k
    let v2 := Necklace.kStepVector w (i + 1) k
    (v1 BinaryStep.L : ℤ) - 1 ≤ v2 BinaryStep.L ∧ v2 BinaryStep.L ≤ (v1 BinaryStep.L : ℤ) + 1 := by
  -- The slice for v2 is the same as v1 except:
  -- - We remove w[i] from the front
  -- - We add w[i+k] to the back
  -- So the L-count changes by: +1 if w[i+k]=L, -1 if w[i]=L, net change in {-1,0,1}
  -- Use the helper lemma
  have hshift := slice_L_count_shift w i k
  simp only at hshift
  -- Necklace.kStepVector is ZVector.ofList of the slice
  unfold Necklace.kStepVector ZVector.ofList at *
  -- The key observation: delta_out and delta_in are each 0 or 1
  -- So the change is in {-1, 0, +1}
  have h_arith : ∀ (c1 : ℕ) (d_out d_in : ℤ),
      (d_out = 0 ∨ d_out = 1) → (d_in = 0 ∨ d_in = 1) →
      let c2 : ℤ := c1 - d_out + d_in
      (c1 : ℤ) - 1 ≤ c2 ∧ c2 ≤ (c1 : ℤ) + 1 := by
    intro c1 d_out d_in hout hin
    rcases hout with rfl | rfl <;> rcases hin with rfl | rfl <;> omega
  -- Apply the arithmetic lemma
  have hdout : (if w (i : ZMod n) = BinaryStep.L then (1 : ℤ) else 0) = 0 ∨
               (if w (i : ZMod n) = BinaryStep.L then (1 : ℤ) else 0) = 1 := by
    split_ifs with h <;> simp
  have hdin : (if w ((i + k) : ZMod n) = BinaryStep.L then (1 : ℤ) else 0) = 0 ∨
              (if w ((i + k) : ZMod n) = BinaryStep.L then (1 : ℤ) else 0) = 1 := by
    split_ifs with h <;> simp
  -- The rest follows from slice_L_count_shift and arithmetic
  -- hshift says: countL slice2 = countL slice1 - delta_out + delta_in
  -- After unfolding Necklace.kStepVector and ZVector.ofList, the goal is about
  -- (List.filter (· == L) slice).length, which equals countL slice
  -- Apply h_arith with the specific counts
  set c1 := (List.filter (fun x => x == BinaryStep.L) (Necklace.slice w i (i + k))).length with hc1
  set c2 := (List.filter (fun x => x == BinaryStep.L) (Necklace.slice w (i + 1) (i + 1 + k))).length with hc2
  have hspec := h_arith c1 _ _ hdout hdin
  simp only at hspec
  -- Now hspec says: c1 - 1 ≤ c1 - delta_out + delta_in ≤ c1 + 1
  -- And by hshift, c2 = c1 - delta_out + delta_in
  -- The goal is c1 - 1 ≤ c2 ≤ c1 + 1
  simp only [← hc1, ← hc2]
  constructor <;> linarith

/-- Helper: Walking from position i by t steps, each step changes L-count by at most 1.
    So if we define f(t) = L-count at position (i + t) mod n, then |f(t+1) - f(t)| ≤ 1. -/
lemma kStepVector_walk_L_count_bounded [NeZero n] (w : BinaryNecklace n) (k i : ℕ) (t : ℕ) :
    let f := fun s => (Necklace.kStepVector w (i + s) k BinaryStep.L : ℤ)
    |f (t + 1) - f t| ≤ 1 := by
  simp only
  have hscoot := kStepVector_scoot_L_count_diff w (i + t) k
  simp only at hscoot
  have h1 : i + (t + 1) = i + t + 1 := by ring
  rw [h1]
  rw [abs_le]
  constructor <;> linarith [hscoot.1, hscoot.2]

/-- If two k-step vectors have L-counts differing by more than 1, there exists an intermediate
    k-step vector with L-count strictly between them. -/
lemma kStepVector_intermediate_exists [NeZero n] (w : BinaryNecklace n) (k i j : ℕ)
    (hi : i < n) (hj : j < n)
    (hdiff : (Necklace.kStepVector w i k BinaryStep.L : ℤ) - Necklace.kStepVector w j k BinaryStep.L > 1 ∨
             (Necklace.kStepVector w j k BinaryStep.L : ℤ) - Necklace.kStepVector w i k BinaryStep.L > 1) :
    ∃ m : ℕ, m < n ∧
      let vi := Necklace.kStepVector w i k BinaryStep.L
      let vj := Necklace.kStepVector w j k BinaryStep.L
      let vm := Necklace.kStepVector w m k BinaryStep.L
      (min vi vj < vm ∧ vm < max vi vj) := by
  -- Define f(t) = L-count at position (i + t) mod n
  -- Find t such that (i + t) mod n = j
  -- Apply discrete_ivt
  let f := fun t => (Necklace.kStepVector w (i + t) k BinaryStep.L : ℤ)
  -- Find t with (i + t) ≡ j (mod n), i.e., t = (j - i) mod n
  -- But we work with ℕ, so t = (j + n - i) mod n when j < i
  let t := if j ≥ i then j - i else j + n - i
  have ht_pos : t > 0 := by
    simp only [t]
    split_ifs with h
    · -- j ≥ i
      by_contra ht_zero
      push_neg at ht_zero
      have hle : j - i ≤ 0 := ht_zero
      have hji : j = i := by omega
      subst hji
      rcases hdiff with hdiff | hdiff <;> simp at hdiff
    · -- j < i
      omega
  have ht_lt_n : t < n := by
    simp only [t]
    split_ifs with h <;> omega
  have hf_t_eq : f t = Necklace.kStepVector w j k BinaryStep.L := by
    simp only [f, t]
    split_ifs with h
    · -- j ≥ i: i + (j - i) = j
      have heq : i + (j - i) = j := Nat.add_sub_cancel' h
      rw [heq]
    · -- j < i: i + (j + n - i) = j + n, and Necklace.kStepVector w (j + n) k = Necklace.kStepVector w j k
      have heq : i + (j + n - i) = j + n := by omega
      rw [heq, kStepVector_add_n w j k]
  have hf_0_eq : f 0 = Necklace.kStepVector w i k BinaryStep.L := by simp [f]
  have hstep : ∀ s < t, |f (s + 1) - f s| ≤ 1 := by
    intro s _
    exact kStepVector_walk_L_count_bounded w k i s
  have hdiff' : f 0 - f t > 1 ∨ f t - f 0 > 1 := by
    simp only [hf_0_eq, hf_t_eq]
    exact hdiff
  obtain ⟨s, hs_lt, hs_intermed⟩ := discrete_ivt f t ht_pos hstep hdiff'
  -- s is the intermediate position, relative to i
  -- The actual position is (i + s) mod n
  use (i + s) % n
  constructor
  · exact Nat.mod_lt (i + s) (NeZero.pos n)
  · simp only [hf_0_eq, hf_t_eq] at hs_intermed
    -- Need to show Necklace.kStepVector w ((i + s) % n) k = Necklace.kStepVector w (i + s) k
    rw [kStepVector_mod_n w (i + s) k]
    exact hs_intermed

/-- In a MOS, any two distinct k-step vectors can differ in L-count by at most 1.
    Otherwise, there would be more than 2 k-step vectors. -/
lemma mos_kStepVector_L_count_diff_le_one [NeZero n] (w : BinaryNecklace n)
    (hw : BinaryNecklace.isMOS w) (k : ℕ) (hk_pos : 0 < k) (hk_lt : k < n)
    (v1 v2 : ZVector BinaryStep) (hv1 : v1 ∈ distinctKStepVectors w k)
    (hv2 : v2 ∈ distinctKStepVectors w k) :
    (v1 BinaryStep.L : ℤ) - 1 ≤ v2 BinaryStep.L ∧ v2 BinaryStep.L ≤ (v1 BinaryStep.L : ℤ) + 1 := by
  -- If the difference were > 1, kStepVector_intermediate_exists would give a third variety
  -- This contradicts the MOS property of variety ≤ 2
  -- Extract positions i, j such that v1 = Necklace.kStepVector w i k, v2 = Necklace.kStepVector w j k
  unfold distinctKStepVectors Necklace.allKStepVectors at hv1 hv2
  rw [List.mem_toFinset, List.mem_map] at hv1 hv2
  obtain ⟨i, hi_range, hv1_eq⟩ := hv1
  obtain ⟨j, hj_range, hv2_eq⟩ := hv2
  rw [List.mem_range] at hi_range hj_range
  -- Rewrite in terms of Necklace.kStepVector
  rw [← hv1_eq, ← hv2_eq]
  -- Prove by contradiction: if difference > 1, we get a third variety
  by_contra h_not
  simp only [not_and_or, not_le] at h_not
  have hdiff : (Necklace.kStepVector w i k BinaryStep.L : ℤ) - Necklace.kStepVector w j k BinaryStep.L > 1 ∨
               (Necklace.kStepVector w j k BinaryStep.L : ℤ) - Necklace.kStepVector w i k BinaryStep.L > 1 := by
    rcases h_not with h_left | h_right
    · left; linarith
    · right; linarith
  -- Use kStepVector_intermediate_exists to get intermediate position m
  obtain ⟨m, hm_lt, hm_intermed⟩ := kStepVector_intermediate_exists w k i j hi_range hj_range hdiff
  -- The k-step vector at m is distinct from both v1 and v2
  let vm := Necklace.kStepVector w m k
  have hvm_mem : vm ∈ distinctKStepVectors w k := by
    unfold distinctKStepVectors Necklace.allKStepVectors
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨m, List.mem_range.mpr hm_lt, rfl⟩
  -- vm has L-count strictly between v1 and v2, so different from both
  simp only at hm_intermed
  have hmin := hm_intermed.1
  have hmax := hm_intermed.2
  have hvm_ne_v1 : vm ≠ Necklace.kStepVector w i k := by
    intro heq
    have hL_eq : vm BinaryStep.L = Necklace.kStepVector w i k BinaryStep.L := congr_arg (· BinaryStep.L) heq
    simp only [vm] at hL_eq
    rw [hL_eq] at hmin hmax
    simp only [min_lt_iff, lt_max_iff] at hmin hmax
    omega
  have hvm_ne_v2 : vm ≠ Necklace.kStepVector w j k := by
    intro heq
    have hL_eq : vm BinaryStep.L = Necklace.kStepVector w j k BinaryStep.L := congr_arg (· BinaryStep.L) heq
    simp only [vm] at hL_eq
    rw [hL_eq] at hmin hmax
    simp only [min_lt_iff, lt_max_iff] at hmin hmax
    omega
  -- Need to show v1 ≠ v2 as well (follows from hdiff)
  have hv1_ne_v2 : Necklace.kStepVector w i k ≠ Necklace.kStepVector w j k := by
    intro heq
    have hL_eq : Necklace.kStepVector w i k BinaryStep.L = Necklace.kStepVector w j k BinaryStep.L := by rw [heq]
    rcases hdiff with hdiff | hdiff <;> simp only [hL_eq] at hdiff <;> linarith
  -- Now we have three distinct vectors
  have hcard_ge_3 : (distinctKStepVectors w k).card ≥ 3 := by
    have h3 : ({Necklace.kStepVector w i k, Necklace.kStepVector w j k, vm} : Finset (ZVector BinaryStep)).card = 3 := by
      rw [Finset.card_insert_eq_ite, Finset.card_insert_eq_ite, Finset.card_singleton]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      simp only [hvm_ne_v1.symm, hvm_ne_v2.symm, hv1_ne_v2, false_or, ite_false]
    have hsub : {Necklace.kStepVector w i k, Necklace.kStepVector w j k, vm} ⊆ distinctKStepVectors w k := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · unfold distinctKStepVectors Necklace.allKStepVectors
        rw [List.mem_toFinset, List.mem_map]
        exact ⟨i, List.mem_range.mpr hi_range, rfl⟩
      · unfold distinctKStepVectors Necklace.allKStepVectors
        rw [List.mem_toFinset, List.mem_map]
        exact ⟨j, List.mem_range.mpr hj_range, rfl⟩
      · exact hvm_mem
    calc (distinctKStepVectors w k).card
        ≥ ({Necklace.kStepVector w i k, Necklace.kStepVector w j k, vm} : Finset (ZVector BinaryStep)).card :=
          Finset.card_le_card hsub
      _ = 3 := h3
  -- But MOS property says card ≤ 2
  have hcard_le_2 : (distinctKStepVectors w k).card ≤ 2 := by
    rw [distinctKStepVectors_card_eq]
    exact hw.2 k hk_pos hk_lt
  -- Contradiction: 3 ≤ card ≤ 2
  omega

/-- In a MOS where the k-step has exactly 2 varieties with counts (p-1, 1),
    we have gcd(k, p) = 1. -/
lemma p_minus_one_occurrences_implies_coprime_to_period [NeZero n]
    (w : BinaryNecklace n) (hw : BinaryNecklace.isMOS w)
    (k : ℕ) (hk_pos : 0 < k) (hk_bound : k < (Necklace.period w).length)
    (g : ZVector BinaryStep)
    (hcount : countKStepVectorPerPeriod w k g = (Necklace.period w).length - 1) :
    Nat.Coprime k (Necklace.period w).length := by
  let pLen := (Necklace.period w).length
  have hpLen_ge_2 : pLen ≥ 2 := period_length_ge_two_of_binary w hw.1
  have hk_lt_n : k < n := lt_of_lt_of_le hk_bound (Necklace.period_length_le_n w)

  -- Step 1: Find a position i₀ where Necklace.kStepVector = g (count ≥ 1 since pLen ≥ 2)
  have ⟨i₀, hi₀_lt, hi₀_eq⟩ : ∃ i₀, i₀ < pLen ∧ Necklace.kStepVector w i₀ k = g := by
    by_contra h
    push_neg at h
    have : countKStepVectorPerPeriod w k g = 0 := by
      unfold countKStepVectorPerPeriod
      rw [List.countP_eq_zero]
      intro i hi
      rw [List.mem_range] at hi
      simp [h i hi]
    omega

  -- Step 2: Find j₀ where Necklace.kStepVector ≠ g (since count = pLen - 1 < pLen)
  have ⟨j₀, hj₀_lt, hj₀_ne⟩ : ∃ j₀, j₀ < pLen ∧ Necklace.kStepVector w j₀ k ≠ g := by
    by_contra h
    push_neg at h
    have : countKStepVectorPerPeriod w k g = pLen := by
      show (List.range pLen).countP (fun i => decide (Necklace.kStepVector w i k = g)) = pLen
      have h_all : ∀ i ∈ List.range pLen, decide (Necklace.kStepVector w i k = g) = true := by
        intro i hi; rw [List.mem_range] at hi; simp [h i hi]
      rw [List.countP_eq_length.mpr h_all, List.length_range]
    omega
  let g' := Necklace.kStepVector w j₀ k

  have hpLen_le_n : pLen ≤ n := Necklace.period_length_le_n w

  -- Step 3: g and g' are in distinctKStepVectors
  have hg_mem : g ∈ distinctKStepVectors w k := by
    unfold distinctKStepVectors Necklace.allKStepVectors
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨i₀, List.mem_range.mpr (by omega), hi₀_eq⟩
  have hg'_mem : g' ∈ distinctKStepVectors w k := by
    unfold distinctKStepVectors Necklace.allKStepVectors
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨j₀, List.mem_range.mpr (by omega), rfl⟩

  -- Step 4: j₀ is the unique position where Necklace.kStepVector ≠ g
  have huniq : ∀ i, i ∈ Finset.range pLen → i ≠ j₀ → Necklace.kStepVector w i k = g := by
    intro i hi hi_ne
    rw [Finset.mem_range] at hi
    by_contra h_ne_g
    -- countP(=g) = pLen - 1
    have hcount' : (List.range pLen).countP (fun j => decide (Necklace.kStepVector w j k = g)) = pLen - 1 :=
      hcount
    -- filter(≠g) has length 1
    have hlen_neg : ((List.range pLen).filter (fun j => !decide (Necklace.kStepVector w j k = g))).length = 1 := by
      have hfilter_sum : ∀ (l : List ℕ) (p : ℕ → Bool),
          (l.filter p).length + (l.filter (fun a => !p a)).length = l.length := by
        intro l p; induction l with
        | nil => simp
        | cons a t ih => cases hp : p a <;> simp_all <;> omega
      have h1 := hfilter_sum (List.range pLen) (fun j => decide (Necklace.kStepVector w j k = g))
      rw [List.length_range] at h1
      have h2 : (List.range pLen).countP (fun j => decide (Necklace.kStepVector w j k = g)) =
          ((List.range pLen).filter (fun j => decide (Necklace.kStepVector w j k = g))).length :=
        List.countP_eq_length_filter
      omega
    -- filter(≠g) is a singleton [a], so both i and j₀ equal a, contradicting i ≠ j₀
    obtain ⟨a, ha⟩ : ∃ a, (List.range pLen).filter (fun j => !decide (Necklace.kStepVector w j k = g)) = [a] := by
      set l := (List.range pLen).filter (fun j => !decide (Necklace.kStepVector w j k = g)) with hl_def
      rcases l with _ | ⟨a, _ | ⟨_, _⟩⟩
      · simp at hlen_neg
      · exact ⟨a, rfl⟩
      · simp at hlen_neg
    have hi_mem : i ∈ (List.range pLen).filter (fun j => !decide (Necklace.kStepVector w j k = g)) :=
      List.mem_filter.mpr ⟨List.mem_range.mpr hi, by simp [h_ne_g]⟩
    have hj₀_mem : j₀ ∈ (List.range pLen).filter (fun j => !decide (Necklace.kStepVector w j k = g)) :=
      List.mem_filter.mpr ⟨List.mem_range.mpr hj₀_lt, by simp [hj₀_ne]⟩
    rw [ha] at hi_mem hj₀_mem
    simp at hi_mem hj₀_mem
    exact hi_ne (hi_mem.trans hj₀_mem.symm)

  -- Step 5: Sum equation via Finset.sum_eq_single
  -- ∑_{i < pLen} (Necklace.kStepVector w i k)(L) = k * periodCount(L)
  have hsum := kStepVector_lettercount_sum_over_period w k hk_pos hk_bound BinaryStep.L
  rw [list_range_map_sum_eq_finset] at hsum
  -- Split: ∑ = pLen * g(L) + (g'(L) - g(L))
  have hsum_diff : ∑ i ∈ Finset.range pLen, ((Necklace.kStepVector w i k) BinaryStep.L - g BinaryStep.L) =
      g' BinaryStep.L - g BinaryStep.L := by
    apply Finset.sum_eq_single j₀
    · intro i hi hi_ne
      have := huniq i hi hi_ne
      simp [this]
    · intro habs; exact absurd (Finset.mem_range.mpr hj₀_lt) habs
  have hsum_split : (↑pLen : ℤ) * g BinaryStep.L + (g' BinaryStep.L - g BinaryStep.L) =
      ↑k * (ZVector.ofList (Necklace.period w)) BinaryStep.L := by
    have h1 : ∑ i ∈ Finset.range pLen, (Necklace.kStepVector w i k) BinaryStep.L =
        ∑ i ∈ Finset.range pLen, (g BinaryStep.L + ((Necklace.kStepVector w i k) BinaryStep.L - g BinaryStep.L)) :=
      Finset.sum_congr rfl (fun i _ => by ring)
    rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hsum_diff] at hsum
    linarith

  -- Step 6: |g(L) - g'(L)| = 1
  have hdiff_le := mos_kStepVector_L_count_diff_le_one w hw k hk_pos hk_lt_n g g' hg_mem hg'_mem
  have hg_ne_g' : g ≠ g' := Ne.symm hj₀_ne
  have hg_total : (g BinaryStep.L : ℤ) + g BinaryStep.s = k := by
    rw [← hi₀_eq]; exact_mod_cast kStepVector_total_count w i₀ k
  have hg'_total : (g' BinaryStep.L : ℤ) + g' BinaryStep.s = k :=
    show (Necklace.kStepVector w j₀ k) BinaryStep.L + (Necklace.kStepVector w j₀ k) BinaryStep.s = k by
      exact_mod_cast kStepVector_total_count w j₀ k
  have hdiff_eq_one : g BinaryStep.L - g' BinaryStep.L = 1 ∨
                      g BinaryStep.L - g' BinaryStep.L = -1 := by
    have hL_ne : g BinaryStep.L ≠ g' BinaryStep.L := by
      intro heq
      have hs_eq : g BinaryStep.s = g' BinaryStep.s := by linarith
      exact hg_ne_g' (funext (fun a => by cases a <;> assumption))
    rcases Int.lt_or_lt_of_ne (sub_ne_zero.mpr hL_ne) with hneg | hpos
    · right; omega
    · left; omega

  -- Step 7: Bézout identity: pLen * g(L) - k * periodCount(L) = ±1
  have hbezout : (↑pLen : ℤ) * g BinaryStep.L -
      ↑k * (ZVector.ofList (Necklace.period w)) BinaryStep.L = 1 ∨
      (↑pLen : ℤ) * g BinaryStep.L -
      ↑k * (ZVector.ofList (Necklace.period w)) BinaryStep.L = -1 := by
    rcases hdiff_eq_one with h | h <;> [left; right] <;> linarith

  -- Step 8: gcd(k, pLen) divides ±1, hence equals 1
  show Nat.gcd k pLen = 1
  have hdvd : (Nat.gcd k pLen : ℤ) ∣ 1 ∨ (Nat.gcd k pLen : ℤ) ∣ -1 := by
    have hdvd_k : (Nat.gcd k pLen : ℤ) ∣ ↑k :=
      Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left k pLen)
    have hdvd_p : (Nat.gcd k pLen : ℤ) ∣ ↑pLen :=
      Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right k pLen)
    rcases hbezout with h | h
    · left; calc (↑(Nat.gcd k pLen) : ℤ)
          ∣ ↑pLen * g BinaryStep.L - ↑k * (ZVector.ofList (Necklace.period w)) BinaryStep.L :=
            dvd_sub (dvd_mul_of_dvd_left hdvd_p _) (dvd_mul_of_dvd_left hdvd_k _)
        _ = 1 := h
    · right; calc (↑(Nat.gcd k pLen) : ℤ)
          ∣ ↑pLen * g BinaryStep.L - ↑k * (ZVector.ofList (Necklace.period w)) BinaryStep.L :=
            dvd_sub (dvd_mul_of_dvd_left hdvd_p _) (dvd_mul_of_dvd_left hdvd_k _)
        _ = -1 := h
  have hgcd_pos : 0 < Nat.gcd k pLen := Nat.pos_of_ne_zero (by
    intro h; simp [h] at hdvd)
  rcases hdvd with h | h
  · exact Nat.le_antisymm (by exact_mod_cast Int.le_of_dvd one_pos h) hgcd_pos
  · have : (Nat.gcd k pLen : ℤ) ∣ 1 := by rwa [Int.dvd_neg] at h
    exact Nat.le_antisymm (by exact_mod_cast Int.le_of_dvd one_pos this) hgcd_pos

/-- If g is a generator of a MOS scale, then the step size k from IsGenerator
    is coprime to the period length.

    Proof: From the prefix bijection, prefix(1) = j₁·g + c₁·p, giving the
    total-count equation j₁·k + c₁·pLen = 1 (a Bézout identity). -/
lemma generator_implies_coprime_to_period [NeZero n]
    (w : BinaryNecklace n) (_hw : BinaryNecklace.isMOS w)
    (g : ZVector BinaryStep) (hg : IsGenerator w g) :
    let per := Necklace.period w
    let pLen := per.length
    ∃ k : ℕ, k < pLen ∧ (∃ i : Fin n, Necklace.kStepVector w i.val k = g) ∧ Nat.Coprime k pLen := by
  obtain ⟨⟨k₀, hk₀_lt_pLen, i₀, hg_appears⟩, r, hprefix_fwd, _hprefix_bwd⟩ := hg
  let per := Necklace.period w
  let pLen := per.length
  let pVec := ZVector.ofList per
  let w' := fun i => w (i + r)
  have hpLen_ge_2 : pLen ≥ 2 := period_length_ge_two_of_binary w _hw.1
  have hpLen_pos : 0 < pLen := by omega
  -- From prefix(1) = j₁·g + c₁·p, extract j₁ and c₁
  obtain ⟨j₁, c₁, hpfx1⟩ := hprefix_fwd ⟨0, hpLen_pos⟩
  -- Total count of prefix(1) is 1
  have hpfx1_total : (Necklace.kStepVector w' 0 1) BinaryStep.L + (Necklace.kStepVector w' 0 1) BinaryStep.s = 1 := by
    unfold Necklace.kStepVector Necklace.slice
    simp only [Nat.add_sub_cancel_left, List.range_one, ZVector.ofList]
    cases hw'0 : w' 0 <;> simp [hw'0]
  -- g has total count k₀
  have hg_total : g BinaryStep.L + g BinaryStep.s = k₀ := by
    rw [← hg_appears]
    exact_mod_cast kStepVector_total_count w i₀.val k₀
  -- pVec has total count pLen
  have hpVec_total : pVec BinaryStep.L + pVec BinaryStep.s = pLen := by
    show (ZVector.ofList per) BinaryStep.L + (ZVector.ofList per) BinaryStep.s = pLen
    unfold ZVector.ofList
    have hsum := binaryStep_count_sum per
    simp only [List.count_eq_countP, List.countP_eq_length_filter] at hsum
    norm_cast
  -- From the prefix equation: j₁·k₀ + c₁·pLen = 1 (Bézout identity)
  have hbezout : (j₁.val : ℤ) * k₀ + c₁ * pLen = 1 := by
    have hL := hpfx1 BinaryStep.L
    have hs := hpfx1 BinaryStep.s
    simp only [Nat.zero_add] at hL hs
    have heq : (Necklace.kStepVector w' 0 1) BinaryStep.L + (Necklace.kStepVector w' 0 1) BinaryStep.s =
               ↑j₁.val * (g BinaryStep.L + g BinaryStep.s) + c₁ * (pVec BinaryStep.L + pVec BinaryStep.s) := by
      calc (Necklace.kStepVector w' 0 1) BinaryStep.L + (Necklace.kStepVector w' 0 1) BinaryStep.s
        = (↑j₁.val * g BinaryStep.L + c₁ * pVec BinaryStep.L) +
          (↑j₁.val * g BinaryStep.s + c₁ * pVec BinaryStep.s) := by rw [hL, hs]
        _ = ↑j₁.val * (g BinaryStep.L + g BinaryStep.s) + c₁ * (pVec BinaryStep.L + pVec BinaryStep.s) := by ring
    rw [hpfx1_total, hg_total, hpVec_total] at heq
    exact heq.symm
  -- Derive Nat.Coprime k₀ pLen from the Bézout identity
  use k₀
  refine ⟨hk₀_lt_pLen, ⟨i₀, hg_appears⟩, ?_⟩
  -- Nat.Coprime k₀ pLen unfolds to Nat.gcd k₀ pLen = 1
  -- We have j₁·k₀ + c₁·pLen = 1 as integers, so gcd(k₀, pLen) | 1
  show Nat.gcd k₀ pLen = 1
  have hdvd : (Nat.gcd k₀ pLen : ℤ) ∣ 1 := by
    have hdvd_k : (Nat.gcd k₀ pLen : ℤ) ∣ ↑k₀ := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left k₀ pLen)
    have hdvd_p : (Nat.gcd k₀ pLen : ℤ) ∣ ↑pLen := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right k₀ pLen)
    calc (↑(Nat.gcd k₀ pLen) : ℤ)
      ∣ ↑j₁.val * ↑k₀ + c₁ * ↑pLen := dvd_add (dvd_mul_of_dvd_right hdvd_k _) (dvd_mul_of_dvd_right hdvd_p _)
      _ = 1 := hbezout
  have hgcd_pos : 0 < Nat.gcd k₀ pLen := Nat.pos_of_ne_zero (by
    intro h; simp [h] at hdvd)
  have hgcd_le : Nat.gcd k₀ pLen ≤ 1 := by exact_mod_cast Int.le_of_dvd one_pos hdvd
  omega

/-- For a binary list (over BinaryStep), filterL.length + filterS.length = length -/
lemma binary_list_filter_sum (l : List BinaryStep) :
    (l.filter (· == BinaryStep.L)).length + (l.filter (· == BinaryStep.s)).length = l.length := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.filter_cons, List.length_cons]
    cases hd <;> simp <;> omega

/-- If `a` is in the prefix `l₁` and satisfies `p`, then `find?` on `l₁ ++ l₂`
    returns some element from `l₁`. -/
private lemma find?_some_of_mem_prefix {α : Type*} (p : α → Bool)
    (l₁ l₂ : List α) (a : α) (ha : a ∈ l₁) (hp : p a = true) :
    ∃ b, (l₁ ++ l₂).find? p = some b ∧ b ∈ l₁ := by
  induction l₁ with
  | nil => simp at ha
  | cons x xs ih =>
    rw [List.cons_append]
    unfold List.find?
    cases hpx : p x
    · -- p x = false: find? skips x
      have ha' : a ∈ xs := by
        rcases List.mem_cons.mp ha with rfl | h
        · simp [hp] at hpx
        · exact h
      obtain ⟨b, hb, hb_mem⟩ := ih ha'
      exact ⟨b, hb, List.mem_cons_of_mem x hb_mem⟩
    · -- p x = true: find? returns x
      exact ⟨x, rfl, List.mem_cons.mpr (Or.inl rfl)⟩

/-- If `w` has translational period `d` (with `d ∣ n`, `0 < d < n`),
    then `(Necklace.period w).length ≤ d`. -/
lemma Necklace.period_length_le_of_translational_period {n : ℕ} [NeZero n]
    {α : Type*} [DecidableEq α]
    (w : Necklace α n) (d : ℕ) (hd_pos : 0 < d) (hd_lt_n : d < n) (hd_dvd : d ∣ n)
    (hper : ∀ (i : ZMod n), w i = w (i + (d : ZMod n))) :
    (Necklace.period w).length ≤ d := by
  -- Step 1: w(i) = w(i % d) for all i (iterate the translational period)
  have hmod : ∀ (i : ℕ), w (i : ZMod n) = w ((i % d : ℕ) : ZMod n) := by
    intro i
    have hmult : ∀ (j m : ℕ), w (j : ZMod n) = w ((j + m * d : ℕ) : ZMod n) := by
      intro j m; induction m with
      | zero => simp
      | succ m ih =>
        rw [ih, hper ((j + m * d : ℕ) : ZMod n)]
        congr 1; push_cast; ring
    have h := hmult (i % d) (i / d)
    rw [show i % d + i / d * d = i from by rw [mul_comm (i / d) d]; exact Nat.mod_add_div i d] at h
    exact h.symm
  -- Step 2: isRepetitionOf w (slice w 0 d) = true
  have hisRep : Necklace.isRepetitionOf w (Necklace.slice w 0 d) = true := by
    unfold Necklace.isRepetitionOf
    simp only [Necklace.slice_length, Nat.sub_zero]
    rw [if_neg (by omega), if_neg (not_not.mpr (by obtain ⟨k, hk⟩ := hd_dvd; simp [hk]))]
    rw [List.all_eq_true]
    intro i hi; simp only [List.mem_range] at hi
    simp only [decide_eq_true_eq, Necklace.slice, bind_pure_comp, Functor.map, Nat.sub_zero,
               List.map_map, Function.comp, Nat.cast_zero, zero_add,
               List.getElem?_map, List.getElem?_range (Nat.mod_lt i hd_pos),
               Option.map, Option.some.injEq]
    exact hmod i
  -- Step 3: period finds something with length ≤ d
  unfold Necklace.period
  -- d ∈ (List.range n).tail
  have hd_mem : d ∈ (List.range n).tail := by
    rw [List.tail_range]
    exact List.mem_range'.mpr ⟨d - 1, by omega, by omega⟩
  -- Split [1, ..., n-1] = [1, ..., d] ++ [d+1, ..., n-1]
  have hsplit : (List.range n).tail =
      List.range' 1 d ++ List.range' (1 + d) (n - 1 - d) := by
    have h := @List.range'_append 1 d (n - 1 - d) 1
    simp only [Nat.one_mul] at h
    rw [List.tail_range, h]
    congr 1; omega
  rw [hsplit, List.map_append]
  -- slice w 0 d is in the first part of the map
  have hd_in_first : Necklace.slice w 0 d ∈ (List.range' 1 d).map (Necklace.slice w 0) := by
    rw [List.mem_map]
    exact ⟨d, List.mem_range'.mpr ⟨d - 1, by omega, by omega⟩, rfl⟩
  -- find? returns something from the first part
  obtain ⟨pfx, hfind, hpfx_mem⟩ := find?_some_of_mem_prefix
    (Necklace.isRepetitionOf w) _ _ _ hd_in_first hisRep
  rw [hfind]; simp only [Option.getD_some]
  -- pfx is in the first part, so pfx = slice w 0 k for some k ≤ d
  rw [List.mem_map] at hpfx_mem
  obtain ⟨k, hk_mem, hk_eq⟩ := hpfx_mem
  rw [← hk_eq, Necklace.slice_length]
  obtain ⟨i, hi, hk_val⟩ := List.mem_range'.mp hk_mem
  omega

/-- If g is a generator for a MOS scale w, then there exists some step size k such that
    g occurs at exactly (period length - 1) positions per period.

    Proof outline:
    1. From IsGenerator, g is period-reduced (appears as some k-step vector)
    2. There's a rotation r where prefixes biject with {j·g + k·p : 0 ≤ j < |p|}
    3. Let gen_len be the prefix length where j = 1 (the "generator length")
    4. At this gen_len, g appears as the gen_len-step vector at position r
    5. By MOS two-variety property, gen_len-step vectors come in exactly 2 types
    6. One type (containing g) occurs p-1 times, the other occurs 1 time
    7. Since g is period-reduced, g is the majority vector -/
theorem generator_implies_p_minus_one_occurrences [NeZero n]
    (w : BinaryNecklace n) (hw : BinaryNecklace.isMOS w)
    (g : ZVector BinaryStep) (hg : IsGenerator w g) :
    let p := (Necklace.period w).length
    ∃ k : ℕ, 0 < k ∧ k < p ∧ countKStepVectorPerPeriod w k g = p - 1 := by
  -- Extract the components of IsGenerator
  obtain ⟨⟨k₀, hk₀_lt_pLen, i₀, hg_appears⟩, r, hprefix_fwd, hprefix_bwd⟩ := hg
  -- g appears as a k₀-step vector at position i₀
  -- There's a rotation r where prefixes correspond to j·g + k·p
  -- From hprefix_bwd with j = 1, we get the generator length

  let per := Necklace.period w
  let pLen := per.length
  let pVec := ZVector.ofList per
  let w' := fun i => w (i + r)

  -- Need pLen > 0 for Fin pLen to be inhabited
  -- The period is non-empty (it's a slice with positive length)
  have hpLen_pos : 0 < pLen := by
    show 0 < (Necklace.period w).length
    unfold Necklace.period
    cases h : (List.range n).tail.map (Necklace.slice w 0) |>.find? (Necklace.isRepetitionOf w) with
    | none => simp only [Option.getD, Necklace.slice_length]; exact NeZero.pos n
    | some pfx =>
      simp only [Option.getD]
      -- pfx is in the mapped list, so it's a slice of positive length
      have hmem : pfx ∈ (List.range n).tail.map (Necklace.slice w 0) := List.mem_of_find?_eq_some h
      rw [List.mem_map] at hmem
      obtain ⟨k, hk_mem, hk_eq⟩ := hmem
      rw [← hk_eq, Necklace.slice_length]
      -- k is in tail of (range n), so k > 0 and k < n
      have hk_in_range : k ∈ List.range n := List.mem_of_mem_tail hk_mem
      rw [List.mem_range] at hk_in_range
      -- tail of (range n) = [1, 2, ..., n-1], so k ≥ 1
      have hk_pos : k > 0 := by
        have hn_pos : n > 0 := NeZero.pos n
        match hn : n with
        | 0 => omega
        | m + 1 =>
          simp only [hn, List.range_succ_eq_map, List.tail_cons] at hk_mem
          rw [List.mem_map] at hk_mem
          obtain ⟨j, _, rfl⟩ := hk_mem
          omega
      omega

  -- For a non-degenerate MOS, period length ≥ 2
  -- isMOS includes isBinary, and a binary word (containing both L and s) has period ≥ 2
  have hpLen_ge_2 : pLen ≥ 2 := period_length_ge_two_of_binary w hw.1

  have hone_lt : (1 : ℕ) < pLen := by omega

  -- From hprefix_bwd with j = 1, get the generator length
  obtain ⟨gen_len_fin, kCoeff, hgen_eq⟩ := hprefix_bwd ⟨1, hone_lt⟩

  -- gen_len = gen_len_fin.val + 1 is the generator length (prefix length where j = 1)
  -- Note: gen_len ∈ {1, ..., pLen} since gen_len_fin.val ∈ {0, ..., pLen-1}
  let gen_len := gen_len_fin.val + 1

  -- At the generator length, the prefix vector at position 0 (in rotated word) equals 1·g + kCoeff·p
  have hprefix_at_gen : ∀ a, (Necklace.kStepVector w' 0 gen_len) a = 1 * g a + kCoeff * pVec a := hgen_eq

  -- Show 0 < gen_len ≤ pLen
  have hgen_pos : 0 < gen_len := by omega
  have hgen_le : gen_len ≤ pLen := by
    have hlt : gen_len_fin.val < pLen := gen_len_fin.isLt
    show gen_len_fin.val + 1 ≤ pLen
    omega

  -- The key theorem about generators in MOS scales:
  -- For the generator g, there exists a step size k where:
  -- 1. 0 < k < pLen
  -- 2. g occurs at exactly pLen - 1 positions
  --
  -- The proof uses the prefix bijection: prefixes at lengths 1, ..., pLen
  -- correspond bijectively to j ∈ {0, ..., pLen-1}. The "generator length"
  -- is the prefix length where j = 1, which gives Necklace.kStepVector = g + kCoeff·p.
  --
  -- For MOS scales, at the generator length (when gen_len < pLen):
  -- - The k-step vectors come in exactly 2 varieties
  -- - One variety occurs pLen - 1 times (the "perfect" generator)
  -- - The other occurs 1 time (the "imperfect" generator)
  -- - g is the perfect generator (up to period multiples)
  --
  -- When gen_len = pLen, we use k₀ from hg_appears instead.

  -- Use k₀ where g directly appears as a k-step vector
  -- The deep theorem is that k₀ has the (pLen-1, 1) distribution for generators
  -- First prove 0 < k₀ (needed in multiple places below)
  have hk₀_pos : 0 < k₀ := by
    by_contra hk0_not_pos
    push_neg at hk0_not_pos
    have hk0_eq : k₀ = 0 := Nat.le_zero.mp hk0_not_pos
    -- If k₀ = 0, then g is the zero vector (0-step vector counts nothing)
    have hg_zero : g = 0 := by
      rw [← hg_appears, hk0_eq]
      unfold Necklace.kStepVector Necklace.slice
      simp only [Nat.add_zero, Nat.sub_self, List.range_zero]
      rfl
    -- By the prefix bijection, prefix(1) = j·g + k·p for some j ∈ Fin pLen, k ∈ ℤ
    obtain ⟨j1, k1, hpfx1⟩ := hprefix_fwd ⟨0, hpLen_pos⟩
    -- Since g = 0, prefix(1) = j1·0 + k1·p = k1·p
    -- The total count of prefix(1) is 1 (it's a single letter)
    -- The total count of k1·p is k1·pLen
    -- So k1·pLen = 1, but pLen ≥ 2, which has no integer solution
    have hpfx1_L : (Necklace.kStepVector w' 0 1) BinaryStep.L = k1 * pVec BinaryStep.L := by
      have := hpfx1 BinaryStep.L
      simp only [hg_zero, ZVector.zero_apply, mul_zero, zero_add] at this
      exact this
    have hpfx1_s : (Necklace.kStepVector w' 0 1) BinaryStep.s = k1 * pVec BinaryStep.s := by
      have := hpfx1 BinaryStep.s
      simp only [hg_zero, ZVector.zero_apply, mul_zero, zero_add] at this
      exact this
    -- Total count of prefix(1): exactly 1 (one letter)
    have hpfx1_total : (Necklace.kStepVector w' 0 1) BinaryStep.L + (Necklace.kStepVector w' 0 1) BinaryStep.s = 1 := by
      unfold Necklace.kStepVector Necklace.slice
      simp only [Nat.add_sub_cancel_left, List.range_one, ZVector.ofList]
      cases hw'0 : w' 0 <;> simp [hw'0]
    -- Total count of pVec: pLen
    have hpVec_total : pVec BinaryStep.L + pVec BinaryStep.s = pLen := by
      show (ZVector.ofList per) BinaryStep.L + (ZVector.ofList per) BinaryStep.s = pLen
      unfold ZVector.ofList
      have hsum := binaryStep_count_sum per
      simp only [List.count_eq_countP, List.countP_eq_length_filter] at hsum
      norm_cast
    -- From hpfx1_L and hpfx1_s: k1 * pVec(L) + k1 * pVec(s) = 1
    have hk1_pLen : k1 * pLen = 1 := by
      calc k1 * pLen
        = k1 * (pVec BinaryStep.L + pVec BinaryStep.s) := by rw [hpVec_total]
        _ = k1 * pVec BinaryStep.L + k1 * pVec BinaryStep.s := by ring
        _ = (Necklace.kStepVector w' 0 1) BinaryStep.L + (Necklace.kStepVector w' 0 1) BinaryStep.s := by
            rw [hpfx1_L, hpfx1_s]
        _ = 1 := hpfx1_total
    -- k1 * pLen = 1 with pLen ≥ 2 has no integer solution
    have hpLen_ge_2_int : (pLen : ℤ) ≥ 2 := Int.ofNat_le.mpr hpLen_ge_2
    -- Case analysis on k1
    rcases Int.lt_or_le 0 k1 with hk1_pos | hk1_le
    · -- k1 > 0, so k1 ≥ 1: k1 * pLen ≥ pLen ≥ 2 > 1
      have hk1_ge_1 : k1 ≥ 1 := hk1_pos
      have : k1 * pLen ≥ 1 * pLen := by
        apply mul_le_mul_of_nonneg_right hk1_ge_1
        exact Int.natCast_nonneg pLen
      simp only [one_mul] at this
      omega
    · -- k1 ≤ 0: k1 * pLen ≤ 0 < 1
      have : k1 * pLen ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hk1_le (Int.natCast_nonneg pLen)
      omega
  use k₀
  refine ⟨hk₀_pos, hk₀_lt_pLen, ?_⟩
  · -- Show countKStepVectorPerPeriod w k₀ g = pLen - 1
    -- Step 1: kCoeff = 0, so gen_len = k₀ and prefix(k₀) = g in the rotated word
    have hkCoeff_zero : kCoeff = 0 := by
      -- Total count of prefix(gen_len): gen_len = gen_len_fin.val + 1
      have hprefix_total : (Necklace.kStepVector w' 0 gen_len) BinaryStep.L +
          (Necklace.kStepVector w' 0 gen_len) BinaryStep.s = gen_len := by
        exact_mod_cast kStepVector_total_count w' 0 gen_len
      -- Total count of 1·g + kCoeff·p: k₀ + kCoeff·pLen
      have hg_total : g BinaryStep.L + g BinaryStep.s = k₀ := by
        rw [← hg_appears]
        exact_mod_cast kStepVector_total_count w i₀.val k₀
      have hpVec_total : pVec BinaryStep.L + pVec BinaryStep.s = pLen := by
        show (ZVector.ofList per) BinaryStep.L + (ZVector.ofList per) BinaryStep.s = pLen
        unfold ZVector.ofList
        have hsum := binaryStep_count_sum per
        simp only [List.count_eq_countP, List.countP_eq_length_filter] at hsum
        norm_cast
      -- From hprefix_at_gen: Necklace.kStepVector w' 0 gen_len = 1·g + kCoeff·p
      -- So total count: gen_len = 1·k₀ + kCoeff·pLen
      have hrhs_total : (k₀ : ℤ) + kCoeff * pLen = gen_len := by
        have hL := hprefix_at_gen BinaryStep.L
        have hs := hprefix_at_gen BinaryStep.s
        have h1 : (1 * g BinaryStep.L + kCoeff * pVec BinaryStep.L) +
               (1 * g BinaryStep.s + kCoeff * pVec BinaryStep.s) =
               (gen_len : ℤ) := by
          rw [← hL, ← hs]; exact hprefix_total
        have h2 : (1 * g BinaryStep.L + kCoeff * pVec BinaryStep.L) +
               (1 * g BinaryStep.s + kCoeff * pVec BinaryStep.s) =
               1 * (g BinaryStep.L + g BinaryStep.s) + kCoeff * (pVec BinaryStep.L + pVec BinaryStep.s) := by ring
        rw [h2, hg_total, hpVec_total] at h1
        linarith
      -- With 1 ≤ gen_len ≤ pLen and 1 ≤ k₀ ≤ pLen - 1
      have hgen_pos_int : (gen_len : ℤ) ≥ 1 := by exact_mod_cast hgen_pos
      have hgen_le_int : (gen_len : ℤ) ≤ pLen := by exact_mod_cast hgen_le
      have hk₀_pos_int : (k₀ : ℤ) ≥ 1 := by exact_mod_cast hk₀_pos
      have hk₀_lt_int : (k₀ : ℤ) < pLen := by exact_mod_cast hk₀_lt_pLen
      -- kCoeff ≥ 1: gen_len = k₀ + kCoeff*pLen ≥ 1 + pLen > pLen ✗
      -- kCoeff ≤ -1: gen_len = k₀ + kCoeff*pLen ≤ (pLen-1) - pLen = -1 < 1 ✗
      by_contra h
      rcases Int.lt_or_lt_of_ne h with hlt | hgt
      · -- kCoeff < 0, so kCoeff ≤ -1
        have hle : kCoeff ≤ -1 := by omega
        have : kCoeff * (pLen : ℤ) ≤ -1 * pLen := by
          apply mul_le_mul_of_nonneg_right hle (Int.natCast_nonneg pLen)
        linarith
      · -- kCoeff > 0, so kCoeff ≥ 1
        have hge : kCoeff ≥ 1 := hgt
        have : kCoeff * (pLen : ℤ) ≥ 1 * pLen := by
          apply mul_le_mul_of_nonneg_right hge (Int.natCast_nonneg pLen)
        linarith

    -- Step 2: gen_len = k₀ (follows from kCoeff = 0 and the total count equation)
    have hgen_eq_k₀ : gen_len = k₀ := by
      -- We re-derive the equation k₀ + kCoeff * pLen = gen_len
      have hg_total' : g BinaryStep.L + g BinaryStep.s = k₀ := by
        rw [← hg_appears]; exact_mod_cast kStepVector_total_count w i₀.val k₀
      have hpVec_total' : pVec BinaryStep.L + pVec BinaryStep.s = pLen := by
        show (ZVector.ofList per) BinaryStep.L + (ZVector.ofList per) BinaryStep.s = pLen
        unfold ZVector.ofList
        have hsum := binaryStep_count_sum per
        simp only [List.count_eq_countP, List.countP_eq_length_filter] at hsum
        norm_cast
      have hprefix_total' : (Necklace.kStepVector w' 0 gen_len) BinaryStep.L +
          (Necklace.kStepVector w' 0 gen_len) BinaryStep.s = gen_len := by
        exact_mod_cast kStepVector_total_count w' 0 gen_len
      have hL := hprefix_at_gen BinaryStep.L
      have hs := hprefix_at_gen BinaryStep.s
      have heq : (k₀ : ℤ) + kCoeff * pLen = gen_len := by
        have h1 : (1 * g BinaryStep.L + kCoeff * pVec BinaryStep.L) +
                  (1 * g BinaryStep.s + kCoeff * pVec BinaryStep.s) = (gen_len : ℤ) := by
          rw [← hL, ← hs]; exact hprefix_total'
        have h2 : (1 * g BinaryStep.L + kCoeff * pVec BinaryStep.L) +
                  (1 * g BinaryStep.s + kCoeff * pVec BinaryStep.s) =
                  1 * (g BinaryStep.L + g BinaryStep.s) + kCoeff * (pVec BinaryStep.L + pVec BinaryStep.s) := by ring
        rw [h2, hg_total', hpVec_total'] at h1
        linarith
      rw [hkCoeff_zero] at heq
      simp at heq
      omega

    -- Step 3: Coprimality gcd(k₀, pLen) = 1
    -- From the prefix bijection, prefix(1) = j₁·g + c₁·p gives Bézout identity j₁·k₀ + c₁·pLen = 1
    have hcoprime : Nat.Coprime k₀ pLen := by
      obtain ⟨j₁, c₁, hpfx1⟩ := hprefix_fwd ⟨0, hpLen_pos⟩
      have hpfx1_total : (Necklace.kStepVector w' 0 1) BinaryStep.L + (Necklace.kStepVector w' 0 1) BinaryStep.s = 1 := by
        unfold Necklace.kStepVector Necklace.slice
        simp only [Nat.add_sub_cancel_left, List.range_one, ZVector.ofList]
        cases hw'0 : w' 0 <;> simp [hw'0]
      have hg_total' : g BinaryStep.L + g BinaryStep.s = k₀ := by
        rw [← hg_appears]; exact_mod_cast kStepVector_total_count w i₀.val k₀
      have hpVec_total' : pVec BinaryStep.L + pVec BinaryStep.s = pLen := by
        show (ZVector.ofList per) BinaryStep.L + (ZVector.ofList per) BinaryStep.s = pLen
        unfold ZVector.ofList
        have hsum := binaryStep_count_sum per
        simp only [List.count_eq_countP, List.countP_eq_length_filter] at hsum
        norm_cast
      have hbezout : (j₁.val : ℤ) * k₀ + c₁ * pLen = 1 := by
        have hL := hpfx1 BinaryStep.L
        have hs := hpfx1 BinaryStep.s
        simp only [Nat.zero_add] at hL hs
        have h1 : (↑↑j₁ * g BinaryStep.L + c₁ * pVec BinaryStep.L) +
                  (↑↑j₁ * g BinaryStep.s + c₁ * pVec BinaryStep.s) = (1 : ℤ) := by
          rw [← hL, ← hs]; exact hpfx1_total
        have h2 : (↑↑j₁ * g BinaryStep.L + c₁ * pVec BinaryStep.L) +
                  (↑↑j₁ * g BinaryStep.s + c₁ * pVec BinaryStep.s) =
                  ↑↑j₁ * (g BinaryStep.L + g BinaryStep.s) + c₁ * (pVec BinaryStep.L + pVec BinaryStep.s) := by ring
        rw [h2, hg_total', hpVec_total'] at h1
        linarith
      show Nat.gcd k₀ pLen = 1
      have hdvd : (Nat.gcd k₀ pLen : ℤ) ∣ 1 := by
        have hdvd_k : (Nat.gcd k₀ pLen : ℤ) ∣ ↑k₀ := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left k₀ pLen)
        have hdvd_p : (Nat.gcd k₀ pLen : ℤ) ∣ ↑pLen := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right k₀ pLen)
        calc (↑(Nat.gcd k₀ pLen) : ℤ)
          ∣ ↑j₁.val * ↑k₀ + c₁ * ↑pLen := dvd_add (dvd_mul_of_dvd_right hdvd_k _) (dvd_mul_of_dvd_right hdvd_p _)
          _ = 1 := hbezout
      have hgcd_pos : 0 < Nat.gcd k₀ pLen := Nat.pos_of_ne_zero (by
        intro h; simp [h] at hdvd)
      have hgcd_le : Nat.gcd k₀ pLen ≤ 1 := by exact_mod_cast Int.le_of_dvd one_pos hdvd
      omega

    -- Step 4: Use coprimality + MOS to prove count = pLen - 1
    -- Strategy: show there are exactly 2 varieties, then use two_varieties_counts_sum
    -- and a determinant argument to get the (pLen-1, 1) split.

    -- 4a: g ∈ distinctKStepVectors
    have hg_mem : g ∈ distinctKStepVectors w k₀ := by
      unfold distinctKStepVectors Necklace.allKStepVectors
      rw [List.mem_toFinset, List.mem_map]
      exact ⟨i₀.val, List.mem_range.mpr i₀.isLt, hg_appears⟩

    -- 4b: There are at most 2 varieties (MOS property)
    have hk₀_lt_n : k₀ < n := by
      calc k₀ < pLen := hk₀_lt_pLen
        _ ≤ n := Necklace.period_length_le_n w
    have hpLen_le_n : pLen ≤ n := Necklace.period_length_le_n w
    have hcard_le_2 : (distinctKStepVectors w k₀).card ≤ 2 :=
      mos_at_most_two_varieties w hw k₀ hk₀_pos hk₀_lt_pLen

    -- 4c: There are at least 2 varieties
    -- If only 1 variety, then all k₀-steps equal g, so w(i+k₀) = w(i) for all i.
    -- Combined with w(i+n) = w(i) and gcd(k₀,n) | k₀ < pLen,
    -- this contradicts pLen being the minimal period.
    have hcard_ge_2 : (distinctKStepVectors w k₀).card ≥ 2 := by
      by_contra h
      push_neg at h
      -- card ≤ 1: either 0 (impossible since g is in the set) or 1
      have hcard_le_1 : (distinctKStepVectors w k₀).card ≤ 1 := by omega
      have hcard_eq_1 : (distinctKStepVectors w k₀).card = 1 := by
        have hcard_pos : (distinctKStepVectors w k₀).card ≥ 1 :=
          Finset.card_pos.mpr ⟨g, hg_mem⟩
        omega
      -- All k₀-step vectors equal g
      have hall_eq_g : ∀ v ∈ distinctKStepVectors w k₀, v = g := by
        have h1 : (distinctKStepVectors w k₀).card ≤ 1 := by omega
        intro v hv
        have h2 := Finset.card_le_one.mp h1
        exact h2 v hv g hg_mem
      -- Every position i has Necklace.kStepVector w i k₀ = g
      have hall_positions : ∀ i : ℕ, Necklace.kStepVector w i k₀ = g := by
        intro i
        have hmem : Necklace.kStepVector w (i % n) k₀ ∈ distinctKStepVectors w k₀ := by
          unfold distinctKStepVectors Necklace.allKStepVectors
          rw [List.mem_toFinset, List.mem_map]
          exact ⟨i % n, List.mem_range.mpr (Nat.mod_lt i (NeZero.pos n)), rfl⟩
        rw [← kStepVector_mod_n]
        exact hall_eq_g _ hmem
      -- From consecutive k₀-steps being equal: w(i) = w(i + k₀) for all i
      -- (shifting by 1 removes w(i) and adds w(i+k₀); if k₀-step unchanged,
      --  w(i) and w(i+k₀) must be the same letter)
      have hperiodic_k₀ : ∀ i : ℕ, w (i : ZMod n) = w ((i + k₀ : ℕ) : ZMod n) := by
        intro i
        -- Both k₀-step vectors at positions i and i+1 equal g, so their L-counts are equal
        have heq_L : Necklace.kStepVector w i k₀ BinaryStep.L = Necklace.kStepVector w (i + 1) k₀ BinaryStep.L := by
          rw [hall_positions i, hall_positions (i + 1)]
        -- slice_L_count_shift relates L-counts via delta_out and delta_in
        have hshift := slice_L_count_shift w i k₀
        simp only at hshift
        -- Name the delta terms (following the pattern from perfect_interval_right_step)
        set delta_out := if w (i : ZMod n) = BinaryStep.L then (1 : ℤ) else 0 with hdelta_out_def
        set delta_in := if w ((i + k₀) : ZMod n) = BinaryStep.L then (1 : ℤ) else 0
          with hdelta_in_def
        -- Equal L-counts + shift relation ⟹ delta_out = delta_in
        have hdelta_eq : delta_out = delta_in := by
          unfold Necklace.kStepVector ZVector.ofList at heq_L
          omega
        -- Normalize the cast in the goal: ↑(i + k₀) → ↑i + ↑k₀
        simp only [Nat.cast_add]
        -- Case split on w[i]
        cases hw_i : w (i : ZMod n)
        · -- w[i] = L → delta_out = 1 → delta_in = 1 → w[i+k₀] = L
          have hw_k : w ((i + k₀) : ZMod n) = BinaryStep.L := by
            by_contra h
            have : delta_out = 1 := by simp only [hdelta_out_def, hw_i, ↓reduceIte]
            have : delta_in = 0 := by simp only [hdelta_in_def, h, ↓reduceIte]
            omega
          rw [hw_k]
        · -- w[i] = s → delta_out = 0 → delta_in = 0 → w[i+k₀] = s
          have hw_k : w ((i + k₀) : ZMod n) = BinaryStep.s := by
            by_contra h
            cases hw_k' : w ((i + k₀) : ZMod n)
            · have : delta_out = 0 := by simp only [hdelta_out_def, hw_i]; decide
              have : delta_in = 1 := by simp only [hdelta_in_def, hw_k', ↓reduceIte]
              omega
            · exact h hw_k'
          rw [hw_k]
      -- Iterate hperiodic_k₀: w(j) = w(j + m·k₀) for all m
      have hiter : ∀ (j m : ℕ), w (↑j : ZMod n) = w (↑(j + m * k₀) : ZMod n) := by
        intro j m; induction m with
        | zero => simp
        | succ m ih =>
          rw [show j + (m + 1) * k₀ = j + m * k₀ + k₀ from by ring]
          exact ih.trans (hperiodic_k₀ (j + m * k₀))
      -- gcd(k₀, n) properties
      have hgcd_pos : 0 < Nat.gcd k₀ n :=
        Nat.pos_of_ne_zero (by intro heq; rw [Nat.gcd_eq_zero_iff] at heq; omega)
      have hgcd_le_k : Nat.gcd k₀ n ≤ k₀ :=
        Nat.le_of_dvd hk₀_pos (Nat.gcd_dvd_left k₀ n)
      have hgcd_lt_n : Nat.gcd k₀ n < n := by omega
      -- Bézout in ZMod n: (gcd k₀ n : ZMod n) = k₀ · gcdA
      have hbez : (↑(Nat.gcd k₀ n) : ZMod n) =
          (↑k₀ : ZMod n) * ((Nat.gcdA k₀ n : ℤ) : ZMod n) := by
        have := congr_arg (fun x : ℤ => (x : ZMod n)) (Nat.gcd_eq_gcd_ab k₀ n)
        push_cast at this
        rwa [ZMod.natCast_self, zero_mul, add_zero] at this
      -- w has translational period gcd(k₀, n)
      have hperiodic_gcd : ∀ (i : ZMod n), w i = w (i + ↑(Nat.gcd k₀ n)) := by
        intro i
        have hi := hiter (ZMod.val i) (ZMod.val ((Nat.gcdA k₀ n : ℤ) : ZMod n))
        rw [ZMod.natCast_zmod_val i] at hi
        rw [hi]; congr 1; push_cast
        rw [ZMod.natCast_zmod_val i,
            ZMod.natCast_zmod_val ((Nat.gcdA k₀ n : ℤ) : ZMod n),
            mul_comm, ← hbez]
      -- period_length_le gives pLen ≤ gcd(k₀, n), but gcd(k₀, n) ≤ k₀ < pLen
      have hpLen_le := Necklace.period_length_le_of_translational_period w
        (Nat.gcd k₀ n) hgcd_pos hgcd_lt_n (Nat.gcd_dvd_right k₀ n) hperiodic_gcd
      omega

    have hcard_eq_2 : (distinctKStepVectors w k₀).card = 2 := by omega

    -- 4d: Get the other variety g'
    obtain ⟨g', hg'_mem, hg'_ne⟩ : ∃ g' ∈ distinctKStepVectors w k₀, g' ≠ g := by
      by_contra h
      push_neg at h
      have : ∀ v ∈ distinctKStepVectors w k₀, v = g := h
      have : (distinctKStepVectors w k₀).card ≤ 1 :=
        Finset.card_le_one.mpr (fun a ha b hb => by rw [this a ha, this b hb])
      omega

    -- 4e: count(g) + count(g') = pLen
    have hsum := two_varieties_counts_sum w k₀ g g' hg_mem hg'_mem hg'_ne.symm hcard_eq_2

    -- 4f: Use kStepVector_lettercount_sum_over_period (double-counting)
    -- and mos_kStepVector_L_count_diff_le_one to show count(g') = 1
    --
    -- From double-counting: count(g)·g(L) + count(g')·g'(L) = k₀·pVec(L)
    -- Substituting count(g) = pLen - count(g'):
    --   pLen·g(L) - count(g')·(g(L) - g'(L)) = k₀·pVec(L)
    -- From MOS: g(L) - g'(L) = ±1 (both varieties have L-counts differing by ≤ 1,
    --   and they're distinct vectors with same total count, so differ by exactly 1)
    -- So count(g') = ±(pLen·g(L) - k₀·pVec(L)) = ±det(g, pVec)
    --
    -- det(g, pVec) = ±1 because:
    --   All prefix vectors prefix(m) ∈ span_ℤ{g, pVec} (from prefix bijection)
    --   prefix(m+1) - prefix(m) = e_{w'(m)} (unit vector for letter w'(m))
    --   Since w' is binary, both e_L and e_s are in span_ℤ{g, pVec}
    --   So span_ℤ{g, pVec} = ℤ², giving |det(g, pVec)| = 1
    --
    -- Therefore count(g') = 1, so count(g) = pLen - 1.

    -- The final step: count(g) = pLen - 1
    -- We prove count(g') = 1 using the determinant argument
    suffices hcount_g' : countKStepVectorPerPeriod w k₀ g' = 1 by omega

    -- Step 4f-i: Both e_L and e_s are integer linear combinations of g and pVec
    -- (from the prefix bijection applied to consecutive prefixes of w')
    have hunit_in_span : ∀ a : BinaryStep,
        ∃ j c : ℤ, ∀ b : BinaryStep,
          (fun x => if x = a then (1 : ℤ) else 0) b = j * g b + c * pVec b := by
      -- Both L and s appear in the period (from isBinary), so we can find positions where they occur
      intro a
      -- Get existence of the letter a in the period
      have hbinary := hw.1
      -- There exist positions in w with letter L and letter s
      obtain ⟨iL, hiL⟩ := hbinary.1
      obtain ⟨is, his⟩ := hbinary.2
      -- The period repeats, so these letters also appear in positions 0..pLen-1 of w'
      -- For simplicity, use the prefix bijection: prefix(m+1) - prefix(m) = e_{w'(m)}
      -- We need to find some m < pLen such that w'(m) = a
      -- Since pLen is the period and w is binary, both letters appear in positions 0..pLen-1
      -- For now, find any two consecutive prefixes and take their difference
      -- The difference formula: (prefix(m+1) - prefix(m))(b) = if w'(m) = b then 1 else 0
      -- Use m = 0: prefix(1) - prefix(0) = e_{w'(0)} where prefix(0) is the zero vector
      -- prefix(1) = j₁ * g + c₁ * pVec for some j₁, c₁
      -- So e_{w'(0)} = j₁ * g + c₁ * pVec
      -- We need both e_L and e_s. Use m = 0 and m = 1 (if pLen ≥ 2)
      -- If w'(0) = L, then e_L is in span. Then use m = 1 or find where s appears.
      -- Key insight: prefix(m+1)(b) - prefix(m)(b) = if w'(m) = b then 1 else 0
      -- Proof: slice(0, m+1) = slice(0, m) ++ [w'(m)]
      -- So count of b in slice(0,m+1) = count in slice(0,m) + (if w'(m) = b then 1 else 0)
      -- Now, hprefix_fwd gives us j, c for each prefix length
      -- For consecutive m and m+1, the difference gives us the unit vector for w'(m)
      -- Since w is binary and period has both letters, there exist m₁, m₂ < pLen with w'(m₁)=L, w'(m₂)=s
      have hrep_proof : Necklace.isRepetitionOf w per = true := by
        show Necklace.isRepetitionOf w (Necklace.period w) = true
        unfold Necklace.period
        cases hfind : ((List.range n).tail.map (Necklace.slice w 0)).find?
            (Necklace.isRepetitionOf w) with
        | some pfx => simp only [Option.getD_some]; exact List.find?_some hfind
        | none =>
          simp only [Option.getD_none]
          unfold Necklace.isRepetitionOf
          simp only [Necklace.slice_length, Nat.sub_zero, ne_eq,
            Nat.pos_iff_ne_zero.mp (NeZero.pos n), ↓reduceIte,
            Nat.mod_self, not_true_eq_false]
          rw [List.all_eq_true]
          intro i hi
          rw [List.mem_range] at hi
          rw [decide_eq_true_eq, Nat.mod_eq_of_lt hi]
          unfold Necklace.slice
          simp only [bind_pure_comp, Functor.map, Nat.sub_zero, Nat.cast_zero, zero_add,
                List.map_map, Function.comp, List.getElem?_map, List.getElem?_range hi,
                Option.map]
      -- Derive divisibility: pLen | n
      have hpLen_dvd_n : pLen ∣ n := by
        have hrep := hrep_proof
        show (Necklace.period w).length ∣ n
        unfold Necklace.isRepetitionOf at hrep
        simp only [ne_eq] at hrep
        split at hrep
        · exact absurd hrep Bool.false_ne_true
        · split at hrep
          · exact absurd hrep Bool.false_ne_true
          · rename_i _ h2
            push_neg at h2
            exact Nat.dvd_of_mod_eq_zero h2
      -- Key periodicity fact: w(j) matches period at j % pLen
      have hper_match : ∀ j : ℕ, j < n →
          some (w ((j : ℕ) : ZMod n)) = per[j % pLen]? := by
        intro j hj
        have hrep := hrep_proof
        unfold Necklace.isRepetitionOf at hrep
        simp only [ne_eq] at hrep
        split at hrep
        · exact absurd hrep Bool.false_ne_true
        · split at hrep
          · exact absurd hrep Bool.false_ne_true
          · rw [List.all_eq_true] at hrep
            have h := hrep j (List.mem_range.mpr hj)
            rwa [decide_eq_true_eq] at h
      have hperiod_has_both : (∃ m : Fin pLen, w' m.val = BinaryStep.L) ∧
                              (∃ m : Fin pLen, w' m.val = BinaryStep.s) := by
        -- Helper: for any letter appearing in w, it appears in w' at some position < pLen
        suffices find_letter : ∀ (pos : ZMod n) (letter : BinaryStep),
            w pos = letter → ∃ m : Fin pLen, w' m.val = letter by
          exact ⟨find_letter iL BinaryStep.L hiL, find_letter is BinaryStep.s his⟩
        intro pos letter hpos
        -- Choose m so that (m + r.val) % pLen = pos.val % pLen
        let m := (pos.val % pLen + pLen - r.val % pLen) % pLen
        have hm_lt : m < pLen := Nat.mod_lt _ hpLen_pos
        use ⟨m, hm_lt⟩
        show w (↑m + r) = letter
        -- Convert ZMod addition to Nat cast
        conv_lhs => rw [show (↑m + r : ZMod n) = ((m + r.val : ℕ) : ZMod n) from by
          push_cast; rw [ZMod.natCast_zmod_val]]
        -- Reduce mod n for use with hper_match
        conv_lhs => rw [show ((m + r.val : ℕ) : ZMod n) = (((m + r.val) % n : ℕ) : ZMod n) from by
          simp]
        -- Use hper_match at (m + r.val) % n
        have hmod_n_lt : (m + r.val) % n < n := Nat.mod_lt _ (NeZero.pos n)
        have hmatch1 := hper_match ((m + r.val) % n) hmod_n_lt
        rw [Nat.mod_mod_of_dvd _ hpLen_dvd_n] at hmatch1
        -- (m + r.val) % pLen = pos.val % pLen
        have hmod_eq : (m + r.val) % pLen = pos.val % pLen := by
          simp only [m]
          have hr_mod : r.val % pLen < pLen := Nat.mod_lt r.val hpLen_pos
          have hpos_mod : pos.val % pLen < pLen := Nat.mod_lt pos.val hpLen_pos
          -- Reduce both summands mod pLen
          rw [Nat.add_mod, Nat.mod_eq_of_lt (Nat.mod_lt _ hpLen_pos)]
          -- Goal: ((pos.val % pLen + pLen - r.val % pLen) % pLen + r.val % pLen) % pLen
          --       = pos.val % pLen
          by_cases h : r.val % pLen ≤ pos.val % pLen
          · -- inner value ∈ [pLen, 2*pLen), so mod = value - pLen
            rw [Nat.mod_eq_sub_mod (by omega : pLen ≤ pos.val % pLen + pLen - r.val % pLen),
                show pos.val % pLen + pLen - r.val % pLen - pLen =
                  pos.val % pLen - r.val % pLen from by omega,
                Nat.mod_eq_of_lt (by omega : pos.val % pLen - r.val % pLen < pLen),
                Nat.sub_add_cancel h, Nat.mod_eq_of_lt hpos_mod]
          · -- inner value ∈ [1, pLen), so mod = value
            push_neg at h
            rw [Nat.mod_eq_of_lt (by omega : pos.val % pLen + pLen - r.val % pLen < pLen),
                Nat.sub_add_cancel (by omega : r.val % pLen ≤ pos.val % pLen + pLen),
                Nat.mod_eq_sub_mod (by omega : pLen ≤ pos.val % pLen + pLen),
                Nat.add_sub_cancel, Nat.mod_eq_of_lt hpos_mod]
        rw [hmod_eq] at hmatch1
        -- Also: w(pos.val) matches per[pos.val % pLen]
        have hpos_lt : pos.val < n := ZMod.val_lt pos
        have hmatch2 := hper_match pos.val hpos_lt
        -- Both equal per[pos.val % pLen]?, so the w values are equal
        rw [← hmatch2] at hmatch1
        have heq := Option.some_injective _ hmatch1
        rw [heq, ZMod.natCast_zmod_val, hpos]
      -- Use prefix bijection and kStepVector_succ_sub to express unit vectors
      -- as integer linear combinations of g and pVec.
      -- For each letter a, find m < pLen with w'(m) = a (from hperiod_has_both),
      -- then prefix(m+1) - prefix(m) = e_{w'(m)} = e_a.
      rcases a with _ | _
      · -- a = L
        obtain ⟨mL, hmL_eq⟩ := hperiod_has_both.1
        -- prefix(mL+1) = j_hi * g + c_hi * pVec
        obtain ⟨j_hi, c_hi, hpfx_hi⟩ := hprefix_fwd mL
        -- prefix(mL) as a linear combination (zero vector if mL = 0)
        obtain ⟨j_lo, c_lo, hpfx_lo⟩ : ∃ j_lo c_lo : ℤ,
            ∀ a, Necklace.kStepVector w' 0 mL.val a = j_lo * g a + c_lo * pVec a := by
          by_cases hmL_zero : mL.val = 0
          · exact ⟨0, 0, fun a => by simp [hmL_zero, Necklace.kStepVector, ZVector.ofList, Necklace.slice]⟩
          · have hmL_pos := Nat.pos_of_ne_zero hmL_zero
            obtain ⟨j, c, h⟩ := hprefix_fwd
              ⟨mL.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) mL.isLt⟩
            simp only [Nat.sub_add_cancel hmL_pos] at h
            exact ⟨↑j.val, c, h⟩
        use ↑j_hi.val - j_lo, c_hi - c_lo
        intro b
        have hstep := kStepVector_succ_sub w' mL.val b
        have h_hi : Necklace.kStepVector w' 0 (mL.val + 1) b =
            ↑j_hi.val * g b + c_hi * pVec b := hpfx_hi b
        have h_lo : Necklace.kStepVector w' 0 mL.val b =
            j_lo * g b + c_lo * pVec b := hpfx_lo b
        have heq_ite : (fun x => if x = BinaryStep.L then (1:ℤ) else 0) b =
            if w' (↑mL.val : ZMod n) = b then 1 else 0 := by
          cases b <;> simp [hmL_eq]
        rw [heq_ite, ← hstep]; linarith
      · -- a = s (symmetric)
        obtain ⟨ms, hms_eq⟩ := hperiod_has_both.2
        obtain ⟨j_hi, c_hi, hpfx_hi⟩ := hprefix_fwd ms
        obtain ⟨j_lo, c_lo, hpfx_lo⟩ : ∃ j_lo c_lo : ℤ,
            ∀ a, Necklace.kStepVector w' 0 ms.val a = j_lo * g a + c_lo * pVec a := by
          by_cases hms_zero : ms.val = 0
          · exact ⟨0, 0, fun a => by simp [hms_zero, Necklace.kStepVector, ZVector.ofList, Necklace.slice]⟩
          · have hms_pos := Nat.pos_of_ne_zero hms_zero
            obtain ⟨j, c, h⟩ := hprefix_fwd
              ⟨ms.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) ms.isLt⟩
            simp only [Nat.sub_add_cancel hms_pos] at h
            exact ⟨↑j.val, c, h⟩
        use ↑j_hi.val - j_lo, c_hi - c_lo
        intro b
        have hstep := kStepVector_succ_sub w' ms.val b
        have h_hi : Necklace.kStepVector w' 0 (ms.val + 1) b =
            ↑j_hi.val * g b + c_hi * pVec b := hpfx_hi b
        have h_lo : Necklace.kStepVector w' 0 ms.val b =
            j_lo * g b + c_lo * pVec b := hpfx_lo b
        have heq_ite : (fun x => if x = BinaryStep.s then (1:ℤ) else 0) b =
            if w' (↑ms.val : ZMod n) = b then 1 else 0 := by
          cases b <;> simp [hms_eq]
        rw [heq_ite, ← hstep]; linarith
    -- Step 4f-ii: det(g, pVec) = ±1
    have hdet : g BinaryStep.L * pVec BinaryStep.s - g BinaryStep.s * pVec BinaryStep.L = 1 ∨
                g BinaryStep.L * pVec BinaryStep.s - g BinaryStep.s * pVec BinaryStep.L = -1 := by
      -- From hunit_in_span, e_L and e_s are in ℤ-span{g, pVec}
      -- So the 2×2 matrix [g | pVec] has an integer inverse, hence det = ±1
      obtain ⟨j_L, c_L, hL⟩ := hunit_in_span BinaryStep.L
      obtain ⟨j_s, c_s, hs⟩ := hunit_in_span BinaryStep.s
      -- Extract the 2×2 system: [j_L c_L; j_s c_s] · [g; pVec] = I
      have hLL : j_L * g BinaryStep.L + c_L * pVec BinaryStep.L = 1 := by
        have h := hL BinaryStep.L; simp at h; linarith
      have hLs : j_L * g BinaryStep.s + c_L * pVec BinaryStep.s = 0 := by
        have h := hL BinaryStep.s; simp at h; linarith
      have hsL : j_s * g BinaryStep.L + c_s * pVec BinaryStep.L = 0 := by
        have h := hs BinaryStep.L; simp at h; linarith
      have hss : j_s * g BinaryStep.s + c_s * pVec BinaryStep.s = 1 := by
        have h := hs BinaryStep.s; simp at h; linarith
      -- det(M) · det(M⁻¹) = det(I) = 1
      have hprod : (g BinaryStep.L * pVec BinaryStep.s - g BinaryStep.s * pVec BinaryStep.L) *
                   (j_L * c_s - j_s * c_L) = 1 := by
        have key : (g BinaryStep.L * pVec BinaryStep.s - g BinaryStep.s * pVec BinaryStep.L) *
                   (j_L * c_s - j_s * c_L) =
                   (j_L * g BinaryStep.L + c_L * pVec BinaryStep.L) *
                   (j_s * g BinaryStep.s + c_s * pVec BinaryStep.s) -
                   (j_L * g BinaryStep.s + c_L * pVec BinaryStep.s) *
                   (j_s * g BinaryStep.L + c_s * pVec BinaryStep.L) := by ring
        rw [key, hLL, hss, hLs, hsL]; ring
      -- In ℤ, a * b = 1 implies a = ±1
      have hunit : IsUnit (g BinaryStep.L * pVec BinaryStep.s - g BinaryStep.s * pVec BinaryStep.L) :=
        isUnit_of_dvd_one ⟨_, hprod.symm⟩
      rwa [Int.isUnit_iff] at hunit

    -- Step 4f-iii: |g(L) - g'(L)| ≤ 1 (MOS property)
    have hdiff_le : (g BinaryStep.L : ℤ) - 1 ≤ g' BinaryStep.L ∧
                     g' BinaryStep.L ≤ (g BinaryStep.L : ℤ) + 1 :=
      mos_kStepVector_L_count_diff_le_one w hw k₀ hk₀_pos hk₀_lt_n g g' hg_mem hg'_mem
    have hg'_ne_sym : g ≠ g' := hg'_ne.symm
    -- g ≠ g' with same total count and |L-diff| ≤ 1 means |L-diff| = 1
    have hg_total : g BinaryStep.L + g BinaryStep.s = k₀ := by
      rw [← hg_appears]; exact_mod_cast kStepVector_total_count w i₀.val k₀
    have hg'_total : g' BinaryStep.L + g' BinaryStep.s = k₀ := by
      -- g' appears as a k₀-step vector somewhere
      have : g' ∈ distinctKStepVectors w k₀ := hg'_mem
      unfold distinctKStepVectors Necklace.allKStepVectors at this
      rw [List.mem_toFinset, List.mem_map] at this
      obtain ⟨i', _, hg'_eq⟩ := this
      rw [← hg'_eq]; exact_mod_cast kStepVector_total_count w i' k₀
    have hdiff_eq_one : g BinaryStep.L - g' BinaryStep.L = 1 ∨
                        g BinaryStep.L - g' BinaryStep.L = -1 := by
      -- g and g' have same total count k₀, so g(L)-g'(L) = -(g(s)-g'(s))
      -- They're distinct, so g(L) ≠ g'(L) (otherwise g(s) = g'(s) too, giving g = g')
      have hL_ne : g BinaryStep.L ≠ g' BinaryStep.L := by
        intro heq
        have hs_eq : g BinaryStep.s = g' BinaryStep.s := by linarith
        exact hg'_ne_sym (funext (fun a => by cases a <;> assumption))
      -- |g(L) - g'(L)| ≤ 1 and ≠ 0, so = 1 or -1
      cases hdiff_le with
      | intro left right =>
        rcases Int.lt_or_lt_of_ne (sub_ne_zero.mpr hL_ne) with hneg | hpos
        · right; omega
        · left; omega

    -- Step 4f-iv: double-counting gives count(g')·(g(L)-g'(L)) = pLen·g(L) - k₀·pVec(L)
    -- and det(g,pVec) = g(L)·pVec(s) - g(s)·pVec(L) = g(L)·pLen - k₀·pVec(L)
    -- so count(g') = |det(g,pVec)| = 1
    have hdet_eq : g BinaryStep.L * pVec BinaryStep.s - g BinaryStep.s * pVec BinaryStep.L =
                   g BinaryStep.L * (pLen : ℤ) - (k₀ : ℤ) * pVec BinaryStep.L := by
      have hpVec_total' : pVec BinaryStep.L + pVec BinaryStep.s = pLen := by
        show (ZVector.ofList per) BinaryStep.L + (ZVector.ofList per) BinaryStep.s = pLen
        unfold ZVector.ofList
        have hsum := binaryStep_count_sum per
        simp only [List.count_eq_countP, List.countP_eq_length_filter] at hsum
        norm_cast
      have hpVec_s : pVec BinaryStep.s = (pLen : ℤ) - pVec BinaryStep.L := by linarith
      have hg_s : g BinaryStep.s = (k₀ : ℤ) - g BinaryStep.L := by
        have := hg_total; push_cast at this ⊢; linarith
      calc g BinaryStep.L * pVec BinaryStep.s - g BinaryStep.s * pVec BinaryStep.L
        _ = g BinaryStep.L * ((pLen : ℤ) - pVec BinaryStep.L) - ((k₀ : ℤ) - g BinaryStep.L) * pVec BinaryStep.L := by
            rw [hpVec_s, hg_s]
        _ = g BinaryStep.L * (pLen : ℤ) - (k₀ : ℤ) * pVec BinaryStep.L := by
            ring

    -- From double-counting + the sum equation:
    -- count(g')·Δ = pLen·g(L) - k₀·pVec(L) = det(g, pVec) = ±1
    -- where Δ = g(L) - g'(L) = ±1
    -- So count(g') = det/Δ = ±1, and since count(g') > 0, count(g') = 1
    have hcount_g'_pos : countKStepVectorPerPeriod w k₀ g' ≥ 1 := by
      -- If count(g') = 0, then count(g) = pLen (from hsum)
      -- But then all k₀-steps in [0, pLen) equal g
      -- By periodicity, all k₀-steps in [0, n) equal g, so card = 1, contradicting card = 2
      by_contra h
      push_neg at h
      have hcount_g'_zero : countKStepVectorPerPeriod w k₀ g' = 0 := Nat.lt_one_iff.mp h
      have hcount_g_eq_pLen : countKStepVectorPerPeriod w k₀ g = pLen := by
        show countKStepVectorPerPeriod w k₀ g = (Necklace.period w).length
        have := hsum; omega
      -- All positions in [0, pLen) have Necklace.kStepVector = g
      have hall_g_in_period : ∀ i < pLen, Necklace.kStepVector w i k₀ = g := by
        intro i hi
        by_contra h_ne
        -- If Necklace.kStepVector w i k₀ ≠ g, then since there are only 2 varieties, it must equal g'
        have hmem : Necklace.kStepVector w i k₀ ∈ distinctKStepVectors w k₀ := by
          unfold distinctKStepVectors Necklace.allKStepVectors
          rw [List.mem_toFinset, List.mem_map]
          have hi_lt_n : i < n := calc i
            _ < pLen := hi
            _ ≤ n := Necklace.period_length_le_n w
          exact ⟨i, List.mem_range.mpr hi_lt_n, rfl⟩
        have honly_two : Necklace.kStepVector w i k₀ = g ∨ Necklace.kStepVector w i k₀ = g' := by
          have hcard : distinctKStepVectors w k₀ = {g, g'} := by
            ext v
            simp only [Finset.mem_insert, Finset.mem_singleton]
            constructor
            · intro hv
              by_contra h_not_either
              push_neg at h_not_either
              -- v is a third variety, contradicting card = 2
              have : Finset.card {g, g', v} ≤ (distinctKStepVectors w k₀).card := by
                apply Finset.card_le_card
                intro x hx
                simp at hx
                rcases hx with rfl | rfl | rfl <;> assumption
              have hcard3 : Finset.card {g, g', v} = 3 := by
                rw [Finset.card_insert_of_notMem (by simp [hg'_ne.symm, h_not_either.1.symm]),
                    Finset.card_insert_of_notMem (by simp [h_not_either.2.symm]),
                    Finset.card_singleton]
              omega
            · intro h
              rcases h with rfl | rfl <;> assumption
          rw [hcard] at hmem
          simp at hmem
          exact hmem
        cases honly_two with
        | inl h_eq_g => exact h_ne h_eq_g
        | inr h_eq_g' =>
          -- But then count(g') > 0
          have : countKStepVectorPerPeriod w k₀ g' > 0 := by
            unfold countKStepVectorPerPeriod
            apply Nat.pos_of_ne_zero
            intro h0
            have : ∀ j ∈ List.range pLen, ¬decide (Necklace.kStepVector w j k₀ = g') := by
              rw [List.countP_eq_zero] at h0; exact h0
            have hi_mem : i ∈ List.range pLen := List.mem_range.mpr hi
            have := this i hi_mem
            simp [h_eq_g'] at this
          omega
      -- By periodicity with period pLen, all positions in [0, n) have Necklace.kStepVector = g
      have hall_g : ∀ i < n, Necklace.kStepVector w i k₀ = g := by
        intro i hi
        -- Use periodicity of Necklace.kStepVector with respect to the necklace's period
        have hperiod : Necklace.kStepVector w i k₀ = Necklace.kStepVector w (i % pLen) k₀ := by
          rw [kStepVector_mod_period w i k₀ (Nat.le_of_lt hk₀_lt_pLen)]
        rw [hperiod]
        apply hall_g_in_period
        exact Nat.mod_lt i hpLen_pos
      -- So distinctKStepVectors.card = 1
      have hcard_eq_1 : (distinctKStepVectors w k₀).card = 1 := by
        have : distinctKStepVectors w k₀ = {g} := by
          ext v
          simp only [Finset.mem_singleton]
          constructor
          · intro hv
            unfold distinctKStepVectors Necklace.allKStepVectors at hv
            rw [List.mem_toFinset, List.mem_map] at hv
            obtain ⟨i, hi, hv_eq⟩ := hv
            rw [List.mem_range] at hi
            rw [← hv_eq]
            exact hall_g i hi
          · intro rfl; exact hg_mem
        rw [this]
        simp
      omega

    -- The determinant is ±1, so count(g') must divide 1
    -- Combined with count(g') ≥ 1, we get count(g') = 1

    -- Double-counting: ∑ Necklace.kStepVector(i)(L) = k₀ * pVec(L)
    have hdouble_count : (countKStepVectorPerPeriod w k₀ g : ℤ) * g BinaryStep.L +
        (countKStepVectorPerPeriod w k₀ g' : ℤ) * g' BinaryStep.L =
        (k₀ : ℤ) * pVec BinaryStep.L := by
      have hsum_L := kStepVector_lettercount_sum_over_period w k₀ hk₀_pos hk₀_lt_pLen BinaryStep.L
      rw [list_range_map_sum_eq_finset] at hsum_L
      -- Split sum by g vs g'
      have : ∑ i ∈ Finset.range pLen, (Necklace.kStepVector w i k₀) BinaryStep.L =
          ∑ i ∈ Finset.range pLen, if Necklace.kStepVector w i k₀ = g then g BinaryStep.L
                                    else if Necklace.kStepVector w i k₀ = g' then g' BinaryStep.L
                                    else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases h : Necklace.kStepVector w i k₀ = g
        · simp only [h, ↓reduceIte]
        · by_cases h' : Necklace.kStepVector w i k₀ = g'
          · simp only [h', ↓reduceIte, hg'_ne]
          · -- Necklace.kStepVector is neither g nor g', but there are only 2 varieties
            exfalso
            have hmem : Necklace.kStepVector w i k₀ ∈ distinctKStepVectors w k₀ := by
              unfold distinctKStepVectors Necklace.allKStepVectors
              rw [List.mem_toFinset, List.mem_map]
              have hi_lt_pLen : i < pLen := Finset.mem_range.mp hi
              have hi_lt_n : i < n := calc i < pLen := hi_lt_pLen
                _ ≤ n := hpLen_le_n
              exact ⟨i, List.mem_range.mpr hi_lt_n, rfl⟩
            have : distinctKStepVectors w k₀ = {g, g'} := by
              ext v; simp
              constructor
              · intro hv
                by_contra hnot
                push_neg at hnot
                have : Finset.card {g, g', v} ≤ 2 := by
                  calc Finset.card {g, g', v}
                    _ ≤ (distinctKStepVectors w k₀).card := by
                      apply Finset.card_le_card
                      intro x hx; simp at hx
                      rcases hx with rfl | rfl | rfl <;> assumption
                    _ = 2 := hcard_eq_2
                have hcard3 : Finset.card {g, g', v} = 3 := by
                  rw [Finset.card_insert_of_notMem (by simp [hg'_ne.symm, hnot.1.symm]),
                      Finset.card_insert_of_notMem (by simp [hnot.2.symm]),
                      Finset.card_singleton]
                omega
              · intro h; rcases h with rfl | rfl <;> assumption
            rw [this] at hmem
            simp at hmem
            rcases hmem with rfl | rfl <;> contradiction
      rw [this] at hsum_L; clear this
      -- Sum over filters
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.range pLen) (fun i => Necklace.kStepVector w i k₀ = g)] at hsum_L
      have h1 : ∑ x ∈ Finset.filter (fun i => Necklace.kStepVector w i k₀ = g) (Finset.range pLen),
          g BinaryStep.L = (Finset.filter (fun i => Necklace.kStepVector w i k₀ = g) (Finset.range pLen)).card * g BinaryStep.L := by
        rw [Finset.sum_const, nsmul_eq_mul]
      have h2 : (Finset.filter (fun i => Necklace.kStepVector w i k₀ = g) (Finset.range pLen)).card =
          countKStepVectorPerPeriod w k₀ g := by
        unfold countKStepVectorPerPeriod
        simp only [Finset.card_def, Finset.filter_val, Finset.range_val]
        rw [← Multiset.countP_eq_card_filter]
        unfold Multiset.range
        rw [Multiset.coe_countP]
      -- Simplify the filtered sums
      have hsum_L_simp : (↑(countKStepVectorPerPeriod w k₀ g) : ℤ) * g BinaryStep.L +
          ∑ x ∈ Finset.filter (fun i => ¬Necklace.kStepVector w i k₀ = g) (Finset.range pLen),
            (if Necklace.kStepVector w x k₀ = g' then g' BinaryStep.L else 0) =
          ↑k₀ * pVec BinaryStep.L := by
        have : ∑ x ∈ Finset.filter (fun i => Necklace.kStepVector w i k₀ = g) (Finset.range pLen),
            (if Necklace.kStepVector w x k₀ = g then g BinaryStep.L else if Necklace.kStepVector w x k₀ = g' then g' BinaryStep.L else 0) =
            ∑ x ∈ Finset.filter (fun i => Necklace.kStepVector w i k₀ = g) (Finset.range pLen), g BinaryStep.L := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [Finset.mem_filter] at hx
          simp [hx.2]
        rw [this] at hsum_L
        -- Simplify the second sum: when ¬Necklace.kStepVector w x k₀ = g, the first if is always false
        have : ∑ x ∈ Finset.filter (fun i => ¬Necklace.kStepVector w i k₀ = g) (Finset.range pLen),
            (if Necklace.kStepVector w x k₀ = g then g BinaryStep.L else if Necklace.kStepVector w x k₀ = g' then g' BinaryStep.L else 0) =
            ∑ x ∈ Finset.filter (fun i => ¬Necklace.kStepVector w i k₀ = g) (Finset.range pLen),
            (if Necklace.kStepVector w x k₀ = g' then g' BinaryStep.L else 0) := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [Finset.mem_filter] at hx
          simp [hx.2]
        rw [this] at hsum_L
        rw [h1, h2] at hsum_L
        show (↑(countKStepVectorPerPeriod w k₀ g) : ℤ) * g BinaryStep.L +
          ∑ x ∈ Finset.filter (fun i => ¬Necklace.kStepVector w i k₀ = g) (Finset.range pLen),
            (if Necklace.kStepVector w x k₀ = g' then g' BinaryStep.L else 0) =
          ↑k₀ * pVec BinaryStep.L
        convert hsum_L using 2
      clear hsum_L h1 h2
      convert hsum_L_simp using 2
      -- The second sum equals count(g') * g'(L)
      -- First, show that the filtered sets are equal (since there are only 2 varieties)
      have hfilter_eq : Finset.filter (fun i => ¬Necklace.kStepVector w i k₀ = g) (Finset.range pLen) =
          Finset.filter (fun i => Necklace.kStepVector w i k₀ = g') (Finset.range pLen) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · intro ⟨hi_lt, hi_ne_g⟩
          constructor
          · exact hi_lt
          · -- Necklace.kStepVector w i k₀ must be in {g, g'}
            have hi_mem : Necklace.kStepVector w i k₀ ∈ distinctKStepVectors w k₀ := by
              unfold distinctKStepVectors Necklace.allKStepVectors
              rw [List.mem_toFinset, List.mem_map]
              have hi_lt_n : i < n := calc i < pLen := hi_lt
                _ ≤ n := hpLen_le_n
              exact ⟨i, List.mem_range.mpr hi_lt_n, rfl⟩
            have : distinctKStepVectors w k₀ = {g, g'} := by
              ext v; simp
              exact ⟨fun hv => by
                by_contra hnot
                push_neg at hnot
                have : Finset.card {g, g', v} ≤ 2 := by
                  calc Finset.card {g, g', v}
                    _ ≤ (distinctKStepVectors w k₀).card := by
                      apply Finset.card_le_card
                      intro x hx; simp at hx
                      rcases hx with rfl | rfl | rfl <;> assumption
                    _ = 2 := hcard_eq_2
                have hcard3 : Finset.card {g, g', v} = 3 := by
                  rw [Finset.card_insert_of_notMem (by simp [hg'_ne.symm, hnot.1.symm]),
                      Finset.card_insert_of_notMem (by simp [hnot.2.symm]),
                      Finset.card_singleton]
                omega,
              fun h => by rcases h with rfl | rfl <;> assumption⟩
            rw [this] at hi_mem
            simp at hi_mem
            rcases hi_mem with rfl | rfl
            · contradiction
            · rfl
        · intro ⟨hi_lt, hi_eq_g'⟩
          constructor
          · exact hi_lt
          · rw [hi_eq_g']; exact hg'_ne
      have : ∑ x ∈ Finset.filter (fun i => ¬Necklace.kStepVector w i k₀ = g) (Finset.range pLen),
          (if Necklace.kStepVector w x k₀ = g' then g' BinaryStep.L else 0) =
          ∑ x ∈ Finset.filter (fun i => Necklace.kStepVector w i k₀ = g') (Finset.range pLen), g' BinaryStep.L := by
        rw [← hfilter_eq]
        apply Finset.sum_congr rfl
        intro x hx
        -- hx : x ∈ filter (¬Necklace.kStepVector = g), which by hfilter_eq means x ∈ filter (Necklace.kStepVector = g')
        have hx' : x ∈ Finset.filter (fun i => Necklace.kStepVector w i k₀ = g') (Finset.range pLen) := by
          rw [← hfilter_eq]; exact hx
        simp only [Finset.mem_filter, Finset.mem_range] at hx'
        simp [hx'.2]
      rw [this]; clear this
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      -- Show countKStepVectorPerPeriod w k₀ g' equals the card of the filtered set
      have : (Finset.filter (fun i => Necklace.kStepVector w i k₀ = g') (Finset.range pLen)).card =
          countKStepVectorPerPeriod w k₀ g' := by
        unfold countKStepVectorPerPeriod
        rw [List.countP_eq_length_filter]
        simp only [Finset.filter_val, Finset.range_val, Finset.card_def]
        congr 1
      rw [this]

    -- Rearrange: count(g') * (g(L) - g'(L)) = pLen * g(L) - k₀ * pVec(L)
    have hcount_eq : (countKStepVectorPerPeriod w k₀ g' : ℤ) * (g BinaryStep.L - g' BinaryStep.L) =
        g BinaryStep.L * (pLen : ℤ) - (k₀ : ℤ) * pVec BinaryStep.L := by
      have : (countKStepVectorPerPeriod w k₀ g : ℤ) = pLen - countKStepVectorPerPeriod w k₀ g' := by
        have h := hsum
        have : (countKStepVectorPerPeriod w k₀ g : ℤ) + (countKStepVectorPerPeriod w k₀ g' : ℤ) = (pLen : ℤ) := by
          simp only [← Nat.cast_add, h]
          rfl
        linarith
      rw [this] at hdouble_count
      linarith

    -- From hdet_eq: RHS = det(g, pVec)
    rw [← hdet_eq] at hcount_eq

    -- So count(g') * (g(L) - g'(L)) = det(g, pVec)
    -- Both sides are ±1, so count(g') = ±1
    rcases hdiff_eq_one with hdiff | hdiff <;> rcases hdet with hdet_val | hdet_val
    · -- g(L) - g'(L) = 1, det = 1: count(g') = 1
      rw [hdiff, hdet_val] at hcount_eq
      simp at hcount_eq
      exact_mod_cast hcount_eq
    · -- g(L) - g'(L) = 1, det = -1: count(g') = -1, contradiction
      rw [hdiff, hdet_val] at hcount_eq
      simp at hcount_eq
    · -- g(L) - g'(L) = -1, det = 1: count(g') = -1, contradiction
      rw [hdiff, hdet_val] at hcount_eq
      simp at hcount_eq
      have : (countKStepVectorPerPeriod w k₀ g' : ℤ) = -1 := by linarith
      omega
    · -- g(L) - g'(L) = -1, det = -1: count(g') = 1
      rw [hdiff, hdet_val] at hcount_eq
      ring_nf at hcount_eq
      have : (countKStepVectorPerPeriod w k₀ g' : ℤ) = 1 := by linarith
      omega

/-- ofList distributes over list append -/
private lemma ZVector_ofList_append [DecidableEq α] (l₁ l₂ : List α) (a : α) :
    ZVector.ofList (l₁ ++ l₂) a = ZVector.ofList l₁ a + ZVector.ofList l₂ a := by
  simp only [ZVector.ofList, List.filter_append, List.length_append, Nat.cast_add]

/-- ofList of cons distributes as singleton + tail -/
private lemma ZVector_ofList_cons [DecidableEq α] (x : α) (l : List α) (a : α) :
    ZVector.ofList (x :: l) a = ZVector.ofList [x] a + ZVector.ofList l a := by
  rw [show x :: l = [x] ++ l from rfl, ZVector_ofList_append]

/-- The period of a necklace equals the slice from 0 to the period length -/
private lemma period_eq_slice_zero [NeZero n] [DecidableEq α] (w : Necklace α n) :
    Necklace.period w = Necklace.slice w 0 (Necklace.period w).length := by
  have ⟨l, hl⟩ : ∃ l, Necklace.period w = Necklace.slice w 0 l := by
    unfold Necklace.period
    cases hfind : ((List.range n).tail.map (Necklace.slice w 0)).find?
        (Necklace.isRepetitionOf w) with
    | some pfx =>
      simp only [Option.getD_some]
      have hmem := List.mem_of_find?_eq_some hfind
      rw [List.mem_map] at hmem
      obtain ⟨l, _, rfl⟩ := hmem
      exact ⟨l, rfl⟩
    | none =>
      simp only [Option.getD_none]
      exact ⟨n, rfl⟩
  have hlen : (Necklace.period w).length = l := by
    rw [hl, Necklace.slice_length]; omega
  rw [hlen]; exact hl

/-- Period length is positive -/
private lemma period_length_pos [NeZero n] [DecidableEq α] (w : Necklace α n) :
    0 < (Necklace.period w).length := by
  unfold Necklace.period
  cases hfind : ((List.range n).tail.map (Necklace.slice w 0)).find?
      (Necklace.isRepetitionOf w) with
  | none =>
    simp only [Option.getD_none]
    rw [Necklace.slice_length]
    exact NeZero.pos n
  | some pfx =>
    simp only [Option.getD_some]
    have hmem := List.mem_of_find?_eq_some hfind
    rw [List.mem_map] at hmem
    obtain ⟨k', hk_mem, hk_eq⟩ := hmem
    rw [← hk_eq, Necklace.slice_length]
    simp only [List.tail_range, List.mem_range'] at hk_mem
    omega

/-- Letter count over any full-period-length segment equals the period vector.
    This follows from pointwise periodicity: w(j) = w(j + pLen), so
    "scooting" a window of length pLen doesn't change the letter counts. -/
private lemma kStepVector_full_period [NeZero n] [DecidableEq α] (w : Necklace α n)
    (m : ℕ) (a : α) :
    Necklace.kStepVector w m (Necklace.period w).length a =
    (ZVector.ofList (Necklace.period w)) a := by
  set pLen := (Necklace.period w).length with hpLen_def
  have hpLen_pos : 0 < pLen := period_length_pos w

  -- Pointwise periodicity: w(j) = w(j % pLen) for all j
  -- (copied from the proven pattern inside kStepVector_mod_period)
  have hpLen_dvd_n : pLen ∣ n := by
    have hRep : Necklace.isRepetitionOf w (Necklace.period w) = true := by
      unfold Necklace.period
      cases hfind : ((List.range n).tail.map (Necklace.slice w 0)).find?
          (Necklace.isRepetitionOf w) with
      | some pfx => simp only [Option.getD_some]; exact List.find?_some hfind
      | none =>
        simp only [Option.getD_none]
        unfold Necklace.isRepetitionOf
        simp only [Necklace.slice_length, Nat.sub_zero, ne_eq,
          Nat.pos_iff_ne_zero.mp (NeZero.pos n), ↓reduceIte,
          Nat.mod_self, not_true_eq_false]
        rw [List.all_eq_true]
        intro i hi
        rw [List.mem_range] at hi
        rw [decide_eq_true_eq, Nat.mod_eq_of_lt hi]
        unfold Necklace.slice
        simp only [bind_pure_comp, Functor.map, Nat.sub_zero, Nat.cast_zero, zero_add,
              List.map_map, Function.comp, List.getElem?_map, List.getElem?_range hi,
              Option.map]
    unfold Necklace.isRepetitionOf at hRep
    simp only [ne_eq] at hRep
    split at hRep
    · exact absurd hRep Bool.false_ne_true
    · split at hRep
      · exact absurd hRep Bool.false_ne_true
      · rename_i _ h2
        push_neg at h2
        exact Nat.dvd_of_mod_eq_zero h2

  have hperiodic : ∀ j : ℕ, w ((j : ℕ) : ZMod n) = w ((j % pLen : ℕ) : ZMod n) := by
    intro j
    have hj_mod_n := Nat.mod_lt j (NeZero.pos n)
    have hj_mod_pLen := Nat.mod_lt j hpLen_pos
    conv_lhs => rw [show ((j : ℕ) : ZMod n) = ((j % n : ℕ) : ZMod n) from by simp []]
    have hRep : Necklace.isRepetitionOf w (Necklace.period w) = true := by
      unfold Necklace.period
      cases hfind : ((List.range n).tail.map (Necklace.slice w 0)).find?
          (Necklace.isRepetitionOf w) with
      | some pfx => simp only [Option.getD_some]; exact List.find?_some hfind
      | none =>
        simp only [Option.getD_none]
        unfold Necklace.isRepetitionOf
        simp only [Necklace.slice_length, Nat.sub_zero, ne_eq,
          Nat.pos_iff_ne_zero.mp (NeZero.pos n), ↓reduceIte,
          Nat.mod_self, not_true_eq_false]
        rw [List.all_eq_true]
        intro i hi
        rw [List.mem_range] at hi
        rw [decide_eq_true_eq, Nat.mod_eq_of_lt hi]
        unfold Necklace.slice
        simp only [bind_pure_comp, Functor.map, Nat.sub_zero, Nat.cast_zero, zero_add,
              List.map_map, Function.comp, List.getElem?_map, List.getElem?_range hi,
              Option.map]
    have hperiod_match : ∀ i, i < n →
        some (w ((i : ℕ) : ZMod n)) = (Necklace.period w)[i % pLen]? := by
      intro i hi
      unfold Necklace.isRepetitionOf at hRep
      simp only [ne_eq] at hRep
      split at hRep
      · exact absurd hRep Bool.false_ne_true
      · split at hRep
        · exact absurd hRep Bool.false_ne_true
        · rw [List.all_eq_true] at hRep
          have := hRep i (List.mem_range.mpr hi)
          rwa [decide_eq_true_eq] at this
    have hperiod_is_slice : Necklace.period w = Necklace.slice w 0 pLen :=
      period_eq_slice_zero w
    have hperiod_elem : ∀ j, j < pLen →
        (Necklace.period w)[j]? = some (w ((j : ℕ) : ZMod n)) := by
      intro j hj
      rw [hperiod_is_slice]
      unfold Necklace.slice
      simp only [bind_pure_comp, Functor.map, Nat.sub_zero, Nat.cast_zero, zero_add,
            List.map_map, Function.comp, List.getElem?_map, List.getElem?_range hj,
            Option.map]
    have h1 := hperiod_match (j % n) hj_mod_n
    rw [Nat.mod_mod_of_dvd j hpLen_dvd_n] at h1
    have h2 := hperiod_elem (j % pLen) hj_mod_pLen
    rw [h2] at h1
    exact Option.some_injective _ h1

  -- From hperiodic: w(j) = w(j + pLen) for all j
  have hperiodic_shift : ∀ j : ℕ,
      w ((j : ℕ) : ZMod n) = w (((j + pLen) : ℕ) : ZMod n) := by
    intro j
    rw [hperiodic j, hperiodic (j + pLen), Nat.add_mod_right]

  -- Scoot: Necklace.kStepVector w m' pLen a = Necklace.kStepVector w (m'+1) pLen a
  -- Removing the first element and adding the last doesn't change the count
  -- because w(m') = w(m' + pLen) by periodicity.
  have scoot : ∀ m', Necklace.kStepVector w m' pLen a = Necklace.kStepVector w (m' + 1) pLen a := by
    intro m'
    unfold Necklace.kStepVector
    have h_lhs := slice_shift_decompose w m' pLen hpLen_pos
    have h_rhs := slice_extend_end w (m' + 1) (pLen - 1)
    rw [show (m' + 1) + (pLen - 1) + 1 = m' + 1 + pLen from by omega] at h_rhs
    -- h_rhs may have ↑(m'+1) + ↑(pLen-1) in the ZMod cast for the last element;
    -- we need to also normalize the slice bound
    conv at h_rhs => rhs; rw [show (m' + 1) + (pLen - 1) = m' + pLen from by omega]
    rw [h_lhs, h_rhs, ZVector_ofList_cons, ZVector_ofList_append, hperiodic_shift m']
    -- The last element on RHS may still have the split cast ↑(m'+1) + ↑(pLen-1);
    -- unify with ↑(m'+pLen) using Nat.cast_add
    have hcast : (↑(m' + pLen) : ZMod n) = ↑(m' + 1) + ↑(pLen - 1) := by
      rw [← Nat.cast_add]; congr 1; omega
    rw [hcast]; ring

  -- By induction: Necklace.kStepVector w m pLen a = Necklace.kStepVector w 0 pLen a
  have h_eq_zero : Necklace.kStepVector w m pLen a = Necklace.kStepVector w 0 pLen a := by
    induction m with
    | zero => rfl
    | succ m' ih => rw [← scoot m', ih]
  -- Necklace.kStepVector w 0 pLen = pVec (since period = slice w 0 pLen)
  rw [h_eq_zero]
  unfold Necklace.kStepVector
  congr 1
  rw [show 0 + pLen = pLen from by omega]
  exact (period_eq_slice_zero w).symm

/-- Splitting a prefix: the prefix of length a+b equals the prefix of length a
    plus the k-step vector starting at position a with length b -/
private lemma kStepVector_prefix_add [NeZero n] [DecidableEq α]
    (w : Necklace α n) (a b : ℕ) (c : α) :
    Necklace.kStepVector w 0 (a + b) c = Necklace.kStepVector w 0 a c + Necklace.kStepVector w a b c := by
  unfold Necklace.kStepVector
  rw [← ZVector_ofList_append]
  congr 1
  -- slice w 0 (a + b) = slice w 0 a ++ slice w a (a + b)
  unfold Necklace.slice
  simp only [Nat.zero_add, Nat.add_sub_cancel_left, Nat.sub_zero,
             bind_pure_comp, Functor.map, List.map_map]
  rw [show a + b = a + b from rfl]
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  ext i
  simp [Function.comp]

/-- Converse: If a k-step vector g occurs at exactly (period length - 1) positions
    per period in a MOS scale, then g is a generator. -/
theorem p_minus_one_occurrences_implies_generator [NeZero n]
    (w : BinaryNecklace n) (hw : BinaryNecklace.isMOS w)
    (g : ZVector BinaryStep) (k : ℕ)
    (hk_pos : 0 < k) (hk_bound : k < (Necklace.period w).length)
    (hcount : countKStepVectorPerPeriod w k g = (Necklace.period w).length - 1) :
    IsGenerator w g := by
  let per := Necklace.period w
  let pLen := per.length
  let pVec := ZVector.ofList per
  have hpLen_def : pLen = (Necklace.period w).length := rfl

  -- Part 1: g appears as a k-step vector
  -- Since countKStepVectorPerPeriod = pLen - 1 ≥ 1, g occurs at least once
  have hpLen_pos : pLen > 0 := by
    have : pLen ≥ 2 := period_length_ge_two_of_binary w hw.1
    omega
  have hcount_pos : countKStepVectorPerPeriod w k g ≥ 1 := by
    rw [hcount]; omega

  -- There exists a position where g appears as the k-step vector
  have hg_appears : ∃ i : Fin n, Necklace.kStepVector w i.val k = g := by
    -- countKStepVectorPerPeriod > 0 means g appears at least once in one period
    unfold countKStepVectorPerPeriod at hcount_pos
    simp only [ge_iff_le] at hcount_pos
    -- The count is over Necklace.allKStepVectors restricted to one period
    -- If count ≥ 1, then g ∈ Necklace.allKStepVectors (restricted to period)
    by_contra h
    push_neg at h
    have : countKStepVectorPerPeriod w k g = 0 := by
      unfold countKStepVectorPerPeriod
      rw [List.countP_eq_zero]
      intro i hi
      rw [List.mem_range] at hi
      simp [h ⟨i, Nat.lt_of_lt_of_le hi (Necklace.period_length_le_n w)⟩]
    omega

  constructor
  · -- g is period-reduced: appears as k-step vector with k < pLen
    obtain ⟨i, hi⟩ := hg_appears
    exact ⟨k, hk_bound, i, hi⟩

  · -- Part 2: Exists rotation with prefix bijection
    -- Strategy: stack g exactly (pLen-1) times, covering k*(pLen-1) letters
    have hcoprime : Nat.Coprime k pLen :=
      p_minus_one_occurrences_implies_coprime_to_period w hw k hk_pos hk_bound g hcount
    have hpLen_ge_2 : pLen ≥ 2 := period_length_ge_two_of_binary w hw.1
    have hpLen_le_n : pLen ≤ n := Necklace.period_length_le_n w

    -- Find the unique imperfect position j₀
    obtain ⟨j₀, hj₀_lt, hj₀_ne⟩ : ∃ j₀, j₀ < pLen ∧ Necklace.kStepVector w j₀ k ≠ g := by
      by_contra h
      push_neg at h
      have : countKStepVectorPerPeriod w k g = pLen := by
        show (List.range pLen).countP (fun i => decide (Necklace.kStepVector w i k = g)) = pLen
        have h_all : ∀ i ∈ List.range pLen, decide (Necklace.kStepVector w i k = g) = true := by
          intro i hi; rw [List.mem_range] at hi; simp [h i hi]
        rw [List.countP_eq_length.mpr h_all, List.length_range]
      omega

    -- All other positions have Necklace.kStepVector = g
    have huniq : ∀ i, i < pLen → i ≠ j₀ → Necklace.kStepVector w i k = g := by
      intro i hi hi_ne
      by_contra h_ne_g
      -- Same uniqueness argument as in p_minus_one_occurrences_implies_coprime_to_period
      have hcount' : (List.range pLen).countP (fun j => decide (Necklace.kStepVector w j k = g)) = pLen - 1 :=
        hcount
      have hlen_neg : ((List.range pLen).filter (fun j => !decide (Necklace.kStepVector w j k = g))).length = 1 := by
        have hfilter_sum : ∀ (l : List ℕ) (p : ℕ → Bool),
            (l.filter p).length + (l.filter (fun a => !p a)).length = l.length := by
          intro l p; induction l with
          | nil => simp
          | cons a t ih => cases hp : p a <;> simp_all <;> omega
        have h1 := hfilter_sum (List.range pLen) (fun j => decide (Necklace.kStepVector w j k = g))
        rw [List.length_range] at h1
        have h2 : (List.range pLen).countP (fun j => decide (Necklace.kStepVector w j k = g)) =
            ((List.range pLen).filter (fun j => decide (Necklace.kStepVector w j k = g))).length :=
          List.countP_eq_length_filter
        omega
      obtain ⟨a, ha⟩ : ∃ a, (List.range pLen).filter (fun j => !decide (Necklace.kStepVector w j k = g)) = [a] := by
        set l := (List.range pLen).filter (fun j => !decide (Necklace.kStepVector w j k = g)) with hl_def
        rcases l with _ | ⟨a, _ | ⟨_, _⟩⟩
        · simp at hlen_neg
        · exact ⟨a, rfl⟩
        · simp at hlen_neg
      have hi_mem : i ∈ (List.range pLen).filter (fun j => !decide (Necklace.kStepVector w j k = g)) :=
        List.mem_filter.mpr ⟨List.mem_range.mpr hi, by simp [h_ne_g]⟩
      have hj₀_mem : j₀ ∈ (List.range pLen).filter (fun j => !decide (Necklace.kStepVector w j k = g)) :=
        List.mem_filter.mpr ⟨List.mem_range.mpr hj₀_lt, by simp [hj₀_ne]⟩
      rw [ha] at hi_mem hj₀_mem
      simp at hi_mem hj₀_mem
      exact hi_ne (hi_mem.trans hj₀_mem.symm)

    -- Choose rotation: r = j₀ + k, so that stacking (p-1) copies of g
    -- places the imperfect step at position (p-1)*k
    use (↑(j₀ + k) : ZMod n)
    set w' := fun i => w (i + (↑(j₀ + k) : ZMod n)) with hw'_def

    -- Period invariance: Necklace.kStepVector w' over one full period equals pVec
    have hperiod_vec : ∀ m a, Necklace.kStepVector w' m pLen a = pVec a := by
      intro m a
      -- Convert Necklace.kStepVector w' m pLen to Necklace.kStepVector w (m + (j₀ + k)) pLen
      have hrw : Necklace.kStepVector w' m pLen = Necklace.kStepVector w (m + (j₀ + k)) pLen := by
        unfold Necklace.kStepVector Necklace.slice
        congr 1
        have h1 : m + pLen - m = pLen := by omega
        have h2 : m + (j₀ + k) + pLen - (m + (j₀ + k)) = pLen := by omega
        rw [h1, h2]
        simp only [List.map_map]
        apply List.map_congr_left
        intro l _
        simp only [Function.comp_apply, hw'_def]
        congr 1; push_cast; ring
      rw [show Necklace.kStepVector w' m pLen a = Necklace.kStepVector w (m + (j₀ + k)) pLen a
          from congr_fun hrw a]
      exact kStepVector_full_period w (m + (j₀ + k)) a

    -- Key: Necklace.kStepVector w' (j*k) k = g for j = 0, ..., pLen-2
    -- because the corresponding position in w is ((j+1)*k + j₀) % pLen ≠ j₀
    have hstep_eq_g : ∀ j : ℕ, j < pLen - 1 →
        Necklace.kStepVector w' (j * k) k = Necklace.kStepVector w ((j + 1) * k + j₀) k := by
      intro j _hj
      -- Necklace.kStepVector w' m k = Necklace.kStepVector w (m + (j₀ + k)) k
      -- by unfolding w' = fun i => w(i + ↑(j₀ + k))
      show Necklace.kStepVector (fun i => w (i + (↑(j₀ + k) : ZMod n))) (j * k) k =
           Necklace.kStepVector w ((j + 1) * k + j₀) k
      unfold Necklace.kStepVector Necklace.slice
      congr 1
      have h1 : j * k + k - (j * k) = k := by omega
      have h2 : (j + 1) * k + j₀ + k - ((j + 1) * k + j₀) = k := by omega
      rw [h1, h2]
      simp only [List.map_map]
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      congr 1; push_cast; ring

    have hstep_is_g : ∀ j : ℕ, j < pLen - 1 → Necklace.kStepVector w' (j * k) k = g := by
      intro j hj
      rw [hstep_eq_g j hj]
      rw [← kStepVector_mod_period w _ k (le_of_lt hk_bound)]
      apply huniq
      · exact Nat.mod_lt _ (by omega)
      · intro heq
        -- ((j+1)*k + j₀) % pLen = j₀ means (j+1)*k ≡ 0 mod pLen
        rw [← hpLen_def] at heq
        have : pLen ∣ (j + 1) * k := by
          have hdm := Nat.div_add_mod ((j + 1) * k + j₀) pLen
          rw [heq] at hdm
          exact ⟨((j + 1) * k + j₀) / pLen, by omega⟩
        have : pLen ∣ (j + 1) := by
          exact (hcoprime.symm.dvd_of_dvd_mul_right this)
        have := Nat.le_of_dvd (by omega) this
        omega

    -- Stacking: prefix(j*k) = j * g for j = 0, ..., pLen-1
    have hstacking : ∀ j : ℕ, j ≤ pLen - 1 →
        ∀ a, Necklace.kStepVector w' 0 (j * k) a = ↑j * g a := by
      intro j hj
      induction j with
      | zero => intro a; simp [Necklace.kStepVector, Necklace.slice, ZVector.ofList]
      | succ j' ih =>
        intro a
        have hj'_lt : j' < pLen - 1 := by omega
        rw [show (j' + 1) * k = j' * k + k from by ring]
        rw [kStepVector_prefix_add w' (j' * k) k a]
        rw [ih (by omega) a, hstep_is_g j' hj'_lt]
        push_cast; ring

    -- Period shift: prefix(m + pLen) = prefix(m) + pVec
    -- First: Necklace.kStepVector w' 0 pLen = pVec (one full period = period vector)
    -- prefix(pLen) = pLen-1 copies of g + 1 copy of g'
    -- = (pLen-1)*g + g' = k*pVec (from lettercount sum)
    -- Actually, more directly: prefix(pLen) = pVec since it covers one full period
    -- We prove it by showing Necklace.kStepVector w 0 pLen = pVec from period = slice w 0 pLen
    have hprefix_pLen : ∀ a, Necklace.kStepVector w' 0 pLen a = pVec a :=
      fun a => hperiod_vec 0 a

    -- Forward direction: ∀ i : Fin pLen, ∃ j c, prefix(i+1) = j*g + c*pVec
    -- Backward direction: ∀ j : Fin pLen, ∃ i c, prefix(i+1) = j*g + c*pVec
    constructor
    · -- Forward
      intro ⟨i, hi⟩
      -- For i+1 = pLen: j = 0, c = 1
      by_cases him : i + 1 = pLen
      · refine ⟨⟨0, by omega⟩, 1, ?_⟩
        intro a; simp; rw [him]; exact hprefix_pLen a
      · -- i+1 < pLen: find j with j*k ≡ i+1 (mod pLen)
        have hi1_lt : i + 1 < pLen := by omega
        have hi1_pos : 0 < i + 1 := by omega
        -- Since gcd(k, pLen) = 1, k is invertible mod pLen
        -- j = (i+1) * k⁻¹ mod pLen
        have ⟨j, hj_lt, hjk⟩ : ∃ j, j < pLen ∧ j * k % pLen = (i + 1) % pLen := by
          haveI : NeZero pLen := ⟨by omega⟩
          -- Bezout: k * gcdA(k, pLen) = 1 in ZMod pLen
          have hbez : (↑k : ZMod pLen) * ((Nat.gcdA k pLen : ℤ) : ZMod pLen) = 1 := by
            have h := congr_arg (fun x : ℤ => (x : ZMod pLen)) (Nat.gcd_eq_gcd_ab k pLen)
            push_cast at h
            rw [ZMod.natCast_self, zero_mul, add_zero, hcoprime, Nat.cast_one] at h
            exact h.symm
          -- j = val((i+1) * gcdA(k, pLen)) in ZMod pLen
          set j_zmod : ZMod pLen := (↑(i + 1) : ZMod pLen) * ((Nat.gcdA k pLen : ℤ) : ZMod pLen)
          refine ⟨ZMod.val j_zmod, ZMod.val_lt j_zmod, ?_⟩
          have hj_eq : j_zmod * (↑k : ZMod pLen) = ↑(i + 1) := by
            show (↑(i + 1) : ZMod pLen) * ((Nat.gcdA k pLen : ℤ) : ZMod pLen) * ↑k = ↑(i + 1)
            rw [mul_assoc, mul_comm ((Nat.gcdA k pLen : ℤ) : ZMod pLen) (↑k : ZMod pLen),
                hbez, mul_one]
          have hconv : ZMod.val (↑(ZMod.val j_zmod * k) : ZMod pLen) =
              ZMod.val (↑(i + 1) : ZMod pLen) := by
            congr 1; rw [Nat.cast_mul, ZMod.natCast_zmod_val]; exact hj_eq
          rwa [ZMod.val_natCast, ZMod.val_natCast] at hconv
        have hj_pos : 0 < j := by
          by_contra hj_zero; push_neg at hj_zero
          have : j = 0 := by omega
          subst this; simp at hjk; rw [Nat.mod_eq_of_lt hi1_lt] at hjk; omega
        have hj_le : j ≤ pLen - 1 := by omega
        -- j*k = (i+1) + q*pLen for some q
        have ⟨q, hq⟩ : ∃ q, j * k = (i + 1) + q * pLen := by
          have := Nat.div_add_mod (j * k) pLen
          rw [hjk, Nat.mod_eq_of_lt hi1_lt, mul_comm] at this
          exact ⟨j * k / pLen, by omega⟩
        refine ⟨⟨j, hj_lt⟩, -(q : ℤ), ?_⟩
        intro a
        -- prefix(i+1) = prefix(j*k - q*pLen) = prefix(j*k) - q*pVec = j*g - q*pVec
        have hstack := hstacking j hj_le a
        -- prefix(j*k) = prefix(i+1 + q*pLen) = prefix(i+1) + q*pVec
        -- So prefix(i+1) = prefix(j*k) - q*pVec = j*g - q*pVec
        have hshift : Necklace.kStepVector w' 0 (j * k) a =
            Necklace.kStepVector w' 0 (i + 1) a + ↑q * pVec a := by
          rw [hq]; clear hq
          induction q with
          | zero => simp
          | succ q' ihq =>
            rw [show (i + 1) + (q' + 1) * pLen = (i + 1 + q' * pLen) + pLen from by ring]
            rw [kStepVector_prefix_add w' (i + 1 + q' * pLen) pLen a]
            rw [show (i + 1 + q' * pLen) = (i + 1) + q' * pLen from by ring] at ihq ⊢
            rw [ihq, hperiod_vec _ a]; push_cast; ring
        linarith
    · -- Backward
      intro ⟨j, hj⟩
      by_cases hjz : j = 0
      · -- j = 0: prefix(pLen) = 0*g + 1*pVec
        subst hjz
        refine ⟨⟨pLen - 1, by omega⟩, 1, ?_⟩
        intro a; simp [show pLen - 1 + 1 = pLen from by omega]
        exact hprefix_pLen a
      · -- j > 0: m = j*k mod pLen ∈ {1,...,pLen-1}
        have hj_pos : 0 < j := by omega
        have hj_le : j ≤ pLen - 1 := by omega
        have hjk_mod : j * k % pLen ≠ 0 := by
          intro h
          have : pLen ∣ j * k := Nat.dvd_of_mod_eq_zero h
          have : pLen ∣ j := hcoprime.symm.dvd_of_dvd_mul_right this
          have := Nat.le_of_dvd (by omega) this
          omega
        set m := j * k % pLen with hm_def
        have hm_pos : 0 < m := by omega
        have hm_lt : m < pLen := Nat.mod_lt _ (by omega)
        have ⟨q, hq⟩ : ∃ q, j * k = m + q * pLen := by
          have := Nat.div_add_mod (j * k) pLen
          rw [mul_comm] at this
          exact ⟨j * k / pLen, by omega⟩
        refine ⟨⟨m - 1, by omega⟩, -(q : ℤ), ?_⟩
        intro a
        simp only [show m - 1 + 1 = m from by omega]
        have hstack := hstacking j hj_le a
        have hshift : Necklace.kStepVector w' 0 (j * k) a =
            Necklace.kStepVector w' 0 m a + ↑q * pVec a := by
          rw [hq]; clear hq
          induction q with
          | zero => simp
          | succ q' ihq =>
            rw [show m + (q' + 1) * pLen = (m + q' * pLen) + pLen from by ring]
            rw [kStepVector_prefix_add w' (m + q' * pLen) pLen a]
            rw [ihq, hperiod_vec _ a]; push_cast; ring
        linarith

/-- Characterization: In a MOS scale, g is a generator iff it occurs at exactly
    (period length - 1) positions for some step size k. -/
theorem generator_iff_p_minus_one_occurrences [NeZero n]
    (w : BinaryNecklace n) (hw : BinaryNecklace.isMOS w) (g : ZVector BinaryStep) :
    IsGenerator w g ↔
    (let p := (Necklace.period w).length
     ∃ k : ℕ, 0 < k ∧ k < p ∧ countKStepVectorPerPeriod w k g = p - 1) := by
  constructor
  · exact generator_implies_p_minus_one_occurrences w hw g
  · intro ⟨k, hk_pos, hk_bound, hcount⟩
    exact p_minus_one_occurrences_implies_generator w hw g k hk_pos hk_bound hcount

/-- Indices at which a binary step size occurs in a given binary scale word.
    Needed for chunking. -/
def indices [NeZero n] (x : BinaryStep) (w : BinaryNecklace n) : List (ZMod n) :=
  List.filter (fun i => (Necklace.get w i = x)) (List.range n)

-- Helper: flatMap with singleton preserves length
private lemma flatMap_singleton_length {α β : Type*} (f : α → β) (l : List α) :
    (List.flatMap (fun a => [f a]) l).length = l.length := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.flatMap_cons, List.length_append, ih, List.length]
    exact Nat.add_comm 1 tl.length

-- Helper: coercing List.range m to List (ZMod m) preserves length
private lemma coe_list_range_length (m : ℕ) :
    (do let a ← List.range m; pure (a : ZMod m)).length = m := by
  simp only [List.bind_eq_flatMap, List.pure_def]
  rw [flatMap_singleton_length, List.length_range]

-- Helper: flatMap with singleton equals map
private lemma flatMap_singleton_eq_map {α β : Type*} (f : α → β) (l : List α) :
    List.flatMap (fun a => [f a]) l = l.map f := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp [ih]

-- Helper: coercing List.range m to List (ZMod m) has no duplicates
private lemma coe_list_range_nodup (m : ℕ) [NeZero m] :
    (do let a ← List.range m; pure (a : ZMod m)).Nodup := by
  simp only [List.bind_eq_flatMap, List.pure_def]
  rw [flatMap_singleton_eq_map]
  apply List.Nodup.map_on
  · intro a ha b hb heq
    simp only [List.mem_range] at ha hb
    have := congr_arg ZMod.val heq
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
    exact this
  · exact List.nodup_range

-- indices is nodup
lemma indices_nodup [NeZero n] (x : BinaryStep) (w : BinaryNecklace n) :
    (indices x w).Nodup := by
  unfold indices
  apply List.Nodup.filter
  exact coe_list_range_nodup n

lemma indices_length_le [NeZero n] (x : BinaryStep) (w : BinaryNecklace n) :
    (indices x w).length ≤ n := by
  unfold indices
  refine le_trans (List.length_filter_le _ _) ?_
  rw [coe_list_range_length]

lemma indices_mem_iff [NeZero n] (x : BinaryStep) (w : BinaryNecklace n) (i : ZMod n) :
    i ∈ indices x w ↔ Necklace.get w i = x := by
  unfold indices Necklace.get
  simp only [List.mem_filter, decide_eq_true_eq, List.bind_eq_flatMap, List.pure_def]
  constructor
  · intro ⟨_, hwi⟩
    exact hwi
  · intro hwi
    constructor
    · simp only [List.mem_flatMap, List.mem_singleton, List.mem_range]
      exact ⟨i.val, ZMod.val_lt i, (ZMod.natCast_zmod_val i).symm⟩
    · exact hwi

/-- Number of chunks of step x (equals number of non-x letters) -/
def numChunks [NeZero n] (x : BinaryStep) (w : BinaryNecklace n) : ℕ :=
  (indices (BinaryStep.otherStep x) w).length

-- numChunks x w = count of (otherStep x) letters
lemma numChunks_eq_count [NeZero n] (x : BinaryStep) (w : BinaryNecklace n) :
    numChunks x w = Necklace.count w (BinaryStep.otherStep x) := by
  unfold numChunks Necklace.count
  rw [← List.toFinset_card_of_nodup (indices_nodup _ _)]
  congr 1
  ext i
  simp only [List.mem_toFinset, indices_mem_iff, Finset.mem_filter, Finset.mem_univ, true_and,
             Necklace.get]

/-- We define a *chunk* of a step size x in a binary scale word w
    as a maximal substring consisting entirely of x. -/
def chunkSizesList [NeZero n] (x : BinaryStep) (w : BinaryNecklace n) : Option (List ℕ) := Id.run do
  -- Find the indices of non-x letters (each ends a chunk of x's)
  let is := indices (BinaryStep.otherStep x) w
  match is |>.head? with
    | none => none  -- No non-x letters means no chunks
    | some firstNonX => Id.run do
      let indexVals := List.map ZMod.val is
      let cappedIndexList := indexVals ++ [ZMod.val firstNonX + n]
      return some (List.map (fun i => cappedIndexList[i + 1]! - cappedIndexList[i]! - 1) (List.range is.length))

/-- Convert chunk sizes to a binary necklace: larger chunks become L, smaller become s.
    Returns none if chunk sizes are not exactly two consecutive integers. -/
noncomputable def chunkSizesToBinary [NeZero n] (x : BinaryStep) (w : BinaryNecklace n) : Option (List BinaryStep) := do
  let sizes ← chunkSizesList x w
  let distinctSizes := sizes.toFinset.toList
  match distinctSizes with
  | [_] => some (sizes.map (fun _ => BinaryStep.L))  -- All same size
  | [a, b] =>
    if a + 1 = b || b + 1 = a then
      let smaller := min a b
      some (sizes.map (fun s => if s = smaller then BinaryStep.s else BinaryStep.L))
    else
      none  -- Not consecutive integers
  | _ => none  -- More than 2 distinct sizes

/-!
## Preservation of MOS property under chunking

The proof follows this structure:

1. **Chunk sizes come in at most 2 values**: If a MOS had chunks of 3+ different sizes
   r < r+i < r+j, we could find 3 distinct k-step subwords, contradicting MOS.

2. **Those sizes differ by 1**: If sizes were r and r+i with i > 1, we could again
   find 3 distinct subwords.

3. **The reduced word is MOS**: For any k consecutive chunks, the same argument shows
   they come in at most 2 total sizes. (Proven in a later section.)
-/

/-- The number of chunks equals the length of the sizes list -/
lemma chunkSizesList_length [NeZero n] (x : BinaryStep) (w : BinaryNecklace n)
    (sizes : List ℕ) (hsizes : chunkSizesList x w = some sizes) :
    sizes.length = numChunks x w := by
  unfold chunkSizesList at hsizes
  unfold numChunks
  simp only [Id.run] at hsizes
  -- The sizes list is constructed as List.map ... (List.range is.length)
  -- where is = indices (otherStep x) w
  -- So sizes.length = is.length = numChunks
  set is := indices (BinaryStep.otherStep x) w with his_def
  cases his : is.head? with
  | none =>
    -- If there are no non-x letters, chunkSizesList returns none, contradicting hsizes
    simp only [his] at hsizes
    -- hsizes : none = some sizes, which is a contradiction
    cases hsizes
  | some firstNonX =>
    -- sizes is defined as List.map ... (List.range is.length)
    simp only [his, pure] at hsizes
    -- hsizes : some (List.map ...) = some sizes
    injection hsizes with hsizes'
    rw [← hsizes']
    simp only [List.length_map, List.length_range]

private lemma indices_vals_sublist_range [NeZero n] (x : BinaryStep) (w : BinaryNecklace n) :
    (List.map ZMod.val (indices x w)).Sublist (List.range n) := by
  unfold indices
  simp only [List.bind_eq_flatMap, List.pure_def]
  rw [flatMap_singleton_eq_map]
  have h1 := (List.filter_sublist
    (p := fun i => decide (Necklace.get w i = x))
    (l := List.map (Nat.cast : ℕ → ZMod n) (List.range n))).map ZMod.val
  suffices h2 : (List.map (Nat.cast : ℕ → ZMod n) (List.range n)).map ZMod.val = List.range n by
    rw [h2] at h1; exact h1
  rw [List.map_map]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, Function.comp, List.getElem_range]
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by simpa using h2)]

private lemma indices_vals_pairwise [NeZero n] (x : BinaryStep) (w : BinaryNecklace n) :
    (List.map ZMod.val (indices x w)).Pairwise (· < ·) :=
  List.pairwise_lt_range.sublist (indices_vals_sublist_range x w)

private lemma strict_mono_ge_add (f : ℕ → ℕ) (k : ℕ)
    (hmono : ∀ i, i < k → f i < f (i + 1)) : f k ≥ f 0 + k := by
  induction k with
  | zero => omega
  | succ m ih =>
    have := hmono m (by omega)
    have := ih (fun i hi => hmono i (by omega))
    omega

private lemma telescoping_sum_sub_one (f : ℕ → ℕ) (k : ℕ)
    (hmono : ∀ i, i < k → f i < f (i + 1)) :
    (List.map (fun i => f (i + 1) - f i - 1) (List.range k)).sum = f k - f 0 - k := by
  induction k with
  | zero => simp
  | succ k' ih =>
    rw [List.range_succ, List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton]
    have hmono' := fun i (hi : i < k') => hmono i (by omega)
    rw [ih hmono']
    have hge := strict_mono_ge_add f k' hmono'
    have := hmono k' (by omega)
    omega

/-- The word length equals sum of chunk sizes plus number of chunks.
    n = (∑ sizes) + sizes.length -/
lemma word_length_eq_sum_chunks [NeZero n] (x : BinaryStep) (w : BinaryNecklace n)
    (sizes : List ℕ) (hsizes : chunkSizesList x w = some sizes) :
    n = sizes.sum + sizes.length := by
  -- Unfold chunkSizesList to extract the structure
  unfold chunkSizesList at hsizes
  simp only [Id.run] at hsizes
  set is := indices (BinaryStep.otherStep x) w with his_def
  cases his : is.head? with
  | none =>
    simp only [his] at hsizes
    cases hsizes
  | some firstNonX =>
    simp only [his, pure] at hsizes
    injection hsizes with hsizes'
    -- sizes = List.map (fun i => cappedIndexList[i + 1]! - cappedIndexList[i]! - 1) (List.range is.length)
    set indexVals := List.map ZMod.val is with hindexVals_def
    set cappedIndexList := indexVals ++ [ZMod.val firstNonX + n] with hcapped_def
    -- The sum of (a[i+1] - a[i] - 1) for i in range(k) is a[k] - a[0] - k
    -- Here a[0] = firstNonX.val and a[k] = firstNonX.val + n, so sum = n - k
    have hlen : sizes.length = is.length := by
      rw [← hsizes']
      simp only [List.length_map, List.length_range]
    have hnonempty : is ≠ [] := by
      intro h
      rw [h] at his
      simp at his
    have hindexVals_nonempty : indexVals ≠ [] := by
      simp only [hindexVals_def]
      intro h
      exact hnonempty (List.eq_nil_of_map_eq_nil h)
    -- The telescoping sum property
    -- sizes.sum = sum of (cappedIndexList[i+1] - cappedIndexList[i] - 1) for i in 0..is.length-1
    -- This equals cappedIndexList[is.length] - cappedIndexList[0] - is.length
    -- = (firstNonX.val + n) - firstNonX.val - is.length = n - is.length
    have hsum : sizes.sum = n - is.length := by
      rw [← hsizes']
      -- Apply telescoping sum with f i = cappedIndexList[i]!
      have hmono : ∀ i, i < is.length → cappedIndexList[i]! < cappedIndexList[i + 1]! := by
        intro i hi
        have hcap_len : cappedIndexList.length = is.length + 1 := by
          simp [hcapped_def, hindexVals_def]
        have h1 : i < cappedIndexList.length := by omega
        have h2 : i + 1 < cappedIndexList.length := by omega
        simp only [getElem!_pos cappedIndexList i h1,
                    getElem!_pos cappedIndexList (i + 1) h2]
        have hpw : cappedIndexList.Pairwise (· < ·) := by
          rw [hcapped_def, List.pairwise_append]
          refine ⟨indices_vals_pairwise (BinaryStep.otherStep x) w,
                  List.pairwise_singleton _ _, ?_⟩
          intro a ha b hb
          simp only [List.mem_singleton] at hb; subst hb
          obtain ⟨z, _, rfl⟩ := List.mem_map.mp ha
          have := ZMod.val_lt z
          omega
        exact (List.pairwise_iff_getElem.mp hpw) i (i + 1) (by omega) (by omega) (by omega)
      rw [telescoping_sum_sub_one (fun i => cappedIndexList[i]!) is.length hmono]
      -- Boundary values
      have his_cons : ∃ tail, is = firstNonX :: tail := List.head?_eq_some_iff.mp his
      obtain ⟨tail, htail⟩ := his_cons
      have hfirst : cappedIndexList[0]! = ZMod.val firstNonX := by
        simp [hcapped_def, hindexVals_def, htail]
      have hindexVals_len : indexVals.length = is.length := by
        simp [hindexVals_def]
      have hlast : cappedIndexList[is.length]! = ZMod.val firstNonX + n := by
        rw [List.getElem!_eq_getElem?_getD, hcapped_def, hindexVals_def, htail]
        simp [List.length_map]
      rw [hlast, hfirst]
      omega
    have hlen_le : is.length ≤ n := indices_length_le (BinaryStep.otherStep x) w
    rw [hsum, hlen]
    omega

/-- Any individual chunk size is strictly less than n (since there's at least one non-x) -/
lemma chunk_size_lt_n [NeZero n] (x : BinaryStep) (w : BinaryNecklace n)
    (sizes : List ℕ) (hsizes : chunkSizesList x w = some sizes)
    (s : ℕ) (hs : s ∈ sizes) : s < n := by
  have hlen : sizes.length = numChunks x w := chunkSizesList_length x w sizes hsizes
  have hsum : n = sizes.sum + sizes.length := word_length_eq_sum_chunks x w sizes hsizes
  -- s ≤ sizes.sum, and sizes.length ≥ 1 (since sizes is nonempty)
  have hs_le_sum : s ≤ sizes.sum := List.single_le_sum (fun _ _ => Nat.zero_le _) s hs
  have hlen_pos : 0 < sizes.length := List.length_pos_of_mem hs
  omega

/-- For a binary necklace, any position not in the indices of otherStep x must have value x -/
private lemma not_in_indices_means_eq [NeZero n] (x : BinaryStep) (w : BinaryNecklace n)
    (i : ZMod n) (hi : i ∉ indices (BinaryStep.otherStep x) w) :
    w i = x := by
  have h := mt (indices_mem_iff (BinaryStep.otherStep x) w i).mpr hi
  unfold Necklace.get at h
  push_neg at h
  cases x <;> cases hw : w i <;> simp_all [BinaryStep.otherStep]

/-- Key extraction lemma: if s ∈ sizes from chunkSizesList, there exist s consecutive x-positions -/
private lemma chunk_consecutive_xs [NeZero n] (x : BinaryStep) (w : BinaryNecklace n)
    (sizes : List ℕ) (hsizes : chunkSizesList x w = some sizes)
    (s : ℕ) (hs_mem : s ∈ sizes) :
    ∃ p : ℕ, p < n ∧
      (∀ m : ℕ, m < s → w ((p + m : ℕ) : ZMod n) = x) ∧
      w (((p : ℕ) : ZMod n) - 1) = BinaryStep.otherStep x ∧
      w ((p + s : ℕ) : ZMod n) = BinaryStep.otherStep x := by
  -- Unfold chunkSizesList to extract structure
  unfold chunkSizesList at hsizes
  simp only [Id.run] at hsizes
  set is := indices (BinaryStep.otherStep x) w with his_def
  cases his : is.head? with
  | none => simp [his] at hsizes
  | some firstNonX =>
    simp only [his, pure] at hsizes
    injection hsizes with hsizes'
    set indexVals := List.map ZMod.val is with hindexVals_def
    set cappedIndexList := indexVals ++ [ZMod.val firstNonX + n] with hcapped_def
    -- Find the chunk index j
    rw [hsizes'.symm] at hs_mem
    rw [List.mem_map] at hs_mem
    obtain ⟨j, hj_range, hj_eq⟩ := hs_mem
    rw [List.mem_range] at hj_range
    -- cappedIndexList properties
    have hcap_len : cappedIndexList.length = is.length + 1 := by
      simp [hcapped_def, hindexVals_def]
    have hpw : cappedIndexList.Pairwise (· < ·) := by
      rw [hcapped_def, List.pairwise_append]
      refine ⟨indices_vals_pairwise (BinaryStep.otherStep x) w,
              List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb; subst hb
      obtain ⟨z, _, rfl⟩ := List.mem_map.mp ha
      have := ZMod.val_lt z; omega
    have hmono : ∀ i, i < is.length → cappedIndexList[i]! < cappedIndexList[i + 1]! := by
      intro i hi
      have h1 : i < cappedIndexList.length := by omega
      have h2 : i + 1 < cappedIndexList.length := by omega
      simp only [getElem!_pos cappedIndexList i h1,
                  getElem!_pos cappedIndexList (i + 1) h2]
      exact (List.pairwise_iff_getElem.mp hpw) i (i + 1) (by omega) (by omega) (by omega)
    -- sizes[j] = cappedIndexList[j+1]! - cappedIndexList[j]! - 1
    -- So cappedIndexList[j]! + s + 1 = cappedIndexList[j+1]!
    have hj_gap : cappedIndexList[j]! + s + 1 = cappedIndexList[j + 1]! := by
      have := hmono j hj_range
      omega
    -- All indexVals are < n
    have hindexVals_lt : ∀ v ∈ indexVals, v < n := by
      intro v hv
      rw [hindexVals_def] at hv
      obtain ⟨z, _, rfl⟩ := List.mem_map.mp hv
      exact ZMod.val_lt z
    -- cappedIndexList[j]! < n (it's an indexVal)
    have hcj_lt_n : cappedIndexList[j]! < n := by
      have hindexVals_len : indexVals.length = is.length := by simp [hindexVals_def]
      have hj_lt_iv : j < indexVals.length := by omega
      have hj_lt_cap : j < cappedIndexList.length := by omega
      suffices cappedIndexList[j]! ∈ indexVals from hindexVals_lt _ this
      rw [getElem!_pos cappedIndexList j hj_lt_cap]
      have h : cappedIndexList[j] = indexVals[j] := by
        show (indexVals ++ [ZMod.val firstNonX + n])[j] = indexVals[j]
        exact List.getElem_append_left hj_lt_iv
      rw [h]
      exact List.getElem_mem ..
    -- Choose starting position p = (cappedIndexList[j]! + 1) % n
    refine ⟨(cappedIndexList[j]! + 1) % n, Nat.mod_lt _ (NeZero.pos n), ?_, ?_, ?_⟩
    intro m hm
    -- Need: w (((cappedIndexList[j]! + 1) % n + m : ℕ) : ZMod n) = x
    -- Key: ((cappedIndexList[j]! + 1) % n + m : ZMod n) = ((cappedIndexList[j]! + 1 + m : ℕ) : ZMod n)
    have hcast_eq : (((cappedIndexList[j]! + 1) % n + m : ℕ) : ZMod n) =
        ((cappedIndexList[j]! + 1 + m : ℕ) : ZMod n) := by
      simp only [Nat.cast_add, ZMod.natCast_mod]
    rw [hcast_eq]
    -- Now show w ((cappedIndexList[j]! + 1 + m : ℕ) : ZMod n) = x
    apply not_in_indices_means_eq
    -- Need: ((cappedIndexList[j]! + 1 + m : ℕ) : ZMod n) ∉ indices (otherStep x) w
    intro hmem
    -- hmem : ((cappedIndexList[j]! + 1 + m : ℕ) : ZMod n) ∈ is
    -- So (cappedIndexList[j]! + 1 + m) % n ∈ indexVals
    set q := cappedIndexList[j]! + 1 + m with hq_def
    have hq_lower : cappedIndexList[j]! < q := by omega
    have hq_upper : q < cappedIndexList[j + 1]! := by omega
    have hq_val : ZMod.val ((q : ℕ) : ZMod n) = q % n := ZMod.val_natCast n q
    -- q % n ∈ indexVals (from hmem)
    have hqmod_mem : q % n ∈ indexVals :=
      List.mem_map.mpr ⟨((q : ℕ) : ZMod n), hmem, hq_val⟩
    -- Helper: cappedIndexList sorted implies getElem! monotonicity
    have hsorted_le : ∀ a b, a ≤ b → b < cappedIndexList.length →
        cappedIndexList[a]! ≤ cappedIndexList[b]! := by
      intro a b hab hb
      rcases Nat.eq_or_lt_of_le hab with rfl | hlt
      · exact le_refl _
      · rw [getElem!_pos cappedIndexList a (by omega), getElem!_pos cappedIndexList b hb]
        exact le_of_lt ((List.pairwise_iff_getElem.mp hpw) a b (by omega) hb hlt)
    -- Case split: q < n or q ≥ n
    by_cases hq_lt_n : q < n
    · -- Case q < n: q % n = q, so q ∈ indexVals directly
      rw [Nat.mod_eq_of_lt hq_lt_n] at hqmod_mem
      obtain ⟨j', hj'_lt_iv, hj'_eq⟩ := List.getElem_of_mem hqmod_mem
      have hindexVals_len : indexVals.length = is.length := by simp [hindexVals_def]
      -- cappedIndexList[j']! = indexVals[j']! = q
      have hcj'_eq : cappedIndexList[j']! = q := by
        rw [getElem!_pos cappedIndexList j' (by omega : j' < cappedIndexList.length)]
        exact (List.getElem_append_left hj'_lt_iv).trans hj'_eq
      -- j' can't be ≤ j (cappedIndexList[j']! ≤ cappedIndexList[j]! < q)
      -- j' can't be ≥ j+1 (q < cappedIndexList[j+1]! ≤ cappedIndexList[j']!)
      rcases Nat.lt_or_ge j' (j + 1) with h | h
      · have := hsorted_le j' j (by omega) (by omega : j < cappedIndexList.length)
        omega
      · have := hsorted_le (j + 1) j' h (by omega : j' < cappedIndexList.length)
        omega
    · -- Case q ≥ n
      push_neg at hq_lt_n
      have his_cons := List.head?_eq_some_iff.mp his
      obtain ⟨tail, htail⟩ := his_cons
      have hindexVals_len : indexVals.length = is.length := by simp [hindexVals_def]
      have hfirst_eq : indexVals[0]! = ZMod.val firstNonX := by
        simp [hindexVals_def, htail]
      have hcap_last : cappedIndexList[is.length]! = ZMod.val firstNonX + n := by
        rw [List.getElem!_eq_getElem?_getD, hcapped_def, hindexVals_def, htail]
        simp [List.length_map]
      -- q < firstNonX.val + n (via sorted cappedIndexList)
      have hq_upper' : q < ZMod.val firstNonX + n := by
        rcases Nat.eq_or_lt_of_le (show j + 1 ≤ is.length from hj_range) with heq | hlt
        · rw [heq] at hq_upper; rwa [hcap_last] at hq_upper
        · have := hsorted_le (j + 1) is.length (by omega) (by omega)
          rw [hcap_last] at this; omega
      -- q % n = q - n (since n ≤ q < 2n)
      have hq_mod : q % n = q - n := by
        have : ZMod.val firstNonX < n := ZMod.val_lt firstNonX
        have hqn_lt : q - n < n := by omega
        conv_lhs => rw [show q = q - n + n from by omega]
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt hqn_lt]
      rw [hq_mod] at hqmod_mem
      -- q - n ∈ indexVals, but q - n < firstNonX.val = indexVals[0]!
      -- All indexVals elements ≥ indexVals[0]! by sorted property → contradiction
      have hq_sub : q - n < ZMod.val firstNonX := by omega
      obtain ⟨j', hj'_lt_iv, hj'_eq⟩ := List.getElem_of_mem hqmod_mem
      have hiv_sorted : indexVals.Pairwise (· < ·) := indices_vals_pairwise (BinaryStep.otherStep x) w
      have hiv0_le : indexVals[0]! ≤ indexVals[j']! := by
        rcases j' with _ | j''
        · exact le_refl _
        · rw [getElem!_pos indexVals 0 (by omega), getElem!_pos indexVals (j'' + 1) (by omega)]
          exact le_of_lt ((List.pairwise_iff_getElem.mp hiv_sorted) 0 (j'' + 1) (by omega) (by omega) (by omega))
      rw [hfirst_eq, getElem!_pos indexVals j' hj'_lt_iv, hj'_eq] at hiv0_le
      omega
    -- Goal 2: w(p-1) = otherStep x
    -- p-1 (mod n) = cappedIndexList[j]! = ZMod.val(is[j]), which is a non-x position
    have hp_sub : ((((cappedIndexList[j]! + 1) % n : ℕ) : ZMod n) - 1) =
        ((cappedIndexList[j]! : ℕ) : ZMod n) := by
      simp only [Nat.cast_add, ZMod.natCast_mod]; ring
    rw [hp_sub]
    have hj_lt_iv : j < indexVals.length := by simp [hindexVals_def]; omega
    have hj_lt_cap' : j < cappedIndexList.length := by omega
    have hcj_is : cappedIndexList[j]! = (is[j]'hj_range).val := by
      rw [getElem!_pos cappedIndexList j hj_lt_cap']
      have h1 : (indexVals ++ [ZMod.val firstNonX + n])[j] = indexVals[j] :=
        List.getElem_append_left hj_lt_iv
      rw [h1]; simp [hindexVals_def, List.getElem_map]
    rw [hcj_is, ZMod.natCast_zmod_val]
    exact (indices_mem_iff (BinaryStep.otherStep x) w _).mp (List.getElem_mem ..)
    -- Goal 3: w(p+s) = otherStep x
    -- p+s (mod n) = cappedIndexList[j+1]!, which is a non-x position
    have hps_cast : (((cappedIndexList[j]! + 1) % n + s : ℕ) : ZMod n) =
        ((cappedIndexList[j + 1]! : ℕ) : ZMod n) := by
      rw [show cappedIndexList[j + 1]! = cappedIndexList[j]! + 1 + s from by omega]
      simp only [Nat.cast_add, ZMod.natCast_mod]
    rw [hps_cast]
    rcases Nat.eq_or_lt_of_le (show j + 1 ≤ is.length from hj_range) with heq | hlt
    · -- j + 1 = is.length: cappedIndexList[j+1]! = firstNonX.val + n
      have his_cons := List.head?_eq_some_iff.mp his
      obtain ⟨tail, htail⟩ := his_cons
      have hcap_last : cappedIndexList[is.length]! = ZMod.val firstNonX + n := by
        rw [List.getElem!_eq_getElem?_getD, hcapped_def, hindexVals_def, htail]
        simp [List.length_map]
      rw [heq, hcap_last]
      have : ((ZMod.val firstNonX + n : ℕ) : ZMod n) = firstNonX := by
        push_cast [Nat.cast_add]; simp []
      rw [this]
      have hmem_is : firstNonX ∈ is := by rw [htail]; exact List.mem_cons_self
      exact (indices_mem_iff (BinaryStep.otherStep x) w _).mp hmem_is
    · -- j + 1 < is.length: cappedIndexList[j+1]! = ZMod.val(is[j+1])
      have hj1_lt_iv : j + 1 < indexVals.length := by simp [hindexVals_def]; omega
      have hj1_lt_cap : j + 1 < cappedIndexList.length := by omega
      have hcj1_is : cappedIndexList[j + 1]! = (is[j + 1]'hlt).val := by
        rw [getElem!_pos cappedIndexList (j + 1) hj1_lt_cap]
        have h1 : (indexVals ++ [ZMod.val firstNonX + n])[j + 1] = indexVals[j + 1] :=
          List.getElem_append_left hj1_lt_iv
        rw [h1]; simp [hindexVals_def, List.getElem_map]
      rw [hcj1_is, ZMod.natCast_zmod_val]
      exact (indices_mem_iff (BinaryStep.otherStep x) w _).mp (List.getElem_mem ..)

/-- Count of non-x letters in a k-step subword starting at position i.
    This counts how many chunk boundaries are crossed. -/
noncomputable def countNonX [NeZero n] (x : BinaryStep) (w : BinaryNecklace n) (k i : ℕ) : ℕ :=
  Multiset.count (BinaryStep.otherStep x) (Necklace.abelianize (Necklace.slice w i (i + k)))

/-- Given a chunk index, return the position of the non-x letter that ends this chunk -/
noncomputable def chunkEndPosition [NeZero n] (x : BinaryStep) (w : BinaryNecklace n)
    (chunkIdx : ℕ) : ℕ :=
  let is := indices (BinaryStep.otherStep x) w
  if h : chunkIdx < is.length then
    (is[chunkIdx]'h).val
  else 0

/-- Given a chunk index, the chunk starts at chunkEndPosition of previous chunk + 1 -/
noncomputable def chunkStartPosition [NeZero n] (x : BinaryStep) (w : BinaryNecklace n)
    (chunkIdx : ℕ) : ℕ :=
  if chunkIdx = 0 then
    -- First chunk starts after the last non-x letter (wrapping around)
    let is := indices (BinaryStep.otherStep x) w
    if h : is.length > 0 then
      ((is[is.length - 1]'(Nat.sub_lt h (Nat.zero_lt_one))).val + 1) % n
    else 0
  else
    (chunkEndPosition x w (chunkIdx - 1) + 1) % n

/-- Given a chunk of size s ≥ k in the word, there exists a position where
    the k-step subword contains only x's (0 non-x letters) -/
lemma exists_position_inside_large_chunk [NeZero n] (x : BinaryStep) (w : BinaryNecklace n)
    (sizes : List ℕ) (hsizes : chunkSizesList x w = some sizes)
    (s : ℕ) (hs_mem : s ∈ sizes) (k : ℕ) (hk_le_s : k ≤ s) :
    ∃ i : ℕ, countNonX x w k i = 0 ∧
             Necklace.abelianize (Necklace.slice w i (i + k)) ∈ (Necklace.allKStepMultisets w k) := by
  obtain ⟨p, hp_lt, hp_all_x, -, -⟩ := chunk_consecutive_xs x w sizes hsizes s hs_mem
  refine ⟨p, ?_, ?_⟩
  · -- countNonX x w k p = 0: all k positions are x, so otherStep x doesn't appear
    unfold countNonX Necklace.abelianize Necklace.slice
    rw [show p + k - p = k from by omega, List.map_map]
    simp only [List.bind_eq_flatMap, List.pure_def]
    rw [flatMap_singleton_eq_map, List.map_map, Multiset.count_eq_zero,
        Multiset.mem_coe, List.mem_map]
    push_neg
    intro m hm
    rw [List.mem_range] at hm
    simp only [Function.comp, ← Nat.cast_add]
    rw [hp_all_x m (by omega)]
    cases x <;> simp [BinaryStep.otherStep]
  · -- Membership: p < n, so slice w p (p+k) appears in allKStepMultisets
    unfold Necklace.allKStepMultisets Necklace.allKStepSubwords
    rw [List.mem_map]
    exact ⟨Necklace.slice w p (p + k),
           List.mem_ofFn.mpr ⟨⟨p, hp_lt⟩, rfl⟩, rfl⟩

private lemma slice_start_mod [NeZero n] (w : BinaryNecklace n) (i k : ℕ) :
    Necklace.slice w i (i + k) = Necklace.slice w (i % n) (i % n + k) := by
  simp only [Necklace.slice, Nat.add_sub_cancel_left]
  congr 1
  apply List.map_congr_left
  intro a _
  congr 1
  simp only [ZMod.natCast_mod]

private lemma abelianize_slice_mem_allKStepMultisets [NeZero n]
    (w : BinaryNecklace n) (i k : ℕ) :
    Necklace.abelianize (Necklace.slice w i (i + k)) ∈
      Necklace.allKStepMultisets w k := by
  unfold Necklace.allKStepMultisets Necklace.allKStepSubwords
  rw [List.mem_map]
  exact ⟨Necklace.slice w (i % n) (i % n + k),
    List.mem_ofFn.mpr ⟨⟨i % n, Nat.mod_lt i (NeZero.pos n)⟩, rfl⟩,
    (congrArg Necklace.abelianize (slice_start_mod w i k)).symm⟩

/-- Given a chunk of size s ≥ r+1, the (r+2)-step ending at the chunk boundary
    has exactly 1 non-x -/
lemma exists_position_at_min_chunk [NeZero n] (x : BinaryStep) (w : BinaryNecklace n)
    (sizes : List ℕ) (hsizes : chunkSizesList x w = some sizes)
    (r : ℕ) (_ : r ∈ sizes) (s : ℕ) (hs_mem : s ∈ sizes) (hs_ge : s ≥ r + 1) :
    ∃ i : ℕ, countNonX x w (r + 2) i = 1 ∧
             Necklace.abelianize (Necklace.slice w i (i + (r + 2))) ∈ (Necklace.allKStepMultisets w (r + 2)) := by
  -- Use the chunk of size s. Start (r+2)-step at p+(s-r-1): last r+1 x's of chunk + boundary non-x
  obtain ⟨p, hp_lt, hp_all_x, -, hp_after⟩ := chunk_consecutive_xs x w sizes hsizes s hs_mem
  refine ⟨p + (s - r - 1), ?_, abelianize_slice_mem_allKStepMultisets w _ _⟩
  · -- countNonX = 1
    unfold countNonX Necklace.abelianize Necklace.slice
    rw [show p + (s - r - 1) + (r + 2) - (p + (s - r - 1)) = r + 2 from by omega, List.map_map]
    simp only [List.bind_eq_flatMap, List.pure_def]
    rw [flatMap_singleton_eq_map, List.map_map]
    -- Split range(r+2) = range(r+1) ++ [r+1]
    rw [show r + 2 = (r + 1) + 1 from by ring, List.range_succ, List.map_append,
        ← Multiset.coe_add, Multiset.count_add, List.map_cons, List.map_nil]
    -- Last element: w at p+s = otherStep x
    have h_last : w ((↑(p + (s - r - 1) + (r + 1)) : ZMod n)) = BinaryStep.otherStep x := by
      simp only [show p + (s - r - 1) + (r + 1) = p + s from by omega]; exact hp_after
    dsimp only [Function.comp]
    simp only [← Nat.cast_add, h_last,
               ← Multiset.cons_coe, Multiset.coe_nil, Multiset.count_cons_self, Multiset.count_zero]
    -- Normalize List.map function (need function equality for rw to find it)
    have h_normalize : ((w ∘ fun k ↦ (↑(p + (s - r - 1)) : ZMod n) + k) ∘ Nat.cast) =
        (fun m => w ((↑(p + (s - r - 1) + m) : ZMod n))) := by
      funext m; simp [Function.comp, Nat.cast_add]
    rw [h_normalize]
    suffices h : Multiset.count (BinaryStep.otherStep x)
        (Multiset.ofList
          (List.map (fun m => w ((↑(p + (s - r - 1) + m) : ZMod n))) (List.range (r + 1)))) = 0 by
      omega
    rw [Multiset.count_eq_zero, Multiset.mem_coe, List.mem_map]
    push_neg
    intro m hm
    rw [List.mem_range] at hm
    have : s - r - 1 + m < s := by omega
    rw [show p + (s - r - 1) + m = p + (s - r - 1 + m) from by ring]
    rw [hp_all_x (s - r - 1 + m) this]
    cases x <;> simp [BinaryStep.otherStep]

/-- Given a chunk of size r, the (r+2)-step starting at the non-x before it
    has exactly 2 non-x letters -/
lemma exists_position_before_min_chunk [NeZero n] (x : BinaryStep) (w : BinaryNecklace n)
    (sizes : List ℕ) (hsizes : chunkSizesList x w = some sizes)
    (r : ℕ) (hr_mem : r ∈ sizes) :
    ∃ i : ℕ, countNonX x w (r + 2) i = 2 ∧
             Necklace.abelianize (Necklace.slice w i (i + (r + 2))) ∈ (Necklace.allKStepMultisets w (r + 2)) := by
  -- Start (r+2)-step at p+n-1 (≡ p-1 mod n): [non-x | r x's | non-x] = 2 non-x
  obtain ⟨p, hp_lt, hp_all_x, hp_before, hp_after⟩ := chunk_consecutive_xs x w sizes hsizes r hr_mem
  have hn_pos : 0 < n := NeZero.pos n
  -- Key position facts using ZMod arithmetic
  have h_first : w ((↑(p + n - 1) : ZMod n)) = BinaryStep.otherStep x := by
    have h_cast : ((p + n - 1 : ℕ) : ZMod n) = ((p : ℕ) : ZMod n) - 1 := by
      rw [show p + n - 1 = p + (n - 1) from by omega, Nat.cast_add]
      have h_neg1 : ((n - 1 : ℕ) : ZMod n) = -1 := by
        apply eq_neg_of_add_eq_zero_left
        have : ((n - 1 + 1 : ℕ) : ZMod n) = 0 := by
          rw [show n - 1 + 1 = n from by omega]; exact ZMod.natCast_self n
        rwa [Nat.cast_add, Nat.cast_one] at this
      rw [h_neg1]; ring
    rw [h_cast]; exact hp_before
  have h_mid : ∀ m, m < r → w ((↑(p + n - 1 + (m + 1)) : ZMod n)) = x := by
    intro m hm
    have h_cast : ((p + n - 1 + (m + 1) : ℕ) : ZMod n) = ((p + m : ℕ) : ZMod n) := by
      rw [show p + n - 1 + (m + 1) = p + m + n from by omega, Nat.cast_add,
          ZMod.natCast_self n, add_zero]
    rw [h_cast]; exact hp_all_x m (by omega)
  have h_last : w ((↑(p + n - 1 + (r + 1)) : ZMod n)) = BinaryStep.otherStep x := by
    have h_cast : ((p + n - 1 + (r + 1) : ℕ) : ZMod n) = ((p + r : ℕ) : ZMod n) := by
      rw [show p + n - 1 + (r + 1) = p + r + n from by omega, Nat.cast_add,
          ZMod.natCast_self n, add_zero]
    rw [h_cast]; exact hp_after
  refine ⟨p + n - 1, ?_, abelianize_slice_mem_allKStepMultisets w _ _⟩
  · -- countNonX = 2
    unfold countNonX Necklace.abelianize Necklace.slice
    rw [show p + n - 1 + (r + 2) - (p + n - 1) = r + 2 from by omega, List.map_map]
    simp only [List.bind_eq_flatMap, List.pure_def]
    rw [flatMap_singleton_eq_map, List.map_map]
    -- Split 1: range(r+2) = range(r+1) ++ [r+1]
    rw [show r + 2 = (r + 1) + 1 from by ring, List.range_succ, List.map_append,
        ← Multiset.coe_add, Multiset.count_add, List.map_cons, List.map_nil]
    -- Last element (position r+1): otherStep x → count = 1
    dsimp only [Function.comp] at h_last ⊢
    simp only [← Nat.cast_add, h_last,
               ← Multiset.cons_coe, Multiset.coe_nil, Multiset.count_cons_self, Multiset.count_zero]
    -- Goal: count_first + 1 = 2
    -- Split 2: range(r+1) = 0 :: map Nat.succ (range r) (using range_succ_eq_map)
    rw [show r + 1 = r + 1 from rfl, List.range_succ_eq_map, List.map_cons, List.map_map,
        ← Multiset.cons_coe]
    dsimp only [Function.comp] at h_first ⊢
    simp only [Nat.cast_zero, add_zero] at h_first ⊢
    rw [h_first, Multiset.count_cons_self]
    -- Normalize List.map function (need function equality for rw to find it)
    have h_normalize : (((w ∘ fun k ↦ (↑(p + n - 1) : ZMod n) + k) ∘ Nat.cast) ∘ Nat.succ) =
        (fun m => w ((↑(p + n - 1 + Nat.succ m) : ZMod n))) := by
      funext m; simp [Function.comp, Nat.cast_add]
    rw [h_normalize]
    suffices h : Multiset.count (BinaryStep.otherStep x)
        (Multiset.ofList
          (List.map (fun m => w ((↑(p + n - 1 + (Nat.succ m)) : ZMod n)))
            (List.range r))) = 0 by omega
    rw [Multiset.count_eq_zero, Multiset.mem_coe, List.mem_map]
    push_neg
    intro m hm
    rw [List.mem_range] at hm
    rw [Nat.succ_eq_add_one, h_mid m hm]
    cases x <;> simp [BinaryStep.otherStep]

/-- Two multisets with different counts of a letter are distinct -/
lemma multiset_ne_of_count_ne {α : Type*} [DecidableEq α] (m1 m2 : Multiset α) (a : α)
    (h : Multiset.count a m1 ≠ Multiset.count a m2) : m1 ≠ m2 := by
  intro heq
  rw [heq] at h
  exact h rfl

/-- Three multisets with counts 0, 1, 2 of some letter are pairwise distinct -/
lemma three_multisets_distinct {α : Type*} [DecidableEq α]
    (m0 m1 m2 : Multiset α) (a : α)
    (h0 : Multiset.count a m0 = 0)
    (h1 : Multiset.count a m1 = 1)
    (h2 : Multiset.count a m2 = 2) :
    m0 ≠ m1 ∧ m1 ≠ m2 ∧ m0 ≠ m2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro heq; rw [heq, h1] at h0; exact absurd h0 (by decide)
  · intro heq; rw [heq, h2] at h1; exact absurd h1 (by decide)
  · intro heq; rw [heq, h2] at h0; exact absurd h0 (by decide)

/-- Key lemma: If w is MOS, chunk sizes come in at most 2 distinct values,
    and those values must be consecutive (r and r+1 for some r).

    Proof: Let r be the minimum chunk size. Consider k = r + 2 step subwords.
    We get three distinct abelianizations from different starting positions:
    1. Starting at the non-x before a size-r chunk: [y|xxxx|y] = r x's, 2 non-x's
    2. Starting at a size-r chunk: [xxxx|y|x...] = (r+1) x's, 1 non-x
    3. Inside a chunk of size ≥ r+2 (if exists): [xxxxxxxx] = (r+2) x's, 0 non-x's

    If any chunk has size ≥ r+2, case 3 applies and we get 3 distinct vectors,
    contradicting MOS. Therefore all chunks have size r or r+1 (consecutive). -/
lemma mos_chunk_sizes_at_most_two (n : ℕ) [NeZero n] (w : BinaryNecklace n)
    (hw : BinaryNecklace.isMOS w) (x : BinaryStep) (sizes : List ℕ)
    (hsizes : chunkSizesList x w = some sizes) :
    sizes.toFinset.card ≤ 2 := by
  -- Proof by contradiction: assume 3+ distinct sizes
  by_contra h
  push_neg at h
  have hcard : 3 ≤ sizes.toFinset.card := h

  -- Extract minimum size r
  have hnonempty : sizes.toFinset.Nonempty := by
    by_contra hempty
    simp only [Finset.not_nonempty_iff_eq_empty] at hempty
    simp [hempty] at hcard
  let r := sizes.toFinset.min' hnonempty

  -- With 3+ distinct sizes, the maximum size is ≥ r + 2
  -- (since we have at least r, r+?, r+?? with gaps of at least 1 each)
  have hmax_ge : ∃ s ∈ sizes.toFinset, s ≥ r + 2 := by
    -- With 3 distinct naturals and minimum r, the other two are ≥ r+1 and ≥ r+2
    -- We use: if S has 3+ elements and min is r, then S \ {r} has 2+ elements with min ≥ r+1
    -- And (S \ {r}) \ {min(S\{r})} has 1+ element with value ≥ r+2
    let S := sizes.toFinset
    have hS_card : 3 ≤ S.card := hcard
    -- S contains r (the minimum)
    have hr_mem : r ∈ S := Finset.min'_mem S hnonempty
    -- S \ {r} has at least 2 elements
    let S' := S.erase r
    have hS'_card : 2 ≤ S'.card := by
      have : S'.card = S.card - 1 := Finset.card_erase_of_mem hr_mem
      omega
    have hS'_nonempty : S'.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      simp [h] at hS'_card
    -- The minimum of S' is > r (since we removed r, the minimum of S)
    let r' := S'.min' hS'_nonempty
    have hr'_mem : r' ∈ S' := Finset.min'_mem S' hS'_nonempty
    have hr'_gt_r : r < r' := by
      have hr'_in_S : r' ∈ S := Finset.mem_of_mem_erase hr'_mem
      have hr'_ne_r : r' ≠ r := Finset.ne_of_mem_erase hr'_mem
      have hr_le_r' : r ≤ r' := Finset.min'_le S r' hr'_in_S
      omega
    have hr'_ge : r' ≥ r + 1 := hr'_gt_r
    -- S' \ {r'} has at least 1 element
    let S'' := S'.erase r'
    have hS''_card : 1 ≤ S''.card := by
      have : S''.card = S'.card - 1 := Finset.card_erase_of_mem hr'_mem
      omega
    have hS''_nonempty : S''.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      simp [h] at hS''_card
    -- The minimum of S'' is > r' ≥ r + 1, so it's ≥ r + 2
    let r'' := S''.min' hS''_nonempty
    have hr''_mem : r'' ∈ S'' := Finset.min'_mem S'' hS''_nonempty
    have hr''_gt_r' : r' < r'' := by
      have hr''_in_S' : r'' ∈ S' := Finset.mem_of_mem_erase hr''_mem
      have hr''_ne_r' : r'' ≠ r' := Finset.ne_of_mem_erase hr''_mem
      have hr'_le_r'' : r' ≤ r'' := Finset.min'_le S' r'' hr''_in_S'
      omega
    have hr''_ge : r'' ≥ r + 2 := by omega
    -- r'' is in SW
    have hr''_in_S : r'' ∈ S := by
      have h1 : r'' ∈ S' := Finset.mem_of_mem_erase hr''_mem
      exact Finset.mem_of_mem_erase h1
    exact ⟨r'', hr''_in_S, hr''_ge⟩

  -- The key k-step to consider is r + 2
  let k := r + 2
  have hk_pos : 0 < k := Nat.zero_lt_succ _

  -- k < n because n ≥ (size of largest chunk) + (number of chunks) ≥ (r+2) + 1 > r + 2
  have hk_lt_n : k < n := by
    -- The word contains a chunk of size ≥ r+2 plus at least one non-x letter
    -- So n ≥ (r + 2) + 1 > r + 2 = k
    obtain ⟨s, hs_mem, hs_ge⟩ := hmax_ge
    -- s is in sizes.toFinset, so s ∈ sizes
    have hs_in_list : s ∈ sizes := List.mem_toFinset.mp hs_mem
    -- Use our helper: any chunk size < n
    have hs_lt_n : s < n := chunk_size_lt_n x w sizes hsizes s hs_in_list
    -- s ≥ r + 2, and s < n, so r + 2 < n, i.e., k < n
    omega

  -- Now we show there are 3 distinct k-step vectors, contradicting MOS
  -- The three cases from starting at different positions:
  --   1. Start at non-x before a size-r chunk: [y|xxx...r...|y] → {r x, 2 non-x}
  --   2. Start at beginning of size-r chunk: [xxx...r...|y|x] → {r+1 x, 1 non-x}
  --   3. Start inside chunk of size ≥ r+2: [xxx...r+2...] → {r+2 x, 0 non-x}

  have hmos_k := hw.2 k hk_pos hk_lt_n

  have hthree_vectors : (Necklace.allKStepMultisets w k).toFinset.card ≥ 3 := by
    -- We construct three distinct (r+2)-step vectors by choosing starting positions:
    --
    -- Position A: Start at the non-x before a size-r chunk → 2 non-x letters
    -- Position B: Start at the first x of a size-r chunk → 1 non-x letter
    -- Position C: Start inside a chunk of size ≥ r+2 → 0 non-x letters
    --
    -- These are distinct because they have 2, 1, 0 non-x letters respectively.

    obtain ⟨largeSize, hLarge_mem, hLarge_ge⟩ := hmax_ge
    have hr_mem : r ∈ sizes.toFinset := Finset.min'_mem sizes.toFinset hnonempty
    have hr_in_list : r ∈ sizes := List.mem_toFinset.mp hr_mem
    have hLarge_in_list : largeSize ∈ sizes := List.mem_toFinset.mp hLarge_mem

    -- Position C: inside a chunk of size largeSize ≥ k = r+2
    obtain ⟨iC, hcountC, hvecC⟩ := exists_position_inside_large_chunk x w sizes hsizes
      largeSize hLarge_in_list k hLarge_ge

    -- Position B: at the end of a chunk of size ≥ r+1 (using largeSize ≥ r+2 ≥ r+1)
    obtain ⟨iB, hcountB, hvecB⟩ := exists_position_at_min_chunk x w sizes hsizes r hr_in_list
      largeSize hLarge_in_list (by omega)

    -- Position A: at the non-x before a chunk of size r
    obtain ⟨iA, hcountA, hvecA⟩ := exists_position_before_min_chunk x w sizes hsizes r hr_in_list

    -- The three vectors are distinct (they have 0, 1, 2 non-x letters)
    let vC := Necklace.abelianize (Necklace.slice w iC (iC + k))
    let vB := Necklace.abelianize (Necklace.slice w iB (iB + k))
    let vA := Necklace.abelianize (Necklace.slice w iA (iA + k))

    have hdistinct : vC ≠ vB ∧ vB ≠ vA ∧ vC ≠ vA := by
      -- countNonX gives the count of otherStep x in the abelianization
      -- vC has count 0, vB has count 1, vA has count 2
      have hC : Multiset.count (BinaryStep.otherStep x) vC = 0 := hcountC
      have hB : Multiset.count (BinaryStep.otherStep x) vB = 1 := hcountB
      have hA : Multiset.count (BinaryStep.otherStep x) vA = 2 := hcountA
      exact three_multisets_distinct vC vB vA (BinaryStep.otherStep x) hC hB hA

    -- All three vectors are in allKStepMultisets, so the finset has ≥ 3 elements
    have hvecC' : vC ∈ (Necklace.allKStepMultisets w k).toFinset := List.mem_toFinset.mpr hvecC
    have hvecB' : vB ∈ (Necklace.allKStepMultisets w k).toFinset := List.mem_toFinset.mpr hvecB
    have hvecA' : vA ∈ (Necklace.allKStepMultisets w k).toFinset := List.mem_toFinset.mpr hvecA

    -- Three distinct elements in a finset means card ≥ 3
    have h3 : ({vC, vB, vA} : Finset _) ⊆ (Necklace.allKStepMultisets w k).toFinset := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · exact hvecC'
      · exact hvecB'
      · exact hvecA'
    have hcard3 : ({vC, vB, vA} : Finset _).card = 3 := by
      have hne1 : vC ≠ vB := hdistinct.1
      have hne2 : vB ≠ vA := hdistinct.2.1
      have hne3 : vC ≠ vA := hdistinct.2.2
      simp only [Finset.card_insert_eq_ite, Finset.card_singleton, Finset.mem_insert,
                 Finset.mem_singleton]
      simp only [hne1, hne2, hne3, or_self, if_false]
    calc (Necklace.allKStepMultisets w k).toFinset.card
        ≥ ({vC, vB, vA} : Finset _).card := Finset.card_le_card h3
      _ = 3 := hcard3

  omega

/-- Key lemma: If w is MOS and has chunks of 2 distinct sizes, they differ by exactly 1.

    Proof: Same as mos_chunk_sizes_at_most_two. If sizes were r and r+i with i > 1,
    then the larger size is ≥ r+2, and the same three positions give three distinct
    (r+2)-step vectors:
    1. Start at non-x before size-r chunk: {r x, 2 non-x}
    2. Start at size-(r+i) chunk: {(r+1) x, 1 non-x}
    3. Inside size-(r+i) chunk: {(r+2) x, 0 non-x}
    This contradicts MOS. -/
lemma mos_chunk_sizes_consecutive (n : ℕ) [NeZero n] (w : BinaryNecklace n)
    (hw : BinaryNecklace.isMOS w) (x : BinaryStep) (sizes : List ℕ)
    (hsizes : chunkSizesList x w = some sizes) (a b : ℕ)
    (ha : a ∈ sizes.toFinset) (hb : b ∈ sizes.toFinset) (hab : a ≠ b) :
    a + 1 = b ∨ b + 1 = a := by
  -- WLOG assume a < b (the other case is symmetric)
  by_contra hnotcons
  push_neg at hnotcons
  -- So a + 1 ≠ b and b + 1 ≠ a, meaning |a - b| ≥ 2
  have hdiff : (a < b ∧ a + 1 < b) ∨ (b < a ∧ b + 1 < a) := by
    rcases Nat.lt_trichotomy a b with hlt | heq | hgt
    · left; exact ⟨hlt, Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hlt) hnotcons.1⟩
    · exact absurd heq hab
    · right; exact ⟨hgt, Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hgt) hnotcons.2⟩

  -- Let r = min(a,b), then max(a,b) ≥ r + 2
  -- This gives 3 distinct (r+2)-step vectors, same argument as mos_chunk_sizes_at_most_two
  rcases hdiff with ⟨hab_lt, hab_gap⟩ | ⟨hba_lt, hba_gap⟩
  · -- Case: a < b and a + 1 < b, so b ≥ a + 2
    -- Use r = a, the larger chunk b ≥ r + 2
    let r := a
    let k := r + 2
    have hk_pos : 0 < k := Nat.zero_lt_succ _

    -- k < n because chunk size b ≥ r+2 exists and any chunk size < n
    have ha_in_list : a ∈ sizes := List.mem_toFinset.mp ha
    have hb_in_list : b ∈ sizes := List.mem_toFinset.mp hb
    have hb_ge : b ≥ r + 2 := hab_gap
    have hb_lt_n : b < n := chunk_size_lt_n x w sizes hsizes b hb_in_list
    have hk_lt_n : k < n := Nat.lt_of_le_of_lt hb_ge hb_lt_n

    -- Apply MOS property
    have hmos_k := hw.2 k hk_pos hk_lt_n

    -- Get three positions with 0, 1, 2 non-x letters
    obtain ⟨iC, hcountC, hvecC⟩ := exists_position_inside_large_chunk x w sizes hsizes
      b hb_in_list k hb_ge
    obtain ⟨iB, hcountB, hvecB⟩ := exists_position_at_min_chunk x w sizes hsizes r ha_in_list
      b hb_in_list (by omega)
    obtain ⟨iA, hcountA, hvecA⟩ := exists_position_before_min_chunk x w sizes hsizes r ha_in_list

    -- The three vectors are distinct
    let vC := Necklace.abelianize (Necklace.slice w iC (iC + k))
    let vB := Necklace.abelianize (Necklace.slice w iB (iB + k))
    let vA := Necklace.abelianize (Necklace.slice w iA (iA + k))

    have hdistinct : vC ≠ vB ∧ vB ≠ vA ∧ vC ≠ vA :=
      three_multisets_distinct vC vB vA (BinaryStep.otherStep x) hcountC hcountB hcountA

    have hvecC' : vC ∈ (Necklace.allKStepMultisets w k).toFinset := List.mem_toFinset.mpr hvecC
    have hvecB' : vB ∈ (Necklace.allKStepMultisets w k).toFinset := List.mem_toFinset.mpr hvecB
    have hvecA' : vA ∈ (Necklace.allKStepMultisets w k).toFinset := List.mem_toFinset.mpr hvecA

    have h3 : ({vC, vB, vA} : Finset _) ⊆ (Necklace.allKStepMultisets w k).toFinset := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;> assumption
    have hcard3 : ({vC, vB, vA} : Finset _).card = 3 := by
      simp only [Finset.card_insert_eq_ite, Finset.card_singleton, Finset.mem_insert,
                 Finset.mem_singleton]
      simp only [hdistinct.1, hdistinct.2.1, hdistinct.2.2, or_self, if_false]
    have hcard_ge : (Necklace.allKStepMultisets w k).toFinset.card ≥ 3 :=
      calc (Necklace.allKStepMultisets w k).toFinset.card
          ≥ ({vC, vB, vA} : Finset _).card := Finset.card_le_card h3
        _ = 3 := hcard3
    omega

  · -- Case: b < a and b + 1 < a, so a ≥ b + 2 (symmetric)
    let r := b
    let k := r + 2
    have hk_pos : 0 < k := Nat.zero_lt_succ _

    have ha_in_list : a ∈ sizes := List.mem_toFinset.mp ha
    have hb_in_list : b ∈ sizes := List.mem_toFinset.mp hb
    have ha_ge : a ≥ r + 2 := hba_gap
    have ha_lt_n : a < n := chunk_size_lt_n x w sizes hsizes a ha_in_list
    have hk_lt_n : k < n := Nat.lt_of_le_of_lt ha_ge ha_lt_n

    have hmos_k := hw.2 k hk_pos hk_lt_n

    obtain ⟨iC, hcountC, hvecC⟩ := exists_position_inside_large_chunk x w sizes hsizes
      a ha_in_list k ha_ge
    obtain ⟨iB, hcountB, hvecB⟩ := exists_position_at_min_chunk x w sizes hsizes r hb_in_list
      a ha_in_list (by omega)
    obtain ⟨iA, hcountA, hvecA⟩ := exists_position_before_min_chunk x w sizes hsizes r hb_in_list

    let vC := Necklace.abelianize (Necklace.slice w iC (iC + k))
    let vB := Necklace.abelianize (Necklace.slice w iB (iB + k))
    let vA := Necklace.abelianize (Necklace.slice w iA (iA + k))

    have hdistinct : vC ≠ vB ∧ vB ≠ vA ∧ vC ≠ vA :=
      three_multisets_distinct vC vB vA (BinaryStep.otherStep x) hcountC hcountB hcountA

    have hvecC' : vC ∈ (Necklace.allKStepMultisets w k).toFinset := List.mem_toFinset.mpr hvecC
    have hvecB' : vB ∈ (Necklace.allKStepMultisets w k).toFinset := List.mem_toFinset.mpr hvecB
    have hvecA' : vA ∈ (Necklace.allKStepMultisets w k).toFinset := List.mem_toFinset.mpr hvecA

    have h3 : ({vC, vB, vA} : Finset _) ⊆ (Necklace.allKStepMultisets w k).toFinset := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;> assumption
    have hcard3 : ({vC, vB, vA} : Finset _).card = 3 := by
      simp only [Finset.card_insert_eq_ite, Finset.card_singleton, Finset.mem_insert,
                 Finset.mem_singleton]
      simp only [hdistinct.1, hdistinct.2.1, hdistinct.2.2, or_self, if_false]
    have hcard_ge : (Necklace.allKStepMultisets w k).toFinset.card ≥ 3 :=
      calc (Necklace.allKStepMultisets w k).toFinset.card
          ≥ ({vC, vB, vA} : Finset _).card := Finset.card_le_card h3
        _ = 3 := hcard3
    omega

/-- If chunkSizesList succeeds, the sizes list is nonempty -/
lemma chunkSizesList_nonempty [NeZero n] (x : BinaryStep) (w : BinaryNecklace n)
    (sizes : List ℕ) (hsizes : chunkSizesList x w = some sizes) :
    sizes ≠ [] := by
  intro hempty
  unfold chunkSizesList at hsizes
  simp only [Id.run] at hsizes
  set is := indices (BinaryStep.otherStep x) w with his_def
  cases his : is.head? with
  | none =>
    simp only [his] at hsizes
    cases hsizes
  | some firstNonX =>
    simp only [his, pure] at hsizes
    -- sizes = List.map ... (List.range is.length)
    injection hsizes with hsizes'
    rw [hempty] at hsizes'
    -- List.map ... (List.range is.length) = [] means is.length = 0
    have hlen : is.length = 0 := by
      have : List.range is.length = [] := by
        by_contra hne
        have hmap_ne : (List.map (fun i =>
          (List.map ZMod.val is ++ [firstNonX.val + n])[i + 1]! -
          (List.map ZMod.val is ++ [firstNonX.val + n])[i]! - 1) (List.range is.length)) ≠ [] := by
          intro h
          rw [List.map_eq_nil_iff] at h
          exact hne h
        rw [hsizes'] at hmap_ne
        exact hmap_ne rfl
      have hrange_len : (List.range is.length).length = 0 := by simp [this]
      simp only [List.length_range] at hrange_len
      exact hrange_len
    -- But is.head? = some _, so is.length > 0
    have hpos : is.length > 0 := by
      cases his' : is with
      | nil =>
        simp only [his', List.head?_nil] at his
        cases his
      | cons hd tl => simp only [List.length_cons, Nat.add_one_pos]
    omega

/-- For a MOS scale, chunkSizesToBinary never returns none when chunkSizesList succeeds.
    This is because MOS scales have at most 2 distinct chunk sizes and they are consecutive. -/
lemma mos_chunkSizesToBinary_ne_none (n : ℕ) [NeZero n] (w : BinaryNecklace n)
    (hw : BinaryNecklace.isMOS w) (x : BinaryStep) (sizes : List ℕ)
    (hsizes : chunkSizesList x w = some sizes)
    (hcontra : chunkSizesToBinary x w = none) : False := by
  unfold chunkSizesToBinary at hcontra
  simp only [hsizes] at hcontra
  -- The do notation expands to (some sizes).bind (fun sizes => ...) which equals the body
  change (match sizes.toFinset.toList with
    | [_] => some (sizes.map (fun _ => BinaryStep.L))
    | [a, b] => if a + 1 = b || b + 1 = a then
        some (sizes.map (fun s => if s = min a b then BinaryStep.s else BinaryStep.L))
      else none
    | _ => none) = none at hcontra
  -- Now hcontra should be about the match expression
  -- Analyze based on number of distinct sizes
  have hat_most_two := mos_chunk_sizes_at_most_two n w hw x sizes hsizes
  have hnonempty := chunkSizesList_nonempty x w sizes hsizes
  -- Split on the match in hcontra
  split at hcontra
  · -- Case: one distinct size [c] - returns some, not none
    cases hcontra
  · -- Case: two distinct sizes [a, b] with consecutive check
    rename_i a b hdistinct
    split at hcontra
    · -- Consecutive: returns some, not none
      cases hcontra
    · -- Not consecutive: but MOS guarantees they are consecutive
      rename_i hnotcons
      have ha : a ∈ sizes.toFinset := by
        rw [← Finset.mem_toList, hdistinct]
        exact List.Mem.head _
      have hb : b ∈ sizes.toFinset := by
        rw [← Finset.mem_toList, hdistinct]
        exact List.Mem.tail a (List.Mem.head _)
      have hab : a ≠ b := by
        intro heq
        have hnodup : sizes.toFinset.toList.Nodup := Finset.nodup_toList _
        rw [hdistinct] at hnodup
        simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
          List.nodup_nil, and_true] at hnodup
        exact hnodup heq
      have hcons := mos_chunk_sizes_consecutive n w hw x sizes hsizes a b ha hb hab
      simp only [decide_eq_true_eq, Bool.or_eq_true, not_or] at hnotcons
      rcases hcons with hcons | hcons <;> omega
  · -- Case: 0 or 3+ distinct sizes - impossible
    rename_i hcase1 hcase2
    -- hcase1 : ∀ head, sizes.toFinset.toList = [head] → False (singleton case doesn't match)
    -- hcase2 : ∀ a b, sizes.toFinset.toList = [a, b] → False (pair case doesn't match)
    -- Either empty (contradicts nonempty) or 3+ (contradicts at_most_two)
    cases hdist_cases : sizes.toFinset.toList with
    | nil =>
      have hcard_zero : sizes.toFinset.card = 0 := by
        rw [← Finset.length_toList, hdist_cases]
        rfl
      have hcard_pos : 0 < sizes.toFinset.card := by
        rw [Finset.card_pos, Finset.nonempty_iff_ne_empty]
        intro hempty
        apply hnonempty
        rw [← List.toFinset_eq_empty_iff, hempty]
      omega
    | cons c rest =>
      cases rest with
      | nil => exact hcase1 c hdist_cases
      | cons d rest' =>
        cases rest' with
        | nil => exact hcase2 c d hdist_cases
        | cons _ _ =>
          have hlen3 : sizes.toFinset.toList.length ≥ 3 := by
            rw [hdist_cases]
            simp only [List.length_cons, ge_iff_le]
            omega
          rw [Finset.length_toList] at hlen3
          omega

/-!
## Periodicity and Repetition

When a MOS has step signature aLbs where d = gcd(a, b) > 1, the word is a d-fold repetition
of a smaller MOS with signature (a/d)L(b/d)s.

This allows us to reduce the multi-period case to the primitive (single-period) case where
gcd(a, b) = 1, and then further reduce to base cases nL1s or 1Lns.
-/

/-- A necklace is a d-fold repetition if w(i) = w(i + n/d) for all i -/
def isRepetition [NeZero n] (w : Necklace α n) (d : ℕ) : Prop :=
  d ∣ n ∧ d > 0 ∧ ∀ i : ZMod n, w i = w (i + (n / d : ℕ))

/-- The primitive period length of a necklace (smallest p such that w is n/p-fold repetition) -/
noncomputable def primitiveLength [NeZero n] [DecidableEq α] (w : Necklace α n) : ℕ :=
  (Necklace.period w).length

/-- Helper: n = a + b for a MOS with signature (a, b) -/
lemma mos_length_eq_sum [NeZero n] (w : BinaryNecklace n)
    (a b : ℕ) (hsig : BinaryNecklace.hasStepSignature w a b) :
    n = a + b := by
  unfold BinaryNecklace.hasStepSignature at hsig
  have hn := Finset.card_univ (α := ZMod n)
  simp only [ZMod.card] at hn
  -- Every position is either L or s
  have hpartition : Finset.univ = Finset.filter (fun i => w i = BinaryStep.L) Finset.univ ∪
                                   Finset.filter (fun i => w i = BinaryStep.s) Finset.univ := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and]
    constructor
    · intro _
      cases hw : w i with
      | L => exact Or.inl rfl
      | s => exact Or.inr rfl
    · intro _; trivial
  have hdisj : Disjoint (Finset.filter (fun i => w i = BinaryStep.L) Finset.univ)
                        (Finset.filter (fun i => w i = BinaryStep.s) Finset.univ) := by
    simp only [Finset.disjoint_filter]
    intro i _ hL hs
    rw [hL] at hs
    exact absurd hs (by decide)
  rw [hpartition, Finset.card_union_of_disjoint hdisj] at hn
  unfold BinaryNecklace.stepSignature Necklace.count at hsig
  simp only [Prod.mk.injEq] at hsig
  omega

/-- Helper: d divides n when d = gcd(a,b) and n = a + b -/
lemma gcd_dvd_sum (a b d : ℕ) (hd : d = Nat.gcd a b) : d ∣ (a + b) := by
  rw [hd]
  exact Nat.dvd_add (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b)

/-- Sum of letter counts across all n starting positions equals k times the total letter count.
    This is a double-counting argument: each occurrence of letter `a` in the necklace
    appears in exactly k windows. -/
private lemma kStepVector_lettercount_sum_all [NeZero n] (w : BinaryNecklace n)
    (k : ℕ) (a : BinaryStep) :
    ∑ i ∈ Finset.range n, (Necklace.kStepVector w i k) a =
    ↑k * ↑(Necklace.count w a) := by
  -- Step 1: Express each k-step vector count as sum of indicators (List sum)
  have h_expand : ∀ i, i < n →
    (Necklace.kStepVector w i k) a = ((List.range k).map (fun m =>
      if w (((i + m : ℕ) : ZMod n)) = a then (1 : ℤ) else 0)).sum := by
    intro i _hi
    unfold Necklace.kStepVector ZVector.ofList Necklace.slice
    rw [show i + k - i = k from by omega, List.map_map,
        list_filter_beq_length_eq_map_ite_sum, List.map_map]
    simp [pure, bind, Nat.cast_add, List.flatMap]
    congr 1
    ext m
    simp [Function.comp]
  -- Step 2: Rewrite LHS as double Finset sum
  have h_lhs : ∑ i ∈ Finset.range n, (Necklace.kStepVector w i k) a =
    ∑ i ∈ Finset.range n, ∑ m ∈ Finset.range k,
      if w (((i + m : ℕ) : ZMod n)) = a then (1 : ℤ) else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [h_expand i (Finset.mem_range.mp hi), list_range_map_sum_eq_finset]
  rw [h_lhs]
  -- Step 3: Exchange summation order
  rw [Finset.sum_comm]
  -- Step 4: Each inner sum counts letter a = count(a)
  -- We prove this by induction on the shift m.
  -- Base case (m=0): direct bijection between range n and ZMod n.
  -- Inductive step: use sum_range_succ/succ' and the fact that (n : ZMod n) = 0.
  have h_shift : ∀ m : ℕ, ∑ i ∈ Finset.range n,
      (if w (((i + m : ℕ) : ZMod n)) = a then (1 : ℤ) else 0) =
      ↑(Necklace.count w a) := by
    intro m
    induction m with
    | zero =>
      simp only [Nat.add_zero]
      -- Convert ℤ indicator sum → ℕ card → Necklace.count
      simp_rw [show ∀ i : ℕ, (if w ((i : ℕ) : ZMod n) = a then (1 : ℤ) else 0) =
          ↑(if w ((i : ℕ) : ZMod n) = a then 1 else 0 : ℕ) from
          fun i => by split_ifs <;> simp]
      rw [← Nat.cast_sum, Finset.sum_boole]
      -- Goal: ↑((range n).filter ...).card = ↑(Necklace.count w a)
      congr 1
      unfold Necklace.count
      apply Finset.card_bij (fun i _hi => ((i : ℕ) : ZMod n))
      · intro i hi
        simp only [Finset.mem_filter] at hi ⊢
        exact ⟨Finset.mem_univ _, hi.2⟩
      · intro i₁ hi₁ i₂ hi₂ h
        have h1 := (Finset.mem_filter.mp hi₁).1
        have h2 := (Finset.mem_filter.mp hi₂).1
        rw [Finset.mem_range] at h1 h2
        have := congr_arg ZMod.val h
        rwa [ZMod.val_natCast, ZMod.val_natCast,
             Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact ⟨ZMod.val j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt j),
          by rw [ZMod.natCast_zmod_val]; exact hj⟩, ZMod.natCast_zmod_val j⟩
    | succ m ih =>
      rw [← ih]
      simp_rw [show ∀ i : ℕ, i + (m + 1) = (i + 1) + m from fun i => by omega]
      set g : ℕ → ℤ := fun j => if w (((j + m : ℕ) : ZMod n)) = a then 1 else 0 with hg_def
      -- g(n) = g(0) since (n + m : ZMod n) = (0 + m : ZMod n)
      have hg_periodic : g n = g 0 := by
        simp only [hg_def, Nat.zero_add]
        have : ((n + m : ℕ) : ZMod n) = ((m : ℕ) : ZMod n) := by
          push_cast; simp []
        rw [this]
      have h1 := Finset.sum_range_succ' g n
      have h2 := Finset.sum_range_succ g n
      linarith
  have h_const : ∑ m ∈ Finset.range k,
      (∑ i ∈ Finset.range n,
        (if w (((i + m : ℕ) : ZMod n)) = a then (1 : ℤ) else 0)) =
      ∑ _m ∈ Finset.range k, ↑(Necklace.count w a) :=
    Finset.sum_congr rfl (fun m _ => h_shift m)
  rw [h_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-!
## Multi-period reduction via scooting (Bjorklund approach)

This section proves that a MOS with gcd(a,b) = d > 1 is a d-fold repetition, using
the "scooting" argument rather than the Bresenham characterization.

### Key insight
When you "scoot" a k-step vector by one position (from i to i+1), the vector changes
by at most one letter substitution: you lose w[i] and gain w[i+k]. This means:
- If two k-step vectors differ by more than one letter, there must be intermediate vectors
- In a MOS, any two vectors can differ by at most one letter

### Main argument
If (n/d)-steps came in 2 sizes with different L-counts, scooting from one to the other
would reveal intermediate sizes, contradicting the MOS property. Therefore all (n/d)-steps
have the same size, which must be the period.
-/

/-- A MOS with gcd(a,b) = d > 1 has only one (n/d)-step vector size.
    This is because if there were two sizes differing by more than one step,
    scooting would reveal intermediate sizes. And if they differ by exactly one step,
    the total L-count constraint is violated. -/
lemma mos_period_step_unique [NeZero n] (w : BinaryNecklace n) (hw : BinaryNecklace.isMOS w)
    (a b : ℕ) (hsig : BinaryNecklace.hasStepSignature w a b)
    (d : ℕ) (hd : d = Nat.gcd a b) (hd_gt : d > 1) :
    (distinctKStepVectors w (n / d)).card = 1 := by
  -- Setup: k = n/d, need 0 < k < n
  let k := n / d
  have hn_eq : n = a + b := mos_length_eq_sum w a b hsig
  have hd_dvd_n : d ∣ n := by rw [hn_eq]; exact gcd_dvd_sum a b d hd
  have hd_dvd_a : d ∣ a := by rw [hd]; exact Nat.gcd_dvd_left a b
  have hd_pos : d > 0 := Nat.zero_lt_one.trans hd_gt
  have hn_pos : n > 0 := NeZero.pos n
  -- k > 0: since d | n and n > 0, we have k = n/d ≥ 1
  have hk_pos : k > 0 := Nat.div_pos (Nat.le_of_dvd hn_pos hd_dvd_n) hd_pos
  -- k < n: since d > 1 and d | n, we have n/d < n
  have hk_lt_n : k < n := Nat.div_lt_self hn_pos hd_gt
  -- By MOS property, at most 2 distinct k-step vectors
  have hcard_le_2 : (distinctKStepVectors w k).card ≤ 2 := by
    rw [distinctKStepVectors_card_eq]
    exact hw.2 k hk_pos hk_lt_n
  -- There's at least one k-step vector (from position 0)
  have hcard_ge_1 : (distinctKStepVectors w k).card ≥ 1 := by
    have hmem : Necklace.kStepVector w 0 k ∈ distinctKStepVectors w k := by
      unfold distinctKStepVectors Necklace.allKStepVectors
      rw [List.mem_toFinset, List.mem_map]
      exact ⟨0, List.mem_range.mpr hn_pos, rfl⟩
    exact Finset.card_pos.mpr ⟨_, hmem⟩
  -- Assume for contradiction there are exactly 2
  by_contra h_ne_1
  have hcard_eq_2 : (distinctKStepVectors w k).card = 2 := by
    have h1 : (distinctKStepVectors w k).card ≥ 1 := hcard_ge_1
    have h2 : (distinctKStepVectors w k).card ≤ 2 := hcard_le_2
    rcases Nat.lt_trichotomy (distinctKStepVectors w k).card 2 with hlt | heq | hgt
    · -- card < 2, so card = 0 or card = 1
      interval_cases (distinctKStepVectors w k).card; omega
    · exact heq
    · omega
  -- Get the two distinct vectors
  rw [Finset.card_eq_two] at hcard_eq_2
  obtain ⟨v1, v2, hne, hcard⟩ := hcard_eq_2
  have hv1_mem : v1 ∈ distinctKStepVectors w k := by rw [hcard]; simp
  have hv2_mem : v2 ∈ distinctKStepVectors w k := by rw [hcard]; simp
  -- By mos_kStepVector_L_count_diff_le_one, their L-counts differ by at most 1
  have hdiff_le_1 := mos_kStepVector_L_count_diff_le_one w hw k hk_pos hk_lt_n v1 v2 hv1_mem hv2_mem
  -- Since v1 ≠ v2, they must have different L-counts (for binary ZVectors, L-count determines the vector)
  have hL_ne : v1 BinaryStep.L ≠ v2 BinaryStep.L := by
    intro hL_eq
    -- If L-counts are equal, s-counts are also equal (s = k - L), so ZVectors are equal
    apply hne
    funext x
    cases x with
    | L => exact hL_eq
    | s =>
      -- Extract witness indices: v1 = kStepVector w i1 k, v2 = kStepVector w i2 k
      have hv1_list := List.mem_toFinset.mp hv1_mem
      have hv2_list := List.mem_toFinset.mp hv2_mem
      rw [Necklace.allKStepVectors, List.mem_map] at hv1_list hv2_list
      obtain ⟨i1, _, hi1⟩ := hv1_list
      obtain ⟨i2, _, hi2⟩ := hv2_list
      have h1 := kStepVector_total_count w i1 k
      have h2 := kStepVector_total_count w i2 k
      rw [hi1] at h1; rw [hi2] at h2
      omega
  -- L-counts differ by exactly 1 (since |L1 - L2| ≤ 1 and L1 ≠ L2)
  -- hdiff_le_1 : (v1 L) - 1 ≤ v2 L ∧ v2 L ≤ (v1 L) + 1 (all in ℤ)
  have hdiff_eq_1 : v1 BinaryStep.L = v2 BinaryStep.L + 1 ∨
                    v2 BinaryStep.L = v1 BinaryStep.L + 1 := by
    rcases hdiff_le_1 with ⟨h1, h2⟩
    -- h1 : (v1 L) - 1 ≤ v2 L
    -- h2 : v2 L ≤ (v1 L) + 1
    rcases Int.lt_trichotomy (v1 BinaryStep.L) (v2 BinaryStep.L) with hlt | heq | hgt
    · -- v1.L < v2.L
      right; omega
    · -- v1.L = v2.L, contradicts hL_ne
      exact absurd heq hL_ne
    · -- v1.L > v2.L
      left; omega
  -- Step A: Extract Necklace.count w BinaryStep.L = a from signature
  have hcountL : Necklace.count w BinaryStep.L = a := by
    have := hsig
    unfold BinaryNecklace.hasStepSignature BinaryNecklace.stepSignature at this
    exact (Prod.mk.inj this).1
  -- Step B: Sum formula from helper lemma
  have hsum := kStepVector_lettercount_sum_all w k BinaryStep.L
  rw [hcountL] at hsum
  -- hsum : ∑ i ∈ Finset.range n, (kStepVector w i k) L = ↑k * ↑a
  -- Step C: Every position's k-step vector is v1 or v2
  have hmem_pair : ∀ i ∈ Finset.range n,
      Necklace.kStepVector w i k = v1 ∨ Necklace.kStepVector w i k = v2 := by
    intro i hi
    have hmem : Necklace.kStepVector w i k ∈ distinctKStepVectors w k := by
      unfold distinctKStepVectors Necklace.allKStepVectors
      rw [List.mem_toFinset, List.mem_map]
      exact ⟨i, List.mem_range.mpr (Finset.mem_range.mp hi), rfl⟩
    rw [hcard] at hmem
    rcases Finset.mem_insert.mp hmem with h | h
    · left; exact h
    · right; exact Finset.mem_singleton.mp h
  -- Step D: Split the sum over positions where kStepVector = v1 vs ≠ v1
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range n)
      (fun i => Necklace.kStepVector w i k = v1)] at hsum
  -- Simplify each filtered sum
  -- For filter (= v1): each term is v1 L
  have hsum1 : ∑ i ∈ (Finset.range n).filter (fun i => Necklace.kStepVector w i k = v1),
      (Necklace.kStepVector w i k) BinaryStep.L =
      ↑((Finset.range n).filter (fun i => Necklace.kStepVector w i k = v1)).card *
      v1 BinaryStep.L := by
    have : ∀ i ∈ (Finset.range n).filter (fun i => Necklace.kStepVector w i k = v1),
        (Necklace.kStepVector w i k) BinaryStep.L = v1 BinaryStep.L :=
      fun i hi => congr_fun (Finset.mem_filter.mp hi).2 _
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  -- For filter (≠ v1): each must be v2
  have hS2_eq_v2 : ∀ i ∈ (Finset.range n).filter (fun i => ¬Necklace.kStepVector w i k = v1),
      Necklace.kStepVector w i k = v2 := by
    intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hi_range, hi_ne⟩
    rcases hmem_pair i hi_range with h | h
    · exact absurd h hi_ne
    · exact h
  have hsum2 : ∑ i ∈ (Finset.range n).filter (fun i => ¬Necklace.kStepVector w i k = v1),
      (Necklace.kStepVector w i k) BinaryStep.L =
      ↑((Finset.range n).filter (fun i => ¬Necklace.kStepVector w i k = v1)).card *
      v2 BinaryStep.L := by
    have : ∀ i ∈ (Finset.range n).filter (fun i => ¬Necklace.kStepVector w i k = v1),
        (Necklace.kStepVector w i k) BinaryStep.L = v2 BinaryStep.L :=
      fun i hi => congr_fun (hS2_eq_v2 i hi) _
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  rw [hsum1, hsum2] at hsum
  -- Step E: Set up cardinality arithmetic
  set N1 := ((Finset.range n).filter (fun i => Necklace.kStepVector w i k = v1)).card with hN1_def
  set N2 := ((Finset.range n).filter (fun i => ¬Necklace.kStepVector w i k = v1)).card with hN2_def
  -- N1 + N2 = n
  have hN_sum : N1 + N2 = n := by
    simp only [hN1_def, hN2_def]
    have hu : (Finset.range n) =
        (Finset.range n).filter (fun i => Necklace.kStepVector w i k = v1) ∪
        (Finset.range n).filter (fun i => ¬Necklace.kStepVector w i k = v1) := by
      ext x; simp [Finset.mem_union, Finset.mem_filter]; tauto
    have hd : Disjoint
        ((Finset.range n).filter (fun i => Necklace.kStepVector w i k = v1))
        ((Finset.range n).filter (fun i => ¬Necklace.kStepVector w i k = v1)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_filter] at hx1 hx2
      exact hx2.2 hx1.2
    rw [← Finset.card_union_of_disjoint hd, ← hu, Finset.card_range]
  -- N1 ≥ 1 (v1 actually occurs)
  have hN1_pos : N1 ≥ 1 := by
    rw [hN1_def]
    have hv1_list := List.mem_toFinset.mp hv1_mem
    rw [Necklace.allKStepVectors, List.mem_map] at hv1_list
    obtain ⟨i1, hi1_range, hi1_eq⟩ := hv1_list
    exact Finset.card_pos.mpr ⟨i1, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (List.mem_range.mp hi1_range), hi1_eq⟩⟩
  -- N2 ≥ 1 (v2 actually occurs)
  have hN2_pos : N2 ≥ 1 := by
    rw [hN2_def]
    have hv2_list := List.mem_toFinset.mp hv2_mem
    rw [Necklace.allKStepVectors, List.mem_map] at hv2_list
    obtain ⟨i2, hi2_range, hi2_eq⟩ := hv2_list
    exact Finset.card_pos.mpr ⟨i2, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (List.mem_range.mp hi2_range),
       fun h => hne (h.symm.trans hi2_eq)⟩⟩
  -- So 1 ≤ N1 ≤ n - 1
  have hN1_lt_n : N1 < n := by omega
  -- Step F: k * a = n * (a / d) since k = n/d and d | a
  have hka_eq : (k : ℤ) * (a : ℤ) = (n : ℤ) * ↑(a / d) := by
    have hkd : k * d = n := Nat.div_mul_cancel hd_dvd_n
    have had : a / d * d = a := Nat.div_mul_cancel hd_dvd_a
    push_cast
    nlinarith
  -- Step G: Derive contradiction from divisibility
  -- hsum : ↑N1 * v1.L + ↑N2 * v2.L = ↑k * ↑a = ↑n * ↑(a/d)
  rw [hka_eq] at hsum
  rcases hdiff_eq_1 with hv1_eq | hv2_eq
  · -- Case: v1 L = v2 L + 1
    rw [hv1_eq] at hsum
    -- ↑N1 * (v2.L + 1) + ↑N2 * v2.L = ↑n * ↑(a/d)
    -- ↑N1 * v2.L + ↑N1 + ↑N2 * v2.L = ↑n * ↑(a/d)
    -- (↑N1 + ↑N2) * v2.L + ↑N1 = ↑n * ↑(a/d)
    -- ↑n * v2.L + ↑N1 = ↑n * ↑(a/d)
    -- ↑N1 = ↑n * (↑(a/d) - v2.L)
    have hN1_eq : (N1 : ℤ) = ↑n * (↑(a / d) - v2 BinaryStep.L) := by
      have hN_cast : (↑N1 + ↑N2 : ℤ) = (↑n : ℤ) := by exact_mod_cast hN_sum
      have h1 : (↑N1 + ↑N2) * v2 BinaryStep.L + ↑N1 = ↑n * ↑(a / d) := by
        linarith [mul_add (↑N1 : ℤ) (v2 BinaryStep.L) 1,
                  add_mul (↑N1 : ℤ) ↑N2 (v2 BinaryStep.L)]
      rw [hN_cast] at h1
      linarith [mul_sub (↑n : ℤ) (↑(a / d) : ℤ) (v2 BinaryStep.L)]
    -- So n | N1
    have hdvd : (n : ℤ) ∣ ↑N1 := ⟨↑(a / d) - v2 BinaryStep.L, hN1_eq⟩
    rw [Int.natCast_dvd_natCast] at hdvd
    -- But 1 ≤ N1 < n, contradicting n | N1
    exact Nat.not_lt.mpr (Nat.le_of_dvd (by omega) hdvd) hN1_lt_n
  · -- Case: v2 L = v1 L + 1
    rw [hv2_eq] at hsum
    -- ↑N1 * v1.L + ↑N2 * (v1.L + 1) = ↑n * ↑(a/d)
    -- (↑N1 + ↑N2) * v1.L + ↑N2 = ↑n * ↑(a/d)
    -- ↑n * v1.L + ↑N2 = ↑n * ↑(a/d)
    -- ↑N2 = ↑n * (↑(a/d) - v1.L)
    have hN2_eq : (N2 : ℤ) = ↑n * (↑(a / d) - v1 BinaryStep.L) := by
      have hN_cast : (↑N1 + ↑N2 : ℤ) = (↑n : ℤ) := by exact_mod_cast hN_sum
      have h1 : (↑N1 + ↑N2) * v1 BinaryStep.L + ↑N2 = ↑n * ↑(a / d) := by
        linarith [mul_add (↑N2 : ℤ) (v1 BinaryStep.L) 1,
                  add_mul (↑N1 : ℤ) ↑N2 (v1 BinaryStep.L)]
      rw [hN_cast] at h1
      linarith [mul_sub (↑n : ℤ) (↑(a / d) : ℤ) (v1 BinaryStep.L)]
    have hdvd : (n : ℤ) ∣ ↑N2 := ⟨↑(a / d) - v1 BinaryStep.L, hN2_eq⟩
    rw [Int.natCast_dvd_natCast] at hdvd
    have hN2_lt_n : N2 < n := by omega
    exact Nat.not_lt.mpr (Nat.le_of_dvd (by omega) hdvd) hN2_lt_n

/-- A MOS with gcd(a,b) = d > 1 is a d-fold repetition (Bjorklund approach).
    The proof uses the scooting argument instead of the Bresenham characterization. -/
lemma mos_repetition_of_gcd_bjorklund [NeZero n] (w : BinaryNecklace n) (hw : BinaryNecklace.isMOS w)
    (a b : ℕ) (hsig : BinaryNecklace.hasStepSignature w a b) (d : ℕ) (hd : d = Nat.gcd a b)
    (hd_gt : d > 1) :
    isRepetition w d := by
  -- Step 1: d divides n
  have hn_eq : n = a + b := mos_length_eq_sum w a b hsig
  have hd_dvd_n : d ∣ n := by rw [hn_eq]; exact gcd_dvd_sum a b d hd
  have hd_pos : d > 0 := Nat.zero_lt_one.trans hd_gt
  -- Step 2: Show all (n/d)-step vectors are identical
  have hunique := mos_period_step_unique w hw a b hsig d hd hd_gt
  -- Step 3: If all (n/d)-steps are the same, the word repeats with period n/d
  refine ⟨hd_dvd_n, hd_pos, ?_⟩
  intro i
  -- w[i] and w[i + n/d] are the first elements of k-step vectors starting at i and i+n/d
  -- Since all (n/d)-step vectors are the same, the slices [i, i+n/d) and [i+n/d, i+2n/d)
  -- have the same multiset. Combined with the scooting argument, this implies w[i] = w[i+n/d]
  let k := n / d
  -- Since card = 1, all k-step vectors are the same
  -- In particular, Necklace.kStepVector at i.val and Necklace.kStepVector at (i.val + 1) are equal
  -- This means the L-count (and hence the multiset) doesn't change when scooting
  -- By scooting: L(i+1) = L(i) - delta_out + delta_in
  --              where delta_out = (w[i]=L ? 1 : 0), delta_in = (w[i+k]=L ? 1 : 0)
  -- If L(i) = L(i+1), then delta_out = delta_in, so w[i] = w[i+k]
  have hk_eq : k = n / d := rfl
  -- Get that all vectors in distinctKStepVectors are equal (there's only one)
  have hsing : ∀ v1 v2, v1 ∈ distinctKStepVectors w k → v2 ∈ distinctKStepVectors w k → v1 = v2 := by
    intro v1 v2 hv1 hv2
    have : (distinctKStepVectors w k).card = 1 := hunique
    rw [Finset.card_eq_one] at this
    obtain ⟨v, hv⟩ := this
    rw [hv] at hv1 hv2
    simp only [Finset.mem_singleton] at hv1 hv2
    rw [hv1, hv2]
  -- Show Necklace.kStepVector at any position is in distinctKStepVectors
  have hmem : ∀ j : ℕ, Necklace.kStepVector w j k ∈ distinctKStepVectors w k := by
    intro j
    unfold distinctKStepVectors Necklace.allKStepVectors
    rw [List.mem_toFinset, List.mem_map]
    use j % n
    constructor
    · exact List.mem_range.mpr (Nat.mod_lt j (NeZero.pos n))
    · exact kStepVector_mod_n w j k
  -- Therefore Necklace.kStepVector at i.val equals Necklace.kStepVector at (i.val + 1)
  have heq_vec : Necklace.kStepVector w i.val k = Necklace.kStepVector w (i.val + 1) k :=
    hsing _ _ (hmem i.val) (hmem (i.val + 1))
  -- Extract the L-count equality
  have heq_L : Necklace.kStepVector w i.val k BinaryStep.L = Necklace.kStepVector w (i.val + 1) k BinaryStep.L :=
    congrFun heq_vec BinaryStep.L
  -- Use slice_L_count_shift to relate the L-counts
  have hshift := slice_L_count_shift w i.val k
  simp only at hshift
  -- hshift says: countL(slice at i+1) = countL(slice at i) - delta_out + delta_in
  -- where delta_out = (w[i]=L ? 1 : 0), delta_in = (w[i+k]=L ? 1 : 0)
  -- And we know countL(slice at i) = countL(slice at i+1) from heq_L
  -- After some arithmetic, this gives delta_out = delta_in
  set delta_out := if w (i.val : ZMod n) = BinaryStep.L then (1 : ℤ) else 0 with hdelta_out_def
  set delta_in := if w ((i.val + k) : ZMod n) = BinaryStep.L then (1 : ℤ) else 0 with hdelta_in_def
  have hdelta_eq : delta_out = delta_in := by
    -- From hshift and heq_L, the L-counts are equal
    unfold Necklace.kStepVector ZVector.ofList at heq_L
    omega
  -- Now delta_out = delta_in means w[i] and w[i+k] are both L or both s
  -- Key: (i.val : ZMod n) = i (casting back)
  have hi_cast : (i.val : ZMod n) = i := by simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
  -- Show that ↑i.val + ↑(n/d) = (i.val + k : ZMod n)
  have hsum_cast : (i.val : ZMod n) + ((n / d) : ZMod n) = ((i.val + k) : ZMod n) := by
    simp only [hk_eq, ← Nat.cast_add]
  -- Case split on w[i]
  cases hw_i : w (i.val : ZMod n)
  · -- w[i] = L, so delta_out = 1
    have hdout : delta_out = 1 := by simp only [hdelta_out_def, hw_i, ↓reduceIte]
    -- So delta_in = 1, meaning w[i+k] = L
    have hw_k : w ((i.val + k) : ZMod n) = BinaryStep.L := by
      by_contra h
      have hdin : delta_in = 0 := by simp only [hdelta_in_def, h, ↓reduceIte]
      omega
    -- w[i] = L = w[i+k]
    -- Goal: w i = w (i + ↑(n/d))
    calc w i = w (i.val : ZMod n) := by rw [hi_cast]
         _ = BinaryStep.L := hw_i
         _ = w ((i.val + k) : ZMod n) := hw_k.symm
         _ = w ((i.val : ZMod n) + ((n / d) : ZMod n)) := by rw [← hsum_cast]
         _ = w (i + ((n / d) : ZMod n)) := by rw [hi_cast]
  · -- w[i] = s, so delta_out = 0
    have hdout : delta_out = 0 := by simp only [hdelta_out_def, hw_i]; decide
    -- So delta_in = 0, meaning w[i+k] = s
    have hw_k : w ((i.val + k) : ZMod n) = BinaryStep.s := by
      by_contra h
      cases hw_k' : w ((i.val + k) : ZMod n)
      · have hdin : delta_in = 1 := by simp only [hdelta_in_def, hw_k', ↓reduceIte]
        omega
      · exact h hw_k'
    -- w[i] = s = w[i+k]
    calc w i = w (i.val : ZMod n) := by rw [hi_cast]
         _ = BinaryStep.s := hw_i
         _ = w ((i.val + k) : ZMod n) := hw_k.symm
         _ = w ((i.val : ZMod n) + ((n / d) : ZMod n)) := by rw [← hsum_cast]
         _ = w (i + ((n / d) : ZMod n)) := by rw [hi_cast]

-- NOTE: The Bresenham/Sturmian characterization of MOS scales has been moved to MOSBresenham.lean
-- This file focuses on the Bjorklund/recursive approach to proving MOS properties.

/-!
## Reflection of generators under expansion

This section formalizes the lifting of generators from the chunked word back to the original.

The key insight is: if we have a generator in the reduced (chunked) word, it lifts to a generator
in the original word. The argument involves "scooting" intervals across chunk boundaries.

### Setup
- We have a MOS word w with a generator after chunking
- Assume more L's than s's (the large step is more frequent)
- The imperfect generator is larger than the perfect generator

### Main argument
1. An interval built on chunk boundaries after expansion will be "a generator" on chunk boundaries
2. Take a "perfect" (smaller) interval - the step to its right is an L (same as first step)
3. We can scoot it over for the entirety of the first chunk and keep it perfect
4. At another chunk: if perfect, we repeat; if imperfect, the step to its right is an s,
   which makes it smaller (and thus perfect)
5. Therefore, the interval is a generator after expansion (only imperfect in one position)
-/

/-- A generator interval is "perfect" at position i if w[i : i+k] occurs n - 1 times in its abelianized form.
    WOLOG we assume in some proofs that the perfect generator occurs as the smaller form.
    A k-step is an "imperfect generator" if it occurs only once. -/
def isPerfectAt [NeZero n] (w : BinaryNecklace n) (g : Multiset BinaryStep) (k i : ℕ) : Bool :=
  Necklace.abelianize (Necklace.slice w i (i + k)) = g

def isImperfectAt [NeZero n] (w : BinaryNecklace n) (_g gImperfect : Multiset BinaryStep) (k i : ℕ) : Bool :=
  Necklace.abelianize (Necklace.slice w i (i + k)) = gImperfect

/-- The "perfect" generator vector (occurs at exactly n-1 positions) -/
noncomputable def perfectGenerator [NeZero n] (w : BinaryNecklace n) (k : ℕ) : Option (Multiset BinaryStep) :=
  let vecs := (Necklace.allKStepMultisets w k).toFinset.toList
  match vecs with
  | [v] => some v
  | [v1, v2] =>
    -- The "perfect" one is the more common one (appears at more positions)
    let count1 := (Necklace.allKStepMultisets w k).filter (· = v1) |>.length
    let count2 := (Necklace.allKStepMultisets w k).filter (· = v2) |>.length
    if count1 ≥ count2 then some v1 else some v2
  | _ => none

/-- The "imperfect" generator vector (occurs at exactly one position) -/
noncomputable def imperfectGenerator [NeZero n] (w : BinaryNecklace n) (k : ℕ) : Option (Multiset BinaryStep) :=
  let vecs := (Necklace.allKStepMultisets w k).toFinset.toList
  match vecs with
  | [_] => none  -- Only one type, no imperfect
  | [v1, v2] =>
    let count1 := (Necklace.allKStepMultisets w k).filter (· = v1) |>.length
    let count2 := (Necklace.allKStepMultisets w k).filter (· = v2) |>.length
    if count1 ≥ count2 then some v2 else some v1
  | _ => none

/-- Check if w has more L's than s's -/
def hasMoreLs [NeZero n] (w : BinaryNecklace n) : Prop :=
  Necklace.count w BinaryStep.L > Necklace.count w BinaryStep.s

/-- Check if imperfect generator is larger than perfect generator
    (contains more steps, or equivalently, has one more L) -/
def imperfectIsLarger [NeZero n] (w : BinaryNecklace n) (k : ℕ) : Prop :=
  match perfectGenerator w k, imperfectGenerator w k with
  | some perf, some imperf =>
    Multiset.count BinaryStep.L imperf > Multiset.count BinaryStep.L perf
  | _, _ => False

/-- Key lemma: For a perfect interval, the step immediately to its right equals the first step.
    This is because if w[i:i+k] is perfect and w[i+1:i+k+1] is also perfect, then w[i] = w[i+k].-/
lemma perfect_interval_right_step [NeZero n] (w : BinaryNecklace n)
    (_hw : BinaryNecklace.isMOS w) (_hL : hasMoreLs w)
    (g : Multiset BinaryStep) (k i : ℕ)
    (_hk : 0 < k) (_hkn : k < n)
    (hperf : isPerfectAt w g k i = true)
    (hperf_next : isPerfectAt w g k (i + 1) = true) :
    w (i : ZMod n) = w ((i + k) : ZMod n) := by
  -- Both slices have the same abelianization g
  -- When scooting from [i, i+k) to [i+1, i+k+1), we remove w[i] and add w[i+k]
  -- If the multiset stays the same, then w[i] = w[i+k]
  unfold isPerfectAt at hperf hperf_next
  -- isPerfectAt uses decidable equality, so = true means the equality holds
  rw [decide_eq_true_eq] at hperf hperf_next
  -- hperf : Necklace.abelianize (slice w i (i+k)) = g
  -- hperf_next : Necklace.abelianize (slice w (i+1) (i+1+k)) = g
  -- Therefore both abelianizations are equal
  have heq_abel : Necklace.abelianize (Necklace.slice w i (i + k)) =
                  Necklace.abelianize (Necklace.slice w (i + 1) (i + 1 + k)) := by
    rw [hperf, hperf_next]
  -- The abelianization is Multiset.ofList of the slice
  -- When scooting: slice(i+1, i+1+k) = slice(i, i+k) with w[i] removed and w[i+k] added
  -- So ofList(slice2) = ofList(slice1) - {w[i]} + {w[i+k]}
  -- If equal, then w[i] = w[i+k]
  unfold Necklace.abelianize at heq_abel
  -- heq_abel : ofList(slice1) = ofList(slice2)
  -- Case analysis on w[i] and w[i+k]
  cases hw_i : w (i : ZMod n) <;> cases hw_k : w ((i + k) : ZMod n)
  · -- w[i] = L, w[i+k] = L
    rfl
  · -- w[i] = L, w[i+k] = s - contradiction
    exfalso
    -- Use slice_L_count_shift which relates count in slice2 to count in slice1
    have hshift := slice_L_count_shift w i k
    simp only at hshift
    -- hshift gives: (countL slice2 : ℤ) = countL slice1 - delta_out + delta_in
    -- where countL l = (l.filter (· == BinaryStep.L)).length
    -- With hw_i: w[i] = L, delta_out = 1
    -- With hw_k: w[i+k] = s, delta_in = 0
    simp only [hw_i, hw_k, ↓reduceIte] at hshift
    -- hshift now says: countL(slice2) = countL(slice1) - 1 + 0
    -- From heq_abel (multiset equality), derive count equality
    have hcount_eq : Multiset.count BinaryStep.L (↑(Necklace.slice w i (i + k))) =
                     Multiset.count BinaryStep.L (↑(Necklace.slice w (i + 1) (i + 1 + k))) := by
      rw [heq_abel]
    -- Convert Multiset.count to filter length
    -- Multiset.count a (↑l) = l.count a = (l.filter (· == a)).length
    simp only [Multiset.coe_count, List.count_eq_countP, List.countP_eq_length_filter] at hcount_eq
    -- Let c1, c2 be the filter lengths
    let c1 := (Necklace.slice w i (i + k)).filter (· == BinaryStep.L) |>.length
    let c2 := (Necklace.slice w (i + 1) (i + 1 + k)).filter (· == BinaryStep.L) |>.length
    -- hcount_eq : c1 = c2
    -- hshift : (c2 : ℤ) = c1 - 1 + 0
    -- This gives c2 = c1 - 1, but c1 = c2, so c2 = c2 - 1, contradiction
    have h1 : c1 = c2 := hcount_eq
    -- hshift has form: c2 = c1 - 1 + (if s = L then 1 else 0)
    -- Since s ≠ L, the if-then-else is 0
    have hne : BinaryStep.s ≠ BinaryStep.L := by decide
    simp only [hne, ↓reduceIte, add_zero] at hshift
    omega
  · -- w[i] = s, w[i+k] = L - contradiction
    exfalso
    -- Use slice_L_count_shift which relates count in slice2 to count in slice1
    have hshift := slice_L_count_shift w i k
    simp only at hshift
    -- With hw_i: w[i] = s, delta_out = 0
    -- With hw_k: w[i+k] = L, delta_in = 1
    simp only [hw_i, hw_k, ↓reduceIte] at hshift
    -- hshift now says: countL(slice2) = countL(slice1) - 0 + 1 = countL(slice1) + 1
    -- From heq_abel (multiset equality), derive count equality
    have hcount_eq : Multiset.count BinaryStep.L (↑(Necklace.slice w i (i + k))) =
                     Multiset.count BinaryStep.L (↑(Necklace.slice w (i + 1) (i + 1 + k))) := by
      rw [heq_abel]
    -- Convert Multiset.count to filter length
    simp only [Multiset.coe_count, List.count_eq_countP, List.countP_eq_length_filter] at hcount_eq
    -- Let c1, c2 be the filter lengths
    let c1 := (Necklace.slice w i (i + k)).filter (· == BinaryStep.L) |>.length
    let c2 := (Necklace.slice w (i + 1) (i + 1 + k)).filter (· == BinaryStep.L) |>.length
    -- hcount_eq : c1 = c2
    -- hshift : c2 = c1 + 1
    -- This gives c2 = c2 + 1, contradiction
    have h1 : c1 = c2 := hcount_eq
    -- hshift has form: c2 = c1 - (if s = L then 1 else 0) + 1
    -- Since s ≠ L, the if-then-else is 0
    have hne : BinaryStep.s ≠ BinaryStep.L := by decide
    simp only [hne, ↓reduceIte, sub_zero] at hshift
    omega
  · -- w[i] = s, w[i+k] = s
    rfl

/-- Key lemma: The step after an imperfect interval is s (the smaller step).
    If w[i:i+k] is imperfect and w[i+1:i+k+1] is perfect, then w[i+k] = s.
    The hypothesis hrel states that gImp has exactly one more L than g
    (which holds for the imperfect vs perfect generator when hasMoreLs). -/
lemma imperfect_interval_right_step [NeZero n] (w : BinaryNecklace n)
    (_hw : BinaryNecklace.isMOS w) (_hL : hasMoreLs w)
    (g gImp : Multiset BinaryStep) (k i : ℕ)
    (_hk : 0 < k) (_hkn : k < n)
    (himperf : isImperfectAt w g gImp k i = true)
    (hperf_next : isPerfectAt w g k (i + 1) = true)
    (hrel : Multiset.count BinaryStep.L gImp = Multiset.count BinaryStep.L g + 1) :
    w ((i + k) : ZMod n) = BinaryStep.s := by
  -- Scooting relationship: g = gImp - {w[i]} + {w[i+k]}
  -- Since gImp has one more L than g, and multisets are equal after scooting,
  -- we must have: removed one L (w[i] = L) and added one s (w[i+k] = s)
  unfold isImperfectAt at himperf
  unfold isPerfectAt at hperf_next
  rw [decide_eq_true_eq] at himperf hperf_next
  -- himperf : slice[i, i+k).abelianize = gImp
  -- hperf_next : slice[i+1, i+k+1).abelianize = g
  -- The scooting relationship: slice2 = slice1 - w[i] + w[i+k] (as multisets)
  -- So: g = gImp - {w[i]} + {w[i+k]}
  -- Taking L-counts: count_L(g) = count_L(gImp) - (if w[i]=L then 1 else 0) + (if w[i+k]=L then 1 else 0)
  -- Using hrel: count_L(gImp) = count_L(g) + 1
  -- So: count_L(g) = count_L(g) + 1 - delta_out + delta_in
  -- Thus: delta_out - delta_in = 1
  -- Since delta_out, delta_in ∈ {0, 1}, we need delta_out = 1 and delta_in = 0
  -- This means w[i] = L and w[i+k] = s
  have hshift := slice_L_count_shift w i k
  simp only at hshift
  -- Convert abelianizations to multiset counts
  have hcount_gImp : Multiset.count BinaryStep.L (↑(Necklace.slice w i (i + k))) =
                     Multiset.count BinaryStep.L gImp := by
    unfold Necklace.abelianize at himperf
    rw [himperf]
  have hcount_g : Multiset.count BinaryStep.L (↑(Necklace.slice w (i + 1) (i + 1 + k))) =
                  Multiset.count BinaryStep.L g := by
    unfold Necklace.abelianize at hperf_next
    rw [hperf_next]
  -- Convert to filter lengths
  simp only [Multiset.coe_count, List.count_eq_countP, List.countP_eq_length_filter] at hcount_gImp hcount_g
  -- Let c1 = countL(slice1), c2 = countL(slice2), cg = count_L(g), cgImp = count_L(gImp)
  -- hcount_gImp : c1 = cgImp
  -- hcount_g : c2 = cg
  -- hrel : cgImp = cg + 1
  -- hshift : c2 = c1 - delta_out + delta_in
  -- We need to show w[i+k] = s, i.e., delta_in = 0
  cases hw_k : w ((i + k) : ZMod n)
  case L =>
    -- w[i+k] = L means delta_in = 1
    -- hshift : c2 = c1 - delta_out + 1
    -- Combining: cg = cgImp - delta_out + 1 = (cg + 1) - delta_out + 1 = cg + 2 - delta_out
    -- So delta_out = 2, but delta_out ∈ {0, 1}, contradiction
    exfalso
    simp only [hw_k, ↓reduceIte] at hshift
    -- hshift : c2 = c1 - delta_out + 1
    -- where delta_out = if w[i] = L then 1 else 0
    cases hw_i : w (i : ZMod n)
    case L =>
      simp only [hw_i, ↓reduceIte] at hshift
      -- hshift : c2 = c1 - 1 + 1 = c1
      -- But c2 = cg and c1 = cgImp = cg + 1
      -- So cg = cg + 1, contradiction
      omega
    case s =>
      simp only [hw_i] at hshift
      -- hshift : c2 = c1 + 1
      -- c2 = cg, c1 = cgImp = cg + 1
      -- So cg = (cg + 1) + 1 = cg + 2, contradiction
      omega
  case s =>
    rfl

/-! ## Production Rules for MOS Expansion

The chunking operation can be reversed using production rules. When a MOS with more L's than s's
(signature aL bs where a > b) is chunked by s, the reduced word can be expanded back using:
- L → (large chunk) = ceil(a/b) L's followed by s
- s → (small chunk) = floor(a/b) L's followed by s

Symmetrically, when a MOS with more s's than L's is chunked by L:
- L → L followed by ceil(b/a) s's
- s → L followed by floor(b/a) s's

These production rules are essential for proving that generators lift under expansion.
-/

/-- The size of a "large" chunk: ceil(majority/minority) = floor(majority/minority) + 1 -/
def largeChunkSize (numMajority numMinority : ℕ) : ℕ :=
  (numMajority + numMinority - 1) / numMinority  -- This is ceiling division

/-- The size of a "small" chunk: floor(majority/minority) -/
def smallChunkSize (numMajority numMinority : ℕ) : ℕ :=
  numMajority / numMinority

/-- Number of large chunks in a MOS: numMajority mod numMinority -/
def numLargeChunks (numMajority numMinority : ℕ) : ℕ :=
  numMajority % numMinority

/-- Number of small chunks in a MOS: numMinority - (numMajority mod numMinority) -/
def numSmallChunks (numMajority numMinority : ℕ) : ℕ :=
  numMinority - (numMajority % numMinority)

/-- Expand a single step according to production rules.
    When chunking by minority step x:
    - L (large chunk) → largeChunkSize copies of majority step, then one minority step
    - s (small chunk) → smallChunkSize copies of majority step, then one minority step
    Here `majorityStep` is the step that appears more often (the one we're NOT chunking by). -/
def expandStep (step : BinaryStep) (numMajority numMinority : ℕ) (majorityStep : BinaryStep) :
    List BinaryStep :=
  let size := match step with
    | BinaryStep.L => largeChunkSize numMajority numMinority
    | BinaryStep.s => smallChunkSize numMajority numMinority
  List.replicate size majorityStep ++ [BinaryStep.otherStep majorityStep]

/-- Expand an entire word using production rules -/
def expandWord (w : List BinaryStep) (numMajority numMinority : ℕ) (majorityStep : BinaryStep) :
    List BinaryStep :=
  (w.map (fun step => expandStep step numMajority numMinority majorityStep)).flatten

/-- Key property: large and small chunk sizes differ by exactly 1 (when minority > 0 and doesn't divide majority) -/
lemma largeChunk_eq_smallChunk_add_one (numMajority numMinority : ℕ) (hmin : numMinority > 0)
    (hmod_ne : numMajority % numMinority ≠ 0) :
    largeChunkSize numMajority numMinority = smallChunkSize numMajority numMinority + 1 := by
  unfold largeChunkSize smallChunkSize
  have hr : numMajority % numMinority > 0 := Nat.pos_of_ne_zero hmod_ne
  have hr_lt : numMajority % numMinority < numMinority := Nat.mod_lt _ hmin
  -- Set q = numMajority / numMinority, r = numMajority % numMinority
  set q := numMajority / numMinority
  set r := numMajority % numMinority
  have hdiv : numMajority = q * numMinority + r := by
    have h := Nat.div_add_mod numMajority numMinority
    -- h : numMinority * q + r = numMajority
    rw [Nat.mul_comm] at h
    -- h : q * numMinority + r = numMajority
    exact h.symm
  -- We prove: (numMajority + numMinority - 1) / numMinority = q + 1
  apply Nat.div_eq_of_lt_le
  · -- Need: (q + 1) * numMinority ≤ numMajority + numMinority - 1
    have h1 : (q + 1) * numMinority = q * numMinority + numMinority := by ring
    rw [h1, hdiv]
    omega
  · -- Need: numMajority + numMinority - 1 < (q + 2) * numMinority
    have h2 : (q + 2) * numMinority = q * numMinority + 2 * numMinority := by ring
    rw [h2, hdiv]
    omega

private lemma binary_list_map_sum (l : List BinaryStep) (fL fs : ℕ) :
    (l.map (fun step => match step with | BinaryStep.L => fL | BinaryStep.s => fs)).sum =
    l.count BinaryStep.L * fL + l.count BinaryStep.s * fs := by
  induction l with
  | nil => simp
  | cons head tail ih => cases head <;> simp [ih] <;> ring

/-- The total length after expansion equals the original period -/
lemma expandWord_length (w : List BinaryStep) (numMajority numMinority : ℕ) (majorityStep : BinaryStep)
    (hlen : w.length = numMinority)
    (hnumL : w.count BinaryStep.L = numMajority % numMinority)
    (hnums : w.count BinaryStep.s = numMinority - numMajority % numMinority) :
    (expandWord w numMajority numMinority majorityStep).length = numMajority + numMinority := by
  unfold expandWord
  rw [List.length_flatten, List.map_map]
  have hfun : (List.length ∘ fun step => expandStep step numMajority numMinority majorityStep) =
    (fun step : BinaryStep => match step with
      | .L => largeChunkSize numMajority numMinority + 1
      | .s => smallChunkSize numMajority numMinority + 1) := by
    funext step; cases step <;> simp [expandStep, Function.comp]
  rw [hfun, binary_list_map_sum, hnumL, hnums]
  by_cases hmin : numMinority = 0
  · subst hmin; simp [largeChunkSize, smallChunkSize, Nat.mod_zero, Nat.div_zero]
  · have hmin_pos : 0 < numMinority := Nat.pos_of_ne_zero hmin
    by_cases hmod : numMajority % numMinority = 0
    · rw [hmod]; simp only [zero_mul, Nat.sub_zero, zero_add]
      unfold smallChunkSize
      have hdiv := Nat.div_add_mod numMajority numMinority
      rw [hmod, Nat.add_zero] at hdiv
      rw [Nat.mul_add, Nat.mul_one, hdiv]
    · have hlarge := largeChunk_eq_smallChunk_add_one numMajority numMinority hmin_pos hmod
      rw [hlarge]; unfold smallChunkSize
      set q := numMajority / numMinority
      set r := numMajority % numMinority
      have hdiv : numMinority * q + r = numMajority := Nat.div_add_mod numMajority numMinority
      have hr_lt : r < numMinority := Nat.mod_lt _ hmin_pos
      zify [hr_lt.le] at hdiv ⊢
      nlinarith

/-!
## Size-preserving view of chunked words

The key to proving the chunked word is MOS is tracking size information.

If the original MOS has signature (a, b) with a > b:
- There are b chunks (one per minority step)
- Chunk sizes are smallChunkSize = ⌊a/b⌋ and largeChunkSize = ⌈a/b⌉
- Number of large chunks = a % b
- Number of small chunks = b - (a % b)

A k-step in the reduced (chunked) word spans k consecutive chunks.
The total size of those k chunks is:
  totalSize = k * smallChunkSize + (number of L's in the k-step)

Since the Bresenham formula determines which chunks are large:
  chunk i is large iff ⌊(i+1)*a/b⌋ > ⌊i*a/b⌋

The number of large chunks in positions [i, i+k) is:
  ⌊(i+k)*a/b⌋ - ⌊i*a/b⌋

This is bounded by ⌊k*a/b⌋ ≤ count ≤ ⌈k*a/b⌉, giving at most 2 values.
Therefore k-steps in the reduced word come in at most 2 sizes.
-/

/-- The Bresenham characterization: chunk i is large iff the floor increases.
    This is the discrete version of "distribute a large chunks evenly among b positions". -/
def isLargeChunk (numMajority numMinority : ℕ) (i : ℕ) : Bool :=
  (i + 1) * numMajority / numMinority > i * numMajority / numMinority

/-- Count of large chunks in positions [start, start + k) using the Bresenham formula -/
def countLargeChunksInRange (numMajority numMinority : ℕ) (start k : ℕ) : ℕ :=
  (start + k) * numMajority / numMinority - start * numMajority / numMinority

/-- Key lemma: The count of large chunks in any k consecutive positions is bounded
    by floor and ceiling of k * numMajority / numMinority.

    Proof sketch:
    - Lower bound: ⌊(start+k)*a/b⌋ - ⌊start*a/b⌋ ≥ ⌊k*a/b⌋
      This follows from the subadditivity of floor: ⌊x+y⌋ ≥ ⌊x⌋ + ⌊y⌋
    - Upper bound: ⌊(start+k)*a/b⌋ - ⌊start*a/b⌋ ≤ ⌈k*a/b⌉
      This follows from: ⌊x+y⌋ ≤ ⌊x⌋ + ⌈y⌉ -/
lemma countLargeChunks_bounded (numMajority numMinority : ℕ) (hmin : numMinority > 0)
    (start k : ℕ) :
    k * numMajority / numMinority ≤ countLargeChunksInRange numMajority numMinority start k ∧
    countLargeChunksInRange numMajority numMinority start k ≤
      (k * numMajority + numMinority - 1) / numMinority := by
  unfold countLargeChunksInRange
  constructor
  · -- Lower bound using subadditivity of floor division
    have hsub : (start + k) * numMajority = start * numMajority + k * numMajority := by ring
    rw [hsub]
    have h := Nat.add_div_le_add_div (start * numMajority) (k * numMajority) numMinority
    omega
  · -- Upper bound: ⌊(s+k)a/b⌋ - ⌊sa/b⌋ ≤ ⌈ka/b⌉
    -- Key: ⌊p+q⌋/b = p/b + (p%b + q)/b, and (p%b + q)/b ≤ (q + b-1)/b since p%b ≤ b-1
    have hsub : (start + k) * numMajority = start * numMajority + k * numMajority := by ring
    rw [hsub]
    set p := start * numMajority
    set q := k * numMajority
    have h1 : (p + q) / numMinority = p / numMinority + (p % numMinority + q) / numMinority := by
      conv_lhs =>
        rw [show p + q = (p % numMinority + q) + (p / numMinority) * numMinority from by
          have := Nat.div_add_mod p numMinority
          have := mul_comm numMinority (p / numMinority)
          omega]
      rw [Nat.add_mul_div_right _ _ hmin]
      omega
    have h2 : (p % numMinority + q) / numMinority ≤ (q + numMinority - 1) / numMinority :=
      Nat.div_le_div_right (by have := Nat.mod_lt p hmin; omega)
    have h3 : (p + q) / numMinority ≤ p / numMinority + (q + numMinority - 1) / numMinority := by
      rw [h1]; exact Nat.add_le_add_left h2 _
    clear h1 h2
    have hge : p / numMinority ≤ (p + q) / numMinority :=
      Nat.div_le_div_right (Nat.le_add_right p q)
    omega

/-- Corollary: The count of large chunks in k consecutive positions comes in at most 2 values.
    Since all counts lie in [⌊ka/b⌋, ⌈ka/b⌉], and this interval has at most 2 integers,
    any two counts differ by at most 1. -/
lemma countLargeChunks_at_most_two_values (numMajority numMinority : ℕ) (hmin : numMinority > 0)
    (k : ℕ) :
    ∀ start1 start2 : ℕ,
      let c1 := countLargeChunksInRange numMajority numMinority start1 k
      let c2 := countLargeChunksInRange numMajority numMinority start2 k
      c1 = c2 ∨ c1 + 1 = c2 ∨ c2 + 1 = c1 := by
  intro start1 start2
  have hb1 := countLargeChunks_bounded numMajority numMinority hmin start1 k
  have hb2 := countLargeChunks_bounded numMajority numMinority hmin start2 k
  -- ceil ≤ floor + 1
  have hceil_le : (k * numMajority + numMinority - 1) / numMinority ≤
      k * numMajority / numMinority + 1 :=
    le_trans (Nat.div_le_div_right (by omega)) (le_of_eq (Nat.add_div_right _ hmin))
  omega

/-- The sum of k consecutive chunk sizes equals k * smallSize + countLarge -/
lemma kChunkSum_eq (numMajority numMinority : ℕ) (start k : ℕ) :
    let small := smallChunkSize numMajority numMinority
    let countL := countLargeChunksInRange numMajority numMinority start k
    -- Sum of k chunks = k * small + countL (since large = small + 1)
    k * small + countL = (start + k) * numMajority / numMinority - start * numMajority / numMinority +
                         k * (numMajority / numMinority) := by
  unfold smallChunkSize countLargeChunksInRange
  ring

/-- Key theorem: k consecutive chunk sizes come in at most 2 total sums.
    This proves that the chunked word satisfies the MOS property for k-steps. -/
theorem kConsecutiveChunkSums_at_most_two (numMajority numMinority : ℕ) (hmin : numMinority > 0)
    (k : ℕ) :
    ∀ start1 start2 : ℕ,
      let sum1 := k * smallChunkSize numMajority numMinority +
                  countLargeChunksInRange numMajority numMinority start1 k
      let sum2 := k * smallChunkSize numMajority numMinority +
                  countLargeChunksInRange numMajority numMinority start2 k
      sum1 = sum2 ∨ sum1 + 1 = sum2 ∨ sum2 + 1 = sum1 := by
  intro start1 start2
  have h := countLargeChunks_at_most_two_values numMajority numMinority hmin k start1 start2
  -- Since sum = k * small + countL, and countL values differ by at most 1, sums differ by at most 1
  omega

/-- A primitive MOS with minority count > 1 has exactly 2 distinct chunk sizes.
    If all sizes were equal, countOther | countX, giving gcd > 1, hence a repetition,
    contradicting primitivity. -/
private lemma prim_mos_has_two_chunk_sizes (n : ℕ) [NeZero n] (w : BinaryNecklace n)
    (hw : BinaryNecklace.isMOS w) (hprim : Necklace.isPrimitive w)
    (x : BinaryStep) (sizes : List ℕ)
    (hsizes : chunkSizesList x w = some sizes)
    (hcountX : Necklace.count w x > 1)
    (hcountOther : Necklace.count w (BinaryStep.otherStep x) > 1) :
    sizes.toFinset.card = 2 := by
  have hat_most_two := mos_chunk_sizes_at_most_two n w hw x sizes hsizes
  have hlen_eq : sizes.length = Necklace.count w (BinaryStep.otherStep x) := by
    rw [chunkSizesList_length x w sizes hsizes, numChunks_eq_count]
  have hnonempty : sizes ≠ [] := by
    intro h; simp [h] at hlen_eq; omega
  have hcard_pos : 0 < sizes.toFinset.card := by
    rw [Finset.card_pos]; cases sizes with
    | nil => exact absurd rfl hnonempty
    | cons s _ => exact ⟨s, by simp⟩
  by_contra hne2
  have hcard_one : sizes.toFinset.card = 1 := by omega
  -- All sizes equal some value c
  rw [Finset.card_eq_one] at hcard_one
  obtain ⟨c, hc⟩ := hcard_one
  have hall_eq : ∀ s ∈ sizes, s = c := fun s hs =>
    Finset.mem_singleton.mp (hc ▸ List.mem_toFinset.mpr hs)
  -- sizes.sum = c * sizes.length
  have hsum_eq : sizes.sum = c * sizes.length := by
    suffices ∀ (l : List ℕ), (∀ s ∈ l, s = c) → l.sum = c * l.length from
      this sizes hall_eq
    intro l hl
    induction l with
    | nil => simp
    | cons head tail ih =>
      simp only [List.sum_cons, List.length_cons]
      rw [hl head List.mem_cons_self, ih (fun s hs => hl s (List.mem_cons_of_mem head hs))]
      ring
  -- n = sizes.sum + sizes.length
  have hword_len := word_length_eq_sum_chunks x w sizes hsizes
  -- count x + count (otherStep x) = n
  have hcount_sum : Necklace.count w x + Necklace.count w (BinaryStep.otherStep x) = n := by
    unfold Necklace.count
    have h1 : (Finset.filter (fun i => w i = x) Finset.univ) ∪
        (Finset.filter (fun i => w i = BinaryStep.otherStep x) Finset.univ) = Finset.univ := by
      ext i; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      cases w i <;> cases x <;> simp [BinaryStep.otherStep]
    have h2 : Disjoint (Finset.filter (fun i => w i = x) Finset.univ)
        (Finset.filter (fun i => w i = BinaryStep.otherStep x) Finset.univ) := by
      rw [Finset.disjoint_filter]; intro i _ h; cases x <;> simp_all [BinaryStep.otherStep]
    rw [← Finset.card_union_of_disjoint h2, h1, Finset.card_univ, ZMod.card n]
  -- countOther | countX (since countX = c * countOther)
  have hcountX_eq_sum : Necklace.count w x = sizes.sum := by omega
  have hdvd : Necklace.count w (BinaryStep.otherStep x) ∣ Necklace.count w x := by
    rw [hcountX_eq_sum, hsum_eq, hlen_eq]
    exact dvd_mul_left _ _
  -- gcd(countL, countS) > 1
  set countL := Necklace.count w BinaryStep.L
  set countS := Necklace.count w BinaryStep.s
  have hsig : BinaryNecklace.hasStepSignature w countL countS := by
    unfold BinaryNecklace.hasStepSignature BinaryNecklace.stepSignature; rfl
  have hcountL_pos : 0 < countL := by
    have hdef : countL = Necklace.count w BinaryStep.L := rfl
    cases x with
    | L => omega
    | s => simp [BinaryStep.otherStep] at hcountOther; omega
  have hdvd_gcd : Necklace.count w (BinaryStep.otherStep x) ∣ Nat.gcd countL countS := by
    cases x with
    | L => exact Nat.dvd_gcd hdvd (dvd_refl countS)
    | s => exact Nat.dvd_gcd (dvd_refl countL) hdvd
  have hgcd_pos : 0 < Nat.gcd countL countS :=
    Nat.gcd_pos_of_pos_left countS hcountL_pos
  have hgcd_gt : Nat.gcd countL countS > 1 :=
    lt_of_lt_of_le hcountOther (Nat.le_of_dvd hgcd_pos hdvd_gcd)
  -- isRepetition from MOS + gcd > 1
  have hrep := mos_repetition_of_gcd_bjorklund w hw countL countS hsig (Nat.gcd countL countS) rfl hgcd_gt
  obtain ⟨hdvd_n, _, hper⟩ := hrep
  -- period ≤ n / gcd < n, contradicting isPrimitive
  have hperiod_le := Necklace.period_length_le_of_translational_period w
    (n / Nat.gcd countL countS)
    (Nat.div_pos (Nat.le_of_dvd (NeZero.pos n) hdvd_n) (by omega))
    (Nat.div_lt_self (NeZero.pos n) hgcd_gt)
    (Nat.div_dvd_of_dvd hdvd_n)
    hper
  rw [hprim] at hperiod_le
  exact absurd (Nat.div_lt_self (NeZero.pos n) hgcd_gt) (by omega)

/-- A position is on a chunk boundary if it's at the start of a chunk. -/
def isChunkBoundary (chunkSizes : List ℕ) (pos : ℕ) : Bool :=
  let boundaries := chunkSizes.scanl (· + · + 1) 0  -- positions after each non-x letter
  pos ∈ boundaries

/-- The cumulative positions of chunk boundaries.
    If chunkSizes = [s₀, s₁, s₂, ...], boundaries are at positions
    0, s₀+1, s₀+1+s₁+1, ... (each chunk has size sᵢ majority steps + 1 minority step) -/
def chunkBoundaries (chunkSizes : List ℕ) : List ℕ :=
  chunkSizes.scanl (fun acc size => acc + size + 1) 0

/-- Get the chunk boundary position for chunk index i -/
def chunkBoundaryAt (chunkSizes : List ℕ) (i : ℕ) : ℕ :=
  (chunkBoundaries chunkSizes).getD i 0

/-- The total length of all chunks equals n (the period of w) -/
private lemma list_map_succ_sum (l : List ℕ) : (l.map (· + 1)).sum = l.sum + l.length := by
  induction l with
  | nil => simp
  | cons head tail ih => simp [ih]; omega

lemma chunkSizes_total_eq_n [NeZero n] (x : BinaryStep) (w : BinaryNecklace n)
    (chunkSizes : List ℕ) (hsizes : chunkSizesList x w = some chunkSizes) :
    (chunkSizes.map (· + 1)).sum = n := by
  have h := word_length_eq_sum_chunks x w chunkSizes hsizes
  rw [list_map_succ_sum]; omega

/-- Chunk boundary i is at position sum of first i chunk sizes (including the +1 for each s) -/
lemma chunkBoundaryAt_eq_sum (chunkSizes : List ℕ) (i : ℕ) (hi : i ≤ chunkSizes.length) :
    chunkBoundaryAt chunkSizes i = ((chunkSizes.take i).map (· + 1)).sum := by
  unfold chunkBoundaryAt chunkBoundaries
  suffices h : ∀ (l : List ℕ) (b : ℕ) (j : ℕ), j ≤ l.length →
      (l.scanl (fun acc size => acc + size + 1) b).getD j 0 =
        b + ((l.take j).map (· + 1)).sum by
    rw [h _ 0 _ hi]; omega
  intro l
  induction l with
  | nil => intro b j hj; simp at hj; subst hj; simp [List.scanl]
  | cons head tail ih =>
    intro b j hj
    cases j with
    | zero => simp [List.scanl]
    | succ k =>
      have hk : k ≤ tail.length := by simp at hj; omega
      rw [List.scanl_cons]
      show (tail.scanl (fun acc size => acc + size + 1) (b + head + 1)).getD k 0 =
        b + (((head :: tail).take (k + 1)).map (· + 1)).sum
      rw [ih (b + head + 1) k hk, List.take_succ_cons, List.map_cons, List.sum_cons]
      omega

private lemma chunkBoundaryAt_succ (chunkSizes : List ℕ) (k : ℕ) (hk : k < chunkSizes.length) :
    chunkBoundaryAt chunkSizes (k + 1) = chunkBoundaryAt chunkSizes k + chunkSizes[k] + 1 := by
  rw [chunkBoundaryAt_eq_sum _ _ (by omega : k + 1 ≤ chunkSizes.length),
      chunkBoundaryAt_eq_sum _ _ (by omega : k ≤ chunkSizes.length)]
  rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
      List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
  omega

/-- The structure of a word relative to its chunk decomposition.
    There exists an offset r such that:
    - At every chunk boundary position (r + chunkBoundaryAt i), the word has otherStep x
    - Within each chunk, positions (r + chunkBoundaryAt i + 1 + m) have value x -/
lemma chunk_word_structure [NeZero n] (x : BinaryStep) (w : BinaryNecklace n)
    (chunkSizes : List ℕ) (hsizes : chunkSizesList x w = some chunkSizes) :
    ∃ r : ℕ, r < n ∧
      (∀ i : ℕ, i ≤ chunkSizes.length →
        w ((r + chunkBoundaryAt chunkSizes i : ℕ) : ZMod n) = BinaryStep.otherStep x) ∧
      (∀ i : ℕ, (hi : i < chunkSizes.length) → ∀ m : ℕ, m < chunkSizes[i]'hi →
        w ((r + chunkBoundaryAt chunkSizes i + 1 + m : ℕ) : ZMod n) = x) := by
  -- Unfold chunkSizesList to extract structure
  unfold chunkSizesList at hsizes
  simp only [Id.run] at hsizes
  set is := indices (BinaryStep.otherStep x) w with his_def
  cases his : is.head? with
  | none => simp [his] at hsizes
  | some firstNonX =>
    simp only [his, pure] at hsizes
    injection hsizes with hsizes'
    set indexVals := List.map ZMod.val is with hindexVals_def
    set cappedIndexList := indexVals ++ [ZMod.val firstNonX + n] with hcapped_def
    -- Lengths
    have hlen : chunkSizes.length = is.length := by
      rw [← hsizes']; simp [List.length_map, List.length_range]
    have hcap_len : cappedIndexList.length = is.length + 1 := by
      simp [hcapped_def, hindexVals_def]
    have hindexVals_len : indexVals.length = is.length := by simp [hindexVals_def]
    -- cappedIndexList is strictly increasing
    have hpw : cappedIndexList.Pairwise (· < ·) := by
      rw [hcapped_def, List.pairwise_append]
      refine ⟨indices_vals_pairwise (BinaryStep.otherStep x) w,
              List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb; subst hb
      obtain ⟨z, _, rfl⟩ := List.mem_map.mp ha
      have := ZMod.val_lt z; omega
    have hmono : ∀ i, i < is.length → cappedIndexList[i]! < cappedIndexList[i + 1]! := by
      intro i hi
      have h1 : i < cappedIndexList.length := by omega
      have h2 : i + 1 < cappedIndexList.length := by omega
      simp only [getElem!_pos cappedIndexList i h1,
                  getElem!_pos cappedIndexList (i + 1) h2]
      exact (List.pairwise_iff_getElem.mp hpw) i (i + 1) (by omega) (by omega) (by omega)
    have hsorted_le : ∀ a b, a ≤ b → b < cappedIndexList.length →
        cappedIndexList[a]! ≤ cappedIndexList[b]! := by
      intro a b hab hb
      rcases Nat.eq_or_lt_of_le hab with rfl | hlt
      · exact le_refl _
      · rw [getElem!_pos cappedIndexList a (by omega), getElem!_pos cappedIndexList b hb]
        exact le_of_lt ((List.pairwise_iff_getElem.mp hpw) a b (by omega) hb hlt)
    -- firstNonX is in is
    have his_cons : ∃ tail, is = firstNonX :: tail := List.head?_eq_some_iff.mp his
    obtain ⟨tail, htail⟩ := his_cons
    -- Key boundary values of cappedIndexList
    have hfirst : cappedIndexList[0]! = ZMod.val firstNonX := by
      simp [hcapped_def, hindexVals_def, htail]
    have hlast : cappedIndexList[is.length]! = ZMod.val firstNonX + n := by
      rw [List.getElem!_eq_getElem?_getD, hcapped_def, hindexVals_def, htail]
      simp [List.length_map]
    -- Gap equation: cappedIndexList[j+1]! = cappedIndexList[j]! + chunkSizes[j]! + 1
    have hgap : ∀ j : ℕ, j < is.length →
        cappedIndexList[j + 1]! = cappedIndexList[j]! + chunkSizes[j]! + 1 := by
      intro j hj
      suffices chunkSizes[j]! = cappedIndexList[j + 1]! - cappedIndexList[j]! - 1 by
        have := hmono j hj; omega
      -- Rewrite chunkSizes to map expression at getElem! level (no dependent type issue)
      rw [← hsizes', getElem!_pos _ j (by simp; omega)]
      simp [List.getElem_map, List.getElem_range]
    -- TELESCOPING: r + chunkBoundaryAt i = cappedIndexList[i]!
    have htelescoping : ∀ i : ℕ, i ≤ is.length →
        ZMod.val firstNonX + chunkBoundaryAt chunkSizes i = cappedIndexList[i]! := by
      intro i
      induction i with
      | zero =>
        intro _
        simp [chunkBoundaryAt, chunkBoundaries, hfirst]
      | succ k ih =>
        intro hk
        have hk_lt : k < is.length := by omega
        rw [chunkBoundaryAt_succ _ _ (by omega : k < chunkSizes.length)]
        -- Goal has chunkSizes[k] (auto-bound), hgap has chunkSizes[k]! — bridge them
        have := ih (by omega : k ≤ is.length)
        have := hgap k hk_lt
        have : chunkSizes[k]! = chunkSizes[k] := getElem!_pos chunkSizes k (by omega)
        omega
    -- cappedIndexList[j]! = is[j].val for j < is.length
    have hcap_eq_is : ∀ j : ℕ, (hj : j < is.length) →
        cappedIndexList[j]! = (is[j]'hj).val := by
      intro j hj
      have hj_lt_iv : j < indexVals.length := by omega
      rw [getElem!_pos cappedIndexList j (by omega : j < cappedIndexList.length)]
      have : (indexVals ++ [ZMod.val firstNonX + n])[j] = indexVals[j] :=
        List.getElem_append_left hj_lt_iv
      rw [this]; simp [hindexVals_def, List.getElem_map]
    -- Choose r = firstNonX.val
    refine ⟨ZMod.val firstNonX, ZMod.val_lt firstNonX, ?_, ?_⟩
    -- BOUNDARY PART
    · intro i hi
      rw [show (ZMod.val firstNonX + chunkBoundaryAt chunkSizes i : ℕ) =
          (cappedIndexList[i]! : ℕ) from by have := htelescoping i (by omega); omega]
      rcases Nat.eq_or_lt_of_le (show i ≤ is.length from by omega) with heq | hlt
      · -- i = is.length: cappedIndexList[i]! = firstNonX.val + n
        rw [heq, hlast]
        have : ((ZMod.val firstNonX + n : ℕ) : ZMod n) = firstNonX := by
          push_cast [Nat.cast_add]; simp
        rw [this]
        have hmem_is : firstNonX ∈ is := by rw [htail]; exact List.mem_cons_self
        exact (indices_mem_iff (BinaryStep.otherStep x) w _).mp hmem_is
      · -- i < is.length: cappedIndexList[i]! = is[i].val
        rw [hcap_eq_is i hlt, ZMod.natCast_zmod_val]
        exact (indices_mem_iff (BinaryStep.otherStep x) w _).mp (List.getElem_mem ..)
    -- INTERIOR PART
    · intro i hi m hm
      -- Position = r + chunkBoundaryAt i + 1 + m = cappedIndexList[i]! + 1 + m
      -- This is strictly between cappedIndexList[i]! and cappedIndexList[i+1]!
      set q := ZMod.val firstNonX + chunkBoundaryAt chunkSizes i + 1 + m
      have hq_eq : q = cappedIndexList[i]! + 1 + m := by
        have := htelescoping i (by omega : i ≤ is.length); omega
      have hi_lt_is : i < is.length := by omega
      have hq_lower : cappedIndexList[i]! < q := by omega
      have hq_upper : q < cappedIndexList[i + 1]! := by
        rw [hq_eq]
        have := hgap i hi_lt_is
        have : chunkSizes[i]! = chunkSizes[i] := getElem!_pos chunkSizes i hi
        omega
      -- q cast to ZMod n is not in indices (otherStep x) w
      apply not_in_indices_means_eq
      intro hmem
      -- hmem : ((q : ℕ) : ZMod n) ∈ is, so q % n ∈ indexVals
      have hq_val : ZMod.val ((q : ℕ) : ZMod n) = q % n := ZMod.val_natCast n q
      have hqmod_mem : q % n ∈ indexVals :=
        List.mem_map.mpr ⟨((q : ℕ) : ZMod n), hmem, hq_val⟩
      by_cases hq_lt_n : q < n
      · -- Case q < n: q % n = q, so q ∈ indexVals directly
        rw [Nat.mod_eq_of_lt hq_lt_n] at hqmod_mem
        obtain ⟨j', hj'_lt_iv, hj'_eq⟩ := List.getElem_of_mem hqmod_mem
        have hcj'_eq : cappedIndexList[j']! = q := by
          rw [getElem!_pos cappedIndexList j' (by omega : j' < cappedIndexList.length)]
          exact (List.getElem_append_left hj'_lt_iv).trans hj'_eq
        -- j' can't be ≤ i (cappedIndexList[j']! ≤ cappedIndexList[i]! < q)
        -- j' can't be ≥ i+1 (q < cappedIndexList[i+1]! ≤ cappedIndexList[j']!)
        rcases Nat.lt_or_ge j' (i + 1) with h | h
        · have := hsorted_le j' i (by omega) (by omega : i < cappedIndexList.length)
          omega
        · have := hsorted_le (i + 1) j' h (by omega : j' < cappedIndexList.length)
          omega
      · -- Case q ≥ n: q % n = q - n
        push_neg at hq_lt_n
        have hfirst_eq : indexVals[0]! = ZMod.val firstNonX := by
          simp [hindexVals_def, htail]
        -- q < firstNonX.val + n (since q < cappedIndexList[i+1]! ≤ cappedIndexList[is.length]!)
        have hq_upper' : q < ZMod.val firstNonX + n := by
          rcases Nat.eq_or_lt_of_le (show i + 1 ≤ is.length from hi_lt_is) with heq | hlt'
          · rw [heq] at hq_upper; rwa [hlast] at hq_upper
          · have := hsorted_le (i + 1) is.length (by omega) (by omega)
            rw [hlast] at this; omega
        -- q % n = q - n (since n ≤ q < 2n)
        have hq_mod : q % n = q - n := by
          have : ZMod.val firstNonX < n := ZMod.val_lt firstNonX
          have hqn_lt : q - n < n := by omega
          conv_lhs => rw [show q = q - n + n from by omega]
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt hqn_lt]
        rw [hq_mod] at hqmod_mem
        -- q - n < firstNonX.val = indexVals[0]!, contradicts sorted indexVals
        have hq_sub : q - n < ZMod.val firstNonX := by omega
        obtain ⟨j', hj'_lt_iv, hj'_eq⟩ := List.getElem_of_mem hqmod_mem
        have hiv_sorted : indexVals.Pairwise (· < ·) :=
          indices_vals_pairwise (BinaryStep.otherStep x) w
        have hiv0_le : indexVals[0]! ≤ indexVals[j']! := by
          rcases j' with _ | j''
          · exact le_refl _
          · rw [getElem!_pos indexVals 0 (by omega),
                 getElem!_pos indexVals (j'' + 1) (by omega)]
            exact le_of_lt ((List.pairwise_iff_getElem.mp hiv_sorted)
              0 (j'' + 1) (by omega) (by omega) (by omega))
        rw [hfirst_eq, getElem!_pos indexVals j' hj'_lt_iv, hj'_eq] at hiv0_le
        omega

private lemma binary_count_L_plus_count_s (l : List BinaryStep) :
    l.count BinaryStep.L + l.count BinaryStep.s = l.length := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    cases head <;> simp_all [] <;> omega

/-- For binary step lists of the same length, equal L-count implies equal multisets. -/
private lemma binary_multiset_eq_of_L_count_eq (l₁ l₂ : List BinaryStep)
    (hlen : l₁.length = l₂.length)
    (hL : l₁.count BinaryStep.L = l₂.count BinaryStep.L) :
    (↑l₁ : Multiset BinaryStep) = ↑l₂ := by
  rw [Multiset.coe_eq_coe, List.perm_iff_count]
  intro a
  cases a with
  | L => exact hL
  | s =>
    have h₁ := binary_count_L_plus_count_s l₁
    have h₂ := binary_count_L_plus_count_s l₂
    omega

/-- Theorem: All MOS necklaces are balanced.
    (Conceptually immediate from mos_kStepVector_L_count_diff_le_one)
-/
theorem allMOSScalesAreBalanced : ∀ n : ℕ, [NeZero n] → (∀ w : BinaryNecklace n, (BinaryNecklace.isMOS w) → (Necklace.isBalanced w)) := by
  intro n _inst w hw
  -- Unfold isBalanced: for all k, w1, w2 in allKStepSubwords, count diff ≤ 1
  unfold Necklace.isBalanced
  intro k hk_pos hk_lt w1 w2 a hw1 hw2
  -- Extract indices for w1 and w2
  rw [Necklace.allKStepSubwords, List.mem_ofFn] at hw1 hw2
  obtain ⟨i, hw1_eq⟩ := hw1
  obtain ⟨j, hw2_eq⟩ := hw2
  -- w1 = slice w i.val (i.val + k), w2 = slice w j.val (j.val + k)
  subst hw1_eq hw2_eq
  -- Get membership in distinctKStepVectors
  have hv1_mem : Necklace.kStepVector w i.val k ∈ distinctKStepVectors w k := by
    unfold distinctKStepVectors Necklace.allKStepVectors
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩
  have hv2_mem : Necklace.kStepVector w j.val k ∈ distinctKStepVectors w k := by
    unfold distinctKStepVectors Necklace.allKStepVectors
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨j.val, List.mem_range.mpr j.isLt, rfl⟩
  -- L-count difference ≤ 1 for MOS
  have hdiff := mos_kStepVector_L_count_diff_le_one w hw k hk_pos hk_lt
                  (Necklace.kStepVector w i.val k) (Necklace.kStepVector w j.val k) hv1_mem hv2_mem
  -- Unfold Necklace.kStepVector to relate to slice count
  -- Necklace.kStepVector w i k = ZVector.ofList (slice w i (i+k))
  -- ZVector.ofList l a = (l.filter (· == a)).length
  unfold Necklace.kStepVector ZVector.ofList at hdiff
  -- Both slices have same length k
  have hlen1 : (Necklace.slice w i.val (i.val + k)).length = k := by
    rw [Necklace.slice_length]; omega
  have hlen2 : (Necklace.slice w j.val (j.val + k)).length = k := by
    rw [Necklace.slice_length]; omega
  cases a with
  | L =>
    -- Direct from hdiff: filter lengths differ by at most 1
    simp only [List.count_eq_countP, List.countP_eq_length_filter]
    -- hdiff gives bounds on the integer difference, convert to natAbs
    have h1 := hdiff.1  -- slice_i_L - 1 ≤ slice_j_L
    have h2 := hdiff.2  -- slice_j_L ≤ slice_i_L + 1
    omega
  | s =>
    -- s-count = length - L-count, lengths are equal, so s-count diff equals L-count diff
    have hfilt1 := binary_list_filter_sum (Necklace.slice w i.val (i.val + k))
    have hfilt2 := binary_list_filter_sum (Necklace.slice w j.val (j.val + k))
    simp only [List.count_eq_countP, List.countP_eq_length_filter]
    have h1 := hdiff.1
    have h2 := hdiff.2
    omega

/-- Splitting a slice at an intermediate point -/
private lemma slice_split [NeZero n] (w : Necklace α n) (i a b : ℕ) :
    Necklace.slice w i (i + a + b) = Necklace.slice w i (i + a) ++ Necklace.slice w (i + a) (i + a + b) := by
  induction b with
  | zero =>
    simp only [Nat.add_zero]
    suffices Necklace.slice w (i + a) (i + a) = [] by rw [this, List.append_nil]
    unfold Necklace.slice; simp []
  | succ b ih =>
    have hLHS : Necklace.slice w i (i + a + (b + 1)) =
        Necklace.slice w i (i + a + b) ++ [w ((i + a + b : ℕ) : ZMod n)] := by
      have := slice_extend_end w i (a + b)
      rw [show i + (a + b) + 1 = i + a + (b + 1) from by omega,
          show i + (a + b) = i + a + b from by omega] at this
      simp only [← Nat.cast_add, ← Nat.add_assoc] at this
      exact this
    have hRHS : Necklace.slice w (i + a) (i + a + (b + 1)) =
        Necklace.slice w (i + a) (i + a + b) ++ [w ((i + a + b : ℕ) : ZMod n)] := by
      have := slice_extend_end w (i + a) b
      rw [show (i + a) + b + 1 = i + a + (b + 1) from by omega] at this
      simp only [← Nat.cast_add] at this
      exact this
    rw [hLHS, ih, hRHS, List.append_assoc]

/-- ZVector.ofList distributes over append -/
private lemma ofList_append [DecidableEq α] (l1 l2 : List α) (a : α) :
    ZVector.ofList (l1 ++ l2) a = ZVector.ofList l1 a + ZVector.ofList l2 a := by
  unfold ZVector.ofList
  rw [List.filter_append, List.length_append, Nat.cast_add]

/-- kStepVector splits when the step count is a sum -/
private lemma kStepVector_split [NeZero n] [DecidableEq α] (w : Necklace α n) (i a b : ℕ) (step : α) :
    Necklace.kStepVector w i (a + b) step =
    Necklace.kStepVector w i a step + Necklace.kStepVector w (i + a) b step := by
  unfold Necklace.kStepVector
  have h : i + (a + b) = i + a + b := by omega
  conv_lhs => rw [show i + (a + b) = i + a + b from h]
  rw [slice_split]
  exact ofList_append _ _ _

/-- Chunk boundary positions are monotone -/
private lemma chunkBoundaryAt_mono (chunkSizes : List ℕ) (a b : ℕ)
    (hab : a ≤ b) (hb : b ≤ chunkSizes.length) :
    chunkBoundaryAt chunkSizes a ≤ chunkBoundaryAt chunkSizes b := by
  induction b with
  | zero => simp at hab; subst hab; exact le_refl _
  | succ b' ih =>
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact le_refl _
    · calc chunkBoundaryAt chunkSizes a
          ≤ chunkBoundaryAt chunkSizes b' := ih (by omega) (by omega)
        _ ≤ chunkBoundaryAt chunkSizes (b' + 1) := by
            rw [chunkBoundaryAt_succ _ _ (by omega)]; omega

/-- When all elements of a slice have the same value v,
    the kStepVector has v-count = k and other-count = 0 -/
private lemma kStepVector_constant_value [NeZero n] (w : BinaryNecklace n) (i k : ℕ) (v : BinaryStep)
    (h : ∀ m : ℕ, m < k → w ((i + m : ℕ) : ZMod n) = v) :
    Necklace.kStepVector w i k = fun step => if step = v then (k : ℤ) else 0 := by
  induction k generalizing i with
  | zero =>
    funext step
    unfold Necklace.kStepVector Necklace.slice ZVector.ofList
    simp [List.range_zero]
  | succ k ih =>
    funext step
    rw [show k + 1 = k + 1 from rfl, kStepVector_split w i k 1 step]
    -- First k elements: all v
    have h' : ∀ m : ℕ, m < k → w ((i + m : ℕ) : ZMod n) = v := fun m hm => h m (by omega)
    rw [congr_fun (ih i h') step]
    -- Last element: w(i+k) = v
    have hk : w ((i + k : ℕ) : ZMod n) = v := h k (by omega)
    unfold Necklace.kStepVector Necklace.slice ZVector.ofList
    simp only [show i + k + 1 - (i + k) = 1 from by omega,
               List.range_one, bind_pure_comp, Functor.map, List.map_singleton,
               Nat.cast_zero, add_zero, hk,
               List.filter_cons, List.filter_nil]
    cases step <;> cases v <;> simp

/-- A single chunk from its start (one past the boundary before it) through its boundary
    contributes exactly 1 to the otherStep x count in the kStepVector.
    The window has length sizes[j] + 1: sizes[j] x-positions followed by 1 boundary. -/
private lemma kStepVector_single_chunk_otherStep [NeZero n]
    (x : BinaryStep) (w : BinaryNecklace n)
    (sizes : List ℕ)
    (r : ℕ)
    (hr_boundary : ∀ i : ℕ, i ≤ sizes.length →
      w ((r + chunkBoundaryAt sizes i : ℕ) : ZMod n) = BinaryStep.otherStep x)
    (hr_x : ∀ i : ℕ, (hi : i < sizes.length) → ∀ m : ℕ, m < sizes[i]'hi →
      w ((r + chunkBoundaryAt sizes i + 1 + m : ℕ) : ZMod n) = x)
    (j : ℕ) (hj : j < sizes.length) :
    Necklace.kStepVector w (r + chunkBoundaryAt sizes j + 1)
      (sizes[j]'hj + 1) (BinaryStep.otherStep x) = 1 := by
  rw [show sizes[j]'hj + 1 = sizes[j]'hj + 1 from rfl, kStepVector_split]
  -- First part: sizes[j] x-positions, otherStep x count = 0
  have h_x_part : Necklace.kStepVector w (r + chunkBoundaryAt sizes j + 1)
      (sizes[j]'hj) (BinaryStep.otherStep x) = 0 := by
    have := congr_fun (kStepVector_constant_value w _ _ x
        (fun m hm => hr_x j hj m hm)) (BinaryStep.otherStep x)
    rw [this]; cases x <;> simp [BinaryStep.otherStep]
  -- Rewrite starting position of second part
  have h_start : r + chunkBoundaryAt sizes j + 1 + sizes[j]'hj =
      r + chunkBoundaryAt sizes (j + 1) := by
    rw [chunkBoundaryAt_succ sizes j hj]; omega
  -- Second part: 1 boundary position
  have h_boundary_part : Necklace.kStepVector w
      (r + chunkBoundaryAt sizes (j + 1)) 1 (BinaryStep.otherStep x) = 1 := by
    have := congr_fun (kStepVector_constant_value w _ 1 (BinaryStep.otherStep x)
        (fun m hm => by
          have : m = 0 := by omega
          subst this; simp only [Nat.add_zero]
          exact hr_boundary (j + 1) (by omega)))
        (BinaryStep.otherStep x)
    rw [this, if_pos rfl]; push_cast
  rw [h_x_part, h_start, h_boundary_part]; simp

/-- From boundary(i) covering k full chunks through boundary(i+k), the otherStep x count
    in the kStepVector equals k + 1 (one per chunk boundary including the starting boundary).
    Requires i + k ≤ sizes.length (non-wrapping). -/
private lemma kStepVector_otherStep_at_boundary [NeZero n]
    (x : BinaryStep) (w : BinaryNecklace n)
    (sizes : List ℕ)
    (r : ℕ)
    (hr_boundary : ∀ i : ℕ, i ≤ sizes.length →
      w ((r + chunkBoundaryAt sizes i : ℕ) : ZMod n) = BinaryStep.otherStep x)
    (hr_x : ∀ i : ℕ, (hi : i < sizes.length) → ∀ m : ℕ, m < sizes[i]'hi →
      w ((r + chunkBoundaryAt sizes i + 1 + m : ℕ) : ZMod n) = x)
    (i k : ℕ) (hik : i + k ≤ sizes.length) :
    Necklace.kStepVector w (r + chunkBoundaryAt sizes i)
      (chunkBoundaryAt sizes (i + k) - chunkBoundaryAt sizes i + 1)
      (BinaryStep.otherStep x) = ↑(k + 1) := by
  induction k with
  | zero =>
    simp only [Nat.add_zero, Nat.sub_self, Nat.zero_add]
    have := congr_fun (kStepVector_constant_value w (r + chunkBoundaryAt sizes i) 1
        (BinaryStep.otherStep x) (fun m hm => by
          have : m = 0 := by omega
          subst this; simp only [Nat.add_zero]
          exact hr_boundary i (by omega)))
        (BinaryStep.otherStep x)
    rw [this, if_pos rfl]
  | succ k ih =>
    have hik' : i + k ≤ sizes.length := by omega
    have hik_lt : i + k < sizes.length := by omega
    have hsucc : chunkBoundaryAt sizes (i + k + 1) =
        chunkBoundaryAt sizes (i + k) + sizes[i + k]'hik_lt + 1 :=
      chunkBoundaryAt_succ sizes (i + k) hik_lt
    have hK_split : chunkBoundaryAt sizes (i + (k + 1)) - chunkBoundaryAt sizes i + 1 =
        (chunkBoundaryAt sizes (i + k) - chunkBoundaryAt sizes i + 1) +
        (sizes[i + k]'hik_lt + 1) := by
      rw [show i + (k + 1) = i + k + 1 from by ring, hsucc]
      have := chunkBoundaryAt_mono sizes i (i + k) (by omega) hik'; omega
    rw [hK_split, kStepVector_split]
    have h_start : r + chunkBoundaryAt sizes i +
        (chunkBoundaryAt sizes (i + k) - chunkBoundaryAt sizes i + 1) =
        r + chunkBoundaryAt sizes (i + k) + 1 := by
      have := chunkBoundaryAt_mono sizes i (i + k) (by omega) hik'; omega
    rw [h_start, ih hik',
        kStepVector_single_chunk_otherStep x w sizes r hr_boundary hr_x (i + k) hik_lt]
    push_cast; ring

/-- From chunkStart(i) (= boundary(i) + 1) covering k full chunks through boundary(i+k),
    the otherStep x count in the kStepVector equals k.
    Window length = chunkBoundaryAt(i+k) - chunkBoundaryAt(i).
    Requires i + k ≤ sizes.length (non-wrapping). -/
private lemma kStepVector_otherStep_from_chunkStart [NeZero n]
    (x : BinaryStep) (w : BinaryNecklace n)
    (sizes : List ℕ)
    (r : ℕ)
    (hr_boundary : ∀ i : ℕ, i ≤ sizes.length →
      w ((r + chunkBoundaryAt sizes i : ℕ) : ZMod n) = BinaryStep.otherStep x)
    (hr_x : ∀ i : ℕ, (hi : i < sizes.length) → ∀ m : ℕ, m < sizes[i]'hi →
      w ((r + chunkBoundaryAt sizes i + 1 + m : ℕ) : ZMod n) = x)
    (i k : ℕ) (hik : i + k ≤ sizes.length) :
    Necklace.kStepVector w (r + chunkBoundaryAt sizes i + 1)
      (chunkBoundaryAt sizes (i + k) - chunkBoundaryAt sizes i)
      (BinaryStep.otherStep x) = ↑k := by
  induction k with
  | zero =>
    simp only [Nat.add_zero, Nat.sub_self]
    unfold Necklace.kStepVector Necklace.slice ZVector.ofList
    simp
  | succ k ih =>
    have hik' : i + k ≤ sizes.length := by omega
    have hik_lt : i + k < sizes.length := by omega
    have hsucc : chunkBoundaryAt sizes (i + k + 1) =
        chunkBoundaryAt sizes (i + k) + sizes[i + k]'hik_lt + 1 :=
      chunkBoundaryAt_succ sizes (i + k) hik_lt
    have hK_split : chunkBoundaryAt sizes (i + (k + 1)) - chunkBoundaryAt sizes i =
        (chunkBoundaryAt sizes (i + k) - chunkBoundaryAt sizes i) +
        (sizes[i + k]'hik_lt + 1) := by
      rw [show i + (k + 1) = i + k + 1 from by ring, hsucc]
      have := chunkBoundaryAt_mono sizes i (i + k) (by omega) hik'; omega
    rw [hK_split, kStepVector_split]
    have h_start : r + chunkBoundaryAt sizes i + 1 +
        (chunkBoundaryAt sizes (i + k) - chunkBoundaryAt sizes i) =
        r + chunkBoundaryAt sizes (i + k) + 1 := by
      have := chunkBoundaryAt_mono sizes i (i + k) (by omega) hik'; omega
    rw [h_start, ih hik',
        kStepVector_single_chunk_otherStep x w sizes r hr_boundary hr_x (i + k) hik_lt]
    push_cast; ring

/-- The last chunk boundary equals n (the total word length). -/
lemma chunkBoundaryAt_total [NeZero n] (x : BinaryStep) (w : BinaryNecklace n)
    (chunkSizes : List ℕ) (hsizes : chunkSizesList x w = some chunkSizes) :
    chunkBoundaryAt chunkSizes chunkSizes.length = n := by
  rw [chunkBoundaryAt_eq_sum _ _ (le_refl _), List.take_length]
  exact chunkSizes_total_eq_n x w chunkSizes hsizes

/-- chunks.length = chunkSizes.length when both come from the same word -/
private lemma chunks_length_eq_sizes [NeZero n] (x : BinaryStep) (w : BinaryNecklace n)
    (sizes : List ℕ) (hsizes : chunkSizesList x w = some sizes)
    (chunks : List BinaryStep) (hchunks : chunkSizesToBinary x w = some chunks) :
    chunks.length = sizes.length := by
  unfold chunkSizesToBinary at hchunks
  simp only [hsizes] at hchunks
  change (match sizes.toFinset.toList with
    | [_] => some (sizes.map (fun _ => BinaryStep.L))
    | [a, b] => if a + 1 = b || b + 1 = a then
        some (sizes.map (fun s => if s = min a b then BinaryStep.s else BinaryStep.L))
      else none
    | _ => none) = some chunks at hchunks
  split at hchunks
  · rw [← Option.some.inj hchunks, List.length_map]
  · split at hchunks
    · rw [← Option.some.inj hchunks, List.length_map]
    · cases hchunks
  · cases hchunks

/-- The production rule transformation: how a generator vector transforms under expansion.

    If gChunked = (numL_in_g, nums_in_g) in the chunked word, then the lifted generator is:
    gLifted = (numL_in_g × largeChunkSize + nums_in_g × smallChunkSize, numL_in_g + nums_in_g)

    This is because:
    - Each L in chunked → largeChunkSize majority steps + 1 minority step
    - Each s in chunked → smallChunkSize majority steps + 1 minority step -/
def liftGeneratorVector (gChunked : ZVector BinaryStep) (numMajority numMinority : ℕ) :
    ZVector BinaryStep :=
  let numL := gChunked BinaryStep.L
  let nums := gChunked BinaryStep.s
  let large := largeChunkSize numMajority numMinority
  let small := smallChunkSize numMajority numMinority
  fun step => match step with
    | BinaryStep.L => numL * large + nums * small  -- L's in lifted = weighted sum
    | BinaryStep.s => numL + nums                   -- s's in lifted = total chunks spanned

/-- liftGeneratorVector is additive: lift(v1 + v2) = lift(v1) + lift(v2) -/
lemma liftGeneratorVector_add (v1 v2 : ZVector BinaryStep) (numMaj numMin : ℕ) :
    liftGeneratorVector (fun a => v1 a + v2 a) numMaj numMin =
    fun a => liftGeneratorVector v1 numMaj numMin a + liftGeneratorVector v2 numMaj numMin a := by
  funext a
  unfold liftGeneratorVector largeChunkSize smallChunkSize
  cases a <;> ring

/-- liftGeneratorVector respects scalar multiplication: lift(c·v) = c·lift(v) -/
lemma liftGeneratorVector_smul (c : ℤ) (v : ZVector BinaryStep) (numMaj numMin : ℕ) :
    liftGeneratorVector (fun a => c * v a) numMaj numMin =
    fun a => c * liftGeneratorVector v numMaj numMin a := by
  funext a
  unfold liftGeneratorVector largeChunkSize smallChunkSize
  cases a <;> ring

/-- Generalized lift that works for any majority step x.
    When x = BinaryStep.L, this equals liftGeneratorVector. When x = BinaryStep.s, the roles
    of the L and s components are swapped:
    - x component gets the weighted sum (majority step count in expanded word)
    - otherStep(x) component gets the total count (boundary step count) -/
def liftGeneratorVectorX (x : BinaryStep) (gChunked : ZVector BinaryStep) (numMaj numMin : ℕ) :
    ZVector BinaryStep :=
  let numL := gChunked BinaryStep.L
  let nums := gChunked BinaryStep.s
  let large := largeChunkSize numMaj numMin
  let small := smallChunkSize numMaj numMin
  fun step => if step = x then numL * large + nums * small
              else numL + nums

lemma liftGeneratorVectorX_L_eq (gChunked : ZVector BinaryStep) (numMaj numMin : ℕ) :
    liftGeneratorVectorX BinaryStep.L gChunked numMaj numMin =
    liftGeneratorVector gChunked numMaj numMin := by
  funext step
  unfold liftGeneratorVectorX liftGeneratorVector
  cases step <;> simp

lemma liftGeneratorVectorX_add (x : BinaryStep) (v1 v2 : ZVector BinaryStep) (numMaj numMin : ℕ) :
    liftGeneratorVectorX x (fun a => v1 a + v2 a) numMaj numMin =
    fun a => liftGeneratorVectorX x v1 numMaj numMin a + liftGeneratorVectorX x v2 numMaj numMin a := by
  funext a
  unfold liftGeneratorVectorX largeChunkSize smallChunkSize
  split_ifs <;> ring

lemma liftGeneratorVectorX_smul (x : BinaryStep) (c : ℤ) (v : ZVector BinaryStep) (numMaj numMin : ℕ) :
    liftGeneratorVectorX x (fun a => c * v a) numMaj numMin =
    fun a => c * liftGeneratorVectorX x v numMaj numMin a := by
  funext a
  unfold liftGeneratorVectorX largeChunkSize smallChunkSize
  split_ifs <;> ring

/-- liftGeneratorVectorX maps the zero vector to zero -/
lemma liftGeneratorVectorX_zero (x : BinaryStep) (numMaj numMin : ℕ) :
    liftGeneratorVectorX x (fun _ => (0 : ℤ)) numMaj numMin = fun _ => 0 := by
  funext a
  unfold liftGeneratorVectorX largeChunkSize smallChunkSize
  split_ifs <;> ring

/-- The sum of L and s components of liftGeneratorVectorX equals
    g(L) × (large + 1) + g(s) × (small + 1), regardless of x.
    This is because the x-component is g(L)×large + g(s)×small and the
    other component is g(L) + g(s), and swapping x doesn't change the sum. -/
private lemma liftGeneratorVectorX_total_sum (x : BinaryStep) (g : ZVector BinaryStep)
    (numMaj numMin : ℕ) :
    liftGeneratorVectorX x g numMaj numMin BinaryStep.L +
    liftGeneratorVectorX x g numMaj numMin BinaryStep.s =
    g BinaryStep.L * (↑(largeChunkSize numMaj numMin) + 1) +
    g BinaryStep.s * (↑(smallChunkSize numMaj numMin) + 1) := by
  unfold liftGeneratorVectorX
  cases x <;> simp <;> ring

/-- Sum decomposition for a list with exactly two distinct nat values -/
private lemma nat_two_val_list_sum {l : List ℕ} {a b : ℕ} (hab : a ≠ b)
    (hmem : ∀ x ∈ l, x = a ∨ x = b) :
    l.sum = l.count a * a + l.count b * b := by
  induction l with
  | nil => simp
  | cons h t ih =>
    have ht := fun x hx => hmem x (List.mem_cons_of_mem h hx)
    rcases hmem h List.mem_cons_self with rfl | rfl
    · simp only [List.sum_cons, List.count_cons_self, List.count_cons_of_ne hab, ih ht]; ring
    · simp only [List.sum_cons, List.count_cons_self, List.count_cons_of_ne (Ne.symm hab), ih ht]
      ring

/-- Count identity for a list with exactly two distinct nat values -/
private lemma nat_two_val_count_sum {l : List ℕ} {a b : ℕ} (hab : a ≠ b)
    (hmem : ∀ x ∈ l, x = a ∨ x = b) :
    l.count a + l.count b = l.length := by
  induction l with
  | nil => simp
  | cons h t ih =>
    have ht := fun x hx => hmem x (List.mem_cons_of_mem h hx)
    rcases hmem h List.mem_cons_self with rfl | rfl
    · simp only [List.count_cons_self, List.count_cons_of_ne hab, List.length_cons]
      have := ih ht; omega
    · simp only [List.count_cons_self, List.count_cons_of_ne (Ne.symm hab), List.length_cons]
      have := ih ht; omega

/-- Key correspondence: chunks[i] and sizes[i] are related through the production rules.
    If chunks[i] = L (large chunk), then sizes[i] = largeChunkSize numMaj numMin.
    If chunks[i] = s (small chunk), then sizes[i] = smallChunkSize numMaj numMin. -/
private lemma chunk_binary_size_match [NeZero n] (x : BinaryStep) (w : BinaryNecklace n)
    (sizes : List ℕ) (hsizes : chunkSizesList x w = some sizes)
    (chunks : List BinaryStep) (hchunks : chunkSizesToBinary x w = some chunks)
    (i : ℕ) (hi : i < sizes.length) :
    let numMaj := Necklace.count w x
    let numMin := Necklace.count w (BinaryStep.otherStep x)
    let hic : i < chunks.length := by rw [chunks_length_eq_sizes x w sizes hsizes chunks hchunks]; exact hi
    sizes[i] = match chunks[i]'hic with
      | BinaryStep.L => largeChunkSize numMaj numMin
      | BinaryStep.s => smallChunkSize numMaj numMin := by
  intro numMaj numMin hic
  -- Derive key facts
  have hlen_eq : sizes.length = numMin := by
    rw [chunkSizesList_length x w sizes hsizes, numChunks_eq_count]
  have hNumMin_pos : 0 < numMin := by
    have hne := chunkSizesList_nonempty x w sizes hsizes
    cases sizes with | nil => exact absurd rfl hne | cons _ _ => simp at hlen_eq; omega
  have hsizes_sum : sizes.sum = numMaj := by
    have h1 := word_length_eq_sum_chunks x w sizes hsizes
    have h2 : numMaj + numMin = n := by
      show Necklace.count w x + Necklace.count w (BinaryStep.otherStep x) = n
      unfold Necklace.count
      have huniv : (Finset.filter (fun i => w i = x) Finset.univ) ∪
          (Finset.filter (fun i => w i = BinaryStep.otherStep x) Finset.univ) = Finset.univ := by
        ext i; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        cases w i <;> cases x <;> simp [BinaryStep.otherStep]
      have hdisj : Disjoint (Finset.filter (fun i => w i = x) Finset.univ)
          (Finset.filter (fun i => w i = BinaryStep.otherStep x) Finset.univ) := by
        rw [Finset.disjoint_filter]; intro i _ h; cases x <;> simp_all [BinaryStep.otherStep]
      rw [← Finset.card_union_of_disjoint hdisj, huniv, Finset.card_univ, ZMod.card n]
    omega
  -- Unfold chunkSizesToBinary and case split
  unfold chunkSizesToBinary at hchunks
  simp only [hsizes] at hchunks
  change (match sizes.toFinset.toList with
    | [_] => some (sizes.map (fun _ => BinaryStep.L))
    | [a, b] => if a + 1 = b || b + 1 = a then
        some (sizes.map (fun s => if s = min a b then BinaryStep.s else BinaryStep.L))
      else none
    | _ => none) = some chunks at hchunks
  split at hchunks
  · -- Case 1: sizes.toFinset.toList = [v], all chunks = L, all sizes = v
    rename_i v htoList
    have hchunks_eq := Option.some.inj hchunks
    have hmem_v : ∀ s ∈ sizes, s = v := by
      intro s hs
      have h1 : s ∈ sizes.toFinset.toList := Finset.mem_toList.mpr (List.mem_toFinset.mpr hs)
      rw [htoList] at h1; simp at h1; exact h1
    have hci : chunks[i]'hic = BinaryStep.L := by
      have h1 : chunks[i]? = some BinaryStep.L := by
        have h2 : (sizes.map (fun _ => BinaryStep.L))[i]? = some BinaryStep.L := by
          rw [List.getElem?_map, List.getElem?_eq_getElem hi]; rfl
        rwa [hchunks_eq] at h2
      have h3 := List.getElem?_eq_getElem (α := BinaryStep) hic
      rw [h3] at h1; exact Option.some.inj h1
    simp only [hci]
    rw [hmem_v _ (List.getElem_mem hi)]
    -- Show v = largeChunkSize: since all sizes = v, v * numMin = numMaj
    have hv_mul : v * numMin = numMaj := by
      rw [← hsizes_sum, ← hlen_eq]
      have : ∀ l : List ℕ, (∀ s ∈ l, s = v) → v * l.length = l.sum := by
        intro l hl
        induction l with
        | nil => simp
        | cons h t ih =>
          rw [List.sum_cons, List.length_cons,
            ← ih (fun s hs => hl s (List.mem_cons_of_mem _ hs)),
            hl h List.mem_cons_self]
          ring
      exact this sizes hmem_v
    unfold largeChunkSize; symm
    apply Nat.div_eq_of_lt_le
    · rw [hv_mul]; omega
    · rw [show (v + 1) * numMin = numMaj + numMin from by rw [← hv_mul]; ring]; omega
  · -- Case 2: sizes.toFinset.toList = [a, b]
    rename_i a b htoList
    split at hchunks
    · -- Consecutive condition holds
      rename_i hcond
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hcond
      have hchunks_eq := Option.some.inj hchunks
      have hab : a ≠ b := by
        intro heq
        have hnodup := Finset.nodup_toList sizes.toFinset
        rw [htoList] at hnodup
        simp [List.nodup_cons] at hnodup
        exact hnodup heq
      have hmem_ab : ∀ s ∈ sizes, s = a ∨ s = b := by
        intro s hs
        have h1 : s ∈ sizes.toFinset.toList := Finset.mem_toList.mpr (List.mem_toFinset.mpr hs)
        rw [htoList] at h1; simp at h1; exact h1
      have ha_mem : a ∈ sizes :=
        List.mem_toFinset.mp (Finset.mem_toList.mp (htoList ▸ List.Mem.head _))
      have hb_mem : b ∈ sizes :=
        List.mem_toFinset.mp (Finset.mem_toList.mp (htoList ▸ List.Mem.tail _ (List.Mem.head _)))
      set s := min a b with hs_def
      have hmax_eq : max a b = s + 1 := by rcases hcond with h | h <;> omega
      -- Every size is s or s+1
      have hmem_sl : ∀ v ∈ sizes, v = s ∨ v = s + 1 := by
        intro v hv
        have h := hmem_ab v hv
        rcases h with ha | hb
        · -- ha : v = a
          rw [ha]
          have h1 : s ≤ a := hs_def ▸ Nat.min_le_left a b
          have h2 : a ≤ s + 1 := hmax_eq ▸ le_max_left a b
          rcases eq_or_lt_of_le h1 with heq | hlt
          · left; exact heq.symm
          · right; omega
        · -- hb : v = b
          rw [hb]
          have h1 : s ≤ b := hs_def ▸ Nat.min_le_right a b
          have h2 : b ≤ s + 1 := hmax_eq ▸ le_max_right a b
          rcases eq_or_lt_of_le h1 with heq | hlt
          · left; exact heq.symm
          · right; omega
      have hsl_ne : s ≠ s + 1 := by omega
      have hs_mem : s ∈ sizes := by
        rcases le_total a b with h | h
        · rw [show s = a from min_eq_left h]; exact ha_mem
        · rw [show s = b from min_eq_right h]; exact hb_mem
      have hs1_mem : (s + 1) ∈ sizes := by
        rw [← hmax_eq]; rcases le_total a b with h | h
        · rw [max_eq_right h]; exact hb_mem
        · rw [max_eq_left h]; exact ha_mem
      -- Key arithmetic: numMaj = numMin * s + count(s+1)
      have hsum_decomp : numMaj = numMin * s + sizes.count (s + 1) := by
        have h1 := nat_two_val_list_sum hsl_ne hmem_sl
        have h2 := nat_two_val_count_sum hsl_ne hmem_sl
        have h3 : sizes.count s * s + sizes.count (s + 1) * (s + 1) =
                  (sizes.count s + sizes.count (s + 1)) * s + sizes.count (s + 1) := by ring
        rw [← hsizes_sum, h1, h3, h2, ← hlen_eq]
      have hcount_s1_pos : 0 < sizes.count (s + 1) :=
        List.count_pos_iff.mpr hs1_mem
      have hcount_s1_lt : sizes.count (s + 1) < numMin := by
        have := nat_two_val_count_sum hsl_ne hmem_sl
        have := List.count_pos_iff.mpr hs_mem; omega
      -- smallChunkSize = s
      have hsmall : smallChunkSize numMaj numMin = s := by
        unfold smallChunkSize; apply Nat.div_eq_of_lt_le
        · -- s * numMin ≤ numMaj
          rw [hsum_decomp, mul_comm]; omega
        · -- numMaj < (s + 1) * numMin
          have h1 : numMaj = numMin * s + sizes.count (s + 1) := hsum_decomp
          have h2 : sizes.count (s + 1) < numMin := hcount_s1_lt
          nlinarith
      -- largeChunkSize = s + 1
      have hlarge : largeChunkSize numMaj numMin = s + 1 := by
        have hmod_ne : numMaj % numMin ≠ 0 := by
          intro hmod
          have h1 := Nat.div_add_mod numMaj numMin
          have h2 : numMaj / numMin = s := by
            have h := hsmall; unfold smallChunkSize at h; exact h
          rw [h2, hmod, Nat.add_zero] at h1
          rw [mul_comm] at h1
          linarith [hsum_decomp, hcount_s1_pos]
        rw [largeChunk_eq_smallChunk_add_one numMaj numMin hNumMin_pos hmod_ne, hsmall]
      -- Case split on sizes[i]
      by_cases hsi : sizes[i] = s
      · -- sizes[i] = min a b, so chunks[i] = s
        have hci : chunks[i]'hic = BinaryStep.s := by
          have h1 : chunks[i]? = some BinaryStep.s := by
            have h2 : (sizes.map (fun s_val => if s_val = min a b then BinaryStep.s else BinaryStep.L))[i]? =
                some BinaryStep.s := by
              rw [List.getElem?_map, List.getElem?_eq_getElem hi]; simp [hsi, hs_def]
            rwa [hchunks_eq] at h2
          have h3 := List.getElem?_eq_getElem (α := BinaryStep) hic
          rw [h3] at h1; exact Option.some.inj h1
        simp only [hci]; rw [hsi, ← hsmall]
      · -- sizes[i] ≠ min a b, so sizes[i] = s + 1 and chunks[i] = L
        have hsi_eq : sizes[i] = s + 1 := by
          rcases hmem_sl _ (List.getElem_mem hi) with h | h
          · exact absurd h hsi
          · exact h
        have hci : chunks[i]'hic = BinaryStep.L := by
          have h1 : chunks[i]? = some BinaryStep.L := by
            have h2 : (sizes.map (fun s_val => if s_val = min a b then BinaryStep.s else BinaryStep.L))[i]? =
                some BinaryStep.L := by
              rw [List.getElem?_map, List.getElem?_eq_getElem hi]; simp [← hs_def, hsi]
            rwa [hchunks_eq] at h2
          have h3 := List.getElem?_eq_getElem (α := BinaryStep) hic
          rw [h3] at h1; exact Option.some.inj h1
        simp only [hci]; rw [hsi_eq, ← hlarge]
    · -- Consecutive condition fails: contradiction
      cases hchunks
  · -- Other patterns: contradiction
    cases hchunks

/-- The kStepVector for a single chunk: from boundary(j) to boundary(j+1).
    This slice has 1 copy of otherStep(x) and sizes[j] copies of x. -/
private lemma single_chunk_kStepVector [NeZero n] (x : BinaryStep) (w : BinaryNecklace n)
    (chunkSizes : List ℕ) (chunks : List BinaryStep)
    (hchunks : chunkSizesToBinary x w = some chunks)
    (hsizes : chunkSizesList x w = some chunkSizes)
    (hlen : chunks.length ≠ 0)
    (r : ℕ)
    (hboundary : ∀ i : ℕ, i ≤ chunkSizes.length →
      w ((r + chunkBoundaryAt chunkSizes i : ℕ) : ZMod n) = BinaryStep.otherStep x)
    (hchunk_vals : ∀ i : ℕ, (hi : i < chunkSizes.length) → ∀ m : ℕ, m < chunkSizes[i]'hi →
      w ((r + chunkBoundaryAt chunkSizes i + 1 + m : ℕ) : ZMod n) = x)
    (j : ℕ) (hj : j < chunkSizes.length) :
    haveI : NeZero chunks.length := ⟨hlen⟩
    let numMaj := Necklace.count w x
    let numMin := Necklace.count w (BinaryStep.otherStep x)
    Necklace.kStepVector w (r + chunkBoundaryAt chunkSizes j) (chunkSizes[j] + 1) =
      liftGeneratorVectorX x
        (ZVector.ofList [(Necklace.toNecklace chunks) (j : ZMod chunks.length)])
        numMaj numMin := by
  haveI : NeZero chunks.length := ⟨hlen⟩
  intro numMaj numMin
  have hlen_eq := chunks_length_eq_sizes x w chunkSizes hsizes chunks hchunks
  have hic : j < chunks.length := hlen_eq ▸ hj
  -- Relate (toNecklace chunks)(j) to chunks[j]
  have hchunks_j : (Necklace.toNecklace chunks) (j : ZMod chunks.length) = chunks[j]'hic := by
    simp only [Necklace.toNecklace]
    rw [getElem!_pos chunks ((j : ZMod chunks.length).val)
        (by rwa [ZMod.val_natCast_of_lt (by omega)])]
    congr 1
    exact ZMod.val_natCast_of_lt (by omega)
  -- Apply chunk_binary_size_match
  have hsm := chunk_binary_size_match x w chunkSizes hsizes chunks hchunks j hj
  -- Decompose kStepVector: sizes[j]+1 = 1 + sizes[j]
  funext step
  rw [show chunkSizes[j]'hj + 1 = 1 + chunkSizes[j]'hj from by omega,
      kStepVector_split w (r + chunkBoundaryAt chunkSizes j) 1 (chunkSizes[j]'hj) step]
  -- First summand: 1 element at boundary = otherStep x
  rw [congr_fun (kStepVector_constant_value w (r + chunkBoundaryAt chunkSizes j) 1
    (BinaryStep.otherStep x) (fun m hm => by
      simp only [show m = 0 from by omega, Nat.add_zero]
      exact hboundary j (le_of_lt hj))) step]
  -- Second summand: sizes[j] elements, all x
  rw [congr_fun (kStepVector_constant_value w (r + chunkBoundaryAt chunkSizes j + 1)
    (chunkSizes[j]'hj) x (hchunk_vals j hj)) step]
  -- Now LHS: (if step = otherStep x then 1 else 0) + (if step = x then sizes[j] else 0)
  -- RHS: liftGeneratorVectorX x (ZVector.ofList [chunks[j]]) numMaj numMin step
  rw [hchunks_j]
  unfold liftGeneratorVectorX ZVector.ofList
  -- Don't unfold largeChunkSize/smallChunkSize to avoid let-binding mismatches with division
  rcases hcj : chunks[j]'hic with _ | _ <;>
    (simp only [hcj, List.filter_cons, List.filter_nil, BinaryStep.otherStep] at *;
     cases step <;> cases x <;> simp_all <;> rfl)

/-- The k-step vector at chunk boundary i equals the lifted version of the chunked k-step vector.
    This is the key lemma connecting the chunked and expanded word structures.

    Given rotation r from chunk_word_structure, the slice of w from r + boundary(startChunk)
    to r + boundary(startChunk + k) spans exactly k chunks. Its letter counts are:
    - x-count = (# L chunks) * large + (# s chunks) * small
    - otherStep(x)-count = k
    This matches liftGeneratorVectorX applied to the chunked k-step vector. -/
lemma kStepVector_boundary_eq_lift [NeZero n] (x : BinaryStep) (w : BinaryNecklace n)
    (chunks : List BinaryStep) (chunkSizes : List ℕ)
    (hchunks : chunkSizesToBinary x w = some chunks)
    (hsizes : chunkSizesList x w = some chunkSizes)
    (hlen : chunks.length ≠ 0)
    (r : ℕ)
    (hboundary : ∀ i : ℕ, i ≤ chunkSizes.length →
      w ((r + chunkBoundaryAt chunkSizes i : ℕ) : ZMod n) = BinaryStep.otherStep x)
    (hchunk_vals : ∀ i : ℕ, (hi : i < chunkSizes.length) → ∀ m : ℕ, m < chunkSizes[i]'hi →
      w ((r + chunkBoundaryAt chunkSizes i + 1 + m : ℕ) : ZMod n) = x)
    (startChunk k : ℕ) (hk : startChunk + k ≤ chunkSizes.length) :
    haveI : NeZero chunks.length := ⟨hlen⟩
    let startPos := chunkBoundaryAt chunkSizes startChunk
    let endPos := chunkBoundaryAt chunkSizes (startChunk + k)
    let numMaj := Necklace.count w x
    let numMin := Necklace.count w (BinaryStep.otherStep x)
    Necklace.kStepVector w (r + startPos) (endPos - startPos) =
      liftGeneratorVectorX x (Necklace.kStepVector (Necklace.toNecklace chunks) startChunk k) numMaj numMin := by
  haveI : NeZero chunks.length := ⟨hlen⟩
  have hchunks_sizes_len := chunks_length_eq_sizes x w chunkSizes hsizes chunks hchunks
  -- Proof by induction on k
  induction k with
  | zero =>
    -- Base case: k=0, both sides are zero (empty slice)
    simp only [Nat.add_zero, Nat.sub_self]
    funext step
    unfold Necklace.kStepVector Necklace.slice
    simp only [Nat.add_zero, Nat.sub_self, List.range_zero, List.map_map]
    show ZVector.ofList [] step = liftGeneratorVectorX x (ZVector.ofList []) _ _ step
    unfold ZVector.ofList
    simp only [List.filter_nil, List.length_nil, Nat.cast_zero]
    unfold liftGeneratorVectorX largeChunkSize smallChunkSize
    split_ifs <;> ring
  | succ k' ih =>
    -- Inductive step: split the slice at boundary(startChunk + k')
    have hk' : startChunk + k' ≤ chunkSizes.length := by omega
    have hsk' : startChunk + k' < chunkSizes.length := by omega
    specialize ih hk'
    rw [show startChunk + (k' + 1) = startChunk + k' + 1 from by omega] at hk ⊢

    -- Decompose the boundary lengths
    have hbdry_succ := chunkBoundaryAt_succ chunkSizes (startChunk + k') hsk'
    have hb_mono := chunkBoundaryAt_mono chunkSizes startChunk (startChunk + k') (by omega) (by omega)
    have hlen_eq : chunkBoundaryAt chunkSizes (startChunk + k' + 1) - chunkBoundaryAt chunkSizes startChunk =
      (chunkBoundaryAt chunkSizes (startChunk + k') - chunkBoundaryAt chunkSizes startChunk) +
      (chunkSizes[startChunk + k'] + 1) := by rw [hbdry_succ]; omega

    -- Split the expanded word's k-step vector
    funext step
    rw [hlen_eq, kStepVector_split]
    have h_pos : r + chunkBoundaryAt chunkSizes startChunk +
      (chunkBoundaryAt chunkSizes (startChunk + k') - chunkBoundaryAt chunkSizes startChunk) =
      r + chunkBoundaryAt chunkSizes (startChunk + k') := by omega
    rw [h_pos]

    -- Apply IH to the first summand
    rw [congr_fun ih step]

    -- Apply single_chunk_kStepVector to the second summand
    rw [congr_fun (single_chunk_kStepVector x w chunkSizes chunks hchunks hsizes hlen r
      hboundary hchunk_vals (startChunk + k') hsk') step]

    -- Now LHS = liftVX(kStepVector_chunks(s,k')) + liftVX(ofList[chunks(s+k')])
    -- RHS = liftVX(kStepVector_chunks(s, k'+1))
    -- Split the RHS using kStepVector decomposition and linearity
    have h_chunked_split : Necklace.kStepVector (Necklace.toNecklace chunks) startChunk (k' + 1) =
      fun a => Necklace.kStepVector (Necklace.toNecklace chunks) startChunk k' a +
               Necklace.kStepVector (Necklace.toNecklace chunks) (startChunk + k') 1 a := by
      funext a; exact kStepVector_split _ _ _ _ a
    conv_rhs => rw [h_chunked_split]
    rw [liftGeneratorVectorX_add]

    -- Cancel the first summand; reduce to kStepVector(chunks, s+k', 1) = ofList[chunks(s+k')]
    congr 1

    -- kStepVector of length 1 is a singleton list
    congr 1
    unfold Necklace.kStepVector Necklace.slice
    simp only [show startChunk + k' + 1 - (startChunk + k') = 1 from by omega,
      List.range_one, List.map_singleton, List.map_singleton,
      bind_pure_comp, Functor.map, Nat.cast_zero, add_zero]

/-- The kStepVector_boundary_eq_lift with wrapping: handles the case where
    startChunk + k > chunkSizes.length by decomposing around the wraparound. -/
lemma kStepVector_boundary_eq_lift_wrapping [NeZero n] (x : BinaryStep) (w : BinaryNecklace n)
    (chunks : List BinaryStep) (chunkSizes : List ℕ)
    (hchunks : chunkSizesToBinary x w = some chunks)
    (hsizes : chunkSizesList x w = some chunkSizes)
    (hlen : chunks.length ≠ 0)
    (r : ℕ)
    (hboundary : ∀ i : ℕ, i ≤ chunkSizes.length →
      w ((r + chunkBoundaryAt chunkSizes i : ℕ) : ZMod n) = BinaryStep.otherStep x)
    (hchunk_vals : ∀ i : ℕ, (hi : i < chunkSizes.length) → ∀ m : ℕ, m < chunkSizes[i]'hi →
      w ((r + chunkBoundaryAt chunkSizes i + 1 + m : ℕ) : ZMod n) = x)
    (startChunk k : ℕ) (hstart : startChunk < chunkSizes.length)
    (_ : 0 < k) (hk : k ≤ chunkSizes.length) :
    haveI : NeZero chunks.length := ⟨hlen⟩
    let startPos := chunkBoundaryAt chunkSizes startChunk
    let numMaj := Necklace.count w x
    let numMin := Necklace.count w (BinaryStep.otherStep x)
    -- The total expanded size (wrapping-aware)
    let kExpanded := if startChunk + k ≤ chunkSizes.length then
        chunkBoundaryAt chunkSizes (startChunk + k) - startPos
      else
        (n - startPos) + chunkBoundaryAt chunkSizes (startChunk + k - chunkSizes.length)
    Necklace.kStepVector w (r + startPos) kExpanded =
      liftGeneratorVectorX x (Necklace.kStepVector (Necklace.toNecklace chunks) startChunk k) numMaj numMin := by
  haveI : NeZero chunks.length := ⟨hlen⟩
  dsimp only []
  have hchunks_sizes_len := chunks_length_eq_sizes x w chunkSizes hsizes chunks hchunks
  have htotal := chunkBoundaryAt_total x w chunkSizes hsizes
  split_ifs with hwrap
  · -- Non-wrapping case: delegate to kStepVector_boundary_eq_lift
    exact kStepVector_boundary_eq_lift x w chunks chunkSizes hchunks hsizes hlen r
      hboundary hchunk_vals startChunk k hwrap
  · -- Wrapping case: split at the wraparound point
    push_neg at hwrap
    set tail := chunkSizes.length - startChunk with htail_def
    set head := k - tail with hhead_def
    have hk_split : k = tail + head := by omega
    have htail_le : startChunk + tail ≤ chunkSizes.length := by omega
    have hhead_le : head ≤ chunkSizes.length := by omega
    have hhead_eq : startChunk + k - chunkSizes.length = head := by omega
    -- Split the chunked kStepVector
    have h_chunked_split : ∀ a, Necklace.kStepVector (Necklace.toNecklace chunks) startChunk k a =
        Necklace.kStepVector (Necklace.toNecklace chunks) startChunk tail a +
        Necklace.kStepVector (Necklace.toNecklace chunks) (startChunk + tail) head a := by
      intro a; rw [hk_split]; exact kStepVector_split _ _ _ _ a
    -- (startChunk + tail) % chunks.length = 0
    have hmod : (startChunk + tail) % chunks.length = 0 := by
      rw [htail_def, show startChunk + (chunkSizes.length - startChunk) = chunkSizes.length from by omega,
          hchunks_sizes_len]; exact Nat.mod_self _
    -- So kStepVector at (startChunk + tail) = kStepVector at 0
    have h_wrap_idx : Necklace.kStepVector (Necklace.toNecklace chunks) (startChunk + tail) head =
        Necklace.kStepVector (Necklace.toNecklace chunks) 0 head := by
      rw [← kStepVector_mod_n]; congr 1
    have h_startPos_le_n : chunkBoundaryAt chunkSizes startChunk ≤ n := by
      rw [← htotal]; exact chunkBoundaryAt_mono _ _ _ (by omega) (le_refl _)
    -- kStepVector w (r + startPos) kExpanded splits as two parts
    rw [hhead_eq]
    funext step
    rw [kStepVector_split w (r + chunkBoundaryAt chunkSizes startChunk) (n - chunkBoundaryAt chunkSizes startChunk) (chunkBoundaryAt chunkSizes head) step]
    set sp := chunkBoundaryAt chunkSizes startChunk with hsp_def
    -- First part: from startChunk boundary to end (= boundary at length)
    have h_first : Necklace.kStepVector w (r + sp) (n - sp) =
        liftGeneratorVectorX x (Necklace.kStepVector (Necklace.toNecklace chunks) startChunk tail)
          (Necklace.count w x) (Necklace.count w (BinaryStep.otherStep x)) := by
      have := kStepVector_boundary_eq_lift x w chunks chunkSizes hchunks hsizes hlen r
        hboundary hchunk_vals startChunk tail htail_le
      dsimp only [] at this
      rwa [show startChunk + tail = chunkSizes.length from by omega, htotal] at this
    -- Second part: from r + n to r + n + B(head) (wrapping via mod n)
    have h_second : Necklace.kStepVector w (r + sp + (n - sp)) (chunkBoundaryAt chunkSizes head) =
        liftGeneratorVectorX x (Necklace.kStepVector (Necklace.toNecklace chunks) 0 head)
          (Necklace.count w x) (Necklace.count w (BinaryStep.otherStep x)) := by
      rw [show r + sp + (n - sp) = r + n from by omega]
      rw [← kStepVector_mod_n w (r + n)]
      rw [show (r + n) % n = r % n from by rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]]
      have hbdry0 : chunkBoundaryAt chunkSizes 0 = 0 := by
        unfold chunkBoundaryAt chunkBoundaries; cases chunkSizes <;> simp [List.scanl]
      have h := kStepVector_boundary_eq_lift x w chunks chunkSizes hchunks hsizes hlen r
        hboundary hchunk_vals 0 head (by omega)
      dsimp only [] at h
      simp only [Nat.zero_add, hbdry0, Nat.add_zero, Nat.sub_zero] at h
      rw [kStepVector_mod_n w r]; exact h
    -- Combine using linearity
    rw [congr_fun h_first step, congr_fun h_second step]
    -- Rewrite RHS: kStepVector(chunks, start, k) = kStepVector(start,tail) + kStepVector(0,head)
    have h_chunked_eq : Necklace.kStepVector (Necklace.toNecklace chunks) startChunk k =
        fun a => Necklace.kStepVector (Necklace.toNecklace chunks) startChunk tail a +
                 Necklace.kStepVector (Necklace.toNecklace chunks) 0 head a := by
      funext a; rw [h_chunked_split a, congr_fun h_wrap_idx a]
    rw [h_chunked_eq, liftGeneratorVectorX_add]

/-- The size of a k-step in the expanded word starting at chunk boundary i,
    spanning exactly k chunks. This equals the sum of k consecutive chunk sizes plus k
    (for the k minority steps at chunk ends). -/
def liftedKStepSize (chunkSizes : List ℕ) (startChunk k : ℕ) : ℕ :=
  let endChunk := startChunk + k
  chunkBoundaryAt chunkSizes endChunk - chunkBoundaryAt chunkSizes startChunk

/-- Chunk boundaries are strictly monotone. -/
private lemma chunkBoundaryAt_strict_mono (chunkSizes : List ℕ) (a b : ℕ)
    (hab : a < b) (hb : b ≤ chunkSizes.length) :
    chunkBoundaryAt chunkSizes a < chunkBoundaryAt chunkSizes b := by
  induction b with
  | zero => omega
  | succ b' ih =>
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hab) with rfl | hlt
    · rw [chunkBoundaryAt_succ _ _ (by omega)]; omega
    · calc chunkBoundaryAt chunkSizes a
          < chunkBoundaryAt chunkSizes b' := ih hlt (by omega)
        _ ≤ chunkBoundaryAt chunkSizes (b' + 1) := by
            rw [chunkBoundaryAt_succ _ _ (by omega)]; omega

/-- Lifted k-step size is < n when spanning fewer than all chunks (with primitivity). -/
private lemma liftedKStepSize_lt_n [NeZero n] (x : BinaryStep) (w : BinaryNecklace n)
    (chunkSizes : List ℕ) (hsizes : chunkSizesList x w = some chunkSizes)
    (i k : ℕ) (hk_pos : 0 < k) (hik : i + k ≤ chunkSizes.length)
    (hnot_full : ¬(i = 0 ∧ k = chunkSizes.length)) :
    liftedKStepSize chunkSizes i k < n := by
  unfold liftedKStepSize; dsimp only []
  have htotal := chunkBoundaryAt_total x w chunkSizes hsizes
  have hb_mono := chunkBoundaryAt_mono chunkSizes i (i + k) (by omega) hik
  by_cases hi : i = 0
  · subst hi; simp only [Nat.zero_add] at *
    have hbdry0 : chunkBoundaryAt chunkSizes 0 = 0 := by
      unfold chunkBoundaryAt chunkBoundaries; cases chunkSizes <;> simp [List.scanl]
    rw [hbdry0, Nat.sub_zero]
    have hk_lt : k < chunkSizes.length := by
      by_contra h; push_neg at h; exact hnot_full ⟨trivial, by omega⟩
    calc chunkBoundaryAt chunkSizes k
        < chunkBoundaryAt chunkSizes chunkSizes.length :=
          chunkBoundaryAt_strict_mono _ _ _ hk_lt (le_refl _)
      _ = n := htotal
  · have hBi_pos := chunkBoundaryAt_strict_mono chunkSizes 0 i (Nat.pos_of_ne_zero hi) (by omega)
    have hBik_le : chunkBoundaryAt chunkSizes (i + k) ≤ n := by
      rw [← htotal]; exact chunkBoundaryAt_mono _ _ _ hik (le_refl _)
    omega

/-- Lifted k-step size is positive when spanning at least one chunk. -/
private lemma liftedKStepSize_pos (chunkSizes : List ℕ)
    (i k : ℕ) (hk_pos : 0 < k) (hik : i + k ≤ chunkSizes.length) :
    0 < liftedKStepSize chunkSizes i k := by
  unfold liftedKStepSize; dsimp only []
  have := chunkBoundaryAt_strict_mono chunkSizes i (i + k) (by omega) hik
  omega

/-- The otherStep component of liftGeneratorVectorX equals the total g(L) + g(s). -/
private lemma liftGenX_otherStep_eq_total (x : BinaryStep) (g : ZVector BinaryStep)
    (numMaj numMin : ℕ) :
    liftGeneratorVectorX x g numMaj numMin (BinaryStep.otherStep x) =
    g BinaryStep.L + g BinaryStep.s := by
  unfold liftGeneratorVectorX; cases x <;> simp [BinaryStep.otherStep]

set_option maxHeartbeats 400000 in
/-- The L-count in k-step subwords of a MOS word's chunk-sizes word takes at most 2 values.
    Proved by direct 3-position argument for the two-distinct-sizes case:
    if L_k takes values with gap ≥ 2, we get K-step vectors in the original word
    with L-counts differing by > 1, contradicting MOS. -/
private lemma chunked_L_counts_two_valued (n : ℕ) [NeZero n] (w : BinaryNecklace n)
    (hw : BinaryNecklace.isMOS w) (x : BinaryStep)
    (sizes : List ℕ) (hsizes : chunkSizesList x w = some sizes)
    (chunks : List BinaryStep) (hchunks : chunkSizesToBinary x w = some chunks)
    (hlen : chunks.length ≠ 0)
    (hcountX : Necklace.count w x > 1)
    (hcountOther : Necklace.count w (BinaryStep.otherStep x) > 1)
    (k : ℕ) (hk_pos : 0 < k) (hk_lt : k < chunks.length) :
    haveI : NeZero chunks.length := ⟨hlen⟩
    ∃ v : ℕ, v ≤ k ∧ ∀ i : ℕ, i < chunks.length →
      (Necklace.slice (Necklace.toNecklace chunks) i (i + k)).count BinaryStep.L = v ∨
      (Necklace.slice (Necklace.toNecklace chunks) i (i + k)).count BinaryStep.L = v + 1 := by
  haveI : NeZero chunks.length := ⟨hlen⟩
  -- chunks.length = sizes.length (from chunkSizesToBinary: all branches map sizes)
  have hchunks_sizes_len : chunks.length = sizes.length := by
    unfold chunkSizesToBinary at hchunks
    simp only [hsizes] at hchunks
    change (match sizes.toFinset.toList with
      | [_] => some (sizes.map (fun _ => BinaryStep.L))
      | [a, b] => if a + 1 = b || b + 1 = a then
          some (sizes.map (fun s => if s = min a b then BinaryStep.s else BinaryStep.L))
        else none
      | _ => none) = some chunks at hchunks
    split at hchunks
    · rw [← Option.some.inj hchunks, List.length_map]
    · split at hchunks
      · rw [← Option.some.inj hchunks, List.length_map]
      · cases hchunks
    · cases hchunks
  -- Chunk sizes have at most 2 distinct values
  have hcard_le := mos_chunk_sizes_at_most_two n w hw x sizes hsizes
  have hne := chunkSizesList_nonempty x w sizes hsizes
  have hcard_pos : 0 < sizes.toFinset.card :=
    Finset.card_pos.mpr ⟨sizes.head hne, List.mem_toFinset.mpr (List.head_mem hne)⟩
  have hcard_cases : sizes.toFinset.card = 1 ∨ sizes.toFinset.card = 2 := by omega
  rcases hcard_cases with hone | htwo
  · -- All chunks same size: chunkSizesToBinary maps all to L, so L-count = k
    refine ⟨k, le_refl k, fun i _ => Or.inl ?_⟩
    -- When card = 1, all elements of chunks are L (using membership)
    have hall_mem : ∀ b ∈ chunks, b = BinaryStep.L := by
      unfold chunkSizesToBinary at hchunks
      simp only [hsizes] at hchunks
      change (match sizes.toFinset.toList with
        | [_] => some (sizes.map (fun _ => BinaryStep.L))
        | [a, b] => if a + 1 = b || b + 1 = a then
            some (sizes.map (fun s => if s = min a b then BinaryStep.s else BinaryStep.L))
          else none
        | _ => none) = some chunks at hchunks
      split at hchunks
      · -- [_] case: chunks = sizes.map (fun _ => L)
        intro b hb
        rw [← Option.some.inj hchunks] at hb
        simp at hb
        exact hb.2
      · -- [a, b] case: contradiction with card = 1
        exfalso
        rename_i _ _ h_tolist
        have : sizes.toFinset.toList.length = 2 := by rw [h_tolist]; simp
        rw [Finset.length_toList] at this; omega
      · -- wildcard: contradiction (none = some)
        cases hchunks
    -- toNecklace maps to L everywhere
    have hconst : ∀ p : ZMod chunks.length,
        (Necklace.toNecklace chunks) p = BinaryStep.L := by
      intro p
      apply hall_mem
      simp only [Necklace.toNecklace]
      rw [getElem!_pos chunks (ZMod.val p) (ZMod.val_lt p)]
      exact List.getElem_mem (ZMod.val_lt p)
    -- slice of constant-L necklace has count = length = k
    have hslice_all_L : ∀ y ∈ Necklace.slice (Necklace.toNecklace chunks) i (i + k),
        BinaryStep.L = y := by
      intro y hy
      simp only [Necklace.slice, List.mem_map] at hy
      obtain ⟨j, _, rfl⟩ := hy
      exact (hconst j).symm
    rw [List.count_eq_length.mpr hslice_all_L, Necklace.slice_length]; omega
  · -- Two distinct chunk sizes: direct MOS contradiction argument
    -- Setup
    set numMaj := Necklace.count w x with hnumMaj_def
    set numMin := Necklace.count w (BinaryStep.otherStep x) with hnumMin_def
    have hnumMin_pos : 0 < numMin := by omega
    -- large ≥ small (ceil ≥ floor)
    have hlarge_ge : largeChunkSize numMaj numMin ≥ smallChunkSize numMaj numMin :=
      Nat.div_le_div_right (by omega)
    -- large ≠ small (since card = 2, both sizes appear)
    have hlarge_ne : largeChunkSize numMaj numMin ≠ smallChunkSize numMaj numMin := by
      intro heq
      -- All sizes are in {large, small} = {small}, so card ≤ 1
      have hsub : sizes.toFinset ⊆ {smallChunkSize numMaj numMin} := by
        intro s hs
        rw [Finset.mem_singleton, List.mem_toFinset] at *
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hs
        have hmatch := chunk_binary_size_match x w sizes hsizes chunks hchunks i hi
        dsimp only [] at hmatch; rw [heq] at hmatch
        exact hmatch.trans (by
          cases chunks[i]'(by rw [chunks_length_eq_sizes x w sizes hsizes chunks hchunks]; exact hi)
          all_goals rfl)
      have := Finset.card_le_card hsub; rw [Finset.card_singleton] at this; omega
    have hlarge_gt : largeChunkSize numMaj numMin > smallChunkSize numMaj numMin := by omega
    -- Get chunk word structure
    obtain ⟨r, _, hboundary, hchunk_vals⟩ := chunk_word_structure x w sizes hsizes
    set m := chunks.length with hm_def
    -- By contradiction: assume L_k not 2-valued
    by_contra h_not
    push_neg at h_not
    -- L_k function
    set Lk : ℕ → ℕ := fun i =>
      (Necklace.slice (Necklace.toNecklace chunks) i (i + k)).count BinaryStep.L with hLk_def
    have hLk_le_k : ∀ i, Lk i ≤ k :=
      fun i => le_trans List.count_le_length (by rw [Necklace.slice_length]; omega)
    -- Find minimum L_k position
    set S := (Finset.range m).image Lk with hS_def
    have hS_ne : S.Nonempty :=
      ⟨Lk 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), rfl⟩⟩
    set v_min := S.min' hS_ne with hv_min_def
    have hv_min_in : v_min ∈ (Finset.range m).image Lk := Finset.min'_mem S hS_ne
    obtain ⟨i₁, hi₁_range, hi₁_eq⟩ := Finset.mem_image.mp hv_min_in
    rw [Finset.mem_range] at hi₁_range
    have hv_min_le_k : v_min ≤ k := hi₁_eq ▸ hLk_le_k i₁
    -- Find position with gap ≥ 2
    obtain ⟨i₂, hi₂_lt, hi₂_ne, hi₂_ne1⟩ := h_not v_min hv_min_le_k
    have hgap : Lk i₂ ≥ v_min + 2 := by
      change Lk i₂ ≠ v_min at hi₂_ne
      change Lk i₂ ≠ v_min + 1 at hi₂_ne1
      have := Finset.min'_le S (Lk i₂)
        (Finset.mem_image.mpr ⟨i₂, Finset.mem_range.mpr hi₂_lt, rfl⟩)
      omega
    -- Apply kStepVector_boundary_eq_lift_wrapping at both positions
    have hk_le : k ≤ sizes.length := by rw [← hchunks_sizes_len]; omega
    have hi₁_sizes : i₁ < sizes.length := by rw [← hchunks_sizes_len]; exact hi₁_range
    have hi₂_sizes : i₂ < sizes.length := by rw [← hchunks_sizes_len]; exact hi₂_lt
    set g₁ := Necklace.kStepVector (Necklace.toNecklace chunks) i₁ k with hg₁_def
    set g₂ := Necklace.kStepVector (Necklace.toNecklace chunks) i₂ k with hg₂_def
    -- Name kExpanded values
    set kE₁ := if i₁ + k ≤ sizes.length then
        chunkBoundaryAt sizes (i₁ + k) - chunkBoundaryAt sizes i₁
      else
        (n - chunkBoundaryAt sizes i₁) + chunkBoundaryAt sizes (i₁ + k - sizes.length)
      with hkE₁_def
    set kE₂ := if i₂ + k ≤ sizes.length then
        chunkBoundaryAt sizes (i₂ + k) - chunkBoundaryAt sizes i₂
      else
        (n - chunkBoundaryAt sizes i₂) + chunkBoundaryAt sizes (i₂ + k - sizes.length)
      with hkE₂_def
    -- Lift equalities
    have hlift₁ : Necklace.kStepVector w (r + chunkBoundaryAt sizes i₁) kE₁ =
        liftGeneratorVectorX x g₁ numMaj numMin :=
      kStepVector_boundary_eq_lift_wrapping x w chunks sizes hchunks hsizes
        hlen r hboundary hchunk_vals i₁ k hi₁_sizes hk_pos hk_le
    have hlift₂ : Necklace.kStepVector w (r + chunkBoundaryAt sizes i₂) kE₂ =
        liftGeneratorVectorX x g₂ numMaj numMin :=
      kStepVector_boundary_eq_lift_wrapping x w chunks sizes hchunks hsizes
        hlen r hboundary hchunk_vals i₂ k hi₂_sizes hk_pos hk_le
    -- kE formulas via total count + lift
    have hkE₁_eq : (↑kE₁ : ℤ) = g₁ BinaryStep.L * (↑(largeChunkSize numMaj numMin) + 1) +
        g₁ BinaryStep.s * (↑(smallChunkSize numMaj numMin) + 1) := by
      have h := kStepVector_total_count w (r + chunkBoundaryAt sizes i₁) kE₁
      rw [hlift₁, liftGeneratorVectorX_total_sum] at h; linarith
    have hkE₂_eq : (↑kE₂ : ℤ) = g₂ BinaryStep.L * (↑(largeChunkSize numMaj numMin) + 1) +
        g₂ BinaryStep.s * (↑(smallChunkSize numMaj numMin) + 1) := by
      have h := kStepVector_total_count w (r + chunkBoundaryAt sizes i₂) kE₂
      rw [hlift₂, liftGeneratorVectorX_total_sum] at h; linarith
    -- g totals and L-component = Lk
    have hg₁_total := kStepVector_total_count (Necklace.toNecklace chunks) i₁ k
    have hg₂_total := kStepVector_total_count (Necklace.toNecklace chunks) i₂ k
    -- kE₂ ≥ kE₁ + 2 (gap in Lk amplified by large - small ≥ 1)
    have hkE_diff : (↑kE₂ : ℤ) - ↑kE₁ =
        (g₂ BinaryStep.L - g₁ BinaryStep.L) *
        (↑(largeChunkSize numMaj numMin) - ↑(smallChunkSize numMaj numMin)) := by
      have hs₁ : g₁ BinaryStep.s = ↑k - g₁ BinaryStep.L := by linarith [hg₁_total]
      have hs₂ : g₂ BinaryStep.s = ↑k - g₂ BinaryStep.L := by linarith [hg₂_total]
      rw [hkE₁_eq, hkE₂_eq, hs₁, hs₂]; ring
    have hgL_ge : g₂ BinaryStep.L - g₁ BinaryStep.L ≥ 2 := by
      -- g(L) = ↑(Lk i) by definitional unfolding
      have : g₁ BinaryStep.L = ↑(Lk i₁) := by
        simp only [hg₁_def, hLk_def, Necklace.kStepVector, ZVector.ofList, List.count,
          List.countP_eq_length_filter]
      have : g₂ BinaryStep.L = ↑(Lk i₂) := by
        simp only [hg₂_def, hLk_def, Necklace.kStepVector, ZVector.ofList, List.count,
          List.countP_eq_length_filter]
      rw [‹g₁ BinaryStep.L = _›, ‹g₂ BinaryStep.L = _›]
      linarith [hgap, hi₁_eq]
    have hkE_gap : kE₂ ≥ kE₁ + 2 := by
      have : (↑kE₂ : ℤ) - ↑kE₁ ≥ 2 := by
        rw [hkE_diff]; nlinarith [hgL_ge, show (↑(largeChunkSize numMaj numMin) : ℤ) -
          ↑(smallChunkSize numMaj numMin) ≥ 1 from by omega]
      omega
    -- kE₁ > 0 (spans k ≥ 1 chunks)
    have hkE₁_pos : 0 < kE₁ := by
      simp only [hkE₁_def]; split_ifs with h
      · exact Nat.sub_pos_of_lt (chunkBoundaryAt_strict_mono sizes i₁ (i₁ + k) (by omega) h)
      · push_neg at h
        have := chunkBoundaryAt_strict_mono sizes 0 (i₁ + k - sizes.length) (by omega) (by omega)
        have := chunkBoundaryAt_mono sizes i₁ sizes.length (by omega) (le_refl _)
        have := chunkBoundaryAt_total x w sizes hsizes
        have : chunkBoundaryAt sizes 0 = 0 := by
          unfold chunkBoundaryAt chunkBoundaries; cases sizes <;> simp [List.scanl]
        omega
    -- kE₂ < n
    have hkE₂_lt_n : kE₂ < n := by
      simp only [hkE₂_def]; split_ifs with h
      · have := liftedKStepSize_lt_n x w sizes hsizes i₂ k hk_pos h
            (by intro ⟨hi, hk⟩; rw [hk, hchunks_sizes_len] at hk_lt; omega)
        unfold liftedKStepSize at this; dsimp only [] at this; exact this
      · push_neg at h
        have := chunkBoundaryAt_strict_mono sizes (i₂ + k - sizes.length) i₂ (by omega) (by omega)
        have := chunkBoundaryAt_mono sizes i₂ sizes.length (by omega) (le_refl _)
        have := chunkBoundaryAt_total x w sizes hsizes; omega
    -- Set K = kE₂ - 1
    set K := kE₂ - 1 with hK_def
    have hK_pos : 0 < K := by omega
    have hK_lt : K < n := by omega
    -- Two K-step vectors in the original word
    set v₁ := Necklace.kStepVector w (r + chunkBoundaryAt sizes i₂ + 1) K with hv₁_def
    set v₂ := Necklace.kStepVector w (r + chunkBoundaryAt sizes i₁) K with hv₂_def
    -- Membership in distinctKStepVectors
    have hv₁_mem : v₁ ∈ distinctKStepVectors w K := by
      rw [hv₁_def]; unfold distinctKStepVectors Necklace.allKStepVectors
      rw [List.mem_toFinset, List.mem_map]
      exact ⟨(r + chunkBoundaryAt sizes i₂ + 1) % n,
        List.mem_range.mpr (Nat.mod_lt _ (NeZero.pos n)), kStepVector_mod_n w _ K⟩
    have hv₂_mem : v₂ ∈ distinctKStepVectors w K := by
      rw [hv₂_def]; unfold distinctKStepVectors Necklace.allKStepVectors
      rw [List.mem_toFinset, List.mem_map]
      exact ⟨(r + chunkBoundaryAt sizes i₁) % n,
        List.mem_range.mpr (Nat.mod_lt _ (NeZero.pos n)), kStepVector_mod_n w _ K⟩
    -- v₁ otherStep(x) count = k - 1
    have hv₁_other : v₁ (BinaryStep.otherStep x) = ↑k - 1 := by
      -- Split kE₂ = 1 + K at boundary(i₂)
      have hsplit := kStepVector_split w (r + chunkBoundaryAt sizes i₂) 1 K
        (BinaryStep.otherStep x)
      rw [show 1 + K = kE₂ from by omega] at hsplit
      -- kStepVector(w, B(i₂), kE₂)(otherStep) = k
      have hfull : Necklace.kStepVector w (r + chunkBoundaryAt sizes i₂) kE₂
          (BinaryStep.otherStep x) = ↑k := by
        rw [hlift₂, liftGenX_otherStep_eq_total]; exact_mod_cast hg₂_total
      -- 1-step vector at boundary has otherStep count = 1
      have h1step : Necklace.kStepVector w (r + chunkBoundaryAt sizes i₂) 1
          (BinaryStep.otherStep x) = 1 := by
        rw [congr_fun (kStepVector_constant_value w _ 1 (BinaryStep.otherStep x) (fun m hm => by
          have : m = 0 := by omega
          subst this; simp only [Nat.add_zero]
          exact hboundary i₂ (by omega))) (BinaryStep.otherStep x)]
        simp only [ite_true, Nat.cast_one]
      rw [hfull, h1step] at hsplit
      have hv₁_rfl : v₁ (BinaryStep.otherStep x) =
        Necklace.kStepVector w (r + chunkBoundaryAt sizes i₂ + 1) K (BinaryStep.otherStep x) := rfl
      linarith only [hsplit, hv₁_rfl]
    -- v₂ otherStep(x) count ≥ k + 1
    have hv₂_other : v₂ (BinaryStep.otherStep x) ≥ ↑k + 1 := by
      -- Split K = kE₁ + (K - kE₁), where K - kE₁ ≥ 1
      have hK_ge : kE₁ ≤ K := by omega
      have hsplit := kStepVector_split w (r + chunkBoundaryAt sizes i₁) kE₁ (K - kE₁)
        (BinaryStep.otherStep x)
      rw [show kE₁ + (K - kE₁) = K from by omega] at hsplit
      -- First part: otherStep count = k
      have hfirst : Necklace.kStepVector w (r + chunkBoundaryAt sizes i₁) kE₁
          (BinaryStep.otherStep x) = ↑k := by
        rw [hlift₁, liftGenX_otherStep_eq_total]; exact_mod_cast hg₁_total
      -- Position after kE₁ steps is a boundary
      have hpos_boundary : w ((r + chunkBoundaryAt sizes i₁ + kE₁ : ℕ) : ZMod n) =
          BinaryStep.otherStep x := by
        simp only [hkE₁_def]; split_ifs with hwrap
        · -- Non-wrapping: position = r + B(i₁ + k)
          have := chunkBoundaryAt_mono sizes i₁ (i₁ + k) (by omega) hwrap
          rw [show r + chunkBoundaryAt sizes i₁ +
            (chunkBoundaryAt sizes (i₁ + k) - chunkBoundaryAt sizes i₁) =
            r + chunkBoundaryAt sizes (i₁ + k) from by omega]
          exact hboundary (i₁ + k) hwrap
        · -- Wrapping: position = r + n + B(head₁), ZMod cast to r + B(head₁)
          push_neg at hwrap
          set head₁ := i₁ + k - sizes.length with hhead₁_def
          have hBi₁_le_n : chunkBoundaryAt sizes i₁ ≤ n := by
            rw [← chunkBoundaryAt_total x w sizes hsizes]
            exact chunkBoundaryAt_mono sizes i₁ sizes.length (by omega) (le_refl _)
          rw [show r + chunkBoundaryAt sizes i₁ +
            ((n - chunkBoundaryAt sizes i₁) + chunkBoundaryAt sizes head₁) =
            (r + chunkBoundaryAt sizes head₁) + n from by omega]
          simp only [Nat.cast_add, ZMod.natCast_self n, add_zero]
          rw [← Nat.cast_add]
          exact hboundary head₁ (by omega)
      -- Second part starts at boundary, so ≥ 1 otherStep
      have hrest_pos : 0 < K - kE₁ := by omega
      have hsplit2 := kStepVector_split w (r + chunkBoundaryAt sizes i₁ + kE₁) 1 (K - kE₁ - 1)
        (BinaryStep.otherStep x)
      rw [show 1 + (K - kE₁ - 1) = K - kE₁ from by omega] at hsplit2
      have h1step : Necklace.kStepVector w (r + chunkBoundaryAt sizes i₁ + kE₁) 1
          (BinaryStep.otherStep x) = 1 := by
        rw [congr_fun (kStepVector_constant_value w _ 1 (BinaryStep.otherStep x) (fun m hm => by
          have : m = 0 := by omega
          subst this; simp only [Nat.add_zero]
          exact hpos_boundary)) (BinaryStep.otherStep x)]
        simp only [ite_true, Nat.cast_one]
      have h_nonneg : Necklace.kStepVector w (r + chunkBoundaryAt sizes i₁ + kE₁ + 1)
          (K - kE₁ - 1) (BinaryStep.otherStep x) ≥ 0 := by
        unfold Necklace.kStepVector ZVector.ofList; exact_mod_cast Nat.zero_le _
      rw [hfirst] at hsplit; rw [h1step] at hsplit2
      have hv₂_rfl : v₂ (BinaryStep.otherStep x) =
        Necklace.kStepVector w (r + chunkBoundaryAt sizes i₁) K (BinaryStep.otherStep x) := rfl
      linarith only [hsplit, hsplit2, h_nonneg, hv₂_rfl]
    -- Derive contradiction via mos_kStepVector_L_count_diff_le_one
    have hmos := mos_kStepVector_L_count_diff_le_one w hw K hK_pos hK_lt v₁ v₂ hv₁_mem hv₂_mem
    have hv₁_total := kStepVector_total_count w (r + chunkBoundaryAt sizes i₂ + 1) K
    have hv₂_total := kStepVector_total_count w (r + chunkBoundaryAt sizes i₁) K
    -- Case split on x to identify which component is otherStep
    cases x with
    | L =>
      simp only [BinaryStep.otherStep] at hv₁_other hv₂_other
      -- v₁(s) = k-1, v₂(s) ≥ k+1; mos says |v₁(L)-v₂(L)| ≤ 1; contradiction
      linarith [hmos.1]
    | s =>
      simp only [BinaryStep.otherStep] at hv₁_other hv₂_other
      -- v₁(L) = k-1, v₂(L) ≥ k+1; mos says v₂(L) ≤ v₁(L)+1; contradiction
      linarith [hmos.2]

/-- Core claim: for a MOS word's chunked binary word, the k-step multisets take ≤ 2 values.
    There exist at most two multisets that appear as k-step abelianizations.

    Proof sketch (by contradiction): If L-counts c(i) in k consecutive chunks take ≥ 3 values,
    pick i₁ with c(i₁) = c_min (and chunk (i₁+k) is large — always possible, see below)
    and i₂ with c(i₂) ≥ c_min + 2. Set K = k*(small+1) + c_min + 1 in the original word.
    Then three positions give K-step minority counts k+1, k, ≤ k-1 → contradiction with hw.

    Key sub-argument: if all positions with c = c_min have chunk (i+k) small, then
    c(i+1) = c(i) - 0 + 0 = c_min for all such i, propagating to ALL positions = c_min.
    This contradicts c_max ≥ c_min + 2, so some c_min position must have chunk (i+k) large. -/
private lemma mos_chunked_kstep_multisets_subset (n : ℕ) [NeZero n] (w : BinaryNecklace n)
    (hw : BinaryNecklace.isMOS w) (x : BinaryStep)
    (sizes : List ℕ) (hsizes : chunkSizesList x w = some sizes)
    (chunks : List BinaryStep) (hchunks : chunkSizesToBinary x w = some chunks)
    (hlen : chunks.length ≠ 0)
    (hcountX : Necklace.count w x > 1)
    (hcountOther : Necklace.count w (BinaryStep.otherStep x) > 1)
    (k : ℕ) (hk_pos : 0 < k) (hk_lt : k < chunks.length) :
    haveI : NeZero chunks.length := ⟨hlen⟩
    ∃ (m₁ m₂ : Multiset BinaryStep),
      ∀ m ∈ (Necklace.allKStepMultisets (Necklace.toNecklace chunks) k), m = m₁ ∨ m = m₂ := by
  haveI : NeZero chunks.length := ⟨hlen⟩
  obtain ⟨v, _, hv⟩ := chunked_L_counts_two_valued n w hw x sizes hsizes chunks hchunks hlen
    hcountX hcountOther k hk_pos hk_lt
  -- Slices with equal L-counts give equal multisets (for binary step lists)
  have heq_mset : ∀ a b : ℕ,
      (Necklace.slice (Necklace.toNecklace chunks) a (a + k)).count BinaryStep.L =
      (Necklace.slice (Necklace.toNecklace chunks) b (b + k)).count BinaryStep.L →
      (↑(Necklace.slice (Necklace.toNecklace chunks) a (a + k)) : Multiset BinaryStep) =
      ↑(Necklace.slice (Necklace.toNecklace chunks) b (b + k)) :=
    fun a b hcount => binary_multiset_eq_of_L_count_eq _ _
      (by simp [Necklace.slice_length]) hcount
  -- Unpack membership in allKStepMultisets to get a position index
  have hmem_unpack : ∀ m : Multiset BinaryStep,
      m ∈ Necklace.allKStepMultisets (Necklace.toNecklace chunks) k →
      ∃ i : ℕ, i < chunks.length ∧
        m = ↑(Necklace.slice (Necklace.toNecklace chunks) i (i + k)) := by
    intro m hm
    simp only [Necklace.allKStepMultisets, Necklace.abelianize, Necklace.allKStepSubwords,
      List.mem_map, List.mem_ofFn] at hm
    obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := hm
    exact ⟨i.val, i.isLt, rfl⟩
  -- Normalize hv at 0
  have hv0 := hv 0 (by omega)
  simp only [Nat.zero_add] at hv0
  -- Case split: all L-counts equal, or some differ
  by_cases h_eq : ∀ i : ℕ, i < chunks.length →
      (Necklace.slice (Necklace.toNecklace chunks) i (i + k)).count BinaryStep.L =
      (Necklace.slice (Necklace.toNecklace chunks) 0 k).count BinaryStep.L
  · -- All L-counts equal: every multiset equals the one at position 0
    refine ⟨↑(Necklace.slice (Necklace.toNecklace chunks) 0 k),
            ↑(Necklace.slice (Necklace.toNecklace chunks) 0 k), fun m hm => ?_⟩
    obtain ⟨i, hi_lt, rfl⟩ := hmem_unpack m hm
    have h := heq_mset i 0 (by rw [h_eq i hi_lt, Nat.zero_add])
    simp only [Nat.zero_add] at h
    exact Or.inl h
  · -- Some position j has a different L-count
    push_neg at h_eq
    obtain ⟨j, hj_lt, hj⟩ := h_eq
    refine ⟨↑(Necklace.slice (Necklace.toNecklace chunks) 0 k),
            ↑(Necklace.slice (Necklace.toNecklace chunks) j (j + k)), fun m hm => ?_⟩
    obtain ⟨i, hi_lt, rfl⟩ := hmem_unpack m hm
    -- Since 0 and j have different L-counts within {v, v+1}, they cover both values
    -- So i's L-count must match one of them
    suffices (Necklace.slice (Necklace.toNecklace chunks) i (i + k)).count BinaryStep.L =
             (Necklace.slice (Necklace.toNecklace chunks) 0 k).count BinaryStep.L ∨
             (Necklace.slice (Necklace.toNecklace chunks) i (i + k)).count BinaryStep.L =
             (Necklace.slice (Necklace.toNecklace chunks) j (j + k)).count BinaryStep.L by
      rcases this with h | h
      · have h' := heq_mset i 0 (by rw [h, Nat.zero_add])
        simp only [Nat.zero_add] at h'
        exact Or.inl h'
      · exact Or.inr (heq_mset i j h)
    rcases hv i hi_lt with hi | hi <;> rcases hv0 with h0 | h0 <;>
      rcases hv j hj_lt with hj' | hj' <;> omega

private lemma mos_chunked_at_most_two_kstep_multisets (n : ℕ) [NeZero n] (w : BinaryNecklace n)
    (hw : BinaryNecklace.isMOS w) (x : BinaryStep)
    (sizes : List ℕ) (hsizes : chunkSizesList x w = some sizes)
    (chunks : List BinaryStep) (hchunks : chunkSizesToBinary x w = some chunks)
    (hlen : chunks.length ≠ 0)
    (hcountX : Necklace.count w x > 1)
    (hcountOther : Necklace.count w (BinaryStep.otherStep x) > 1)
    (k : ℕ) (hk_pos : 0 < k) (hk_lt : k < chunks.length) :
    haveI : NeZero chunks.length := ⟨hlen⟩
    (Necklace.allKStepMultisets (Necklace.toNecklace chunks) k).toFinset.card ≤ 2 := by
  haveI : NeZero chunks.length := ⟨hlen⟩
  obtain ⟨m₁, m₂, hmem⟩ := mos_chunked_kstep_multisets_subset n w hw x sizes hsizes
    chunks hchunks hlen hcountX hcountOther k hk_pos hk_lt
  calc (Necklace.allKStepMultisets (Necklace.toNecklace chunks) k).toFinset.card
      ≤ ({m₁, m₂} : Finset _).card := by
        apply Finset.card_le_card
        intro m hm
        rw [List.mem_toFinset] at hm
        rcases hmem m hm with h | h <;> simp [h]
    _ ≤ 2 := Finset.card_le_two

/-- The chunk sizes of a primitive MOS scale, when converted to binary (L for larger, s for smaller),
    form a primitive MOS necklace. -/
theorem chunkSizesOfPrimMOSFormPrimMOS (n : ℕ) [NeZero n] (w : BinaryNecklace n)
    (hw : BinaryNecklace.isMOS w) (hprim : Necklace.isPrimitive w)
    (x : BinaryStep) (chunks : List BinaryStep)
    (hchunks : chunkSizesToBinary x w = some chunks) (hlen : chunks.length ≠ 0)
    (hcountX : Necklace.count w x > 1)
    (hcountOther : Necklace.count w (BinaryStep.otherStep x) > 1) :
    haveI : NeZero chunks.length := ⟨hlen⟩
    BinaryNecklace.isMOS (Necklace.toNecklace chunks) := by
  haveI : NeZero chunks.length := ⟨hlen⟩
  -- Extract sizes from chunkSizesToBinary
  have hsizes_exists : ∃ sizes, chunkSizesList x w = some sizes := by
    unfold chunkSizesToBinary at hchunks
    cases hsizes : chunkSizesList x w with
    | none => simp [hsizes] at hchunks
    | some sizes => exact ⟨sizes, rfl⟩
  obtain ⟨sizes, hsizes⟩ := hsizes_exists
  set m := chunks.length with hm_def
  constructor
  · -- Part 1: isBinary — chunks contains both L and s
    have hcard_two := prim_mos_has_two_chunk_sizes n w hw hprim x sizes hsizes hcountX hcountOther
    -- Unfold chunkSizesToBinary to determine the structure of chunks
    unfold chunkSizesToBinary at hchunks
    simp only [hsizes] at hchunks
    change (match sizes.toFinset.toList with
      | [_] => some (sizes.map (fun _ => BinaryStep.L))
      | [a, b] => if a + 1 = b || b + 1 = a then
          some (sizes.map (fun s => if s = min a b then BinaryStep.s else BinaryStep.L))
        else none
      | _ => none) = some chunks at hchunks
    split at hchunks
    · -- Case [head]: all same size, card = 1, contradicts hcard_two
      rename_i head hdist
      exfalso
      have : sizes.toFinset.card = 1 := by
        rw [← Finset.length_toList, hdist]; simp
      omega
    · -- Case [a, b]: the main case
      rename_i a b hdist
      split at hchunks
      · -- Consecutive: chunks = sizes.map (fun s => if s = min a b then s else L)
        injection hchunks with hchunks_eq
        -- a and b are in sizes, and a ≠ b
        have ha_mem : a ∈ sizes :=
          List.mem_toFinset.mp (Finset.mem_toList.mp
            (show a ∈ sizes.toFinset.toList from by rw [hdist]; exact List.mem_cons_self))
        have hb_mem : b ∈ sizes :=
          List.mem_toFinset.mp (Finset.mem_toList.mp
            (show b ∈ sizes.toFinset.toList from by
              rw [hdist]; exact List.mem_cons.mpr (Or.inr List.mem_cons_self)))
        have hab_ne : a ≠ b := by
          intro heq
          have hnodup := Finset.nodup_toList sizes.toFinset
          rw [hdist] at hnodup
          simp [List.nodup_cons] at hnodup
          exact hnodup heq
        -- s ∈ chunks (via min a b, which maps to s)
        have hs_mem : BinaryStep.s ∈ chunks := by
          rw [← hchunks_eq, List.mem_map]
          have hmin_mem : min a b ∈ sizes := by
            rcases Nat.le_total a b with h | h
            · rw [Nat.min_eq_left h]; exact ha_mem
            · rw [Nat.min_eq_right h]; exact hb_mem
          exact ⟨min a b, hmin_mem, by simp⟩
        -- L ∈ chunks (via max a b, which maps to L since max ≠ min)
        have hL_mem : BinaryStep.L ∈ chunks := by
          rw [← hchunks_eq, List.mem_map]
          have hmax_mem : max a b ∈ sizes := by
            rcases Nat.le_total a b with h | h
            · rw [Nat.max_eq_right h]; exact hb_mem
            · rw [Nat.max_eq_left h]; exact ha_mem
          have hmax_ne_min : ¬(max a b = min a b) := by omega
          exact ⟨max a b, hmax_mem, by simp [hmax_ne_min]⟩
        -- Convert list membership to isBinary of the necklace
        constructor
        · -- ∃ i, (toNecklace chunks) i = L
          obtain ⟨j, hj_lt, hjL⟩ := List.mem_iff_getElem.mp hL_mem
          exact ⟨(j : ZMod m), by
            show chunks[((j : ℕ) : ZMod m).val]! = BinaryStep.L
            rw [ZMod.val_natCast_of_lt (show j < m by omega)]
            simp only [getElem!_pos, hj_lt, hjL]⟩
        · -- ∃ i, (toNecklace chunks) i = s
          obtain ⟨j, hj_lt, hjs⟩ := List.mem_iff_getElem.mp hs_mem
          exact ⟨(j : ZMod m), by
            show chunks[((j : ℕ) : ZMod m).val]! = BinaryStep.s
            rw [ZMod.val_natCast_of_lt (show j < m by omega)]
            simp only [getElem!_pos, hj_lt, hjs]⟩
      · -- Not consecutive: none = some chunks, contradiction
        cases hchunks
    · -- Case _: catch-all, impossible given card = 2
      exfalso
      rename_i h_not_single h_not_pair
      have hlen : sizes.toFinset.toList.length = 2 := by
        rw [Finset.length_toList]; exact hcard_two
      cases hdist : sizes.toFinset.toList with
      | nil => simp [hdist] at hlen
      | cons c rest =>
        cases rest with
        | nil => simp [hdist] at hlen
        | cons d rest' =>
          cases rest' with
          | nil => exact h_not_pair c d hdist
          | cons _ _ => simp [hdist] at hlen
  · -- Part 2: ≤ 2 distinct k-step multisets for all k
    intro k hk_pos hk_lt
    exact mos_chunked_at_most_two_kstep_multisets n w hw x sizes hsizes chunks hchunks hlen
      hcountX hcountOther k hk_pos hk_lt

/-- The expansion operation: takes a chunked binary word and chunk sizes, produces the expanded word.
    This is the inverse of chunking. -/
noncomputable def expand (chunked : List BinaryStep) (chunkSizes : List ℕ) (x : BinaryStep) :
    Option (List BinaryStep) :=
  if chunked.length ≠ chunkSizes.length then none
  else some (List.flatten (List.zipWith (fun _step size =>
    List.replicate size x ++ [BinaryStep.otherStep x]
  ) chunked chunkSizes))

/-- ZVector scooting: if the letter leaving on the left equals the letter entering on the right,
    the kStepVector is unchanged when shifting by one position. -/
lemma scoot_kStepVector [NeZero n] (w : BinaryNecklace n) (i k : ℕ) (hk : 0 < k)
    (heq : w (i : ZMod n) = w ((i + k) : ZMod n)) :
    Necklace.kStepVector w i k = Necklace.kStepVector w (i + 1) k := by
  unfold Necklace.kStepVector
  funext a
  -- slice(i, i+k) = [w(i)] ++ slice(i+1, i+k)
  have h1 := slice_shift_decompose w i k hk
  -- slice(i+1, i+1+k) = slice(i+1, i+k) ++ [w(i+k)]
  have h2 := slice_extend_end w (i + 1) (k - 1)
  have hk2 : i + 1 + (k - 1) + 1 = i + 1 + k := by omega
  have hk1 : i + 1 + (k - 1) = i + k := by omega
  rw [hk2, hk1] at h2
  have hzmod : (↑(i + 1) + ↑(k - 1) : ZMod n) = (↑(i + k) : ZMod n) := by
    rw [← Nat.cast_add]; congr 1
  simp only [hzmod] at h2
  rw [h1, h2, ZVector_ofList_cons, ofList_append, heq]
  simp only [← Nat.cast_add]
  ring

/-- Interval scooting for kStepVector: if all positions in [chunkStart, chunkEnd) have the same
    letter as kLifted positions ahead, then the kStepVector is constant across the interval. -/
lemma scoot_kStepVector_interval [NeZero n] (w : BinaryNecklace n)
    (g : ZVector BinaryStep) (k : ℕ) (chunkStart chunkEnd : ℕ)
    (hk : 0 < k)
    (hscoot : ∀ j, chunkStart ≤ j → j < chunkEnd →
      w (j : ZMod n) = w ((j + k) : ZMod n))
    (hperfStart : Necklace.kStepVector w chunkStart k = g) :
    ∀ j, chunkStart ≤ j → j ≤ chunkEnd →
      Necklace.kStepVector w j k = g := by
  intro j hj_start hj_end
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases eq_or_lt_of_le hj_start with rfl | hj_gt
    · exact hperfStart
    · have hj_pred_start : chunkStart ≤ j - 1 := by omega
      have hj_pred_end : j - 1 ≤ chunkEnd := by omega
      have hperf_pred := ih (j - 1) (by omega) hj_pred_start hj_pred_end
      have hscoot_pred := hscoot (j - 1) hj_pred_start (by omega)
      have hshift := scoot_kStepVector w (j - 1) k hk hscoot_pred
      have : j - 1 + 1 = j := by omega
      rw [this] at hshift
      rw [← hshift, hperf_pred]

/-- Corollary: The scooting argument - a perfect interval can be moved across a chunk
    while remaining perfect, because the step to its right matches its first step. -/
lemma scoot_perfect_interval [NeZero n] (w : BinaryNecklace n)
    (_hw : BinaryNecklace.isMOS w) (x : BinaryStep)
    (g : Multiset BinaryStep) (k : ℕ) (chunkStart chunkEnd : ℕ)
    (_hk : 0 < k) (_hkn : k < n)
    (hchunk : ∀ j, chunkStart ≤ j → j < chunkEnd → w (j : ZMod n) = x)
    (hperfStart : isPerfectAt w g k chunkStart = true) :
    ∀ j, chunkStart ≤ j → j ≤ chunkEnd - k → isPerfectAt w g k j = true := by
  -- The interval stays perfect as we scoot it across the chunk of x's
  -- because the step leaving on the left (an x) is the same as the step entering on the right
  intro j hj_start hj_end
  -- Induction on the distance from chunkStart
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases eq_or_lt_of_le hj_start with rfl | hj_gt
    · -- Base case: j = chunkStart
      exact hperfStart
    · -- Inductive case: j > chunkStart
      -- Position j - 1 is also in [chunkStart, chunkEnd - k], so it's perfect by IH
      have hj_pred_start : chunkStart ≤ j - 1 := by omega
      have hj_pred_end : j - 1 ≤ chunkEnd - k := by omega
      have hperf_pred : isPerfectAt w g k (j - 1) = true := ih (j - 1) (by omega) hj_pred_start hj_pred_end
      -- At position j - 1:
      -- - w[j-1] is in the chunk, so w[j-1] = x
      -- - w[j-1+k] is also in the chunk (since j - 1 + k < chunkEnd), so w[j-1+k] = x
      -- Since both equal x, scooting from j-1 to j preserves the multiset
      have hj_pred_lt : j - 1 < chunkEnd := by omega
      have hw_left : w (((j - 1) : ℕ) : ZMod n) = x := hchunk (j - 1) hj_pred_start hj_pred_lt
      have hj_pred_k_ge : chunkStart ≤ j - 1 + k := by omega
      have hj_pred_k_lt : j - 1 + k < chunkEnd := by omega
      have hw_right : w (((j - 1 + k) : ℕ) : ZMod n) = x := hchunk (j - 1 + k) hj_pred_k_ge hj_pred_k_lt
      -- The multiset at j equals the multiset at j-1 because we remove x and add x
      unfold isPerfectAt at hperf_pred ⊢
      rw [decide_eq_true_eq] at hperf_pred ⊢
      -- Show that the abelianization at j equals the abelianization at j-1
      -- Use j = (j - 1) + 1 to rewrite the goal
      have j_eq : j = (j - 1) + 1 := by omega
      conv_lhs => rw [j_eq]
      -- Now goal is: abelianize(slice((j-1)+1, (j-1)+1+k)) = g
      -- The key: when scooting, we remove w[j-1] and add w[j-1+k]
      -- Since both equal x, the multiset is unchanged
      have habel_eq : Necklace.abelianize (Necklace.slice w ((j - 1) + 1) ((j - 1) + 1 + k)) =
                      Necklace.abelianize (Necklace.slice w (j - 1) ((j - 1) + k)) := by
        -- slice(j-1, j-1+k) = w(j-1) :: slice(j, j-1+k)
        have hdecomp := slice_shift_decompose w (j - 1) k _hk
        -- slice(j, j+k) = slice(j, j-1+k) ++ [w(j-1+k)]
        have hextend : Necklace.slice w ((j - 1) + 1) ((j - 1) + 1 + k) =
            Necklace.slice w ((j - 1) + 1) ((j - 1) + k) ++
              [w (((j - 1) + k : ℕ) : ZMod n)] := by
          have h1 : (j - 1) + 1 + k = ((j - 1) + 1) + (k - 1) + 1 := by omega
          have h2 : (j - 1) + 1 + (k - 1) = (j - 1) + k := by omega
          rw [h1, slice_extend_end]
          simp only [← Nat.cast_add, h2]
        -- Since w(j-1) = x = w(j-1+k), the multisets are permutations
        unfold Necklace.abelianize
        rw [hextend, hdecomp, hw_left, hw_right]
        exact Multiset.coe_eq_coe.mpr List.perm_append_comm
      rw [habel_eq, hperf_pred]

/-- If exactly one position in {0,...,n-1} has kStepVector ≠ g, then countKStepVectorPerPeriod = pLen - 1.
    This is a pure counting lemma: n - 1 out of n positions satisfy the predicate. -/
private lemma countKStepVector_eq_of_unique_mismatch [NeZero n]
    (w : BinaryNecklace n) (hprim : Necklace.isPrimitive w)
    (g : ZVector BinaryStep) (k : ℕ) (j₁ : ℕ) (hj₁_lt : j₁ < n)
    (hbad : Necklace.kStepVector w j₁ k ≠ g)
    (hgood : ∀ j, j < n → j ≠ j₁ → Necklace.kStepVector w j k = g) :
    countKStepVectorPerPeriod w k g = (Necklace.period w).length - 1 := by
  unfold countKStepVectorPerPeriod
  rw [hprim]
  set P : ℕ → Bool := fun i => decide (Necklace.kStepVector w i k = g)
  change (List.range n).countP P = n - 1
  -- Generalize over the list and prove by induction
  suffices h : ∀ (l : List ℕ), l.Nodup → j₁ ∈ l →
      (∀ j ∈ l, j ≠ j₁ → Necklace.kStepVector w j k = g) →
      l.countP P = l.length - 1 by
    have := h _ List.nodup_range (List.mem_range.mpr hj₁_lt)
      (fun j hj hjne => hgood j (List.mem_range.mp hj) hjne)
    simp only [List.length_range] at this
    exact this
  intro l hl hmem hgood'
  induction l with
  | nil => simp at hmem
  | cons a t ih =>
    simp only [List.countP_cons, List.length_cons]
    rcases eq_or_ne a j₁ with rfl | hne
    · -- a = j₁: after rfl, j₁ is replaced by a everywhere
      have hP_false : P a = false := by
        change decide (Necklace.kStepVector w a k = g) = false
        exact decide_eq_false_iff_not.mpr hbad
      have ha_not_in_t : a ∉ t := (List.nodup_cons.mp hl).1
      have ht_all : t.countP P = t.length := by
        apply List.countP_eq_length.mpr
        intro i hi
        simp only [P, decide_eq_true_eq]
        exact hgood' i (List.mem_cons_of_mem _ hi) (fun h => ha_not_in_t (h ▸ hi))
      simp [hP_false, ht_all]
    · -- a ≠ j₁: predicate is true here
      have hP_true : P a = true := by
        change decide (Necklace.kStepVector w a k = g) = true
        exact decide_eq_true_eq.mpr (hgood' a List.mem_cons_self hne)
      simp only [hP_true, ite_true]
      have ht_nodup := (List.nodup_cons.mp hl).2
      have hj₁_in_t : j₁ ∈ t := (List.mem_cons.mp hmem).resolve_left (Ne.symm hne)
      have ht_count := ih ht_nodup hj₁_in_t
        (fun j hj hjne => hgood' j (List.mem_cons_of_mem _ hj) hjne)
      have ht_pos : 0 < t.length := by
        cases t with
        | nil => simp at hj₁_in_t
        | cons => simp
      omega

/-- For a primitive MOS necklace, the step counts are coprime. -/
private lemma primitive_mos_coprime_counts [NeZero n]
    (w : BinaryNecklace n) (hw : BinaryNecklace.isMOS w) (hprim : Necklace.isPrimitive w) :
    Nat.gcd (Necklace.count w BinaryStep.L) (Necklace.count w BinaryStep.s) = 1 := by
  by_contra h
  set countL := Necklace.count w BinaryStep.L
  set countS := Necklace.count w BinaryStep.s
  have hcountL_pos : 0 < countL := by
    obtain ⟨⟨i, hi⟩, _⟩ := hw.1
    show 0 < Necklace.count w BinaryStep.L
    unfold Necklace.count
    exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  have hgcd_pos : 0 < Nat.gcd countL countS := Nat.gcd_pos_of_pos_left _ hcountL_pos
  have hgcd_gt : Nat.gcd countL countS > 1 := by omega
  have hsig : BinaryNecklace.hasStepSignature w countL countS := by
    unfold BinaryNecklace.hasStepSignature BinaryNecklace.stepSignature; rfl
  have hrep := mos_repetition_of_gcd_bjorklund w hw countL countS hsig
    (Nat.gcd countL countS) rfl hgcd_gt
  obtain ⟨hdvd_n, _, hper⟩ := hrep
  have hperiod_le := Necklace.period_length_le_of_translational_period w
    (n / Nat.gcd countL countS)
    (Nat.div_pos (Nat.le_of_dvd (NeZero.pos n) hdvd_n) (by omega))
    (Nat.div_lt_self (NeZero.pos n) hgcd_gt)
    (Nat.div_dvd_of_dvd hdvd_n)
    hper
  rw [hprim] at hperiod_le
  exact absurd (Nat.div_lt_self (NeZero.pos n) hgcd_gt) (by omega)

/-- If a k-step vector appears in a primitive MOS word and has |det| = 1 with the
    letter count vector, then it appears at exactly n-1 positions per period.

    The proof follows the same double-counting + determinant argument as in
    generator_implies_p_minus_one_occurrences, but takes |det| = 1 as a hypothesis
    rather than deriving it from the prefix bijection. -/
private lemma countKStepVector_of_det [NeZero n]
    (w : BinaryNecklace n) (hw : BinaryNecklace.isMOS w) (hprim : Necklace.isPrimitive w)
    (g : ZVector BinaryStep) (k : ℕ) (hk_pos : 0 < k) (hk_lt : k < n)
    (hg_mem : g ∈ distinctKStepVectors w k)
    (hdet : g BinaryStep.L * ↑(Necklace.count w BinaryStep.s) -
            g BinaryStep.s * ↑(Necklace.count w BinaryStep.L) = 1 ∨
            g BinaryStep.L * ↑(Necklace.count w BinaryStep.s) -
            g BinaryStep.s * ↑(Necklace.count w BinaryStep.L) = -1) :
    countKStepVectorPerPeriod w k g = n - 1 := by
  -- Step 1: At most 2 varieties (MOS)
  have hk_lt_pLen : k < (Necklace.period w).length := by rw [hprim]; exact hk_lt
  have hcard_le_2 := mos_at_most_two_varieties w hw k hk_pos hk_lt_pLen
  -- Step 2: At least 2 varieties (if only 1, get translational period contradiction)
  have hcard_ge_2 : (distinctKStepVectors w k).card ≥ 2 := by
    by_contra h_lt
    push_neg at h_lt
    have hcard_eq_1 : (distinctKStepVectors w k).card = 1 := by
      have := Finset.card_pos.mpr ⟨g, hg_mem⟩; omega
    -- All k-step vectors equal g
    have hall : ∀ i : ℕ, Necklace.kStepVector w i k = g := by
      intro i
      have hmem : Necklace.kStepVector w (i % n) k ∈ distinctKStepVectors w k := by
        unfold distinctKStepVectors Necklace.allKStepVectors
        rw [List.mem_toFinset, List.mem_map]
        exact ⟨i % n, List.mem_range.mpr (Nat.mod_lt i (NeZero.pos n)), rfl⟩
      have := Finset.card_le_one.mp (by omega : (distinctKStepVectors w k).card ≤ 1)
      rw [← kStepVector_mod_n]; exact this _ hmem _ hg_mem
    -- From all equal: w(j) = w(j+k) for all j (binary alphabet argument)
    have hperiodic : ∀ j : ℕ, w (↑j : ZMod n) = w (↑(j + k) : ZMod n) := by
      intro j
      have heq_L : (Necklace.kStepVector w j k) BinaryStep.L =
          (Necklace.kStepVector w (j + 1) k) BinaryStep.L := by
        rw [hall j, hall (j + 1)]
      cases hw_j : w (↑j : ZMod n) <;> cases hw_jk : w (↑(j + k) : ZMod n)
      · rfl
      · exfalso
        have hshift := slice_L_count_shift w j k
        simp only [hw_j, hw_jk, ← Nat.cast_add, ite_true,
          if_neg (show BinaryStep.s ≠ BinaryStep.L from by decide)] at hshift
        unfold Necklace.kStepVector ZVector.ofList at heq_L
        linarith
      · exfalso
        have hshift := slice_L_count_shift w j k
        simp only [hw_j, hw_jk, ← Nat.cast_add, ite_true,
          if_neg (show BinaryStep.s ≠ BinaryStep.L from by decide)] at hshift
        unfold Necklace.kStepVector ZVector.ofList at heq_L
        linarith
      · rfl
    -- Iterate: w(j) = w(j + m*k) for all m
    have hiter : ∀ (j m : ℕ), w (↑j : ZMod n) = w (↑(j + m * k) : ZMod n) := by
      intro j m; induction m with
      | zero => simp
      | succ m ih =>
        rw [show j + (m + 1) * k = j + m * k + k from by ring]
        exact ih.trans (hperiodic (j + m * k))
    -- Bézout: gcd(k, n) is a translational period
    have hgcd_pos : 0 < Nat.gcd k n :=
      Nat.pos_of_ne_zero (by intro h; rw [Nat.gcd_eq_zero_iff] at h; omega)
    have hbez : (↑(Nat.gcd k n) : ZMod n) =
        (↑k : ZMod n) * ((Nat.gcdA k n : ℤ) : ZMod n) := by
      have := congr_arg (fun x : ℤ => (x : ZMod n)) (Nat.gcd_eq_gcd_ab k n)
      push_cast at this; rwa [ZMod.natCast_self, zero_mul, add_zero] at this
    have hperiodic_gcd : ∀ (i : ZMod n), w i = w (i + ↑(Nat.gcd k n)) := by
      intro i
      have hi := hiter (ZMod.val i) (ZMod.val ((Nat.gcdA k n : ℤ) : ZMod n))
      rw [ZMod.natCast_zmod_val i] at hi
      rw [hi]; congr 1; push_cast
      rw [ZMod.natCast_zmod_val i,
          ZMod.natCast_zmod_val ((Nat.gcdA k n : ℤ) : ZMod n),
          mul_comm, ← hbez]
    have hgcd_le_k := Nat.le_of_dvd hk_pos (Nat.gcd_dvd_left k n)
    have hpLen_le := Necklace.period_length_le_of_translational_period w
      (Nat.gcd k n) hgcd_pos (by omega : Nat.gcd k n < n)
      (Nat.gcd_dvd_right k n) hperiodic_gcd
    rw [hprim] at hpLen_le; omega
  -- Step 3: Exactly 2 varieties
  have hcard_eq_2 : (distinctKStepVectors w k).card = 2 := by omega
  -- Step 4: Get the other variety g'
  obtain ⟨g', hg'_mem, hg'_ne⟩ : ∃ g' ∈ distinctKStepVectors w k, g' ≠ g := by
    by_contra h; push_neg at h
    have : (distinctKStepVectors w k).card ≤ 1 :=
      Finset.card_le_one.mpr (fun a ha b hb => by rw [h a ha, h b hb])
    omega
  -- Step 5: count(g) + count(g') = n (primitive word has period n)
  have hpLen_eq : (Necklace.period w).length = n := hprim
  have hsum := two_varieties_counts_sum w k g g' hg_mem hg'_mem hg'_ne.symm hcard_eq_2
  rw [hpLen_eq] at hsum
  -- Step 6: Double-counting - sum of L-counts across all positions
  have hsum_L := kStepVector_lettercount_sum_all w k BinaryStep.L
  -- Every position has kStepVector = g or g'
  have hmem_pair : ∀ i < n, Necklace.kStepVector w i k = g ∨ Necklace.kStepVector w i k = g' := by
    intro i hi
    have hmem : Necklace.kStepVector w i k ∈ distinctKStepVectors w k := by
      unfold distinctKStepVectors Necklace.allKStepVectors
      rw [List.mem_toFinset, List.mem_map]
      exact ⟨i, List.mem_range.mpr hi, rfl⟩
    have hpair : distinctKStepVectors w k = {g, g'} := by
      ext v; simp only [Finset.mem_insert, Finset.mem_singleton]; constructor
      · intro hv; by_contra hnot; push_neg at hnot
        have : ({g, g', v} : Finset _).card ≤ 2 := by
          calc _ ≤ (distinctKStepVectors w k).card :=
            Finset.card_le_card (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption)
            _ = 2 := hcard_eq_2
        have : ({g, g', v} : Finset _).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp [hg'_ne.symm, hnot.1.symm]),
              Finset.card_insert_of_notMem (by simp [hnot.2.symm]),
              Finset.card_singleton]
        omega
      · intro h; rcases h with rfl | rfl <;> assumption
    rw [hpair] at hmem; simp at hmem; exact hmem
  -- Split the double-counting sum
  have hdc : (countKStepVectorPerPeriod w k g : ℤ) * g BinaryStep.L +
      (countKStepVectorPerPeriod w k g' : ℤ) * g' BinaryStep.L =
      ↑k * ↑(Necklace.count w BinaryStep.L) := by
    -- Rewrite the sum over range n by splitting into g and g' positions
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range n)
        (fun i => Necklace.kStepVector w i k = g)] at hsum_L
    have h1 : ∑ i ∈ (Finset.range n).filter (fun i => Necklace.kStepVector w i k = g),
        (Necklace.kStepVector w i k) BinaryStep.L =
        ↑((Finset.range n).filter (fun i => Necklace.kStepVector w i k = g)).card *
        g BinaryStep.L := by
      have key : ∀ i ∈ (Finset.range n).filter (fun i => Necklace.kStepVector w i k = g),
          (Necklace.kStepVector w i k) BinaryStep.L = g BinaryStep.L := by
        intro i hi
        have : Necklace.kStepVector w i k = g := by
          simp only [Finset.mem_filter] at hi; exact hi.2
        exact congr_fun this BinaryStep.L
      have := Finset.sum_eq_card_nsmul key; rw [nsmul_eq_mul] at this; exact this
    have h2 : ∀ i ∈ (Finset.range n).filter (fun i => ¬Necklace.kStepVector w i k = g),
        Necklace.kStepVector w i k = g' := by
      intro i hi
      have ⟨hi_range, hi_ne⟩ : i < n ∧ ¬Necklace.kStepVector w i k = g := by
        simp only [Finset.mem_filter, Finset.mem_range] at hi; exact hi
      exact (hmem_pair i hi_range).resolve_left hi_ne
    have h3 : ∑ i ∈ (Finset.range n).filter (fun i => ¬Necklace.kStepVector w i k = g),
        (Necklace.kStepVector w i k) BinaryStep.L =
        ↑((Finset.range n).filter (fun i => ¬Necklace.kStepVector w i k = g)).card *
        g' BinaryStep.L := by
      have key : ∀ i ∈ (Finset.range n).filter (fun i => ¬Necklace.kStepVector w i k = g),
          (Necklace.kStepVector w i k) BinaryStep.L = g' BinaryStep.L := by
        intro i hi; exact congr_fun (h2 i hi) BinaryStep.L
      have := Finset.sum_eq_card_nsmul key; rw [nsmul_eq_mul] at this; exact this
    -- Relate filter card to countKStepVectorPerPeriod
    have hc1 : ((Finset.range n).filter (fun i => Necklace.kStepVector w i k = g)).card =
        countKStepVectorPerPeriod w k g := by
      unfold countKStepVectorPerPeriod; rw [hprim]
      simp only [Finset.card_def, Finset.filter_val, Finset.range_val,
        ← Multiset.countP_eq_card_filter]; rfl
    have hc2 : ((Finset.range n).filter (fun i => ¬Necklace.kStepVector w i k = g)).card =
        countKStepVectorPerPeriod w k g' := by
      -- The complement filter for g is exactly the filter for g' (since only 2 varieties)
      have hfilt_eq : (Finset.range n).filter (fun i => ¬Necklace.kStepVector w i k = g) =
          (Finset.range n).filter (fun i => Necklace.kStepVector w i k = g') := by
        ext i; simp only [Finset.mem_filter, Finset.mem_range]; constructor
        · intro ⟨hi, hne⟩; exact ⟨hi, (hmem_pair i hi).resolve_left hne⟩
        · intro ⟨hi, heq⟩; exact ⟨hi, by rw [heq]; exact hg'_ne⟩
      rw [hfilt_eq]; unfold countKStepVectorPerPeriod; rw [hprim]
      simp only [Finset.card_def, Finset.filter_val, Finset.range_val,
        ← Multiset.countP_eq_card_filter]; rfl
    rw [h1, h3, hc1, hc2] at hsum_L; exact_mod_cast hsum_L
  -- Step 7: |g(L) - g'(L)| = 1 (MOS property + distinct + same total count)
  have hdiff := mos_kStepVector_L_count_diff_le_one w hw k hk_pos hk_lt g g' hg_mem hg'_mem
  have hg_total : g BinaryStep.L + g BinaryStep.s = ↑k := by
    have hg_list := List.mem_toFinset.mp hg_mem
    rw [Necklace.allKStepVectors, List.mem_map] at hg_list
    obtain ⟨i, _, hg_eq⟩ := hg_list
    rw [← hg_eq]; exact_mod_cast kStepVector_total_count w i k
  have hg'_total : g' BinaryStep.L + g' BinaryStep.s = ↑k := by
    have hg'_list := List.mem_toFinset.mp hg'_mem
    rw [Necklace.allKStepVectors, List.mem_map] at hg'_list
    obtain ⟨i, _, hg'_eq⟩ := hg'_list
    rw [← hg'_eq]; exact_mod_cast kStepVector_total_count w i k
  have hL_ne : g BinaryStep.L ≠ g' BinaryStep.L := by
    intro heq; exact hg'_ne.symm (funext fun a => by cases a <;> [exact heq; linarith])
  have hdiff_eq : g BinaryStep.L - g' BinaryStep.L = 1 ∨
                  g BinaryStep.L - g' BinaryStep.L = -1 := by
    rcases hdiff with ⟨h1, h2⟩
    rcases Int.lt_or_lt_of_ne (sub_ne_zero.mpr hL_ne) with hneg | hpos
    · right; omega
    · left; omega
  -- Step 8: count(g') ≥ 1
  have hcount_g'_pos : countKStepVectorPerPeriod w k g' ≥ 1 := by
    by_contra h_lt; push_neg at h_lt
    have hzero : countKStepVectorPerPeriod w k g' = 0 := by omega
    have : countKStepVectorPerPeriod w k g = n := by omega
    -- All positions have kStepVector = g, so card = 1, contradiction
    have : (distinctKStepVectors w k).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      have ha_list := List.mem_toFinset.mp ha
      have hb_list := List.mem_toFinset.mp hb
      rw [Necklace.allKStepVectors, List.mem_map] at ha_list hb_list
      obtain ⟨ia, hia, ha_eq⟩ := ha_list
      obtain ⟨ib, hib, hb_eq⟩ := hb_list
      -- Show kStepVector at ia and ib both equal g
      have hia_lt : ia < n := List.mem_range.mp hia
      have hib_lt : ib < n := List.mem_range.mp hib
      have hia_g : Necklace.kStepVector w ia k = g := by
        by_contra h_ne
        have : Necklace.kStepVector w ia k = g' :=
          (hmem_pair ia hia_lt).resolve_left h_ne
        -- Then ia contributes to count(g'), contradicting count = 0
        have : countKStepVectorPerPeriod w k g' ≥ 1 := by
          unfold countKStepVectorPerPeriod; rw [hprim]
          apply Nat.pos_of_ne_zero; intro h0
          have := List.countP_eq_zero.mp h0
          have := this ia (List.mem_range.mpr hia_lt)
          simp [‹Necklace.kStepVector w ia k = g'›] at this
        omega
      have hib_g : Necklace.kStepVector w ib k = g := by
        by_contra h_ne
        have : Necklace.kStepVector w ib k = g' :=
          (hmem_pair ib hib_lt).resolve_left h_ne
        have : countKStepVectorPerPeriod w k g' ≥ 1 := by
          unfold countKStepVectorPerPeriod; rw [hprim]
          apply Nat.pos_of_ne_zero; intro h0
          have := List.countP_eq_zero.mp h0
          have := this ib (List.mem_range.mpr hib_lt)
          simp [‹Necklace.kStepVector w ib k = g'›] at this
        omega
      rw [← ha_eq, ← hb_eq, hia_g, hib_g]
    omega
  -- Step 9: Algebra - count(g') * Δ = -det, where |Δ| = 1 and |det| = 1
  -- From double-counting: count(g) * g(L) + count(g') * g'(L) = k * numL
  -- Substituting count(g) = n - count(g'):
  -- (n - cg') * g(L) + cg' * g'(L) = k * numL
  -- n * g(L) + cg' * (g'(L) - g(L)) = k * numL
  -- cg' * (g'(L) - g(L)) = k * numL - n * g(L) = -det
  set cg := (countKStepVectorPerPeriod w k g : ℤ) with hcg_def
  set cg' := (countKStepVectorPerPeriod w k g' : ℤ) with hcg'_def
  have hcg_sum : cg + cg' = ↑n := by simp only [hcg_def, hcg'_def]; exact_mod_cast hsum
  have halg : cg' * (g' BinaryStep.L - g BinaryStep.L) =
      ↑k * ↑(Necklace.count w BinaryStep.L) - ↑n * g BinaryStep.L := by
    have : cg = ↑n - cg' := by linarith
    rw [this] at hdc; linarith
  -- det = g(L) * numS - g(s) * numL = g(L) * n - k * numL (using g(L) + g(s) = k, numL + numS = n)
  have hcount_sum : (Necklace.count w BinaryStep.L : ℤ) + ↑(Necklace.count w BinaryStep.s) = ↑n := by
    have hsig : BinaryNecklace.hasStepSignature w
        (Necklace.count w BinaryStep.L) (Necklace.count w BinaryStep.s) := by
      unfold BinaryNecklace.hasStepSignature BinaryNecklace.stepSignature; rfl
    have := mos_length_eq_sum w _ _ hsig; exact_mod_cast this.symm
  have hdet_eq_neg : g BinaryStep.L * ↑(Necklace.count w BinaryStep.s) -
      g BinaryStep.s * ↑(Necklace.count w BinaryStep.L) =
      g BinaryStep.L * ↑n - ↑k * ↑(Necklace.count w BinaryStep.L) := by
    have hgs : g BinaryStep.s = ↑k - g BinaryStep.L := by linarith
    have hnumS : (↑(Necklace.count w BinaryStep.s) : ℤ) =
        ↑n - ↑(Necklace.count w BinaryStep.L) := by linarith
    rw [hgs, hnumS]; ring
  -- So cg' * Δ = -(det) where Δ = g'(L) - g(L) = ±1 and det = ±1
  have halg2 : cg' * (g' BinaryStep.L - g BinaryStep.L) =
      -(g BinaryStep.L * ↑(Necklace.count w BinaryStep.s) -
        g BinaryStep.s * ↑(Necklace.count w BinaryStep.L)) := by
    rw [hdet_eq_neg]; linarith
  -- Since |Δ| = 1 and |det| = 1: |cg'| = 1
  have hcg'_eq_one : cg' = 1 := by
    rcases hdiff_eq with hΔ | hΔ <;> rcases hdet with hd | hd <;>
    · rw [show g' BinaryStep.L - g BinaryStep.L = -(g BinaryStep.L - g' BinaryStep.L) from by ring,
          hΔ] at halg2
      rw [hd] at halg2
      have hcg'_pos : (0 : ℤ) < cg' := by simp only [hcg'_def]; omega
      linarith
  -- Step 10: count(g) = n - 1
  have : countKStepVectorPerPeriod w k g' = 1 := by
    rw [hcg'_def] at hcg'_eq_one; exact_mod_cast hcg'_eq_one
  omega

/-- A generator of a binary word cannot be the zero vector.
    If g = 0, then all prefixes are multiples of the period vector p,
    but prefix(1) has total count 1 while k·p has total count k·pLen ≠ 1 for pLen ≥ 2. -/
lemma isGenerator_ne_zero [NeZero n] (w : BinaryNecklace n)
    (hbin : BinaryNecklace.isBinary w) (g : ZVector BinaryStep)
    (hg : IsGenerator w g) : g ≠ 0 := by
  intro hg_zero
  obtain ⟨_, r, hprefix_fwd, _⟩ := hg
  let w' := fun i => w (i + r)
  let per := Necklace.period w
  let pLen := per.length
  let pVec := ZVector.ofList per
  have hpLen_ge_2 : pLen ≥ 2 := period_length_ge_two_of_binary w hbin
  have hpLen_pos : 0 < pLen := by omega
  obtain ⟨_, k₁, hpfx1⟩ := hprefix_fwd ⟨0, hpLen_pos⟩
  have hpfx1_L : (Necklace.kStepVector w' 0 1) BinaryStep.L = k₁ * pVec BinaryStep.L := by
    have := hpfx1 BinaryStep.L
    simp only [hg_zero, ZVector.zero_apply, mul_zero, zero_add] at this
    exact this
  have hpfx1_s : (Necklace.kStepVector w' 0 1) BinaryStep.s = k₁ * pVec BinaryStep.s := by
    have := hpfx1 BinaryStep.s
    simp only [hg_zero, ZVector.zero_apply, mul_zero, zero_add] at this
    exact this
  have hpfx1_total : (Necklace.kStepVector w' 0 1) BinaryStep.L +
      (Necklace.kStepVector w' 0 1) BinaryStep.s = 1 := by
    unfold Necklace.kStepVector Necklace.slice
    simp only [Nat.add_sub_cancel_left, List.range_one, ZVector.ofList]
    cases hw'0 : w' 0 <;> simp [hw'0]
  have hpVec_total : pVec BinaryStep.L + pVec BinaryStep.s = pLen := by
    show (ZVector.ofList per) BinaryStep.L + (ZVector.ofList per) BinaryStep.s = pLen
    unfold ZVector.ofList
    have hsum := binaryStep_count_sum per
    simp only [List.count_eq_countP, List.countP_eq_length_filter] at hsum
    norm_cast
  have hk1_pLen : k₁ * pLen = 1 := by
    calc k₁ * pLen
      = k₁ * (pVec BinaryStep.L + pVec BinaryStep.s) := by rw [hpVec_total]
      _ = k₁ * pVec BinaryStep.L + k₁ * pVec BinaryStep.s := by ring
      _ = (Necklace.kStepVector w' 0 1) BinaryStep.L +
          (Necklace.kStepVector w' 0 1) BinaryStep.s := by rw [hpfx1_L, hpfx1_s]
      _ = 1 := hpfx1_total
  have hpLen_ge_2_int : (pLen : ℤ) ≥ 2 := Int.ofNat_le.mpr hpLen_ge_2
  rcases Int.lt_or_le 0 k₁ with hk1_pos | hk1_le
  · have : k₁ * pLen ≥ 1 * pLen := mul_le_mul_of_nonneg_right hk1_pos (Int.natCast_nonneg pLen)
    simp only [one_mul] at this; omega
  · have : k₁ * pLen ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hk1_le (Int.natCast_nonneg pLen)
    omega

/-- For a primitive MOS necklace, any generator has |det| = 1 with respect to the letter counts.
    That is: |g(L) * count(w,s) - g(s) * count(w,L)| = 1. -/
private lemma generator_det_abs_one [NeZero n] (w : BinaryNecklace n)
    (hw : BinaryNecklace.isMOS w) (hprim : Necklace.isPrimitive w)
    (g : ZVector BinaryStep) (hgen : IsGenerator w g) :
    g BinaryStep.L * ↑(Necklace.count w BinaryStep.s) -
    g BinaryStep.s * ↑(Necklace.count w BinaryStep.L) = 1 ∨
    g BinaryStep.L * ↑(Necklace.count w BinaryStep.s) -
    g BinaryStep.s * ↑(Necklace.count w BinaryStep.L) = -1 := by
  -- Step 1: From generator, get k with count(g) = n - 1
  obtain ⟨k, hk_pos, hk_lt_pLen, hcount⟩ := generator_implies_p_minus_one_occurrences w hw g hgen
  rw [hprim] at hk_lt_pLen hcount
  -- Step 2: g ∈ distinctKStepVectors w k (count > 0 means it appears)
  have hg_mem : g ∈ distinctKStepVectors w k := by
    by_contra h_not_mem
    have : countKStepVectorPerPeriod w k g = 0 := by
      unfold countKStepVectorPerPeriod; rw [hprim]
      apply List.countP_eq_zero.mpr
      intro i hi; simp only [decide_eq_true_eq]
      intro heq; exact h_not_mem (by
        unfold distinctKStepVectors Necklace.allKStepVectors
        rw [List.mem_toFinset, List.mem_map]
        exact ⟨i, hi, heq⟩)
    omega
  -- Step 3: Exactly 2 varieties (MOS ≤ 2, count < n means ≥ 2)
  have hcard_le_2 := mos_at_most_two_varieties w hw k hk_pos (by rw [hprim]; exact hk_lt_pLen)
  have hcard_ge_2 : (distinctKStepVectors w k).card ≥ 2 := by
    by_contra h_lt; push_neg at h_lt
    have hcard_eq_1 : (distinctKStepVectors w k).card = 1 := by
      have := Finset.card_pos.mpr ⟨g, hg_mem⟩; omega
    have hall : ∀ i < n, Necklace.kStepVector w i k = g := by
      intro i hi
      exact Finset.card_le_one.mp (by omega) _
        (by unfold distinctKStepVectors Necklace.allKStepVectors
            rw [List.mem_toFinset, List.mem_map]; exact ⟨i, List.mem_range.mpr hi, rfl⟩)
        _ hg_mem
    have : countKStepVectorPerPeriod w k g = n := by
      unfold countKStepVectorPerPeriod; rw [hprim]
      show (List.range n).countP (fun i => decide (Necklace.kStepVector w i k = g)) = n
      rw [show (List.range n).countP (fun i => decide (Necklace.kStepVector w i k = g)) =
          (List.range n).length from
        List.countP_eq_length.mpr (fun i hi => by simp [hall i (List.mem_range.mp hi)])]
      exact List.length_range
    omega
  have hcard_eq_2 : (distinctKStepVectors w k).card = 2 := by omega
  -- Step 4: Get g' ≠ g
  obtain ⟨g', hg'_mem, hg'_ne⟩ : ∃ g' ∈ distinctKStepVectors w k, g' ≠ g := by
    by_contra h; push_neg at h
    have : (distinctKStepVectors w k).card ≤ 1 :=
      Finset.card_le_one.mpr (fun a ha b hb => by rw [h a ha, h b hb])
    omega
  -- Step 5: count(g) + count(g') = n, so count(g') = 1
  have hsum := two_varieties_counts_sum w k g g' hg_mem hg'_mem hg'_ne.symm hcard_eq_2
  rw [hprim] at hsum
  have hcount_g' : countKStepVectorPerPeriod w k g' = 1 := by omega
  -- Step 6: Every kStepVector is g or g'
  have hmem_pair : ∀ i < n, Necklace.kStepVector w i k = g ∨ Necklace.kStepVector w i k = g' := by
    intro i hi
    have hmem : Necklace.kStepVector w i k ∈ distinctKStepVectors w k := by
      unfold distinctKStepVectors Necklace.allKStepVectors
      rw [List.mem_toFinset, List.mem_map]; exact ⟨i, List.mem_range.mpr hi, rfl⟩
    have hpair : distinctKStepVectors w k = {g, g'} := by
      ext v; simp only [Finset.mem_insert, Finset.mem_singleton]; constructor
      · intro hv; by_contra hnot; push_neg at hnot
        have : ({g, g', v} : Finset _).card ≤ 2 :=
          calc _ ≤ (distinctKStepVectors w k).card :=
            Finset.card_le_card (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption)
            _ = 2 := hcard_eq_2
        have : ({g, g', v} : Finset _).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp [hg'_ne.symm, hnot.1.symm]),
              Finset.card_insert_of_notMem (by simp [hnot.2.symm]),
              Finset.card_singleton]
        omega
      · intro h; rcases h with rfl | rfl <;> assumption
    rw [hpair] at hmem; simp at hmem; exact hmem
  -- Step 7: Double-counting: (n-1)*g(L) + g'(L) = k * numL
  have hsum_L := kStepVector_lettercount_sum_all w k BinaryStep.L
  have hdc : ((n - 1 : ℕ) : ℤ) * g BinaryStep.L + g' BinaryStep.L =
      ↑k * ↑(Necklace.count w BinaryStep.L) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range n)
        (fun i => Necklace.kStepVector w i k = g)] at hsum_L
    have h1 : ∑ i ∈ (Finset.range n).filter (fun i => Necklace.kStepVector w i k = g),
        (Necklace.kStepVector w i k) BinaryStep.L =
        ↑((Finset.range n).filter (fun i => Necklace.kStepVector w i k = g)).card *
        g BinaryStep.L := by
      have := Finset.sum_eq_card_nsmul (s := (Finset.range n).filter
        (fun i => Necklace.kStepVector w i k = g)) (fun i hi => by
        show (Necklace.kStepVector w i k) BinaryStep.L = g BinaryStep.L
        have heq : Necklace.kStepVector w i k = g := (Finset.mem_filter.mp hi).2
        rw [heq])
      rw [nsmul_eq_mul] at this; exact this
    have h2 : ∀ i ∈ (Finset.range n).filter (fun i => ¬Necklace.kStepVector w i k = g),
        Necklace.kStepVector w i k = g' := by
      intro i hi
      have ⟨hi_range, hi_ne⟩ := Finset.mem_filter.mp hi
      exact (hmem_pair i (Finset.mem_range.mp hi_range)).resolve_left hi_ne
    have h3 : ∑ i ∈ (Finset.range n).filter (fun i => ¬Necklace.kStepVector w i k = g),
        (Necklace.kStepVector w i k) BinaryStep.L =
        ↑((Finset.range n).filter (fun i => ¬Necklace.kStepVector w i k = g)).card *
        g' BinaryStep.L := by
      have := Finset.sum_eq_card_nsmul (s := (Finset.range n).filter
        (fun i => ¬Necklace.kStepVector w i k = g)) (fun i hi => by
        show (Necklace.kStepVector w i k) BinaryStep.L = g' BinaryStep.L
        rw [h2 i hi])
      rw [nsmul_eq_mul] at this; exact this
    have hc1 : ((Finset.range n).filter (fun i => Necklace.kStepVector w i k = g)).card =
        countKStepVectorPerPeriod w k g := by
      unfold countKStepVectorPerPeriod; rw [hprim]
      simp only [Finset.card_def, Finset.filter_val, Finset.range_val,
        ← Multiset.countP_eq_card_filter]; rfl
    have hc2 : ((Finset.range n).filter (fun i => ¬Necklace.kStepVector w i k = g)).card =
        countKStepVectorPerPeriod w k g' := by
      have hfilt_eq : (Finset.range n).filter (fun i => ¬Necklace.kStepVector w i k = g) =
          (Finset.range n).filter (fun i => Necklace.kStepVector w i k = g') := by
        ext i; simp only [Finset.mem_filter, Finset.mem_range]; constructor
        · intro ⟨hi, hne⟩; exact ⟨hi, (hmem_pair i hi).resolve_left hne⟩
        · intro ⟨hi, heq⟩; exact ⟨hi, by rw [heq]; exact hg'_ne⟩
      rw [hfilt_eq]; unfold countKStepVectorPerPeriod; rw [hprim]
      simp only [Finset.card_def, Finset.filter_val, Finset.range_val,
        ← Multiset.countP_eq_card_filter]; rfl
    rw [h1, h3, hc1, hc2, hcount, hcount_g'] at hsum_L
    simp only [Nat.cast_one, one_mul] at hsum_L
    exact_mod_cast hsum_L
  -- Step 8: g(L) + g(s) = k and g'(L) + g'(s) = k (total count)
  have hg_total : g BinaryStep.L + g BinaryStep.s = ↑k := by
    have hg_list := List.mem_toFinset.mp hg_mem
    rw [Necklace.allKStepVectors, List.mem_map] at hg_list
    obtain ⟨i, _, hg_eq⟩ := hg_list
    rw [← hg_eq]; exact_mod_cast kStepVector_total_count w i k
  -- Step 9: |g'(L) - g(L)| ≤ 1 and g'(L) ≠ g(L)
  have hdiff := mos_kStepVector_L_count_diff_le_one w hw k hk_pos hk_lt_pLen g g' hg_mem hg'_mem
  have hL_ne : g BinaryStep.L ≠ g' BinaryStep.L := by
    intro heq
    have hg'_total : g' BinaryStep.L + g' BinaryStep.s = ↑k := by
      have hg'_list := List.mem_toFinset.mp hg'_mem
      rw [Necklace.allKStepVectors, List.mem_map] at hg'_list
      obtain ⟨i, _, hg'_eq⟩ := hg'_list
      rw [← hg'_eq]; exact_mod_cast kStepVector_total_count w i k
    exact hg'_ne.symm (funext fun a => by cases a <;> [exact heq; linarith])
  have hdiff_eq : g BinaryStep.L - g' BinaryStep.L = 1 ∨
                  g BinaryStep.L - g' BinaryStep.L = -1 := by
    rcases hdiff with ⟨h1, h2⟩
    rcases Int.lt_or_lt_of_ne (sub_ne_zero.mpr hL_ne) with hneg | hpos
    · right; omega
    · left; omega
  -- Step 10: Algebra - det = g(L) - g'(L), so |det| = 1
  -- count_sum : (numL : ℤ) + numS = n
  have hcount_sum : (Necklace.count w BinaryStep.L : ℤ) + ↑(Necklace.count w BinaryStep.s) = ↑n := by
    have hsig : BinaryNecklace.hasStepSignature w
        (Necklace.count w BinaryStep.L) (Necklace.count w BinaryStep.s) := by
      unfold BinaryNecklace.hasStepSignature BinaryNecklace.stepSignature; rfl
    have := mos_length_eq_sum w _ _ hsig; exact_mod_cast this.symm
  -- det = g(L)*n - k*numL
  have hdet_eq : g BinaryStep.L * ↑(Necklace.count w BinaryStep.s) -
      g BinaryStep.s * ↑(Necklace.count w BinaryStep.L) =
      g BinaryStep.L * ↑n - ↑k * ↑(Necklace.count w BinaryStep.L) := by
    have hgs : g BinaryStep.s = ↑k - g BinaryStep.L := by linarith
    have hnumS : (↑(Necklace.count w BinaryStep.s) : ℤ) =
        ↑n - ↑(Necklace.count w BinaryStep.L) := by linarith
    rw [hgs, hnumS]; ring
  -- From double-counting: g'(L) = k*numL - (n-1)*g(L)
  -- So g(L) - g'(L) = g(L) - (k*numL - (n-1)*g(L)) = n*g(L) - k*numL = det
  have hdet_eq_diff : g BinaryStep.L * ↑(Necklace.count w BinaryStep.s) -
      g BinaryStep.s * ↑(Necklace.count w BinaryStep.L) =
      g BinaryStep.L - g' BinaryStep.L := by
    rw [hdet_eq]
    have : g' BinaryStep.L = ↑k * ↑(Necklace.count w BinaryStep.L) -
        ↑(n - 1) * g BinaryStep.L := by linarith
    have hn1 : (↑(n - 1 : ℕ) : ℤ) = ↑n - 1 := by
      have := NeZero.pos n; omega
    rw [hn1] at this; linarith
  rw [hdet_eq_diff]; exact hdiff_eq

/-- List.count equals Necklace.count for toNecklace'd lists. -/
private lemma list_count_eq_necklace_count (l : List BinaryStep)
    (hlen : l.length ≠ 0) (a : BinaryStep) :
    haveI : NeZero l.length := ⟨hlen⟩
    l.count a = Necklace.count (Necklace.toNecklace l) a := by
  haveI : NeZero l.length := ⟨hlen⟩
  -- Case split to expose l.length as succ, making ZMod reduce to Fin
  match l, hlen with
  | [], h => exact absurd rfl h
  | hd :: tl, _ =>
    simp only [Necklace.count, Necklace.toNecklace, List.length_cons]
    -- Now ZMod (tl.length + 1) = Fin (tl.length + 1) definitionally
    -- Define f using getElem! to match the goal term
    set f : Fin (tl.length + 1) → BinaryStep := fun i => (hd :: tl)[i.val]!
    -- Key: Multiset.map f Finset.univ.val = ↑(hd :: tl) via Fin.univ_val_map
    have hmap : Multiset.map f Finset.univ.val = ↑(hd :: tl) := by
      have hf_eq : f = fun i => (hd :: tl)[i.val]'(i.isLt) :=
        funext fun i => getElem!_pos (hd :: tl) i.val i.isLt
      rw [hf_eq, Fin.univ_val_map]
      exact congrArg _ (List.ofFn_getElem (hd :: tl))
    rw [← Multiset.coe_count, ← hmap, Multiset.count_map]
    change Finset.card (Finset.filter (fun i => a = f i) Finset.univ) =
           Finset.card (Finset.filter (fun i => f i = a) Finset.univ)
    exact congr_arg _ (Finset.filter_congr (fun _ _ => eq_comm))

/-- The expansion count identity: numMaj = countL * large + countS * small
    where the counts are of chunk letters (L = large chunk, s = small chunk). -/
private lemma chunk_numMaj_identity [NeZero n] (x : BinaryStep) (w : BinaryNecklace n)
    (chunkSizes : List ℕ) (hsizes : chunkSizesList x w = some chunkSizes)
    (chunks : List BinaryStep) (hchunks : chunkSizesToBinary x w = some chunks)
    (_ : chunks.length ≠ 0) :
    Necklace.count w x =
    chunks.count BinaryStep.L * largeChunkSize (Necklace.count w x) (Necklace.count w (BinaryStep.otherStep x)) +
    chunks.count BinaryStep.s * smallChunkSize (Necklace.count w x) (Necklace.count w (BinaryStep.otherStep x)) := by
  set numMaj := Necklace.count w x
  set numMin := Necklace.count w (BinaryStep.otherStep x)
  -- Step 1: chunkSizes.sum = numMaj
  have hsizes_sum : chunkSizes.sum = numMaj := by
    have h1 := word_length_eq_sum_chunks x w chunkSizes hsizes
    have h2 : numMaj + numMin = n := by
      show Necklace.count w x + Necklace.count w (BinaryStep.otherStep x) = n
      unfold Necklace.count
      have huniv : (Finset.filter (fun i => w i = x) Finset.univ) ∪
          (Finset.filter (fun i => w i = BinaryStep.otherStep x) Finset.univ) = Finset.univ := by
        ext i; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        cases w i <;> cases x <;> simp [BinaryStep.otherStep]
      have hdisj : Disjoint (Finset.filter (fun i => w i = x) Finset.univ)
          (Finset.filter (fun i => w i = BinaryStep.otherStep x) Finset.univ) := by
        rw [Finset.disjoint_filter]; intro i _ h; cases x <;> simp_all [BinaryStep.otherStep]
      rw [← Finset.card_union_of_disjoint hdisj, huniv, Finset.card_univ, ZMod.card n]
    have hlen_eq : chunkSizes.length = numMin := by
      rw [chunkSizesList_length x w chunkSizes hsizes, numChunks_eq_count]
    omega
  -- Step 2: chunkSizes = chunks.map (fun step => match step with | L => large | s => small)
  have hlen_eq := chunks_length_eq_sizes x w chunkSizes hsizes chunks hchunks
  have hchunks_map : chunkSizes = chunks.map (fun step => match step with
      | BinaryStep.L => largeChunkSize numMaj numMin
      | BinaryStep.s => smallChunkSize numMaj numMin) := by
    apply List.ext_getElem
    · rw [List.length_map]; exact hlen_eq.symm
    · intro i hi _
      rw [List.getElem_map]
      exact chunk_binary_size_match x w chunkSizes hsizes chunks hchunks i hi
  -- Combine: only rewrite the LHS to avoid changing args of largeChunkSize/smallChunkSize
  conv_lhs => rw [← hsizes_sum, hchunks_map]
  exact binary_list_map_sum chunks (largeChunkSize numMaj numMin) (smallChunkSize numMaj numMin)

/-- The determinant of the lifted generator equals ±1 times the determinant of the chunked generator.
    For x = L: det_w(gLifted) = det_chunks(gChunked)
    For x = s: det_w(gLifted) = -det_chunks(gChunked)
    Combined with large = small + 1. -/
private lemma det_liftGeneratorVectorX [NeZero n] (x : BinaryStep)
    (w : BinaryNecklace n)
    (chunks : List BinaryStep) (chunkSizes : List ℕ)
    (hchunks : chunkSizesToBinary x w = some chunks)
    (hsizes : chunkSizesList x w = some chunkSizes)
    (hlen : chunks.length ≠ 0)
    (hw_chunked : haveI : NeZero chunks.length := ⟨hlen⟩;
                  BinaryNecklace.isMOS (Necklace.toNecklace chunks))
    (gChunked : ZVector BinaryStep)
    (_ : Necklace.isPrimitive w) :
    haveI : NeZero chunks.length := ⟨hlen⟩
    let gLifted := liftGeneratorVectorX x gChunked (Necklace.count w x) (Necklace.count w (BinaryStep.otherStep x))
    (gLifted BinaryStep.L * ↑(Necklace.count w BinaryStep.s) -
     gLifted BinaryStep.s * ↑(Necklace.count w BinaryStep.L) =
     gChunked BinaryStep.L * ↑(Necklace.count (Necklace.toNecklace chunks) BinaryStep.s) -
     gChunked BinaryStep.s * ↑(Necklace.count (Necklace.toNecklace chunks) BinaryStep.L)) ∨
    (gLifted BinaryStep.L * ↑(Necklace.count w BinaryStep.s) -
     gLifted BinaryStep.s * ↑(Necklace.count w BinaryStep.L) =
     -(gChunked BinaryStep.L * ↑(Necklace.count (Necklace.toNecklace chunks) BinaryStep.s) -
       gChunked BinaryStep.s * ↑(Necklace.count (Necklace.toNecklace chunks) BinaryStep.L))) := by
  haveI : NeZero chunks.length := ⟨hlen⟩
  -- Key variables
  set numMaj := Necklace.count w x with hnumMaj_def
  set numMin := Necklace.count w (BinaryStep.otherStep x) with hnumMin_def
  set large := largeChunkSize numMaj numMin
  set small := smallChunkSize numMaj numMin
  -- chunks.length = numMin
  have hm_eq : chunks.length = numMin := by
    rw [chunks_length_eq_sizes x w chunkSizes hsizes chunks hchunks,
        chunkSizesList_length x w chunkSizes hsizes, numChunks_eq_count]
  -- numMin > 0
  have hmin_pos : 0 < numMin := by omega
  -- numMaj % numMin ≠ 0 (chunked word has both L and s → two distinct chunk sizes)
  have hmod_ne : numMaj % numMin ≠ 0 := by
    intro h_eq
    -- If numMaj % numMin = 0, largeChunkSize = smallChunkSize, so all chunks mapped to L
    -- contradicting hw_chunked.1 (isBinary needs ∃ s)
    have hlarge_eq_small : large = small := by
      change (numMaj + numMin - 1) / numMin = numMaj / numMin
      have hd := Nat.div_add_mod numMaj numMin
      rw [h_eq, Nat.add_zero] at hd -- hd : numMin * (numMaj / numMin) = numMaj
      conv_lhs => rw [← hd]
      conv_lhs => rw [show numMin * (numMaj / numMin) + numMin - 1 =
          (numMin - 1) + numMin * (numMaj / numMin) from by omega]
      rw [Nat.add_mul_div_left _ _ hmin_pos]
      have : (numMin - 1) / numMin = 0 := Nat.div_eq_of_lt (by omega)
      omega
    -- All sizes equal small (since large = small), so toFinset has ≤ 1 element
    have hsizes_eq : ∀ i (hi : i < chunkSizes.length), chunkSizes[i] = small := by
      intro i hi
      have hic : i < chunks.length := by
        rw [chunks_length_eq_sizes x w chunkSizes hsizes chunks hchunks]; exact hi
      have hmatch := chunk_binary_size_match x w chunkSizes hsizes chunks hchunks i hi
      cases hv : chunks[i]'hic <;> simp only [hv] at hmatch
      · rw [hmatch]; exact hlarge_eq_small  -- L case: size = large = small
      · exact hmatch  -- s case: size = small
    have hsizes_card : chunkSizes.toFinset.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [List.mem_toFinset] at ha hb
      obtain ⟨ia, hia, rfl⟩ := List.mem_iff_getElem.mp ha
      obtain ⟨ib, hib, rfl⟩ := List.mem_iff_getElem.mp hb
      exact (hsizes_eq ia hia).trans (hsizes_eq ib hib).symm
    -- Unfold chunkSizesToBinary: in the [_] branch, all chunks are L
    have hall_L : ∀ b ∈ chunks, b = BinaryStep.L := by
      unfold chunkSizesToBinary at hchunks
      simp only [hsizes] at hchunks
      change (match chunkSizes.toFinset.toList with
        | [_] => some (chunkSizes.map (fun _ => BinaryStep.L))
        | [a, b] => if a + 1 = b || b + 1 = a then
            some (chunkSizes.map (fun s => if s = min a b then BinaryStep.s else BinaryStep.L))
          else none
        | _ => none) = some chunks at hchunks
      split at hchunks
      · intro b hb
        rw [← Option.some.inj hchunks] at hb
        simp at hb; exact hb.2
      · exfalso
        rename_i _ _ h_tolist
        have : chunkSizes.toFinset.toList.length = 2 := by rw [h_tolist]; simp
        rw [Finset.length_toList] at this; omega
      · cases hchunks
    -- But hw_chunked says chunks has an s element
    obtain ⟨j, hjs⟩ := hw_chunked.1.2
    have hj_L : (Necklace.toNecklace chunks) j = BinaryStep.L := by
      apply hall_L
      simp only [Necklace.toNecklace]
      rw [getElem!_pos chunks j.val (ZMod.val_lt j)]
      exact List.getElem_mem (ZMod.val_lt j)
    rw [hj_L] at hjs; exact BinaryStep.noConfusion hjs
  -- large = small + 1
  have hlarge : (large : ℤ) = ↑small + 1 := by
    exact_mod_cast largeChunk_eq_smallChunk_add_one numMaj numMin hmin_pos hmod_ne
  -- Expansion identity with List.count
  have h_decomp := chunk_numMaj_identity x w chunkSizes hsizes chunks hchunks hlen
  -- Convert List.count to Necklace.count
  have h_cL : chunks.count BinaryStep.L = Necklace.count (Necklace.toNecklace chunks) BinaryStep.L :=
    list_count_eq_necklace_count chunks hlen BinaryStep.L
  have h_cS : chunks.count BinaryStep.s = Necklace.count (Necklace.toNecklace chunks) BinaryStep.s :=
    list_count_eq_necklace_count chunks hlen BinaryStep.s
  -- Binary exhaustion: countL + countS = chunks.length = numMin
  have h_binary : (↑(Necklace.count (Necklace.toNecklace chunks) BinaryStep.L) : ℤ) +
      ↑(Necklace.count (Necklace.toNecklace chunks) BinaryStep.s) = ↑numMin := by
    have := binaryStep_count_sum chunks
    rw [h_cL, h_cS] at this; exact_mod_cast this.trans hm_eq
  -- Expansion identity with Necklace.count (in ℤ)
  have h_numMaj : (↑numMaj : ℤ) =
      ↑(Necklace.count (Necklace.toNecklace chunks) BinaryStep.L) * ↑large +
      ↑(Necklace.count (Necklace.toNecklace chunks) BinaryStep.s) * ↑small := by
    rw [← h_cL, ← h_cS]; exact_mod_cast h_decomp
  -- Case split on x
  cases x with
  | L =>
    left
    show (gChunked BinaryStep.L * ↑large + gChunked BinaryStep.s * ↑small) *
        ↑(Necklace.count w BinaryStep.s) -
        (gChunked BinaryStep.L + gChunked BinaryStep.s) *
        ↑(Necklace.count w BinaryStep.L) =
        gChunked BinaryStep.L * ↑(Necklace.count (Necklace.toNecklace chunks) BinaryStep.s) -
        gChunked BinaryStep.s * ↑(Necklace.count (Necklace.toNecklace chunks) BinaryStep.L)
    -- count(w, s) = numMin (since x = L, otherStep L = s)
    -- count(w, L) = numMaj (since x = L)
    have hws : Necklace.count w BinaryStep.s = numMin := by
      simp only [hnumMin_def, BinaryStep.otherStep]
    have hwL : Necklace.count w BinaryStep.L = numMaj := rfl
    rw [hws, hwL]
    -- Substitute and close with linarith
    set cL := (↑(Necklace.count (Necklace.toNecklace chunks) BinaryStep.L) : ℤ)
    set cS := (↑(Necklace.count (Necklace.toNecklace chunks) BinaryStep.s) : ℤ)
    rw [show (↑numMaj : ℤ) = cL * ↑large + cS * ↑small from h_numMaj,
        show (↑large : ℤ) = ↑small + 1 from hlarge,
        show (↑numMin : ℤ) = cL + cS from by linarith [h_binary]]
    ring
  | s =>
    right
    show (gChunked BinaryStep.L + gChunked BinaryStep.s) *
        ↑(Necklace.count w BinaryStep.s) -
        (gChunked BinaryStep.L * ↑large + gChunked BinaryStep.s * ↑small) *
        ↑(Necklace.count w BinaryStep.L) =
        -(gChunked BinaryStep.L * ↑(Necklace.count (Necklace.toNecklace chunks) BinaryStep.s) -
          gChunked BinaryStep.s * ↑(Necklace.count (Necklace.toNecklace chunks) BinaryStep.L))
    -- count(w, s) = numMaj (since x = s)
    -- count(w, L) = numMin (since x = s, otherStep s = L)
    have hws : Necklace.count w BinaryStep.s = numMaj := rfl
    have hwL : Necklace.count w BinaryStep.L = numMin := by
      simp only [hnumMin_def, BinaryStep.otherStep]
    rw [hws, hwL]
    set cL := (↑(Necklace.count (Necklace.toNecklace chunks) BinaryStep.L) : ℤ)
    set cS := (↑(Necklace.count (Necklace.toNecklace chunks) BinaryStep.s) : ℤ)
    rw [show (↑numMaj : ℤ) = cL * ↑large + cS * ↑small from h_numMaj,
        show (↑large : ℤ) = ↑small + 1 from hlarge,
        show (↑numMin : ℤ) = cL + cS from by linarith [h_binary]]
    ring

/-- Main theorem: Generators reflect under expansion.
    If the chunked word has a generator, and the expansion is a MOS, then the expanded word
    also has a generator built from the lifted intervals.

    Proof outline:
    1. The generator in the chunked word spans k chunks
    2. When lifted to the original word, it spans the total steps in k chunks
    3. Perfect intervals can be "scooted" within a chunk (same letter throughout)
    4. When crossing a chunk boundary, perfect stays perfect (scooting argument)
    5. Only one position is imperfect, so the lifted interval is a generator -/
theorem generator_reflects_under_expansion_L (n : ℕ) [NeZero n] (w : BinaryNecklace n)
    (hw : BinaryNecklace.isMOS w) (hprim : Necklace.isPrimitive w) (x : BinaryStep)
    (chunks : List BinaryStep) (chunkSizes : List ℕ)
    (hchunks : chunkSizesToBinary x w = some chunks)
    (hsizes : chunkSizesList x w = some chunkSizes)
    (hlen : chunks.length ≠ 0)
    (_ : hasMoreLs w)  -- More L's than s's
    (hw_chunked : haveI : NeZero chunks.length := ⟨hlen⟩;
                  BinaryNecklace.isMOS (Necklace.toNecklace chunks))
    (hgenChunked : haveI : NeZero chunks.length := ⟨hlen⟩;
                   HasGenerator (Necklace.toNecklace chunks))
    (hprim_chunked : haveI : NeZero chunks.length := ⟨hlen⟩;
                     Necklace.isPrimitive (Necklace.toNecklace chunks)) :
    HasGenerator w := by
  haveI : NeZero chunks.length := ⟨hlen⟩

  -- Step 1: Extract the generator from the chunked word
  obtain ⟨gChunked, hgenChunked'⟩ := hgenChunked
  have hgChunked_ne_zero := isGenerator_ne_zero _ hw_chunked.1 gChunked hgenChunked'

  -- Step 2: Get rotation offset r from chunk_word_structure
  obtain ⟨r, _hr_lt, hboundary, hchunk_vals⟩ := chunk_word_structure x w chunkSizes hsizes

  -- Step 3: Compute the lifted generator using production rules
  let numMaj := Necklace.count w x
  let numMin := Necklace.count w (BinaryStep.otherStep x)
  let gLifted := liftGeneratorVectorX x gChunked numMaj numMin

  use gLifted

  -- Extract kChunked and iChunked from the generator
  obtain ⟨⟨kChunked, hkChunked_lt, iChunked, hgChunked_appears⟩, hgenChunked_rot⟩ := hgenChunked'
  have hchunks_sizes_len := chunks_length_eq_sizes x w chunkSizes hsizes chunks hchunks
  have htotal := chunkBoundaryAt_total x w chunkSizes hsizes
  have hiChunked_lt : iChunked.val < chunkSizes.length := hchunks_sizes_len ▸ iChunked.isLt
  have hpLen_le : (Necklace.period (Necklace.toNecklace chunks)).length ≤ chunks.length :=
    Necklace.period_length_le_n (Necklace.toNecklace chunks)
  have hkChunked_lt_len : kChunked < chunkSizes.length := by omega

  -- Strategy: use p_minus_one_occurrences_implies_generator.
  -- We need kLifted with 0 < kLifted < n and countKStepVectorPerPeriod = n - 1.

  by_cases hwrap : iChunked.val + kChunked ≤ chunkSizes.length
  · -- Non-wrapping case
    by_cases hk0 : kChunked = 0
    · -- Degenerate case: kChunked = 0 means gChunked is the zero vector.
      -- This cannot arise for a genuine generator of a binary word.
      exfalso; exact hgChunked_ne_zero (by
        rw [← hgChunked_appears, hk0]
        unfold Necklace.kStepVector Necklace.slice
        simp only [Nat.add_zero, Nat.sub_self, List.range_zero]
        rfl)
    · -- Main case: kChunked > 0
      have hkChunked_pos : 0 < kChunked := Nat.pos_of_ne_zero hk0
      apply p_minus_one_occurrences_implies_generator w hw gLifted
        (liftedKStepSize chunkSizes iChunked.val kChunked)
      · -- 0 < kLifted
        exact liftedKStepSize_pos chunkSizes iChunked.val kChunked hkChunked_pos hwrap
      · -- kLifted < period length
        rw [hprim]
        exact liftedKStepSize_lt_n x w chunkSizes hsizes _ _
            hkChunked_pos hwrap (by intro ⟨h1, h2⟩; omega)
      · -- countKStepVectorPerPeriod w kLifted gLifted = pLen - 1
        -- Use determinant approach: |det(gLifted)| = 1 implies count = n - 1
        rw [show (Necklace.period w).length = n from hprim]
        have hkLifted_pos := liftedKStepSize_pos chunkSizes iChunked.val kChunked hkChunked_pos hwrap
        have hkLifted_lt := liftedKStepSize_lt_n x w chunkSizes hsizes _ _
            hkChunked_pos hwrap (by intro ⟨h1, h2⟩; omega)
        -- gLifted appears at position (r + boundary(iChunked)) via boundary_eq_lift
        have hgLifted_appears : Necklace.kStepVector w
            ((r + chunkBoundaryAt chunkSizes iChunked.val) % n)
            (liftedKStepSize chunkSizes iChunked.val kChunked) = gLifted := by
          rw [kStepVector_mod_n]
          have := kStepVector_boundary_eq_lift x w chunks chunkSizes hchunks hsizes hlen r
              hboundary hchunk_vals iChunked.val kChunked hwrap
          simp only [hgChunked_appears] at this
          exact this
        have hg_mem : gLifted ∈ distinctKStepVectors w
            (liftedKStepSize chunkSizes iChunked.val kChunked) := by
          unfold distinctKStepVectors Necklace.allKStepVectors
          rw [List.mem_toFinset, List.mem_map]
          exact ⟨(r + chunkBoundaryAt chunkSizes iChunked.val) % n,
            List.mem_range.mpr (Nat.mod_lt _ (NeZero.pos n)),
            hgLifted_appears⟩
        -- |det(gLifted)| = 1 from generator_det_abs_one on chunked word + lifting identity
        have hdet : gLifted BinaryStep.L * ↑(Necklace.count w BinaryStep.s) -
            gLifted BinaryStep.s * ↑(Necklace.count w BinaryStep.L) = 1 ∨
            gLifted BinaryStep.L * ↑(Necklace.count w BinaryStep.s) -
            gLifted BinaryStep.s * ↑(Necklace.count w BinaryStep.L) = -1 := by
          have hdet_chunked := generator_det_abs_one (Necklace.toNecklace chunks)
            hw_chunked hprim_chunked gChunked ⟨⟨kChunked, hkChunked_lt, iChunked, hgChunked_appears⟩, hgenChunked_rot⟩
          have hdet_lift := det_liftGeneratorVectorX x w chunks chunkSizes hchunks hsizes
            hlen hw_chunked gChunked hprim
          rcases hdet_lift with hpos | hneg <;> rcases hdet_chunked with hc1 | hcn1
          · left; rw [hpos, hc1]
          · right; rw [hpos, hcn1]
          · right; rw [hneg, hc1]
          · left; rw [hneg, hcn1]; ring
        exact countKStepVector_of_det w hw hprim gLifted _ hkLifted_pos hkLifted_lt hg_mem hdet
  · -- Wrapping case (iChunked + kChunked > chunkSizes.length)
    push_neg at hwrap
    have hkChunked_pos : 0 < kChunked := by omega
    apply p_minus_one_occurrences_implies_generator w hw gLifted
      ((n - chunkBoundaryAt chunkSizes iChunked.val) +
       chunkBoundaryAt chunkSizes (iChunked.val + kChunked - chunkSizes.length))
    · -- 0 < kLifted
      have hBi_lt_n : chunkBoundaryAt chunkSizes iChunked.val < n := by
        rw [← htotal]
        exact chunkBoundaryAt_strict_mono chunkSizes _ _ hiChunked_lt (le_refl _)
      omega
    · -- kLifted < period length
      rw [hprim]
      have hik_sub_lt : iChunked.val + kChunked - chunkSizes.length < iChunked.val := by omega
      have := chunkBoundaryAt_strict_mono chunkSizes _ _ hik_sub_lt (by omega)
      have hBi_le_n : chunkBoundaryAt chunkSizes iChunked.val ≤ n := by
        rw [← htotal]; exact chunkBoundaryAt_mono _ _ _ (by omega) (le_refl _)
      omega
    · -- countKStepVectorPerPeriod w kLifted gLifted = pLen - 1
      set kLifted := (n - chunkBoundaryAt chunkSizes iChunked.val) +
        chunkBoundaryAt chunkSizes (iChunked.val + kChunked - chunkSizes.length) with hkLifted_def
      rw [show (Necklace.period w).length = n from hprim]
      have hBi_lt_n : chunkBoundaryAt chunkSizes iChunked.val < n := by
        rw [← htotal]
        exact chunkBoundaryAt_strict_mono chunkSizes _ _ hiChunked_lt (le_refl _)
      have hkLifted_pos : 0 < kLifted := by omega
      have hik_sub_lt : iChunked.val + kChunked - chunkSizes.length < iChunked.val := by omega
      have hkLifted_lt : kLifted < n := by
        have := chunkBoundaryAt_strict_mono chunkSizes _ _ hik_sub_lt (by omega)
        have hBi_le_n : chunkBoundaryAt chunkSizes iChunked.val ≤ n := by
          rw [← htotal]; exact chunkBoundaryAt_mono _ _ _ (by omega) (le_refl _)
        omega
      -- gLifted appears via boundary_eq_lift_wrapping
      have hgLifted_appears : Necklace.kStepVector w
          ((r + chunkBoundaryAt chunkSizes iChunked.val) % n) kLifted = gLifted := by
        rw [kStepVector_mod_n]
        have := kStepVector_boundary_eq_lift_wrapping x w chunks chunkSizes hchunks hsizes hlen r
            hboundary hchunk_vals iChunked.val kChunked hiChunked_lt hkChunked_pos
            (by omega : kChunked ≤ chunkSizes.length)
        simp only [show iChunked.val + kChunked ≤ chunkSizes.length ↔ False from ⟨by omega, False.elim⟩,
          hgChunked_appears] at this
        exact this
      have hg_mem : gLifted ∈ distinctKStepVectors w kLifted := by
        unfold distinctKStepVectors Necklace.allKStepVectors
        rw [List.mem_toFinset, List.mem_map]
        exact ⟨(r + chunkBoundaryAt chunkSizes iChunked.val) % n,
          List.mem_range.mpr (Nat.mod_lt _ (NeZero.pos n)),
          hgLifted_appears⟩
      have hdet : gLifted BinaryStep.L * ↑(Necklace.count w BinaryStep.s) -
          gLifted BinaryStep.s * ↑(Necklace.count w BinaryStep.L) = 1 ∨
          gLifted BinaryStep.L * ↑(Necklace.count w BinaryStep.s) -
          gLifted BinaryStep.s * ↑(Necklace.count w BinaryStep.L) = -1 := by
        have hdet_chunked := generator_det_abs_one (Necklace.toNecklace chunks)
          hw_chunked hprim_chunked gChunked ⟨⟨kChunked, hkChunked_lt, iChunked, hgChunked_appears⟩, hgenChunked_rot⟩
        have hdet_lift := det_liftGeneratorVectorX x w chunks chunkSizes hchunks hsizes
          hlen hw_chunked gChunked hprim
        rcases hdet_lift with hpos | hneg <;> rcases hdet_chunked with hc1 | hcn1
        · left; rw [hpos, hc1]
        · right; rw [hpos, hcn1]
        · right; rw [hneg, hc1]
        · left; rw [hneg, hcn1]; ring
      exact countKStepVector_of_det w hw hprim gLifted _ hkLifted_pos hkLifted_lt hg_mem hdet

/-- Symmetric version for when there are more s's than L's (chunking by s).
    The proof follows the same structure as _L, using liftGeneratorVectorX x
    which automatically handles the swapped roles of L and s. -/
theorem generator_reflects_under_expansion_s (n : ℕ) [NeZero n] (w : BinaryNecklace n)
    (hw : BinaryNecklace.isMOS w) (hprim : Necklace.isPrimitive w) (x : BinaryStep)
    (chunks : List BinaryStep) (chunkSizes : List ℕ)
    (hchunks : chunkSizesToBinary x w = some chunks)
    (hsizes : chunkSizesList x w = some chunkSizes)
    (hlen : chunks.length ≠ 0)
    (_ : ¬hasMoreLs w)  -- More s's than L's (or equal)
    (hw_chunked : haveI : NeZero chunks.length := ⟨hlen⟩;
                  BinaryNecklace.isMOS (Necklace.toNecklace chunks))
    (hgenChunked : haveI : NeZero chunks.length := ⟨hlen⟩;
                   HasGenerator (Necklace.toNecklace chunks))
    (hprim_chunked : haveI : NeZero chunks.length := ⟨hlen⟩;
                     Necklace.isPrimitive (Necklace.toNecklace chunks)) :
    HasGenerator w := by
  haveI : NeZero chunks.length := ⟨hlen⟩
  obtain ⟨gChunked, hgenChunked'⟩ := hgenChunked
  have hgChunked_ne_zero := isGenerator_ne_zero _ hw_chunked.1 gChunked hgenChunked'
  obtain ⟨r, _hr_lt, hboundary, hchunk_vals⟩ := chunk_word_structure x w chunkSizes hsizes
  let numMaj := Necklace.count w x
  let numMin := Necklace.count w (BinaryStep.otherStep x)
  let gLifted := liftGeneratorVectorX x gChunked numMaj numMin
  use gLifted
  obtain ⟨⟨kChunked, hkChunked_lt, iChunked, hgChunked_appears⟩, hgenChunked_rot⟩ := hgenChunked'
  have hchunks_sizes_len := chunks_length_eq_sizes x w chunkSizes hsizes chunks hchunks
  have htotal := chunkBoundaryAt_total x w chunkSizes hsizes
  have hiChunked_lt : iChunked.val < chunkSizes.length := hchunks_sizes_len ▸ iChunked.isLt
  have hpLen_le : (Necklace.period (Necklace.toNecklace chunks)).length ≤ chunks.length :=
    Necklace.period_length_le_n (Necklace.toNecklace chunks)
  have hkChunked_lt_len : kChunked < chunkSizes.length := by omega
  by_cases hwrap : iChunked.val + kChunked ≤ chunkSizes.length
  · by_cases hk0 : kChunked = 0
    · exfalso; exact hgChunked_ne_zero (by
        rw [← hgChunked_appears, hk0]
        unfold Necklace.kStepVector Necklace.slice
        simp only [Nat.add_zero, Nat.sub_self, List.range_zero]
        rfl)
    · have hkChunked_pos : 0 < kChunked := Nat.pos_of_ne_zero hk0
      apply p_minus_one_occurrences_implies_generator w hw gLifted
        (liftedKStepSize chunkSizes iChunked.val kChunked)
      · exact liftedKStepSize_pos chunkSizes iChunked.val kChunked hkChunked_pos hwrap
      · rw [hprim]
        exact liftedKStepSize_lt_n x w chunkSizes hsizes _ _
            hkChunked_pos hwrap (by intro ⟨h1, h2⟩; omega)
      · -- countKStepVectorPerPeriod w kLifted gLifted = pLen - 1
        -- Use determinant approach: |det(gLifted)| = 1 implies count = n - 1
        rw [show (Necklace.period w).length = n from hprim]
        have hkLifted_pos := liftedKStepSize_pos chunkSizes iChunked.val kChunked hkChunked_pos hwrap
        have hkLifted_lt := liftedKStepSize_lt_n x w chunkSizes hsizes _ _
            hkChunked_pos hwrap (by intro ⟨h1, h2⟩; omega)
        have hgLifted_appears : Necklace.kStepVector w
            ((r + chunkBoundaryAt chunkSizes iChunked.val) % n)
            (liftedKStepSize chunkSizes iChunked.val kChunked) = gLifted := by
          rw [kStepVector_mod_n]
          have := kStepVector_boundary_eq_lift x w chunks chunkSizes hchunks hsizes hlen r
              hboundary hchunk_vals iChunked.val kChunked hwrap
          simp only [hgChunked_appears] at this
          exact this
        have hg_mem : gLifted ∈ distinctKStepVectors w
            (liftedKStepSize chunkSizes iChunked.val kChunked) := by
          unfold distinctKStepVectors Necklace.allKStepVectors
          rw [List.mem_toFinset, List.mem_map]
          exact ⟨(r + chunkBoundaryAt chunkSizes iChunked.val) % n,
            List.mem_range.mpr (Nat.mod_lt _ (NeZero.pos n)),
            hgLifted_appears⟩
        have hdet : gLifted BinaryStep.L * ↑(Necklace.count w BinaryStep.s) -
            gLifted BinaryStep.s * ↑(Necklace.count w BinaryStep.L) = 1 ∨
            gLifted BinaryStep.L * ↑(Necklace.count w BinaryStep.s) -
            gLifted BinaryStep.s * ↑(Necklace.count w BinaryStep.L) = -1 := by
          have hdet_chunked := generator_det_abs_one (Necklace.toNecklace chunks)
            hw_chunked hprim_chunked gChunked ⟨⟨kChunked, hkChunked_lt, iChunked, hgChunked_appears⟩, hgenChunked_rot⟩
          have hdet_lift := det_liftGeneratorVectorX x w chunks chunkSizes hchunks hsizes
            hlen hw_chunked gChunked hprim
          rcases hdet_lift with hpos | hneg <;> rcases hdet_chunked with hc1 | hcn1
          · left; rw [hpos, hc1]
          · right; rw [hpos, hcn1]
          · right; rw [hneg, hc1]
          · left; rw [hneg, hcn1]; ring
        exact countKStepVector_of_det w hw hprim gLifted _ hkLifted_pos hkLifted_lt hg_mem hdet
  · push_neg at hwrap
    have hkChunked_pos : 0 < kChunked := by omega
    apply p_minus_one_occurrences_implies_generator w hw gLifted
      ((n - chunkBoundaryAt chunkSizes iChunked.val) +
       chunkBoundaryAt chunkSizes (iChunked.val + kChunked - chunkSizes.length))
    · have hBi_lt_n : chunkBoundaryAt chunkSizes iChunked.val < n := by
        rw [← htotal]
        exact chunkBoundaryAt_strict_mono chunkSizes _ _ hiChunked_lt (le_refl _)
      omega
    · rw [hprim]
      have hik_sub_lt : iChunked.val + kChunked - chunkSizes.length < iChunked.val := by omega
      have := chunkBoundaryAt_strict_mono chunkSizes _ _ hik_sub_lt (by omega)
      have hBi_le_n : chunkBoundaryAt chunkSizes iChunked.val ≤ n := by
        rw [← htotal]; exact chunkBoundaryAt_mono _ _ _ (by omega) (le_refl _)
      omega
    · -- countKStepVectorPerPeriod w kLifted gLifted = pLen - 1
      set kLifted := (n - chunkBoundaryAt chunkSizes iChunked.val) +
        chunkBoundaryAt chunkSizes (iChunked.val + kChunked - chunkSizes.length) with hkLifted_def
      rw [show (Necklace.period w).length = n from hprim]
      have hBi_lt_n : chunkBoundaryAt chunkSizes iChunked.val < n := by
        rw [← htotal]
        exact chunkBoundaryAt_strict_mono chunkSizes _ _ hiChunked_lt (le_refl _)
      have hkLifted_pos : 0 < kLifted := by omega
      have hik_sub_lt : iChunked.val + kChunked - chunkSizes.length < iChunked.val := by omega
      have hkLifted_lt : kLifted < n := by
        have := chunkBoundaryAt_strict_mono chunkSizes _ _ hik_sub_lt (by omega)
        have hBi_le_n : chunkBoundaryAt chunkSizes iChunked.val ≤ n := by
          rw [← htotal]; exact chunkBoundaryAt_mono _ _ _ (by omega) (le_refl _)
        omega
      have hgLifted_appears : Necklace.kStepVector w
          ((r + chunkBoundaryAt chunkSizes iChunked.val) % n) kLifted = gLifted := by
        rw [kStepVector_mod_n]
        have := kStepVector_boundary_eq_lift_wrapping x w chunks chunkSizes hchunks hsizes hlen r
            hboundary hchunk_vals iChunked.val kChunked hiChunked_lt hkChunked_pos
            (by omega : kChunked ≤ chunkSizes.length)
        simp only [show iChunked.val + kChunked ≤ chunkSizes.length ↔ False from ⟨by omega, False.elim⟩,
          hgChunked_appears] at this
        exact this
      have hg_mem : gLifted ∈ distinctKStepVectors w kLifted := by
        unfold distinctKStepVectors Necklace.allKStepVectors
        rw [List.mem_toFinset, List.mem_map]
        exact ⟨(r + chunkBoundaryAt chunkSizes iChunked.val) % n,
          List.mem_range.mpr (Nat.mod_lt _ (NeZero.pos n)),
          hgLifted_appears⟩
      have hdet : gLifted BinaryStep.L * ↑(Necklace.count w BinaryStep.s) -
          gLifted BinaryStep.s * ↑(Necklace.count w BinaryStep.L) = 1 ∨
          gLifted BinaryStep.L * ↑(Necklace.count w BinaryStep.s) -
          gLifted BinaryStep.s * ↑(Necklace.count w BinaryStep.L) = -1 := by
        have hdet_chunked := generator_det_abs_one (Necklace.toNecklace chunks)
          hw_chunked hprim_chunked gChunked ⟨⟨kChunked, hkChunked_lt, iChunked, hgChunked_appears⟩, hgenChunked_rot⟩
        have hdet_lift := det_liftGeneratorVectorX x w chunks chunkSizes hchunks hsizes
          hlen hw_chunked gChunked hprim
        rcases hdet_lift with hpos | hneg <;> rcases hdet_chunked with hc1 | hcn1
        · left; rw [hpos, hc1]
        · right; rw [hpos, hcn1]
        · right; rw [hneg, hc1]
        · left; rw [hneg, hcn1]; ring
      exact countKStepVector_of_det w hw hprim gLifted _ hkLifted_pos hkLifted_lt hg_mem hdet

/-!
## Main Theorem: All MOS Scales Have Generators
-/

/-- If a necklace has a translational period d (d | n, 0 < d), then (n/d) divides
    the count of any letter. -/
private lemma count_dvd_of_translational_period [NeZero n] (w : BinaryNecklace n) (d : ℕ)
    (hd_pos : 0 < d) (hd_dvd : d ∣ n)
    (hper : ∀ i : ZMod n, w i = w (i + (d : ZMod n)))
    (a : BinaryStep) : (n / d) ∣ Necklace.count w a := by
  -- Step 1: Iterate periodicity: w i = w (i + k*d)
  have hiter : ∀ (k : ℕ) (i : ZMod n), w i = w (i + ((k * d : ℕ) : ZMod n)) := by
    intro k; induction k with
    | zero => intro i; simp
    | succ k ih =>
      intro i; rw [ih i, hper (i + ↑(k * d))]
      congr 1; push_cast; ring
  -- Step 2: w depends only on val % d
  have hmod : ∀ i : ZMod n, w i = w ((i.val % d : ℕ) : ZMod n) := by
    intro i; symm
    rw [hiter (i.val / d) ((i.val % d : ℕ) : ZMod n)]
    congr 1; rw [← Nat.cast_add]
    have : i.val % d + i.val / d * d = i.val := by
      linarith [Nat.mod_add_div i.val d, mul_comm d (i.val / d)]
    rw [this]; simp [ZMod.natCast_val, ZMod.cast_id']
  -- Step 3: Define projection f : ZMod n → Fin d
  let f : ZMod n → Fin d := fun i => ⟨i.val % d, Nat.mod_lt _ hd_pos⟩
  set q := n / d with hq_def
  have hqd : n = d * q := by
    rw [mul_comm]; exact (Nat.div_mul_cancel hd_dvd).symm
  -- Bound helper: r + k * d < n for r < d, k < q
  have hbound : ∀ (rv kv : ℕ), rv < d → kv < q → rv + kv * d < n := by
    intro rv kv hrv hkv
    calc rv + kv * d
      _ < d + kv * d := by omega
      _ = (kv + 1) * d := by ring
      _ ≤ q * d := by apply Nat.mul_le_mul_right; omega
      _ = d * q := by ring
      _ = n := hqd.symm
  -- Step 4: Fiber cardinality = q for each r : Fin d
  have fiber_card : ∀ r : Fin d,
      (Finset.filter (fun i : ZMod n => f i = r) Finset.univ).card = q := by
    intro r
    -- Bijection: Fin q → fiber(r) via k ↦ (r.val + k * d : ZMod n)
    let φ : Fin q → ZMod n := fun k => ((r.val + k.val * d : ℕ) : ZMod n)
    have hφ_inj : Function.Injective φ := by
      intro k₁ k₂ h; simp only [φ] at h
      have := congr_arg ZMod.val h
      rw [ZMod.val_natCast_of_lt (hbound _ _ r.isLt k₁.isLt),
          ZMod.val_natCast_of_lt (hbound _ _ r.isLt k₂.isLt)] at this
      -- this : r.val + k₁.val * d = r.val + k₂.val * d
      ext; exact mul_right_cancel₀ (by omega : (d : ℕ) ≠ 0) (by omega)
    have hφ_image : Finset.image φ Finset.univ =
        Finset.filter (fun i : ZMod n => f i = r) Finset.univ := by
      ext i; simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, φ, f]
      constructor
      · rintro ⟨k, rfl⟩
        ext
        simp only [ZMod.val_natCast_of_lt (hbound _ _ r.isLt k.isLt),
                    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt r.isLt]
      · intro hfi
        have hmod_eq : i.val % d = r.val := congr_arg Fin.val hfi
        refine ⟨⟨i.val / d, Nat.div_lt_of_lt_mul (by linarith [ZMod.val_lt i])⟩, ?_⟩
        have : r.val + i.val / d * d = i.val := by
          linarith [Nat.mod_add_div i.val d, mul_comm d (i.val / d), hmod_eq]
        simp only [this, ZMod.natCast_val, ZMod.cast_id', id_eq]
    rw [← hφ_image, Finset.card_image_of_injective _ hφ_inj, Finset.card_univ, Fintype.card_fin]
  -- Step 5: Decompose count by fibers
  unfold Necklace.count
  rw [show Finset.filter (fun i : ZMod n => w i = a) Finset.univ =
      Finset.biUnion (Finset.filter (fun r : Fin d => w ((r.val : ℕ) : ZMod n) = a)
        Finset.univ)
        (fun r => Finset.filter (fun i : ZMod n => f i = r) Finset.univ) from by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, f]
    constructor
    · intro hi
      exact ⟨⟨i.val % d, Nat.mod_lt _ hd_pos⟩, by rwa [← hmod i], rfl⟩
    · rintro ⟨r, hr, hir⟩
      rw [hmod i, show (i.val % d : ℕ) = r.val from congr_arg Fin.val hir]
      exact hr]
  rw [Finset.card_biUnion (by
    intro r₁ _ r₂ _ hne
    exact Finset.disjoint_filter.mpr (fun i _ h₁ h₂ => hne (h₁ ▸ h₂)))]
  rw [Finset.sum_congr rfl (fun r _ => fiber_card r)]
  simp [mul_comm]

/-- Any necklace aLbs with gcd(a, b) = 1 is primitive -/
lemma necklace_with_coprime_sig_is_primitive (n : ℕ) [NeZero n] (a : ℕ) (b : ℕ)
    (h_coprime : Nat.gcd a b = 1)
    (w : BinaryNecklace n)
    (_haL : Necklace.count w BinaryStep.L = a)
    (_hbs : Necklace.count w BinaryStep.s = b) : Necklace.isPrimitive w := by
  by_contra h_not_prim
  unfold Necklace.isPrimitive at h_not_prim
  set pLen := (Necklace.period w).length with hpLen_def
  have hpLen_le := Necklace.period_length_le_n w
  have hpLen_lt : pLen < n := by omega
  -- Period properties: isRepetitionOf w (period w) = true
  have hRep : Necklace.isRepetitionOf w (Necklace.period w) = true := by
    unfold Necklace.period
    cases hfind : ((List.range n).tail.map (Necklace.slice w 0)).find?
        (Necklace.isRepetitionOf w) with
    | some pfx => simp only [Option.getD_some]; exact List.find?_some hfind
    | none =>
      simp only [Option.getD_none]
      -- period w = slice w 0 n, which has length n, contradicting pLen < n
      have : (Necklace.slice w 0 n).length = n := Necklace.slice_length w 0 n
      unfold Necklace.period at hpLen_def
      rw [hfind, Option.getD_none] at hpLen_def
      omega
  -- pLen > 0
  have hpLen_pos : 0 < pLen := by
    unfold Necklace.isRepetitionOf at hRep
    simp only [ne_eq] at hRep
    split at hRep
    · exact absurd hRep Bool.false_ne_true
    · omega
  -- pLen | n
  have hpLen_dvd : pLen ∣ n := by
    unfold Necklace.isRepetitionOf at hRep
    simp only [ne_eq] at hRep
    split at hRep
    · exact absurd hRep Bool.false_ne_true
    · split at hRep
      · exact absurd hRep Bool.false_ne_true
      · rename_i _ h2; push_neg at h2
        exact Nat.dvd_of_mod_eq_zero h2
  -- period w = slice w 0 pLen
  have hperiod_is_slice : Necklace.period w = Necklace.slice w 0 pLen := by
    have ⟨l, hl⟩ : ∃ l, Necklace.period w = Necklace.slice w 0 l := by
      unfold Necklace.period
      cases hfind : ((List.range n).tail.map (Necklace.slice w 0)).find?
          (Necklace.isRepetitionOf w) with
      | some pfx =>
        simp only [Option.getD_some]
        have hmem := List.mem_of_find?_eq_some hfind
        rw [List.mem_map] at hmem
        obtain ⟨l, _, rfl⟩ := hmem; exact ⟨l, rfl⟩
      | none => simp only [Option.getD_none]; exact ⟨n, rfl⟩
    rw [hl]; congr 1
    have : pLen = l := by rw [hpLen_def, hl, Necklace.slice_length]; omega
    omega
  -- Pointwise matching: w(i) = (period w)[i % pLen] for i < n
  have hperiod_match : ∀ i, i < n →
      some (w ((i : ℕ) : ZMod n)) = (Necklace.period w)[i % pLen]? := by
    intro i hi
    unfold Necklace.isRepetitionOf at hRep
    simp only [ne_eq] at hRep
    split at hRep
    · exact absurd hRep Bool.false_ne_true
    · split at hRep
      · exact absurd hRep Bool.false_ne_true
      · rw [List.all_eq_true] at hRep
        have := hRep i (List.mem_range.mpr hi)
        rwa [decide_eq_true_eq] at this
  -- period[j] = w(j) for j < pLen
  have hperiod_elem : ∀ j, j < pLen →
      (Necklace.period w)[j]? = some (w ((j : ℕ) : ZMod n)) := by
    intro j hj
    rw [hperiod_is_slice]
    unfold Necklace.slice
    simp only [bind_pure_comp, Functor.map, Nat.sub_zero, Nat.cast_zero, zero_add,
          List.map_map, Function.comp, List.getElem?_map, List.getElem?_range hj, Option.map]
  -- Pointwise periodicity: w(j) = w(j % pLen)
  have hperiodic : ∀ j : ℕ, w ((j : ℕ) : ZMod n) = w ((j % pLen : ℕ) : ZMod n) := by
    intro j
    have hj_mod_n := Nat.mod_lt j (NeZero.pos n)
    have hj_mod_pLen := Nat.mod_lt j hpLen_pos
    conv_lhs => rw [show ((j : ℕ) : ZMod n) = ((j % n : ℕ) : ZMod n) from by simp []]
    have h1 := hperiod_match (j % n) hj_mod_n
    rw [Nat.mod_mod_of_dvd j hpLen_dvd] at h1
    have h2 := hperiod_elem (j % pLen) hj_mod_pLen
    rw [h2] at h1; exact Option.some_injective _ h1
  -- Translational periodicity: w(i) = w(i + pLen)
  have htrans : ∀ i : ZMod n, w i = w (i + (pLen : ZMod n)) := by
    intro i
    have h1 := hperiodic i.val
    have h2 := hperiodic (i.val + pLen)
    rw [Nat.add_mod_right] at h2
    rw [show (i.val : ZMod n) = i from by simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]] at h1
    rw [show ((i.val + pLen : ℕ) : ZMod n) = i + (pLen : ZMod n) from by
      push_cast; simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]] at h2
    rw [h1, h2]
  -- Count divisibility: (n/pLen) | count(w, L) and (n/pLen) | count(w, s)
  have hdvd_L := count_dvd_of_translational_period w pLen hpLen_pos hpLen_dvd htrans BinaryStep.L
  have hdvd_s := count_dvd_of_translational_period w pLen hpLen_pos hpLen_dvd htrans BinaryStep.s
  -- (n/pLen) | gcd(a, b) = 1
  have hdvd_gcd : (n / pLen) ∣ Nat.gcd a b :=
    Nat.dvd_gcd (_haL ▸ hdvd_L) (_hbs ▸ hdvd_s)
  rw [h_coprime] at hdvd_gcd
  -- n/pLen ≤ 1
  have hle := Nat.le_of_dvd (by omega) hdvd_gcd
  -- But n/pLen ≥ 2
  have hge : n / pLen ≥ 2 := by
    have hmul := Nat.div_mul_cancel hpLen_dvd
    have h1 := Nat.div_pos (Nat.le_of_dvd (NeZero.pos n) hpLen_dvd) hpLen_pos
    by_contra hlt; push_neg at hlt
    have : n / pLen = 1 := by omega
    rw [this] at hmul; simp at hmul; omega
  omega

/-- Chunks of a primitive MOS form a primitive necklace.
    Key idea: gcd(chunks.count L, chunks.count s) divides gcd(count w x, count w (otherStep x)) = 1. -/
private lemma chunk_primitivity [NeZero n] (x : BinaryStep) (w : BinaryNecklace n)
    (hw : BinaryNecklace.isMOS w) (hprim : Necklace.isPrimitive w)
    (sizes : List ℕ) (hsizes : chunkSizesList x w = some sizes)
    (chunks : List BinaryStep) (hchunks : chunkSizesToBinary x w = some chunks)
    (hlen : chunks.length ≠ 0) :
    haveI : NeZero chunks.length := ⟨hlen⟩
    Necklace.isPrimitive (Necklace.toNecklace chunks) := by
  haveI : NeZero chunks.length := ⟨hlen⟩
  have hcoprime_w := primitive_mos_coprime_counts w hw hprim
  have hcoprime_wx : Nat.gcd (Necklace.count w x) (Necklace.count w (BinaryStep.otherStep x)) = 1 := by
    cases x with
    | L => exact hcoprime_w
    | s => rw [BinaryStep.otherStep, Nat.gcd_comm]; exact hcoprime_w
  set numMaj := Necklace.count w x
  set numMin := Necklace.count w (BinaryStep.otherStep x)
  have hlen_eq : chunks.length = numMin := by
    rw [chunks_length_eq_sizes x w sizes hsizes chunks hchunks,
        chunkSizesList_length x w sizes hsizes, numChunks_eq_count]
  have h_bsum := binaryStep_count_sum chunks
  have h_decomp := chunk_numMaj_identity x w sizes hsizes chunks hchunks hlen
  have hd_dvd_numMaj : Nat.gcd (chunks.count BinaryStep.L) (chunks.count BinaryStep.s) ∣ numMaj := by
    change _ ∣ Necklace.count w x
    rw [h_decomp]
    exact Nat.dvd_add
      (dvd_mul_of_dvd_left (Nat.gcd_dvd_left _ _) _)
      (dvd_mul_of_dvd_left (Nat.gcd_dvd_right _ _) _)
  have hd_dvd_numMin : Nat.gcd (chunks.count BinaryStep.L) (chunks.count BinaryStep.s) ∣ numMin := by
    rw [← hlen_eq, ← h_bsum]
    exact Nat.dvd_add (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
  have hcoprime_chunks : Nat.gcd (chunks.count BinaryStep.L) (chunks.count BinaryStep.s) = 1 :=
    Nat.dvd_one.mp (hcoprime_wx ▸ Nat.dvd_gcd hd_dvd_numMaj hd_dvd_numMin)
  rw [list_count_eq_necklace_count chunks hlen BinaryStep.L,
      list_count_eq_necklace_count chunks hlen BinaryStep.s] at hcoprime_chunks
  exact necklace_with_coprime_sig_is_primitive chunks.length _ _ hcoprime_chunks
    (Necklace.toNecklace chunks) rfl rfl

/-- An nL1s word is primitive (period = n) since gcd(n-1, 1) = 1 -/
lemma nL1s_is_primitive (n : ℕ) [NeZero n] (w : BinaryNecklace n)
    (_ : BinaryNecklace.isMOS w) (hone_s : Necklace.count w BinaryStep.s = 1) :
    Necklace.isPrimitive w := by
  have hL_count : Necklace.count w BinaryStep.L = n - 1 := by
    have htotal : Necklace.count w BinaryStep.L + Necklace.count w BinaryStep.s = n := by
      unfold Necklace.count
      have huniv : (Finset.filter (fun i => w i = BinaryStep.L) Finset.univ) ∪
          (Finset.filter (fun i => w i = BinaryStep.s) Finset.univ) = Finset.univ := by
        ext i; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        cases w i <;> simp
      have hdisj : Disjoint (Finset.filter (fun i => w i = BinaryStep.L) Finset.univ)
          (Finset.filter (fun i => w i = BinaryStep.s) Finset.univ) := by
        rw [Finset.disjoint_filter]; intro i _ hL; simp_all
      rw [← Finset.card_union_of_disjoint hdisj, huniv]
      simp only [Finset.card_univ, ZMod.card n]
    omega
  have hcoprime : Nat.gcd (n - 1) 1 = 1 := Nat.gcd_one_right (n - 1)
  exact necklace_with_coprime_sig_is_primitive n (n - 1) 1 hcoprime w hL_count hone_s

/-- For a rotated nL1s word where s is at position n-1, all other positions have L -/
lemma nL1s_rotated_structure (n : ℕ) [NeZero n] (w : BinaryNecklace n)
    (hone_s : Necklace.count w BinaryStep.s = 1) (s_pos : ZMod n) (hs_pos : w s_pos = BinaryStep.s) :
    let r := s_pos + 1
    let w' := fun i => w (i + r)
    (w' (n - 1 : ZMod n) = BinaryStep.s) ∧
    (∀ i : ℕ, i < n - 1 → w' (i : ZMod n) = BinaryStep.L) := by
  intro r w'
  -- Uniqueness of the s position
  have hunique : ∀ j : ZMod n, w j = BinaryStep.s → j = s_pos := by
    intro j hj
    unfold Necklace.count at hone_s
    rw [Finset.card_eq_one] at hone_s
    obtain ⟨a, ha⟩ := hone_s
    have hj_mem : j ∈ ({a} : Finset (ZMod n)) := by
      rw [← ha]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
    have hs_mem : s_pos ∈ ({a} : Finset (ZMod n)) := by
      rw [← ha]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ s_pos, hs_pos⟩
    simp only [Finset.mem_singleton] at hj_mem hs_mem
    rw [hj_mem, hs_mem]
  constructor
  · -- w' (n-1) = w ((n-1) + s_pos + 1) = w(-1 + s_pos + 1) = w(s_pos) = s
    simp only [w', r]
    convert hs_pos using 2
    -- Goal: ↑n - 1 + (s_pos + 1) = s_pos
    rw [show (↑n : ZMod n) = 0 from ZMod.natCast_self n]; ring
  · -- For i < n-1, w' i = L (since the only s is at s_pos, not at i + s_pos + 1)
    intro i hi
    simp only [w', r]
    have hne : (↑i : ZMod n) + (s_pos + 1) ≠ s_pos := by
      intro heq
      have h1 : (↑i : ZMod n) + 1 = 0 := by
        calc (↑i : ZMod n) + 1
            = (↑i + (s_pos + 1)) - s_pos := by ring
          _ = s_pos - s_pos := by rw [heq]
          _ = 0 := by ring
      have h2 : (↑(i + 1) : ZMod n) = 0 := by push_cast; exact h1
      have h3 : (i + 1) % n = 0 := by
        have := congr_arg ZMod.val h2
        rwa [ZMod.val_natCast, ZMod.val_zero] at this
      have h4 : n ∣ (i + 1) := Nat.dvd_of_mod_eq_zero h3
      have := Nat.le_of_dvd (by omega) h4
      omega
    have hne_s : w ((↑i : ZMod n) + (s_pos + 1)) ≠ BinaryStep.s := fun h => hne (hunique _ h)
    cases h : w ((↑i : ZMod n) + (s_pos + 1))
    · rfl
    · exact absurd h hne_s

/-- For a rotated 1Lns word where L is at position n-1, all other positions have s -/
lemma ns1L_rotated_structure (n : ℕ) [NeZero n] (w : BinaryNecklace n)
    (hone_L : Necklace.count w BinaryStep.L = 1) (L_pos : ZMod n) (hL_pos : w L_pos = BinaryStep.L) :
    let r := L_pos + 1
    let w' := fun i => w (i + r)
    (w' (n - 1 : ZMod n) = BinaryStep.L) ∧
    (∀ i : ℕ, i < n - 1 → w' (i : ZMod n) = BinaryStep.s) := by
  intro r w'
  have hunique : ∀ j : ZMod n, w j = BinaryStep.L → j = L_pos := by
    intro j hj
    unfold Necklace.count at hone_L
    rw [Finset.card_eq_one] at hone_L
    obtain ⟨a, ha⟩ := hone_L
    have hj_mem : j ∈ ({a} : Finset (ZMod n)) := by
      rw [← ha]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
    have hL_mem : L_pos ∈ ({a} : Finset (ZMod n)) := by
      rw [← ha]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ L_pos, hL_pos⟩
    simp only [Finset.mem_singleton] at hj_mem hL_mem
    rw [hj_mem, hL_mem]
  constructor
  · simp only [w', r]
    convert hL_pos using 2
    rw [show (↑n : ZMod n) = 0 from ZMod.natCast_self n]; ring
  · intro i hi
    simp only [w', r]
    have hne : (↑i : ZMod n) + (L_pos + 1) ≠ L_pos := by
      intro heq
      have h1 : (↑i : ZMod n) + 1 = 0 := by
        calc (↑i : ZMod n) + 1
            = (↑i + (L_pos + 1)) - L_pos := by ring
          _ = L_pos - L_pos := by rw [heq]
          _ = 0 := by ring
      have h2 : (↑(i + 1) : ZMod n) = 0 := by push_cast; exact h1
      have h3 : (i + 1) % n = 0 := by
        have := congr_arg ZMod.val h2
        rwa [ZMod.val_natCast, ZMod.val_zero] at this
      have h4 : n ∣ (i + 1) := Nat.dvd_of_mod_eq_zero h3
      have := Nat.le_of_dvd (by omega) h4
      omega
    have hne_L : w ((↑i : ZMod n) + (L_pos + 1)) ≠ BinaryStep.L := fun h => hne (hunique _ h)
    cases h : w ((↑i : ZMod n) + (L_pos + 1))
    · exact absurd h hne_L
    · rfl

/-- If all positions 0..m-1 are L, then kStepVector counts m L's and 0 s's -/
private lemma kStepVector_allL_prefix [NeZero n] (w : BinaryNecklace n) (m : ℕ)
    (hallL : ∀ j : ℕ, j < m → w (↑j : ZMod n) = BinaryStep.L) (a : BinaryStep) :
    (Necklace.kStepVector w 0 m) a = if a = BinaryStep.L then (m : ℤ) else 0 := by
  induction m with
  | zero =>
    simp only [Necklace.kStepVector, ZVector.ofList, Necklace.slice, Nat.sub_zero,
               Nat.cast_zero]
    split <;> rfl
  | succ m ih =>
    have ih' := ih (fun j hj => hallL j (by omega))
    have hw_m : w (↑m : ZMod n) = BinaryStep.L := hallL m (by omega)
    have hsub := kStepVector_succ_sub w m a
    -- hsub : kStepVector w 0 (m+1) a - kStepVector w 0 m a = if w ↑m = a then 1 else 0
    rw [hw_m] at hsub
    cases a with
    | L =>
      simp only [↓reduceIte, Nat.cast_succ] at ih' hsub ⊢
      linarith
    | s =>
      simp only [reduceCtorEq, ↓reduceIte] at ih' hsub ⊢
      linarith

/-- If all positions 0..m-1 are s, then kStepVector counts 0 L's and m s's -/
private lemma kStepVector_alls_prefix [NeZero n] (w : BinaryNecklace n) (m : ℕ)
    (halls : ∀ j : ℕ, j < m → w (↑j : ZMod n) = BinaryStep.s) (a : BinaryStep) :
    (Necklace.kStepVector w 0 m) a = if a = BinaryStep.s then (m : ℤ) else 0 := by
  induction m with
  | zero =>
    simp only [Necklace.kStepVector, ZVector.ofList, Necklace.slice, Nat.sub_zero,
               Nat.cast_zero]
    split <;> rfl
  | succ m ih =>
    have ih' := ih (fun j hj => halls j (by omega))
    have hw_m : w (↑m : ZMod n) = BinaryStep.s := halls m (by omega)
    have hsub := kStepVector_succ_sub w m a
    rw [hw_m] at hsub
    cases a with
    | L =>
      simp only [reduceCtorEq, ↓reduceIte] at ih' hsub ⊢
      linarith
    | s =>
      simp only [↓reduceIte, Nat.cast_succ] at ih' hsub ⊢
      linarith

/-- The kStepVector over the full necklace counts each letter -/
private lemma kStepVector_zero_n_eq_count [NeZero n] (w : BinaryNecklace n) (a : BinaryStep) :
    Necklace.kStepVector w 0 n a = ↑(Necklace.count w a) := by
  -- Step 1: Convert kStepVector to explicit List sum
  have h_as_sum : Necklace.kStepVector w 0 n a =
      ((List.range n).map (fun m => if w ((m : ℕ) : ZMod n) = a then (1 : ℤ) else 0)).sum := by
    unfold Necklace.kStepVector ZVector.ofList Necklace.slice
    rw [show 0 + n - 0 = n from by omega, List.map_map,
        list_filter_beq_length_eq_map_ite_sum, List.map_map]
    simp [pure, bind, List.flatMap]
    congr 1
    ext m
    simp [Function.comp]
  -- Step 2: Convert List sum to Finset sum, then to count
  rw [h_as_sum, list_range_map_sum_eq_finset]
  simp_rw [show ∀ i : ℕ, (if w ((i : ℕ) : ZMod n) = a then (1 : ℤ) else 0) =
      ↑(if w ((i : ℕ) : ZMod n) = a then 1 else 0 : ℕ) from
      fun i => by split_ifs <;> simp]
  rw [← Nat.cast_sum, Finset.sum_boole]
  congr 1
  unfold Necklace.count
  apply Finset.card_bij (fun i _hi => ((i : ℕ) : ZMod n))
  · intro i hi; simp only [Finset.mem_filter] at hi ⊢; exact ⟨Finset.mem_univ _, hi.2⟩
  · intro i₁ hi₁ i₂ hi₂ h
    have h1 := (Finset.mem_filter.mp hi₁).1; have h2 := (Finset.mem_filter.mp hi₂).1
    rw [Finset.mem_range] at h1 h2
    have := congr_arg ZMod.val h
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this
  · intro j hj; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact ⟨ZMod.val j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt j),
      by rw [ZMod.natCast_zmod_val]; exact hj⟩, ZMod.natCast_zmod_val j⟩

/-- For a primitive necklace, the period vector equals the letter count -/
private lemma period_vector_eq_count [NeZero n] (w : BinaryNecklace n)
    (hprim : Necklace.isPrimitive w) (a : BinaryStep) :
    (ZVector.ofList (Necklace.period w)) a = ↑(Necklace.count w a) := by
  have hperiod_eq : Necklace.period w = Necklace.slice w 0 n := by
    have h := period_eq_slice_zero w; rwa [hprim] at h
  rw [hperiod_eq]
  have h := kStepVector_zero_n_eq_count w a
  unfold Necklace.kStepVector at h
  simp only [zero_add] at h
  exact h

/-- Base case: A MOS of form nL1s has a generator.
    (Chunking by L gives a one-letter necklace, so we've hit the base case.) -/
lemma mos_nL1s_has_generator (n : ℕ) [NeZero n] (w : BinaryNecklace n)
    (hw : BinaryNecklace.isMOS w)
    (hone_s : Necklace.count w BinaryStep.s = 1) : HasGenerator w := by
  -- When there's exactly 1 s, the scale has generator g = {1L, 0s}
  -- The word has (n-1) L's and 1 s.
  -- Define g = {1L, 0s}
  let g : ZVector BinaryStep := fun a => if a = BinaryStep.L then 1 else 0
  use g
  unfold IsGenerator
  -- Find the unique position of s
  have hs_exists : ∃ pos : ZMod n, w pos = BinaryStep.s := by
    unfold Necklace.count at hone_s
    have hpos : 0 < (Finset.filter (fun i => w i = BinaryStep.s) Finset.univ).card := by omega
    rw [Finset.card_pos] at hpos
    obtain ⟨pos, hpos_mem⟩ := hpos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpos_mem
    exact ⟨pos, hpos_mem⟩
  obtain ⟨s_pos, hs_pos⟩ := hs_exists
  -- Rotate so s is at the last position (index n-1 in Fin n, or equivalently -1 in ZMod n)
  -- If s is at s_pos, rotate by r = -s_pos - 1 so s ends up at position -1 ≡ n-1
  let r : ZMod n := s_pos + 1
  constructor
  · -- g appears as some k-step vector (at k=1, at any L position)
    use 1
    constructor
    · -- 1 < pLen: the period length is at least 2 for a binary MOS
      exact period_length_ge_two_of_binary w hw.1
    -- Since count s = 1 and n ≥ 1, there must be an L (unless n = 1)
    by_cases hn : n = 1
    · -- n = 1 case: the word is just "s", but then count s = 1 = n, contradiction
      subst hn
      use ⟨0, by omega⟩
      exfalso
      -- isMOS implies isBinary, which requires both L and s to exist
      have hbin := hw.1
      obtain ⟨iL, hiL⟩ := hbin.1
      obtain ⟨is, his⟩ := hbin.2
      -- But in ZMod 1, all elements equal 0
      have hiL0 : iL = 0 := Subsingleton.elim iL 0
      have his0 : is = 0 := Subsingleton.elim is 0
      -- So w 0 = L and w 0 = s
      rw [hiL0] at hiL
      rw [his0] at his
      -- This gives L = s, a contradiction
      have heq : BinaryStep.L = BinaryStep.s := hiL.symm.trans his
      exact BinaryStep.noConfusion heq
    · -- n > 1: there's at least one L
      have hL_count : Necklace.count w BinaryStep.L = n - 1 := by
        -- Total count = n, s count = 1, so L count = n - 1
        -- Prove L count + s count = n
        have htotal : Necklace.count w BinaryStep.L + Necklace.count w BinaryStep.s = n := by
          unfold Necklace.count
          have huniv : (Finset.filter (fun i => w i = BinaryStep.L) Finset.univ) ∪
              (Finset.filter (fun i => w i = BinaryStep.s) Finset.univ) = Finset.univ := by
            ext i
            simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
            cases w i <;> simp
          have hdisj : Disjoint (Finset.filter (fun i => w i = BinaryStep.L) Finset.univ)
              (Finset.filter (fun i => w i = BinaryStep.s) Finset.univ) := by
            rw [Finset.disjoint_filter]
            intro i _ hL
            simp_all
          rw [← Finset.card_union_of_disjoint hdisj, huniv]
          simp only [Finset.card_univ, ZMod.card n]
        omega
      have hL_exists : ∃ pos : ZMod n, w pos = BinaryStep.L := by
        have hn' : n > 1 := by
          have hne : n ≠ 0 := NeZero.ne n
          omega
        have hpos : 0 < n - 1 := by omega
        have hcard_pos : 0 < Necklace.count w BinaryStep.L := by omega
        unfold Necklace.count at hcard_pos
        rw [Finset.card_pos] at hcard_pos
        obtain ⟨pos, hpos_mem⟩ := hcard_pos
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpos_mem
        exact ⟨pos, hpos_mem⟩
      obtain ⟨L_pos, hL_pos⟩ := hL_exists
      use ⟨L_pos.val, L_pos.val_lt⟩
      -- Show Necklace.kStepVector w L_pos.val 1 = g
      unfold Necklace.kStepVector ZVector.ofList
      funext a
      -- The slice is just [w L_pos] = [BinaryStep.L]
      have hslice : Necklace.slice w L_pos.val (L_pos.val + 1) = [w L_pos] := by
        unfold Necklace.slice
        simp only [add_tsub_cancel_left, List.range_one, bind_pure_comp]
        simp
      simp only [hslice, hL_pos]
      cases a with
      | L =>
        simp only [g, ↓reduceIte, List.filter_singleton, beq_self_eq_true,
                   Bool.cond_true, List.length_singleton, Nat.cast_one]
      | s =>
        simp only [g, List.filter_singleton]
        decide
  · -- There exists a good rotation
    use r
    -- For nL1s word rotated so s is at position n-1:
    -- - g = {1L, 0s}
    -- - p (period) = {(n-1)L, 1s} (the whole word, since it's primitive)
    -- - Prefix of length i+1 (for i < n-1) = {(i+1)L, 0s} = (i+1)*g + 0*p
    -- - Prefix of length n = {(n-1)L, 1s} = 0*g + 1*p
    -- This gives j values: 1, 2, ..., n-1, 0 - a bijection with {0, ..., n-1}
    -- Use helper lemmas
    have hprim := nL1s_is_primitive n w hw hone_s
    have hrot := nL1s_rotated_structure n w hone_s s_pos hs_pos
    -- pLen = n since primitive
    have hpLen : (Necklace.period w).length = n := hprim
    constructor
    · -- Every prefix is j*g + k*p for some j < pLen
      intro i
      -- i : Fin pLen where pLen = n
      -- Case split on whether i.val < n - 1 or i.val = n - 1
      by_cases hi : i.val < n - 1
      · -- i < n-1: prefix has (i+1) L's and 0 s's
        -- j = i+1, k = 0
        have hj_bound : i.val + 1 < (Necklace.period w).length := by simp only [hpLen]; omega
        use ⟨i.val + 1, hj_bound⟩
        use 0
        intro a
        have hallL := kStepVector_allL_prefix (fun i => w (i + r)) (i.val + 1)
          (fun j hj => hrot.2 j (by omega)) a
        simp only [zero_mul, add_zero] at hallL ⊢
        rw [hallL]
        cases a with
        | L => simp [g, mul_one]
        | s => simp [g, mul_zero]
      · -- i = n-1: prefix has (n-1) L's and 1 s
        -- j = 0, k = 1
        push_neg at hi
        have hi_eq : i.val = n - 1 := by
          have := i.isLt; simp only [hpLen] at this; omega
        have h0_bound : 0 < (Necklace.period w).length := by simp only [hpLen]; exact NeZero.pos n
        use ⟨0, h0_bound⟩
        use 1
        intro a
        -- kStepVector w' 0 n a = 0 * g a + 1 * p a = p a
        simp only [one_mul]
        -- Need: kStepVector w' 0 n a = ZVector.ofList (period w) a
        rw [show i.val + 1 = n from by omega]
        rw [period_vector_eq_count w hprim a]
        -- Need: kStepVector w' 0 n a = ↑(count w a)
        -- Compute via allL + one step
        have hn_pos : 1 < n := by
          have := period_length_ge_two_of_binary w hw.1; omega
        have hallL := kStepVector_allL_prefix (fun i => w (i + r)) (n - 1)
          (fun j hj => hrot.2 j hj) a
        have hsub := kStepVector_succ_sub (fun i => w (i + r)) (n - 1) a
        rw [show n - 1 + 1 = n from by omega] at hsub
        have hw_last : w ((↑(n - 1 : ℕ) : ZMod n) + r) = BinaryStep.s := by
          have h := hrot.1
          change w ((↑n - 1 : ZMod n) + r) = BinaryStep.s at h
          rwa [Nat.cast_sub (show 1 ≤ n from by omega), Nat.cast_one]
        rw [hw_last] at hsub
        have hL_count : Necklace.count w BinaryStep.L = n - 1 := by
          have h := kStepVector_total_count w 0 n
          rw [kStepVector_zero_n_eq_count, kStepVector_zero_n_eq_count, hone_s] at h
          norm_cast at h; omega
        cases a with
        | L =>
          simp only [↓reduceIte, reduceCtorEq] at hallL hsub ⊢
          rw [hL_count]; push_cast; linarith
        | s =>
          simp only [reduceCtorEq, ↓reduceIte] at hallL hsub ⊢
          rw [hone_s]; push_cast; linarith
    · -- Every j < pLen is realized (surjectivity)
      intro j
      by_cases hj : j.val = 0
      · -- j = 0: realized by i = n-1 (full prefix)
        have hn1_bound : n - 1 < (Necklace.period w).length := by
          simp only [hpLen]; exact Nat.sub_lt (NeZero.pos n) Nat.one_pos
        use ⟨n - 1, hn1_bound⟩
        use 1
        intro a
        -- full prefix = period
        simp only [one_mul]
        rw [show (n - 1 : ℕ) + 1 = n from by omega]
        rw [period_vector_eq_count w hprim a]
        have hn_pos : 1 < n := by
          have := period_length_ge_two_of_binary w hw.1; omega
        have hallL := kStepVector_allL_prefix (fun i => w (i + r)) (n - 1)
          (fun j hj => hrot.2 j hj) a
        have hsub := kStepVector_succ_sub (fun i => w (i + r)) (n - 1) a
        rw [show n - 1 + 1 = n from by omega] at hsub
        have hw_last : w ((↑(n - 1 : ℕ) : ZMod n) + r) = BinaryStep.s := by
          have h := hrot.1
          change w ((↑n - 1 : ZMod n) + r) = BinaryStep.s at h
          rwa [Nat.cast_sub (show 1 ≤ n from by omega), Nat.cast_one]
        rw [hw_last] at hsub
        have hL_count : Necklace.count w BinaryStep.L = n - 1 := by
          have h := kStepVector_total_count w 0 n
          rw [kStepVector_zero_n_eq_count, kStepVector_zero_n_eq_count, hone_s] at h
          norm_cast at h; omega
        rw [hj]
        cases a with
        | L =>
          simp only [↓reduceIte, reduceCtorEq] at hallL hsub ⊢
          rw [hL_count]; push_cast; linarith
        | s =>
          simp only [reduceCtorEq, ↓reduceIte] at hallL hsub ⊢
          rw [hone_s]; push_cast; linarith
      · -- j > 0: realized by i = j-1 (prefix of length j)
        have hj_pos : 0 < j.val := Nat.pos_of_ne_zero hj
        have hjm1_bound : j.val - 1 < (Necklace.period w).length := by
          have := j.isLt; omega
        use ⟨j.val - 1, hjm1_bound⟩
        use 0
        intro a
        -- prefix of all L's
        have hj_lt : j.val ≤ n - 1 := by
          have := j.isLt; simp only [hpLen] at this; omega
        have hallL := kStepVector_allL_prefix (fun i => w (i + r)) j.val
          (fun k hk => hrot.2 k (by omega)) a
        simp only [zero_mul, add_zero] at hallL ⊢
        rw [show j.val - 1 + 1 = j.val from by omega, hallL]
        cases a with
        | L => simp [g, mul_one]
        | s => simp [g, mul_zero]

/-- Base case: A MOS of form 1Lns has a generator.
    (Symmetric to nL1s.) -/
lemma mos_1Lns_has_generator (n : ℕ) [NeZero n] (w : BinaryNecklace n)
    (hw : BinaryNecklace.isMOS w)
    (hone_L : Necklace.count w BinaryStep.L = 1) : HasGenerator w := by
  -- When there's exactly 1 L, the scale has generator g = {0L, 1s}
  -- Symmetric to mos_nL1s_has_generator with L↔s
  let g : ZVector BinaryStep := fun a => if a = BinaryStep.s then 1 else 0
  use g
  unfold IsGenerator
  -- Find the unique position of L
  have hL_exists : ∃ pos : ZMod n, w pos = BinaryStep.L := by
    unfold Necklace.count at hone_L
    have hpos : 0 < (Finset.filter (fun i => w i = BinaryStep.L) Finset.univ).card := by omega
    rw [Finset.card_pos] at hpos
    obtain ⟨pos, hpos_mem⟩ := hpos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpos_mem
    exact ⟨pos, hpos_mem⟩
  obtain ⟨L_pos, hL_pos⟩ := hL_exists
  let r : ZMod n := L_pos + 1
  -- Total count helper
  have htotal : Necklace.count w BinaryStep.L + Necklace.count w BinaryStep.s = n := by
    unfold Necklace.count
    have huniv : (Finset.filter (fun i => w i = BinaryStep.L) Finset.univ) ∪
        (Finset.filter (fun i => w i = BinaryStep.s) Finset.univ) = Finset.univ := by
      ext i; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      cases w i <;> simp
    have hdisj : Disjoint (Finset.filter (fun i => w i = BinaryStep.L) Finset.univ)
        (Finset.filter (fun i => w i = BinaryStep.s) Finset.univ) := by
      rw [Finset.disjoint_filter]; intro i _ hL; simp_all
    rw [← Finset.card_union_of_disjoint hdisj, huniv]
    simp only [Finset.card_univ, ZMod.card n]
  have hs_count : Necklace.count w BinaryStep.s = n - 1 := by omega
  constructor
  · -- g appears as some k-step vector (at k=1, at any s position)
    use 1
    constructor
    · exact period_length_ge_two_of_binary w hw.1
    by_cases hn : n = 1
    · subst hn
      use ⟨0, by omega⟩
      exfalso
      have hbin := hw.1
      obtain ⟨iL, hiL⟩ := hbin.1; obtain ⟨is, his⟩ := hbin.2
      have hiL0 : iL = 0 := Subsingleton.elim iL 0
      have his0 : is = 0 := Subsingleton.elim is 0
      rw [hiL0] at hiL; rw [his0] at his
      exact BinaryStep.noConfusion (hiL.symm.trans his)
    · -- n > 1: find an s position
      have hs_exists : ∃ pos : ZMod n, w pos = BinaryStep.s := by
        have hcard_pos : 0 < Necklace.count w BinaryStep.s := by omega
        unfold Necklace.count at hcard_pos
        rw [Finset.card_pos] at hcard_pos
        obtain ⟨pos, hpos_mem⟩ := hcard_pos
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpos_mem
        exact ⟨pos, hpos_mem⟩
      obtain ⟨s_pos, hs_pos⟩ := hs_exists
      use ⟨s_pos.val, s_pos.val_lt⟩
      unfold Necklace.kStepVector ZVector.ofList
      funext a
      have hslice : Necklace.slice w s_pos.val (s_pos.val + 1) = [w s_pos] := by
        unfold Necklace.slice
        simp only [add_tsub_cancel_left, List.range_one, bind_pure_comp]
        simp
      simp only [hslice, hs_pos]
      cases a with
      | L =>
        simp only [g, List.filter_singleton]
        decide
      | s =>
        simp only [g, ↓reduceIte, List.filter_singleton, beq_self_eq_true,
                   Bool.cond_true, List.length_singleton, Nat.cast_one]
  · -- There exists a good rotation
    use r
    have hprim : Necklace.isPrimitive w := by
      have hcoprime : Nat.gcd 1 (n - 1) = 1 := Nat.gcd_one_left (n - 1)
      exact necklace_with_coprime_sig_is_primitive n 1 (n - 1) hcoprime w hone_L hs_count
    have hrot := ns1L_rotated_structure n w hone_L L_pos hL_pos
    have hpLen : (Necklace.period w).length = n := hprim
    constructor
    · -- Every prefix is j*g + k*p for some j < pLen
      intro i
      by_cases hi : i.val < n - 1
      · -- i < n-1: prefix of all s's, j = i+1, k = 0
        have hj_bound : i.val + 1 < (Necklace.period w).length := by simp only [hpLen]; omega
        use ⟨i.val + 1, hj_bound⟩
        use 0
        intro a
        have halls := kStepVector_alls_prefix (fun i => w (i + r)) (i.val + 1)
          (fun j hj => hrot.2 j (by omega)) a
        simp only [zero_mul, add_zero] at halls ⊢
        rw [halls]
        cases a with
        | L => simp [g, mul_zero]
        | s => simp [g, mul_one]
      · -- i = n-1: full word = period, j = 0, k = 1
        push_neg at hi
        have hi_eq : i.val = n - 1 := by
          have := i.isLt; simp only [hpLen] at this; omega
        have h0_bound : 0 < (Necklace.period w).length := by simp only [hpLen]; exact NeZero.pos n
        use ⟨0, h0_bound⟩
        use 1
        intro a
        simp only [one_mul]
        rw [show i.val + 1 = n from by omega]
        rw [period_vector_eq_count w hprim a]
        have hn_pos : 1 < n := by
          have := period_length_ge_two_of_binary w hw.1; omega
        have halls := kStepVector_alls_prefix (fun i => w (i + r)) (n - 1)
          (fun j hj => hrot.2 j hj) a
        have hsub := kStepVector_succ_sub (fun i => w (i + r)) (n - 1) a
        rw [show n - 1 + 1 = n from by omega] at hsub
        have hw_last : w ((↑(n - 1 : ℕ) : ZMod n) + r) = BinaryStep.L := by
          have h := hrot.1
          change w ((↑n - 1 : ZMod n) + r) = BinaryStep.L at h
          rwa [Nat.cast_sub (show 1 ≤ n from by omega), Nat.cast_one]
        rw [hw_last] at hsub
        cases a with
        | L =>
          simp only [reduceCtorEq, ↓reduceIte] at halls hsub ⊢
          rw [hone_L]; push_cast; linarith
        | s =>
          simp only [↓reduceIte, reduceCtorEq] at halls hsub ⊢
          rw [hs_count]; push_cast; linarith
    · -- Every j < pLen is realized (surjectivity)
      intro j
      by_cases hj : j.val = 0
      · -- j = 0: realized by i = n-1 (full prefix)
        have hn1_bound : n - 1 < (Necklace.period w).length := by
          simp only [hpLen]; exact Nat.sub_lt (NeZero.pos n) Nat.one_pos
        use ⟨n - 1, hn1_bound⟩
        use 1
        intro a
        simp only [one_mul]
        rw [show (n - 1 : ℕ) + 1 = n from by omega]
        rw [period_vector_eq_count w hprim a]
        have hn_pos : 1 < n := by
          have := period_length_ge_two_of_binary w hw.1; omega
        have halls := kStepVector_alls_prefix (fun i => w (i + r)) (n - 1)
          (fun j hj => hrot.2 j hj) a
        have hsub := kStepVector_succ_sub (fun i => w (i + r)) (n - 1) a
        rw [show n - 1 + 1 = n from by omega] at hsub
        have hw_last : w ((↑(n - 1 : ℕ) : ZMod n) + r) = BinaryStep.L := by
          have h := hrot.1
          change w ((↑n - 1 : ZMod n) + r) = BinaryStep.L at h
          rwa [Nat.cast_sub (show 1 ≤ n from by omega), Nat.cast_one]
        rw [hw_last] at hsub
        rw [hj]
        cases a with
        | L =>
          simp only [reduceCtorEq, ↓reduceIte] at halls hsub ⊢
          rw [hone_L]; push_cast; linarith
        | s =>
          simp only [↓reduceIte, reduceCtorEq] at halls hsub ⊢
          rw [hs_count]; push_cast; linarith
      · -- j > 0: realized by i = j-1 (prefix of length j)
        have hj_pos : 0 < j.val := Nat.pos_of_ne_zero hj
        have hjm1_bound : j.val - 1 < (Necklace.period w).length := by
          have := j.isLt; omega
        use ⟨j.val - 1, hjm1_bound⟩
        use 0
        intro a
        have hj_lt : j.val ≤ n - 1 := by
          have := j.isLt; simp only [hpLen] at this; omega
        have halls := kStepVector_alls_prefix (fun i => w (i + r)) j.val
          (fun k hk => hrot.2 k (by omega)) a
        simp only [zero_mul, add_zero] at halls ⊢
        rw [show j.val - 1 + 1 = j.val from by omega, halls]
        cases a with
        | L => simp [g, mul_zero]
        | s => simp [g, mul_one]

/-- Helper: chunkSizesToBinary preserves length from numChunks.
    The proof is technical: chunkSizesToBinary maps over the sizes list,
    which has the same length as indices (otherStep x) w = numChunks x w. -/
lemma chunkSizesToBinary_length [NeZero n] (x : BinaryStep) (w : BinaryNecklace n)
    (chunks : List BinaryStep) (hchunks : chunkSizesToBinary x w = some chunks) :
    chunks.length = numChunks x w := by
  -- Extract sizes from chunkSizesToBinary
  unfold chunkSizesToBinary at hchunks
  cases hsizes : chunkSizesList x w with
  | none => simp [hsizes] at hchunks
  | some sizes =>
    have hlen := chunkSizesList_length x w sizes hsizes
    simp only [hsizes] at hchunks
    -- hchunks is now about the match on sizes.toFinset.toList
    change (match sizes.toFinset.toList with
      | [_] => some (sizes.map (fun _ => BinaryStep.L))
      | [a, b] => if a + 1 = b || b + 1 = a then
          some (sizes.map (fun s => if s = min a b then BinaryStep.s else BinaryStep.L))
        else none
      | _ => none) = some chunks at hchunks
    -- In all successful branches, chunks = sizes.map f
    split at hchunks
    · -- Single distinct size
      rw [← Option.some.inj hchunks, List.length_map, hlen]
    · -- Two distinct sizes
      split at hchunks
      · rw [← Option.some.inj hchunks, List.length_map, hlen]
      · cases hchunks
    · cases hchunks

/-- A binary MOS has exactly one of some step if and only if chunking gives a one-letter word -/
lemma chunks_length_one_iff_count_one (n : ℕ) [NeZero n] (w : BinaryNecklace n)
    (x : BinaryStep) (chunks : List BinaryStep)
    (hchunks : chunkSizesToBinary x w = some chunks) :
    chunks.length = 1 ↔ Necklace.count w (BinaryStep.otherStep x) = 1 := by
  rw [chunkSizesToBinary_length x w chunks hchunks, numChunks_eq_count]

/-- Helper: The number of chunks is strictly less than the original length
    (since each chunk contains at least one step of the chunked type) -/
lemma numChunks_lt_length (n : ℕ) [NeZero n] (w : BinaryNecklace n)
    (_ : BinaryNecklace.isMOS w) (x : BinaryStep)
    (hbinary : BinaryNecklace.isBinary w) :
    numChunks x w < n := by
  -- numChunks x w = (indices (otherStep x) w).length = count of non-x letters
  -- This is < n because there's at least one x letter (from isBinary)
  -- We work directly with Necklace.count which uses Finset
  have hcount_x_pos : 0 < Necklace.count w x := by
    cases x with
    | L =>
      obtain ⟨iL, hiL⟩ := hbinary.1
      unfold Necklace.count
      apply Finset.card_pos.mpr
      use iL
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hiL]
    | s =>
      obtain ⟨is, his⟩ := hbinary.2
      unfold Necklace.count
      apply Finset.card_pos.mpr
      use is
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, his]
  -- count x + count (otherStep x) = n (for binary words)
  have hsum : Necklace.count w x + Necklace.count w (BinaryStep.otherStep x) = n := by
    unfold Necklace.count
    have huniv : (Finset.filter (fun i => w i = x) Finset.univ) ∪
        (Finset.filter (fun i => w i = BinaryStep.otherStep x) Finset.univ) = Finset.univ := by
      ext i
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      cases hxi : w i with
      | L => cases x <;> simp [BinaryStep.otherStep]
      | s => cases x <;> simp [BinaryStep.otherStep]
    have hdisj : Disjoint (Finset.filter (fun i => w i = x) Finset.univ)
        (Finset.filter (fun i => w i = BinaryStep.otherStep x) Finset.univ) := by
      rw [Finset.disjoint_filter]
      intro i _ hx
      cases x <;> simp_all [BinaryStep.otherStep]
    rw [← Finset.card_union_of_disjoint hdisj, huniv]
    simp only [Finset.card_univ, ZMod.card n]
  -- numChunks = indices length ≤ n (since indices is a sublist of range n)
  have hle : numChunks x w ≤ n := by
    unfold numChunks
    exact indices_length_le _ _
  -- We need numChunks x w < n
  -- numChunks counts positions with otherStep x
  -- Since count w x > 0 (from isBinary), numChunks < n
  have hlt : numChunks x w < n := by
    by_contra hge
    push_neg at hge
    have heq : numChunks x w = n := Nat.le_antisymm hle hge
    -- If numChunks x w = n, then all positions have otherStep x
    -- So every i : ZMod n is in indices (otherStep x) w
    have hall : ∀ i : ZMod n, i ∈ indices (BinaryStep.otherStep x) w := by
      intro i
      -- indices has length n, and it's a sublist of a list with n distinct elements
      -- So it must contain all elements
      have hindices_nodup : (indices (BinaryStep.otherStep x) w).Nodup := indices_nodup _ _
      have hcard : (indices (BinaryStep.otherStep x) w).toFinset.card = n := by
        rw [List.toFinset_card_of_nodup hindices_nodup]
        unfold numChunks at heq
        exact heq
      -- All ZMod n elements are in the finset
      have hall_finset : ∀ j : ZMod n, j ∈ (indices (BinaryStep.otherStep x) w).toFinset := by
        intro j
        by_contra hj
        have hcard_lt : (indices (BinaryStep.otherStep x) w).toFinset.card < Fintype.card (ZMod n) := by
          apply Finset.card_lt_card
          rw [Finset.ssubset_univ_iff]
          intro heq
          have : j ∈ (indices (BinaryStep.otherStep x) w).toFinset := by
            rw [heq]
            exact Finset.mem_univ j
          exact hj this
        simp only [ZMod.card, hcard] at hcard_lt
        omega
      exact List.mem_toFinset.mp (hall_finset i)
    -- But there exists i with w i = x, not otherStep x
    cases x with
    | L =>
      obtain ⟨iL, hiL⟩ := hbinary.1
      have h := hall iL
      rw [indices_mem_iff] at h
      simp only [BinaryStep.otherStep, Necklace.get, hiL] at h
      exact nomatch h
    | s =>
      obtain ⟨is, his⟩ := hbinary.2
      have h := hall is
      rw [indices_mem_iff] at h
      simp only [BinaryStep.otherStep, Necklace.get, his] at h
      exact nomatch h
  exact hlt

/-- The period length divides n. Extracted from the proof of kStepVector_mod_period. -/
private lemma period_dvd_length [NeZero n] [DecidableEq α] (w : Necklace α n) :
    (Necklace.period w).length ∣ n := by
  have hRep : Necklace.isRepetitionOf w (Necklace.period w) = true := by
    unfold Necklace.period
    cases hfind : ((List.range n).tail.map (Necklace.slice w 0)).find?
        (Necklace.isRepetitionOf w) with
    | some pfx => simp only [Option.getD_some]; exact List.find?_some hfind
    | none =>
      simp only [Option.getD_none]
      unfold Necklace.isRepetitionOf
      simp only [Necklace.slice_length, Nat.sub_zero, ne_eq,
        Nat.pos_iff_ne_zero.mp (NeZero.pos n), ↓reduceIte,
        Nat.mod_self, not_true_eq_false]
      rw [List.all_eq_true]
      intro i hi
      rw [List.mem_range] at hi
      rw [decide_eq_true_eq, Nat.mod_eq_of_lt hi]
      unfold Necklace.slice
      simp only [bind_pure_comp, Functor.map, Nat.sub_zero, Nat.cast_zero, zero_add,
            List.map_map, Function.comp, List.getElem?_map, List.getElem?_range hi,
            Option.map]
  unfold Necklace.isRepetitionOf at hRep
  simp only [ne_eq] at hRep
  split at hRep
  · exact absurd hRep Bool.false_ne_true
  · split at hRep
    · exact absurd hRep Bool.false_ne_true
    · rename_i _ h2
      push_neg at h2
      exact Nat.dvd_of_mod_eq_zero h2

/-- Pointwise periodicity: w(j) = w(j % pLen) for all j.
    Extracted from the proof of kStepVector_mod_period. -/
private lemma period_pointwise [NeZero n] [DecidableEq α] (w : Necklace α n) (j : ℕ) :
    w ((j : ℕ) : ZMod n) = w ((j % (Necklace.period w).length : ℕ) : ZMod n) := by
  set pLen := (Necklace.period w).length with hpLen_def
  have hpLen_pos : 0 < pLen := period_length_pos w
  have hpLen_dvd_n : pLen ∣ n := period_dvd_length w
  have hj_mod_n := Nat.mod_lt j (NeZero.pos n)
  have hj_mod_pLen := Nat.mod_lt j hpLen_pos
  conv_lhs => rw [show ((j : ℕ) : ZMod n) = ((j % n : ℕ) : ZMod n) from by simp []]
  -- Extract matching from isRepetitionOf
  have hRep : Necklace.isRepetitionOf w (Necklace.period w) = true := by
    unfold Necklace.period
    cases hfind : ((List.range n).tail.map (Necklace.slice w 0)).find?
        (Necklace.isRepetitionOf w) with
    | some pfx => simp only [Option.getD_some]; exact List.find?_some hfind
    | none =>
      simp only [Option.getD_none]
      unfold Necklace.isRepetitionOf
      simp only [Necklace.slice_length, Nat.sub_zero, ne_eq,
        Nat.pos_iff_ne_zero.mp (NeZero.pos n), ↓reduceIte,
        Nat.mod_self, not_true_eq_false]
      rw [List.all_eq_true]
      intro i hi
      rw [List.mem_range] at hi
      rw [decide_eq_true_eq, Nat.mod_eq_of_lt hi]
      unfold Necklace.slice
      simp only [bind_pure_comp, Functor.map, Nat.sub_zero, Nat.cast_zero, zero_add,
            List.map_map, Function.comp, List.getElem?_map, List.getElem?_range hi,
            Option.map]
  have hperiod_match : ∀ i, i < n →
      some (w ((i : ℕ) : ZMod n)) = (Necklace.period w)[i % pLen]? := by
    intro i hi
    unfold Necklace.isRepetitionOf at hRep
    simp only [ne_eq] at hRep
    split at hRep
    · exact absurd hRep Bool.false_ne_true
    · split at hRep
      · exact absurd hRep Bool.false_ne_true
      · rw [List.all_eq_true] at hRep
        have := hRep i (List.mem_range.mpr hi)
        rwa [decide_eq_true_eq] at this
  have hperiod_is_slice : Necklace.period w = Necklace.slice w 0 pLen :=
    period_eq_slice_zero w
  have hperiod_elem : ∀ j, j < pLen →
      (Necklace.period w)[j]? = some (w ((j : ℕ) : ZMod n)) := by
    intro j hj
    rw [hperiod_is_slice]
    unfold Necklace.slice
    simp only [bind_pure_comp, Functor.map, Nat.sub_zero, Nat.cast_zero, zero_add,
          List.map_map, Function.comp, List.getElem?_map, List.getElem?_range hj,
          Option.map]
  have h1 := hperiod_match (j % n) hj_mod_n
  rw [Nat.mod_mod_of_dvd j hpLen_dvd_n] at h1
  have h2 := hperiod_elem (j % pLen) hj_mod_pLen
  rw [h2] at h1
  exact Option.some_injective _ h1

/-- A non-primitive MOS has a generator, assuming all shorter MOS necklaces do.
    Since w is non-primitive, it is a d-fold repetition of a shorter word w' (its period).
    w' is itself a MOS (the k-step vectors of a repetition are exactly those of its period).
    By the induction hypothesis, w' has a generator g. Since w's k-step vectors are the same
    as those of w', g is also a generator of w. -/
private lemma hasGenerator_of_nonprimitive_mos (n : ℕ) [NeZero n]
    (w : BinaryNecklace n) (hw : BinaryNecklace.isMOS w)
    (h_not_prim : ¬ Necklace.isPrimitive w)
    (ih : ∀ (m : ℕ), m < n → ∀ [NeZero m],
      ∀ (w : BinaryNecklace m), BinaryNecklace.isMOS w → HasGenerator w) :
    HasGenerator w := by
  -- Period length properties
  set pLen := (Necklace.period w).length with hpLen_def
  have hpLen_pos : 0 < pLen := period_length_pos w
  have hpLen_lt_n : pLen < n := by
    have := Necklace.period_length_le_n w
    unfold Necklace.isPrimitive at h_not_prim; omega
  haveI : NeZero pLen := ⟨by omega⟩
  -- Pointwise periodicity
  have hperiodic : ∀ j : ℕ, w ((j : ℕ) : ZMod n) = w ((j % pLen : ℕ) : ZMod n) :=
    fun j => by rw [hpLen_def]; exact period_pointwise w j
  -- Helper: (i.val : ZMod n) = i
  have hval_cast : ∀ i : ZMod n, (i.val : ZMod n) = i :=
    fun i => by simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
  -- Helper: ((j : ℕ) : ZMod pLen).val = j % pLen
  have hval_mod : ∀ j : ℕ, ((j : ℕ) : ZMod pLen).val = j % pLen :=
    fun j => ZMod.val_natCast pLen j
  -- Construct the period necklace
  let wper : BinaryNecklace pLen := fun (i : ZMod pLen) => w (i.val : ZMod n)
  -- Key fact: wper(j) = w(j) for natural number positions, via periodicity
  have hwper_eq : ∀ j : ℕ, wper ((j : ℕ) : ZMod pLen) = w ((j : ℕ) : ZMod n) := by
    intro j
    show w ((((j : ℕ) : ZMod pLen).val : ℕ) : ZMod n) = w ((j : ℕ) : ZMod n)
    rw [hval_mod, ← hperiodic]
  -- Period necklace is MOS
  have hwper_mos : BinaryNecklace.isMOS wper := by
    constructor
    · -- isBinary: wper uses both L and s
      constructor
      · obtain ⟨i, hi⟩ := hw.1.1
        exact ⟨(i.val % pLen : ZMod pLen), by
          show w ((((i.val % pLen : ℕ) : ZMod pLen).val : ℕ) : ZMod n) = BinaryStep.L
          rw [hval_mod, Nat.mod_eq_of_lt (Nat.mod_lt _ hpLen_pos),
              ← hperiodic i.val, hval_cast]
          exact hi⟩
      · obtain ⟨i, hi⟩ := hw.1.2
        exact ⟨(i.val % pLen : ZMod pLen), by
          show w ((((i.val % pLen : ℕ) : ZMod pLen).val : ℕ) : ZMod n) = BinaryStep.s
          rw [hval_mod, Nat.mod_eq_of_lt (Nat.mod_lt _ hpLen_pos),
              ← hperiodic i.val, hval_cast]
          exact hi⟩
    · -- At most 2 distinct k-step multisets for each k
      intro k hk_pos hk_lt
      have hk_lt_n : k < n := lt_trans hk_lt hpLen_lt_n
      -- Every k-step multiset of wper appears as a k-step multiset of w
      have hsubset : (Necklace.allKStepMultisets wper k).toFinset ⊆
          (Necklace.allKStepMultisets w k).toFinset := by
        intro m hm
        rw [List.mem_toFinset] at hm ⊢
        unfold Necklace.allKStepMultisets Necklace.allKStepSubwords at hm ⊢
        rw [List.mem_map] at hm ⊢
        obtain ⟨sub, hsub_mem, rfl⟩ := hm
        rw [List.mem_ofFn] at hsub_mem
        obtain ⟨i, rfl⟩ := hsub_mem
        -- slice wper i (i+k) = slice w i (i+k) by periodicity
        have hslice_eq : Necklace.slice wper i.val (i.val + k) =
            Necklace.slice w i.val (i.val + k) := by
          unfold Necklace.slice
          simp only [Nat.add_sub_cancel_left, bind_pure_comp, Functor.map, List.map_map]
          apply List.map_congr_left
          intro t _
          simp only [Function.comp_apply, ← Nat.cast_add]
          exact hwper_eq (i.val + t)
        rw [hslice_eq]
        exact ⟨_, List.mem_ofFn.mpr ⟨⟨i.val, lt_trans i.isLt hpLen_lt_n⟩, rfl⟩, rfl⟩
      exact le_trans (Finset.card_le_card hsubset) (hw.2 k hk_pos hk_lt_n)
  -- k-step vectors of wper equal those of w (for any position and length)
  have hkstep_eq : ∀ m k, Necklace.kStepVector wper m k = Necklace.kStepVector w m k := by
    intro m k
    unfold Necklace.kStepVector
    congr 1
    unfold Necklace.slice
    simp only [Nat.add_sub_cancel_left, bind_pure_comp, Functor.map, List.map_map]
    apply List.map_congr_left
    intro t _
    simp only [Function.comp_apply, ← Nat.cast_add]
    exact hwper_eq (m + t)
  -- wper is primitive (its period length = pLen)
  have hwper_prim : Necklace.isPrimitive wper := by
    by_contra h_not_prim_wper
    set qLen := (Necklace.period wper).length with hqLen_def
    have hqLen_pos : 0 < qLen := period_length_pos wper
    have hqLen_lt_pLen : qLen < pLen := by
      have := Necklace.period_length_le_n wper
      unfold Necklace.isPrimitive at h_not_prim_wper; omega
    have hqLen_dvd_pLen : qLen ∣ pLen := period_dvd_length wper
    -- wper has pointwise periodicity with period qLen
    have hwper_periodic_q : ∀ j : ℕ, wper ((j : ℕ) : ZMod pLen) =
        wper ((j % qLen : ℕ) : ZMod pLen) :=
      fun j => by rw [hqLen_def]; exact period_pointwise wper j
    -- Derive: w has translational period qLen
    have hw_trans : ∀ i : ZMod n, w i = w (i + (qLen : ZMod n)) := by
      intro i
      -- w(i) = wper(i.val) = wper(i.val % q) = wper((i.val+q) % q) = wper(i.val+q) = w(i+q)
      have h1 : w i = wper ((i.val : ℕ) : ZMod pLen) := by
        conv_lhs => rw [show i = (i.val : ZMod n) from (hval_cast i).symm]
        exact (hwper_eq i.val).symm
      have h2 : w (i + (qLen : ZMod n)) = wper (((i.val + qLen) : ℕ) : ZMod pLen) := by
        have hcast : i + (qLen : ZMod n) = ((i.val + qLen : ℕ) : ZMod n) := by
          rw [Nat.cast_add, hval_cast]
        rw [hcast]
        exact (hwper_eq (i.val + qLen)).symm
      rw [h1, h2, hwper_periodic_q i.val, hwper_periodic_q (i.val + qLen), Nat.add_mod_right]
    -- period_length_le_of_translational_period gives pLen ≤ qLen, contradicting qLen < pLen
    have hqLen_dvd_n : qLen ∣ n := dvd_trans hqLen_dvd_pLen (period_dvd_length w)
    have := Necklace.period_length_le_of_translational_period w qLen hqLen_pos
      (lt_trans hqLen_lt_pLen hpLen_lt_n) hqLen_dvd_n hw_trans
    omega
  -- Period equality: Necklace.period wper = Necklace.period w
  have hperiod_eq : Necklace.period wper = Necklace.period w := by
    -- Both equal slice _ 0 pLen
    have h1 : Necklace.period wper = Necklace.slice wper 0 pLen := by
      have := period_eq_slice_zero wper
      rwa [hwper_prim] at this
    have h2 : Necklace.period w = Necklace.slice w 0 pLen := period_eq_slice_zero w
    rw [h1, h2]
    -- slice wper 0 pLen = slice w 0 pLen
    unfold Necklace.slice
    simp only [Nat.sub_zero, bind_pure_comp, Functor.map, List.map_map]
    apply List.map_congr_left
    intro t _
    simp only [Function.comp_apply, ← Nat.cast_add, Nat.zero_add]
    exact hwper_eq t
  -- Apply IH
  obtain ⟨g, hg⟩ := ih pLen hpLen_lt_n wper hwper_mos
  -- Transfer generator from period necklace to w
  refine ⟨g, ?_⟩
  show IsGenerator w g
  unfold IsGenerator at hg ⊢
  -- Don't rw [hperiod_eq] at hg (fails due to dependent types).
  -- Instead, convert Fin types manually using these equalities:
  have hperiod_len_eq : (Necklace.period wper).length = (Necklace.period w).length := by
    rw [hperiod_eq]
  have hperiodvec_eq : ZVector.ofList (Necklace.period wper) =
      ZVector.ofList (Necklace.period w) := by rw [hperiod_eq]
  constructor
  · -- Period-reduced
    obtain ⟨k₀, hk₀_lt, i₀, hi₀⟩ := hg.1
    exact ⟨k₀, by omega,
      ⟨i₀.val, lt_trans i₀.isLt hpLen_lt_n⟩,
      by rw [← hkstep_eq]; exact hi₀⟩
  · -- Rotation condition
    obtain ⟨r_per, hfwd, hbwd⟩ := hg.2
    refine ⟨(r_per.val : ZMod n), ?_, ?_⟩
    · -- Forward
      intro i
      obtain ⟨j', k_coeff, hpref⟩ := hfwd ⟨i.val, by omega⟩
      refine ⟨⟨j'.val, by omega⟩, k_coeff, fun a => ?_⟩
      have hrot_eq : Necklace.kStepVector (fun j => w (j + (r_per.val : ZMod n))) 0 (i.val + 1) =
          Necklace.kStepVector (fun j => wper (j + r_per)) 0 (i.val + 1) := by
        unfold Necklace.kStepVector Necklace.slice
        simp only [Nat.zero_add, bind_pure_comp, Functor.map, List.map_map]
        congr 1
        apply List.map_congr_left
        intro t _
        simp only [Function.comp_apply, ← Nat.cast_add, Nat.zero_add]
        -- Goal: w ↑(t + r_per.val) = wper (↑t + r_per)
        conv_rhs => rw [show (r_per : ZMod pLen) = ((r_per.val : ℕ) : ZMod pLen) from by
          simp [ZMod.natCast_val, ZMod.cast_id'], ← Nat.cast_add]
        exact (hwper_eq (t + r_per.val)).symm
      rw [hrot_eq, ← hperiodvec_eq]
      exact hpref a
    · -- Backward
      intro j
      obtain ⟨i', k_coeff, hpref⟩ := hbwd ⟨j.val, by omega⟩
      refine ⟨⟨i'.val, by omega⟩, k_coeff, fun a => ?_⟩
      have hrot_eq : Necklace.kStepVector (fun j => w (j + (r_per.val : ZMod n))) 0 (i'.val + 1) =
          Necklace.kStepVector (fun j => wper (j + r_per)) 0 (i'.val + 1) := by
        unfold Necklace.kStepVector Necklace.slice
        simp only [Nat.zero_add, bind_pure_comp, Functor.map, List.map_map]
        congr 1
        apply List.map_congr_left
        intro t _
        simp only [Function.comp_apply, ← Nat.cast_add, Nat.zero_add]
        conv_rhs => rw [show (r_per : ZMod pLen) = ((r_per.val : ℕ) : ZMod pLen) from by
          simp [ZMod.natCast_val, ZMod.cast_id'], ← Nat.cast_add]
        exact (hwper_eq (t + r_per.val)).symm
      rw [hrot_eq, ← hperiodvec_eq]
      exact hpref a

/-- Main theorem: Every MOS scale has a generator.

The proof is by strong induction on n:
- Base case (n ≤ 2): The generator is trivial (1-step is itself a generator)
- Inductive case (primitive): Chunk the MOS by L (or s) to get a smaller MOS word,
  apply the induction hypothesis, then reflect the generator back.
- Inductive case (non-primitive): The word is a d-fold repetition of a shorter MOS;
  the generator of the period lifts to a generator of the whole word.
-/
theorem allMOSScalesHaveGenerator : ∀ n : ℕ, [NeZero n] →
    (∀ w : BinaryNecklace n, (BinaryNecklace.isMOS w) → (HasGenerator w)) := by
  intro n
  -- Strong induction on n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro _inst w hw
    -- Get the binary property from MOS
    have hbinary : BinaryNecklace.isBinary w := hw.1
    -- Case split: does one step occur exactly once? (base case)
    by_cases hone_s : Necklace.count w BinaryStep.s = 1
    · -- Base case: nL1s - L is a generator
      exact mos_nL1s_has_generator n w hw hone_s
    · by_cases hone_L : Necklace.count w BinaryStep.L = 1
      · -- Base case: 1Lns - s is a generator
        exact mos_1Lns_has_generator n w hw hone_L
      · -- Inductive case: both steps occur more than once
        -- Derive that both counts > 1
        have hcountL_gt : Necklace.count w BinaryStep.L > 1 := by
          obtain ⟨i, hi⟩ := hbinary.1
          have : Necklace.count w BinaryStep.L ≥ 1 :=
            Finset.one_le_card.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
          omega
        have hcountS_gt : Necklace.count w BinaryStep.s > 1 := by
          obtain ⟨i, hi⟩ := hbinary.2
          have : Necklace.count w BinaryStep.s ≥ 1 :=
            Finset.one_le_card.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
          omega
        -- Handle primitive vs non-primitive
        suffices hprim_case : Necklace.isPrimitive w → HasGenerator w by
          by_cases hprim : Necklace.isPrimitive w
          · exact hprim_case hprim
          · exact hasGenerator_of_nonprimitive_mos n w hw hprim ih
        intro hprim
        -- Choose to chunk by the more frequent step
        by_cases hL : hasMoreLs w
        · -- More L's than s's: chunk by L
          let x := BinaryStep.L
          cases hchunks : chunkSizesList x w with
          | none =>
            -- If no chunks, all letters are L - contradicts isBinary
            -- chunkSizesList L w = none means indices (otherStep L) w = [] (no s letters)
            -- But isBinary requires at least one s
            exfalso
            unfold chunkSizesList at hchunks
            simp only [Id.run] at hchunks
            -- Analyze based on whether indices has elements
            obtain ⟨is, his⟩ := hbinary.2
            have his_mem : is ∈ indices (BinaryStep.otherStep x) w := by
              rw [indices_mem_iff]
              simp only [x, BinaryStep.otherStep, Necklace.get, his]
            -- indices s w is nonempty, so head? = some _
            cases hindices : (indices (BinaryStep.otherStep x) w).head? with
            | none =>
              -- indices is empty, contradicting his_mem
              rw [List.head?_eq_none_iff] at hindices
              simp only [hindices] at his_mem
              exact List.not_mem_nil his_mem
            | some firstNonX =>
              -- In this case, chunkSizesList returns some _, not none
              simp only [hindices, pure] at hchunks
              cases hchunks
          | some sizes =>
            cases hbinary_chunks : chunkSizesToBinary x w with
            | none =>
              -- Can't happen for a MOS (chunk sizes are consecutive)
              exfalso
              exact mos_chunkSizesToBinary_ne_none n w hw x sizes hchunks hbinary_chunks
            | some chunks =>
              have hlen : chunks.length ≠ 0 := by
                -- chunks.length = sizes.length = numChunks = count of s letters ≥ 1
                -- First show chunks.length = sizes.length by analyzing chunkSizesToBinary
                have hsizes_nonempty := chunkSizesList_nonempty x w sizes hchunks
                have hchunks_len : chunks.length = sizes.length := by
                  unfold chunkSizesToBinary at hbinary_chunks
                  simp only [hchunks] at hbinary_chunks
                  change (match sizes.toFinset.toList with
                    | [_] => some (sizes.map (fun _ => BinaryStep.L))
                    | [a, b] => if a + 1 = b || b + 1 = a then
                        some (sizes.map (fun s => if s = min a b then BinaryStep.s else BinaryStep.L))
                      else none
                    | _ => none) = some chunks at hbinary_chunks
                  split at hbinary_chunks
                  · injection hbinary_chunks with h; rw [← h, List.length_map]
                  · split at hbinary_chunks
                    · injection hbinary_chunks with h; rw [← h, List.length_map]
                    · cases hbinary_chunks
                  · cases hbinary_chunks
                rw [hchunks_len, ne_eq]
                intro hlen_zero
                apply hsizes_nonempty
                cases sizes with
                | nil => rfl
                | cons _ _ => simp at hlen_zero
              have hlt : chunks.length < n := by
                -- chunks.length = numChunks x w = count of s letters < n
                have hsizes_len := chunkSizesList_length x w sizes hchunks
                have hchunks_len : chunks.length = sizes.length := by
                  unfold chunkSizesToBinary at hbinary_chunks
                  simp only [hchunks] at hbinary_chunks
                  change (match sizes.toFinset.toList with
                    | [_] => some (sizes.map (fun _ => BinaryStep.L))
                    | [a, b] => if a + 1 = b || b + 1 = a then
                        some (sizes.map (fun s => if s = min a b then BinaryStep.s else BinaryStep.L))
                      else none
                    | _ => none) = some chunks at hbinary_chunks
                  split at hbinary_chunks
                  · injection hbinary_chunks with h; rw [← h, List.length_map]
                  · split at hbinary_chunks
                    · injection hbinary_chunks with h; rw [← h, List.length_map]
                    · cases hbinary_chunks
                  · cases hbinary_chunks
                rw [hchunks_len, hsizes_len]
                exact numChunks_lt_length n w hw x hbinary
              haveI : NeZero chunks.length := ⟨hlen⟩
              have hw_chunked : BinaryNecklace.isMOS (Necklace.toNecklace chunks) := by
                exact chunkSizesOfPrimMOSFormPrimMOS n w hw hprim x chunks
                  hbinary_chunks hlen hcountL_gt hcountS_gt
              have hgen_chunked : HasGenerator (Necklace.toNecklace chunks) := by
                have := ih chunks.length hlt
                exact this (Necklace.toNecklace chunks) hw_chunked
              have hsizes : chunkSizesList x w = some sizes := hchunks
              have hprim_chunked : Necklace.isPrimitive (Necklace.toNecklace chunks) :=
                chunk_primitivity x w hw hprim sizes hsizes chunks hbinary_chunks hlen
              exact generator_reflects_under_expansion_L n w hw hprim x chunks sizes
                hbinary_chunks hsizes hlen hL hw_chunked hgen_chunked hprim_chunked
        · -- More s's than L's: chunk by s (symmetric)
          let x := BinaryStep.s
          cases hchunks : chunkSizesList x w with
          | none =>
            -- chunkSizesList s w = none means no L letters - contradicts isBinary
            exfalso
            unfold chunkSizesList at hchunks
            simp only [Id.run] at hchunks
            -- Analyze based on whether indices has elements
            obtain ⟨iL, hiL⟩ := hbinary.1
            have hiL_mem : iL ∈ indices (BinaryStep.otherStep x) w := by
              rw [indices_mem_iff]
              simp only [x, BinaryStep.otherStep, Necklace.get, hiL]
            -- indices L w is nonempty, so head? = some _
            cases hindices : (indices (BinaryStep.otherStep x) w).head? with
            | none =>
              -- indices is empty, contradicting hiL_mem
              rw [List.head?_eq_none_iff] at hindices
              simp only [hindices] at hiL_mem
              exact List.not_mem_nil hiL_mem
            | some firstNonX =>
              -- In this case, chunkSizesList returns some _, not none
              simp only [hindices, pure] at hchunks
              cases hchunks
          | some sizes =>
            cases hbinary_chunks : chunkSizesToBinary x w with
            | none =>
              -- Can't happen for a MOS (chunk sizes are consecutive)
              exfalso
              exact mos_chunkSizesToBinary_ne_none n w hw x sizes hchunks hbinary_chunks
            | some chunks =>
              have hlen : chunks.length ≠ 0 := by
                -- chunks.length = numChunks = count of L letters ≥ 1
                have hsizes_nonempty := chunkSizesList_nonempty x w sizes hchunks
                have hchunks_len : chunks.length = sizes.length := by
                  unfold chunkSizesToBinary at hbinary_chunks
                  simp only [hchunks] at hbinary_chunks
                  change (match sizes.toFinset.toList with
                    | [_] => some (sizes.map (fun _ => BinaryStep.L))
                    | [a, b] => if a + 1 = b || b + 1 = a then
                        some (sizes.map (fun s => if s = min a b then BinaryStep.s else BinaryStep.L))
                      else none
                    | _ => none) = some chunks at hbinary_chunks
                  split at hbinary_chunks
                  · injection hbinary_chunks with h; rw [← h, List.length_map]
                  · split at hbinary_chunks
                    · injection hbinary_chunks with h; rw [← h, List.length_map]
                    · cases hbinary_chunks
                  · cases hbinary_chunks
                rw [hchunks_len, ne_eq]
                intro hlen_zero
                apply hsizes_nonempty
                cases sizes with
                | nil => rfl
                | cons _ _ => simp at hlen_zero
              have hlt : chunks.length < n := by
                -- chunks.length = count of L letters < n
                have hsizes_len := chunkSizesList_length x w sizes hchunks
                have hchunks_len : chunks.length = sizes.length := by
                  unfold chunkSizesToBinary at hbinary_chunks
                  simp only [hchunks] at hbinary_chunks
                  change (match sizes.toFinset.toList with
                    | [_] => some (sizes.map (fun _ => BinaryStep.L))
                    | [a, b] => if a + 1 = b || b + 1 = a then
                        some (sizes.map (fun s => if s = min a b then BinaryStep.s else BinaryStep.L))
                      else none
                    | _ => none) = some chunks at hbinary_chunks
                  split at hbinary_chunks
                  · injection hbinary_chunks with h; rw [← h, List.length_map]
                  · split at hbinary_chunks
                    · injection hbinary_chunks with h; rw [← h, List.length_map]
                    · cases hbinary_chunks
                  · cases hbinary_chunks
                rw [hchunks_len, hsizes_len]
                exact numChunks_lt_length n w hw x hbinary
              haveI : NeZero chunks.length := ⟨hlen⟩
              have hw_chunked : BinaryNecklace.isMOS (Necklace.toNecklace chunks) := by
                exact chunkSizesOfPrimMOSFormPrimMOS n w hw hprim x chunks
                  hbinary_chunks hlen hcountS_gt hcountL_gt
              have hgen_chunked : HasGenerator (Necklace.toNecklace chunks) := by
                have := ih chunks.length hlt
                exact this (Necklace.toNecklace chunks) hw_chunked
              have hsizes : chunkSizesList x w = some sizes := hchunks
              have hprim_chunked : Necklace.isPrimitive (Necklace.toNecklace chunks) :=
                chunk_primitivity x w hw hprim sizes hsizes chunks hbinary_chunks hlen
              exact generator_reflects_under_expansion_s n w hw hprim x chunks sizes
                hbinary_chunks hsizes hlen hL hw_chunked hgen_chunked hprim_chunked
