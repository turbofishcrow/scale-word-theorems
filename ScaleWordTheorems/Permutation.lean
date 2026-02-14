import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic
import ScaleWordTheorems.Basic

/-!
# Permutation Infrastructure for Ternary Scale Words

The symmetric group S₃ acts on ternary scale words by permuting letters.
This file defines that action and proves that key properties are S₃-invariant,
enabling WLOG arguments of the form "it suffices to prove the result for words
with step signature aX bY cZ."

## Main Definitions

* `Necklace.applyPerm`: Apply a letter permutation σ to a necklace
* `ZVector.applyPerm`: Apply a letter permutation σ to a ZVector
* `IsS3Invariant`: A property of ternary necklaces is S₃-invariant

## Main Results

* `Necklace.slice_applyPerm`: Slices of σ(w) are σ-images of slices of w
* `Necklace.allKStepMultisets_toFinset_card_applyPerm`: The number of distinct
  k-step multisets is preserved under letter permutation
* `isS3Invariant_isMV3`: MV3 is S₃-invariant
* `isS3Invariant_isBalanced`: Balanced is S₃-invariant
* `wlog_perm`: WLOG reduction lemma

## References

Based on Lemmas P1–P3 in the theorems document (Permutation lemmas section).
-/

/-! ## Action on Necklaces -/

namespace Necklace

variable {α : Type*} {n : ℕ}

/-- Apply a letter permutation to a necklace (covariant action on codomain).
    Each letter `w i` is replaced by `σ (w i)`. -/
def applyPerm (σ : Equiv.Perm α) (w : Necklace α n) : Necklace α n :=
  σ ∘ w

@[simp] lemma applyPerm_apply (σ : Equiv.Perm α) (w : Necklace α n) (i : ZMod n) :
    applyPerm σ w i = σ (w i) := rfl

/-- Applying the identity permutation does nothing. -/
@[simp] lemma applyPerm_one (w : Necklace α n) :
    applyPerm (1 : Equiv.Perm α) w = w := by
  funext i; simp [applyPerm]

/-- Applying two permutations in sequence. -/
lemma applyPerm_mul (σ τ : Equiv.Perm α) (w : Necklace α n) :
    applyPerm (σ * τ) w = applyPerm σ (applyPerm τ w) := by
  funext i; simp [applyPerm]

/-- Applying σ then σ⁻¹ recovers the original. -/
@[simp] lemma applyPerm_symm_cancel (σ : Equiv.Perm α) (w : Necklace α n) :
    applyPerm σ.symm (applyPerm σ w) = w := by
  funext i; simp [applyPerm]

/-- Applying σ⁻¹ then σ recovers the original. -/
@[simp] lemma applyPerm_cancel_symm (σ : Equiv.Perm α) (w : Necklace α n) :
    applyPerm σ (applyPerm σ.symm w) = w := by
  funext i; simp [applyPerm]

/-- `applyPerm σ` is injective. -/
lemma applyPerm_injective (σ : Equiv.Perm α) :
    Function.Injective (applyPerm σ : Necklace α n → Necklace α n) := by
  intro w₁ w₂ h
  have : applyPerm σ.symm (applyPerm σ w₁) = applyPerm σ.symm (applyPerm σ w₂) :=
    congrArg _ h
  simpa using this

/-- `applyPerm σ` is surjective. -/
lemma applyPerm_surjective (σ : Equiv.Perm α) :
    Function.Surjective (applyPerm σ : Necklace α n → Necklace α n) :=
  fun w => ⟨applyPerm σ.symm w, by simp⟩

/-- `applyPerm σ` is bijective. -/
lemma applyPerm_bijective (σ : Equiv.Perm α) :
    Function.Bijective (applyPerm σ : Necklace α n → Necklace α n) :=
  ⟨applyPerm_injective σ, applyPerm_surjective σ⟩

/-! ### Interaction with slices and subwords -/

/-- Slices of a permuted necklace are pointwise images of the original slices. -/
lemma slice_applyPerm [NeZero n] (σ : Equiv.Perm α) (w : Necklace α n) (i j : ℕ) :
    slice (applyPerm σ w) i j = (slice w i j).map σ := by
  unfold slice applyPerm
  simp [List.map_map]

/-- k-step subwords of a permuted necklace are pointwise images. -/
lemma allKStepSubwords_applyPerm [NeZero n] [DecidableEq α]
    (σ : Equiv.Perm α) (w : Necklace α n) (k : ℕ) :
    allKStepSubwords (applyPerm σ w) k =
    (allKStepSubwords w k).map (List.map σ) := by
  -- Each k-step subword of σ(w) is the σ-image of the corresponding subword of w,
  -- by `slice_applyPerm`.
  unfold allKStepSubwords
  simp only [List.map_ofFn]
  congr 1; funext i
  exact slice_applyPerm σ w i.val (i.val + k)

/-- k-step multisets of a permuted necklace are images under `Multiset.map σ`.
    This is the key lemma: abelianized subwords are permuted correspondingly. -/
lemma allKStepMultisets_applyPerm [NeZero n] [DecidableEq α]
    (σ : Equiv.Perm α) (w : Necklace α n) (k : ℕ) :
    allKStepMultisets (applyPerm σ w) k =
    (allKStepMultisets w k).map (Multiset.map σ) := by
  unfold allKStepMultisets
  rw [allKStepSubwords_applyPerm]
  simp only [List.map_map]
  congr 1

/-- The number of distinct k-step multisets is preserved under letter permutation.
    This is the central fact enabling MV3/SV3 invariance. -/
lemma allKStepMultisets_toFinset_card_applyPerm [NeZero n] [DecidableEq α]
    (σ : Equiv.Perm α) (w : Necklace α n) (k : ℕ) :
    (allKStepMultisets (applyPerm σ w) k).toFinset.card =
    (allKStepMultisets w k).toFinset.card := by
  rw [allKStepMultisets_applyPerm]
  have h : ((allKStepMultisets w k).map (Multiset.map σ)).toFinset =
      (allKStepMultisets w k).toFinset.image (Multiset.map σ) := by
    ext; simp
  rw [h]
  exact Finset.card_image_of_injective _ (Multiset.map_injective σ.injective)

/-! ### Interaction with letter counts -/

/-- Counting letter `a` in `σ(w)` equals counting `σ⁻¹(a)` in `w`. -/
lemma count_applyPerm [NeZero n] [DecidableEq α]
    (σ : Equiv.Perm α) (w : Necklace α n) (a : α) :
    count (applyPerm σ w) a = count w (σ.symm a) := by
  unfold count applyPerm
  congr 1; ext i
  simp [Function.comp, Equiv.apply_eq_iff_eq_symm_apply]

end Necklace

/-! ## Action on ZVectors -/

namespace ZVector

variable {α : Type*}

/-- Apply a letter permutation to a ZVector (contravariant action on domain).
    If `v` is the Parikh vector of word `w`, then `applyPerm σ v` is the
    Parikh vector of `σ(w)`: the count of letter `a` in `σ(w)` equals the
    count of `σ⁻¹(a)` in `w`. -/
def applyPerm (σ : Equiv.Perm α) (v : ZVector α) : ZVector α :=
  v ∘ σ.symm

@[simp] lemma applyPerm_apply (σ : Equiv.Perm α) (v : ZVector α) (a : α) :
    applyPerm σ v a = v (σ.symm a) := rfl

@[simp] lemma applyPerm_one (v : ZVector α) :
    applyPerm (1 : Equiv.Perm α) v = v := by
  funext a; simp [applyPerm]

lemma applyPerm_mul (σ τ : Equiv.Perm α) (v : ZVector α) :
    applyPerm (σ * τ) v = applyPerm σ (applyPerm τ v) := by
  funext a; rfl

/-- Compatibility: the Parikh vector of a mapped list equals the permuted Parikh vector.
    This connects the two `applyPerm` definitions. -/
lemma ofList_map_eq_applyPerm [DecidableEq α] (σ : Equiv.Perm α) (l : List α) :
    ofList (l.map σ) = applyPerm σ (ofList l) := by
  funext a
  simp only [ofList, applyPerm_apply]
  norm_cast
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.filter_cons]
    by_cases h : x = σ.symm a
    · subst h; simp [ih]
    · have : σ x ≠ a := fun h' => h (by rwa [Equiv.apply_eq_iff_eq_symm_apply] at h')
      simp [h, this, ih]

end ZVector

/-! ## S₃-Invariance -/

/-- A property of ternary necklaces is **S₃-invariant** if it is preserved
    under all letter permutations. -/
def IsS3Invariant {n : ℕ} (P : TernaryNecklace n → Prop) : Prop :=
  ∀ (σ : Equiv.Perm StepSize) (w : TernaryNecklace n), P w ↔ P (Necklace.applyPerm σ w)

/-! ### WLOG Reduction -/

/-- **WLOG lemma**: If `P` is S₃-invariant and `P (σ(w))` holds for some `σ`,
    then `P w` holds. This lets us choose a convenient representative. -/
theorem wlog_perm {n : ℕ} {P : TernaryNecklace n → Prop}
    (hP : IsS3Invariant P) (w : TernaryNecklace n)
    (σ : Equiv.Perm StepSize) (h : P (Necklace.applyPerm σ w)) : P w :=
  (hP σ w).mpr h

/-- Equivalent formulation: `P w` iff `P (σ(w))` for any σ. -/
theorem s3invariant_iff {n : ℕ} {P : TernaryNecklace n → Prop}
    (hP : IsS3Invariant P) (σ : Equiv.Perm StepSize) (w : TernaryNecklace n) :
    P w ↔ P (Necklace.applyPerm σ w) :=
  hP σ w

/-! ## TernaryNecklace-Specific Lemmas -/

namespace TernaryNecklace

variable {n : ℕ}

/-- `isTernary` is equivalent to: every letter occurs at least once. -/
lemma isTernary_iff_forall (w : TernaryNecklace n) :
    isTernary w ↔ ∀ a : StepSize, ∃ i : ZMod n, w i = a := by
  constructor
  · intro ⟨hL, hm, hs⟩ a
    match a with
    | .L => exact hL
    | .m => exact hm
    | .s => exact hs
  · intro h
    exact ⟨h .L, h .m, h .s⟩

/-- `isTernary` is preserved under letter permutation. -/
lemma isTernary_applyPerm (σ : Equiv.Perm StepSize) (w : TernaryNecklace n) :
    isTernary (Necklace.applyPerm σ w) ↔ isTernary w := by
  simp only [isTernary_iff_forall, Necklace.applyPerm_apply]
  constructor
  · intro h a
    obtain ⟨i, hi⟩ := h (σ a)
    exact ⟨i, σ.injective hi⟩
  · intro h a
    obtain ⟨i, hi⟩ := h (σ.symm a)
    exact ⟨i, by simp [hi]⟩

/-- Pair identification commutes with letter permutation:
    identifying `a` and `b` in `σ(w)` equals applying `σ` to `w` with
    `σ⁻¹(a)` and `σ⁻¹(b)` identified. -/
lemma identifyPair_applyPerm [NeZero n]
    (σ : Equiv.Perm StepSize) (w : TernaryNecklace n) (a b : StepSize) :
    identifyPair (Necklace.applyPerm σ w) a b =
    Necklace.applyPerm σ (identifyPair w (σ.symm a) (σ.symm b)) := by
  funext i
  simp only [identifyPair, Necklace.applyPerm_apply]
  -- Goal: (if σ(w i) = a then b else σ(w i)) = σ(if w i = σ⁻¹ a then σ⁻¹ b else w i)
  -- The two conditions are equivalent by Equiv.apply_eq_iff_eq_symm_apply.
  by_cases h : w i = σ.symm a
  · simp [h, Equiv.apply_symm_apply]
  · simp [h, show σ (w i) ≠ a from fun h' => h (by rwa [Equiv.apply_eq_iff_eq_symm_apply] at h')]

end TernaryNecklace

/-! ## Invariance of Specific Properties -/

section Invariance

variable {n : ℕ} [NeZero n]

/-- **MV3 is S₃-invariant.**
    Proof strategy: `isTernary` is permutation-invariant (shown above),
    and the number of distinct k-step multisets is preserved since `Multiset.map σ`
    is a bijection on multisets. -/
theorem isS3Invariant_isMV3 : IsS3Invariant (TernaryNecklace.isMV3 (n := n)) := by
  intro σ w
  simp only [TernaryNecklace.isMV3]
  constructor
  · intro ⟨htern, hmv⟩
    refine ⟨(TernaryNecklace.isTernary_applyPerm σ w).mpr htern, fun k hk hkn => ?_⟩
    rw [Necklace.allKStepMultisets_toFinset_card_applyPerm]
    exact hmv k hk hkn
  · intro ⟨htern, hmv⟩
    refine ⟨(TernaryNecklace.isTernary_applyPerm σ w).mp htern, fun k hk hkn => ?_⟩
    rw [← Necklace.allKStepMultisets_toFinset_card_applyPerm σ]
    exact hmv k hk hkn

/-- Count of `a` in `l.map σ` equals count of `σ⁻¹(a)` in `l`. -/
private lemma list_count_map_perm {α : Type*} [DecidableEq α]
    (σ : Equiv.Perm α) (l : List α) (a : α) :
    (l.map σ).count a = l.count (σ.symm a) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons]
    by_cases h : x = σ.symm a
    · subst h; simp [ih]
    · have : σ x ≠ a := fun h' => h (by rwa [Equiv.apply_eq_iff_eq_symm_apply] at h')
      simp [h, this, ih]

/-- **Balanced is S₃-invariant.** -/
theorem isS3Invariant_isBalanced :
    IsS3Invariant (Necklace.isBalanced (α := StepSize) (n := n)) := by
  intro σ w
  simp only [Necklace.isBalanced]
  constructor
  · intro h k hk hkn w1 w2 a hw1 hw2
    rw [Necklace.allKStepSubwords_applyPerm] at hw1 hw2
    obtain ⟨w1', hw1', rfl⟩ := List.mem_map.mp hw1
    obtain ⟨w2', hw2', rfl⟩ := List.mem_map.mp hw2
    simp only [list_count_map_perm]
    exact h k hk hkn w1' w2' (σ.symm a) hw1' hw2'
  · intro h k hk hkn w1 w2 a hw1 hw2
    have hw1' : w1.map σ ∈ Necklace.allKStepSubwords (Necklace.applyPerm σ w) k := by
      rw [Necklace.allKStepSubwords_applyPerm]; exact List.mem_map.mpr ⟨w1, hw1, rfl⟩
    have hw2' : w2.map σ ∈ Necklace.allKStepSubwords (Necklace.applyPerm σ w) k := by
      rw [Necklace.allKStepSubwords_applyPerm]; exact List.mem_map.mpr ⟨w2, hw2, rfl⟩
    have := h k hk hkn _ _ (σ a) hw1' hw2'
    simp only [list_count_map_perm, Equiv.symm_apply_apply] at this
    exact this

end Invariance

/-! ## Step Signature Under Permutation -/

namespace TernaryNecklace

variable {n : ℕ} [NeZero n]

/-- The step count multiset {#L, #m, #s} is an S₃-invariant:
    applying σ permutes which letter has which count. -/
lemma count_applyPerm_eq (σ : Equiv.Perm StepSize) (w : TernaryNecklace n) (a : StepSize) :
    Necklace.count (Necklace.applyPerm σ w) a = Necklace.count w (σ.symm a) :=
  Necklace.count_applyPerm σ w a

/-- Given a ternary word whose step counts form a multiset with two equal values,
    there exists σ such that σ(w) has step signature a**X** b**Y** b**Z**
    (i.e. the unique count is assigned to **X** and the repeated count to **Y** and **Z**). -/
theorem exists_perm_canonical_signature_two_equal
    (w : TernaryNecklace n)
    (a b : ℕ) (_ha : a ≠ b)
    (hcounts : ∃ (x : StepSize), Necklace.count w x = a ∧
      ∀ y : StepSize, y ≠ x → Necklace.count w y = b) :
    ∃ σ : Equiv.Perm StepSize,
      Necklace.count (Necklace.applyPerm σ w) StepSize.L = a ∧
      Necklace.count (Necklace.applyPerm σ w) StepSize.m = b ∧
      Necklace.count (Necklace.applyPerm σ w) StepSize.s = b := by
  obtain ⟨x, hx_eq, hx_ne⟩ := hcounts
  cases x with
  | L =>
    exact ⟨1, by simp [hx_eq],
               by simp [hx_ne .m (by decide)],
               by simp [hx_ne .s (by decide)]⟩
  | m =>
    refine ⟨Equiv.swap .L .m, ?_, ?_, ?_⟩ <;> rw [count_applyPerm_eq]
    · rw [show (Equiv.swap StepSize.L StepSize.m).symm StepSize.L = StepSize.m from by decide]
      exact hx_eq
    · rw [show (Equiv.swap StepSize.L StepSize.m).symm StepSize.m = StepSize.L from by decide]
      exact hx_ne .L (by decide)
    · rw [show (Equiv.swap StepSize.L StepSize.m).symm StepSize.s = StepSize.s from by decide]
      exact hx_ne .s (by decide)
  | s =>
    refine ⟨Equiv.swap .L .s, ?_, ?_, ?_⟩ <;> rw [count_applyPerm_eq]
    · rw [show (Equiv.swap StepSize.L StepSize.s).symm StepSize.L = StepSize.s from by decide]
      exact hx_eq
    · rw [show (Equiv.swap StepSize.L StepSize.s).symm StepSize.m = StepSize.m from by decide]
      exact hx_ne .m (by decide)
    · rw [show (Equiv.swap StepSize.L StepSize.s).symm StepSize.s = StepSize.L from by decide]
      exact hx_ne .L (by decide)

end TernaryNecklace
