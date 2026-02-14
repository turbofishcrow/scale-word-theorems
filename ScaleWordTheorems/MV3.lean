import ScaleWordTheorems.Basic
import ScaleWordTheorems.MOS
import ScaleWordTheorems.Permutation
import ScaleWordTheorems.PairIdentificationAndDeletion
import ScaleWordTheorems.TwistedNecklaces

open BigOperators

/-!
# Ternary Scale Theorems (MV3)

Definitions and theorem statements for ternary scale theory, including
the classification of MV3 (maximum variety 3) necklaces.

## References

Based on <https://en.xen.wiki/w/Ternary_scale_theorems>
-/

/-! ## Interleaving (general) -/

namespace Necklace

variable {α : Type*} {n : ℕ} [NeZero n]

/-- A necklace is an *interleaving* with `numStrands` strands if `numStrands > 1`,
    `numStrands ∣ n`, and each strand gives the same sub-sequence as strand 0.
    Strand `s` consists of positions `s, s + numStrands, s + 2·numStrands, …`. -/
def isInterleaving (w : Necklace α n) (numStrands : ℕ) : Prop :=
  numStrands > 1 ∧
  numStrands ∣ n ∧
  ∀ (s : Fin numStrands) (j : Fin (n / numStrands)),
    w ((j.val * numStrands + s.val : ℕ) : ZMod n) =
    w ((j.val * numStrands : ℕ) : ZMod n)

/-- The reversal of a necklace: `w` read backwards, i.e. `fun i => w (n - i)`. -/
def reversal (w : Necklace α n) : Necklace α n :=
  fun i => w (-i)

/-- A necklace is *chiral* if its reversal is not a rotation of itself. -/
def isChiral (w : Necklace α n) : Prop :=
  ¬ ∃ r : ZMod n, ∀ i : ZMod n, w (-i) = w (i + r)

/-- A necklace is a *contrainterleaving* if it consists of two mutually
    interleaved strands that are the two chiralities (a scale and its reversal)
    of a chiral sub-scale. That is, `numStrands = 2`, `2 ∣ n`, strand 0 gives
    a sub-sequence and strand 1 gives its reversal (up to rotation). -/
def isContrainterleaving (w : Necklace α n) : Prop :=
  2 ∣ n ∧
  ∃ r : ZMod n,
    -- strand 1 is the reversal of strand 0 (up to rotation r)
    ∀ j : Fin (n / 2),
      w ((j.val * 2 + 1 : ℕ) : ZMod n) =
      w ((((n / 2 - 1 - j.val) * 2 : ℕ) : ZMod n) + r)

/-- Extract strand `s` from a 2-interleaving: strand `s` consists of
    positions `s, s+2, s+4, …`, giving a sub-necklace of length `n/2`. -/
def strand2 [NeZero (n / 2)] (w : Necklace α n) (s : Fin 2) : Necklace α (n / 2) :=
  fun j => w ((j.val * 2 + s.val : ℕ) : ZMod n)

end Necklace

/-! ## ZVector pair identification -/

/-- Identify two values `x` and `y` in a `ZVector`: merge the count of `x` into `y`,
    setting the `x`-component to zero. -/
def ZVector.identifyPair [DecidableEq α] (v : ZVector α) (x y : α) : ZVector α :=
  fun a => if a = x then 0 else if a = y then v x + v y else v a

/-! ## Unreduced generator -/

/-- An *unreduced generator* of `w` is a vector `g` satisfying the stacking property
    of `IsGenerator` without requiring `g` to be period-reduced.
    That is, there exists a rotation where the prefix vectors correspond
    bijectively to `{j·g + k·p : 0 ≤ j < |p|}`. -/
def IsUnreducedGenerator [NeZero n] [DecidableEq α] (w : Necklace α n) (g : ZVector α) : Prop :=
  let per := Necklace.period w
  let pLen := per.length
  let p := ZVector.ofList per
  ∃ r : ZMod n,
    let w' := fun i => w (i + r)
    (∀ i : Fin pLen,
      ∃ j : Fin pLen, ∃ k : ℤ,
        ∀ a : α, (Necklace.kStepVector w' 0 (i.val + 1)) a = j.val * g a + k * p a) ∧
    (∀ j : Fin pLen,
      ∃ i : Fin pLen, ∃ k : ℤ,
        ∀ a : α, (Necklace.kStepVector w' 0 (i.val + 1)) a = j.val * g a + k * p a)

/-! ## Ternary-specific definitions and theorems -/

namespace TernaryNecklace

variable {n : ℕ} [NeZero n]

/-! ### S₃-equivalence -/

/-- Two ternary necklaces are *S₃-equivalent* if one can be obtained from
    the other by permuting step sizes and rotating. -/
def isS3Equivalent (w₁ w₂ : TernaryNecklace n) : Prop :=
  ∃ (σ : Equiv.Perm StepSize) (r : ZMod n),
    ∀ i : ZMod n, w₁ i = σ (w₂ (i + r))

/-! ### Well-formed sequence (WFS) -/

/-- A necklace has a *well-formed sequence* (WFS) if there exist a period `p`,
    step size `k` with `gcd(k, n) = 1`, starting position `r`, and periodic
    sequence `seq` of k-step vectors such that:
    - The first `n - 1` k-step vectors follow the periodic pattern `seq`.
    - The closing vector (the last k-step vector) is not in `seq`. -/
def hasWFS (w : TernaryNecklace n) : Prop :=
  ∃ (p : ℕ) (hp : 0 < p) (k r : ℕ) (seq : Fin p → ZVector StepSize),
    Nat.Coprime k n ∧
    (∀ i : Fin (n - 1),
      Necklace.kStepVector w (r + i.val * k) k =
        seq ⟨i.val % p, Nat.mod_lt _ hp⟩) ∧
    (∀ j : Fin p,
      Necklace.kStepVector w (r + (n - 1) * k) k ≠ seq j)

/-- The *aggregate* of a WFS: the pointwise sum of one complete period
    of the WFS vectors. -/
def wfsAggregate (p : ℕ) (seq : Fin p → ZVector StepSize) : ZVector StepSize :=
  fun a => ∑ j : Fin p, seq j a

/-! ### Alternating sequence (AS) -/

/-- A necklace has an *alternating sequence* (AS) if it has a WFS with period 2. -/
def hasAS (w : TernaryNecklace n) : Prop :=
  ∃ (k r : ℕ) (seq : Fin 2 → ZVector StepSize),
    Nat.Coprime k n ∧
    (∀ i : Fin (n - 1),
      Necklace.kStepVector w (r + i.val * k) k =
        seq ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩) ∧
    (∀ j : Fin 2,
      Necklace.kStepVector w (r + (n - 1) * k) k ≠ seq j)

/-! ### SV3 (Strict Variety 3) -/

/-- A ternary necklace is *SV3* (strict variety 3) if for every `k` with `0 < k < n`,
    there are exactly 3 distinct k-step multisets. -/
def isSV3 (w : TernaryNecklace n) : Prop :=
  isTernary w ∧
  ∀ k : ℕ, 0 < k → k < n →
    (Necklace.allKStepMultisets w k).toFinset.card = 3

/-! ### Regular MV3 scales -/

/-- A primitive ternary scale is *odd-regular* if it has odd length and is
    S₃-equivalent to a MOS substitution scale with step signature `(a, a, b)`
    where `b` is odd and `gcd(2a, b) = 1`, constructed from some rotation of
    the binary MOS `(2a)X bZ` by replacing every other X with Y. -/
def isOddRegular (w : TernaryNecklace n) : Prop :=
  Necklace.isPrimitive w ∧
  n % 2 = 1 ∧
  ∃ (σ : Equiv.Perm StepSize) (a b : ℕ),
    a > 0 ∧ b > 0 ∧ b % 2 = 1 ∧ Nat.Coprime (2 * a) b ∧ n = 2 * a + b ∧
    Necklace.count (Necklace.applyPerm σ w) StepSize.L = a ∧
    Necklace.count (Necklace.applyPerm σ w) StepSize.m = a ∧
    Necklace.count (Necklace.applyPerm σ w) StepSize.s = b ∧
    isPartialPairwiseMOS (Necklace.applyPerm σ w) StepSize.L StepSize.m ∧
    isPartialDeletionMOS (Necklace.applyPerm σ w) StepSize.s

/-- A primitive ternary scale is *even-regular* if it has even length and is
    S₃-equivalent to a MOS substitution scale with step signature `(a, a, 2c)`
    where `a` is odd and `gcd(a, c) = 1`, constructed from some rotation of
    the binary MOS `(2a)X (2c)Z` by replacing every other X with Y. -/
def isEvenRegular (w : TernaryNecklace n) : Prop :=
  Necklace.isPrimitive w ∧
  n % 2 = 0 ∧
  ∃ (σ : Equiv.Perm StepSize) (a c : ℕ),
    a > 0 ∧ c > 0 ∧ a % 2 = 1 ∧ Nat.Coprime a c ∧ n = 2 * a + 2 * c ∧
    Necklace.count (Necklace.applyPerm σ w) StepSize.L = a ∧
    Necklace.count (Necklace.applyPerm σ w) StepSize.m = a ∧
    Necklace.count (Necklace.applyPerm σ w) StepSize.s = 2 * c ∧
    isPartialPairwiseMOS (Necklace.applyPerm σ w) StepSize.L StepSize.m ∧
    isPartialDeletionMOS (Necklace.applyPerm σ w) StepSize.s

/-! ### Sporadic patterns -/

/-- Sporadic balanced: S₃-equivalent to XYXZXYX (Fraenkel word, 4X 2Y 1Z). -/
def isSporadicBalanced (w : TernaryNecklace n) : Prop :=
  n = 7 ∧
  ∃ (σ : Equiv.Perm StepSize) (r : ZMod n),
    let w' := fun i => σ (w (i + r))
    w' ((0 : ℕ) : ZMod n) = StepSize.L ∧
    w' ((1 : ℕ) : ZMod n) = StepSize.m ∧
    w' ((2 : ℕ) : ZMod n) = StepSize.L ∧
    w' ((3 : ℕ) : ZMod n) = StepSize.s ∧
    w' ((4 : ℕ) : ZMod n) = StepSize.L ∧
    w' ((5 : ℕ) : ZMod n) = StepSize.m ∧
    w' ((6 : ℕ) : ZMod n) = StepSize.L

/-- Sporadic non-balanced: S₃-equivalent to XYZYX (2X 2Y 1Z). -/
def isSporadicNonBalanced (w : TernaryNecklace n) : Prop :=
  n = 5 ∧
  ∃ (σ : Equiv.Perm StepSize) (r : ZMod n),
    let w' := fun i => σ (w (i + r))
    w' ((0 : ℕ) : ZMod n) = StepSize.L ∧
    w' ((1 : ℕ) : ZMod n) = StepSize.m ∧
    w' ((2 : ℕ) : ZMod n) = StepSize.s ∧
    w' ((3 : ℕ) : ZMod n) = StepSize.m ∧
    w' ((4 : ℕ) : ZMod n) = StepSize.L

/-! ### Twisted MV3 -/

/-- A primitive ternary scale is *twisted MV3* if it has step signature
    `(ka, ka, kb)` for some `k > 1` with `gcd(2a, b) = 1`, constructed from
    a k-fold multi-MOS word with possible boundary X↔Z interchanges, then
    replacing every other X with Y. -/
def isTwistedMV3 (w : TernaryNecklace n) : Prop :=
  Necklace.isPrimitive w ∧
  ∃ (σ : Equiv.Perm StepSize) (k a b : ℕ),
    k > 1 ∧ a > 0 ∧ b > 0 ∧ Nat.Coprime (2 * a) b ∧ n = k * (2 * a + b) ∧
    Necklace.count (Necklace.applyPerm σ w) StepSize.L = k * a ∧
    Necklace.count (Necklace.applyPerm σ w) StepSize.m = k * a ∧
    Necklace.count (Necklace.applyPerm σ w) StepSize.s = k * b

/-! ## AS Property Theorems -/

/-- AS scales have odd length, or are S₃-equivalent to `(XY)^r XZ`
    for some `r ≥ 1`. -/
theorem as_odd_or_special_form (w : TernaryNecklace n)
    (hprim : Necklace.isPrimitive w) (htern : isTernary w) (has : hasAS w) :
    n % 2 = 1 ∨
    ∃ (σ : Equiv.Perm StepSize) (r : ℕ) (rot : ZMod n),
      r ≥ 1 ∧ n = 2 * r + 2 ∧
      ∀ i : Fin n,
        σ (w ((i.val : ZMod n) + rot)) =
          if i.val = n - 1 then StepSize.s
          else if i.val % 2 = 0 then StepSize.L
          else StepSize.m := sorry

/-- Odd AS scales have step signature S₃-equivalent to `(a, b, b)`. -/
theorem as_odd_stepSignature (w : TernaryNecklace n)
    (hprim : Necklace.isPrimitive w) (htern : isTernary w)
    (has : hasAS w) (hodd : n % 2 = 1) :
    ∃ (σ : Equiv.Perm StepSize) (a b : ℕ),
      a > 0 ∧ b > 0 ∧ n = a + 2 * b ∧
      Necklace.count (Necklace.applyPerm σ w) StepSize.L = a ∧
      Necklace.count (Necklace.applyPerm σ w) StepSize.m = b ∧
      Necklace.count (Necklace.applyPerm σ w) StepSize.s = b := sorry

/-- Odd AS scales are SV3. -/
theorem as_odd_isSV3 (w : TernaryNecklace n)
    (hprim : Necklace.isPrimitive w) (htern : isTernary w)
    (has : hasAS w) (hodd : n % 2 = 1) :
    isSV3 w := sorry

/-- Odd AS scales are pairwise-MOS. -/
theorem as_odd_isPairwiseMOS (w : TernaryNecklace n)
    (hprim : Necklace.isPrimitive w) (htern : isTernary w)
    (has : hasAS w) (hodd : n % 2 = 1) :
    isPairwiseMOS w := sorry

/-- Odd AS scales are MOS substitution scales. -/
theorem as_odd_isMOSSubstitution (w : TernaryNecklace n)
    (hprim : Necklace.isPrimitive w) (htern : isTernary w)
    (has : hasAS w) (hodd : n % 2 = 1) :
    isMOSSubstitution w := sorry

/-! ## Pairwise-MOS and Balanced -/

/-- All pairwise-MOS scales are balanced. -/
theorem pairwiseMOS_implies_isBalanced (w : TernaryNecklace n)
    (hprim : Necklace.isPrimitive w) (htern : isTernary w)
    (hpmos : isPairwiseMOS w) :
    Necklace.isBalanced w := sorry

/-! ## Even-Regular Stacking Theorems -/

/-- Even-regular scales consist of two chains of stacked `g`, each with `n/2`
    notes, where `g` is a k-step vector with `gcd(k, n) = 2`.
    Moreover, identifying the two equal-count step sizes (L and m after
    permutation) turns `g` into an unreduced generator of the resulting MOS. -/
theorem evenRegular_two_chains (w : TernaryNecklace n)
    (h : isEvenRegular w) :
    ∃ (σ : Equiv.Perm StepSize) (k : ℕ) (g : ZVector StepSize) (r : ℕ),
      let w' := Necklace.applyPerm σ w
      Nat.gcd k n = 2 ∧
      (∀ i : Fin (n / 2), Necklace.kStepVector w' (r + i.val * k) k = g) ∧
      (∀ i : Fin (n / 2),
        Necklace.kStepVector w' (r + n / 2 + i.val * k) k = g) ∧
      IsUnreducedGenerator (identifyPair w' StepSize.L StepSize.m)
        (ZVector.identifyPair g StepSize.L StepSize.m) := sorry

/-- The two chains of an even-regular scale are offset by the `(n/2)`-step
    interval. -/
theorem evenRegular_chains_offset (w : TernaryNecklace n)
    (h : isEvenRegular w) :
    ∃ (k r : ℕ),
      Nat.gcd k n = 2 ∧
      Necklace.kStepVector w r (n / 2) ≠
        Necklace.kStepVector w (r + k) (n / 2) := sorry

/-- Even-regular scales are balanced. -/
theorem evenRegular_isBalanced (w : TernaryNecklace n)
    (h : isEvenRegular w) :
    Necklace.isBalanced w := sorry

/-! ## Classification of Balanced MV3 -/

/-- Primitive balanced ternary scales are pairwise-MOS. -/
theorem balanced_primitive_ternary_isPairwiseMOS (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (hprim : Necklace.isPrimitive w)
    (htern : isTernary w) :
    isPairwiseMOS w := sorry

/-- Classification of balanced primitive ternary scales:
    sporadic balanced, odd-regular, or even-regular. -/
theorem balanced_primitive_ternary_classification (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (hprim : Necklace.isPrimitive w)
    (htern : isTernary w) :
    isSporadicBalanced w ∨ isOddRegular w ∨ isEvenRegular w := sorry

/-- All primitive balanced ternary scales are MV3. -/
theorem balanced_primitive_ternary_isMV3 (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (hprim : Necklace.isPrimitive w)
    (htern : isTernary w) :
    isMV3 w := sorry

/-- A balanced primitive ternary scale is SV3 iff it is not even-regular. -/
theorem balanced_sv3_iff_not_evenRegular (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (hprim : Necklace.isPrimitive w)
    (htern : isTernary w) :
    isSV3 w ↔ ¬ isEvenRegular w := sorry

/-- Odd-regular balanced scales have a WFS of period 2 (are AS). -/
theorem oddRegular_isAS (w : TernaryNecklace n)
    (h : isOddRegular w) (hbal : Necklace.isBalanced w) :
    hasAS w := sorry

/-! ## Classification of All MV3 -/

/-- Classification of primitive MV3 scales:
    balanced, sporadic non-balanced, or twisted. -/
theorem mv3_classification (w : TernaryNecklace n)
    (hprim : Necklace.isPrimitive w) (hmv3 : isMV3 w) :
    Necklace.isBalanced w ∨ isSporadicNonBalanced w ∨ isTwistedMV3 w := sorry

/-! ## Even-Regular as Interleavings -/

/-- Even-regular scales of length 4 (i.e., `xyxz`) are interleavings of
    a 2-note MOS. -/
theorem evenRegular_four_isInterleaving (w : TernaryNecklace n)
    (h : isEvenRegular w) (hn : n = 4) :
    Necklace.isInterleaving w 2 := sorry

/-- Doubly-even (`n ≡ 0 mod 4`) even-regular scales with `n > 4` are
    interleavings of two copies of a smaller even-regular scale. -/
theorem evenRegular_doubly_even_isInterleaving [NeZero (n / 2)]
    (w : TernaryNecklace n)
    (h : isEvenRegular w) (hmod : n % 4 = 0) (hgt : n > 4) :
    Necklace.isInterleaving w 2 ∧
    isEvenRegular (Necklace.strand2 w ⟨0, by omega⟩) := sorry

/-- Singly-even (`n ≡ 2 mod 4`) even-regular scales are contrainterleavings
    of the two chiralities of an odd-regular scale. -/
theorem evenRegular_singly_even_isContrainterleaving [NeZero (n / 2)]
    (w : TernaryNecklace n)
    (h : isEvenRegular w) (hmod : n % 4 = 2) :
    Necklace.isContrainterleaving w ∧
    isOddRegular (Necklace.strand2 w ⟨0, by omega⟩) := sorry

end TernaryNecklace
