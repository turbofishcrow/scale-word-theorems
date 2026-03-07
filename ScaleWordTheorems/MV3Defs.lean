import ScaleWordTheorems.Basic
import ScaleWordTheorems.MOS
import ScaleWordTheorems.MOSBalanced
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

/-- A necklace is a *k-interleaving* if `k > 1`, `k ∣ n`, and all k strands
    of k-step multisets are rotations of each other. Strand `s` at position `j`
    gives the k-step vector `kStepVector w (j * k + s) k`, a word of length
    `n / k` whose letters are k-step multisets (`ZVector`s). -/
def isInterleaving [DecidableEq α] (w : Necklace α n) (k : ℕ) : Prop :=
  k > 1 ∧
  k ∣ n ∧
  ∀ (s : Fin k),
    ∃ d : ℕ,
      ∀ j : Fin (n / k),
        Necklace.kStepVector w (j.val * k + s.val) k =
        Necklace.kStepVector w ((j.val + d) % (n / k) * k) k

/-- The reversal of a necklace: `w` read backwards, i.e. `fun i => w (n - i)`. -/
def reversal (w : Necklace α n) : Necklace α n :=
  fun i => w (-i)

/-- A necklace is *chiral* if its reversal is not a rotation of itself. -/
def isChiral (w : Necklace α n) : Prop :=
  ¬ ∃ r : ZMod n, ∀ i : ZMod n, w (-i) = w (i + r)

/-- A necklace is a *2-contrainterleaving* if `2 ∣ n` and strand 1 of 2-step
    multisets is the reversal of strand 0 (up to rotation). Strand `s` at
    position `j` gives the 2-step vector `kStepVector w (j * 2 + s) 2`. -/
def isContrainterleaving [DecidableEq α] (w : Necklace α n) : Prop :=
  2 ∣ n ∧
  ∃ d : ℕ,
    -- strand 1 is the reversal of strand 0 (up to rotation d)
    ∀ j : Fin (n / 2),
      Necklace.kStepVector w (j.val * 2 + 1) 2 =
      Necklace.kStepVector w (((n / 2 - 1 - j.val + d) % (n / 2)) * 2) 2

/-- Extract strand `s` from a 2-interleaving: strand `s` consists of the
    2-step vectors at positions `s, s+2, s+4, …`, giving a sub-necklace of
    length `n/2` whose letters are 2-step vectors (`ZVector α`). -/
def strand2 [NeZero (n / 2)] [DecidableEq α] (w : Necklace α n) (s : Fin 2) :
    Necklace (ZVector α) (n / 2) :=
  fun j => Necklace.kStepVector w (j.val * 2 + s.val) 2

end Necklace

/-! ## ZVector pair identification -/

/-- Identify two values `x` and `y` in a `ZVector`: merge the count of `x` into `y`,
    setting the `x`-component to zero. -/
def ZVector.identifyPair [DecidableEq α] (v : ZVector α) (x y : α) : ZVector α :=
  fun a => if a = x then 0 else if a = y then v x + v y else v a

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
    k < n ∧
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

/-- Strict order on binary steps for lexicographic comparison: L < s. -/
private def binaryLt : BinaryStep → BinaryStep → Prop
  | .L, .s => True
  | _, _ => False

/-- A binary list is the lexicographically first rotation (under L < s ordering). -/
def isLexFirstRotation (c : List BinaryStep) : Prop :=
  ∀ r, 0 < r → r < c.length → List.Lex binaryLt c (c.rotate r)

/-- A primitive ternary scale is *twisted MV3* if, up to permutation of step sizes,
    it arises from the alternating substitution φ applied to a boundary-twisted
    power of the lex. first rotation of a primitive binary MOS word (Christoffel word).

    Construction (Bulgakova et al. 2023):
    1. Start with a primitive binary MOS word `c` of length `M = 2a + b` with
       step counts `2a` large and `b` small, where `a > 0`, `b > 0`, `gcd(2a, b) = 1`.
       `c` is the lexicographically first rotation (Christoffel word, L < s).
    2. Form a binary word `u` of length `kM` (for some `k > 1`) that is a
       boundary-twisted `k`-power of `c`: `u` agrees with `c^k` except possibly
       at the `2(k−1)` block-boundary positions, where `(s, L)` pairs may be
       swapped to `(L, s)`
    3. Apply the alternating substitution φ: reading `u` left to right, each `L`
       alternates between `StepSize.L` and `StepSize.m`, each `s` maps to `StepSize.s`
    4. The resulting ternary word, read circularly, equals `w` up to step permutation -/
def isTwistedMV3 (w : TernaryNecklace n) : Prop :=
  Necklace.isPrimitive w ∧
  ∃ (σ : Equiv.Perm StepSize) (k a b : ℕ) (c u : List BinaryStep) (s : ZMod n),
    k > 1 ∧ a > 0 ∧ b > 0 ∧ Nat.Coprime (2 * a) b ∧ n = k * (2 * a + b) ∧
    -- c is a primitive MOS (Christoffel word) of length 2a + b
    c.length = 2 * a + b ∧
    circularHasMOSProperty c ∧
    isLexFirstRotation c ∧
    c.count BinaryStep.L = 2 * a ∧
    c.count BinaryStep.s = b ∧
    -- u is a boundary-twisted k-power of c
    TwistedConstruction.isBoundaryTwistedPower u c k ∧
    -- Some rotation of w equals φ(u) up to S₃ permutation σ
    -- (the starting position s determines the block boundaries for twisting)
    (List.ofFn (fun i : Fin n => σ (w (s + i.val : ZMod n)))) =
      TwistedConstruction.phiSubst u

/-- The deep combinatorial fact: a necklace that reads off φ(u), where u is a
    boundary-twisted power of a Christoffel word, has ≤ 3 distinct k-step multisets.

    This encapsulates the core argument of Bulgakova–Buzhinsky–Goncharov (2023), Claim 4:
    the spectrum of each power of a twisted MV3 scale matches that of the corresponding
    power of the underlying interleaved MOS, which has abelian complexity ≤ 3. -/
private lemma phiSubst_twistedPower_multisets_le_three
    (K a b : ℕ) (c u : List BinaryStep)
    (hK : K > 1) (ha : a > 0) (hb : b > 0)
    (hcop : Nat.Coprime (2 * a) b)
    (hclen : c.length = 2 * a + b)
    (hcL : c.count BinaryStep.L = 2 * a)
    (hcs : c.count BinaryStep.s = b)
    (hmos : circularHasMOSProperty c)
    (hlex : isLexFirstRotation c)
    (htwist : TwistedConstruction.isBoundaryTwistedPower u c K)
    (N : ℕ) (hN : N = K * (2 * a + b))
    [NeZero N]
    (v : Necklace StepSize N)
    (hv : List.ofFn (fun i : Fin N => v (↑i.val : ZMod N)) =
      TwistedConstruction.phiSubst u)
    (d : ℕ) (hd : 0 < d) (hdN : d < N) :
    (Necklace.allKStepMultisets v d).toFinset.card ≤ 3 := sorry

/-- Twisted MV3 scales are MV3 (have at most 3 distinct k-step multisets for each k).

    **Proof outline** (Bulgakova et al. 2023, Claim 4):
    The alternating substitution φ applied to a boundary-twisted Christoffel
    word power produces a ternary word whose 2-step intervals come from stacking
    2-steps of the underlying MOS. The interleaving structure of φ ensures that
    each k-step subword has at most 3 distinct abelianizations. The key observation
    is that w is a 2-strand interleaving, and each strand's k-step structure is
    controlled by the primitive MOS c. -/
theorem twistedMV3_isMV3 (w : TernaryNecklace n)
    (h : isTwistedMV3 w) : isMV3 w := by
  obtain ⟨hprim, σ, K, a, b, c, u, s, hK, ha, hb, hcop, hn, hclen,
          hmos, hlex, hcL, hcs, htwist, hofn⟩ := h
  -- Define rotated and permuted necklaces
  set w' : Necklace StepSize n := fun i => w (i + s) with hw'_def
  set wσ : Necklace StepSize n := Necklace.applyPerm σ w' with hwσ_def
  -- List.ofFn of wσ equals phiSubst u (from hofn, adjusting commutativity)
  have hofn' : List.ofFn (fun i : Fin n => wσ (↑i.val : ZMod n)) =
      TwistedConstruction.phiSubst u := by
    have : (fun i : Fin n => wσ (↑i.val : ZMod n)) =
        (fun i : Fin n => σ (w (s + ↑i.val : ZMod n))) := by
      funext i
      simp only [hwσ_def, Necklace.applyPerm_apply, hw'_def]
      congr 2; ring
    rw [this]; exact hofn
  -- phiSubst u has all three step sizes
  have hL_count : u.count BinaryStep.L ≥ 2 := by
    rw [htwist.2.2.1, hcL]; nlinarith
  have hs_count : u.count BinaryStep.s ≥ 1 := by
    rw [htwist.2.2.2.1, hcs]; nlinarith
  obtain ⟨hL_mem, hm_mem, hs_mem⟩ := TwistedConstruction.phiSubst_isTernary u hL_count hs_count
  -- wσ is ternary (each step size appears in phiSubst u, hence in wσ)
  have htern_wσ : isTernary wσ := by
    rw [isTernary_iff_forall]
    intro a
    have hmem : a ∈ TwistedConstruction.phiSubst u := by cases a <;> assumption
    rw [← hofn', List.mem_iff_getElem] at hmem
    obtain ⟨idx, hidx, hget⟩ := hmem
    simp only [List.getElem_ofFn] at hget
    exact ⟨(↑idx : ZMod n), hget⟩
  -- w' is ternary (by permutation invariance)
  have htern_w' : isTernary w' := (isTernary_applyPerm σ w').mp htern_wσ
  -- w is ternary (rotation preserves ternarity)
  have htern : isTernary w := by
    rw [isTernary_iff_forall]
    intro a
    obtain ⟨i, hi⟩ := (isTernary_iff_forall w').mp htern_w' a
    exact ⟨i + s, hi⟩
  constructor
  · exact htern
  · intro k hk hkn
    -- card(allKStepMultisets w k) = card(... w' ...) by rotation invariance
    have h_rot : (Necklace.allKStepMultisets w k).toFinset.card =
        (Necklace.allKStepMultisets w' k).toFinset.card := by
      rw [← allKStepMultisets_toFinset_card_rotate w s k]
    -- card(... w' ...) = card(... wσ ...) by permutation invariance
    have h_perm : (Necklace.allKStepMultisets w' k).toFinset.card =
        (Necklace.allKStepMultisets wσ k).toFinset.card := by
      rw [Necklace.allKStepMultisets_toFinset_card_applyPerm σ w' k]
    rw [h_rot, h_perm]
    exact phiSubst_twistedPower_multisets_le_three K a b c u
      hK ha hb hcop hclen hcL hcs hmos hlex htwist n hn wσ hofn' k hk hkn


end TernaryNecklace
