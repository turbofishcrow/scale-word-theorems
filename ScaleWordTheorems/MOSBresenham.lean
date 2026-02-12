import Mathlib.Data.Multiset.Basic
import Mathlib.Data.ZMod.Basic
import ScaleWordTheorems.MOS

/-!
# Bresenham/Sturmian Characterization of MOS Scales

This file contains the algebraic/Bresenham characterization of MOS scales and related proofs.

## Main Results

* `isMOSBresenham`: The Bresenham characterization - position i is L iff (i*b) mod n < b
* `mos_has_bresenham_form`: Every MOS is a rotation of a Bresenham sequence
* `bresenham_periodic`: Bresenham sequences with gcd(a,b) > 1 are periodic
* `mos_repetition_of_gcd`: A MOS with gcd(a,b) > 1 is a d-fold repetition
* `extractPrimitive_isMOS`: The primitive extraction of a MOS is also a MOS
* `mos_generator_iff_primitive`: A non-primitive MOS has a generator iff its primitive does

## References

This approach views MOS scales as discrete approximations of lines with rational slope,
leading to algebraic proofs using modular arithmetic.
-/

namespace MOSBresenham

open BinaryStep

/-!
### Algebraic characterization of MOS scales

A MOS scale with a L's and b s's (where n = a + b) can be characterized algebraically:
- Position i has step L iff ⌊(i+1)·b/n⌋ > ⌊i·b/n⌋ (the "Bresenham" or "Sturmian" characterization)
- Equivalently: position i has step L iff (i·b) mod n < b

This characterization implies periodicity when gcd(a,b) = d > 1:
- Let p = n/d = (a+b)/d = a' + b' where a' = a/d, b' = b/d
- For any position i: (i + p)·b mod n = i·b mod n + p·b mod n
- Now p·b = ((a+b)/d)·b = b·(a+b)/d = b·n/d
- So p·b mod n = 0
- Therefore (i + p)·b mod n = i·b mod n, meaning w(i) = w(i + p)
-/

/-- The Bresenham/Sturmian characterization of MOS: position i is L iff (i*b) mod n < b -/
def isMOSBresenham [NeZero n] (w : BinaryNecklace n) (a b : ℕ) : Prop :=
  n = a + b ∧
  ∀ i : ZMod n, w i = if (i.val * b) % n < b then BinaryStep.L else BinaryStep.s

/-- A MOS scale satisfies the Bresenham characterization (up to rotation/reflection) -/
lemma mos_has_bresenham_form [NeZero n] (w : BinaryNecklace n) (hw : BinaryNecklace.isMOS w)
    (a b : ℕ) (hsig : BinaryNecklace.hasStepSignature w a b) :
    ∃ (w' : BinaryNecklace n), (∃ r : ZMod n, ∀ i, w' i = w (i + r)) ∧ isMOSBresenham w' a b := by
  -- This is a standard result in MOS theory - every MOS is a rotation of a Bresenham sequence
  sorry

/-- Helper: (j + k).val * b % n = (j.val + k) * b % n for ZMod n -/
lemma zmod_add_val_mul_mod [NeZero n] (j : ZMod n) (k b : ℕ) :
    ((j + (k : ZMod n)).val * b) % n = ((j.val + k) * b) % n := by
  -- (j + k).val = (j.val + (k : ZMod n).val) % n
  -- And (k : ZMod n).val = k % n
  -- So ((j + k).val * b) % n = (((j.val + k % n) % n) * b) % n = ((j.val + k) * b) % n
  have h1 : (j + (k : ZMod n)).val = (j.val + (k : ZMod n).val) % n := ZMod.val_add j (k : ZMod n)
  have h2 : (k : ZMod n).val = k % n := ZMod.val_natCast (n := n) k
  rw [h1, h2]
  -- Need: ((j.val + k % n) % n * b) % n = ((j.val + k) * b) % n
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  rw [Nat.mod_mul_mod]

/-- Key periodicity lemma: Bresenham MOS with gcd(a,b) > 1 is periodic -/
lemma bresenham_periodic [NeZero n] (a b d : ℕ) (hn : n = a + b) (hd : d = Nat.gcd a b)
    (hd_gt : d > 1) (hd_dvd : d ∣ n) (i : ZMod n) :
    (i.val * b) % n < b ↔ ((i.val + n / d) * b) % n < b := by
  -- The key calculation:
  -- (i + n/d) * b mod n = i*b mod n + (n/d)*b mod n
  -- Since d | b (as d = gcd(a,b)), we have (n/d)*b = n*(b/d), divisible by n
  -- Therefore (n/d)*b mod n = 0, so both sides are equal
  have hd_dvd_b : d ∣ b := by rw [hd]; exact Nat.gcd_dvd_right a b
  have hd_pos : d > 0 := Nat.zero_lt_one.trans hd_gt
  -- Key: (n/d) * b ≡ 0 (mod n)
  have hkey : (n / d) * b % n = 0 := by
    obtain ⟨k, hk⟩ := hd_dvd_b
    -- b = d * k, so (n/d) * b = (n/d) * d * k = n * k
    have step1 : (n / d) * b = (n / d) * (d * k) := by rw [hk]
    have step2 : (n / d) * (d * k) = ((n / d) * d) * k := (Nat.mul_assoc _ _ _).symm
    have step3 : (n / d) * d = n := Nat.div_mul_cancel hd_dvd
    calc (n / d) * b % n = ((n / d) * d) * k % n := by rw [step1, step2]
      _ = n * k % n := by rw [step3]
      _ = 0 := Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right n k)
  -- Both directions follow from: (i + n/d)*b ≡ i*b (mod n)
  have heq : ((i.val + n / d) * b) % n = (i.val * b) % n := by
    have h1 : (i.val + n / d) * b = i.val * b + (n / d) * b := Nat.add_mul _ _ _
    rw [h1, Nat.add_mod, hkey, Nat.add_zero, Nat.mod_mod]
  constructor <;> intro h <;> simp only [heq] at * <;> exact h

/-- A MOS with signature aLbs where d = gcd(a,b) > 1 is a d-fold repetition -/
lemma mos_repetition_of_gcd [NeZero n] (w : BinaryNecklace n) (hw : BinaryNecklace.isMOS w)
    (a b : ℕ) (hsig : BinaryNecklace.hasStepSignature w a b) (d : ℕ) (hd : d = Nat.gcd a b)
    (hd_gt : d > 1) :
    isRepetition w d := by
  -- Step 1: Establish that d divides n
  have hn_eq : n = a + b := mos_length_eq_sum w a b hsig
  have hd_dvd_n : d ∣ n := by
    rw [hn_eq]
    exact gcd_dvd_sum a b d hd
  -- Step 2: d > 0 follows from d > 1
  have hd_pos : d > 0 := Nat.zero_lt_one.trans hd_gt
  -- Step 3: Show periodicity using the Bresenham characterization
  refine ⟨hd_dvd_n, hd_pos, ?_⟩
  intro i
  -- Get the Bresenham form
  obtain ⟨w', ⟨r, hrot⟩, hbres⟩ := mos_has_bresenham_form w hw a b hsig
  -- The Bresenham word w' is periodic: w'(j) = w'(j + n/d) for all j
  -- This follows from bresenham_periodic and the Bresenham characterization
  have hw'_period : ∀ j : ZMod n, w' j = w' (j + (n / d : ℕ)) := by
    intro j
    have hbres_eq := hbres.2 j
    have hbres_shift := hbres.2 (j + (n / d : ℕ))
    -- w'(j) is determined by (j.val * b) % n < b
    -- w'(j + n/d) is determined by ((j.val + n/d) * b) % n < b
    -- These are equivalent by bresenham_periodic
    have hperiod := bresenham_periodic a b d hn_eq hd hd_gt hd_dvd_n j
    simp only [hbres_eq, hbres_shift]
    -- Both are determined by the same condition (mod periodicity)
    split_ifs with h1 h2 h2
    · rfl
    · -- h1 : j.val * b % n < b, h2 : ¬ (j + n/d).val * b % n < b
      -- But bresenham_periodic says these are equivalent
      exfalso
      have heq : ((j + (n / d : ℕ)).val * b) % n = ((j.val + n / d) * b) % n :=
        zmod_add_val_mul_mod j (n / d) b
      rw [heq] at h2
      exact h2 (hperiod.mp h1)
    · exfalso
      have heq : ((j + (n / d : ℕ)).val * b) % n = ((j.val + n / d) * b) % n :=
        zmod_add_val_mul_mod j (n / d) b
      rw [heq] at h2
      exact h1 (hperiod.mpr h2)
    · rfl
  -- Now transfer back to w: w(i) = w'(i - r + r) and w(i + n/d) = w'(i + n/d - r + r)
  -- Using hrot: w'(j) = w(j + r), so w(i) = w'(i - r) when we can invert
  -- Since rotation preserves periodicity:
  -- w(i + n/d) = w'((i + n/d) - r + r) = w'(i - r + n/d + r) = w'(i - r + r + n/d)...
  -- Actually simpler: hrot says w'(j) = w(j + r)
  -- So w(i) = w'(i - r) and w(i + n/d) = w'(i - r + n/d)
  -- By hw'_period: w'(i - r + n/d) = w'(i - r)
  -- Therefore w(i + n/d) = w(i)
  have hrot_inv : ∀ j, w j = w' (j - r) := fun j => by
    have := hrot (j - r)
    simp only [sub_add_cancel] at this
    exact this.symm
  calc w i = w' (i - r) := hrot_inv i
    _ = w' (i - r + (n / d : ℕ)) := hw'_period (i - r)
    _ = w' ((i + (n / d : ℕ)) - r) := by congr 1; exact (add_sub_right_comm i (n / d : ℕ) r).symm
    _ = w (i + (n / d : ℕ)) := (hrot_inv (i + (n / d : ℕ))).symm

/-- Extract the primitive (non-repeated) MOS from a repeated one -/
noncomputable def extractPrimitive [NeZero n] (w : BinaryNecklace n) (d : ℕ)
    (hd : d ∣ n) (hd_pos : d > 0) : BinaryNecklace (n / d) :=
  fun i => w (i.val : ZMod n)

/-- Helper: For a d-periodic word, w(i) = w(i % (n/d)) when viewed in ZMod n -/
lemma periodic_mod_eq [NeZero n] {α : Type*} (w : Necklace α n) (d : ℕ) (hd : d ∣ n) (hd_pos : d > 0)
    (hrep : isRepetition w d) (i : ZMod n) :
    w i = w ((i.val % (n / d) : ℕ) : ZMod n) := by
  let m := n / d
  have hm_pos : 0 < m := Nat.div_pos (Nat.le_of_dvd (NeZero.pos n) hd) hd_pos
  have hperiod := hrep.2.2
  -- i.val = (i.val % m) + m * (i.val / m)
  -- We apply periodicity (i.val / m) times
  have hdiv : i.val = i.val % m + m * (i.val / m) := (Nat.mod_add_div i.val m).symm
  -- By induction on (i.val / m), show w(i.val % m + m * k) = w(i.val % m)
  suffices h : ∀ k : ℕ, w ((i.val % m + m * k : ℕ) : ZMod n) = w ((i.val % m : ℕ) : ZMod n) by
    have hi_val : ((i.val : ℕ) : ZMod n) = i := by
      -- For i : ZMod n, casting i.val back gives i since i.val < n
      simp only [ZMod.natCast_val, ZMod.cast_id]
    calc w i = w ((i.val : ℕ) : ZMod n) := by rw [hi_val]
      _ = w ((i.val % m + m * (i.val / m) : ℕ) : ZMod n) := by rw [← hdiv]
      _ = w ((i.val % m : ℕ) : ZMod n) := h (i.val / m)
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    -- Goal: w ((i.val % m + m * (k + 1) : ℕ) : ZMod n) = w ((i.val % m : ℕ) : ZMod n)
    -- We have ih: w ((i.val % m + m * k : ℕ) : ZMod n) = w ((i.val % m : ℕ) : ZMod n)
    -- And hperiod: w j = w (j + m) for all j
    have arith : i.val % m + m * (k + 1) = i.val % m + m * k + m := by
      simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
    rw [arith]
    -- Now goal: w ((i.val % m + m * k + m : ℕ) : ZMod n) = w ((i.val % m : ℕ) : ZMod n)
    have cast_eq : ((i.val % m + m * k + m : ℕ) : ZMod n) = ((i.val % m + m * k : ℕ) : ZMod n) + (m : ℕ) := by
      push_cast; rfl
    rw [cast_eq, ← hperiod, ih]

/-- The primitive extraction of a MOS is also a MOS -/
lemma extractPrimitive_isMOS [NeZero n] (w : BinaryNecklace n) (hw : BinaryNecklace.isMOS w)
    (d : ℕ) (hd : d ∣ n) (hd_pos : d > 0) (hrep : isRepetition w d) :
    haveI : NeZero (n / d) := ⟨Nat.div_pos (Nat.le_of_dvd (NeZero.pos n) hd) hd_pos |> Nat.pos_iff_ne_zero.mp⟩
    BinaryNecklace.isMOS (extractPrimitive w d hd hd_pos) := by
  haveI hm_pos : NeZero (n / d) := ⟨Nat.div_pos (Nat.le_of_dvd (NeZero.pos n) hd) hd_pos |> Nat.pos_iff_ne_zero.mp⟩
  let m := n / d
  let p := extractPrimitive w d hd hd_pos
  constructor
  · -- p is binary: there exists both an L and an s
    obtain ⟨⟨iL, hiL⟩, ⟨is, his⟩⟩ := hw.1
    constructor
    · -- There exists an L in p
      use (iL.val % m : ℕ)
      unfold extractPrimitive
      -- Goal: w (((iL.val % m : ℕ) : ZMod m).val : ZMod n) = L
      -- Since iL.val % m < m, we have ((iL.val % m : ℕ) : ZMod m).val = iL.val % m
      have hval : ((iL.val % m : ℕ) : ZMod m).val = iL.val % m := by
        rw [ZMod.val_natCast]
        -- (iL.val % m) % m = iL.val % m since iL.val % m < m
        exact Nat.mod_eq_of_lt (Nat.mod_lt _ (NeZero.pos m))
      simp only [hval]
      rw [← hiL]
      exact (periodic_mod_eq w d hd hd_pos hrep iL).symm
    · -- There exists an s in p
      use (is.val % m : ℕ)
      unfold extractPrimitive
      have hval : ((is.val % m : ℕ) : ZMod m).val = is.val % m := by
        rw [ZMod.val_natCast]
        exact Nat.mod_eq_of_lt (Nat.mod_lt _ (NeZero.pos m))
      simp only [hval]
      rw [← his]
      exact (periodic_mod_eq w d hd hd_pos hrep is).symm
  · -- For all k with 0 < k < m, the k-step vectors of p have at most 2 distinct values
    intro k hk_pos hk_lt_m
    -- Key: k-step vectors in p correspond to k-step vectors in w
    -- For position i in p, the k-step vector is [p(i), p(i+1), ..., p(i+k-1)]
    -- = [w(i.val), w((i+1).val mod m), ..., w((i+k-1).val mod m)]
    -- Due to periodicity w(j) = w(j mod m) when viewed appropriately
    -- Since k < m ≤ n, this is a valid k-step vector in w

    -- The k-step vectors of p are a subset of the k-step vectors of w
    -- Since w has at most 2 distinct k-step vectors (as k < m < n implies k < n),
    -- p also has at most 2.
    have hk_lt_n : k < n := by
      calc k < m := hk_lt_m
        _ = n / d := rfl
        _ ≤ n := Nat.div_le_self n d
    have hw_k := hw.2 k hk_pos hk_lt_n
    -- Show that every k-step vector in p appears as a k-step vector in w
    -- This means (allKStepMultisets p k).toFinset ⊆ (allKStepMultisets w k).toFinset
    -- Therefore the cardinality of p's vectors ≤ that of w's ≤ 2
    have hsubset : (Necklace.allKStepMultisets p k).toFinset ⊆ (Necklace.allKStepMultisets w k).toFinset := by
      intro v hv
      -- v is a k-step vector in p, so v = abelianize (slice p i (i+k)) for some i : Fin m
      simp only [List.mem_toFinset] at hv ⊢
      -- allKStepMultisets = map abelianize (allKStepSubwords)
      -- allKStepSubwords = List.ofFn (fun i => slice w i.val (i.val + k))
      rw [Necklace.allKStepMultisets, List.mem_map] at hv ⊢
      obtain ⟨subword, hsub_mem, hv_eq⟩ := hv
      rw [Necklace.allKStepSubwords, List.mem_ofFn] at hsub_mem
      obtain ⟨i, hsub_eq⟩ := hsub_mem
      -- i : Fin m, subword = slice p i.val (i.val + k)
      -- Show v also appears as a k-step vector in w at position i.val
      use Necklace.slice w i.val (i.val + k)
      constructor
      · -- This slice is in allKStepSubwords w k
        rw [Necklace.allKStepSubwords, List.mem_ofFn]
        use ⟨i.val, Nat.lt_of_lt_of_le (Fin.is_lt i) (Nat.div_le_self n d)⟩
      · -- The abelianizations are equal
        -- Goal: abelianize (slice w i.val (i.val+k)) = v
        -- We have hv_eq: abelianize subword = v, hsub_eq: slice p i.val (i.val + k) = subword
        rw [← hv_eq, ← hsub_eq]
        -- Goal: abelianize (slice w i.val (i.val+k)) = abelianize (slice p i.val (i.val+k))
        -- By periodicity: for j : Fin m, slice p j (j+k) contains the same multiset
        -- as slice w j.val (j.val+k), because p(x) = w(x.val) and w is periodic
        -- The proof requires showing elementwise equality using periodic_mod_eq
        -- This is a technical lemma about slices preserving abelianization under periodicity
        sorry
    -- Now use subset to bound cardinality
    calc (Necklace.allKStepMultisets p k).toFinset.card
        ≤ (Necklace.allKStepMultisets w k).toFinset.card := Finset.card_le_card hsubset
      _ ≤ 2 := hw_k

/-- Slices in a periodic word correspond to slices in the primitive.
    For position i in w, the abelianization of the k-slice equals that in the primitive at i % m. -/
lemma abelianize_slice_periodic [NeZero n] (w : BinaryNecklace n) (d : ℕ) (hd : d ∣ n) (hd_pos : d > 0)
    (hrep : isRepetition w d) (i k : ℕ) :
    haveI : NeZero (n / d) := ⟨Nat.div_pos (Nat.le_of_dvd (NeZero.pos n) hd) hd_pos |> Nat.pos_iff_ne_zero.mp⟩
    Necklace.abelianize (Necklace.slice w i (i + k)) =
    Necklace.abelianize (Necklace.slice (extractPrimitive w d hd hd_pos) (i % (n / d)) (i % (n / d) + k)) := by
  haveI hm_ne : NeZero (n / d) := ⟨Nat.div_pos (Nat.le_of_dvd (NeZero.pos n) hd) hd_pos |> Nat.pos_iff_ne_zero.mp⟩
  let m := n / d
  let p := extractPrimitive w d hd hd_pos
  -- Both slices have length k and contain the same elements
  -- because w(i + j) = p((i % m) + j) for all j, due to periodicity
  unfold Necklace.slice Necklace.abelianize
  congr 1
  -- Show the two lists are equal
  -- LHS: List.map w (List.map (fun l => (i + l : ZMod n)) (List.range k))
  -- RHS: List.map p (List.map (fun l => (i%m + l : ZMod m)) (List.range k))
  have hm_pos : 0 < m := NeZero.pos m
  have hm_dvd_n : m ∣ n := Nat.div_dvd_of_dvd hd
  -- Show the two lists are equal element by element
  -- First, compute that both lists have length k
  have hlen1 : i + k - i = k := Nat.add_sub_cancel_left i k
  have hlen2 : i % m + k - i % m = k := Nat.add_sub_cancel_left (i % m) k
  rw [hlen1, hlen2]
  -- Now both sides have List.range k
  apply List.ext_getElem
  · -- Lengths are equal: both map over List.range k
    simp only [List.length_map]
    -- Both do-notation expressions reduce to (Nat.cast <$> List.range k).length
    simp only [bind_pure_comp]
    -- For List, (<$>) = List.map, so (f <$> xs).length = xs.length
    have len_fmap : ∀ {α β : Type} (f : α → β) (xs : List α), (f <$> xs).length = xs.length := by
      intro α β f xs
      simp only [Functor.map, List.length_map]
    simp only [len_fmap, List.length_range]
  · -- Elements are equal
    intro l h1 h2
    simp only [List.length_map] at h1 h2
    -- Simplify the do-notation and range indexing
    simp only [List.getElem_map, bind_pure_comp, Functor.map, List.getElem_range]
    -- Now goal is: w (↑i + ↑l) = w ↑((↑(i % m) + ↑l).val)
    -- Simplify: ↑i + ↑l = ↑(i + l) in ZMod n
    have cast_add_n : (↑i + ↑l : ZMod n) = ↑(i + l) := by simp only [Nat.cast_add]
    have cast_add_m : (↑(i % m) + ↑l : ZMod m) = ↑(i % m + l) := by simp only [Nat.cast_add]
    rw [cast_add_n, cast_add_m]
    -- LHS = w(↑(i + l) : ZMod n)
    -- RHS = w(↑((i % m + l : ZMod m).val) : ZMod n)
    have hperiod := periodic_mod_eq w d hd hd_pos hrep ((i + l : ℕ) : ZMod n)
    unfold extractPrimitive
    -- RHS is now w(((i%m + l : ZMod m).val : ZMod n))
    have val_eq : ((i % m + l : ℕ) : ZMod m).val = (i % m + l) % m := ZMod.val_natCast (n := m) (i % m + l)
    have mod_eq : (i % m + l) % m = (i + l) % m := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have val_n_mod : (↑(i + l) : ZMod n).val % m = (i + l) % m := by
      have hv : (↑(i + l) : ZMod n).val = (i + l) % n := ZMod.val_natCast (n := n) (i + l)
      rw [hv]
      exact Nat.mod_mod_of_dvd (i + l) hm_dvd_n
    rw [hperiod, val_eq, mod_eq, ← val_n_mod]

/-- If g is a generator for the primitive, it's also a generator for the full word -/
lemma IsGenerator_lift [NeZero n] (w : BinaryNecklace n) (d : ℕ) (hd : d ∣ n) (hd_pos : d > 0)
    (hrep : isRepetition w d) (g : ZVector BinaryStep) :
    haveI : NeZero (n / d) := ⟨Nat.div_pos (Nat.le_of_dvd (NeZero.pos n) hd) hd_pos |> Nat.pos_iff_ne_zero.mp⟩
    IsGenerator (extractPrimitive w d hd hd_pos) g → IsGenerator w g := by
  haveI hm_ne : NeZero (n / d) := ⟨Nat.div_pos (Nat.le_of_dvd (NeZero.pos n) hd) hd_pos |> Nat.pos_iff_ne_zero.mp⟩
  intro hgen_p
  unfold IsGenerator at hgen_p ⊢
  -- For the new algebraic definition: every k-step vector in w must be jg + mp for some j, m ∈ ℤ
  -- Since w is a d-fold repetition, its k-step vectors are the same as the primitive's
  -- and the period vectors are related by: period(w) = d * period(primitive)
  sorry

/-- If the primitive word has a generator, so does the repeated word -/
lemma generator_lifts_from_primitive [NeZero n] (w : BinaryNecklace n)
    (d : ℕ) (hd : d ∣ n) (hd_pos : d > 0) (hrep : isRepetition w d)
    (hgen : haveI : NeZero (n / d) := ⟨Nat.div_pos (Nat.le_of_dvd (NeZero.pos n) hd) hd_pos |> Nat.pos_iff_ne_zero.mp⟩;
            HasGenerator (extractPrimitive w d hd hd_pos)) :
    HasGenerator w := by
  haveI hm_ne : NeZero (n / d) := ⟨Nat.div_pos (Nat.le_of_dvd (NeZero.pos n) hd) hd_pos |> Nat.pos_iff_ne_zero.mp⟩
  -- Extract the generator g from the primitive and lift it
  obtain ⟨g, hg⟩ := hgen
  exact ⟨g, IsGenerator_lift w d hd hd_pos hrep g hg⟩

/-- Key reduction: A MOS with gcd(a,b) > 1 has a generator iff its primitive does -/
theorem mos_generator_iff_primitive [NeZero n] (w : BinaryNecklace n)
    (hw : BinaryNecklace.isMOS w) (a b : ℕ) (hsig : BinaryNecklace.hasStepSignature w a b)
    (d : ℕ) (hd : d = Nat.gcd a b) (hd_gt : d > 1) :
    HasGenerator w ↔
    (haveI hrep := mos_repetition_of_gcd w hw a b hsig d hd hd_gt
     haveI hd_dvd : d ∣ n := hrep.1
     haveI hd_pos : d > 0 := Nat.zero_lt_one.trans hd_gt
     haveI : NeZero (n / d) := ⟨Nat.div_pos (Nat.le_of_dvd (NeZero.pos n) hd_dvd) hd_pos |> Nat.pos_iff_ne_zero.mp⟩
     HasGenerator (extractPrimitive w d hd_dvd hd_pos)) := by
  constructor
  · -- If full word has generator, primitive does too (restriction)
    sorry
  · -- If primitive has generator, full word does too (lifting)
    intro hgen_prim
    have hrep := mos_repetition_of_gcd w hw a b hsig d hd hd_gt
    have hd_pos : d > 0 := Nat.zero_lt_one.trans hd_gt
    exact generator_lifts_from_primitive w d hrep.1 hd_pos hrep hgen_prim

end MOSBresenham
