import ScaleWordTheorems.MV3EvenRegular

open BigOperators

namespace TernaryNecklace

variable {n : ℕ} [NeZero n]

/-! ## Even-Regular as Interleavings -/

/-- Half-period swap: in an even-regular data scale, shifting by `n/2`
    swaps L and m while keeping s fixed. This follows from:
    1. The binary MOS `B` has period `p = n/2`, so `B(i) = B(i+p)`.
    2. The deletion word (non-s letters in order) is alternating `LmLm…`.
    3. Since there are `a` (odd) X-positions per period, the L/m assignment
       flips between the two halves. -/
private lemma half_period_swap (w : TernaryNecklace n)
    (a c : ℕ) (_ha_pos : a > 0) (_hc_pos : c > 0) (ha_odd : a % 2 = 1)
    (hcop : Nat.Coprime a c) (hn : n = 2 * a + 2 * c)
    (hcountL : Necklace.count w .L = a) (hcountm : Necklace.count w .m = a)
    (hcounts : Necklace.count w .s = 2 * c)
    (_hmos : isPartialPairwiseMOS w .L .m)
    (hdel : isPartialDeletionMOS w .s)
    (i : ℕ) :
    w ((i + n / 2 : ℕ) : ZMod n) =
    match w ((i : ℕ) : ZMod n) with | .L => .m | .m => .L | .s => .s := by
  have hn_pos : n > 0 := by omega
  set p := n / 2 with hp_def
  have hp_val : p = a + c := by omega
  -- ===== Binary MOS setup =====
  set B := identifiedToBinary (TernaryNecklace.identifyPair w .L .m) with hB_def
  have hB_mos : BinaryNecklace.isMOS B :=
    identifiedToBinary_isMOS w hcountL hcountm hcounts _ha_pos (by omega) _hmos
  have hB_countL : Necklace.count B .L = 2 * a :=
    identifiedToBinary_count_L w hcountL hcountm
  have hB_counts_val : Necklace.count B .s = 2 * c :=
    identifiedToBinary_count_s w hcounts
  have hB_period : (Necklace.period B).length = p := by
    have := binary_mos_period_half a c _ha_pos _hc_pos hcop hn B hB_mos hB_countL hB_counts_val
    omega
  -- B(j) = .s ↔ w(j) = .s
  have hB_s_iff : ∀ j : ℕ, B ((j : ℕ) : ZMod n) = BinaryStep.s ↔
      w ((j : ℕ) : ZMod n) = .s := by
    intro j
    simp only [hB_def, identifiedToBinary, Function.comp, TernaryNecklace.identifyPair]
    cases w ((j : ℕ) : ZMod n) <;> simp [msToBinary]
  -- B(j) = B(j + p)
  have hB_shift : ∀ j, B ((j : ℕ) : ZMod n) = B (((j + p) : ℕ) : ZMod n) := by
    intro j
    have h1 := period_pointwise B j; rw [hB_period] at h1
    have h2 := period_pointwise B (j + p)
    rw [hB_period, Nat.add_mod_right] at h2
    exact h1.trans h2.symm
  -- s ↔ s under shift
  have hs_iff : ∀ j, w ((j : ℕ) : ZMod n) = .s ↔ w (((j + p) : ℕ) : ZMod n) = .s := by
    intro j; rw [← hB_s_iff j, ← hB_s_iff (j + p)]
    exact ⟨fun h => hB_shift j ▸ h, fun h => (hB_shift j).symm ▸ h⟩
  -- ===== Suffices: non-s positions swap =====
  suffices hswap : w ((i : ℕ) : ZMod n) ≠ .s →
      w (((i + p) : ℕ) : ZMod n) ≠ w ((i : ℕ) : ZMod n) by
    rcases hw : w ((i : ℕ) : ZMod n) with _ | _ | _
    · -- w(i) = .L → w(i+p) = .m
      have hne := hswap (by rw [hw]; decide)
      rw [hw] at hne
      have hns_ip : w (((i + p) : ℕ) : ZMod n) ≠ .s := by
        intro h; rw [← hs_iff] at h; rw [hw] at h; exact absurd h (by decide)
      rcases hw' : w (((i + p) : ℕ) : ZMod n) with _ | _ | _
      · exact absurd hw' hne
      · rfl
      · exact absurd hw' hns_ip
    · -- w(i) = .m → w(i+p) = .L
      have hne := hswap (by rw [hw]; decide)
      rw [hw] at hne
      have hns_ip : w (((i + p) : ℕ) : ZMod n) ≠ .s := by
        intro h; rw [← hs_iff] at h; rw [hw] at h; exact absurd h (by decide)
      rcases hw' : w (((i + p) : ℕ) : ZMod n) with _ | _ | _
      · rfl
      · exact absurd hw' hne
      · exact absurd hw' hns_ip
    · -- w(i) = .s → w(i+p) = .s
      exact (hs_iff i).mp hw
  -- ===== Alternation argument =====
  intro hw_ne_s
  -- Set up deletion word D
  set D := TernaryNecklace.orderedDeletion w .s with hD_def
  have hDlen : D.length = 2 * a := by
    have := orderedDeletion_length w .s; rw [hcounts] at this; linarith
  have hDlen_pos : 0 < D.length := by linarith
  have hbin : ∀ j, (hj : j < D.length) → D[j] = .L ∨ D[j] = .m := by
    intro j hj
    have hmem := List.getElem_mem hj
    simp only [D, TernaryNecklace.orderedDeletion, List.mem_filter,
      decide_eq_true_eq] at hmem
    rcases hval : D[j] with _ | _ | _
    · left; rfl
    · right; rfl
    · exact absurd hval hmem.2
  have hDcountL : D.count .L = a := by
    rw [hD_def, orderedDeletion_count_ne w .s .L (by decide)]; exact hcountL
  have hDcountm : D.count .m = a := by
    rw [hD_def, orderedDeletion_count_ne w .s .m (by decide)]; exact hcountm
  obtain ⟨halt, hne_D⟩ := balanced_circular_mos_is_alternating D a _ha_pos hDlen
    hbin hDcountL hDcountm hdel
  -- Position reduction to [0, n)
  set wList := (List.range n).map (fun k => w (↑k : ZMod n)) with hwList_def
  set i₀ := i % n with hi₀_def
  have hi₀_lt : i₀ < n := Nat.mod_lt i hn_pos
  have hwi₀ : w (↑i₀ : ZMod n) = w (↑i : ZMod n) := by
    congr 1; simp [hi₀_def, ZMod.natCast_mod]
  have hwi₀_ne_s : w (↑i₀ : ZMod n) ≠ .s := by rw [hwi₀]; exact hw_ne_s
  -- Deletion index q at position i₀
  set q := ((wList.take i₀).filter (· ≠ .s)).length with hq_def
  have hq_lt : q < D.length := prefix_filter_lt_D_length w i₀ hi₀_lt hwi₀_ne_s
  have hDq : D[q]'hq_lt = w (↑i : ZMod n) := by
    rw [← hwi₀]; exact orderedDeletion_getElem w i₀ hi₀_lt hwi₀_ne_s hq_lt
  -- Position (i + p) % n
  set i₁ := (i + p) % n with hi₁_def
  have hi₁_lt : i₁ < n := Nat.mod_lt _ hn_pos
  have hwi₁ : w (↑i₁ : ZMod n) = w (↑(i + p) : ZMod n) := by
    congr 1; simp [hi₁_def, ZMod.natCast_mod]
  have hwi₁_ne_s : w (↑i₁ : ZMod n) ≠ .s := by
    rw [hwi₁]; intro h; rw [← hs_iff] at h; exact hw_ne_s h
  -- Deletion index q₁ at position i₁
  set q₁ := ((wList.take i₁).filter (· ≠ .s)).length with hq₁_def
  have hq₁_lt : q₁ < D.length := prefix_filter_lt_D_length w i₁ hi₁_lt hwi₁_ne_s
  have hDq₁ : D[q₁]'hq₁_lt = w (↑(i + p) : ZMod n) := by
    rw [← hwi₁]; exact orderedDeletion_getElem w i₁ hi₁_lt hwi₁_ne_s hq₁_lt
  -- Slice filter length: non-s count in [i₀, i₀ + p) = a
  have hksv_s : Necklace.kStepVector w i₀ p .s = ↑c := by
    -- Bridge: kStepVector w .s = kStepVector B .s
    have hbridge := (identifiedToBinary_kStepVector_s w i₀ p).symm
    -- kStepVector(B, ·, p, .s) is constant = period_vec(.s) by kStepVector_full_period
    have hfull : ∀ j, Necklace.kStepVector B j p BinaryStep.s =
        (ZVector.ofList (Necklace.period B)) BinaryStep.s := by
      intro j
      have := kStepVector_full_period B j BinaryStep.s
      rwa [hB_period] at this
    -- Compute period_vec(.s) = c via kStepVector_add + total count
    have h1 := kStepVector_add B 0 p p BinaryStep.s
    simp only [Nat.zero_add, hfull 0, hfull p] at h1
    have htotal := kStepVector_zero_n_eq_count B BinaryStep.s
    rw [hB_counts_val] at htotal
    have hnn : Necklace.kStepVector B 0 n BinaryStep.s =
        Necklace.kStepVector B 0 (p + p) BinaryStep.s :=
      congr_arg (fun k => Necklace.kStepVector B 0 k BinaryStep.s) (show n = p + p by omega)
    have hpv_s : (ZVector.ofList (Necklace.period B)) BinaryStep.s = ↑c := by
      have : (↑(2 * c) : ℤ) = 2 * ↑c := by push_cast; ring
      linarith [h1, htotal, hnn, this]
    rw [hbridge, hfull i₀, hpv_s]
  have hfilt_a : ((Necklace.slice w i₀ (i₀ + p)).filter (· ≠ .s)).length = a := by
    have hksv_s' : Necklace.kStepVector w i₀ p .s = ↑(p - a) := by
      rw [hksv_s]; norm_cast; omega
    exact nonS_filter_length w i₀ p a hksv_s' (by omega)
  -- nonSBefore_advance: q₁ % D.length = (q + a) % D.length
  have hp_lt_n : p < n := by linarith
  have hi₁_eq : i₁ = (i₀ + p) % n := by
    rw [hi₁_def, hi₀_def, Nat.add_mod, Nat.mod_eq_of_lt hp_lt_n]
  have hi₀_mod_self : i₀ % n = i₀ := Nat.mod_eq_of_lt hi₀_lt
  have hadv : q₁ % D.length = (q + a) % D.length := by
    have h := nonSBefore_advance w i₀ p a (by omega) hfilt_a.symm
    simp only [hi₀_mod_self] at h
    rw [hq₁_def, hi₁_eq]
    convert h using 2
  -- Parity argument: q₁ % 2 ≠ q % 2 (since a is odd)
  have hq₁_parity : q₁ % 2 ≠ q % 2 := by
    have hq₁_lt' : q₁ < 2 * a := by linarith
    have hmod : q₁ % (2 * a) = (q + a) % (2 * a) := by rwa [hDlen] at hadv
    have hq₁_eq : q₁ = (q + a) % (2 * a) := by
      rw [← Nat.mod_eq_of_lt hq₁_lt']; exact hmod
    have h1 : q₁ % 2 = (q + a) % 2 := by
      rw [hq₁_eq, Nat.mod_mod_of_dvd _ (dvd_mul_right 2 a)]
    rw [h1]; omega
  -- D[q₁] ≠ D[q] from alternation + parity
  have hDne : D[q₁]'hq₁_lt ≠ D[q]'hq_lt := by
    rw [halt q₁ hq₁_lt, halt q hq_lt]
    intro heq
    exact hq₁_parity (by
      rcases Nat.mod_two_eq_zero_or_one q₁ with h1 | h1 <;>
      rcases Nat.mod_two_eq_zero_or_one q with h2 | h2 <;>
      simp_all)
  -- Conclude: w(i+p) ≠ w(i)
  rw [hDq, hDq₁] at hDne
  exact hDne

/-- 2-step twist: the 2-step ZVector at position `i + n/2` has its L and m
    components swapped compared to position `i`. -/
private lemma kStepVector_two_twist (w : TernaryNecklace n)
    (a c : ℕ) (ha_pos : a > 0) (hc_pos : c > 0) (ha_odd : a % 2 = 1)
    (hcop : Nat.Coprime a c) (hn : n = 2 * a + 2 * c)
    (hcountL : Necklace.count w .L = a) (hcountm : Necklace.count w .m = a)
    (hcounts : Necklace.count w .s = 2 * c)
    (hmos : isPartialPairwiseMOS w .L .m)
    (hdel : isPartialDeletionMOS w .s)
    (i : ℕ) (x : StepSize) :
    Necklace.kStepVector w (i + n / 2) 2 x =
    Necklace.kStepVector w i 2 (match x with | .L => .m | .m => .L | .s => .s) := by
  set p := n / 2 with hp_def
  -- Local helper: kStepVector at window size 1 = single position check
  have hone : ∀ (j : ℕ) (a : StepSize),
      Necklace.kStepVector w j 1 a = if w ((j : ℕ) : ZMod n) = a then 1 else 0 := by
    intro j a
    simp only [Necklace.kStepVector, ZVector.ofList, Necklace.slice,
      show j + 1 - j = 1 from by omega, List.range_one]
    split_ifs with h <;> simp [h]
  have hswap_i := half_period_swap w a c ha_pos hc_pos ha_odd hcop hn
    hcountL hcountm hcounts hmos hdel i
  have hswap_i1 := half_period_swap w a c ha_pos hc_pos ha_odd hcop hn
    hcountL hcountm hcounts hmos hdel (i + 1)
  -- Rewrite (i+1+p) to (i+p+1) in ZMod
  have hpos : ((i + 1 + p : ℕ) : ZMod n) = ((i + p + 1 : ℕ) : ZMod n) := by
    push_cast; ring
  rw [hpos] at hswap_i1
  -- Decompose kStepVector via kStepVector_add (2 = 1 + 1)
  rw [show (2 : ℕ) = 1 + 1 from rfl,
      kStepVector_add w (i + p) 1 1 x,
      kStepVector_add w i 1 1 (match x with | .L => .m | .m => .L | .s => .s)]
  -- Use hone to reduce each to if/then/else
  simp only [hone (i + p) x, hone ((i + p) + 1) x,
    hone i (match x with | .L => .m | .m => .L | .s => .s),
    hone (i + 1) (match x with | .L => .m | .m => .L | .s => .s)]
  -- Substitute half_period_swap values
  rw [hswap_i, hswap_i1]
  -- Close by case analysis on w(i), w(i+1), x
  rcases w ((i : ℕ) : ZMod n) with _ | _ | _ <;>
  rcases w (((i + 1) : ℕ) : ZMod n) with _ | _ | _ <;>
  cases x <;> simp

/-- In an even-regular data scale, the 2-step ZVector at every position is
    one of at most 3 types: `(1,1,0)`, `(1,0,1)`, or `(0,1,1)` plus
    possibly `(2,0,0)`, `(0,2,0)`, `(0,0,2)`. More importantly, the
    s-component equals the binary s-component (which has period `n/2`). -/
private lemma kStepVector_two_s_periodic (w : TernaryNecklace n)
    (a c : ℕ) (ha_pos : a > 0) (hc_pos : c > 0)
    (hcop : Nat.Coprime a c) (hn : n = 2 * a + 2 * c)
    (hcountL : Necklace.count w .L = a) (hcountm : Necklace.count w .m = a)
    (hcounts : Necklace.count w .s = 2 * c)
    (hmos : isPartialPairwiseMOS w .L .m)
    (i : ℕ) :
    Necklace.kStepVector w (i + n / 2) 2 .s = Necklace.kStepVector w i 2 .s := by
  -- The s-count equals the binary Z-count, which has period n/2
  set B := identifiedToBinary (TernaryNecklace.identifyPair w .L .m) with hB_def
  have hs_bridge : ∀ j, Necklace.kStepVector w j 2 .s =
      Necklace.kStepVector B j 2 .s := by
    intro j; exact (identifiedToBinary_kStepVector_s w j 2).symm
  rw [hs_bridge, hs_bridge]
  -- B has period n/2, so kStepVector(B, i+p, 2) = kStepVector(B, i, 2)
  have hB_mos : BinaryNecklace.isMOS B :=
    identifiedToBinary_isMOS w hcountL hcountm hcounts ha_pos (by omega) hmos
  have hpLen : (Necklace.period B).length = n / 2 := by
    have := binary_mos_period_half a c ha_pos hc_pos hcop hn B hB_mos
      (identifiedToBinary_count_L w hcountL hcountm)
      (identifiedToBinary_count_s w hcounts)
    omega
  rw [← hpLen]
  exact congr_fun (kStepVector_add_period B i 2) .s

/-- Transfer interleaving from `applyPerm σ w` to `w`. -/
private lemma isInterleaving_of_applyPerm (σ : Equiv.Perm StepSize)
    (w : TernaryNecklace n) (k : ℕ)
    (h : Necklace.isInterleaving (Necklace.applyPerm σ w) k) :
    Necklace.isInterleaving w k := by
  obtain ⟨hk, hkn, hs⟩ := h
  refine ⟨hk, hkn, fun s => ?_⟩
  obtain ⟨d, hd⟩ := hs s
  exact ⟨d, fun j => by
    have := hd j
    rw [kStepVector_applyPerm, kStepVector_applyPerm] at this
    funext x; have := congr_fun this (σ x); simp [ZVector.applyPerm] at this; exact this⟩

/-- Even-regular scales of length 4 (i.e., `xyxz`) are 2-interleavings:
    all strands of 2-step multisets are rotations of each other, and
    each strand (after mapping) is a 2-note MOS.

    **Proof**: Since `a = 1` and `c = 1`, the template MOS is `2X 2Z` and
    the scale is determined up to S₃-equivalence and rotation. -/
theorem evenRegular_four_isInterleaving [NeZero (n / 2)] (w : TernaryNecklace n)
    (h : isEvenRegular w) (hn : n = 4) :
    Necklace.isInterleaving w 2 ∧
    ∃ (φ : ZVector StepSize → StepSize),
      Necklace.hasMOSProperty (φ ∘ Necklace.strand2 w ⟨0, by omega⟩) := by
  obtain ⟨_hprim, _heven, σ, a, c, ha_pos, hc_pos, ha_odd, hcop, hn_eq,
    hcountL, hcountm, hcounts, hmos, hdel⟩ := h
  have ha1 : a = 1 := by omega
  have hc1 : c = 1 := by omega
  subst ha1; subst hc1
  set w' := Necklace.applyPerm σ w with hw'_def
  set p := n / 2 with hp_def
  have hp_val : p = 2 := by omega
  -- All 2-step s-components of w' equal 1 (since binary MOS has period p=2, so
  -- the 2-step = full-period step, giving constant s-count = period_vec.s = c = 1)
  have hs_val : ∀ i, Necklace.kStepVector w' i 2 .s = 1 := by
    intro i
    set B := identifiedToBinary (TernaryNecklace.identifyPair w' .L .m) with hB_def
    have hB_mos : BinaryNecklace.isMOS B :=
      identifiedToBinary_isMOS w' hcountL hcountm hcounts (by omega) (by omega) hmos
    have hpLen : (Necklace.period B).length = 2 := by
      have := binary_mos_period_half 1 1 (by omega) (by omega) hcop hn_eq B hB_mos
        (identifiedToBinary_count_L w' hcountL hcountm)
        (identifiedToBinary_count_s w' hcounts)
      omega
    have hpv_s : (ZVector.ofList (Necklace.period B)) .s = 1 := by
      have := (period_vector_of_half_period 1 1 (by omega) (by omega) hcop hn_eq B hB_mos
        (identifiedToBinary_count_L w' hcountL hcountm)
        (identifiedToBinary_count_s w' hcounts) hpLen).2
      exact_mod_cast this
    have h2 : Necklace.kStepVector B i 2 .s = (ZVector.ofList (Necklace.period B)) .s := by
      rw [← hpLen]; exact kStepVector_full_period B i .s
    rw [← identifiedToBinary_kStepVector_s w' i 2, h2, hpv_s]
  -- All 2-step vectors of w' have L + m = 1
  have hLm_one : ∀ i, Necklace.kStepVector w' i 2 .L + Necklace.kStepVector w' i 2 .m = 1 := by
    intro i
    have ht := kStepVector_total_count_ternary w' i 2
    have hs := hs_val i
    push_cast at ht; linarith
  -- Each L component is 0 or 1
  have hL_01 : ∀ i, Necklace.kStepVector w' i 2 .L = 0 ∨
      Necklace.kStepVector w' i 2 .L = 1 := by
    intro i
    have hnn : Necklace.kStepVector w' i 2 .L ≥ 0 := by
      unfold Necklace.kStepVector ZVector.ofList; exact_mod_cast Nat.zero_le _
    have hm_nn : Necklace.kStepVector w' i 2 .m ≥ 0 := by
      unfold Necklace.kStepVector ZVector.ofList; exact_mod_cast Nat.zero_le _
    have hle : Necklace.kStepVector w' i 2 .L ≤ 1 := by linarith [hLm_one i]
    omega
  -- Twist: V(i + p) swaps L ↔ m
  have htwist : ∀ i x, Necklace.kStepVector w' (i + p) 2 x =
      Necklace.kStepVector w' i 2 (match x with | .L => .m | .m => .L | .s => .s) := by
    intro i x; rw [hp_def]
    exact kStepVector_two_twist w' 1 1 (by omega) (by omega) (by omega) hcop hn_eq
      hcountL hcountm hcounts hmos hdel i x
  -- Key: if V(i).L = V(j).L then V(i) = V(j) (since s is const and total is fixed)
  have hL_determines : ∀ i j,
      Necklace.kStepVector w' i 2 .L = Necklace.kStepVector w' j 2 .L →
      Necklace.kStepVector w' i 2 = Necklace.kStepVector w' j 2 := by
    intro i j hL; funext x; cases x with
    | L => exact hL
    | m => linarith [hLm_one i, hLm_one j]
    | s => rw [hs_val, hs_val]
  -- If V(i).L ≠ V(j).L then V(i) = twist(V(j))
  have hL_determines_twist : ∀ i j,
      Necklace.kStepVector w' i 2 .L ≠ Necklace.kStepVector w' j 2 .L →
      Necklace.kStepVector w' i 2 = Necklace.kStepVector w' (j + p) 2 := by
    intro i j hne
    apply hL_determines
    rw [htwist j .L]; simp only
    rcases hL_01 i with h0 | h1 <;> rcases hL_01 j with h0' | h1'
    · exact absurd (h0.trans h0'.symm) hne
    · rw [h0]; linarith [hLm_one j, h1']
    · rw [h1]; linarith [hLm_one j, h0']
    · exact absurd (h1.trans h1'.symm) hne
  -- Helper to decompose j : Fin (n/2) into {0, 1} when p = 2
  have hFin2 : ∀ j : Fin (n / 2), j = ⟨0, by omega⟩ ∨ j = ⟨1, by omega⟩ := by
    intro ⟨jv, hjv⟩; rcases jv with _ | _ | _ <;> [left; right; omega] <;> rfl
  -- ===== Part 1: isInterleaving w 2 =====
  have hn2 : n / 2 = 2 := by omega
  constructor
  · -- Transfer from w' to w
    apply isInterleaving_of_applyPerm σ w 2
    refine ⟨by omega, ⟨2, by omega⟩, fun s => ?_⟩
    fin_cases s
    · -- s = 0: d = 0 trivially
      exact ⟨0, fun j => by simp [Nat.mod_eq_of_lt j.isLt]⟩
    · -- s = 1: case split on V(1).L = V(0).L
      by_cases hcase : Necklace.kStepVector w' 1 2 .L = Necklace.kStepVector w' 0 2 .L
      · -- V(1) = V(0): d = 0
        refine ⟨0, fun j => ?_⟩
        rcases hFin2 j with rfl | rfl
        · -- j = 0: V(1) = V(0)
          simp only [hn2]
          show Necklace.kStepVector w' 1 2 = Necklace.kStepVector w' 0 2
          exact hL_determines 1 0 hcase
        · -- j = 1: V(3) = V(2) (from twist of V(1) = V(0))
          simp only [hn2]
          show Necklace.kStepVector w' 3 2 = Necklace.kStepVector w' 2 2
          have h10 := hL_determines 1 0 hcase
          have : Necklace.kStepVector w' (1 + p) 2 = Necklace.kStepVector w' (0 + p) 2 := by
            funext x; rw [htwist 1 x, htwist 0 x]; exact congr_fun h10 _
          convert this using 2 <;> omega
      · -- V(1) ≠ V(0): d = 1
        refine ⟨1, fun j => ?_⟩
        rcases hFin2 j with rfl | rfl
        · -- j = 0: V(1) = V(((0+1)%2)*2) = V(2)
          simp only [hn2]
          show Necklace.kStepVector w' 1 2 = Necklace.kStepVector w' 2 2
          convert hL_determines_twist 1 0 hcase using 2; omega
        · -- j = 1: V(3) = V(((1+1)%2)*2) = V(0)
          simp only [hn2]
          show Necklace.kStepVector w' 3 2 = Necklace.kStepVector w' 0 2
          have h3eq : Necklace.kStepVector w' 3 2 = Necklace.kStepVector w' (1 + p) 2 := by
            congr 1; omega
          rw [h3eq]; apply hL_determines
          rw [htwist 1 .L]; simp only
          rcases hL_01 1 with h0 | h1 <;> rcases hL_01 0 with h0' | h1'
          · exact absurd (h0.trans h0'.symm) hcase
          · linarith [hLm_one 1]
          · linarith [hLm_one 1]
          · exact absurd (h1.trans h1'.symm) hcase
  · -- ===== Part 2: hasMOSProperty =====
    -- V(0) ≠ V(2) (from twist + s=1, L+m=1 means V can't be self-twist)
    have hV02_ne : Necklace.kStepVector w 0 2 ≠ Necklace.kStepVector w 2 2 := by
      intro heq
      have heq' : Necklace.kStepVector w' 0 2 = Necklace.kStepVector w' 2 2 := by
        rw [hw'_def, kStepVector_applyPerm, kStepVector_applyPerm, heq]
      have h2eq : Necklace.kStepVector w' 2 2 = Necklace.kStepVector w' (0 + p) 2 := by
        congr 1; omega
      rw [h2eq] at heq'
      have := congr_fun heq' .L
      rw [htwist 0 .L] at this; simp only at this
      -- this : V(0).L = V(0).m, hLm_one 0 : L + m = 1 → 2L = 1, impossible in ℤ
      rcases hL_01 0 with h0 | h1 <;> linarith [hLm_one 0]
    refine ⟨fun v => if v = Necklace.kStepVector w 0 2 then .L else .m, ?_⟩
    constructor
    · -- ≥ 2 distinct values
      refine ⟨.L, .m, by decide, ⟨(0 : ZMod (n / 2)), by simp [Necklace.strand2]⟩,
        ⟨(1 : ZMod (n / 2)), ?_⟩⟩
      simp only [Function.comp, Necklace.strand2]
      show (if Necklace.kStepVector w ((1 : ZMod (n / 2)).val * 2 + 0) 2 =
        Necklace.kStepVector w 0 2 then StepSize.L else StepSize.m) = StepSize.m
      have h1val : (1 : ZMod (n / 2)).val = 1 := by
        rw [show n / 2 = 2 from hp_val]; decide
      simp only [h1val, one_mul, Nat.add_zero]
      rw [if_neg (Ne.symm hV02_ne)]
    · -- ≤ 2 k-step multisets for valid k
      intro k hk hk_lt
      have hk_lt' : k < 2 := by omega
      interval_cases k
      -- card of toFinset ≤ length of list ≤ n/2 = 2
      calc (Necklace.allKStepMultisets _ 1).toFinset.card
          ≤ (Necklace.allKStepMultisets _ 1).length := List.toFinset_card_le _
        _ = n / 2 := by
            simp [Necklace.allKStepMultisets, Necklace.allKStepSubwords, List.length_ofFn]
        _ = 2 := hn2

/-- Transfer contrainterleaving from `applyPerm σ w` to `w`. -/
private lemma isContrainterleaving_of_applyPerm (σ : Equiv.Perm StepSize)
    (w : TernaryNecklace n)
    (h : Necklace.isContrainterleaving (Necklace.applyPerm σ w)) :
    Necklace.isContrainterleaving w := by
  obtain ⟨hdvd, d, hd⟩ := h
  refine ⟨hdvd, d, fun j => ?_⟩
  have := hd j
  rw [kStepVector_applyPerm, kStepVector_applyPerm] at this
  funext x; have := congr_fun this (σ x); simp [ZVector.applyPerm] at this; exact this

/-! ### Infrastructure for interleaving proofs

The following lemmas capture fundamental properties of binary MOS
(Christoffel) words needed for the interleaving and contrainterleaving theorems. -/

/-- If consecutive k-step vectors of a binary necklace are equal, then the letter
    at position `i` equals the letter at position `i + k`. -/
private lemma binary_kstep_eq_implies_letter_eq (B : BinaryNecklace n)
    (i k : ℕ)
    (heq : Necklace.kStepVector B i k = Necklace.kStepVector B (i + 1) k) :
    B ((i : ℕ) : ZMod n) = B (((i + k) : ℕ) : ZMod n) := by
  have heq_L : Necklace.kStepVector B i k BinaryStep.L =
      Necklace.kStepVector B (i + 1) k BinaryStep.L := congr_fun heq BinaryStep.L
  have hshift := slice_L_count_shift B i k
  simp only at hshift
  -- Normalize cast: ↑(i+k) = ↑i + ↑k in ZMod n
  have hcast : (↑(i + k) : ZMod n) = (↑i + ↑k : ZMod n) := by push_cast; ring
  cases hw_i : B ((i : ℕ) : ZMod n) <;> cases hw_k : B (((i + k) : ℕ) : ZMod n)
  · rfl
  · exfalso
    rw [hcast] at hw_k
    simp [hw_i, hw_k] at hshift
    unfold Necklace.kStepVector ZVector.ofList at heq_L; linarith
  · exfalso
    rw [hcast] at hw_k
    simp [hw_i, hw_k] at hshift
    unfold Necklace.kStepVector ZVector.ofList at heq_L; linarith
  · rfl

/-- If two positions have the same pair of letters in their 2-step window,
    then their 2-step vectors are equal. -/
private lemma kStepVector_one_eq (w : BinaryNecklace n) (m : ℕ) (a : BinaryStep) :
    Necklace.kStepVector w m 1 a = if w ((m : ℕ) : ZMod n) = a then 1 else 0 := by
  simp only [Necklace.kStepVector, ZVector.ofList, Necklace.slice,
    show m + 1 - m = 1 from by omega, List.range_one]
  split_ifs with h <;> simp [h]

/-- Variant: if the letters are SWAPPED (i↔j+1 and i+1↔j), the 2-step
    multiset counts are still equal (since kStepVector counts, not orders). -/
private lemma kStepVector_two_eq_of_letter_swap (w : BinaryNecklace n) (i j : ℕ)
    (h0 : w ((i : ℕ) : ZMod n) = w (((j + 1) : ℕ) : ZMod n))
    (h1 : w (((i + 1) : ℕ) : ZMod n) = w ((j : ℕ) : ZMod n)) :
    Necklace.kStepVector w i 2 = Necklace.kStepVector w j 2 := by
  funext a
  rw [show (2 : ℕ) = 1 + 1 from rfl,
      kStepVector_add w i 1 1 a, kStepVector_add w j 1 1 a,
      kStepVector_one_eq w i a, kStepVector_one_eq w (i + 1) a,
      kStepVector_one_eq w j a, kStepVector_one_eq w (j + 1) a, h0, h1]
  omega

private lemma kStepVector_two_eq_of_letter_eq (w : BinaryNecklace n) (i j : ℕ)
    (h0 : w ((i : ℕ) : ZMod n) = w ((j : ℕ) : ZMod n))
    (h1 : w (((i + 1) : ℕ) : ZMod n) = w (((j + 1) : ℕ) : ZMod n)) :
    Necklace.kStepVector w i 2 = Necklace.kStepVector w j 2 := by
  funext a
  rw [show (2 : ℕ) = 1 + 1 from rfl,
      kStepVector_add w i 1 1 a, kStepVector_add w j 1 1 a]
  rw [kStepVector_one_eq w i a, kStepVector_one_eq w j a,
      kStepVector_one_eq w (i + 1) a, kStepVector_one_eq w (j + 1) a, h0, h1]

/-- **Binary 2-step rotation (even period)**: For a binary MOS `B` with even
    period `p`, the binary 2-step count vectors at odd positions are a cyclic
    rotation of those at even positions.

    The proof extracts the MOS generator step `k₀` (which is odd since
    `gcd(k₀, p) = 1` and `p` is even), finds the unique "bad" position,
    shows the k₀-shift preserves 2-step vectors on one parity strand,
    then derives the rotation. -/
private lemma binary_2step_even_odd_rotation (B : BinaryNecklace n)
    (hmos : BinaryNecklace.isMOS B)
    (p : ℕ) (hpLen : (Necklace.period B).length = p)
    (hp_even : p % 2 = 0) (hp_pos : p > 0) :
    ∃ d : ℕ, ∀ j : Fin p,
      Necklace.kStepVector B (j.val * 2 + 1) 2 =
      Necklace.kStepVector B (((j.val + d) % p) * 2) 2 := by
  -- ===== Part A: Generator setup =====
  have hbin : BinaryNecklace.isBinary B := hmos.1
  have hp_ge2 : p ≥ 2 := by rw [← hpLen]; exact period_length_ge_two_of_binary B hbin
  obtain ⟨g, hgen⟩ := allMOSScalesHaveGenerator n B hmos
  obtain ⟨k₀, hk₀_pos, hk₀_lt, hk₀_count⟩ :=
    generator_implies_p_minus_one_occurrences B hbin g hgen
  rw [hpLen] at hk₀_lt hk₀_count
  have hk₀_cop : Nat.Coprime k₀ p := by
    have := p_minus_one_occurrences_implies_coprime_to_period B hbin k₀ hk₀_pos
      (by rw [hpLen]; exact hk₀_lt) g (by rw [hpLen]; exact hk₀_count)
    rwa [hpLen] at this
  -- k₀ is odd (coprime to even p)
  have hk₀_odd : k₀ % 2 = 1 := by
    by_contra h
    have hk₀_even : 2 ∣ k₀ := by omega
    have hp_even' : 2 ∣ p := by omega
    have : 2 ∣ Nat.gcd k₀ p := Nat.dvd_gcd hk₀_even hp_even'
    rw [hk₀_cop] at this; omega
  -- ===== Part B: Unique bad position =====
  -- Unfold countKStepVectorPerPeriod to work with List.countP directly
  dsimp only [countKStepVectorPerPeriod] at hk₀_count
  rw [hpLen] at hk₀_count
  have hbad : ∃ b : ℕ, b < p ∧ Necklace.kStepVector B b k₀ ≠ g ∧
      (∀ i : ℕ, i < p → i ≠ b → Necklace.kStepVector B i k₀ = g) := by
    set pred := fun j => decide (Necklace.kStepVector B j k₀ = g)
    have hexists : ∃ b, b < p ∧ Necklace.kStepVector B b k₀ ≠ g := by
      by_contra hall; push_neg at hall
      have h := List.countP_eq_length.mpr (fun i hi =>
        decide_eq_true_eq.mpr (hall i (List.mem_range.mp hi)))
      rw [List.length_range] at h
      -- h : countP (fun i => decide ...) = p, hk₀_count : countP pred = p - 1
      -- These use the same predicate (pred = fun j => decide ...)
      change (List.range p).countP pred = p at h
      omega
    obtain ⟨b, hb_lt, hb_ne⟩ := hexists
    refine ⟨b, hb_lt, hb_ne, fun i hi hne => ?_⟩
    by_contra hi_ne
    have hp_i : pred i = false := by simp [pred, hi_ne]
    have hp_b : pred b = false := by simp [pred, hb_ne]
    have hi_mem : i ∈ List.range p := List.mem_range.mpr hi
    have hb_mem : b ∈ List.range p := List.mem_range.mpr hb_lt
    have h1 : ((List.range p).erase i).countP pred = (List.range p).countP pred := by
      rw [List.countP_erase]; simp [hi_mem, hp_i]
    have hb_mem' : b ∈ (List.range p).erase i :=
      List.mem_erase_of_ne (Ne.symm hne) |>.mpr hb_mem
    have h2 : (((List.range p).erase i).erase b).countP pred =
        ((List.range p).erase i).countP pred := by
      rw [List.countP_erase]; simp [hb_mem', hp_b]
    have h3 : (((List.range p).erase i).erase b).length = p - 2 := by
      rw [List.length_erase_of_mem hb_mem',
        List.length_erase_of_mem hi_mem, List.length_range]; omega
    have : (List.range p).countP pred ≤ p - 2 :=
      calc (List.range p).countP pred
          = ((List.range p).erase i).countP pred := h1.symm
        _ = (((List.range p).erase i).erase b).countP pred := h2.symm
        _ ≤ (((List.range p).erase i).erase b).length := List.countP_le_length
        _ = p - 2 := h3
    omega
  obtain ⟨b, hb_lt, hb_ne, hb_good⟩ := hbad
  -- ===== Part C: Good positions fixed under k₀-shift =====
  have hgood_all : ∀ i : ℕ, i % p ≠ b → Necklace.kStepVector B i k₀ = g := by
    intro i hi
    have h := hb_good (i % p) (Nat.mod_lt i hp_pos) hi
    rw [← kStepVector_mod_period B i k₀ (by rw [hpLen]; omega), hpLen]
    exact h
  have hfixed : ∀ i : ℕ, i % p ≠ b → (i + 1) % p ≠ b →
      B ((i : ℕ) : ZMod n) = B (((i + k₀) : ℕ) : ZMod n) := by
    intro i hi1 hi2
    exact binary_kstep_eq_implies_letter_eq B i k₀
      (by rw [hgood_all i hi1, hgood_all (i + 1) hi2])
  -- ===== Part D: 2-step preserved on one strand =====
  set j₀ := (b + p - 1) % p with hj₀_def
  have hj₀_lt : j₀ < p := Nat.mod_lt _ hp_pos
  have hj₀_succ : (j₀ + 1) % p = b := by
    simp only [hj₀_def]
    rcases Nat.eq_zero_or_pos b with rfl | hb_pos
    · simp only [Nat.zero_add]
      rw [Nat.mod_eq_of_lt (by omega : p - 1 < p)]
      rw [show p - 1 + 1 = p from by omega, Nat.mod_self]
    · rw [show b + p - 1 = (b - 1) + 1 * p from by omega, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt (by omega : b - 1 < p),
        show b - 1 + 1 = b from by omega, Nat.mod_eq_of_lt hb_lt]
  have hj₀_ne_b : j₀ ≠ b := by
    intro heq; rw [heq] at hj₀_succ
    have h1 : (b + 1) % p = b := hj₀_succ
    have h2 : (b + 1) % p = if b + 1 = p then 0 else b + 1 := by
      split_ifs with h
      · rw [h, Nat.mod_self]
      · exact Nat.mod_eq_of_lt (by omega)
    rw [h2] at h1; split_ifs at h1 with h <;> omega
  -- b and j₀ have different parities
  have hparity : j₀ % 2 ≠ b % 2 := by
    rcases Nat.eq_zero_or_pos b with rfl | hb_pos
    · simp only [hj₀_def, Nat.zero_add]
      rw [Nat.mod_eq_of_lt (by omega : p - 1 < p)]; omega
    · have hj₀_eq : j₀ = b - 1 := by
        simp only [hj₀_def]
        rw [show b + p - 1 = (b - 1) + 1 * p from by omega, Nat.add_mul_mod_self_right,
          Nat.mod_eq_of_lt (by omega : b - 1 < p)]
      rw [hj₀_eq]; omega
  -- Key: i%p has the same parity as i (since p is even)
  have hmod_parity : ∀ i : ℕ, i % p % 2 = i % 2 :=
    fun i => Nat.mod_mod_of_dvd i (by omega : 2 ∣ p)
  -- 2-step preserved on the j₀-parity strand
  have hstrand : ∀ i : ℕ, i % 2 = j₀ % 2 →
      Necklace.kStepVector B i 2 = Necklace.kStepVector B (i + k₀) 2 := by
    intro i hi_par
    by_cases hi_j₀ : i % p = j₀
    · -- Case 2: i ≡ j₀ (mod p) — the swap position
      -- Use scoot equations to show L-counts are preserved
      -- V_2(i) = V_2(j₀) and V_2(i+k₀) = V_2(j₀+k₀) by periodicity
      -- So it suffices to show V_2(j₀) = V_2(j₀+k₀)
      have hV_i : Necklace.kStepVector B i 2 = Necklace.kStepVector B j₀ 2 := by
        rw [← kStepVector_mod_period B i 2 (by rw [hpLen]; omega), hpLen, hi_j₀]
      have hV_ik : Necklace.kStepVector B (i + k₀) 2 =
          Necklace.kStepVector B (j₀ + k₀) 2 := by
        rw [← kStepVector_mod_period B (i + k₀) 2 (by rw [hpLen]; omega), hpLen,
            ← kStepVector_mod_period B (j₀ + k₀) 2 (by rw [hpLen]; omega), hpLen]
        congr 1
        exact (show Nat.ModEq p i j₀ from by
          rw [Nat.ModEq, hi_j₀, Nat.mod_eq_of_lt hj₀_lt]).add_right k₀
      rw [hV_i, hV_ik]
      -- Show V_2(j₀) = V_2(j₀+k₀) via scoot equations
      -- Scoot at j₀: V_{k₀}(j₀+1).L = V_{k₀}(j₀).L - δ(j₀,L) + δ(j₀+k₀,L)
      -- Scoot at b:   V_{k₀}(b+1).L  = V_{k₀}(b).L  - δ(b,L)  + δ(b+k₀,L)
      -- Sum gives: δ(j₀+k₀,L) + δ(b+k₀,L) = δ(j₀,L) + δ(b,L)
      -- V_{k₀}(j₀) = g (j₀ is a good position)
      have hV_j₀ : Necklace.kStepVector B j₀ k₀ = g :=
        hb_good j₀ hj₀_lt hj₀_ne_b
      -- V_{k₀}(j₀+1) = V_{k₀}(b) (by periodicity, since (j₀+1)%p = b)
      have hV_b_eq : Necklace.kStepVector B (j₀ + 1) k₀ = Necklace.kStepVector B b k₀ := by
        rw [← kStepVector_mod_period B (j₀ + 1) k₀ (by rw [hpLen]; omega), hpLen, hj₀_succ]
      -- V_{k₀}(b+1) = g ((b+1)%p ≠ b since p ≥ 2)
      have hV_b1 : Necklace.kStepVector B (b + 1) k₀ = g := by
        apply hgood_all
        have h1 : (b + 1) % p = if b + 1 = p then 0 else b + 1 := by
          split_ifs with h
          · rw [h, Nat.mod_self]
          · exact Nat.mod_eq_of_lt (by omega)
        rw [h1]; split_ifs with h <;> omega
      -- Derive hsum from slice_L_count_shift via unfolding to common form
      have hscoot_j₀ := slice_L_count_shift B j₀ k₀
      have hscoot_b := slice_L_count_shift B b k₀
      dsimp only at hscoot_j₀ hscoot_b
      -- dsimp normalizes ↑(j₀+k₀) to ↑j₀+↑k₀; convert back
      have hcast_j₀k : (↑j₀ + ↑k₀ : ZMod n) = ↑(j₀ + k₀) := by push_cast; ring
      have hcast_bk : (↑b + ↑k₀ : ZMod n) = ↑(b + k₀) := by push_cast; ring
      simp only [hcast_j₀k] at hscoot_j₀
      simp only [hcast_bk] at hscoot_b
      have hV_j₀_L := congr_fun hV_j₀ BinaryStep.L
      have hV_b_eq_L := congr_fun hV_b_eq BinaryStep.L
      have hV_b1_L := congr_fun hV_b1 BinaryStep.L
      dsimp only [Necklace.kStepVector, ZVector.ofList] at hV_j₀_L hV_b_eq_L hV_b1_L
      -- Everything is in ↑(filter...).length form with ↑(m+k) casts
      -- hscoot_j₀: countL(j₀+1) = countL(j₀) - [j₀=L] + [(j₀+k₀)=L]
      -- hscoot_b:  countL(b+1) = countL(b) - [b=L] + [(b+k₀)=L]
      -- hV_j₀_L: countL(j₀) = g.L, hV_b_eq_L: countL(j₀+1) = countL(b), hV_b1_L: countL(b+1) = g.L
      have hsum : (if B (((j₀ + k₀) : ℕ) : ZMod n) = BinaryStep.L then (1 : ℤ) else 0) +
          (if B (((b + k₀) : ℕ) : ZMod n) = BinaryStep.L then 1 else 0) =
          (if B ((j₀ : ℕ) : ZMod n) = BinaryStep.L then 1 else 0) +
          (if B ((b : ℕ) : ZMod n) = BinaryStep.L then 1 else 0) := by linarith
      -- Now show V_2(j₀) = V_2(j₀+k₀) via kStepVector_add decomposition
      funext a
      rw [show (2 : ℕ) = 1 + 1 from rfl,
          kStepVector_add B j₀ 1 1 a, kStepVector_add B (j₀ + k₀) 1 1 a]
      -- Decompose 1-step vectors into if-then-else
      have hone : ∀ (m : ℕ) (a : BinaryStep),
          Necklace.kStepVector B m 1 a = if B ((m : ℕ) : ZMod n) = a then 1 else 0 := by
        intro m a'
        simp only [Necklace.kStepVector, ZVector.ofList, Necklace.slice,
          show m + 1 - m = 1 from by omega, List.range_one]
        split_ifs with h <;> simp [h]
      rw [hone j₀ a, hone (j₀ + 1) a, hone (j₀ + k₀) a]
      -- For the 4th term: position (j₀ + k₀ + 1) vs (j₀ + 1 + k₀)
      have hcast : ((j₀ + k₀ + 1 : ℕ) : ZMod n) = ((j₀ + 1 + k₀ : ℕ) : ZMod n) := by
        push_cast; ring
      rw [show j₀ + k₀ + 1 = (j₀ + k₀) + 1 from by omega, hone (j₀ + k₀ + 1) a, hcast]
      -- Helper: letter equality from position congruence mod p
      have letter_eq_of_cong : ∀ a' b' : ℕ, a' % p = b' % p →
          B ((a' : ℕ) : ZMod n) = B ((b' : ℕ) : ZMod n) := by
        intro a' b' hcong
        have heq1step : Necklace.kStepVector B a' 1 = Necklace.kStepVector B b' 1 := by
          rw [← kStepVector_mod_period B a' 1 (by rw [hpLen]; omega), hpLen,
              ← kStepVector_mod_period B b' 1 (by rw [hpLen]; omega), hpLen, hcong]
        have h3 := congr_fun heq1step BinaryStep.L
        rw [hone a' BinaryStep.L, hone b' BinaryStep.L] at h3
        cases hc1 : B ((a' : ℕ) : ZMod n) <;> cases hc2 : B ((b' : ℕ) : ZMod n)
        · rfl
        · exfalso; simp [hc1, hc2] at h3
        · exfalso; simp [hc1, hc2] at h3
        · rfl
      -- B(j₀+1) = B(b) since (j₀+1) ≡ b (mod p)
      have hBj₀1_eq_Bb' : B (((j₀ + 1) : ℕ) : ZMod n) = B ((b : ℕ) : ZMod n) :=
        letter_eq_of_cong (j₀ + 1) b (by rw [hj₀_succ, Nat.mod_eq_of_lt hb_lt])
      -- B(j₀+1+k₀) = B(b+k₀) since (j₀+1+k₀) ≡ (b+k₀) (mod p)
      have hBj₀1k_eq_Bbk : B (((j₀ + 1 + k₀) : ℕ) : ZMod n) = B (((b + k₀) : ℕ) : ZMod n) :=
        letter_eq_of_cong (j₀ + 1 + k₀) (b + k₀)
          ((show Nat.ModEq p (j₀ + 1) b from by
            rw [Nat.ModEq, hj₀_succ, Nat.mod_eq_of_lt hb_lt]).add_right k₀)
      -- Now the main computation: use hsum and the periodicity equalities
      rw [hBj₀1_eq_Bb', hBj₀1k_eq_Bbk]
      -- Goal: (if B(↑j₀) = a then 1 else 0) + (if B(↑b) = a then 1 else 0) =
      --       (if B(↑(j₀+k₀)) = a then 1 else 0) + (if B(↑(b+k₀)) = a then 1 else 0)
      cases a with
      | L => linarith
      | s =>
        have hone_L_s : ∀ m, (if B ((m : ℕ) : ZMod n) = BinaryStep.s then (1 : ℤ) else 0) =
            1 - (if B ((m : ℕ) : ZMod n) = BinaryStep.L then 1 else 0) := by
          intro m; cases B ((m : ℕ) : ZMod n) <;> simp
        rw [hone_L_s j₀, hone_L_s b, hone_L_s (j₀ + k₀), hone_L_s (b + k₀)]
        linarith
    · -- Case 1: i % p ≠ j₀ — both i and i+1 are "good"
      have hi_ne_b : i % p ≠ b := by
        intro heq
        have : i % p % 2 = b % 2 := by rw [heq]
        rw [hmod_parity] at this
        exact hparity (by omega)
      have hi1_ne_b : (i + 1) % p ≠ b := by
        intro heq
        apply hi_j₀
        have h1 : (i + 1) % p = b := heq
        have h2 : (j₀ + 1) % p = b := hj₀_succ
        -- (i+1) ≡ (j₀+1) mod p → i ≡ j₀ mod p
        have : i + 1 ≡ j₀ + 1 [MOD p] := by rw [Nat.ModEq]; rw [h1, h2]
        have hmodeq := Nat.ModEq.add_right_cancel' 1 this
        rw [Nat.ModEq] at hmodeq
        rwa [Nat.mod_eq_of_lt hj₀_lt] at hmodeq
      have hfixed_i := hfixed i hi_ne_b hi1_ne_b
      have hfixed_i1 : B (((i + 1) : ℕ) : ZMod n) = B (((i + 1 + k₀) : ℕ) : ZMod n) := by
        have hi1_ne_b' : (i + 1) % p ≠ b := hi1_ne_b
        have hi2_ne_b : (i + 2) % p ≠ b := by
          intro heq
          have : (i + 2) % p % 2 = b % 2 := by rw [heq]
          rw [hmod_parity] at this; exact hparity (by omega)
        exact hfixed (i + 1) hi1_ne_b hi2_ne_b
      exact kStepVector_two_eq_of_letter_eq B i (i + k₀) hfixed_i (by
        convert hfixed_i1 using 2; push_cast; ring)
  -- ===== Part E: Rotation offset =====
  -- Helper: kStepVector B has period p
  have hperiodic : ∀ a b : ℕ, a % p = b % p →
      Necklace.kStepVector B a 2 = Necklace.kStepVector B b 2 := by
    intro a b hab
    rw [← kStepVector_mod_period B a 2 (by rw [hpLen]; omega), hpLen,
        ← kStepVector_mod_period B b 2 (by rw [hpLen]; omega), hpLen, hab]
  by_cases hj₀_par : j₀ % 2 = 1
  · -- j₀ odd: odd strand preserved, d = (k₀+1)/2
    -- V(j*2+1) = V(j*2+1+k₀) = V((j+(k₀+1)/2)*2) since k₀+1 = 2*((k₀+1)/2)
    refine ⟨(k₀ + 1) / 2, fun j => ?_⟩
    rw [hstrand (j.val * 2 + 1) (by omega),
        show j.val * 2 + 1 + k₀ = (j.val + (k₀ + 1) / 2) * 2 from by omega]
    apply hperiodic
    -- ((j+d)*2) % p = (((j+d)%p)*2) % p
    conv_lhs => rw [Nat.mul_mod]
    conv_rhs => rw [Nat.mul_mod, Nat.mod_mod]
  · -- j₀ even: even strand preserved, d = p - (k₀-1)/2
    -- V(m*2) = V(m*2+k₀) = V((m+d')*2+1) where d' = (k₀-1)/2
    -- So V(j*2+1) = V(((j+p-d')%p)*2) by choosing m = (j+p-d')%p
    set d' := (k₀ - 1) / 2 with hd'_def
    have hd'_rel : k₀ = 2 * d' + 1 := by omega
    have hd'_le_p : d' ≤ p := by omega
    refine ⟨p - d', fun j => ?_⟩
    set m₀ := (j.val + (p - d')) % p with hm₀_def
    -- Even strand: V(m₀*2) = V((m₀+d')*2+1)
    have h1 : Necklace.kStepVector B (m₀ * 2) 2 =
        Necklace.kStepVector B ((m₀ + d') * 2 + 1) 2 := by
      have h := hstrand (m₀ * 2) (by omega)
      rw [show m₀ * 2 + k₀ = (m₀ + d') * 2 + 1 from by omega] at h; exact h
    -- (m₀ + d') ≡ j (mod p), so V(j*2+1) = V((m₀+d')*2+1) by periodicity
    have hmod_eq : (m₀ + d') % p = j.val := by
      rw [hm₀_def, Nat.add_mod ((j.val + (p - d')) % p) d' p, Nat.mod_mod,
          ← Nat.add_mod (j.val + (p - d')) d' p,
          show j.val + (p - d') + d' = j.val + p from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
    have h2 : Necklace.kStepVector B (j.val * 2 + 1) 2 =
        Necklace.kStepVector B ((m₀ + d') * 2 + 1) 2 := by
      apply hperiodic
      -- ((m₀+d')*2+1) % p = (j*2+1) % p from (m₀+d') ≡ j (mod p)
      conv_lhs => rw [Nat.add_mod (j.val * 2) 1 p, Nat.mul_mod, Nat.mod_eq_of_lt j.isLt]
      conv_rhs => rw [Nat.add_mod ((m₀ + d') * 2) 1 p, Nat.mul_mod, hmod_eq]
    rw [h2, ← h1]

/-- Helper: kStepVector of a ternary necklace is n-periodic in the position. -/
private lemma kStepVector_n_periodic (w : TernaryNecklace n) (m k : ℕ) :
    Necklace.kStepVector w (m + n) k = Necklace.kStepVector w m k := by
  set pLen := (Necklace.period w).length with hpLen_def
  have hpLen_pos : 0 < pLen := by
    rw [hpLen_def]; exact period_length_pos w
  have hpLen_dvd : pLen ∣ n := period_dvd_length w
  rw [← kStepVector_mod_period' w (m + n) k,
      ← kStepVector_mod_period' w m k]
  congr 1
  have : (m + n) % pLen = m % pLen := by
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hpLen_dvd, Nat.add_zero, Nat.mod_mod]
  exact this

/-- If the s-components of k-step vectors match, the non-s filter lengths match. -/
private lemma filter_neq_s_length_eq_of_kStepVector_s_eq
    (w : TernaryNecklace n) (r₁ r₂ k : ℕ)
    (h : Necklace.kStepVector w r₁ k .s = Necklace.kStepVector w r₂ k .s) :
    ((Necklace.slice w r₁ (r₁ + k)).filter (· ≠ .s)).length =
    ((Necklace.slice w r₂ (r₂ + k)).filter (· ≠ .s)).length := by
  have hv : ∀ r, (Necklace.kStepVector w r k .s : ℤ) =
      ↑((Necklace.slice w r (r + k)).filter (· == .s)).length := by
    intro r; unfold Necklace.kStepVector ZVector.ofList; simp
  have hs : ((Necklace.slice w r₁ (r₁ + k)).filter (· == .s)).length =
      ((Necklace.slice w r₂ (r₂ + k)).filter (· == .s)).length := by
    have := h; rw [hv, hv] at this; exact_mod_cast this
  have hcomp : ∀ r, ((Necklace.slice w r (r + k)).filter (· ≠ .s)).length +
      ((Necklace.slice w r (r + k)).filter (· == .s)).length =
      (Necklace.slice w r (r + k)).length := by
    intro r
    have hc := List.length_eq_length_filter_add (fun x => !decide (x = StepSize.s))
      (l := Necklace.slice w r (r + k))
    simp only [Bool.not_not] at hc
    have h1 : (Necklace.slice w r (r + k)).filter (fun x => !decide (x = StepSize.s)) =
        (Necklace.slice w r (r + k)).filter (· ≠ .s) := by congr 1; ext x; simp [ne_eq]
    have h2 : (Necklace.slice w r (r + k)).filter (fun x => decide (x = StepSize.s)) =
        (Necklace.slice w r (r + k)).filter (· == .s) := by congr 1
    rw [h1, h2] at hc; omega
  have hlen : ∀ r, (Necklace.slice w r (r + k)).length = k := by
    intro r; rw [Necklace.slice_length]; omega
  have := hcomp r₁; have := hcomp r₂; have := hlen r₁; have := hlen r₂; omega

private lemma add_mod_two_ne {q₁ q₂ : ℕ} (hq : q₁ % 2 ≠ q₂ % 2) (t : ℕ) :
    (q₁ + t) % 2 ≠ (q₂ + t) % 2 := by
  intro h; apply hq
  have h1 := Nat.add_mod q₁ t 2
  have h2 := Nat.add_mod q₂ t 2
  omega

private lemma alternating_window_count_sum (D : List StepSize) (a : ℕ)
    (hDlen : D.length = 2 * a) (hDlen_pos : 0 < D.length)
    (hbin_D : ∀ i, (hi : i < D.length) → D[i] = .L ∨ D[i] = .m)
    (halt : ∀ i, (hi : i < D.length) → D[i] = D[i % 2]'(by omega))
    (hne_D : D[0]'(by omega) ≠ D[1]'(by omega))
    (q₁ q₂ α' : ℕ) (hq : q₁ % 2 ≠ q₂ % 2) :
    ((List.range α').map (fun t =>
      D[(q₁ + t) % D.length]'(Nat.mod_lt _ hDlen_pos))).count .L +
    ((List.range α').map (fun t =>
      D[(q₂ + t) % D.length]'(Nat.mod_lt _ hDlen_pos))).count .L = α' := by
  have hdvd2 : 2 ∣ D.length := ⟨a, hDlen⟩
  -- The two D-values at corresponding positions are always different
  have hne_pair : ∀ t, D[(q₁ + t) % D.length]'(Nat.mod_lt _ hDlen_pos) ≠
      D[(q₂ + t) % D.length]'(Nat.mod_lt _ hDlen_pos) := by
    intro t
    have h1 := halt ((q₁ + t) % D.length) (Nat.mod_lt _ hDlen_pos)
    have h2 := halt ((q₂ + t) % D.length) (Nat.mod_lt _ hDlen_pos)
    rw [h1, h2]
    have hp : (q₁ + t) % D.length % 2 ≠ (q₂ + t) % D.length % 2 := by
      rw [Nat.mod_mod_of_dvd _ hdvd2, Nat.mod_mod_of_dvd _ hdvd2]
      exact add_mod_two_ne hq t
    rcases Nat.mod_two_eq_zero_or_one ((q₁ + t) % D.length) with hp₁ | hp₁ <;>
      rcases Nat.mod_two_eq_zero_or_one ((q₂ + t) % D.length) with hp₂ | hp₂
    · exact absurd (hp₁.trans hp₂.symm) hp
    · simp only [hp₁, hp₂]; exact hne_D
    · simp only [hp₁, hp₂]; exact Ne.symm hne_D
    · exact absurd (hp₁.trans hp₂.symm) hp
  -- Each pair contributes exactly 1 .L total
  have hone : ∀ t,
      (if D[(q₁ + t) % D.length]'(Nat.mod_lt _ hDlen_pos) == .L then 1 else 0) +
      (if D[(q₂ + t) % D.length]'(Nat.mod_lt _ hDlen_pos) == .L then 1 else 0) = 1 := by
    intro t
    have hne := hne_pair t
    have hb1 := hbin_D ((q₁ + t) % D.length) (Nat.mod_lt _ hDlen_pos)
    have hb2 := hbin_D ((q₂ + t) % D.length) (Nat.mod_lt _ hDlen_pos)
    rcases hb1 with h1 | h1 <;> rcases hb2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [h1, h2]; decide
    · rw [h1, h2]; decide
    · exact absurd (h1.trans h2.symm) hne
  -- Induction on α'
  induction α' with
  | zero => simp
  | succ α' ih =>
    rw [List.range_succ, List.map_append, List.map_append,
        List.count_append, List.count_append,
        List.map_singleton, List.map_singleton]
    simp only [List.count_cons, List.count_nil]
    have := hone α'
    omega

/-- **Ternary 2-step rotation**: For a ternary word `w` whose binary projection
    is a MOS with even period `p`, and whose non-`s` letters alternate `L/m`
    (from `isPartialDeletionMOS w .s`), the ternary 2-step count vectors at
    odd positions are a cyclic rotation of those at even positions.

    **Proof strategy**: Extends `binary_2step_even_odd_rotation` to the ternary case.
    At non-mixed binary 2-step positions:
    - `(2, 0)`: both letters are non-s → ternary 2-step is always `(1,1,0)`
    - `(0, 2)`: both are s → ternary 2-step is always `(0,0,2)`
    At mixed `(1, 1)` positions: the L/m assignment depends on the "rank parity"
    (position index among non-s letters mod 2). The rank parity is preserved under
    the mode shift because the MOS substitution structure has period-2 filling:
    the number of non-s letters in a k-step window (= `g.L`) controls the parity,
    and the combination of `g.L` parity with the half-period L↔m twist (from
    `kStepVector_two_twist`) ensures the ternary 2-step counts match.
    When `g.L` is even: `V_ternary(i) = V_ternary(i+k)` at mixed positions.
    When `g.L` is odd: `V_ternary(i+k) = twist(V_ternary(i))`, but then
    `twist(V_ternary(i)) = V_ternary(i+p)`, giving `V_ternary(i+k) = V_ternary(i+p)`,
    so the rotation offset shifts by `p/2`. -/
private lemma ternary_2step_rotation_even_period
    (w : TernaryNecklace n)
    (a c : ℕ) (ha_pos : a > 0) (hc_pos : c > 0) (ha_odd : a % 2 = 1)
    (hcop : Nat.Coprime a c) (hn_eq : n = 2 * a + 2 * c)
    (hcountL : Necklace.count w .L = a) (hcountm : Necklace.count w .m = a)
    (hcounts : Necklace.count w .s = 2 * c)
    (hmos : isPartialPairwiseMOS w .L .m)
    (hdel : isPartialDeletionMOS w .s)
    (hp_even : (a + c) % 2 = 0) (hp_ge4 : a + c ≥ 4) :
    let p := n / 2
    ∃ d : ℕ, ∀ j : Fin p,
      Necklace.kStepVector w (j.val * 2 + 1) 2 =
      Necklace.kStepVector w (((j.val + d) % p) * 2) 2 := by
  set p := n / 2 with hp_def
  have hp_val : p = a + c := by omega
  have hp_pos : p > 0 := by omega
  have hn_pos : n > 0 := by omega
  have hp_even' : p % 2 = 0 := by omega
  -- ===== Binary MOS setup =====
  set B := identifiedToBinary (TernaryNecklace.identifyPair w .L .m) with hB_def
  have hB_mos : BinaryNecklace.isMOS B :=
    identifiedToBinary_isMOS w hcountL hcountm hcounts ha_pos (by omega) hmos
  have hB_countL : Necklace.count B .L = 2 * a :=
    identifiedToBinary_count_L w hcountL hcountm
  have hB_counts : Necklace.count B .s = 2 * c :=
    identifiedToBinary_count_s w hcounts
  have hpLen : (Necklace.period B).length = p := by
    have := binary_mos_period_half a c ha_pos hc_pos hcop hn_eq B hB_mos hB_countL hB_counts
    omega
  -- ===== Binary rotation =====
  obtain ⟨d_bin, hd_bin⟩ := binary_2step_even_odd_rotation B hB_mos p hpLen hp_even' hp_pos
  -- ===== s-components match under d_bin =====
  have hs_eq : ∀ j : Fin p,
      Necklace.kStepVector w (j.val * 2 + 1) 2 .s =
      Necklace.kStepVector w (((j.val + d_bin) % p) * 2) 2 .s := by
    intro j
    have h := congr_fun (hd_bin j) .s
    rwa [identifiedToBinary_kStepVector_s w _ 2,
         identifiedToBinary_kStepVector_s w _ 2] at h
  -- ===== Even strand twist: shifting by p/2 swaps L↔m =====
  -- V(2*((j+d+p/2)%p), x) = V(2*((j+d)%p), swap(x))
  have htwist_strand : ∀ j : Fin p, ∀ x : StepSize,
      Necklace.kStepVector w (((j.val + (d_bin + p / 2)) % p) * 2) 2 x =
      Necklace.kStepVector w (((j.val + d_bin) % p) * 2) 2
        (match x with | .L => .m | .m => .L | .s => .s) := by
    intro j x
    set r := (j.val + d_bin) % p with hr_def
    have hr_lt : r < p := Nat.mod_lt _ hp_pos
    -- (j + d_bin + p/2) % p = (r + p/2) % p
    have hmod : (j.val + (d_bin + p / 2)) % p = (r + p / 2) % p := by
      rw [hr_def]; rw [show j.val + (d_bin + p / 2) = j.val + d_bin + p / 2 from by omega]
      rw [Nat.add_mod, Nat.mod_eq_of_lt (show p / 2 < p from by omega)]
    rw [hmod]
    -- Case split: r + p/2 < p or r + p/2 ≥ p
    by_cases hrp : r + p / 2 < p
    · -- (r + p/2) % p = r + p/2
      rw [Nat.mod_eq_of_lt hrp]
      -- 2*(r + p/2) = 2*r + p
      rw [show (r + p / 2) * 2 = r * 2 + p from by omega]
      -- Use kStepVector_two_twist at position r*2
      exact kStepVector_two_twist w a c ha_pos hc_pos ha_odd hcop hn_eq
        hcountL hcountm hcounts hmos hdel (r * 2) x
    · -- (r + p/2) % p = r + p/2 - p
      push_neg at hrp
      have hrp_mod : (r + p / 2) % p = r + p / 2 - p := by
        conv_lhs => rw [show r + p / 2 = (r + p / 2 - p) + 1 * p from by omega]
        rw [Nat.add_mul_mod_self_right,
            Nat.mod_eq_of_lt (by omega : r + p / 2 - p < p)]
      rw [hrp_mod]
      -- 2*(r + p/2 - p) = 2*r + p - 2*p = 2*r + p - n
      -- V(2*r + p - n) = V(2*r + p) by n-periodicity (backwards)
      have hpos_eq : (r + p / 2 - p) * 2 + n = r * 2 + p := by omega
      have hV_shift : Necklace.kStepVector w ((r + p / 2 - p) * 2) 2 =
          Necklace.kStepVector w (r * 2 + p) 2 := by
        rw [← hpos_eq, kStepVector_n_periodic]
      rw [hV_shift]
      exact kStepVector_two_twist w a c ha_pos hc_pos ha_odd hcop hn_eq
        hcountL hcountm hcounts hmos hdel (r * 2) x
  -- ===== s-components match under d_bin + p/2 =====
  have hs_shift : ∀ j : Fin p,
      Necklace.kStepVector w (j.val * 2 + 1) 2 .s =
      Necklace.kStepVector w (((j.val + (d_bin + p / 2)) % p) * 2) 2 .s := by
    intro j
    rw [htwist_strand j .s]; exact hs_eq j
  -- ===== Uniformity: either d_bin or d_bin + p/2 works for L =====
  -- At non-mixed binary 2-step positions: V_ternary(L) matches with BOTH offsets
  --   (since (1,1,0) and (0,0,2) are L↔m symmetric)
  -- At mixed (1,1) positions: exactly one of d_bin, d_bin+p/2 works.
  -- The rank parity argument (using nonSBefore_advance with the MOS generator)
  -- shows the choice is uniform across all mixed positions.
  have h_uniform : (∀ j : Fin p,
      Necklace.kStepVector w (j.val * 2 + 1) 2 .L =
      Necklace.kStepVector w (((j.val + d_bin) % p) * 2) 2 .L) ∨
    (∀ j : Fin p,
      Necklace.kStepVector w (j.val * 2 + 1) 2 .L =
      Necklace.kStepVector w (((j.val + (d_bin + p / 2)) % p) * 2) 2 .L) := by
    -- ===== Parity argument: nonSBefore sum has constant parity =====
    -- At non-mixed (0,2) and (2,0) binary positions, V.L matches for any offset.
    -- At mixed (1,1) positions, V.L depends on nonSBefore(position) % 2.
    -- The key: (nb(2j+1) + nb(2*(j+d)%p)) % 2 is constant in j,
    -- because advancing j by 1 changes the sum by 2α ≡ 0 (mod 2).
    -- ===== Setup ordered deletion word D =====
    set D := TernaryNecklace.orderedDeletion w .s with hD_def
    have hDlen : D.length = 2 * a := by
      have := orderedDeletion_length w .s; rw [hcounts] at this; linarith
    have hDlen_pos : 0 < D.length := by omega
    have hbin_D : ∀ i, (hi : i < D.length) → D[i] = .L ∨ D[i] = .m := by
      intro i hi
      have hmem := List.getElem_mem hi
      simp only [D, TernaryNecklace.orderedDeletion, List.mem_filter,
        decide_eq_true_eq] at hmem
      rcases hval : D[i] with _ | _ | _
      · left; rfl
      · right; rfl
      · exact absurd hval hmem.2
    have hDcountL : D.count .L = a := by
      rw [hD_def, orderedDeletion_count_ne w .s .L (by decide)]; exact hcountL
    have hDcountm : D.count .m = a := by
      rw [hD_def, orderedDeletion_count_ne w .s .m (by decide)]; exact hcountm
    obtain ⟨halt, hne_D⟩ := balanced_circular_mos_is_alternating D a ha_pos hDlen
      hbin_D hDcountL hDcountm hdel
    -- ===== nonSBefore setup =====
    set wList := (List.range n).map (fun i => w (↑i : ZMod n)) with hwList_def
    set nb : ℕ → ℕ := fun i =>
      ((wList.take (i % n)).filter (· ≠ .s)).length with hnb_def
    have hdvd2 : 2 ∣ D.length := ⟨a, hDlen⟩
    have h_mod2 : ∀ x y : ℕ, x % D.length = y % D.length → x % 2 = y % 2 :=
      fun x y h => by
        calc x % 2 = x % D.length % 2 := (Nat.mod_mod_of_dvd x hdvd2).symm
          _ = y % D.length % 2 := by rw [h]
          _ = y % 2 := Nat.mod_mod_of_dvd y hdvd2
    -- ===== Parity constancy =====
    have hparity_const : ∀ j₁ j₂ : Fin p,
        (nb (j₁.val * 2 + 1) + nb (((j₁.val + d_bin) % p) * 2)) % 2 =
        (nb (j₂.val * 2 + 1) + nb (((j₂.val + d_bin) % p) * 2)) % 2 := by
      suffices hstep : ∀ j : ℕ, j + 1 < p →
          (nb ((j + 1) * 2 + 1) + nb (((j + 1 + d_bin) % p) * 2)) % 2 =
          (nb (j * 2 + 1) + nb (((j + d_bin) % p) * 2)) % 2 by
        suffices hall : ∀ j : ℕ, j < p →
            (nb (j * 2 + 1) + nb (((j + d_bin) % p) * 2)) % 2 =
            (nb (0 * 2 + 1) + nb (((0 + d_bin) % p) * 2)) % 2 by
          intro j₁ j₂; rw [hall j₁.val j₁.isLt, hall j₂.val j₂.isLt]
        intro j hj; induction j with
        | zero => rfl
        | succ j ih => rw [hstep j (by omega), ih (by omega)]
      intro j hj
      -- Odd strand advance: nb((j+1)*2+1) ≡ nb(j*2+1) + α (mod D.length)
      set α := ((Necklace.slice w (j * 2 + 1) (j * 2 + 3)).filter (· ≠ .s)).length
      have hodd := nonSBefore_advance w (j * 2 + 1) 2 α (by omega) rfl
      rw [show j * 2 + 1 + 2 = (j + 1) * 2 + 1 from by ring] at hodd
      -- Even strand advance
      set e := (j + d_bin) % p with he_def
      have he_lt : e < p := Nat.mod_lt _ hp_pos
      set β := ((Necklace.slice w (e * 2) (e * 2 + 2)).filter (· ≠ .s)).length
      have heven := nonSBefore_advance w (e * 2) 2 β (by omega) rfl
      rw [show e * 2 + 2 = (e + 1) * 2 from by ring] at heven
      -- Even-strand wrap: (e+1)*2 % n = ((j+1+d)%p)*2
      have he_next : (e + 1) * 2 % n = ((j + 1 + d_bin) % p) * 2 := by
        have he_mod : (j + 1 + d_bin) % p = (e + 1) % p := by
          rw [he_def, show j + 1 + d_bin = j + d_bin + 1 from by omega,
            Nat.add_mod (j + d_bin) 1 p,
            Nat.mod_eq_of_lt (show (1 : ℕ) < p from by omega)]
        by_cases hep : e + 1 < p
        · rw [Nat.mod_eq_of_lt (show (e + 1) * 2 < n from by omega),
            he_mod, Nat.mod_eq_of_lt hep]
        · have hep_eq : e + 1 = p := by omega
          have h1 : (e + 1) * 2 = n := by omega
          have h2 : (j + 1 + d_bin) % p = 0 := by
            rw [he_mod, hep_eq, Nat.mod_self]
          rw [h1, Nat.mod_self, h2]
      -- Convert mod-D.length to mod-2, typed with nb
      have hodd2 : nb ((j + 1) * 2 + 1) % 2 = (nb (j * 2 + 1) + α) % 2 :=
        h_mod2 _ _ hodd
      -- Connect nb(((j+1+d)%p)*2) to nb((e+1)*2) via he_next
      -- nb depends on its arg only through arg % n
      have nb_mod_n : ∀ a b : ℕ, a % n = b % n → nb a = nb b := by
        intro a b hab; simp only [hnb_def, hab]
      have harg_eq : (((j + 1 + d_bin) % p) * 2) % n = ((e + 1) * 2) % n := by
        rw [he_next]
        exact Nat.mod_eq_of_lt (by
          have h1 := Nat.mod_lt (j + 1 + d_bin) hp_pos
          have h2 : n = p * 2 := by rw [hp_val]; omega
          omega)
      have hnb_connect : nb (((j + 1 + d_bin) % p) * 2) = nb ((e + 1) * 2) :=
        nb_mod_n _ _ harg_eq
      have heven2 : nb (((j + 1 + d_bin) % p) * 2) % 2 = (nb (e * 2) + β) % 2 := by
        rw [hnb_connect]; exact h_mod2 _ _ heven
      -- α = β (non-s counts match via hs_eq)
      have hαβ : α = β :=
        filter_neq_s_length_eq_of_kStepVector_s_eq w _ _ 2 (hs_eq ⟨j, by omega⟩)
      -- Combine: sum changes by α + β = 2α ≡ 0 (mod 2)
      calc (nb ((j + 1) * 2 + 1) + nb (((j + 1 + d_bin) % p) * 2)) % 2
          = (nb ((j + 1) * 2 + 1) % 2 + nb (((j + 1 + d_bin) % p) * 2) % 2) % 2 :=
            Nat.add_mod ..
        _ = ((nb (j * 2 + 1) + α) % 2 + (nb (e * 2) + β) % 2) % 2 := by
            rw [hodd2, heven2]
        _ = (nb (j * 2 + 1) + α + (nb (e * 2) + β)) % 2 := by
            rw [← Nat.add_mod]
        _ = (nb (j * 2 + 1) + nb (e * 2) + 2 * α) % 2 := by rw [hαβ]; ring_nf
        _ = (nb (j * 2 + 1) + nb (e * 2)) % 2 := by
            rw [show nb (j * 2 + 1) + nb (e * 2) + 2 * α =
              nb (j * 2 + 1) + nb (e * 2) + α * 2 from by ring,
              Nat.add_mul_mod_self_right]
        _ = (nb (j * 2 + 1) + nb (((j + d_bin) % p) * 2)) % 2 := by rfl
    -- ===== D-window L-count depends only on q % 2 =====
    have hDwindow_mod2 : ∀ q₁ q₂ α' : ℕ, q₁ % 2 = q₂ % 2 →
        ((List.range α').map (fun t =>
          D[(q₁ + t) % D.length]'(Nat.mod_lt _ hDlen_pos))).count .L =
        ((List.range α').map (fun t =>
          D[(q₂ + t) % D.length]'(Nat.mod_lt _ hDlen_pos))).count .L := by
      intro q₁ q₂ α' hq; congr 1; apply List.map_congr_left; intro t _
      have h1 := halt ((q₁ + t) % D.length) (Nat.mod_lt _ hDlen_pos)
      have h2 := halt ((q₂ + t) % D.length) (Nat.mod_lt _ hDlen_pos)
      rw [h1, h2]; congr 1
      calc (q₁ + t) % D.length % 2 = (q₁ + t) % 2 := Nat.mod_mod_of_dvd _ hdvd2
        _ = (q₁ % 2 + t % 2) % 2 := Nat.add_mod ..
        _ = (q₂ % 2 + t % 2) % 2 := by rw [hq]
        _ = (q₂ + t) % 2 := (Nat.add_mod ..).symm
        _ = (q₂ + t) % D.length % 2 := (Nat.mod_mod_of_dvd _ hdvd2).symm
    -- V.L is non-negative (it's a count cast to ℤ)
    have hVL_nn : ∀ r k, 0 ≤ Necklace.kStepVector w r k .L := by
      intro r k; change 0 ≤ (ZVector.ofList (Necklace.slice w r (r + k))) .L
      unfold ZVector.ofList; simp
    -- ===== Case split on parity =====
    by_cases hc : (nb 1 + nb ((d_bin % p) * 2)) % 2 = 0
    · -- Same parity → d_bin works
      left; intro j
      have hpc := hparity_const j ⟨0, hp_pos⟩; simp at hpc; rw [hc] at hpc
      have hq_parity : nb (j.val * 2 + 1) % 2 = nb (((j.val + d_bin) % p) * 2) % 2 := by
        omega
      -- Both have D-window of same size starting at positions with same parity
      set α_j := ((Necklace.slice w (j.val * 2 + 1) (j.val * 2 + 3)).filter
        (· ≠ .s)).length
      have hα_eq : α_j = ((Necklace.slice w (((j.val + d_bin) % p) * 2)
          (((j.val + d_bin) % p) * 2 + 2)).filter (· ≠ .s)).length :=
        filter_neq_s_length_eq_of_kStepVector_s_eq w _ _ 2 (hs_eq j)
      have hbr_odd := orderedDeletion_window_Lcount w (j.val * 2 + 1) 2 α_j
        hDlen_pos (by omega) rfl
      have hbr_even := orderedDeletion_window_Lcount w (((j.val + d_bin) % p) * 2) 2 α_j
        hDlen_pos (by omega) hα_eq
      -- D-window L-counts match since q₁ % 2 = q₂ % 2
      have hcounts_eq : (Necklace.kStepVector w (j.val * 2 + 1) 2 .L).natAbs =
          (Necklace.kStepVector w (((j.val + d_bin) % p) * 2) 2 .L).natAbs := by
        rw [← hbr_odd, ← hbr_even]
        exact hDwindow_mod2 _ _ α_j hq_parity
      -- natAbs equality + non-negativity → integer equality
      have h1 := Int.natAbs_of_nonneg (hVL_nn (j.val * 2 + 1) 2)
      have h2 := Int.natAbs_of_nonneg (hVL_nn (((j.val + d_bin) % p) * 2) 2)
      linarith [congrArg (↑· : ℕ → ℤ) hcounts_eq]
    · -- Different parity → d_bin + p/2 works
      right; intro j
      -- By htwist_strand: V(twist_even, .L) = V(even, .m)
      have htwist_L := htwist_strand j .L
      dsimp only at htwist_L
      rw [htwist_L]
      -- Goal: V.L(odd) = V.m(even). Use totals + D-window.
      have hpc := hparity_const j ⟨0, hp_pos⟩; simp at hpc
      have hq_diff : nb (j.val * 2 + 1) % 2 ≠ nb (((j.val + d_bin) % p) * 2) % 2 := by
        omega
      set α_j := ((Necklace.slice w (j.val * 2 + 1) (j.val * 2 + 3)).filter
        (· ≠ .s)).length
      have hα_eq : α_j = ((Necklace.slice w (((j.val + d_bin) % p) * 2)
          (((j.val + d_bin) % p) * 2 + 2)).filter (· ≠ .s)).length :=
        filter_neq_s_length_eq_of_kStepVector_s_eq w _ _ 2 (hs_eq j)
      have hbr_odd := orderedDeletion_window_Lcount w (j.val * 2 + 1) 2 α_j
        hDlen_pos (by omega) rfl
      have hbr_even := orderedDeletion_window_Lcount w (((j.val + d_bin) % p) * 2) 2 α_j
        hDlen_pos (by omega) hα_eq
      -- V.L(odd).natAbs + V.L(even).natAbs = α_j
      -- (D-window L-counts at opposite parities sum to window size)
      have hDwindow_sum := alternating_window_count_sum D a hDlen hDlen_pos hbin_D halt hne_D
      have hsum_α : (Necklace.kStepVector w (j.val * 2 + 1) 2 .L).natAbs +
          (Necklace.kStepVector w (((j.val + d_bin) % p) * 2) 2 .L).natAbs = α_j := by
        rw [← hbr_odd, ← hbr_even]
        exact hDwindow_sum _ _ α_j hq_diff
      -- V.L(even) + V.m(even) = ↑α_j (total non-s count in window)
      have hLm_even : Necklace.kStepVector w (((j.val + d_bin) % p) * 2) 2 .L +
          Necklace.kStepVector w (((j.val + d_bin) % p) * 2) 2 .m = ↑α_j := by
        have ht := kStepVector_total_count_ternary w (((j.val + d_bin) % p) * 2) 2
        have hs_j := hs_eq j
        -- Suffices: ↑α_j + V.s(odd) = 2
        suffices hα_s : (↑α_j : ℤ) + Necklace.kStepVector w (j.val * 2 + 1) 2 .s = 2 by
          push_cast at ht; linarith
        -- V.s = ↑(filter(==s).length)
        have hv_s : Necklace.kStepVector w (j.val * 2 + 1) 2 .s =
            ↑((Necklace.slice w (j.val * 2 + 1) (j.val * 2 + 1 + 2)).filter
              (· == .s)).length := by
          unfold Necklace.kStepVector ZVector.ofList; simp
        rw [hv_s]
        -- α_j + filter(==s).length = slice.length = 2
        have hfilt : α_j + ((Necklace.slice w (j.val * 2 + 1) (j.val * 2 + 1 + 2)).filter
            (· == .s)).length = 2 := by
          -- Bridge α_j to the filter complement form
          have hα_rfl : α_j = ((Necklace.slice w (j.val * 2 + 1) (j.val * 2 + 1 + 2)).filter
              (· ≠ .s)).length := rfl
          have hc := List.length_eq_length_filter_add (fun x => !decide (x = StepSize.s))
            (l := Necklace.slice w (j.val * 2 + 1) (j.val * 2 + 1 + 2))
          simp only [Bool.not_not] at hc
          have h1 : (Necklace.slice w (j.val * 2 + 1) (j.val * 2 + 1 + 2)).filter
              (fun x => !decide (x = StepSize.s)) =
              (Necklace.slice w (j.val * 2 + 1) (j.val * 2 + 1 + 2)).filter (· ≠ .s) := by
            congr 1; ext x; simp [ne_eq]
          have h2 : (Necklace.slice w (j.val * 2 + 1) (j.val * 2 + 1 + 2)).filter
              (fun x => decide (x = StepSize.s)) =
              (Necklace.slice w (j.val * 2 + 1) (j.val * 2 + 1 + 2)).filter (· == .s) := by
            congr 1
          rw [h1, h2] at hc
          have hlen := Necklace.slice_length w (j.val * 2 + 1) (j.val * 2 + 1 + 2)
          omega
        exact_mod_cast hfilt
      -- Combine: V.L(odd) = V.m(even)
      have h1 := Int.natAbs_of_nonneg (hVL_nn (j.val * 2 + 1) 2)
      have h2 := Int.natAbs_of_nonneg (hVL_nn (((j.val + d_bin) % p) * 2) 2)
      have hcast : (↑(Necklace.kStepVector w (j.val * 2 + 1) 2 .L).natAbs : ℤ) +
          ↑(Necklace.kStepVector w (((j.val + d_bin) % p) * 2) 2 .L).natAbs = ↑α_j := by
        exact_mod_cast hsum_α
      linarith
  -- ===== Conclude =====
  rcases h_uniform with hL | hL
  · -- d_bin works
    exact ⟨d_bin, fun j => by
      funext x; cases x with
      | L => exact hL j
      | m =>
        have ht1 := kStepVector_total_count_ternary w (j.val * 2 + 1) 2
        have ht2 := kStepVector_total_count_ternary w (((j.val + d_bin) % p) * 2) 2
        linarith [hL j, hs_eq j]
      | s => exact hs_eq j⟩
  · -- d_bin + p/2 works
    exact ⟨d_bin + p / 2, fun j => by
      funext x; cases x with
      | L => exact hL j
      | m =>
        have ht1 := kStepVector_total_count_ternary w (j.val * 2 + 1) 2
        have ht2 := kStepVector_total_count_ternary w
          (((j.val + (d_bin + p / 2)) % p) * 2) 2
        linarith [hL j, hs_shift j]
      | s => exact hs_shift j⟩

/-- Letter equality from period congruence: if two positions are congruent
    modulo the period length, the binary necklace has the same letter there. -/
private lemma binary_letter_eq_of_period_cong (B : BinaryNecklace n)
    (_hmos : BinaryNecklace.isMOS B)
    (p : ℕ) (hpLen : (Necklace.period B).length = p) (hp_pos : p > 1)
    (a₁ a₂ : ℕ) (hcong : a₁ % p = a₂ % p) :
    B ((a₁ : ℕ) : ZMod n) = B ((a₂ : ℕ) : ZMod n) := by
  have heq1step : Necklace.kStepVector B a₁ 1 = Necklace.kStepVector B a₂ 1 := by
    rw [← kStepVector_mod_period B a₁ 1 (by rw [hpLen]; omega), hpLen,
        ← kStepVector_mod_period B a₂ 1 (by rw [hpLen]; omega), hpLen, hcong]
  have h3 := congr_fun heq1step BinaryStep.L
  rw [kStepVector_one_eq B a₁ BinaryStep.L, kStepVector_one_eq B a₂ BinaryStep.L] at h3
  cases hc1 : B ((a₁ : ℕ) : ZMod n) <;> cases hc2 : B ((a₂ : ℕ) : ZMod n)
  · rfl
  · exfalso; simp [hc1, hc2] at h3
  · exfalso; simp [hc1, hc2] at h3
  · rfl

/-- **MOS letter palindrome**: For a binary MOS with odd period `p ≥ 3`,
    there exists a rotation `r` such that the letter at position `r + j`
    equals the letter at position `r + p - 1 - j` for all `j < p`.

    **Proof strategy**: The generator `k₀` (coprime to `p`) gives a unique
    "bad" position `b` where the `k₀`-step vector differs. The letters in
    the rank ordering (visiting positions by `k₀`-steps) form two contiguous
    arcs separated by two break ranks. Choosing `r` so that the palindromic
    reflection maps each arc to itself gives the full letter palindrome. -/
private lemma mos_letter_palindrome (B : BinaryNecklace n)
    (hmos : BinaryNecklace.isMOS B)
    (p : ℕ) (hpLen : (Necklace.period B).length = p)
    (hp_odd : p % 2 = 1) (hp_ge3 : p ≥ 3) :
    ∃ r : ℕ, ∀ j : ℕ, j < p →
      B ((r + j : ℕ) : ZMod n) = B ((r + p - 1 - j : ℕ) : ZMod n) := by
  -- ===== Part A: Generator setup =====
  have hbin : BinaryNecklace.isBinary B := hmos.1
  have hp_pos : p > 0 := by omega
  obtain ⟨g, hgen⟩ := allMOSScalesHaveGenerator n B hmos
  obtain ⟨k₀, hk₀_pos, hk₀_lt, hk₀_count⟩ :=
    generator_implies_p_minus_one_occurrences B hbin g hgen
  rw [hpLen] at hk₀_lt hk₀_count
  have hk₀_cop : Nat.Coprime k₀ p := by
    have := p_minus_one_occurrences_implies_coprime_to_period B hbin k₀ hk₀_pos
      (by rw [hpLen]; exact hk₀_lt) g (by rw [hpLen]; exact hk₀_count)
    rwa [hpLen] at this
  -- ===== Part B: Unique bad position =====
  dsimp only [countKStepVectorPerPeriod] at hk₀_count
  rw [hpLen] at hk₀_count
  have hbad : ∃ b : ℕ, b < p ∧ Necklace.kStepVector B b k₀ ≠ g ∧
      (∀ i : ℕ, i < p → i ≠ b → Necklace.kStepVector B i k₀ = g) := by
    set pred := fun j => decide (Necklace.kStepVector B j k₀ = g)
    have hexists : ∃ b, b < p ∧ Necklace.kStepVector B b k₀ ≠ g := by
      by_contra hall; push_neg at hall
      have h := List.countP_eq_length.mpr (fun i hi =>
        decide_eq_true_eq.mpr (hall i (List.mem_range.mp hi)))
      rw [List.length_range] at h
      change (List.range p).countP pred = p at h; omega
    obtain ⟨b, hb_lt, hb_ne⟩ := hexists
    refine ⟨b, hb_lt, hb_ne, fun i hi hne => ?_⟩
    by_contra hi_ne
    have hp_i : pred i = false := by simp [pred, hi_ne]
    have hp_b : pred b = false := by simp [pred, hb_ne]
    have hi_mem : i ∈ List.range p := List.mem_range.mpr hi
    have hb_mem : b ∈ List.range p := List.mem_range.mpr hb_lt
    have h1 : ((List.range p).erase i).countP pred = (List.range p).countP pred := by
      rw [List.countP_erase]; simp [hi_mem, hp_i]
    have hb_mem' : b ∈ (List.range p).erase i :=
      List.mem_erase_of_ne (Ne.symm hne) |>.mpr hb_mem
    have h2 : (((List.range p).erase i).erase b).countP pred =
        ((List.range p).erase i).countP pred := by
      rw [List.countP_erase]; simp [hb_mem', hp_b]
    have h3 : (((List.range p).erase i).erase b).length = p - 2 := by
      rw [List.length_erase_of_mem hb_mem',
        List.length_erase_of_mem hi_mem, List.length_range]; omega
    have : (List.range p).countP pred ≤ p - 2 :=
      calc (List.range p).countP pred
          = ((List.range p).erase i).countP pred := h1.symm
        _ = (((List.range p).erase i).erase b).countP pred := h2.symm
        _ ≤ (((List.range p).erase i).erase b).length := List.countP_le_length
        _ = p - 2 := h3
    omega
  obtain ⟨b, hb_lt, _hb_ne, hb_good⟩ := hbad
  -- ===== Part C: Good positions fixed under k₀-shift =====
  have hgood_all : ∀ i : ℕ, i % p ≠ b → Necklace.kStepVector B i k₀ = g := by
    intro i hi
    have h := hb_good (i % p) (Nat.mod_lt i hp_pos) hi
    rw [← kStepVector_mod_period B i k₀ (by rw [hpLen]; omega), hpLen]; exact h
  have hfixed : ∀ i : ℕ, i % p ≠ b → (i + 1) % p ≠ b →
      B ((i : ℕ) : ZMod n) = B (((i + k₀) : ℕ) : ZMod n) := by
    intro i hi1 hi2
    exact binary_kstep_eq_implies_letter_eq B i k₀
      (by rw [hgood_all i hi1, hgood_all (i + 1) hi2])
  -- ===== Part D: Chain lemma =====
  -- B(m) = B(m + t * k₀) when no intermediate position hits the bad position
  have hchain : ∀ (m t : ℕ),
      (∀ s, s < t → (m + s * k₀) % p ≠ b) →
      (∀ s, s < t → (m + s * k₀ + 1) % p ≠ b) →
      B ((m : ℕ) : ZMod n) = B (((m + t * k₀) : ℕ) : ZMod n) := by
    intro m t hb1 hb2
    induction t with
    | zero => simp
    | succ t' ih =>
      have h1 := ih (fun s hs => hb1 s (by omega)) (fun s hs => hb2 s (by omega))
      have h2 := hfixed (m + t' * k₀) (hb1 t' (by omega)) (hb2 t' (by omega))
      rw [h1]; convert h2 using 2; push_cast; ring
  -- ===== Part E: Palindrome via arc analysis =====
  -- Strategy: Choose r' = (2b + k₀) * ((p+1)/2). For each j < p, find a chain
  -- of k₀-steps connecting r'+j to r'+p-1-j. The palindromic reflection
  -- guarantees that breaks (at b and b-1 mod p) always appear together in the
  -- same chain direction, so the other direction is break-free.
  haveI : NeZero p := ⟨by omega⟩
  -- E1: Coprime preimage — for any target < p, ∃ t < p with t * k₀ % p = target
  have hpreimage : ∀ target : ℕ, target < p → ∃ t < p, t * k₀ % p = target := by
    intro target ht
    have hbez : (↑k₀ : ZMod p) * ((Nat.gcdA k₀ p : ℤ) : ZMod p) = 1 := by
      have := congr_arg (fun x : ℤ => (x : ZMod p)) (Nat.gcd_eq_gcd_ab k₀ p)
      push_cast at this ⊢; rw [ZMod.natCast_self, zero_mul, add_zero] at this
      rw [show k₀.gcd p = 1 from hk₀_cop, Nat.cast_one] at this; exact this.symm
    set c := ((Nat.gcdA k₀ p : ℤ) : ZMod p)
    have hck : c * (↑k₀ : ZMod p) = 1 := by rw [mul_comm]; exact hbez
    set t₀ := ZMod.val ((↑target : ZMod p) * c)
    refine ⟨t₀, ZMod.val_lt _, ?_⟩
    suffices h : (↑(t₀ * k₀) : ZMod p) = (↑target : ZMod p) by
      have := congr_arg ZMod.val h
      simp only [ZMod.val_natCast] at this
      rw [Nat.mod_eq_of_lt ht] at this; exact this
    push_cast; rw [show (t₀ : ZMod p) = (↑target : ZMod p) * c from ZMod.natCast_zmod_val _]
    calc ((↑target : ZMod p) * c) * ↑k₀ = ↑target * (c * ↑k₀) := by ring
      _ = ↑target * 1 := by rw [hck]
      _ = ↑target := mul_one _
  -- E2: Choose palindromic rotation
  let r' := (2 * b + k₀) * ((p + 1) / 2)
  refine ⟨r', fun j hj => ?_⟩
  -- Trivial case: center of palindrome (j = (p-1)/2)
  by_cases hj_center : 2 * j + 1 = p
  · have : (r' + p - 1 - j : ℕ) = (r' + j : ℕ) := by omega
    simp only [this]
  · -- Nontrivial case: suffices to handle 2j+1 < p (other case by j ↔ p-1-j)
    suffices h_half : ∀ j', j' < p → 2 * j' + 1 ≠ p → 2 * j' + 1 < p →
        B ((r' + j' : ℕ) : ZMod n) = B ((r' + p - 1 - j' : ℕ) : ZMod n) by
      rcases Nat.lt_or_ge (2 * j + 1) p with hlt | hge
      · exact h_half j hj hj_center hlt
      · -- 2j+1 > p: reduce to j' = p-1-j
        have hj_big : 2 * j ≥ p := by omega
        have hj'_lt : p - 1 - j < p := by omega
        have hj'_ne : 2 * (p - 1 - j) + 1 ≠ p := by omega
        have hj'_small : 2 * (p - 1 - j) + 1 < p := by omega
        have := h_half (p - 1 - j) hj'_lt hj'_ne hj'_small
        -- this : B(r'+p-1-j) = B(r'+p-1-(p-1-j)) = B(r'+j)
        have hrw1 : (r' + p - 1 - (p - 1 - j) : ℕ) = (r' + j : ℕ) := by omega
        rw [hrw1] at this
        have hrw2 : (r' + p - 1 - j : ℕ) = (r' + (p - 1 - j) : ℕ) := by omega
        rw [hrw2]; exact this.symm
    intro j hj hj_center hj_small
    -- Now 2j+1 < p, so the chain argument works
    set m := r' + j with hm_def
    set Δ := p - 1 - 2 * j with hΔ_def
    have hΔ_pos : Δ > 0 := by omega
    have hΔ_lt : Δ < p := by omega
    have hΔ_eq : m + Δ = r' + (p - 1 - j) := by omega
    -- Find chain step count t with t * k₀ ≡ Δ (mod p)
    obtain ⟨t_fwd, ht_lt, ht_eq⟩ := hpreimage Δ hΔ_lt
    have ht_pos : t_fwd > 0 := by
      by_contra h; push_neg at h
      have : t_fwd = 0 := by omega
      simp [this] at ht_eq; omega
    set t_bwd := p - t_fwd with ht_bwd_def
    have ht_bwd_pos : t_bwd > 0 := by omega
    -- Forward target: (m + t_fwd * k₀) % p = (m + Δ) % p
    have hfwd_target : (m + t_fwd * k₀) % p = (m + Δ) % p := by
      have : (t_fwd * k₀) % p = Δ % p := by rw [ht_eq, Nat.mod_eq_of_lt hΔ_lt]
      rw [Nat.add_mod, this, ← Nat.add_mod]
    -- Backward target: (m + Δ + t_bwd * k₀) % p = m % p
    have hbwd_target : (m + Δ + t_bwd * k₀) % p = m % p := by
      have h1 : (m + t_fwd * k₀ + t_bwd * k₀) % p = m % p := by
        have hrw : m + t_fwd * k₀ + t_bwd * k₀ = m + k₀ * p := by
          calc m + t_fwd * k₀ + t_bwd * k₀
              = m + (t_fwd + t_bwd) * k₀ := by ring
            _ = m + p * k₀ := by rw [show t_fwd + t_bwd = p from by omega]
            _ = m + k₀ * p := by ring
        rw [hrw, Nat.add_mul_mod_self_right]
      have h2 : (m + Δ + t_bwd * k₀) % p = (m + t_fwd * k₀ + t_bwd * k₀) % p := by
        conv_lhs => rw [Nat.add_mod (m + Δ) (t_bwd * k₀) p]
        conv_rhs => rw [Nat.add_mod (m + t_fwd * k₀) (t_bwd * k₀) p]
        congr 1; congr 1; exact hfwd_target.symm
      rw [h2, h1]
    -- Reflection identity: 2m + (t_fwd-1)*k₀ ≡ 2b + p - 1 (mod p)
    have hrefl_sum : (2 * m + (t_fwd - 1) * k₀) % p = (2 * b + (p - 1)) % p := by
      -- 2*r' = (2*b+k₀)*(p+1), so 2*r' ≡ 2*b+k₀ (mod p)
      -- Then 2*m + (t_fwd-1)*k₀ = 2*b + k₀ + 2*j + t_fwd*k₀ - k₀
      --   = 2*b + 2*j + Δ = 2*b + p - 1, all mod p
      have hp1_half : 2 * ((p + 1) / 2) = p + 1 := by omega
      have h2r' : 2 * r' = (2 * b + k₀) * (p + 1) := by
        show 2 * ((2 * b + k₀) * ((p + 1) / 2)) = _
        calc 2 * ((2 * b + k₀) * ((p + 1) / 2))
            = (2 * b + k₀) * (2 * ((p + 1) / 2)) := by ring
          _ = (2 * b + k₀) * (p + 1) := by rw [hp1_half]
      have hΔ_sum : Δ + 2 * j = p - 1 := by omega
      set q := t_fwd * k₀ / p with hq_def
      have hdiv : p * q + Δ = t_fwd * k₀ := by
        have h1 := Nat.div_add_mod (t_fwd * k₀) p
        rw [ht_eq] at h1; exact h1
      -- Show: 2*m + (t_fwd-1)*k₀ = (2*b + p - 1) + (2*b + k₀ + q) * p
      have hkey : 2 * m + (t_fwd - 1) * k₀ = (2 * b + (p - 1)) + (2 * b + k₀ + q) * p := by
        have h3 : (t_fwd - 1) * k₀ + k₀ = t_fwd * k₀ := by
          have h := add_mul (t_fwd - 1) 1 k₀
          simp only [one_mul] at h
          rw [show t_fwd - 1 + 1 = t_fwd from by omega] at h
          linarith
        -- Expand products, add k₀ to both sides to avoid ℕ subtraction
        have hr_full : 2 * r' = (2 * b + k₀) * p + (2 * b + k₀) := by
          rw [h2r']; ring
        have hgoal_exp : (2 * b + k₀ + q) * p = (2 * b + k₀) * p + q * p := by ring
        rw [hgoal_exp]
        linarith [hm_def, hr_full, hdiv, hΔ_sum, h3, mul_comm p q]
      rw [hkey, Nat.add_mul_mod_self_right]
    -- Helper: from (a+1) % p = b, derive a % p = (b+p-1) % p
    have hab_pred : ∀ a : ℕ, (a + 1) % p = b → a % p = (b + (p - 1)) % p := by
      intro a ha
      have h := (Nat.add_mod_right a p).symm
      rw [show a + p = a + 1 + (p - 1) from by omega, Nat.add_mod, ha,
          Nat.mod_eq_of_lt (show p - 1 < p from by omega)] at h
      exact h
    -- Helper: ZMod cancellation — (a+c) % p = (a+x) % p → c = x (when c,x < p)
    have cancel_mod : ∀ (a c x : ℕ), c < p → x < p →
        (a + c) % p = (a + x) % p → c = x := by
      intro a c x hc hx heq
      have h1 : (↑a : ZMod p) + ↑c = ↑a + ↑x := by
        have := (ZMod.natCast_eq_natCast_iff (a + c) (a + x) p).mpr heq
        simp only [Nat.cast_add] at this; exact this
      have h2 : (↑c : ZMod p) = ↑x := add_left_cancel h1
      have h3 := (ZMod.natCast_eq_natCast_iff c x p).mp h2
      change c % p = x % p at h3
      rwa [Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hx] at h3
    -- Helper: coprime injectivity — s ↦ (m + s*k₀) % p is injective for s < p
    have hinj : ∀ s₁ s₂, s₁ < p → s₂ < p →
        (m + s₁ * k₀) % p = (m + s₂ * k₀) % p → s₁ = s₂ := by
      intro s₁ s₂ hs₁ hs₂ heq
      have hzmod : (↑m : ZMod p) + ↑s₁ * ↑k₀ = ↑m + ↑s₂ * ↑k₀ := by
        have := (ZMod.natCast_eq_natCast_iff (m + s₁ * k₀) (m + s₂ * k₀) p).mpr heq
        simp only [Nat.cast_add, Nat.cast_mul] at this; exact this
      have h2 : (↑s₁ : ZMod p) * ↑k₀ = ↑s₂ * ↑k₀ := add_left_cancel hzmod
      have hk₀_unit : IsUnit (↑k₀ : ZMod p) := by
        have hbez : (↑k₀ : ZMod p) * ((Nat.gcdA k₀ p : ℤ) : ZMod p) = 1 := by
          have := congr_arg (fun x : ℤ => (x : ZMod p)) (Nat.gcd_eq_gcd_ab k₀ p)
          push_cast at this ⊢; rw [ZMod.natCast_self, zero_mul, add_zero] at this
          rw [show k₀.gcd p = 1 from hk₀_cop, Nat.cast_one] at this; exact this.symm
        exact IsUnit.of_mul_eq_one _ hbez
      have h3 : (↑s₁ : ZMod p) = ↑s₂ := hk₀_unit.mul_right_cancel h2
      have h4 := (ZMod.natCast_eq_natCast_iff s₁ s₂ p).mp h3
      change s₁ % p = s₂ % p at h4
      rwa [Nat.mod_eq_of_lt hs₁, Nat.mod_eq_of_lt hs₂] at h4
    -- Helper: backward position s corresponds to forward position t_fwd + s
    have hbwd_as_fwd : ∀ s, (m + Δ + s * k₀) % p = (m + (t_fwd + s) * k₀) % p := by
      intro s
      have hrw : (t_fwd + s) * k₀ = t_fwd * k₀ + s * k₀ := by ring
      rw [hrw]
      conv_lhs => rw [show m + Δ + s * k₀ = (m + Δ) + s * k₀ from by ring]
      conv_rhs => rw [show m + (t_fwd * k₀ + s * k₀) = (m + t_fwd * k₀) + s * k₀ from by ring]
      rw [Nat.add_mod, Nat.add_mod (m + t_fwd * k₀)]
      congr 1; congr 1; exact hfwd_target.symm
    -- Reflection: forward chain avoiding b also avoids b-1 (mod p).
    have hfwd_clean_2_of_1 :
        (∀ s, s < t_fwd → (m + s * k₀) % p ≠ b) →
        (∀ s, s < t_fwd → (m + s * k₀ + 1) % p ≠ b) := by
      intro hno_b s hs habs
      -- From habs, (m + s*k₀) % p = (b+p-1) % p
      have hpred := hab_pred (m + s * k₀) habs
      -- Reflection: the sum (m+s*k₀) + (m+(t_fwd-1-s)*k₀) = 2m+(t_fwd-1)*k₀
      have hsum_eq : m + s * k₀ + (m + (t_fwd - 1 - s) * k₀) =
          2 * m + (t_fwd - 1) * k₀ := by
        have hsub : s + (t_fwd - 1 - s) = t_fwd - 1 := by omega
        have : s * k₀ + (t_fwd - 1 - s) * k₀ = (t_fwd - 1) * k₀ := by
          rw [← add_mul, hsub]
        linarith
      have hsum_mod : (m + s * k₀ + (m + (t_fwd - 1 - s) * k₀)) % p =
          (2 * b + (p - 1)) % p := by rw [hsum_eq]; exact hrefl_sum
      -- Extract c = (m+(t_fwd-1-s)*k₀) % p, show c = b via cancel_mod
      set c := (m + (t_fwd - 1 - s) * k₀) % p with hc_def
      have hc_lt : c < p := Nat.mod_lt _ hp_pos
      -- From hsum_mod: rewrite to get ((b+(p-1))%p + c) % p = (2*b + (p-1)) % p
      have hlhs : ((b + (p - 1)) % p + c) % p = (2 * b + (p - 1)) % p := by
        have h := hsum_mod
        rw [Nat.add_mod (m + s * k₀)] at h
        rw [hpred, ← hc_def] at h; exact h
      have hrhs : ((b + (p - 1)) % p + b) % p = (2 * b + (p - 1)) % p := by
        rw [Nat.add_mod ((b + (p - 1)) % p) b p, Nat.mod_mod, ← Nat.add_mod]
        congr 1; omega
      exact absurd (cancel_mod _ c b hc_lt hb_lt (hlhs.trans hrhs.symm))
        (hno_b _ (by omega))
    -- Disjointness: if forward chain hits b, backward chain avoids b and b-1.
    have hbwd_clean_of_fwd_hits :
        (∃ s, s < t_fwd ∧ (m + s * k₀) % p = b) →
        (∀ s, s < t_bwd → (m + Δ + s * k₀) % p ≠ b) ∧
        (∀ s, s < t_bwd → (m + Δ + s * k₀ + 1) % p ≠ b) := by
      intro ⟨s₀, hs₀_lt, hs₀_eq⟩
      -- By reflection, (m + (t_fwd-1-s₀)*k₀) has residue (b+p-1) % p
      have hrefl_step : (m + (t_fwd - 1 - s₀) * k₀) % p = (b + (p - 1)) % p := by
        set c := (m + (t_fwd - 1 - s₀) * k₀) % p with hc_def
        have hc_lt : c < p := Nat.mod_lt _ hp_pos
        have hsum_eq : m + s₀ * k₀ + (m + (t_fwd - 1 - s₀) * k₀) =
            2 * m + (t_fwd - 1) * k₀ := by
          have hsub : s₀ + (t_fwd - 1 - s₀) = t_fwd - 1 := by omega
          have : s₀ * k₀ + (t_fwd - 1 - s₀) * k₀ = (t_fwd - 1) * k₀ := by
            rw [← add_mul, hsub]
          linarith
        have hsum_mod : (m + s₀ * k₀ + (m + (t_fwd - 1 - s₀) * k₀)) % p =
            (2 * b + (p - 1)) % p := by rw [hsum_eq]; exact hrefl_sum
        -- (b + c) % p = (2*b + p - 1) % p, so c = (b + p - 1) % p
        have hbc : (b + c) % p = (2 * b + (p - 1)) % p := by
          have h := hsum_mod
          rw [Nat.add_mod (m + s₀ * k₀)] at h
          rw [hs₀_eq, ← hc_def] at h; exact h
        -- 2*b + (p-1) = b + (b + (p-1))
        have hbp_lt : (b + (p - 1)) % p < p := Nat.mod_lt _ hp_pos
        exact cancel_mod b c ((b + (p - 1)) % p) hc_lt hbp_lt (by
          rw [hbc, Nat.add_mod b ((b + (p - 1)) % p) p, Nat.mod_mod, ← Nat.add_mod]
          congr 1; omega)
      constructor
      · -- Part 1: backward chain avoids b (by disjointness)
        intro s hs habs
        -- backward pos s = forward pos (t_fwd + s) by hbwd_as_fwd
        -- forward pos s₀ = b = backward pos s = forward pos (t_fwd + s)
        -- By injectivity, s₀ = t_fwd + s, contradicting s₀ < t_fwd
        have h1 := (hbwd_as_fwd s).symm.trans habs
        have h2 := hinj s₀ (t_fwd + s) (by omega) (by omega) (hs₀_eq.trans h1.symm)
        omega
      · -- Part 2: backward chain avoids b-1 (by disjointness + reflection)
        intro s hs habs
        -- (m + Δ + s*k₀ + 1) % p = b → (m + Δ + s*k₀) % p = (b+p-1) % p
        have hpred' := hab_pred (m + Δ + s * k₀) habs
        -- backward pos s has residue (b+p-1) % p = forward pos (t_fwd-1-s₀)
        have h1 := (hbwd_as_fwd s).symm.trans hpred'
        have h2 := hinj (t_fwd - 1 - s₀) (t_fwd + s) (by omega) (by omega)
          (hrefl_step.trans h1.symm)
        omega
    -- Case split: does any forward chain step hit b?
    by_cases hfwd_hits : ∃ s, s < t_fwd ∧ (m + s * k₀) % p = b
    · -- Forward chain hits b → use backward chain (which is break-free)
      obtain ⟨hbwd_c1, hbwd_c2⟩ := hbwd_clean_of_fwd_hits hfwd_hits
      have hbwd_chain := hchain (m + Δ) t_bwd hbwd_c1 hbwd_c2
      have hbwd_period := binary_letter_eq_of_period_cong B hmos p hpLen (by omega)
        (m + Δ + t_bwd * k₀) m hbwd_target
      have := (hbwd_chain.trans hbwd_period).symm
      rw [hΔ_eq] at this
      have hrw : (r' + p - 1 - j : ℕ) = (r' + (p - 1 - j) : ℕ) := by omega
      rw [hrw]; exact this
    · -- Forward chain avoids b → also avoids b-1 (by reflection)
      push_neg at hfwd_hits
      have hfwd_c1 := hfwd_hits
      have hfwd_c2 := hfwd_clean_2_of_1 hfwd_c1
      have hfwd_chain := hchain m t_fwd hfwd_c1 hfwd_c2
      have hfwd_period := binary_letter_eq_of_period_cong B hmos p hpLen (by omega)
        (m + t_fwd * k₀) (m + Δ) hfwd_target
      have := hfwd_chain.trans hfwd_period
      rw [hΔ_eq] at this
      have hrw : (r' + p - 1 - j : ℕ) = (r' + (p - 1 - j) : ℕ) := by omega
      rw [hrw]; exact this

/-- **Binary 2-step palindrome (odd period)**: For a binary MOS with odd period `p`,
    the binary 2-step count vectors satisfy a palindromic symmetry:
    `∃ r, ∀ i, V_binary(r + i) = V_binary(r + p - 2 - i)` for `0 ≤ i < p - 1`.

    Derives from the letter palindrome: if `B(r+j) = B(r+p-1-j)` for all `j`,
    then `V(r+i, 2) = V(r+p-2-i, 2)` since the 2-step window letters match. -/
private lemma binary_2step_palindrome_odd_period (B : BinaryNecklace n)
    (hmos : BinaryNecklace.isMOS B)
    (p : ℕ) (hpLen : (Necklace.period B).length = p)
    (hp_odd : p % 2 = 1) (hp_pos : p > 0) :
    ∃ r : ℕ, ∀ i : ℕ, i + 1 < p →
      Necklace.kStepVector B (r + i) 2 =
      Necklace.kStepVector B (r + p - 2 - i) 2 := by
  rcases Nat.lt_or_ge p 3 with hp_small | hp_ge3
  · -- p = 1: vacuously true (no i with i + 1 < 1)
    exact ⟨0, fun i hi => by omega⟩
  · -- p ≥ 3: use letter palindrome
    obtain ⟨r, hpal⟩ := mos_letter_palindrome B hmos p hpLen hp_odd hp_ge3
    exact ⟨r, fun i hi => by
      apply kStepVector_two_eq_of_letter_swap
      · -- B(r+i) = B((r+p-2-i)+1) = B(r+p-1-i), from palindrome at j=i
        have := hpal i (by omega)
        convert this using 2; congr 1; omega
      · -- B((r+i)+1) = B(r+p-2-i), from palindrome at j=i+1
        have := hpal (i + 1) (by omega)
        convert this using 2; congr 1; omega⟩

/-- **Ternary contrainterleaving from palindrome**: For a ternary word `w` whose
    binary projection is a MOS with odd period `p`, and whose non-`s` letters
    alternate `L/m`, the word is a 2-contrainterleaving: strand 1 is the reversal
    (up to rotation) of strand 0.

    **Proof strategy**: Combines the binary palindrome with the L↔m twist.
    Since `p` is odd, `V(2j+1) = V(2(j-(p-1)/2) + p) = twist(V(2(j-(p-1)/2)))`.
    The binary palindrome gives `V_binary(r+i) = V_binary(r+p-2-i)`.
    The rank parity at palindrome-paired positions differs by 1 (since the
    Christoffel palindrome has the property that ranks at mirrored positions
    sum to a constant). Combined with the twist, this gives:
    `V_ternary(2j+1) = V_ternary(((p-1-j+d) % p) * 2)` for some `d`. -/
private lemma ternary_contrainterleaving_odd_period
    (w : TernaryNecklace n)
    (a c : ℕ) (ha_pos : a > 0) (hc_pos : c > 0) (ha_odd : a % 2 = 1)
    (hcop : Nat.Coprime a c) (hn_eq : n = 2 * a + 2 * c)
    (hcountL : Necklace.count w .L = a) (hcountm : Necklace.count w .m = a)
    (hcounts : Necklace.count w .s = 2 * c)
    (hmos : isPartialPairwiseMOS w .L .m)
    (hdel : isPartialDeletionMOS w .s)
    (hp_odd : (a + c) % 2 = 1) :
    Necklace.isContrainterleaving w := by
  sorry

/-- In a doubly-even even-regular scale, strand 1 of the 2-step vectors
    is a rotation of strand 0.

    **Proof strategy** (from `interleaving.txt`): The binary MOS generator `k`
    is odd (since `gcd(k, p) = 1` and `p` is even). In the MOS period, the
    mode-shift by `k` swaps two consecutive positions. Since `k` is odd, these
    have different parities and lie in the same 2-step window, so the binary
    2-step stacking is preserved. For the ternary L/m split: positions with
    binary 2-step `(2, 0)` or `(0, 2)` always give `(1,1,0)` or `(0,0,2)`,
    and at "mixed" positions `(1, 1)`, the L/m split follows an alternating
    pattern determined by the MOS substitution structure with period-2 filling. -/
private lemma doubly_even_strand1_rotation
    (w : TernaryNecklace n)
    (a c : ℕ) (ha_pos : a > 0) (hc_pos : c > 0) (ha_odd : a % 2 = 1)
    (hcop : Nat.Coprime a c) (hn_eq : n = 2 * a + 2 * c)
    (hcountL : Necklace.count w .L = a) (hcountm : Necklace.count w .m = a)
    (hcounts : Necklace.count w .s = 2 * c)
    (hmos : isPartialPairwiseMOS w .L .m)
    (hdel : isPartialDeletionMOS w .s)
    (hmod : n % 4 = 0) (hgt : n > 4) :
    let p := n / 2
    ∃ d : ℕ, ∀ j : Fin p,
      Necklace.kStepVector w (j.val * 2 + 1) 2 =
      Necklace.kStepVector w (((j.val + d) % p) * 2) 2 :=
  ternary_2step_rotation_even_period w a c ha_pos hc_pos ha_odd hcop hn_eq
    hcountL hcountm hcounts hmos hdel (by omega) (by omega)

/-- In a doubly-even even-regular scale, strand 0 of the 2-step vectors
    (after an appropriate letter map) is itself an even-regular scale.

    **Proof strategy** (from `interleaving.txt`): The 2-step vectors take
    values in `{(1,1,0), (1,0,1), (0,1,1), (0,0,2)}`. The map
    `(1,1,0)/(0,0,2) → s`, `(1,0,1) → L`, `(0,1,1) → m` produces a
    necklace of length `n/2` with step signature `(a', a', 2c')`, `a'` odd,
    `gcd(a', c') = 1`. This inherits the MOS substitution structure from the
    binary MOS: `(1,1,0)/(0,0,2)` are non-slot letters and `(1,0,1)/(0,1,1)`
    are slot letters filled by a period-2 filling MOS. -/
private lemma doubly_even_strand0_evenRegular [NeZero (n / 2)]
    (w : TernaryNecklace n)
    (h : isEvenRegular w) (hmod : n % 4 = 0) (hgt : n > 4) :
    ∃ (φ : ZVector StepSize → StepSize),
      isEvenRegular (φ ∘ Necklace.strand2 w ⟨0, by omega⟩) := by
  sorry

/-- Doubly-even (`n ≡ 0 mod 4`) even-regular scales with `n > 4` are
    2-interleavings of a smaller even-regular scale.

    **Proof outline**: The binary MOS generator `k` is odd (since `gcd(k, p) = 1`
    and `p` is even). Shifting by `k` maps even positions to odd positions.
    The mode-shift swaps two adjacent letters within the same 2-step window
    (since `k` is odd), so 2-step vectors are preserved. Hence strand 1 =
    rotation of strand 0. Each strand is an even-regular scale of length `n/2`. -/
theorem evenRegular_doubly_even_isInterleaving [NeZero (n / 2)]
    (w : TernaryNecklace n)
    (h : isEvenRegular w) (hmod : n % 4 = 0) (hgt : n > 4) :
    Necklace.isInterleaving w 2 ∧
    ∃ (φ : ZVector StepSize → StepSize),
      isEvenRegular (φ ∘ Necklace.strand2 w ⟨0, by omega⟩) := by
  obtain ⟨hprim, heven, σ, a, c, ha_pos, hc_pos, ha_odd, hcop, hn_eq,
    hcountL, hcountm, hcounts, hmos, hdel⟩ := h
  constructor
  · -- Part 1: isInterleaving w 2
    apply isInterleaving_of_applyPerm σ w 2
    refine ⟨by omega, ⟨a + c, by omega⟩, fun s => ?_⟩
    fin_cases s
    · -- s = 0: strand 0 is trivially a self-rotation
      exact ⟨0, fun j => by simp [Nat.mod_eq_of_lt j.isLt]⟩
    · -- s = 1: strand 1 = rotation of strand 0
      exact doubly_even_strand1_rotation _ a c ha_pos hc_pos ha_odd hcop hn_eq
        hcountL hcountm hcounts hmos hdel hmod hgt
  · -- Part 2: ∃ φ, isEvenRegular (φ ∘ strand2 w ⟨0, _⟩)
    exact doubly_even_strand0_evenRegular w
      ⟨hprim, heven, σ, a, c, ha_pos, hc_pos, ha_odd, hcop, hn_eq,
       hcountL, hcountm, hcounts, hmos, hdel⟩ hmod hgt

/-- In a singly-even even-regular scale, the 2-step vectors satisfy the
    contrainterleaving condition: strand 1 is the reversal (up to rotation)
    of strand 0.

    **Proof strategy**: Since `p = n/2` is odd, `V(2j + p)` is in strand 1.
    By `kStepVector_two_twist`, `V(2j + p)` swaps L↔m of `V(2j)`.
    The MOS palindrome structure gives the reversal, yielding contrainterleaving. -/
private lemma singly_even_contrainterleaving
    (w : TernaryNecklace n)
    (a c : ℕ) (ha_pos : a > 0) (hc_pos : c > 0) (ha_odd : a % 2 = 1)
    (hcop : Nat.Coprime a c) (hn_eq : n = 2 * a + 2 * c)
    (hcountL : Necklace.count w .L = a) (hcountm : Necklace.count w .m = a)
    (hcounts : Necklace.count w .s = 2 * c)
    (hmos : isPartialPairwiseMOS w .L .m)
    (hdel : isPartialDeletionMOS w .s)
    (hmod : n % 4 = 2) :
    Necklace.isContrainterleaving w :=
  ternary_contrainterleaving_odd_period w a c ha_pos hc_pos ha_odd hcop hn_eq
    hcountL hcountm hcounts hmos hdel (by omega)

/-- In a singly-even even-regular scale, strand 0 of the 2-step vectors
    (after an appropriate letter map) is an odd-regular scale.

    **Proof strategy** (from `interleaving.txt`): The 2-step stacking gives
    an MOS substitution scale with period-2 filling. In the singly-even case,
    there are oddly many non-slot letters in each strand, and the two strands
    have "opposite" fillings (swapping `x+y` and `x+z`), giving opposite
    chiralities of an odd-regular scale. -/
private lemma singly_even_strand0_oddRegular [NeZero (n / 2)]
    (w : TernaryNecklace n)
    (h : isEvenRegular w) (hmod : n % 4 = 2) :
    ∃ (φ : ZVector StepSize → StepSize),
      isOddRegular (φ ∘ Necklace.strand2 w ⟨0, by omega⟩) := by
  sorry

/-- Singly-even (`n ≡ 2 mod 4`) even-regular scales are 2-contrainterleavings:
    strand 1 of 2-step multisets is the reversal of strand 0, and each strand
    (after mapping) is an odd-regular scale.

    **Proof outline**: Since `p = n/2` is odd, position `2j + p` is odd for
    even `2j`. By `kStepVector_two_twist`, `V(2j + p)` swaps L↔m of `V(2j)`.
    So strand 1 at index `j + (p-1)/2` = twist of strand 0 at index `j`.
    The palindrome structure of the binary MOS gives the reversal, yielding
    contrainterleaving. Each strand is an odd-regular scale of length `n/2`. -/
theorem evenRegular_singly_even_isContrainterleaving [NeZero (n / 2)]
    (w : TernaryNecklace n)
    (h : isEvenRegular w) (hmod : n % 4 = 2) :
    Necklace.isContrainterleaving w ∧
    ∃ (φ : ZVector StepSize → StepSize),
      isOddRegular (φ ∘ Necklace.strand2 w ⟨0, by omega⟩) := by
  obtain ⟨_hprim, _heven, σ, a, c, ha_pos, hc_pos, ha_odd, hcop, hn_eq,
    hcountL, hcountm, hcounts, hmos, hdel⟩ := h
  constructor
  · apply isContrainterleaving_of_applyPerm σ w
    exact singly_even_contrainterleaving _ a c ha_pos hc_pos ha_odd hcop hn_eq
      hcountL hcountm hcounts hmos hdel hmod
  · exact singly_even_strand0_oddRegular w
      ⟨_hprim, _heven, σ, a, c, ha_pos, hc_pos, ha_odd, hcop, hn_eq,
       hcountL, hcountm, hcounts, hmos, hdel⟩ hmod

end TernaryNecklace
