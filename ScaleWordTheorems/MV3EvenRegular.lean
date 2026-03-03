import ScaleWordTheorems.MV3OddRegular

open BigOperators

namespace TernaryNecklace

variable {n : ℕ} [NeZero n]

/-! ## Even-Regular Stacking Theorems -/

/-- A binary MOS with signature (2a, 2c) where gcd(a,c) = 1 has period length a + c = n/2.
    Since gcd(2a, 2c) = 2 > 1, the necklace is a 2-fold repetition. The period length
    can't be n (that would mean gcd(2a,2c) = 1), so it must be n/2. -/
private lemma binary_mos_period_half (a c : ℕ) (ha_pos : a > 0) (_hc_pos : c > 0)
    (hcop : Nat.Coprime a c) (hn : n = 2 * a + 2 * c)
    (B : BinaryNecklace n) (hB_mos : BinaryNecklace.isMOS B)
    (hB_countL : Necklace.count B .L = 2 * a) (hB_counts : Necklace.count B .s = 2 * c) :
    (Necklace.period B).length = a + c := by
  set pLen := (Necklace.period B).length with hpLen_def
  have hn_pos : 0 < n := by omega
  have hgcd_eq : Nat.gcd (2 * a) (2 * c) = 2 := by rw [Nat.gcd_mul_left]; simp [hcop]
  -- Step 1: B is a 2-fold repetition (gcd(2a, 2c) = 2 > 1)
  have hsig : BinaryNecklace.hasStepSignature B (2 * a) (2 * c) := by
    simp only [BinaryNecklace.hasStepSignature, BinaryNecklace.stepSignature, hB_countL, hB_counts]
  obtain ⟨hdvd_n, _, hper⟩ := mos_repetition_of_gcd_bjorklund B hB_mos (2 * a) (2 * c) hsig
    (Nat.gcd (2 * a) (2 * c)) rfl (by omega)
  -- Step 2: pLen ≤ n/2 (from translational period n/2)
  have hpLen_le : pLen ≤ n / 2 := by
    rw [← show n / Nat.gcd (2 * a) (2 * c) = n / 2 from by rw [hgcd_eq]]
    exact Necklace.period_length_le_of_translational_period B _
      (Nat.div_pos (Nat.le_of_dvd hn_pos hdvd_n) (by omega))
      (Nat.div_lt_self hn_pos (by omega)) (Nat.div_dvd_of_dvd hdvd_n) hper
  -- Step 3: (n/pLen) | gcd(2a, 2c) = 2 (via prefix_mod_period + counts)
  have hpLen_dvd : pLen ∣ n := period_dvd_length B
  -- count(B, a) = (n/pLen) * periodVec(a)
  have hcount_eq : ∀ (x : BinaryStep), (↑(Necklace.count B x) : ℤ) =
      ↑(n / pLen) * (ZVector.ofList (Necklace.period B)) x := by
    intro x
    have h1 := prefix_mod_period B n x
    rw [Nat.mod_eq_zero_of_dvd hpLen_dvd] at h1
    have h0 : (Necklace.kStepVector B 0 0 x : ℤ) = 0 := by
      simp [Necklace.kStepVector, ZVector.ofList, Necklace.slice]
    simp only [h0, zero_add] at h1
    rw [← h1, kStepVector_zero_n_eq_count]
  -- (n/pLen) | count(B, x) for each x
  have hq_dvd : ∀ x : BinaryStep, (n / pLen) ∣ (Necklace.count B x) := by
    intro x
    have hpv_nn : (ZVector.ofList (Necklace.period B)) x ≥ 0 := by
      unfold ZVector.ofList; exact_mod_cast Nat.zero_le _
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hpv_nn
    have h := hcount_eq x; rw [hm] at h
    exact ⟨m, by exact_mod_cast h⟩
  -- (n/pLen) | gcd(2a, 2c) = 2
  have hq_le2 : n / pLen ≤ 2 := by
    have h1 : (n / pLen) ∣ (2 * a) := hB_countL ▸ hq_dvd .L
    have h2 : (n / pLen) ∣ (2 * c) := hB_counts ▸ hq_dvd .s
    exact Nat.le_of_dvd (by omega) (hgcd_eq ▸ Nat.dvd_gcd h1 h2)
  -- Step 4: pLen ≤ n/2 and n/pLen ≤ 2 and pLen | n → pLen = n/2 = a+c
  have hpLen_pos : 0 < pLen := period_length_pos B
  have hq_pos : 0 < n / pLen := Nat.div_pos (Nat.le_of_dvd hn_pos hpLen_dvd) hpLen_pos
  have hn_eq : n = n / pLen * pLen := (Nat.div_mul_cancel hpLen_dvd).symm
  -- Case split: n/pLen = 1 (impossible) or n/pLen = 2
  interval_cases (n / pLen)
  · -- n/pLen = 1: n = pLen, but pLen ≤ n/2, contradiction
    omega
  · -- n/pLen = 2: n = 2 * pLen, so pLen = n/2 = a + c
    omega

/-- The period vector of a binary MOS with signature (2a, 2c) and period a+c has
    L-component = a and s-component = c. -/
private lemma period_vector_of_half_period (a c : ℕ) (ha_pos : a > 0) (_hc_pos : c > 0)
    (_hcop : Nat.Coprime a c) (hn : n = 2 * a + 2 * c)
    (B : BinaryNecklace n) (_hB_mos : BinaryNecklace.isMOS B)
    (hB_countL : Necklace.count B .L = 2 * a) (hB_counts : Necklace.count B .s = 2 * c)
    (hpLen : (Necklace.period B).length = a + c) :
    (ZVector.ofList (Necklace.period B)) .L = ↑a ∧
    (ZVector.ofList (Necklace.period B)) .s = ↑c := by
  -- From prefix_mod_period with m=n: count(B, x) = (n/pLen) * pVec(x)
  -- With n/pLen = 2: pVec(x) = count(B, x) / 2
  set pLen := (Necklace.period B).length with hpLen_def
  have hpLen_dvd : pLen ∣ n := period_dvd_length B
  have hn_2pLen : n = 2 * pLen := by omega
  have hn_div : n / pLen = 2 := by
    rw [hn_2pLen, Nat.mul_div_cancel _ (by omega : 0 < pLen)]
  have hcount_eq : ∀ x : BinaryStep,
      (↑(Necklace.count B x) : ℤ) = 2 * (ZVector.ofList (Necklace.period B)) x := by
    intro x
    have h1 := prefix_mod_period B n x
    rw [Nat.mod_eq_zero_of_dvd hpLen_dvd] at h1
    have h0 : (Necklace.kStepVector B 0 0 x : ℤ) = 0 := by
      simp [Necklace.kStepVector, ZVector.ofList, Necklace.slice]
    simp only [h0, zero_add] at h1
    rw [← kStepVector_zero_n_eq_count B x, h1, hn_div]; norm_cast
  constructor
  · have := hcount_eq .L; rw [hB_countL] at this; push_cast at this; linarith
  · have := hcount_eq .s; rw [hB_counts] at this; push_cast at this; linarith

set_option maxHeartbeats 4800000
/-- From even-regular data: extract generator step `k` (coprime to `n/2`),
    starting position `r`, and generator vector `g` with even non-s count.
    In each period (chain), `p - 1` positions have ternary vector `g`, and
    the closing position differs.

    **Proof outline** (from even-regular.txt):
    The map `p` (conflating L with m) yields MOS `M` with signature `2aX 2cZ`.
    Since `gcd(a, c) = 1`, `M` has period length `a + c = n/2`, giving two
    generator chains. The perfect k-step of `M` is `iW + jZ` with `0 < i < a`.
    Since `a` is odd, after possibly taking the period-complement, `i` is even,
    so each preimage in the ternary necklace satisfies `|w|_L = |w|_m = i/2`
    and `|w|_s = j` — a unique lift. The imperfect generator has odd non-s
    count, giving a different ternary vector at the closing position. -/
private lemma evenRegular_kstep_data (w : TernaryNecklace n)
    (_heven : n % 2 = 0) (a c : ℕ)
    (_ha_pos : a > 0) (_hc_pos : c > 0) (_ha_odd : a % 2 = 1)
    (_hcop : Nat.Coprime a c) (_hn : n = 2 * a + 2 * c)
    (_hcountL : Necklace.count w .L = a) (_hcountm : Necklace.count w .m = a)
    (_hcounts : Necklace.count w .s = 2 * c)
    (_hmos : isPartialPairwiseMOS w .L .m)
    (_hdel : isPartialDeletionMOS w .s) :
    let p := n / 2
    ∃ (k : ℕ) (g : ZVector StepSize) (r : ℕ),
      0 < k ∧ k < p ∧ Nat.Coprime k p ∧
      (∀ i : Fin (p - 1),
        Necklace.kStepVector w (r + i.val * k) k = g) ∧
      (∀ i : Fin (p - 1),
        Necklace.kStepVector w (r + p + i.val * k) k = g) ∧
      Necklace.kStepVector w (r + (p - 1) * k) k ≠ g ∧
      Necklace.kStepVector w (r + p + (p - 1) * k) k ≠ g ∧
      IsGenerator (identifyPair w .L .m)
        (ZVector.identifyPair g .L .m) := by
  -- ===== Phase 1: Binary MOS bridge =====
  set p := n / 2 with hp_def
  have hp_eq : p = a + c := by omega
  have hn_pos : 0 < n := by omega
  have hp_pos : 0 < p := by omega
  have hp_ge2 : p ≥ 2 := by omega
  set B := identifiedToBinary (TernaryNecklace.identifyPair w .L .m) with hB_def
  have hB_mos : BinaryNecklace.isMOS B :=
    identifiedToBinary_isMOS w _hcountL _hcountm _hcounts _ha_pos (by omega) _hmos
  have hB_countL : Necklace.count B .L = 2 * a :=
    identifiedToBinary_count_L w _hcountL _hcountm
  have hB_counts : Necklace.count B .s = 2 * c :=
    identifiedToBinary_count_s w _hcounts
  -- ===== Phase 2: Period = p = a + c =====
  have hpLen : (Necklace.period B).length = p := by
    have := binary_mos_period_half a c _ha_pos _hc_pos _hcop _hn B hB_mos hB_countL hB_counts
    omega
  have ⟨hpvL, hpvs⟩ := period_vector_of_half_period a c _ha_pos _hc_pos _hcop _hn B hB_mos
    hB_countL hB_counts (hpLen.trans hp_eq)
  -- ===== Phase 3: Generator extraction =====
  obtain ⟨g_bin, hgen⟩ := allMOSScalesHaveGenerator n B hB_mos
  obtain ⟨k, hk_pos, hk_lt_p, hcount_g⟩ :=
    generator_implies_p_minus_one_occurrences B hB_mos.1 g_bin hgen
  rw [hpLen] at hk_lt_p hcount_g
  have hcop_k : Nat.Coprime k p := by
    rw [← hpLen]
    exact p_minus_one_occurrences_implies_coprime_to_period B hB_mos.1 k hk_pos
      (hpLen ▸ hk_lt_p) g_bin (hpLen ▸ hcount_g)
  -- g_bin components are non-negative
  have hgL_nn : g_bin .L ≥ 0 := by
    have ⟨_, _, _, hg_app⟩ := hgen.1; rw [← hg_app]
    unfold Necklace.kStepVector ZVector.ofList; exact_mod_cast Nat.zero_le _
  have hgs_nn : g_bin .s ≥ 0 := by
    have ⟨_, _, _, hg_app⟩ := hgen.1; rw [← hg_app]
    unfold Necklace.kStepVector ZVector.ofList; exact_mod_cast Nat.zero_le _
  -- g_bin(.L) + g_bin(.s) = k
  -- Unfold countKStepVectorPerPeriod and replace period length with p
  have hcount_g' : (List.range p).countP
      (fun i => decide (Necklace.kStepVector B i k = g_bin)) = p - 1 := by
    have : (Necklace.period B).length = p := hpLen
    simp only [countKStepVectorPerPeriod, this] at hcount_g; exact hcount_g
  have hg_sum : g_bin .L + g_bin .s = ↑k := by
    have : ∃ i₀, i₀ < p ∧ Necklace.kStepVector B i₀ k = g_bin := by
      by_contra hall; push_neg at hall
      have : (List.range p).countP (fun i => decide (Necklace.kStepVector B i k = g_bin)) = 0 :=
        List.countP_eq_zero.mpr (fun i hi => by simp [hall i (List.mem_range.mp hi)])
      rw [this] at hcount_g'; omega
    obtain ⟨i₀, _, hi₀_eq⟩ := this
    rw [← hi₀_eq]; exact_mod_cast kStepVector_total_count B i₀ k
  -- ===== Phase 4: Bézout identity (from sum formula, not requiring primitivity) =====
  -- Sum formula: ∑_{i<p} kStepVector(B, i, k, .L) = k * pVec(.L) = k * a
  have hsum := kStepVector_lettercount_sum_over_period B k hk_pos (hpLen ▸ hk_lt_p) .L
  rw [hpLen, hpvL] at hsum
  -- Find bad position (unique position where kStepVector ≠ g_bin)
  have hbad : ∃ i₀ : ℕ, i₀ < p ∧ Necklace.kStepVector B i₀ k ≠ g_bin ∧
      (∀ j : ℕ, j < p → j ≠ i₀ → Necklace.kStepVector B j k = g_bin) := by
    have hexists_bad : ∃ i₀, i₀ < p ∧ Necklace.kStepVector B i₀ k ≠ g_bin := by
      by_contra hall; push_neg at hall
      have h := List.countP_eq_length.mpr (fun i hi =>
        decide_eq_true_eq.mpr (hall i (List.mem_range.mp hi)))
      rw [List.length_range] at h; rw [h] at hcount_g'; omega
    obtain ⟨i₀, hi₀_lt, hi₀_bad⟩ := hexists_bad
    refine ⟨i₀, hi₀_lt, hi₀_bad, fun j hj hne => ?_⟩
    by_contra hj_bad
    set pred := fun i => decide (Necklace.kStepVector B i k = g_bin)
    have hp_i₀ : pred i₀ = false := by simp [pred, hi₀_bad]
    have hp_j : pred j = false := by simp [pred, hj_bad]
    have hi₀_mem : i₀ ∈ List.range p := List.mem_range.mpr hi₀_lt
    have hj_mem : j ∈ List.range p := List.mem_range.mpr hj
    have h1 : ((List.range p).erase j).countP pred = (List.range p).countP pred := by
      rw [List.countP_erase]; simp [hj_mem, hp_j]
    have h2 : ((List.range p).erase j).length = p - 1 := by
      rw [List.length_erase_of_mem hj_mem, List.length_range]
    have hi₀_mem' : i₀ ∈ (List.range p).erase j :=
      List.mem_erase_of_ne (Ne.symm hne) |>.mpr hi₀_mem
    have h4 : (((List.range p).erase j).erase i₀).countP pred =
        ((List.range p).erase j).countP pred := by
      rw [List.countP_erase]; simp [hi₀_mem', hp_i₀]
    have h5 : (((List.range p).erase j).erase i₀).length = p - 2 := by
      rw [List.length_erase_of_mem hi₀_mem', h2]; omega
    have hcg : (List.range p).countP pred = p - 1 := hcount_g'
    have hle := List.countP_le_length (p := pred) (l := ((List.range p).erase j).erase i₀)
    omega
  obtain ⟨i₀, hi₀_lt, hi₀_bad, hi₀_good⟩ := hbad
  -- Split sum: (p-1) * g_bin.L + g'_bin.L = k * a (where g'_bin is the bad vector)
  set g'_bin := Necklace.kStepVector B i₀ k with hg'_def
  have hg'_total : g'_bin .L + g'_bin .s = ↑k := by
    exact_mod_cast kStepVector_total_count B i₀ k
  have hsum_split : (↑p : ℤ) * g_bin .L + (g'_bin .L - g_bin .L) = ↑k * ↑a := by
    rw [list_range_map_sum_eq_finset] at hsum
    have h1 : ∑ i ∈ Finset.range p, (Necklace.kStepVector B i k) .L =
        ∑ i ∈ Finset.range p,
          (g_bin .L + ((Necklace.kStepVector B i k) .L - g_bin .L)) :=
      Finset.sum_congr rfl (fun i _ => by ring)
    rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have hdiff : ∑ i ∈ Finset.range p,
        ((Necklace.kStepVector B i k) .L - g_bin .L) = g'_bin .L - g_bin .L := by
      apply Finset.sum_eq_single i₀
      · intro i hi hi_ne; rw [Finset.mem_range] at hi
        rw [hi₀_good i hi hi_ne]; ring
      · intro habs; exact absurd (Finset.mem_range.mpr hi₀_lt) habs
    linarith
  -- Bézout: p * g_bin.L - k * a = ±(g_bin.L - g'_bin.L)
  -- And |g_bin.L - g'_bin.L| = 1 (scoot argument)
  have hdiff_le : g_bin .L - 1 ≤ g'_bin .L ∧ g'_bin .L ≤ g_bin .L + 1 := by
    rcases Nat.eq_zero_or_pos i₀ with rfl | hi₀_pos
    · have hscoot := kStepVector_scoot_L_count_diff B 0 k
      simp only at hscoot
      rw [hi₀_good 1 (by omega) (by omega)] at hscoot
      constructor <;> linarith [hscoot.1, hscoot.2]
    · have hscoot := kStepVector_scoot_L_count_diff B (i₀ - 1) k
      simp only at hscoot
      rw [Nat.sub_add_cancel hi₀_pos,
          hi₀_good (i₀ - 1) (by omega) (by omega)] at hscoot
      exact hscoot
  have hbezout : (↑p : ℤ) * g_bin .L - ↑k * ↑a = 1 ∨
      (↑p : ℤ) * g_bin .L - ↑k * ↑a = -1 := by
    have hne : g_bin .L ≠ g'_bin .L := by
      intro heq
      have hs_eq : g_bin .s = g'_bin .s := by linarith [hg_sum, hg'_total]
      exact hi₀_bad (funext (fun x => by cases x; exact heq.symm; exact hs_eq.symm))
    rcases Int.lt_or_lt_of_ne (sub_ne_zero.mpr hne) with hneg | hpos
    · right; omega
    · left; omega
  -- ===== Phase 5: Parity and complement =====
  -- If g_bin.L is odd, replace (k, g_bin, i₀) with (p-k, pVec-g_bin, (i₀+k)%p).
  -- The complement has .L = a - g_bin.L (even since both are odd).
  -- Introduce unified variables K, G, I₀ with guaranteed even G.L.
  set pVec := ZVector.ofList (Necklace.period B) with hpVec_def
  -- Period complement relation: kStepVector B (i+k) (p-k) = pVec - kStepVector B i k
  have hcomp : ∀ i (x : BinaryStep),
      Necklace.kStepVector B (i + k) (p - k) x =
      pVec x - Necklace.kStepVector B i k x := by
    intro i x
    have h1 := kStepVector_add B i k (p - k) x
    rw [show k + (p - k) = p from by omega] at h1
    have h2 : Necklace.kStepVector B i p x = pVec x := by
      rw [hB_def, ← hpLen]; exact kStepVector_full_period _ i x
    linarith
  -- Case split on parity of g_bin.L
  suffices heff : ∃ (K : ℕ) (G : ZVector BinaryStep) (I₀ : ℕ),
      0 < K ∧ K < p ∧ Nat.Coprime K p ∧
      G .L ≥ 0 ∧ G .s ≥ 0 ∧ G .L + G .s = ↑K ∧ G .L % 2 = 0 ∧
      I₀ < p ∧ Necklace.kStepVector B I₀ K ≠ G ∧
      (∀ j, j < p → j ≠ I₀ → Necklace.kStepVector B j K = G) ∧
      -- Scoot property: closing vector differs by ≤ 1 from G in each component
      (Necklace.kStepVector B I₀ K) .L + (Necklace.kStepVector B I₀ K) .s = ↑K ∧
      -- The sum formula still holds (for ternary lift)
      (∀ (x : BinaryStep),
        ∑ i ∈ Finset.range p, Necklace.kStepVector B i K x = ↑K * pVec x) ∧
      IsGenerator B G by
    obtain ⟨K, G, I₀, hK_pos, hK_lt, hcop_K, hGL_nn, hGs_nn, hG_sum, hGL_even,
            hI₀_lt, hI₀_bad, hI₀_good, hG'_total, _hsum_eff, hG_gen⟩ := heff
    -- ===== Phase 6: Ternary lift =====
    -- With G.L even, define ternary generator
    set gL_half := G .L / 2 with hgL_half_def
    -- g_tern : StepSize → ℤ with .L = .m = gL_half, .s = G.s
    set g_tern : ZVector StepSize := fun x =>
      match x with | .L => gL_half | .m => gL_half | .s => G .s with hg_tern_def
    -- Bridge: B's k-step .s = w's k-step .s
    have hbridge_s : ∀ i, Necklace.kStepVector B i K .s = Necklace.kStepVector w i K .s := by
      intro i; exact identifiedToBinary_kStepVector_s w i K
    -- Bridge: B's k-step .L = w's k-step .L + .m (from total count + .s bridge)
    have hbridge_L : ∀ i, (Necklace.kStepVector B i K .L : ℤ) =
        Necklace.kStepVector w i K .L + Necklace.kStepVector w i K .m := by
      intro i
      have hB_total : (Necklace.kStepVector B i K .L : ℤ) + Necklace.kStepVector B i K .s = ↑K :=
        by exact_mod_cast kStepVector_total_count B i K
      have hw_total : (Necklace.kStepVector w i K .L : ℤ) + Necklace.kStepVector w i K .m +
          Necklace.kStepVector w i K .s = ↑K :=
        by exact_mod_cast kStepVector_total_count_ternary w i K
      linarith [hbridge_s i]
    -- Ternary lift: if kStepVector B j K = G, then kStepVector w j K = g_tern
    -- Key: .s matches (bridge), .L + .m = G.L (even), and deletion MOS ⟹ .L = .m = G.L/2
    have hlift : ∀ j, Necklace.kStepVector B j K = G →
        Necklace.kStepVector w j K = g_tern := by
      intro j hj_eq
      have hs_eq : Necklace.kStepVector w j K .s = G .s := by
        rw [← hbridge_s, congr_fun hj_eq .s]
      have htotal : (Necklace.kStepVector w j K .L : ℤ) + Necklace.kStepVector w j K .m +
          Necklace.kStepVector w j K .s = ↑K := by
        exact_mod_cast kStepVector_total_count_ternary w j K
      have hLm_sum : Necklace.kStepVector w j K .L + Necklace.kStepVector w j K .m = G .L := by
        linarith [hG_sum, hs_eq]
      -- Prove kStepVector .L = G.L / 2 using alternating deletion word
      have hL_val : Necklace.kStepVector w j K .L = G .L / 2 := by
        -- Set up deletion word D
        set D := TernaryNecklace.orderedDeletion w .s with hD_def
        have hDlen : D.length = 2 * a := by
          have hdel : D.length + Necklace.count w .s = n := orderedDeletion_length w .s
          rw [_hcounts] at hdel; omega
        have hDlen_pos : 0 < D.length := by omega
        have hbin : ∀ i, (hi : i < D.length) → D[i] = .L ∨ D[i] = .m := by
          intro i hi
          have hne : D[i] ≠ .s := fun h => by
            have := List.getElem_mem hi
            simp only [D, TernaryNecklace.orderedDeletion, List.mem_filter,
              decide_eq_true_eq] at this
            exact this.2 h
          cases h : D[i] with | L => left; rfl | m => right; rfl | s => exact absurd h hne
        have hDcountL : D.count .L = a := by
          rw [hD_def, orderedDeletion_count_ne w .s .L (by decide)]; exact _hcountL
        have hDcountm : D.count .m = a := by
          rw [hD_def, orderedDeletion_count_ne w .s .m (by decide)]; exact _hcountm
        -- D is alternating
        obtain ⟨halt, hne_D⟩ := balanced_circular_mos_is_alternating D a _ha_pos hDlen
          hbin hDcountL hDcountm _hdel
        -- G.L as a nat: nonS = G.L.natAbs
        set nonS := (G .L).natAbs with hnonS_def
        have hnonS_cast : (↑nonS : ℤ) = G .L :=
          Int.natAbs_of_nonneg hGL_nn
        have hnonS_le_K : nonS ≤ K := by
          have : (↑nonS : ℤ) ≤ ↑K := by rw [hnonS_cast]; linarith [hGs_nn, hG_sum]
          exact_mod_cast this
        -- kStepVector .s = ↑(K - nonS)
        have hs_as_nat : Necklace.kStepVector w j K .s = ↑(K - nonS) := by
          have : G .s = ↑(K - nonS) := by
            have : (↑(K - nonS) : ℤ) = ↑K - ↑nonS := by omega
            rw [this, hnonS_cast]; linarith [hG_sum]
          rw [hs_eq, this]
        -- Filter length = nonS (via nonS_filter_length)
        have hfilt_len : ((Necklace.slice w j (j + K)).filter (· ≠ .s)).length = nonS :=
          nonS_filter_length w j K nonS hs_as_nat hnonS_le_K
        -- nonS is even (since G.L is even and non-negative)
        have hnonS_even : nonS % 2 = 0 := by
          have : (↑nonS : ℤ) % 2 = 0 := by rw [hnonS_cast]; exact hGL_even
          exact_mod_cast this
        obtain ⟨halfL, hhalfL⟩ : ∃ m, nonS = 2 * m := ⟨nonS / 2, by omega⟩
        -- orderedDeletion_window_Lcount: D-window L-count = (kStepVector .L).natAbs
        set q := (((List.range n).map (fun i => w (↑i : ZMod n))).take
            (j % n)).filter (· ≠ .s) |>.length
        have hK_le_n : K ≤ n := by omega
        have hbridge := orderedDeletion_window_Lcount w j K nonS hDlen_pos hK_le_n hfilt_len.symm
        -- alternating_even_window_Lcount: D-window L-count = halfL
        have hD_window := alternating_even_window_Lcount D a halfL _ha_pos hDlen
          halt hne_D hbin q hDlen_pos
        rw [hhalfL] at hbridge
        -- (kStepVector .L).natAbs = halfL
        have hL_nn : Necklace.kStepVector w j K .L ≥ 0 := by
          unfold Necklace.kStepVector ZVector.ofList; exact_mod_cast Nat.zero_le _
        have hL_eq : Necklace.kStepVector w j K .L = ↑halfL := by
          have : (Necklace.kStepVector w j K .L).natAbs = halfL :=
            hbridge.symm.trans hD_window
          rw [← this, Int.natAbs_of_nonneg hL_nn]
        have hGL_half : G .L / 2 = ↑halfL := by
          rw [← hnonS_cast, hhalfL]; push_cast; omega
        rw [hL_eq, hGL_half]
      funext x; cases x
      case s => simp only [g_tern]; exact hs_eq
      case L => simp only [g_tern, hgL_half_def]; exact hL_val
      case m =>
        simp only [g_tern, hgL_half_def]
        have hGL_div2 : G .L / 2 + G .L / 2 = G .L := by omega
        linarith [hLm_sum, hL_val]
    -- Binary bad ternary: if kStepVector B j K ≠ G, then kStepVector w j K ≠ g_tern
    have hbad_lift : ∀ j, Necklace.kStepVector B j K ≠ G →
        Necklace.kStepVector w j K ≠ g_tern := by
      intro j hj_ne heq
      apply hj_ne; funext x; cases x
      case s =>
        have := congr_fun heq .s; simp only [g_tern] at this
        rw [hbridge_s]; exact this
      case L =>
        -- From heq: .L = .m = gL_half, so binary .L = 2 * gL_half = G.L
        have hL := congr_fun heq .L; simp only [g_tern, hgL_half_def] at hL
        have hm := congr_fun heq .m; simp only [g_tern, hgL_half_def] at hm
        -- Binary .L = ternary .L + ternary .m = 2 * (G.L / 2) = G.L
        have h := hbridge_L j; rw [hL, hm] at h
        have hGL_half : G .L / 2 + G .L / 2 = G .L := by
          have := Int.emod_add_mul_ediv (G .L) 2
          rw [hGL_even] at this; linarith
        linarith
    -- ===== Phase 7: Two chains + closing =====
    -- Binary periodicity: kStepVector B (i+p) K = kStepVector B i K
    have hperiodic_B : ∀ i, Necklace.kStepVector B (i + p) K = Necklace.kStepVector B i K := by
      intro i; rw [← hpLen]; exact kStepVector_add_period B i K
    -- Binary mod-period: kStepVector B (j%p) K = kStepVector B j K
    have hmod_B : ∀ j, Necklace.kStepVector B (j % p) K = Necklace.kStepVector B j K := by
      intro j; rw [← hpLen]; exact kStepVector_mod_period' B j K
    -- Key: for any j, if j%p ≠ I₀ then kStepVector B j K = G
    have hgood_any : ∀ j, j % p ≠ I₀ → Necklace.kStepVector B j K = G := by
      intro j hne
      rw [← hmod_B]; exact hI₀_good _ (Nat.mod_lt _ hp_pos) hne
    -- Set r = (I₀ + K) % p so that I₀ = (r + (p-1)*K) % p
    set r := (I₀ + K) % p with hr_def
    -- Good position mod-p argument
    haveI : NeZero p := ⟨by omega⟩
    have hmod_ne_good : ∀ i, i < p - 1 → (r + i * K) % p ≠ I₀ := by
      intro i hi heq
      suffices h_dvd : p ∣ (i + 1) from absurd (Nat.le_of_dvd (by omega) h_dvd) (by omega)
      suffices h_mod : (i + 1) % p = 0 from Nat.dvd_of_mod_eq_zero h_mod
      have h1 : (↑(r + i * K) : ZMod p) = (↑I₀ : ZMod p) := by
        rw [← ZMod.natCast_zmod_val (↑(r + i * K) : ZMod p),
            ← ZMod.natCast_zmod_val (↑I₀ : ZMod p)]
        congr 1; simp only [ZMod.val_natCast]; rwa [Nat.mod_eq_of_lt hI₀_lt]
      have hr_eq : (↑r : ZMod p) = ↑I₀ + ↑K := by
        suffices h : (↑r : ZMod p) = (↑(I₀ + K) : ZMod p) by rw [h]; push_cast; ring
        rw [← ZMod.natCast_zmod_val (↑r : ZMod p),
            ← ZMod.natCast_zmod_val (↑(I₀ + K) : ZMod p)]
        congr 1; simp only [ZMod.val_natCast]
        rw [hr_def]; exact Nat.mod_eq_of_lt (Nat.mod_lt _ hp_pos)
      have h2 : (↑K : ZMod p) * (1 + ↑i) = 0 := by
        have h_eq : (↑r : ZMod p) + ↑i * ↑K = ↑I₀ := by push_cast at h1; exact h1
        rw [hr_eq] at h_eq; linear_combination h_eq
      have hu : IsUnit (↑K : ZMod p) := by rwa [ZMod.isUnit_iff_coprime]
      have h3 : (1 : ZMod p) + ↑i = 0 := hu.mul_left_cancel (h2.trans (mul_zero _).symm)
      have h4 : (↑(i + 1) : ZMod p) = 0 := by push_cast; linear_combination h3
      have := congr_arg ZMod.val h4; simp only [ZMod.val_natCast, ZMod.val_zero] at this; exact this
    -- Closing mod: (r + (p-1)*K) % p = I₀
    have hclose_mod : (r + (p - 1) * K) % p = I₀ := by
      have h1 : r + (p - 1) * K ≡ I₀ + K + (p - 1) * K [MOD p] :=
        Nat.ModEq.add_right _ (Nat.mod_modEq (I₀ + K) p)
      have h2 : I₀ + K + (p - 1) * K = I₀ + p * K := by
        have hp1 : 1 ≤ p := by omega
        have : (p - 1) * K + K = p * K := by
          conv_rhs => rw [← Nat.sub_add_cancel hp1]
          rw [Nat.add_mul, one_mul]
        omega
      rw [Nat.ModEq, h2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hI₀_lt] at h1; exact h1
    -- Chain 1
    have hchain1 : ∀ i : Fin (p - 1),
        Necklace.kStepVector w (r + i.val * K) K = g_tern := by
      intro ⟨i, hi⟩
      apply hlift; apply hgood_any; exact hmod_ne_good i hi
    -- Chain 2: shifted by p (uses binary periodicity + ternary lift)
    have hchain2 : ∀ i : Fin (p - 1),
        Necklace.kStepVector w (r + p + i.val * K) K = g_tern := by
      intro ⟨i, hi⟩
      apply hlift
      rw [show r + p + i * K = (r + i * K) + p from by ring, hperiodic_B]
      apply hgood_any; exact hmod_ne_good i hi
    -- Closing 1
    have hclose1 : Necklace.kStepVector w (r + (p - 1) * K) K ≠ g_tern := by
      apply hbad_lift
      rw [← hmod_B, hclose_mod]; exact hI₀_bad
    -- Closing 2: shifted by p
    have hclose2 : Necklace.kStepVector w (r + p + (p - 1) * K) K ≠ g_tern := by
      apply hbad_lift
      rw [show r + p + (p - 1) * K = (r + (p - 1) * K) + p from by ring, hperiodic_B,
          ← hmod_B, hclose_mod]
      exact hI₀_bad
    -- ===== Phase 8: IsGenerator =====
    have hIsGen : IsGenerator (identifyPair w .L .m)
        (ZVector.identifyPair g_tern .L .m) := by
      set I := TernaryNecklace.identifyPair w .L .m
      set g_ident := ZVector.identifyPair g_tern .L .m
      -- Period length equality: period(I) = period(B) = p
      have hpB_lt_n : (Necklace.period B).length < n := by rw [hpLen]; omega
      have hpI_eq : (Necklace.period I).length = p := by
        rw [period_length_identifyPair_eq w hpB_lt_n, hpLen]
      -- Period-reduced: K < pLen(I) and g_ident appears at position r
      constructor
      · refine ⟨K, hpI_eq ▸ hK_lt, ⟨r % n, Nat.mod_lt _ (by omega)⟩, ?_⟩
        have h1 : Necklace.kStepVector w (r + 0 * K) K = g_tern :=
          hchain1 ⟨0, by omega⟩
        simp at h1
        rw [show (⟨r % n, _⟩ : Fin n).val = r % n from rfl]
        rw [show Necklace.kStepVector I (r % n) K = ZVector.identifyPair (Necklace.kStepVector w (r % n) K) .L .m from
          identifyPair_kStepVector w .L .m (by decide) (r % n) K]
        rw [kStepVector_mod_n, h1]
      · -- Stacking: transfer from IsGenerator B G
        obtain ⟨_, r₀, hfwd_B, hbwd_B⟩ := hG_gen
        -- Period vector correspondence
        set pVec_I := ZVector.ofList (Necklace.period I)
        set pVec_B := ZVector.ofList (Necklace.period B)
        -- pVec_I components: use kStepVector_full_period
        have hpvI_L : pVec_I .L = 0 := by
          show (ZVector.ofList (Necklace.period I)) .L = 0
          rw [← kStepVector_full_period I 0 .L]
          change (Necklace.kStepVector (TernaryNecklace.identifyPair w .L .m) 0 _ .L : ℤ) = _
          exact_mod_cast kStepVector_identifyPair_L_eq_zero w 0 _
        have hpvI_m : pVec_I .m = pVec_B .L := by
          show (ZVector.ofList (Necklace.period I)) .m = (ZVector.ofList (Necklace.period B)) .L
          rw [← kStepVector_full_period I 0 .m, ← kStepVector_full_period B 0 .L, hpI_eq, hpLen]
          show (Necklace.kStepVector (TernaryNecklace.identifyPair w .L .m) 0 p .m : ℤ) =
            Necklace.kStepVector (identifiedToBinary (TernaryNecklace.identifyPair w .L .m)) 0 p .L
          exact_mod_cast (kStepVector_identifiedToBinary_L_eq_identifyPair_m w 0 p).symm
        have hpvI_s : pVec_I .s = pVec_B .s := by
          show (ZVector.ofList (Necklace.period I)) .s = (ZVector.ofList (Necklace.period B)) .s
          rw [← kStepVector_full_period I 0 .s, ← kStepVector_full_period B 0 .s, hpI_eq, hpLen]
          -- Chain: I.kStepVector .s = w.kStepVector .s (via identifyPair_kStepVector)
          --        w.kStepVector .s = B.kStepVector .s (via identifiedToBinary_kStepVector_s)
          have hI_s : Necklace.kStepVector I 0 p .s = Necklace.kStepVector w 0 p .s := by
            show Necklace.kStepVector (TernaryNecklace.identifyPair w .L .m) 0 p .s = _
            rw [identifyPair_kStepVector w .L .m (by decide) 0 p]; simp [ZVector.identifyPair]
          exact_mod_cast hI_s.symm ▸ (identifiedToBinary_kStepVector_s w 0 p).symm
        -- g_ident components
        have hg_L : g_ident .L = 0 := by simp [g_ident, ZVector.identifyPair]
        have hg_m : g_ident .m = G .L := by
          simp only [g_ident, ZVector.identifyPair, g_tern]
          split_ifs <;> simp_all
          show gL_half + gL_half = G .L; omega
        have hg_s : g_ident .s = G .s := by
          simp [g_ident, ZVector.identifyPair, g_tern]
        -- kStepVector correspondence for I and B (rotated)
        -- After kStepVector_rotate, goals have (r₀.val + 0); simplify with add_zero
        have kstep_rot_L (m : ℕ) :
            Necklace.kStepVector (fun i => I (i + r₀)) 0 m .L = 0 := by
          rw [kStepVector_rotate]; simp only [Nat.add_zero]
          change Necklace.kStepVector (TernaryNecklace.identifyPair w .L .m) _ _ _ = _
          exact_mod_cast kStepVector_identifyPair_L_eq_zero w _ _
        have kstep_rot_m (m : ℕ) :
            (Necklace.kStepVector (fun i => I (i + r₀)) 0 m .m : ℤ) =
            Necklace.kStepVector (fun i => B (i + r₀)) 0 m .L := by
          rw [kStepVector_rotate, kStepVector_rotate]; simp only [Nat.add_zero]
          change (Necklace.kStepVector (TernaryNecklace.identifyPair w .L .m) _ _ .m : ℤ) =
            Necklace.kStepVector (identifiedToBinary (TernaryNecklace.identifyPair w .L .m)) _ _ .L
          exact_mod_cast (kStepVector_identifiedToBinary_L_eq_identifyPair_m w _ _).symm
        have kstep_rot_s (m : ℕ) :
            (Necklace.kStepVector (fun i => I (i + r₀)) 0 m .s : ℤ) =
            Necklace.kStepVector (fun i => B (i + r₀)) 0 m .s := by
          rw [kStepVector_rotate, kStepVector_rotate]; simp only [Nat.add_zero]
          -- Chain: I.kStepVector .s = w.kStepVector .s = B.kStepVector .s
          have hI_s : Necklace.kStepVector I (ZMod.val r₀) m .s =
              Necklace.kStepVector w (ZMod.val r₀) m .s := by
            show Necklace.kStepVector (TernaryNecklace.identifyPair w .L .m) _ _ .s = _
            rw [identifyPair_kStepVector w .L .m (by decide) _ _]; simp [ZVector.identifyPair]
          exact_mod_cast hI_s.symm ▸ (identifiedToBinary_kStepVector_s w _ _).symm
        -- Use the same rotation
        refine ⟨r₀, ?_, ?_⟩
        -- Forward direction
        · intro ⟨i, hi⟩
          have hi' : i < (Necklace.period B).length := by omega
          obtain ⟨⟨j, hj⟩, k', hpref⟩ := hfwd_B ⟨i, hi'⟩
          refine ⟨⟨j, ?_⟩, k', fun a => ?_⟩
          · omega
          · cases a with
            | L => simp [kstep_rot_L, hg_L, hpvI_L]
            | m =>
              have := hpref .L
              rw [kstep_rot_m, hg_m, hpvI_m]; exact this
            | s =>
              have := hpref .s
              rw [kstep_rot_s, hg_s, hpvI_s]; exact this
        -- Backward direction
        · intro ⟨j, hj⟩
          have hj' : j < (Necklace.period B).length := by omega
          obtain ⟨⟨i, hi⟩, k', hpref⟩ := hbwd_B ⟨j, hj'⟩
          refine ⟨⟨i, ?_⟩, k', fun a => ?_⟩
          · omega
          · cases a with
            | L => simp [kstep_rot_L, hg_L, hpvI_L]
            | m =>
              have := hpref .L
              rw [kstep_rot_m, hg_m, hpvI_m]; exact this
            | s =>
              have := hpref .s
              rw [kstep_rot_s, hg_s, hpvI_s]; exact this
    exact ⟨K, g_tern, r, hK_pos, hK_lt, hcop_K, hchain1, hchain2, hclose1, hclose2, hIsGen⟩
  -- ===== Proof of suffices (Phase 5 case split) =====
  obtain ⟨m, hm_even | hm_odd⟩ := Nat.even_or_odd' (g_bin .L).natAbs
  · -- Case: g_bin.L is even — use (k, g_bin, i₀) directly
    refine ⟨k, g_bin, i₀, hk_pos, hk_lt_p, hcop_k, hgL_nn, hgs_nn, hg_sum, ?_, hi₀_lt,
            hi₀_bad, hi₀_good, hg'_total, ?_, hgen⟩
    · -- G.L % 2 = 0
      have h1 : (g_bin .L).natAbs % 2 = 0 := by omega
      have h2 : Even (g_bin .L).natAbs := Nat.even_iff.mpr h1
      exact Int.even_iff.mp (Int.natAbs_even.mp h2)
    · -- Sum formula
      intro x; rw [← list_range_map_sum_eq_finset]
      have h := kStepVector_lettercount_sum_over_period B k hk_pos (hpLen ▸ hk_lt_p) x
      rw [hpLen] at h; rw [h]
  · -- Case: g_bin.L is odd — use complement (p-k, pVec-g_bin, (i₀+k)%p)
    set K := p - k with hK_def
    set G : ZVector BinaryStep := fun x => pVec x - g_bin x with hG_def
    set I₀ := (i₀ + k) % p with hI₀_def
    have hK_pos : 0 < K := by omega
    have hK_lt : K < p := by omega
    have hcop_K : Nat.Coprime K p := by
      have h1 : Nat.Coprime (p - k) k :=
        (Nat.coprime_sub_self_left (le_of_lt hk_lt_p)).mpr (hcop_k.symm)
      rwa [show p = k + (p - k) from by omega, Nat.coprime_add_self_right]
    have hgL_le_a : g_bin .L ≤ ↑a := by
      rcases hbezout with h | h <;> nlinarith [hk_lt_p]
    have hgs_le_c : g_bin .s ≤ ↑c := by
      -- p * g_bin.s = p * (k - g_bin.L) = p*k - p*g_bin.L = p*k - (k*a ± 1) = k*c ∓ 1
      have h1 : (↑p : ℤ) * g_bin .s = ↑p * ↑k - ↑p * g_bin .L := by
        have := hg_sum; push_cast at this ⊢; nlinarith
      rcases hbezout with hb | hb
      · -- p * g_bin.L = k * a + 1, so p * g_bin.s = p*k - k*a - 1 = k*c - 1
        have h2 : (↑p : ℤ) * g_bin .s = ↑k * ↑c - 1 := by
          push_cast [hp_eq] at h1 ⊢; nlinarith
        nlinarith [hk_lt_p, hgs_nn]
      · -- p * g_bin.L = k * a - 1, so p * g_bin.s = p*k - k*a + 1 = k*c + 1
        have h2 : (↑p : ℤ) * g_bin .s = ↑k * ↑c + 1 := by
          push_cast [hp_eq] at h1 ⊢; nlinarith
        nlinarith [hk_lt_p, hgs_nn, _hc_pos]
    have hGL_nn : G .L ≥ 0 := by simp only [G]; rw [hpvL]; linarith [hgL_le_a]
    have hGs_nn : G .s ≥ 0 := by simp only [G]; rw [hpvs]; linarith [hgs_le_c]
    have hG_sum : G .L + G .s = ↑K := by
      simp only [G]; rw [hpvL, hpvs]
      have hK_cast : (↑K : ℤ) = ↑p - ↑k := by
        have : k ≤ p := le_of_lt hk_lt_p
        omega
      rw [hK_cast, hp_eq]; push_cast; linarith [hg_sum]
    have hGL_even : G .L % 2 = 0 := by
      simp only [G]; rw [hpvL]
      -- a - g_bin.L: a is odd, g_bin.L is odd ⟹ difference is even
      have hgL_odd : g_bin .L % 2 = 1 := by
        have h1 : (g_bin .L).natAbs % 2 = 1 := by omega
        have h2 : Odd (g_bin .L).natAbs := Nat.odd_iff.mpr h1
        exact Int.odd_iff.mp (Int.natAbs_odd.mp h2)
      have ha_cast : (↑a : ℤ) % 2 = 1 := by exact_mod_cast _ha_odd
      omega
    have hI₀_lt : I₀ < p := Nat.mod_lt _ hp_pos
    -- Complement counting: kStepVector B j K = G for all j ≠ I₀
    have hI₀_good : ∀ j, j < p → j ≠ I₀ → Necklace.kStepVector B j K = G := by
      intro j hj hne
      -- Use complement: kStepVector B j (p-k) x = pVec x - kStepVector B (j-k) k x
      -- where (j-k) % p ≠ i₀ (from j ≠ I₀ = (i₀+k)%p)
      -- So kStepVector B (j-k)%p k = g_bin, giving kStepVector B j (p-k) = pVec - g_bin = G
      -- First show: kStepVector B j (p-k) = kStepVector B (j%p + k + (p-k)) - backwards, use complement
      -- Actually: kStepVector B ((j + p - k) % p + k) (p-k) = pVec - kStepVector B ((j+p-k)%p) k
      -- And (j + p - k) % p + k ≡ j (mod p)
      set j' := (j + p - k) % p with hj'_def
      have hj'_lt : j' < p := Nat.mod_lt _ hp_pos
      -- Key mod calculation: ((j + p - k) % p + k) % p = j
      have hmod_calc : ((j + p - k) % p + k) % p = j := by
        have h1 : (j + p - k) % p + k ≡ (j + p - k) + k [MOD p] :=
          Nat.ModEq.add_right k (Nat.mod_modEq _ p)
        rw [Nat.ModEq] at h1
        rw [show j + p - k + k = j + p from by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt hj] at h1
        exact h1
      have hj'_ne_i₀ : j' ≠ i₀ := by
        intro heq
        apply hne; rw [hI₀_def, ← heq, hj'_def, hmod_calc]
      have hj'_good : Necklace.kStepVector B j' k = g_bin := hi₀_good j' hj'_lt hj'_ne_i₀
      -- kStepVector B (j' + k) (p - k) = pVec - kStepVector B j' k = pVec - g_bin = G
      have hcomp_eq : ∀ x, Necklace.kStepVector B (j' + k) (p - k) x =
          pVec x - g_bin x := by
        intro x; rw [hcomp j', congr_fun hj'_good x]
      -- Transfer: kStepVector B j K = kStepVector B (j'+k) K (since (j'+k) % p = j, mod-period)
      rw [show K = p - k from rfl]
      -- kStepVector B j (p-k) = kStepVector B (j'+k) (p-k) by mod-period
      have hmod_step : Necklace.kStepVector B j (p - k) = Necklace.kStepVector B (j' + k) (p - k) := by
        have h := kStepVector_mod_period' B (j' + k) (p - k)
        rw [hpLen, hmod_calc] at h; exact h
      rw [hmod_step]; funext x; exact hcomp_eq x
    have hI₀_bad : Necklace.kStepVector B I₀ K ≠ G := by
      -- I₀ = (i₀ + k) % p. kStepVector B I₀ (p-k) = pVec - kStepVector B i₀ k ≠ pVec - g_bin
      -- since kStepVector B i₀ k ≠ g_bin
      intro heq
      apply hi₀_bad
      -- From heq: kStepVector B I₀ (p-k) = G = pVec - g_bin
      -- kStepVector B (i₀ + k) (p-k) = pVec - kStepVector B i₀ k (complement)
      -- So pVec - kStepVector B i₀ k = pVec - g_bin, hence kStepVector B i₀ k = g_bin
      have : ∀ x, Necklace.kStepVector B (i₀ + k) (p - k) x = pVec x - g_bin x := by
        intro x
        have h1 : Necklace.kStepVector B I₀ (p - k) x = (pVec x - g_bin x) :=
          congr_fun heq x
        -- I₀ = (i₀ + k) % p, and kStepVector is periodic mod period length
        have h_mod := congr_fun (kStepVector_mod_period' B (i₀ + k) (p - k)) x
        rw [hpLen] at h_mod  -- period length = p
        -- h_mod : kStepVector B ((i₀+k) % p) (p-k) x = kStepVector B (i₀+k) (p-k) x
        rw [← h_mod]; exact h1
      have h2 : ∀ x, Necklace.kStepVector B (i₀ + k) (p - k) x = pVec x - Necklace.kStepVector B i₀ k x := by
        intro x; exact hcomp i₀ x
      funext x; have := this x; have := h2 x; linarith
    have hG'_total : (Necklace.kStepVector B I₀ K) .L + (Necklace.kStepVector B I₀ K) .s = ↑K := by
      exact_mod_cast kStepVector_total_count B I₀ K
    have hsum_eff : ∀ (x : BinaryStep),
        ∑ i ∈ Finset.range p, Necklace.kStepVector B i K x = ↑K * pVec x := by
      intro x; rw [← list_range_map_sum_eq_finset]
      have h := kStepVector_lettercount_sum_over_period B K hK_pos (hpLen ▸ hK_lt) x
      rw [hpLen] at h; rw [h]
    have hG_gen : IsGenerator B G := by
      apply p_minus_one_occurrences_implies_generator B hB_mos.1 G K hK_pos (hpLen ▸ hK_lt)
      simp only [countKStepVectorPerPeriod, hpLen]
      -- Count positions j < p with kStepVector B j K = G: all except I₀
      -- Erase I₀ from List.range p: all remaining give true
      have hI₀_in : I₀ ∈ List.range p := List.mem_range.mpr hI₀_lt
      set pred := fun j => decide (Necklace.kStepVector B j K = G)
      have hfalse : pred I₀ = false := by simp [pred, hI₀_bad]
      have htrue : ∀ j ∈ (List.range p).erase I₀, pred j = true := by
        intro j hj
        have hj_ne : j ≠ I₀ := by
          intro heq; subst heq
          exact List.nodup_range.not_mem_erase hj
        have hj_lt : j < p := List.mem_range.mp (List.mem_of_mem_erase hj)
        simp [pred, hI₀_good j hj_lt hj_ne]
      have h1 : ((List.range p).erase I₀).countP pred =
          ((List.range p).erase I₀).length := by
        exact List.countP_eq_length.mpr htrue
      have h2 : ((List.range p).erase I₀).length = p - 1 := by
        rw [List.length_erase_of_mem hI₀_in, List.length_range]
      have h3 : (List.range p).countP pred = ((List.range p).erase I₀).countP pred := by
        rw [List.countP_erase]; simp [hI₀_in, hfalse]
      omega
    exact ⟨K, G, I₀, hK_pos, hK_lt, hcop_K, hGL_nn, hGs_nn, hG_sum, hGL_even,
           hI₀_lt, hI₀_bad, hI₀_good, hG'_total, hsum_eff, hG_gen⟩

/-- Chain data for an even-regular scale: a permutation `σ`, a step size `k`
    with `gcd(k, n/2) = 1`, a k-step vector `g`, and a starting position `r`
    such that there are two chains of `p - 1` stacked `g`. -/
structure EvenRegularChainData (n : ℕ) [NeZero n] (w : TernaryNecklace n) where
  σ : Equiv.Perm StepSize
  k : ℕ
  g : ZVector StepSize
  r : ℕ
  hk_pos : 0 < k
  hk_lt : k < n / 2
  hcop : Nat.Coprime k (n / 2)
  hchain1 : ∀ i : Fin (n / 2 - 1),
    Necklace.kStepVector (Necklace.applyPerm σ w) (r + i.val * k) k = g
  hchain2 : ∀ i : Fin (n / 2 - 1),
    Necklace.kStepVector (Necklace.applyPerm σ w) (r + n / 2 + i.val * k) k = g
  hclose1 : Necklace.kStepVector (Necklace.applyPerm σ w) (r + (n / 2 - 1) * k) k ≠ g
  hclose2 : Necklace.kStepVector (Necklace.applyPerm σ w) (r + n / 2 + (n / 2 - 1) * k) k ≠ g
  hgen : IsGenerator (TernaryNecklace.identifyPair (Necklace.applyPerm σ w) .L .m)
    (ZVector.identifyPair g .L .m)
  hcount_L_odd : Necklace.count (Necklace.applyPerm σ w) .L % 2 = 1
  hcount_L_lt : Necklace.count (Necklace.applyPerm σ w) .L < n / 2

/-- The two chains of an even-regular scale are offset by the `(n/2)`-step
    interval: for each non-closing index `i`, the k-step vector at position
    `r + i*k` equals the k-step vector at position `r + n/2 + i*k` (both = g). -/
theorem evenRegular_chains_offset (w : TernaryNecklace n)
    (d : EvenRegularChainData n w) :
    let w' := Necklace.applyPerm d.σ w
    let p := n / 2
    ∀ i : Fin (p - 1),
      Necklace.kStepVector w' (d.r + i.val * d.k) d.k =
      Necklace.kStepVector w' (d.r + p + i.val * d.k) d.k := by
  intro w' p i
  exact (d.hchain1 i).trans (d.hchain2 i).symm

/-- In an alternating word D (D[i]=D[i%2], D[0]≠D[1], binary with L/m) of length 2a,
    any window of size m has L-count in {⌊m/2⌋, ⌈m/2⌉}. -/
private lemma alternating_window_Lcount_bounds (D : List StepSize) (a m : ℕ)
    (ha : a > 0) (hlen : D.length = 2 * a)
    (halt : ∀ i, (hi : i < D.length) → D[i] = D[i % 2]'(by omega))
    (hne : D[0]'(by omega) ≠ D[1]'(by omega))
    (hbin : ∀ i, (hi : i < D.length) → D[i] = .L ∨ D[i] = .m)
    (hDlen_pos : 0 < D.length)
    (q : ℕ) :
    m / 2 ≤ ((List.range m).map (fun t =>
      D[(q + t) % D.length]'(Nat.mod_lt _ hDlen_pos))).count .L ∧
    ((List.range m).map (fun t =>
      D[(q + t) % D.length]'(Nat.mod_lt _ hDlen_pos))).count .L ≤ (m + 1) / 2 := by
  set W := (List.range m).map (fun t =>
    D[(q + t) % D.length]'(Nat.mod_lt _ hDlen_pos)) with hW_def
  rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
  · -- m = 2j: L-count = j by alternating_even_window_Lcount
    have hDwindow := alternating_even_window_Lcount D a j ha hlen halt hne hbin q hDlen_pos
    have hm2j : m = 2 * j := by omega
    subst hm2j
    have h1 : 2 * j / 2 = j := Nat.mul_div_cancel_left j (by omega)
    have h2 : (2 * j + 1) / 2 = j := by omega
    rw [h1, h2]; exact ⟨le_of_eq hDwindow.symm, le_of_eq hDwindow⟩
  · -- m = 2j + 1: window = (window of 2j) ++ [last element]
    have heven := alternating_even_window_Lcount D a j ha hlen halt hne hbin q hDlen_pos
    -- Decompose W = first 2j elements ++ [last element]
    have hdecomp : W.count .L =
      ((List.range (2 * j)).map (fun t =>
        D[(q + t) % D.length]'(Nat.mod_lt _ hDlen_pos))).count .L +
      ([D[(q + 2 * j) % D.length]'(Nat.mod_lt _ hDlen_pos)]).count .L := by
      rw [hW_def, hj, show 2 * j + 1 = 2 * j + 1 from rfl]
      rw [show (2 * j + 1) = (2 * j) + 1 from by omega]
      rw [List.range_succ, List.map_append, List.count_append, List.map_singleton]
    rw [hdecomp, heven]
    have h1 : (2 * j + 1) / 2 = j := by omega
    have h2 : (2 * j + 1 + 1) / 2 = j + 1 := by
      rw [show 2 * j + 1 + 1 = 2 * (j + 1) from by omega]
      exact Nat.mul_div_cancel_left (j + 1) (by omega)
    -- The last element is either .L (count 1) or .m (count 0)
    rcases hbin ((q + 2 * j) % D.length) (Nat.mod_lt _ hDlen_pos) with hL | hm
    · have hcount : ([D[(q + 2 * j) % D.length]'(Nat.mod_lt _ hDlen_pos)]).count .L = 1 := by
        rw [hL]; decide
      rw [hcount, hj, h1, h2]; omega
    · have hcount : ([D[(q + 2 * j) % D.length]'(Nat.mod_lt _ hDlen_pos)]).count .L = 0 := by
        rw [hm]; decide
      rw [hcount, hj, h1, h2]; omega

/-- Bound on L-count in a k-step window: nonS/2 ≤ Lc ≤ (nonS+1)/2 where
    nonS is the non-s count. Bridge from `orderedDeletion_window_Lcount` and
    `alternating_window_Lcount_bounds`. -/
private lemma evenRegular_slice_Lcount_bounds (w : TernaryNecklace n)
    (a c : ℕ) (ha_pos : a > 0) (hn : n = 2 * a + 2 * c)
    (hcountL : Necklace.count w .L = a) (hcountm : Necklace.count w .m = a)
    (hcounts : Necklace.count w .s = 2 * c)
    (hdel : isPartialDeletionMOS w .s)
    (r k : ℕ) (_hk_pos : 0 < k) (hk_lt : k < n) :
    let sl := Necklace.slice w r (r + k)
    let nonS := sl.count .L + sl.count .m
    nonS / 2 ≤ sl.count .L ∧ sl.count .L ≤ (nonS + 1) / 2 := by
  intro sl nonS
  -- Set up deletion word D
  set D := TernaryNecklace.orderedDeletion w .s with hD_def
  have hDlen : D.length = 2 * a := by
    have h : D.length + Necklace.count w .s = n := orderedDeletion_length w .s
    rw [hcounts, hn] at h; omega
  have hDlen_pos : 0 < D.length := by omega
  have hmem_ne_s : ∀ x ∈ D, x ≠ .s := fun x hx => by
    simp only [D, TernaryNecklace.orderedDeletion, List.mem_filter,
      decide_eq_true_eq] at hx; exact hx.2
  have hbin : ∀ i, (hi : i < D.length) → D[i] = .L ∨ D[i] = .m := by
    intro i hi
    have hne : D[i] ≠ .s := hmem_ne_s _ (List.getElem_mem hi)
    cases h : D[i] with | L => left; rfl | m => right; rfl | s => exact absurd h hne
  have hDcountL : D.count .L = a := by
    rw [hD_def, orderedDeletion_count_ne w .s .L (by decide)]; exact hcountL
  have hDcountm : D.count .m = a := by
    rw [hD_def, orderedDeletion_count_ne w .s .m (by decide)]; exact hcountm
  obtain ⟨halt, hne⟩ := balanced_circular_mos_is_alternating D a ha_pos hDlen
    hbin hDcountL hDcountm hdel
  -- nonS = filter(≠s).length
  have hnonS_eq : nonS = (sl.filter (· ≠ .s)).length := by
    -- count L + count m + count s = length (by induction, no filter involved)
    have htotal : ∀ (l : List StepSize),
        l.count .L + l.count .m + l.count .s = l.length := by
      intro l; induction l with
      | nil => simp
      | cons x xs ih => cases x <;> simp [List.length_cons] <;> omega
    -- filter(≠s).length + filter(==s).length = length (library lemma)
    have hcomp := List.length_eq_length_filter_add
      (fun x => !decide (x = StepSize.s)) (l := sl)
    simp only [Bool.not_not] at hcomp
    rw [show sl.filter (fun x => !decide (x = StepSize.s)) =
        sl.filter (· ≠ .s) from by congr 1; ext x; simp [ne_eq],
      show sl.filter (fun x => decide (x = StepSize.s)) =
        sl.filter (· == .s) from by congr 1] at hcomp
    simp only [← List.count_eq_length_filter] at hcomp
    have := htotal sl; omega
  -- Bridge: L-count = D-window L-count
  set wList := (List.range n).map (fun i => w (↑i : ZMod n)) with hwList_def
  set q := ((wList.take (r % n)).filter (· ≠ .s)).length with hq_def
  have hbridge : ((List.range nonS).map (fun t =>
      D[(q + t) % D.length]'(Nat.mod_lt _ hDlen_pos))).count .L =
      (Necklace.kStepVector w r k .L).natAbs := by
    rw [hnonS_eq]
    exact orderedDeletion_window_Lcount w r k _ hDlen_pos (by omega) rfl
  have hkv_eq : (Necklace.kStepVector w r k .L).natAbs = sl.count .L := by
    simp only [Necklace.kStepVector, ZVector.ofList, Int.natAbs_natCast,
      ← List.count_eq_length_filter, sl]
  rw [hkv_eq] at hbridge
  -- Apply alternating_window_Lcount_bounds
  have hbounds := alternating_window_Lcount_bounds D a nonS ha_pos hDlen halt hne
    hbin hDlen_pos q
  rw [hbridge] at hbounds
  exact hbounds

/-- Core balance proof for even-regular data: given a scale with step signature
    `(a, a, 2c)` where `a` is odd and `gcd(a, c) = 1`, show it is balanced.

    **Proof outline** (from even-regular.txt):
    • s-count: Conflating L and m gives a MOS, so the s-count in any k-step
      subword takes at most 2 consecutive values → s-count differs by ≤ 1.
    • L/m-count: If the non-s count in a k-step subword is even, then
      |w|_L = |w|_m = (non-s count)/2, uniquely determined.
      If the non-s count is odd, then |w|_L and |w|_m each differ by ≤ 1
      (from the alternating L/m structure). -/
private lemma evenRegular_data_isBalanced (w : TernaryNecklace n)
    (a c : ℕ) (_ha_pos : a > 0) (_hc_pos : c > 0)
    (_ha_odd : a % 2 = 1) (_hcop : Nat.Coprime a c) (_hn : n = 2 * a + 2 * c)
    (_hcountL : Necklace.count w .L = a) (_hcountm : Necklace.count w .m = a)
    (_hcounts : Necklace.count w .s = 2 * c)
    (_hmos : isPartialPairwiseMOS w .L .m)
    (_hdel : isPartialDeletionMOS w .s) :
    Necklace.isBalanced w := by
  intro k hk hk' w1 w2 a' hw1 hw2
  -- Extract positions
  rw [Necklace.allKStepSubwords, List.mem_ofFn] at hw1 hw2
  obtain ⟨i, rfl⟩ := hw1; obtain ⟨j, rfl⟩ := hw2
  cases a' with
  | s => exact identification_preserves_letter_balance w .L .m (by decide) .s
          (by decide) (by decide) _hmos k hk hk'
          (Necklace.slice w i.val (i.val + k)) (Necklace.slice w j.val (j.val + k))
          (List.mem_ofFn.mpr ⟨i, rfl⟩) (List.mem_ofFn.mpr ⟨j, rfl⟩)
  | L =>
    -- L-count bounds from alternating structure
    have hb1 := evenRegular_slice_Lcount_bounds w a c _ha_pos _hn
        _hcountL _hcountm _hcounts _hdel i.val k hk hk'
    have hb2 := evenRegular_slice_Lcount_bounds w a c _ha_pos _hn
        _hcountL _hcountm _hcounts _hdel j.val k hk hk'
    -- s-count balance
    have hs := identification_preserves_letter_balance w .L .m (by decide) .s
        (by decide) (by decide) _hmos k hk hk'
        (Necklace.slice w i.val (i.val + k)) (Necklace.slice w j.val (j.val + k))
        (List.mem_ofFn.mpr ⟨i, rfl⟩) (List.mem_ofFn.mpr ⟨j, rfl⟩)
    -- Name counts to avoid long expressions
    set L1 := (Necklace.slice w i.val (i.val + k)).count .L
    set m1 := (Necklace.slice w i.val (i.val + k)).count .m
    set s1 := (Necklace.slice w i.val (i.val + k)).count .s
    set L2 := (Necklace.slice w j.val (j.val + k)).count .L
    set m2 := (Necklace.slice w j.val (j.val + k)).count .m
    set s2 := (Necklace.slice w j.val (j.val + k)).count .s
    -- L + m + s = k for each slice (by induction on list, avoids kStepVector)
    have ternary_total : ∀ (l : List StepSize),
        l.count .L + l.count .m + l.count .s = l.length := by
      intro l; induction l with
      | nil => simp
      | cons x xs ih => cases x <;> simp [List.length_cons] <;> omega
    have ht1 := ternary_total (Necklace.slice w i.val (i.val + k))
    have ht2 := ternary_total (Necklace.slice w j.val (j.val + k))
    have hlen1 : (Necklace.slice w i.val (i.val + k)).length = k := by
      have := Necklace.slice_length w i.val (i.val + k); omega
    have hlen2 : (Necklace.slice w j.val (j.val + k)).length = k := by
      have := Necklace.slice_length w j.val (j.val + k); omega
    -- Eliminate division: nonS/2 ≤ L → nonS ≤ 2L+1
    have hb1_lo : L1 + m1 ≤ 2 * L1 + 1 := by
      have := hb1.1; set d := (L1 + m1) / 2; set r := (L1 + m1) % 2
      have := Nat.div_add_mod (L1 + m1) 2
      have := Nat.mod_lt (L1 + m1) (show 0 < 2 from by omega); omega
    -- Eliminate division: L ≤ (nonS+1)/2 → 2L ≤ nonS+1
    have hb1_hi : 2 * L1 ≤ L1 + m1 + 1 := by
      have := hb1.2; set d := (L1 + m1 + 1) / 2
      have := Nat.div_mul_le_self (L1 + m1 + 1) 2; omega
    have hb2_lo : L2 + m2 ≤ 2 * L2 + 1 := by
      have := hb2.1; set d := (L2 + m2) / 2; set r := (L2 + m2) % 2
      have := Nat.div_add_mod (L2 + m2) 2
      have := Nat.mod_lt (L2 + m2) (show 0 < 2 from by omega); omega
    have hb2_hi : 2 * L2 ≤ L2 + m2 + 1 := by
      have := hb2.2; set d := (L2 + m2 + 1) / 2
      have := Nat.div_mul_le_self (L2 + m2 + 1) 2; omega
    omega
  | m =>
    -- Same bounds and setup as L case
    have hb1 := evenRegular_slice_Lcount_bounds w a c _ha_pos _hn
        _hcountL _hcountm _hcounts _hdel i.val k hk hk'
    have hb2 := evenRegular_slice_Lcount_bounds w a c _ha_pos _hn
        _hcountL _hcountm _hcounts _hdel j.val k hk hk'
    have hs := identification_preserves_letter_balance w .L .m (by decide) .s
        (by decide) (by decide) _hmos k hk hk'
        (Necklace.slice w i.val (i.val + k)) (Necklace.slice w j.val (j.val + k))
        (List.mem_ofFn.mpr ⟨i, rfl⟩) (List.mem_ofFn.mpr ⟨j, rfl⟩)
    set L1 := (Necklace.slice w i.val (i.val + k)).count .L
    set m1 := (Necklace.slice w i.val (i.val + k)).count .m
    set s1 := (Necklace.slice w i.val (i.val + k)).count .s
    set L2 := (Necklace.slice w j.val (j.val + k)).count .L
    set m2 := (Necklace.slice w j.val (j.val + k)).count .m
    set s2 := (Necklace.slice w j.val (j.val + k)).count .s
    have ternary_total : ∀ (l : List StepSize),
        l.count .L + l.count .m + l.count .s = l.length := by
      intro l; induction l with
      | nil => simp
      | cons x xs ih => cases x <;> simp [List.length_cons] <;> omega
    have ht1 := ternary_total (Necklace.slice w i.val (i.val + k))
    have ht2 := ternary_total (Necklace.slice w j.val (j.val + k))
    have hlen1 : (Necklace.slice w i.val (i.val + k)).length = k := by
      have := Necklace.slice_length w i.val (i.val + k); omega
    have hlen2 : (Necklace.slice w j.val (j.val + k)).length = k := by
      have := Necklace.slice_length w j.val (j.val + k); omega
    have hb1_lo : L1 + m1 ≤ 2 * L1 + 1 := by
      have := hb1.1; set d := (L1 + m1) / 2; set r := (L1 + m1) % 2
      have := Nat.div_add_mod (L1 + m1) 2
      have := Nat.mod_lt (L1 + m1) (show 0 < 2 from by omega); omega
    have hb1_hi : 2 * L1 ≤ L1 + m1 + 1 := by
      have := hb1.2; set d := (L1 + m1 + 1) / 2
      have := Nat.div_mul_le_self (L1 + m1 + 1) 2; omega
    have hb2_lo : L2 + m2 ≤ 2 * L2 + 1 := by
      have := hb2.1; set d := (L2 + m2) / 2; set r := (L2 + m2) % 2
      have := Nat.div_add_mod (L2 + m2) 2
      have := Nat.mod_lt (L2 + m2) (show 0 < 2 from by omega); omega
    have hb2_hi : 2 * L2 ≤ L2 + m2 + 1 := by
      have := hb2.2; set d := (L2 + m2 + 1) / 2
      have := Nat.div_mul_le_self (L2 + m2 + 1) 2; omega
    omega

/-- Even-regular scales are balanced. -/
theorem evenRegular_isBalanced (w : TernaryNecklace n)
    (h : isEvenRegular w) :
    Necklace.isBalanced w := by
  obtain ⟨_hprim, _heven, σ, a, c, ha_pos, hc_pos, ha_odd, hcop, hn,
    hcountL, hcountm, hcounts, hmos, hdel⟩ := h
  exact (isS3Invariant_isBalanced σ w).mpr
    (evenRegular_data_isBalanced _ a c ha_pos hc_pos ha_odd hcop hn
      hcountL hcountm hcounts hmos hdel)


/-! ## Even-Regular as Interleavings -/

/-- Even-regular scales of length 4 (i.e., `xyxz`) are interleavings of
    a 2-note MOS.

    **Proof**: The `n = 4` case is trivial (included for completeness).
    Since `a = 1` and `c = 1`, the template MOS is `2X 2Z` and the scale
    is determined up to S₃-equivalence and rotation. -/
theorem evenRegular_four_isInterleaving [NeZero (n / 2)] (w : TernaryNecklace n)
    (h : isEvenRegular w) (hn : n = 4) :
    Necklace.isInterleaving w 2 ∧
    ∃ (φ : ZVector StepSize → StepSize),
      Necklace.hasMOSProperty (φ ∘ Necklace.strand2 w ⟨0, by omega⟩) := sorry

/-- Doubly-even (`n ≡ 0 mod 4`) even-regular scales with `n > 4` are
    interleavings of two copies of a smaller even-regular scale.

    **Proof outline** (from interleaving.txt):
    Let s₁ = stacked 2-steps from 0-degree, s₂ = offset at a generator
    chosen to have the same interval class as a generator for the
    lexicographically first mode of `aX 2kZ`. This induces s₁ = s₂ (same
    period, both primitive). Both s₁ and s₂ are MOS substitution scales
    with a filling MOS of period 2. Since both `a` and `2k` are even,
    there are evenly many chunk boundaries, hence evenly many non-slot
    letters in both → both strands are even-regular. -/
theorem evenRegular_doubly_even_isInterleaving [NeZero (n / 2)]
    (w : TernaryNecklace n)
    (h : isEvenRegular w) (hmod : n % 4 = 0) (hgt : n > 4) :
    Necklace.isInterleaving w 2 ∧
    ∃ (φ : ZVector StepSize → StepSize),
      isEvenRegular (φ ∘ Necklace.strand2 w ⟨0, by omega⟩) := sorry

/-- Singly-even (`n ≡ 2 mod 4`) even-regular scales are contrainterleavings
    of the two chiralities of an odd-regular scale.

    **Proof outline** (from interleaving.txt):
    Let s₁ = stacked 2-steps from 0-degree, s₂ = from (n/2)-degree.
    Since `n/2` is odd, s₁ and s₂ differ only by interchanging `y` and `z`,
    giving them the same period (both primitive). Both are MOS substitution
    scales with filling MOS of period 2. Since there are evenly many slot
    letters in both s₁ and s₂, there are oddly many non-slot letters.
    Since s₁ and s₂ differ by interchanging `y` and `z`, they have
    "opposite" filling letters (`x+y` vs `x+z`) → opposite chiralities
    of an odd-regular MV3 scale. -/
theorem evenRegular_singly_even_isContrainterleaving [NeZero (n / 2)]
    (w : TernaryNecklace n)
    (h : isEvenRegular w) (hmod : n % 4 = 2) :
    Necklace.isContrainterleaving w ∧
    ∃ (φ : ZVector StepSize → StepSize),
      isOddRegular (φ ∘ Necklace.strand2 w ⟨0, by omega⟩) := sorry


end TernaryNecklace
