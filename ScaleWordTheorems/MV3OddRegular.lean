import ScaleWordTheorems.MV3AS

open BigOperators

namespace TernaryNecklace

variable {n : ℕ} [NeZero n]

/-! ### From odd-regular to AS: helper lemmas -/

/-- hasAS is preserved under letter permutation (inverse direction):
    if `applyPerm σ w` has an AS, then so does `w`. -/
private lemma hasAS_of_applyPerm (σ : Equiv.Perm StepSize)
    (w : TernaryNecklace n)
    (h : hasAS (Necklace.applyPerm σ w)) : hasAS w := by
  obtain ⟨k₀, r, seq_σ, hk₀_lt, hcop, hseq, hclose⟩ := h
  refine ⟨k₀, r, fun j => ZVector.applyPerm σ.symm (seq_σ j), ?_, hcop, ?_, ?_⟩
  · exact hk₀_lt
  · intro i
    have h_eq := hseq i
    rw [kStepVector_applyPerm] at h_eq
    -- h_eq : ZVector.applyPerm σ (kStepVector w ...) = seq_σ (i%2)
    -- Apply σ.symm to both sides
    funext a
    have := congr_fun h_eq (σ a)
    simp [ZVector.applyPerm] at this ⊢
    exact this
  · intro j hj
    -- hj : kStepVector w ... = ZVector.applyPerm σ.symm (seq_σ j)
    apply hclose j
    rw [kStepVector_applyPerm, hj]
    funext a; simp [ZVector.applyPerm]

/-! ### Odd-regular data extraction

From the pairwise-MOS hypothesis, extract the generator step k₀, starting position r,
and the non-s count per generator (which is odd). -/


set_option maxHeartbeats 800000 in
/-- Steps 1–3 of the oddRegular → AS proof: from the identified binary MOS,
    extract a generator step `k₀` coprime to n, a starting position `r`, and
    the non-s count `nonS` per k₀-step subword (odd, since `n` is odd).
    At n−1 of the n k₀-step positions, the s-count is `k₀ − nonS`;
    at the closing position, it differs. -/
private lemma oddRegular_kstep_data (w : TernaryNecklace n)
    (hodd : n % 2 = 1) (a b : ℕ)
    (ha_pos : a > 0) (hb_pos : b > 0) (hcop : Nat.Coprime (2 * a) b)
    (hn_eq : n = 2 * a + b)
    (hcountL : Necklace.count w .L = a) (hcountm : Necklace.count w .m = a)
    (hcounts : Necklace.count w .s = b)
    (hmos : isPartialPairwiseMOS w .L .m) :
    ∃ (k₀ : ℕ), Nat.Coprime k₀ n ∧ 0 < k₀ ∧ k₀ < n ∧
    ∃ (r : ℕ) (nonS : ℕ),
      0 < nonS ∧ nonS % 2 = 1 ∧ nonS ≤ k₀ ∧
      (↑nonS * ↑b - ↑(k₀ - nonS) * ↑(2 * a) = (1 : ℤ) ∨
       ↑nonS * ↑b - ↑(k₀ - nonS) * ↑(2 * a) = (-1 : ℤ)) ∧
      (∀ i : Fin (n - 1),
        (Necklace.kStepVector w (r + i.val * k₀) k₀) .s = ↑(k₀ - nonS)) ∧
      (Necklace.kStepVector w (r + (n - 1) * k₀) k₀) .s ≠ ↑(k₀ - nonS) := by
  -- Build the binary MOS bridge
  set B := identifiedToBinary (TernaryNecklace.identifyPair w .L .m) with hB_def
  have hB_mos : BinaryNecklace.isMOS B :=
    identifiedToBinary_isMOS w hcountL hcountm hcounts ha_pos hb_pos hmos
  have hB_countL : Necklace.count B .L = 2 * a :=
    identifiedToBinary_count_L w hcountL hcountm
  have hB_counts : Necklace.count B .s = b :=
    identifiedToBinary_count_s w hcounts
  -- B is primitive since gcd(2a, b) = 1
  have hB_prim : Necklace.isPrimitive B :=
    necklace_with_coprime_sig_is_primitive n (2 * a) b hcop B hB_countL hB_counts
  -- Get generator
  obtain ⟨g, hgen⟩ := allMOSScalesHaveGenerator n B hB_mos
  -- Get k₀ with g occurring at (n-1) positions
  obtain ⟨k₀, hk₀_pos, hk₀_lt_p, hcount_g⟩ :=
    generator_implies_p_minus_one_occurrences B hB_mos.1 g hgen
  have hk₀_lt : k₀ < n := hB_prim ▸ hk₀_lt_p
  -- k₀ is coprime to n
  have hcop_k : Nat.Coprime k₀ n := by
    rw [← hB_prim]
    exact p_minus_one_occurrences_implies_coprime_to_period B hB_mos.1 k₀ hk₀_pos hk₀_lt_p g hcount_g
  -- Determinant condition
  have hdet := generator_det_abs_one B hB_mos.1 hB_prim g hgen
  -- g components are non-negative (they count occurrences in slices)
  have hgL_nn : g .L ≥ 0 := by
    have ⟨_, _, _, hg_app⟩ := hgen.1
    rw [← hg_app]; unfold Necklace.kStepVector ZVector.ofList; exact_mod_cast Nat.zero_le _
  have hgs_nn : g .s ≥ 0 := by
    have ⟨_, _, _, hg_app⟩ := hgen.1
    rw [← hg_app]; unfold Necklace.kStepVector ZVector.ofList; exact_mod_cast Nat.zero_le _
  -- g(.L) + g(.s) = k₀ (binary component sum)
  have hg_sum : g .L + g .s = ↑k₀ := by
    -- g is realized as a k₀-step vector at some position (from countKStepVectorPerPeriod ≥ 1)
    have hn_ge2 : n ≥ 2 := by omega
    -- countKStepVectorPerPeriod = n-1 ≥ 1, so there exists a position where kStepVector = g
    have : ∃ i₀ : ℕ, i₀ < n ∧ Necklace.kStepVector B i₀ k₀ = g := by
      unfold countKStepVectorPerPeriod at hcount_g
      rw [hB_prim] at hcount_g
      by_contra hall; push_neg at hall
      have hzero : (List.range n).countP (fun i => decide (Necklace.kStepVector B i k₀ = g)) = 0 :=
        List.countP_eq_zero.mpr (fun i hi => by simp [hall i (List.mem_range.mp hi)])
      rw [hzero] at hcount_g; omega
    obtain ⟨i₀, _, hi₀_eq⟩ := this
    rw [← hi₀_eq]; exact_mod_cast kStepVector_total_count B i₀ k₀
  -- g(.L) > 0
  have hgL_pos : g .L > 0 := by
    by_contra h; push_neg at h
    have hgL_zero : g .L = 0 := le_antisymm h hgL_nn
    have hgs_k₀ : g .s = ↑k₀ := by linarith
    rw [hgL_zero, hgs_k₀, hB_countL, hB_counts] at hdet
    -- det becomes 0 * b - k₀ * (2*a) = ±1, i.e. -(k₀*(2*a)) = ±1
    rcases hdet with h | h <;> simp only [zero_mul, zero_sub] at h <;>
      nlinarith [show (↑k₀ : ℤ) ≥ 1 from by exact_mod_cast hk₀_pos,
                 show (↑(2 * a) : ℤ) ≥ 2 from by exact_mod_cast (show 2 * a ≥ 2 from by omega)]
  -- g(.L) is odd
  have hgL_odd : g .L % 2 = 1 := by
    -- From det: g(.L) * b - g(.s) * 2a = ±1
    -- g(.L) * b is odd (since ±1 + even = odd)
    -- b is odd (n = 2a + b, n odd, 2a even)
    have hb_odd : b % 2 = 1 := by omega
    -- From det: g(.L) * b - g(.s) * (2a) = ±1
    -- g(.s) * (2a) is even, so g(.L) * b is odd; b is odd, so g(.L) is odd
    rw [hB_countL, hB_counts] at hdet
    have hgLb_odd : g .L * ↑b % 2 = 1 := by
      have hmul : g .s * (↑(2 * a) : ℤ) = 2 * (g .s * ↑a) := by push_cast; ring
      rcases hdet with h | h
      · have heq : g .L * ↑b = 1 + 2 * (g .s * (↑a : ℤ)) := by linarith [hmul]
        rw [heq, Int.add_mul_emod_self_left]; norm_num
      · have heq : g .L * ↑b = -1 + 2 * (g .s * (↑a : ℤ)) := by linarith [hmul]
        rw [heq, Int.add_mul_emod_self_left]; norm_num
    rwa [Int.mul_emod, show (↑b : ℤ) % 2 = 1 from by exact_mod_cast hb_odd,
      mul_one, Int.emod_emod_of_dvd _ (by norm_num : (2 : ℤ) ∣ 2)] at hgLb_odd
  -- Set nonS
  set nonS := (g .L).natAbs with hnonS_def
  have hnonS_eq : (g .L) = ↑nonS := by rw [hnonS_def, Int.natAbs_of_nonneg hgL_nn.le]
  have hnonS_pos : 0 < nonS := by
    have : (0 : ℤ) < ↑nonS := by rw [← hnonS_eq]; exact hgL_pos
    exact_mod_cast this
  have hnonS_odd : nonS % 2 = 1 := by
    have : (↑nonS : ℤ) % 2 = 1 := by rw [← hnonS_eq]; exact hgL_odd
    exact_mod_cast this
  have hnonS_le : nonS ≤ k₀ := by
    have : (↑nonS : ℤ) ≤ ↑k₀ := by rw [← hnonS_eq]; linarith
    exact_mod_cast this
  -- g(.s) = k₀ - nonS
  have hgs_eq : g .s = ↑(k₀ - nonS) := by
    have : g .s = ↑k₀ - ↑nonS := by linarith [hg_sum, hnonS_eq]
    rw [this]; omega
  -- The bridge: kStepVector w i k₀ .s = kStepVector B i k₀ .s
  have hbridge : ∀ i, Necklace.kStepVector B i k₀ .s = Necklace.kStepVector w i k₀ .s :=
    fun i => identifiedToBinary_kStepVector_s w i k₀
  -- Setup for finding positions
  have hn_pos : 0 < n := by omega
  have hpLen : (Necklace.period B).length = n := hB_prim
  -- k₀ is invertible in ZMod n
  have hbez : (↑(Nat.gcd k₀ n) : ZMod n) =
      (↑k₀ : ZMod n) * ((Nat.gcdA k₀ n : ℤ) : ZMod n) := by
    have := congr_arg (fun x : ℤ => (x : ZMod n)) (Nat.gcd_eq_gcd_ab k₀ n)
    push_cast at this; rwa [ZMod.natCast_self, zero_mul, add_zero] at this
  have hk₀_inv : (↑k₀ : ZMod n) * ((Nat.gcdA k₀ n : ℤ) : ZMod n) = 1 := by
    rw [← hbez, hcop_k]; simp
  set c := ((Nat.gcdA k₀ n : ℤ) : ZMod n) with hc_def
  have hck₀ : c * (↑k₀ : ZMod n) = 1 := by rw [mul_comm]; exact hk₀_inv
  -- For any m < n, find t < n with m = (r₀ + t*k₀) % n (for any starting r₀)
  -- Choose r₀ via the closing position
  -- First find the unique bad position using countKStepVector_eq_of_unique_mismatch-style reasoning
  -- We use: at n-1 positions kStepVector = g, at 1 position it differs
  -- Recover stacking positions
  have hRecover : ∀ (r₀ : ℕ) (m : ℕ), m < n →
      ∃ t, t < n ∧ m = (r₀ + t * k₀) % n := by
    intro r₀ m hm
    set t₀ := ZMod.val (((↑m : ZMod n) - (↑r₀ : ZMod n)) * c) with ht₀_def
    refine ⟨t₀, ZMod.val_lt _, ?_⟩
    suffices h : (↑(r₀ + t₀ * k₀) : ZMod n) = (↑m : ZMod n) by
      have := congr_arg ZMod.val h
      simp only [ZMod.val_natCast] at this
      rw [Nat.mod_eq_of_lt hm] at this; exact this.symm
    push_cast
    rw [show (t₀ : ZMod n) = ((↑m : ZMod n) - (↑r₀ : ZMod n)) * c from
      ZMod.natCast_zmod_val _]
    calc (↑r₀ : ZMod n) + ((↑m - ↑r₀) * c) * ↑k₀
        = ↑r₀ + (↑m - ↑r₀) * (c * ↑k₀) := by ring
      _ = ↑r₀ + (↑m - ↑r₀) * 1 := by rw [hck₀]
      _ = ↑m := by ring
  -- All positions: kStepVector B i k₀ ∈ {g, g'} for some g'
  -- At n-1 of n positions, kStepVector = g (from hcount_g)
  -- Set r so the bad position is at stacking index n-1
  -- First, find which positions are good vs bad
  -- Every position j < n has kStepVector B j k₀ = g or ≠ g
  -- From count = n-1, exactly one is bad
  -- Choose r = (bad_pos + k₀) % n so bad_pos = (r + (n-1)*k₀) % n
  -- Approach: pick any r₀ = 0, classify all stacking positions
  have hgood_at : ∀ j : ℕ, j < n → Necklace.kStepVector B j k₀ = g →
      Necklace.kStepVector w j k₀ .s = ↑(k₀ - nonS) := by
    intro j _ hj_eq
    rw [← hbridge, ← hgs_eq]; exact congr_fun hj_eq .s
  -- The closing vector's .s component differs from g.s
  -- Sum formula: ∑_{j<n} kStepVector B j k₀ .s = k₀ * b
  have hsum : ((List.range n).map (fun j => Necklace.kStepVector B j k₀ .s)).sum = ↑k₀ * ↑b := by
    have h := kStepVector_lettercount_sum_over_period B k₀ hk₀_pos hk₀_lt_p .s
    rw [hpLen] at h
    rw [h, period_vector_eq_count B hB_prim .s, hB_counts]
  -- At the bad position, .s ≠ g.s (from det condition)
  have hbad_s : ∀ j : ℕ, j < n → Necklace.kStepVector B j k₀ ≠ g →
      Necklace.kStepVector B j k₀ .s ≠ g .s := by
    intro j _ hj_ne hj_eq
    apply hj_ne
    -- Binary vectors with same .s and same total are equal
    have hj_total : (Necklace.kStepVector B j k₀) .L + (Necklace.kStepVector B j k₀) .s = ↑k₀ :=
      by exact_mod_cast kStepVector_total_count B j k₀
    have hL_eq : (Necklace.kStepVector B j k₀) .L = g .L := by linarith [hg_sum]
    exact funext fun a => by cases a <;> [exact hL_eq; exact hj_eq]
  -- Find bad position and set r
  have hbad : ∃ i₀ : ℕ, i₀ < n ∧ Necklace.kStepVector B i₀ k₀ ≠ g ∧
      (∀ j : ℕ, j < n → j ≠ i₀ → Necklace.kStepVector B j k₀ = g) := by
    -- countP = n - 1 means exactly 1 of n positions has kStepVector ≠ g
    unfold countKStepVectorPerPeriod at hcount_g; rw [hpLen] at hcount_g
    -- There exists a bad position (otherwise count = n, contradicting n - 1)
    have hexists_bad : ∃ i₀, i₀ < n ∧ Necklace.kStepVector B i₀ k₀ ≠ g := by
      by_contra hall; push_neg at hall
      have h := List.countP_eq_length.mpr (fun i hi => by
        exact decide_eq_true_eq.mpr (hall i (List.mem_range.mp hi)))
      rw [List.length_range] at h; rw [h] at hcount_g; omega
    obtain ⟨i₀, hi₀_lt, hi₀_bad⟩ := hexists_bad
    refine ⟨i₀, hi₀_lt, hi₀_bad, fun j hj hne => ?_⟩
    -- All other positions must be good (otherwise countP ≤ n - 2)
    by_contra hj_bad
    set p := fun i => decide (Necklace.kStepVector B i k₀ = g)
    -- Normalize hcount_g to remove internal let binding from unfold
    have hcg : (List.range n).countP p = n - 1 := hcount_g
    have hp_i₀ : p i₀ = false := by simp [p, hi₀_bad]
    have hp_j : p j = false := by simp [p, hj_bad]
    have hi₀_mem : i₀ ∈ List.range n := List.mem_range.mpr hi₀_lt
    have hj_mem : j ∈ List.range n := List.mem_range.mpr hj
    -- Erase j: countP p doesn't change (since p j = false)
    have h1 : ((List.range n).erase j).countP p =
        (List.range n).countP p := by
      rw [List.countP_erase]; simp [hj_mem, hp_j]
    -- Erase j: length decreases by 1
    have h2 : ((List.range n).erase j).length = n - 1 := by
      rw [List.length_erase_of_mem hj_mem, List.length_range]
    -- countP p on erased list ≤ its length
    have h3 : ((List.range n).erase j).countP p ≤ n - 1 := by
      calc ((List.range n).erase j).countP p
          ≤ ((List.range n).erase j).length := List.countP_le_length
        _ = n - 1 := h2
    -- Erase i₀ from the erased list: countP p still doesn't change
    have hi₀_mem' : i₀ ∈ (List.range n).erase j :=
      List.mem_erase_of_ne (Ne.symm hne) |>.mpr hi₀_mem
    have h4 : (((List.range n).erase j).erase i₀).countP p =
        ((List.range n).erase j).countP p := by
      rw [List.countP_erase]; simp [hi₀_mem', hp_i₀]
    have h5 : (((List.range n).erase j).erase i₀).length = n - 2 := by
      rw [List.length_erase_of_mem hi₀_mem', h2]; omega
    have h6 : (List.range n).countP p ≤ n - 2 := by
      calc (List.range n).countP p = ((List.range n).erase j).countP p := h1.symm
        _ = (((List.range n).erase j).erase i₀).countP p := h4.symm
        _ ≤ (((List.range n).erase j).erase i₀).length := List.countP_le_length
        _ = n - 2 := h5
    omega
  obtain ⟨i₀, hi₀_lt, hi₀_bad, hi₀_good⟩ := hbad
  set r := (i₀ + k₀) % n with hr_def
  -- At good positions: use hRecover to map stacking index i to position, then apply hi₀_good
  have hgood : ∀ i : Fin (n - 1),
      (Necklace.kStepVector w (r + i.val * k₀) k₀) .s = ↑(k₀ - nonS) := by
    intro ⟨i, hi⟩
    rw [← hbridge, ← hgs_eq]
    -- kStepVector B (r + i*k₀) k₀ = g
    rw [← kStepVector_mod_n]
    have hmod_lt : (r + i * k₀) % n < n := Nat.mod_lt _ hn_pos
    have hmod_ne : (r + i * k₀) % n ≠ i₀ := by
      intro heq
      -- Goal: derive n | (i + 1), contradicting i < n - 1
      suffices h_dvd : n ∣ (i + 1) by
        exact absurd (Nat.le_of_dvd (by omega) h_dvd) (by omega)
      -- Prove (i+1) % n = 0 via ZMod arithmetic
      suffices h_mod : (i + 1) % n = 0 from Nat.dvd_of_mod_eq_zero h_mod
      -- In ZMod n: ↑(r + i*k₀) = ↑i₀
      have h1 : (↑(r + i * k₀) : ZMod n) = (↑i₀ : ZMod n) := by
        rw [← ZMod.natCast_zmod_val (↑(r + i * k₀) : ZMod n),
            ← ZMod.natCast_zmod_val (↑i₀ : ZMod n)]
        congr 1; simp only [ZMod.val_natCast]
        rwa [Nat.mod_eq_of_lt hi₀_lt]
      -- ↑k₀ * (1 + ↑i) = 0 in ZMod n
      have h2 : (↑k₀ : ZMod n) * (1 + ↑i) = 0 := by
        have h_eq : (↑r : ZMod n) + ↑i * ↑k₀ = ↑i₀ := by push_cast at h1; exact h1
        have hr_eq : (↑r : ZMod n) = ↑i₀ + ↑k₀ := by
          suffices h : (↑r : ZMod n) = (↑(i₀ + k₀) : ZMod n) by rw [h]; push_cast; ring
          rw [← ZMod.natCast_zmod_val (↑r : ZMod n),
              ← ZMod.natCast_zmod_val (↑(i₀ + k₀) : ZMod n)]
          congr 1; simp only [ZMod.val_natCast]
          rw [hr_def]; exact Nat.mod_eq_of_lt (Nat.mod_lt _ hn_pos)
        rw [hr_eq] at h_eq
        linear_combination h_eq
      -- k₀ is a unit, cancel to get 1 + ↑i = 0
      have hu : IsUnit (↑k₀ : ZMod n) := IsUnit.of_mul_eq_one c hk₀_inv
      have h3 : (1 : ZMod n) + ↑i = 0 :=
        hu.mul_left_cancel (h2.trans (mul_zero _).symm)
      -- ↑(i+1) = 0 in ZMod n, so (i+1) % n = 0
      have h4 : (↑(i + 1) : ZMod n) = 0 := by push_cast; linear_combination h3
      have := congr_arg ZMod.val h4
      simp only [ZMod.val_natCast, ZMod.val_zero] at this
      exact this
    exact congr_fun (hi₀_good _ hmod_lt hmod_ne) .s
  -- At closing position: (r + (n-1)*k₀) % n = i₀
  have hr_close : (r + (n - 1) * k₀) % n = i₀ := by
    have h1 : r + (n - 1) * k₀ ≡ i₀ + k₀ + (n - 1) * k₀ [MOD n] :=
      Nat.ModEq.add_right _ (Nat.mod_modEq (i₀ + k₀) n)
    have h2 : i₀ + k₀ + (n - 1) * k₀ = i₀ + n * k₀ := by
      have : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn_pos
      nlinarith
    rw [Nat.ModEq, h2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi₀_lt] at h1
    exact h1
  have hclose : (Necklace.kStepVector w (r + (n - 1) * k₀) k₀) .s ≠ ↑(k₀ - nonS) := by
    rw [← hbridge, ← hgs_eq, ← kStepVector_mod_n, hr_close]
    exact hbad_s i₀ hi₀_lt hi₀_bad
  have hdet_nonS : ↑nonS * ↑b - ↑(k₀ - nonS) * ↑(2 * a) = (1 : ℤ) ∨
      ↑nonS * ↑b - ↑(k₀ - nonS) * ↑(2 * a) = (-1 : ℤ) := by
    rw [hB_countL, hB_counts] at hdet
    rw [← hnonS_eq, ← hgs_eq]; exact hdet
  exact ⟨k₀, hcop_k, hk₀_pos, hk₀_lt, r, nonS, hnonS_pos, hnonS_odd, hnonS_le, hdet_nonS, hgood, hclose⟩

/-! ### Balanced circular MOS is alternating -/

/-- A balanced binary circular MOS of length 2a (a L's, a m's) must be alternating.
    This is the converse of `alternating_circular_mos`. -/
lemma balanced_circular_mos_is_alternating (D : List StepSize) (a : ℕ)
    (ha : a > 0) (hlen : D.length = 2 * a)
    (hbin : ∀ i, (hi : i < D.length) → D[i] = .L ∨ D[i] = .m)
    (hcountL : D.count .L = a) (hcountm : D.count .m = a)
    (hmos : circularHasMOSProperty D) :
    (∀ i, (hi : i < D.length) → D[i] = D[i % 2]'(by omega)) ∧
    D[0]'(by omega) ≠ D[1]'(by omega) := by
  have hlen_pos : 0 < D.length := by omega
  -- Step 1: All consecutive pairs differ
  have hall_diff : ∀ i, (hi : i < D.length) →
      D[i]'(by omega) ≠ D[(i + 1) % D.length]'(Nat.mod_lt _ hlen_pos) := by
    by_contra h_not; push_neg at h_not
    obtain ⟨i₀, hi₀, heq₀⟩ := h_not
    -- a = 1 case: all elements equal → toFinset.card < 2, contradiction
    rcases Nat.eq_or_lt_of_le ha with rfl | ha2
    · have h01 : D[0]'(by omega) = D[1]'(by omega) := by
        have : i₀ < 2 := by omega
        have hlen2 : D.length = 2 := by omega
        interval_cases i₀
        · simpa [hlen2] using heq₀
        · simpa [hlen2] using heq₀.symm
      have : D.toFinset.card < 2 := by
        suffices h : D.toFinset ⊆ {D[0]'(by omega)} by
          exact lt_of_le_of_lt (Finset.card_le_card h) (by simp)
        intro x hx
        simp only [Finset.mem_singleton, List.mem_toFinset] at hx ⊢
        rw [List.mem_iff_getElem] at hx
        obtain ⟨j, hj, rfl⟩ := hx
        have : j < 2 := by omega
        interval_cases j <;> [rfl; exact h01.symm]
      linarith [hmos.2.1]
    · -- a ≥ 2: use k=2 MOS
      have hmos2 := hmos.2.2 2 (by omega) (by omega : 2 < D.length)
      set v := D[i₀]'hi₀ with hv_def
      have hv_bin := hbin i₀ hi₀
      -- D is not constant (has both L and m)
      have h_not_const : ¬ ∀ p, (hp : p < D.length) →
          D[p]'(by omega) = D[(p + 1) % D.length]'(Nat.mod_lt _ hlen_pos) := by
        intro h
        have hconst : ∀ i, (hi : i < D.length) → D[i]'(by omega) = D[0]'(by omega) := by
          intro i hi; induction i with
          | zero => rfl
          | succ n ih =>
            have h_step := h n (by omega)
            simp only [Nat.mod_eq_of_lt (show n + 1 < D.length by omega)] at h_step
            exact h_step.symm.trans (ih (by omega))
        rcases hbin 0 (by omega) with h0 | h0
        · have : D.count .m = 0 := List.count_eq_zero.mpr (fun hmem => by
            rw [List.mem_iff_getElem] at hmem; obtain ⟨j, hj, heqj⟩ := hmem
            have h1 := (hconst j hj).trans h0; rw [heqj] at h1; exact absurd h1 (by decide))
          linarith [hcountm]
        · have : D.count .L = 0 := List.count_eq_zero.mpr (fun hmem => by
            rw [List.mem_iff_getElem] at hmem; obtain ⟨j, hj, heqj⟩ := hmem
            have h1 := (hconst j hj).trans h0; rw [heqj] at h1; exact absurd h1 (by decide))
          linarith [hcountL]
      push_neg at h_not_const
      obtain ⟨p, hp, hne_p⟩ := h_not_const
      -- Case: does an "opposite" same-pair exist?
      by_cases h_opp : ∃ q : Fin D.length,
          D[q.val]'q.isLt ≠ v ∧
          D[q.val]'q.isLt = D[(q.val + 1) % D.length]'(Nat.mod_lt _ hlen_pos)
      · -- 3 distinct k=2 multisets → card ≥ 3 > 2, contradicting MOS
        obtain ⟨⟨q, hq⟩, hqv, heq_q⟩ := h_opp
        exfalso
        -- Simplify k=2 multisets: for i < D.length, the k=2 multiset is ↑[D[i], D[(i+1)%len]]
        have hm_simp : ∀ i, (hi : i < D.length) →
            Multiset.ofList ((List.range 2).map (fun j => D[(i + j) % D.length]!)) =
            ↑[D[i]'hi, D[(i + 1) % D.length]'(Nat.mod_lt _ hlen_pos)] := by
          intro i hi
          have h_gi : D[i]! = D[i]'hi := getElem!_pos D i hi
          have h_gi1 : D[(i + 1) % D.length]! =
              D[(i + 1) % D.length]'(Nat.mod_lt _ hlen_pos) :=
            getElem!_pos D ((i + 1) % D.length) (Nat.mod_lt _ hlen_pos)
          simp only [show List.range 2 = [0, 1] from rfl, List.map_cons,
            List.map_nil, Nat.add_zero, Nat.mod_eq_of_lt hi, h_gi, h_gi1]
        -- The multiset list
        set mlist := (List.range D.length).map (fun i =>
          Multiset.ofList ((List.range 2).map
            (fun j => D[(i + j) % D.length]!))) with hmlist_def
        -- Three multisets: {|v,v|}, {|D[q],D[q]|} (≠v), {|D[p],D[(p+1)%len]|} (different)
        set m₁ : Multiset StepSize := ↑[v, v] with hm₁_eq
        set m₂ : Multiset StepSize := ↑[D[q]'hq, D[q]'hq] with hm₂_eq
        set m₃ : Multiset StepSize :=
          ↑[D[p]'hp, D[(p + 1) % D.length]'(Nat.mod_lt _ hlen_pos)] with hm₃_eq
        -- All 3 in the toFinset
        have hm₁_mem : m₁ ∈ mlist.toFinset := by
          rw [List.mem_toFinset, List.mem_map]
          refine ⟨i₀, List.mem_range.mpr hi₀, ?_⟩
          rw [hm_simp i₀ hi₀, show D[i₀]'hi₀ = v from hv_def.symm,
            show D[(i₀ + 1) % D.length]'_ = v from heq₀.symm.trans hv_def.symm]
        have hm₂_mem : m₂ ∈ mlist.toFinset := by
          rw [List.mem_toFinset, List.mem_map]
          refine ⟨q, List.mem_range.mpr hq, ?_⟩
          rw [hm_simp q hq, show D[(q+1) % D.length]'_ = D[q]'hq from heq_q.symm]
        have hm₃_mem : m₃ ∈ mlist.toFinset := by
          rw [List.mem_toFinset, List.mem_map]
          exact ⟨p, List.mem_range.mpr hp, hm_simp p hp⟩
        -- Pairwise distinct
        have h12 : m₁ ≠ m₂ := by
          intro h; have hv_mem : v ∈ m₁ := by simp [m₁]
          rw [h] at hv_mem; simp [m₂] at hv_mem; exact hqv hv_mem.symm
        have h13 : m₁ ≠ m₃ := by
          intro h; rw [hm₁_eq, hm₃_eq, Multiset.coe_eq_coe] at h
          exact absurd (h.nodup_iff.mpr (by simp [List.nodup_cons, hne_p]))
            (by simp [List.nodup_cons])
        have h23 : m₂ ≠ m₃ := by
          intro h; rw [hm₂_eq, hm₃_eq, Multiset.coe_eq_coe] at h
          exact absurd (h.nodup_iff.mpr (by simp [List.nodup_cons, hne_p]))
            (by simp [List.nodup_cons])
        -- Card ≥ 3, contradicting hmos2 (≤ 2)
        have hsub : ({m₁, m₂, m₃} : Finset _) ⊆ mlist.toFinset := by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl <;> assumption
        have hcard : 3 ≤ mlist.toFinset.card := by
          have h3 : ({m₁, m₂, m₃} : Finset _).card = 3 := by
            rw [Finset.card_insert_of_notMem (by simp [h12, h13]),
              Finset.card_insert_of_notMem (by simp [h23]),
              Finset.card_singleton]
          linarith [Finset.card_le_card hsub]
        linarith [hmos2]
      · -- No opposite same-pair: every non-v value is followed by v
        push_neg at h_opp
        have hfollowed : ∀ j, (hj : j < D.length) → D[j]'(by omega) ≠ v →
            D[(j + 1) % D.length]'(Nat.mod_lt _ hlen_pos) = v := by
          intro j hj hne
          by_contra h
          have hDj := hbin j hj
          have hDj1 := hbin ((j + 1) % D.length) (Nat.mod_lt _ hlen_pos)
          have heq : D[j]'hj = D[(j + 1) % D.length]'(Nat.mod_lt _ hlen_pos) := by
            rcases hv_bin with hv | hv <;> rcases hDj with h1 | h1 <;>
              rcases hDj1 with h2 | h2 <;> simp_all
          exact absurd heq (h_opp ⟨j, hj⟩ hne)
        -- Injection argument: non-v positions → v positions via successor.
        -- Count of v is a
        have hcountv : D.count v = a := by
          rcases hv_bin with hv | hv <;> rwa [hv_def, hv]
        -- Position (i₀+1)%len also has value v
        have hi₀_succ_v : D[(i₀ + 1) % D.length]'(Nat.mod_lt _ hlen_pos) = v :=
          heq₀.symm.trans hv_def.symm
        -- Use Fin D.length for positions
        set nonV := (Finset.univ : Finset (Fin D.length)).filter
          (fun j => D[j.val] ≠ v) with hnonV_def
        set vSet := (Finset.univ : Finset (Fin D.length)).filter
          (fun j => D[j.val] = v) with hvSet_def
        -- The successor map (mod len) sends non-v into v
        set f : Fin D.length → Fin D.length :=
          fun j => ⟨(j.val + 1) % D.length, Nat.mod_lt _ hlen_pos⟩ with hf_def
        have hf_maps : ∀ j ∈ nonV, f j ∈ vSet := by
          intro j hj
          rw [hnonV_def, Finset.mem_filter] at hj
          rw [hvSet_def, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hfollowed j.val j.isLt hj.2⟩
        -- The map f is injective on nonV
        have hf_inj : Set.InjOn f ↑nonV := by
          intro j₁ _ j₂ _ heq_f
          have h := congr_arg Fin.val heq_f
          simp only [hf_def, Fin.val_mk] at h
          -- h : (j₁.val+1) % len = (j₂.val+1) % len → j₁ = j₂
          have hmod : j₁.val ≡ j₂.val [MOD D.length] :=
            Nat.ModEq.add_right_cancel' 1 (h : j₁.val + 1 ≡ j₂.val + 1 [MOD D.length])
          rw [Nat.ModEq, Nat.mod_eq_of_lt j₁.isLt, Nat.mod_eq_of_lt j₂.isLt] at hmod
          exact Fin.ext hmod
        -- Position (i₀+1)%len is in vSet but not in image of f on nonV
        have hi₀_succ_fin : (⟨(i₀ + 1) % D.length, Nat.mod_lt _ hlen_pos⟩ : Fin D.length) ∈ vSet := by
          rw [hvSet_def, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hi₀_succ_v⟩
        have hi₀_not_img :
            (⟨(i₀ + 1) % D.length, Nat.mod_lt _ hlen_pos⟩ : Fin D.length) ∉
            Finset.image f nonV := by
          intro hmem
          rw [Finset.mem_image] at hmem
          obtain ⟨j, hj_mem, hj_eq⟩ := hmem
          rw [hnonV_def, Finset.mem_filter] at hj_mem
          have hval_eq : j.val = i₀ := by
            have h : (j.val + 1) % D.length = (i₀ + 1) % D.length := by
              have := congr_arg Fin.val hj_eq; simp only [hf_def, Fin.val_mk] at this; exact this
            have hmod : j.val ≡ i₀ [MOD D.length] :=
              Nat.ModEq.add_right_cancel' 1 h
            rwa [Nat.ModEq, Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt hi₀] at hmod
          exact hj_mem.2 (by simp only [hval_eq, hv_def])
        -- So nonV.card < vSet.card
        have hcard_strict : nonV.card < vSet.card := by
          calc nonV.card
              = (Finset.image f nonV).card := (Finset.card_image_of_injOn hf_inj).symm
            _ < vSet.card := Finset.card_lt_card
                (Finset.ssubset_iff_of_subset (Finset.image_subset_iff.mpr hf_maps)
                  |>.mpr ⟨_, hi₀_succ_fin, hi₀_not_img⟩)
        -- Partition: nonV.card + vSet.card = D.length
        have hpartition : nonV.card + vSet.card = D.length := by
          have h1 : vSet.card + nonV.card =
              (Finset.univ : Finset (Fin D.length)).card :=
            Finset.card_filter_add_card_filter_not _
          simp only [Finset.card_univ, Fintype.card_fin] at h1; omega
        -- Count v positions = a
        have hv_count : vSet.card = a := by
          rw [← hcountv, hvSet_def, Finset.card_def, Finset.filter_val,
            Finset.val_univ_fin, Multiset.filter_coe, Multiset.coe_card,
            ← List.countP_eq_length_filter, List.count_eq_countP]
          conv_rhs => rw [← List.map_getElem_finRange D]
          rw [List.countP_map]; congr 1
        omega
  -- Step 2: Period 2 (binary + all-diff → D[j+2] = D[j])
  have hperiod2 : ∀ j, (hj : j + 2 < D.length) → D[j + 2]'(by omega) = D[j]'(by omega) := by
    intro j hj
    have hd1 := hall_diff j (by omega)
    simp only [Nat.mod_eq_of_lt (show j + 1 < D.length by omega)] at hd1
    have hd2 := hall_diff (j + 1) (by omega)
    simp only [show (j + 1 + 1) % D.length = j + 2 from Nat.mod_eq_of_lt (by omega)] at hd2
    rcases hbin j (by omega), hbin (j + 1) (by omega), hbin (j + 2) (by omega) with
      ⟨hj0 | hj0, hj1 | hj1, hj2 | hj2⟩ <;> simp_all
  constructor
  · -- Strong induction: D[i] = D[i % 2]
    intro i hi
    exact Nat.strongRecOn i (fun n ih => by
      intro hn; match n with
      | 0 => rfl
      | 1 => rfl
      | m + 2 =>
        rw [hperiod2 m (by omega), ih m (by omega) (by omega)]
        congr 1; omega) hi
  · have h := hall_diff 0 (by omega)
    simp only [Nat.zero_add, Nat.mod_eq_of_lt (show 1 < D.length by omega)] at h
    exact h

/-- Filtering preserves counts of other letters:
    `(orderedDeletion w x).count y = Necklace.count w y` when `y ≠ x`. -/
lemma orderedDeletion_count_ne (w : TernaryNecklace n) (x y : StepSize)
    (hne : y ≠ x) :
    (TernaryNecklace.orderedDeletion w x).count y = Necklace.count w y := by
  unfold TernaryNecklace.orderedDeletion Necklace.count
  -- Normalize monadic elaboration
  have heq : ∀ (l : List ℕ), (do let a ← l; pure (↑a : ZMod n)) =
      l.map (Nat.cast : ℕ → ZMod n) := by
    intro l; induction l with
    | nil => rfl
    | cons a l ih => simp only [List.map_cons]; exact congrArg _ ih
  simp only [heq, List.map_map]
  set wList := (List.range n).map (w ∘ (Nat.cast : ℕ → ZMod n))
  -- LHS: count y in (wList.filter (· ≠ x))
  -- Since y ≠ x, filtering out x doesn't remove any y's
  -- Use Multiset.count_filter_of_pos via coercion
  have hmulti : Multiset.count y (Multiset.filter (· ≠ x) (↑wList : Multiset StepSize)) =
      Multiset.count y ↑wList :=
    Multiset.count_filter_of_pos hne
  rw [← Multiset.coe_count, ← Multiset.filter_coe, hmulti, Multiset.coe_count]
  -- Goal: wList.count y = (Finset.filter (fun i => w i = y) Finset.univ).card
  -- wList.count y counts positions i < n where w(↑i) = y
  rw [List.count_eq_countP, List.countP_eq_length_filter, List.filter_map,
      List.length_map]
  -- ((List.range n).filter ((· == y) ∘ w ∘ Nat.cast)).length = Finset.card ...
  rw [← List.toFinset_card_of_nodup (List.Nodup.filter _ List.nodup_range),
      List.toFinset_filter, List.toFinset_range]
  apply Finset.card_bij (fun i _hi => ((i : ℕ) : ZMod n))
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, Function.comp,
      BEq.beq, decide_eq_true_eq, true_and] at hi ⊢
    exact hi.2
  · intro i₁ hi₁ i₂ hi₂ h
    have h1 := (Finset.mem_filter.mp hi₁).1; rw [Finset.mem_range] at h1
    have h2 := (Finset.mem_filter.mp hi₂).1; rw [Finset.mem_range] at h2
    have := congr_arg ZMod.val h
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨ZMod.val j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt j), ?_⟩,
      ZMod.natCast_zmod_val j⟩
    simp only [Function.comp, BEq.beq, decide_eq_true_eq, ZMod.natCast_zmod_val]
    exact hj

/-! ### AS construction from generator data + deletion MOS

Given the generator step data and the deletion MOS, construct the alternating sequence. -/

/-- The non-.s filter length of a k₀-step slice equals nonS when the .s count is k₀ - nonS. -/
lemma nonS_filter_length (w : TernaryNecklace n) (i k₀ nonS : ℕ)
    (hs : (Necklace.kStepVector w i k₀) .s = ↑(k₀ - nonS)) (hle : nonS ≤ k₀) :
    ((Necklace.slice w i (i + k₀)).filter (· ≠ .s)).length = nonS := by
  -- kStepVector .s = (slice.filter (· == .s)).length
  have hslice_len : (Necklace.slice w i (i + k₀)).length = k₀ := by
    rw [Necklace.slice_length]; omega
  have hs_count : ((Necklace.slice w i (i + k₀)).filter (· == .s)).length = k₀ - nonS := by
    have : (Necklace.kStepVector w i k₀ .s) = ↑((Necklace.slice w i (i + k₀)).filter
        (· == StepSize.s)).length := by
      unfold Necklace.kStepVector ZVector.ofList; simp
    rw [this] at hs; exact_mod_cast hs
  -- complement: filter_ne + filter_eq = total length
  have hcomp := List.length_eq_length_filter_add (fun x => !decide (x = StepSize.s))
    (l := Necklace.slice w i (i + k₀))
  simp only [Bool.not_not] at hcomp
  -- (· ≠ .s) filter uses `decide (x ≠ .s)` = `!decide (x = .s)` = `!(x == .s)`
  -- Need to connect the two filter forms
  have h1 : (Necklace.slice w i (i + k₀)).filter (fun x => !decide (x = StepSize.s)) =
      (Necklace.slice w i (i + k₀)).filter (· ≠ .s) := by
    congr 1; ext x; simp [ne_eq]
  have h2 : (Necklace.slice w i (i + k₀)).filter (fun x => decide (x = StepSize.s)) =
      (Necklace.slice w i (i + k₀)).filter (· == .s) := by
    congr 1
  rw [h1, h2] at hcomp
  omega

/-- In an alternating word D (D[i] = D[i%2], D[0] ≠ D[1]) of length 2a,
    the nonS-step L-count depends only on the starting parity q % 2.
    Moreover the two parities give values differing by 1. -/
private lemma alternating_nonS_window_Lcount (D : List StepSize) (a nonS : ℕ)
    (ha : a > 0) (hlen : D.length = 2 * a)
    (halt : ∀ i, (hi : i < D.length) → D[i] = D[i % 2]'(by omega))
    (_ : D[0]'(by omega) ≠ D[1]'(by omega))
    (_ : 0 < nonS) (_ : nonS % 2 = 1) (_ : nonS < 2 * a)
    (q : ℕ) :
    ((List.range nonS).map (fun t =>
      D[(q + t) % D.length]'(Nat.mod_lt _ (by omega)))).count .L =
    ((List.range nonS).map (fun t =>
      D[(q % 2 + t) % D.length]'(Nat.mod_lt _ (by omega)))).count .L := by
  congr 1
  apply List.map_congr_left
  intro t _
  have hdvd : 2 ∣ D.length := ⟨a, hlen⟩
  have h_idx_eq : (q + t) % D.length % 2 = (q % 2 + t) % D.length % 2 := by
    simp only [Nat.mod_mod_of_dvd _ hdvd, Nat.add_mod, Nat.mod_mod]
  have h1 := halt ((q + t) % D.length) (Nat.mod_lt _ (by omega))
  have h2 := halt ((q % 2 + t) % D.length) (Nat.mod_lt _ (by omega))
  simp only [h1, h2, h_idx_eq]

/-- In an alternating word D (D[i] = D[i%2], D[0] ≠ D[1]) of length 2a,
    L-counts in windows of odd size `nonS` at positions 0 and 1 differ by exactly 1. -/
private lemma alternating_window_Lcount_abs_diff (D : List StepSize) (a nonS : ℕ)
    (ha : a > 0) (hlen : D.length = 2 * a)
    (halt : ∀ i, (hi : i < D.length) → D[i] = D[i % 2]'(by omega))
    (hne : D[0]'(by omega) ≠ D[1]'(by omega))
    (hbin : ∀ i, (hi : i < D.length) → D[i] = .L ∨ D[i] = .m)
    (hnonS_pos : 0 < nonS) (hnonS_odd : nonS % 2 = 1) (_ : nonS < 2 * a)
    (nWLc : ℕ → ℕ)
    (hDlen_pos : 0 < D.length)
    (hnWLc : nWLc = fun q => ((List.range nonS).map (fun t =>
      D[(q + t) % D.length]'(Nat.mod_lt _ hDlen_pos))).count .L) :
    (nWLc 0 : ℤ) - (nWLc 1 : ℤ) = 1 ∨ (nWLc 0 : ℤ) - (nWLc 1 : ℤ) = -1 := by
  subst hnWLc
  have hdvd : 2 ∣ D.length := ⟨a, hlen⟩
  -- Simplify: D[(q+t)%len] = D[(q+t)%2]
  have hsimp : ∀ q t, D[(q + t) % D.length]'(Nat.mod_lt _ hDlen_pos) =
      D[(q + t) % 2]'(by omega) := by
    intro q t
    have h1 := halt ((q + t) % D.length) (Nat.mod_lt _ hDlen_pos)
    simp only [Nat.mod_mod_of_dvd _ hdvd] at h1
    exact h1
  -- Simplify both counts to use D[(q+t)%2]
  have hcount_simp : ∀ q, ((List.range nonS).map (fun t =>
      D[(q + t) % D.length]'(Nat.mod_lt _ hDlen_pos))).count .L =
      ((List.range nonS).map (fun t => D[(q + t) % 2]'(by omega))).count .L := by
    intro q; congr 1; apply List.map_congr_left; intro t _; exact hsimp q t
  simp only [hcount_simp]
  -- Window 0 = D[0] :: middle, Window 1 = middle ++ [D[1]], so counts differ by endpoints.
  -- Define the shared middle count
  set mid := ((List.range (nonS - 1)).map (fun t =>
    D[(1 + t) % 2]'(by omega))).count .L with hmid_def
  -- Head decomposition for window 0: range nonS = 0 :: map succ (range (nonS-1))
  have hc0 : ((List.range nonS).map (fun t =>
      D[(0 + t) % 2]'(by omega))).count .L =
      mid + (if D[0]'(by omega) == .L then 1 else 0) := by
    conv_lhs => rw [show nonS = (nonS - 1) + 1 from by omega, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.count_cons]
    congr 1; rw [hmid_def]
    -- Middle counts match: (0 + (t+1)) % 2 = (1 + t) % 2
    congr 1; apply List.map_congr_left; intro t _
    dsimp only [Function.comp]
    show D[(0 + (t + 1)) % 2]'(by omega) = D[(1 + t) % 2]'(by omega)
    simp only [show (0 : ℕ) + (t + 1) = 1 + t from by omega]
  -- Tail decomposition for window 1: range nonS = range (nonS-1) ++ [nonS-1]
  have hc1 : ((List.range nonS).map (fun t =>
      D[(1 + t) % 2]'(by omega))).count .L =
      mid + (if D[1]'(by omega) == .L then 1 else 0) := by
    conv_lhs => rw [show nonS = (nonS - 1) + 1 from by omega, List.range_succ]
    simp only [List.map_append, List.map_singleton, List.count_append,
      show (1 + (nonS - 1)) % 2 = 1 from by omega]
    simp only [List.count_cons, List.count_nil, Nat.zero_add]
    rfl
  rw [hc0, hc1]
  -- Case split on D[0] and D[1]
  rcases hbin 0 (by omega) with h0 | h0 <;> rcases hbin 1 (by omega) with h1 | h1
  · exact absurd (by rw [h0, h1]) hne
  · left; simp [h0, h1]
  · right; simp [h0, h1]
  · exact absurd (by rw [h0, h1]) hne

/-- In an alternating circular word D of length 2a (D[i] = D[i%2], D[0] ≠ D[1], binary),
    a contiguous window of even length 2j has exactly j entries equal to .L. -/
lemma alternating_even_window_Lcount (D : List StepSize) (a j : ℕ)
    (ha : a > 0) (hlen : D.length = 2 * a)
    (halt : ∀ i, (hi : i < D.length) → D[i] = D[i % 2]'(by omega))
    (hne : D[0]'(by omega) ≠ D[1]'(by omega))
    (hbin : ∀ i, (hi : i < D.length) → D[i] = .L ∨ D[i] = .m)
    (q : ℕ) (hDlen_pos : 0 < D.length) :
    ((List.range (2 * j)).map (fun t =>
      D[(q + t) % D.length]'(Nat.mod_lt _ hDlen_pos))).count .L = j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 from by ring,
        List.range_succ, List.range_succ, List.map_append, List.map_append,
        List.count_append, List.count_append,
        List.map_singleton, List.map_singleton,
        ih]
    simp only [List.count_singleton]
    -- Helper: equal indices give equal getElem (handling dependent proof)
    have idx_eq : ∀ (i j : ℕ) (hi : i < D.length) (hj : j < D.length),
        i = j → D[i]'hi = D[j]'hj := by
      intro i j hi hj h; subst h; rfl
    have hdvd : 2 ∣ D.length := ⟨a, hlen⟩
    have hpar0 : (q + (2 * j)) % D.length % 2 = q % 2 := by
      rw [Nat.mod_mod_of_dvd _ hdvd]; omega
    have hpar1 : (q + (2 * j + 1)) % D.length % 2 = (q + 1) % 2 := by
      rw [Nat.mod_mod_of_dvd _ hdvd]; omega
    have hq_lt : q % 2 < D.length := by omega
    have hq1_lt : (q + 1) % 2 < D.length := by omega
    have hmod0_lt : (q + 2 * j) % D.length < D.length := Nat.mod_lt _ hDlen_pos
    have hmod1_lt : (q + (2 * j + 1)) % D.length < D.length := Nat.mod_lt _ hDlen_pos
    -- Chain halt + idx_eq to relate D[(q+2j)%len] to D[q%2]
    have h0 : D[(q + 2 * j) % D.length]'hmod0_lt = D[q % 2]'hq_lt :=
      (halt _ hmod0_lt).trans (idx_eq _ _ _ hq_lt hpar0)
    have h1 : D[(q + (2 * j + 1)) % D.length]'hmod1_lt = D[(q + 1) % 2]'hq1_lt :=
      (halt _ hmod1_lt).trans (idx_eq _ _ _ hq1_lt hpar1)
    -- Rewrite in goal (safe: abstracting over StepSize values, not indices)
    rw [h0, h1]
    -- D[q%2] and D[(q+1)%2] are different, one is .L one is .m
    have hne' : D[q % 2]'hq_lt ≠ D[(q + 1) % 2]'hq1_lt := by
      rcases Nat.mod_two_eq_zero_or_one q with hq | hq
      · exact (idx_eq _ _ hq_lt (by omega) hq).symm ▸
          (idx_eq _ _ hq1_lt (by omega) (show (q+1)%2 = 1 by omega)).symm ▸ hne
      · exact (idx_eq _ _ hq_lt (by omega) hq).symm ▸
          (idx_eq _ _ hq1_lt (by omega) (show (q+1)%2 = 0 by omega)).symm ▸ hne.symm
    rcases hbin (q % 2) hq_lt with hL | hm
    · rcases hbin ((q + 1) % 2) hq1_lt with hL' | hm'
      · exact absurd (hL.trans hL'.symm) hne'
      · simp [hL, hm']
    · rcases hbin ((q + 1) % 2) hq1_lt with hL' | hm'
      · simp [hm, hL']
      · exact absurd (hm.trans hm'.symm) hne'

/-- Steps 4–6 of the oddRegular → AS proof: from the generator step data
    (constant s-count at n−1 positions, different at the closing position) and the
    deletion MOS (which forces the deletion word to alternate), construct the AS.

    The key insight is that k₀-step windows are adjacent in w, so the non-s positions
    in each window form a contiguous block of odd length `nonS` in the alternating
    deletion word. Since `nonS` is odd, the L-count alternates between `⌈nonS/2⌉`
    and `⌊nonS/2⌋` at consecutive windows. -/
private lemma oddRegular_construct_AS (w : TernaryNecklace n)
    (_hodd : n % 2 = 1) (a b : ℕ)
    (_ha_pos : a > 0) (_hn_eq : n = 2 * a + b)
    (_hcountL : Necklace.count w .L = a) (_hcountm : Necklace.count w .m = a)
    (_hcounts : Necklace.count w .s = b)
    (_hdel : isPartialDeletionMOS w .s)
    (k₀ : ℕ) (hcop_k : Nat.Coprime k₀ n) (_hk₀_pos : 0 < k₀) (_hk₀_lt : k₀ < n)
    (r nonS : ℕ) (_hnonS_pos : 0 < nonS) (_hnonS_odd : nonS % 2 = 1) (_hnonS_le : nonS ≤ k₀)
    (hs_count : ∀ i : Fin (n - 1),
      (Necklace.kStepVector w (r + i.val * k₀) k₀) .s = ↑(k₀ - nonS))
    (hs_close : (Necklace.kStepVector w (r + (n - 1) * k₀) k₀) .s ≠ ↑(k₀ - nonS)) :
    (∀ i : Fin (n - 1), Necklace.kStepVector w (r + i.val * k₀) k₀ =
      Necklace.kStepVector w (r + (i.val % 2) * k₀) k₀) ∧
    (Necklace.kStepVector w (r + 0 * k₀) k₀ .L -
      Necklace.kStepVector w (r + 1 * k₀) k₀ .L = 1 ∨
     Necklace.kStepVector w (r + 0 * k₀) k₀ .L -
      Necklace.kStepVector w (r + 1 * k₀) k₀ .L = -1) ∧
    hasAS w := by
  -- n ≥ 3 (odd, n = 2a+b, a>0, b>0 → n ≥ 3)
  have hn_pos : 0 < n := by omega
  have hn_ge3 : n ≥ 3 := by omega
  -- Set up deletion word
  set D := TernaryNecklace.orderedDeletion w .s with hD_def
  have hDlen : D.length = 2 * a := by
    have hdel : D.length + Necklace.count w .s = n := orderedDeletion_length w .s
    rw [_hcounts] at hdel; omega
  have hDlen_pos : 0 < D.length := by omega
  -- D entries are .L or .m
  have hmem_ne_s : ∀ a ∈ D, a ≠ .s := fun a ha => by
    simp only [D, TernaryNecklace.orderedDeletion, List.mem_filter,
      decide_eq_true_eq] at ha; exact ha.2
  have hbin : ∀ i, (hi : i < D.length) → D[i] = .L ∨ D[i] = .m := by
    intro i hi
    have hne : D[i] ≠ .s := hmem_ne_s _ (List.getElem_mem hi)
    cases h : D[i] with
    | L => exact Or.inl rfl
    | m => exact Or.inr rfl
    | s => exact absurd h hne
  -- D has count a of each letter
  have hDcountL : D.count .L = a := by
    rw [hD_def, orderedDeletion_count_ne w .s .L (by decide)]; exact _hcountL
  have hDcountm : D.count .m = a := by
    rw [hD_def, orderedDeletion_count_ne w .s .m (by decide)]; exact _hcountm
  -- D is alternating (balanced_circular_mos_is_alternating)
  obtain ⟨halt, hne⟩ := balanced_circular_mos_is_alternating D a _ha_pos hDlen
    hbin hDcountL hDcountm _hdel
  -- nonS < 2a: nonS is odd but 2a is even, so nonS ≠ 2a.
  -- And nonS ≤ 2a from the sum formula + s' ≤ k₀ ≤ n-1.
  have hnonS_lt : nonS < 2 * a := by
    -- Use parity: nonS odd, 2a even → nonS ≠ 2a → suffices nonS ≤ 2a
    suffices h : nonS ≤ 2 * a by omega
    -- Sum formula: ∑ i, kStepVector .s = k₀ * count .s = k₀ * b
    have hsum := kStepVector_lettercount_sum w k₀ .s
    rw [_hcounts] at hsum
    -- The stacking positions r+i*k₀ (i=0..n-1) biject onto 0..n-1 by coprimality.
    -- Reindex: ∑ j=0..n-1, kStepVector(r+j*k₀) = ∑ i=0..n-1, kStepVector(i).
    have hreindex : ∑ j ∈ Finset.range n, Necklace.kStepVector w (r + j * k₀) k₀ .s =
        ∑ i ∈ Finset.range n, Necklace.kStepVector w i k₀ .s := by
      apply Finset.sum_nbij (fun j => (r + j * k₀) % n)
      · intro j _; exact Finset.mem_range.mpr (Nat.mod_lt _ hn_pos)
      · intro j₁ hj₁ j₂ hj₂ heq
        simp only [Finset.mem_coe, Finset.mem_range] at hj₁ hj₂
        have h1 : ((r + j₁ * k₀ : ℕ) : ZMod n) = ((r + j₂ * k₀ : ℕ) : ZMod n) := by
          rw [← ZMod.natCast_zmod_val (↑(r + j₁ * k₀) : ZMod n),
              ← ZMod.natCast_zmod_val (↑(r + j₂ * k₀) : ZMod n)]
          congr 1; simp only [ZMod.val_natCast]; exact heq
        have h2 : (↑k₀ : ZMod n) * (↑j₁ - ↑j₂) = 0 := by push_cast at h1 ⊢; linear_combination h1
        have hunit : IsUnit (↑k₀ : ZMod n) :=
          (ZMod.unitOfCoprime k₀ hcop_k).isUnit
        have h3 : (↑j₁ : ZMod n) = ↑j₂ := by
          by_contra h; have : (↑j₁ : ZMod n) - ↑j₂ ≠ 0 := sub_ne_zero.mpr h
          exact absurd (hunit.mul_left_cancel (h2.trans (mul_zero _).symm)) this
        have h4 := congr_arg ZMod.val h3
        simp only [ZMod.val_natCast] at h4
        rwa [Nat.mod_eq_of_lt hj₁, Nat.mod_eq_of_lt hj₂] at h4
      · intro i hi; simp only [Finset.mem_coe, Finset.mem_range] at hi
        set u := ZMod.unitOfCoprime k₀ hcop_k
        set j := ZMod.val ((↑i - ↑r : ZMod n) * Units.val (u⁻¹)) with hj_def
        refine ⟨j, Finset.mem_range.mpr (ZMod.val_lt _), ?_⟩
        have hmod : (↑(r + j * k₀) : ZMod n) = (↑i : ZMod n) := by
          push_cast; rw [hj_def, ZMod.natCast_zmod_val, mul_assoc]
          have hinv : Units.val (u⁻¹) * (↑k₀ : ZMod n) = 1 := by
            show Units.val (u⁻¹) * Units.val u = 1
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
          rw [hinv, mul_one, add_sub_cancel]
        have := congr_arg ZMod.val hmod
        rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hi] at this
      · intro j _; rw [← kStepVector_mod_n]
    rw [← hreindex] at hsum
    -- Split: good positions (i < n-1) contribute k₀ - nonS, closing contributes s'
    -- Sum of good positions: (n-1) * (k₀ - nonS)
    have hgood_sum : ∑ j ∈ Finset.range (n - 1),
        Necklace.kStepVector w (r + j * k₀) k₀ .s = ↑((n - 1) * (k₀ - nonS)) := by
      have h_eq : ∀ j ∈ Finset.range (n - 1),
          Necklace.kStepVector w (r + j * k₀) k₀ .s = (↑(k₀ - nonS) : ℤ) :=
        fun j hj => hs_count ⟨j, Finset.mem_range.mp hj⟩
      rw [Finset.sum_congr rfl h_eq, Finset.sum_const, Finset.card_range]
      simp []
    -- Split range n = range (n-1) ∪ {n-1}
    have hsplit : ∑ j ∈ Finset.range n, Necklace.kStepVector w (r + j * k₀) k₀ .s =
        (∑ j ∈ Finset.range (n - 1), Necklace.kStepVector w (r + j * k₀) k₀ .s) +
          Necklace.kStepVector w (r + (n - 1) * k₀) k₀ .s := by
      have h := Finset.sum_range_succ
        (fun j => Necklace.kStepVector w (r + j * k₀) k₀ .s) (n - 1)
      rw [show n - 1 + 1 = n from by omega] at h
      exact h
    rw [hsplit, hgood_sum] at hsum
    -- s' = kStepVector at closing ≥ 0, s' ≤ k₀
    set s' := Necklace.kStepVector w (r + (n - 1) * k₀) k₀ .s with hs'_def
    have hs'_nn : s' ≥ 0 := by
      rw [hs'_def]; unfold Necklace.kStepVector ZVector.ofList; exact_mod_cast Nat.zero_le _
    have hs'_le : s' ≤ ↑k₀ := by
      have := kStepVector_component_sum w (r + (n - 1) * k₀) k₀
      rw [stepSize_sum] at this
      have hL_nn : Necklace.kStepVector w (r + (n - 1) * k₀) k₀ .L ≥ 0 := by
        unfold Necklace.kStepVector ZVector.ofList; exact_mod_cast Nat.zero_le _
      have hm_nn : Necklace.kStepVector w (r + (n - 1) * k₀) k₀ .m ≥ 0 := by
        unfold Necklace.kStepVector ZVector.ofList; exact_mod_cast Nat.zero_le _
      linarith
    -- From hsum: (n-1)*(k₀-nonS) + s' = k₀*b
    -- s' ≤ k₀ → (n-1)*(k₀-nonS) ≥ k₀*(b-1)
    -- → (n-1)*nonS ≤ (n-1)*k₀ - k₀*(b-1) = k₀*(n-b) = k₀*2a
    -- k₀ ≤ n-1 → (n-1)*nonS ≤ (n-1)*2a → nonS ≤ 2a
    have h_ineq : (n - 1) * nonS ≤ k₀ * (2 * a) := by
      have : ↑((n - 1) * (k₀ - nonS)) + s' = ↑(k₀ * b) := hsum
      have : (↑((n - 1) * (k₀ - nonS)) : ℤ) = ↑(k₀ * b) - s' := by linarith
      have h1 : (↑(k₀ * b) : ℤ) - s' ≥ ↑(k₀ * b) - ↑k₀ := by linarith
      have h2 : (↑(k₀ * b) : ℤ) - ↑k₀ = ↑k₀ * (↑b - 1) := by push_cast; ring
      -- (n-1)*(k₀-nonS) ≥ k₀*(b-1)
      -- → (n-1)*k₀ - (n-1)*nonS ≥ k₀*(b-1)
      -- → (n-1)*nonS ≤ (n-1)*k₀ - k₀*(b-1) = k₀*(n-1-(b-1)) = k₀*(n-b) = k₀*2a
      -- (n-1)*(k₀-nonS) + s' = k₀*b and s' ≤ k₀
      -- → (n-1)*(k₀-nonS) ≥ k₀*(b-1)
      -- → (n-1)*k₀ - (n-1)*nonS ≥ k₀*b - k₀
      -- → (n-1)*nonS ≤ (n-1)*k₀ - k₀*b + k₀ = k₀*(n-b) = k₀*2a
      have hsum_eq : ↑((n - 1) * (k₀ - nonS)) + s' = ↑(k₀ * b) := hsum
      have h3 : (↑((n - 1) * (k₀ - nonS)) : ℤ) ≥ ↑(k₀ * b) - ↑k₀ := by linarith
      zify [_hnonS_le, (show 1 ≤ n from by omega)] at h3 ⊢
      nlinarith [_hn_eq]
    -- k₀ ≤ n - 1, so k₀ * 2a ≤ (n-1) * 2a
    have : k₀ * (2 * a) ≤ (n - 1) * (2 * a) := Nat.mul_le_mul_right _ (by omega)
    have := Nat.le_of_mul_le_mul_left (h_ineq.trans this) (by omega : 0 < n - 1)
    exact this
  -- Each good k₀-step window has nonS non-.s entries
  have hslice_j : ∀ t, t < n - 1 →
      nonS = ((Necklace.slice w (r + t * k₀) (r + t * k₀ + k₀)).filter
        (· ≠ .s)).length :=
    fun t ht => (nonS_filter_length w (r + t * k₀) k₀ nonS
      (hs_count ⟨t, ht⟩) _hnonS_le).symm
  -- Deletion bridge: L-count in k₀-windows = nonS-window L-count in D
  set wList := (List.range n).map (fun i => w (↑i : ZMod n)) with hwList_def
  set q₀ := ((wList.take (r % n)).filter (· ≠ StepSize.s)).length with hq₀_def
  -- Define the nonS-window L-count on D
  set nWLc : ℕ → ℕ := fun i =>
    ((List.range nonS).map (fun t =>
      D[(i + t) % D.length]'(Nat.mod_lt _ hDlen_pos))).count .L
    with hnWLc_def
  -- Modular reduction: nWLc (i % D.length) = nWLc i
  have hnWLc_mod : ∀ i, nWLc (i % D.length) = nWLc i := by
    intro i; simp only [nWLc]; congr 1
    apply List.map_congr_left; intro t ht
    congr 1
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  -- Bridge: for t < n-1, kStepVector .L at position t = nWLc at q₀ + t*nonS
  have hbridge : ∀ t, t < n - 1 →
      nWLc ((q₀ + t * nonS) % D.length) =
        (Necklace.kStepVector w (r + t * k₀) k₀ .L).natAbs := by
    intro t ht
    -- Use telescope: nonSBefore advances by nonS per window
    set nb_t := ((wList.take ((r + t * k₀) % n)).filter
      (· ≠ StepSize.s)).length with hnb_t_def
    have htelescope : nb_t % D.length = (q₀ + t * nonS) % D.length := by
      rw [hnb_t_def]
      suffices h : ∀ s, s < n - 1 →
          ((wList.take ((r + s * k₀) % n)).filter
            (· ≠ StepSize.s)).length % D.length =
          (q₀ + s * nonS) % D.length from h t ht
      intro s
      induction s with
      | zero => intro _; simp only [Nat.zero_mul, Nat.add_zero, ← hq₀_def]
      | succ s' ih =>
        intro hs
        have hslice_s := hslice_j s' (by omega)
        have hstep := nonSBefore_advance w (r + s' * k₀) k₀ nonS
          (by omega) hslice_s
        rw [show r + (s' + 1) * k₀ = r + s' * k₀ + k₀ from by ring]
        trans (((wList.take ((r + s' * k₀) % n)).filter
            (· ≠ StepSize.s)).length + nonS) % D.length
        · exact hstep
        · conv_lhs => rw [Nat.add_mod]
          rw [ih (by omega)]
          rw [← Nat.add_mod]
          congr 1; ring
    -- Geometric bridge
    have hbr : nWLc nb_t =
        (Necklace.kStepVector w (r + t * k₀) k₀ .L).natAbs :=
      orderedDeletion_window_Lcount w (r + t * k₀) k₀ nonS hDlen_pos (by omega)
        (hslice_j t ht)
    calc nWLc ((q₀ + t * nonS) % D.length)
        = nWLc (nb_t % D.length) := by rw [← htelescope]
      _ = nWLc nb_t := hnWLc_mod nb_t
      _ = (Necklace.kStepVector w (r + t * k₀) k₀ .L).natAbs := hbr
  -- L-counts alternate: since D alternates and nonS is odd,
  -- nWLc(q₀ + t*nonS) depends on (q₀ + t*nonS) % 2 = (q₀ + t) % 2 (nonS odd)
  have hLalt : ∀ t, t < n - 1 →
      (Necklace.kStepVector w (r + t * k₀) k₀ .L).natAbs =
        nWLc ((q₀ + t) % 2) := by
    intro t ht
    rw [← hbridge t ht, hnWLc_mod]
    show nWLc (q₀ + t * nonS) = nWLc ((q₀ + t) % 2)
    have h1 := alternating_nonS_window_Lcount D a nonS _ha_pos hDlen halt hne
      _hnonS_pos _hnonS_odd hnonS_lt (q₀ + t * nonS)
    change nWLc (q₀ + t * nonS) = _ at h1
    rw [h1]
    -- (q₀ + t * nonS) % 2 = (q₀ + t) % 2 since nonS % 2 = 1
    have h_mod_eq : (q₀ + t * nonS) % 2 = (q₀ + t) % 2 := by
      have h_mul : (t * nonS) % 2 = t % 2 := by
        rw [Nat.mul_mod, _hnonS_odd, Nat.mul_one,
            Nat.mod_mod_of_dvd t (dvd_refl 2)]
      rw [Nat.add_mod, h_mul, ← Nat.add_mod]
    rw [h_mod_eq]
  -- Define seq: the two alternating k-step vectors
  -- n-1 ≥ 2 so positions 0 and 1 are both valid
  have hn_sub_ge2 : n - 1 ≥ 2 := by omega
  set seq : Fin 2 → ZVector StepSize := fun j =>
    Necklace.kStepVector w (r + j.val * k₀) k₀
  -- Good positions: kStepVector at i = seq(i%2)
  have hgood : ∀ i : Fin (n - 1),
      Necklace.kStepVector w (r + i.val * k₀) k₀ =
        seq ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩ := by
    intro ⟨i, hi⟩; simp only [seq]
    -- .s equality: both = k₀ - nonS
    have hs_eq : (Necklace.kStepVector w (r + i * k₀) k₀ .s) =
        (Necklace.kStepVector w (r + i % 2 * k₀) k₀ .s) := by
      have h1 := hs_count ⟨i, hi⟩
      have h2 := hs_count ⟨i % 2, by omega⟩
      simp at h1 h2; rw [h1, h2]
    -- .L equality: natAbs values match (from alternation pattern)
    have hL_eq : (Necklace.kStepVector w (r + i * k₀) k₀ .L) =
        (Necklace.kStepVector w (r + i % 2 * k₀) k₀ .L) := by
      have hnn1 : (Necklace.kStepVector w (r + i * k₀) k₀ .L) ≥ 0 := by
        unfold Necklace.kStepVector ZVector.ofList; exact_mod_cast Nat.zero_le _
      have hnn2 : (Necklace.kStepVector w (r + i % 2 * k₀) k₀ .L) ≥ 0 := by
        unfold Necklace.kStepVector ZVector.ofList; exact_mod_cast Nat.zero_le _
      have h1 := hLalt i hi
      have h2 := hLalt (i % 2) (by omega)
      -- (q₀ + i) % 2 = (q₀ + i % 2) % 2
      rw [show (q₀ + i % 2) % 2 = (q₀ + i) % 2 from by
        rw [Nat.add_mod, Nat.mod_mod_of_dvd i (dvd_refl 2), ← Nat.add_mod]] at h2
      -- h1 and h2 now have equal RHS, so natAbs values are equal
      have h_abs : (Necklace.kStepVector w (r + i * k₀) k₀ .L).natAbs =
          (Necklace.kStepVector w (r + i % 2 * k₀) k₀ .L).natAbs := by rw [h1, h2]
      -- Convert natAbs equality to ℤ equality using non-negativity
      -- a ≥ 0 → a = ↑(a.natAbs) (via |a| = a and ↑natAbs = |a|)
      calc Necklace.kStepVector w (r + i * k₀) k₀ .L
          = ↑(Necklace.kStepVector w (r + i * k₀) k₀ .L).natAbs := by
            rw [Int.natCast_natAbs, abs_of_nonneg hnn1]
        _ = ↑(Necklace.kStepVector w (r + i % 2 * k₀) k₀ .L).natAbs := by
            exact_mod_cast h_abs
        _ = Necklace.kStepVector w (r + i % 2 * k₀) k₀ .L := by
            rw [Int.natCast_natAbs, abs_of_nonneg hnn2]
    -- .m from component sum: .L + .m + .s = k₀ at both positions
    have htot1 := kStepVector_component_sum w (r + i * k₀) k₀
    rw [stepSize_sum] at htot1
    have htot2 := kStepVector_component_sum w (r + i % 2 * k₀) k₀
    rw [stepSize_sum] at htot2
    funext a; cases a with
    | s => exact hs_eq
    | L => exact hL_eq
    | m => linarith
  -- Closing: ≠ both seq values (since .s differs)
  have hclose : ∀ j : Fin 2,
      Necklace.kStepVector w (r + (n - 1) * k₀) k₀ ≠ seq j := by
    intro ⟨j, hj⟩
    simp only [seq]
    intro heq
    have := congr_fun heq .s
    simp at this
    have h_seq_s := hs_count ⟨j, by omega⟩
    simp at h_seq_s
    rw [h_seq_s] at this
    exact hs_close this
  -- L-difference: |seq(0).L - seq(1).L| = 1
  have hL_diff : Necklace.kStepVector w (r + 0 * k₀) k₀ .L -
      Necklace.kStepVector w (r + 1 * k₀) k₀ .L = 1 ∨
     Necklace.kStepVector w (r + 0 * k₀) k₀ .L -
      Necklace.kStepVector w (r + 1 * k₀) k₀ .L = -1 := by
    -- From hLalt: seq(j).L.natAbs = nWLc((q₀+j) % 2)
    have h0 := hLalt 0 (by omega)
    have h1 := hLalt 1 (by omega)
    -- Only simplify q₀ + 0 → q₀ in h0; do NOT normalize r + 0*k₀ → r
    simp only [Nat.add_zero] at h0
    -- seq(j).L ≥ 0
    have hnn0 : (Necklace.kStepVector w (r + 0 * k₀) k₀ .L) ≥ 0 := by
      unfold Necklace.kStepVector ZVector.ofList; exact_mod_cast Nat.zero_le _
    have hnn1 : (Necklace.kStepVector w (r + 1 * k₀) k₀ .L) ≥ 0 := by
      unfold Necklace.kStepVector ZVector.ofList; exact_mod_cast Nat.zero_le _
    -- So seq(j).L = ↑(seq(j).L.natAbs)
    have heq0 : Necklace.kStepVector w (r + 0 * k₀) k₀ .L =
        ↑(Necklace.kStepVector w (r + 0 * k₀) k₀ .L).natAbs := by
      rw [Int.natCast_natAbs, abs_of_nonneg hnn0]
    have heq1 : Necklace.kStepVector w (r + 1 * k₀) k₀ .L =
        ↑(Necklace.kStepVector w (r + 1 * k₀) k₀ .L).natAbs := by
      rw [Int.natCast_natAbs, abs_of_nonneg hnn1]
    -- From alternating_window_Lcount_abs_diff
    have hdiff := alternating_window_Lcount_abs_diff D a nonS _ha_pos hDlen halt hne hbin
      _hnonS_pos _hnonS_odd hnonS_lt nWLc hDlen_pos rfl
    rcases Nat.mod_two_eq_zero_or_one q₀ with hq | hq
    · -- q₀ % 2 = 0, (q₀+1) % 2 = 1
      rw [hq] at h0
      rw [show (q₀ + 1) % 2 = 1 from by omega] at h1
      rw [heq0, heq1, h0, h1]
      exact hdiff
    · -- q₀ % 2 = 1, (q₀+1) % 2 = 0
      rw [hq] at h0
      rw [show (q₀ + 1) % 2 = 0 from by omega] at h1
      rw [heq0, heq1, h0, h1]
      rcases hdiff with h | h <;> [right; left] <;> omega
  refine ⟨fun i => ?_, hL_diff, k₀, r, seq, _hk₀_lt, hcop_k, hgood, hclose⟩
  have := hgood i; simp only [seq] at this; exact this

/-- The core construction: from oddRegular data (counts, pairwise MOS, deletion MOS)
    on a ternary necklace, construct an AS.

    **Proof outline**:
    1. Convert `identifyPair w L m` to a `BinaryNecklace n` (type bridge: m → L, s → s).
       The coprime step counts `(2a, b)` ensure this binary MOS is primitive.
    2. Apply `allMOSScalesHaveGenerator` to get generator `g` at step `k₀`,
       then `generator_implies_p_minus_one_occurrences` to get n−1 positions with
       `kStepVector = g`.
    3. From the count formula `(n−1)·g(m) + g'(m) = k₀·2a` and `g'(m) = g(m) ± 1`,
       derive `n·g(m) = k₀·2a ∓ 1`, so `g(m)` is odd (since `n` is odd).
    4. The deletion MOS (`circularHasMOSProperty` on `orderedDeletion w s`) gives
       a balanced binary MOS of length `2a` with `a` copies of each letter.
       This must be alternating: `(Lm)^a` (up to rotation).
    5. At k₀-spaced positions, windows of length `k₀` are adjacent. Each contains
       `g(m)` non-s positions (odd), forming a contiguous block of the alternating
       L/m pattern. Consecutive blocks alternate between `⌈g(m)/2⌉` and `⌊g(m)/2⌋`
       L's, giving alternating ternary k₀-step vectors.
    6. The unique position with binary vector `g'` has different s-count, making
       the closing vector distinct from both alternating types. -/
private lemma oddRegular_data_hasAS (w : TernaryNecklace n)
    (hodd : n % 2 = 1) (a b : ℕ)
    (ha_pos : a > 0) (hb_pos : b > 0) (_hb_odd : b % 2 = 1)
    (hcop : Nat.Coprime (2 * a) b) (hn_eq : n = 2 * a + b)
    (hcountL : Necklace.count w .L = a)
    (hcountm : Necklace.count w .m = a)
    (hcounts : Necklace.count w .s = b)
    (hmos : isPartialPairwiseMOS w .L .m)
    (hdel : isPartialDeletionMOS w .s) :
    hasAS w := by
  obtain ⟨k₀, hcop_k, hk₀_pos, hk₀_lt, r, nonS, hnonS_pos, hnonS_odd, hnonS_le,
    _hdet, hs_count, hs_close⟩ :=
    oddRegular_kstep_data w hodd a b ha_pos hb_pos hcop hn_eq hcountL hcountm hcounts hmos
  exact (oddRegular_construct_AS w hodd a b ha_pos hn_eq hcountL hcountm hcounts hdel
    k₀ hcop_k hk₀_pos hk₀_lt r nonS hnonS_pos hnonS_odd hnonS_le hs_count hs_close).2.2

/-- Odd-regular scales have an AS.

**Proof sketch**:
1. Extract the oddRegular data: permutation σ, counts a, a, b, MOS properties.
2. Apply `oddRegular_data_hasAS` to the permuted necklace `σw` to get `hasAS (σw)`.
3. Transfer back via `hasAS_of_applyPerm` to get `hasAS w`. -/
theorem oddRegular_hasAS (w : TernaryNecklace n)
    (h : isOddRegular w) : hasAS w := by
  obtain ⟨hprim, hodd, σ, a, b, ha_pos, hb_pos, hb_odd, hcop, hn_eq,
    hcountL, hcountm, hcounts, hmos, hdel⟩ := h
  exact hasAS_of_applyPerm σ w
    (oddRegular_data_hasAS _ hodd a b ha_pos hb_pos hb_odd hcop hn_eq
      hcountL hcountm hcounts hmos hdel)

/-- gcd(2a, b) = 1 with b odd implies gcd(a, b) = 1. -/
private lemma coprime_of_double_coprime (a b : ℕ)
    (hcop : Nat.Coprime (2 * a) b) (_ : b % 2 = 1) :
    Nat.Coprime a b :=
  hcop.coprime_dvd_left (Dvd.intro_left 2 rfl)

/-- If f ∘ w is primitive, then w is primitive. -/
private lemma isPrimitive_of_comp {α β : Type*} [DecidableEq α] [DecidableEq β]
    (w : Necklace α n) (f : α → β)
    (h : Necklace.isPrimitive (f ∘ w)) :
    Necklace.isPrimitive w := by
  -- Contrapositive: if w is not primitive, f ∘ w is not primitive either.
  by_contra h_not_prim
  set pLen := (Necklace.period w).length
  have hpLen_pos : 0 < pLen := period_length_pos w
  have hpLen_lt_n : pLen < n := by
    have := Necklace.period_length_le_n w; unfold Necklace.isPrimitive at h_not_prim; omega
  have hpLen_dvd : pLen ∣ n := period_dvd_length w
  have hw_per : ∀ j : ℕ, w ((j : ℕ) : ZMod n) = w ((j % pLen : ℕ) : ZMod n) :=
    fun j => period_pointwise w j
  -- f ∘ w has the same pointwise periodicity
  have hfw_per : ∀ j : ℕ, (f ∘ w) ((j : ℕ) : ZMod n) = (f ∘ w) ((j % pLen : ℕ) : ZMod n) :=
    fun j => congrArg f (hw_per j)
  -- Convert to translational periodicity for f ∘ w
  have hfw_trans : ∀ i : ZMod n, (f ∘ w) i = (f ∘ w) (i + (pLen : ZMod n)) := by
    intro i
    have h1 := hfw_per i.val
    have h2 := hfw_per (i.val + pLen)
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq] at h1
    rw [Nat.add_mod_right] at h2
    rw [h1, ← h2]; congr 1
    simp [Nat.cast_add, ZMod.natCast_val, ZMod.cast_id']
  -- f ∘ w has period ≤ pLen < n, contradicting isPrimitive
  have := Necklace.period_length_le_of_translational_period (f ∘ w) pLen hpLen_pos hpLen_lt_n
    hpLen_dvd hfw_trans
  unfold Necklace.isPrimitive at h; omega

/-- isPrimitive is preserved under applyPerm. -/
lemma isPrimitive_applyPerm (σ : Equiv.Perm StepSize)
    (w : TernaryNecklace n) (h : Necklace.isPrimitive w) :
    Necklace.isPrimitive (Necklace.applyPerm σ w) := by
  -- Contrapositive: if applyPerm σ w is not primitive, neither is w.
  by_contra h_not_prim
  set w' := Necklace.applyPerm σ w with hw'_def
  set pLen := (Necklace.period w').length
  have hpLen_pos : 0 < pLen := period_length_pos w'
  have hpLen_lt_n : pLen < n := by
    have := Necklace.period_length_le_n w'
    unfold Necklace.isPrimitive at h_not_prim; omega
  have hpLen_dvd : pLen ∣ n := period_dvd_length w'
  -- w' has pointwise periodicity: w'(j) = w'(j % pLen) for all j
  have hw'_per : ∀ j : ℕ, w' ((j : ℕ) : ZMod n) = w' ((j % pLen : ℕ) : ZMod n) :=
    fun j => period_pointwise w' j
  -- Since w' = σ ∘ w and σ is injective, w has the same pointwise periodicity
  have hw_per : ∀ j : ℕ, w ((j : ℕ) : ZMod n) = w ((j % pLen : ℕ) : ZMod n) := by
    intro j
    have := hw'_per j
    simp only [hw'_def, Necklace.applyPerm, Function.comp] at this
    exact σ.injective this
  -- Convert pointwise to translational periodicity: w i = w (i + pLen) for all i : ZMod n
  have hw_trans : ∀ i : ZMod n, w i = w (i + (pLen : ZMod n)) := by
    intro i
    have h1 := hw_per i.val
    have h2 := hw_per (i.val + pLen)
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq] at h1
    rw [Nat.add_mod_right] at h2
    -- h1 : w i = w ↑(i.val % pLen), h2 : w ↑(i.val + pLen) = w ↑(i.val % pLen)
    -- Goal: w i = w (i + ↑pLen)
    rw [h1, ← h2]
    congr 1
    simp [Nat.cast_add, ZMod.natCast_val, ZMod.cast_id']
  -- This gives period w ≤ pLen < n, contradicting isPrimitive
  have := Necklace.period_length_le_of_translational_period w pLen hpLen_pos hpLen_lt_n
    hpLen_dvd hw_trans
  unfold Necklace.isPrimitive at h; omega

/-- isPartialPairwisePrimMOS is preserved under applyPerm. -/
private lemma isPartialPairwisePrimMOS_applyPerm (σ : Equiv.Perm StepSize)
    (w : TernaryNecklace n) (x y : StepSize)
    (h : isPartialPairwisePrimMOS w x y) :
    isPartialPairwisePrimMOS (Necklace.applyPerm σ w) (σ x) (σ y) := by
  obtain ⟨hmos, hprim⟩ := h
  exact ⟨isPartialPairwiseMOS_applyPerm σ w x y hmos, by
    rw [identifyPair_applyPerm, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact isPrimitive_applyPerm σ _ hprim⟩

omit [NeZero n] in
/-- Swapping the pair order: identifyPair w y x = applyPerm (swap x y) (identifyPair w x y). -/
private lemma identifyPair_swap (w : TernaryNecklace n) (x y : StepSize) (hxy : x ≠ y) :
    TernaryNecklace.identifyPair w y x =
    Necklace.applyPerm (Equiv.swap x y) (TernaryNecklace.identifyPair w x y) := by
  funext i
  simp only [TernaryNecklace.identifyPair, Necklace.applyPerm, Function.comp]
  by_cases hx : w i = x
  · -- w i = x: LHS = x (since x ≠ y), RHS = swap(y) = x
    have hne : w i ≠ y := hx ▸ hxy
    simp [hx, Equiv.swap_apply_right]
  · by_cases hy : w i = y
    · -- w i = y: LHS = x, RHS = swap(y) = x
      simp [hy, Equiv.swap_apply_right]
    · -- w i ∉ {x, y}: LHS = w i, RHS = swap(w i) = w i
      simp [hx, hy, Equiv.swap_apply_of_ne_of_ne hx hy]

/-- isPartialPairwisePrimMOS is symmetric in the pair. -/
private lemma isPartialPairwisePrimMOS_swap (w : TernaryNecklace n) (x y : StepSize) (hxy : x ≠ y)
    (h : isPartialPairwisePrimMOS w x y) :
    isPartialPairwisePrimMOS w y x := by
  obtain ⟨hmos, hprim⟩ := h
  unfold isPartialPairwisePrimMOS
  rw [identifyPair_swap w x y hxy]
  exact ⟨hasMOSProperty_applyPerm _ _ hmos, isPrimitive_applyPerm _ _ hprim⟩

/-- isPairwisePrimMOS transfers back through applyPerm:
    if `applyPerm σ w` is pairwise-prim-MOS, so is `w`. -/
lemma isPairwisePrimMOS_of_applyPerm (σ : Equiv.Perm StepSize)
    (w : TernaryNecklace n)
    (h : isPairwisePrimMOS (Necklace.applyPerm σ w)) :
    isPairwisePrimMOS w := by
  -- Apply σ⁻¹ to transfer each partial condition back to w.
  have key : ∀ x y : StepSize, x ≠ y →
      isPartialPairwisePrimMOS (Necklace.applyPerm σ w) x y →
      isPartialPairwisePrimMOS w (σ.symm x) (σ.symm y) := by
    intro x y _ hpmos
    have := isPartialPairwisePrimMOS_applyPerm σ.symm (Necklace.applyPerm σ w) x y hpmos
    have heq : Necklace.applyPerm σ.symm (Necklace.applyPerm σ w) = w := by
      funext i; simp [Necklace.applyPerm, Function.comp]
    rwa [heq] at this
  obtain ⟨h1, h2, h3⟩ := h
  have k1 := key .L .m (by decide) h1
  have k2 := key .m .s (by decide) h2
  have k3 := key .L .s (by decide) h3
  -- We have isPartialPairwisePrimMOS for pairs (σ⁻¹L,σ⁻¹m), (σ⁻¹m,σ⁻¹s), (σ⁻¹L,σ⁻¹s).
  -- These cover all unordered pairs; use swap symmetry to match ordered pairs.
  -- Exhaustive case analysis on which permutation σ⁻¹ is.
  -- StepSize has 3 elements, so there are 6 permutations.
  -- For each, the three pairs match up to the three required pairs (possibly swapped).
  have sw := isPartialPairwisePrimMOS_swap w
  -- Determine σ⁻¹ on each element; eliminate impossible cases by injectivity.
  have hinj := σ.symm.injective
  have vals : ∀ x : StepSize, x = .L ∨ x = .m ∨ x = .s := fun x => by cases x <;> simp
  -- Case-split on σ⁻¹(L), σ⁻¹(m), σ⁻¹(s) and eliminate non-injective combinations.
  rcases vals (σ.symm .L) with hL | hL | hL <;>
  rcases vals (σ.symm .m) with hm | hm | hm <;>
  rcases vals (σ.symm .s) with hs | hs | hs <;>
  simp only [hL, hm, hs] at k1 k2 k3 <;> (
    first
    -- 6 valid permutations:
    -- (L,m,s): k1=(L,m), k2=(m,s), k3=(L,s)
    | exact ⟨k1, k2, k3⟩
    -- (L,s,m): k1=(L,s), k2=(s,m), k3=(L,m)
    | exact ⟨k3, sw _ _ (by decide) k2, k1⟩
    -- (m,L,s): k1=(m,L), k2=(L,s), k3=(m,s)
    | exact ⟨sw _ _ (by decide) k1, k3, k2⟩
    -- (m,s,L): k1=(m,s), k2=(s,L), k3=(m,L)
    | exact ⟨sw _ _ (by decide) k3, k1, sw _ _ (by decide) k2⟩
    -- (s,L,m): k1=(s,L), k2=(L,m), k3=(s,m)
    | exact ⟨k2, sw _ _ (by decide) k3, sw _ _ (by decide) k1⟩
    -- (s,m,L): k1=(s,m), k2=(m,L), k3=(s,L)
    | exact ⟨sw _ _ (by decide) k2, sw _ _ (by decide) k1, sw _ _ (by decide) k3⟩
    -- 21 contradictory (non-injective) cases:
    | (exfalso; first
      | exact absurd (hinj (hL.trans hm.symm)) (by decide)
      | exact absurd (hinj (hL.trans hs.symm)) (by decide)
      | exact absurd (hinj (hm.trans hs.symm)) (by decide))
  )

/-- After identifying a non-s pair, all "good" k₀-step identified vectors are equal.
    Since the s-component is constant and the components sum to k₀, the y-component
    (= v.x + v.y = k₀ - v.s) is also constant, and x-component is always 0. -/
private lemma identified_kStepVector_good_eq (w : TernaryNecklace n)
    (k₀ r : ℕ) (nonS : ℕ)
    (hgood : ∀ i : Fin (n - 1),
      (Necklace.kStepVector w (r + i.val * k₀) k₀) .s = ↑(k₀ - nonS))
    (x y : StepSize) (hxy : x ≠ y) (hxs : x ≠ .s) (hys : y ≠ .s)
    (i j : Fin (n - 1)) :
    ZVector.identifyPair (Necklace.kStepVector w (r + i.val * k₀) k₀) x y =
    ZVector.identifyPair (Necklace.kStepVector w (r + j.val * k₀) k₀) x y := by
  set vi := Necklace.kStepVector w (r + i.val * k₀) k₀
  set vj := Necklace.kStepVector w (r + j.val * k₀) k₀
  -- Both have the same s-component
  have hi_s : vi .s = ↑(k₀ - nonS) := hgood i
  have hj_s : vj .s = ↑(k₀ - nonS) := hgood j
  -- Component sums: v.L + v.m + v.s = k₀
  have hi_sum : vi .L + vi .m + vi .s = ↑k₀ := by
    have := kStepVector_component_sum w (r + i.val * k₀) k₀
    rw [stepSize_sum] at this; linarith
  have hj_sum : vj .L + vj .m + vj .s = ↑k₀ := by
    have := kStepVector_component_sum w (r + j.val * k₀) k₀
    rw [stepSize_sum] at this; linarith
  -- Since {x,y} = {L,m}, v.x + v.y = k₀ - v.s is the same for both
  -- Show: vi.x + vi.y = vj.x + vj.y (both = k₀ - (k₀ - nonS))
  have hxy_sum : vi x + vi y = vj x + vj y := by
    -- vi.x + vi.y + vi.s = k₀ and vj.x + vj.y + vj.s = k₀, with vi.s = vj.s
    -- Since {x,y,s} = StepSize, vi.L + vi.m + vi.s = vi.x + vi.y + vi.s
    -- But x,y,s may be L,m,s in different orders
    -- Simplest: cases on x and y
    cases x <;> cases y <;> simp_all <;> linarith
  funext a
  simp only [ZVector.identifyPair]
  split
  · rfl  -- a = x: both are 0
  · split
    · linarith [hxy_sum]  -- a = y: both are v.x + v.y
    · -- a ≠ x, a ≠ y: must be .s
      have ha_s : a = .s := by cases a <;> cases x <;> cases y <;> simp_all
      subst ha_s; rw [hi_s, hj_s]

/-- The identified l*k₀-step vectors have ≤ 2 distinct values when the ternary necklace
    has n-1 positions with the same k₀-step s-component.

    **Proof outline**: After identifying x with y (both ∈ {L,m}), the k₀-step identified
    vectors are constant at the n-1 "good" positions (by `identified_kStepVector_good_eq`).
    The l*k₀-step identified vector at position j sums l consecutive identified k₀-step
    vectors. Windows not touching the "bad" position (n-1) give the same sum; windows
    touching it also give the same sum (bad contributes one fixed different vector).
    So ≤ 2 distinct values. -/
private lemma identified_lk_le_two_nonequi (w : TernaryNecklace n)
    (k₀ r : ℕ) (nonS : ℕ) (l : ℕ)
    (hcop : Nat.Coprime k₀ n) (hodd : n % 2 = 1) (hn_ge : n ≥ 3)
    (hl_pos : 0 < l) (hl_le : l ≤ n - 1)
    (hgood : ∀ i : Fin (n - 1),
      (Necklace.kStepVector w (r + i.val * k₀) k₀) .s = ↑(k₀ - nonS))
    (hbad : (Necklace.kStepVector w (r + (n - 1) * k₀) k₀) .s ≠ ↑(k₀ - nonS))
    (_ : Necklace.count w .L = a) (_ : Necklace.count w .m = a)
    (_ : isPartialDeletionMOS w .s)
    (x y : StepSize) (hxy : x ≠ y) (hxs : x ≠ .s) (hys : y ≠ .s) :
    (Necklace.allKStepVectors (TernaryNecklace.identifyPair w x y) (l * k₀)).toFinset.card ≤ 2 := by
  -- Step 1: Classification of l*k₀-step vectors by induction using window shift
  -- The identified k₀-step vectors at good positions are all equal
  set T_good := ZVector.identifyPair (Necklace.kStepVector w (r + 0 * k₀) k₀) x y with hT_good_def
  have hT_eq : ∀ i : Fin (n - 1),
      ZVector.identifyPair (Necklace.kStepVector w (r + i.val * k₀) k₀) x y = T_good := by
    intro i; exact identified_kStepVector_good_eq w k₀ r nonS hgood x y hxy hxs hys i ⟨0, by omega⟩
  -- The l*k₀-step identified vector at position r+j*k₀
  -- Non-crossing (j < n-l): window {j,...,j+l-1} ⊂ {0,...,n-2} → sum = l·T_good
  -- Crossing (j ≥ n-l): window contains n-1 → sum = (l-1)·T_good + T_bad
  -- We prove this by induction using kStepVector_window_shift_fun
  set iv₁ := ZVector.identifyPair (Necklace.kStepVector w r (l * k₀)) x y with hiv₁_def
  set iv₃ := ZVector.identifyPair (Necklace.kStepVector w (r + (n - l) * k₀) (l * k₀)) x y with hiv₃_def
  -- Classification: l*k₀-step identified vectors at positions r+j*k₀ take two forms
  have hclass : ∀ j, j < n →
      ZVector.identifyPair (Necklace.kStepVector w (r + j * k₀) (l * k₀)) x y =
        if j < n - l then iv₁ else iv₃ := by
    intro j hj
    induction j with
    | zero =>
      simp only [Nat.zero_mul, Nat.add_zero]
      rw [if_pos (by omega : 0 < n - l)]
    | succ j IH =>
      have hj_lt : j < n := by omega
      have IH := IH hj_lt
      -- Window shift recurrence: S(j+1) = S(j) - T(j) + T(j+l)
      have hrec : Necklace.kStepVector w (r + (j + 1) * k₀) (l * k₀) =
          Necklace.kStepVector w (r + j * k₀) (l * k₀) -
          Necklace.kStepVector w (r + j * k₀) k₀ +
          Necklace.kStepVector w (r + (j + l) * k₀) k₀ := by
        have h := kStepVector_window_shift_fun w (r + j * k₀) k₀ l hl_pos
        rw [show r + j * k₀ + k₀ = r + (j + 1) * k₀ from by ring,
            show r + j * k₀ + l * k₀ = r + (j + l) * k₀ from by ring] at h
        exact h
      -- Apply identifyPair to the recurrence (identifyPair distributes over ± pointwise)
      have hrec_id : ZVector.identifyPair (Necklace.kStepVector w (r + (j + 1) * k₀) (l * k₀)) x y =
          ZVector.identifyPair (Necklace.kStepVector w (r + j * k₀) (l * k₀)) x y -
          ZVector.identifyPair (Necklace.kStepVector w (r + j * k₀) k₀) x y +
          ZVector.identifyPair (Necklace.kStepVector w (r + (j + l) * k₀) k₀) x y := by
        rw [hrec]; funext a
        simp only [ZVector.identifyPair, ZVector.sub_apply, ZVector.add_apply]
        by_cases hax : a = x <;> by_cases hay : a = y <;> simp [hax, hay, hxy.symm]; ring
      -- Case analysis: what are T(j) and T(j+l)?
      by_cases hjnl : j + 1 < n - l
      · -- j+1 < n-l: both T(j) and T(j+l) are good
        rw [if_pos hjnl]
        have hj_good : j < n - 1 := by omega
        have hjl_good : j + l < n - 1 := by omega
        have hTj := hT_eq ⟨j, by omega⟩
        have hTjl := hT_eq ⟨j + l, by omega⟩
        simp only [] at hTj hTjl
        rw [hrec_id, IH, if_pos (by omega : j < n - l), hTj, hTjl,
            show iv₁ - T_good + T_good = iv₁ from by funext a; simp [ZVector.sub_apply, ZVector.add_apply]]
      · -- j+1 ≥ n-l
        rw [if_neg hjnl]
        by_cases hjnl_eq : j + 1 = n - l
        · -- Transition: j+1 = n-l, so the result equals iv₃
          rw [show r + (j + 1) * k₀ = r + (n - l) * k₀ from by rw [hjnl_eq]]
        · -- j+1 > n-l: crossing region, both T(j) and T(j+l) are good
          -- T(j) good because j < n-1; T(j+l) good because (j+l) % n < n-1
          have hj_good : j < n - 1 := by omega
          have hjl_mod : (j + l) % n < n - 1 := by
            have hjl_ge : j + l ≥ n := by omega
            have hjl_lt : j + l < 2 * n := by omega
            rw [Nat.mod_eq_sub_mod hjl_ge, Nat.mod_eq_of_lt (by omega)]; omega
          have hTj := hT_eq ⟨j, by omega⟩
          simp only [] at hTj
          -- For T(j+l), we need to handle the modular reduction
          -- kStepVector w (r + (j+l)*k₀) k₀ has index (j+l), but in the stacking
          -- sequence positions are 0,...,n-1 and the index is (j+l) mod n
          -- Since r + (j+l)*k₀ and r + ((j+l) mod n)*k₀ give the same kStepVector
          -- (modular periodicity), we can use hT_eq at index (j+l) mod n
          have hTjl_reduce : Necklace.kStepVector w (r + (j + l) * k₀) k₀ =
              Necklace.kStepVector w (r + ((j + l) % n) * k₀) k₀ := by
            rw [← kStepVector_mod_n w (r + (j + l) * k₀) k₀,
                ← kStepVector_mod_n w (r + ((j + l) % n) * k₀) k₀]
            congr 1
            show (r + (j + l) * k₀) % n = (r + ((j + l) % n) * k₀) % n
            conv_lhs => rw [Nat.add_mod, Nat.mul_mod]
            conv_rhs => rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod_of_dvd _ (dvd_refl n)]
          have hTjl := hT_eq ⟨(j + l) % n, hjl_mod⟩
          simp only [] at hTjl
          rw [hrec_id, IH, if_neg (by omega : ¬(j < n - l)), hTj,
              show ZVector.identifyPair (Necklace.kStepVector w (r + (j + l) * k₀) k₀) x y = T_good from by
                rw [hTjl_reduce]; exact hTjl,
              show iv₃ - T_good + T_good = iv₃ from by funext a; simp [ZVector.sub_apply, ZVector.add_apply]]
  -- Step 2: Coprime bijection to cover all positions
  have hk_unit := coprime_isUnit_zmod k₀ hcop (by omega : n ≥ 2)
  set g : ZMod n → ZMod n := fun j => (↑r : ZMod n) + j * (↑k₀ : ZMod n)
  have g_surj : Function.Surjective g := by
    apply Finite.surjective_of_injective
    intro j₁ j₂ h
    have h1 : j₁ * (↑k₀ : ZMod n) = j₂ * (↑k₀ : ZMod n) := add_left_cancel h
    rw [mul_comm j₁, mul_comm j₂] at h1; exact hk_unit.mul_left_cancel h1
  have hg_mod : ∀ j : ZMod n,
      Necklace.kStepVector w (g j).val (l * k₀) =
      Necklace.kStepVector w (r + j.val * k₀) (l * k₀) := by
    intro j
    have hmod : (g j).val = (r + j.val * k₀) % n := by
      have h1 : (↑((g j).val) : ZMod n) = (↑(r + j.val * k₀) : ZMod n) := by
        rw [natCast_zmod_val]; show g j = _
        rw [Nat.cast_add, Nat.cast_mul, natCast_zmod_val]
      have h2 := congr_arg ZMod.val h1
      rwa [ZMod.val_natCast, ZMod.val_natCast,
           Nat.mod_eq_of_lt (ZMod.val_lt (g j))] at h2
    rw [show (g j).val = (r + j.val * k₀) % n from hmod]
    exact kStepVector_mod_n w (r + j.val * k₀) (l * k₀)
  -- Step 3: Every identified l*k₀-step vector is iv₁ or iv₃
  have hmem : ∀ v ∈ (Necklace.allKStepVectors
      (TernaryNecklace.identifyPair w x y) (l * k₀)).toFinset,
      v = iv₁ ∨ v = iv₃ := by
    intro v hv
    rw [List.mem_toFinset] at hv
    unfold Necklace.allKStepVectors at hv
    simp only [List.mem_map, List.mem_range] at hv
    obtain ⟨i, hi, rfl⟩ := hv
    rw [identifyPair_kStepVector w x y hxy i (l * k₀)]
    obtain ⟨j, hgj⟩ := g_surj (i : ZMod n)
    have hi_eq : (g j).val = i := by
      rw [hgj, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
    have hkv_eq : Necklace.kStepVector w i (l * k₀) =
        Necklace.kStepVector w (r + j.val * k₀) (l * k₀) := by
      rw [← hi_eq]; exact hg_mod j
    rw [hkv_eq, hclass j.val (ZMod.val_lt j)]
    by_cases hjnl : j.val < n - l
    · left; rw [if_pos hjnl]
    · right; rw [if_neg hjnl]
  -- Step 4: Subset of a 2-element set ⇒ card ≤ 2
  have hsub : (Necklace.allKStepVectors
      (TernaryNecklace.identifyPair w x y) (l * k₀)).toFinset ⊆ {iv₁, iv₃} := by
    intro v hv; rw [Finset.mem_insert, Finset.mem_singleton]
    exact hmem v hv
  calc (Necklace.allKStepVectors _ (l * k₀)).toFinset.card
      ≤ ({iv₁, iv₃} : Finset _).card := Finset.card_le_card hsub
    _ ≤ 2 := by
        have := Finset.card_insert_le iv₁ ({iv₃} : Finset _)
        simp only [Finset.card_singleton] at this; linarith

/-- Generic ≤ 2 lemma for l*k'-step vectors: if a necklace has n-1 identical k'-step
    vectors (at coprime-spaced stacking positions) and 1 different one, then for any
    l ∈ [1, n-1], the l*k'-step vectors take ≤ 2 distinct values.

    This generalizes `identified_lk_le_two_nonequi` by working directly on any necklace
    (including one that's already been pair-identified) without requiring the identification
    pair to avoid `.s`. -/
private lemma lk_le_two_of_constant_good (w' : TernaryNecklace n)
    (k' r' : ℕ) (l : ℕ)
    (hcop : Nat.Coprime k' n) (hn_ge : n ≥ 3)
    (hl_pos : 0 < l) (hl_le : l ≤ n - 1)
    (T_good : ZVector StepSize)
    (hT_eq : ∀ i : Fin (n - 1),
      Necklace.kStepVector w' (r' + i.val * k') k' = T_good)
    (_ : Necklace.kStepVector w' (r' + (n - 1) * k') k' ≠ T_good) :
    (Necklace.allKStepVectors w' (l * k')).toFinset.card ≤ 2 := by
  -- Define the two candidate l*k'-step vectors
  set v₁ := Necklace.kStepVector w' r' (l * k') with hv₁_def
  set v₃ := Necklace.kStepVector w' (r' + (n - l) * k') (l * k') with hv₃_def
  -- Classification by induction using window shift
  have hclass : ∀ j, j < n →
      Necklace.kStepVector w' (r' + j * k') (l * k') =
        if j < n - l then v₁ else v₃ := by
    intro j hj
    induction j with
    | zero =>
      simp only [Nat.zero_mul, Nat.add_zero]
      rw [if_pos (by omega : 0 < n - l)]
    | succ j IH =>
      have hj_lt : j < n := by omega
      have IH := IH hj_lt
      -- Window shift recurrence
      have hrec := kStepVector_window_shift_fun w' (r' + j * k') k' l hl_pos
      rw [show r' + j * k' + k' = r' + (j + 1) * k' from by ring,
          show r' + j * k' + l * k' = r' + (j + l) * k' from by ring] at hrec
      by_cases hjnl : j + 1 < n - l
      · -- Non-crossing: both T(j) and T(j+l) are good
        rw [if_pos hjnl]
        have hTj := hT_eq ⟨j, by omega⟩
        have hTjl := hT_eq ⟨j + l, by omega⟩
        simp only [] at hTj hTjl
        rw [hrec, IH, if_pos (by omega : j < n - l), hTj, hTjl,
            show v₁ - T_good + T_good = v₁ from by
              funext a; simp [ZVector.sub_apply, ZVector.add_apply]]
      · rw [if_neg hjnl]
        by_cases hjnl_eq : j + 1 = n - l
        · -- Transition
          rw [show r' + (j + 1) * k' = r' + (n - l) * k' from by rw [hjnl_eq]]
        · -- Crossing: T(j) good, T((j+l)%n) good, both cancel
          have hj_good : j < n - 1 := by omega
          have hjl_mod : (j + l) % n < n - 1 := by
            have hjl_ge : j + l ≥ n := by omega
            have hjl_lt : j + l < 2 * n := by omega
            rw [Nat.mod_eq_sub_mod hjl_ge, Nat.mod_eq_of_lt (by omega)]; omega
          have hTj := hT_eq ⟨j, by omega⟩
          simp only [] at hTj
          have hTjl_reduce : Necklace.kStepVector w' (r' + (j + l) * k') k' =
              Necklace.kStepVector w' (r' + ((j + l) % n) * k') k' := by
            rw [← kStepVector_mod_n w' (r' + (j + l) * k') k',
                ← kStepVector_mod_n w' (r' + ((j + l) % n) * k') k']
            congr 1
            show (r' + (j + l) * k') % n = (r' + ((j + l) % n) * k') % n
            conv_lhs => rw [Nat.add_mod, Nat.mul_mod]
            conv_rhs => rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod_of_dvd _ (dvd_refl n)]
          have hTjl := hT_eq ⟨(j + l) % n, hjl_mod⟩
          simp only [] at hTjl
          rw [hrec, IH, if_neg (by omega : ¬(j < n - l)), hTj,
              show Necklace.kStepVector w' (r' + (j + l) * k') k' = T_good from by
                rw [hTjl_reduce]; exact hTjl,
              show v₃ - T_good + T_good = v₃ from by
                funext a; simp [ZVector.sub_apply, ZVector.add_apply]]
  -- Coprime bijection to cover all positions
  have hk_unit := coprime_isUnit_zmod k' hcop (by omega : n ≥ 2)
  set g : ZMod n → ZMod n := fun j => (↑r' : ZMod n) + j * (↑k' : ZMod n)
  have g_surj : Function.Surjective g := by
    apply Finite.surjective_of_injective
    intro j₁ j₂ h
    have h1 : j₁ * (↑k' : ZMod n) = j₂ * (↑k' : ZMod n) := add_left_cancel h
    rw [mul_comm j₁, mul_comm j₂] at h1; exact hk_unit.mul_left_cancel h1
  have hg_mod : ∀ j : ZMod n,
      Necklace.kStepVector w' (g j).val (l * k') =
      Necklace.kStepVector w' (r' + j.val * k') (l * k') := by
    intro j
    have hmod : (g j).val = (r' + j.val * k') % n := by
      have h1 : (↑((g j).val) : ZMod n) = (↑(r' + j.val * k') : ZMod n) := by
        rw [natCast_zmod_val]; show g j = _
        rw [Nat.cast_add, Nat.cast_mul, natCast_zmod_val]
      have h2 := congr_arg ZMod.val h1
      rwa [ZMod.val_natCast, ZMod.val_natCast,
           Nat.mod_eq_of_lt (ZMod.val_lt (g j))] at h2
    rw [show (g j).val = (r' + j.val * k') % n from hmod]
    exact kStepVector_mod_n w' (r' + j.val * k') (l * k')
  -- Every l*k'-step vector is v₁ or v₃
  have hmem : ∀ v ∈ (Necklace.allKStepVectors w' (l * k')).toFinset,
      v = v₁ ∨ v = v₃ := by
    intro v hv
    rw [List.mem_toFinset] at hv
    unfold Necklace.allKStepVectors at hv
    simp only [List.mem_map, List.mem_range] at hv
    obtain ⟨i, hi, rfl⟩ := hv
    obtain ⟨j, hgj⟩ := g_surj (i : ZMod n)
    have hi_eq : (g j).val = i := by
      rw [hgj, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
    have hkv_eq : Necklace.kStepVector w' i (l * k') =
        Necklace.kStepVector w' (r' + j.val * k') (l * k') := by
      rw [← hi_eq]; exact hg_mod j
    rw [hkv_eq, hclass j.val (ZMod.val_lt j)]
    by_cases hjnl : j.val < n - l
    · left; rw [if_pos hjnl]
    · right; rw [if_neg hjnl]
  -- Subset of a 2-element set ⇒ card ≤ 2
  have hsub : (Necklace.allKStepVectors w' (l * k')).toFinset ⊆ {v₁, v₃} := by
    intro v hv; rw [Finset.mem_insert, Finset.mem_singleton]
    exact hmem v hv
  calc (Necklace.allKStepVectors _ (l * k')).toFinset.card
      ≤ ({v₁, v₃} : Finset _).card := Finset.card_le_card hsub
    _ ≤ 2 := by
        have := Finset.card_insert_le v₁ ({v₃} : Finset _)
        simp only [Finset.card_singleton] at this; linarith

set_option maxHeartbeats 1600000
/-- The closing k₀-step vector's L-component equals one of the two alternating
    L-components. This is the key fact for the 2k₀-step collapse.

    **Proof**: From the sum constraint
    `(n-1)/2 * (seq(0).L + seq(1).L) + g3.L = k₀ * a`
    and the determinant `nonS * n - 2a * k₀ = ±1`, we derive
    `g3.L = (nonS ∓ 1) / 2`. Since `seq(0).L + seq(1).L = nonS` (from
    alternation of the deletion word) and both are nonneg with odd sum,
    one of them equals `(nonS - 1)/2` and the other `(nonS + 1)/2`.
    Hence `g3.L` matches one of them. -/
private lemma closing_L_in_seq_L (w : TernaryNecklace n)
    (hodd : n % 2 = 1) (a b : ℕ)
    (ha_pos : a > 0) (hb_pos : b > 0) (_hcop : Nat.Coprime (2 * a) b)
    (hn_eq : n = 2 * a + b)
    (hcountL : Necklace.count w .L = a) (hcountm : Necklace.count w .m = a)
    (hcounts : Necklace.count w .s = b)
    (_hmos_Lm : isPartialPairwiseMOS w .L .m)
    (hdel : isPartialDeletionMOS w .s)
    (k₀ r nonS : ℕ)
    (hcop_k : Nat.Coprime k₀ n) (hk₀_pos : 0 < k₀) (hk₀_lt : k₀ < n)
    (hnonS_pos : 0 < nonS) (hnonS_odd : nonS % 2 = 1) (hnonS_le : nonS ≤ k₀)
    (hdet_nonS : ↑nonS * ↑b - ↑(k₀ - nonS) * ↑(2 * a) = (1 : ℤ) ∨
       ↑nonS * ↑b - ↑(k₀ - nonS) * ↑(2 * a) = (-1 : ℤ))
    (hgood : ∀ i : Fin (n - 1),
      (Necklace.kStepVector w (r + i.val * k₀) k₀) .s = ↑(k₀ - nonS))
    (hbad : (Necklace.kStepVector w (r + (n - 1) * k₀) k₀) .s ≠ ↑(k₀ - nonS)) :
    let seq := fun (j : ℕ) => Necklace.kStepVector w (r + j * k₀) k₀
    let g3 := Necklace.kStepVector w (r + (n - 1) * k₀) k₀
    (g3 .L = (seq 0) .L ∨ g3 .L = (seq 1) .L) ∧
    (g3 .m = (seq 0) .m ∨ g3 .m = (seq 1) .m) := by
  intro seq g3
  have hn_pos : 0 < n := by omega
  -- Good positions: .L + .m = nonS (since .s = k₀ - nonS and .L + .m + .s = k₀)
  have hcast_sub : (↑(k₀ - nonS) : ℤ) = ↑k₀ - ↑nonS := by omega
  have h0Lm : seq 0 .L + seq 0 .m = ↑nonS := by
    have htot := kStepVector_component_sum w (r + 0 * k₀) k₀
    rw [stepSize_sum] at htot
    have hs_eq := hgood ⟨0, by omega⟩; simp only [seq] at hs_eq ⊢
    linarith [hcast_sub]
  have h1Lm : seq 1 .L + seq 1 .m = ↑nonS := by
    have htot := kStepVector_component_sum w (r + 1 * k₀) k₀
    rw [stepSize_sum] at htot
    have hs_eq := hgood ⟨1, by omega⟩; simp only [seq] at hs_eq ⊢
    linarith [hcast_sub]
  -- Expand determinant: nonS * n = 2a * k₀ ± 1
  have hdet_expand : ↑nonS * ↑n = ↑(2 * a) * ↑k₀ + (1 : ℤ) ∨
      ↑nonS * ↑n = ↑(2 * a) * ↑k₀ - (1 : ℤ) := by
    rcases hdet_nonS with h | h <;> [left; right] <;> {
      have : (↑(k₀ - nonS) : ℤ) = ↑k₀ - ↑nonS := by omega
      have : (↑b : ℤ) = ↑n - ↑(2 * a) := by push_cast; omega
      nlinarith
    }
  -- nonS < 2a from the determinant + parity
  have hnonS_lt_2a : nonS < 2 * a := by
    have h_ub : (↑nonS : ℤ) * ↑n ≤ ↑(2 * a) * ↑k₀ + 1 := by
      rcases hdet_expand with h | h <;> linarith
    have h1 : (↑nonS : ℤ) * ↑n < ↑(2 * a) * ↑n + 1 := by
      have : (↑k₀ : ℤ) < ↑n := by exact_mod_cast hk₀_lt
      have : (0 : ℤ) < ↑(2 * a) := by exact_mod_cast show 0 < 2 * a by omega
      nlinarith
    have h2 : nonS ≤ 2 * a := by
      by_contra h; push_neg at h
      have : (↑(2 * a) : ℤ) + 1 ≤ ↑nonS := by exact_mod_cast h
      nlinarith [show (↑n : ℤ) ≥ 1 from by exact_mod_cast hn_pos]
    omega
  -- Step 3: g3.s from s-sum + determinant.
  -- ∑ j=0..n-1 seq(j).s = k₀ * b (via coprime reindexing)
  have hs_sum : ∑ j ∈ Finset.range n, seq j .s = ↑k₀ * ↑b := by
    rw [← hcounts]; exact kStepVector_stacking_sum w k₀ r hcop_k (by omega) .s
  -- Split: good (n-1 terms with s = k₀ - nonS) + closing
  have hs_split : (∑ j ∈ Finset.range (n - 1), seq j .s) + g3 .s =
      ∑ j ∈ Finset.range n, seq j .s := by
    have h := Finset.sum_range_succ (fun j => seq j .s) (n - 1)
    rw [show n - 1 + 1 = n from by omega] at h; linarith
  have hs_good : ∑ j ∈ Finset.range (n - 1), seq j .s = ↑((n - 1) * (k₀ - nonS)) := by
    have h_eq : ∀ j ∈ Finset.range (n - 1), seq j .s = (↑(k₀ - nonS) : ℤ) :=
      fun j hj => hgood ⟨j, Finset.mem_range.mp hj⟩
    rw [Finset.sum_congr rfl h_eq, Finset.sum_const, Finset.card_range]; simp
  -- g3.s = k₀*b - (n-1)*(k₀-nonS)
  have hg3s_eq : g3 .s = ↑(k₀ * b) - ↑((n - 1) * (k₀ - nonS)) := by
    have : (↑(k₀ * b) : ℤ) = ↑k₀ * ↑b := by push_cast; ring
    linarith
  -- From det: k₀*b = (k₀-nonS)*n ± 1
  have hkb : ↑(k₀ * b) = ↑(k₀ - nonS) * ↑n + (1 : ℤ) ∨
      ↑(k₀ * b) = ↑(k₀ - nonS) * ↑n - (1 : ℤ) := by
    rcases hdet_expand with h | h <;> [left; right] <;> {
      have : (↑(k₀ * b) : ℤ) = ↑k₀ * ↑b := by push_cast; ring
      have hb_cast : (↑b : ℤ) = ↑n - 2 * ↑a := by omega
      have : ↑k₀ * (↑b : ℤ) = ↑k₀ * ↑n - 2 * ↑a * ↑k₀ := by rw [hb_cast]; ring
      have : ↑(k₀ - nonS) * (↑n : ℤ) = ↑k₀ * ↑n - ↑nonS * ↑n := by rw [hcast_sub]; ring
      have : ↑(2 * a) * (↑k₀ : ℤ) = 2 * ↑a * ↑k₀ := by push_cast; ring
      linarith
    }
  -- g3.s = (k₀-nonS)*n ± 1 - (n-1)*(k₀-nonS) = (k₀-nonS) ± 1
  have hg3s_val : g3 .s = ↑(k₀ - nonS) + 1 ∨ g3 .s = ↑(k₀ - nonS) - 1 := by
    have hn1 : (↑(n - 1) : ℤ) = ↑n - 1 := by omega
    rcases hkb with h | h <;> [left; right] <;> {
      rw [hg3s_eq, h]; push_cast; rw [hn1]; ring
    }
  -- g3.L + g3.m + g3.s = k₀
  have hg3_tot := kStepVector_component_sum w (r + (n - 1) * k₀) k₀
  rw [stepSize_sum] at hg3_tot; change _ at hg3_tot
  -- g3.L + g3.m = nonS ∓ 1
  have hg3_Lm : g3 .L + g3 .m = ↑nonS - 1 ∨ g3 .L + g3 .m = ↑nonS + 1 := by
    rcases hg3s_val with hs | hs <;> [left; right] <;> linarith [hcast_sub]

  -- Step 4: L-sum and m-sum via coprime reindexing.
  have hL_sum : ∑ j ∈ Finset.range n, seq j .L = ↑k₀ * ↑a := by
    rw [← hcountL]; exact kStepVector_stacking_sum w k₀ r hcop_k (by omega) .L
  have hm_sum : ∑ j ∈ Finset.range n, seq j .m = ↑k₀ * ↑a := by
    rw [← hcountm]; exact kStepVector_stacking_sum w k₀ r hcop_k (by omega) .m
  -- Split into good + closing
  have hL_split : (∑ j ∈ Finset.range (n - 1), seq j .L) + g3 .L = ↑k₀ * ↑a := by
    have h := Finset.sum_range_succ (fun j => seq j .L) (n - 1)
    rw [show n - 1 + 1 = n from by omega] at h; linarith
  have hm_split : (∑ j ∈ Finset.range (n - 1), seq j .m) + g3 .m = ↑k₀ * ↑a := by
    have h := Finset.sum_range_succ (fun j => seq j .m) (n - 1)
    rw [show n - 1 + 1 = n from by omega] at h; linarith
  -- Equating L and m: good_L + g3.L = good_m + g3.m
  have hLm_eq : (∑ j ∈ Finset.range (n - 1), seq j .L) + g3 .L =
      (∑ j ∈ Finset.range (n - 1), seq j .m) + g3 .m := by linarith

  -- Step 5: From the AS, good positions alternate: seq(i) = seq(i%2) for i < n-1.
  -- Good sum of (.L - .m) telescopes to (n-1)/2 * (seq(0).L - seq(0).m + seq(1).L - seq(1).m)
  -- = (n-1)/2 * ((seq(0).L + seq(1).L) - (seq(0).m + seq(1).m))
  -- = (n-1)/2 * (2*(seq(0).L + seq(1).L) - 2*nonS)
  -- = (n-1) * (seq(0).L + seq(1).L - nonS)
  -- From hLm_eq: this = g3.m - g3.L.
  -- Since |g3.L - g3.m| ≤ g3.L + g3.m ≤ nonS + 1 < 2a + 2 ≤ n,
  -- and (n-1)|g3.m - g3.L|, we need g3.L = g3.m (and seq(0).L + seq(1).L = nonS).
  -- This requires the alternation data from oddRegular_construct_AS.

  -- Get the alternation: seq(i) = seq(i%2) for i < n-1
  have ⟨halt, hLdiff, has⟩ := oddRegular_construct_AS w hodd a b ha_pos hn_eq hcountL hcountm hcounts hdel
    k₀ hcop_k hk₀_pos hk₀_lt r nonS hnonS_pos hnonS_odd hnonS_le hgood hbad
  -- halt gives: kStepVector(r+i*k₀, k₀) = kStepVector(r+(i%2)*k₀, k₀) for i < n-1
  -- Key fact: at good positions, seq(i).L depends only on i%2.
  have hgood_alt : ∀ i : Fin (n - 1), seq i.val .L = seq (i.val % 2) .L := by
    intro ⟨i, hi⟩
    exact congr_fun (halt ⟨i, hi⟩) .L
  -- Good L-sum = (n-1)/2 * (seq(0).L + seq(1).L)
  have hL_good : ∑ j ∈ Finset.range (n - 1), seq j .L =
      ↑((n - 1) / 2) * (seq 0 .L + seq 1 .L) := by
    have hterms : ∀ j ∈ Finset.range (n - 1),
        seq j .L = if j % 2 = 0 then seq 0 .L else seq 1 .L := by
      intro j hj; rw [hgood_alt ⟨j, Finset.mem_range.mp hj⟩]
      split_ifs with h
      · exact congr_arg (· .L) (show seq (j % 2) = seq 0 from by rw [h])
      · exact congr_arg (· .L) (show seq (j % 2) = seq 1 from by
          rw [show j % 2 = 1 from Nat.mod_two_ne_zero.mp h])
    rw [Finset.sum_congr rfl hterms, show n - 1 = 2 * ((n - 1) / 2) from by omega,
        show 2 * ((n - 1) / 2) / 2 = (n - 1) / 2 from by omega, mul_add]
    exact alternating_sum ((n - 1) / 2) (seq 0 .L) (seq 1 .L)
  -- Similarly for m
  have hgood_alt_m : ∀ i : Fin (n - 1), seq i.val .m = seq (i.val % 2) .m := by
    intro ⟨i, hi⟩
    -- From h0Lm/h1Lm + hgood: .L + .m = nonS at all good positions
    -- So .m = nonS - .L. Combined with .L alternation, .m alternates.
    have hLm_i : seq i .L + seq i .m = ↑nonS := by
      have htot := kStepVector_component_sum w (r + i * k₀) k₀
      rw [stepSize_sum] at htot
      have hs_eq := hgood ⟨i, hi⟩; simp only [seq] at hs_eq ⊢; linarith [hcast_sub]
    have hLm_i2 : seq (i % 2) .L + seq (i % 2) .m = ↑nonS := by
      rcases Nat.mod_two_eq_zero_or_one i with h | h <;> rw [h] <;> [exact h0Lm; exact h1Lm]
    linarith [hgood_alt ⟨i, hi⟩]
  have hm_good : ∑ j ∈ Finset.range (n - 1), seq j .m =
      ↑((n - 1) / 2) * (seq 0 .m + seq 1 .m) := by
    have hterms : ∀ j ∈ Finset.range (n - 1),
        seq j .m = if j % 2 = 0 then seq 0 .m else seq 1 .m := by
      intro j hj; rw [hgood_alt_m ⟨j, Finset.mem_range.mp hj⟩]
      split_ifs with h
      · exact congr_arg (· .m) (show seq (j % 2) = seq 0 from by rw [h])
      · exact congr_arg (· .m) (show seq (j % 2) = seq 1 from by
          rw [show j % 2 = 1 from Nat.mod_two_ne_zero.mp h])
    rw [Finset.sum_congr rfl hterms, show n - 1 = 2 * ((n - 1) / 2) from by omega,
        show 2 * ((n - 1) / 2) / 2 = (n - 1) / 2 from by omega, mul_add]
    exact alternating_sum ((n - 1) / 2) (seq 0 .m) (seq 1 .m)
  -- From hLm_eq + hL_good + hm_good:
  -- (n-1)/2 * (seq(0).L + seq(1).L) + g3.L = (n-1)/2 * (seq(0).m + seq(1).m) + g3.m
  -- Let S_L = seq(0).L + seq(1).L, S_m = seq(0).m + seq(1).m
  -- S_L + S_m = 2*nonS (from h0Lm + h1Lm)
  -- g3.L - g3.m = (n-1)/2 * (S_m - S_L) = (n-1)/2 * (2*nonS - 2*S_L) = (n-1)*(nonS - S_L)
  set S_L := seq 0 .L + seq 1 .L with hSL_def
  have hSm : seq 0 .m + seq 1 .m = 2 * ↑nonS - S_L := by linarith
  have hg3_diff : g3 .L - g3 .m = ↑((n - 1) / 2) * (seq 0 .m + seq 1 .m - S_L) := by
    linarith [hLm_eq, hL_good, hm_good]
  have hg3_diff2 : g3 .L - g3 .m = ↑(n - 1) * (↑nonS - S_L) := by
    have hn1_eq : (↑(n - 1) : ℤ) = 2 * ↑((n - 1) / 2) := by push_cast; omega
    rw [hg3_diff, hSm, hn1_eq]; ring
  -- Bounding: |g3.L - g3.m| ≤ g3.L + g3.m ≤ nonS + 1 ≤ 2a ≤ n - 1
  have hg3L_nn : g3 .L ≥ 0 := by
    simp only [g3]; unfold Necklace.kStepVector ZVector.ofList; exact_mod_cast Nat.zero_le _
  have hg3m_nn : g3 .m ≥ 0 := by
    simp only [g3]; unfold Necklace.kStepVector ZVector.ofList; exact_mod_cast Nat.zero_le _
  have hg3_bound : |g3 .L - g3 .m| ≤ ↑(n - 1) := by
    have h1 : |g3 .L - g3 .m| ≤ g3 .L + g3 .m := by
      rw [abs_le]; constructor <;> linarith
    have h2 : g3 .L + g3 .m ≤ ↑nonS + 1 := by
      rcases hg3_Lm with h | h <;> linarith
    have h3 : (↑nonS : ℤ) + 1 ≤ ↑(2 * a) := by exact_mod_cast hnonS_lt_2a
    have h4 : (↑(2 * a) : ℤ) ≤ ↑(n - 1) := by push_cast; omega
    linarith
  -- From hg3_diff2: g3.L - g3.m = (n-1) * (nonS - S_L).
  -- If |nonS - S_L| ≥ 2, then |g3.L-g3.m| ≥ 2(n-1) > n-1 ≥ |g3.L-g3.m|. Contradiction.
  -- If |nonS - S_L| = 1, then |g3.L-g3.m| = n-1 and g3.L+g3.m ≤ nonS+1 ≤ n-1.
  --   So max(g3.L, g3.m) ≥ (n-1)/2 and both are nonneg.
  --   WLOG g3.L-g3.m = n-1: g3.L = ((g3.L+g3.m) + (n-1))/2, g3.m = ((g3.L+g3.m)-(n-1))/2.
  --   g3.m ≥ 0 ⟹ g3.L+g3.m ≥ n-1. Combined with ≤ n-1: g3.L+g3.m = n-1 = nonS+1.
  --   So nonS = n-2 = 2a+b-2 < 2a ⟹ b < 2 ⟹ b = 1. n = 2a+1.
  --   g3.L = n-1 = 2a. But g3 counts L in k₀ < n letters, and total L count = a < 2a.
  --   Since every occurrence of L in the necklace is at most a, g3.L ≤ a < 2a. Contradiction.
  -- Therefore S_L = nonS.
  have hSL_eq : S_L = ↑nonS := by
    by_contra h
    have hne : ↑nonS - S_L ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    have habs_ge : (↑(n - 1) : ℤ) ≤ |g3 .L - g3 .m| := by
      calc (↑(n - 1) : ℤ) = ↑(n - 1) * 1 := by ring
        _ ≤ ↑(n - 1) * |↑nonS - S_L| := by
          apply mul_le_mul_of_nonneg_left (Int.one_le_abs hne); exact_mod_cast Nat.zero_le _
        _ = |↑(n - 1) * (↑nonS - S_L)| := by
          rw [abs_mul, abs_of_nonneg (show (↑(n - 1) : ℤ) ≥ 0 from by exact_mod_cast Nat.zero_le _)]
        _ = |g3 .L - g3 .m| := by rw [← hg3_diff2]
    -- So |g3.L - g3.m| = n-1 (from hg3_bound + habs_ge)
    have habs_eq : |g3 .L - g3 .m| = ↑(n - 1) := le_antisymm hg3_bound habs_ge
    -- g3.L + g3.m ≤ nonS + 1 ≤ n - 1 = |g3.L - g3.m|
    have h2 : g3 .L + g3 .m ≤ ↑nonS + 1 := by
      rcases hg3_Lm with h | h <;> linarith
    have h3 : (↑nonS : ℤ) + 1 ≤ ↑(n - 1) := by omega
    -- g3.L + g3.m ≤ |g3.L - g3.m|. Since both nonneg, one must be 0 and the other = n-1.
    -- g3.L + g3.m ≤ n - 1 = |g3.L - g3.m| ≤ g3.L + g3.m (from abs_le bound)
    -- So g3.L + g3.m = n - 1, and one of them is 0, other is n - 1.
    have h4 : g3 .L + g3 .m ≤ |g3 .L - g3 .m| := by linarith
    have h5 : g3 .L + g3 .m = ↑(n - 1) := by
      have : |g3 .L - g3 .m| ≤ g3 .L + g3 .m := by rw [abs_le]; constructor <;> linarith
      linarith
    -- g3.L ≤ a and g3.m ≤ a via kStepVector_add + kStepVector_full_cycle:
    -- kStepVector(w, i, k₀) + kStepVector(w, i+k₀, n-k₀) = kStepVector(w, i, n) = count(w)
    have hg3L_le_a : g3 .L ≤ ↑a := by
      have hadd := kStepVector_add w (r + (n - 1) * k₀) k₀ (n - k₀) .L
      rw [show k₀ + (n - k₀) = n from by omega] at hadd
      rw [kStepVector_full_cycle, hcountL] at hadd
      have : Necklace.kStepVector w (r + (n - 1) * k₀ + k₀) (n - k₀) .L ≥ 0 := by
        unfold Necklace.kStepVector ZVector.ofList; exact_mod_cast Nat.zero_le _
      simp only [g3]; linarith
    have hg3m_le_a : g3 .m ≤ ↑a := by
      have hadd := kStepVector_add w (r + (n - 1) * k₀) k₀ (n - k₀) .m
      rw [show k₀ + (n - k₀) = n from by omega] at hadd
      rw [kStepVector_full_cycle, hcountm] at hadd
      have : Necklace.kStepVector w (r + (n - 1) * k₀ + k₀) (n - k₀) .m ≥ 0 := by
        unfold Necklace.kStepVector ZVector.ofList; exact_mod_cast Nat.zero_le _
      simp only [g3]; linarith
    -- g3.L ≤ a and g3.m ≤ a, but g3.L + g3.m = n-1 = 2a+b-1 ≥ 2a.
    -- So n-1 ≤ 2a, b ≤ 1, b = 1, and both = a. Then g3.L = g3.m, so g3.L - g3.m = 0.
    -- From hg3_diff2: 0 = (n-1)*(nonS - S_L). Since n ≥ 3: nonS = S_L. Contradicts hne.
    have h6 : (↑(n - 1) : ℤ) ≤ ↑a + ↑a := by linarith [h5]
    have h6' : 2 * (↑a : ℤ) ≤ ↑(n - 1) := by omega
    have h7 : g3 .L = g3 .m := by linarith
    have h8 : g3 .L - g3 .m = 0 := by linarith
    rw [hg3_diff2] at h8
    have hn1_pos : (0 : ℤ) < ↑(n - 1) := by omega
    have h9 : ↑nonS - S_L = 0 := by
      have hmul : (↑(n - 1) : ℤ) * (↑nonS - S_L) = 0 := by linarith
      have hne' : (↑(n - 1) : ℤ) ≠ 0 := by omega
      exact (mul_eq_zero.mp hmul).resolve_left hne'
    exact absurd h9 hne
  -- g3.L = g3.m (from S_L = nonS)
  have hg3_eq : g3 .L = g3 .m := by
    have : g3 .L - g3 .m = 0 := by
      rw [hg3_diff2, show (↑nonS : ℤ) - S_L = 0 from by linarith [hSL_eq], mul_zero]
    linarith
  -- 2 * g3.L ∈ {nonS - 1, nonS + 1}
  have hg3L_val : 2 * g3 .L = ↑nonS - 1 ∨ 2 * g3 .L = ↑nonS + 1 := by
    rcases hg3_Lm with h | h <;> [left; right] <;> linarith
  -- g3.L ∈ {seq(0).L, seq(1).L}: since S_L = seq(0).L + seq(1).L = nonS, and
  -- 2*g3.L = nonS ± 1, if g3.L ≠ seq(0).L then seq(1).L = nonS - seq(0).L = g3.L.
  -- Derive g3.L result
  have hg3_L_result : g3 .L = seq 0 .L ∨ g3 .L = seq 1 .L := by
    by_cases h0 : g3 .L = seq 0 .L
    · exact Or.inl h0
    · right
      have hseq_ne : seq 0 .L ≠ seq 1 .L := by
        intro heq; have : 2 * seq 0 .L = ↑nonS := by linarith [hSL_eq, hSL_def]
        have : (↑nonS : ℤ) % 2 = 0 := by omega
        have : (nonS : ℤ) % 2 = 1 := by exact_mod_cast hnonS_odd
        omega
      have hseq0_val : 2 * seq 0 .L = ↑nonS - 1 ∨ 2 * seq 0 .L = ↑nonS + 1 := by
        simp only [seq] at hLdiff hSL_def ⊢
        rcases hLdiff with h | h <;> [right; left] <;> linarith [hSL_eq, hSL_def]
      have hne_2 : 2 * g3 .L ≠ 2 * seq 0 .L := by omega
      have hsum_2 : 2 * g3 .L + 2 * seq 0 .L = 2 * ↑nonS := by
        rcases hg3L_val with hg | hg <;> rcases hseq0_val with hs | hs <;> omega
      linarith [hSL_eq, hSL_def]
  -- Derive g3.m result: g3.m = g3.L = seq(j₀).L = nonS - seq(j₀).L = seq(1-j₀).m
  have hg3_m_result : g3 .m = seq 0 .m ∨ g3 .m = seq 1 .m := by
    rcases hg3_L_result with h0 | h1
    · -- g3.L = seq(0).L → g3.m = g3.L = seq(0).L = nonS - seq(1).L = seq(1).m
      right; linarith [hSL_eq, hSL_def]
    · -- g3.L = seq(1).L → g3.m = g3.L = seq(1).L = nonS - seq(0).L = seq(0).m
      left; linarith [hSL_eq, hSL_def]
  exact ⟨hg3_L_result, hg3_m_result⟩

/-- For any function on StepSize, the sum over a permutation of {L, m, s} equals
    the sum over {L, m, s}. -/
private lemma stepSize_sum_perm (f : StepSize → ℤ) (x y z : StepSize)
    (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y) :
    f x + f y + f z = f .L + f .m + f .s := by
  rcases x with _ | _ | _ <;> rcases y with _ | _ | _ <;>
    rcases z with _ | _ | _ <;> simp_all <;> ring

/-- In a 3-element type, if a ≠ x, a ≠ y, and {x, y, z} are pairwise distinct, then a = z. -/
private lemma stepSize_eq_third {a x y z : StepSize}
    (hax : a ≠ x) (hay : a ≠ y) (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y) : a = z := by
  rcases a with _ | _ | _ <;> rcases x with _ | _ | _ <;>
    rcases y with _ | _ | _ <;> rcases z with _ | _ | _ <;> simp_all

/-- If the k₀-step vectors alternate between two values at good positions, and
    the closing vector's z-component matches one of the alternating z-values, then
    the identified 2k₀-step vectors have an (n-1, 1) split. -/
private lemma identified_2k_stacking_split (w : TernaryNecklace n)
    (hodd : n % 2 = 1) (k₀ r nonS : ℕ)
    (_hcop_k : Nat.Coprime k₀ n) (hk₀_pos : 0 < k₀) (hk₀_lt : k₀ < n)
    (halt : ∀ i : Fin (n - 1), Necklace.kStepVector w (r + i.val * k₀) k₀ =
      Necklace.kStepVector w (r + (i.val % 2) * k₀) k₀)
    (_hgood : ∀ i : Fin (n - 1),
      (Necklace.kStepVector w (r + i.val * k₀) k₀) .s = ↑(k₀ - nonS))
    (_hbad : (Necklace.kStepVector w (r + (n - 1) * k₀) k₀) .s ≠ ↑(k₀ - nonS))
    (x y z : StepSize) (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y)
    (hg3_z : Necklace.kStepVector w (r + (n - 1) * k₀) k₀ z =
        Necklace.kStepVector w (r + 0 * k₀) k₀ z ∨
      Necklace.kStepVector w (r + (n - 1) * k₀) k₀ z =
        Necklace.kStepVector w (r + 1 * k₀) k₀ z)
    (hseq_z_ne : Necklace.kStepVector w (r + 0 * k₀) k₀ z ≠
        Necklace.kStepVector w (r + 1 * k₀) k₀ z) :
    let w' := TernaryNecklace.identifyPair w x y
    ∃ i_bad : Fin n,
      Necklace.kStepVector w' (r + i_bad.val * k₀) (2 * k₀) ≠
        Necklace.kStepVector w' r (2 * k₀) ∧
      ∀ i : Fin n, i ≠ i_bad →
        Necklace.kStepVector w' (r + i.val * k₀) (2 * k₀) =
          Necklace.kStepVector w' r (2 * k₀) := by
  intro w'
  -- Key fact: the z-component of the 2k₀-step vector determines the identified vector.
  -- After identifyPair x y: x-comp = 0, z-comp unchanged, y-comp = 2k₀ - z-comp.
  have hid_eq_iff : ∀ i j : ℕ,
      Necklace.kStepVector w' (r + i * k₀) (2 * k₀) =
        Necklace.kStepVector w' (r + j * k₀) (2 * k₀) ↔
      Necklace.kStepVector w (r + i * k₀) (2 * k₀) z =
        Necklace.kStepVector w (r + j * k₀) (2 * k₀) z := by
    intro i j
    constructor
    · intro h
      have := congr_fun h z
      rw [identifyPair_kStepVector w x y hxy _ _, identifyPair_kStepVector w x y hxy _ _] at this
      simp only [ZVector.identifyPair] at this
      rw [if_neg hzx, if_neg hzy, if_neg hzx, if_neg hzy] at this
      exact this
    · intro h
      rw [identifyPair_kStepVector w x y hxy, identifyPair_kStepVector w x y hxy]
      funext a
      simp only [ZVector.identifyPair]
      by_cases hax : a = x
      · subst hax; rw [if_pos rfl, if_pos rfl]
      · rw [if_neg hax, if_neg hax]
        by_cases hay : a = y
        · rw [if_pos hay, if_pos hay]
          have hperm_i := stepSize_sum_perm
            (Necklace.kStepVector w (r + i * k₀) (2 * k₀)) x y z hxy hzx hzy
          have hperm_j := stepSize_sum_perm
            (Necklace.kStepVector w (r + j * k₀) (2 * k₀)) x y z hxy hzx hzy
          have hsum_i := kStepVector_component_sum w (r + i * k₀) (2 * k₀)
          have hsum_j := kStepVector_component_sum w (r + j * k₀) (2 * k₀)
          rw [stepSize_sum] at hsum_i hsum_j
          linarith
        · -- a ≠ x, a ≠ y, so a = z
          have haz : a = z := stepSize_eq_third hax hay hxy hzx hzy
          rw [if_neg hay, if_neg hay]
          subst haz; exact h
  -- Shorthand for k₀-step z-component
  set Vz : ℕ → ℤ := fun j => Necklace.kStepVector w (r + j * k₀) k₀ z with hVz_def
  -- z-component of 2k₀-step vector via kStepVector_add
  have hz_2k : ∀ i : ℕ,
      Necklace.kStepVector w (r + i * k₀) (2 * k₀) z = Vz i + Vz (i + 1) := by
    intro i
    have := kStepVector_add w (r + i * k₀) k₀ k₀ z
    rw [show k₀ + k₀ = 2 * k₀ from by ring,
        show r + i * k₀ + k₀ = r + (i + 1) * k₀ from by ring] at this
    exact this
  -- For good positions i < n-1: V(i) = V(i%2) by alternation
  -- z-comp of 2k₀-step = V(i).z + V(i+1).z
  -- For i < n-2: Vz(i) + Vz(i+1) = Vz(0) + Vz(1) by alternation
  have hz_good_sum : ∀ i : ℕ, i + 1 < n - 1 → Vz i + Vz (i + 1) = Vz 0 + Vz 1 := by
    intro i hi
    have h1 : Vz i = Vz (i % 2) := congr_fun (halt ⟨i, by omega⟩) z
    have h2 : Vz (i + 1) = Vz ((i + 1) % 2) := congr_fun (halt ⟨i + 1, by omega⟩) z
    rw [h1, h2]
    rcases Nat.mod_two_eq_zero_or_one i with hmod | hmod
    · have h3 : (i + 1) % 2 = 1 := by omega
      rw [hmod, h3]
    · have h3 : (i + 1) % 2 = 0 := by omega
      rw [hmod, h3, add_comm]
  -- Vz(n-2) = Vz(1) since (n-2)%2 = 1
  have hVz_n2 : Vz (n - 2) = Vz 1 := by
    show Necklace.kStepVector w (r + (n - 2) * k₀) k₀ z =
      Necklace.kStepVector w (r + 1 * k₀) k₀ z
    have h := congr_fun (halt ⟨n - 2, by omega⟩) z
    rwa [show (n - 2) % 2 = 1 from by omega] at h
  -- Vz(n) = Vz(0) by mod-n periodicity
  have hVz_n_wrap : Vz n = Vz 0 := by
    show Necklace.kStepVector w (r + n * k₀) k₀ z = Necklace.kStepVector w (r + 0 * k₀) k₀ z
    rw [Nat.zero_mul, Nat.add_zero]
    have h1 := kStepVector_mod_n w (r + n * k₀) k₀
    rw [Nat.add_mul_mod_self_left] at h1
    have h2 := kStepVector_mod_n w r k₀
    exact congr_fun (h1.symm.trans h2) z
  -- Convert hg3_z/hseq_z_ne to use Vz
  have hg3_z' : Vz (n - 1) = Vz 0 ∨ Vz (n - 1) = Vz 1 := hg3_z
  have hseq_z_ne' : Vz 0 ≠ Vz 1 := hseq_z_ne
  rcases hg3_z' with hg3_z0 | hg3_z1
  · -- Vz(n-1) = Vz(0): bad index is n-1
    refine ⟨⟨n - 1, by omega⟩, ?_, ?_⟩
    · -- bad: 2k₀-step at n-1 ≠ 2k₀-step at 0
      intro heq
      -- Normalize heq to match hid_eq_iff pattern
      have heq' : w'.kStepVector (r + (n - 1) * k₀) (2 * k₀) =
          w'.kStepVector (r + 0 * k₀) (2 * k₀) := by
        simp only [Nat.zero_mul, Nat.add_zero]; exact heq
      have hzeq := (hid_eq_iff (n - 1) 0).mp heq'
      rw [hz_2k (n - 1), hz_2k 0,
          show n - 1 + 1 = n from by omega, show (0 : ℕ) + 1 = 1 from rfl,
          hVz_n_wrap, hg3_z0] at hzeq
      exact hseq_z_ne' (by linarith)
    · -- good: for i ≠ n-1
      intro i hi
      suffices h : w'.kStepVector (r + i.val * k₀) (2 * k₀) = w'.kStepVector (r + 0 * k₀) (2 * k₀) by
        simpa only [Nat.zero_mul, Nat.add_zero] using h
      apply (hid_eq_iff i.val 0).mpr
      rw [hz_2k i.val, hz_2k 0, show (0 : ℕ) + 1 = 1 from rfl]
      by_cases hi_lt : i.val + 1 < n - 1
      · exact hz_good_sum i.val hi_lt
      · -- i.val = n-2
        have hival : i.val = n - 2 := by
          have := i.isLt; have : i.val ≠ n - 1 := fun h => hi (Fin.ext h); omega
        rw [hival, show n - 2 + 1 = n - 1 from by omega, hVz_n2, hg3_z0, add_comm]
  · -- Vz(n-1) = Vz(1): bad index is n-2
    refine ⟨⟨n - 2, by omega⟩, ?_, ?_⟩
    · -- bad: 2k₀-step at n-2 ≠ 2k₀-step at 0
      intro heq
      -- Normalize heq to match hid_eq_iff pattern
      have heq' : w'.kStepVector (r + (n - 2) * k₀) (2 * k₀) =
          w'.kStepVector (r + 0 * k₀) (2 * k₀) := by
        simp only [Nat.zero_mul, Nat.add_zero]; exact heq
      have hzeq := (hid_eq_iff (n - 2) 0).mp heq'
      rw [hz_2k (n - 2), hz_2k 0,
          show n - 2 + 1 = n - 1 from by omega, show (0 : ℕ) + 1 = 1 from rfl,
          hVz_n2, hg3_z1] at hzeq
      exact hseq_z_ne' (by linarith)
    · -- good: for i ≠ n-2
      intro i hi
      suffices h : w'.kStepVector (r + i.val * k₀) (2 * k₀) = w'.kStepVector (r + 0 * k₀) (2 * k₀) by
        simpa only [Nat.zero_mul, Nat.add_zero] using h
      apply (hid_eq_iff i.val 0).mpr
      rw [hz_2k i.val, hz_2k 0, show (0 : ℕ) + 1 = 1 from rfl]
      by_cases hi_lt : i.val + 1 < n - 1
      · exact hz_good_sum i.val hi_lt
      · -- i.val = n-1
        have hival : i.val = n - 1 := by
          have := i.isLt; have : i.val ≠ n - 2 := fun h => hi (Fin.ext h); omega
        rw [hival, show n - 1 + 1 = n from by omega, hVz_n_wrap, hg3_z1, add_comm]

/-- From a (n-1, 1) split for 2k₀-step identified vectors, derive ≤ 2 k-step multisets
    for all k. Uses `lk_le_two_of_constant_good` with k' = 2k₀ after reindexing the
    stacking positions, then coprime reduction for arbitrary k. -/
private lemma allK_le_two_of_2k_split (w' : TernaryNecklace n)
    (hodd : n % 2 = 1) (k₀ : ℕ) (hcop_k : Nat.Coprime k₀ n) (_hk₀_pos : 0 < k₀)
    (hcop_2k : Nat.Coprime (2 * k₀) n)
    (r : ℕ) (hn_ge : n ≥ 3)
    (T_good : ZVector StepSize)
    (_hT_def : T_good = Necklace.kStepVector w' r (2 * k₀))
    (hsplit : ∃ i_bad : Fin n,
      Necklace.kStepVector w' (r + i_bad.val * k₀) (2 * k₀) ≠ T_good ∧
      ∀ i : Fin n, i ≠ i_bad →
        Necklace.kStepVector w' (r + i.val * k₀) (2 * k₀) = T_good) :
    ∀ k : ℕ, 0 < k → k < n →
      (Necklace.allKStepMultisets w' k).toFinset.card ≤ 2 := by
  obtain ⟨i_bad, hbad_vec, hgood_all⟩ := hsplit
  -- Step 1: Any position p with kStepVector ≠ T_good must be ≡ r + i_bad*k₀ (mod n)
  set p_bad := r + i_bad.val * k₀
  have honly_bad : ∀ p, Necklace.kStepVector w' p (2 * k₀) ≠ T_good →
      p % n = p_bad % n := by
    intro p hp
    by_contra hne
    have hp_mod := kStepVector_mod_n w' p (2 * k₀)
    -- Find j ∈ Fin n with (r + j*k₀) % n = p % n
    have hk_unit := coprime_isUnit_zmod k₀ hcop_k (by omega : n ≥ 2)
    set g : ZMod n → ZMod n := fun j => (↑r : ZMod n) + j * (↑k₀ : ZMod n)
    have g_surj : Function.Surjective g := by
      apply Finite.surjective_of_injective
      intro j₁ j₂ h
      have h1 : j₁ * (↑k₀ : ZMod n) = j₂ * (↑k₀ : ZMod n) := add_left_cancel h
      rw [mul_comm j₁, mul_comm j₂] at h1; exact hk_unit.mul_left_cancel h1
    obtain ⟨j, hgj⟩ := g_surj (↑(p % n) : ZMod n)
    have hmod_eq : (r + j.val * k₀) % n = p % n := by
      have h1 : (↑(r + j.val * k₀) : ZMod n) = (↑(p % n) : ZMod n) := by
        rw [Nat.cast_add, Nat.cast_mul, natCast_zmod_val]; exact hgj
      have h2 := congr_arg ZMod.val h1
      rwa [ZMod.val_natCast, ZMod.val_natCast,
           Nat.mod_eq_of_lt (Nat.mod_lt p (by omega))] at h2
    -- Convert j : ZMod n to Fin n
    have hj_lt : j.val < n := ZMod.val_lt j
    set j' : Fin n := ⟨j.val, hj_lt⟩
    -- j' ≠ i_bad (because p % n ≠ p_bad % n)
    have hj_ne : j' ≠ i_bad := by
      intro heq
      have : j.val = i_bad.val := congrArg Fin.val heq
      rw [this] at hmod_eq; exact hne hmod_eq.symm
    -- So kStepVector at (r + j*k₀) = T_good
    have hgood_j := hgood_all j' hj_ne
    -- But kStepVector at p = kStepVector at (r + j*k₀) (same mod n)
    -- hgood_j: kStepVector w' (r + j'.val * k₀) = T_good
    -- We need: kStepVector w' p = T_good (to contradict hp)
    apply hp
    rw [← hp_mod, ← hmod_eq, kStepVector_mod_n]
    exact hgood_j
  -- Step 2: Reindex for lk_le_two_of_constant_good with k' = 2k₀
  set r' := p_bad + 2 * k₀
  have hT_eq : ∀ i : Fin (n - 1),
      Necklace.kStepVector w' (r' + i.val * (2 * k₀)) (2 * k₀) = T_good := by
    intro i
    by_contra h
    have hmod := honly_bad _ h
    -- (r' + i * (2k₀)) % n = p_bad % n
    -- r' = p_bad + 2k₀, so (p_bad + (i+1)*(2k₀)) % n = p_bad % n
    -- (i+1)*(2k₀) ≡ 0 (mod n), gcd(2k₀,n) = 1 → n | (i+1)
    have hrw : (r' + i.val * (2 * k₀)) % n = (p_bad + (i.val + 1) * (2 * k₀)) % n := by
      congr 1; show p_bad + 2 * k₀ + i.val * (2 * k₀) = p_bad + (i.val + 1) * (2 * k₀); ring
    rw [hrw] at hmod
    have hmod2 : ((i.val + 1) * (2 * k₀)) % n = 0 := by
      have hmod3 := Nat.sub_mod_eq_zero_of_mod_eq hmod
      rwa [show p_bad + (i.val + 1) * (2 * k₀) - p_bad = (i.val + 1) * (2 * k₀) from by omega]
        at hmod3
    have hdvd : n ∣ (i.val + 1) * (2 * k₀) := Nat.dvd_of_mod_eq_zero hmod2
    have hdvd_i : n ∣ i.val + 1 := by
      have hdvd' : n ∣ (2 * k₀) * (i.val + 1) := by rwa [mul_comm]
      exact hcop_2k.symm.dvd_of_dvd_mul_left hdvd'
    have hi_lt := i.isLt  -- i.val < n - 1
    have hi_pos : 0 < i.val + 1 := by omega
    exact absurd (Nat.le_of_dvd hi_pos hdvd_i) (by omega)
  have hbad' : Necklace.kStepVector w' (r' + (n - 1) * (2 * k₀)) (2 * k₀) ≠ T_good := by
    rw [show r' + (n - 1) * (2 * k₀) = p_bad + n * (2 * k₀) from by
      show p_bad + 2 * k₀ + (n - 1) * (2 * k₀) = p_bad + n * (2 * k₀)
      have h1 : n - 1 + 1 = n := by omega
      nlinarith]
    rw [← kStepVector_mod_n w' (p_bad + n * (2 * k₀)) (2 * k₀)]
    rw [Nat.add_mul_mod_self_left]
    rw [kStepVector_mod_n]
    exact hbad_vec
  -- Step 3: Apply lk_le_two_of_constant_good
  intro k hk_pos hk_lt
  -- Find l with l * (2k₀) % n = k
  obtain ⟨l₀, hl₀_pos, hl₀_lt, hl₀_inv⟩ := exists_modular_inverse (2 * k₀) hcop_2k (by omega)
  set l := l₀ * k % n
  have hl_lt : l < n := Nat.mod_lt _ (by omega)
  have hlk : l * (2 * k₀) % n = k := by
    have : l₀ * (2 * k₀) % n = 1 := hl₀_inv
    have : l * (2 * k₀) % n = l₀ * k % n * (2 * k₀) % n := rfl
    rw [this, Nat.mul_mod, Nat.mod_mod_of_dvd, ← Nat.mul_mod,
        show l₀ * k * (2 * k₀) = l₀ * (2 * k₀) * k from by ring, Nat.mul_mod, hl₀_inv,
        one_mul, Nat.mod_mod_of_dvd, Nat.mod_eq_of_lt hk_lt]
    all_goals exact dvd_refl _
  have hl_pos : 0 < l := by
    by_contra h; push_neg at h
    have hl0 : l = 0 := by omega
    rw [hl0, zero_mul, Nat.zero_mod] at hlk; omega
  have hl_le : l ≤ n - 1 := by omega
  -- lk_le_two_of_constant_good gives allKStepVectors(w', l*(2k₀)) ≤ 2
  have h2 := lk_le_two_of_constant_good w' (2 * k₀) r' l hcop_2k hn_ge hl_pos hl_le
    T_good hT_eq hbad'
  -- Transfer: allKStepVectors card for l*(2k₀) = card for k (mod n reduction)
  rw [← distinctKStepVectors_card_eq]
  unfold distinctKStepVectors
  rw [← hlk, ← kStepVectors_card_mod_n]; exact h2

/-- Non-equinumerous pair identification gives a MOS (2k₀ aggregate stacking). -/
private lemma nonEquinumerous_identifyPair_hasMOS (w : TernaryNecklace n)
    (hodd : n % 2 = 1) (a b : ℕ)
    (ha_pos : a > 0) (hb_pos : b > 0) (hcop : Nat.Coprime (2 * a) b)
    (hn_eq : n = 2 * a + b)
    (hcountL : Necklace.count w .L = a) (hcountm : Necklace.count w .m = a)
    (hcounts : Necklace.count w .s = b)
    (hmos_Lm : isPartialPairwiseMOS w .L .m)
    (hdel : isPartialDeletionMOS w .s) :
    isPartialPairwiseMOS w .m .s ∧ isPartialPairwiseMOS w .L .s := by
  have hn_ge : n ≥ 3 := by omega
  -- Extract k₀-step generator data from the L=m binary MOS
  obtain ⟨k₀, hcop_k, hk₀_pos, hk₀_lt, r, nonS, hnonS_pos, hnonS_odd, hnonS_le, _hdet, hgood, hbad⟩ :=
    oddRegular_kstep_data w hodd a b ha_pos hb_pos hcop hn_eq hcountL hcountm hcounts hmos_Lm
  -- Key abbreviations
  set seq := fun (j : ℕ) => Necklace.kStepVector w (r + j * k₀) k₀ with hseq_def
  set g3 := Necklace.kStepVector w (r + (n - 1) * k₀) k₀ with hg3_def
  -- The closing vector's L-component matches one of the alternating values
  have ⟨hg3_L, hg3_m⟩ := closing_L_in_seq_L w hodd a b ha_pos hb_pos hcop hn_eq
    hcountL hcountm hcounts hmos_Lm hdel k₀ r nonS hcop_k hk₀_pos hk₀_lt
    hnonS_pos hnonS_odd hnonS_le _hdet hgood hbad
  -- 2k₀ coprime to n (since k₀ coprime to n and n odd)
  have hcop_2k : Nat.Coprime (2 * k₀) n := by
    have : Nat.Coprime 2 n := by
      rw [Nat.coprime_two_left]
      rwa [Nat.odd_iff]
    exact this.mul_left hcop_k
  -- Get alternation data (shared by both cases)
  have ⟨halt, hLdiff, _⟩ := oddRegular_construct_AS w hodd a b ha_pos hn_eq
    hcountL hcountm hcounts hdel k₀ hcop_k hk₀_pos hk₀_lt r nonS
    hnonS_pos hnonS_odd hnonS_le hgood hbad
  -- seq(0).L ≠ seq(1).L (from L-difference = ±1)
  have hseq_L_ne : seq 0 .L ≠ seq 1 .L := by
    intro heq
    have heq' : Necklace.kStepVector w (r + 0 * k₀) k₀ .L =
        Necklace.kStepVector w (r + 1 * k₀) k₀ .L := heq
    rcases hLdiff with h | h <;> linarith
  -- seq(0).m ≠ seq(1).m (from L + m = nonS constant and L differs)
  have hseq_m_ne : seq 0 .m ≠ seq 1 .m := by
    intro heq
    have heq' : Necklace.kStepVector w (r + 0 * k₀) k₀ .m =
        Necklace.kStepVector w (r + 1 * k₀) k₀ .m := heq
    have h0s := hgood ⟨0, by omega⟩
    have h1s := hgood ⟨1, by omega⟩
    have h0sum := kStepVector_component_sum w (r + 0 * k₀) k₀
    have h1sum := kStepVector_component_sum w (r + 1 * k₀) k₀
    rw [stepSize_sum] at h0sum h1sum
    -- h0s/h1s say seq(i).s = k₀ - nonS, so seq(i).L + seq(i).m = nonS
    -- heq' says seq(0).m = seq(1).m, so seq(0).L = seq(1).L
    have : Necklace.kStepVector w (r + 0 * k₀) k₀ .L =
        Necklace.kStepVector w (r + 1 * k₀) k₀ .L := by linarith
    exact hseq_L_ne this
  constructor
  · -- isPartialPairwiseMOS w .m .s
    show Necklace.hasMOSProperty (TernaryNecklace.identifyPair w .m .s)
    constructor
    · exact identified_uses_two_values w (isTernary_of_positive_counts hcountL hcountm hcounts
        ha_pos ha_pos hb_pos) .m .s (by decide)
    · -- (n-1, 1) split for 2k₀-step identified vectors under m=s, then reduction
      set w_ms := TernaryNecklace.identifyPair w .m .s with hw_ms_def
      have hsplit := identified_2k_stacking_split w hodd k₀ r nonS hcop_k hk₀_pos hk₀_lt
        halt hgood hbad .m .s .L (by decide) (by decide) (by decide) hg3_L hseq_L_ne
      exact allK_le_two_of_2k_split w_ms hodd k₀ hcop_k hk₀_pos hcop_2k r hn_ge
        (Necklace.kStepVector w_ms r (2 * k₀)) rfl hsplit
  · -- isPartialPairwiseMOS w .L .s
    show Necklace.hasMOSProperty (TernaryNecklace.identifyPair w .L .s)
    constructor
    · exact identified_uses_two_values w (isTernary_of_positive_counts hcountL hcountm hcounts
        ha_pos ha_pos hb_pos) .L .s (by decide)
    · -- (n-1, 1) split for 2k₀-step identified vectors under L=s, then reduction
      set w_Ls := TernaryNecklace.identifyPair w .L .s with hw_Ls_def
      have hsplit := identified_2k_stacking_split w hodd k₀ r nonS hcop_k hk₀_pos hk₀_lt
        halt hgood hbad .L .s .m (by decide) (by decide) (by decide) hg3_m hseq_m_ne
      exact allK_le_two_of_2k_split w_Ls hodd k₀ hcop_k hk₀_pos hcop_2k r hn_ge
        (Necklace.kStepVector w_Ls r (2 * k₀)) rfl hsplit

/-- Odd-regular scales are pairwise-primitive-MOS. -/
theorem oddRegular_isPairwisePrimMOS (w : TernaryNecklace n)
    (h : isOddRegular w) : isPairwisePrimMOS w := by
  obtain ⟨hprim, hodd, σ, a, b, ha_pos, hb_pos, hb_odd, hcop, hn_eq,
    hcountL, hcountm, hcounts, hmos, hdel⟩ := h
  set w' := Necklace.applyPerm σ w
  -- Transfer back through σ at the end
  apply isPairwisePrimMOS_of_applyPerm σ
  -- Now show isPairwisePrimMOS w'
  -- Part 1: L=m identification (equinumerous)
  have hmos_Lm : isPartialPairwisePrimMOS w' .L .m := by
    refine ⟨hmos, ?_⟩
    -- Use identifiedToBinary bridge: msToBinary ∘ (identifyPair w' .L .m) is primitive
    have hB_prim : Necklace.isPrimitive (identifiedToBinary (TernaryNecklace.identifyPair w' .L .m)) :=
      necklace_with_coprime_sig_is_primitive n (2 * a) b hcop _
        (identifiedToBinary_count_L w' hcountL hcountm)
        (identifiedToBinary_count_s w' hcounts)
    -- Transfer back: if msToBinary ∘ v is primitive, then v is primitive
    exact isPrimitive_of_comp _ msToBinary hB_prim
  -- Part 2: m=s and L=s identifications (non-equinumerous)
  have hmos_ms_Ls := nonEquinumerous_identifyPair_hasMOS w' hodd a b ha_pos hb_pos hcop hn_eq
    hcountL hcountm hcounts hmos hdel
  -- Coprimality for non-equinumerous pairs: gcd(a, a+b) = 1
  have hab_coprime : Nat.Coprime a (a + b) := by
    show Nat.gcd a (a + b) = 1
    rw [show a + b = b + a from by omega, Nat.gcd_add_self_right]
    exact coprime_of_double_coprime a b hcop hb_odd
  have hmos_ms : isPartialPairwisePrimMOS w' .m .s := by
    refine ⟨hmos_ms_Ls.1, ?_⟩
    apply isPrimitive_of_comp _ msToBinary
    apply necklace_with_coprime_sig_is_primitive n a (a + b) hab_coprime
    · -- count L = a: only L positions in w' map to BinaryStep.L
      show Finset.card (Finset.filter (fun i => msToBinary ((TernaryNecklace.identifyPair w' .m .s) i) = .L) Finset.univ) = a
      have : Finset.filter (fun i => msToBinary ((TernaryNecklace.identifyPair w' .m .s) i) = .L)
          Finset.univ = Finset.filter (fun i => w' i = .L) Finset.univ := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          TernaryNecklace.identifyPair, msToBinary]
        constructor
        · intro h; cases hw : w' i <;> simp_all
        · intro h; simp [h]
      rw [this]; exact hcountL
    · -- count s = a + b: m and s positions both map to BinaryStep.s
      show Finset.card (Finset.filter (fun i => msToBinary ((TernaryNecklace.identifyPair w' .m .s) i) = .s) Finset.univ) = a + b
      have : Finset.filter (fun i => msToBinary ((TernaryNecklace.identifyPair w' .m .s) i) = .s)
          Finset.univ =
          Finset.filter (fun i => w' i = .m) Finset.univ ∪
          Finset.filter (fun i => w' i = .s) Finset.univ := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
          TernaryNecklace.identifyPair, msToBinary]
        constructor
        · intro h; cases hw : w' i <;> simp_all
        · rintro (h | h) <;> simp_all
      rw [this, Finset.card_union_of_disjoint]
      · unfold Necklace.count at hcountm hcounts; omega
      · rw [Finset.disjoint_filter]; intro i _ h1 h2; rw [h1] at h2; exact absurd h2 (by decide)
  have hmos_Ls : isPartialPairwisePrimMOS w' .L .s := by
    refine ⟨hmos_ms_Ls.2, ?_⟩
    apply isPrimitive_of_comp _ msToBinary
    apply necklace_with_coprime_sig_is_primitive n a (a + b) hab_coprime
    · -- count L = a: only m positions in w' map to BinaryStep.L
      show Finset.card (Finset.filter (fun i => msToBinary ((TernaryNecklace.identifyPair w' .L .s) i) = .L) Finset.univ) = a
      have : Finset.filter (fun i => msToBinary ((TernaryNecklace.identifyPair w' .L .s) i) = .L)
          Finset.univ = Finset.filter (fun i => w' i = .m) Finset.univ := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          TernaryNecklace.identifyPair, msToBinary]
        constructor
        · intro h; cases hw : w' i <;> simp_all
        · intro h; simp [h]
      rw [this]; exact hcountm
    · -- count s = a + b: L and s positions both map to BinaryStep.s
      show Finset.card (Finset.filter (fun i => msToBinary ((TernaryNecklace.identifyPair w' .L .s) i) = .s) Finset.univ) = a + b
      have : Finset.filter (fun i => msToBinary ((TernaryNecklace.identifyPair w' .L .s) i) = .s)
          Finset.univ =
          Finset.filter (fun i => w' i = .L) Finset.univ ∪
          Finset.filter (fun i => w' i = .s) Finset.univ := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
          TernaryNecklace.identifyPair, msToBinary]
        constructor
        · intro h; cases hw : w' i <;> simp_all
        · rintro (h | h) <;> simp_all
      rw [this, Finset.card_union_of_disjoint]
      · unfold Necklace.count at hcountL hcounts; omega
      · rw [Finset.disjoint_filter]; intro i _ h1 h2; rw [h1] at h2; exact absurd h2 (by decide)
  exact ⟨hmos_Lm, hmos_ms, hmos_Ls⟩

/-! ## Pairwise-MOS and Balance -/

/-- Adjacent k-step subwords of a ternary necklace have a-counts differing by at most 1. -/
private lemma kStepVector_scoot_count_diff (w : TernaryNecklace n) (i k : ℕ) (a : StepSize)
    (hk : 0 < k) :
    |Necklace.kStepVector w (i + 1) k a - Necklace.kStepVector w i k a| ≤ 1 := by
  -- kStepVector w i k a = kStepVector w i 1 a + kStepVector w (i+1) (k-1) a
  have h1 : Necklace.kStepVector w i k a =
      Necklace.kStepVector w i 1 a + Necklace.kStepVector w (i + 1) (k - 1) a := by
    have := kStepVector_add w i 1 (k - 1) a
    rwa [show 1 + (k - 1) = k from by omega] at this
  -- kStepVector w (i+1) k a = kStepVector w (i+1) (k-1) a + kStepVector w (i+k) 1 a
  have h2 : Necklace.kStepVector w (i + 1) k a =
      Necklace.kStepVector w (i + 1) (k - 1) a + Necklace.kStepVector w (i + k) 1 a := by
    have := kStepVector_add w (i + 1) (k - 1) 1 a
    rwa [show k - 1 + 1 = k from by omega, show i + 1 + (k - 1) = i + k from by omega] at this
  -- So the difference = kStepVector w (i+k) 1 a - kStepVector w i 1 a
  have hdiff : Necklace.kStepVector w (i + 1) k a - Necklace.kStepVector w i k a =
      Necklace.kStepVector w (i + k) 1 a - Necklace.kStepVector w i 1 a := by linarith
  rw [hdiff]
  -- Each singleton kStepVector is 0 or 1
  have hsin1 := kStepVector_singleton w i a
  have hsin2 := kStepVector_singleton w (i + k) a
  rw [hsin1, hsin2]
  split_ifs <;> simp (config := { decide := true }) []

/-- Walking t steps, each step changes a-count by at most 1. -/
private lemma kStepVector_walk_count_bounded (w : TernaryNecklace n) (k i : ℕ)
    (a : StepSize) (hk : 0 < k) (t : ℕ) :
    |Necklace.kStepVector w (i + (t + 1)) k a - Necklace.kStepVector w (i + t) k a| ≤ 1 := by
  have : i + (t + 1) = (i + t) + 1 := by ring
  rw [this]
  exact kStepVector_scoot_count_diff w (i + t) k a hk

/-- If identifying x with y gives a MOS and a is distinct from both x and y,
    then the a-count in k-step subwords of w differs by at most 1.

    **Proof outline**: The count of `a` in a k-step subword of w equals its count
    in the corresponding subword of `identifyPair w x y` (since `a ≠ x`).
    The identified necklace uses only 2 values and has ≤ 2 k-step multisets,
    so the a-count (which determines the multiset) takes at most 2 values.
    By the discrete IVT (sliding window changes count by ≤ 1), these values
    are consecutive, giving count difference ≤ 1. -/
lemma identification_preserves_letter_balance (w : TernaryNecklace n)
    (x y : StepSize) (hxy : x ≠ y) (a : StepSize) (hax : a ≠ x) (hay : a ≠ y)
    (hmos : isPartialPairwiseMOS w x y)
    (k : ℕ) (hk : 0 < k) (hk' : k < n)
    (w1 w2 : List StepSize) (hw1 : w1 ∈ Necklace.allKStepSubwords w k)
    (hw2 : w2 ∈ Necklace.allKStepSubwords w k) :
    Int.natAbs ((w1.count a : ℤ) - (w2.count a : ℤ)) ≤ 1 := by
  -- Extract positions
  rw [Necklace.allKStepSubwords, List.mem_ofFn] at hw1 hw2
  obtain ⟨i, rfl⟩ := hw1
  obtain ⟨j, rfl⟩ := hw2
  -- Set up identified necklace
  set w' := TernaryNecklace.identifyPair w x y with hw'_def
  -- Key: kStepVector w' m k a = kStepVector w m k a (since a ≠ x, a ≠ y)
  have hcount_inv : ∀ m : ℕ, Necklace.kStepVector w' m k a = Necklace.kStepVector w m k a := by
    intro m
    rw [hw'_def, identifyPair_kStepVector w x y hxy m k]
    simp [ZVector.identifyPair, hax, hay]
  -- The MOS property of w' gives ≤ 2 distinct k-step multisets
  have hmult_le_2 := hmos.2 k hk hk'
  -- Via distinctKStepVectors_card_eq, ≤ 2 distinct k-step vectors
  have hvec_le_2 : (distinctKStepVectors w' k).card ≤ 2 := by
    rw [distinctKStepVectors_card_eq]; exact hmult_le_2
  -- If the a-counts differ by > 1, we get a third k-step vector via discrete IVT
  by_contra h_gt
  push_neg at h_gt
  -- The a-count = kStepVector _ _ k a (modulo ℕ/ℤ cast)
  -- slice w m (m+k) has count a = kStepVector w m k a as ℕ → ℤ
  have hcount_eq : ∀ m : ℕ, ((Necklace.slice w m (m + k)).count a : ℤ) =
      Necklace.kStepVector w m k a := by
    intro m
    unfold Necklace.kStepVector ZVector.ofList
    simp only [List.count_eq_countP, List.countP_eq_length_filter]
  rw [hcount_eq, hcount_eq] at h_gt
  -- So |kStepVector w i k a - kStepVector w j k a| > 1
  have hdiff : Necklace.kStepVector w i.val k a - Necklace.kStepVector w j.val k a > 1 ∨
      Necklace.kStepVector w j.val k a - Necklace.kStepVector w i.val k a > 1 := by
    omega
  -- Use discrete IVT to find intermediate position
  set f := fun t => Necklace.kStepVector w (i.val + t) k a with hf_def
  -- Find t such that i + t wraps to j
  set t := if j.val ≥ i.val then j.val - i.val else j.val + n - i.val with ht_def
  have ht_pos : t > 0 := by
    simp only [ht_def]
    split_ifs with h
    · by_contra ht0; push_neg at ht0
      have : j.val = i.val := by omega
      rw [this] at hdiff; omega
    · omega
  have ht_lt_n : t < n := by
    simp only [ht_def]; split_ifs with h <;> omega
  have hf_t_eq : f t = Necklace.kStepVector w j.val k a := by
    simp only [hf_def, ht_def]
    split_ifs with h
    · congr 1; omega
    · rw [show i.val + (j.val + n - i.val) = j.val + n from by omega]
      exact congr_fun (kStepVector_add_n w j.val k) a
  have hf_0_eq : f 0 = Necklace.kStepVector w i.val k a := by simp [hf_def]
  have hstep : ∀ s < t, |f (s + 1) - f s| ≤ 1 := by
    intro s _
    exact kStepVector_walk_count_bounded w k i.val a hk s
  have hdiff' : f 0 - f t > 1 ∨ f t - f 0 > 1 := by
    rw [hf_0_eq, hf_t_eq]; exact hdiff
  obtain ⟨s, hs_lt, hs_intermed⟩ := discrete_ivt f t ht_pos hstep hdiff'
  -- Position (i + s) % n gives a third k-step vector of w'
  set m := (i.val + s) % n with hm_def
  have hm_lt : m < n := Nat.mod_lt _ (NeZero.pos n)
  -- kStepVector w' at m has a-count strictly between those at i and j
  have hm_a : Necklace.kStepVector w' m k a = f s := by
    simp only [hf_def, hm_def]
    rw [hcount_inv, ← kStepVector_mod_n w (i.val + s) k]
  -- The k-step vector at m is in distinctKStepVectors w'
  have hm_mem : Necklace.kStepVector w' m k ∈ distinctKStepVectors w' k := by
    unfold distinctKStepVectors Necklace.allKStepVectors
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨m, List.mem_range.mpr hm_lt, rfl⟩
  have hi_mem : Necklace.kStepVector w' i.val k ∈ distinctKStepVectors w' k := by
    unfold distinctKStepVectors Necklace.allKStepVectors
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩
  have hj_mem : Necklace.kStepVector w' j.val k ∈ distinctKStepVectors w' k := by
    unfold distinctKStepVectors Necklace.allKStepVectors
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨j.val, List.mem_range.mpr j.isLt, rfl⟩
  -- Three distinct vectors: at i, j, and m
  have hvm_ne_vi : Necklace.kStepVector w' m k ≠ Necklace.kStepVector w' i.val k := by
    intro heq
    have ha_eq := congr_fun heq a
    rw [hm_a, hcount_inv] at ha_eq
    -- ha_eq : f s = kStepVector w i.val k a, i.e. f s = f 0
    have hfs_eq_f0 : f s = f 0 := by rw [ha_eq, hf_0_eq]
    rw [hfs_eq_f0] at hs_intermed
    simp only [min_lt_iff, lt_max_iff] at hs_intermed; omega
  have hvm_ne_vj : Necklace.kStepVector w' m k ≠ Necklace.kStepVector w' j.val k := by
    intro heq
    have ha_eq := congr_fun heq a
    rw [hm_a, hcount_inv] at ha_eq
    -- ha_eq : f s = kStepVector w j.val k a, i.e. f s = f t
    have hfs_eq_ft : f s = f t := by rw [ha_eq, hf_t_eq]
    rw [hfs_eq_ft] at hs_intermed
    simp only [min_lt_iff, lt_max_iff] at hs_intermed; omega
  have hvi_ne_vj : Necklace.kStepVector w' i.val k ≠ Necklace.kStepVector w' j.val k := by
    intro heq
    have ha_eq := congr_fun heq a
    rw [hcount_inv, hcount_inv] at ha_eq
    rw [hf_0_eq, hf_t_eq] at hdiff'; omega
  -- Three distinct vectors → card ≥ 3
  have hcard_ge_3 : (distinctKStepVectors w' k).card ≥ 3 := by
    have h3 : ({Necklace.kStepVector w' i.val k, Necklace.kStepVector w' j.val k,
        Necklace.kStepVector w' m k} : Finset (ZVector StepSize)).card = 3 := by
      rw [Finset.card_insert_eq_ite, Finset.card_insert_eq_ite, Finset.card_singleton]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      simp only [hvi_ne_vj, hvm_ne_vi.symm, hvm_ne_vj.symm, false_or, ite_false]
    calc (distinctKStepVectors w' k).card
        ≥ ({Necklace.kStepVector w' i.val k, Necklace.kStepVector w' j.val k,
            Necklace.kStepVector w' m k} : Finset (ZVector StepSize)).card :=
          Finset.card_le_card (by
            intro v hv
            simp only [Finset.mem_insert, Finset.mem_singleton] at hv
            rcases hv with rfl | rfl | rfl
            · exact hi_mem
            · exact hj_mem
            · exact hm_mem)
      _ = 3 := h3
  omega

end TernaryNecklace
