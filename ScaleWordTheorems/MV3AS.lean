import ScaleWordTheorems.MV3Defs

open BigOperators

namespace TernaryNecklace

variable {n : ℕ} [NeZero n]

/-! ## AS and Odd-Regular Scales -/

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

/-- The total count of all three step sizes equals the necklace length. -/
lemma count_total (w : TernaryNecklace n) :
    Necklace.count w StepSize.L + Necklace.count w StepSize.m +
      Necklace.count w StepSize.s = n := by
  unfold Necklace.count
  have hunion : Finset.filter (fun i => w i = StepSize.L) Finset.univ ∪
      Finset.filter (fun i => w i = StepSize.m) Finset.univ ∪
      Finset.filter (fun i => w i = StepSize.s) Finset.univ =
      (Finset.univ : Finset (ZMod n)) := by
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun _ => trivial, fun _ => by cases w i <;> simp⟩
  have hd1 : Disjoint
      (Finset.filter (fun i => w i = StepSize.L) Finset.univ)
      (Finset.filter (fun i => w i = StepSize.m) Finset.univ) :=
    Finset.disjoint_filter.mpr fun _ _ h => by rw [h]; decide
  have hd2 : Disjoint
      (Finset.filter (fun i => w i = StepSize.L) Finset.univ ∪
       Finset.filter (fun i => w i = StepSize.m) Finset.univ)
      (Finset.filter (fun i => w i = StepSize.s) Finset.univ) :=
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_filter.mpr fun _ _ h => by rw [h]; decide,
       Finset.disjoint_filter.mpr fun _ _ h => by rw [h]; decide⟩
  rw [← Finset.card_union_of_disjoint hd1,
      ← Finset.card_union_of_disjoint hd2,
      hunion, Finset.card_univ, ZMod.card]

/-- In a ternary necklace, every step size occurs at least once,
    so every letter count is positive. -/
lemma count_pos_of_isTernary (w : TernaryNecklace n)
    (htern : isTernary w) (a : StepSize) :
    0 < Necklace.count w a := by
  unfold Necklace.count
  rw [Finset.card_pos]
  obtain ⟨i, hi⟩ := (isTernary_iff_forall w).mp htern a
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩

/-- A ternary necklace has length ≥ 3: three distinct letters each occur at
    least once, and their positions are pairwise distinct. -/
lemma ternary_length_ge_three (w : TernaryNecklace n)
    (htern : isTernary w) : n ≥ 3 := by
  have h := count_total w
  have hL := count_pos_of_isTernary w htern StepSize.L
  have hm := count_pos_of_isTernary w htern StepSize.m
  have hs := count_pos_of_isTernary w htern StepSize.s
  omega

omit [NeZero n] in
/-- Modular inverse: if `gcd(k, n) = 1` and `n ≥ 2`,
    there exists `l₀ ∈ [1, n−1]` with `l₀ · k ≡ 1 (mod n)`. -/
lemma exists_modular_inverse (k : ℕ)
    (hcop : Nat.Coprime k n) (hn : n ≥ 2) :
    ∃ l₀, 0 < l₀ ∧ l₀ < n ∧ l₀ * k % n = 1 := by
  -- Use Bezout's identity: gcd(k, n) = k * gcdA + n * gcdB = 1
  have bezout := Int.gcd_eq_gcd_ab (↑k : ℤ) (↑n : ℤ)
  rw [show Int.gcd (↑k : ℤ) (↑n : ℤ) = Nat.gcd k n from rfl] at bezout
  rw [hcop] at bezout
  -- Take l₀ = gcdA % n (reduced to ℕ)
  set a := Int.gcdA (↑k : ℤ) (↑n : ℤ) with ha_def
  have hn_pos : (0 : ℤ) < ↑n := by positivity
  set l₀ := (a % (↑n : ℤ)).toNat with hl₀_def
  have ha_nn : 0 ≤ a % (↑n : ℤ) := Int.emod_nonneg _ (ne_of_gt hn_pos)
  have hl₀_cast : (↑l₀ : ℤ) = a % ↑n := Int.toNat_of_nonneg ha_nn
  have hl₀_lt : l₀ < n := by
    have := Int.emod_lt_of_pos a hn_pos
    omega
  have hl₀_inv : l₀ * k % n = 1 := by
    -- Work in ℤ: show ↑l₀ * ↑k ≡ 1 (mod ↑n)
    have h_int : (↑l₀ * ↑k) % (↑n : ℤ) = 1 := by
      calc (↑l₀ * ↑k) % (↑n : ℤ)
          = (a % ↑n * ↑k) % ↑n := by rw [hl₀_cast]
        _ = (a * ↑k) % ↑n := by rw [Int.mul_emod, Int.emod_emod_of_dvd a dvd_rfl, ← Int.mul_emod]
        _ = (↑k * a) % ↑n := by ring_nf
        _ = (↑k * a + ↑n * Int.gcdB (↑k : ℤ) (↑n : ℤ)) % ↑n := by
            rw [Int.add_mul_emod_self_left]
        _ = 1 % ↑n := by rw [← bezout]; ring_nf
        _ = 1 := Int.emod_eq_of_lt (by omega) (by omega)
    -- Transfer from ℤ to ℕ
    have h_cast : (↑(l₀ * k % n) : ℤ) = 1 := by
      rw [Int.natCast_mod]
      exact_mod_cast h_int
    exact_mod_cast h_cast
  have hl₀_pos : 0 < l₀ := by
    by_contra h; push_neg at h
    interval_cases l₀
    simp at hl₀_inv
  exact ⟨l₀, hl₀_pos, hl₀_lt, hl₀_inv⟩

omit [NeZero n] in
/-- For `n` odd (≥ 3) and `gcd(k, n) = 1`, there exists an odd `l ∈ [1, n−2]`
    with `l·k ≡ 1` or `l·k ≡ −1 (mod n)`.

    **Proof.** Let `l₀` be the modular inverse of `k` in `[1, n−1]`.
    If `l₀` is odd, take `l = l₀` (with `l·k ≡ 1`).
    If `l₀` is even, take `l = n − l₀` which is odd (since `n` is odd),
    lies in `[1, n−1]`, and satisfies `l·k ≡ −1 (mod n)`.
    In both cases `l ≤ n − 2` since `l` is odd and `l < n`. -/
private lemma exists_odd_quasi_inverse (k : ℕ)
    (hodd : n % 2 = 1) (hcop : Nat.Coprime k n) (hn : n ≥ 3) :
    ∃ l, 0 < l ∧ l ≤ n - 2 ∧ l % 2 = 1 ∧
      (l * k % n = 1 ∨ l * k % n = n - 1) := by
  obtain ⟨l₀, hl₀_pos, hl₀_lt, hl₀_inv⟩ := exists_modular_inverse k hcop (by omega)
  by_cases hl₀_odd : l₀ % 2 = 1
  · -- l₀ is odd: l₀ ≤ n − 2 since l₀ < n and n − 1 is even
    exact ⟨l₀, hl₀_pos, by omega, hl₀_odd, Or.inl hl₀_inv⟩
  · -- l₀ is even: take l = n − l₀ (odd since n odd, l₀ even)
    refine ⟨n - l₀, by omega, by omega, by omega, Or.inr ?_⟩
    -- Show (n − l₀) * k % n = n − 1.
    -- Key identity: (n − l₀) * k + l₀ * k = n * k
    have h_sum : (n - l₀) * k + l₀ * k = n * k := by
      rw [← add_mul, Nat.sub_add_cancel (by omega : l₀ ≤ n)]
    -- Taking both sides mod n: ((n−l₀)*k % n + l₀*k % n) % n = 0
    have h_mod0 : ((n - l₀) * k % n + l₀ * k % n) % n = 0 := by
      rw [← Nat.add_mod, h_sum, Nat.mul_mod_right]
    -- Substituting l₀ * k % n = 1:
    rw [hl₀_inv] at h_mod0
    -- h_mod0 : ((n − l₀) * k % n + 1) % n = 0
    -- The value (n−l₀)*k % n + 1 is ≤ n (mod bound) and ≥ n (divisibility),
    -- so it equals n, giving (n−l₀)*k % n = n − 1.
    suffices h : (n - l₀) * k % n + 1 = n by omega
    exact le_antisymm
      (Nat.mod_lt _ (by omega))
      (Nat.le_of_dvd (Nat.succ_pos _) (Nat.dvd_of_mod_eq_zero h_mod0))

/-- Splitting a k-step vector: the `(m₁+m₂)`-step vector from `i` equals
    the `m₁`-step vector from `i` plus the `m₂`-step vector from `i + m₁`. -/
lemma kStepVector_add {α : Type*} [DecidableEq α] (w : Necklace α n)
    (i m₁ m₂ : ℕ) (a : α) :
    Necklace.kStepVector w i (m₁ + m₂) a =
    Necklace.kStepVector w i m₁ a + Necklace.kStepVector w (i + m₁) m₂ a := by
  unfold Necklace.kStepVector
  conv_lhs => rw [show i + (m₁ + m₂) = i + m₁ + m₂ from by omega]
  suffices hsplit : Necklace.slice w i (i + m₁ + m₂) =
      Necklace.slice w i (i + m₁) ++ Necklace.slice w (i + m₁) (i + m₁ + m₂) by
    rw [hsplit]; unfold ZVector.ofList
    rw [List.filter_append, List.length_append, Nat.cast_add]
  induction m₂ with
  | zero =>
    suffices Necklace.slice w (i + m₁) (i + m₁) = [] by
      rw [Nat.add_zero, this, List.append_nil]
    unfold Necklace.slice; simp
  | succ m₂ ih =>
    have hLHS : Necklace.slice w i (i + m₁ + (m₂ + 1)) =
        Necklace.slice w i (i + m₁ + m₂) ++ [w ((i + m₁ + m₂ : ℕ) : ZMod n)] := by
      have := slice_extend_end w i (m₁ + m₂)
      rw [show i + (m₁ + m₂) + 1 = i + m₁ + (m₂ + 1) from by omega,
          show i + (m₁ + m₂) = i + m₁ + m₂ from by omega] at this
      simp only [← Nat.cast_add, ← Nat.add_assoc] at this
      exact this
    have hRHS : Necklace.slice w (i + m₁) (i + m₁ + (m₂ + 1)) =
        Necklace.slice w (i + m₁) (i + m₁ + m₂) ++ [w ((i + m₁ + m₂ : ℕ) : ZMod n)] := by
      have := slice_extend_end w (i + m₁) m₂
      rw [show i + m₁ + m₂ + 1 = i + m₁ + (m₂ + 1) from by omega] at this
      simp only [← Nat.cast_add, ← Nat.add_assoc] at this
      exact this
    rw [hLHS, ih, hRHS, List.append_assoc]

/-- A single step gives the indicator for the letter at that position. -/
lemma kStepVector_singleton (w : TernaryNecklace n)
    (i : ℕ) (a : StepSize) :
    Necklace.kStepVector w i 1 a =
    if w ((i : ℕ) : ZMod n) = a then 1 else 0 := by
  simp only [Necklace.kStepVector, Necklace.slice, ZVector.ofList,
             show i + 1 - i = 1 from by omega, List.range_succ, List.range_zero,
             List.nil_append]
  by_cases h : w ((i : ℕ) : ZMod n) = a
  · simp [h]
  · simp [beq_eq_false_iff_ne.mpr h, h]

/-- Ternary kStepVector total count: L + m + s = k. -/
lemma kStepVector_total_count_ternary (w : TernaryNecklace n)
    (i k : ℕ) :
    (Necklace.kStepVector w i k) .L + (Necklace.kStepVector w i k) .m +
    (Necklace.kStepVector w i k) .s = ↑k := by
  induction k generalizing i with
  | zero => simp [Necklace.kStepVector, ZVector.ofList, Necklace.slice]
  | succ k ih =>
    have hadd : ∀ a : StepSize, Necklace.kStepVector w i (k + 1) a =
        Necklace.kStepVector w i k a + Necklace.kStepVector w (i + k) 1 a :=
      fun a => kStepVector_add w i k 1 a
    simp only [hadd]
    have h_single : (Necklace.kStepVector w (i + k) 1) .L +
        (Necklace.kStepVector w (i + k) 1) .m +
        (Necklace.kStepVector w (i + k) 1) .s = 1 := by
      simp only [kStepVector_singleton]
      have : ∀ (v : StepSize),
          (if v = .L then (1 : ℤ) else 0) + (if v = .m then 1 else 0) +
          (if v = .s then 1 else 0) = 1 := by
        intro v; cases v <;> simp
      exact this _
    push_cast; linarith [ih i]

/-- Shifting the start of a full-cycle kStepVector by 1 doesn't change the result. -/
private lemma kStepVector_shift_one_n (w : TernaryNecklace n)
    (i : ℕ) (a : StepSize) :
    Necklace.kStepVector w (i + 1) n a = Necklace.kStepVector w i n a := by
  unfold Necklace.kStepVector
  have hn_pos := NeZero.pos n
  -- Decompose LHS: slice w (i+1) (i+1+n) = slice w (i+1) (i+n) ++ [w ↑i]
  have h_lhs : Necklace.slice w (i + 1) (i + 1 + n) =
      Necklace.slice w (i + 1) (i + n) ++ [w ((i : ℕ) : ZMod n)] := by
    have h := slice_extend_end w (i + 1) (n - 1)
    rw [show i + 1 + (n - 1) + 1 = i + 1 + n from by omega] at h
    -- h : slice w (i+1) (i+1+n) = slice w (i+1) (i+1+(n-1)) ++ [w ↑(i+1+(n-1))]
    rw [h]; congr 1
    · congr 1; omega  -- slice index: i+1+(n-1) = i+n
    · congr 1; congr 1  -- w term: need ↑(i+1) + ↑(n-1) = ↑i in ZMod n
      rw [← Nat.cast_add, show i + 1 + (n - 1) = i + n from by omega,
          Nat.cast_add, CharP.cast_eq_zero (ZMod n) n, add_zero]
  -- Decompose RHS: slice w i (i+n) = [w ↑i] ++ slice w (i+1) (i+n)
  have h_rhs := slice_shift_decompose w i n hn_pos
  rw [h_lhs, h_rhs]
  -- Goal: ofList (slice ++ [w ↑i]) a = ofList (w ↑i :: slice) a
  unfold ZVector.ofList
  rw [List.filter_append, List.length_append, Nat.cast_add,
      show w ((i : ℕ) : ZMod n) :: Necklace.slice w (i + 1) (i + n) =
           [w ((i : ℕ) : ZMod n)] ++ Necklace.slice w (i + 1) (i + n) from rfl,
      List.filter_append, List.length_append, Nat.cast_add]
  omega

/-- A full cycle from position 0 counts each letter. -/
private lemma kStepVector_zero_n (w : TernaryNecklace n) (a : StepSize) :
    Necklace.kStepVector w 0 n a = ↑(Necklace.count w a) := by
  -- Step 1: Convert kStepVector to Finset.range sum using kStepVector_add + kStepVector_singleton
  have h_as_sum : ∀ m : ℕ, Necklace.kStepVector w 0 m a =
      ∑ i ∈ Finset.range m, if w ((i : ℕ) : ZMod n) = a then (1 : ℤ) else 0 := by
    intro m; induction m with
    | zero =>
      simp only [Finset.sum_range_zero]
      unfold Necklace.kStepVector Necklace.slice ZVector.ofList
      simp
    | succ m ih =>
      rw [kStepVector_add w 0 m 1 a, ih, Nat.zero_add, kStepVector_singleton,
          Finset.sum_range_succ]
  -- Step 2: Convert Finset.range sum to Finset.card via sum_boole
  rw [h_as_sum]
  simp_rw [show ∀ i : ℕ, (if w ((i : ℕ) : ZMod n) = a then (1 : ℤ) else 0) =
      ↑(if w ((i : ℕ) : ZMod n) = a then 1 else 0 : ℕ) from
      fun i => by split_ifs <;> simp]
  rw [← Nat.cast_sum, Finset.sum_boole]
  congr 1
  -- Step 3: Bijection between Finset.range n and Finset.univ via k ↦ ↑k
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

/-- A full cycle from any starting position counts each letter. -/
lemma kStepVector_full_cycle (w : TernaryNecklace n)
    (i : ℕ) (a : StepSize) :
    Necklace.kStepVector w i n a = ↑(Necklace.count w a) := by
  suffices hi : Necklace.kStepVector w i n a = Necklace.kStepVector w 0 n a by
    rw [hi, kStepVector_zero_n]
  induction i with
  | zero => rfl
  | succ i ih => rw [kStepVector_shift_one_n, ih]

/-- A full cycle (`q * n` steps) gives `q` times the letter count. -/
private lemma kStepVector_mul_n (w : TernaryNecklace n)
    (i q : ℕ) (a : StepSize) :
    Necklace.kStepVector w i (q * n) a = ↑q * ↑(Necklace.count w a) := by
  induction q with
  | zero =>
    simp only [Nat.cast_zero, zero_mul]
    simp [Necklace.kStepVector, Necklace.slice, ZVector.ofList]
  | succ q ih =>
    rw [show (q + 1) * n = q * n + n from by ring, kStepVector_add, ih,
        kStepVector_full_cycle]
    push_cast; ring

/-- Round-trip: casting `p.val` back to `ZMod n` gives `p`. -/
lemma natCast_zmod_val (p : ZMod n) : (↑(ZMod.val p) : ZMod n) = p := by
  have h : ZMod.val (↑(ZMod.val p) : ZMod n) = ZMod.val p := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (ZMod.val_lt p)]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := NeZero.pos n; omega⟩
  exact Fin.val_injective h

omit [NeZero n] in
/-- In `ZMod n`, `↑(n − 1) = −1`. -/
private lemma natCast_pred_eq_neg_one (hn : n ≥ 2) :
    (↑(n - 1) : ZMod n) = -1 := by
  rw [Nat.cast_sub (by omega : 1 ≤ n), CharP.cast_eq_zero (ZMod n) n,
      Nat.cast_one, zero_sub]

/-- When `m ≡ 1 (mod n)`, the m-step vector at position `p` decomposes as
    `q` complete wraps of the necklace plus an indicator for the letter at `p`,
    where `q = m / n`. -/
private lemma kStepVector_decomp_mod_one (w : TernaryNecklace n)
    (p : ZMod n) (m : ℕ) (hm : m % n = 1) (_hn : n ≥ 2) (a : StepSize) :
    Necklace.kStepVector w p.val m a =
    ↑(m / n) * ↑(Necklace.count w a) + if w p = a then 1 else 0 := by
  have hm_div : m = m / n * n + 1 := by
    have h := Nat.div_add_mod m n; rw [hm, mul_comm] at h; exact h.symm
  conv_lhs => rw [hm_div]
  rw [kStepVector_add, kStepVector_mul_n, kStepVector_singleton]
  congr 2
  -- Goal: ((p.val + m / n * n : ℕ) : ZMod n) = p
  rw [Nat.cast_add, Nat.cast_mul, CharP.cast_eq_zero (ZMod n) n,
      mul_zero, add_zero, natCast_zmod_val]

/-- When `m ≡ n−1 (mod n)`, the m-step vector at position `p` decomposes as
    `(q+1)` complete wraps minus an indicator for the letter at `p − 1`,
    where `q = m / n`. -/
private lemma kStepVector_decomp_mod_nm1 (w : TernaryNecklace n)
    (p : ZMod n) (m : ℕ) (hm : m % n = n - 1) (hn : n ≥ 2) (a : StepSize) :
    Necklace.kStepVector w p.val m a =
    ↑(m / n + 1) * ↑(Necklace.count w a) - if w (p - 1) = a then 1 else 0 := by
  -- Key: m + 1 = (m/n + 1) * n, so kStepVector at (m+1) = (m/n+1) * count
  have hm1 : m + 1 = (m / n + 1) * n := by
    have h := Nat.div_add_mod m n; rw [hm, mul_comm] at h
    rw [show (m / n + 1) * n = m / n * n + n from by ring]; omega
  -- Split m + 1 = m + 1
  have hsplit := kStepVector_add w p.val m 1 a
  -- kStepVector at (m+1) = (m/n+1) * count
  have hcycle : Necklace.kStepVector w p.val (m + 1) a =
      ↑(m / n + 1) * ↑(Necklace.count w a) := by
    rw [hm1, kStepVector_mul_n]
  -- Singleton gives indicator at position p.val + m
  rw [kStepVector_singleton] at hsplit
  -- Simplify position: ((p.val + m : ℕ) : ZMod n) = p - 1
  have hpos : w ((p.val + m : ℕ) : ZMod n) = w (p - 1) := by
    congr 1
    rw [Nat.cast_add, natCast_zmod_val]
    -- (↑m : ZMod n) = -1
    have : (↑m : ZMod n) = -1 := by
      have hm_div : m = n * (m / n) + (n - 1) := by
        have h := Nat.div_add_mod m n; rw [hm] at h; exact h.symm
      conv_lhs => rw [hm_div]
      rw [Nat.cast_add, Nat.cast_mul, CharP.cast_eq_zero (ZMod n) n,
          zero_mul, zero_add, natCast_pred_eq_neg_one hn]
    rw [this]; ring
  rw [hpos] at hsplit
  -- hsplit : kStepVector w p.val (m+1) a = kStepVector w p.val m a + (if ...)
  -- hcycle : kStepVector w p.val (m+1) a = (m/n+1) * count
  -- So kStepVector w p.val m a = (m/n+1) * count - (if ...)
  omega

/-- When `m ≡ 1 (mod n)`, the m-step vector at position `i` is
    `q · totalVector + indicator(w(i))` where `q = m / n`.
    So equal m-step vectors ↔ equal letters. -/
private lemma kStepVector_eq_iff_letter_eq (w : TernaryNecklace n)
    (i j : ZMod n) (m : ℕ) (hm : m % n = 1) (hn : n ≥ 2) :
    w i = w j ↔
    Necklace.kStepVector w i.val m = Necklace.kStepVector w j.val m := by
  constructor
  · intro heq
    funext a
    rw [kStepVector_decomp_mod_one w i m hm hn a,
        kStepVector_decomp_mod_one w j m hm hn a, heq]
  · intro heq
    by_contra hne
    have hne' : w j ≠ w i := fun h => hne h.symm
    have hi := congr_fun heq (w i)
    rw [kStepVector_decomp_mod_one w i m hm hn (w i),
        kStepVector_decomp_mod_one w j m hm hn (w i),
        if_pos rfl, if_neg hne'] at hi
    omega

/-- When `m ≡ n−1 (mod n)`, the m-step vector at position `i+1` is
    `(q+1) · totalVector − indicator(w(i))` where `q = m / n`.
    So equal m-step vectors at `i+1, j+1` ↔ equal letters at `i, j`. -/
private lemma kStepVector_eq_iff_letter_eq_shift (w : TernaryNecklace n)
    (i j : ZMod n) (m : ℕ) (hm : m % n = n - 1) (hn : n ≥ 2) :
    w i = w j ↔
    Necklace.kStepVector w (i + 1).val m = Necklace.kStepVector w (j + 1).val m := by
  constructor
  · intro heq
    funext a
    have h1 := kStepVector_decomp_mod_nm1 w (i + 1) m hm hn a
    have h2 := kStepVector_decomp_mod_nm1 w (j + 1) m hm hn a
    rw [show (i + 1 : ZMod n) - 1 = i by ring] at h1
    rw [show (j + 1 : ZMod n) - 1 = j by ring] at h2
    rw [h1, h2, heq]
  · intro heq
    by_contra hne
    have hne' : w j ≠ w i := fun h => hne h.symm
    have hi := congr_fun heq (w i)
    have h1 := kStepVector_decomp_mod_nm1 w (i + 1) m hm hn (w i)
    have h2 := kStepVector_decomp_mod_nm1 w (j + 1) m hm hn (w i)
    rw [show (i + 1 : ZMod n) - 1 = i by ring] at h1
    rw [show (j + 1 : ZMod n) - 1 = j by ring] at h2
    rw [h1, h2, if_pos rfl, if_neg hne'] at hi
    omega

/-- When `l·k ≡ ±1 (mod n)`, positions with the same letter have the same
    `(l·k)`-step vector (up to a uniform position shift), and vice versa.
    That is, there is a bijection `f` on `ZMod n` such that
    `w i = w j ↔ kStepVector(f i) = kStepVector(f j)`. -/
private lemma lk_step_determines_letter (w : TernaryNecklace n)
    (l k : ℕ) (hl_mod : l * k % n = 1 ∨ l * k % n = n - 1) (hn : n ≥ 3) :
    ∃ (f : ZMod n ≃ ZMod n), ∀ i j : ZMod n,
      w i = w j ↔
      Necklace.kStepVector w (f i).val (l * k) =
        Necklace.kStepVector w (f j).val (l * k) := by
  rcases hl_mod with hmod1 | hmodn1
  · -- Case l*k ≡ 1 (mod n): f = id
    refine ⟨Equiv.refl _, fun i j => ?_⟩
    simp only [Equiv.refl_apply]
    exact kStepVector_eq_iff_letter_eq w i j (l * k) hmod1 (by omega)
  · -- Case l*k ≡ n-1 (mod n): f = (· + 1)
    refine ⟨⟨(· + 1), (· - 1), fun i => by ring, fun i => by ring⟩, fun i j => ?_⟩
    dsimp
    exact kStepVector_eq_iff_letter_eq_shift w i j (l * k) hmodn1 (by omega)

/-- Window shift recurrence: shifting the start by `k` removes one k-step vector
    and adds another. -/
private lemma kStepVector_window_shift (w : TernaryNecklace n)
    (i k l : ℕ) (_ : 0 < l) (a : StepSize) :
    Necklace.kStepVector w (i + k) (l * k) a =
      Necklace.kStepVector w i (l * k) a -
      Necklace.kStepVector w i k a +
      Necklace.kStepVector w (i + l * k) k a := by
  have h1 := kStepVector_add w i k (l * k) a
  have h2 := kStepVector_add w i (l * k) k a
  rw [show k + l * k = l * k + k from by ring] at h1
  linarith

/-- Window shift recurrence at function level (ZVector equality). -/
lemma kStepVector_window_shift_fun (w : TernaryNecklace n)
    (i k l : ℕ) (hl : 0 < l) :
    Necklace.kStepVector w (i + k) (l * k) =
      Necklace.kStepVector w i (l * k) -
      Necklace.kStepVector w i k +
      Necklace.kStepVector w (i + l * k) k := by
  funext a
  simp only [ZVector.sub_apply, ZVector.add_apply]
  exact kStepVector_window_shift w i k l hl a

/-- Classification of `(l·k)`-step vectors at abstract positions.

    For `j < n − l` (non-crossing), `S(j)` alternates between `S(0)` and `S(1)`
    depending on parity.  For `j ≥ n − l` (crossing), `S(j) = S(n − l)`. -/
private lemma alternating_lk_class (w : TernaryNecklace n)
    (k r : ℕ) (seq : Fin 2 → ZVector StepSize) (l : ℕ)
    (hodd : n % 2 = 1) (hl_pos : 0 < l) (hl_le : l ≤ n - 2) (hl_odd : l % 2 = 1)
    (hseq : ∀ i : Fin (n - 1),
      Necklace.kStepVector w (r + i.val * k) k =
        seq ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩)
    (_ : ∀ j : Fin 2,
      Necklace.kStepVector w (r + (n - 1) * k) k ≠ seq j)
    (j : ℕ) (hj : j < n) :
    Necklace.kStepVector w (r + j * k) (l * k) =
      if j < n - l then
        if j % 2 = 0 then Necklace.kStepVector w r (l * k)
        else Necklace.kStepVector w (r + k) (l * k)
      else
        Necklace.kStepVector w (r + (n - l) * k) (l * k) := by
  induction j with
  | zero => simp [show 0 < n - l from by omega]
  | succ j IH =>
    have hj_lt : j < n := by omega
    have IH := IH hj_lt
    -- Recurrence: S(j+1) = S(j) - T(j) + T(j+l)
    have hrec : Necklace.kStepVector w (r + (j + 1) * k) (l * k) =
        Necklace.kStepVector w (r + j * k) (l * k) -
        Necklace.kStepVector w (r + j * k) k +
        Necklace.kStepVector w (r + (j + l) * k) k := by
      have h := kStepVector_window_shift_fun w (r + j * k) k l hl_pos
      rw [show r + j * k + k = r + (j + 1) * k from by ring,
          show r + j * k + l * k = r + (j + l) * k from by ring] at h
      exact h
    -- T(j) = seq(j % 2) since j < n-1
    have hTj : Necklace.kStepVector w (r + j * k) k =
        seq ⟨j % 2, Nat.mod_lt _ (by omega)⟩ := hseq ⟨j, by omega⟩
    -- Key identity: v₂ = v₁ - seq(0) + seq(1)
    have hv₂_eq : Necklace.kStepVector w (r + k) (l * k) =
        Necklace.kStepVector w r (l * k) -
        seq ⟨0, by omega⟩ + seq ⟨1, by omega⟩ := by
      have h := kStepVector_window_shift_fun w r k l hl_pos
      rw [show r + l * k = r + l * k from rfl] at h
      rw [h]; congr 1; congr 1
      · simpa using hseq ⟨0, by omega⟩
      · have := hseq ⟨l, by omega⟩
        rw [this]; congr 1; ext; simp; exact hl_odd
    -- Case split on position type
    by_cases h_nc : j + 1 < n - l
    · -- Non-crossing: j+1 < n-l
      have hj_nc : j < n - l := by omega
      have hjl_lt : j + l < n - 1 := by omega
      by_cases hj_even : j % 2 = 0
      · -- j even → S(j) = v₁, S(j+1) = v₂
        have hSj : Necklace.kStepVector w (r + j * k) (l * k) =
            Necklace.kStepVector w r (l * k) := by
          rw [IH, if_pos hj_nc, if_pos hj_even]
        have hTj_val : Necklace.kStepVector w (r + j * k) k = seq ⟨0, by omega⟩ :=
          hTj.trans (by congr 1; ext; exact hj_even)
        have hTjl_val : Necklace.kStepVector w (r + (j + l) * k) k = seq ⟨1, by omega⟩ :=
          (hseq ⟨j + l, hjl_lt⟩).trans (by congr 1; ext; simp only []; omega)
        rw [hrec, hSj, hTj_val, hTjl_val, if_pos h_nc,
            if_neg (show ¬((j + 1) % 2 = 0) from by omega)]
        exact hv₂_eq.symm
      · -- j odd → S(j) = v₂, S(j+1) = v₁
        have hSj : Necklace.kStepVector w (r + j * k) (l * k) =
            Necklace.kStepVector w (r + k) (l * k) := by
          rw [IH, if_pos hj_nc, if_neg hj_even]
        have hTj_val : Necklace.kStepVector w (r + j * k) k = seq ⟨1, by omega⟩ :=
          hTj.trans (by congr 1; ext; simp only []; omega)
        have hTjl_val : Necklace.kStepVector w (r + (j + l) * k) k = seq ⟨0, by omega⟩ :=
          (hseq ⟨j + l, hjl_lt⟩).trans (by congr 1; ext; simp only []; omega)
        rw [hrec, hSj, hTj_val, hTjl_val, if_pos h_nc,
            if_pos (show (j + 1) % 2 = 0 from by omega)]
        -- v₂ - seq(1) + seq(0) = v₁
        rw [hv₂_eq]
        funext a; simp only [ZVector.sub_apply, ZVector.add_apply]; omega
    · by_cases h_eq : j + 1 = n - l
      · -- Transition: j+1 = n-l, trivially S(n-l) = v₃
        simp [h_eq]
      · -- Crossing: j+1 > n-l. S(j+1) = S(j) since T(j) = T(j+l).
        have h_cross : n - l < j + 1 := by omega
        -- T(j+l) reduced modulo n equals T(j+l-n)
        have hjl_ge : j + l ≥ n := by omega
        have hjl_lt2n : j + l < 2 * n := by omega
        -- Periodicity: kStepVector at (j+l) = kStepVector at (j+l-n) in abstract pos
        have hperiod : Necklace.kStepVector w (r + (j + l) * k) k =
            Necklace.kStepVector w (r + (j + l - n) * k) k := by
          have hmod : (r + (j + l) * k) % n = (r + (j + l - n) * k) % n := by
            have : r + (j + l) * k = r + (j + l - n) * k + n * k := by
              have : (j + l) * k = (j + l - n) * k + n * k := by
                rw [← add_mul, Nat.sub_add_cancel (by omega : n ≤ j + l)]
              omega
            rw [this]; exact Nat.add_mul_mod_self_left (r + (j + l - n) * k) n k
          rw [← kStepVector_mod_n w (r + (j + l) * k) k,
              ← kStepVector_mod_n w (r + (j + l - n) * k) k, hmod]
        -- T(j+l-n) = seq((j+l-n)%2) = seq(j%2) = T(j)
        have hjln_lt : j + l - n < n - 1 := by omega
        have hTjln : Necklace.kStepVector w (r + (j + l - n) * k) k =
            seq ⟨(j + l - n) % 2, Nat.mod_lt _ (by omega)⟩ := hseq ⟨j + l - n, hjln_lt⟩
        -- Key parity: (j+l-n) % 2 = j % 2 (since l+n is even)
        have hpar : (j + l - n) % 2 = j % 2 := by omega
        have hTjl_eq : Necklace.kStepVector w (r + (j + l) * k) k =
            Necklace.kStepVector w (r + j * k) k := by
          rw [hperiod, hTjln, hTj]; congr 1; ext; simp; exact hpar
        -- S(j+1) = S(j) since T(j) = T(j+l) cancels
        have hcancel : Necklace.kStepVector w (r + (j + 1) * k) (l * k) =
            Necklace.kStepVector w (r + j * k) (l * k) := by
          rw [hrec, hTjl_eq]
          funext a; simp only [ZVector.sub_apply, ZVector.add_apply]; omega
        -- By IH, S(j) = v₃ (since j ≥ n-l)
        rw [hcancel, IH]
        simp [show ¬(j < n - l) from by omega, h_nc]

omit [NeZero n] in
/-- A coprime natural number is a unit in `ZMod n`. -/
lemma coprime_isUnit_zmod (k : ℕ) (hcop : Nat.Coprime k n) (hn : n ≥ 2) :
    IsUnit ((k : ℕ) : ZMod n) := by
  obtain ⟨l₀, _, _, hl₀_inv⟩ := exists_modular_inverse k hcop hn
  have h : (↑k : ZMod n) * (↑l₀ : ZMod n) = 1 := by
    rw [← Nat.cast_mul, show k * l₀ = l₀ * k from mul_comm k l₀]
    have hdiv : l₀ * k = n * (l₀ * k / n) + 1 := by
      have := Nat.div_add_mod (l₀ * k) n; rw [hl₀_inv] at this; omega
    rw [hdiv, Nat.cast_add, Nat.cast_mul, CharP.cast_eq_zero (ZMod n) n,
        zero_mul, zero_add, Nat.cast_one]
  exact ⟨⟨(↑k : ZMod n), (↑l₀ : ZMod n), h, by rwa [mul_comm] at h⟩, rfl⟩

/-- The affine map `j ↦ r + j * k` covers all of `ZMod n` when `gcd(k, n) = 1`. -/
private lemma coprime_affine_surj (k r : ℕ) (hcop : Nat.Coprime k n) (hn : n ≥ 2) :
    ∀ p : ZMod n, ∃ j : ZMod n, p = (↑r : ZMod n) + j * (↑k : ZMod n) := by
  have hk_unit := coprime_isUnit_zmod k hcop hn
  have hsurj : Function.Surjective
      (fun j : ZMod n => (↑r : ZMod n) + j * (↑k : ZMod n)) :=
    Finite.surjective_of_injective (fun j₁ j₂ h => by
      have h1 : j₁ * (↑k : ZMod n) = j₂ * (↑k : ZMod n) := add_left_cancel h
      rw [mul_comm j₁, mul_comm j₂] at h1
      exact hk_unit.mul_left_cancel h1)
  intro p; obtain ⟨j, hj⟩ := hsurj p; exact ⟨j, hj.symm⟩

/-- If `seq 0 = seq 1` in an alternating k-step sequence with a distinct closing
    vector, the necklace cannot be ternary.

    **Proof idea.** If `seq 0 = seq 1`, the `(l·k)`-step vectors take at most 2
    values (all non-crossing windows are equal, all crossing windows are equal).
    By `lk_step_determines_letter` (since `l·k ≡ ±1 mod n`), at most 2 distinct
    `(l·k)`-step vectors implies at most 2 distinct letters, contradicting
    ternarity. -/
private lemma alternating_seq_ne (w : TernaryNecklace n)
    (htern : isTernary w)
    (k r : ℕ) (seq : Fin 2 → ZVector StepSize) (l : ℕ)
    (hcop : Nat.Coprime k n) (hodd : n % 2 = 1)
    (hl_pos : 0 < l) (hl_le : l ≤ n - 2) (hl_odd : l % 2 = 1)
    (hl_mod : l * k % n = 1 ∨ l * k % n = n - 1)
    (hseq : ∀ i : Fin (n - 1),
      Necklace.kStepVector w (r + i.val * k) k =
        seq ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩)
    (hclose : ∀ j : Fin 2,
      Necklace.kStepVector w (r + (n - 1) * k) k ≠ seq j) :
    seq ⟨0, by omega⟩ ≠ seq ⟨1, by omega⟩ := by
  intro heq
  have hn_ge : n ≥ 3 := by omega
  -- Step 1: v₁ = v₂ when seq 0 = seq 1
  have hv12 : Necklace.kStepVector w r (l * k) =
      Necklace.kStepVector w (r + k) (l * k) := by
    have hrec := kStepVector_window_shift_fun w r k l hl_pos
    have hT0 : Necklace.kStepVector w r k = seq ⟨0, by omega⟩ := by
      simpa using hseq ⟨0, by omega⟩
    have hTl : Necklace.kStepVector w (r + l * k) k = seq ⟨0, by omega⟩ := by
      have h := hseq ⟨l, by omega⟩
      simp only [] at h; rw [h]
      have : (⟨l % 2, Nat.mod_lt l (by omega)⟩ : Fin 2) = ⟨1, by omega⟩ := by
        ext; simp only []; exact hl_odd
      rw [this]; exact heq.symm
    rw [hrec, hT0, hTl]
    funext a; simp only [ZVector.sub_apply, ZVector.add_apply]; omega
  -- Step 2: All (l*k)-step vectors take values in {v₁, v₃}
  have hclass : ∀ p : ZMod n,
      Necklace.kStepVector w p.val (l * k) = Necklace.kStepVector w r (l * k) ∨
      Necklace.kStepVector w p.val (l * k) =
        Necklace.kStepVector w (r + (n - l) * k) (l * k) := by
    intro p
    obtain ⟨j, hj⟩ := coprime_affine_surj k r hcop (by omega : n ≥ 2) p
    have hmod : p.val = (r + j.val * k) % n := by
      have h1 : (↑(p.val) : ZMod n) = (↑(r + j.val * k) : ZMod n) := by
        rw [natCast_zmod_val, Nat.cast_add, Nat.cast_mul, natCast_zmod_val, hj]
      have h2 := congr_arg ZMod.val h1
      rwa [ZMod.val_natCast, ZMod.val_natCast,
           Nat.mod_eq_of_lt (ZMod.val_lt p)] at h2
    have hkv : Necklace.kStepVector w p.val (l * k) =
        Necklace.kStepVector w (r + j.val * k) (l * k) := by
      rw [show p.val = (r + j.val * k) % n from hmod]
      exact kStepVector_mod_n w (r + j.val * k) (l * k)
    rw [hkv]
    have hjn := ZMod.val_lt j
    have := alternating_lk_class w k r seq l hodd hl_pos hl_le hl_odd hseq hclose
      j.val hjn
    rw [this]
    by_cases hj_nc : j.val < n - l
    · left; rw [if_pos hj_nc]
      by_cases hpar : j.val % 2 = 0
      · rw [if_pos hpar]
      · rw [if_neg hpar]; exact hv12.symm
    · right; rw [if_neg hj_nc]
  -- Step 3: From ternarity, get 3 pairwise distinct (l*k)-step vectors
  obtain ⟨f, hf⟩ := lk_step_determines_letter w l k hl_mod hn_ge
  obtain ⟨iL, hiL⟩ := ((isTernary_iff_forall w).mp htern) StepSize.L
  obtain ⟨im, him⟩ := ((isTernary_iff_forall w).mp htern) StepSize.m
  obtain ⟨is, his⟩ := ((isTernary_iff_forall w).mp htern) StepSize.s
  have hLm : Necklace.kStepVector w (f iL).val (l * k) ≠
      Necklace.kStepVector w (f im).val (l * k) :=
    mt (hf iL im).mpr (by rw [hiL, him]; decide)
  have hms : Necklace.kStepVector w (f im).val (l * k) ≠
      Necklace.kStepVector w (f is).val (l * k) :=
    mt (hf im is).mpr (by rw [him, his]; decide)
  have hLs : Necklace.kStepVector w (f iL).val (l * k) ≠
      Necklace.kStepVector w (f is).val (l * k) :=
    mt (hf iL is).mpr (by rw [hiL, his]; decide)
  -- Step 4: Pigeonhole — 3 pairwise distinct values can't all be in {v₁, v₃}
  rcases hclass (f iL) with h1 | h1 <;> rcases hclass (f im) with h2 | h2
  · exact hLm (h1.trans h2.symm)
  · rcases hclass (f is) with h3 | h3
    · exact hLs (h1.trans h3.symm)
    · exact hms (h2.trans h3.symm)
  · rcases hclass (f is) with h3 | h3
    · exact hms (h2.trans h3.symm)
    · exact hLs (h1.trans h3.symm)
  · exact hLm (h1.trans h2.symm)

/-- Having all `(l·k)`-step vectors in a 2-element set contradicts ternarity. -/
private lemma two_values_contradicts_ternary (w : TernaryNecklace n)
    (htern : isTernary w) (l k : ℕ)
    (hl_mod : l * k % n = 1 ∨ l * k % n = n - 1) (hn_ge : n ≥ 3)
    (a b : ZVector StepSize)
    (hab : ∀ p : ZMod n, Necklace.kStepVector w p.val (l * k) = a ∨
        Necklace.kStepVector w p.val (l * k) = b) :
    False := by
  obtain ⟨f, hf⟩ := lk_step_determines_letter w l k hl_mod hn_ge
  obtain ⟨iL, hiL⟩ := ((isTernary_iff_forall w).mp htern) StepSize.L
  obtain ⟨im, him⟩ := ((isTernary_iff_forall w).mp htern) StepSize.m
  obtain ⟨is, his⟩ := ((isTernary_iff_forall w).mp htern) StepSize.s
  have hLm := mt (hf iL im).mpr (by rw [hiL, him]; decide)
  have hms := mt (hf im is).mpr (by rw [him, his]; decide)
  have hLs := mt (hf iL is).mpr (by rw [hiL, his]; decide)
  rcases hab (f iL) with h1 | h1 <;> rcases hab (f im) with h2 | h2
  · exact hLm (h1.trans h2.symm)
  · rcases hab (f is) with h3 | h3
    · exact hLs (h1.trans h3.symm)
    · exact hms (h2.trans h3.symm)
  · rcases hab (f is) with h3 | h3
    · exact hms (h2.trans h3.symm)
    · exact hLs (h1.trans h3.symm)
  · exact hLm (h1.trans h2.symm)

/-- When `seq 0 = seq 1` in an alternating sequence, all `(l·k)`-step vectors
    at abstract positions take one of two values (non-crossing vs crossing). -/
private lemma equal_seq_lk_class (w : TernaryNecklace n)
    (k r : ℕ) (seq : Fin 2 → ZVector StepSize) (l : ℕ)
    (hl_pos : 0 < l) (hl_lt : l < n)
    (hseq : ∀ i : Fin (n - 1),
      Necklace.kStepVector w (r + i.val * k) k =
        seq ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩)
    (heq : seq ⟨0, by omega⟩ = seq ⟨1, by omega⟩)
    (j : ℕ) (hj : j < n) :
    Necklace.kStepVector w (r + j * k) (l * k) =
      if j < n - l then Necklace.kStepVector w r (l * k)
      else Necklace.kStepVector w (r + (n - l) * k) (l * k) := by
  have hT_eq : ∀ i : ℕ, i < n - 1 →
      Necklace.kStepVector w (r + i * k) k = seq ⟨0, by omega⟩ := by
    intro i hi
    have h := hseq ⟨i, hi⟩
    rw [h]
    rcases Nat.mod_two_eq_zero_or_one i with hpar | hpar
    · congr 1; ext; exact hpar
    · rw [show (⟨i % 2, _⟩ : Fin 2) = ⟨1, by omega⟩ from by ext; exact hpar]
      exact heq.symm
  induction j with
  | zero => simp [show 0 < n - l from by omega]
  | succ j IH =>
    have hj_lt : j < n := by omega
    have hT_eq' := hT_eq
    have IH := IH hj_lt hT_eq'
    have hrec : Necklace.kStepVector w (r + (j + 1) * k) (l * k) =
        Necklace.kStepVector w (r + j * k) (l * k) -
        Necklace.kStepVector w (r + j * k) k +
        Necklace.kStepVector w (r + (j + l) * k) k := by
      have h := kStepVector_window_shift_fun w (r + j * k) k l hl_pos
      rw [show r + j * k + k = r + (j + 1) * k from by ring,
          show r + j * k + l * k = r + (j + l) * k from by ring] at h
      exact h
    have hTj : Necklace.kStepVector w (r + j * k) k = seq ⟨0, by omega⟩ :=
      hT_eq j (by omega)
    by_cases h_nc : j + 1 < n - l
    · -- Non-crossing: T(j+l) = seq 0, so S(j+1) = S(j) = S(0)
      have hTjl : Necklace.kStepVector w (r + (j + l) * k) k = seq ⟨0, by omega⟩ :=
        hT_eq (j + l) (by omega)
      rw [hrec, hTj, hTjl, IH, if_pos (show j < n - l from by omega), if_pos h_nc]
      funext a; simp only [ZVector.sub_apply, ZVector.add_apply]; omega
    · by_cases h_eq : j + 1 = n - l
      · -- Transition: j+1 = n-l, trivially S(n-l) = S(n-l)
        simp [h_eq]
      · -- Crossing: T(j+l) wraps around, still equals seq 0, so S(j+1) = S(j) = S(n-l)
        have hjl_ge : j + l ≥ n := by omega
        have hperiod : Necklace.kStepVector w (r + (j + l) * k) k =
            Necklace.kStepVector w (r + (j + l - n) * k) k := by
          have hmod : (r + (j + l) * k) % n = (r + (j + l - n) * k) % n := by
            have : r + (j + l) * k = r + (j + l - n) * k + n * k := by
              have : (j + l) * k = (j + l - n) * k + n * k := by
                rw [← add_mul, Nat.sub_add_cancel hjl_ge]
              omega
            rw [this]; exact Nat.add_mul_mod_self_left _ n k
          rw [← kStepVector_mod_n w (r + (j + l) * k) k,
              ← kStepVector_mod_n w (r + (j + l - n) * k) k, hmod]
        have hTjl : Necklace.kStepVector w (r + (j + l) * k) k = seq ⟨0, by omega⟩ := by
          rw [hperiod]; exact hT_eq (j + l - n) (by omega)
        rw [hrec, hTj, hTjl, IH, if_neg (show ¬(j < n - l) from by omega), if_neg h_nc]
        funext a; simp only [ZVector.sub_apply, ZVector.add_apply]; omega

/-- If a ternary necklace has an AS, the two AS terms are distinct.

    **Proof.** Assume `seq 0 = seq 1`. Then all non-closing k-step vectors equal `seq 0`.
    The modular inverse `l₀` (with `l₀·k ≡ 1 mod n`) gives `(l₀·k)`-step vectors
    that take at most 2 values, contradicting ternarity. -/
lemma as_seq_ne (w : TernaryNecklace n) (htern : isTernary w)
    (k r : ℕ) (seq : Fin 2 → ZVector StepSize)
    (hcop : Nat.Coprime k n)
    (hseq : ∀ i : Fin (n - 1),
      Necklace.kStepVector w (r + i.val * k) k =
        seq ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩)
    (_ : ∀ j : Fin 2,
      Necklace.kStepVector w (r + (n - 1) * k) k ≠ seq j) :
    seq ⟨0, by omega⟩ ≠ seq ⟨1, by omega⟩ := by
  intro heq
  have hn_ge : n ≥ 3 := ternary_length_ge_three w htern
  obtain ⟨l₀, hl₀_pos, hl₀_lt, hl₀_inv⟩ := exists_modular_inverse k hcop (by omega)
  -- Classify all (l₀·k)-step vectors into at most 2 values
  have hclass := fun j hj =>
    equal_seq_lk_class w k r seq l₀ hl₀_pos hl₀_lt hseq heq j hj
  -- Every (l₀·k)-step vector equals one of two values
  have hab : ∀ p : ZMod n,
      Necklace.kStepVector w p.val (l₀ * k) =
        Necklace.kStepVector w r (l₀ * k) ∨
      Necklace.kStepVector w p.val (l₀ * k) =
        Necklace.kStepVector w (r + (n - l₀) * k) (l₀ * k) := by
    intro p
    obtain ⟨j, hj⟩ := coprime_affine_surj k r hcop (by omega) p
    have hmod : p.val = (r + j.val * k) % n := by
      have h1 : (↑(p.val) : ZMod n) = (↑(r + j.val * k) : ZMod n) := by
        rw [natCast_zmod_val, Nat.cast_add, Nat.cast_mul, natCast_zmod_val, hj]
      have h2 := congr_arg ZMod.val h1
      rwa [ZMod.val_natCast, ZMod.val_natCast,
           Nat.mod_eq_of_lt (ZMod.val_lt p)] at h2
    rw [show p.val = (r + j.val * k) % n from hmod, kStepVector_mod_n]
    have := hclass j.val (ZMod.val_lt j)
    split_ifs at this
    · exact Or.inl this
    · exact Or.inr this
  exact two_values_contradicts_ternary w htern l₀ k (Or.inl hl₀_inv) hn_ge _ _ hab

/-- Count of even elements below `m` in `ZMod n`. -/
private lemma card_filter_lt_even_zmod (m : ℕ) (hm_even : m % 2 = 0) (hmn : m ≤ n) :
    (Finset.filter (fun j : ZMod n =>
      ZMod.val j < m ∧ ZMod.val j % 2 = 0) Finset.univ).card = m / 2 := by
  rw [show m / 2 = (Finset.range (m / 2)).card from (Finset.card_range _).symm]
  symm
  apply Finset.card_bij (fun i _ => ((2 * i : ℕ) : ZMod n))
  · intro i hi; rw [Finset.mem_range] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    exact ⟨by omega, by omega⟩
  · intro i₁ hi₁ i₂ hi₂ h
    rw [Finset.mem_range] at hi₁ hi₂
    have := congr_arg ZMod.val h
    rw [ZMod.val_natCast, ZMod.val_natCast,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact ⟨j.val / 2, Finset.mem_range.mpr (by omega),
      by rw [show 2 * (j.val / 2) = j.val from by omega]; exact natCast_zmod_val j⟩

/-- Count of odd elements below `m` in `ZMod n`. -/
private lemma card_filter_lt_odd_zmod (m : ℕ) (hm_even : m % 2 = 0) (hmn : m ≤ n) :
    (Finset.filter (fun j : ZMod n =>
      ZMod.val j < m ∧ ZMod.val j % 2 ≠ 0) Finset.univ).card = m / 2 := by
  rw [show m / 2 = (Finset.range (m / 2)).card from (Finset.card_range _).symm]
  symm
  apply Finset.card_bij (fun i _ => ((2 * i + 1 : ℕ) : ZMod n))
  · intro i hi; rw [Finset.mem_range] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    exact ⟨by omega, by omega⟩
  · intro i₁ hi₁ i₂ hi₂ h
    rw [Finset.mem_range] at hi₁ hi₂
    have := congr_arg ZMod.val h
    rw [ZMod.val_natCast, ZMod.val_natCast,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact ⟨j.val / 2, Finset.mem_range.mpr (by omega),
      by rw [show 2 * (j.val / 2) + 1 = j.val from by omega]; exact natCast_zmod_val j⟩

/-- Count of elements ≥ `m` in `ZMod n`. -/
private lemma card_filter_ge_zmod (m : ℕ) (hmn : m ≤ n) :
    (Finset.filter (fun j : ZMod n =>
      m ≤ ZMod.val j) Finset.univ).card = n - m := by
  rw [show n - m = (Finset.range (n - m)).card from (Finset.card_range _).symm]
  symm
  apply Finset.card_bij (fun i _ => ((m + i : ℕ) : ZMod n))
  · intro i hi; rw [Finset.mem_range] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]; omega
  · intro i₁ hi₁ i₂ hi₂ h
    rw [Finset.mem_range] at hi₁ hi₂
    have := congr_arg ZMod.val h
    rw [ZMod.val_natCast, ZMod.val_natCast,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact ⟨j.val - m, Finset.mem_range.mpr (by have := ZMod.val_lt j; omega),
      by rw [show m + (j.val - m) = j.val from by omega]; exact natCast_zmod_val j⟩

/-- In the alternating k-step sequence, the `(l·k)`-step vectors come in
    exactly 3 types with multiplicities `(n−l)/2`, `(n−l)/2`, `l`.

    Non-crossing windows of odd length `l` split by start parity into two
    groups of `(n−l)/2`, and all `l` crossing windows share the same sum
    (by the parity-symmetry argument for arcs in an alternating circle). -/
private lemma alternating_lk_three_types (w : TernaryNecklace n)
    (htern : isTernary w)
    (k r : ℕ) (seq : Fin 2 → ZVector StepSize) (l : ℕ)
    (hcop : Nat.Coprime k n) (hodd : n % 2 = 1)
    (hl_pos : 0 < l) (hl_le : l ≤ n - 2) (hl_odd : l % 2 = 1)
    (hl_mod : l * k % n = 1 ∨ l * k % n = n - 1)
    (hseq : ∀ i : Fin (n - 1),
      Necklace.kStepVector w (r + i.val * k) k =
        seq ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩)
    (hclose : ∀ j : Fin 2,
      Necklace.kStepVector w (r + (n - 1) * k) k ≠ seq j) :
    ∃ (v₁ v₂ v₃ : ZVector StepSize),
      v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃ ∧
      (∀ i : ZMod n, Necklace.kStepVector w i.val (l * k) = v₁ ∨
        Necklace.kStepVector w i.val (l * k) = v₂ ∨
        Necklace.kStepVector w i.val (l * k) = v₃) ∧
      (Finset.filter (fun i : ZMod n =>
        Necklace.kStepVector w i.val (l * k) = v₁) Finset.univ).card = (n - l) / 2 ∧
      (Finset.filter (fun i : ZMod n =>
        Necklace.kStepVector w i.val (l * k) = v₂) Finset.univ).card = (n - l) / 2 ∧
      (Finset.filter (fun i : ZMod n =>
        Necklace.kStepVector w i.val (l * k) = v₃) Finset.univ).card = l := by
  have hn_ge : n ≥ 3 := by omega
  have hne := alternating_seq_ne w htern k r seq l hcop hodd hl_pos hl_le hl_odd
    hl_mod hseq hclose
  -- Define the three (l·k)-step vector types
  set v₁ := Necklace.kStepVector w r (l * k)
  set v₂ := Necklace.kStepVector w (r + k) (l * k)
  set v₃ := Necklace.kStepVector w (r + (n - l) * k) (l * k)
  -- Build coprime affine bijection g : ZMod n → ZMod n
  have hk_unit := coprime_isUnit_zmod k hcop (by omega : n ≥ 2)
  set g : ZMod n → ZMod n := fun j => (↑r : ZMod n) + j * (↑k : ZMod n)
  have g_inj : Function.Injective g := fun j₁ j₂ h => by
    have h1 : j₁ * (↑k : ZMod n) = j₂ * (↑k : ZMod n) := add_left_cancel h
    rw [mul_comm j₁, mul_comm j₂] at h1; exact hk_unit.mul_left_cancel h1
  have g_surj : Function.Surjective g := Finite.surjective_of_injective g_inj
  -- Mod relation: kStepVector at g(j) = kStepVector at r + j.val * k
  have hg_mod : ∀ j : ZMod n,
      Necklace.kStepVector w (g j).val (l * k) =
      Necklace.kStepVector w (r + j.val * k) (l * k) := by
    intro j
    have hmod : (g j).val = (r + j.val * k) % n := by
      have h1 : (↑((g j).val) : ZMod n) = (↑(r + j.val * k) : ZMod n) := by
        rw [natCast_zmod_val]; show g j = _
        rw [Nat.cast_add, Nat.cast_mul, natCast_zmod_val]
      have h2 := congr_arg ZMod.val h1
      rwa [ZMod.val_natCast, ZMod.val_natCast,
           Nat.mod_eq_of_lt (ZMod.val_lt (g j))] at h2
    rw [show (g j).val = (r + j.val * k) % n from hmod]
    exact kStepVector_mod_n w (r + j.val * k) (l * k)
  -- Classification shorthand
  have hclass : ∀ j : ZMod n,
      Necklace.kStepVector w (r + j.val * k) (l * k) =
        if j.val < n - l then
          if j.val % 2 = 0 then v₁ else v₂
        else v₃ :=
    fun j => alternating_lk_class w k r seq l hodd hl_pos hl_le hl_odd hseq hclose
      j.val (ZMod.val_lt j)
  -- Coverage: every position gives v₁, v₂, or v₃
  have hcoverage : ∀ p : ZMod n,
      Necklace.kStepVector w p.val (l * k) = v₁ ∨
      Necklace.kStepVector w p.val (l * k) = v₂ ∨
      Necklace.kStepVector w p.val (l * k) = v₃ := by
    intro p; obtain ⟨j, rfl⟩ := g_surj p
    rw [hg_mod, hclass]
    by_cases hj_nc : j.val < n - l
    · by_cases hpar : j.val % 2 = 0
      · left; rw [if_pos hj_nc, if_pos hpar]
      · right; left; rw [if_pos hj_nc, if_neg hpar]
    · right; right; rw [if_neg hj_nc]
  -- Pairwise distinctness
  have h12 : v₁ ≠ v₂ := by
    intro heq
    have hrec := kStepVector_window_shift_fun w r k l hl_pos
    -- hrec has unfolded forms; use heq : v₁ = v₂ pointwise
    have hT_eq : Necklace.kStepVector w r k = Necklace.kStepVector w (r + l * k) k := by
      funext a
      have h1 := congr_fun hrec a
      have h2 := congr_fun heq a
      simp only [ZVector.sub_apply, ZVector.add_apply] at h1
      change Necklace.kStepVector w r (l * k) a =
        Necklace.kStepVector w (r + k) (l * k) a at h2
      omega
    have hT0 : Necklace.kStepVector w r k = seq ⟨0, by omega⟩ := by
      simpa using hseq ⟨0, by omega⟩
    have hTl : Necklace.kStepVector w (r + l * k) k = seq ⟨1, by omega⟩ := by
      have h := hseq ⟨l, by omega⟩; simp only [] at h; rw [h]
      congr 1; ext; simp only []; exact hl_odd
    rw [hT0, hTl] at hT_eq; exact hne hT_eq
  have h13 : v₁ ≠ v₃ := by
    intro heq
    exact two_values_contradicts_ternary w htern l k hl_mod hn_ge v₁ v₂ (fun p => by
      rcases hcoverage p with h | h | h
      · left; exact h
      · right; exact h
      · left; exact h ▸ heq.symm)
  have h23 : v₂ ≠ v₃ := by
    intro heq
    exact two_values_contradicts_ternary w htern l k hl_mod hn_ge v₁ v₂ (fun p => by
      rcases hcoverage p with h | h | h
      · left; exact h
      · right; exact h
      · right; exact h ▸ heq.symm)
  -- Transfer cardinalities via bijection g
  have hcard_transfer : ∀ (P : ZMod n → Prop) [DecidablePred P],
      (Finset.filter P Finset.univ).card =
      (Finset.filter (fun j => P (g j)) Finset.univ).card := by
    intro P _
    have h : Finset.filter P Finset.univ =
        (Finset.filter (fun j => P (g j)) Finset.univ).image g := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      exact ⟨fun hx => by obtain ⟨j, rfl⟩ := g_surj x; exact ⟨j, hx, rfl⟩,
             fun ⟨_, hj, hgx⟩ => hgx ▸ hj⟩
    rw [h, Finset.card_image_of_injective _ g_inj]
  -- Classification iff for the three types
  have hiff_v1 : ∀ j : ZMod n,
      Necklace.kStepVector w (g j).val (l * k) = v₁ ↔
      (j.val < n - l ∧ j.val % 2 = 0) := by
    intro j; rw [hg_mod, hclass]; constructor
    · intro heq
      by_cases hj_nc : j.val < n - l
      · rw [if_pos hj_nc] at heq; by_cases hpar : j.val % 2 = 0
        · exact ⟨hj_nc, hpar⟩
        · rw [if_neg hpar] at heq; exact absurd heq h12.symm
      · rw [if_neg hj_nc] at heq; exact absurd heq h13.symm
    · intro ⟨hj_nc, hpar⟩; rw [if_pos hj_nc, if_pos hpar]
  have hiff_v2 : ∀ j : ZMod n,
      Necklace.kStepVector w (g j).val (l * k) = v₂ ↔
      (j.val < n - l ∧ j.val % 2 ≠ 0) := by
    intro j; rw [hg_mod, hclass]; constructor
    · intro heq
      by_cases hj_nc : j.val < n - l
      · rw [if_pos hj_nc] at heq; by_cases hpar : j.val % 2 = 0
        · rw [if_pos hpar] at heq; exact absurd heq h12
        · exact ⟨hj_nc, hpar⟩
      · rw [if_neg hj_nc] at heq; exact absurd heq h23.symm
    · intro ⟨hj_nc, hpar⟩; rw [if_pos hj_nc, if_neg hpar]
  have hiff_v3 : ∀ j : ZMod n,
      Necklace.kStepVector w (g j).val (l * k) = v₃ ↔
      (n - l ≤ j.val) := by
    intro j; rw [hg_mod, hclass]; constructor
    · intro heq
      by_contra hlt; push_neg at hlt
      rw [if_pos hlt] at heq; by_cases hpar : j.val % 2 = 0
      · rw [if_pos hpar] at heq; exact absurd heq h13
      · rw [if_neg hpar] at heq; exact absurd heq h23
    · intro hge; rw [if_neg (by omega)]
  refine ⟨v₁, v₂, v₃, h12, h13, h23, hcoverage, ?_, ?_, ?_⟩
  -- Cardinality v₁ = (n-l)/2
  · rw [hcard_transfer, show Finset.filter (fun j => Necklace.kStepVector w (g j).val
        (l * k) = v₁) Finset.univ = Finset.filter (fun j : ZMod n =>
        ZMod.val j < n - l ∧ ZMod.val j % 2 = 0) Finset.univ from
      Finset.filter_congr (fun j _ => hiff_v1 j)]
    exact card_filter_lt_even_zmod (n - l) (by omega) (by omega)
  -- Cardinality v₂ = (n-l)/2
  · rw [hcard_transfer, show Finset.filter (fun j => Necklace.kStepVector w (g j).val
        (l * k) = v₂) Finset.univ = Finset.filter (fun j : ZMod n =>
        ZMod.val j < n - l ∧ ZMod.val j % 2 ≠ 0) Finset.univ from
      Finset.filter_congr (fun j _ => hiff_v2 j)]
    exact card_filter_lt_odd_zmod (n - l) (by omega) (by omega)
  -- Cardinality v₃ = l
  · rw [hcard_transfer, show Finset.filter (fun j => Necklace.kStepVector w (g j).val
        (l * k) = v₃) Finset.univ = Finset.filter (fun j : ZMod n =>
        n - l ≤ ZMod.val j) Finset.univ from
      Finset.filter_congr (fun j _ => hiff_v3 j)]
    rw [card_filter_ge_zmod (n - l) (by omega)]; omega

private lemma as_alternating_letter_counts (w : TernaryNecklace n)
    (_ : Necklace.isPrimitive w) (htern : isTernary w)
    (k r : ℕ) (seq : Fin 2 → ZVector StepSize) (l : ℕ)
    (hcop : Nat.Coprime k n) (hodd : n % 2 = 1)
    (hl_pos : 0 < l) (hl_le : l ≤ n - 2) (hl_odd : l % 2 = 1)
    (hl_mod : l * k % n = 1 ∨ l * k % n = n - 1)
    (hseq : ∀ i : Fin (n - 1),
      Necklace.kStepVector w (r + i.val * k) k =
        seq ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩)
    (hclose : ∀ j : Fin 2,
      Necklace.kStepVector w (r + (n - 1) * k) k ≠ seq j) :
    ∃ x : StepSize,
      Necklace.count w x = l ∧
      ∀ y : StepSize, y ≠ x → Necklace.count w y = (n - l) / 2 := by
  have hn_ge := ternary_length_ge_three w htern
  -- Step 1: The (l·k)-step vector determines the letter (up to uniform shift).
  obtain ⟨f, hf⟩ := lk_step_determines_letter w l k hl_mod hn_ge
  -- Step 2: The lk-step vectors come in 3 types with multiplicities (n-l)/2, (n-l)/2, l.
  obtain ⟨v₁, v₂, v₃, hv12, hv13, hv23, h_cover, hc1, hc2, hc3⟩ :=
    alternating_lk_three_types w htern k r seq l hcop hodd hl_pos hl_le hl_odd hl_mod hseq hclose
  -- Step 3: Build φ : StepSize → ZVector StepSize mapping each letter to its lk-type.
  -- For each letter a, pick a representative position with that letter.
  have hrep : ∀ a : StepSize, ∃ i : ZMod n, w i = a :=
    (isTernary_iff_forall w).mp htern
  let φ : StepSize → ZVector StepSize :=
    fun a => Necklace.kStepVector w (f (hrep a).choose).val (l * k)
  -- φ is well-defined: if w(i) = a then kStepVector(f(i)) = φ(a)
  have hφ_wd : ∀ (a : StepSize) (i : ZMod n), w i = a →
      Necklace.kStepVector w (f i).val (l * k) = φ a := by
    intro a i hi
    exact (hf i (hrep a).choose).mp (hi.trans (hrep a).choose_spec.symm)
  -- φ is injective
  have hφ_inj : Function.Injective φ := by
    intro a b hab
    have := (hf (hrep a).choose (hrep b).choose).mpr hab
    rw [(hrep a).choose_spec, (hrep b).choose_spec] at this
    exact this
  -- The letter filter equals the kStepVector filter (composed with f)
  have h_sets : ∀ a : StepSize,
      Finset.filter (fun i : ZMod n => w i = a) Finset.univ =
      Finset.filter (fun i : ZMod n =>
        Necklace.kStepVector w (f i).val (l * k) = φ a) Finset.univ := by
    intro a; ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => hφ_wd a i h,
      fun h => by
        have := (hf i (hrep a).choose).mpr h
        rwa [(hrep a).choose_spec] at this⟩
  -- Composing with the bijection f preserves filter cardinality
  have h_card_f : ∀ v : ZVector StepSize,
      (Finset.filter (fun i : ZMod n =>
        Necklace.kStepVector w (f i).val (l * k) = v) Finset.univ).card =
      (Finset.filter (fun j : ZMod n =>
        Necklace.kStepVector w j.val (l * k) = v) Finset.univ).card := by
    intro v
    have h_image : (Finset.filter (fun i : ZMod n =>
        Necklace.kStepVector w (f i).val (l * k) = v) Finset.univ).image f =
        Finset.filter (fun j : ZMod n =>
          Necklace.kStepVector w j.val (l * k) = v) Finset.univ := by
      ext j
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨i, hi, hfi⟩ => hfi ▸ hi,
        fun hj => ⟨f.symm j, by simp [f.apply_symm_apply, hj], f.apply_symm_apply j⟩⟩
    rw [← h_image, Finset.card_image_of_injective _ f.injective]
  -- Combine: count w a = filter card for φ(a)
  have hcount : ∀ a : StepSize,
      Necklace.count w a =
      (Finset.filter (fun j : ZMod n =>
        Necklace.kStepVector w j.val (l * k) = φ a) Finset.univ).card := by
    intro a; unfold Necklace.count; rw [h_sets a, h_card_f (φ a)]
  -- φ maps into {v₁, v₂, v₃}
  have hφ_range : ∀ a : StepSize, φ a = v₁ ∨ φ a = v₂ ∨ φ a = v₃ :=
    fun a => h_cover (f (hrep a).choose)
  -- By pigeonhole (3 → 2 is impossible), ∃ x with φ(x) = v₃
  have hφ_surj_v3 : ∃ x : StepSize, φ x = v₃ := by
    by_contra h_no; push_neg at h_no
    have h_v12 : ∀ a, φ a = v₁ ∨ φ a = v₂ := by
      intro a; rcases hφ_range a with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h (h_no a)
    rcases h_v12 StepSize.L, h_v12 StepSize.m, h_v12 StepSize.s with
      ⟨hL | hL, hm | hm, hs | hs⟩ <;> first
      | exact absurd (hφ_inj (hL.trans hm.symm)) (by decide)
      | exact absurd (hφ_inj (hL.trans hs.symm)) (by decide)
      | exact absurd (hφ_inj (hm.trans hs.symm)) (by decide)
  -- Finish: the letter with φ(x) = v₃ has count l, the others have count (n-l)/2.
  obtain ⟨x, hx⟩ := hφ_surj_v3
  refine ⟨x, ?_, ?_⟩
  · rw [hcount x, hx]; exact hc3
  · intro y hy
    have hφy_ne : φ y ≠ v₃ := fun h => hy (hφ_inj (h.trans hx.symm))
    rcases hφ_range y with hvy | hvy | hvy
    · rw [hcount y, hvy]; exact hc1
    · rw [hcount y, hvy]; exact hc2
    · exact absurd hvy hφy_ne

/-- Core combinatorial lemma: In an odd primitive ternary AS, there is a
    distinguished step size such that the other two have equal counts.

    Combines `exists_odd_quasi_inverse` (to find odd `l`) with
    `as_alternating_letter_counts` (which gives counts `(l, (n−l)/2, (n−l)/2)`). -/
private lemma as_odd_two_counts_equal (w : TernaryNecklace n)
    (hprim : Necklace.isPrimitive w) (htern : isTernary w)
    (k r : ℕ) (seq : Fin 2 → ZVector StepSize)
    (hcop : Nat.Coprime k n) (hodd : n % 2 = 1)
    (hseq : ∀ i : Fin (n - 1),
      Necklace.kStepVector w (r + i.val * k) k =
        seq ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩)
    (hclose : ∀ j : Fin 2,
      Necklace.kStepVector w (r + (n - 1) * k) k ≠ seq j) :
    ∃ x : StepSize, ∀ y z : StepSize, y ≠ x → z ≠ x →
      Necklace.count w y = Necklace.count w z := by
  have hn_ge := ternary_length_ge_three w htern
  obtain ⟨l, hl_pos, hl_le, hl_odd, hl_mod⟩ :=
    exists_odd_quasi_inverse k hodd hcop hn_ge
  obtain ⟨x, _, hx_other⟩ :=
    as_alternating_letter_counts w hprim htern k r seq l hcop hodd
      hl_pos hl_le hl_odd hl_mod hseq hclose
  exact ⟨x, fun y z hy hz => by rw [hx_other y hy, hx_other z hz]⟩

/-- In an odd AS, two of the three step-size counts are equal
    (and both counts are positive by the ternary assumption).

    Note: when `n = 3`, all three counts equal 1, so `a = b` is possible. -/
private lemma as_odd_has_two_equal_counts (w : TernaryNecklace n)
    (hprim : Necklace.isPrimitive w) (htern : isTernary w)
    (has : hasAS w) (hodd : n % 2 = 1) :
    ∃ (x : StepSize) (a b : ℕ),
      Necklace.count w x = a ∧
      (∀ y : StepSize, y ≠ x → Necklace.count w y = b) ∧
      a > 0 ∧ b > 0 := by
  obtain ⟨k, r, seq, hk_lt_n, hcop, hseq, hclose⟩ := has
  obtain ⟨x, hx_eq⟩ := as_odd_two_counts_equal w hprim htern k r seq hcop hodd hseq hclose
  -- Pick any y ≠ x to name the "other" count
  obtain ⟨y, hy⟩ : ∃ y : StepSize, y ≠ x := by
    cases x with
    | L => exact ⟨StepSize.m, by decide⟩
    | m => exact ⟨StepSize.L, by decide⟩
    | s => exact ⟨StepSize.L, by decide⟩
  exact ⟨x, Necklace.count w x, Necklace.count w y, rfl,
    fun z hz => hx_eq z y hz hy,
    count_pos_of_isTernary w htern x,
    count_pos_of_isTernary w htern y⟩

/-- Odd AS scales have step signature S₃-equivalent to `(a, b, b)`.

**Proof sketch.** Let `n ≥ 3` and let `g₁, g₂` be the two terms of the AS, with
closing vector `g₃`. The circular word of stacked `k`-steps is `(g₁ g₂)^⌊n/2⌋ g₃`. For a step
formed by stacking `l` generators (which we may take to be odd, since `n` is odd
and we can take equave (equave := step signature as vector) complements), the three `l`-step vector sizes are:

1. `⌈k/2⌉ g₁ + ⌊k/2⌋ g₂`
2. `⌊k/2⌋ g₁ + ⌈k/2⌉ g₂`
3. `⌊k/2⌋ g₁ + ⌊k/2⌋ g₂ + g₃`

By counting length-`l` subwords of `(g₁ g₂)^⌊n/2⌋`, the first two sizes both
occur `(n − l) / 2` times. In particular, for `l = 1`, `g₁` and `g₂` each occur
`(n − 1) / 2` times and `g₃` occurs once, giving step signature `(1, (n−1)/2, (n−1)/2)`
up to S₃-equivalence. -/
theorem as_odd_stepSignature (w : TernaryNecklace n)
    (hprim : Necklace.isPrimitive w) (htern : isTernary w)
    (has : hasAS w) (hodd : n % 2 = 1) :
    ∃ (σ : Equiv.Perm StepSize) (a b : ℕ),
      a > 0 ∧ b > 0 ∧ n = a + 2 * b ∧
      Necklace.count (Necklace.applyPerm σ w) StepSize.L = a ∧
      Necklace.count (Necklace.applyPerm σ w) StepSize.m = b ∧
      Necklace.count (Necklace.applyPerm σ w) StepSize.s = b := by
  -- Step 1: From the AS, extract that two letter counts are equal.
  obtain ⟨x, a, b, hxa, hxb, ha_pos, hb_pos⟩ :=
    as_odd_has_two_equal_counts w hprim htern has hodd
  by_cases hab : a = b
  · -- Special case: all three counts are equal (happens when n = 3).
    subst hab
    have hall : ∀ st : StepSize, Necklace.count w st = a := by
      intro st
      by_cases h : st = x
      · subst h; exact hxa
      · exact hxb st h
    refine ⟨1, a, a, ha_pos, ha_pos, ?_, ?_, ?_, ?_⟩
    · linarith [count_total w, hall StepSize.L, hall StepSize.m, hall StepSize.s]
    all_goals rw [Necklace.applyPerm_one]; exact hall _
  · -- Step 2: Find a permutation σ putting the unique count at L.
    obtain ⟨σ, hσL, hσm, hσs⟩ :=
      exists_perm_canonical_signature_two_equal w a b hab ⟨x, hxa, hxb⟩
    -- Step 3: Assemble the result.
    refine ⟨σ, a, b, ha_pos, hb_pos, ?_, hσL, hσm, hσs⟩
    -- Prove n = a + 2 * b from the total count identity.
    have htotal := count_total w
    cases x with
    | L => linarith [hxb StepSize.m (by decide), hxb StepSize.s (by decide)]
    | m => linarith [hxb StepSize.L (by decide), hxb StepSize.s (by decide)]
    | s => linarith [hxb StepSize.L (by decide), hxb StepSize.m (by decide)]

/-- The full-cycle k-step vector (step count = n) is the same regardless of
    starting position, since each full cycle visits all n positions. -/
private lemma kStepVector_full_const (w : TernaryNecklace n) (i : ℕ) :
    Necklace.kStepVector w i n = Necklace.kStepVector w 0 n := by
  have hn_pos := NeZero.pos n
  suffices h : ∀ j, Necklace.kStepVector w (j + 1) n = Necklace.kStepVector w j n by
    induction i with
    | zero => rfl
    | succ i ih => exact (h i).trans ih
  intro j; funext a
  have h1 := kStepVector_add w j 1 (n - 1) a
  have h2 := kStepVector_add w (j + 1) (n - 1) 1 a
  have hn1 : 1 + (n - 1) = n := by omega
  have hn2 : n - 1 + 1 = n := by omega
  rw [hn1] at h1; rw [hn2] at h2
  have hperiod := congr_fun (kStepVector_add_n w j 1) a
  rw [show j + 1 + (n - 1) = j + n from by omega] at h2
  linarith

/-- Equave complement: k-step and (n−k)-step multisets are in bijection
    via `M ↦ (total multiset) − M`, so their distinct-count is the same. -/
private lemma kStepMultisets_card_eq_complement (w : TernaryNecklace n)
    (k : ℕ) (_ : 0 < k) (hk' : k < n) :
    (Necklace.allKStepMultisets w k).toFinset.card =
    (Necklace.allKStepMultisets w (n - k)).toFinset.card := by
  rw [← distinctKStepVectors_card_eq, ← distinctKStepVectors_card_eq]
  unfold distinctKStepVectors
  -- Define the total vector and complement map
  set T := Necklace.kStepVector w 0 n
  set f : ZVector StepSize → ZVector StepSize := fun v a => T a - v a
  have hf_inj : Function.Injective f := by
    intro v₁ v₂ h; funext a; have := congr_fun h a; simp only [f] at this; omega
  -- Complement relation: kStepVector w i k + kStepVector w (i+k) (n-k) = T
  have hcomp : ∀ i a,
      Necklace.kStepVector w i k a + Necklace.kStepVector w (i + k) (n - k) a = T a := by
    intro i a
    have h := kStepVector_add w i k (n - k) a
    rw [show k + (n - k) = n from by omega] at h
    have hfull := congr_fun (kStepVector_full_const w i) a
    linarith
  -- Show the two toFinsets are related by f
  suffices h : (Necklace.allKStepVectors w (n - k)).toFinset =
      (Necklace.allKStepVectors w k).toFinset.image f by
    rw [h, Finset.card_image_of_injective _ hf_inj]
  ext v; simp only [Finset.mem_image, List.mem_toFinset]
  unfold Necklace.allKStepVectors
  simp only [List.mem_map, List.mem_range]
  constructor
  · -- v is an (n-k)-step vector → v = f(some k-step vector)
    rintro ⟨j, hj, rfl⟩
    -- Use j + (n-k) as the unreduced starting index for the k-step vector
    refine ⟨Necklace.kStepVector w (j + (n - k)) k,
      ⟨(j + (n - k)) % n, Nat.mod_lt _ (by omega),
        kStepVector_mod_n w (j + (n - k)) k⟩, ?_⟩
    funext a; simp only [f]
    have hshift : Necklace.kStepVector w (j + (n - k) + k) (n - k) =
        Necklace.kStepVector w j (n - k) := by
      rw [show j + (n - k) + k = j + n from by omega]
      exact kStepVector_add_n w j (n - k)
    have := hcomp (j + (n - k)) a
    rw [congr_fun hshift a] at this; omega
  · -- v = f(some k-step vector) → v is an (n-k)-step vector
    rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    refine ⟨(i + k) % n, Nat.mod_lt _ (by omega), ?_⟩
    funext a; simp only [f]
    rw [congr_fun (kStepVector_mod_n w (i + k) (n - k)) a]
    have := hcomp i a; omega

/-- Adding a full cycle `n` to the step count doesn't change the number of
    distinct k-step vectors, since each vector shifts by the constant `T`. -/
private lemma kStepVectors_card_add_n (w : TernaryNecklace n) (m : ℕ) :
    (Necklace.allKStepVectors w (m + n)).toFinset.card =
    (Necklace.allKStepVectors w m).toFinset.card := by
  set T := Necklace.kStepVector w 0 n
  -- Each (m+n)-step vector = corresponding m-step vector + T
  have hshift : ∀ i, Necklace.kStepVector w i (m + n) =
      Necklace.kStepVector w i m + T := by
    intro i; funext a
    show _ = Necklace.kStepVector w i m a + T a
    have h := kStepVector_add w i m n a
    have hfull := congr_fun (kStepVector_full_const w (i + m)) a; linarith
  -- (· + T) is injective
  have hinj : Function.Injective (· + T : ZVector StepSize → ZVector StepSize) := by
    intro a b h; funext x
    have := congr_fun h x
    change a x + T x = b x + T x at this; linarith
  -- Show the two toFinsets are related by translation
  suffices h : (Necklace.allKStepVectors w (m + n)).toFinset =
      (Necklace.allKStepVectors w m).toFinset.image (· + T) by
    rw [h, Finset.card_image_of_injective _ hinj]
  ext v; simp only [Finset.mem_image, List.mem_toFinset]
  unfold Necklace.allKStepVectors; simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨Necklace.kStepVector w i m, ⟨i, hi, rfl⟩, (hshift i).symm⟩
  · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, hi, hshift i⟩

/-- Reducing the step count mod `n` doesn't change the distinct vector count. -/
lemma kStepVectors_card_mod_n (w : TernaryNecklace n) (m : ℕ) :
    (Necklace.allKStepVectors w m).toFinset.card =
    (Necklace.allKStepVectors w (m % n)).toFinset.card := by
  suffices h : ∀ q, (Necklace.allKStepVectors w (m % n + n * q)).toFinset.card =
      (Necklace.allKStepVectors w (m % n)).toFinset.card by
    conv_lhs => rw [show m = m % n + n * (m / n) from (Nat.mod_add_div m n).symm]
    exact h (m / n)
  intro q; induction q with
  | zero => rw [Nat.mul_zero, Nat.add_zero]
  | succ q ih =>
    rw [show m % n + n * (q + 1) = m % n + n * q + n from by ring]
    rw [kStepVectors_card_add_n]; exact ih

/-- For an odd `l ∈ [1, n−2]`, the `(l·k₀)`-step vectors take exactly 3 distinct
    values.  Uses `alternating_lk_class` for classification (no `hl_mod` needed)
    and proves distinctness via `hne : seq 0 ≠ seq 1` (from `alternating_seq_ne`)
    and `hclose`. -/
private lemma as_odd_lk_three_distinct (w : TernaryNecklace n)
    (htern : isTernary w)
    (k₀ r : ℕ) (seq : Fin 2 → ZVector StepSize) (l : ℕ)
    (hcop : Nat.Coprime k₀ n) (hodd : n % 2 = 1)
    (hl_pos : 0 < l) (hl_le : l ≤ n - 2) (hl_odd : l % 2 = 1)
    (hseq : ∀ i : Fin (n - 1),
      Necklace.kStepVector w (r + i.val * k₀) k₀ =
        seq ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩)
    (hclose : ∀ j : Fin 2,
      Necklace.kStepVector w (r + (n - 1) * k₀) k₀ ≠ seq j) :
    (Necklace.allKStepVectors w (l * k₀)).toFinset.card = 3 := by
  have hn_ge := ternary_length_ge_three w htern
  -- Get seq 0 ≠ seq 1 from alternating_seq_ne (using exists_odd_quasi_inverse)
  obtain ⟨l₀, hl₀_pos, hl₀_le, hl₀_odd, hl₀_mod⟩ :=
    exists_odd_quasi_inverse k₀ hodd hcop hn_ge
  have hne : seq ⟨0, by omega⟩ ≠ seq ⟨1, by omega⟩ :=
    alternating_seq_ne w htern k₀ r seq l₀ hcop hodd hl₀_pos hl₀_le hl₀_odd hl₀_mod hseq hclose
  -- Name the three vector types
  set v₁ := Necklace.kStepVector w r (l * k₀)
  set v₂ := Necklace.kStepVector w (r + k₀) (l * k₀)
  set v₃ := Necklace.kStepVector w (r + (n - l) * k₀) (l * k₀)
  -- Classification: every position gives one of v₁, v₂, v₃
  have hclass : ∀ j, j < n →
      Necklace.kStepVector w (r + j * k₀) (l * k₀) = v₁ ∨
      Necklace.kStepVector w (r + j * k₀) (l * k₀) = v₂ ∨
      Necklace.kStepVector w (r + j * k₀) (l * k₀) = v₃ := by
    intro j hj
    have := alternating_lk_class w k₀ r seq l hodd hl_pos hl_le hl_odd hseq hclose j hj
    rw [this]
    by_cases hjnl : j < n - l
    · rw [if_pos hjnl]
      by_cases hpar : j % 2 = 0
      · left; rw [if_pos hpar]
      · right; left; rw [if_neg hpar]
    · right; right; rw [if_neg hjnl]
  -- v₁ ≠ v₂: window shift gives v₂ = v₁ - seq(0) + seq(l % 2) = v₁ - seq(0) + seq(1)
  have hv12 : v₁ ≠ v₂ := by
    intro heq
    have hrec := kStepVector_window_shift_fun w r k₀ l hl_pos
    rw [show r + k₀ = r + 1 * k₀ from by ring] at hrec
    -- kStepVector at r = seq 0
    have hT0 : Necklace.kStepVector w r k₀ = seq ⟨0, by omega⟩ := by
      simpa using hseq ⟨0, by omega⟩
    -- kStepVector at r + l*k₀ = seq (l % 2) = seq 1
    have hTl : Necklace.kStepVector w (r + l * k₀) k₀ = seq ⟨1, by omega⟩ := by
      have h := hseq ⟨l, by omega⟩
      simp only [] at h; rw [h]
      congr 1; ext; simp only []; exact hl_odd
    rw [show r + 1 * k₀ = r + k₀ from by ring] at hrec
    -- v₂ = v₁ - seq(0) + seq(1), and v₁ = v₂ gives seq(0) = seq(1)
    apply hne; funext a
    have hrec_a : v₂ a = v₁ a - Necklace.kStepVector w r k₀ a +
        Necklace.kStepVector w (r + l * k₀) k₀ a := congr_fun hrec a
    rw [hT0, hTl] at hrec_a
    have := congr_fun heq a
    change v₁ a = v₂ a at this
    linarith
  -- v₃ ≠ v₂: crossing boundary recurrence
  have hv23 : v₂ ≠ v₃ := by
    intro heq
    -- n - l is even (n odd, l odd), so n - l - 1 is odd
    have hnl_par : (n - l - 1) % 2 = 1 := by omega
    -- The vector at position n-l-1 (non-crossing, odd) equals v₂
    have hprev : Necklace.kStepVector w (r + (n - l - 1) * k₀) (l * k₀) = v₂ := by
      have := alternating_lk_class w k₀ r seq l hodd hl_pos hl_le hl_odd hseq hclose
        (n - l - 1) (by omega)
      rw [this, if_pos (by omega : n - l - 1 < n - l), if_neg (by omega : ¬(n - l - 1) % 2 = 0)]
    -- Window shift: v₃ = v_prev - seq(n-l-1 mod 2) + close
    have hrec := kStepVector_window_shift_fun w (r + (n - l - 1) * k₀) k₀ l hl_pos
    have hrw1 : r + (n - l - 1) * k₀ + k₀ = r + (n - l) * k₀ := by
      calc _ = r + ((n - l - 1) + 1) * k₀ := by ring
        _ = _ := by rw [show n - l - 1 + 1 = n - l from by omega]
    have hrw2 : r + (n - l - 1) * k₀ + l * k₀ = r + (n - 1) * k₀ := by
      calc _ = r + ((n - l - 1) + l) * k₀ := by ring
        _ = _ := by rw [show n - l - 1 + l = n - 1 from by omega]
    rw [hrw1, hrw2] at hrec
    -- seq at position n-l-1: parity is 1
    have hTnl : Necklace.kStepVector w (r + (n - l - 1) * k₀) k₀ =
        seq ⟨1, by omega⟩ := by
      have h := hseq ⟨n - l - 1, by omega⟩; simp only [] at h; rw [h]
      congr 1; ext; simp only []; exact hnl_par
    -- From hrec: v₃ = v₂ - seq(1) + close. If v₃ = v₂ then close = seq(1).
    have hclose1 := hclose ⟨1, by omega⟩
    apply hclose1; funext a
    have hrec_a := congr_fun hrec a
    simp only [ZVector.sub_apply, ZVector.add_apply] at hrec_a
    have hprev_a := congr_fun hprev a
    have heq_a := congr_fun heq a
    change v₂ a = v₃ a at heq_a
    rw [hTnl] at hrec_a; linarith
  -- v₃ ≠ v₁: same recurrence, but v₁ = v₂ - seq(0) + seq(1) "inverted"
  have hv13 : v₁ ≠ v₃ := by
    intro heq
    have hnl_par : (n - l - 1) % 2 = 1 := by omega
    have hprev : Necklace.kStepVector w (r + (n - l - 1) * k₀) (l * k₀) = v₂ := by
      have := alternating_lk_class w k₀ r seq l hodd hl_pos hl_le hl_odd hseq hclose
        (n - l - 1) (by omega)
      rw [this, if_pos (by omega : n - l - 1 < n - l), if_neg (by omega : ¬(n - l - 1) % 2 = 0)]
    have hrec := kStepVector_window_shift_fun w (r + (n - l - 1) * k₀) k₀ l hl_pos
    have hrw1 : r + (n - l - 1) * k₀ + k₀ = r + (n - l) * k₀ := by
      calc _ = r + ((n - l - 1) + 1) * k₀ := by ring
        _ = _ := by rw [show n - l - 1 + 1 = n - l from by omega]
    have hrw2 : r + (n - l - 1) * k₀ + l * k₀ = r + (n - 1) * k₀ := by
      calc _ = r + ((n - l - 1) + l) * k₀ := by ring
        _ = _ := by rw [show n - l - 1 + l = n - 1 from by omega]
    rw [hrw1, hrw2] at hrec
    have hTnl : Necklace.kStepVector w (r + (n - l - 1) * k₀) k₀ =
        seq ⟨1, by omega⟩ := by
      have h := hseq ⟨n - l - 1, by omega⟩; simp only [] at h; rw [h]
      congr 1; ext; simp only []; exact hnl_par
    -- From v₂ = v₁ - seq(0) + seq(1) and v₃ = v₂ - seq(1) + close:
    -- v₁ = v₃ gives close = seq(0)
    have hT0 : Necklace.kStepVector w r k₀ = seq ⟨0, by omega⟩ := by
      simpa using hseq ⟨0, by omega⟩
    have hTl : Necklace.kStepVector w (r + l * k₀) k₀ = seq ⟨1, by omega⟩ := by
      have h := hseq ⟨l, by omega⟩; simp only [] at h; rw [h]
      congr 1; ext; simp only []; exact hl_odd
    have hrec_v2 := kStepVector_window_shift_fun w r k₀ l hl_pos
    have hclose0 := hclose ⟨0, by omega⟩
    apply hclose0; funext a
    have hrec_a := congr_fun hrec a
    simp only [ZVector.sub_apply, ZVector.add_apply] at hrec_a
    have hprev_a := congr_fun hprev a
    have heq_a := congr_fun heq a; change v₁ a = v₃ a at heq_a
    rw [hTnl] at hrec_a
    have hrec_v2_a := congr_fun hrec_v2 a
    simp only [ZVector.sub_apply, ZVector.add_apply] at hrec_v2_a
    rw [hT0, hTl] at hrec_v2_a; linarith
  -- All three values appear (using coprime_affine_surj)
  -- v₁ appears: position j = 0
  have hv1_mem : v₁ ∈ (Necklace.allKStepVectors w (l * k₀)).toFinset := by
    rw [List.mem_toFinset]; unfold Necklace.allKStepVectors
    simp only [List.mem_map, List.mem_range]
    exact ⟨r % n, Nat.mod_lt _ (by omega),
      kStepVector_mod_n w r (l * k₀)⟩
  -- v₂ appears: position r + k₀
  have hv2_mem : v₂ ∈ (Necklace.allKStepVectors w (l * k₀)).toFinset := by
    rw [List.mem_toFinset]; unfold Necklace.allKStepVectors
    simp only [List.mem_map, List.mem_range]
    exact ⟨(r + k₀) % n, Nat.mod_lt _ (by omega),
      kStepVector_mod_n w (r + k₀) (l * k₀)⟩
  -- v₃ appears: position r + (n-l)*k₀
  have hv3_mem : v₃ ∈ (Necklace.allKStepVectors w (l * k₀)).toFinset := by
    rw [List.mem_toFinset]; unfold Necklace.allKStepVectors
    simp only [List.mem_map, List.mem_range]
    exact ⟨(r + (n - l) * k₀) % n, Nat.mod_lt _ (by omega),
      kStepVector_mod_n w (r + (n - l) * k₀) (l * k₀)⟩
  -- Every element is one of the three
  have hcover : ∀ v ∈ (Necklace.allKStepVectors w (l * k₀)).toFinset,
      v = v₁ ∨ v = v₂ ∨ v = v₃ := by
    intro v hv; rw [List.mem_toFinset] at hv
    unfold Necklace.allKStepVectors at hv
    simp only [List.mem_map, List.mem_range] at hv
    obtain ⟨i, hi, rfl⟩ := hv
    -- Map i to abstract position j via coprime_affine_surj
    obtain ⟨j, hj⟩ := coprime_affine_surj k₀ r hcop (by omega) ((i : ℕ) : ZMod n)
    have hmod : i = (r + j.val * k₀) % n := by
      have h1 : (↑i : ZMod n) = (↑(r + j.val * k₀) : ZMod n) := by
        rw [Nat.cast_add, Nat.cast_mul, natCast_zmod_val]; exact hj
      have h2 := congr_arg ZMod.val h1
      rwa [ZMod.val_natCast, ZMod.val_natCast,
           Nat.mod_eq_of_lt (by omega : i < n)] at h2
    rw [hmod, kStepVector_mod_n]
    exact hclass j.val (ZMod.val_lt j)
  -- Conclude: card = 3
  have hsub : (Necklace.allKStepVectors w (l * k₀)).toFinset ⊆
      {v₁, v₂, v₃} := by
    intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hcover v hv
  have hsup : {v₁, v₂, v₃} ⊆ (Necklace.allKStepVectors w (l * k₀)).toFinset := by
    intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact hv1_mem
    · exact hv2_mem
    · exact hv3_mem
  have heq_set := Finset.Subset.antisymm hsub hsup
  rw [heq_set]
  have h1 : v₁ ∉ ({v₂, v₃} : Finset _) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨hv12, hv13⟩
  have h2 : v₂ ∉ ({v₃} : Finset _) := by
    simp only [Finset.mem_singleton]; exact hv23
  rw [Finset.card_insert_eq_ite, if_neg h1, Finset.card_insert_eq_ite, if_neg h2,
      Finset.card_singleton]

/-- In an odd AS, for any `k` with `0 < k < n`, the k-step multisets take
    exactly 3 values.

    **Proof.** Let `k₀` be the AS step size with `gcd(k₀, n) = 1`.
    Choose `l ∈ [1, n−1]` with `l·k₀ ≡ k (mod n)`.
    If `l` is odd (hence `l ≤ n−2`): `as_odd_lk_three_distinct` gives exactly
    3 `l·k₀`-step vector types, and `kStepVectors_card_mod_n` transfers to `k`.
    If `l` is even: `n − l` is odd and `(n−l)·k₀ ≡ n − k (mod n)`, so the
    `(n−k)`-step multisets take 3 values. By equave complementation
    (`kStepMultisets_card_eq_complement`), the k-step multisets also take 3 values. -/
private lemma as_odd_kStep_three_values (w : TernaryNecklace n)
    (_ : Necklace.isPrimitive w) (htern : isTernary w)
    (has : hasAS w) (hodd : n % 2 = 1)
    (k : ℕ) (hk : 0 < k) (hk' : k < n) :
    (Necklace.allKStepMultisets w k).toFinset.card = 3 := by
  have hn_ge := ternary_length_ge_three w htern
  -- Extract the AS data
  obtain ⟨k₀, r, seq, hk₀_lt, hcop, hseq, hclose⟩ := has
  -- Find l with l * k₀ ≡ k (mod n)
  obtain ⟨l₀, hl₀_pos, hl₀_lt, hl₀_inv⟩ := exists_modular_inverse k₀ hcop (by omega)
  set l := l₀ * k % n
  have hl_lt : l < n := Nat.mod_lt _ (by omega)
  -- l * k₀ ≡ k (mod n)
  have hlk : l * k₀ % n = k := by
    have : l₀ * k₀ % n = 1 := hl₀_inv
    have : l * k₀ % n = l₀ * k % n * k₀ % n := rfl
    rw [this, Nat.mul_mod, Nat.mod_mod_of_dvd, ← Nat.mul_mod,
        show l₀ * k * k₀ = l₀ * k₀ * k from by ring, Nat.mul_mod, hl₀_inv,
        one_mul, Nat.mod_mod_of_dvd, Nat.mod_eq_of_lt hk']
    all_goals exact dvd_refl _
  -- l > 0 (since k > 0)
  have hl_pos : 0 < l := by
    by_contra h; push_neg at h; interval_cases l
    simp at hlk; omega
  -- Helper: given odd l' ∈ [1, n-2] with l' * k₀ % n = k',
  -- conclude (allKStepMultisets w k').toFinset.card = 3
  have odd_case : ∀ l' k', 0 < l' → l' ≤ n - 2 → l' % 2 = 1 →
      l' * k₀ % n = k' → 0 < k' → k' < n →
      (Necklace.allKStepMultisets w k').toFinset.card = 3 := by
    intro l' k' hl'_pos hl'_le hl'_odd hl'k hk'_pos hk'_lt
    -- (l'*k₀)-step vectors take 3 values
    have h3 := as_odd_lk_three_distinct w htern k₀ r seq l' hcop hodd
      hl'_pos hl'_le hl'_odd hseq hclose
    -- Transfer to k'-step vectors via mod-n reduction
    rw [← distinctKStepVectors_card_eq]
    unfold distinctKStepVectors
    rw [← hl'k, ← kStepVectors_card_mod_n, h3]
  by_cases hl_odd : l % 2 = 1
  · -- l is odd ⇒ l ≤ n - 2 (since l < n and n - 1 is even)
    exact odd_case l k hl_pos (by omega) hl_odd hlk hk hk'
  · -- l is even ⇒ n - l is odd, (n-l)*k₀ ≡ n-k (mod n)
    have hnl_odd : (n - l) % 2 = 1 := by omega
    have hnl_pos : 0 < n - l := by omega
    have hnl_le : n - l ≤ n - 2 := by omega  -- l ≥ 2 since l even, l > 0
    have hnk_pos : 0 < n - k := by omega
    have hnk_lt : n - k < n := by omega
    have hnlk : (n - l) * k₀ % n = n - k := by
      -- (n-l)*k₀ + l*k₀ = n*k₀, so (n-l)*k₀ ≡ -l*k₀ ≡ -k ≡ n-k (mod n)
      have hsum : (n - l) * k₀ + l * k₀ = n * k₀ := by
        rw [← add_mul, Nat.sub_add_cancel (le_of_lt hl_lt)]
      have hmod : ((n - l) * k₀ % n + l * k₀ % n) % n = 0 := by
        rw [← Nat.add_mod, hsum, Nat.mul_mod_right]
      rw [hlk] at hmod
      -- hmod: ((n-l)*k₀ % n + k) % n = 0
      -- So (n-l)*k₀ % n + k ∈ {0, n, 2n, ...}. Since both are < n, sum < 2n.
      -- Sum ≥ 1 (since k ≥ 1), so sum = n. Thus (n-l)*k₀ % n = n - k.
      have hlt : (n - l) * k₀ % n < n := Nat.mod_lt _ (by omega)
      suffices h : (n - l) * k₀ % n + k = n by omega
      obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hmod
      -- q = 1: sum > 0 forces q ≥ 1, and sum < 2n forces q ≤ 1
      have : q = 1 := by
        have hq_pos : 0 < q := by
          rcases Nat.eq_zero_or_pos q with rfl | h
          · simp at hq; omega
          · exact h
        by_contra hne; have hq_ge : q ≥ 2 := by omega
        nlinarith
      subst this; linarith
    -- Apply odd case for n-k
    have h3 := odd_case (n - l) (n - k) hnl_pos hnl_le hnl_odd hnlk hnk_pos hnk_lt
    -- Use equave complement to transfer from (n-k)-step to k-step
    rw [kStepMultisets_card_eq_complement w k hk hk']; exact h3

/-- Odd AS scales are SV3. -/
theorem as_odd_isSV3 (w : TernaryNecklace n)
    (hprim : Necklace.isPrimitive w) (htern : isTernary w)
    (has : hasAS w) (hodd : n % 2 = 1) :
    isSV3 w :=
  ⟨htern, fun k hk hkn =>
    as_odd_kStep_three_values w hprim htern has hodd k hk hkn⟩

/-! ### Pair identification gives MOS -/

/-- Shifting the k-step window by one physical position changes each component
    by at most 1.  That is, `|kStepVector(w, i+1, k)(a) - kStepVector(w, i, k)(a)| ≤ 1`. -/
private lemma kStepVector_component_scoot (w : TernaryNecklace n)
    (i k : ℕ) (a : StepSize) :
    |Necklace.kStepVector w (i + 1) k a - Necklace.kStepVector w i k a| ≤ 1 := by
  -- Window shift: kStepVector(i+1, k) = kStepVector(i, k) - [w(i)] + [w(i+k)]
  by_cases hk : k = 0
  · subst hk; simp [Necklace.kStepVector, Necklace.slice, ZVector.ofList]
  have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
  have hsplit_old := kStepVector_add w i 1 (k - 1) a
  have hsplit_new := kStepVector_add w (i + 1) (k - 1) 1 a
  rw [show 1 + (k - 1) = k from by omega] at hsplit_old
  rw [show k - 1 + 1 = k from by omega] at hsplit_new
  rw [show i + 1 + (k - 1) = i + k from by omega] at hsplit_new
  -- The shared middle part cancels
  have hdiff : Necklace.kStepVector w (i + 1) k a - Necklace.kStepVector w i k a =
      Necklace.kStepVector w (i + k) 1 a - Necklace.kStepVector w i 1 a := by linarith
  rw [hdiff, kStepVector_singleton, kStepVector_singleton, abs_le]
  -- The difference of two indicators is in {-1, 0, 1}
  constructor <;> split_ifs <;> omega

/-- identifyPair is additive on ZVectors. -/
private lemma ZVector_identifyPair_add (u v : ZVector StepSize) (x y : StepSize) :
    ZVector.identifyPair (u + v) x y = ZVector.identifyPair u x y + ZVector.identifyPair v x y := by
  funext a
  by_cases hax : a = x
  · simp [ZVector.identifyPair, hax]
  · by_cases hay : a = y
    · simp [ZVector.identifyPair, hay]; split_ifs <;> ring
    · simp [ZVector.identifyPair, hax, hay]

/-- The k-step vector of a pair-identified necklace equals the pair-identified
    k-step vector of the original necklace. -/
lemma identifyPair_kStepVector (w : TernaryNecklace n)
    (x y : StepSize) (hxy : x ≠ y) (i k : ℕ) :
    Necklace.kStepVector (TernaryNecklace.identifyPair w x y) i k =
    ZVector.identifyPair (Necklace.kStepVector w i k) x y := by
  induction k generalizing i with
  | zero =>
    funext a
    simp [Necklace.kStepVector, Necklace.slice, ZVector.ofList, ZVector.identifyPair]
  | succ k ih =>
    -- Lift kStepVector_add to function level
    have h_add_ip : Necklace.kStepVector (TernaryNecklace.identifyPair w x y) i (k + 1) =
        Necklace.kStepVector (TernaryNecklace.identifyPair w x y) i k +
        Necklace.kStepVector (TernaryNecklace.identifyPair w x y) (i + k) 1 := by
      funext b; exact kStepVector_add _ i k 1 b
    have h_add_w : Necklace.kStepVector w i (k + 1) =
        Necklace.kStepVector w i k + Necklace.kStepVector w (i + k) 1 := by
      funext b; exact kStepVector_add _ i k 1 b
    -- Single-step commutation
    have h_one : Necklace.kStepVector (TernaryNecklace.identifyPair w x y) (i + k) 1 =
        ZVector.identifyPair (Necklace.kStepVector w (i + k) 1) x y := by
      funext a
      simp only [kStepVector_singleton, ZVector.identifyPair, TernaryNecklace.identifyPair]
      by_cases hax : a = x
      · subst hax; split_ifs <;> simp_all
      · by_cases hay : a = y
        · subst hay; split_ifs <;> simp_all
        · split_ifs <;> simp_all
    -- Combine using additivity
    rw [h_add_ip, ih i, h_one, h_add_w, ZVector_identifyPair_add]

/-- Three integers with all pairwise absolute differences ≤ 1 have at most 2 distinct values:
    at least one pair must be equal. -/
private lemma three_close_values (a b c : ℤ)
    (hab : |a - b| ≤ 1) (hac : |a - c| ≤ 1) (hbc : |b - c| ≤ 1) :
    a = b ∨ a = c ∨ b = c := by
  rw [abs_le] at hab hac hbc; omega

/-- k-step vector decomposes into a sum of singleton vectors. -/
lemma kStepVector_as_singleton_sum (w : TernaryNecklace n)
    (j m : ℕ) (a : StepSize) :
    ∑ i ∈ Finset.range m, Necklace.kStepVector w (j + i) 1 a =
    Necklace.kStepVector w j m a := by
  induction m with
  | zero => simp [Necklace.kStepVector, Necklace.slice, ZVector.ofList]
  | succ m ih => rw [Finset.sum_range_succ, ih]; exact (kStepVector_add w j m 1 a).symm

/-- Double-counting sum identity: the sum of k-step z-counts across all n starting
    positions equals k times the total letter count.  Each of the n positions
    contributes its letter to exactly k windows. -/
lemma kStepVector_lettercount_sum (w : TernaryNecklace n) (k : ℕ) (a : StepSize) :
    ∑ i ∈ Finset.range n, Necklace.kStepVector w i k a =
    ↑k * ↑(Necklace.count w a) := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero, zero_mul]
    apply Finset.sum_eq_zero; intro i _
    simp [Necklace.kStepVector, Necklace.slice, ZVector.ofList]
  | succ k ih =>
    simp_rw [fun i => kStepVector_add w i k 1 a]
    rw [Finset.sum_add_distrib, ih]
    -- The shifted singleton sum equals count
    suffices h : ∑ i ∈ Finset.range n, Necklace.kStepVector w (i + k) 1 a =
        ↑(Necklace.count w a) by
      rw [h]; push_cast; ring
    have hcomm : ∀ i ∈ Finset.range n, Necklace.kStepVector w (i + k) 1 a =
        Necklace.kStepVector w (k + i) 1 a := by
      intros; congr 1; omega
    rw [Finset.sum_congr rfl hcomm, kStepVector_as_singleton_sum, kStepVector_full_cycle]

/-- Coprime reindexing for stacking sums:
    ∑ j=0..n-1, f(r + j*k) = ∑ i=0..n-1, f(i) when gcd(k,n) = 1. -/
lemma coprime_stacking_sum (n : ℕ) [NeZero n] (f : ℕ → ℤ)
    (hf_mod : ∀ i, f (i % n) = f i)
    (k r : ℕ) (hcop : Nat.Coprime k n) (hn_ge : n ≥ 2) :
    ∑ j ∈ Finset.range n, f (r + j * k) =
    ∑ i ∈ Finset.range n, f i := by
  have hn_pos : 0 < n := by omega
  apply Finset.sum_nbij (fun j => (r + j * k) % n)
  · intro j _; exact Finset.mem_range.mpr (Nat.mod_lt _ hn_pos)
  · intro j₁ hj₁ j₂ hj₂ h_eq
    simp only [Finset.mem_coe, Finset.mem_range] at hj₁ hj₂
    have hinj : Function.Injective (ZMod.val : ZMod n → ℕ) := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩; exact Fin.val_injective
    have h1 : ((r + j₁ * k : ℕ) : ZMod n) = ((r + j₂ * k : ℕ) : ZMod n) := by
      apply hinj; simp only [ZMod.val_natCast]; exact h_eq
    have h2 : (↑k : ZMod n) * (↑j₁ - ↑j₂) = 0 := by push_cast at h1 ⊢; linear_combination h1
    have hunit := coprime_isUnit_zmod k hcop hn_ge
    have h3 : (↑j₁ : ZMod n) = ↑j₂ := by
      by_contra h; exact absurd (hunit.mul_left_cancel (h2.trans (mul_zero _).symm))
        (sub_ne_zero.mpr h)
    have h4 := congr_arg ZMod.val h3
    rwa [ZMod.val_natCast, ZMod.val_natCast,
        Nat.mod_eq_of_lt hj₁, Nat.mod_eq_of_lt hj₂] at h4
  · intro i hi
    have hi_lt := Finset.mem_range.mp (Finset.mem_coe.mp hi)
    obtain ⟨j, hj⟩ := coprime_affine_surj k r hcop (by omega) (↑i : ZMod n)
    refine ⟨j.val, Finset.mem_coe.mpr (Finset.mem_range.mpr (ZMod.val_lt j)), ?_⟩
    have h1 : (↑(r + j.val * k) : ZMod n) = (↑i : ZMod n) := by
      rw [Nat.cast_add, Nat.cast_mul, natCast_zmod_val]; exact hj.symm
    have h2 := congr_arg ZMod.val h1
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hi_lt] at h2
  · intro j _; exact (hf_mod (r + j * k)).symm

/-- Coprime reindexing applied to kStepVector letter sums:
    ∑ j=0..n-1, kStepVector(r+j*k, k)(a) = k * count(w, a). -/
lemma kStepVector_stacking_sum (w : TernaryNecklace n)
    (k r : ℕ) (hcop : Nat.Coprime k n) (hn_ge : n ≥ 2) (a : StepSize) :
    ∑ j ∈ Finset.range n, Necklace.kStepVector w (r + j * k) k a =
    ↑k * ↑(Necklace.count w a) := by
  rw [← kStepVector_lettercount_sum w k a]
  exact coprime_stacking_sum n (fun i => Necklace.kStepVector w i k a)
    (fun i => congr_fun (kStepVector_mod_n w i k) a) k r hcop hn_ge

/-- Sum of alternating values over an even-length range. -/
lemma alternating_sum (d : ℕ) (a b : ℤ) :
    ∑ j ∈ Finset.range (2 * d), (if j % 2 = 0 then a else b) = ↑d * a + ↑d * b := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [show 2 * (d + 1) = 2 * d + 1 + 1 from by ring,
        Finset.sum_range_succ, Finset.sum_range_succ, ih,
        if_neg (show ¬((2 * d + 1) % 2 = 0) from by omega),
        if_pos (show (2 * d) % 2 = 0 from by omega)]
    push_cast; ring

/-- The two alternating k₀-step types in an AS scale have z-components differing
    by at most 1, where z is the step size with the distinct count.

    **Proof sketch**: If |seq(0)(z) - seq(1)(z)| ≥ 2, the discrete IVT on the
    physical cycle forces close(z) to be the unique intermediate value.
    If the gap is ≥ 3, a second application of IVT yields a 4th value (contradiction
    with only 3 distinct k-step vectors).  So the gap is exactly 2 and
    close(z) = midpoint.  The sum identity then gives n | count(z), but
    0 < count(z) < n: contradiction. -/
private lemma as_odd_seq_diff_le_one (w : TernaryNecklace n)
    (hprim : Necklace.isPrimitive w) (htern : isTernary w)
    (has : hasAS w) (hodd : n % 2 = 1)
    (k r : ℕ) (seq : Fin 2 → ZVector StepSize)
    (hcop : Nat.Coprime k n)
    (hseq : ∀ i : Fin (n - 1),
      Necklace.kStepVector w (r + i.val * k) k =
        seq ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩)
    (hclose : ∀ j : Fin 2,
      Necklace.kStepVector w (r + (n - 1) * k) k ≠ seq j)
    (z : StepSize) :
    |seq 0 z - seq 1 z| ≤ 1 := by
  by_contra h_abs
  push_neg at h_abs  -- h_abs : 1 < |seq 0 z - seq 1 z|
  have hn3 := ternary_length_ge_three w htern
  have hk_pos : 0 < k := by
    by_contra h; push_neg at h; interval_cases k; simp [Nat.Coprime] at hcop; omega
  set s₀ := seq 0 z
  set s₁ := seq 1 z
  set close_z := Necklace.kStepVector w (r + (n - 1) * k) k z
  -- Values of the k-step z-component at stacking positions
  have hf0 : Necklace.kStepVector w r k z = s₀ := by
    have := hseq ⟨0, by omega⟩; simp at this; exact congr_fun this z
  have hf1 : Necklace.kStepVector w (r + k) k z = s₁ := by
    have := hseq ⟨1, by omega⟩; simp at this; exact congr_fun this z
  -- All k-step z-values are in {s₀, s₁, close_z} (via coprime bijection)
  have hvals : ∀ p : ℕ, Necklace.kStepVector w p k z = s₀ ∨
      Necklace.kStepVector w p k z = s₁ ∨
      Necklace.kStepVector w p k z = close_z := by
    intro p
    obtain ⟨j, hj⟩ := coprime_affine_surj k r hcop (by omega) (↑(p % n) : ZMod n)
    -- p % n = (r + j.val * k) % n
    have hp_mod : p % n = (r + j.val * k) % n := by
      have h1 : (↑(p % n) : ZMod n) = (↑(r + j.val * k) : ZMod n) := by
        rw [Nat.cast_add, Nat.cast_mul, natCast_zmod_val]; exact hj
      have h2 := congr_arg ZMod.val h1
      rwa [ZMod.val_natCast, ZMod.val_natCast,
           Nat.mod_eq_of_lt (Nat.mod_lt p (by omega))] at h2
    -- Reduce kStepVector w p k to kStepVector w (r + j.val * k) k
    have hkv : Necklace.kStepVector w p k = Necklace.kStepVector w (r + j.val * k) k := by
      rw [← kStepVector_mod_n w p k, hp_mod, kStepVector_mod_n]
    rw [congr_fun hkv z]
    -- Classify by j.val
    by_cases hj_lt : j.val < n - 1
    · -- Regular position: use hseq
      have hsv := congr_fun (hseq ⟨j.val, by omega⟩) z
      simp only [] at hsv; rw [hsv]
      rcases Nat.mod_two_eq_zero_or_one j.val with h | h
      · left; congr 1; exact Fin.ext (by simp [h])
      · right; left; congr 1; exact Fin.ext (by simp [h])
    · -- Closing position: j.val = n - 1
      right; right
      have hj_eq : j.val = n - 1 := by have := ZMod.val_lt j; omega
      rw [hj_eq]
  -- Physical walk f(i) = kStepVector(w, r+i, k)(z)
  set f : ℕ → ℤ := fun i => Necklace.kStepVector w (r + i) k z
  have hf_step : ∀ s, s < k → |f (s + 1) - f s| ≤ 1 := by
    intro s _; show |Necklace.kStepVector w (r + s + 1) k z -
        Necklace.kStepVector w (r + s) k z| ≤ 1
    rw [show r + s + 1 = r + s + 1 from rfl]
    exact kStepVector_component_scoot w (r + s) k z
  have hf0' : f 0 = s₀ := by simp [f, hf0]
  have hfk : f k = s₁ := by show Necklace.kStepVector w (r + k) k z = s₁; exact hf1
  -- |s₀ - s₁| > 1, apply discrete_ivt (from MOS.lean)
  have hdiff : f 0 - f k > 1 ∨ f k - f 0 > 1 := by
    rw [hf0', hfk]; rcases lt_abs.mp h_abs with h | h <;> omega
  obtain ⟨s, hs_lt, hs_lo, hs_hi⟩ := discrete_ivt f k hk_pos hf_step hdiff
  -- f(s) is strictly between min(s₀, s₁) and max(s₀, s₁)
  have hfs_val := hvals (r + s)
  -- f(s) ∈ {s₀, s₁, close_z} but f(s) ≠ s₀ and f(s) ≠ s₁, so f(s) = close_z
  have hfs_ne_s0 : f s ≠ s₀ := by intro h; rw [hf0', hfk] at hs_lo hs_hi; omega
  have hfs_ne_s1 : f s ≠ s₁ := by intro h; rw [hf0', hfk] at hs_lo hs_hi; omega
  have hfs_eq : f s = close_z := by
    rcases hfs_val with h | h | h
    · exact absurd h hfs_ne_s0
    · exact absurd h hfs_ne_s1
    · exact h
  -- close_z is strictly between s₀ and s₁
  rw [hfs_eq, hf0', hfk] at hs_lo hs_hi
  -- If |s₀ - s₁| ≥ 3: second IVT application gives contradiction
  -- Either close_z - min ≥ 2 or max - close_z ≥ 2
  have h_gap_bound : close_z - min s₀ s₁ ≥ 1 ∧ max s₀ s₁ - close_z ≥ 1 := by
    constructor <;> omega
  -- Total gap: (close_z - min) + (max - close_z) = max - min = |s₀ - s₁| ≥ 2
  -- We show |s₀ - s₁| = 2 by contradiction: if ≥ 3, find a 4th value
  by_cases h_eq2 : |s₀ - s₁| = 2
  · -- |s₀ - s₁| = 2: close_z is the unique midpoint
    -- s₀ + s₁ = 2 * close_z
    have h_mid : s₀ + s₁ = 2 * close_z := by
      simp only [min_def, max_def] at hs_lo hs_hi
      rw [abs_eq (by omega : (0:ℤ) ≤ 2)] at h_eq2
      rcases h_eq2 with h | h <;> split_ifs at hs_lo hs_hi <;> omega
    -- Sum identity: ∑ kStepVector(w, r+j*k, k)(z) = k * count(z)
    -- LHS = (n-1)/2 * s₀ + (n-1)/2 * s₁ + close_z = n * close_z
    -- So n * close_z = k * count(z)
    have hcount_z := count_pos_of_isTernary w htern z
    have hcount_lt : Necklace.count w z < n := by
      have := count_total w
      have := count_pos_of_isTernary w htern StepSize.L
      have := count_pos_of_isTernary w htern StepSize.m
      have := count_pos_of_isTernary w htern StepSize.s
      cases z <;> omega
    -- Stacking sum = global sum (via coprime bijection)
    have hsum_eq : ∑ j ∈ Finset.range n, Necklace.kStepVector w (r + j * k) k z =
        ↑k * ↑(Necklace.count w z) := by
      rw [← kStepVector_lettercount_sum w k z]
      -- Coprime bijection reindexing: j ↦ (r + j * k) % n is a bijection on range n
      have hval_inj : Function.Injective (ZMod.val : ZMod n → ℕ) := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        exact Fin.val_injective
      have hk_unit := coprime_isUnit_zmod k hcop (by omega : n ≥ 2)
      apply Finset.sum_nbij (fun j => (r + j * k) % n)
      · -- Maps into range n
        intro j _; exact Finset.mem_range.mpr (Nat.mod_lt _ (by omega))
      · -- Injective on range n
        intro j₁ hj₁ j₂ hj₂ h_eq
        have hj₁_lt := Finset.mem_range.mp (Finset.mem_coe.mp hj₁)
        have hj₂_lt := Finset.mem_range.mp (Finset.mem_coe.mp hj₂)
        have h_zmod : (↑(r + j₁ * k) : ZMod n) = (↑(r + j₂ * k) : ZMod n) := by
          apply hval_inj; simp only [ZMod.val_natCast]; exact h_eq
        push_cast at h_zmod
        have h2 : (↑j₁ : ZMod n) * ↑k = (↑j₂ : ZMod n) * ↑k := add_left_cancel h_zmod
        have h2' : (↑k : ZMod n) * ↑j₁ = (↑k : ZMod n) * ↑j₂ := by
          rw [mul_comm, h2, mul_comm]
        have h3 := hk_unit.mul_left_cancel h2'
        have h4 := congr_arg ZMod.val h3
        rw [ZMod.val_natCast, ZMod.val_natCast,
            Nat.mod_eq_of_lt hj₁_lt, Nat.mod_eq_of_lt hj₂_lt] at h4
        exact h4
      · -- Surjective onto range n
        intro i hi
        have hi_lt := Finset.mem_range.mp (Finset.mem_coe.mp hi)
        obtain ⟨j, hj⟩ := coprime_affine_surj k r hcop (by omega) (↑i : ZMod n)
        refine ⟨j.val, Finset.mem_coe.mpr (Finset.mem_range.mpr (ZMod.val_lt j)), ?_⟩
        have h1 : (↑(r + j.val * k) : ZMod n) = (↑i : ZMod n) := by
          rw [Nat.cast_add, Nat.cast_mul, natCast_zmod_val]; exact hj.symm
        have h2 := congr_arg ZMod.val h1
        rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hi_lt] at h2
      · -- Values match: f j = g ((r + j * k) % n)
        intro j _
        exact (congr_fun (kStepVector_mod_n w (r + j * k) k).symm z)
    -- Express stacking sum using AS pattern
    have hstacking : ∑ j ∈ Finset.range n, Necklace.kStepVector w (r + j * k) k z =
        ↑((n - 1) / 2) * s₀ + ↑((n - 1) / 2) * s₁ + close_z := by
      -- Split off the closing term (j = n-1)
      have hsplit := Finset.sum_range_succ
          (fun j => Necklace.kStepVector w (r + j * k) k z) (n - 1)
      rw [show n - 1 + 1 = n from by omega] at hsplit; rw [hsplit]
      suffices h : ∑ j ∈ Finset.range (n - 1), Necklace.kStepVector w (r + j * k) k z =
          ↑((n - 1) / 2) * s₀ + ↑((n - 1) / 2) * s₁ by linarith
      -- Each term in range (n-1) alternates between s₀ and s₁
      have hterms : ∀ j ∈ Finset.range (n - 1),
          Necklace.kStepVector w (r + j * k) k z = if j % 2 = 0 then s₀ else s₁ := by
        intro j hj
        have hj_lt := Finset.mem_range.mp hj
        have hsv := congr_fun (hseq ⟨j, by omega⟩) z
        simp only [] at hsv; rw [hsv]
        split_ifs with h
        · show seq ⟨j % 2, by omega⟩ z = seq 0 z
          exact congr_fun (congr_arg seq (Fin.ext h)) z
        · show seq ⟨j % 2, by omega⟩ z = seq 1 z
          exact congr_fun (congr_arg seq (Fin.ext (Nat.mod_two_ne_zero.mp h))) z
      rw [Finset.sum_congr rfl hterms]
      nth_rw 1 [show n - 1 = 2 * ((n - 1) / 2) from by omega]
      exact alternating_sum _ s₀ s₁
    -- Combine: n * close_z = k * count(z)
    have h_n_close : ↑n * close_z = ↑k * ↑(Necklace.count w z) := by
      have h_eq := hstacking; rw [hsum_eq] at h_eq
      have h_half : (↑((n - 1) / 2) : ℤ) * 2 = ↑n - 1 := by
        have : (n - 1) % 2 = 0 := by omega
        push_cast; omega
      -- ((n-1)/2) * (s₀ + s₁) = ((n-1)/2) * 2 * close_z = (n-1) * close_z
      have key : (↑((n - 1) / 2) : ℤ) * s₀ + ↑((n - 1) / 2) * s₁ =
          (↑n - 1) * close_z := by
        rw [← mul_add, h_mid, ← mul_assoc, h_half]
      linarith
    -- n | count(z) via Nat-level coprimality
    have hclose_nn : close_z ≥ 0 := by
      simp only [close_z]; unfold Necklace.kStepVector ZVector.ofList Necklace.slice
      positivity
    have h_nat : n * close_z.toNat = k * Necklace.count w z := by
      have hcast : (↑close_z.toNat : ℤ) = close_z := Int.toNat_of_nonneg hclose_nn
      exact_mod_cast (show (↑(n * close_z.toNat) : ℤ) = ↑(k * Necklace.count w z) from by
        push_cast; rw [hcast]; exact h_n_close)
    have h_dvd : n ∣ Necklace.count w z :=
      hcop.symm.dvd_of_dvd_mul_left ⟨close_z.toNat, h_nat.symm⟩
    exact absurd (Nat.le_of_dvd hcount_z h_dvd) (by omega)
  · -- |s₀ - s₁| ≥ 3: second IVT gives 4th value
    -- Establish close_z between s₀ and s₁ (without min/max)
    have hbnd : s₀ < close_z ∧ close_z < s₁ ∨ s₁ < close_z ∧ close_z < s₀ := by
      simp only [min_def, max_def] at hs_lo hs_hi
      split_ifs at hs_lo hs_hi <;> [left; right] <;> exact ⟨hs_lo, hs_hi⟩
    have hs_pos : 0 < s := by
      rcases Nat.eq_zero_or_pos s with rfl | hp
      · exact absurd hf0' hfs_ne_s0
      · exact hp
    -- One of the two sub-walks has gap > 1
    by_cases hdl : f 0 - f s > 1 ∨ f s - f 0 > 1
    · -- IVT on [0, s]: f goes from s₀ to close_z
      obtain ⟨t, ht_lt, ht_lo, ht_hi⟩ :=
        discrete_ivt f s hs_pos (fun i hi => hf_step i (by omega)) hdl
      rw [hf0', hfs_eq] at ht_lo ht_hi
      -- f(t) ∈ {s₀, s₁, close_z} but strictly between s₀ and close_z: contradiction
      rcases hvals (r + t) with h | h | h <;> (change f t = _ at h) <;>
        (simp only [min_def, max_def] at ht_lo ht_hi;
         split_ifs at ht_lo ht_hi <;>
         rcases hbnd with ⟨_, _⟩ | ⟨_, _⟩ <;> linarith)
    · -- IVT on [s, k]: f goes from close_z to s₁
      push_neg at hdl
      -- Since |s₀ - close_z| ≤ 1 and |s₀ - s₁| ≥ 3, the other gap > 1
      have hdr : f s - f k > 1 ∨ f k - f s > 1 := by
        rw [hf0'] at hdl; rw [hfs_eq, hfk]
        rcases hbnd with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hab := abs_of_nonpos (show s₀ - s₁ ≤ 0 by linarith)
          rw [hab] at h_abs h_eq2; right; omega
        · have hab := abs_of_nonneg (show s₀ - s₁ ≥ 0 by linarith)
          rw [hab] at h_abs h_eq2; left; omega
      -- Shifted walk g(i) = f(s + i)
      set g : ℕ → ℤ := fun i => f (s + i) with hg_def
      have hg0 : g 0 = close_z := hfs_eq
      have hgend : g (k - s) = s₁ := by
        show f (s + (k - s)) = s₁; rw [show s + (k - s) = k from by omega]; exact hfk
      have hg_step : ∀ i, i < k - s → |g (i + 1) - g i| ≤ 1 := by
        intro i hi; show |f (s + i + 1) - f (s + i)| ≤ 1
        exact hf_step (s + i) (by omega)
      have hdiff_g : g 0 - g (k - s) > 1 ∨ g (k - s) - g 0 > 1 := by
        rw [hg0, hgend]; rw [hfs_eq, hfk] at hdr; exact hdr
      obtain ⟨t, ht_lt, ht_lo, ht_hi⟩ :=
        discrete_ivt g (k - s) (by omega) hg_step hdiff_g
      rw [hg0, hgend] at ht_lo ht_hi
      -- g(t) = f(s+t) ∈ {s₀, s₁, close_z} but strictly between close_z and s₁
      rcases hvals (r + (s + t)) with h | h | h <;> (change g t = _ at h) <;>
        (simp only [min_def, max_def] at ht_lo ht_hi;
         split_ifs at ht_lo ht_hi <;>
         rcases hbnd with ⟨_, _⟩ | ⟨_, _⟩ <;> linarith)

/-- The sum of all components of a k-step vector equals k. -/
lemma kStepVector_component_sum (w : TernaryNecklace n) (i k : ℕ) :
    ∑ a : StepSize, Necklace.kStepVector w i k a = ↑k := by
  induction k generalizing i with
  | zero =>
    apply Finset.sum_eq_zero; intro a _
    simp [Necklace.kStepVector, Necklace.slice, ZVector.ofList]
  | succ k ih =>
    have hsplit : ∀ a, Necklace.kStepVector w i (k + 1) a =
        Necklace.kStepVector w i k a + Necklace.kStepVector w (i + k) 1 a :=
      fun a => kStepVector_add w i k 1 a
    simp_rw [hsplit, Finset.sum_add_distrib, ih]
    suffices h : ∑ a : StepSize, Necklace.kStepVector w (i + k) 1 a = 1 by
      push_cast; linarith
    simp_rw [kStepVector_singleton]
    rw [Finset.sum_eq_single (w ((i + k : ℕ) : ZMod n))
      (fun a _ hne => if_neg (Ne.symm hne))
      (fun h => absurd (Finset.mem_univ _) h)]
    simp

/-! ### Pair identification gives MOS: diff structure and collapse -/

/-- Given three integers with absolute values ≤ 1 summing to zero and not all zero,
    there is a pair with opposite nonzero values (i.e., that sum to zero). -/
private lemma exists_cancelling_pair (dL dm ds : ℤ)
    (hL : |dL| ≤ 1) (hm : |dm| ≤ 1) (hs : |ds| ≤ 1)
    (hsum : dL + dm + ds = 0) (hne : dL ≠ 0 ∨ dm ≠ 0 ∨ ds ≠ 0) :
    (dL + dm = 0 ∧ dL ≠ 0) ∨ (dL + ds = 0 ∧ dL ≠ 0) ∨ (dm + ds = 0 ∧ dm ≠ 0) := by
  rw [abs_le] at hL hm hs; omega

/-- Expanding a sum over StepSize into three terms. -/
lemma stepSize_sum (f : StepSize → ℤ) :
    ∑ a : StepSize, f a = f .L + f .m + f .s := by
  simp only [Finset.univ, Fintype.elems]
  rw [Finset.sum_insert (show StepSize.L ∉ ({.m, .s} : Finset StepSize) from by decide),
      Finset.sum_insert (show StepSize.m ∉ ({.s} : Finset StepSize) from by decide),
      Finset.sum_singleton]
  ring

/-- The diff structure of an AS: the component-wise differences between the two
    alternating k₀-step types have a cancelling pair. That is, there exist distinct
    step sizes x, y such that `(seq 0)(x) + (seq 0)(y) = (seq 1)(x) + (seq 1)(y)`
    and `(seq 0)(x) ≠ (seq 1)(x)`, while the third step size z has equal values. -/
private lemma seq_diff_structure (w : TernaryNecklace n)
    (k r : ℕ) (seq : Fin 2 → ZVector StepSize)
    (hseq0 : Necklace.kStepVector w r k = seq ⟨0, by omega⟩)
    (hseq1 : Necklace.kStepVector w (r + k) k = seq ⟨1, by omega⟩)
    (hdiff : ∀ a : StepSize, |seq ⟨0, by omega⟩ a - seq ⟨1, by omega⟩ a| ≤ 1)
    (hne : seq ⟨0, by omega⟩ ≠ seq ⟨1, by omega⟩) :
    ∃ x y : StepSize, x ≠ y ∧
      seq ⟨0, by omega⟩ x - seq ⟨1, by omega⟩ x + (seq ⟨0, by omega⟩ y - seq ⟨1, by omega⟩ y) = 0 ∧
      seq ⟨0, by omega⟩ x ≠ seq ⟨1, by omega⟩ x ∧
      ∀ z : StepSize, z ≠ x → z ≠ y → seq ⟨0, by omega⟩ z = seq ⟨1, by omega⟩ z := by
  set s₀ := seq ⟨0, by omega⟩
  set s₁ := seq ⟨1, by omega⟩
  -- Sum of diffs = 0: both seq vectors sum to k
  have h0 := kStepVector_component_sum w r k
  have h1 := kStepVector_component_sum w (r + k) k
  rw [hseq0, stepSize_sum] at h0; rw [hseq1, stepSize_sum] at h1
  have hd_sum : s₀ .L - s₁ .L + (s₀ .m - s₁ .m) + (s₀ .s - s₁ .s) = 0 := by linarith
  -- Not all diffs zero
  have hd_ne : s₀ .L - s₁ .L ≠ 0 ∨ s₀ .m - s₁ .m ≠ 0 ∨ s₀ .s - s₁ .s ≠ 0 := by
    by_contra h; push_neg at h
    apply hne; funext a; cases a <;> linarith [h.1, h.2.1, h.2.2]
  -- Find cancelling pair
  rcases exists_cancelling_pair _ _ _ (hdiff .L) (hdiff .m) (hdiff .s) hd_sum hd_ne with
    ⟨hcancel, hne_xy⟩ | ⟨hcancel, hne_xy⟩ | ⟨hcancel, hne_xy⟩
  · refine ⟨.L, .m, by decide, hcancel, fun h => hne_xy (by linarith), ?_⟩
    intro z hz1 hz2; cases z
    · exact absurd rfl hz1
    · exact absurd rfl hz2
    · linarith
  · refine ⟨.L, .s, by decide, hcancel, fun h => hne_xy (by linarith), ?_⟩
    intro z hz1 hz2; cases z
    · exact absurd rfl hz1
    · linarith
    · exact absurd rfl hz2
  · refine ⟨.m, .s, by decide, hcancel, fun h => hne_xy (by linarith), ?_⟩
    intro z hz1 hz2; cases z
    · linarith
    · exact absurd rfl hz1
    · exact absurd rfl hz2

/-- Identifying the cancelling pair collapses the two alternating seq types. -/
private lemma identifyPair_collapses_seq
    (seq : Fin 2 → ZVector StepSize) (x y : StepSize) (_ : x ≠ y)
    (hcancel : seq ⟨0, by omega⟩ x - seq ⟨1, by omega⟩ x +
      (seq ⟨0, by omega⟩ y - seq ⟨1, by omega⟩ y) = 0)
    (hz : ∀ z : StepSize, z ≠ x → z ≠ y →
      seq ⟨0, by omega⟩ z = seq ⟨1, by omega⟩ z) :
    ZVector.identifyPair (seq ⟨0, by omega⟩) x y =
    ZVector.identifyPair (seq ⟨1, by omega⟩) x y := by
  funext a
  simp only [ZVector.identifyPair]
  by_cases hax : a = x
  · simp [hax]
  · by_cases hay : a = y
    · rw [if_neg hax, if_neg hax, if_pos hay, if_pos hay]; linarith
    · rw [if_neg hax, if_neg hay, if_neg hax, if_neg hay]; exact hz a hax hay

/-- Identifying the cancelling pair collapses v₁ and v₂ for any odd l.
    Since v₂ = v₁ − seq(0) + seq(1) (window shift), and identification
    makes seq(0) and seq(1) equal, it follows that identified v₁ = identified v₂. -/
private lemma identifyPair_collapses_v1_v2 (w : TernaryNecklace n)
    (k r : ℕ) (seq : Fin 2 → ZVector StepSize) (l : ℕ) (x y : StepSize)
    (_ : x ≠ y) (hl_pos : 0 < l) (hl_le : l ≤ n - 2) (hl_odd : l % 2 = 1)
    (hseq : ∀ i : Fin (n - 1),
      Necklace.kStepVector w (r + i.val * k) k =
        seq ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩)
    (hcancel : seq ⟨0, by omega⟩ x - seq ⟨1, by omega⟩ x +
      (seq ⟨0, by omega⟩ y - seq ⟨1, by omega⟩ y) = 0)
    (hz : ∀ z : StepSize, z ≠ x → z ≠ y →
      seq ⟨0, by omega⟩ z = seq ⟨1, by omega⟩ z) :
    ZVector.identifyPair (Necklace.kStepVector w r (l * k)) x y =
    ZVector.identifyPair (Necklace.kStepVector w (r + k) (l * k)) x y := by
  -- Window shift: v₂(a) = v₁(a) - seq(0)(a) + seq(l%2)(a) = v₁(a) - seq(0)(a) + seq(1)(a)
  set v₁ := Necklace.kStepVector w r (l * k)
  set v₂ := Necklace.kStepVector w (r + k) (l * k)
  have hrec := kStepVector_window_shift_fun w r k l hl_pos
  rw [show r + k = r + 1 * k from by ring] at hrec
  rw [show r + 1 * k = r + k from by ring] at hrec
  -- kStepVector at r = seq 0
  have hT0 : Necklace.kStepVector w r k = seq ⟨0, by omega⟩ := by
    simpa using hseq ⟨0, by omega⟩
  -- kStepVector at r + l*k = seq 1 (since l is odd)
  have hTl : Necklace.kStepVector w (r + l * k) k = seq ⟨1, by omega⟩ := by
    have h := hseq ⟨l, by omega⟩
    simp only [] at h; rw [h]; congr 1; ext; simp only []; exact hl_odd
  -- Pointwise: v₂(a) = v₁(a) - seq(0)(a) + seq(1)(a)
  have hshift : ∀ a, v₂ a = v₁ a - seq ⟨0, by omega⟩ a + seq ⟨1, by omega⟩ a := by
    intro a; have := congr_fun hrec a
    simp only [ZVector.sub_apply, ZVector.add_apply] at this
    rw [hT0, hTl] at this; linarith
  -- Now show identified vectors are equal pointwise
  funext a
  simp only [ZVector.identifyPair]
  by_cases hax : a = x
  · simp [hax]
  · by_cases hay : a = y
    · rw [if_neg hax, if_neg hax, if_pos hay, if_pos hay]
      rw [hshift x, hshift y]; linarith
    · rw [if_neg hax, if_neg hay, if_neg hax, if_neg hay]
      rw [hshift a]; linarith [hz a hax hay]

/-- After identifying the cancelling pair, the (l·k₀)-step vectors have ≤ 2 values
    for odd l, because the two alternating types collapse. -/
private lemma identified_lk_le_two (w : TernaryNecklace n)
    (k₀ r : ℕ) (seq : Fin 2 → ZVector StepSize) (l : ℕ) (x y : StepSize)
    (hxy : x ≠ y) (hodd : n % 2 = 1) (hcop : Nat.Coprime k₀ n)
    (hl_pos : 0 < l) (hl_le : l ≤ n - 2) (hl_odd : l % 2 = 1)
    (hseq : ∀ i : Fin (n - 1),
      Necklace.kStepVector w (r + i.val * k₀) k₀ =
        seq ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩)
    (hclose : ∀ j : Fin 2,
      Necklace.kStepVector w (r + (n - 1) * k₀) k₀ ≠ seq j)
    (hcancel : seq ⟨0, by omega⟩ x - seq ⟨1, by omega⟩ x +
      (seq ⟨0, by omega⟩ y - seq ⟨1, by omega⟩ y) = 0)
    (hz : ∀ z : StepSize, z ≠ x → z ≠ y →
      seq ⟨0, by omega⟩ z = seq ⟨1, by omega⟩ z) :
    (Necklace.allKStepVectors (TernaryNecklace.identifyPair w x y) (l * k₀)).toFinset.card ≤ 2 := by
  -- Classification: every position j gives v₁, v₂, or v₃
  have hclass : ∀ j : ZMod n,
      Necklace.kStepVector w (r + j.val * k₀) (l * k₀) =
        if j.val < n - l then
          if j.val % 2 = 0 then Necklace.kStepVector w r (l * k₀)
          else Necklace.kStepVector w (r + k₀) (l * k₀)
        else
          Necklace.kStepVector w (r + (n - l) * k₀) (l * k₀) :=
    fun j => alternating_lk_class w k₀ r seq l hodd hl_pos hl_le hl_odd hseq hclose
      j.val (ZMod.val_lt j)
  -- Coprime affine bijection g : ZMod n → ZMod n
  have hk_unit := coprime_isUnit_zmod k₀ hcop (by omega : n ≥ 2)
  set g : ZMod n → ZMod n := fun j => (↑r : ZMod n) + j * (↑k₀ : ZMod n)
  have g_inj : Function.Injective g := fun j₁ j₂ h => by
    have h1 : j₁ * (↑k₀ : ZMod n) = j₂ * (↑k₀ : ZMod n) := add_left_cancel h
    rw [mul_comm j₁, mul_comm j₂] at h1; exact hk_unit.mul_left_cancel h1
  have g_surj : Function.Surjective g := Finite.surjective_of_injective g_inj
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
  -- The collapse: identified v₁ = identified v₂
  have hcollapse := identifyPair_collapses_v1_v2 w k₀ r seq l x y hxy hl_pos hl_le hl_odd
    hseq hcancel hz
  -- Every identified vector is one of two values
  set iv₁ := ZVector.identifyPair (Necklace.kStepVector w r (l * k₀)) x y
  set iv₃ := ZVector.identifyPair (Necklace.kStepVector w (r + (n - l) * k₀) (l * k₀)) x y
  have hmem : ∀ v ∈ (Necklace.allKStepVectors
      (TernaryNecklace.identifyPair w x y) (l * k₀)).toFinset,
      v = iv₁ ∨ v = iv₃ := by
    intro v hv
    rw [List.mem_toFinset] at hv
    unfold Necklace.allKStepVectors at hv
    simp only [List.mem_map, List.mem_range] at hv
    obtain ⟨i, hi, rfl⟩ := hv
    rw [identifyPair_kStepVector w x y hxy i (l * k₀)]
    -- Find j with (r + j*k₀) % n = i via coprime bijection
    obtain ⟨j, hgj⟩ := g_surj (i : ZMod n)
    have hi_eq : (g j).val = i := by
      rw [hgj, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
    have hkv_eq : Necklace.kStepVector w i (l * k₀) =
        Necklace.kStepVector w (r + j.val * k₀) (l * k₀) := by
      rw [← hi_eq]; exact hg_mod j
    rw [hkv_eq, hclass j]
    by_cases hinl : j.val < n - l
    · rw [if_pos hinl]
      by_cases hpar : j.val % 2 = 0
      · left; rw [if_pos hpar]
      · left; rw [if_neg hpar]; exact hcollapse.symm
    · right; rw [if_neg hinl]
  -- Subset of a 2-element set ⇒ card ≤ 2
  have hsub : (Necklace.allKStepVectors
      (TernaryNecklace.identifyPair w x y) (l * k₀)).toFinset ⊆ {iv₁, iv₃} := by
    intro v hv; rw [Finset.mem_insert, Finset.mem_singleton]
    exact hmem v hv
  calc (Necklace.allKStepVectors _ (l * k₀)).toFinset.card
      ≤ ({iv₁, iv₃} : Finset _).card := Finset.card_le_card hsub
    _ ≤ 2 := by
        have := Finset.card_insert_le iv₁ ({iv₃} : Finset _)
        simp only [Finset.card_singleton] at this; linarith

/-- After identifying the cancelling pair, the k-step multisets have ≤ 2 values
    for all valid k. Mirrors `as_odd_kStep_three_values`. -/
private lemma identified_kStep_le_two (w : TernaryNecklace n)
    (_ : Necklace.isPrimitive w) (htern : isTernary w)
    (k₀ r : ℕ) (seq : Fin 2 → ZVector StepSize)
    (hcop : Nat.Coprime k₀ n) (hodd : n % 2 = 1)
    (hseq : ∀ i : Fin (n - 1),
      Necklace.kStepVector w (r + i.val * k₀) k₀ =
        seq ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩)
    (hclose : ∀ j : Fin 2,
      Necklace.kStepVector w (r + (n - 1) * k₀) k₀ ≠ seq j)
    (x y : StepSize) (hxy : x ≠ y)
    (hcancel : seq ⟨0, by omega⟩ x - seq ⟨1, by omega⟩ x +
      (seq ⟨0, by omega⟩ y - seq ⟨1, by omega⟩ y) = 0)
    (hz : ∀ z : StepSize, z ≠ x → z ≠ y →
      seq ⟨0, by omega⟩ z = seq ⟨1, by omega⟩ z) :
    ∀ k : ℕ, 0 < k → k < n →
      (Necklace.allKStepMultisets (TernaryNecklace.identifyPair w x y) k).toFinset.card ≤ 2 := by
  have hn_ge := ternary_length_ge_three w htern
  intro k hk hk'
  -- Find l with l * k₀ % n = k
  obtain ⟨l₀, hl₀_pos, hl₀_lt, hl₀_inv⟩ := exists_modular_inverse k₀ hcop (by omega)
  set l := l₀ * k % n
  have hl_lt : l < n := Nat.mod_lt _ (by omega)
  -- l * k₀ ≡ k (mod n)
  have hlk : l * k₀ % n = k := by
    have : l₀ * k₀ % n = 1 := hl₀_inv
    have : l * k₀ % n = l₀ * k % n * k₀ % n := rfl
    rw [this, Nat.mul_mod, Nat.mod_mod_of_dvd, ← Nat.mul_mod,
        show l₀ * k * k₀ = l₀ * k₀ * k from by ring, Nat.mul_mod, hl₀_inv,
        one_mul, Nat.mod_mod_of_dvd, Nat.mod_eq_of_lt hk']
    all_goals exact dvd_refl _
  -- l > 0 (since k > 0)
  have hl_pos : 0 < l := by
    by_contra h; push_neg at h
    have hl0 : l = 0 := by omega
    rw [hl0, zero_mul, Nat.zero_mod] at hlk; omega
  set w' := TernaryNecklace.identifyPair w x y
  -- Helper: given odd l' ∈ [1, n-2] with l' * k₀ % n = k',
  -- conclude identified k'-step multisets ≤ 2
  have odd_case : ∀ l' k', 0 < l' → l' ≤ n - 2 → l' % 2 = 1 →
      l' * k₀ % n = k' → 0 < k' → k' < n →
      (Necklace.allKStepMultisets w' k').toFinset.card ≤ 2 := by
    intro l' k' hl'_pos hl'_le hl'_odd hl'k hk'_pos hk'_lt
    -- identified (l'*k₀)-step vectors have ≤ 2 values
    have h2 := identified_lk_le_two w k₀ r seq l' x y hxy hodd hcop
      hl'_pos hl'_le hl'_odd hseq hclose hcancel hz
    -- Transfer to k'-step via mod-n reduction and ZVector↔multiset
    rw [← distinctKStepVectors_card_eq]
    unfold distinctKStepVectors
    rw [← hl'k, ← kStepVectors_card_mod_n]; exact h2
  by_cases hl_odd : l % 2 = 1
  · -- l is odd ⇒ l ≤ n - 2 (since l < n and n - 1 is even)
    exact odd_case l k hl_pos (by omega) hl_odd hlk hk hk'
  · -- l is even ⇒ n - l is odd, (n-l)*k₀ ≡ n-k (mod n)
    have hnl_odd : (n - l) % 2 = 1 := by omega
    have hnl_pos : 0 < n - l := by omega
    have hnl_le : n - l ≤ n - 2 := by omega
    have hnk_pos : 0 < n - k := by omega
    have hnk_lt : n - k < n := by omega
    have hnlk : (n - l) * k₀ % n = n - k := by
      have hsum : (n - l) * k₀ + l * k₀ = n * k₀ := by
        rw [← add_mul, Nat.sub_add_cancel (le_of_lt hl_lt)]
      have hmod : ((n - l) * k₀ % n + l * k₀ % n) % n = 0 := by
        rw [← Nat.add_mod, hsum, Nat.mul_mod_right]
      rw [hlk] at hmod
      have hlt : (n - l) * k₀ % n < n := Nat.mod_lt _ (by omega)
      suffices h : (n - l) * k₀ % n + k = n by omega
      obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hmod
      have : q = 1 := by
        have hq_pos : 0 < q := by
          rcases Nat.eq_zero_or_pos q with rfl | h
          · simp at hq; omega
          · exact h
        by_contra hne; have hq_ge : q ≥ 2 := by omega
        nlinarith
      subst this; linarith
    have h2 := odd_case (n - l) (n - k) hnl_pos hnl_le hnl_odd hnlk hnk_pos hnk_lt
    rw [kStepMultisets_card_eq_complement w' k hk hk']; exact h2

omit [NeZero n] in
/-- A ternary necklace with positive counts of each step size is ternary. -/
lemma isTernary_of_positive_counts {n : ℕ} [NeZero n] {w : TernaryNecklace n}
    {a b c : ℕ}
    (hcountL : Necklace.count w .L = a) (hcountm : Necklace.count w .m = b)
    (hcounts : Necklace.count w .s = c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : isTernary w := by
  have count_pos_exists : ∀ (st : StepSize), 0 < Necklace.count w st → ∃ i, w i = st := by
    intro st hst
    unfold Necklace.count at hst
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hst
    exact ⟨i, (Finset.mem_filter.mp hi).2⟩
  exact ⟨count_pos_exists .L (by omega), count_pos_exists .m (by omega),
         count_pos_exists .s (by omega)⟩

omit [NeZero n] in
/-- The identified necklace uses at least 2 distinct values. -/
lemma identified_uses_two_values (w : TernaryNecklace n)
    (htern : isTernary w) (x y : StepSize) (hxy : x ≠ y) :
    ∃ a b : StepSize, a ≠ b ∧
      (∃ i : ZMod n, (TernaryNecklace.identifyPair w x y) i = a) ∧
      (∃ i : ZMod n, (TernaryNecklace.identifyPair w x y) i = b) := by
  -- Find the third step size z ≠ x, z ≠ y
  have hz : ∃ z : StepSize, z ≠ x ∧ z ≠ y := by
    cases x <;> cases y <;> simp_all <;>
      first | exact ⟨.L, by decide, by decide⟩
             | exact ⟨.m, by decide, by decide⟩
             | exact ⟨.s, by decide, by decide⟩
  obtain ⟨z, hzx, hzy⟩ := hz
  -- y appears (from any original x position)
  obtain ⟨ix, hix⟩ := (isTernary_iff_forall w).mp htern x
  have hy_exists : ∃ i : ZMod n, (TernaryNecklace.identifyPair w x y) i = y :=
    ⟨ix, by simp [TernaryNecklace.identifyPair, hix]⟩
  -- z appears (from any original z position, unchanged since z ≠ x)
  obtain ⟨iz, hiz⟩ := (isTernary_iff_forall w).mp htern z
  have hwiz : w iz ≠ x := by rw [hiz]; exact hzx
  have hz_exists : ∃ i : ZMod n, (TernaryNecklace.identifyPair w x y) i = z :=
    ⟨iz, by show (if w iz = x then y else w iz) = z; rw [if_neg hwiz]; exact hiz⟩
  exact ⟨y, z, hzy.symm, hy_exists, hz_exists⟩

/-- Odd AS scales have a pair of step sizes whose identification yields a MOS. -/
private lemma as_odd_pair_identification_mos (w : TernaryNecklace n)
    (hprim : Necklace.isPrimitive w) (htern : isTernary w)
    (has : hasAS w) (hodd : n % 2 = 1) :
    ∃ x y : StepSize, x ≠ y ∧
      isPartialPairwiseMOS w x y := by
  have hn_ge := ternary_length_ge_three w htern
  -- Extract AS data
  have has' := has
  obtain ⟨k₀, r, seq, hk₀_lt, hcop, hseq, hclose⟩ := has
  -- Get seq 0 ≠ seq 1
  obtain ⟨l₀, hl₀_pos, hl₀_le, hl₀_odd, hl₀_mod⟩ :=
    exists_odd_quasi_inverse k₀ hodd hcop hn_ge
  have hne := alternating_seq_ne w htern k₀ r seq l₀ hcop hodd hl₀_pos hl₀_le hl₀_odd
    hl₀_mod hseq hclose
  -- Get diff ≤ 1
  have hdiff := as_odd_seq_diff_le_one w hprim htern has' hodd k₀ r seq hcop hseq hclose
  -- Get seq at positions 0 and 1
  have hseq0 : Necklace.kStepVector w r k₀ = seq ⟨0, by omega⟩ := by
    simpa using hseq ⟨0, by omega⟩
  have hseq1 : Necklace.kStepVector w (r + k₀) k₀ = seq ⟨1, by omega⟩ := by
    have h := hseq ⟨1, by omega⟩; simpa using h
  -- Extract the cancelling pair
  obtain ⟨x, y, hxy, hcancel, _, hz⟩ :=
    seq_diff_structure w k₀ r seq hseq0 hseq1 hdiff hne
  -- Combine
  refine ⟨x, y, hxy, ?_⟩
  show Necklace.hasMOSProperty (TernaryNecklace.identifyPair w x y)
  exact ⟨identified_uses_two_values w htern x y hxy,
    identified_kStep_le_two w hprim htern k₀ r seq hcop hodd hseq hclose x y hxy hcancel hz⟩

/-! ### From AS to odd-regular: helper lemmas -/

/-- Modular endgame: if l*k₀ ≡ ±1 and c*k₀ ≡ ±1 (mod n), with l + 2c = n,
    then n | 3. -/
private lemma mod_endgame_dvd_three (n l c k₀ : ℕ)
    (hn : n ≥ 3)
    (hsum : l + 2 * c = n)
    (hl_mod : l * k₀ % n = 1 ∨ l * k₀ % n = n - 1)
    (hc_mod : c * k₀ % n = 1 ∨ c * k₀ % n = n - 1) :
    n ∣ 3 := by
  -- Work in ℤ: derive (n : ℤ) | (ε₁ + 2*ε₂)
  set ε₁ := l * k₀ % n
  set ε₂ := c * k₀ % n
  have h_rem1 : (↑n : ℤ) ∣ (↑(l * k₀) - ↑ε₁) := by
    rw [← Nat.cast_sub (Nat.mod_le _ _)]
    show (↑n : ℤ) ∣ ↑(l * k₀ - l * k₀ % n)
    rw [Nat.sub_eq_of_eq_add (Nat.div_add_mod (l * k₀) n).symm, Nat.cast_mul]
    exact dvd_mul_right _ _
  have h_rem2 : (↑n : ℤ) ∣ (↑(c * k₀) - ↑ε₂) := by
    rw [← Nat.cast_sub (Nat.mod_le _ _)]
    show (↑n : ℤ) ∣ ↑(c * k₀ - c * k₀ % n)
    rw [Nat.sub_eq_of_eq_add (Nat.div_add_mod (c * k₀) n).symm, Nat.cast_mul]
    exact dvd_mul_right _ _
  -- n | (l*k₀ - ε₁ + 2*(c*k₀ - ε₂)) = n | (n*k₀ - (ε₁ + 2*ε₂))
  have h_comb := dvd_add h_rem1 (dvd_mul_of_dvd_right h_rem2 2)
  have h_simp : (↑(l * k₀) : ℤ) - ↑ε₁ + 2 * (↑(c * k₀) - ↑ε₂) =
      ↑n * ↑k₀ - (↑ε₁ + 2 * ↑ε₂) := by push_cast; nlinarith [hsum]
  rw [h_simp] at h_comb
  -- h_comb : n | (n*k₀ - (ε₁ + 2*ε₂)), and n | n*k₀, so n | (ε₁ + 2*ε₂)
  have hdvd : (↑n : ℤ) ∣ (↑ε₁ + 2 * ↑ε₂) := by
    have h_nk : (↑n : ℤ) ∣ (↑n * ↑k₀) := dvd_mul_right _ _
    have h := dvd_sub h_nk h_comb
    rwa [show (↑n : ℤ) * ↑k₀ - (↑n * ↑k₀ - (↑ε₁ + 2 * ↑ε₂)) =
        ↑ε₁ + 2 * ↑ε₂ from by ring] at h
  -- Case split on ε₁ ∈ {1, n-1} and ε₂ ∈ {1, n-1}
  rcases hl_mod with h₁ | h₁ <;> rcases hc_mod with h₂ | h₂ <;>
    simp only [h₁, h₂] at hdvd
  -- ε₁=1, ε₂=1: (n:ℤ) | (1+2) = 3 → n | 3 in ℕ
  · exact_mod_cast hdvd
  -- ε₁=1, ε₂=n-1: (n:ℤ) | (1 + 2*(n-1)) = (n:ℤ) | (2n-1)
  · exfalso
    simp only [Nat.cast_one] at hdvd
    have h_eq : (1 : ℤ) + 2 * ↑(n - 1) = 2 * ↑n - 1 := by omega
    rw [h_eq] at hdvd
    have h1 := dvd_sub (dvd_mul_left (↑n : ℤ) 2) hdvd
    rw [show (2 : ℤ) * ↑n - (2 * ↑n - 1) = 1 from by ring] at h1
    have : (↑n : ℤ) ≤ 1 := Int.le_of_dvd (by omega) h1
    omega
  -- ε₁=n-1, ε₂=1: (n:ℤ) | ((n-1)+2) = (n:ℤ) | (n+1)
  · exfalso
    simp only [Nat.cast_one] at hdvd
    have h_eq : (↑(n - 1) : ℤ) + 2 * (1 : ℤ) = ↑n + 1 := by push_cast; omega
    rw [h_eq] at hdvd
    have h1 := dvd_sub hdvd (dvd_refl (↑n : ℤ))
    rw [show (↑n : ℤ) + 1 - ↑n = 1 from by ring] at h1
    have : (↑n : ℤ) ≤ 1 := Int.le_of_dvd (by omega) h1
    omega
  -- ε₁=n-1, ε₂=n-1: (n:ℤ) | ((n-1)+2*(n-1)) = (n:ℤ) | (3n-3)
  · have h_eq : (↑(n - 1) : ℤ) + 2 * ↑(n - 1) = 3 * ↑n - 3 := by omega
    rw [h_eq] at hdvd
    have h1 := dvd_sub (dvd_mul_left (↑n : ℤ) 3) hdvd
    rw [show (3 : ℤ) * ↑n - (3 * ↑n - 3) = 3 from by ring] at h1
    exact_mod_cast h1

/-- In an odd AS with neutral letter z₀ (seq(0)(z₀) = seq(1)(z₀)),
    if count(z₀) = (n-l)/2 where l is the quasi-inverse, then n = 3.

    **Proof sketch**: By coprime reindexing and double-counting,
    k₀ * count(z₀) = (n-1)*v + c where v = seq(0)(z₀) and c = close(z₀).
    The scoot property forces |v - c| ≤ 1, and v = c gives n | count(z₀)
    (contradiction). So k₀ * count(z₀) ≡ ±1 (mod n).
    Combined with k₀ * l ≡ ±1 (mod n), we get n | (ε₁ + 2ε₂) with
    ε₁, ε₂ ∈ {1, n-1}, forcing n | 3, hence n = 3. -/
private lemma as_neutral_forces_n_eq_3 (w : TernaryNecklace n)
    (htern : isTernary w)
    (k₀ r : ℕ) (seq : Fin 2 → ZVector StepSize)
    (hcop : Nat.Coprime k₀ n) (hodd : n % 2 = 1)
    (hseq : ∀ i : Fin (n - 1),
      Necklace.kStepVector w (r + i.val * k₀) k₀ =
        seq ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩)
    (hclose : ∀ j : Fin 2,
      Necklace.kStepVector w (r + (n - 1) * k₀) k₀ ≠ seq j)
    (z₀ : StepSize)
    (hz₀ : seq ⟨0, by omega⟩ z₀ = seq ⟨1, by omega⟩ z₀)
    (l : ℕ) (_hl_pos : 0 < l) (hl_le : l ≤ n - 2) (hl_odd : l % 2 = 1)
    (hl_mod : l * k₀ % n = 1 ∨ l * k₀ % n = n - 1)
    (hcz₀ : Necklace.count w z₀ = (n - l) / 2) :
    n = 3 := by
  have hn_ge := ternary_length_ge_three w htern
  have hk_pos : 0 < k₀ := by
    by_contra h; push_neg at h; interval_cases k₀; simp [Nat.Coprime] at hcop; omega
  set v := seq ⟨0, by omega⟩ z₀
  set close_z := Necklace.kStepVector w (r + (n - 1) * k₀) k₀ z₀
  -- Step 1: Stacking sum = global sum via coprime reindexing
  have hsum_eq : ∑ j ∈ Finset.range n, Necklace.kStepVector w (r + j * k₀) k₀ z₀ =
      ↑k₀ * ↑(Necklace.count w z₀) := by
    rw [← kStepVector_lettercount_sum w k₀ z₀]
    have hval_inj : Function.Injective (ZMod.val : ZMod n → ℕ) := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      exact Fin.val_injective
    have hk_unit := coprime_isUnit_zmod k₀ hcop (by omega : n ≥ 2)
    apply Finset.sum_nbij (fun j => (r + j * k₀) % n)
    · intro j _; exact Finset.mem_range.mpr (Nat.mod_lt _ (by omega))
    · intro j₁ hj₁ j₂ hj₂ h_eq
      have hj₁_lt := Finset.mem_range.mp (Finset.mem_coe.mp hj₁)
      have hj₂_lt := Finset.mem_range.mp (Finset.mem_coe.mp hj₂)
      have h_zmod : (↑(r + j₁ * k₀) : ZMod n) = (↑(r + j₂ * k₀) : ZMod n) := by
        apply hval_inj; simp only [ZMod.val_natCast]; exact h_eq
      push_cast at h_zmod
      have h2 : (↑j₁ : ZMod n) * ↑k₀ = (↑j₂ : ZMod n) * ↑k₀ := add_left_cancel h_zmod
      have h2' : (↑k₀ : ZMod n) * ↑j₁ = (↑k₀ : ZMod n) * ↑j₂ := by
        rw [mul_comm, h2, mul_comm]
      have h3 := hk_unit.mul_left_cancel h2'
      have h4 := congr_arg ZMod.val h3
      rw [ZMod.val_natCast, ZMod.val_natCast,
          Nat.mod_eq_of_lt hj₁_lt, Nat.mod_eq_of_lt hj₂_lt] at h4
      exact h4
    · intro i hi
      have hi_lt := Finset.mem_range.mp (Finset.mem_coe.mp hi)
      obtain ⟨j, hj⟩ := coprime_affine_surj k₀ r hcop (by omega) (↑i : ZMod n)
      refine ⟨j.val, Finset.mem_coe.mpr (Finset.mem_range.mpr (ZMod.val_lt j)), ?_⟩
      have h1 : (↑(r + j.val * k₀) : ZMod n) = (↑i : ZMod n) := by
        rw [Nat.cast_add, Nat.cast_mul, natCast_zmod_val]; exact hj.symm
      have h2 := congr_arg ZMod.val h1
      rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hi_lt] at h2
    · intro j _
      exact (congr_fun (kStepVector_mod_n w (r + j * k₀) k₀).symm z₀)
  -- Step 2: Stacking sum = (n-1)*v + close_z (all regular terms are v)
  have hstacking : ∑ j ∈ Finset.range n, Necklace.kStepVector w (r + j * k₀) k₀ z₀ =
      ↑(n - 1) * v + close_z := by
    have hsplit := Finset.sum_range_succ
        (fun j => Necklace.kStepVector w (r + j * k₀) k₀ z₀) (n - 1)
    rw [show n - 1 + 1 = n from by omega] at hsplit; rw [hsplit]
    suffices h : ∑ j ∈ Finset.range (n - 1), Necklace.kStepVector w (r + j * k₀) k₀ z₀ =
        ↑(n - 1) * v by linarith
    have hterms : ∀ j ∈ Finset.range (n - 1),
        Necklace.kStepVector w (r + j * k₀) k₀ z₀ = v := by
      intro j hj
      have hj_lt := Finset.mem_range.mp hj
      have hsv := congr_fun (hseq ⟨j, by omega⟩) z₀
      simp only [] at hsv; rw [hsv]
      rcases Nat.mod_two_eq_zero_or_one j with h | h
      · exact congr_fun (congr_arg seq (Fin.ext h)) z₀
      · rw [show (⟨j % 2, _⟩ : Fin 2) = ⟨1, by omega⟩ from Fin.ext h]
        exact hz₀.symm
    rw [Finset.sum_congr rfl hterms, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
  -- Combine: (n-1)*v + close_z = k₀ * count(z₀)
  have hident : ↑(n - 1) * v + close_z = ↑k₀ * ↑(Necklace.count w z₀) := by
    linarith [hsum_eq, hstacking]
  -- Step 3: |v - close_z| ≤ 1 via scoot
  have h_scoot : |v - close_z| ≤ 1 := by
    have hraw := kStepVector_component_scoot w (r + (n - 1) * k₀) k₀ z₀
    -- Find stacking position j matching physical position r+(n-1)*k₀+1
    obtain ⟨j, hj⟩ := coprime_affine_surj k₀ r hcop (by omega)
        (↑(r + (n - 1) * k₀ + 1) : ZMod n)
    -- j.val ≠ n-1 (else consecutive positions have same residue mod n)
    have hj_ne : j.val ≠ n - 1 := by
      intro heq
      have h1 := hj
      rw [show (↑j : ZMod n) = (↑j.val : ZMod n) from (natCast_zmod_val j).symm,
          heq] at h1
      have h2 : (↑(r + (n - 1) * k₀) : ZMod n) = (↑r : ZMod n) + ↑(n - 1) * ↑k₀ := by
        push_cast; ring
      rw [← h2] at h1
      have h3 := congr_arg ZMod.val h1
      rw [ZMod.val_natCast, ZMod.val_natCast] at h3
      -- h3 : (r+(n-1)*k₀+1) % n = (r+(n-1)*k₀) % n — impossible for n ≥ 2
      have hmod : r + (n - 1) * k₀ ≡ r + (n - 1) * k₀ + 1 [MOD n] :=
        (h3 : Nat.ModEq n _ _).symm
      rw [Nat.modEq_iff_dvd' (by omega)] at hmod
      rw [show r + (n - 1) * k₀ + 1 - (r + (n - 1) * k₀) = 1 from by omega] at hmod
      exact absurd (Nat.le_of_dvd (by omega) hmod) (by omega)
    have hj_lt : j.val < n - 1 := by have := ZMod.val_lt j; omega
    -- kStepVector at r+(n-1)*k₀+1 has z₀-component v
    have hadj_val : Necklace.kStepVector w (r + (n - 1) * k₀ + 1) k₀ z₀ = v := by
      have hmod : (r + (n - 1) * k₀ + 1) % n = (r + j.val * k₀) % n := by
        have h1 : (↑(r + (n - 1) * k₀ + 1) : ZMod n) = (↑(r + j.val * k₀) : ZMod n) := by
          rw [hj, Nat.cast_add, Nat.cast_mul, natCast_zmod_val]
        have h2 := congr_arg ZMod.val h1
        rwa [ZMod.val_natCast, ZMod.val_natCast] at h2
      have hkv : Necklace.kStepVector w (r + (n - 1) * k₀ + 1) k₀ =
          Necklace.kStepVector w (r + j.val * k₀) k₀ := by
        conv_lhs => rw [← kStepVector_mod_n w (r + (n - 1) * k₀ + 1) k₀]
        rw [hmod]
        exact kStepVector_mod_n w (r + j.val * k₀) k₀
      rw [congr_fun hkv z₀]
      have hsv := congr_fun (hseq ⟨j.val, by omega⟩) z₀
      simp only [] at hsv; rw [hsv]
      rcases Nat.mod_two_eq_zero_or_one j.val with h | h
      · exact congr_fun (congr_arg seq (Fin.ext h)) z₀
      · rw [show (⟨j.val % 2, _⟩ : Fin 2) = ⟨1, by omega⟩ from Fin.ext h]
        exact hz₀.symm
    rwa [hadj_val] at hraw
  -- Step 4: v ≠ close_z (else n | count(z₀), contradiction)
  have h_ne : v ≠ close_z := by
    intro heq
    have h_nv : ↑n * v = ↑k₀ * ↑(Necklace.count w z₀) := by
      have h := hident; rw [← heq] at h
      have : (↑(n - 1) : ℤ) * v + v = ↑n * v := by
        rw [show (↑(n - 1) : ℤ) = ↑n - 1 from by omega]; ring
      linarith
    have hv_nn : v ≥ 0 := by
      have : v = Necklace.kStepVector w r k₀ z₀ := by
        have := congr_fun (hseq ⟨0, by omega⟩) z₀
        simp only [Nat.zero_mul, Nat.add_zero, Nat.zero_mod] at this
        exact this.symm
      rw [this]; unfold Necklace.kStepVector ZVector.ofList Necklace.slice; positivity
    have h_nat : n * v.toNat = k₀ * Necklace.count w z₀ := by
      have hcast : (↑v.toNat : ℤ) = v := Int.toNat_of_nonneg hv_nn
      exact_mod_cast (show (↑(n * v.toNat) : ℤ) = ↑(k₀ * Necklace.count w z₀) from by
        push_cast; rw [hcast]; exact h_nv)
    have h_dvd : n ∣ Necklace.count w z₀ :=
      hcop.symm.dvd_of_dvd_mul_left ⟨v.toNat, h_nat.symm⟩
    have hcz_pos := count_pos_of_isTernary w htern z₀
    have hcz_lt : Necklace.count w z₀ < n := by
      have := count_total w
      have := count_pos_of_isTernary w htern StepSize.L
      have := count_pos_of_isTernary w htern StepSize.m
      have := count_pos_of_isTernary w htern StepSize.s
      cases z₀ <;> omega
    exact absurd (Nat.le_of_dvd hcz_pos h_dvd) (by omega)
  -- Step 5: close_z = v ± 1, so k₀ * count(z₀) ≡ ±1 (mod n)
  have h_pm : close_z = v + 1 ∨ close_z = v - 1 := by
    obtain ⟨h1, h2⟩ := abs_le.mp h_scoot; omega
  have hcz_mod : Necklace.count w z₀ * k₀ % n = 1 ∨
      Necklace.count w z₀ * k₀ % n = n - 1 := by
    -- From hident: (n-1)*v + close_z = k₀ * count(z₀)
    -- close_z = v+1: k₀*count = (n-1)*v + v + 1 = n*v + 1
    -- close_z = v-1: k₀*count = (n-1)*v + v - 1 = n*v - 1
    have hv_nn : v ≥ 0 := by
      have : v = Necklace.kStepVector w r k₀ z₀ := by
        have := congr_fun (hseq ⟨0, by omega⟩) z₀
        simp only [Nat.zero_mul, Nat.add_zero, Nat.zero_mod] at this
        exact this.symm
      rw [this]; unfold Necklace.kStepVector ZVector.ofList Necklace.slice; positivity
    rcases h_pm with hc | hc
    · -- close_z = v + 1: k₀ * count = n*v + 1
      left
      have h_eq : ↑k₀ * ↑(Necklace.count w z₀) = ↑n * v + 1 := by
        have : (↑(n - 1) : ℤ) * v + (v + 1) = ↑n * v + 1 := by
          rw [show (↑(n - 1) : ℤ) = ↑n - 1 from by omega]; ring
        linarith [hident, hc]
      have h_nat : k₀ * Necklace.count w z₀ = n * v.toNat + 1 := by
        have hcast : (↑v.toNat : ℤ) = v := Int.toNat_of_nonneg hv_nn
        exact_mod_cast (show (↑(k₀ * Necklace.count w z₀) : ℤ) = ↑(n * v.toNat + 1) from by
          push_cast; rw [hcast]; linarith [h_eq])
      rw [show Necklace.count w z₀ * k₀ = k₀ * Necklace.count w z₀ from by ring,
          h_nat, show n * v.toNat + 1 = 1 + n * v.toNat from by omega,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : 1 < n)]
    · -- close_z = v - 1: k₀ * count = n*v - 1
      right
      have h_eq : ↑k₀ * ↑(Necklace.count w z₀) = ↑n * v - 1 := by
        have : (↑(n - 1) : ℤ) * v + (v - 1) = ↑n * v - 1 := by
          rw [show (↑(n - 1) : ℤ) = ↑n - 1 from by omega]; ring
        linarith [hident, hc]
      -- v ≥ 1 (since n*v ≥ 1, and n ≥ 1)
      have hv_pos : v ≥ 1 := by
        by_contra hlt; push_neg at hlt
        have hv0 : v = 0 := by omega
        rw [hv0, mul_zero, zero_sub] at h_eq
        have : (↑k₀ * ↑(Necklace.count w z₀) : ℤ) ≥ 0 := by positivity
        linarith
      -- n*v - 1 = n*(v-1) + (n-1), so mod n = n-1
      have h_nat : k₀ * Necklace.count w z₀ = n * (v.toNat - 1) + (n - 1) := by
        have hcast : (↑v.toNat : ℤ) = v := Int.toNat_of_nonneg hv_nn
        have hv1 : v.toNat ≥ 1 := by omega
        exact_mod_cast (show (↑(k₀ * Necklace.count w z₀) : ℤ) =
            ↑(n * (v.toNat - 1) + (n - 1)) from by
          push_cast [Nat.cast_sub hv1, Nat.cast_sub (by omega : 1 ≤ n)]
          rw [hcast]; linarith [h_eq])
      rw [show Necklace.count w z₀ * k₀ = k₀ * Necklace.count w z₀ from by ring,
          h_nat, show n * (v.toNat - 1) + (n - 1) = (n - 1) + n * (v.toNat - 1) from by omega,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : n - 1 < n)]
  -- Step 6: Modular endgame
  have hsum_ln : l + 2 * ((n - l) / 2) = n := by omega
  have hdvd3 := mod_endgame_dvd_three n l ((n - l) / 2) k₀ (by omega) hsum_ln
      hl_mod (by rwa [hcz₀] at hcz_mod)
  -- n | 3, n ≥ 3 → n = 3
  have : n ≤ 3 := Nat.le_of_dvd (by omega) hdvd3
  omega

/-- The cancelling pair in an odd AS has equal letter counts.
    This connects the pair identification MOS (which is for the cancelling pair)
    to the step signature (which requires equal counts at L and m).

    **Proof**: From `as_alternating_letter_counts`, there is a distinguished
    step size d with count(d) = l (odd) and count(others) = (n-l)/2.
    If d is the neutral letter z₀ (the one with seq(0)(z₀) = seq(1)(z₀)),
    then count(x) = count(y) = (n-l)/2 immediately.
    Otherwise d ∈ {x, y} and `as_neutral_forces_n_eq_3` gives n = 3,
    where all counts are 1. -/
private lemma cancelling_pair_equal_counts (w : TernaryNecklace n)
    (hprim : Necklace.isPrimitive w) (htern : isTernary w)
    (hodd : n % 2 = 1)
    (x y : StepSize) (_hxy : x ≠ y)
    (k₀ r : ℕ) (seq : Fin 2 → ZVector StepSize)
    (hcop : Nat.Coprime k₀ n)
    (hseq : ∀ i : Fin (n - 1),
      Necklace.kStepVector w (r + i.val * k₀) k₀ =
        seq ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩)
    (hclose : ∀ j : Fin 2,
      Necklace.kStepVector w (r + (n - 1) * k₀) k₀ ≠ seq j)
    (hz : ∀ z : StepSize, z ≠ x → z ≠ y →
      seq ⟨0, by omega⟩ z = seq ⟨1, by omega⟩ z) :
    Necklace.count w x = Necklace.count w y := by
  have hn_ge := ternary_length_ge_three w htern
  -- Get the third letter z₀
  obtain ⟨z₀, hz₀x, hz₀y⟩ : ∃ z₀ : StepSize, z₀ ≠ x ∧ z₀ ≠ y := by
    cases x <;> cases y <;> simp_all
    · exact ⟨.s, by decide, by decide⟩
    · exact ⟨.m, by decide, by decide⟩
    · exact ⟨.s, by decide, by decide⟩
    · exact ⟨.L, by decide, by decide⟩
    · exact ⟨.m, by decide, by decide⟩
    · exact ⟨.L, by decide, by decide⟩
  -- seq(0)(z₀) = seq(1)(z₀) from the cancelling pair condition
  have hz₀_eq := hz z₀ hz₀x hz₀y
  -- Get count structure: ∃ d, count(d) = l, count(others) = (n-l)/2
  obtain ⟨l, hl_pos, hl_le, hl_odd, hl_mod⟩ :=
    exists_odd_quasi_inverse k₀ hodd hcop hn_ge
  obtain ⟨d, hd_count, hd_other⟩ :=
    as_alternating_letter_counts w hprim htern k₀ r seq l hcop hodd
      hl_pos hl_le hl_odd hl_mod hseq hclose
  -- Case split: z₀ = d or z₀ ≠ d
  by_cases hzd : z₀ = d
  · -- Case 1: z₀ = d → count(x) = (n-l)/2 = count(y)
    have hx_ne_d : x ≠ d := fun h => hz₀x (hzd.trans h.symm)
    have hy_ne_d : y ≠ d := fun h => hz₀y (hzd.trans h.symm)
    rw [hd_other x hx_ne_d, hd_other y hy_ne_d]
  · -- Case 2: z₀ ≠ d, so count(z₀) = (n-l)/2
    have hcz₀ : Necklace.count w z₀ = (n - l) / 2 := hd_other z₀ hzd
    -- Modular argument forces n = 3
    have hn3 := as_neutral_forces_n_eq_3 w htern k₀ r seq hcop hodd
      hseq hclose z₀ hz₀_eq l hl_pos hl_le hl_odd hl_mod hcz₀
    -- When n = 3: l = 1, all counts = 1
    subst hn3
    have hl1 : l = 1 := by omega
    subst hl1
    have : Necklace.count w x = 1 := by
      by_cases h : x = d
      · rw [h, hd_count]
      · exact hd_other x h
    have : Necklace.count w y = 1 := by
      by_cases h : y = d
      · rw [h, hd_count]
      · exact hd_other y h
    omega

/-- Applying a letter permutation preserves hasMOSProperty. -/
lemma hasMOSProperty_applyPerm (σ : Equiv.Perm StepSize)
    (w : Necklace StepSize n) (h : Necklace.hasMOSProperty w) :
    Necklace.hasMOSProperty (Necklace.applyPerm σ w) := by
  obtain ⟨⟨a, b, hab, ⟨i, hi⟩, ⟨j, hj⟩⟩, hmult⟩ := h
  constructor
  · exact ⟨σ a, σ b, σ.injective.ne hab,
      ⟨i, show σ (w i) = σ a by rw [hi]⟩,
      ⟨j, show σ (w j) = σ b by rw [hj]⟩⟩
  · intro k hk hkn
    rw [Necklace.allKStepMultisets_toFinset_card_applyPerm]
    exact hmult k hk hkn

/-- Pair identification MOS is preserved under letter permutation:
    if identifying x, y in w gives a MOS, then identifying σ(x), σ(y) in σ(w)
    also gives a MOS. -/
lemma isPartialPairwiseMOS_applyPerm (σ : Equiv.Perm StepSize)
    (w : TernaryNecklace n) (x y : StepSize)
    (h : isPartialPairwiseMOS w x y) :
    isPartialPairwiseMOS (Necklace.applyPerm σ w) (σ x) (σ y) := by
  show Necklace.hasMOSProperty
    (TernaryNecklace.identifyPair (Necklace.applyPerm σ w) (σ x) (σ y))
  rw [identifyPair_applyPerm, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact hasMOSProperty_applyPerm σ _ h

/-- Given distinct step sizes x ≠ y, there exists a permutation σ
    sending x to L and y to m. -/
lemma exists_perm_x_to_L_y_to_m (x y : StepSize) (hxy : x ≠ y) :
    ∃ σ : Equiv.Perm StepSize, σ x = StepSize.L ∧ σ y = StepSize.m ∧
      ∀ z : StepSize, z ≠ x → z ≠ y → σ z = StepSize.s := by
  cases x <;> cases y <;> simp_all
  · -- L, m → id
    exact ⟨1, rfl, rfl, fun z hz1 hz2 => by cases z <;> simp_all⟩
  · -- L, s → swap m s
    refine ⟨Equiv.swap .m .s, ?_, ?_, fun z hz1 hz2 => ?_⟩
    · decide
    · decide
    · cases z <;> simp_all
  · -- m, L → swap L m
    refine ⟨Equiv.swap .L .m, ?_, ?_, fun z hz1 hz2 => ?_⟩
    · decide
    · decide
    · cases z <;> simp_all; decide
  · -- m, s → cycle: m→L, s→m, L→s
    let σ : Equiv.Perm StepSize := {
      toFun := fun | .L => .s | .m => .L | .s => .m
      invFun := fun | .L => .m | .m => .s | .s => .L
      left_inv := fun x => by cases x <;> rfl
      right_inv := fun x => by cases x <;> rfl
    }
    exact ⟨σ, rfl, rfl, fun z hz1 hz2 => by cases z <;> simp_all; rfl⟩
  · -- s, L → cycle: s→L, L→m, m→s
    let σ : Equiv.Perm StepSize := {
      toFun := fun | .L => .m | .m => .s | .s => .L
      invFun := fun | .L => .s | .m => .L | .s => .m
      left_inv := fun x => by cases x <;> rfl
      right_inv := fun x => by cases x <;> rfl
    }
    exact ⟨σ, rfl, rfl, fun z hz1 hz2 => by cases z <;> simp_all; rfl⟩
  · -- s, m → swap L s
    refine ⟨Equiv.swap .L .s, ?_, ?_, fun z hz1 hz2 => ?_⟩
    · decide
    · decide
    · cases z <;> simp_all

/-- If l * k ≡ ±1 (mod n) with n ≥ 3, then gcd(l, n) = 1. -/
private lemma quasi_inverse_coprime (l k n : ℕ) (hn : n ≥ 3)
    (h : l * k % n = 1 ∨ l * k % n = n - 1) :
    Nat.Coprime l n := by
  -- gcd(l, n) divides l*k and n*(l*k/n), hence l*k % n = l*k - n*(l*k/n)
  have hdvd_lk : Nat.gcd l n ∣ l * k := dvd_mul_of_dvd_left (Nat.gcd_dvd_left l n) k
  have hdvd_nq : Nat.gcd l n ∣ n * (l * k / n) :=
    dvd_mul_of_dvd_left (Nat.gcd_dvd_right l n) _
  have hdvd_mod : Nat.gcd l n ∣ l * k % n := by
    have hsub := Nat.dvd_sub hdvd_lk hdvd_nq
    rwa [show l * k - n * (l * k / n) = l * k % n from by
      have := Nat.div_add_mod (l * k) n; omega] at hsub
  rcases h with h | h
  · -- l * k % n = 1, so gcd l n ∣ 1
    rw [h] at hdvd_mod; exact Nat.dvd_one.mp hdvd_mod
  · -- l * k % n = n - 1, so gcd l n ∣ n - 1 and gcd l n ∣ n, hence gcd l n ∣ 1
    rw [h] at hdvd_mod
    have := Nat.dvd_sub (Nat.gcd_dvd_right l n) hdvd_mod
    rw [show n - (n - 1) = 1 from by omega] at this
    exact Nat.dvd_one.mp this

set_option maxHeartbeats 400000 in
/-- From AS structure + quasi-inverse, the identified pair counts `2a` and
    the remaining count `b` are coprime.

    **Proof**: From `as_alternating_letter_counts`, one letter has count `l₀`
    and the other two have count `(n-l₀)/2`. The cancelling pair has equal counts
    (`count(x) = count(y) = a`). Either `b = l₀` (and `gcd(l₀, n) = 1` gives
    `gcd(2a, b) = 1`), or all counts equal, forcing `l₀ = 1, n = 3`. -/
private lemma as_coprime_counts (w : TernaryNecklace n)
    (hprim : Necklace.isPrimitive w) (htern : isTernary w)
    (k₀ r : ℕ) (seq : Fin 2 → ZVector StepSize)
    (hcop_as : Nat.Coprime k₀ n) (hodd : n % 2 = 1)
    (hseq : ∀ i : Fin (n - 1),
      Necklace.kStepVector w (r + i.val * k₀) k₀ =
        seq ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩)
    (hclose : ∀ j : Fin 2,
      Necklace.kStepVector w (r + (n - 1) * k₀) k₀ ≠ seq j)
    (x y z₀ : StepSize) (hxy : x ≠ y) (hz₀x : z₀ ≠ x) (hz₀y : z₀ ≠ y)
    (hcount_eq : Necklace.count w x = Necklace.count w y) :
    Nat.Coprime (2 * Necklace.count w x) (Necklace.count w z₀) := by
  have hn_ge := ternary_length_ge_three w htern
  obtain ⟨l₀, hl₀_pos, hl₀_le, hl₀_odd, hl₀_mod⟩ :=
    exists_odd_quasi_inverse k₀ hodd hcop_as hn_ge
  obtain ⟨d, hd_count, hd_rest⟩ := as_alternating_letter_counts w hprim htern
    k₀ r seq l₀ hcop_as hodd hl₀_pos hl₀_le hl₀_odd hl₀_mod hseq hclose
  have hcop_l₀ := quasi_inverse_coprime l₀ k₀ n hn_ge hl₀_mod
  -- n = 2 * count x + count z₀ since x, y, z₀ are distinct and count x = count y
  have hn_eq : n = 2 * Necklace.count w x + Necklace.count w z₀ := by
    have htotal := count_total w
    cases x <;> cases y <;> cases z₀ <;>
      first
      | exact absurd rfl hxy
      | exact absurd rfl hz₀x
      | exact absurd rfl hz₀y
      | omega
  -- Key: gcd(2*count_x, count_z₀) | gcd(count_z₀, n) via n = 2*count_x + count_z₀
  set g := Nat.gcd (2 * Necklace.count w x) (Necklace.count w z₀)
  suffices hbn : Nat.gcd (Necklace.count w z₀) n = 1 by
    have hdvd_2a : g ∣ 2 * Necklace.count w x := Nat.gcd_dvd_left _ _
    have hdvd_b : g ∣ Necklace.count w z₀ := Nat.gcd_dvd_right _ _
    have hdvd_n : g ∣ n := hn_eq ▸ Nat.dvd_add hdvd_2a hdvd_b
    exact Nat.dvd_one.mp (hbn ▸ Nat.dvd_gcd hdvd_b hdvd_n)
  -- Show gcd(count_z₀, n) = 1 by case analysis on the distinguished letter d
  by_cases hd_z₀ : d = z₀
  · -- Case 1: d = z₀, so count z₀ = l₀ and Coprime l₀ n
    rw [hd_z₀] at hd_count
    rw [hd_count]
    exact hcop_l₀
  · -- Case 2: d ∈ {x, y}
    have hd_in : d = x ∨ d = y := by
      cases d <;> cases x <;> cases y <;> cases z₀ <;>
        first
        | exact absurd rfl hxy
        | exact absurd rfl hz₀x
        | exact absurd rfl hz₀y
        | exact absurd rfl hd_z₀
        | exact Or.inl rfl
        | exact Or.inr rfl
    have hcx_eq_l₀ : Necklace.count w x = l₀ := by
      rcases hd_in with rfl | rfl
      · exact hd_count
      · rwa [hcount_eq]
    have hcz₀_eq : Necklace.count w z₀ = (n - l₀) / 2 := by
      rcases hd_in with rfl | rfl
      · exact hd_rest z₀ hz₀x
      · exact hd_rest z₀ hz₀y
    -- n = 2l₀ + (n-l₀)/2 implies n = 3l₀
    have hn_3l₀ : n = 3 * l₀ := by
      have h1 := hn_eq; rw [hcx_eq_l₀, hcz₀_eq] at h1
      have := Nat.div_add_mod (n - l₀) 2; omega
    -- l₀ | n and Coprime l₀ n, so l₀ = 1
    have hl₀_one : l₀ = 1 := by
      have hdvd_n : l₀ ∣ n := hn_3l₀ ▸ dvd_mul_left l₀ 3
      have := Nat.dvd_gcd (dvd_refl l₀) hdvd_n
      rw [hcop_l₀] at this; exact Nat.dvd_one.mp this
    have : Necklace.count w z₀ = 1 := by rw [hcz₀_eq]; omega
    rw [this]; simp

/-- The ordered deletion (removing one step type) has ≤ 2 distinct values. -/
private lemma orderedDeletion_toFinset_card
    (w : TernaryNecklace n) (x : StepSize) :
    (TernaryNecklace.orderedDeletion w x).toFinset.card ≤ 2 := by
  have hmem : ∀ a ∈ TernaryNecklace.orderedDeletion w x, a ≠ x :=
    fun a ha => by simp only [TernaryNecklace.orderedDeletion, List.mem_filter,
      decide_eq_true_eq] at ha; exact ha.2
  suffices h : ∃ (b c : StepSize), (TernaryNecklace.orderedDeletion w x).toFinset ⊆ {b, c} by
    obtain ⟨b, c, hsub⟩ := h
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  cases x with
  | L => exact ⟨.m, .s, fun a ha => by
      rw [List.mem_toFinset] at ha; have := hmem a ha; cases a <;> simp_all⟩
  | m => exact ⟨.L, .s, fun a ha => by
      rw [List.mem_toFinset] at ha; have := hmem a ha; cases a <;> simp_all⟩
  | s => exact ⟨.L, .m, fun a ha => by
      rw [List.mem_toFinset] at ha; have := hmem a ha; cases a <;> simp_all⟩

/-- The length of the ordered deletion = n minus the count of the deleted step. -/
lemma orderedDeletion_length (w : TernaryNecklace n) (x : StepSize) :
    (TernaryNecklace.orderedDeletion w x).length + Necklace.count w x = n := by
  unfold TernaryNecklace.orderedDeletion Necklace.count
  -- Step 1: Normalize monadic elaboration.
  -- (List.range n).map (fun i => w ↑i) elaborates to map w (do a ← range n; pure ↑a).
  -- Convert the inner (do ...) back to (List.range n).map Nat.cast, then combine maps.
  have heq : ∀ (l : List ℕ), (do let a ← l; pure (↑a : ZMod n)) =
      l.map (Nat.cast : ℕ → ZMod n) := by
    intro l; induction l with
    | nil => rfl
    | cons a l ih => simp only [List.map_cons]; exact congrArg _ ih
  simp only [heq, List.map_map]
  -- Goal: ((List.range n).map (w ∘ Nat.cast)).filter (· ≠ x) |>.length + ... = n
  -- Step 2: Move filter inside map, then drop map for length
  rw [List.filter_map, List.length_map]
  -- Goal: ((List.range n).filter ((· ≠ x) ∘ w ∘ Nat.cast)).length + ... = n
  -- Step 3: Reduce to showing filter.length = |{i : ZMod n | w i ≠ x}|
  suffices h : ((List.range n).filter ((· ≠ x) ∘ w ∘ (Nat.cast : ℕ → ZMod n))).length =
      (Finset.filter (fun i : ZMod n => w i ≠ x) Finset.univ).card by
    rw [h, ← Finset.card_union_of_disjoint
      (Finset.disjoint_filter.mpr fun _ _ h => h)]
    have : Finset.filter (fun i : ZMod n => w i ≠ x) Finset.univ ∪
        Finset.filter (fun i : ZMod n => w i = x) Finset.univ =
        (Finset.univ : Finset (ZMod n)) := by
      ext i; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
      exact ⟨fun _ => trivial, fun _ => (em (w i = x)).elim Or.inr Or.inl⟩
    rw [this, Finset.card_univ, ZMod.card]
  -- Step 4: Convert list filter length to finset filter card via nodup + toFinset
  have hnd : ((List.range n).filter ((· ≠ x) ∘ w ∘ (Nat.cast : ℕ → ZMod n))).Nodup :=
    List.Nodup.filter _ List.nodup_range
  rw [← List.toFinset_card_of_nodup hnd, List.toFinset_filter, List.toFinset_range]
  -- Goal: ((Finset.range n).filter ...).card = ((Finset.univ : Finset (ZMod n)).filter ...).card
  -- Step 5: Bijection Finset.range n ↔ Finset.univ (ZMod n) via Nat.cast
  apply Finset.card_bij (fun i _hi => ((i : ℕ) : ZMod n))
  · -- map preserves membership
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, Function.comp,
      ne_eq, decide_eq_true_eq, true_and] at hi ⊢
    exact hi.2
  · -- injectivity
    intro i₁ hi₁ i₂ hi₂ h
    have h1 := (Finset.mem_filter.mp hi₁).1
    have h2 := (Finset.mem_filter.mp hi₂).1
    rw [Finset.mem_range] at h1 h2
    have := congr_arg ZMod.val h
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this
  · -- surjectivity
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq] at hj
    refine ⟨ZMod.val j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt j), ?_⟩,
      ZMod.natCast_zmod_val j⟩
    simp only [Function.comp, ne_eq, decide_eq_true_eq, ZMod.natCast_zmod_val]
    exact hj

/-- If `Necklace.count w y > 0` and `y ≠ x`, then `y ∈ orderedDeletion w x`. -/
private lemma mem_orderedDeletion_of_ne_of_count_pos (w : TernaryNecklace n)
    (x y : StepSize) (hne : y ≠ x) (hcount : Necklace.count w y > 0) :
    y ∈ TernaryNecklace.orderedDeletion w x := by
  -- Get a position where w has value y
  have ⟨p, hp⟩ : ∃ p : ZMod n, w p = y := by
    by_contra h; push_neg at h
    have : Necklace.count w y = 0 := Finset.card_eq_zero.mpr
      (Finset.filter_eq_empty_iff.mpr (fun i _ => h i))
    omega
  -- Unfold orderedDeletion and fix monadic elaboration
  unfold TernaryNecklace.orderedDeletion
  have heq : ∀ (l : List ℕ), (do let a ← l; pure (↑a : ZMod n)) =
      l.map (Nat.cast : ℕ → ZMod n) := by
    intro l; induction l with
    | nil => rfl
    | cons a l ih => simp only [List.map_cons]; exact congrArg _ ih
  simp only [heq, List.map_map]
  apply List.mem_filter.mpr
  constructor
  · have hmem := List.mem_range.mpr (ZMod.val_lt p)
    have := List.mem_map_of_mem (f := w ∘ Nat.cast) hmem
    simp only [Function.comp, ZMod.natCast_zmod_val, hp] at this
    exact this
  · simp only [ne_eq, decide_eq_true_eq]; exact hne

/-! ### Bridge: StepSize → BinaryStep

Map {L, m, s} to {L, s} for connecting to binary MOS theory after pair identification. -/

/-- Map StepSize to BinaryStep: L → L, m → L, s → s.
    After `identifyPair w .L .m`, only m and s remain, mapped to L and s. -/
def msToBinary : StepSize → BinaryStep
  | .L => .L | .m => .L | .s => .s

/-- The identified necklace `identifyPair w .L .m` viewed as a BinaryNecklace. -/
def identifiedToBinary (w : Necklace StepSize n) : BinaryNecklace n :=
  msToBinary ∘ w

/-- Composing a necklace with a function distributes over k-step multisets. -/
private lemma allKStepMultisets_comp [DecidableEq α] [DecidableEq β]
    (w : Necklace α n) (f : α → β) (k : ℕ) :
    Necklace.allKStepMultisets (f ∘ w) k =
      (Necklace.allKStepMultisets w k).map (Multiset.map f) := by
  have slice_comp : ∀ (a b : ℕ), Necklace.slice (f ∘ w) a b =
      (Necklace.slice w a b).map f := by
    intro a b; simp [Necklace.slice, List.map_map]
  unfold Necklace.allKStepMultisets Necklace.allKStepSubwords
  simp only [List.map_ofFn]
  congr 1; funext i
  simp only [Function.comp, slice_comp, Necklace.abelianize, Multiset.map_coe]

/-- The bridge preserves the MOS property: if `identifyPair w .L .m` has the MOS property,
    then its binary image is a binary MOS. -/
lemma identifiedToBinary_isMOS (w : TernaryNecklace n)
    (hcountL : Necklace.count w .L = a) (hcountm : Necklace.count w .m = a)
    (hcounts : Necklace.count w .s = b)
    (ha_pos : a > 0) (hb_pos : b > 0)
    (hmos : isPartialPairwiseMOS w .L .m) :
    BinaryNecklace.isMOS (identifiedToBinary (TernaryNecklace.identifyPair w .L .m)) := by
  set w' := TernaryNecklace.identifyPair w .L .m with hw'
  constructor
  · -- isBinary: the binary necklace uses both L and s
    constructor
    · -- ∃ i, (msToBinary ∘ w') i = .L
      -- From ha_pos: count w .L = a > 0 → ∃ i, w i = .L
      have : 0 < Necklace.count w .L := by omega
      rw [Necklace.count, Finset.card_pos] at this
      obtain ⟨i, hi⟩ := this
      rw [Finset.mem_filter] at hi
      exact ⟨i, by simp [identifiedToBinary, msToBinary, hw', TernaryNecklace.identifyPair, hi.2]⟩
    · -- ∃ i, (msToBinary ∘ w') i = .s
      have : 0 < Necklace.count w .s := by omega
      rw [Necklace.count, Finset.card_pos] at this
      obtain ⟨i, hi⟩ := this
      rw [Finset.mem_filter] at hi
      exact ⟨i, by simp [identifiedToBinary, msToBinary, hw', TernaryNecklace.identifyPair, hi.2]⟩
  · -- ≤ 2 k-step multisets
    intro k hk_pos hk_lt
    rw [show identifiedToBinary w' = msToBinary ∘ w' from rfl,
        allKStepMultisets_comp w' msToBinary k]
    have heq : ((Necklace.allKStepMultisets w' k).map (Multiset.map msToBinary)).toFinset =
        (Necklace.allKStepMultisets w' k).toFinset.image (Multiset.map msToBinary) := by
      ext x; simp [List.mem_toFinset, Finset.mem_image, List.mem_map]
    calc ((Necklace.allKStepMultisets w' k).map (Multiset.map msToBinary)).toFinset.card
        ≤ (Necklace.allKStepMultisets w' k).toFinset.card := by
            rw [heq]; exact Finset.card_image_le
      _ ≤ 2 := hmos.2 k hk_pos hk_lt

/-- Count of BinaryStep.L in the bridge = 2a (the L and m counts combined). -/
lemma identifiedToBinary_count_L (w : TernaryNecklace n)
    (hcountL : Necklace.count w .L = a) (hcountm : Necklace.count w .m = a) :
    Necklace.count (identifiedToBinary (TernaryNecklace.identifyPair w .L .m)) .L = 2 * a := by
  unfold Necklace.count
  have heq : Finset.filter (fun i => identifiedToBinary (TernaryNecklace.identifyPair w .L .m) i
      = BinaryStep.L) Finset.univ =
      Finset.filter (fun i => w i = .L) Finset.univ ∪
      Finset.filter (fun i => w i = .m) Finset.univ := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      identifiedToBinary, msToBinary, TernaryNecklace.identifyPair, Function.comp]
    constructor
    · intro h; cases hw : w i <;> simp_all
    · rintro (h | h) <;> simp_all
  rw [heq, Finset.card_union_of_disjoint]
  · unfold Necklace.count at hcountL hcountm; omega
  · rw [Finset.disjoint_filter]
    intro i _ h1 h2; rw [h1] at h2; exact absurd h2 (by decide)

/-- Count of BinaryStep.s in the bridge = b (the s count is unchanged). -/
lemma identifiedToBinary_count_s (w : TernaryNecklace n)
    (hcounts : Necklace.count w .s = b) :
    Necklace.count (identifiedToBinary (TernaryNecklace.identifyPair w .L .m)) .s = b := by
  rw [← hcounts]; unfold Necklace.count; congr 1; ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    identifiedToBinary, msToBinary, TernaryNecklace.identifyPair, Function.comp]
  constructor
  · intro h; by_contra hne; cases hw : w i <;> simp_all
  · intro h; simp_all

/-- The .s component of the binary bridge's kStepVector equals the .s component of w's kStepVector.
    This is the key bridge for `oddRegular_kstep_data`. -/
lemma identifiedToBinary_kStepVector_s (w : TernaryNecklace n) (i k : ℕ) :
    Necklace.kStepVector (identifiedToBinary (TernaryNecklace.identifyPair w .L .m)) i k BinaryStep.s =
    Necklace.kStepVector w i k StepSize.s := by
  -- Step 1: identifyPair preserves the .s component
  have h_ip : (Necklace.kStepVector (TernaryNecklace.identifyPair w .L .m) i k) .s =
      (Necklace.kStepVector w i k) .s := by
    rw [identifyPair_kStepVector w .L .m (by decide) i k]
    simp [ZVector.identifyPair]
  -- Step 2: msToBinary preserves the .s count in slices
  rw [← h_ip]
  set w' := TernaryNecklace.identifyPair w .L .m
  simp only [Necklace.kStepVector, identifiedToBinary]
  rw [show Necklace.slice (msToBinary ∘ w') i (i + k) =
      (Necklace.slice w' i (i + k)).map msToBinary from by
    simp [Necklace.slice, List.map_map]]
  simp only [ZVector.ofList]
  -- Suffices: count of BinaryStep.s in l.map msToBinary = count of StepSize.s in l
  suffices ∀ (l : List StepSize),
      ((l.map msToBinary).filter (· == BinaryStep.s)).length =
      (l.filter (· == StepSize.s)).length by exact_mod_cast this _
  intro l; induction l with
  | nil => simp
  | cons a t ih => cases a <;> simp [msToBinary, ih]

/-! ### Period and kStepVector correspondence for `identifyPair`/`identifiedToBinary` -/

/-- The `.L` component of kStepVectors of `identifyPair w .L .m` is always 0,
    since `identifyPair w .L .m` never outputs `.L`. -/
lemma kStepVector_identifyPair_L_eq_zero (w : TernaryNecklace n) (i k : ℕ) :
    Necklace.kStepVector (TernaryNecklace.identifyPair w .L .m) i k .L = 0 := by
  rw [identifyPair_kStepVector w .L .m (by decide) i k]
  simp [ZVector.identifyPair]

/-- The binary `.L` component equals the ternary `.m` component under identification:
    `kStepVector B i k .L = kStepVector (identifyPair w .L .m) i k .m`
    where `B = identifiedToBinary (identifyPair w .L .m)`. -/
lemma kStepVector_identifiedToBinary_L_eq_identifyPair_m
    (w : TernaryNecklace n) (i k : ℕ) :
    Necklace.kStepVector (identifiedToBinary (TernaryNecklace.identifyPair w .L .m)) i k .L =
    Necklace.kStepVector (TernaryNecklace.identifyPair w .L .m) i k .m := by
  set I := TernaryNecklace.identifyPair w .L .m
  simp only [Necklace.kStepVector, identifiedToBinary]
  rw [show Necklace.slice (msToBinary ∘ I) i (i + k) =
      (Necklace.slice I i (i + k)).map msToBinary from by
    simp [Necklace.slice, List.map_map]]
  simp only [ZVector.ofList]
  suffices h : ∀ (l : List StepSize), (∀ x ∈ l, x = .m ∨ x = .s) →
      ((l.map msToBinary).filter (· == BinaryStep.L)).length =
      (l.filter (· == StepSize.m)).length by
    have hms : ∀ x ∈ Necklace.slice I i (i + k), x = .m ∨ x = .s := by
      intro x hx
      simp only [Necklace.slice, List.mem_map] at hx
      obtain ⟨j, _, rfl⟩ := hx
      simp only [I, TernaryNecklace.identifyPair]
      split_ifs with h
      · exact Or.inl rfl
      · cases hw : w (↑j : ZMod n) with
        | L => exact absurd hw h
        | m => exact Or.inl rfl
        | s => exact Or.inr rfl
    exact_mod_cast h _ hms
  intro l hl; induction l with
  | nil => simp
  | cons a t ih =>
    have ha := hl a (List.mem_cons.mpr (Or.inl rfl))
    have ht : ∀ x ∈ t, x = .m ∨ x = .s :=
      fun x hx => hl x (List.mem_cons.mpr (Or.inr hx))
    rcases ha with rfl | rfl <;> simp [msToBinary, ih ht]

/-- The period lengths of `identifyPair w .L .m` and `identifiedToBinary (identifyPair w .L .m)`
    are equal. This follows because `msToBinary` is injective on `{.m, .s}` (the range of
    `identifyPair w .L .m`), so translational periods transfer in both directions. -/
lemma period_length_identifyPair_eq (w : TernaryNecklace n)
    (hpB_lt : (Necklace.period (identifiedToBinary (TernaryNecklace.identifyPair w .L .m))).length < n) :
    (Necklace.period (TernaryNecklace.identifyPair w .L .m)).length =
    (Necklace.period (identifiedToBinary (TernaryNecklace.identifyPair w .L .m))).length := by
  set I := TernaryNecklace.identifyPair w .L .m
  set B := identifiedToBinary I
  set pI := (Necklace.period I).length
  set pB := (Necklace.period B).length
  -- I only outputs .m or .s (never .L)
  have hI_val : ∀ j : ZMod n, I j = .m ∨ I j = .s := by
    intro j; simp only [I, TernaryNecklace.identifyPair]
    split_ifs with h
    · exact Or.inl rfl
    · cases hw : w j with
      | L => exact absurd hw h
      | m => exact Or.inl rfl
      | s => exact Or.inr rfl
  -- Helper: period gives translational invariance w(j) = w(j + pLen)
  have I_shift : ∀ i : ZMod n, I i = I (i + (pI : ZMod n)) := by
    intro i
    have h1 := period_pointwise I (ZMod.val i)
    have h2 := period_pointwise I (ZMod.val i + pI)
    rw [Nat.add_mod_right] at h2
    rw [show (i.val : ZMod n) = i from by
      simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]] at h1
    rw [show ((i.val + pI : ℕ) : ZMod n) = i + (pI : ZMod n) from by
      push_cast; simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]] at h2
    rw [h1, h2]
  have B_shift : ∀ i : ZMod n, B i = B (i + (pB : ZMod n)) := by
    intro i
    have h1 := period_pointwise B (ZMod.val i)
    have h2 := period_pointwise B (ZMod.val i + pB)
    rw [Nat.add_mod_right] at h2
    rw [show (i.val : ZMod n) = i from by
      simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]] at h1
    rw [show ((i.val + pB : ℕ) : ZMod n) = i + (pB : ZMod n) from by
      push_cast; simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]] at h2
    rw [h1, h2]
  -- pI ≤ pB: B has translational period pB ⟹ I has period pB (by injectivity of msToBinary on {.m,.s})
  have hpI_le : pI ≤ pB := by
    apply Necklace.period_length_le_of_translational_period I pB
      (period_length_pos B) hpB_lt (period_dvd_length B)
    intro i
    have hBi : msToBinary (I i) = msToBinary (I (i + (pB : ZMod n))) := B_shift i
    rcases hI_val i with h1 | h1 <;> rcases hI_val (i + (pB : ZMod n)) with h2 | h2 <;>
      simp only [h1, h2, msToBinary] at hBi ⊢ <;>
      first | rfl | exact absurd hBi (by decide)
  -- pB ≤ pI: I has translational period pI ⟹ B = msToBinary ∘ I does too
  have hpB_le : pB ≤ pI := by
    apply Necklace.period_length_le_of_translational_period B pI
      (period_length_pos I) (by omega) (period_dvd_length I)
    intro i
    show B i = B (i + (pI : ZMod n))
    exact congr_arg msToBinary (I_shift i)
  omega

/-! ### Deletion MOS from AS: helper lemmas

Proving that the ordered deletion of the non-equinumerous step gives a MOS.
Uses the generator structure of the template MOS and the AS alternation. -/

/-- Equal k-step vectors of w imply equal k-step vectors of f ∘ w. -/
private lemma kStepVector_comp_eq_of_kStepVector_eq [DecidableEq α] [Fintype α]
    [DecidableEq β] (w : Necklace α n) (f : α → β) (i₁ i₂ k : ℕ)
    (h : Necklace.kStepVector w i₁ k = Necklace.kStepVector w i₂ k) :
    Necklace.kStepVector (f ∘ w) i₁ k = Necklace.kStepVector (f ∘ w) i₂ k := by
  rw [kStepVector_eq_ofMultiset, kStepVector_eq_ofMultiset] at h
  have hm := ZVector.ofMultiset_injective h
  simp only [Necklace.abelianize] at hm
  have slice_comp : ∀ (a b : ℕ), Necklace.slice (f ∘ w) a b =
      (Necklace.slice w a b).map f := by
    intro a b; simp [Necklace.slice, List.map_map]
  rw [kStepVector_eq_ofMultiset, kStepVector_eq_ofMultiset]
  simp only [Necklace.abelianize, slice_comp, ← Multiset.map_coe]
  exact congr_arg (fun m => ZVector.ofMultiset (Multiset.map f m)) hm

/-- If all k-step vectors of a binary MOS are the same and gcd(k,n)=1, then False.
    Proof: sliding window gives B(i)=B(i+k), Bezout gives B(i)=B(i+1), so B is constant,
    contradicting the binary property. -/
private lemma mos_uniform_kstep_absurd (B : BinaryNecklace n)
    (hmos : BinaryNecklace.isMOS B) (k : ℕ) (_ : 0 < k)
    (hcop : Nat.Coprime k n)
    (hall : ∀ i : ℕ, Necklace.kStepVector B i k = Necklace.kStepVector B 0 k) :
    False := by
  -- Step 1: B(i) = B(i+k) for all i (sliding window)
  have hperiodic_k : ∀ i : ℕ, B (↑i : ZMod n) = B (↑(i + k) : ZMod n) := by
    intro i
    have heq_L : Necklace.kStepVector B i k BinaryStep.L =
        Necklace.kStepVector B (i + 1) k BinaryStep.L := by
      rw [hall i, hall (i + 1)]
    have hshift := slice_L_count_shift B i k
    dsimp only at hshift
    simp only [Necklace.kStepVector, ZVector.ofList] at heq_L
    simp only [Nat.cast_add]
    split_ifs at hshift with h1 h2
    · exact h1.trans h2.symm
    · linarith
    · linarith
    · -- Both ≠ .L, so both = .s
      rename_i h2
      have not_L_is_s : ∀ (x : BinaryStep), x ≠ .L → x = .s := by
        intro x hx; cases x <;> [exact absurd rfl hx; rfl]
      rw [not_L_is_s _ h1, not_L_is_s _ h2]
  -- Step 2: Iterate: B(j) = B(j + m*k) for all m
  have hiter : ∀ (j m : ℕ), B (↑j : ZMod n) = B (↑(j + m * k) : ZMod n) := by
    intro j m; induction m with
    | zero => simp
    | succ m ih =>
      rw [show j + (m + 1) * k = j + m * k + k from by ring]
      exact ih.trans (hperiodic_k (j + m * k))
  -- Step 3: Bezout: (gcd k n : ZMod n) = k * gcdA
  have hbez : (↑(Nat.gcd k n) : ZMod n) =
      (↑k : ZMod n) * ((Nat.gcdA k n : ℤ) : ZMod n) := by
    have := congr_arg (fun x : ℤ => (x : ZMod n)) (Nat.gcd_eq_gcd_ab k n)
    push_cast at this; rwa [ZMod.natCast_self, zero_mul, add_zero] at this
  -- Step 4: B has translational period 1
  have hperiodic_1 : ∀ (i : ZMod n), B i = B (i + 1) := by
    intro i
    have hi := hiter (ZMod.val i) (ZMod.val ((Nat.gcdA k n : ℤ) : ZMod n))
    rw [ZMod.natCast_zmod_val i] at hi
    rw [hi]; congr 1; push_cast
    rw [ZMod.natCast_zmod_val i,
        ZMod.natCast_zmod_val ((Nat.gcdA k n : ℤ) : ZMod n),
        mul_comm, ← hbez, hcop.gcd_eq_one, Nat.cast_one]
  -- Step 5: B is constant
  have hconst : ∀ i : ZMod n, B i = B 0 := by
    intro i
    have hnat : ∀ j : ℕ, B (↑j : ZMod n) = B 0 := by
      intro j; induction j with
      | zero => simp
      | succ j ih =>
        rw [show (↑(j + 1) : ZMod n) = (↑j : ZMod n) + 1 from by push_cast; ring]
        rw [← hperiodic_1]; exact ih
    rw [show i = (↑(ZMod.val i) : ZMod n) from (ZMod.natCast_zmod_val i).symm]
    exact hnat (ZMod.val i)
  -- Step 6: Contradiction with isBinary
  obtain ⟨i, hi⟩ := hmos.1.1
  obtain ⟨j, hj⟩ := hmos.1.2
  have : B i = B j := by rw [hconst i, hconst j]
  rw [hi, hj] at this; exact absurd this (by decide)

/-- kStepVector commutes with applyPerm via ZVector.applyPerm. -/
lemma kStepVector_applyPerm (σ : Equiv.Perm StepSize)
    (w : TernaryNecklace n) (i k : ℕ) :
    Necklace.kStepVector (Necklace.applyPerm σ w) i k =
      ZVector.applyPerm σ (Necklace.kStepVector w i k) := by
  unfold Necklace.kStepVector
  rw [Necklace.slice_applyPerm]
  exact ZVector.ofList_map_eq_applyPerm σ _

/-- Claim 0: For a primitive binary MOS with coprime letter counts,
    the generator's L-count is coprime to the total L-count.
    Proof: |g(L)·b − g(s)·2a| = 1 implies gcd(g(L), 2a) | 1. -/
private lemma generator_L_coprime
    (B : BinaryNecklace n)
    (hmos : BinaryNecklace.isMOS B) (hprim : Necklace.isPrimitive B)
    (g : ZVector BinaryStep) (hgen : IsGenerator B g)
    (a b : ℕ) (_hcop : Nat.Coprime (2 * a) b)
    (_hcountL : Necklace.count B .L = 2 * a)
    (_hcounts : Necklace.count B .s = b) :
    Nat.Coprime (Int.natAbs (g .L)) (2 * a) := by
  -- From generator_det_abs_one: g(L)*b - g(s)*2a = ±1
  have hdet := generator_det_abs_one B hmos.1 hprim g hgen
  rw [_hcountL, _hcounts] at hdet
  -- IsCoprime in ℤ: ∃ u v, u * g(.L) + v * (2a) = 1
  obtain ⟨u, v, huv⟩ : IsCoprime (g .L) (↑(2 * a) : ℤ) := by
    rcases hdet with hd | hd
    · exact ⟨↑b, -g .s, by linarith⟩
    · exact ⟨-(↑b : ℤ), g .s, by linarith⟩
  -- Any common divisor of |g(.L)| and 2a divides u*g(.L)+v*(2a) = 1
  show Nat.gcd (Int.natAbs (g .L)) (2 * a) = 1
  apply Nat.dvd_one.mp
  set d := Nat.gcd (Int.natAbs (g .L)) (2 * a)
  have hd1 : (↑d : ℤ) ∣ g .L :=
    Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left ..))
  have hd2 : (↑d : ℤ) ∣ ↑(2 * a) :=
    Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right ..)
  have : (↑d : ℤ) ∣ 1 := huv ▸
    dvd_add (dvd_mul_of_dvd_right hd1 u) (dvd_mul_of_dvd_right hd2 v)
  exact_mod_cast this

/-- If f has period c, then f has period m * c for any m : ℕ. -/
private lemma mul_period_fin2 {n : ℕ} (f : ZMod n → Fin 2) (c : ZMod n)
    (hper : ∀ q, f (q + c) = f q) (m : ℕ) :
    ∀ q, f (q + (↑m : ZMod n) * c) = f q := by
  induction m with
  | zero => intro q; simp
  | succ m ih =>
    intro q
    have : (↑(m + 1) : ZMod n) * c = ↑m * c + c := by push_cast; ring
    rw [this, ← add_assoc]
    exact (hper _).trans (ih q)

/-- Claim 2 (core): If a binary function on ZMod(2a) flips when shifted by j,
    and gcd(j, 2a) = 1, then it has period 2.
    Proof: f(q+2j) = f(q). Since gcd(2j, 2a) = 2 (from gcd(j,a)=1),
    Bézout gives 2 = 2j·u + 2a·v, so f(q+2) = f(q+2j·u) = f(q). -/
private lemma period_two_of_coprime_flip {a : ℕ} (ha : a > 0)
    (f : ZMod (2 * a) → Fin 2) (j : ℕ)
    (hcop : Nat.Coprime j (2 * a))
    (hflip : ∀ q : ZMod (2 * a), f (q + ↑j) ≠ f q) :
    ∀ q : ZMod (2 * a), f (q + 2) = f q := by
  haveI : NeZero (2 * a) := ⟨by omega⟩
  -- In Fin 2: if a ≠ b and b ≠ c then a = c
  have fin2_cancel : ∀ (x y z : Fin 2), x ≠ y → y ≠ z → x = z := by decide
  -- Double flip: f(q + j + j) = f(q)
  have hper : ∀ q, f (q + (↑j + ↑j)) = f q := by
    intro q; rw [← add_assoc]
    exact (fin2_cancel _ _ _ (Ne.symm (hflip q)) (Ne.symm (hflip (q + ↑j)))).symm
  -- j is a unit in ZMod(2a)
  set u := ZMod.unitOfCoprime j hcop
  -- u⁻¹ * (↑j + ↑j) = 2, since ↑u = ↑j definitionally
  have hinv : (↑u⁻¹ : ZMod (2 * a)) * (↑j + ↑j) = 2 := by
    change (↑u⁻¹ : ZMod (2 * a)) * (↑u + ↑u) = 2
    have h1 : (↑u⁻¹ : ZMod (2 * a)) * ↑u = 1 := u.inv_val
    have : (↑u⁻¹ : ZMod (2 * a)) * (↑u + ↑u) = 2 * (↑u⁻¹ * ↑u) := by ring
    rw [this, h1, mul_one]
  -- Lift u⁻¹ to ℕ via ZMod.val
  set m₀ := ZMod.val (↑u⁻¹ : ZMod (2 * a))
  have hm₀ : (↑m₀ : ZMod (2 * a)) = ↑u⁻¹ := ZMod.natCast_zmod_val _
  have h2 : (↑m₀ : ZMod (2 * a)) * (↑j + ↑j) = 2 := by rw [hm₀]; exact hinv
  -- Conclude: f(q + 2) = f(q + m₀ * (j+j)) = f(q) by mul_period_fin2
  intro q
  have := mul_period_fin2 f _ hper m₀ q
  rwa [h2] at this

/-- A binary list that is periodic with period 2 and uses both values
    has the circular MOS property. -/
lemma alternating_circular_mos (D : List StepSize) (a : ℕ)
    (hlen : D.length = 2 * a) (ha : a > 0)
    (halt : ∀ i, (hi : i < D.length) →
      D[i] = D[i % 2]'(by omega))
    (hne : D[0]'(by omega) ≠ D[1]'(by omega)) :
    circularHasMOSProperty D := by
  have hlen_pos : 0 < D.length := by omega
  refine ⟨by omega, ?_, ?_⟩
  -- Part 2: D uses ≥ 2 distinct values
  · have h0 : D[0]'(by omega) ∈ D := List.getElem_mem ..
    have h1 : D[1]'(by omega) ∈ D := List.getElem_mem ..
    have hsub : {D[0]'(by omega), D[1]'(by omega)} ⊆ D.toFinset := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact List.mem_toFinset.mpr ‹_›
    exact le_trans (Finset.card_pair hne ▸ le_refl _) (Finset.card_le_card hsub)
  -- Part 3: ≤ 2 distinct k-step multisets
  · intro k hk_pos hk_lt
    -- The k-step multiset at position i depends only on i % 2
    suffices ∀ i, i < D.length →
        (List.range k).map (fun j => D[(i + j) % D.length]!) =
        (List.range k).map (fun j => D[(i % 2 + j) % D.length]!) by
      set F := fun i => Multiset.ofList
        ((List.range k).map (fun j => D[(i + j) % D.length]!))
      have hF_mod : ∀ i, i < D.length → F i = F (i % 2) :=
        fun i hi => congr_arg Multiset.ofList (this i hi)
      suffices hsub : ((List.range D.length).map F).toFinset ⊆ {F 0, F 1} from
        le_trans (Finset.card_le_card hsub)
          (le_trans (Finset.card_insert_le ..) (by simp))
      intro m hm
      rw [List.mem_toFinset, List.mem_map] at hm
      obtain ⟨i, hi, rfl⟩ := hm
      rw [List.mem_range] at hi
      rw [hF_mod i hi]
      rcases Nat.mod_two_eq_zero_or_one i with h | h <;> rw [h] <;> simp
    -- Main: the k-step list at i equals the k-step list at (i % 2)
    intro i _hi
    apply List.map_congr_left; intro t ht; rw [List.mem_range] at ht
    have h1 : (i + t) % D.length < D.length := Nat.mod_lt _ hlen_pos
    have h2 : (i % 2 + t) % D.length < D.length := Nat.mod_lt _ hlen_pos
    rw [getElem!_pos D _ h1, getElem!_pos D _ h2, halt _ h1, halt _ h2]
    congr 1
    rw [hlen]
    have := Nat.mod_mod_of_dvd (i + t) (dvd_mul_right 2 a)
    have := Nat.mod_mod_of_dvd (i % 2 + t) (dvd_mul_right 2 a)
    omega

/-- If a list D of length 2a has a coprime flip (D[(i+j)%len] ≠ D[i] with gcd(j,2a)=1),
    then D has the circular MOS property. Bridges period_two_of_coprime_flip and
    alternating_circular_mos. -/
private lemma circular_mos_of_flip (D : List StepSize) (a : ℕ)
    (hlen : D.length = 2 * a) (ha : a > 0)
    (hbin : ∀ i, (hi : i < D.length) → D[i] = .L ∨ D[i] = .m)
    (j : ℕ) (hcop : Nat.Coprime j (2 * a))
    (hflip : ∀ i, (hi : i < D.length) →
      D[(i + j) % D.length]'(Nat.mod_lt _ (by omega)) ≠ D[i]) :
    circularHasMOSProperty D := by
  haveI : NeZero (2 * a) := ⟨by omega⟩
  have hlen_pos : 0 < D.length := by omega
  -- Define f : ZMod(2a) → Fin 2 encoding the letter at each position
  set f : ZMod (2 * a) → Fin 2 :=
    fun q => if D[ZMod.val q]'(by have := ZMod.val_lt q; omega) = .L then 0 else 1
  -- Key property: f values equal iff D values equal (since D is binary in {.L, .m})
  have hf_eq_iff : ∀ (p q : ZMod (2 * a)),
      f p = f q ↔ D[ZMod.val p]'(by have := ZMod.val_lt p; omega) =
                   D[ZMod.val q]'(by have := ZMod.val_lt q; omega) := by
    intro p q; simp only [f]
    have hp := hbin (ZMod.val p) (by have := ZMod.val_lt p; omega)
    have hq := hbin (ZMod.val q) (by have := ZMod.val_lt q; omega)
    constructor
    · intro h
      rcases hp with hp | hp <;> rcases hq with hq | hq <;> simp_all
    · intro h; rw [h]
  -- val(q + j) = (val q + j) % D.length
  have hval_add : ∀ q : ZMod (2 * a),
      ZMod.val (q + (↑j : ZMod (2 * a))) = (ZMod.val q + j) % D.length := by
    intro q; rw [hlen, ZMod.val_add, ZMod.val_natCast]
    have h1 : ZMod.val q % (2 * a) = ZMod.val q := Nat.mod_eq_of_lt (ZMod.val_lt q)
    have h2 : (ZMod.val q + j) % (2 * a) =
        (ZMod.val q % (2 * a) + j % (2 * a)) % (2 * a) := Nat.add_mod ..
    rw [h1] at h2; exact h2.symm
  -- f flips at shift j
  have hf_flip : ∀ q : ZMod (2 * a), f (q + ↑j) ≠ f q := by
    intro q
    rw [ne_eq, hf_eq_iff]
    have hq_lt : ZMod.val q < D.length := by have := ZMod.val_lt q; omega
    have hne := hflip (ZMod.val q) hq_lt
    have hval := hval_add q
    intro heq; apply hne
    have : D[ZMod.val (q + (↑j : ZMod (2*a)))]'(by have := ZMod.val_lt (q + (↑j : ZMod (2*a))); omega) =
           D[(ZMod.val q + j) % D.length]'(Nat.mod_lt _ hlen_pos) := by
      congr 1
    rw [this] at heq; exact heq
  -- Apply period_two_of_coprime_flip
  have hper2 := period_two_of_coprime_flip ha f j hcop hf_flip
  -- Convert: D[i] = D[i % 2] for all valid i
  have halt : ∀ i, (hi : i < D.length) → D[i] = D[i % 2]'(by omega) := by
    intro i hi
    -- f(↑i) = f(↑(i%2)) via mul_period_fin2 with m = i/2
    have hfi : f (↑i : ZMod (2*a)) = f (↑(i%2) : ZMod (2*a)) := by
      have key : (↑i : ZMod (2*a)) = ↑(i%2) + ↑(i/2) * 2 := by
        have h : i = i % 2 + i / 2 * 2 := by omega
        nth_rw 1 [h]; push_cast; ring
      rw [key]; exact mul_period_fin2 f 2 hper2 (i / 2) ↑(i%2)
    rw [hf_eq_iff] at hfi
    -- hfi : D[val(↑i)] = D[val(↑(i%2))], convert val to concrete indices
    have hv1 : ZMod.val (↑i : ZMod (2*a)) = i := by
      rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt (by omega)
    have hv2 : ZMod.val (↑(i%2) : ZMod (2*a)) = i % 2 := by
      rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt (by omega)
    simp only [hv1, hv2] at hfi
    exact hfi
  -- D[0] ≠ D[1]
  have hne : D[0]'(by omega) ≠ D[1]'(by omega) := by
    -- j is odd: gcd(j, 2a) = 1 and 2 | 2a implies 2 ∤ j
    have hj_odd : j % 2 = 1 := by
      by_contra h
      have : 2 ∣ j := Nat.dvd_of_mod_eq_zero (by omega)
      have h2 := Nat.dvd_gcd this (dvd_mul_right 2 a)
      rw [hcop] at h2; omega
    -- D[j % len] ≠ D[0] from hflip at i = 0
    have h0 := hflip 0 (by omega)
    simp only [Nat.zero_add] at h0
    -- D[j % len] = D[1] via halt + modular arithmetic
    have hmod : (j % D.length) % 2 = 1 := by
      rw [hlen, Nat.mod_mod_of_dvd _ (dvd_mul_right 2 a)]; exact hj_odd
    have h1 := halt (j % D.length) (Nat.mod_lt _ hlen_pos)
    simp only [hmod] at h1
    -- h1 : D[j % D.length] = D[1], h0 : D[j % D.length] ≠ D[0]
    rw [h1] at h0
    exact Ne.symm h0
  exact alternating_circular_mos D a hlen ha halt hne

/-- Sliding window for j-window L-count: if the element leaving the window
    equals the element entering, the L-count is preserved. -/
private lemma jwindow_slide_count (D : List StepSize) (j i : ℕ)
    (hlen_pos : 0 < D.length) (hj_pos : 0 < j)
    (heq : D[(i + j) % D.length]'(Nat.mod_lt _ hlen_pos) =
           D[i % D.length]'(Nat.mod_lt _ hlen_pos)) :
    ((List.range j).map (fun t =>
      D[(i + 1 + t) % D.length]'(Nat.mod_lt _ hlen_pos))).count .L =
    ((List.range j).map (fun t =>
      D[(i + t) % D.length]'(Nat.mod_lt _ hlen_pos))).count .L := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  set L := D.length
  set f := fun t => D[(i + t) % L]'(Nat.mod_lt _ hlen_pos) with hf_def
  set g := fun t => D[(i + 1 + t) % L]'(Nat.mod_lt _ hlen_pos) with hg_def
  set mid := (List.range j').map g with hmid_def
  -- Window at i: f(0) :: mid (via range_succ_eq_map)
  have hwin_f : (List.range (j' + 1)).map f = f 0 :: mid := by
    conv_lhs => rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    exact List.map_congr_left (fun t _ => by
      simp only [Function.comp, hf_def, hg_def]; congr 2; omega)
  -- Window at i+1: mid ++ [g j'] (via range_succ)
  have hwin_g : (List.range (j' + 1)).map g = mid ++ [g j'] := by
    rw [List.range_succ, List.map_append, List.map_singleton]
  -- f(0) = g(j') from heq
  have hfg : f 0 = g j' := by
    simp only [hf_def, hg_def, Nat.add_zero]
    have h : i + 1 + j' = i + (j' + 1) := by omega
    rw [h]; exact heq.symm
  -- Conclude by permutation: f(0) :: mid ~ mid ++ [g(j')]
  rw [hwin_g, hwin_f, hfg]
  exact (List.perm_append_comm.count_eq StepSize.L).symm

/-- If gcd(j, m) = 1, the map t ↦ (q₀ + t*j) % m surjects onto [0, m). -/
private lemma coprime_surj_mod (j q₀ m : ℕ) [NeZero m]
    (hcop : Nat.Coprime j m) (i : ℕ) (hi : i < m) :
    ∃ t < m, (q₀ + t * j) % m = i := by
  have hbez : (↑j : ZMod m) * ((Nat.gcdA j m : ℤ) : ZMod m) = 1 := by
    have := congr_arg (fun x : ℤ => (x : ZMod m)) (Nat.gcd_eq_gcd_ab j m)
    push_cast at this ⊢; rw [ZMod.natCast_self, zero_mul, add_zero] at this
    rw [hcop.gcd_eq_one, Nat.cast_one] at this; exact this.symm
  set c := ((Nat.gcdA j m : ℤ) : ZMod m)
  have hcj : c * (↑j : ZMod m) = 1 := by rw [mul_comm]; exact hbez
  set t₀ := ZMod.val (((↑i : ZMod m) - (↑q₀ : ZMod m)) * c)
  refine ⟨t₀, ZMod.val_lt _, ?_⟩
  suffices h : (↑(q₀ + t₀ * j) : ZMod m) = (↑i : ZMod m) by
    have := congr_arg ZMod.val h
    simp only [ZMod.val_natCast] at this
    rw [Nat.mod_eq_of_lt hi] at this; exact this
  push_cast; rw [show (t₀ : ZMod m) = ((↑i : ZMod m) - ↑q₀) * c from ZMod.natCast_zmod_val _]
  calc (↑q₀ : ZMod m) + ((↑i - ↑q₀) * c) * ↑j
      = ↑q₀ + (↑i - ↑q₀) * (c * ↑j) := by ring
    _ = ↑q₀ + (↑i - ↑q₀) * 1 := by rw [hcj]
    _ = ↑i := by ring

/-- Composing identifyPair/msToBinary and filtering for .L is the same as
    filtering for ≠ .s on the original list. -/
private lemma msToBinary_filter_L_eq_ne_s (l : List StepSize) :
    ((l.map (fun x => msToBinary (if x = StepSize.L then StepSize.m else x))).filter
      (· == BinaryStep.L)).length =
    (l.filter (· ≠ StepSize.s)).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.filter_cons]
    cases a <;> simp_all [msToBinary]

/-- Single-step advancement of nonSBefore: at position m, the prefix non-.s
    count advances by the singleton filter length, modulo D.length. -/
private lemma nonSBefore_single_step (w : TernaryNecklace n) (m : ℕ) (hm : m < n) :
    let wList := (List.range n).map (fun i => w (↑i : ZMod n))
    let D := orderedDeletion w .s
    ((wList.take ((m + 1) % n)).filter (· ≠ .s)).length % D.length =
      (((wList.take m).filter (· ≠ .s)).length +
       ([w (↑m : ZMod n)].filter (· ≠ .s)).length) % D.length := by
  intro wList D
  have hwLen : wList.length = n := by simp [wList]
  have hm_bound : m < wList.length := hwLen ▸ hm
  have htake_succ : wList.take (m + 1) = wList.take m ++ [wList[m]] :=
    List.take_succ_eq_append_getElem hm_bound
  have hget : wList[m] = w (↑m : ZMod n) := by
    simp only [wList, bind_pure_comp, Functor.map, List.map_map,
      List.getElem_map, List.getElem_range, Function.comp]
  have hnsb_succ : ((wList.take (m + 1)).filter (· ≠ .s)).length =
      ((wList.take m).filter (· ≠ .s)).length +
      ([w (↑m : ZMod n)].filter (· ≠ .s)).length := by
    rw [htake_succ, List.filter_append, List.length_append, hget]
  by_cases hm1 : m + 1 < n
  · rw [Nat.mod_eq_of_lt hm1, hnsb_succ]
  · have hm1_eq : m + 1 = n := by omega
    rw [hm1_eq, Nat.mod_self, List.take_zero, List.filter_nil, List.length_nil]
    have hnsb_n : ((wList.take n).filter (· ≠ .s)).length = D.length := by
      rw [List.take_of_length_le (le_of_eq hwLen)]; rfl
    have : ((wList.take m).filter (· ≠ .s)).length +
        ([w (↑m : ZMod n)].filter (· ≠ .s)).length = D.length := by
      rw [← hnsb_succ, hm1_eq, hnsb_n]
    rw [this, Nat.mod_self, Nat.zero_mod]

/-- Extending a slice by one position adds the singleton filter length. -/
private lemma slice_filter_succ (w : TernaryNecklace n) (r k : ℕ) :
    ((Necklace.slice w r (r + (k + 1))).filter (· ≠ .s)).length =
      ((Necklace.slice w r (r + k)).filter (· ≠ .s)).length +
      ([w (↑(r + k) : ZMod n)].filter (· ≠ .s)).length := by
  simp only [Necklace.slice, show r + (k + 1) - r = k + 1 from by omega,
             show r + k - r = k from by omega, bind_pure_comp, Functor.map, List.map_map]
  rw [List.range_succ, List.map_append, List.map_singleton,
      List.filter_append, List.length_append]
  simp only [Function.comp, Nat.cast_add]

/-- Extending a slice by one position appends the next necklace entry. -/
private lemma slice_append_singleton (w : TernaryNecklace n) (r k : ℕ) :
    Necklace.slice w r (r + (k + 1)) =
      Necklace.slice w r (r + k) ++ [w (↑(r + k) : ZMod n)] := by
  simp only [Necklace.slice, show r + (k + 1) - r = k + 1 from by omega,
             show r + k - r = k from by omega, bind_pure_comp, Functor.map, List.map_map]
  rw [List.range_succ, List.map_append, List.map_singleton]
  simp only [Function.comp, Nat.cast_add]

/-- General list fact: if `l[k]` passes the filter, then the element at index
    `(l.take k).filter(p).length` in `l.filter p` is `l[k]`. -/
private lemma getElem_filter_prefix {α : Type*} (l : List α) (p : α → Bool) (k : ℕ)
    (hk : k < l.length) (hpk : p (l[k]) = true)
    (hm : ((l.take k).filter p).length < (l.filter p).length) :
    (l.filter p)[((l.take k).filter p).length] = l[k] := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a t ih =>
    cases k with
    | zero =>
      simp only [List.take_zero, List.filter_nil, List.length_nil, List.getElem_cons_zero] at *
      simp [List.filter_cons_of_pos hpk]
    | succ k' =>
      simp only [List.getElem_cons_succ] at hpk
      by_cases hpa : p a = true
      · simp only [List.take_succ_cons, List.filter_cons_of_pos hpa, List.length_cons] at hk hm ⊢
        simp only [List.getElem_cons_succ]
        exact ih k' (by omega) hpk (by omega)
      · simp only [List.take_succ_cons, List.filter_cons_of_neg hpa, List.length_cons] at hk hm ⊢
        exact ih k' (by omega) hpk hm

/-- General list fact: if `l[k]` passes the filter, then the prefix count is strictly less
    than the total filtered length. -/
private lemma length_filter_take_lt {α : Type*} (l : List α) (p : α → Bool) (k : ℕ)
    (hk : k < l.length) (hpk : p (l[k]) = true) :
    ((l.take k).filter p).length < (l.filter p).length := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a t ih =>
    cases k with
    | zero =>
      simp only [List.take_zero, List.filter_nil, List.length_nil, List.getElem_cons_zero] at *
      rw [List.filter_cons_of_pos hpk]; simp [List.length_cons]
    | succ k' =>
      simp only [List.getElem_cons_succ] at hpk
      by_cases hpa : p a = true
      · simp only [List.take_succ_cons, List.filter_cons_of_pos hpa, List.length_cons] at hk ⊢
        exact Nat.succ_lt_succ (ih k' (by omega) hpk)
      · simp only [List.take_succ_cons, List.filter_cons_of_neg hpa, List.length_cons] at hk ⊢
        exact ih k' (by omega) hpk

/-- The m-th entry of D (= wList.filter (· ≠ .s)) at position p equals w(↑p),
    when m = #{non-.s entries before position p} and w(↑p) ≠ .s. -/
private lemma orderedDeletion_getElem
    (w : TernaryNecklace n) (p : ℕ) (hp : p < n) (hw : w (↑p : ZMod n) ≠ .s) :
    let wList := (List.range n).map (fun i => w (↑i : ZMod n))
    let D := orderedDeletion w .s
    let m := ((wList.take p).filter (· ≠ .s)).length
    (hm : m < D.length) → D[m] = w (↑p : ZMod n) := by
  intro wList D m hm
  have hwLen : wList.length = n := by simp [wList]
  have hp' : p < wList.length := hwLen ▸ hp
  have hget : wList[p]'hp' = w (↑p : ZMod n) := by
    simp only [wList, bind_pure_comp, Functor.map, List.map_map,
      List.getElem_map, List.getElem_range, Function.comp]
  show (wList.filter (· ≠ .s))[m] = w (↑p : ZMod n)
  rw [← hget]
  exact getElem_filter_prefix wList (fun x => decide (x ≠ StepSize.s)) p hp'
    (decide_eq_true (by rw [hget]; exact hw)) hm

/-- The prefix non-.s count before any non-.s position is strictly less than D.length. -/
private lemma prefix_filter_lt_D_length
    (w : TernaryNecklace n) (p : ℕ) (hp : p < n) (hw : w (↑p : ZMod n) ≠ .s) :
    let wList := (List.range n).map (fun i => w (↑i : ZMod n))
    ((wList.take p).filter (· ≠ .s)).length < (orderedDeletion w .s).length := by
  intro wList
  have hwLen : wList.length = n := by simp [wList]
  have hp' : p < wList.length := hwLen ▸ hp
  have hget : wList[p]'hp' = w (↑p : ZMod n) := by
    simp only [wList, bind_pure_comp, Functor.map, List.map_map,
      List.getElem_map, List.getElem_range, Function.comp]
  show ((wList.take p).filter (· ≠ .s)).length < (wList.filter (· ≠ .s)).length
  exact length_filter_take_lt wList (fun x => decide (x ≠ StepSize.s)) p hp'
    (decide_eq_true (by rw [hget]; exact hw))

/-- The prefix non-.s count advances by j per k₀-window (mod 2a).
    If k consecutive positions starting at r have j non-.s entries,
    then nonSBefore((r+k) % n) ≡ nonSBefore(r) + j (mod D.length). -/
lemma nonSBefore_advance
    (w : TernaryNecklace n) (r k j : ℕ) (hk_le : k ≤ n) :
    let wList := (List.range n).map (fun i => w (↑i : ZMod n))
    let D := orderedDeletion w .s
    j = ((Necklace.slice w r (r + k)).filter (· ≠ .s)).length →
    ((wList.take ((r + k) % n)).filter (· ≠ .s)).length % D.length =
      (((wList.take (r % n)).filter (· ≠ .s)).length + j) % D.length := by
  intro wList D hj; rw [hj]
  suffices h : ∀ k', k' ≤ n →
      ((wList.take ((r + k') % n)).filter (· ≠ .s)).length % D.length =
      (((wList.take (r % n)).filter (· ≠ .s)).length +
       ((Necklace.slice w r (r + k')).filter (· ≠ .s)).length) % D.length from
    h k hk_le
  intro k'
  induction k' with
  | zero =>
    intro _
    have hslice_zero : ((Necklace.slice w r (r + 0)).filter (· ≠ .s)).length = 0 := by
      simp [Necklace.slice]
    rw [hslice_zero]; simp
  | succ m ih =>
    intro hm_le
    rw [slice_filter_succ]
    -- Modular step identity: (r + (m + 1)) % n = ((r + m) % n + 1) % n
    have hmod_step : (r + (m + 1)) % n = ((r + m) % n + 1) % n := by
      conv_lhs => rw [show r + (m + 1) = r + m + 1 from by ring, Nat.add_mod]
      conv_rhs =>
        rw [Nat.add_mod, Nat.mod_eq_of_lt (Nat.mod_lt (r + m) (Nat.pos_of_neZero n))]
    rw [hmod_step]
    -- ZMod cast: ↑((r + m) % n) = ↑(r + m) in ZMod n
    have hcast_eq : w (↑((r + m) % n) : ZMod n) = w (↑(r + m) : ZMod n) := by
      congr 1
      conv_rhs => rw [← Nat.div_add_mod (r + m) n]
      push_cast; simp []
    -- Single step at position (r + m) % n
    have hm_lt : (r + m) % n < n := Nat.mod_lt _ (Nat.pos_of_neZero n)
    have hstep := nonSBefore_single_step w ((r + m) % n) hm_lt
    rw [hstep]
    -- Match singleton filter terms via ZMod cast
    rw [hcast_eq]
    -- Apply IH
    have ih' := ih (by omega)
    -- Combine via modular arithmetic
    conv_lhs => rw [Nat.add_mod]
    rw [ih']
    rw [← Nat.add_mod]
    congr 1; omega

/-- **Geometric bridge**: The j-window L-count in the ordered deletion D at position
    `nonSBefore(r)` equals `(kStepVector w r k .L).natAbs`, where `nonSBefore(r)` is
    the number of non-.s entries before position `r` in the linear reading of `w`.

    Both sides count the number of .L entries in positions r, r+1, ..., r+k-1 of the necklace.
    Since .L ≠ .s, filtering out .s entries preserves the .L count. -/
lemma orderedDeletion_window_Lcount
    (w : TernaryNecklace n) (r k j : ℕ) (hDlen_pos : 0 < (orderedDeletion w .s).length)
    (hk_le : k ≤ n) :
    let wList := (List.range n).map (fun i => w (↑i : ZMod n))
    let D := orderedDeletion w .s
    let q := ((wList.take (r % n)).filter (· ≠ .s)).length
    j = ((Necklace.slice w r (r + k)).filter (· ≠ .s)).length →
    ((List.range j).map (fun t =>
      D[(q + t) % D.length]'(Nat.mod_lt _ hDlen_pos))).count .L =
    (Necklace.kStepVector w r k .L).natAbs := by
  intro wList D q hj; subst hj
  -- Both sides count .L in the k-window. Prove by induction on k.
  suffices h : ∀ k', k' ≤ n →
      ((List.range ((Necklace.slice w r (r + k')).filter (· ≠ .s)).length).map (fun t =>
        D[(q + t) % D.length]'(Nat.mod_lt _ hDlen_pos))).count .L =
      (Necklace.slice w r (r + k')).count .L from by
    rw [h k hk_le]
    -- RHS: (kStepVector w r k .L).natAbs = (slice w r (r+k)).count .L
    simp only [Necklace.kStepVector, ZVector.ofList, Int.natAbs_natCast,
      ← List.count_eq_length_filter]
  intro k'
  induction k' with
  | zero => intro _; simp [Necklace.slice]
  | succ k' ih =>
    intro hk'_le
    rw [slice_filter_succ, slice_append_singleton]
    by_cases hw : w (↑(r + k') : ZMod n) = .s
    · -- w(r+k') = .s: filter doesn't grow, count doesn't change
      have hfilt0 : ([w (↑(r + k') : ZMod n)].filter (· ≠ .s)).length = 0 := by
        conv_lhs => rw [hw]; simp
      rw [hfilt0, Nat.add_zero, ih (by omega), List.count_append]
      simp [show w ((↑r : ZMod n) + ↑k') = .s from by rw [← Nat.cast_add]; exact hw]
    · -- w(r+k') ≠ .s: filter grows by 1, D window extends by one entry
      have hδ : ([w (↑(r + k') : ZMod n)].filter (· ≠ .s)).length = 1 := by
        have h := decide_eq_true hw
        simp only [List.filter_cons, h, ite_true, List.filter_nil,
          List.length_cons, List.length_nil]
      rw [hδ, List.range_succ, List.map_append, List.map_singleton,
          List.count_append, List.count_append, ih (by omega)]
      congr 1
      -- D[(q + j_old) % D.length] = w(↑(r+k')), so singleton counts match
      have hD_eq : D[(q + ((Necklace.slice w r (r + k')).filter (· ≠ .s)).length) %
          D.length]'(Nat.mod_lt _ hDlen_pos) = w (↑(r + k') : ZMod n) := by
        -- Use nonSBefore_advance + orderedDeletion_getElem
        set j_old := ((Necklace.slice w r (r + k')).filter (· ≠ .s)).length
        set p := (r + k') % n with hp_def
        have hp_lt : p < n := Nat.mod_lt _ (Nat.pos_of_neZero n)
        have hcast : w (↑p : ZMod n) = w (↑(r + k') : ZMod n) := by
          show w (↑((r + k') % n) : ZMod n) = w (↑(r + k') : ZMod n)
          congr 1
          conv_rhs => rw [← Nat.div_add_mod (r + k') n]
          push_cast; simp []
        have hw_p : w (↑p : ZMod n) ≠ .s := by rw [hcast]; exact hw
        have hm_lt := prefix_filter_lt_D_length w p hp_lt hw_p
        have hge := orderedDeletion_getElem w p hp_lt hw_p hm_lt
        -- hge : D[nonSBefore(p)] = w(↑p)
        rw [hcast] at hge
        -- hge : D[nonSBefore(p)] = w(↑(r+k'))
        have hadv := (nonSBefore_advance w r k' j_old (by omega : k' ≤ n)) rfl
        -- hadv : nonSBefore(p) % D.length = (q + j_old) % D.length
        rw [Nat.mod_eq_of_lt hm_lt] at hadv
        -- hadv : nonSBefore(p) = (q + j_old) % D.length
        -- Transport the getElem index: indices are equal, bounds are proof-irrelevant
        have heq_idx : D[(q + j_old) % D.length]'(Nat.mod_lt _ hDlen_pos) =
            D[((wList.take p).filter (· ≠ .s)).length]'hm_lt := by
          congr 1; exact hadv.symm
        exact heq_idx.trans hge
      rw [hD_eq]

set_option maxHeartbeats 400000 in
/-- The ordered deletion of .s from the permuted necklace gives a circular MOS.
    This is the key step in proving AS → odd-regular.

    **Proof**: Uses the generator of the template MOS B to show that D alternates.
    The AS alternation in stacking order transfers to j-step alternation in D
    (where j = generator's .L count), and since gcd(j, 2a) = 1, D has period 2. -/
private lemma as_odd_deletion_mos (w : TernaryNecklace n)
    (_ : Necklace.isPrimitive w) (htern : isTernary w)
    (hodd : n % 2 = 1)
    (k₀ r₀ : ℕ) (seq : Fin 2 → ZVector StepSize)
    (hk₀_lt : k₀ < n)
    (hcop_as : Nat.Coprime k₀ n)
    (hseq_as : ∀ i : Fin (n - 1),
      Necklace.kStepVector w (r₀ + i.val * k₀) k₀ =
        seq ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩)
    (hclose_as : ∀ j : Fin 2,
      Necklace.kStepVector w (r₀ + (n - 1) * k₀) k₀ ≠ seq j)
    (σ : Equiv.Perm StepSize)
    (x y : StepSize) (hxy : x ≠ y)
    (hσx : σ x = .L) (hσy : σ y = .m)
    (hcount_eq : Necklace.count w x = Necklace.count w y)
    (hmos : isPartialPairwiseMOS w x y)
    (hcancel : seq ⟨0, by omega⟩ x - seq ⟨1, by omega⟩ x +
      (seq ⟨0, by omega⟩ y - seq ⟨1, by omega⟩ y) = 0)
    (hx_ne : seq ⟨0, by omega⟩ x ≠ seq ⟨1, by omega⟩ x)
    (hz_same : ∀ z : StepSize, z ≠ x → z ≠ y →
      seq ⟨0, by omega⟩ z = seq ⟨1, by omega⟩ z) :
    isPartialDeletionMOS (Necklace.applyPerm σ w) .s := by
  set w' := Necklace.applyPerm σ w
  set D := TernaryNecklace.orderedDeletion w' .s
  set a := Necklace.count w x
  have ha_pos : a > 0 := count_pos_of_isTernary w htern x
  -- Find the third step size z₀
  obtain ⟨z₀, hz₀x, hz₀y⟩ : ∃ z₀ : StepSize, z₀ ≠ x ∧ z₀ ≠ y := by
    cases x <;> cases y <;> simp_all
    · exact ⟨.s, by decide, by decide⟩
    · exact ⟨.m, by decide, by decide⟩
    · exact ⟨.s, by decide, by decide⟩
    · exact ⟨.L, by decide, by decide⟩
    · exact ⟨.m, by decide, by decide⟩
    · exact ⟨.L, by decide, by decide⟩
  -- σ maps z₀ to .s (since σ is bijective and .L, .m are taken)
  have hσz₀ : σ z₀ = .s := by
    have h1 : σ z₀ ≠ .L := fun h => hz₀x (σ.injective (h.trans hσx.symm))
    have h2 : σ z₀ ≠ .m := fun h => hz₀y (σ.injective (h.trans hσy.symm))
    cases hv : σ z₀ <;> simp_all
  have hσ_symm_s : σ.symm .s = z₀ := by
    rw [← hσz₀]; exact σ.symm_apply_apply z₀
  -- D.length = 2 * a
  have hDlen : D.length = 2 * a := by
    have hdel := orderedDeletion_length w' .s
    have hcs : Necklace.count w' .s = Necklace.count w z₀ := by
      rw [count_applyPerm_eq, hσ_symm_s]
    have hn_eq : n = 2 * a + Necklace.count w z₀ := by
      change n = 2 * Necklace.count w x + Necklace.count w z₀
      have htotal := count_total w
      cases x <;> cases y <;> cases z₀ <;>
        first
        | exact absurd rfl hxy
        | exact absurd rfl hz₀x
        | exact absurd rfl hz₀y
        | omega
    rw [hcs] at hdel; linarith
  /- Key step: D has the circular MOS property.
     D entries are binary (.L or .m). Using the template MOS generator theory,
     we construct j coprime to 2a with D[(i+j)%len] ≠ D[i] for all i. -/
  -- D entries are .L or .m (since we filter out .s)
  have hmem_ne_s : ∀ a ∈ D, a ≠ .s := fun a ha => by
    simp only [D, TernaryNecklace.orderedDeletion, List.mem_filter,
      decide_eq_true_eq] at ha; exact ha.2
  have hbin : ∀ i, (hi : i < D.length) → D[i] = .L ∨ D[i] = .m := by
    intro i hi
    have hne : D[i] ≠ .s := hmem_ne_s _ (List.mem_iff_getElem.mpr ⟨i, hi, rfl⟩)
    cases h : D[i] with
    | L => exact Or.inl rfl
    | m => exact Or.inr rfl
    | s => exact absurd h hne
  -- Construct j coprime to 2a with the flip property
  obtain ⟨j, hcop, hflip⟩ : ∃ j : ℕ, Nat.Coprime j (2 * a) ∧
      ∀ i, (hi : i < D.length) →
        D[(i + j) % D.length]'(Nat.mod_lt _ (by omega)) ≠ D[i] := by
    -- Step 1: Build template MOS B = identifiedToBinary(identifyPair w' .L .m)
    have hmos_w' : isPartialPairwiseMOS w' .L .m := by
      have := isPartialPairwiseMOS_applyPerm σ w x y hmos
      rwa [hσx, hσy] at this
    have hcountL_w' : Necklace.count w' .L = a := by
      change Necklace.count (Necklace.applyPerm σ w) .L = a
      rw [count_applyPerm_eq, show σ.symm .L = x from by rw [← hσx, σ.symm_apply_apply]]
    have hcountm_w' : Necklace.count w' .m = a := by
      change Necklace.count (Necklace.applyPerm σ w) .m = a
      rw [count_applyPerm_eq, show σ.symm .m = y from by rw [← hσy, σ.symm_apply_apply]]
      exact hcount_eq.symm
    have hcounts_w' : Necklace.count w' .s = Necklace.count w z₀ := by
      change Necklace.count (Necklace.applyPerm σ w) .s = _
      rw [count_applyPerm_eq, hσ_symm_s]
    set b := Necklace.count w z₀ with hb_def
    have hb_pos : b > 0 := count_pos_of_isTernary w htern z₀
    set B := identifiedToBinary (TernaryNecklace.identifyPair w' .L .m) with hB_def
    have hB_mos : BinaryNecklace.isMOS B :=
      identifiedToBinary_isMOS w' hcountL_w' hcountm_w' hcounts_w' ha_pos hb_pos hmos_w'
    have hcountL_B : Necklace.count B .L = 2 * a :=
      identifiedToBinary_count_L w' hcountL_w' hcountm_w'
    have hcounts_B : Necklace.count B .s = b :=
      identifiedToBinary_count_s w' hcounts_w'
    -- Key stacking: k₀-step vectors of B at all stacking positions are equal
    have hk₀_pos : 0 < k₀ := by
      rcases Nat.eq_zero_or_pos k₀ with rfl | h
      · simp [Nat.Coprime] at hcop_as
        linarith [count_pos_of_isTernary w htern .L,
                  count_pos_of_isTernary w htern .m, count_total w]
      · exact h
    have hstack_B : ∀ t : ℕ, t < n - 1 →
        Necklace.kStepVector B (r₀ + t * k₀) k₀ =
        Necklace.kStepVector B r₀ k₀ := by
      intro t ht
      set w_id := TernaryNecklace.identifyPair w' .L .m with hw_id_def
      have hσ_symm_L : σ.symm .L = x := by rw [← hσx, σ.symm_apply_apply]
      have hσ_symm_m : σ.symm .m = y := by rw [← hσy, σ.symm_apply_apply]
      have hchain : ∀ i : ℕ, Necklace.kStepVector w_id i k₀ =
          ZVector.identifyPair (ZVector.applyPerm σ
            (Necklace.kStepVector w i k₀)) .L .m := by
        intro i
        show Necklace.kStepVector (TernaryNecklace.identifyPair
          (Necklace.applyPerm σ w) .L .m) i k₀ = _
        rw [identifyPair_kStepVector _ .L .m (by decide) i k₀,
            kStepVector_applyPerm]
      have hstack_w_id : Necklace.kStepVector w_id (r₀ + t * k₀) k₀ =
          Necklace.kStepVector w_id r₀ k₀ := by
        have h0 : Necklace.kStepVector w r₀ k₀ = seq ⟨0, by omega⟩ := by
          have := hseq_as ⟨0, by omega⟩; simpa using this
        rw [hchain (r₀ + t * k₀), hchain r₀, hseq_as ⟨t, ht⟩, h0]
        rcases Nat.mod_two_eq_zero_or_one t with h_mod | h_mod
        · simp only [h_mod]
        · simp only [h_mod]; funext a_step
          simp only [ZVector.identifyPair]
          by_cases haL : a_step = .L
          · simp [haL]
          · by_cases ham : a_step = .m
            · simp only [ham, if_neg (show StepSize.m ≠ StepSize.L from by decide), ite_true,
                ZVector.applyPerm, Function.comp, hσ_symm_L, hσ_symm_m]
              linarith
            · have has : a_step = .s := by
                rcases a_step with _ | _ | _ <;> simp_all
              simp only [ZVector.applyPerm, Function.comp, has, hσ_symm_s]
              exact (hz_same z₀ hz₀x hz₀y).symm
      show Necklace.kStepVector (msToBinary ∘ w_id) (r₀ + t * k₀) k₀ =
           Necklace.kStepVector (msToBinary ∘ w_id) r₀ k₀
      exact kStepVector_comp_eq_of_kStepVector_eq w_id msToBinary _ _ k₀ hstack_w_id
    -- Step 2: B is primitive (by contradiction using mos_uniform_kstep_absurd)
    have hB_prim : Necklace.isPrimitive B := by
      by_contra h_not_prim
      set pLen := (Necklace.period B).length with hpLen_def
      have hpLen_pos : 0 < pLen := period_length_pos B
      have hpLen_dvd : pLen ∣ n := period_dvd_length B
      have hpLen_lt : pLen < n := by
        have := Necklace.period_length_le_n B
        unfold Necklace.isPrimitive at h_not_prim; omega
      have hcop_pLen : Nat.Coprime k₀ pLen := hcop_as.coprime_dvd_right hpLen_dvd
      -- kStepVector B has period pLen (from period_pointwise)
      have hkstep_period : ∀ (m₁ m₂ : ℕ), m₁ % pLen = m₂ % pLen →
          Necklace.kStepVector B m₁ k₀ = Necklace.kStepVector B m₂ k₀ := by
        intro m₁ m₂ hmod
        have hptwise : ∀ j, B (↑(m₁ + j) : ZMod n) = B (↑(m₂ + j) : ZMod n) := by
          intro j
          have : (m₁ + j) % pLen = (m₂ + j) % pLen := by
            rw [Nat.add_mod m₁, hmod, ← Nat.add_mod]
          exact (period_pointwise B (m₁ + j)).trans
            (by rw [this]; exact (period_pointwise B (m₂ + j)).symm)
        unfold Necklace.kStepVector; congr 1
        apply List.ext_getElem
        · simp [Necklace.slice_length]
        · intro i hi₁ hi₂
          simp only [Necklace.slice, bind_pure_comp, Functor.map,
            show m₁ + k₀ - m₁ = k₀ from by omega,
            show m₂ + k₀ - m₂ = k₀ from by omega,
            List.getElem_map, List.getElem_range, ← Nat.cast_add]
          exact hptwise i
      -- All kStepVectors of B equal kStepVector B r₀ k₀
      have hall_eq_r₀ : ∀ m : ℕ, Necklace.kStepVector B m k₀ =
          Necklace.kStepVector B r₀ k₀ := by
        intro m
        haveI : NeZero pLen := ⟨by omega⟩
        -- Bezout: k₀ * gcdA ≡ 1 (mod pLen)
        have hbez : (↑(Nat.gcd k₀ pLen) : ZMod pLen) =
            (↑k₀ : ZMod pLen) * ((Nat.gcdA k₀ pLen : ℤ) : ZMod pLen) := by
          have := congr_arg (fun x : ℤ => (x : ZMod pLen)) (Nat.gcd_eq_gcd_ab k₀ pLen)
          push_cast at this; rwa [ZMod.natCast_self, zero_mul, add_zero] at this
        have hk₀_inv : (↑k₀ : ZMod pLen) * ((Nat.gcdA k₀ pLen : ℤ) : ZMod pLen) = 1 := by
          rw [← hbez, hcop_pLen.gcd_eq_one]; simp
        set c := ((Nat.gcdA k₀ pLen : ℤ) : ZMod pLen) with hc_def
        set t₀ := ZMod.val (((↑m : ZMod pLen) - (↑r₀ : ZMod pLen)) * c)
        have ht₀_lt : t₀ < pLen := ZMod.val_lt _
        have ht₀_valid : t₀ < n - 1 := by omega
        -- (r₀ + t₀ * k₀) ≡ m (mod pLen)
        have hmod_eq : (r₀ + t₀ * k₀) % pLen = m % pLen := by
          suffices h : (↑(r₀ + t₀ * k₀) : ZMod pLen) = (↑m : ZMod pLen) by
            have := congr_arg ZMod.val h
            simp only [ZMod.val_natCast] at this; omega
          push_cast; rw [show (t₀ : ZMod pLen) = ((↑m : ZMod pLen) - ↑r₀) * c from
            ZMod.natCast_zmod_val _]
          have hck₀ : c * (↑k₀ : ZMod pLen) = 1 := by rw [mul_comm]; exact hk₀_inv
          calc (↑r₀ : ZMod pLen) + ((↑m - ↑r₀) * c) * ↑k₀
              = ↑r₀ + (↑m - ↑r₀) * (c * ↑k₀) := by ring
            _ = ↑r₀ + (↑m - ↑r₀) * 1 := by rw [hck₀]
            _ = ↑m := by ring
        calc Necklace.kStepVector B m k₀
            = Necklace.kStepVector B (r₀ + t₀ * k₀) k₀ :=
                hkstep_period m (r₀ + t₀ * k₀) hmod_eq.symm
          _ = Necklace.kStepVector B r₀ k₀ := hstack_B t₀ ht₀_valid
      have hall : ∀ i : ℕ, Necklace.kStepVector B i k₀ =
          Necklace.kStepVector B 0 k₀ := by
        intro i; rw [hall_eq_r₀ i, hall_eq_r₀ 0]
      exact mos_uniform_kstep_absurd B hB_mos k₀ hk₀_pos hcop_as hall
    -- Step 3: Coprime counts (from primitive + MOS)
    have hcop_counts : Nat.Coprime (2 * a) b := by
      have := primitive_mos_coprime_counts B hB_mos hB_prim
      rwa [hcountL_B, hcounts_B] at this
    -- Step 4: The k₀-step vector of B is a generator (since it has (n-1,1) split)
    set g₀ := Necklace.kStepVector B r₀ k₀ with hg₀_def
    have hprim_eq : (Necklace.period B).length = n := hB_prim
    have hg₀_count : countKStepVectorPerPeriod B k₀ g₀ =
        (Necklace.period B).length - 1 := by
      -- Bezout inverse of k₀ mod n
      have hbez : (↑(Nat.gcd k₀ n) : ZMod n) =
          (↑k₀ : ZMod n) * ((Nat.gcdA k₀ n : ℤ) : ZMod n) := by
        have := congr_arg (fun x : ℤ => (x : ZMod n)) (Nat.gcd_eq_gcd_ab k₀ n)
        push_cast at this; rwa [ZMod.natCast_self, zero_mul, add_zero] at this
      have hk₀_inv : (↑k₀ : ZMod n) * ((Nat.gcdA k₀ n : ℤ) : ZMod n) = 1 := by
        rw [← hbez, hcop_as.gcd_eq_one]; simp
      set c := ((Nat.gcdA k₀ n : ℤ) : ZMod n) with hc_def
      have hck₀ : c * (↑k₀ : ZMod n) = 1 := by rw [mul_comm]; exact hk₀_inv
      -- For any m < n, find t < n with m = (r₀ + t*k₀) % n
      have hRecover : ∀ m : ℕ, m < n →
          ∃ t, t < n ∧ m = (r₀ + t * k₀) % n := by
        intro m hm
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
      -- Bad position: the (n-1)-th stacking position
      set j₁ := (r₀ + (n - 1) * k₀) % n with hj₁_def
      have hj₁_lt : j₁ < n := Nat.mod_lt _ (by omega)
      -- Bad: kStepVector B j₁ k₀ ≠ g₀ (otherwise all would be uniform)
      have hbad : Necklace.kStepVector B j₁ k₀ ≠ g₀ := by
        intro h_eq
        have hall_g₀ : ∀ t, t < n →
            Necklace.kStepVector B (r₀ + t * k₀) k₀ = g₀ := by
          intro t ht
          by_cases ht' : t < n - 1
          · exact hstack_B t ht'
          · rw [show t = n - 1 from by omega, ← kStepVector_mod_n]; exact h_eq
        have hall : ∀ i : ℕ, Necklace.kStepVector B i k₀ =
            Necklace.kStepVector B 0 k₀ := by
          suffices h : ∀ i : ℕ, Necklace.kStepVector B i k₀ = g₀ by
            intro i; rw [h i, h 0]
          intro i
          obtain ⟨t, ht_lt, hi_eq⟩ := hRecover (i % n) (Nat.mod_lt i (by omega))
          calc Necklace.kStepVector B i k₀
              = Necklace.kStepVector B (i % n) k₀ :=
                  (kStepVector_mod_n B i k₀).symm
            _ = Necklace.kStepVector B ((r₀ + t * k₀) % n) k₀ := by rw [hi_eq]
            _ = Necklace.kStepVector B (r₀ + t * k₀) k₀ :=
                  kStepVector_mod_n B _ k₀
            _ = g₀ := hall_g₀ t ht_lt
        exact mos_uniform_kstep_absurd B hB_mos k₀ hk₀_pos hcop_as hall
      -- Good: all other positions give g₀
      have hgood : ∀ m, m < n → m ≠ j₁ →
          Necklace.kStepVector B m k₀ = g₀ := by
        intro m hm hm_ne
        obtain ⟨t, ht_lt, hm_eq⟩ := hRecover m hm
        have ht_ne : t ≠ n - 1 := by
          intro h; rw [h] at hm_eq; exact hm_ne hm_eq
        rw [hm_eq, kStepVector_mod_n]
        exact hstack_B t (by omega)
      exact countKStepVector_eq_of_unique_mismatch B hB_prim g₀ k₀ j₁ hj₁_lt hbad hgood
    have hg₀_gen : IsGenerator B g₀ :=
      p_minus_one_occurrences_implies_generator B hB_mos.1 g₀ k₀
        hk₀_pos (by rw [hprim_eq]; exact hk₀_lt) hg₀_count
    -- Step 5: j = |g₀(.L)| is coprime to 2a
    set j := (g₀ .L).natAbs with hj_def
    have hcop : Nat.Coprime j (2 * a) :=
      generator_L_coprime B hB_mos hB_prim g₀ hg₀_gen a b hcop_counts hcountL_B hcounts_B
    -- Step 6: Flip property from running count argument
    have hflip : ∀ i, (hi : i < D.length) →
        D[(i + j) % D.length]'(Nat.mod_lt _ (by omega)) ≠ D[i] := by
      haveI : NeZero (2 * a) := ⟨by omega⟩
      -- j is odd (since gcd(j, 2a) = 1 and 2 | 2a)
      have hj_odd : j % 2 = 1 := by
        by_contra h
        have hj_even : 2 ∣ j := Nat.dvd_of_mod_eq_zero (by omega)
        have h2 := Nat.dvd_gcd hj_even (dvd_mul_right 2 a)
        rw [hcop] at h2; omega
      /- Parity witness: g encodes the j-step L-count parity of D.
         (1) g flips at every j-step (from AS → orderedDeletion bridge).
         (2) D[i]=D[(i+j)%len] ⟹ g stable at i→i+1 (sliding window). -/
      -- j > 0 from coprimality
      have hj_pos : 0 < j := by
        by_contra h; push_neg at h
        have : j = 0 := by omega
        simp [this, Nat.Coprime] at hcop
      -- j-window L-count on D (ℕ-indexed)
      set jWLc : ℕ → ℕ := fun i =>
        ((List.range j).map (fun t =>
          D[(i + t) % D.length]'(Nat.mod_lt _ (by omega)))).count .L
        with hjWLc_def
      -- Modular reduction: jWLc (i % D.length) = jWLc i
      have hjWLc_mod : ∀ i, jWLc (i % D.length) = jWLc i := by
        intro i; simp only [jWLc]; congr 1
        apply List.ext_getElem (by simp)
        intro idx h₁ h₂
        simp only [List.getElem_map, List.getElem_range]; congr 1
        rw [Nat.add_mod (i % D.length) idx D.length,
            Nat.mod_mod_of_dvd _ (dvd_refl D.length), ← Nat.add_mod]
      -- Stacking correspondence
      set v₀ := (seq ⟨0, by omega⟩ x).natAbs with hv₀_def
      set v₁ := (seq ⟨1, by omega⟩ x).natAbs with hv₁_def
      have hstacking : ∃ q₀ : ℕ, ∀ t, t < 2 * a →
          jWLc ((q₀ + t * j) % (2 * a)) =
            if t % 2 = 0 then v₀ else v₁ := by
        -- 2a ≤ n - 1 (since n = 2a + b with b ≥ 1)
        have h2a_le : 2 * a ≤ n - 1 := by
          have h : D.length + Necklace.count w' .s = n := orderedDeletion_length w' .s
          rw [hDlen, hcounts_w'] at h; omega
        -- σ.symm .L = x
        have hσ_symm_L : σ.symm .L = x := by
          rw [← hσx]; exact σ.symm_apply_apply x
        -- The L-count in k₀-step slice of w' alternates between v₀ and v₁
        have h_kstep_L : ∀ t, t < n - 1 →
            (Necklace.kStepVector w' (r₀ + t * k₀) k₀ .L).natAbs =
              if t % 2 = 0 then v₀ else v₁ := by
          intro t ht
          change (Necklace.kStepVector (Necklace.applyPerm σ w) _ _ .L).natAbs = _
          rw [kStepVector_applyPerm]
          simp only [ZVector.applyPerm_apply, hσ_symm_L]
          have h_seq := hseq_as ⟨t, ht⟩
          rw [h_seq]
          rcases Nat.mod_two_eq_zero_or_one t with h | h <;> simp [h, hv₀_def, hv₁_def]
        -- Deletion bridge: j-window L-count in D = L-count in k₀-step slice.
        -- Deleting .s from k₀-step windows of w' gives consecutive j-windows in D,
        -- since each window has j non-.s entries and they tile the necklace in order.
        have h_deletion_bridge : ∃ q₀ : ℕ, ∀ t, t < 2 * a →
            jWLc ((q₀ + t * j) % (2 * a)) =
              (Necklace.kStepVector w' (r₀ + t * k₀) k₀ .L).natAbs := by
          have hDlen_pos :0 < D.length := by rw [hDlen]; omega
          set wList' := (List.range n).map (fun i => w' (↑i : ZMod n)) with hwList'_def
          set q₀' := ((wList'.take (r₀ % n)).filter (· ≠ StepSize.s)).length
            with hq₀'_def
          -- General hslice: non-.s count in each perfect k₀-window equals j
          have hslice_gen : ∀ s, s < n - 1 →
              j = ((Necklace.slice w' (r₀ + s * k₀)
                  (r₀ + s * k₀ + k₀)).filter (· ≠ StepSize.s)).length := by
            intro s hs
            have h1 : j = (Necklace.kStepVector B (r₀ + s * k₀) k₀
                BinaryStep.L).natAbs := by
              rw [show Necklace.kStepVector B (r₀ + s * k₀) k₀ = g₀
                from hstack_B s hs]
            rw [h1]
            change ((Necklace.slice B (r₀ + s * k₀) (r₀ + s * k₀ + k₀)).filter
              (· == BinaryStep.L)).length = _
            have hslice_eq : Necklace.slice B (r₀ + s * k₀) (r₀ + s * k₀ + k₀) =
                (Necklace.slice w' (r₀ + s * k₀) (r₀ + s * k₀ + k₀)).map
                  (fun x => msToBinary
                    (if x = StepSize.L then StepSize.m else x)) := by
              unfold Necklace.slice
              simp only [hB_def, identifiedToBinary, List.map_map]
              congr 1
            rw [hslice_eq]
            exact msToBinary_filter_L_eq_ne_s _
          refine ⟨q₀', fun t ht => ?_⟩
          set nb_t :=
            ((wList'.take ((r₀ + t * k₀) % n)).filter
              (· ≠ StepSize.s)).length with hnb_t_def
          -- Sub-fact 1: the non-.s count in each perfect k₀-window equals j
          have hslice_j : j = ((Necklace.slice w' (r₀ + t * k₀)
              (r₀ + t * k₀ + k₀)).filter (· ≠ StepSize.s)).length :=
            hslice_gen t (by omega)
          -- Sub-fact 2: prefix telescope (nonSBefore advances by j per window)
          have htelescope : nb_t % D.length =
              (q₀' + t * j) % D.length := by
            rw [hnb_t_def]
            suffices h : ∀ s, s < 2 * a →
                ((wList'.take ((r₀ + s * k₀) % n)).filter
                  (· ≠ StepSize.s)).length % D.length =
                (q₀' + s * j) % D.length from h t ht
            intro s
            induction s with
            | zero => intro _; simp only [Nat.zero_mul, Nat.add_zero, ← hq₀'_def]
            | succ s' ih =>
              intro hs
              have hslice_s := hslice_gen s' (by omega)
              have hstep := nonSBefore_advance w' (r₀ + s' * k₀) k₀ j
                (by omega) hslice_s
              rw [show r₀ + (s' + 1) * k₀ = r₀ + s' * k₀ + k₀ from by ring]
              trans (((wList'.take ((r₀ + s' * k₀) % n)).filter
                  (· ≠ StepSize.s)).length + j) % D.length
              · exact hstep
              · conv_lhs => rw [Nat.add_mod]
                rw [ih (by omega)]
                rw [← Nat.add_mod]
                congr 1; ring
          -- Sub-fact 3: geometric bridge (jWLc at nonSBefore = kStepVector)
          have hbridge : jWLc nb_t =
              (Necklace.kStepVector w' (r₀ + t * k₀) k₀ .L).natAbs :=
            orderedDeletion_window_Lcount w' (r₀ + t * k₀) k₀ j hDlen_pos (by omega) hslice_j
          -- Combine the three sub-facts
          calc jWLc ((q₀' + t * j) % (2 * a))
              = jWLc ((q₀' + t * j) % D.length) := by rw [hDlen]
            _ = jWLc (nb_t % D.length) := by rw [← htelescope]
            _ = jWLc nb_t := hjWLc_mod nb_t
            _ = (Necklace.kStepVector w' (r₀ + t * k₀) k₀ .L).natAbs :=
                hbridge
        obtain ⟨q₀, h_bridge⟩ := h_deletion_bridge
        exact ⟨q₀, fun t ht => by rw [h_bridge t ht, h_kstep_L t (by omega)]⟩
      obtain ⟨q₀, hstacking⟩ := hstacking
      -- The two alternating values are distinct
      have hvL_ne : v₀ ≠ v₁ := by
        intro h; apply hx_ne
        -- Both seq values are nonneg (ZVector.ofList entries = ↑ℕ)
        have h0_nn : 0 ≤ seq ⟨0, by omega⟩ x := by
          have := congr_fun (hseq_as ⟨0, by omega⟩).symm x
          simp only [show (0 : ℕ) % 2 = 0 from rfl,
            show (0 : ℕ) * k₀ = 0 from by ring, Nat.add_zero] at this
          rw [this]; unfold Necklace.kStepVector ZVector.ofList
          exact_mod_cast Nat.zero_le _
        have h1_nn : 0 ≤ seq ⟨1, by omega⟩ x := by
          have := congr_fun (hseq_as ⟨1, by omega⟩).symm x
          simp only [show (1 : ℕ) % 2 = 1 from rfl,
            show 1 * k₀ = k₀ from by ring] at this
          rw [this]; unfold Necklace.kStepVector ZVector.ofList
          exact_mod_cast Nat.zero_le _
        -- natAbs is injective on nonneg integers
        have h0_cast : (↑v₀ : ℤ) = seq ⟨0, by omega⟩ x :=
          Int.natAbs_of_nonneg h0_nn
        have h1_cast : (↑v₁ : ℤ) = seq ⟨1, by omega⟩ x :=
          Int.natAbs_of_nonneg h1_nn
        linarith [show (↑v₀ : ℤ) = ↑v₁ from by exact_mod_cast h]
      -- Extend hstacking to all t (periodicity in t)
      have hstacking' : ∀ t : ℕ,
          jWLc ((q₀ + t * j) % (2 * a)) =
            if t % 2 = 0 then v₀ else v₁ := by
        intro t
        have hred : (q₀ + t * j) % (2 * a) =
            (q₀ + (t % (2 * a)) * j) % (2 * a) := by
          have h : (t * j) % (2 * a) = ((t % (2 * a)) * j) % (2 * a) := by
            conv_lhs => rw [Nat.mul_mod]
            conv_rhs => rw [Nat.mul_mod, Nat.mod_mod_of_dvd t (dvd_refl (2 * a))]
          rw [Nat.add_mod, h, ← Nat.add_mod]
        rw [hred, show t % 2 = (t % (2 * a)) % 2 from
          (Nat.mod_mod_of_dvd t (dvd_mul_right 2 a)).symm]
        exact hstacking (t % (2 * a)) (Nat.mod_lt _ (by omega))
      -- hLflip: j-window L-counts flip at every j-step
      have hLflip : ∀ i, jWLc (i + j) ≠ jWLc i := by
        intro i
        rw [← hjWLc_mod i, ← hjWLc_mod (i + j), hDlen]
        obtain ⟨t, _, ht_eq⟩ := coprime_surj_mod j q₀ (2 * a) hcop
          (i % (2 * a)) (Nat.mod_lt _ (by omega))
        have hij : (i + j) % (2 * a) = (q₀ + (t + 1) * j) % (2 * a) := by
          conv_lhs => rw [Nat.add_mod, show i % (2 * a) = (q₀ + t * j) % (2 * a)
            from ht_eq.symm, ← Nat.add_mod]
          congr 1; ring
        rw [← ht_eq, hij, hstacking' t, hstacking' (t + 1)]
        rcases Nat.mod_two_eq_zero_or_one t with h | h <;> simp [h, hvL_ne, hvL_ne.symm] <;> omega
      -- hLbinary: j-window L-counts take exactly 2 values
      have hLbinary : ∀ i, jWLc i = jWLc 0 ∨ jWLc i = jWLc j := by
        intro i
        have hLne : jWLc 0 ≠ jWLc j := by
          have := hLflip 0; simp only [Nat.zero_add] at this; exact this.symm
        -- Express all three values via stacking
        rw [← hjWLc_mod i, hDlen]
        obtain ⟨t, _, ht_eq⟩ := coprime_surj_mod j q₀ (2 * a) hcop
          (i % (2 * a)) (Nat.mod_lt _ (by omega))
        rw [← ht_eq, hstacking' t]
        -- jWLc 0 via stacking
        obtain ⟨t₀, _, ht₀_eq⟩ := coprime_surj_mod j q₀ (2 * a) hcop 0 (by omega)
        have hval0 : jWLc 0 = if t₀ % 2 = 0 then v₀ else v₁ := by
          have h := hstacking' t₀; rw [ht₀_eq] at h; exact h
        -- jWLc j via stacking
        obtain ⟨t₁, _, ht₁_eq⟩ := coprime_surj_mod j q₀ (2 * a) hcop
          (j % (2 * a)) (Nat.mod_lt _ (by omega))
        have hvalj : jWLc j = if t₁ % 2 = 0 then v₀ else v₁ := by
          have h := hstacking' t₁; rw [ht₁_eq] at h
          rwa [show jWLc (j % (2 * a)) = jWLc j from by rw [← hDlen]; exact hjWLc_mod j] at h
        -- Case analysis
        rcases Nat.mod_two_eq_zero_or_one t with ht | ht <;>
          rcases Nat.mod_two_eq_zero_or_one t₀ with ht₀ | ht₀ <;>
          rcases Nat.mod_two_eq_zero_or_one t₁ with ht₁ | ht₁ <;>
          simp_all
      have hLne : jWLc 0 ≠ jWLc j := by
        have := hLflip 0; simp only [Nat.zero_add] at this; exact this.symm
      -- Construct the parity witness
      obtain ⟨g, hg_flip, hg_slide⟩ :
          ∃ g : ZMod (2 * a) → Fin 2,
            (∀ q : ZMod (2 * a), g (q + ↑j) ≠ g q) ∧
            (∀ (i : ℕ) (hi : i < D.length),
              D[(i + j) % D.length]'(Nat.mod_lt _ (by omega)) = D[i] →
              g ((↑i : ZMod (2 * a)) + 1) = g ↑i) := by
        -- Helper: (a + b % n) % n = (a + b) % n
        have mod_add_mod : ∀ (a b n : ℕ), 0 < n →
            (a + b % n) % n = (a + b) % n := by
          intro a b n _
          rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (dvd_refl n), ← Nat.add_mod]
        refine ⟨fun q => if jWLc (ZMod.val q) = jWLc 0 then 0 else 1, ?_, ?_⟩
        -- hg_flip: g(q + j) ≠ g(q)
        · intro q; simp only
          -- Relate ZMod.val(q + j) to ZMod.val(q) + j via periodicity
          have hval_q : jWLc (ZMod.val (q + (↑j : ZMod (2 * a)))) =
              jWLc (ZMod.val q + j) := by
            have hmod := hjWLc_mod (ZMod.val q + j)
            rw [hDlen] at hmod; rw [← hmod]; congr 1
            rw [ZMod.val_add, ZMod.val_natCast,
                mod_add_mod _ _ _ (by omega)]
          rw [hval_q]
          have hne := hLflip (ZMod.val q)
          by_cases h1 : jWLc (ZMod.val q) = jWLc 0
          · -- jWLc(val q) = jWLc 0 → jWLc(val q + j) ≠ jWLc 0
            have h2 : jWLc (ZMod.val q + j) ≠ jWLc 0 :=
              fun h => hne (h.trans h1.symm)
            rw [if_neg h2, if_pos h1]; decide
          · -- jWLc(val q) ≠ jWLc 0 → jWLc(val q) = jWLc j (by binary)
            rcases hLbinary (ZMod.val q) with hq | hq
            · exact absurd hq h1
            · have h2 : jWLc (ZMod.val q + j) ≠ jWLc j :=
                fun h => hne (h.trans hq.symm)
              rcases hLbinary (ZMod.val q + j) with hqj | hqj
              · rw [if_pos hqj, if_neg h1]; decide
              · exact absurd hqj h2
        -- hg_slide: D[i]=D[i+j] → g(↑i+1) = g(↑i)
        · intro i hi heq_D; simp only
          -- Sliding window: jWLc(i+1) = jWLc(i)
          have hslide : jWLc (i + 1) = jWLc i :=
            jwindow_slide_count D j i (by omega) hj_pos (by
              have h1 : (i + j) % D.length = (i + j) % D.length := rfl
              have h2 : i % D.length = i := Nat.mod_eq_of_lt hi
              simp only [h2]; exact heq_D)
          -- ZMod.val conversions
          have hvi : ZMod.val (↑i : ZMod (2 * a)) = i := by
            rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
          have hvi1 : jWLc (ZMod.val ((↑i : ZMod (2 * a)) + 1)) =
              jWLc (i + 1) := by
            have hmod := hjWLc_mod (i + 1)
            rw [hDlen] at hmod; rw [← hmod]; congr 1
            have : (↑i + 1 : ZMod (2 * a)) = ↑(i + 1 : ℕ) := by push_cast; ring
            rw [this, ZMod.val_natCast]
          rw [hvi1, hvi, hslide]
      -- g has period 2 (from period_two_of_coprime_flip)
      have hg_per2 := period_two_of_coprime_flip ha_pos g j hcop hg_flip
      -- g(q+1) ≠ g(q): since j is odd, g(q+j) = g(q+1) by period 2
      have hg_flip1 : ∀ q : ZMod (2 * a), g (q + 1) ≠ g q := by
        intro q
        have hne := hg_flip q
        suffices h : g (q + ↑j) = g (q + 1) by rwa [h] at hne
        have hcast : (↑j : ZMod (2 * a)) = ↑(j / 2) * 2 + 1 := by
          calc (↑j : ZMod (2 * a))
              = ↑(j / 2 * 2 + 1 : ℕ) := by congr 1; omega
            _ = ↑(j / 2) * 2 + 1 := by push_cast; ring
        calc g (q + ↑j)
            = g ((q + 1) + ↑(j / 2) * 2) := by congr 1; rw [hcast]; ring
          _ = g (q + 1) := mul_period_fin2 g 2 hg_per2 (j / 2) (q + 1)
      -- Conclude: D[i] ≠ D[(i+j)%len] by contradiction
      intro i hi heq
      exact absurd (hg_slide i hi heq) (hg_flip1 ↑i)
    exact ⟨j, hcop, hflip⟩
  exact circular_mos_of_flip D a hDlen ha_pos hbin j hcop hflip

/-- Odd AS scales are odd-regular scales. -/
theorem as_odd_isOddRegular (w : TernaryNecklace n)
    (hprim : Necklace.isPrimitive w) (htern : isTernary w)
    (has : hasAS w) (hodd : n % 2 = 1) :
    isOddRegular w := by
  have hn_ge := ternary_length_ge_three w htern
  -- Step 1: Extract AS data and cancelling pair
  have has' := has
  obtain ⟨k₀, r, seq, hk₀_lt, hcop_as, hseq, hclose⟩ := has
  obtain ⟨l₀, hl₀_pos, hl₀_le, hl₀_odd, hl₀_mod⟩ :=
    exists_odd_quasi_inverse k₀ hodd hcop_as hn_ge
  have hne := alternating_seq_ne w htern k₀ r seq l₀ hcop_as hodd hl₀_pos hl₀_le hl₀_odd
    hl₀_mod hseq hclose
  have hdiff := as_odd_seq_diff_le_one w hprim htern has' hodd k₀ r seq hcop_as hseq hclose
  have hseq0 : Necklace.kStepVector w r k₀ = seq ⟨0, by omega⟩ := by
    simpa using hseq ⟨0, by omega⟩
  have hseq1 : Necklace.kStepVector w (r + k₀) k₀ = seq ⟨1, by omega⟩ := by
    have h := hseq ⟨1, by omega⟩; simpa using h
  obtain ⟨x, y, hxy, hcancel, hx_ne, hz⟩ :=
    seq_diff_structure w k₀ r seq hseq0 hseq1 hdiff hne
  -- Build the MOS for the identified necklace
  have hmos : isPartialPairwiseMOS w x y := by
    show Necklace.hasMOSProperty (TernaryNecklace.identifyPair w x y)
    exact ⟨identified_uses_two_values w htern x y hxy,
      identified_kStep_le_two w hprim htern k₀ r seq hcop_as hodd hseq hclose x y hxy hcancel hz⟩
  -- Step 2: The cancelling pair has equal letter counts
  have hcount_eq := cancelling_pair_equal_counts w hprim htern hodd x y hxy
    k₀ r seq hcop_as hseq hclose hz
  -- Step 3: Find σ mapping x → L, y → m, z₀ → s
  obtain ⟨σ, hσx, hσy, hσz⟩ := exists_perm_x_to_L_y_to_m x y hxy
  -- Step 4: Transfer MOS through σ
  have hmos_perm := isPartialPairwiseMOS_applyPerm σ w x y hmos
  rw [hσx, hσy] at hmos_perm
  -- Step 5: Set up counts via count_applyPerm_eq
  set a := Necklace.count w x with ha_def
  have hσ_symm_L : σ.symm .L = x := by rw [← hσx, Equiv.symm_apply_apply]
  have hσ_symm_m : σ.symm .m = y := by rw [← hσy, Equiv.symm_apply_apply]
  have hcountL : Necklace.count (Necklace.applyPerm σ w) .L = a := by
    rw [count_applyPerm_eq, hσ_symm_L]
  have hcountm : Necklace.count (Necklace.applyPerm σ w) .m = a := by
    rw [count_applyPerm_eq, hσ_symm_m, ← hcount_eq]
  -- The third step size z₀ and its count b
  obtain ⟨z₀, hz₀x, hz₀y⟩ : ∃ z₀ : StepSize, z₀ ≠ x ∧ z₀ ≠ y := by
    cases x <;> cases y <;> simp_all
    · exact ⟨.s, by decide, by decide⟩
    · exact ⟨.m, by decide, by decide⟩
    · exact ⟨.s, by decide, by decide⟩
    · exact ⟨.L, by decide, by decide⟩
    · exact ⟨.m, by decide, by decide⟩
    · exact ⟨.L, by decide, by decide⟩
  set b := Necklace.count w z₀ with hb_def
  have hσ_symm_s : σ.symm .s = z₀ := by
    rw [← hσz z₀ hz₀x hz₀y, Equiv.symm_apply_apply]
  have hcounts : Necklace.count (Necklace.applyPerm σ w) .s = b := by
    rw [count_applyPerm_eq, hσ_symm_s]
  -- Step 6: n = 2a + b
  have hn_eq : n = 2 * a + b := by
    have htotal := count_total (Necklace.applyPerm σ w)
    rw [hcountL, hcountm, hcounts] at htotal; linarith
  -- Step 7: b is odd
  have hb_odd : b % 2 = 1 := by omega
  -- Step 8: a > 0 and b > 0
  have ha_pos : a > 0 := count_pos_of_isTernary w htern x
  have hb_pos : b > 0 := count_pos_of_isTernary w htern z₀
  -- Step 9: Coprime
  have hcop : Nat.Coprime (2 * a) b :=
    as_coprime_counts w hprim htern k₀ r seq hcop_as hodd hseq hclose x y z₀ hxy hz₀x hz₀y hcount_eq
  -- Step 10: Deletion MOS
  have hdel : isPartialDeletionMOS (Necklace.applyPerm σ w) .s :=
    as_odd_deletion_mos w hprim htern hodd k₀ r seq hk₀_lt hcop_as hseq hclose
      σ x y hxy hσx hσy hcount_eq hmos hcancel hx_ne hz
  -- Assemble
  exact ⟨hprim, hodd, σ, a, b, ha_pos, hb_pos, hb_odd, hcop, hn_eq,
    hcountL, hcountm, hcounts, hmos_perm, hdel⟩


end TernaryNecklace
