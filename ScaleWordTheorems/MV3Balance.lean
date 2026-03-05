import ScaleWordTheorems.MV3EvenRegular

open BigOperators

namespace TernaryNecklace

variable {n : ℕ} [NeZero n]

/-- All pairwise-MOS scales are balanced. Each letter's balance follows from the
    pair identification that preserves it: L from m=s, m from L=s, s from L=m. -/
theorem pairwiseMOS_implies_isBalanced (w : TernaryNecklace n)
    (_hprim : Necklace.isPrimitive w) (_htern : isTernary w)
    (hpmos : isPairwiseMOS w) :
    Necklace.isBalanced w := by
  obtain ⟨hLm, hms, hLs⟩ := hpmos
  intro k hk hk' w1 w2 a hw1 hw2
  have go := fun x y hxy a' hax hay hmos =>
    identification_preserves_letter_balance w x y hxy a' hax hay hmos k hk hk' w1 w2 hw1 hw2
  cases a with
  | L => exact go .m .s (by decide) .L (by decide) (by decide) hms
  | m => exact go .L .s (by decide) .m (by decide) (by decide) hLs
  | s => exact go .L .m (by decide) .s (by decide) (by decide) hLm

/-- Composing a necklace with a function distributes over k-step multisets. -/
private lemma allKStepMultisets_comp' {α β : Type*} [DecidableEq α] [DecidableEq β]
    (w : Necklace α n) (f : α → β) (k : ℕ) :
    Necklace.allKStepMultisets (f ∘ w) k =
      (Necklace.allKStepMultisets w k).map (Multiset.map f) := by
  unfold Necklace.allKStepMultisets Necklace.allKStepSubwords
  simp only [List.map_ofFn]
  congr 1; funext i
  simp only [Function.comp, Necklace.abelianize, Multiset.map_coe]
  congr 1; simp [Necklace.slice, List.map_map]

/-- Composing a primitive necklace with a function injective on its range
    preserves primitivity. -/
private lemma isPrimitive_comp_of_injective_on_range {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (w : Necklace α n) (f : α → β)
    (hprim : Necklace.isPrimitive w)
    (hinj : ∀ i j : ZMod n, f (w i) = f (w j) → w i = w j) :
    Necklace.isPrimitive (f ∘ w) := by
  by_contra h_not_prim
  set pLen := (Necklace.period (f ∘ w)).length
  have hpLen_pos : 0 < pLen := period_length_pos (f ∘ w)
  have hpLen_lt_n : pLen < n := by
    have := Necklace.period_length_le_n (f ∘ w)
    unfold Necklace.isPrimitive at h_not_prim; omega
  have hpLen_dvd : pLen ∣ n := period_dvd_length (f ∘ w)
  have hfw_per : ∀ j : ℕ, (f ∘ w) ((j : ℕ) : ZMod n) =
      (f ∘ w) ((j % pLen : ℕ) : ZMod n) :=
    fun j => period_pointwise (f ∘ w) j
  have hfw_trans : ∀ i : ZMod n,
      (f ∘ w) i = (f ∘ w) (i + (pLen : ZMod n)) := by
    intro i
    have h1 := hfw_per i.val
    have h2 := hfw_per (i.val + pLen)
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq] at h1
    rw [Nat.add_mod_right] at h2
    rw [h1, ← h2]; congr 1
    simp [Nat.cast_add, ZMod.natCast_val, ZMod.cast_id']
  have hw_trans : ∀ i : ZMod n, w i = w (i + (pLen : ZMod n)) :=
    fun i => hinj i (i + (pLen : ZMod n)) (hfw_trans i)
  have := Necklace.period_length_le_of_translational_period w pLen
    hpLen_pos hpLen_lt_n hpLen_dvd hw_trans
  unfold Necklace.isPrimitive at hprim; omega

/-- Total count of binary steps equals n. -/
private lemma binary_count_total (w : BinaryNecklace n) :
    Necklace.count w .L + Necklace.count w .s = n := by
  unfold Necklace.count
  have hunion : Finset.filter (fun i => w i = .L) Finset.univ ∪
      Finset.filter (fun i => w i = .s) Finset.univ = Finset.univ := by
    ext i; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    cases hw : w i <;> simp
  have hdisj : Disjoint (Finset.filter (fun i => w i = .L) Finset.univ)
                         (Finset.filter (fun i => w i = .s) Finset.univ) :=
    Finset.disjoint_filter.mpr (fun _ _ h => by rw [h]; decide)
  rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, ZMod.card]

/-- PWF ternary scales have odd length.
    Proof: each pair identification gives a primitive binary MOS via `msToBinary`.
    By `primitive_mos_coprime_counts`, we get coprimality conditions on the step
    counts. If n were even, a parity argument yields a contradiction. -/
private lemma pwf_n_odd (w : TernaryNecklace n)
    (htern : isTernary w) (hpwf : isPairwisePrimMOS w) :
    n % 2 = 1 := by
  obtain ⟨⟨hmosLm, hprimLm⟩, ⟨hmosms, hprimms⟩, ⟨hmosLs, hprimLs⟩⟩ := hpwf
  set p := Necklace.count w .L
  set q := Necklace.count w .m
  set r := Necklace.count w .s
  have hpqr : p + q + r = n := count_total w
  obtain ⟨⟨iL, hiL⟩, ⟨im, him⟩, ⟨is, his⟩⟩ := htern
  -- For each pair identification, build the binary bridge and extract coprimality.
  -- The binary bridge B = msToBinary ∘ (identifyPair w x y) is a primitive binary MOS.
  -- msToBinary maps L→L, m→L, s→s, and is injective on {v | v ≠ x} when x ∈ {L, m}.

  -- From (m,s) identification: gcd(p, q+r) = 1
  have h1 : Nat.gcd p (q + r) = 1 := by
    set B := identifiedToBinary (identifyPair w .m .s)
    have hBmos : BinaryNecklace.isMOS B := by
      constructor
      · exact ⟨⟨iL, by simp [B, identifiedToBinary, identifyPair, hiL, msToBinary]⟩,
               ⟨is, by simp [B, identifiedToBinary, identifyPair, his, msToBinary]⟩⟩
      · intro k hk hk'
        rw [show B = msToBinary ∘ identifyPair w .m .s from rfl,
            allKStepMultisets_comp' _ msToBinary k]
        calc ((Necklace.allKStepMultisets _ k).map (Multiset.map msToBinary)).toFinset.card
            ≤ (Necklace.allKStepMultisets _ k).toFinset.card := by
              rw [show ((Necklace.allKStepMultisets (identifyPair w .m .s) k).map
                  (Multiset.map msToBinary)).toFinset =
                  (Necklace.allKStepMultisets (identifyPair w .m .s) k).toFinset.image
                  (Multiset.map msToBinary) from by
                ext; simp [List.mem_toFinset, Finset.mem_image, List.mem_map]]
              exact Finset.card_image_le
          _ ≤ 2 := hmosms.2 k hk hk'
    have hBprim : Necklace.isPrimitive B :=
      isPrimitive_comp_of_injective_on_range _ msToBinary hprimms (by
        intro i j hij
        have hIi : identifyPair w .m .s i ≠ .m := by
          by_cases h : w i = .m <;> simp [identifyPair, h]
        have hIj : identifyPair w .m .s j ≠ .m := by
          by_cases h : w j = .m <;> simp [identifyPair, h]
        cases hvi : identifyPair w .m .s i <;> cases hvj : identifyPair w .m .s j <;>
          simp_all [msToBinary])
    have hcL : Necklace.count B .L = p := by
      unfold Necklace.count; congr 1; ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show msToBinary (identifyPair w .m .s i) = .L ↔ w i = .L
      cases hw : w i <;> simp [identifyPair, msToBinary, hw]
    have hcs : Necklace.count B .s = q + r := by
      have := binary_count_total B; omega
    rw [← hcL, ← hcs]; exact primitive_mos_coprime_counts B hBmos hBprim

  -- From (L,s) identification: gcd(q, p+r) = 1
  have h2 : Nat.gcd q (p + r) = 1 := by
    set B := identifiedToBinary (identifyPair w .L .s)
    have hBmos : BinaryNecklace.isMOS B := by
      constructor
      · exact ⟨⟨im, by simp [B, identifiedToBinary, identifyPair, him, msToBinary]⟩,
               ⟨is, by simp [B, identifiedToBinary, identifyPair, his, msToBinary]⟩⟩
      · intro k hk hk'
        rw [show B = msToBinary ∘ identifyPair w .L .s from rfl,
            allKStepMultisets_comp' _ msToBinary k]
        calc ((Necklace.allKStepMultisets _ k).map (Multiset.map msToBinary)).toFinset.card
            ≤ (Necklace.allKStepMultisets _ k).toFinset.card := by
              rw [show ((Necklace.allKStepMultisets (identifyPair w .L .s) k).map
                  (Multiset.map msToBinary)).toFinset =
                  (Necklace.allKStepMultisets (identifyPair w .L .s) k).toFinset.image
                  (Multiset.map msToBinary) from by
                ext; simp [List.mem_toFinset, Finset.mem_image, List.mem_map]]
              exact Finset.card_image_le
          _ ≤ 2 := hmosLs.2 k hk hk'
    have hBprim : Necklace.isPrimitive B :=
      isPrimitive_comp_of_injective_on_range _ msToBinary hprimLs (by
        intro i j hij
        have hIi : identifyPair w .L .s i ≠ .L := by
          by_cases h : w i = .L <;> simp [identifyPair, h]
        have hIj : identifyPair w .L .s j ≠ .L := by
          by_cases h : w j = .L <;> simp [identifyPair, h]
        cases hvi : identifyPair w .L .s i <;> cases hvj : identifyPair w .L .s j <;>
          simp_all [msToBinary])
    have hcL : Necklace.count B .L = q := by
      unfold Necklace.count; congr 1; ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show msToBinary (identifyPair w .L .s i) = .L ↔ w i = .m
      cases hw : w i <;> simp [identifyPair, msToBinary, hw]
    have hcs : Necklace.count B .s = p + r := by
      have := binary_count_total B; omega
    rw [← hcL, ← hcs]; exact primitive_mos_coprime_counts B hBmos hBprim

  -- From (L,m) identification: gcd(p+q, r) = 1
  have h3 : Nat.gcd (p + q) r = 1 := by
    set B := identifiedToBinary (identifyPair w .L .m)
    have hBmos : BinaryNecklace.isMOS B := by
      constructor
      · exact ⟨⟨iL, by simp [B, identifiedToBinary, identifyPair, hiL, msToBinary]⟩,
               ⟨is, by simp [B, identifiedToBinary, identifyPair, his, msToBinary]⟩⟩
      · intro k hk hk'
        rw [show B = msToBinary ∘ identifyPair w .L .m from rfl,
            allKStepMultisets_comp' _ msToBinary k]
        calc ((Necklace.allKStepMultisets _ k).map (Multiset.map msToBinary)).toFinset.card
            ≤ (Necklace.allKStepMultisets _ k).toFinset.card := by
              rw [show ((Necklace.allKStepMultisets (identifyPair w .L .m) k).map
                  (Multiset.map msToBinary)).toFinset =
                  (Necklace.allKStepMultisets (identifyPair w .L .m) k).toFinset.image
                  (Multiset.map msToBinary) from by
                ext; simp [List.mem_toFinset, Finset.mem_image, List.mem_map]]
              exact Finset.card_image_le
          _ ≤ 2 := hmosLm.2 k hk hk'
    have hBprim : Necklace.isPrimitive B :=
      isPrimitive_comp_of_injective_on_range _ msToBinary hprimLm (by
        intro i j hij
        have hIi : identifyPair w .L .m i ≠ .L := by
          by_cases h : w i = .L <;> simp [identifyPair, h]
        have hIj : identifyPair w .L .m j ≠ .L := by
          by_cases h : w j = .L <;> simp [identifyPair, h]
        cases hvi : identifyPair w .L .m i <;> cases hvj : identifyPair w .L .m j <;>
          simp_all [msToBinary])
    have hcL : Necklace.count B .L = p + q := by
      show _ = Necklace.count w .L + Necklace.count w .m
      unfold Necklace.count
      have heq : Finset.filter (fun i => B i = .L) Finset.univ =
          Finset.filter (fun i => w i = .L) Finset.univ ∪
          Finset.filter (fun i => w i = .m) Finset.univ := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
        show msToBinary (identifyPair w .L .m i) = .L ↔ w i = .L ∨ w i = .m
        cases hw : w i <;> simp [identifyPair, msToBinary, hw]
      rw [heq, Finset.card_union_of_disjoint (by
        rw [Finset.disjoint_filter]; intro i _ h1 h2; rw [h1] at h2; exact absurd h2 (by decide))]
    have hcs : Necklace.count B .s = r := by
      have := binary_count_total B; omega
    rw [← hcL, ← hcs]; exact primitive_mos_coprime_counts B hBmos hBprim

  -- Parity argument: if n is even, p and q are odd, p+q is even,
  -- r is even, contradicting gcd(p+q, r) = 1.
  by_contra heven
  have hp : p % 2 = 1 := by
    by_contra h
    have h2p : 2 ∣ p := by omega
    have h2qr : 2 ∣ (q + r) := by omega
    have := Nat.dvd_gcd h2p h2qr; rw [h1] at this; omega
  have hq : q % 2 = 1 := by
    by_contra h
    have h2q : 2 ∣ q := by omega
    have h2pr : 2 ∣ (p + r) := by omega
    have := Nat.dvd_gcd h2q h2pr; rw [h2] at this; omega
  have h2pq : 2 ∣ (p + q) := by omega
  have h2r : 2 ∣ r := by omega
  have := Nat.dvd_gcd h2pq h2r; rw [h3] at this; omega

/-- A PWF ternary necklace is primitive.
    If w had a non-trivial period d, then identifyPair w .m .s would inherit it,
    contradicting the primitivity of that identification. -/
private lemma isPrimitive_of_isPairwisePrimMOS (w : TernaryNecklace n)
    (hpwf : isPairwisePrimMOS w) : Necklace.isPrimitive w := by
  obtain ⟨_, ⟨_, hprim⟩, _⟩ := hpwf
  by_contra h_not_prim
  set v := identifyPair w .m .s
  set pLen := (Necklace.period w).length
  have hpLen_pos : 0 < pLen := period_length_pos w
  have hpLen_lt_n : pLen < n := by
    have := Necklace.period_length_le_n w
    unfold Necklace.isPrimitive at h_not_prim; omega
  have hpLen_dvd : pLen ∣ n := period_dvd_length w
  have hw_per : ∀ j : ℕ, w ((j : ℕ) : ZMod n) = w ((j % pLen : ℕ) : ZMod n) :=
    fun j => period_pointwise w j
  have hv_per : ∀ j : ℕ, v ((j : ℕ) : ZMod n) = v ((j % pLen : ℕ) : ZMod n) := by
    intro j; simp only [v, identifyPair, hw_per j]
  have hv_trans : ∀ i : ZMod n, v i = v (i + (pLen : ZMod n)) := by
    intro i
    have h1 := hv_per i.val
    have h2 := hv_per (i.val + pLen)
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq] at h1
    rw [Nat.add_mod_right] at h2
    rw [h1, ← h2]; congr 1
    simp [Nat.cast_add, ZMod.natCast_val, ZMod.cast_id']
  have := Necklace.period_length_le_of_translational_period v pLen
    hpLen_pos hpLen_lt_n hpLen_dvd hv_trans
  unfold Necklace.isPrimitive at hprim; omega

/-- The s-component of the binary bridge's k-step vector equals w's s-component.
    Since B(j) = .s iff w(j) = .s, windows of B and w agree on s-counts. -/
private lemma kStepVector_bridge_s (w : TernaryNecklace n) (i k : ℕ) :
    (Necklace.kStepVector (identifiedToBinary (identifyPair w .L .m)) i k) .s =
    (Necklace.kStepVector w i k) .s := by
  induction k generalizing i with
  | zero => simp [Necklace.kStepVector, Necklace.slice, ZVector.ofList]
  | succ k ih =>
    rw [kStepVector_add (identifiedToBinary (identifyPair w .L .m)) i k 1 .s,
        kStepVector_add w i k 1 .s, ih i]
    congr 1
    -- Single-step case: B(i+k) = .s ↔ w(i+k) = .s
    unfold Necklace.kStepVector Necklace.slice ZVector.ofList
    simp only [show (i + k) + 1 - (i + k) = 1 from by omega,
               List.range_succ, List.range_zero, List.nil_append]
    cases h : w ((↑i : ZMod n) + ↑k) <;> simp [identifiedToBinary, identifyPair, msToBinary, h]

/-- The L-component of B's k-step vector equals (w.L + w.m) components summed.
    Since B(j) = .L iff w(j) ∈ {.L, .m}. -/
private lemma kStepVector_bridge_L (w : TernaryNecklace n) (i k : ℕ) :
    (Necklace.kStepVector (identifiedToBinary (identifyPair w .L .m)) i k) .L =
    (Necklace.kStepVector w i k) .L + (Necklace.kStepVector w i k) .m := by
  induction k generalizing i with
  | zero => simp [Necklace.kStepVector, Necklace.slice, ZVector.ofList]
  | succ k ih =>
    rw [kStepVector_add (identifiedToBinary (identifyPair w .L .m)) i k 1 .L,
        kStepVector_add w i k 1 .L, kStepVector_add w i k 1 .m, ih i]
    suffices h : Necklace.kStepVector (identifiedToBinary (identifyPair w .L .m)) (i + k) 1 .L =
        Necklace.kStepVector w (i + k) 1 .L + Necklace.kStepVector w (i + k) 1 .m by linarith
    -- Single-step case: B(j) = .L iff w(j) ∈ {.L, .m}
    unfold Necklace.kStepVector Necklace.slice ZVector.ofList
    simp only [show (i + k) + 1 - (i + k) = 1 from by omega,
               List.range_succ, List.range_zero, List.nil_append]
    cases h : w ((↑i : ZMod n) + ↑k) <;> simp [identifiedToBinary, identifyPair, msToBinary, h]

/-- The L-component of the (m,s)-binary bridge's k-step vector equals w's L-component.
    Since B₁(j) = .L iff w(j) = .L, windows of B₁ and w agree on L-counts. -/
private lemma kStepVector_bridge_L_ms (w : TernaryNecklace n) (i k : ℕ) :
    (Necklace.kStepVector (identifiedToBinary (identifyPair w .m .s)) i k) .L =
    (Necklace.kStepVector w i k) .L := by
  induction k generalizing i with
  | zero => simp [Necklace.kStepVector, Necklace.slice, ZVector.ofList]
  | succ k ih =>
    rw [kStepVector_add (identifiedToBinary (identifyPair w .m .s)) i k 1 .L,
        kStepVector_add w i k 1 .L, ih i]
    congr 1
    unfold Necklace.kStepVector Necklace.slice ZVector.ofList
    simp only [show (i + k) + 1 - (i + k) = 1 from by omega,
               List.range_succ, List.range_zero, List.nil_append]
    cases h : w ((↑i : ZMod n) + ↑k) <;> simp [identifiedToBinary, identifyPair, msToBinary, h]

/-- The s-component of the (m,s)-binary bridge = w's (m+s) count.
    Since B₁(j) = .s iff w(j) ∈ {.m, .s}. -/
private lemma kStepVector_bridge_s_ms (w : TernaryNecklace n) (i k : ℕ) :
    (Necklace.kStepVector (identifiedToBinary (identifyPair w .m .s)) i k) .s =
    (Necklace.kStepVector w i k) .m + (Necklace.kStepVector w i k) .s := by
  induction k generalizing i with
  | zero => simp [Necklace.kStepVector, Necklace.slice, ZVector.ofList]
  | succ k ih =>
    rw [kStepVector_add (identifiedToBinary (identifyPair w .m .s)) i k 1 .s,
        kStepVector_add w i k 1 .m, kStepVector_add w i k 1 .s, ih i]
    suffices h : Necklace.kStepVector (identifiedToBinary (identifyPair w .m .s)) (i + k) 1 .s =
        Necklace.kStepVector w (i + k) 1 .m + Necklace.kStepVector w (i + k) 1 .s by linarith
    unfold Necklace.kStepVector Necklace.slice ZVector.ofList
    simp only [show (i + k) + 1 - (i + k) = 1 from by omega,
               List.range_succ, List.range_zero, List.nil_append]
    cases h : w ((↑i : ZMod n) + ↑k) <;> simp [identifiedToBinary, identifyPair, msToBinary, h]

/-- The L-component of the (L,s)-binary bridge's k-step vector equals w's m-component.
    Since B₂(j) = .L iff w(j) = .m. -/
private lemma kStepVector_bridge_m_Ls (w : TernaryNecklace n) (i k : ℕ) :
    (Necklace.kStepVector (identifiedToBinary (identifyPair w .L .s)) i k) .L =
    (Necklace.kStepVector w i k) .m := by
  induction k generalizing i with
  | zero => simp [Necklace.kStepVector, Necklace.slice, ZVector.ofList]
  | succ k ih =>
    rw [kStepVector_add (identifiedToBinary (identifyPair w .L .s)) i k 1 .L,
        kStepVector_add w i k 1 .m, ih i]
    congr 1
    unfold Necklace.kStepVector Necklace.slice ZVector.ofList
    simp only [show (i + k) + 1 - (i + k) = 1 from by omega,
               List.range_succ, List.range_zero, List.nil_append]
    cases h : w ((↑i : ZMod n) + ↑k) <;> simp [identifiedToBinary, identifyPair, msToBinary, h]

/-- The s-component of the (L,s)-binary bridge = w's (L+s) count.
    Since B₂(j) = .s iff w(j) ∈ {.L, .s}. -/
private lemma kStepVector_bridge_Ls_Ls (w : TernaryNecklace n) (i k : ℕ) :
    (Necklace.kStepVector (identifiedToBinary (identifyPair w .L .s)) i k) .s =
    (Necklace.kStepVector w i k) .L + (Necklace.kStepVector w i k) .s := by
  induction k generalizing i with
  | zero => simp [Necklace.kStepVector, Necklace.slice, ZVector.ofList]
  | succ k ih =>
    rw [kStepVector_add (identifiedToBinary (identifyPair w .L .s)) i k 1 .s,
        kStepVector_add w i k 1 .L, kStepVector_add w i k 1 .s, ih i]
    suffices h : Necklace.kStepVector (identifiedToBinary (identifyPair w .L .s)) (i + k) 1 .s =
        Necklace.kStepVector w (i + k) 1 .L + Necklace.kStepVector w (i + k) 1 .s by linarith
    unfold Necklace.kStepVector Necklace.slice ZVector.ofList
    simp only [show (i + k) + 1 - (i + k) = 1 from by omega,
               List.range_succ, List.range_zero, List.nil_append]
    cases h : w ((↑i : ZMod n) + ↑k) <;> simp [identifiedToBinary, identifyPair, msToBinary, h]

/-- A primitive binary MOS with n ≥ 3 has a generator stacking structure:
    there exist step k, rotation r, generator g such that gcd(k,n) = 1
    and positions r, r+k, ..., r+(n-2)k all have k-step vector g,
    while position r+(n-1)k has a different k-step vector. -/
private lemma primitive_mos_stacking (B : BinaryNecklace n)
    (hmos : BinaryNecklace.isMOS B) (hprim : Necklace.isPrimitive B) (hn_ge3 : n ≥ 3) :
    ∃ (k r : ℕ) (g : ZVector BinaryStep),
      0 < k ∧ k < n ∧ Nat.Coprime k n ∧
      (∀ i, i < n - 1 → Necklace.kStepVector B (r + i * k) k = g) ∧
      (Necklace.kStepVector B (r + (n - 1) * k) k ≠ g) := by
  have hn_pos : 0 < n := by omega
  obtain ⟨g, hgen⟩ := allMOSScalesHaveGenerator n B hmos
  have hbin : BinaryNecklace.isBinary B := hmos.1
  obtain ⟨k, hk_pos, hk_lt, hk_count⟩ :=
    generator_implies_p_minus_one_occurrences B hbin g hgen
  have hk_cop : Nat.Coprime k n := by
    have := p_minus_one_occurrences_implies_coprime_to_period B hbin k hk_pos hk_lt g hk_count
    rwa [hprim] at this
  rw [hprim] at hk_lt hk_count
  -- Find bad position: exactly 1 position where vector ≠ g
  have hbad : ∃ i₀ : ℕ, i₀ < n ∧ Necklace.kStepVector B i₀ k ≠ g ∧
      (∀ j : ℕ, j < n → j ≠ i₀ → Necklace.kStepVector B j k = g) := by
    unfold countKStepVectorPerPeriod at hk_count
    rw [show (Necklace.period B).length = n from hprim] at hk_count
    have hexists_bad : ∃ i₀, i₀ < n ∧ Necklace.kStepVector B i₀ k ≠ g := by
      by_contra hall; push_neg at hall
      have h := List.countP_eq_length.mpr (fun i hi => by
        exact decide_eq_true_eq.mpr (hall i (List.mem_range.mp hi)))
      rw [List.length_range] at h; rw [h] at hk_count; omega
    obtain ⟨i₀, hi₀_lt, hi₀_bad⟩ := hexists_bad
    refine ⟨i₀, hi₀_lt, hi₀_bad, fun j hj hne => ?_⟩
    by_contra hj_bad
    set p := fun i => decide (Necklace.kStepVector B i k = g)
    have hcg : (List.range n).countP p = n - 1 := hk_count
    have hp_i₀ : p i₀ = false := by simp [p, hi₀_bad]
    have hp_j : p j = false := by simp [p, hj_bad]
    have hi₀_mem : i₀ ∈ List.range n := List.mem_range.mpr hi₀_lt
    have hj_mem : j ∈ List.range n := List.mem_range.mpr hj
    have h1 : ((List.range n).erase j).countP p = (List.range n).countP p := by
      rw [List.countP_erase]; simp [hj_mem, hp_j]
    have h2 : ((List.range n).erase j).length = n - 1 := by
      rw [List.length_erase_of_mem hj_mem, List.length_range]
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
  set r := (i₀ + k) % n with hr_def
  have hk_unit : IsUnit (↑k : ZMod n) := coprime_isUnit_zmod k hk_cop (by omega)
  -- Good stacking indices avoid the bad position
  have hgood_pos : ∀ i : ℕ, i < n - 1 → (r + i * k) % n ≠ i₀ := by
    intro i hi heq
    suffices h_dvd : n ∣ (i + 1) by
      exact absurd (Nat.le_of_dvd (by omega) h_dvd) (by omega)
    suffices h_mod : (i + 1) % n = 0 from Nat.dvd_of_mod_eq_zero h_mod
    have h1 : (↑(r + i * k) : ZMod n) = (↑i₀ : ZMod n) := by
      rw [← ZMod.natCast_zmod_val (↑(r + i * k) : ZMod n),
          ← ZMod.natCast_zmod_val (↑i₀ : ZMod n)]
      congr 1; simp only [ZMod.val_natCast]
      rwa [Nat.mod_eq_of_lt hi₀_lt]
    have h2 : (↑k : ZMod n) * (1 + ↑i) = 0 := by
      have h_eq : (↑r : ZMod n) + ↑i * ↑k = ↑i₀ := by push_cast at h1; exact h1
      have hr_eq : (↑r : ZMod n) = ↑i₀ + ↑k := by
        suffices h : (↑r : ZMod n) = (↑(i₀ + k) : ZMod n) by rw [h]; push_cast; ring
        rw [← ZMod.natCast_zmod_val (↑r : ZMod n),
            ← ZMod.natCast_zmod_val (↑(i₀ + k) : ZMod n)]
        congr 1; simp only [ZMod.val_natCast]
        rw [hr_def]; exact Nat.mod_eq_of_lt (Nat.mod_lt _ hn_pos)
      rw [hr_eq] at h_eq; linear_combination h_eq
    have h3 : (1 : ZMod n) + ↑i = 0 :=
      hk_unit.mul_left_cancel (h2.trans (mul_zero _).symm)
    have h4 : (↑(i + 1) : ZMod n) = 0 := by push_cast; linear_combination h3
    have := congr_arg ZMod.val h4
    simp only [ZMod.val_natCast, ZMod.val_zero] at this; exact this
  -- Closing stacking index hits the bad position
  have hclose_pos : (r + (n - 1) * k) % n = i₀ := by
    have h1 : r + (n - 1) * k ≡ i₀ + k + (n - 1) * k [MOD n] :=
      Nat.ModEq.add_right _ (Nat.mod_modEq (i₀ + k) n)
    have h2 : i₀ + k + (n - 1) * k = i₀ + n * k := by
      have : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn_pos; nlinarith
    rw [Nat.ModEq, h2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi₀_lt] at h1; exact h1
  exact ⟨k, r, g, hk_pos, hk_lt, hk_cop,
    fun i hi => by rw [← kStepVector_mod_n]; exact hi₀_good _ (Nat.mod_lt _ hn_pos) (hgood_pos i hi),
    fun heq => hi₀_bad (by rw [← kStepVector_mod_n, hclose_pos] at heq; exact heq)⟩

/-- kStepVector values are non-negative (since they count occurrences). -/
private lemma kStepVector_nonneg' (w : TernaryNecklace n) (i k : ℕ) (a : StepSize) :
    0 ≤ Necklace.kStepVector w i k a := by
  simp only [Necklace.kStepVector, ZVector.ofList]; exact Nat.cast_nonneg _

/-- Relates kStepVector to List.count via Nat.cast. -/
private lemma kStepVector_eq_cast_count' (w : TernaryNecklace n) (i k : ℕ) (a : StepSize) :
    Necklace.kStepVector w i k a = ↑((Necklace.slice w i (i + k)).count a) := by
  simp only [Necklace.kStepVector, ZVector.ofList, List.count_eq_countP,
    List.countP_eq_length_filter]

/-- Balance implies kStepVector differences are at most 1 for any two starting positions. -/
private lemma balanced_kStepVector_diff' (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (k : ℕ) (hk : 0 < k) (hkn : k < n)
    (i j : ℕ) (a : StepSize) :
    Int.natAbs (Necklace.kStepVector w i k a - Necklace.kStepVector w j k a) ≤ 1 := by
  rw [← congr_fun (kStepVector_mod_n w i k) a, ← congr_fun (kStepVector_mod_n w j k) a]
  rw [kStepVector_eq_cast_count', kStepVector_eq_cast_count']
  exact hbal k hk hkn _ _ a
    (List.mem_ofFn.mpr ⟨⟨i % n, Nat.mod_lt i (NeZero.pos n)⟩, rfl⟩)
    (List.mem_ofFn.mpr ⟨⟨j % n, Nat.mod_lt j (NeZero.pos n)⟩, rfl⟩)

/-- Core lemma: in a balanced ternary necklace with count_x = count_y,
    no k-step vector can have x-count ≥ 2 and y-count = 0.
    Proof by double counting: balance forces every x-count ≥ 1 (sum ≥ n) and
    every y-count ≤ 1 (sum ≤ n), but equal counts make the sums equal,
    forcing every y-count = 1. The position with y = 0 contradicts this. -/
private lemma balanced_two_equal_no_x2_y0 (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w)
    (x y : StepSize) (_hxy : x ≠ y)
    (heq : Necklace.count w x = Necklace.count w y)
    (k : ℕ) (hk_pos : 0 < k) (hk_lt : k < n)
    (j : ℕ) (hx2 : Necklace.kStepVector w j k x ≥ 2)
    (hy0 : Necklace.kStepVector w j k y = 0) :
    False := by
  have hn_pos : 0 < n := by omega
  -- From balance + x ≥ 2 at j: all x-counts ≥ 1
  have hx_lb : ∀ i ∈ Finset.range n, Necklace.kStepVector w i k x ≥ 1 := by
    intro i _
    have h := balanced_kStepVector_diff' w hbal k hk_pos hk_lt i j x
    have h_int : |Necklace.kStepVector w i k x - Necklace.kStepVector w j k x| ≤ 1 := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast h
    rw [abs_le] at h_int; linarith [h_int.1]
  -- From balance + y = 0 at j: all y-counts ≤ 1
  have hy_ub : ∀ i ∈ Finset.range n, Necklace.kStepVector w i k y ≤ 1 := by
    intro i _
    have h := balanced_kStepVector_diff' w hbal k hk_pos hk_lt i j y
    have h_int : |Necklace.kStepVector w i k y - Necklace.kStepVector w j k y| ≤ 1 := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast h
    rw [hy0] at h_int; rw [abs_le] at h_int; linarith [h_int.2]
  -- Sum of x-counts ≥ n
  have hsx : ↑k * ↑(Necklace.count w x) ≥ (↑n : ℤ) := by
    rw [← kStepVector_lettercount_sum]
    calc ∑ i ∈ Finset.range n, Necklace.kStepVector w i k x
        ≥ ∑ _ ∈ Finset.range n, (1 : ℤ) := Finset.sum_le_sum hx_lb
      _ = ↑n := by simp
  -- Sum of y-counts ≤ n
  have hsy : ↑k * ↑(Necklace.count w y) ≤ (↑n : ℤ) := by
    rw [← kStepVector_lettercount_sum]
    calc ∑ i ∈ Finset.range n, Necklace.kStepVector w i k y
        ≤ ∑ _ ∈ Finset.range n, (1 : ℤ) := Finset.sum_le_sum hy_ub
      _ = ↑n := by simp
  -- Equal counts: n ≤ k * count_x = k * count_y ≤ n
  rw [heq] at hsx
  -- Sum of y = n exactly, but y(j%n) = 0 while each term ∈ [0,1]:
  -- removing j%n gives n-1 terms summing to n, each ≤ 1. Contradiction.
  have hsum_eq : ∑ i ∈ Finset.range n, Necklace.kStepVector w i k y = ↑n :=
    le_antisymm (by linarith [kStepVector_lettercount_sum w k y])
      (by linarith [kStepVector_lettercount_sum w k y])
  have hj_mem : j % n ∈ Finset.range n := Finset.mem_range.mpr (Nat.mod_lt _ hn_pos)
  have hvy_j : Necklace.kStepVector w (j % n) k y = 0 := by rwa [kStepVector_mod_n]
  -- ∑ (erase j%n) = n, but |erase| = n-1 and each term ≤ 1
  have hrest : ∑ i ∈ (Finset.range n).erase (j % n), Necklace.kStepVector w i k y = ↑n := by
    have := Finset.add_sum_erase (Finset.range n) (fun i => Necklace.kStepVector w i k y) hj_mem
    linarith
  have hle : ∑ i ∈ (Finset.range n).erase (j % n), Necklace.kStepVector w i k y ≤ ↑n - 1 := by
    calc ∑ i ∈ (Finset.range n).erase (j % n), Necklace.kStepVector w i k y
        ≤ ∑ _ ∈ (Finset.range n).erase (j % n), (1 : ℤ) :=
          Finset.sum_le_sum (fun i hi => hy_ub i (Finset.mem_of_mem_erase hi))
      _ = ↑((Finset.range n).erase (j % n)).card := by simp
      _ ≤ ↑n - 1 := by
          rw [Finset.card_erase_of_mem hj_mem, Finset.card_range]; omega
  linarith

set_option maxHeartbeats 1600000
/-- When count_L = count_m, a balanced PWF odd ternary necklace has an alternating sequence.
    Uses the (L,m) bridge: at the generator, good positions have constant s-count and L+m = t.
    Equal counts force Lmin = mmin = v₀. If t even: degenerate (only one good-position type).
    If t odd: alternation forced by no_x2_y0 at step 2k₀ (when v₀ = 0, QQ and RR directly
    violate no_x2_y0; when v₀ ≥ 1, 3-type argument using both (m,s) and (L,s) MOS at 2k₀). -/
private lemma balanced_two_equal_hasAS_Lm (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (htern : isTernary w)
    (hpwf : isPairwisePrimMOS w) (hodd : n % 2 = 1)
    (heq : Necklace.count w .L = Necklace.count w .m) :
    hasAS w := by
  obtain ⟨⟨hmosLm, hprimLm⟩, ⟨hmosms, hprimms⟩, ⟨hmosLs, hprimLs⟩⟩ := hpwf
  obtain ⟨⟨iL, hiL⟩, ⟨im, him⟩, ⟨is, his⟩⟩ := htern
  -- n ≥ 3 from ternarity
  have hn_ge3 : n ≥ 3 := by
    have hiLm : iL ≠ im := by intro h; have := hiL.symm.trans (h ▸ him); exact absurd this (by decide)
    have hiLs : iL ≠ is := by intro h; have := hiL.symm.trans (h ▸ his); exact absurd this (by decide)
    have hims : im ≠ is := by intro h; have := him.symm.trans (h ▸ his); exact absurd this (by decide)
    have h3 : ({iL, im, is} : Finset (ZMod n)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hiLm, hiLs]),
          Finset.card_insert_of_notMem (by simp [hims]), Finset.card_singleton]
    have := Finset.card_le_card (Finset.subset_univ ({iL, im, is} : Finset (ZMod n)))
    rw [h3, Finset.card_univ, ZMod.card] at this; exact this
  have hn_pos : 0 < n := by omega
  -- Step 1: Build (L,m) bridge → binary MOS
  set B := identifiedToBinary (identifyPair w .L .m) with hB_def
  have hBmos : BinaryNecklace.isMOS B := by
    constructor
    · exact ⟨⟨iL, by simp [B, identifiedToBinary, identifyPair, hiL, msToBinary]⟩,
             ⟨is, by simp [B, identifiedToBinary, identifyPair, his, msToBinary]⟩⟩
    · intro k hk hk'
      rw [show B = msToBinary ∘ identifyPair w .L .m from rfl, allKStepMultisets_comp' _ msToBinary k]
      calc ((Necklace.allKStepMultisets _ k).map (Multiset.map msToBinary)).toFinset.card
          ≤ (Necklace.allKStepMultisets _ k).toFinset.card := by
            rw [show ((Necklace.allKStepMultisets (identifyPair w .L .m) k).map
                (Multiset.map msToBinary)).toFinset =
                (Necklace.allKStepMultisets (identifyPair w .L .m) k).toFinset.image
                (Multiset.map msToBinary) from by ext; simp [List.mem_toFinset, Finset.mem_image, List.mem_map]]
            exact Finset.card_image_le
        _ ≤ 2 := hmosLm.2 k hk hk'
  have hBprim : Necklace.isPrimitive B :=
    isPrimitive_comp_of_injective_on_range _ msToBinary hprimLm (by
      intro i j hij
      have hIi : identifyPair w .L .m i ≠ .L := by by_cases h : w i = .L <;> simp [identifyPair, h]
      have hIj : identifyPair w .L .m j ≠ .L := by by_cases h : w j = .L <;> simp [identifyPair, h]
      cases hvi : identifyPair w .L .m i <;> cases hvj : identifyPair w .L .m j <;> simp_all [msToBinary])
  -- Steps 2-4: Generator, step k₀, coprimality, stacking
  obtain ⟨k₀, r, g, hk₀_pos, hk₀_lt, hk₀_cop, hgood_B_stacking, hclose_B_stacking⟩ :=
    primitive_mos_stacking B hBmos hBprim hn_ge3
  -- Bridge relations
  have h_bridge_s : ∀ j, (Necklace.kStepVector B j k₀) .s = (Necklace.kStepVector w j k₀) .s :=
    fun j => kStepVector_bridge_s w j k₀
  -- g .s ≠ closing s-value
  have hg_total : g .L + g .s = ↑k₀ := by
    have hg0 := hgood_B_stacking 0 (by omega)
    rw [show r + 0 * k₀ = r from by omega] at hg0
    rw [← hg0]; exact_mod_cast kStepVector_total_count B r k₀
  -- Good positions: s-count = g .s, L + m = g .L
  have hgood_s : ∀ i, i < n - 1 → (Necklace.kStepVector w (r + i * k₀) k₀) .s = g .s := by
    intro i hi; rw [← h_bridge_s, hgood_B_stacking i hi]
  have hgood_Lm : ∀ i, i < n - 1 →
      (Necklace.kStepVector w (r + i * k₀) k₀) .L +
      (Necklace.kStepVector w (r + i * k₀) k₀) .m = g .L := by
    intro i hi; have := kStepVector_bridge_L w (r + i * k₀) k₀
    rw [hgood_B_stacking i hi] at this; linarith
  -- Closing s-count ≠ g .s
  have hclose_s_ne : (Necklace.kStepVector w (r + (n - 1) * k₀) k₀) .s ≠ g .s := by
    intro heq; apply hclose_B_stacking; funext a
    have hj_total : (Necklace.kStepVector B (r + (n - 1) * k₀) k₀) .L +
        (Necklace.kStepVector B (r + (n - 1) * k₀) k₀) .s = ↑k₀ :=
      by exact_mod_cast kStepVector_total_count B (r + (n - 1) * k₀) k₀
    have hs_eq : (Necklace.kStepVector B (r + (n - 1) * k₀) k₀) .s = g .s := by
      rw [h_bridge_s]; exact heq
    have hL_eq : (Necklace.kStepVector B (r + (n - 1) * k₀) k₀) .L = g .L := by linarith
    cases a <;> [exact hL_eq; exact hs_eq]
  -- Phase D: Case analysis on good-position vectors
  -- If all good vectors equal → degenerate hasAS
  rcases Classical.em (∀ i, i < n - 1 →
      Necklace.kStepVector w (r + i * k₀) k₀ = Necklace.kStepVector w r k₀) with hall_eq | hall_neq
  · have hQ_s : (Necklace.kStepVector w r k₀) .s = g .s := by
      have := hgood_s 0 (by omega); rwa [show r + 0 * k₀ = r from by omega] at this
    exact ⟨k₀, r, fun _ => Necklace.kStepVector w r k₀, hk₀_lt, hk₀_cop,
      fun i => hall_eq i.val i.isLt,
      fun _ heq => hclose_s_ne ((congr_fun heq .s).trans hQ_s)⟩
  · -- At least 2 distinct good-position types
    push_neg at hall_neq; obtain ⟨i₁, hi₁_lt, hi₁_ne⟩ := hall_neq
    set Q := Necklace.kStepVector w r k₀ with hQ_def
    set R := Necklace.kStepVector w (r + i₁ * k₀) k₀ with hR_def
    have h0k : r + 0 * k₀ = r := by omega
    -- Q and R differ in L-component
    have hQR_L_ne : Q .L ≠ R .L := by
      intro heq; apply hi₁_ne
      have hgood_det : ∀ i j, i < n - 1 → j < n - 1 →
          (Necklace.kStepVector w (r + i * k₀) k₀) .L =
          (Necklace.kStepVector w (r + j * k₀) k₀) .L →
          Necklace.kStepVector w (r + i * k₀) k₀ =
          Necklace.kStepVector w (r + j * k₀) k₀ := by
        intro i j hi hj hL_eq; funext a; cases a with
        | L => exact hL_eq
        | m => linarith [hgood_Lm i hi, hgood_Lm j hj]
        | s => rw [hgood_s i hi, hgood_s j hj]
      have h := hgood_det i₁ 0 hi₁_lt (by omega) (by
        show (Necklace.kStepVector w (r + i₁ * k₀) k₀) .L =
            (Necklace.kStepVector w (r + 0 * k₀) k₀) .L
        rw [h0k]; exact heq.symm)
      rw [h0k] at h; exact h
    -- Good vectors determined by L-component
    have hgood_det : ∀ i j, i < n - 1 → j < n - 1 →
        (Necklace.kStepVector w (r + i * k₀) k₀) .L =
        (Necklace.kStepVector w (r + j * k₀) k₀) .L →
        Necklace.kStepVector w (r + i * k₀) k₀ =
        Necklace.kStepVector w (r + j * k₀) k₀ := by
      intro i j hi hj hL_eq; funext a; cases a with
      | L => exact hL_eq
      | m => linarith [hgood_Lm i hi, hgood_Lm j hj]
      | s => rw [hgood_s i hi, hgood_s j hj]
    -- (m,s)-bridge has ≤ 2 distinct k₀-step vectors → every good vector is Q or R
    have hms_le2 : (distinctKStepVectors (identifyPair w .m .s) k₀).card ≤ 2 := by
      rw [distinctKStepVectors_card_eq]; exact hmosms.2 k₀ hk₀_pos hk₀_lt
    have hident_mem : ∀ j,
        Necklace.kStepVector (identifyPair w .m .s) j k₀ ∈
        distinctKStepVectors (identifyPair w .m .s) k₀ := by
      intro j; unfold distinctKStepVectors Necklace.allKStepVectors
      rw [List.mem_toFinset, List.mem_map]
      exact ⟨j % n, List.mem_range.mpr (Nat.mod_lt _ hn_pos), kStepVector_mod_n _ _ _⟩
    have hident_L : ∀ j,
        (Necklace.kStepVector (identifyPair w .m .s) j k₀) .L =
        (Necklace.kStepVector w j k₀) .L := by
      intro j; rw [identifyPair_kStepVector w .m .s (by decide) j k₀]; simp [ZVector.identifyPair]
    have hvQR_ne : Necklace.kStepVector (identifyPair w .m .s) r k₀ ≠
        Necklace.kStepVector (identifyPair w .m .s) (r + i₁ * k₀) k₀ := by
      intro heq; apply hQR_L_ne
      change (Necklace.kStepVector w r k₀) .L = (Necklace.kStepVector w (r + i₁ * k₀) k₀) .L
      rw [← hident_L, ← hident_L, heq]
    have hms_eq2 : (distinctKStepVectors (identifyPair w .m .s) k₀).card = 2 := by
      have hge := Finset.card_le_card (show
          {Necklace.kStepVector (identifyPair w .m .s) r k₀,
           Necklace.kStepVector (identifyPair w .m .s) (r + i₁ * k₀) k₀} ⊆
          distinctKStepVectors (identifyPair w .m .s) k₀ from
        Finset.insert_subset_iff.mpr
          ⟨hident_mem r, Finset.singleton_subset_iff.mpr (hident_mem (r + i₁ * k₀))⟩)
      rw [Finset.card_pair hvQR_ne] at hge; omega
    -- Every good-position vector is Q or R
    have h_two_types : ∀ i, i < n - 1 →
        Necklace.kStepVector w (r + i * k₀) k₀ = Q ∨
        Necklace.kStepVector w (r + i * k₀) k₀ = R := by
      intro i hi
      by_cases heq_vQ : Necklace.kStepVector (identifyPair w .m .s) (r + i * k₀) k₀ =
          Necklace.kStepVector (identifyPair w .m .s) r k₀
      · left; have hL_eq : (Necklace.kStepVector w (r + i * k₀) k₀) .L =
            (Necklace.kStepVector w (r + 0 * k₀) k₀) .L := by
          rw [h0k]; rw [← hident_L, ← hident_L, heq_vQ]
        have h := hgood_det i 0 hi (by omega) hL_eq; rw [h0k] at h; exact h
      · right
        have h1 : ((distinctKStepVectors (identifyPair w .m .s) k₀).erase
            (Necklace.kStepVector (identifyPair w .m .s) r k₀)).card = 1 := by
          rw [Finset.card_erase_of_mem (hident_mem r)]; omega
        obtain ⟨u, hu⟩ := Finset.card_eq_one.mp h1
        have hvu := Finset.mem_singleton.mp
          (hu ▸ Finset.mem_erase.mpr ⟨heq_vQ, hident_mem (r + i * k₀)⟩)
        have hRu := Finset.mem_singleton.mp
          (hu ▸ Finset.mem_erase.mpr ⟨hvQR_ne.symm, hident_mem (r + i₁ * k₀)⟩)
        exact hgood_det i i₁ hi hi₁_lt (by rw [← hident_L, ← hident_L, hvu.trans hRu.symm])
    -- Closing position differs from Q and R
    have hclose_ne_Q : Necklace.kStepVector w (r + (n - 1) * k₀) k₀ ≠ Q := by
      intro heq; apply hclose_s_ne; rw [heq]
      have := hgood_s 0 (by omega); rwa [h0k] at this
    have hclose_ne_R : Necklace.kStepVector w (r + (n - 1) * k₀) k₀ ≠ R := by
      intro heq; apply hclose_s_ne; rw [heq]; exact hgood_s i₁ hi₁_lt
    -- KEY: Force alternation using count_L = count_m
    -- Balance at k₀ forces |Q.L - R.L| = 1
    have hd_abs : |Q .L - R .L| = 1 := by
      have hb : (Q .L - R .L).natAbs ≤ 1 :=
        balanced_kStepVector_diff' w hbal k₀ hk₀_pos hk₀_lt r (r + i₁ * k₀) .L
      have hne : Q .L - R .L ≠ 0 := sub_ne_zero.mpr hQR_L_ne
      have hpos := Int.natAbs_pos.mpr hne
      have h1 : (Q .L - R .L).natAbs = 1 := by omega
      rw [Int.abs_eq_natAbs]; exact_mod_cast h1
    -- Set d = R.L - Q.L (= ±1)
    set d := R .L - Q .L with hd_def
    have hd_pm1 : d = 1 ∨ d = -1 := by
      have : |Q .L - R .L| = 1 := hd_abs
      rw [abs_eq (by norm_num : (1 : ℤ) ≥ 0)] at this
      rcases this with h | h <;> [right; left] <;> linarith
    -- Q and R share the same s-count and the same L+m total
    have hQR_s : Q .s = R .s := by
      have h0 := hgood_s 0 (by omega); rw [h0k] at h0
      have hi := hgood_s i₁ hi₁_lt
      linarith
    have hQR_Lm : Q .L + Q .m = R .L + R .m := by
      have h0 := hgood_Lm 0 (by omega); rw [h0k] at h0
      have hi := hgood_Lm i₁ hi₁_lt; linarith
    -- So R.m = Q.m - d
    have hRm : R .m = Q .m - d := by linarith [hQR_Lm]
    -- And R.L - R.m = (Q.L - Q.m) + 2d
    have hRLm : R .L - R .m = (Q .L - Q .m) + 2 * d := by linarith [hRm]
    -- Stacking sum: ∑_{j=0}^{n-1} (L_j - m_j) = k₀ * (count_L - count_m) = 0
    have hstack_diff : ∑ j ∈ Finset.range n,
        (Necklace.kStepVector w (r + j * k₀) k₀ .L -
         Necklace.kStepVector w (r + j * k₀) k₀ .m) = 0 := by
      have hL := kStepVector_stacking_sum w k₀ r hk₀_cop (by omega) StepSize.L
      have hm := kStepVector_stacking_sum w k₀ r hk₀_cop (by omega) StepSize.m
      rw [heq] at hL; rw [Finset.sum_sub_distrib]; linarith
    -- Closing position: determine C.L - C.m
    -- From balance: |C.s - g.s| ≤ 1 and C.s ≠ g.s, so C.s = g.s ± 1
    -- From balance + total: C.L ∈ {Q.L, R.L} and C.m ∈ {Q.m, R.m}
    -- Both cases give C.L - C.m = (Q.L - Q.m) + d
    set C := Necklace.kStepVector w (r + (n - 1) * k₀) k₀ with hC_def
    have hCLm : C .L - C .m = (Q .L - Q .m) + d := by
      -- Balance at k₀: |C.L - Q.L| ≤ 1 and |C.L - R.L| ≤ 1
      have hbL_Q := balanced_kStepVector_diff' w hbal k₀ hk₀_pos hk₀_lt
        (r + (n - 1) * k₀) r .L
      have hbL_R := balanced_kStepVector_diff' w hbal k₀ hk₀_pos hk₀_lt
        (r + (n - 1) * k₀) (r + i₁ * k₀) .L
      have hbm_Q := balanced_kStepVector_diff' w hbal k₀ hk₀_pos hk₀_lt
        (r + (n - 1) * k₀) r .m
      have hbm_R := balanced_kStepVector_diff' w hbal k₀ hk₀_pos hk₀_lt
        (r + (n - 1) * k₀) (r + i₁ * k₀) .m
      -- C.L is within 1 of both Q.L and R.L, where |Q.L - R.L| = 1
      -- So C.L ∈ {Q.L, R.L}
      have hCL : C .L = Q .L ∨ C .L = R .L := by
        have h1 : |C .L - Q .L| ≤ 1 := by rw [Int.abs_eq_natAbs]; exact_mod_cast hbL_Q
        have h2 : |C .L - R .L| ≤ 1 := by rw [Int.abs_eq_natAbs]; exact_mod_cast hbL_R
        rw [abs_le] at h1 h2
        by_cases hc : C .L = Q .L
        · exact Or.inl hc
        · right; rcases hd_pm1 with hd1 | hd1 <;> omega
      have hCm : C .m = Q .m ∨ C .m = R .m := by
        have h1 : |C .m - Q .m| ≤ 1 := by rw [Int.abs_eq_natAbs]; exact_mod_cast hbm_Q
        have h2 : |C .m - R .m| ≤ 1 := by rw [Int.abs_eq_natAbs]; exact_mod_cast hbm_R
        rw [abs_le] at h1 h2; rw [hRm] at h2
        by_cases hc : C .m = Q .m
        · exact Or.inl hc
        · right; rcases hd_pm1 with hd1 | hd1 <;> omega
      -- C.L + C.m ≠ Q.L + Q.m (since C.s ≠ Q.s = g.s)
      have hCLm_ne : C .L + C .m ≠ Q .L + Q .m := by
        intro heq'
        have hCs : C .s = Q .s := by
          have h1 := kStepVector_total_count_ternary w (r + (n - 1) * k₀) k₀
          have h2 := kStepVector_total_count_ternary w r k₀
          change C .L + C .m + C .s = ↑k₀ at h1
          change Q .L + Q .m + Q .s = ↑k₀ at h2
          linarith
        exact hclose_s_ne (hCs.trans (hgood_s 0 (by omega) |>.symm.trans (by rw [h0k])).symm)
      -- Eliminate impossible combinations
      rcases hCL with hCL | hCL <;> rcases hCm with hCm | hCm
      · -- C.L = Q.L, C.m = Q.m → C.L + C.m = Q.L + Q.m, contradiction
        exfalso; exact hCLm_ne (by rw [hCL, hCm])
      · -- C.L = Q.L, C.m = R.m
        rw [hCL, hCm, hRm]; ring
      · -- C.L = R.L, C.m = Q.m
        rw [hCL, hCm]; linarith
      · -- C.L = R.L, C.m = R.m → C.L + C.m = R.L + R.m = Q.L + Q.m, contradiction
        exfalso; exact hCLm_ne (by rw [hCL, hCm]; linarith [hQR_Lm])
    -- Now prove alternation is forced
    -- Split the stacking sum into good positions + closing position
    have hsum_split : (∑ j ∈ Finset.range (n - 1),
        (Necklace.kStepVector w (r + j * k₀) k₀ .L -
         Necklace.kStepVector w (r + j * k₀) k₀ .m)) +
        (C .L - C .m) = 0 := by
      have h := hstack_diff
      have hn1 : n = (n - 1) + 1 := by omega
      conv at h => lhs; rw [show Finset.range n = Finset.range ((n - 1) + 1) from by rw [← hn1]]
      rw [Finset.sum_range_succ] at h; exact h
    -- Each good position contributes Q.L - Q.m (if Q) or (Q.L - Q.m) + 2d (if R)
    -- Sum over good = (n-1)(Q.L - Q.m) + 2d * nR where nR = #{j < n-1 | V(j) = R}
    -- Combined: (n-1)(Q.L - Q.m) + 2d * nR + (Q.L - Q.m) + d = 0
    -- i.e., n(Q.L - Q.m) + d(2*nR + 1) = 0
    set a := Q .L - Q .m with ha_def
    -- Express each term in the good-position sum
    have hterm : ∀ j, j < n - 1 →
        Necklace.kStepVector w (r + j * k₀) k₀ .L -
        Necklace.kStepVector w (r + j * k₀) k₀ .m =
        a + (if Necklace.kStepVector w (r + j * k₀) k₀ = R then 2 * d else 0) := by
      intro j hj
      rcases h_two_types j hj with hQ | hR
      · rw [hQ, if_neg (fun h => hQR_L_ne (congr_fun h .L))]; simp; rfl
      · rw [hR, if_pos rfl]; linarith [hRLm]
    have hgood_sum : ∑ j ∈ Finset.range (n - 1),
        (Necklace.kStepVector w (r + j * k₀) k₀ .L -
         Necklace.kStepVector w (r + j * k₀) k₀ .m) =
        (↑(n - 1) : ℤ) * a + 2 * d * ↑((Finset.range (n - 1)).filter
          (fun j => Necklace.kStepVector w (r + j * k₀) k₀ = R)).card := by
      rw [Finset.sum_congr rfl (fun j hj => hterm j (Finset.mem_range.mp hj))]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
      simp only [nsmul_eq_mul]
      congr 1
      rw [← Finset.sum_filter, Finset.sum_const]
      simp only [nsmul_eq_mul]; ring
    set nR := ((Finset.range (n - 1)).filter
      (fun j => Necklace.kStepVector w (r + j * k₀) k₀ = R)).card
    -- Key equation: n * a + d * (2 * nR + 1) = 0
    have hkey : (↑n : ℤ) * a + d * (2 * ↑nR + 1) = 0 := by
      have h1 := hsum_split
      rw [hgood_sum, hCLm] at h1
      have hn1 : (↑(n - 1) : ℤ) = ↑n - 1 := by omega
      rw [hn1] at h1; ring_nf at h1 ⊢; linarith
    -- nR < n - 1 (position 0 is Q, so at least one Q exists)
    have hnR_lt : nR < n - 1 := by
      have h0Q : 0 ∈ Finset.range (n - 1) \ (Finset.range (n - 1)).filter
          (fun j => Necklace.kStepVector w (r + j * k₀) k₀ = R) := by
        rw [Finset.mem_sdiff]; exact ⟨Finset.mem_range.mpr (by omega), by
          rw [Finset.mem_filter]; push_neg; intro _
          rw [h0k]; exact fun h => hQR_L_ne (congr_fun (h ▸ rfl : Q = R) .L)⟩
      have := Finset.card_pos.mpr ⟨0, h0Q⟩
      have := Finset.card_sdiff_add_card_eq_card
        (Finset.filter_subset (fun j => Necklace.kStepVector w (r + j * k₀) k₀ = R)
          (Finset.range (n - 1)))
      rw [Finset.card_range] at this; omega
    -- nR ≥ 1 (position i₁ is R)
    have hnR_ge1 : nR ≥ 1 := by
      have hi₁_mem : i₁ ∈ (Finset.range (n - 1)).filter
          (fun j => Necklace.kStepVector w (r + j * k₀) k₀ = R) :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi₁_lt, rfl⟩
      exact Finset.card_pos.mpr ⟨i₁, hi₁_mem⟩
    -- From hkey: n * a = -d * (2 * nR + 1)
    -- Since n is odd and 2*nR + 1 is odd, and |d| = 1:
    -- n | (2*nR + 1). Since 1 ≤ 2*nR + 1 ≤ 2*(n-2) + 1 = 2n - 3 < 2n,
    -- the only possibility is 2*nR + 1 = n, giving nR = (n-1)/2.
    -- Then a = -d.
    have h2nR1_eq_n : 2 * (nR : ℤ) + 1 = ↑n := by
      have h1 : (↑n : ℤ) ∣ d * (2 * ↑nR + 1) := ⟨-a, by linarith⟩
      -- Since gcd(d, n) = 1 (d = ±1), n | (2*nR + 1)
      have hcop_d_n : IsCoprime d (↑n : ℤ) := by
        rcases hd_pm1 with h | h
        · rw [h]; exact isCoprime_one_left
        · rw [h]; exact IsCoprime.neg_left isCoprime_one_left
      have h2 : (↑n : ℤ) ∣ 2 * ↑nR + 1 :=
        hcop_d_n.symm.dvd_of_dvd_mul_left h1
      -- 1 ≤ 2*nR + 1 ≤ 2n - 3
      have h_lb : (1 : ℤ) ≤ 2 * ↑nR + 1 := by omega
      have h_ub : 2 * (nR : ℤ) + 1 ≤ 2 * ↑n - 3 := by
        have : nR ≤ n - 2 := by omega
        omega
      -- Only multiple of n in [1, 2n-3] is n itself
      obtain ⟨c, hc⟩ := h2
      have hn_ge3_int : (n : ℤ) ≥ 3 := by exact_mod_cast hn_ge3
      have hc_pos : c > 0 := by nlinarith
      have hc_le1 : c ≤ 1 := by nlinarith
      have : c = 1 := by omega
      subst this; linarith
    have ha_eq : a = -d := by
      have h := hkey; rw [h2nR1_eq_n] at h
      have hn0 : (↑n : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have : ↑n * (a + d) = 0 := by linear_combination h
      have := (mul_eq_zero.mp this).resolve_left hn0
      linarith
    -- Now show alternation is forced by proving no consecutive same-type pair.
    -- Key insight: nR = (n-1)/2 (from 2*nR+1 = n), position 0 is Q,
    -- and the (m,s) MOS at 2k₀ forbids QQ + RR coexisting (hdichotomy).
    -- If QQ exists: no RR → R is isolated → maximum (n-1)/2 isolated R's
    -- in n-1 positions starting with Q forces QRQR...QR, contradicting QQ.
    -- Same argument for RR by symmetry.
    -- Use hdichotomy from the (m,s) MOS at 2k₀
    have hcop_2k : Nat.Coprime (2 * k₀) n := by
      have : Nat.Coprime 2 n := by rw [Nat.coprime_two_left]; rwa [Nat.odd_iff]
      exact this.mul_left hk₀_cop
    have hms_2k_le2 :
        (distinctKStepVectors (identifyPair w .m .s) (2 * k₀)).card ≤ 2 := by
      have hk₂_pos : 0 < (2 * k₀) % n := by
        rw [Nat.pos_iff_ne_zero]; intro h0
        have : n ∣ Nat.gcd (2 * k₀) n :=
          Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h0) dvd_rfl
        rw [hcop_2k] at this; exact absurd (Nat.le_of_dvd one_pos this) (by omega)
      have : (distinctKStepVectors (identifyPair w .m .s) (2 * k₀)).card =
          (distinctKStepVectors (identifyPair w .m .s) ((2 * k₀) % n)).card := by
        unfold distinctKStepVectors; exact kStepVectors_card_mod_n _ _
      rw [this, distinctKStepVectors_card_eq]; exact hmosms.2 _ hk₂_pos (Nat.mod_lt _ hn_pos)
    have h2k_L : ∀ j,
        (Necklace.kStepVector (identifyPair w .m .s) (r + j * k₀) (2 * k₀)) .L =
        (Necklace.kStepVector w (r + j * k₀) k₀) .L +
        (Necklace.kStepVector w (r + (j + 1) * k₀) k₀) .L := by
      intro j
      have := kStepVector_add (identifyPair w .m .s) (r + j * k₀) k₀ k₀ .L
      rw [show k₀ + k₀ = 2 * k₀ from by ring,
          show r + j * k₀ + k₀ = r + (j + 1) * k₀ from by ring] at this
      rw [this, hident_L, hident_L]
    have hmem_2k : ∀ j,
        Necklace.kStepVector (identifyPair w .m .s) j (2 * k₀) ∈
        distinctKStepVectors (identifyPair w .m .s) (2 * k₀) := by
      intro j; unfold distinctKStepVectors Necklace.allKStepVectors
      rw [List.mem_toFinset, List.mem_map]
      exact ⟨j % n, List.mem_range.mpr (Nat.mod_lt _ hn_pos), kStepVector_mod_n _ _ _⟩
    have hQR_ne : Q ≠ R := fun h => hQR_L_ne (congr_fun h .L)
    -- hdichotomy: QQ and RR can't both exist (would give 3 distinct 2k₀ types)
    have hdichotomy :
        (∀ i, i + 1 < n - 1 →
          ¬ (Necklace.kStepVector w (r + i * k₀) k₀ = Q ∧
             Necklace.kStepVector w (r + (i + 1) * k₀) k₀ = Q)) ∨
        (∀ i, i + 1 < n - 1 →
          ¬ (Necklace.kStepVector w (r + i * k₀) k₀ = R ∧
             Necklace.kStepVector w (r + (i + 1) * k₀) k₀ = R)) := by
      -- A mixed pair exists (since both Q and R occur among good positions)
      have hmixed_exists : ∃ j₁, j₁ + 1 < n - 1 ∧
          Necklace.kStepVector w (r + j₁ * k₀) k₀ ≠
          Necklace.kStepVector w (r + (j₁ + 1) * k₀) k₀ := by
        by_contra hall; push_neg at hall
        have : ∀ i, i < n - 1 → Necklace.kStepVector w (r + i * k₀) k₀ = Q := by
          intro i hi; induction i with
          | zero => rw [h0k]
          | succ j ih => rw [← hall j (by omega)]; exact ih (by omega)
        exact hi₁_ne (this i₁ hi₁_lt)
      obtain ⟨j₁, hj₁_lt, hj₁_ne⟩ := hmixed_exists
      have hMix_L :
          (Necklace.kStepVector (identifyPair w .m .s) (r + j₁ * k₀) (2 * k₀)) .L =
          Q .L + R .L := by
        rw [h2k_L]; rcases h_two_types j₁ (by omega) with hj₁Q | hj₁R
        · rw [hj₁Q, (h_two_types (j₁ + 1) (by omega)).resolve_left
            (fun h => hj₁_ne (hj₁Q.trans h.symm))]
        · rw [hj₁R, (h_two_types (j₁ + 1) (by omega)).resolve_right
            (fun h => hj₁_ne (hj₁R.trans h.symm)), add_comm]
      by_contra h; push_neg at h
      obtain ⟨⟨i₂, hi₂, hiQ, hi1Q⟩, ⟨i₃, hi₃, hiR, hi1R⟩⟩ := h
      have hQQ_L := h2k_L i₂; rw [hiQ, hi1Q] at hQQ_L
      have hRR_L := h2k_L i₃; rw [hiR, hi1R] at hRR_L
      have hd12 : Necklace.kStepVector (identifyPair w .m .s) (r + i₂ * k₀) (2 * k₀) ≠
          Necklace.kStepVector (identifyPair w .m .s) (r + j₁ * k₀) (2 * k₀) := by
        intro h; have := congr_fun h .L; rw [hQQ_L, hMix_L] at this
        exact hQR_L_ne (by linarith)
      have hd13 : Necklace.kStepVector (identifyPair w .m .s) (r + i₂ * k₀) (2 * k₀) ≠
          Necklace.kStepVector (identifyPair w .m .s) (r + i₃ * k₀) (2 * k₀) := by
        intro h; have := congr_fun h .L; rw [hQQ_L, hRR_L] at this
        exact hQR_L_ne (by linarith)
      have hd23 : Necklace.kStepVector (identifyPair w .m .s) (r + j₁ * k₀) (2 * k₀) ≠
          Necklace.kStepVector (identifyPair w .m .s) (r + i₃ * k₀) (2 * k₀) := by
        intro h; have := congr_fun h .L; rw [hMix_L, hRR_L] at this
        exact hQR_L_ne (by linarith)
      have hge3 : 3 ≤ (distinctKStepVectors (identifyPair w .m .s) (2 * k₀)).card :=
        calc 3 = ({Necklace.kStepVector (identifyPair w .m .s) (r + i₂ * k₀) (2 * k₀),
                   Necklace.kStepVector (identifyPair w .m .s) (r + j₁ * k₀) (2 * k₀),
                   Necklace.kStepVector (identifyPair w .m .s) (r + i₃ * k₀) (2 * k₀)}
                  : Finset _).card := by
              rw [Finset.card_insert_of_notMem (by simp [hd12, hd13]),
                  Finset.card_insert_of_notMem (by simp [hd23]), Finset.card_singleton]
          _ ≤ _ := Finset.card_le_card (Finset.insert_subset_iff.mpr
              ⟨hmem_2k _, Finset.insert_subset_iff.mpr
                ⟨hmem_2k _, Finset.singleton_subset_iff.mpr (hmem_2k _)⟩⟩)
      omega
    -- Now prove: no same-type consecutive pair can exist.
    -- The injection argument: if QQ exists but no RR, then R is isolated,
    -- and nR = (n-1)/2 isolated R's in n-1 positions starting with Q
    -- forces perfect alternation QRQR...QR, contradicting QQ.
    -- Key combinatorial fact: in a binary sequence of even length 2m starting
    -- with Q, with m R's all isolated (no adjacent R's), the sequence is QRQR...QR.
    have halt : ∀ i, i + 1 < n - 1 →
        Necklace.kStepVector w (r + i * k₀) k₀ ≠
        Necklace.kStepVector w (r + (i + 1) * k₀) k₀ := by
      intro i hi heq_vi
      rcases h_two_types i (by omega) with hQ_i | hR_i <;>
        rcases h_two_types (i + 1) (by omega) with hQ_i1 | hR_i1
      · -- QQ case: derive contradiction via injection argument
        -- hdichotomy → no RR
        have hno_RR : ∀ j, j + 1 < n - 1 →
            ¬ (Necklace.kStepVector w (r + j * k₀) k₀ = R ∧
               Necklace.kStepVector w (r + (j + 1) * k₀) k₀ = R) := by
          rcases hdichotomy with h | h
          · exfalso; exact h i hi ⟨hQ_i, hQ_i1⟩
          · exact h
        -- Injection: each R at position j ≥ 1 has predecessor j-1 = Q (no RR).
        -- Position 0 = Q, so no R at 0.
        -- This gives |{R positions}| ≤ |{Q positions}| - 1
        -- (the injection j ↦ j-1 misses Q-position i, since i+1 is Q not R).
        -- But 2*nR + 1 = n forces nR = nQ = (n-1)/2. Contradiction.
        -- Count R-positions more than Q-positions minus 1
        have hnR_strict : 2 * (((Finset.range (n - 1)).filter
            (fun j => Necklace.kStepVector w (r + j * k₀) k₀ = R)).card : ℤ) + 1 ≤
            ↑n - 2 := by
          set SR := (Finset.range (n - 1)).filter
            (fun j => Necklace.kStepVector w (r + j * k₀) k₀ = R)
          set SQ := (Finset.range (n - 1)).filter
            (fun j => Necklace.kStepVector w (r + j * k₀) k₀ = Q)
          -- No R at position 0
          have hR_ge1 : ∀ j ∈ SR, j ≥ 1 := by
            intro j hj; rw [Finset.mem_filter] at hj
            by_contra h; push_neg at h
            have := Nat.lt_one_iff.mp h; subst this
            rw [h0k] at hj; exact hQR_ne (hj.2 ▸ rfl)
          -- Predecessor of each R is Q (no RR + h_two_types)
          have hR_pred_Q : ∀ j ∈ SR, j - 1 ∈ SQ := by
            intro j hj
            have hj_lt := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
            have hj_R := (Finset.mem_filter.mp hj).2
            have hj1 : j - 1 < n - 1 := by omega
            have hj_ge := hR_ge1 j hj
            have hpred : Necklace.kStepVector w (r + (j - 1) * k₀) k₀ = Q := by
              rcases h_two_types (j - 1) hj1 with h | h
              · exact h
              · exfalso; have hj1j : j - 1 + 1 = j := by omega
                exact hno_RR (j - 1) (by omega) ⟨h, hj1j ▸ hj_R⟩
            exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj1, hpred⟩
          -- f(j) = j - 1 is injective on SR
          have hf_inj : ∀ j₁ ∈ SR, ∀ j₂ ∈ SR, j₁ - 1 = j₂ - 1 → j₁ = j₂ := by
            intro j₁ hj₁ j₂ hj₂ heq
            have := hR_ge1 j₁ hj₁; have := hR_ge1 j₂ hj₂; omega
          -- Position i is in SQ but not in the image of f
          have hi_Q : i ∈ SQ :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hQ_i⟩
          have hi_not_hit : ∀ j ∈ SR, j - 1 ≠ i := by
            intro j hj heq
            have hj_ge := hR_ge1 j hj
            have : j = i + 1 := by omega
            rw [this] at hj
            exact hQR_L_ne (congr_fun (hQ_i1.symm.trans (Finset.mem_filter.mp hj).2) .L)
          -- So f maps SR injectively into SQ \ {i}
          have hcard_le : SR.card ≤ SQ.card - 1 := by
            have hle := Finset.card_le_card_of_injOn (fun j => j - 1)
              (fun j hj => Finset.mem_erase.mpr ⟨hi_not_hit j hj, hR_pred_Q j hj⟩)
              (fun j₁ hj₁ j₂ hj₂ h => hf_inj j₁ (Finset.mem_coe.mp hj₁) j₂ (Finset.mem_coe.mp hj₂) h)
            rw [Finset.card_erase_of_mem hi_Q] at hle; exact hle
          -- SQ + SR = n - 1
          have hSQR : SQ.card + SR.card = n - 1 := by
            have hdisj : Disjoint SQ SR := by
              rw [Finset.disjoint_filter]
              intro j _ hQ hR; exact hQR_L_ne (congr_fun (hQ.symm.trans hR) .L)
            have hunion : SQ ∪ SR = Finset.range (n - 1) := by
              ext j; rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
              constructor
              · rintro (⟨hj, _⟩ | ⟨hj, _⟩) <;> exact hj
              · intro hj; have := h_two_types j (Finset.mem_range.mp hj)
                rcases this with h | h
                · left; exact ⟨hj, h⟩
                · right; exact ⟨hj, h⟩
            rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_range]
          omega
        linarith [h2nR1_eq_n]
      · -- QR case: V(i) = Q, V(i+1) = R. But heq_vi says they're equal.
        exact hQR_ne (hQ_i.symm.trans heq_vi |>.trans hR_i1)
      · -- RQ case: similar
        exact hQR_ne (hR_i.symm.trans heq_vi |>.trans hQ_i1).symm
      · -- RR case: hdichotomy → no QQ
        have hno_QQ : ∀ j, j + 1 < n - 1 →
            ¬ (Necklace.kStepVector w (r + j * k₀) k₀ = Q ∧
               Necklace.kStepVector w (r + (j + 1) * k₀) k₀ = Q) := by
          rcases hdichotomy with h | h
          · exact h
          · exfalso; exact h i hi ⟨hR_i, hR_i1⟩
        -- Split on V(n-2) (last good position)
        rcases h_two_types (n - 2) (by omega) with hVlast_Q | hVlast_R
        · -- V(n-2) = Q: use (L,s) bridge at 2k₀ to get 3 types → contradiction
          -- The cross pair at position n-2 spans good position n-2 (Q) and closing (C).
          -- C.L = R.L and C.m = Q.m (from balance + hCLm_ne constraints).
          -- (L,s) bridge 2k₀ L-values: RR→2R.m, mixed→Q.m+R.m, cross→2Q.m.
          -- These are 3 distinct values → contradiction with ≤ 2 types.
          -- First show C.L = R.L by (m,s) bridge 2k₀ constraint
          have hCL_eq : C .L = R .L := by
            -- V(n-2)=Q. 2k₀ (m,s) cross L = Q.L + C.L. Types are 2R.L (RR) and Q.L+R.L (mixed).
            -- If C.L = Q.L: cross = 2Q.L, giving 3rd type. Contradiction.
            have hMix_exists : ∃ j₁, j₁ + 1 < n - 1 ∧
                Necklace.kStepVector w (r + j₁ * k₀) k₀ ≠
                Necklace.kStepVector w (r + (j₁ + 1) * k₀) k₀ := by
              by_contra hall; push_neg at hall
              have : ∀ j, j < n - 1 → Necklace.kStepVector w (r + j * k₀) k₀ = Q := by
                intro j hj; induction j with
                | zero => rw [h0k]
                | succ j ih => rw [← hall j (by omega)]; exact ih (by omega)
              exact hi₁_ne (this i₁ hi₁_lt)
            obtain ⟨j₁, hj₁_lt, hj₁_ne⟩ := hMix_exists
            have hMix_L :
                (Necklace.kStepVector (identifyPair w .m .s) (r + j₁ * k₀) (2 * k₀)) .L =
                Q .L + R .L := by
              rw [h2k_L]; rcases h_two_types j₁ (by omega) with h1 | h1
              · rw [h1, (h_two_types (j₁ + 1) (by omega)).resolve_left
                  (fun h => hj₁_ne (h1.trans h.symm))]
              · rw [h1, (h_two_types (j₁ + 1) (by omega)).resolve_right
                  (fun h => hj₁_ne (h1.trans h.symm)), add_comm]
            have hRR_L := h2k_L i; rw [hR_i, hR_i1] at hRR_L
            -- C.L must be R.L; if C.L = Q.L, cross gives 3rd type
            rcases (show C .L = Q .L ∨ C .L = R .L from by
              -- Same analysis as hCL from above
              have hbL_Q := balanced_kStepVector_diff' w hbal k₀ hk₀_pos hk₀_lt
                (r + (n - 1) * k₀) r .L
              have hbL_R := balanced_kStepVector_diff' w hbal k₀ hk₀_pos hk₀_lt
                (r + (n - 1) * k₀) (r + i₁ * k₀) .L
              have h1 : |C .L - Q .L| ≤ 1 := by rw [Int.abs_eq_natAbs]; exact_mod_cast hbL_Q
              have h2 : |C .L - R .L| ≤ 1 := by rw [Int.abs_eq_natAbs]; exact_mod_cast hbL_R
              rw [abs_le] at h1 h2
              by_cases hc : C .L = Q .L
              · exact Or.inl hc
              · right; rcases hd_pm1 with hd1 | hd1 <;> omega) with hCLQ | hCLR
            · -- C.L = Q.L → 3 types in (m,s) bridge at 2k₀
              exfalso
              have hcross_L := h2k_L (n - 2)
              rw [show n - 2 + 1 = n - 1 from by omega, hVlast_Q] at hcross_L
              -- hcross_L: ... .L = Q.L + C.L, where C.L = Q.L
              -- Distinctness proofs use hcross_L + hCLQ via linarith
              have hd1 : Necklace.kStepVector (identifyPair w .m .s) (r + (n - 2) * k₀) (2 * k₀) ≠
                  Necklace.kStepVector (identifyPair w .m .s) (r + i * k₀) (2 * k₀) := by
                intro h; have := congr_fun h .L; rw [hRR_L] at this
                exact hQR_L_ne (by linarith [hcross_L, hCLQ])
              have hd2 : Necklace.kStepVector (identifyPair w .m .s) (r + (n - 2) * k₀) (2 * k₀) ≠
                  Necklace.kStepVector (identifyPair w .m .s) (r + j₁ * k₀) (2 * k₀) := by
                intro h; have := congr_fun h .L; rw [hMix_L] at this
                exact hQR_L_ne (by linarith [hcross_L, hCLQ])
              have hd3 : Necklace.kStepVector (identifyPair w .m .s) (r + i * k₀) (2 * k₀) ≠
                  Necklace.kStepVector (identifyPair w .m .s) (r + j₁ * k₀) (2 * k₀) := by
                intro h; have := congr_fun h .L; rw [hRR_L, hMix_L] at this
                exact hQR_L_ne (by linarith)
              have hge3 : 3 ≤ (distinctKStepVectors (identifyPair w .m .s) (2 * k₀)).card :=
                calc 3 = ({Necklace.kStepVector (identifyPair w .m .s) (r + (n - 2) * k₀) (2 * k₀),
                           Necklace.kStepVector (identifyPair w .m .s) (r + i * k₀) (2 * k₀),
                           Necklace.kStepVector (identifyPair w .m .s) (r + j₁ * k₀) (2 * k₀)}
                          : Finset _).card := by
                      rw [Finset.card_insert_of_notMem (by simp [hd1, hd2]),
                          Finset.card_insert_of_notMem (by simp [hd3]), Finset.card_singleton]
                  _ ≤ _ := Finset.card_le_card (Finset.insert_subset_iff.mpr
                      ⟨hmem_2k _, Finset.insert_subset_iff.mpr
                        ⟨hmem_2k _, Finset.singleton_subset_iff.mpr (hmem_2k _)⟩⟩)
              omega
            · exact hCLR
          -- Now C.L = R.L. Show C.m = Q.m.
          have hCm_eq : C .m = Q .m := by
            have hCm_cases : C .m = Q .m ∨ C .m = R .m := by
              have hbm_Q := balanced_kStepVector_diff' w hbal k₀ hk₀_pos hk₀_lt
                (r + (n - 1) * k₀) r .m
              have hbm_R := balanced_kStepVector_diff' w hbal k₀ hk₀_pos hk₀_lt
                (r + (n - 1) * k₀) (r + i₁ * k₀) .m
              have h1 : |C .m - Q .m| ≤ 1 := by rw [Int.abs_eq_natAbs]; exact_mod_cast hbm_Q
              have h2 : |C .m - R .m| ≤ 1 := by rw [Int.abs_eq_natAbs]; exact_mod_cast hbm_R
              rw [abs_le] at h1 h2; rw [hRm] at h2
              by_cases hc : C .m = Q .m
              · exact Or.inl hc
              · right; rcases hd_pm1 with hd1 | hd1 <;> omega
            rcases hCm_cases with h | h
            · exact h
            · -- C.m = R.m → C.L + C.m = R.L + R.m = Q.L + Q.m → C.s = g.s → contradiction
              exfalso
              have : C .L + C .m = Q .L + Q .m := by rw [hCL_eq, h]; linarith [hQR_Lm]
              have hCs : C .s = Q .s := by
                have h1 := kStepVector_total_count_ternary w (r + (n - 1) * k₀) k₀
                have h2 := kStepVector_total_count_ternary w r k₀
                change C .L + C .m + C .s = ↑k₀ at h1
                change Q .L + Q .m + Q .s = ↑k₀ at h2; linarith
              exact hclose_s_ne (hCs.trans (hgood_s 0 (by omega) |>.symm.trans (by rw [h0k])).symm)
          -- Now use (L,s) bridge at 2k₀ to get 3 types → contradiction
          -- 2k₀ (L,s) bridge L-value = w's m-count over 2k₀ window
          have hLs_2k_le2 :
              (distinctKStepVectors (identifyPair w .L .s) (2 * k₀)).card ≤ 2 := by
            have hk₂_pos : 0 < (2 * k₀) % n := by
              rw [Nat.pos_iff_ne_zero]; intro h0
              have : n ∣ Nat.gcd (2 * k₀) n :=
                Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h0) dvd_rfl
              rw [hcop_2k] at this; exact absurd (Nat.le_of_dvd one_pos this) (by omega)
            have : (distinctKStepVectors (identifyPair w .L .s) (2 * k₀)).card =
                (distinctKStepVectors (identifyPair w .L .s) ((2 * k₀) % n)).card := by
              unfold distinctKStepVectors; exact kStepVectors_card_mod_n _ _
            rw [this, distinctKStepVectors_card_eq]; exact hmosLs.2 _ hk₂_pos (Nat.mod_lt _ hn_pos)
          have hident_m_Ls : ∀ j,
              (identifyPair w .L .s).kStepVector j k₀ .m = w.kStepVector j k₀ .m := by
            intro j; rw [identifyPair_kStepVector w .L .s (by decide) j k₀]
            simp [ZVector.identifyPair]
          have h2k_m_Ls : ∀ j,
              (Necklace.kStepVector (identifyPair w .L .s) (r + j * k₀) (2 * k₀)) .m =
              (Necklace.kStepVector w (r + j * k₀) k₀) .m +
              (Necklace.kStepVector w (r + (j + 1) * k₀) k₀) .m := by
            intro j
            have := kStepVector_add (identifyPair w .L .s) (r + j * k₀) k₀ k₀ .m
            rw [show k₀ + k₀ = 2 * k₀ from by ring,
                show r + j * k₀ + k₀ = r + (j + 1) * k₀ from by ring] at this
            rw [hident_m_Ls, hident_m_Ls] at this; exact this
          have hmem_2k_Ls : ∀ j,
              Necklace.kStepVector (identifyPair w .L .s) j (2 * k₀) ∈
              distinctKStepVectors (identifyPair w .L .s) (2 * k₀) := by
            intro j; unfold distinctKStepVectors Necklace.allKStepVectors
            rw [List.mem_toFinset, List.mem_map]
            exact ⟨j % n, List.mem_range.mpr (Nat.mod_lt _ hn_pos), kStepVector_mod_n _ _ _⟩
          -- Three 2k₀ (L,s) bridge L-values: RR→2R.m, mixed→Q.m+R.m, cross→Q.m+C.m=2Q.m
          have hRR_m := h2k_m_Ls i; rw [hR_i, hR_i1] at hRR_m
          have hMix_exists2 : ∃ j₁, j₁ + 1 < n - 1 ∧
              Necklace.kStepVector w (r + j₁ * k₀) k₀ ≠
              Necklace.kStepVector w (r + (j₁ + 1) * k₀) k₀ := by
            by_contra hall; push_neg at hall
            have : ∀ j, j < n - 1 → Necklace.kStepVector w (r + j * k₀) k₀ = Q := by
              intro j hj; induction j with
              | zero => rw [h0k]
              | succ j ih => rw [← hall j (by omega)]; exact ih (by omega)
            exact hi₁_ne (this i₁ hi₁_lt)
          obtain ⟨j₂, hj₂_lt, hj₂_ne⟩ := hMix_exists2
          have hMix_m :
              (Necklace.kStepVector (identifyPair w .L .s) (r + j₂ * k₀) (2 * k₀)) .m =
              Q .m + R .m := by
            have h := h2k_m_Ls j₂
            rcases h_two_types j₂ (by omega) with hj₂Q | hj₂R
            · rw [hj₂Q, (h_two_types (j₂ + 1) (by omega)).resolve_left
                (fun h => hj₂_ne (hj₂Q.trans h.symm))] at h; exact h
            · rw [hj₂R, (h_two_types (j₂ + 1) (by omega)).resolve_right
                (fun h => hj₂_ne (hj₂R.trans h.symm))] at h; linarith
          have hcross_m := h2k_m_Ls (n - 2)
          rw [show n - 2 + 1 = n - 1 from by omega, hVlast_Q] at hcross_m
          -- hcross_m: ... .m = Q.m + C.m, where C.m = Q.m (hCm_eq)
          -- Three pairwise distinct (L,s) types
          have hd1' : Necklace.kStepVector (identifyPair w .L .s) (r + (n - 2) * k₀) (2 * k₀) ≠
              Necklace.kStepVector (identifyPair w .L .s) (r + i * k₀) (2 * k₀) := by
            intro h; have := congr_fun h .m; rw [hRR_m] at this
            have hd0 : d = 0 := by linarith [hRm, hcross_m, hCm_eq]
            rcases hd_pm1 with h | h <;> linarith
          have hd2' : Necklace.kStepVector (identifyPair w .L .s) (r + (n - 2) * k₀) (2 * k₀) ≠
              Necklace.kStepVector (identifyPair w .L .s) (r + j₂ * k₀) (2 * k₀) := by
            intro h; have := congr_fun h .m; rw [hMix_m] at this
            have hd0 : d = 0 := by linarith [hRm, hcross_m, hCm_eq]
            rcases hd_pm1 with h | h <;> linarith
          have hd3' : Necklace.kStepVector (identifyPair w .L .s) (r + i * k₀) (2 * k₀) ≠
              Necklace.kStepVector (identifyPair w .L .s) (r + j₂ * k₀) (2 * k₀) := by
            intro h; have := congr_fun h .m; rw [hRR_m, hMix_m] at this
            have hd0 : d = 0 := by linarith [hRm]
            rcases hd_pm1 with h | h <;> linarith
          have hge3' : 3 ≤ (distinctKStepVectors (identifyPair w .L .s) (2 * k₀)).card :=
            calc 3 = ({Necklace.kStepVector (identifyPair w .L .s) (r + (n - 2) * k₀) (2 * k₀),
                       Necklace.kStepVector (identifyPair w .L .s) (r + i * k₀) (2 * k₀),
                       Necklace.kStepVector (identifyPair w .L .s) (r + j₂ * k₀) (2 * k₀)}
                      : Finset _).card := by
                  rw [Finset.card_insert_of_notMem (by simp [hd1', hd2']),
                      Finset.card_insert_of_notMem (by simp [hd3']), Finset.card_singleton]
              _ ≤ _ := Finset.card_le_card (Finset.insert_subset_iff.mpr
                  ⟨hmem_2k_Ls _, Finset.insert_subset_iff.mpr
                    ⟨hmem_2k_Ls _, Finset.singleton_subset_iff.mpr (hmem_2k_Ls _)⟩⟩)
          omega
        · -- V(n-2) = R: successor injection from Q → R works cleanly
          -- Each Q at j with j < n-2 has successor j+1 = R (no QQ).
          -- All Q's have j ≤ n-3 (since V(n-2) = R).
          -- Injection j ↦ j+1 misses R-position i+1 (since V(i) = R, not Q).
          -- So nQ ≤ nR - 1, giving 2*nR + 1 ≥ n + 2 > n. Contradicts 2*nR+1 = n.
          have hnR_strict : 2 * (((Finset.range (n - 1)).filter
              (fun j => Necklace.kStepVector w (r + j * k₀) k₀ = R)).card : ℤ) + 1 ≥
              ↑n + 2 := by
            set SR := (Finset.range (n - 1)).filter
              (fun j => Necklace.kStepVector w (r + j * k₀) k₀ = R)
            set SQ := (Finset.range (n - 1)).filter
              (fun j => Necklace.kStepVector w (r + j * k₀) k₀ = Q)
            -- All Q's are at j ≤ n-3 (V(n-2) = R)
            have hQ_lt : ∀ j ∈ SQ, j < n - 2 := by
              intro j hj; rw [Finset.mem_filter] at hj
              have hj_lt := Finset.mem_range.mp hj.1
              by_contra h; push_neg at h
              have : j = n - 2 := by omega
              rw [this] at hj
              exact hQR_L_ne (congr_fun (hj.2.symm.trans hVlast_R) .L)
            -- Successor of each Q is R (no QQ and j+1 < n-1)
            have hQ_succ_R : ∀ j ∈ SQ, j + 1 ∈ SR := by
              intro j hj
              have hj_lt := hQ_lt j hj
              have hj_Q := (Finset.mem_filter.mp hj).2
              have hsucc : Necklace.kStepVector w (r + (j + 1) * k₀) k₀ = R := by
                rcases h_two_types (j + 1) (by omega) with h | h
                · exfalso; exact hno_QQ j (by omega) ⟨hj_Q, h⟩
                · exact h
              exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hsucc⟩
            -- f(j) = j + 1 is injective
            have hf_inj : ∀ j₁ ∈ SQ, ∀ j₂ ∈ SQ, j₁ + 1 = j₂ + 1 → j₁ = j₂ :=
              fun _ _ _ _ h => by omega
            -- Position i+1 is R but not in the image
            have hi1_not_hit : ∀ j ∈ SQ, j + 1 ≠ i + 1 := by
              intro j hj heq
              have : j = i := by omega
              rw [this] at hj
              exact hQR_L_ne (congr_fun ((Finset.mem_filter.mp hj).2.symm.trans hR_i) .L)
            have hi1_R : i + 1 ∈ SR :=
              Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hR_i1⟩
            -- Injective map from SQ into SR \ {i+1}
            have hcard_le : SQ.card ≤ SR.card - 1 := by
              have hle := Finset.card_le_card_of_injOn (fun j => j + 1)
                (fun j hj => Finset.mem_erase.mpr ⟨hi1_not_hit j hj, hQ_succ_R j hj⟩)
                (fun j₁ hj₁ j₂ hj₂ h => hf_inj j₁ (Finset.mem_coe.mp hj₁) j₂ (Finset.mem_coe.mp hj₂) h)
              rw [Finset.card_erase_of_mem hi1_R] at hle; exact hle
            -- SQ + SR = n - 1
            have hSQR : SQ.card + SR.card = n - 1 := by
              have hdisj : Disjoint SQ SR := by
                rw [Finset.disjoint_filter]
                intro j _ hQ hR; exact hQR_L_ne (congr_fun (hQ.symm.trans hR) .L)
              have hunion : SQ ∪ SR = Finset.range (n - 1) := by
                ext j; rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
                constructor
                · rintro (⟨hj, _⟩ | ⟨hj, _⟩) <;> exact hj
                · intro hj; have := h_two_types j (Finset.mem_range.mp hj)
                  rcases this with h | h
                  · left; exact ⟨hj, h⟩
                  · right; exact ⟨hj, h⟩
              rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_range]
            -- SQ ≤ SR - 1 and SQ + SR = n-1 → 2*SR ≥ n → 2*SR+1 ≥ n+1 > n
            omega
          linarith [h2nR1_eq_n]
    -- Alternation → hasAS
    have h_pattern : ∀ i, i < n - 1 →
        Necklace.kStepVector w (r + i * k₀) k₀ =
        if i % 2 = 0 then Q else R := by
      intro i; induction i with
      | zero => intro _; simp; rfl
      | succ j ih =>
        intro hj1
        have hprev := ih (by omega)
        have hne := halt j (by omega)
        rw [hprev] at hne
        rcases Nat.mod_two_eq_zero_or_one j with hmod | hmod
        · rw [if_pos hmod] at hne; rw [if_neg (by omega)]
          exact (h_two_types (j + 1) hj1).resolve_left (Ne.symm hne)
        · rw [if_neg (show j % 2 ≠ 0 from by omega)] at hne
          rw [if_pos (by omega)]
          exact (h_two_types (j + 1) hj1).resolve_right (Ne.symm hne)
    exact ⟨k₀, r, fun j => if j.val = 0 then Q else R, hk₀_lt, hk₀_cop,
      fun i => by rw [h_pattern i.val i.isLt],
      fun j => by fin_cases j <;> simp <;> [exact hclose_ne_Q; exact hclose_ne_R]⟩

private lemma isBalanced_applyPerm' (σ : Equiv.Perm StepSize) (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) :
    Necklace.isBalanced (Necklace.applyPerm σ w) := by
  intro k hk hkn w1 w2 a hw1 hw2
  rw [Necklace.allKStepSubwords_applyPerm] at hw1 hw2
  simp only [List.mem_map] at hw1 hw2
  obtain ⟨w1', hw1'mem, hw1'eq⟩ := hw1
  obtain ⟨w2', hw2'mem, hw2'eq⟩ := hw2
  rw [← hw1'eq, ← hw2'eq,
      show a = σ (σ.symm a) from (σ.apply_symm_apply a).symm,
      List.count_map_of_injective _ σ σ.injective,
      List.count_map_of_injective _ σ σ.injective]
  exact hbal k hk hkn w1' w2' (σ.symm a) hw1'mem hw2'mem

/-- hasAS transfers back through applyPerm. (Copy for forward reference.) -/
private lemma hasAS_of_applyPerm' (σ : Equiv.Perm StepSize)
    (w : TernaryNecklace n)
    (h : hasAS (Necklace.applyPerm σ w)) : hasAS w := by
  obtain ⟨k₀, r, seq_σ, hk₀_lt, hcop, hseq, hclose⟩ := h
  refine ⟨k₀, r, fun j => ZVector.applyPerm σ.symm (seq_σ j), ?_, hcop, ?_, ?_⟩
  · exact hk₀_lt
  · intro i
    have h_eq := hseq i
    rw [kStepVector_applyPerm] at h_eq
    funext a
    have := congr_fun h_eq (σ a)
    simp [ZVector.applyPerm] at this ⊢
    exact this
  · intro j hj
    apply hclose j
    rw [kStepVector_applyPerm, hj]
    funext a; simp [ZVector.applyPerm]

/-- When two step counts are equal, a balanced PWF odd ternary necklace has an alternating
    sequence. Uses `applyPerm` to reduce to the count_L = count_m case. -/
private lemma balanced_two_equal_hasAS (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (htern : isTernary w)
    (hpwf : isPairwisePrimMOS w) (hodd : n % 2 = 1)
    (x y z : StepSize) (hxy : x ≠ y) (_hxz : x ≠ z) (_hyz : y ≠ z)
    (heq : Necklace.count w x = Necklace.count w y) :
    hasAS w := by
  obtain ⟨σ, hσx, hσy, _⟩ := exists_perm_x_to_L_y_to_m x y hxy
  set w' := Necklace.applyPerm σ w
  have hbal' : Necklace.isBalanced w' := isBalanced_applyPerm' σ w hbal
  have htern' : isTernary w' := (isTernary_applyPerm σ w).mpr htern
  have hpwf' : isPairwisePrimMOS w' :=
    isPairwisePrimMOS_of_applyPerm σ.symm w' (by rwa [Necklace.applyPerm_symm_cancel])
  have heq' : Necklace.count w' .L = Necklace.count w' .m := by
    rw [count_applyPerm_eq, count_applyPerm_eq,
        show σ.symm .L = x from by rw [← hσx, Equiv.symm_apply_apply],
        show σ.symm .m = y from by rw [← hσy, Equiv.symm_apply_apply]]
    exact heq
  exact hasAS_of_applyPerm' σ w (balanced_two_equal_hasAS_Lm w' hbal' htern' hpwf' hodd heq')

/-! ## Classification of Balanced MV3 -/

/-- Counting z in a slice of the identified word equals counting z in the original slice,
    when z ≠ x and z ≠ y. -/
private lemma count_slice_identifyPair (w : TernaryNecklace n)
    (x y z : StepSize) (hzx : z ≠ x) (hzy : z ≠ y) (i k : ℕ) :
    (Necklace.slice (TernaryNecklace.identifyPair w x y) i (i + k)).count z =
    (Necklace.slice w i (i + k)).count z := by
  induction k with
  | zero => simp [Necklace.slice]
  | succ k ih =>
    rw [show i + (k + 1) = i + k + 1 from by omega]
    rw [slice_extend_end (TernaryNecklace.identifyPair w x y) i k,
        slice_extend_end w i k,
        List.count_append, List.count_append, ih]
    congr 1
    simp only [List.count_cons, List.count_nil, TernaryNecklace.identifyPair]
    split <;> simp_all [Ne.symm hzy, Ne.symm hzx]

/-- For lists containing only values y and z (with y ≠ z), count y + count z = length. -/
private lemma count_yz_eq_length (l : List StepSize) (y z : StepSize) (hyz : y ≠ z)
    (honly : ∀ v ∈ l, v = y ∨ v = z) :
    l.count y + l.count z = l.length := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    have htail : ∀ v ∈ tail, v = y ∨ v = z :=
      fun v hv => honly v (List.mem_cons.mpr (Or.inr hv))
    have hhead := honly head (List.mem_cons.mpr (Or.inl rfl))
    have := ih htail
    cases head <;> cases y <;> cases z <;> simp_all [List.length_cons] <;> omega

/-- For two same-length lists using only values y and z, equal z-count implies equal multisets. -/
private lemma stepsize_multiset_eq_of_count_eq (l₁ l₂ : List StepSize)
    (hlen : l₁.length = l₂.length) (y z : StepSize)
    (honly₁ : ∀ v ∈ l₁, v = y ∨ v = z) (honly₂ : ∀ v ∈ l₂, v = y ∨ v = z)
    (hz : l₁.count z = l₂.count z) :
    (↑l₁ : Multiset StepSize) = ↑l₂ := by
  rw [Multiset.coe_eq_coe, List.perm_iff_count]
  intro a
  by_cases haz : a = z
  · subst haz; exact hz
  · by_cases hay : a = y
    · subst hay
      have h₁ := count_yz_eq_length l₁ a z haz honly₁
      have h₂ := count_yz_eq_length l₂ a z haz honly₂
      omega
    · -- a ≠ y and a ≠ z, so count a = 0 for both
      have h₁ : l₁.count a = 0 := by
        rw [List.count_eq_zero]
        intro hm
        rcases honly₁ a hm with rfl | rfl <;> contradiction
      have h₂ : l₂.count a = 0 := by
        rw [List.count_eq_zero]
        intro hm
        rcases honly₂ a hm with rfl | rfl <;> contradiction
      rw [h₁, h₂]

/-- Balanced ternary implies each pair identification is MOS.

    **Proof outline** (5.1.1(a)): For any letter `z`, the `z`-count in
    subwords of any given length varies by ≤ 1 (from balance). After
    identifying `x` and `y`, this gives a binary balanced word. For such a word,
    equal `z`-count implies equal multiset, so ≤ 2 distinct k-step multisets. -/
private lemma balanced_ternary_identification_hasMOS (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (htern : isTernary w)
    (x y : StepSize) (_hxy : x ≠ y) :
    Necklace.hasMOSProperty (w.identifyPair x y) := by
  constructor
  · exact identified_uses_two_values w htern x y _hxy
  · intro k hk hk'
    -- Find the third step size z
    have hz : ∃ z : StepSize, z ≠ x ∧ z ≠ y := by
      cases x <;> cases y <;> simp_all <;>
        first | exact ⟨.L, by decide, by decide⟩
               | exact ⟨.m, by decide, by decide⟩
               | exact ⟨.s, by decide, by decide⟩
    obtain ⟨z, hzx, hzy⟩ := hz
    -- All values in identified slices are y or z
    have hid_val : ∀ (p : ZMod n),
        TernaryNecklace.identifyPair w x y p = y ∨
        TernaryNecklace.identifyPair w x y p = z := by
      intro p
      unfold TernaryNecklace.identifyPair
      by_cases h : w p = x
      · rw [if_pos h]; exact Or.inl rfl
      · rw [if_neg h]
        cases h_wp : (w p) <;> cases x <;> cases y <;> cases z <;> simp_all
    have hvals : ∀ (i m : ℕ),
        ∀ v ∈ Necklace.slice (TernaryNecklace.identifyPair w x y) i (i + m), v = y ∨ v = z := by
      intro i m
      induction m with
      | zero => simp [Necklace.slice]
      | succ m ihm =>
        intro v hv
        rw [show i + (m + 1) = i + m + 1 from by omega,
            slice_extend_end] at hv
        rw [List.mem_append] at hv
        rcases hv with hv | hv
        · exact ihm v hv
        · rw [List.mem_singleton] at hv; rw [hv]; exact hid_val _
    -- z-count in identified slice = z-count in original slice
    have hcount_eq : ∀ (i : ℕ),
        (Necklace.slice (TernaryNecklace.identifyPair w x y) i (i + k)).count z =
        (Necklace.slice w i (i + k)).count z := by
      intro i
      exact count_slice_identifyPair w x y z hzx hzy i k
    -- z-counts in original slices vary by ≤ 1 (from balance of w)
    have hbal_z : ∀ (i j : ℕ), i < n → j < n →
        Int.natAbs (((Necklace.slice w i (i + k)).count z : ℤ) -
          ((Necklace.slice w j (j + k)).count z : ℤ)) ≤ 1 := by
      intro i j hi hj
      exact hbal k hk hk'
        (Necklace.slice w i (i + k)) (Necklace.slice w j (j + k)) z
        (List.mem_ofFn.mpr ⟨⟨i, hi⟩, rfl⟩) (List.mem_ofFn.mpr ⟨⟨j, hj⟩, rfl⟩)
    -- Unpack membership in allKStepMultisets
    set w' := TernaryNecklace.identifyPair w x y with hw'_def
    have hmem_unpack : ∀ m : Multiset StepSize,
        m ∈ Necklace.allKStepMultisets w' k →
        ∃ i : ℕ, i < n ∧ m = ↑(Necklace.slice w' i (i + k)) := by
      intro m hm
      simp only [Necklace.allKStepMultisets, Necklace.abelianize, Necklace.allKStepSubwords,
        List.mem_map, List.mem_ofFn] at hm
      obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := hm
      exact ⟨i.val, i.isLt, rfl⟩
    -- Equal z-count + equal length + only y,z → equal multiset
    have heq_mset : ∀ a b : ℕ, a < n → b < n →
        (Necklace.slice w' a (a + k)).count z =
        (Necklace.slice w' b (b + k)).count z →
        (↑(Necklace.slice w' a (a + k)) : Multiset StepSize) =
        ↑(Necklace.slice w' b (b + k)) := by
      intro a b _ _ hcount
      exact stepsize_multiset_eq_of_count_eq _ _
        (by simp [Necklace.slice_length]) y z (hvals a k) (hvals b k) hcount
    -- z-counts take ≤ 2 values, so ≤ 2 multisets
    by_cases h_eq : ∀ i : ℕ, i < n →
        (Necklace.slice w' i (i + k)).count z =
        (Necklace.slice w' 0 (0 + k)).count z
    · -- All z-counts equal: 1 multiset
      refine (Finset.card_le_card ?_).trans (by simp : ({↑(Necklace.slice w' 0 (0 + k)),
          ↑(Necklace.slice w' 0 (0 + k))} : Finset _).card ≤ 2)
      intro m hm
      rw [List.mem_toFinset] at hm
      obtain ⟨i, hi_lt, rfl⟩ := hmem_unpack m hm
      simp [heq_mset i 0 hi_lt (NeZero.pos n) (h_eq i hi_lt)]
    · -- Some position j has different z-count
      push_neg at h_eq
      obtain ⟨j, hj_lt, hj⟩ := h_eq
      have hcard_bound : ({↑(Necklace.slice w' 0 (0 + k)),
          ↑(Necklace.slice w' j (j + k))} : Finset (Multiset StepSize)).card ≤ 2 :=
        le_trans (Finset.card_insert_le _ _) (by simp)
      refine (Finset.card_le_card ?_).trans hcard_bound
      intro m hm
      rw [List.mem_toFinset] at hm
      obtain ⟨i, hi_lt, rfl⟩ := hmem_unpack m hm
      suffices (Necklace.slice w' i (i + k)).count z =
               (Necklace.slice w' 0 (0 + k)).count z ∨
               (Necklace.slice w' i (i + k)).count z =
               (Necklace.slice w' j (j + k)).count z by
        rcases this with h | h
        · simp [heq_mset i 0 hi_lt (NeZero.pos n) h]
        · simp [heq_mset i j hi_lt hj_lt h]
      -- All z-counts in {v, v+1} for some v, so 0 and j cover both values
      have h0 : Int.natAbs (((Necklace.slice w 0 (0 + k)).count z : ℤ) -
          ((Necklace.slice w i (i + k)).count z : ℤ)) ≤ 1 :=
        hbal_z 0 i (NeZero.pos n) hi_lt
      have hj' : Int.natAbs (((Necklace.slice w 0 (0 + k)).count z : ℤ) -
          ((Necklace.slice w j (j + k)).count z : ℤ)) ≤ 1 :=
        hbal_z 0 j (NeZero.pos n) hj_lt
      have hi' : Int.natAbs (((Necklace.slice w j (j + k)).count z : ℤ) -
          ((Necklace.slice w i (i + k)).count z : ℤ)) ≤ 1 :=
        hbal_z j i hj_lt hi_lt
      rw [hcount_eq, hcount_eq, hcount_eq] at *
      omega

/-- Primitive balanced ternary scales are pairwise-MOS. -/
theorem balanced_primitive_ternary_isPairwiseMOS (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (_hprim : Necklace.isPrimitive w)
    (htern : isTernary w) :
    isPairwiseMOS w :=
  ⟨balanced_ternary_identification_hasMOS w hbal htern .L .m (by decide),
   balanced_ternary_identification_hasMOS w hbal htern .m .s (by decide),
   balanced_ternary_identification_hasMOS w hbal htern .L .s (by decide)⟩

/-- Balance is preserved under step permutation. -/
private lemma isBalanced_applyPerm (σ : Equiv.Perm StepSize) (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) :
    Necklace.isBalanced (Necklace.applyPerm σ w) := by
  intro k hk hkn w1 w2 a hw1 hw2
  -- w1, w2 are k-step subwords of σ ∘ w, hence σ-images of subwords of w
  rw [Necklace.allKStepSubwords_applyPerm] at hw1 hw2
  simp only [List.mem_map] at hw1 hw2
  obtain ⟨w1', hw1'mem, hw1'eq⟩ := hw1
  obtain ⟨w2', hw2'mem, hw2'eq⟩ := hw2
  -- Count of a in σ-image = count of σ⁻¹(a) in original
  rw [← hw1'eq, ← hw2'eq,
      show a = σ (σ.symm a) from (σ.apply_symm_apply a).symm,
      List.count_map_of_injective _ σ σ.injective,
      List.count_map_of_injective _ σ σ.injective]
  exact hbal k hk hkn w1' w2' (σ.symm a) hw1'mem hw2'mem

omit [NeZero n] in
/-- `isSporadicBalanced` is preserved under `applyPerm`: if `applyPerm σ w`
    is sporadic balanced, then so is `w` (compose σ with the witness). -/
private lemma isSporadicBalanced_of_applyPerm (σ : Equiv.Perm StepSize)
    (w : TernaryNecklace n) (h : isSporadicBalanced (Necklace.applyPerm σ w)) :
    isSporadicBalanced w := by
  obtain ⟨hn, τ, r, h0, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨hn, τ * σ, r, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Equiv.Perm.mul_apply, Necklace.applyPerm_apply] at * <;> assumption

/-- Given all-distinct counts, there exists a permutation putting them in
    strictly decreasing order: count L > count m > count s. -/
private lemma exists_perm_ordered_counts (w : TernaryNecklace n)
    (hLm : Necklace.count w .L ≠ Necklace.count w .m)
    (hms : Necklace.count w .m ≠ Necklace.count w .s)
    (hLs : Necklace.count w .L ≠ Necklace.count w .s) :
    ∃ σ : Equiv.Perm StepSize,
      Necklace.count (Necklace.applyPerm σ w) .L >
        Necklace.count (Necklace.applyPerm σ w) .m ∧
      Necklace.count (Necklace.applyPerm σ w) .m >
        Necklace.count (Necklace.applyPerm σ w) .s := by
  -- Enumerate the 6 strict orderings of 3 distinct values
  set a := Necklace.count w .L
  set b := Necklace.count w .m
  set c := Necklace.count w .s
  -- Helper: for any σ, reduce to count w (σ⁻¹ ·)
  have go : ∀ σ : Equiv.Perm StepSize,
      Necklace.count w (σ.symm .L) > Necklace.count w (σ.symm .m) →
      Necklace.count w (σ.symm .m) > Necklace.count w (σ.symm .s) →
      ∃ σ', Necklace.count (Necklace.applyPerm σ' w) .L >
              Necklace.count (Necklace.applyPerm σ' w) .m ∧
            Necklace.count (Necklace.applyPerm σ' w) .m >
              Necklace.count (Necklace.applyPerm σ' w) .s :=
    fun σ h1 h2 => ⟨σ, by simp only [count_applyPerm_eq]; exact ⟨h1, h2⟩⟩
  -- Case split on orderings of a, b, c. Use `rw` (not `simp`) to avoid
  -- swap_symm normalization removing `.symm` before our lemmas match.
  rcases Nat.lt_or_gt_of_ne hLm with hab | hab <;>
    rcases Nat.lt_or_gt_of_ne hms with hbc | hbc
  · -- a < b < c: swap L s (σ⁻¹: L↦s, m↦m, s↦L)
    exact go (Equiv.swap .L .s)
      (by rw [show (Equiv.swap StepSize.L StepSize.s).symm .L = .s from by decide,
              show (Equiv.swap StepSize.L StepSize.s).symm .m = .m from by decide]; omega)
      (by rw [show (Equiv.swap StepSize.L StepSize.s).symm .m = .m from by decide,
              show (Equiv.swap StepSize.L StepSize.s).symm .s = .L from by decide]; omega)
  · -- a < b, b > c
    rcases Nat.lt_or_gt_of_ne hLs with hac | hac
    · -- a < c < b: cycle (σ⁻¹: L↦m, m↦s, s↦L)
      exact go (Equiv.swap .L .m * Equiv.swap .L .s)
        (by rw [show ((Equiv.swap .L .m * Equiv.swap .L .s) : Equiv.Perm StepSize).symm .L = .m
                  from by decide,
                show ((Equiv.swap .L .m * Equiv.swap .L .s) : Equiv.Perm StepSize).symm .m = .s
                  from by decide]; omega)
        (by rw [show ((Equiv.swap .L .m * Equiv.swap .L .s) : Equiv.Perm StepSize).symm .m = .s
                  from by decide,
                show ((Equiv.swap .L .m * Equiv.swap .L .s) : Equiv.Perm StepSize).symm .s = .L
                  from by decide]; omega)
    · -- c < a < b: swap L m (σ⁻¹: L↦m, m↦L, s↦s)
      exact go (Equiv.swap .L .m)
        (by rw [show (Equiv.swap StepSize.L StepSize.m).symm .L = .m from by decide,
                show (Equiv.swap StepSize.L StepSize.m).symm .m = .L from by decide]; omega)
        (by rw [show (Equiv.swap StepSize.L StepSize.m).symm .m = .L from by decide,
                show (Equiv.swap StepSize.L StepSize.m).symm .s = .s from by decide]; omega)
  · -- a > b, b < c
    rcases Nat.lt_or_gt_of_ne hLs with hac | hac
    · -- b < a < c: cycle (σ⁻¹: L↦s, m↦L, s↦m)
      exact go (Equiv.swap .L .s * Equiv.swap .L .m)
        (by rw [show ((Equiv.swap .L .s * Equiv.swap .L .m) : Equiv.Perm StepSize).symm .L = .s
                  from by decide,
                show ((Equiv.swap .L .s * Equiv.swap .L .m) : Equiv.Perm StepSize).symm .m = .L
                  from by decide]; omega)
        (by rw [show ((Equiv.swap .L .s * Equiv.swap .L .m) : Equiv.Perm StepSize).symm .m = .L
                  from by decide,
                show ((Equiv.swap .L .s * Equiv.swap .L .m) : Equiv.Perm StepSize).symm .s = .m
                  from by decide]; omega)
    · -- b < c < a: swap m s (σ⁻¹: L↦L, m↦s, s↦m)
      exact go (Equiv.swap .m .s)
        (by rw [show (Equiv.swap StepSize.m StepSize.s).symm .L = .L from by decide,
                show (Equiv.swap StepSize.m StepSize.s).symm .m = .s from by decide]; omega)
        (by rw [show (Equiv.swap StepSize.m StepSize.s).symm .m = .s from by decide,
                show (Equiv.swap StepSize.m StepSize.s).symm .s = .m from by decide]; omega)
  · -- a > b > c: identity
    exact go 1 (by simp; omega) (by simp; omega)

/-- The 2-step subword starting at position i is [w(i), w(i+1)]. -/
lemma slice_two (w : TernaryNecklace n) (i : ℕ) :
    Necklace.slice w i (i + 2) = [w (i : ZMod n), w ((i + 1 : ℕ) : ZMod n)] := by
  rw [show i + 2 = i + 1 + 1 from by omega]
  rw [slice_shift_decompose w i 2 (by omega)]
  congr 1
  rw [slice_shift_decompose w (i + 1) 1 (by omega)]
  suffices Necklace.slice w (i + 1 + 1) (i + 1 + 1) = [] by
    rw [this]
  unfold Necklace.slice; simp

/-- Balance gives: for any two positions i, j and letter a, the a-count
    of the 2-step subwords at i and j differ by at most 1. -/
private lemma balanced_two_step_count_diff (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (hn : n > 2) (i j : Fin n) (a : StepSize) :
    Int.natAbs (((Necklace.slice w i.val (i.val + 2)).count a : ℤ) -
                ((Necklace.slice w j.val (j.val + 2)).count a : ℤ)) ≤ 1 :=
  hbal 2 (by omega) hn _ _ a
    (List.mem_ofFn.mpr ⟨i, rfl⟩) (List.mem_ofFn.mpr ⟨j, rfl⟩)

/-- ZMod-friendly version: balance for 2-step subwords at ZMod n positions. -/
private lemma balanced_two_step_diff_zmod (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (hn : n > 2) (i j : ZMod n) (a : StepSize) :
    Int.natAbs (([w i, w (i + 1)].count a : ℤ) -
                ([w j, w (j + 1)].count a : ℤ)) ≤ 1 := by
  have h := balanced_two_step_count_diff w hbal hn
    ⟨i.val, ZMod.val_lt i⟩ ⟨j.val, ZMod.val_lt j⟩ a
  rw [slice_two, slice_two] at h
  simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val] at h
  exact h

/-- No two consecutive s's in a balanced ternary necklace with a > b > c.
    Proof: If ss exists, all 2-step subwords have s-count ≥ 1.
    Every L at position j must have w(j+1) = s (since w(j) = L ≠ s).
    Injecting L-positions into s-positions via (· + 1) gives a ≤ c,
    contradicting a > b > c. -/
private lemma balanced_no_ss (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (htern : isTernary w)
    (hLm : Necklace.count w .L > Necklace.count w .m)
    (hms : Necklace.count w .m > Necklace.count w .s) :
    ∀ i : ZMod n, ¬ (w i = .s ∧ w (i + 1) = .s) := by
  intro i₀ ⟨hi₀, hi₀1⟩
  have hn : n > 2 := by
    have := count_pos_of_isTernary w htern .L
    have := count_pos_of_isTernary w htern .m
    have := count_pos_of_isTernary w htern .s
    have := count_total w; omega
  -- For any L-position j, w(j+1) = s
  have hL_succ_s : ∀ j : ZMod n, w j = .L → w (j + 1) = .s := by
    intro j hj
    have hdiff := balanced_two_step_diff_zmod w hbal hn i₀ j .s
    rw [hi₀, hi₀1, hj] at hdiff
    -- hdiff : |[.s, .s].count .s - [.L, w(j+1)].count .s| ≤ 1
    -- [.s, .s].count .s = 2, [.L, w(j+1)].count .s = if w(j+1)=s then 1 else 0
    simp only [List.count_cons, List.count_nil, beq_iff_eq] at hdiff
    -- If w(j+1) ≠ s: |2 - 0| = 2 > 1, contradiction
    cases hj1 : w (j + 1) with
    | s => rfl
    | L => rw [hj1] at hdiff; simp at hdiff
    | m => rw [hj1] at hdiff; simp at hdiff
  -- Injection: (· + 1) maps L-positions into s-positions
  have hle : Necklace.count w .L ≤ Necklace.count w .s := by
    unfold Necklace.count
    apply Finset.card_le_card_of_injOn (· + 1)
    · intro x hx
      have hxL := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hL_succ_s x hxL⟩)
    · intro x hx y hy hxy
      exact add_right_cancel hxy
  omega

/-- If LL exists in a balanced ternary necklace, every s has L on both sides. -/
private lemma balanced_ss_flanked_by_L_of_LL (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (hn : n > 2)
    (j₀ : ZMod n) (hLL : w j₀ = .L ∧ w (j₀ + 1) = .L)
    (p : ZMod n) (hp : w p = .s) :
    w (p - 1) = .L ∧ w (p + 1) = .L := by
  constructor
  · -- 2-step subword at j₀ has L-count 2
    -- 2-step subword at p-1 is [w(p-1), s], L-count ≥ 1 → w(p-1) = L
    have hdiff := balanced_two_step_diff_zmod w hbal hn j₀ (p - 1) .L
    rw [hLL.1, hLL.2] at hdiff
    rw [show p - 1 + 1 = p from sub_add_cancel p 1, hp] at hdiff
    simp only [List.count_cons, List.count_nil, beq_iff_eq] at hdiff
    cases hv : w (p - 1) with
    | L => rfl
    | m => rw [hv] at hdiff; simp at hdiff
    | s => rw [hv] at hdiff; simp at hdiff
  · -- 2-step subword at p is [s, w(p+1)], L-count ≥ 1 → w(p+1) = L
    have hdiff := balanced_two_step_diff_zmod w hbal hn j₀ p .L
    rw [hLL.1, hLL.2, hp] at hdiff
    simp only [List.count_cons, List.count_nil, beq_iff_eq] at hdiff
    cases hv : w (p + 1) with
    | L => rfl
    | m => rw [hv] at hdiff; simp at hdiff
    | s => rw [hv] at hdiff; simp at hdiff

/-- Step (i): In a balanced ternary necklace with count L > count m > count s,
    the subword LsL appears.
    Proof: Assume no LsL. No LL either implies every L is followed by m or sm,
    giving a ≤ b m-positions, contradicting a > b. So LL exists.
    Then every s is flanked by L's (2-step balance), giving LsL. -/
private lemma balanced_has_LsL (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (htern : isTernary w)
    (hLm : Necklace.count w .L > Necklace.count w .m)
    (hms : Necklace.count w .m > Necklace.count w .s) :
    ∃ i : ZMod n, w i = .L ∧ w (i + 1) = .s ∧ w (i + 2) = .L := by
  have hno_ss := balanced_no_ss w hbal htern hLm hms
  have hn : n > 2 := by
    have := count_pos_of_isTernary w htern .L
    have := count_pos_of_isTernary w htern .m
    have := count_pos_of_isTernary w htern .s
    have := count_total w; omega
  -- Get an s-position (s exists since c ≥ 1)
  have hs_pos := count_pos_of_isTernary w htern .s
  rw [Necklace.count, Finset.card_pos] at hs_pos
  obtain ⟨p, hp⟩ := hs_pos
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  -- Either LL exists or not
  by_cases hLL : ∃ j : ZMod n, w j = .L ∧ w (j + 1) = .L
  · -- LL exists: every s is flanked by L → LsL
    obtain ⟨j₀, hj₀⟩ := hLL
    have hflank := balanced_ss_flanked_by_L_of_LL w hbal hn j₀ hj₀ p hp
    exact ⟨p - 1, hflank.1, by rwa [sub_add_cancel],
      by rw [show p - 1 + 2 = p + 1 from by ring]; exact hflank.2⟩
  · -- No LL: show a ≤ b, contradicting a > b
    push_neg at hLL
    -- For each L at position j: w(j+1) ≠ L (no LL), so w(j+1) = m or s
    -- If w(j+1) = s: w(j+2) ≠ s (no ss) so w(j+2) = L or m
    --   If w(j+2) = L: we found LsL, done!
    --   If w(j+2) = m: type Lsm, map j ↦ j+2
    -- If w(j+1) = m: type Lm, map j ↦ j+1
    -- If all L-positions are type Lm or Lsm (no LsL found), injection gives a ≤ b
    -- We use classical logic: either ∃ LsL (done) or ∀ j, w j = L → w(j+1) = s → w(j+2) ≠ L
    by_cases hLsL : ∃ j : ZMod n, w j = .L ∧ w (j + 1) = .s ∧ w (j + 2) = .L
    · exact hLsL
    · push_neg at hLsL
      -- Now: no LL, no LsL. Every L maps to an m-position.
      have hL_to_m : ∀ j : ZMod n, w j = .L →
          (w (j + 1) = .m) ∨ (w (j + 1) = .s ∧ w (j + 2) = .m) := by
        intro j hj
        have hj1_neL : w (j + 1) ≠ .L := by
          intro hc; exact hLL j hj hc
        cases hj1 : w (j + 1) with
        | L => exact absurd hj1 hj1_neL
        | m => exact Or.inl rfl
        | s =>
          right; refine ⟨rfl, ?_⟩
          have hj2_neS : w (j + 2) ≠ .s := by
            intro hc
            exact hno_ss (j + 1) ⟨hj1, by rwa [show j + 1 + 1 = j + 2 from by ring]⟩
          have hj2_neL : w (j + 2) ≠ .L := by
            intro hc; exact hLsL j hj hj1 hc
          cases hw : w (j + 2) with
          | L => exact absurd hw hj2_neL
          | s => exact absurd hw hj2_neS
          | m => rfl
      -- Define f : L-positions → ZMod n mapping j to its associated m-position
      -- Type Lm: j ↦ j+1; Type Lsm: j ↦ j+2
      -- f is injective: same-type is clear; cross-type: if j₁+1 = j₂+2 then
      -- w(j₂+1) = s (type Lsm) and j₁ = j₂+1 so w(j₁) = w(j₂+1) = s, but w(j₁) = L, contradiction.
      -- Similarly j₁+2 = j₂+1 means j₁+1 = j₂ so w(j₂) = w(j₁+1) and j₁ is Lsm so w(j₁+1) = s,
      -- but w(j₂) = L, contradiction.
      let f : ZMod n → ZMod n := fun j =>
        if w (j + 1) = .m then j + 1 else j + 2
      have hf_m : ∀ j : ZMod n, w j = .L → w (f j) = .m := by
        intro j hj
        simp only [f]
        split
        · assumption
        · have := hL_to_m j hj
          cases this with
          | inl h => simp [h] at *
          | inr h => exact h.2
      have hf_inj : ∀ j₁ j₂ : ZMod n, w j₁ = .L → w j₂ = .L →
          f j₁ = f j₂ → j₁ = j₂ := by
        intro j₁ j₂ hj₁ hj₂ hfeq
        simp only [f] at hfeq
        split at hfeq <;> split at hfeq
        · -- Both Lm: j₁+1 = j₂+1 → j₁ = j₂
          exact add_right_cancel hfeq
        · -- j₁ Lm, j₂ Lsm: j₁+1 = j₂+2
          rename_i hm₁ hm₂
          have hj₂s : w (j₂ + 1) = .s := by
            cases hL_to_m j₂ hj₂ with
            | inl h => exact absurd h hm₂
            | inr h => exact h.1
          -- j₁ + 1 = j₂ + 2 = (j₂ + 1) + 1, so j₁ = j₂ + 1
          have heq : j₁ = j₂ + 1 := add_right_cancel (show j₁ + 1 = (j₂ + 1) + 1 by rw [hfeq]; ring)
          -- w(j₁) = w(j₂+1) = s, but w(j₁) = L
          rw [heq] at hj₁; simp_all
        · -- j₁ Lsm, j₂ Lm: j₁+2 = j₂+1
          rename_i hm₁ hm₂
          have hj₁s : w (j₁ + 1) = .s := by
            cases hL_to_m j₁ hj₁ with
            | inl h => exact absurd h hm₁
            | inr h => exact h.1
          -- j₁ + 2 = j₂ + 1, so j₁ + 1 = j₂ (add -1 to both sides)
          -- Then w(j₂) = w(j₁+1) = s, contradicts w(j₂) = L
          have heq : j₂ = j₁ + 1 := add_right_cancel (show j₂ + 1 = (j₁ + 1) + 1 by rw [← hfeq]; ring)
          rw [heq] at hj₂; simp_all
        · -- Both Lsm: j₁+2 = j₂+2 → j₁ = j₂
          exact add_right_cancel (show j₁ + 2 = j₂ + 2 from hfeq)
      exfalso
      have hle : Necklace.count w .L ≤ Necklace.count w .m := by
        unfold Necklace.count
        apply Finset.card_le_card_of_injOn f
        · intro x hx
          have hxL := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
          exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf_m x hxL⟩)
        · intro x hx y hy hxy
          have hxL := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
          have hyL := (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
          exact hf_inj x y hxL hyL hxy
      omega

/-- The 3-step subword starting at position i is [w(i), w(i+1), w(i+2)]. -/
lemma slice_three (w : TernaryNecklace n) (i : ℕ) :
    Necklace.slice w i (i + 3) = [w (i : ZMod n), w ((i + 1 : ℕ) : ZMod n),
      w ((i + 2 : ℕ) : ZMod n)] := by
  rw [show i + 3 = i + 2 + 1 from by omega]
  rw [slice_shift_decompose w i 3 (by omega)]
  congr 1
  rw [show i + 2 + 1 = (i + 1) + 1 + 1 from by omega]
  rw [slice_shift_decompose w (i + 1) 2 (by omega)]
  congr 1
  rw [slice_shift_decompose w (i + 2) 1 (by omega)]
  suffices Necklace.slice w (i + 2 + 1) (i + 2 + 1) = [] by rw [this]
  unfold Necklace.slice; simp

/-- Balance for 3-step subwords at ZMod n positions. -/
private lemma balanced_three_step_diff_zmod (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (hn : n > 3) (i j : ZMod n) (a : StepSize) :
    Int.natAbs (([w i, w (i + 1), w (i + 2)].count a : ℤ) -
                ([w j, w (j + 1), w (j + 2)].count a : ℤ)) ≤ 1 := by
  have h := hbal 3 (by omega) hn _ _ a
    (List.mem_ofFn.mpr ⟨⟨i.val, ZMod.val_lt i⟩, rfl⟩)
    (List.mem_ofFn.mpr ⟨⟨j.val, ZMod.val_lt j⟩, rfl⟩)
  rw [slice_three, slice_three] at h
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, ZMod.natCast_zmod_val] at h
  convert h using 2

/-- The 4-step subword starting at position i is [w(i), w(i+1), w(i+2), w(i+3)]. -/
lemma slice_four (w : TernaryNecklace n) (i : ℕ) :
    Necklace.slice w i (i + 4) = [w (i : ZMod n), w ((i + 1 : ℕ) : ZMod n),
      w ((i + 2 : ℕ) : ZMod n), w ((i + 3 : ℕ) : ZMod n)] := by
  rw [show i + 4 = i + 3 + 1 from by omega]
  rw [slice_shift_decompose w i 4 (by omega)]
  congr 1
  rw [show i + 3 + 1 = (i + 1) + 2 + 1 from by omega]
  rw [slice_shift_decompose w (i + 1) 3 (by omega)]
  congr 1
  rw [show (i + 1) + 2 + 1 = (i + 2) + 1 + 1 from by omega]
  rw [slice_shift_decompose w (i + 2) 2 (by omega)]
  congr 1
  rw [slice_shift_decompose w (i + 3) 1 (by omega)]
  suffices Necklace.slice w (i + 3 + 1) (i + 3 + 1) = [] by rw [this]
  unfold Necklace.slice; simp

/-- Balance for 4-step subwords at ZMod n positions. -/
private lemma balanced_four_step_diff_zmod (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (hn : n > 4) (i j : ZMod n) (a : StepSize) :
    Int.natAbs (([w i, w (i + 1), w (i + 2), w (i + 3)].count a : ℤ) -
                ([w j, w (j + 1), w (j + 2), w (j + 3)].count a : ℤ)) ≤ 1 := by
  have h := hbal 4 (by omega) hn _ _ a
    (List.mem_ofFn.mpr ⟨⟨i.val, ZMod.val_lt i⟩, rfl⟩)
    (List.mem_ofFn.mpr ⟨⟨j.val, ZMod.val_lt j⟩, rfl⟩)
  rw [slice_four, slice_four] at h
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, ZMod.natCast_zmod_val] at h
  convert h using 2

/-- The 5-step subword starting at position i is [w(i), ..., w(i+4)]. -/
private lemma slice_five (w : TernaryNecklace n) (i : ℕ) :
    Necklace.slice w i (i + 5) = [w (i : ZMod n), w ((i + 1 : ℕ) : ZMod n),
      w ((i + 2 : ℕ) : ZMod n), w ((i + 3 : ℕ) : ZMod n),
      w ((i + 4 : ℕ) : ZMod n)] := by
  rw [show i + 5 = i + 4 + 1 from by omega]
  rw [slice_shift_decompose w i 5 (by omega)]; congr 1
  rw [show i + 4 + 1 = (i + 1) + 3 + 1 from by omega]
  rw [slice_shift_decompose w (i + 1) 4 (by omega)]; congr 1
  rw [show (i + 1) + 3 + 1 = (i + 2) + 2 + 1 from by omega]
  rw [slice_shift_decompose w (i + 2) 3 (by omega)]; congr 1
  rw [show (i + 2) + 2 + 1 = (i + 3) + 1 + 1 from by omega]
  rw [slice_shift_decompose w (i + 3) 2 (by omega)]; congr 1
  rw [slice_shift_decompose w (i + 4) 1 (by omega)]
  suffices Necklace.slice w (i + 4 + 1) (i + 4 + 1) = [] by rw [this]
  unfold Necklace.slice; simp

/-- Balance for 5-step subwords at ZMod n positions. -/
private lemma balanced_five_step_diff_zmod (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (hn : n > 5) (i j : ZMod n) (a : StepSize) :
    Int.natAbs (([w i, w (i + 1), w (i + 2), w (i + 3), w (i + 4)].count a : ℤ) -
                ([w j, w (j + 1), w (j + 2), w (j + 3), w (j + 4)].count a : ℤ)) ≤ 1 := by
  have h := hbal 5 (by omega) hn _ _ a
    (List.mem_ofFn.mpr ⟨⟨i.val, ZMod.val_lt i⟩, rfl⟩)
    (List.mem_ofFn.mpr ⟨⟨j.val, ZMod.val_lt j⟩, rfl⟩)
  rw [slice_five, slice_five] at h
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, ZMod.natCast_zmod_val] at h
  convert h using 2

/-- The 6-step subword starting at position i is [w(i), ..., w(i+5)]. -/
private lemma slice_six (w : TernaryNecklace n) (i : ℕ) :
    Necklace.slice w i (i + 6) = [w (i : ZMod n), w ((i + 1 : ℕ) : ZMod n),
      w ((i + 2 : ℕ) : ZMod n), w ((i + 3 : ℕ) : ZMod n),
      w ((i + 4 : ℕ) : ZMod n), w ((i + 5 : ℕ) : ZMod n)] := by
  rw [show i + 6 = i + 5 + 1 from by omega]
  rw [slice_shift_decompose w i 6 (by omega)]; congr 1
  rw [show i + 5 + 1 = (i + 1) + 4 + 1 from by omega]
  rw [slice_shift_decompose w (i + 1) 5 (by omega)]; congr 1
  rw [show (i + 1) + 4 + 1 = (i + 2) + 3 + 1 from by omega]
  rw [slice_shift_decompose w (i + 2) 4 (by omega)]; congr 1
  rw [show (i + 2) + 3 + 1 = (i + 3) + 2 + 1 from by omega]
  rw [slice_shift_decompose w (i + 3) 3 (by omega)]; congr 1
  rw [show (i + 3) + 2 + 1 = (i + 4) + 1 + 1 from by omega]
  rw [slice_shift_decompose w (i + 4) 2 (by omega)]; congr 1
  rw [slice_shift_decompose w (i + 5) 1 (by omega)]
  suffices Necklace.slice w (i + 5 + 1) (i + 5 + 1) = [] by rw [this]
  unfold Necklace.slice; simp

/-- Balance for 6-step subwords at ZMod n positions. -/
private lemma balanced_six_step_diff_zmod (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (hn : n > 6) (i j : ZMod n) (a : StepSize) :
    Int.natAbs (([w i, w (i + 1), w (i + 2), w (i + 3), w (i + 4), w (i + 5)].count a : ℤ) -
                ([w j, w (j + 1), w (j + 2), w (j + 3), w (j + 4), w (j + 5)].count a : ℤ))
                ≤ 1 := by
  have h := hbal 6 (by omega) hn _ _ a
    (List.mem_ofFn.mpr ⟨⟨i.val, ZMod.val_lt i⟩, rfl⟩)
    (List.mem_ofFn.mpr ⟨⟨j.val, ZMod.val_lt j⟩, rfl⟩)
  rw [slice_six, slice_six] at h
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, ZMod.natCast_zmod_val] at h
  convert h using 2

/-- No two consecutive m's in a balanced ternary necklace with a > b > c. -/
private lemma balanced_no_mm (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (htern : isTernary w)
    (hLm : Necklace.count w .L > Necklace.count w .m)
    (hms : Necklace.count w .m > Necklace.count w .s) :
    ∀ i : ZMod n, ¬ (w i = .m ∧ w (i + 1) = .m) := by
  obtain ⟨j, hjL, hjs, hjL2⟩ := balanced_has_LsL w hbal htern hLm hms
  have hn : n > 2 := by
    have := count_pos_of_isTernary w htern .L
    have := count_pos_of_isTernary w htern .m
    have := count_pos_of_isTernary w htern .s
    have := count_total w; omega
  intro i ⟨hi, hi1⟩
  -- [m,m] has m-count 2, [L,s] from LsL has m-count 0
  have hdiff := balanced_two_step_diff_zmod w hbal hn i j .m
  rw [hi, hi1, hjL, hjs] at hdiff
  simp at hdiff

/-- No mLm pattern in a balanced ternary necklace with a > b > c. -/
private lemma balanced_no_mLm (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (htern : isTernary w)
    (hLm : Necklace.count w .L > Necklace.count w .m)
    (hms : Necklace.count w .m > Necklace.count w .s) :
    ∀ i : ZMod n, ¬ (w i = .m ∧ w (i + 1) = .L ∧ w (i + 2) = .m) := by
  obtain ⟨j, hjL, hjs, hjL2⟩ := balanced_has_LsL w hbal htern hLm hms
  have hn : n > 3 := by
    have := count_pos_of_isTernary w htern .L
    have := count_pos_of_isTernary w htern .m
    have := count_pos_of_isTernary w htern .s
    have := count_total w
    -- a > b > c ≥ 1 → a ≥ 3, b ≥ 2, c ≥ 1 → n ≥ 6 > 3
    omega
  intro i ⟨hi, hi1, hi2⟩
  -- [m,L,m] has m-count 2, [L,s,L] has m-count 0
  have hdiff := balanced_three_step_diff_zmod w hbal hn i j .m
  rw [hi, hi1, hi2, hjL, hjs, hjL2] at hdiff
  simp at hdiff

/-- kStepVector values are non-negative (since they count occurrences). -/
private lemma kStepVector_nonneg (w : TernaryNecklace n) (i k : ℕ) (a : StepSize) :
    0 ≤ Necklace.kStepVector w i k a := by
  simp only [Necklace.kStepVector, ZVector.ofList]; exact Nat.cast_nonneg _

/-- Relates kStepVector to List.count via Nat.cast. -/
private lemma kStepVector_eq_cast_count (w : TernaryNecklace n) (i k : ℕ) (a : StepSize) :
    Necklace.kStepVector w i k a = ↑((Necklace.slice w i (i + k)).count a) := by
  simp only [Necklace.kStepVector, ZVector.ofList, List.count_eq_countP,
    List.countP_eq_length_filter]

/-- Balance implies kStepVector differences are at most 1 for any two starting positions. -/
private lemma balanced_kStepVector_diff (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (k : ℕ) (hk : 0 < k) (hkn : k < n)
    (i j : ℕ) (a : StepSize) :
    Int.natAbs (Necklace.kStepVector w i k a - Necklace.kStepVector w j k a) ≤ 1 := by
  rw [← congr_fun (kStepVector_mod_n w i k) a, ← congr_fun (kStepVector_mod_n w j k) a]
  rw [kStepVector_eq_cast_count, kStepVector_eq_cast_count]
  exact hbal k hk hkn _ _ a
    (List.mem_ofFn.mpr ⟨⟨i % n, Nat.mod_lt i (NeZero.pos n)⟩, rfl⟩)
    (List.mem_ofFn.mpr ⟨⟨j % n, Nat.mod_lt j (NeZero.pos n)⟩, rfl⟩)

/-- When LL exists and we have all the structural properties, find mLLm.
    Argument: By pigeonhole (b > c), some gap between consecutive m's has no s,
    giving mL^k m. k ≥ 2 by no_mm and no_mLm. k ≥ 3 leads to contradiction:
    L^k → L^{k-1}sL^{k-1} by k-step balance → (k+2)-step m-count 0 vs 2.
    So k = 2. -/
private lemma balanced_mLLm_of_LL (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (htern : isTernary w)
    (_hLm : Necklace.count w .L > Necklace.count w .m)
    (hms : Necklace.count w .m > Necklace.count w .s)
    (_hno_mm : ∀ i : ZMod n, ¬ (w i = .m ∧ w (i + 1) = .m))
    (hno_mLm : ∀ i : ZMod n, ¬ (w i = .m ∧ w (i + 1) = .L ∧ w (i + 2) = .m))
    (_hno_ss : ∀ i : ZMod n, ¬ (w i = .s ∧ w (i + 1) = .s))
    (hLsL : ∃ i : ZMod n, w i = .L ∧ w (i + 1) = .s ∧ w (i + 2) = .L)
    (hn : n > 2)
    (_hsflanked : ∀ (p : ZMod n), w p = .s → w (p - 1) = .L ∧ w (p + 1) = .L)
    (hm_fwd : ∀ i : ZMod n, w i = .m → w (i + 1) = .L)
    (_hm_bwd : ∀ i : ZMod n, w i = .m → w (i - 1) = .L) :
    ∃ i : ZMod n, w i = .m ∧ w (i + 1) = .L ∧ w (i + 2) = .L ∧ w (i + 3) = .m := by
  -- Part B: k ≥ 3 with mL^k m at position i₀ gives contradiction.
  have no_large : ∀ (i₀ : ZMod n) (k : ℕ), k ≥ 3 →
      w i₀ = .m →
      (∀ j : ℕ, 1 ≤ j → j ≤ k → w (i₀ + (↑j : ZMod n)) = .L) →
      w (i₀ + (↑(k + 1) : ZMod n)) = .m → False := by
    intro i₀ k hk3 hi₀ hLrun hend
    -- Step 1: Show n > k + 2 (needed for (k+2)-step balance)
    have hn_gt_k : n > k := by
      by_contra hle; push_neg at hle
      have := hLrun n (by omega) hle
      rw [ZMod.natCast_self, add_zero] at this
      rw [hi₀] at this; exact absurd this (by decide)
    have hn_gt_k2 : n > k + 2 := by
      by_contra hle; push_neg at hle
      have hall : ∀ q : ZMod n, w q = .m ∨ w q = .L := by
        intro q
        have hq_eq : q = i₀ + ↑((q - i₀).val) := by rw [ZMod.natCast_zmod_val (q - i₀)]; ring
        rw [hq_eq]
        rcases Nat.eq_zero_or_pos (q - i₀).val with h0 | h0
        · left; rw [h0, Nat.cast_zero, add_zero]; exact hi₀
        · rcases Nat.lt_or_ge (q - i₀).val (k + 1) with hlt | hge
          · right; exact hLrun _ h0 (by omega)
          · left
            have : (q - i₀).val = k + 1 := by have := ZMod.val_lt (q - i₀); omega
            rw [this]; exact hend
      obtain ⟨p', _, hps', _⟩ := hLsL
      rcases hall (p' + 1) with h | h <;> simp [h] at hps'
    -- Step 2: Extract s position from hLsL
    obtain ⟨p, hpL, hps, hpL2⟩ := hLsL
    -- Helper: if all k' positions from j have value a, then kStepVector for b ≠ a is 0
    have kStepVector_run_zero : ∀ (j k' : ℕ) (a b : StepSize), a ≠ b →
        (∀ t : ℕ, t < k' → w ((j + t : ℕ) : ZMod n) = a) →
        Necklace.kStepVector w j k' b = 0 := by
      intro j k' a b hab hall
      rw [← kStepVector_as_singleton_sum]
      apply Finset.sum_eq_zero; intro i hi
      rw [kStepVector_singleton, hall i (Finset.mem_range.mp hi)]
      exact if_neg hab
    -- Step 3: L-run at i₀+1 has .m count = 0 and .L count = k
    have hLrun_nat : ∀ t : ℕ, t < k → w ((i₀.val + 1 + t : ℕ) : ZMod n) = .L := by
      intro t ht
      have := hLrun (t + 1) (by omega) (by omega)
      rwa [show ((i₀.val + 1 + t : ℕ) : ZMod n) = i₀ + (↑(t + 1) : ZMod n) from by
        push_cast; rw [ZMod.natCast_zmod_val i₀]; ring]
    have hLrun_m0 : Necklace.kStepVector w (i₀.val + 1) k .m = 0 :=
      kStepVector_run_zero _ _ .L .m (by decide) hLrun_nat
    have hLrun_Lk : Necklace.kStepVector w (i₀.val + 1) k .L = ↑k := by
      have hLrun_s0 : Necklace.kStepVector w (i₀.val + 1) k .s = 0 :=
        kStepVector_run_zero _ _ .L .s (by decide) hLrun_nat
      linarith [kStepVector_total_count_ternary w (i₀.val + 1) k]
    -- Step 4: Every k-step window has m + s ≤ 1 (from L-count ≥ k - 1)
    have hms_le1 : ∀ j : ℕ,
        Necklace.kStepVector w j k .m + Necklace.kStepVector w j k .s ≤ 1 := by
      intro j
      have hbal_L := balanced_kStepVector_diff w hbal k (by omega) hn_gt_k (i₀.val + 1) j .L
      rw [hLrun_Lk] at hbal_L
      have : Necklace.kStepVector w j k .L ≥ ↑k - 1 := by
        have h1 : |((↑k : ℤ) - Necklace.kStepVector w j k .L)| ≤ 1 := by
          rw [← Int.natCast_natAbs]; exact_mod_cast hbal_L
        linarith [(abs_le.mp h1).2]
      linarith [kStepVector_total_count_ternary w j k]
    -- Step 5: k-step at p.val has m = 0 (contains s at p+1)
    have hm_at_p : Necklace.kStepVector w p.val k .m = 0 := by
      have hs : Necklace.kStepVector w p.val k .s ≥ 1 := by
        have h1 := kStepVector_add w p.val 1 (k - 1) .s
        rw [show 1 + (k - 1) = k from by omega] at h1
        have h2 := kStepVector_add w (p.val + 1) 1 (k - 2) .s
        rw [show 1 + (k - 2) = k - 1 from by omega] at h2
        rw [h1, h2, kStepVector_singleton, kStepVector_singleton,
            show ((p.val : ℕ) : ZMod n) = p from ZMod.natCast_zmod_val p, hpL,
            show ((p.val + 1 : ℕ) : ZMod n) = p + 1 from by
              push_cast; rw [ZMod.natCast_zmod_val p],
            hps]; simp
        exact kStepVector_nonneg w _ _ _
      linarith [hms_le1 p.val, kStepVector_nonneg w p.val k .m]
    -- Step 6: k-step at (p+1).val has m = 0 (s at p+1 is first element)
    have hm_at_pp1 : Necklace.kStepVector w (p + 1).val k .m = 0 := by
      have hs : Necklace.kStepVector w (p + 1).val k .s ≥ 1 := by
        have h1 := kStepVector_add w (p + 1).val 1 (k - 1) .s
        rw [show 1 + (k - 1) = k from by omega] at h1
        rw [h1, kStepVector_singleton,
            show (((p + 1).val : ℕ) : ZMod n) = p + 1 from ZMod.natCast_zmod_val (p + 1), hps]; simp
        exact kStepVector_nonneg w _ _ _
      linarith [hms_le1 (p + 1).val, kStepVector_nonneg w (p + 1).val k .m]
    -- Useful ZMod cast: ↑(n - 1) = -1
    have hn1_cast : (↑(n - 1) : ZMod n) = -1 := by
      suffices h : (↑(n - 1) : ZMod n) + 1 = 0 from eq_neg_of_add_eq_zero_left h
      have : (↑(n - 1) + ↑(1 : ℕ) : ZMod n) = ↑n := by
        rw [← Nat.cast_add]; congr 1; omega
      rw [Nat.cast_one] at this; rw [this]; exact ZMod.natCast_self n
    -- Useful cast: ↑(p.val + n - 1) = p - 1
    have hcast_pm1 : ((p.val + n - 1 : ℕ) : ZMod n) = p - 1 := by
      rw [show p.val + n - 1 = p.val + (n - 1) from by omega, Nat.cast_add,
          ZMod.natCast_zmod_val p, hn1_cast]; ring
    -- Step 7: k-step at p.val + n - 1 (= p - 1 in ZMod) has m = 0
    have hm_at_pm1 : Necklace.kStepVector w (p.val + n - 1) k .m = 0 := by
      have hs : Necklace.kStepVector w (p.val + n - 1) k .s ≥ 1 := by
        -- The s at p+1 is in this window (at index 2, and k ≥ 3)
        have h1 := kStepVector_add w (p.val + n - 1) 2 (k - 2) .s
        rw [show 2 + (k - 2) = k from by omega] at h1
        have h2 := kStepVector_add w (p.val + n - 1 + 2) 1 (k - 3) .s
        rw [show 1 + (k - 3) = k - 2 from by omega] at h2
        rw [h1, h2, kStepVector_singleton,
            show ((p.val + n - 1 + 2 : ℕ) : ZMod n) = p + 1 from by
              rw [show p.val + n - 1 + 2 = p.val + (n + 1) from by omega]
              push_cast; rw [ZMod.natCast_zmod_val p, ZMod.natCast_self]; ring,
            hps]; simp
        linarith [kStepVector_nonneg w (p.val + n - 1) 2 .s,
                  kStepVector_nonneg w (p.val + n - 1 + 2 + 1) (k - 3) .s]
      linarith [hms_le1 (p.val + n - 1), kStepVector_nonneg w (p.val + n - 1) k .m]
    -- Step 8: w(p - 1) ≠ m
    have hp_m1_ne_m : w (p - 1) ≠ .m := by
      intro heq
      have h := kStepVector_add w (p.val + n - 1) 1 (k - 1) .m
      rw [show 1 + (k - 1) = k from by omega, hm_at_pm1, kStepVector_singleton,
          hcast_pm1, heq] at h; simp at h
      linarith [kStepVector_nonneg w (p.val + n - 1 + 1) (k - 1) .m]
    -- Step 9: w(p + ↑k) ≠ m
    have hp_pk_ne_m : w (p + ↑k) ≠ .m := by
      intro heq
      have h := kStepVector_add w (p + 1).val (k - 1) 1 .m
      rw [show k - 1 + 1 = k from by omega, hm_at_pp1, kStepVector_singleton] at h
      have hcast : (((p + 1).val + (k - 1) : ℕ) : ZMod n) = p + ↑k := by
        rw [Nat.cast_add, ZMod.natCast_zmod_val (p + 1)]
        have : (↑(k - 1) : ZMod n) = ↑k - 1 := by
          suffices h : (↑(k - 1) : ZMod n) + 1 = ↑k from eq_sub_of_add_eq h
          have h : (↑(k - 1 + 1) : ZMod n) = ↑k := by congr 1; omega
          rwa [Nat.cast_add, Nat.cast_one] at h
        rw [this]; ring
      rw [hcast, heq] at h; simp at h
      linarith [kStepVector_nonneg w (p + 1).val (k - 1) .m]
    -- Step 10: (k+2)-step at p.val + n - 1 has m-count = 0
    have hm_zero : Necklace.kStepVector w (p.val + n - 1) (k + 2) .m = 0 := by
      have h1 := kStepVector_add w (p.val + n - 1) 1 (k + 1) .m
      rw [show 1 + (k + 1) = k + 2 from by omega] at h1
      have h2 := kStepVector_add w (p.val + n) k 1 .m
      rw [h1, show p.val + n - 1 + 1 = p.val + n from by omega, h2]
      -- First singleton: w(p-1) ≠ m
      rw [kStepVector_singleton, hcast_pm1, if_neg hp_m1_ne_m]
      -- Middle k: kStepVector at p.val + n = kStepVector at p.val (= 0)
      have hmid : Necklace.kStepVector w (p.val + n) k .m =
          Necklace.kStepVector w p.val k .m := by
        rw [← congr_fun (kStepVector_mod_n w (p.val + n) k) .m]
        rw [show (p.val + n) % n = p.val % n from Nat.add_mod_right p.val n]
        exact congr_fun (kStepVector_mod_n w p.val k) .m
      rw [hmid, hm_at_p]
      -- Last singleton: w(p + ↑k) ≠ m
      rw [kStepVector_singleton,
          show ((p.val + n + k : ℕ) : ZMod n) = p + ↑k from by
            push_cast; rw [ZMod.natCast_zmod_val p, ZMod.natCast_self]; ring,
          if_neg hp_pk_ne_m]; simp
    -- Step 11: (k+2)-step at i₀.val has m-count = 2
    have hm_two : Necklace.kStepVector w i₀.val (k + 2) .m = 2 := by
      have h1 := kStepVector_add w i₀.val 1 (k + 1) .m
      rw [show 1 + (k + 1) = k + 2 from by omega] at h1
      have h2 := kStepVector_add w (i₀.val + 1) k 1 .m
      rw [h1, h2]
      rw [kStepVector_singleton, ZMod.natCast_zmod_val i₀, hi₀]; simp only [ite_true]
      rw [hLrun_m0, kStepVector_singleton,
          show ((i₀.val + 1 + k : ℕ) : ZMod n) = i₀ + (↑(k + 1) : ZMod n) from by
            push_cast; rw [ZMod.natCast_zmod_val i₀]; ring,
          hend]; simp
    -- Step 12: Balance violation — |2 - 0| = 2 > 1
    have hbalance := balanced_kStepVector_diff w hbal (k + 2) (by omega) hn_gt_k2
      i₀.val (p.val + n - 1) .m
    rw [hm_two, hm_zero] at hbalance; simp at hbalance
  -- Part A: by contradiction, assume no mLLm.
  by_contra h_no_mLLm
  push_neg at h_no_mLLm
  -- Get an s-position
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : ZMod n, w p₀ = .s := by
    have hs_pos := count_pos_of_isTernary w htern .s
    rw [Necklace.count, Finset.card_pos] at hs_pos
    obtain ⟨p, hp⟩ := hs_pos
    exact ⟨p, (Finset.mem_filter.mp hp).2⟩
  -- For each m at position i, ∃ d with w(i + 1 + ↑d) ≠ L
  have hex : ∀ i : ZMod n, w i = .m → ∃ d : ℕ, w (i + 1 + (↑d : ZMod n)) ≠ .L := by
    intro i _
    exact ⟨(p₀ - i - 1).val, by
      rw [ZMod.natCast_zmod_val, show i + 1 + (p₀ - i - 1) = p₀ from by ring, hp₀]
      decide⟩
  -- For each m at i, the first non-L after i+1 must be s (not m).
  -- If m: d=1 → mLm (hno_mLm); d=2 → mLLm (h_no_mLLm); d≥3 → no_large.
  have first_nonL_is_s : ∀ i : ZMod n, (hi : w i = .m) →
      let d := Nat.find (hex i hi)
      w (i + 1 + (↑d : ZMod n)) = .s := by
    intro i hi
    simp only
    set d := Nat.find (hex i hi) with hd_def
    have hd_spec : w (i + 1 + (↑d : ZMod n)) ≠ .L := Nat.find_spec (hex i hi)
    have hd_min : ∀ d' : ℕ, d' < d → w (i + 1 + (↑d' : ZMod n)) = .L :=
      fun d' hd' => of_not_not (Nat.find_min (hex i hi) hd')
    -- Positions i+1, ..., i+d are all L (shifting from hd_min)
    have hLrun : ∀ j : ℕ, 1 ≤ j → j ≤ d → w (i + (↑j : ZMod n)) = .L := by
      intro j hj1 hjd
      have h := hd_min (j - 1) (by omega)
      -- h : w (i + 1 + ↑(j-1)) = .L, need: w (i + ↑j) = .L
      -- i + 1 + ↑(j-1) = i + ↑j since j-1+1 = j (j ≥ 1)
      convert h using 2
      have : (j - 1 + 1 : ℕ) = j := by omega
      conv_lhs => rw [show j = j - 1 + 1 from this.symm]
      push_cast; ring
    -- Show the first non-L can't be m
    have hd_ne_m : w (i + 1 + (↑d : ZMod n)) ≠ .m := by
      intro hm
      -- d ≥ 1 (since w(i+1) = L, d = 0 would give w(i+1) ≠ L)
      have hd_ge1 : d ≥ 1 := by
        by_contra h; push_neg at h
        have : d = 0 := by omega
        simp only [this, Nat.cast_zero, add_zero] at hd_spec
        exact hd_spec (hm_fwd i hi)
      -- w(i + (d+1)) = m (rewriting hm)
      have hend : w (i + (↑(d + 1) : ZMod n)) = .m := by convert hm using 2; push_cast; ring
      -- Case split: d < 3 or d ≥ 3
      rcases Nat.lt_or_ge d 3 with hd3 | hd3
      · -- d ∈ {1, 2}
        interval_cases d
        · -- d = 1: mLm at i
          have h1 := hLrun 1 le_rfl le_rfl; norm_cast at h1
          exact hno_mLm i ⟨hi, h1, hend⟩
        · -- d = 2: mLLm at i
          have h1 := hLrun 1 le_rfl (by omega); norm_cast at h1
          have h2 := hLrun 2 (by omega) le_rfl; norm_cast at h2
          exact h_no_mLLm i hi h1 h2 hend
      · -- d ≥ 3: no_large
        exact no_large i d hd3 hi hLrun hend
    -- Not L and not m, so it's s
    cases hw : w (i + 1 + (↑d : ZMod n)) with
    | L => exact absurd hw hd_spec
    | m => exact absurd hw hd_ne_m
    | s => rfl
  -- Injection from m-positions to s-positions via the first non-L
  let f : ZMod n → ZMod n := fun i =>
    if h : w i = .m then i + 1 + (↑(Nat.find (hex i h)) : ZMod n) else 0
  have hle : Necklace.count w .m ≤ Necklace.count w .s := by
    unfold Necklace.count
    apply Finset.card_le_card_of_injOn f
    · -- f maps m-positions to s-positions
      intro x hx
      have hxM := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
      have hfx : f x = x + 1 + (↑(Nat.find (hex x hxM)) : ZMod n) := dif_pos hxM
      have hfs := first_nonL_is_s x hxM
      simp only at hfs
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hfx]; exact hfs⟩)
    · -- f is injective on m-positions
      intro x₁ hx₁ x₂ hx₂ hfeq
      have hx₁M := (Finset.mem_filter.mp (Finset.mem_coe.mp hx₁)).2
      have hx₂M := (Finset.mem_filter.mp (Finset.mem_coe.mp hx₂)).2
      have hf₁ : f x₁ = x₁ + 1 + (↑(Nat.find (hex x₁ hx₁M)) : ZMod n) := dif_pos hx₁M
      have hf₂ : f x₂ = x₂ + 1 + (↑(Nat.find (hex x₂ hx₂M)) : ZMod n) := dif_pos hx₂M
      set d₁ := Nat.find (hex x₁ hx₁M) with hd₁_def
      set d₂ := Nat.find (hex x₂ hx₂M) with hd₂_def
      have hfeq' : x₁ + 1 + (↑d₁ : ZMod n) = x₂ + 1 + (↑d₂ : ZMod n) := by
        rw [← hf₁, ← hf₂]; exact hfeq
      have hd₁_min : ∀ d' : ℕ, d' < d₁ → w (x₁ + 1 + (↑d' : ZMod n)) = .L :=
        fun d' hd' => of_not_not (Nat.find_min (hex x₁ hx₁M) hd')
      have hd₂_min : ∀ d' : ℕ, d' < d₂ → w (x₂ + 1 + (↑d' : ZMod n)) = .L :=
        fun d' hd' => of_not_not (Nat.find_min (hex x₂ hx₂M) hd')
      -- WLOG d₁ ≤ d₂
      rcases le_total d₁ d₂ with hle | hle
      · rcases eq_or_lt_of_le hle with heq | hlt
        · -- d₁ = d₂: cancel to get x₁ = x₂
          rw [heq] at hfeq'
          exact add_right_cancel (add_right_cancel hfeq')
        · -- d₁ < d₂: position x₂ + 1 + ↑(d₂-d₁-1) = x₁, in the L-run → w(x₁) = L, contradiction
          exfalso
          have hL := hd₂_min (d₂ - d₁ - 1) (by omega)
          -- Show x₂ + 1 + ↑(d₂-d₁-1) = x₁
          have hnat : (d₂ - d₁ - 1 + 1 + d₁ : ℕ) = d₂ := by omega
          have hcast : (↑(d₂ - d₁ - 1) : ZMod n) + 1 + ↑d₁ = ↑d₂ := by
            conv_rhs => rw [← hnat]
            push_cast; ring
          -- x₂ + 1 + ↑(d₂-d₁-1) + (1 + ↑d₁) = x₂ + 1 + ↑d₂ = x₁ + 1 + ↑d₁
          have heq_pos : x₂ + 1 + (↑(d₂ - d₁ - 1) : ZMod n) = x₁ := by
            suffices h : (x₂ + 1 + (↑(d₂ - d₁ - 1) : ZMod n)) + (1 + (↑d₁ : ZMod n)) =
                x₁ + (1 + (↑d₁ : ZMod n)) from add_right_cancel h
            rw [show (x₂ + 1 + (↑(d₂ - d₁ - 1) : ZMod n)) + (1 + (↑d₁ : ZMod n)) =
              x₂ + 1 + ((↑(d₂ - d₁ - 1) : ZMod n) + 1 + ↑d₁) from by ring]
            rw [hcast, ← hfeq']; ring
          rw [heq_pos] at hL; exact absurd hL (by rw [hx₁M]; decide)
      · rcases eq_or_lt_of_le hle with heq | hlt
        · -- d₂ = d₁: cancel to get x₁ = x₂
          rw [← heq] at hfeq'
          exact add_right_cancel (add_right_cancel hfeq')
        · -- d₂ < d₁: symmetric
          exfalso
          have hL := hd₁_min (d₁ - d₂ - 1) (by omega)
          have hnat : (d₁ - d₂ - 1 + 1 + d₂ : ℕ) = d₁ := by omega
          have hcast : (↑(d₁ - d₂ - 1) : ZMod n) + 1 + ↑d₂ = ↑d₁ := by
            conv_rhs => rw [← hnat]
            push_cast; ring
          have heq_pos : x₁ + 1 + (↑(d₁ - d₂ - 1) : ZMod n) = x₂ := by
            suffices h : (x₁ + 1 + (↑(d₁ - d₂ - 1) : ZMod n)) + (1 + (↑d₂ : ZMod n)) =
                x₂ + (1 + (↑d₂ : ZMod n)) from add_right_cancel h
            rw [show (x₁ + 1 + (↑(d₁ - d₂ - 1) : ZMod n)) + (1 + (↑d₂ : ZMod n)) =
              x₁ + 1 + ((↑(d₁ - d₂ - 1) : ZMod n) + 1 + ↑d₂) from by ring]
            rw [hcast, hfeq']; ring
          rw [heq_pos] at hL; exact absurd hL (by rw [hx₂M]; decide)
  omega

/-- Step (ii-a): The subword mLLm appears.
    Proof: No mm (2-step balance), no mLm (3-step balance).
    With these: if no LL, flow counting gives b ≤ c (contradiction), so LL exists.
    With LL: every s flanked by L. Between consecutive m's, the structure is
    L^{a1} s L^{a2} s ... s L^{ar}. Since c < b, some m-gap has no s (all L's),
    giving mL^k m. k ≥ 2 (no mm, no mLm). k ≤ 2 by (2k-1)-step balance. So k = 2. -/
private lemma balanced_has_mLLm (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (htern : isTernary w)
    (hLm : Necklace.count w .L > Necklace.count w .m)
    (hms : Necklace.count w .m > Necklace.count w .s) :
    ∃ i : ZMod n, w i = .m ∧ w (i + 1) = .L ∧ w (i + 2) = .L ∧ w (i + 3) = .m := by
  have hno_mm := balanced_no_mm w hbal htern hLm hms
  have hno_mLm := balanced_no_mLm w hbal htern hLm hms
  have hno_ss := balanced_no_ss w hbal htern hLm hms
  obtain ⟨j₀, hjL, hjs, hjL2⟩ := balanced_has_LsL w hbal htern hLm hms
  have hn : n > 2 := by
    have := count_pos_of_isTernary w htern .L
    have := count_pos_of_isTernary w htern .m
    have := count_pos_of_isTernary w htern .s
    have := count_total w; omega
  -- Step 1: LL exists.
  -- If no LL: no mm, no mLm, no LL. After mL, next must be s (not m by mLm, not L by LL).
  -- So every m maps (via ms or mLs) to an s. Injection gives b ≤ c, contradiction.
  by_cases hLL : ∃ j : ZMod n, w j = .L ∧ w (j + 1) = .L
  · -- Step 2: LL exists → mLLm
    obtain ⟨j₁, hj₁L, hj₁L'⟩ := hLL
    -- Every s is flanked by L
    have hsflanked := balanced_ss_flanked_by_L_of_LL w hbal hn j₁ ⟨hj₁L, hj₁L'⟩
    -- Every m is followed by L (s must be preceded by L, not m; and no mm)
    have hm_fwd : ∀ i : ZMod n, w i = .m → w (i + 1) = .L := by
      intro i him
      cases hi1 : w (i + 1) with
      | L => rfl
      | m => exact absurd ⟨him, hi1⟩ (hno_mm i)
      | s =>
        have := (hsflanked (i + 1) hi1).1
        rw [show i + 1 - 1 = i from by ring] at this; simp_all
    -- Every m is preceded by L
    have hm_bwd : ∀ i : ZMod n, w i = .m → w (i - 1) = .L := by
      intro i him
      cases hi1 : w (i - 1) with
      | L => rfl
      | m =>
        exact absurd ⟨hi1, by rw [show i - 1 + 1 = i from by ring]; exact him⟩ (hno_mm (i - 1))
      | s =>
        have := (hsflanked (i - 1) hi1).2
        rw [show i - 1 + 1 = i from by ring] at this; simp_all
    exact balanced_mLLm_of_LL w hbal htern hLm hms hno_mm hno_mLm hno_ss
      ⟨j₀, hjL, hjs, hjL2⟩ hn hsflanked hm_fwd hm_bwd
  · push_neg at hLL
    -- Flow argument: no LL, no mm, no mLm → b ≤ c
    -- After m, next is L or s (no mm). After mL, next is s (no mLm, no LL).
    -- So: for every m at position i, w(i+1) = s OR (w(i+1) = L ∧ w(i+2) = s).
    -- In both cases, each m maps to a unique s within distance 2.
    -- Define f(i) = if w(i+1) = s then i+1 else i+2
    -- f maps m-positions to s-positions, injectively → b ≤ c, contradiction.
    have hm_to_s : ∀ i : ZMod n, w i = .m →
        (w (i + 1) = .s) ∨ (w (i + 1) = .L ∧ w (i + 2) = .s) := by
      intro i hi
      have hi1_neM : w (i + 1) ≠ .m := by
        intro hc; exact hno_mm i ⟨hi, hc⟩
      cases hi1 : w (i + 1) with
      | m => exact absurd hi1 hi1_neM
      | s => exact Or.inl rfl
      | L =>
        right; refine ⟨rfl, ?_⟩
        -- w(i+2) ≠ m (no mLm) and w(i+2) ≠ L (no LL)
        have hi2_neM : w (i + 2) ≠ .m := by
          intro hc; exact hno_mLm i ⟨hi, hi1, hc⟩
        have hi2_neL : w (i + 2) ≠ .L := by
          intro hc; exact hLL (i + 1) hi1 (by rwa [show i + 1 + 1 = i + 2 from by ring])
        cases hw : w (i + 2) with
        | m => exact absurd hw hi2_neM
        | L => exact absurd hw hi2_neL
        | s => rfl
    -- Injection from m-positions to s-positions
    let g : ZMod n → ZMod n := fun i =>
      if w (i + 1) = .s then i + 1 else i + 2
    have hg_s : ∀ i : ZMod n, w i = .m → w (g i) = .s := by
      intro i hi; simp only [g]
      split
      · assumption
      · have := hm_to_s i hi
        cases this with
        | inl h => simp [h] at *
        | inr h => exact h.2
    have hg_inj : ∀ i₁ i₂ : ZMod n, w i₁ = .m → w i₂ = .m →
        g i₁ = g i₂ → i₁ = i₂ := by
      intro i₁ i₂ hi₁ hi₂ hgeq
      simp only [g] at hgeq
      split at hgeq <;> split at hgeq
      · exact add_right_cancel hgeq
      · rename_i hs₁ hs₂
        have hi₂L : w (i₂ + 1) = .L := by
          cases hm_to_s i₂ hi₂ with
          | inl h => exact absurd h hs₂
          | inr h => exact h.1
        have heq : i₁ = i₂ + 1 :=
          add_right_cancel (show i₁ + 1 = (i₂ + 1) + 1 by rw [hgeq]; ring)
        rw [heq] at hi₁; simp_all
      · rename_i hs₁ hs₂
        have hi₁L : w (i₁ + 1) = .L := by
          cases hm_to_s i₁ hi₁ with
          | inl h => exact absurd h hs₁
          | inr h => exact h.1
        have heq : i₂ = i₁ + 1 :=
          add_right_cancel (show i₂ + 1 = (i₁ + 1) + 1 by rw [← hgeq]; ring)
        rw [heq] at hi₂; simp_all
      · exact add_right_cancel (show i₁ + 2 = i₂ + 2 from hgeq)
    exfalso
    have hle : Necklace.count w .m ≤ Necklace.count w .s := by
      unfold Necklace.count
      apply Finset.card_le_card_of_injOn g
      · intro x hx
        have hxM := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
        exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg_s x hxM⟩)
      · intro x hx y hy hxy
        have hxM := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
        have hyM := (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
        exact hg_inj x y hxM hyM hxy
    omega

/-- Step (ii-b): The subword LmLLmL appears.
    Proof: From mLLm, the m's are each flanked by L (since LL exists,
    every s is flanked by L, so m can't be adjacent to s; and no mm).
    So L borders mLLm on both sides: LmLLmL. -/
private lemma balanced_has_LmLLmL (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (htern : isTernary w)
    (hLm : Necklace.count w .L > Necklace.count w .m)
    (hms : Necklace.count w .m > Necklace.count w .s) :
    ∃ i : ZMod n, w i = .L ∧ w (i + 1) = .m ∧ w (i + 2) = .L ∧
      w (i + 3) = .L ∧ w (i + 4) = .m ∧ w (i + 5) = .L := by
  obtain ⟨i, him, hiL1, hiL2, him3⟩ := balanced_has_mLLm w hbal htern hLm hms
  have hno_mm := balanced_no_mm w hbal htern hLm hms
  have hn : n > 2 := by
    have := count_pos_of_isTernary w htern .L
    have := count_pos_of_isTernary w htern .m
    have := count_pos_of_isTernary w htern .s
    have := count_total w; omega
  -- LL exists (from the mLLm at i)
  have hLL : w (i + 1) = .L ∧ w (i + 1 + 1) = .L := by
    exact ⟨hiL1, by rw [show i + 1 + 1 = i + 2 from by ring]; exact hiL2⟩
  have hsflanked := balanced_ss_flanked_by_L_of_LL w hbal hn (i + 1) hLL
  -- Every m is flanked by L
  have hm_fwd : ∀ j : ZMod n, w j = .m → w (j + 1) = .L := by
    intro j hj
    cases hj1 : w (j + 1) with
    | L => rfl
    | m => exact absurd ⟨hj, hj1⟩ (hno_mm j)
    | s =>
      have := (hsflanked (j + 1) hj1).1
      rw [show j + 1 - 1 = j from by ring] at this; simp_all
  have hm_bwd : ∀ j : ZMod n, w j = .m → w (j - 1) = .L := by
    intro j hj
    cases hj1 : w (j - 1) with
    | L => rfl
    | m =>
      exact absurd ⟨hj1, by rw [show j - 1 + 1 = j from by ring]; exact hj⟩ (hno_mm (j - 1))
    | s =>
      have := (hsflanked (j - 1) hj1).2
      rw [show j - 1 + 1 = j from by ring] at this; simp_all
  -- Now apply: w(i-1) = L and w(i+4) = L
  have h_left := hm_bwd i him
  have h_right := hm_fwd (i + 3) him3
  refine ⟨i - 1, h_left, by rw [show i - 1 + 1 = i from by ring]; exact him, ?_, ?_, ?_, ?_⟩
  · rw [show i - 1 + 2 = i + 1 from by ring]; exact hiL1
  · rw [show i - 1 + 3 = i + 2 from by ring]; exact hiL2
  · rw [show i - 1 + 4 = i + 3 from by ring]; exact him3
  · rw [show i - 1 + 5 = i + 4 from by ring]
    rw [show i + 4 = i + 3 + 1 from by ring]
    exact h_right

/-- Step (iii): The 7-letter subword LmLsLmL appears.
    Proof: Take any s at position p. By 4-step m-balance (mLLm has m-count 2,
    so every 4-step subword has m-count ≥ 1), the letters at p-2 and p+2 must be m.
    This gives mLsLm. Then the m's are flanked by L (from LmLLmL), giving LmLsLmL. -/
private lemma balanced_has_LmLsLmL (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (htern : isTernary w)
    (hLm : Necklace.count w .L > Necklace.count w .m)
    (hms : Necklace.count w .m > Necklace.count w .s) :
    ∃ i : ZMod n, w i = .L ∧ w (i + 1) = .m ∧ w (i + 2) = .L ∧
      w (i + 3) = .s ∧ w (i + 4) = .L ∧ w (i + 5) = .m ∧ w (i + 6) = .L := by
  -- Get mLLm and structural facts
  obtain ⟨i₀, hi₀m, hi₀L1, hi₀L2, hi₀m3⟩ := balanced_has_mLLm w hbal htern hLm hms
  have hno_mm := balanced_no_mm w hbal htern hLm hms
  have hn4 : n > 4 := by
    have := count_pos_of_isTernary w htern .L
    have := count_pos_of_isTernary w htern .m
    have := count_pos_of_isTernary w htern .s
    have := count_total w; omega
  have hn2 : n > 2 := by omega
  -- LL exists
  have hLL : w (i₀ + 1) = .L ∧ w (i₀ + 1 + 1) = .L :=
    ⟨hi₀L1, by rw [show i₀ + 1 + 1 = i₀ + 2 from by ring]; exact hi₀L2⟩
  have hsflanked := balanced_ss_flanked_by_L_of_LL w hbal hn2 (i₀ + 1) hLL
  -- Every m is flanked by L
  have hm_fwd : ∀ j : ZMod n, w j = .m → w (j + 1) = .L := by
    intro j hj
    cases hj1 : w (j + 1) with
    | L => rfl
    | m => exact absurd ⟨hj, hj1⟩ (hno_mm j)
    | s =>
      have := (hsflanked (j + 1) hj1).1
      rw [show j + 1 - 1 = j from by ring] at this; simp_all
  have hm_bwd : ∀ j : ZMod n, w j = .m → w (j - 1) = .L := by
    intro j hj
    cases hj1 : w (j - 1) with
    | L => rfl
    | m =>
      exact absurd ⟨hj1, by rw [show j - 1 + 1 = j from by ring]; exact hj⟩ (hno_mm (j - 1))
    | s =>
      have := (hsflanked (j - 1) hj1).2
      rw [show j - 1 + 1 = j from by ring] at this; simp_all
  -- Get an s-position
  have hs_pos := count_pos_of_isTernary w htern .s
  rw [Necklace.count, Finset.card_pos] at hs_pos
  obtain ⟨p, hp⟩ := hs_pos
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  -- s at p is flanked by L: LsL
  have hpL := (hsflanked p hp).1  -- w(p-1) = L
  have hpR := (hsflanked p hp).2  -- w(p+1) = L
  -- 4-step balance: mLLm has m-count 2, so every 4-step subword has m-count ≥ 1
  -- The 4-step subword [w(p-2), L, s, L] at p-2 must have m-count ≥ 1 → w(p-2) = m
  have hpm2 : w (p - 2) = .m := by
    have hdiff := balanced_four_step_diff_zmod w hbal hn4 i₀ (p - 2) .m
    rw [hi₀m, hi₀L1, hi₀L2, hi₀m3] at hdiff
    rw [show p - 2 + 1 = p - 1 from by ring, hpL,
        show p - 2 + 2 = p from by ring, hp,
        show p - 2 + 3 = p + 1 from by ring, hpR] at hdiff
    simp only [List.count_cons, List.count_nil, beq_iff_eq] at hdiff
    cases hv : w (p - 2) with
    | m => rfl
    | L => rw [hv] at hdiff; simp at hdiff
    | s => rw [hv] at hdiff; simp at hdiff
  -- The 4-step subword [L, s, L, w(p+2)] at p-1 must have m-count ≥ 1 → w(p+2) = m
  have hpp2 : w (p + 2) = .m := by
    have hdiff := balanced_four_step_diff_zmod w hbal hn4 i₀ (p - 1) .m
    rw [hi₀m, hi₀L1, hi₀L2, hi₀m3] at hdiff
    rw [show p - 1 + 1 = p from by ring, hp,
        show p - 1 + 2 = p + 1 from by ring, hpR,
        show p - 1 + 3 = p + 2 from by ring] at hdiff
    rw [hpL] at hdiff
    simp only [List.count_cons, List.count_nil, beq_iff_eq] at hdiff
    cases hv : w (p + 2) with
    | m => rfl
    | L => rw [hv] at hdiff; simp at hdiff
    | s => rw [hv] at hdiff; simp at hdiff
  -- Now we have mLsLm at p-2. The m's are flanked by L.
  have h_left := hm_bwd (p - 2) hpm2
  have h_right := hm_fwd (p + 2) hpp2
  refine ⟨p - 3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show p - 3 = p - 2 - 1 from by ring]; exact h_left
  · rw [show p - 3 + 1 = p - 2 from by ring]; exact hpm2
  · rw [show p - 3 + 2 = p - 1 from by ring]; exact hpL
  · rw [show p - 3 + 3 = p from by ring]; exact hp
  · rw [show p - 3 + 4 = p + 1 from by ring]; exact hpR
  · rw [show p - 3 + 5 = p + 2 from by ring]; exact hpp2
  · rw [show p - 3 + 6 = p + 3 from by ring]
    rw [show p + 3 = p + 2 + 1 from by ring]
    exact h_right

/-- For each s at position p in a balanced ternary necklace with a > b > c,
    the next 7 values are determined: s L m L L m L, and w(p+7) = s.
    Uses: flanking (2-step), 4-step m-balance, no_mLm (3-step),
    6-step s-balance, 3-step L-balance (mLs), 5-step L-balance. -/
private lemma s_neighborhood (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (htern : isTernary w)
    (hLm : Necklace.count w .L > Necklace.count w .m)
    (hms : Necklace.count w .m > Necklace.count w .s)
    (p : ZMod n) (hp : w p = .s) :
    w (p + 1) = .L ∧ w (p + 2) = .m ∧ w (p + 3) = .L ∧
    w (p + 4) = .L ∧ w (p + 5) = .m ∧ w (p + 6) = .L ∧
    w (p + 7) = .s := by
  -- Structural facts
  have hno_mm := balanced_no_mm w hbal htern hLm hms
  have hno_mLm := balanced_no_mLm w hbal htern hLm hms
  obtain ⟨i₀, hi₀m, hi₀L1, hi₀L2, hi₀m3⟩ := balanced_has_mLLm w hbal htern hLm hms
  obtain ⟨j₀, hj₀L, hj₀m, hj₀L2, hj₀L3, hj₀m4, hj₀L5⟩ :=
    balanced_has_LmLLmL w hbal htern hLm hms
  have hn4 : n > 4 := by
    have := count_pos_of_isTernary w htern .L
    have := count_pos_of_isTernary w htern .m
    have := count_pos_of_isTernary w htern .s
    have := count_total w; omega
  have hn2 : n > 2 := by omega
  -- LL exists
  have hLL : w (i₀ + 1) = .L ∧ w (i₀ + 1 + 1) = .L :=
    ⟨hi₀L1, by rw [show i₀ + 1 + 1 = i₀ + 2 from by ring]; exact hi₀L2⟩
  have hsflanked := balanced_ss_flanked_by_L_of_LL w hbal hn2 (i₀ + 1) hLL
  -- m flanked by L
  have hm_fwd : ∀ j : ZMod n, w j = .m → w (j + 1) = .L := by
    intro j hj; cases hj1 : w (j + 1) with
    | L => rfl
    | m => exact absurd ⟨hj, hj1⟩ (hno_mm j)
    | s => have := (hsflanked (j + 1) hj1).1
           rw [show j + 1 - 1 = j from by ring] at this; simp_all
  have hm_bwd : ∀ j : ZMod n, w j = .m → w (j - 1) = .L := by
    intro j hj; cases hj1 : w (j - 1) with
    | L => rfl
    | m => exact absurd ⟨hj1, by rw [show j - 1 + 1 = j from by ring]; exact hj⟩
             (hno_mm (j - 1))
    | s => have := (hsflanked (j - 1) hj1).2
           rw [show j - 1 + 1 = j from by ring] at this; simp_all
  -- n > 6 (if n ≤ 6: LmLLmL pattern covers all positions, no room for s)
  have hn6 : n > 6 := by
    by_contra hle; push_neg at hle
    have hn6' : n = 5 ∨ n = 6 := by omega
    rcases hn6' with rfl | rfl
    · -- n = 5: j₀+4 ≡ j₀-1 (mod 5), giving mLm at j₀-1
      -- j₀-1 = j₀+4: m, j₀: L, j₀+1: m → mLm contradiction
      exact hno_mLm (j₀ + 4)
        ⟨hj₀m4,
         by rw [show j₀ + 4 + 1 = j₀ + (5 : ZMod 5) from by ring,
                show (5 : ZMod 5) = 0 from by decide]; simp [hj₀L],
         by rw [show j₀ + 4 + 2 = j₀ + 1 + (5 : ZMod 5) from by ring,
                show (5 : ZMod 5) = 0 from by decide]; simp [hj₀m]⟩
    · -- n = 6: all 6 positions have values L or m, but count s > 0
      exfalso
      have hs_count := count_pos_of_isTernary w htern .s
      have : Necklace.count w .s = 0 := by
        rw [Necklace.count]; apply Finset.card_eq_zero.mpr
        rw [Finset.filter_eq_empty_iff]
        intro p _
        -- p = j₀ + (p - j₀), and (p - j₀).val ∈ {0,...,5}
        -- Every position is L or m, so ≠ s
        have hall : ∀ k : Fin 6, w (j₀ + (k : ℕ)) ≠ .s := by
          intro ⟨k, hk⟩
          interval_cases k <;> simp_all []
        have hp : p = j₀ + ((p - j₀).val : ℕ) := by
          rw [ZMod.natCast_zmod_val]; ring
        rw [hp]
        exact hall ⟨(p - j₀).val, ZMod.val_lt _⟩
      omega
  have hn5 : n > 5 := by omega
  have hn3 : n > 3 := by omega
  -- w(p+1) = L (s flanked by L)
  have h1 := (hsflanked p hp).2
  -- w(p-1) = L
  have hm1 := (hsflanked p hp).1
  -- w(p+2) = m (4-step m-balance: mLLm has m-count 2, [L,s,L,w(p+2)] needs m-count ≥ 1)
  have h2 : w (p + 2) = .m := by
    have hdiff := balanced_four_step_diff_zmod w hbal hn4 i₀ (p - 1) .m
    rw [hi₀m, hi₀L1, hi₀L2, hi₀m3] at hdiff
    rw [show p - 1 + 1 = p from by ring, hp,
        show p - 1 + 2 = p + 1 from by ring, h1,
        show p - 1 + 3 = p + 2 from by ring, hm1] at hdiff
    simp only [List.count_cons, List.count_nil, beq_iff_eq] at hdiff
    cases hv : w (p + 2) with
    | m => rfl
    | L => rw [hv] at hdiff; simp at hdiff
    | s => rw [hv] at hdiff; simp at hdiff
  -- w(p-2) = m (symmetric 4-step argument)
  have hm2 : w (p - 2) = .m := by
    have hdiff := balanced_four_step_diff_zmod w hbal hn4 i₀ (p - 2) .m
    rw [hi₀m, hi₀L1, hi₀L2, hi₀m3] at hdiff
    rw [show p - 2 + 1 = p - 1 from by ring, hm1,
        show p - 2 + 2 = p from by ring, hp,
        show p - 2 + 3 = p + 1 from by ring, h1] at hdiff
    simp only [List.count_cons, List.count_nil, beq_iff_eq] at hdiff
    cases hv : w (p - 2) with
    | m => rfl
    | L => rw [hv] at hdiff; simp at hdiff
    | s => rw [hv] at hdiff; simp at hdiff
  -- w(p+3) = L (m flanked by L: w(p+2) = m → w(p+3) = w(p+2+1) = L)
  have h3 : w (p + 3) = .L := by
    rw [show p + 3 = p + 2 + 1 from by ring]; exact hm_fwd (p + 2) h2
  -- w(p-3) = L
  have hm3 : w (p - 3) = .L := by
    rw [show p - 3 = p - 2 - 1 from by ring]; exact hm_bwd (p - 2) hm2
  -- w(p+4): not m (no_mLm at p+2), not s (6-step s-balance: LmLLmL has s-count 0,
  --   [L,s,L,m,L,s] at p-1 would have s-count 2)
  have h4 : w (p + 4) = .L := by
    have h4_nm : w (p + 4) ≠ .m := by
      intro hc; exact hno_mLm (p + 2)
        ⟨h2, by rw [show p + 2 + 1 = p + 3 from by ring]; exact h3,
         by rwa [show p + 2 + 2 = p + 4 from by ring]⟩
    have h4_ns : w (p + 4) ≠ .s := by
      intro hc
      have hdiff := balanced_six_step_diff_zmod w hbal hn6 j₀ (p - 1) .s
      rw [hj₀L, hj₀m, hj₀L2, hj₀L3, hj₀m4, hj₀L5] at hdiff
      rw [show p - 1 + 1 = p from by ring, hp,
          show p - 1 + 2 = p + 1 from by ring, h1,
          show p - 1 + 3 = p + 2 from by ring, h2,
          show p - 1 + 4 = p + 3 from by ring, h3,
          show p - 1 + 5 = p + 4 from by ring, hc, hm1] at hdiff
      simp at hdiff
    cases hv : w (p + 4) with
    | L => rfl | m => exact absurd hv h4_nm | s => exact absurd hv h4_ns
  -- w(p-4) = L (symmetric)
  have hm4 : w (p - 4) = .L := by
    have hm4_nm : w (p - 4) ≠ .m := by
      intro hc; exact hno_mLm (p - 4)
        ⟨hc, by rw [show p - 4 + 1 = p - 3 from by ring]; exact hm3,
         by rw [show p - 4 + 2 = p - 2 from by ring]; exact hm2⟩
    have hm4_ns : w (p - 4) ≠ .s := by
      intro hc
      have hdiff := balanced_six_step_diff_zmod w hbal hn6 j₀ (p - 4) .s
      rw [hj₀L, hj₀m, hj₀L2, hj₀L3, hj₀m4, hj₀L5] at hdiff
      rw [show p - 4 + 1 = p - 3 from by ring, hm3,
          show p - 4 + 2 = p - 2 from by ring, hm2,
          show p - 4 + 3 = p - 1 from by ring, hm1,
          show p - 4 + 4 = p from by ring, hp,
          show p - 4 + 5 = p + 1 from by ring, h1, hc] at hdiff
      simp at hdiff
    cases hv : w (p - 4) with
    | L => rfl | m => exact absurd hv hm4_nm | s => exact absurd hv hm4_ns
  -- mLs exists at p-2: [m, L, s] (from w(p-2)=m, w(p-1)=L, w(p)=s)
  -- w(p+5): not L (3-step L-balance: LLL at p+3 has L-count 3, mLs has 1, diff 2)
  --         not s (6-step s-balance: [s,L,m,L,L,s] at p would have s-count 2... wait, let me check)
  -- Actually: not s by 4-step balance. [L,L,s,w(p+6)] at p+3 — if w(p+5)=s then w(p+6)=L (flanking)
  --   giving [L,L,s,L] with m-count 0. mLLm has m-count 2. |2-0|=2. Contradiction.
  have h5 : w (p + 5) = .m := by
    have h5_nL : w (p + 5) ≠ .L := by
      intro hc
      -- [L,L,L] at p+3 has L-count 3. mLs [m,L,s] at p-2 has L-count 1. |3-1|=2.
      have hdiff := balanced_three_step_diff_zmod w hbal hn3 (p + 3) (p - 2) .L
      rw [show p + 3 + 1 = p + 4 from by ring, h4,
          show p + 3 + 2 = p + 5 from by ring, hc, h3,
          show p - 2 + 1 = p - 1 from by ring, hm1,
          show p - 2 + 2 = p from by ring, hp, hm2] at hdiff
      simp at hdiff
    have h5_ns : w (p + 5) ≠ .s := by
      intro hc
      -- s at p+5 flanked by L: w(p+6) = L
      have hp6 := (hsflanked (p + 5) hc).2
      rw [show p + 5 + 1 = p + 6 from by ring] at hp6
      -- [L,L,s,L] at p+3 has m-count 0. mLLm has m-count 2.
      have hdiff := balanced_four_step_diff_zmod w hbal hn4 i₀ (p + 3) .m
      rw [hi₀m, hi₀L1, hi₀L2, hi₀m3, h3,
          show p + 3 + 1 = p + 4 from by ring, h4,
          show p + 3 + 2 = p + 5 from by ring, hc,
          show p + 3 + 3 = p + 6 from by ring, hp6] at hdiff
      simp at hdiff
    cases hv : w (p + 5) with
    | m => rfl | L => exact absurd hv h5_nL | s => exact absurd hv h5_ns
  -- w(p+6) = L (m flanked by L)
  have h6 : w (p + 6) = .L := by
    rw [show p + 6 = p + 5 + 1 from by ring]; exact hm_fwd (p + 5) h5
  -- w(p+7): not m (no_mLm at p+5), not L (5-step L-balance)
  have h7 : w (p + 7) = .s := by
    have h7_nm : w (p + 7) ≠ .m := by
      intro hc; exact hno_mLm (p + 5)
        ⟨h5, by rw [show p + 5 + 1 = p + 6 from by ring]; exact h6,
         by rwa [show p + 5 + 2 = p + 7 from by ring]⟩
    have h7_nL : w (p + 7) ≠ .L := by
      intro hc
      -- 5-step L-balance: [L,L,m,L,L] at p+3 has L-count 4.
      -- [m,L,s,L,m] at p-2 has L-count 2. |4-2|=2.
      have hdiff := balanced_five_step_diff_zmod w hbal hn5 (p + 3) (p - 2) .L
      rw [h3, show p + 3 + 1 = p + 4 from by ring, h4,
          show p + 3 + 2 = p + 5 from by ring, h5,
          show p + 3 + 3 = p + 6 from by ring, h6,
          show p + 3 + 4 = p + 7 from by ring, hc,
          hm2, show p - 2 + 1 = p - 1 from by ring, hm1,
          show p - 2 + 2 = p from by ring, hp,
          show p - 2 + 3 = p + 1 from by ring, h1,
          show p - 2 + 4 = p + 2 from by ring, h2] at hdiff
      simp at hdiff
    cases hv : w (p + 7) with
    | s => rfl | m => exact absurd hv h7_nm | L => exact absurd hv h7_nL
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- Step (iv): The word has translational period 7, i.e., w(i) = w(i + 7)
    for all i. Proof: Each surrounding letter of LmLsLmL is forced;
    every s has this determined neighborhood, so the whole word repeats. -/
private lemma balanced_all_distinct_periodic_seven (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (htern : isTernary w)
    (hLm : Necklace.count w .L > Necklace.count w .m)
    (hms : Necklace.count w .m > Necklace.count w .s) :
    ∀ i : ZMod n, w i = w (i + 7) := by
  -- Get an s-position
  have hs_pos := count_pos_of_isTernary w htern .s
  rw [Necklace.count, Finset.card_pos] at hs_pos
  obtain ⟨p₀, hp₀⟩ := hs_pos
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp₀
  -- For any s at p: the next 7 values are sLmLLmL and w(p+7) = s
  have snbr := s_neighborhood w hbal htern hLm hms
  -- For any s at p: w(p+j+7) = w(p+j) for j = 0,...,6
  have shift_eq : ∀ p : ZMod n, w p = .s → ∀ j : Fin 7,
      w (p + (j : ℕ)) = w (p + 7 + (j : ℕ)) := by
    intro p hp j
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := snbr p hp
    have h7s := h7  -- w(p+7) = s
    obtain ⟨h1', h2', h3', h4', h5', h6', _⟩ := snbr (p + 7) h7s
    fin_cases j <;> simp_all [show p + 7 + 1 = p + (7 + 1) from by ring,
      show p + 7 + 2 = p + (7 + 2) from by ring,
      show p + 7 + 3 = p + (7 + 3) from by ring,
      show p + 7 + 4 = p + (7 + 4) from by ring,
      show p + 7 + 5 = p + (7 + 5) from by ring,
      show p + 7 + 6 = p + (7 + 6) from by ring]
  -- Every position 7k ahead of p₀ is also s
  have hs_rep : ∀ k : ℕ, w (p₀ + (7 * k : ℕ)) = .s := by
    intro k; induction k with
    | zero => simp [hp₀]
    | succ k ih =>
      have := (snbr (p₀ + (7 * k : ℕ)) ih).2.2.2.2.2.2
      rw [show p₀ + (7 * k : ℕ) + 7 = p₀ + (7 * (k + 1) : ℕ) from by push_cast; ring] at this
      exact this
  -- Main proof: decompose i = (p₀ + 7q) + d where d < 7
  intro i
  set r := (i - p₀).val
  set d := r % 7
  set q := r / 7
  have hd7 : d < 7 := Nat.mod_lt _ (by norm_num)
  have hqd : r = 7 * q + d := (Nat.div_add_mod r 7).symm
  -- p₀ + 7q is an s-position
  have hsq := hs_rep q
  -- shift_eq gives w((p₀+7q) + d) = w((p₀+7q) + 7 + d)
  have hse := shift_eq (p₀ + (7 * q : ℕ)) hsq ⟨d, hd7⟩
  -- Rewrite i in terms of p₀ + 7q + d
  have hi : (i : ZMod n) = p₀ + (7 * q : ℕ) + (d : ZMod n) := by
    calc i = p₀ + (i - p₀) := by ring
      _ = p₀ + ((i - p₀).val : ZMod n) := by rw [ZMod.natCast_zmod_val]
      _ = p₀ + ((7 * q + d : ℕ) : ZMod n) := by rw [show (i - p₀).val = 7 * q + d from hqd]
      _ = p₀ + (7 * q : ℕ) + (d : ZMod n) := by push_cast; ring
  rw [hi, show p₀ + (7 * q : ℕ) + (d : ZMod n) + 7 =
          p₀ + (7 * q : ℕ) + 7 + (d : ZMod n) from by ring]
  exact hse

/-- Balanced primitive ternary scales with all three distinct step counts
    must be the Fraenkel word `XYXZXYX` (sporadic balanced). -/
private lemma balanced_all_distinct_isSporadicBalanced (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (hprim : Necklace.isPrimitive w)
    (htern : isTernary w)
    (hLm : Necklace.count w .L ≠ Necklace.count w .m)
    (hms : Necklace.count w .m ≠ Necklace.count w .s)
    (hLs : Necklace.count w .L ≠ Necklace.count w .s) :
    isSporadicBalanced w := by
  -- Step 0: WLOG normalize counts so L > m > s
  obtain ⟨σ, hLm', hms'⟩ := exists_perm_ordered_counts w hLm hms hLs
  set w' := Necklace.applyPerm σ w
  have hbal' : Necklace.isBalanced w' := isBalanced_applyPerm σ w hbal
  have hprim' : Necklace.isPrimitive w' := isPrimitive_applyPerm σ w hprim
  have htern' : isTernary w' := (isTernary_applyPerm σ w).mpr htern
  -- Steps 1-3: The 7-letter pattern LmLsLmL appears in w'
  obtain ⟨i, hi0, hi1, hi2, hi3, hi4, hi5, hi6⟩ :=
    balanced_has_LmLsLmL w' hbal' htern' hLm' hms'
  -- Step 4: w' has translational period 7
  have hper := balanced_all_distinct_periodic_seven w' hbal' htern' hLm' hms'
  -- n = 7: Use Bézout + primitivity.
  have hn_eq : n = 7 := by
    -- Iterate hper: w(i) = w(i + m * 7) for all m
    have hiter : ∀ (j m : ℕ), w' (j : ZMod n) = w' ((j + m * 7 : ℕ) : ZMod n) := by
      intro j m; induction m with
      | zero => simp
      | succ m ih =>
        have hstep := hper ((j + m * 7 : ℕ) : ZMod n)
        rw [show ((j + m * 7 : ℕ) : ZMod n) + 7 = ((j + (m + 1) * 7 : ℕ) : ZMod n) from by
          push_cast; ring] at hstep
        exact ih.trans hstep
    -- Bézout: gcd(7, n) is a translational period
    have hgcd_pos : 0 < Nat.gcd 7 n :=
      Nat.pos_of_ne_zero (by intro h; rw [Nat.gcd_eq_zero_iff] at h; omega)
    have hbez : (↑(Nat.gcd 7 n) : ZMod n) =
        (↑(7 : ℕ) : ZMod n) * ((Nat.gcdA 7 n : ℤ) : ZMod n) := by
      have := congr_arg (fun x : ℤ => (x : ZMod n)) (Nat.gcd_eq_gcd_ab 7 n)
      push_cast at this; rwa [ZMod.natCast_self, zero_mul, add_zero] at this
    have hperiodic_gcd : ∀ (j : ZMod n), w' j = w' (j + ↑(Nat.gcd 7 n)) := by
      intro j
      have hj := hiter (ZMod.val j) (ZMod.val ((Nat.gcdA 7 n : ℤ) : ZMod n))
      rw [ZMod.natCast_zmod_val j] at hj
      rw [hj]; congr 1
      rw [show ((ZMod.val j + ZMod.val ((Nat.gcdA 7 n : ℤ) : ZMod n) * 7 : ℕ) : ZMod n) =
          (ZMod.val j : ZMod n) + (ZMod.val ((Nat.gcdA 7 n : ℤ) : ZMod n) : ZMod n) * 7 from by
            push_cast; ring,
          ZMod.natCast_zmod_val j,
          ZMod.natCast_zmod_val ((Nat.gcdA 7 n : ℤ) : ZMod n)]
      rw [show ((Nat.gcdA 7 n : ℤ) : ZMod n) * 7 = (7 : ℕ) * ((Nat.gcdA 7 n : ℤ) : ZMod n)
            from by push_cast; ring]
      rw [← hbez]
    -- gcd(7,n) ∈ {1, 7} since 7 is prime
    have h7_prime : Nat.Prime 7 := by decide
    have hgcd_cases := h7_prime.eq_one_or_self_of_dvd (Nat.gcd 7 n) (Nat.gcd_dvd_left 7 n)
    -- gcd = 1 is impossible: period ≤ 1 but primitivity says period = n ≥ 5
    have hn5 : n > 4 := by
      have := count_pos_of_isTernary w' htern' .L
      have := count_pos_of_isTernary w' htern' .m
      have := count_pos_of_isTernary w' htern' .s
      have := count_total w'; omega
    have hgcd_ne_1 : Nat.gcd 7 n ≠ 1 := by
      intro hgcd1
      have hperiod_le := Necklace.period_length_le_of_translational_period w'
        (Nat.gcd 7 n) hgcd_pos (by omega) (Nat.gcd_dvd_right 7 n) hperiodic_gcd
      rw [hprim', hgcd1] at hperiod_le; omega
    -- gcd = 7: so 7 ∣ n. If n > 7, period ≤ 7 < n contradicts primitivity.
    have hgcd7 : Nat.gcd 7 n = 7 := by
      rcases hgcd_cases with h | h
      · exact absurd h hgcd_ne_1
      · exact h
    have h7_dvd : 7 ∣ n := by rw [← hgcd7]; exact Nat.gcd_dvd_right 7 n
    by_contra hne
    have h7_lt : 7 < n := by
      rcases h7_dvd with ⟨k, hk⟩
      cases k with
      | zero => simp at hk; omega
      | succ k => cases k with
        | zero => omega
        | succ k => omega
    have hperiod_le := Necklace.period_length_le_of_translational_period w'
      (Nat.gcd 7 n) hgcd_pos (by omega) (Nat.gcd_dvd_right 7 n) hperiodic_gcd
    rw [hprim', hgcd7] at hperiod_le; omega
  -- Construct isSporadicBalanced w'
  have hsb : isSporadicBalanced w' := by
    refine ⟨hn_eq, 1, i, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Equiv.Perm.one_apply]
    · rw [show ((0 : ℕ) : ZMod n) + i = i from by push_cast; ring]; exact hi0
    · rw [show ((1 : ℕ) : ZMod n) + i = i + 1 from by push_cast; ring]; exact hi1
    · rw [show ((2 : ℕ) : ZMod n) + i = i + 2 from by push_cast; ring]; exact hi2
    · rw [show ((3 : ℕ) : ZMod n) + i = i + 3 from by push_cast; ring]; exact hi3
    · rw [show ((4 : ℕ) : ZMod n) + i = i + 4 from by push_cast; ring]; exact hi4
    · rw [show ((5 : ℕ) : ZMod n) + i = i + 5 from by push_cast; ring]; exact hi5
    · rw [show ((6 : ℕ) : ZMod n) + i = i + 6 from by push_cast; ring]; exact hi6
  exact isSporadicBalanced_of_applyPerm σ w hsb

/-- When the k₀-stacking has an isolated minority type among good positions
    (no consecutive Qmin pairs), construct hasAS.
    Proof approach: build binary bridge B₁ for (m,s) identification,
    use its generator k₁ to establish (n-1,1) split of .L at step k₁,
    then show alternation of .m at good k₁-positions via 2k₁ MOS analysis.
    Cases: D1 (few Qmin) → AS at k₁; D3 (many Qmin) → sporadic balanced. -/
private lemma hasAS_of_stacking_nonalt (w : TernaryNecklace n)
    (htern : isTernary w) (hpwf : isPairwisePrimMOS w)
    (hodd : n % 2 = 1) (hns : ¬ isSporadicBalanced w)
    (k₀ r : ℕ) (_hk₀_lt : k₀ < n) (_hk₀_cop : Nat.Coprime k₀ n)
    (hn_ge3 : n ≥ 3)
    (Qmaj Qmin : ZVector StepSize)
    (_h_two_types : ∀ i, i < n - 1 →
        Necklace.kStepVector w (r + i * k₀) k₀ = Qmaj ∨
        Necklace.kStepVector w (r + i * k₀) k₀ = Qmin)
    (_hclose_ne_maj : Necklace.kStepVector w (r + (n - 1) * k₀) k₀ ≠ Qmaj)
    (_hclose_ne_min : Necklace.kStepVector w (r + (n - 1) * k₀) k₀ ≠ Qmin)
    (_h_isolated : ∀ i, i + 1 < n - 1 →
        ¬ (Necklace.kStepVector w (r + i * k₀) k₀ = Qmin ∧
           Necklace.kStepVector w (r + (i + 1) * k₀) k₀ = Qmin))
    (hneq_Lm : Necklace.count w .L ≠ Necklace.count w .m)
    (hneq_ms : Necklace.count w .m ≠ Necklace.count w .s)
    (hneq_Ls : Necklace.count w .L ≠ Necklace.count w .s) :
    hasAS w := by
  -- Extract PWF components and ternarity
  obtain ⟨⟨hmosLm, hprimLm⟩, ⟨hmosms, hprimms⟩, ⟨hmosLs, hprimLs⟩⟩ := hpwf
  obtain ⟨⟨iL, hiL⟩, ⟨im, him⟩, ⟨is, his⟩⟩ := htern
  have hn_pos : 0 < n := by omega
  -- Build B₁ = identifiedToBinary(identifyPair w .m .s) — the (m,s)-bridge
  set B₁ := identifiedToBinary (identifyPair w .m .s) with hB₁_def
  have hB₁mos : BinaryNecklace.isMOS B₁ := by
    constructor
    · exact ⟨⟨iL, by simp [B₁, identifiedToBinary, identifyPair, hiL, msToBinary]⟩,
             ⟨im, by simp [B₁, identifiedToBinary, identifyPair, him, msToBinary]⟩⟩
    · intro k hk hk'
      rw [show B₁ = msToBinary ∘ identifyPair w .m .s from rfl,
          allKStepMultisets_comp' _ msToBinary k]
      calc ((Necklace.allKStepMultisets _ k).map (Multiset.map msToBinary)).toFinset.card
          ≤ (Necklace.allKStepMultisets _ k).toFinset.card := by
            rw [show ((Necklace.allKStepMultisets (identifyPair w .m .s) k).map
                (Multiset.map msToBinary)).toFinset =
                (Necklace.allKStepMultisets (identifyPair w .m .s) k).toFinset.image
                (Multiset.map msToBinary) from by
              ext; simp [List.mem_toFinset, Finset.mem_image, List.mem_map]]
            exact Finset.card_image_le
        _ ≤ 2 := hmosms.2 k hk hk'
  have hB₁prim : Necklace.isPrimitive B₁ :=
    isPrimitive_comp_of_injective_on_range _ msToBinary hprimms (by
      intro i j hij
      have hIi : identifyPair w .m .s i ≠ .m := by
        by_cases h : w i = .m <;> simp [identifyPair, h]
      have hIj : identifyPair w .m .s j ≠ .m := by
        by_cases h : w j = .m <;> simp [identifyPair, h]
      cases hvi : identifyPair w .m .s i <;> cases hvj : identifyPair w .m .s j <;>
        simp_all [msToBinary])
  -- Get generator k₁ with stacking structure from B₁
  obtain ⟨k₁, r₁, g₁, hk₁_pos, hk₁_lt, hk₁_cop, hgood₁_B, hclose₁_B⟩ :=
    primitive_mos_stacking B₁ hB₁mos hB₁prim hn_ge3
  -- Bridge: at good k₁-positions, w's .L = g₁.L (constant)
  have hgood₁_L : ∀ i : ℕ, i < n - 1 →
      (Necklace.kStepVector w (r₁ + i * k₁) k₁) .L = g₁ .L := by
    intro i hi
    have h := kStepVector_bridge_L_ms w (r₁ + i * k₁) k₁
    rw [hgood₁_B i hi] at h; linarith
  -- Bridge: at good k₁-positions, w's .m + .s = g₁.s (constant)
  have hgood₁_ms : ∀ i : ℕ, i < n - 1 →
      (Necklace.kStepVector w (r₁ + i * k₁) k₁) .m +
      (Necklace.kStepVector w (r₁ + i * k₁) k₁) .s = g₁ .s := by
    intro i hi
    have h := kStepVector_bridge_s_ms w (r₁ + i * k₁) k₁
    rw [hgood₁_B i hi] at h; linarith
  -- Closing: w's .L ≠ g₁.L (since B₁'s closing vector ≠ g₁)
  have hclose₁_L_ne : (Necklace.kStepVector w (r₁ + (n - 1) * k₁) k₁) .L ≠ g₁ .L := by
    intro heq; apply hclose₁_B
    have hg₁_total : g₁ .L + g₁ .s = ↑k₁ := by
      have h := hgood₁_B 0 (by omega)
      rw [show r₁ + 0 * k₁ = r₁ from by omega] at h
      rw [← h]; exact_mod_cast kStepVector_total_count B₁ r₁ k₁
    have hj_total : (Necklace.kStepVector B₁ (r₁ + (n - 1) * k₁) k₁) .L +
        (Necklace.kStepVector B₁ (r₁ + (n - 1) * k₁) k₁) .s = ↑k₁ :=
      by exact_mod_cast kStepVector_total_count B₁ (r₁ + (n - 1) * k₁) k₁
    have hL_eq : (Necklace.kStepVector B₁ (r₁ + (n - 1) * k₁) k₁) .L = g₁ .L := by
      have h := kStepVector_bridge_L_ms w (r₁ + (n - 1) * k₁) k₁; linarith
    have hs_eq : (Necklace.kStepVector B₁ (r₁ + (n - 1) * k₁) k₁) .s = g₁ .s := by
      linarith
    exact funext fun a => by cases a <;> [exact hL_eq; exact hs_eq]
  -- Good-position vectors determined by .m (since .L and .m+.s are constant)
  have hgood₁_det : ∀ i j : ℕ, i < n - 1 → j < n - 1 →
      (Necklace.kStepVector w (r₁ + i * k₁) k₁) .m =
      (Necklace.kStepVector w (r₁ + j * k₁) k₁) .m →
      Necklace.kStepVector w (r₁ + i * k₁) k₁ =
      Necklace.kStepVector w (r₁ + j * k₁) k₁ := by
    intro i j hi hj hm_eq
    funext a; cases a with
    | L => rw [hgood₁_L i hi, hgood₁_L j hj]
    | m => exact hm_eq
    | s => linarith [hgood₁_ms i hi, hgood₁_ms j hj]
  -- Case: all good vectors are the same → degenerate hasAS
  rcases Classical.em (∀ i : ℕ, i < n - 1 →
      Necklace.kStepVector w (r₁ + i * k₁) k₁ = Necklace.kStepVector w r₁ k₁) with
      hall_eq | hall_neq
  · have hQ₁_L : (Necklace.kStepVector w r₁ k₁) .L = g₁ .L := by
      have := hgood₁_L 0 (by omega); rwa [show r₁ + 0 * k₁ = r₁ from by omega] at this
    exact ⟨k₁, r₁, fun _ => Necklace.kStepVector w r₁ k₁, hk₁_lt, hk₁_cop,
      fun i => hall_eq i.val i.isLt,
      fun _ heq => hclose₁_L_ne ((congr_fun heq .L).trans hQ₁_L)⟩
  · -- ≥ 2 distinct good-position vector types at step k₁
    push_neg at hall_neq
    obtain ⟨i₂, hi₂_lt, hi₂_ne⟩ := hall_neq
    set Q₁ := Necklace.kStepVector w r₁ k₁ with hQ₁_def
    set R₁ := Necklace.kStepVector w (r₁ + i₂ * k₁) k₁ with hR₁_def
    have h0k₁ : r₁ + 0 * k₁ = r₁ := by omega
    -- Q₁ and R₁ have different .m components
    have hQ₁R₁_m_ne : Q₁ .m ≠ R₁ .m := by
      intro heq; apply hi₂_ne
      have h := hgood₁_det i₂ 0 hi₂_lt (by omega) (by
        show (Necklace.kStepVector w (r₁ + i₂ * k₁) k₁) .m =
            (Necklace.kStepVector w (r₁ + 0 * k₁) k₁) .m
        rw [h0k₁]; exact heq.symm)
      rw [h0k₁] at h; exact h
    -- MOS of identifyPair w .L .s gives ≤ 2 distinct k₁-step vectors
    have hLs_le2 : (distinctKStepVectors (identifyPair w .L .s) k₁).card ≤ 2 := by
      rw [distinctKStepVectors_card_eq]; exact hmosLs.2 k₁ hk₁_pos hk₁_lt
    -- identifyPair .L .s preserves the .m component of k₁-step vectors
    have hident₁_m : ∀ j : ℕ,
        (Necklace.kStepVector (identifyPair w .L .s) j k₁) .m =
        (Necklace.kStepVector w j k₁) .m := by
      intro j; rw [identifyPair_kStepVector w .L .s (by decide) j k₁]
      simp [ZVector.identifyPair]
    -- Any position's identifyPair k₁-step vector is in distinctKStepVectors
    have hident₁_mem : ∀ j : ℕ,
        Necklace.kStepVector (identifyPair w .L .s) j k₁ ∈
        distinctKStepVectors (identifyPair w .L .s) k₁ := by
      intro j; unfold distinctKStepVectors Necklace.allKStepVectors
      rw [List.mem_toFinset, List.mem_map]
      exact ⟨j % n, List.mem_range.mpr (Nat.mod_lt _ hn_pos), kStepVector_mod_n _ _ _⟩
    -- identifyPair vectors at Q₁ and R₁ positions are distinct (different .m)
    have hvQ₁R₁_ne : Necklace.kStepVector (identifyPair w .L .s) r₁ k₁ ≠
        Necklace.kStepVector (identifyPair w .L .s) (r₁ + i₂ * k₁) k₁ := by
      intro heq; apply hQ₁R₁_m_ne
      change (Necklace.kStepVector w r₁ k₁) .m =
          (Necklace.kStepVector w (r₁ + i₂ * k₁) k₁) .m
      rw [← hident₁_m, ← hident₁_m, heq]
    -- Card = 2 (two distinct elements in a set of size ≤ 2)
    have hLs_eq2 : (distinctKStepVectors (identifyPair w .L .s) k₁).card = 2 := by
      have hge := Finset.card_le_card (show
          {Necklace.kStepVector (identifyPair w .L .s) r₁ k₁,
           Necklace.kStepVector (identifyPair w .L .s) (r₁ + i₂ * k₁) k₁} ⊆
          distinctKStepVectors (identifyPair w .L .s) k₁ from
        Finset.insert_subset_iff.mpr
          ⟨hident₁_mem r₁, Finset.singleton_subset_iff.mpr (hident₁_mem (r₁ + i₂ * k₁))⟩)
      rw [Finset.card_pair hvQ₁R₁_ne] at hge; omega
    -- Every good k₁-position vector of w is Q₁ or R₁
    have h_two_types₁ : ∀ i : ℕ, i < n - 1 →
        Necklace.kStepVector w (r₁ + i * k₁) k₁ = Q₁ ∨
        Necklace.kStepVector w (r₁ + i * k₁) k₁ = R₁ := by
      intro i hi
      by_cases heq_vQ : Necklace.kStepVector (identifyPair w .L .s) (r₁ + i * k₁) k₁ =
          Necklace.kStepVector (identifyPair w .L .s) r₁ k₁
      · left
        have hm_eq : (Necklace.kStepVector w (r₁ + i * k₁) k₁) .m =
            (Necklace.kStepVector w (r₁ + 0 * k₁) k₁) .m := by
          rw [h0k₁]; rw [← hident₁_m, ← hident₁_m, heq_vQ]
        have h := hgood₁_det i 0 hi (by omega) hm_eq
        rw [h0k₁] at h; exact h
      · right
        have h1 : ((distinctKStepVectors (identifyPair w .L .s) k₁).erase
            (Necklace.kStepVector (identifyPair w .L .s) r₁ k₁)).card = 1 := by
          rw [Finset.card_erase_of_mem (hident₁_mem r₁)]; omega
        obtain ⟨u, hu⟩ := Finset.card_eq_one.mp h1
        have hvu := Finset.mem_singleton.mp
          (hu ▸ Finset.mem_erase.mpr ⟨heq_vQ, hident₁_mem (r₁ + i * k₁)⟩)
        have hRu := Finset.mem_singleton.mp
          (hu ▸ Finset.mem_erase.mpr ⟨hvQ₁R₁_ne.symm, hident₁_mem (r₁ + i₂ * k₁)⟩)
        have hm_eq : (Necklace.kStepVector w (r₁ + i * k₁) k₁) .m =
            (Necklace.kStepVector w (r₁ + i₂ * k₁) k₁) .m := by
          rw [← hident₁_m, ← hident₁_m, hvu.trans hRu.symm]
        exact hgood₁_det i i₂ hi hi₂_lt hm_eq
    -- Closing ≠ Q₁ and ≠ R₁ (because .L differs from good types)
    have hclose₁_ne_Q : Necklace.kStepVector w (r₁ + (n - 1) * k₁) k₁ ≠ Q₁ := by
      intro heq; apply hclose₁_L_ne; rw [heq]
      have := hgood₁_L 0 (by omega); rwa [h0k₁] at this
    have hclose₁_ne_R : Necklace.kStepVector w (r₁ + (n - 1) * k₁) k₁ ≠ R₁ := by
      intro heq; apply hclose₁_L_ne; rw [heq]; exact hgood₁_L i₂ hi₂_lt
    -- Phase D: check alternation at step k₁
    rcases Classical.em (∀ i : ℕ, i + 1 < n - 1 →
        Necklace.kStepVector w (r₁ + i * k₁) k₁ ≠
        Necklace.kStepVector w (r₁ + (i + 1) * k₁) k₁) with halt₁ | hnalt₁
    · -- Alternation: consecutive good vectors differ → Q₁R₁Q₁R₁... pattern
      have h_pattern₁ : ∀ i : ℕ, i < n - 1 →
          Necklace.kStepVector w (r₁ + i * k₁) k₁ =
          if i % 2 = 0 then Q₁ else R₁ := by
        intro i
        induction i with
        | zero => intro _; simp; rfl
        | succ j ih =>
          intro hj1
          have hprev := ih (by omega)
          have hne := halt₁ j (by omega)
          rw [hprev] at hne
          rcases Nat.mod_two_eq_zero_or_one j with hmod | hmod
          · rw [if_pos hmod] at hne
            have hmod1 : (j + 1) % 2 ≠ 0 := by omega
            rw [if_neg hmod1]
            exact (h_two_types₁ (j + 1) hj1).resolve_left (Ne.symm hne)
          · rw [if_neg (show j % 2 ≠ 0 from by omega)] at hne
            have hmod0 : (j + 1) % 2 = 0 := by omega
            rw [if_pos hmod0]
            exact (h_two_types₁ (j + 1) hj1).resolve_right (Ne.symm hne)
      exact ⟨k₁, r₁, fun j => if j.val = 0 then Q₁ else R₁, hk₁_lt, hk₁_cop,
        fun i => by rw [h_pattern₁ i.val i.isLt],
        fun j => by fin_cases j <;> simp <;> [exact hclose₁_ne_Q; exact hclose₁_ne_R]⟩
    · -- Non-alternation at both k₀ and k₁: try third bridge B₂
      -- Build B₂ = identifiedToBinary(identifyPair w .L .s) — the (L,s)-bridge
      set B₂ := identifiedToBinary (identifyPair w .L .s) with hB₂_def
      have hB₂mos : BinaryNecklace.isMOS B₂ := by
        constructor
        · exact ⟨⟨im, by simp [B₂, identifiedToBinary, identifyPair, him, msToBinary]⟩,
                 ⟨iL, by simp [B₂, identifiedToBinary, identifyPair, hiL, msToBinary]⟩⟩
        · intro k hk hk'
          rw [show B₂ = msToBinary ∘ identifyPair w .L .s from rfl,
              allKStepMultisets_comp' _ msToBinary k]
          calc ((Necklace.allKStepMultisets _ k).map (Multiset.map msToBinary)).toFinset.card
              ≤ (Necklace.allKStepMultisets _ k).toFinset.card := by
                rw [show ((Necklace.allKStepMultisets (identifyPair w .L .s) k).map
                    (Multiset.map msToBinary)).toFinset =
                    (Necklace.allKStepMultisets (identifyPair w .L .s) k).toFinset.image
                    (Multiset.map msToBinary) from by
                  ext; simp [List.mem_toFinset, Finset.mem_image, List.mem_map]]
                exact Finset.card_image_le
            _ ≤ 2 := hmosLs.2 k hk hk'
      have hB₂prim : Necklace.isPrimitive B₂ :=
        isPrimitive_comp_of_injective_on_range _ msToBinary hprimLs (by
          intro i j hij
          have hIi : identifyPair w .L .s i ≠ .L := by
            by_cases h : w i = .L <;> simp [identifyPair, h]
          have hIj : identifyPair w .L .s j ≠ .L := by
            by_cases h : w j = .L <;> simp [identifyPair, h]
          cases hvi : identifyPair w .L .s i <;> cases hvj : identifyPair w .L .s j <;>
            simp_all [msToBinary])
      -- Get generator k₂ with stacking structure from B₂
      obtain ⟨k₂, r₂, g₂, hk₂_pos, hk₂_lt, hk₂_cop, hgood₂_B, hclose₂_B⟩ :=
        primitive_mos_stacking B₂ hB₂mos hB₂prim hn_ge3
      -- Bridge: at good k₂-positions, w's .m = g₂.L (constant)
      have hgood₂_m : ∀ i : ℕ, i < n - 1 →
          (Necklace.kStepVector w (r₂ + i * k₂) k₂) .m = g₂ .L := by
        intro i hi
        have h := kStepVector_bridge_m_Ls w (r₂ + i * k₂) k₂
        rw [hgood₂_B i hi] at h; linarith
      -- Bridge: at good k₂-positions, w's .L + .s = g₂.s (constant)
      have hgood₂_Ls : ∀ i : ℕ, i < n - 1 →
          (Necklace.kStepVector w (r₂ + i * k₂) k₂) .L +
          (Necklace.kStepVector w (r₂ + i * k₂) k₂) .s = g₂ .s := by
        intro i hi
        have h := kStepVector_bridge_Ls_Ls w (r₂ + i * k₂) k₂
        rw [hgood₂_B i hi] at h; linarith
      -- Closing: w's .m ≠ g₂.L (since B₂'s closing vector ≠ g₂)
      have hclose₂_m_ne : (Necklace.kStepVector w (r₂ + (n - 1) * k₂) k₂) .m ≠ g₂ .L := by
        intro heq; apply hclose₂_B
        have hg₂_total : g₂ .L + g₂ .s = ↑k₂ := by
          have h := hgood₂_B 0 (by omega)
          rw [show r₂ + 0 * k₂ = r₂ from by omega] at h
          rw [← h]; exact_mod_cast kStepVector_total_count B₂ r₂ k₂
        have hj_total : (Necklace.kStepVector B₂ (r₂ + (n - 1) * k₂) k₂) .L +
            (Necklace.kStepVector B₂ (r₂ + (n - 1) * k₂) k₂) .s = ↑k₂ :=
          by exact_mod_cast kStepVector_total_count B₂ (r₂ + (n - 1) * k₂) k₂
        have hL_eq : (Necklace.kStepVector B₂ (r₂ + (n - 1) * k₂) k₂) .L = g₂ .L := by
          have h := kStepVector_bridge_m_Ls w (r₂ + (n - 1) * k₂) k₂; linarith
        have hs_eq : (Necklace.kStepVector B₂ (r₂ + (n - 1) * k₂) k₂) .s = g₂ .s := by
          linarith
        exact funext fun a => by cases a <;> [exact hL_eq; exact hs_eq]
      -- Good-position vectors determined by .L (since .m and .L+.s are constant)
      have hgood₂_det : ∀ i j : ℕ, i < n - 1 → j < n - 1 →
          (Necklace.kStepVector w (r₂ + i * k₂) k₂) .L =
          (Necklace.kStepVector w (r₂ + j * k₂) k₂) .L →
          Necklace.kStepVector w (r₂ + i * k₂) k₂ =
          Necklace.kStepVector w (r₂ + j * k₂) k₂ := by
        intro i j hi hj hL_eq
        funext a; cases a with
        | L => exact hL_eq
        | m => rw [hgood₂_m i hi, hgood₂_m j hj]
        | s => linarith [hgood₂_Ls i hi, hgood₂_Ls j hj]
      -- Case: all good vectors the same → degenerate hasAS
      rcases Classical.em (∀ i : ℕ, i < n - 1 →
          Necklace.kStepVector w (r₂ + i * k₂) k₂ = Necklace.kStepVector w r₂ k₂) with
          hall_eq₂ | hall_neq₂
      · have hQ₂_m : (Necklace.kStepVector w r₂ k₂) .m = g₂ .L := by
          have := hgood₂_m 0 (by omega); rwa [show r₂ + 0 * k₂ = r₂ from by omega] at this
        exact ⟨k₂, r₂, fun _ => Necklace.kStepVector w r₂ k₂, hk₂_lt, hk₂_cop,
          fun i => hall_eq₂ i.val i.isLt,
          fun _ heq => hclose₂_m_ne ((congr_fun heq .m).trans hQ₂_m)⟩
      · -- ≥ 2 distinct good-position vector types at step k₂
        push_neg at hall_neq₂
        obtain ⟨i₃, hi₃_lt, hi₃_ne⟩ := hall_neq₂
        set Q₂ := Necklace.kStepVector w r₂ k₂ with hQ₂_def
        set R₂ := Necklace.kStepVector w (r₂ + i₃ * k₂) k₂ with hR₂_def
        have h0k₂ : r₂ + 0 * k₂ = r₂ := by omega
        -- Q₂ and R₂ have different .L components
        have hQ₂R₂_L_ne : Q₂ .L ≠ R₂ .L := by
          intro heq; apply hi₃_ne
          have h := hgood₂_det i₃ 0 hi₃_lt (by omega) (by
            show (Necklace.kStepVector w (r₂ + i₃ * k₂) k₂) .L =
                (Necklace.kStepVector w (r₂ + 0 * k₂) k₂) .L
            rw [h0k₂]; exact heq.symm)
          rw [h0k₂] at h; exact h
        -- MOS of identifyPair w .m .s gives ≤ 2 distinct k₂-step vectors
        have hms_le2₂ : (distinctKStepVectors (identifyPair w .m .s) k₂).card ≤ 2 := by
          rw [distinctKStepVectors_card_eq]; exact hmosms.2 k₂ hk₂_pos hk₂_lt
        -- identifyPair .m .s preserves the .L component of k₂-step vectors
        have hident₂_L : ∀ j : ℕ,
            (Necklace.kStepVector (identifyPair w .m .s) j k₂) .L =
            (Necklace.kStepVector w j k₂) .L := by
          intro j; rw [identifyPair_kStepVector w .m .s (by decide) j k₂]
          simp [ZVector.identifyPair]
        -- Any position's identifyPair k₂-step vector is in distinctKStepVectors
        have hident₂_mem : ∀ j : ℕ,
            Necklace.kStepVector (identifyPair w .m .s) j k₂ ∈
            distinctKStepVectors (identifyPair w .m .s) k₂ := by
          intro j; unfold distinctKStepVectors Necklace.allKStepVectors
          rw [List.mem_toFinset, List.mem_map]
          exact ⟨j % n, List.mem_range.mpr (Nat.mod_lt _ hn_pos), kStepVector_mod_n _ _ _⟩
        -- identifyPair vectors at Q₂ and R₂ positions are distinct (different .L)
        have hvQ₂R₂_ne : Necklace.kStepVector (identifyPair w .m .s) r₂ k₂ ≠
            Necklace.kStepVector (identifyPair w .m .s) (r₂ + i₃ * k₂) k₂ := by
          intro heq; apply hQ₂R₂_L_ne
          change (Necklace.kStepVector w r₂ k₂) .L =
              (Necklace.kStepVector w (r₂ + i₃ * k₂) k₂) .L
          rw [← hident₂_L, ← hident₂_L, heq]
        -- Card = 2
        have hms_eq2₂ : (distinctKStepVectors (identifyPair w .m .s) k₂).card = 2 := by
          have hge := Finset.card_le_card (show
              {Necklace.kStepVector (identifyPair w .m .s) r₂ k₂,
               Necklace.kStepVector (identifyPair w .m .s) (r₂ + i₃ * k₂) k₂} ⊆
              distinctKStepVectors (identifyPair w .m .s) k₂ from
            Finset.insert_subset_iff.mpr
              ⟨hident₂_mem r₂, Finset.singleton_subset_iff.mpr (hident₂_mem (r₂ + i₃ * k₂))⟩)
          rw [Finset.card_pair hvQ₂R₂_ne] at hge; omega
        -- Every good k₂-position vector of w is Q₂ or R₂
        have h_two_types₂ : ∀ i : ℕ, i < n - 1 →
            Necklace.kStepVector w (r₂ + i * k₂) k₂ = Q₂ ∨
            Necklace.kStepVector w (r₂ + i * k₂) k₂ = R₂ := by
          intro i hi
          by_cases heq_vQ : Necklace.kStepVector (identifyPair w .m .s) (r₂ + i * k₂) k₂ =
              Necklace.kStepVector (identifyPair w .m .s) r₂ k₂
          · left
            have hL_eq : (Necklace.kStepVector w (r₂ + i * k₂) k₂) .L =
                (Necklace.kStepVector w (r₂ + 0 * k₂) k₂) .L := by
              rw [h0k₂]; rw [← hident₂_L, ← hident₂_L, heq_vQ]
            have h := hgood₂_det i 0 hi (by omega) hL_eq
            rw [h0k₂] at h; exact h
          · right
            have h1 : ((distinctKStepVectors (identifyPair w .m .s) k₂).erase
                (Necklace.kStepVector (identifyPair w .m .s) r₂ k₂)).card = 1 := by
              rw [Finset.card_erase_of_mem (hident₂_mem r₂)]; omega
            obtain ⟨u, hu⟩ := Finset.card_eq_one.mp h1
            have hvu := Finset.mem_singleton.mp
              (hu ▸ Finset.mem_erase.mpr ⟨heq_vQ, hident₂_mem (r₂ + i * k₂)⟩)
            have hRu := Finset.mem_singleton.mp
              (hu ▸ Finset.mem_erase.mpr ⟨hvQ₂R₂_ne.symm, hident₂_mem (r₂ + i₃ * k₂)⟩)
            have hL_eq : (Necklace.kStepVector w (r₂ + i * k₂) k₂) .L =
                (Necklace.kStepVector w (r₂ + i₃ * k₂) k₂) .L := by
              rw [← hident₂_L, ← hident₂_L, hvu.trans hRu.symm]
            exact hgood₂_det i i₃ hi hi₃_lt hL_eq
        -- Closing ≠ Q₂ and ≠ R₂
        have hclose₂_ne_Q : Necklace.kStepVector w (r₂ + (n - 1) * k₂) k₂ ≠ Q₂ := by
          intro heq; apply hclose₂_m_ne; rw [heq]
          have := hgood₂_m 0 (by omega); rwa [h0k₂] at this
        have hclose₂_ne_R : Necklace.kStepVector w (r₂ + (n - 1) * k₂) k₂ ≠ R₂ := by
          intro heq; apply hclose₂_m_ne; rw [heq]; exact hgood₂_m i₃ hi₃_lt
        -- Check alternation at step k₂
        rcases Classical.em (∀ i : ℕ, i + 1 < n - 1 →
            Necklace.kStepVector w (r₂ + i * k₂) k₂ ≠
            Necklace.kStepVector w (r₂ + (i + 1) * k₂) k₂) with halt₂ | hnalt₂
        · -- Alternation → hasAS
          have h_pattern₂ : ∀ i : ℕ, i < n - 1 →
              Necklace.kStepVector w (r₂ + i * k₂) k₂ =
              if i % 2 = 0 then Q₂ else R₂ := by
            intro i
            induction i with
            | zero => intro _; simp; rfl
            | succ j ih =>
              intro hj1
              have hprev := ih (by omega)
              have hne := halt₂ j (by omega)
              rw [hprev] at hne
              rcases Nat.mod_two_eq_zero_or_one j with hmod | hmod
              · rw [if_pos hmod] at hne
                have hmod1 : (j + 1) % 2 ≠ 0 := by omega
                rw [if_neg hmod1]
                exact (h_two_types₂ (j + 1) hj1).resolve_left (Ne.symm hne)
              · rw [if_neg (show j % 2 ≠ 0 from by omega)] at hne
                have hmod0 : (j + 1) % 2 = 0 := by omega
                rw [if_pos hmod0]
                exact (h_two_types₂ (j + 1) hj1).resolve_right (Ne.symm hne)
          exact ⟨k₂, r₂, fun j => if j.val = 0 then Q₂ else R₂, hk₂_lt, hk₂_cop,
            fun i => by rw [h_pattern₂ i.val i.isLt],
            fun j => by fin_cases j <;> simp <;> [exact hclose₂_ne_Q; exact hclose₂_ne_R]⟩
        · -- Non-alternation at all three bridges: forces n=7 sporadic balanced
          exfalso
          -- Reconstruct full hypotheses from destructured components
          have hpwf' : isPairwisePrimMOS w :=
            ⟨⟨hmosLm, hprimLm⟩, ⟨hmosms, hprimms⟩, ⟨hmosLs, hprimLs⟩⟩
          have hprim' := isPrimitive_of_isPairwisePrimMOS w hpwf'
          have htern' : isTernary w := ⟨⟨iL, hiL⟩, ⟨im, him⟩, ⟨is, his⟩⟩
          have hbal := pairwiseMOS_implies_isBalanced w hprim' htern'
            ⟨hmosLm, hmosms, hmosLs⟩
          -- All three bridges non-alternating + balanced + primitive + ternary
          -- forces n=7 sporadic balanced, contradicting hns.
          -- Case split on step count equality
          exact hns (balanced_all_distinct_isSporadicBalanced w hbal hprim'
                  htern' hneq_Lm hneq_ms hneq_Ls)

set_option maxHeartbeats 400000
/-- PWF ternary scales (odd, not sporadic balanced) have an alternating sequence.
    Proof outline from the case analysis on μ (the minority count in Λ₂):
    • Case 1 (μ = 2): has AS((f−1)Q + R, (f-1)Q + T) with 1 bad interval fQ.
    • Case 2 (μ ≥ ⌈n/2⌉): Σ = QRQR…QRT, has AS(Q, R).
    • Case 3 (3 ≤ μ ≤ ⌊n/2⌋): All subcases either are impossible or give n=7 + abacaba
      (= sporadic balanced, which is excluded by hypothesis). -/
private lemma pwf_hasAS (w : TernaryNecklace n)
    (htern : isTernary w) (hpwf : isPairwisePrimMOS w)
    (hodd : n % 2 = 1) (hns : ¬ isSporadicBalanced w) :
    hasAS w := by
  have hprim := isPrimitive_of_isPairwisePrimMOS w hpwf
  -- Handle equal-count cases directly via balanced + bridge alternation
  have hbal_early := pairwiseMOS_implies_isBalanced w hprim
    (by exact htern) ⟨hpwf.1.1, hpwf.2.1.1, hpwf.2.2.1⟩
  by_cases heq_Lm : Necklace.count w .L = Necklace.count w .m
  · exact balanced_two_equal_hasAS_Lm w hbal_early htern hpwf hodd heq_Lm
  by_cases heq_ms : Necklace.count w .m = Necklace.count w .s
  · exact balanced_two_equal_hasAS w hbal_early htern hpwf hodd .m .s .L
      (by decide) (by decide) (by decide) heq_ms
  by_cases heq_Ls : Necklace.count w .L = Necklace.count w .s
  · exact balanced_two_equal_hasAS w hbal_early htern hpwf hodd .L .s .m
      (by decide) (by decide) (by decide) heq_Ls
  -- All counts pairwise distinct: proceed with existing bridge analysis
  obtain ⟨⟨hmosLm, hprimLm⟩, ⟨hmosms, hprimms⟩, ⟨hmosLs, hprimLs⟩⟩ := hpwf
  obtain ⟨⟨iL, hiL⟩, ⟨im, him⟩, ⟨is, his⟩⟩ := htern
  -- Step 1: Binary bridge for (L,m) identification
  set B := identifiedToBinary (identifyPair w .L .m) with hB_def
  have hBmos : BinaryNecklace.isMOS B := by
    constructor
    · exact ⟨⟨iL, by simp [B, identifiedToBinary, identifyPair, hiL, msToBinary]⟩,
             ⟨is, by simp [B, identifiedToBinary, identifyPair, his, msToBinary]⟩⟩
    · intro k hk hk'
      rw [show B = msToBinary ∘ identifyPair w .L .m from rfl,
          allKStepMultisets_comp' _ msToBinary k]
      calc ((Necklace.allKStepMultisets _ k).map (Multiset.map msToBinary)).toFinset.card
          ≤ (Necklace.allKStepMultisets _ k).toFinset.card := by
            rw [show ((Necklace.allKStepMultisets (identifyPair w .L .m) k).map
                (Multiset.map msToBinary)).toFinset =
                (Necklace.allKStepMultisets (identifyPair w .L .m) k).toFinset.image
                (Multiset.map msToBinary) from by
              ext; simp [List.mem_toFinset, Finset.mem_image, List.mem_map]]
            exact Finset.card_image_le
        _ ≤ 2 := hmosLm.2 k hk hk'
  have hBprim : Necklace.isPrimitive B :=
    isPrimitive_comp_of_injective_on_range _ msToBinary hprimLm (by
      intro i j hij
      have hIi : identifyPair w .L .m i ≠ .L := by
        by_cases h : w i = .L <;> simp [identifyPair, h]
      have hIj : identifyPair w .L .m j ≠ .L := by
        by_cases h : w j = .L <;> simp [identifyPair, h]
      cases hvi : identifyPair w .L .m i <;> cases hvj : identifyPair w .L .m j <;>
        simp_all [msToBinary])
  -- Step 2: B has a generator
  obtain ⟨g, hgen⟩ := allMOSScalesHaveGenerator n B hBmos
  have hBbin : BinaryNecklace.isBinary B := hBmos.1
  -- Step 3: Extract generator step k₀ with count = n-1, then derive coprimality
  obtain ⟨k₀, hk₀_pos, hk₀_lt, hk₀_count⟩ :=
    generator_implies_p_minus_one_occurrences B hBbin g hgen
  have hk₀_cop : Nat.Coprime k₀ n := by
    have := p_minus_one_occurrences_implies_coprime_to_period B hBbin k₀ hk₀_pos hk₀_lt g hk₀_count
    rwa [hBprim] at this
  rw [hBprim] at hk₀_lt hk₀_count
  -- n ≥ 3 from ternarity (three distinct positions for L, m, s)
  have hn_ge3 : n ≥ 3 := by
    have hiLm : iL ≠ im := by
      intro h; have := hiL.symm.trans (h ▸ him); exact absurd this (by decide)
    have hiLs : iL ≠ is := by
      intro h; have := hiL.symm.trans (h ▸ his); exact absurd this (by decide)
    have hims : im ≠ is := by
      intro h; have := him.symm.trans (h ▸ his); exact absurd this (by decide)
    have h3 : ({iL, im, is} : Finset (ZMod n)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hiLm, hiLs]),
          Finset.card_insert_of_notMem (by simp [hims]),
          Finset.card_singleton]
    have := Finset.card_le_card (Finset.subset_univ ({iL, im, is} : Finset (ZMod n)))
    rw [h3, Finset.card_univ, ZMod.card] at this; exact this
  -- Step 4: B has exactly 2 distinct k₀-step vectors with counts (n-1, 1).
  -- From MOS property, distinctKStepVectors ≤ 2. From count(g) = n-1 < n, card ≥ 2.
  have hvec_le_2 : (distinctKStepVectors B k₀).card ≤ 2 :=
    mos_at_most_two_varieties B hBmos k₀ hk₀_pos (by rw [hBprim]; exact hk₀_lt)
  -- g is in distinctKStepVectors (count > 0)
  have hg_mem : g ∈ distinctKStepVectors B k₀ := by
    unfold distinctKStepVectors Necklace.allKStepVectors
    rw [List.mem_toFinset]
    by_contra h_not_mem
    have h_count_zero : countKStepVectorPerPeriod B k₀ g = 0 := by
      unfold countKStepVectorPerPeriod; rw [hBprim]
      rw [List.countP_eq_zero]; intro i hi
      simp only [decide_eq_true_eq]
      intro heq; exact h_not_mem (List.mem_map.mpr ⟨i, hi, heq⟩)
    omega
  -- There exists g' ≠ g (otherwise count(g) = n, not n-1)
  have hvec_ge_2 : (distinctKStepVectors B k₀).card ≥ 2 := by
    by_contra h_lt; push_neg at h_lt
    have hcard_1 : (distinctKStepVectors B k₀).card = 1 := by
      have := Finset.card_pos.mpr ⟨g, hg_mem⟩; omega
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard_1
    have hsum := counts_sum_to_period B k₀
    rw [hBprim, hv] at hsum
    have hgv : g = v := Finset.mem_singleton.mp (hv ▸ hg_mem)
    rw [← hgv, Finset.sum_singleton] at hsum; omega
  have hvec_eq_2 : (distinctKStepVectors B k₀).card = 2 := by omega
  -- Extract g' ≠ g from the set of card 2
  have herase_card : ((distinctKStepVectors B k₀).erase g).card = 1 := by
    rw [Finset.card_erase_of_mem hg_mem]; omega
  obtain ⟨g', hg'_mem_erase⟩ :=
    Finset.card_pos.mp (by omega : 0 < ((distinctKStepVectors B k₀).erase g).card)
  have hg'_mem : g' ∈ distinctKStepVectors B k₀ := Finset.mem_of_mem_erase hg'_mem_erase
  have hg'_ne : g' ≠ g := Finset.ne_of_mem_erase hg'_mem_erase
  -- count(g') = 1 by two_varieties_counts_sum
  have hcounts_sum := two_varieties_counts_sum B k₀ g g' hg_mem hg'_mem hg'_ne.symm hvec_eq_2
  rw [hBprim] at hcounts_sum
  have hg'_count : countKStepVectorPerPeriod B k₀ g' = 1 := by omega
  -- Step 5: The k₀-step vectors of w project to those of B.
  -- At position j, the s-count of w's k₀-step vector = s-count of B's k₀-step vector.
  have h_bridge_s : ∀ j : ℕ, (Necklace.kStepVector B j k₀) .s =
      (Necklace.kStepVector w j k₀) .s := fun j => kStepVector_bridge_s w j k₀
  -- Step 6: g .s ≠ g' .s (binary vectors with same total and same s-count must be equal)
  have hg_total : g .L + g .s = ↑k₀ := by
    have h := hg_mem; unfold distinctKStepVectors Necklace.allKStepVectors at h
    rw [List.mem_toFinset] at h
    obtain ⟨j, _, hj_eq⟩ := List.mem_map.mp h
    rw [← hj_eq]; exact_mod_cast kStepVector_total_count B j k₀
  have hg'_total : g' .L + g' .s = ↑k₀ := by
    have h := hg'_mem; unfold distinctKStepVectors Necklace.allKStepVectors at h
    rw [List.mem_toFinset] at h
    obtain ⟨j, _, hj_eq⟩ := List.mem_map.mp h
    rw [← hj_eq]; exact_mod_cast kStepVector_total_count B j k₀
  have hgs_ne : g .s ≠ g' .s := by
    intro heq
    have hL_eq : g .L = g' .L := by linarith
    exact hg'_ne (funext fun a => by cases a <;> [exact hL_eq.symm; exact heq.symm])
  -- Step 7: Extract the unique bad position i₀ (where B has g' instead of g)
  have hn_pos : 0 < n := by omega
  have hbad : ∃ i₀ : ℕ, i₀ < n ∧ Necklace.kStepVector B i₀ k₀ ≠ g ∧
      (∀ j : ℕ, j < n → j ≠ i₀ → Necklace.kStepVector B j k₀ = g) := by
    unfold countKStepVectorPerPeriod at hk₀_count
    rw [show (Necklace.period B).length = n from hBprim] at hk₀_count
    have hexists_bad : ∃ i₀, i₀ < n ∧ Necklace.kStepVector B i₀ k₀ ≠ g := by
      by_contra hall; push_neg at hall
      have h := List.countP_eq_length.mpr (fun i hi => by
        exact decide_eq_true_eq.mpr (hall i (List.mem_range.mp hi)))
      rw [List.length_range] at h; rw [h] at hk₀_count; omega
    obtain ⟨i₀, hi₀_lt, hi₀_bad⟩ := hexists_bad
    refine ⟨i₀, hi₀_lt, hi₀_bad, fun j hj hne => ?_⟩
    by_contra hj_bad
    set p := fun i => decide (Necklace.kStepVector B i k₀ = g)
    have hcg : (List.range n).countP p = n - 1 := hk₀_count
    have hp_i₀ : p i₀ = false := by simp [p, hi₀_bad]
    have hp_j : p j = false := by simp [p, hj_bad]
    have hi₀_mem : i₀ ∈ List.range n := List.mem_range.mpr hi₀_lt
    have hj_mem : j ∈ List.range n := List.mem_range.mpr hj
    have h1 : ((List.range n).erase j).countP p = (List.range n).countP p := by
      rw [List.countP_erase]; simp [hj_mem, hp_j]
    have h2 : ((List.range n).erase j).length = n - 1 := by
      rw [List.length_erase_of_mem hj_mem, List.length_range]
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
  -- Step 8: Set r and establish good/closing stacking positions
  set r := (i₀ + k₀) % n with hr_def
  have hk₀_unit : IsUnit (↑k₀ : ZMod n) := coprime_isUnit_zmod k₀ hk₀_cop (by omega)
  -- Good stacking indices avoid the bad position i₀
  have hgood_pos : ∀ i : ℕ, i < n - 1 → (r + i * k₀) % n ≠ i₀ := by
    intro i hi heq
    suffices h_dvd : n ∣ (i + 1) by
      exact absurd (Nat.le_of_dvd (by omega) h_dvd) (by omega)
    suffices h_mod : (i + 1) % n = 0 from Nat.dvd_of_mod_eq_zero h_mod
    have h1 : (↑(r + i * k₀) : ZMod n) = (↑i₀ : ZMod n) := by
      rw [← ZMod.natCast_zmod_val (↑(r + i * k₀) : ZMod n),
          ← ZMod.natCast_zmod_val (↑i₀ : ZMod n)]
      congr 1; simp only [ZMod.val_natCast]
      rwa [Nat.mod_eq_of_lt hi₀_lt]
    have h2 : (↑k₀ : ZMod n) * (1 + ↑i) = 0 := by
      have h_eq : (↑r : ZMod n) + ↑i * ↑k₀ = ↑i₀ := by push_cast at h1; exact h1
      have hr_eq : (↑r : ZMod n) = ↑i₀ + ↑k₀ := by
        suffices h : (↑r : ZMod n) = (↑(i₀ + k₀) : ZMod n) by rw [h]; push_cast; ring
        rw [← ZMod.natCast_zmod_val (↑r : ZMod n),
            ← ZMod.natCast_zmod_val (↑(i₀ + k₀) : ZMod n)]
        congr 1; simp only [ZMod.val_natCast]
        rw [hr_def]; exact Nat.mod_eq_of_lt (Nat.mod_lt _ hn_pos)
      rw [hr_eq] at h_eq; linear_combination h_eq
    have h3 : (1 : ZMod n) + ↑i = 0 :=
      hk₀_unit.mul_left_cancel (h2.trans (mul_zero _).symm)
    have h4 : (↑(i + 1) : ZMod n) = 0 := by push_cast; linear_combination h3
    have := congr_arg ZMod.val h4
    simp only [ZMod.val_natCast, ZMod.val_zero] at this; exact this
  -- Closing stacking index hits the bad position i₀
  have hclose_pos : (r + (n - 1) * k₀) % n = i₀ := by
    have h1 : r + (n - 1) * k₀ ≡ i₀ + k₀ + (n - 1) * k₀ [MOD n] :=
      Nat.ModEq.add_right _ (Nat.mod_modEq (i₀ + k₀) n)
    have h2 : i₀ + k₀ + (n - 1) * k₀ = i₀ + n * k₀ := by
      have : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn_pos; nlinarith
    rw [Nat.ModEq, h2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi₀_lt] at h1; exact h1
  -- At good stacking positions, B has generator g
  have hgood_B : ∀ i : ℕ, i < n - 1 → Necklace.kStepVector B (r + i * k₀) k₀ = g := by
    intro i hi; rw [← kStepVector_mod_n]
    exact hi₀_good _ (Nat.mod_lt _ hn_pos) (hgood_pos i hi)
  -- At closing position, B has the imperfect vector (≠ g)
  have hclose_B : Necklace.kStepVector B (r + (n - 1) * k₀) k₀ ≠ g := by
    rw [← kStepVector_mod_n, hclose_pos]; exact hi₀_bad
  -- Good positions: w's s-count = g .s (from bridge)
  have hgood_s : ∀ i : ℕ, i < n - 1 →
      (Necklace.kStepVector w (r + i * k₀) k₀) .s = g .s := by
    intro i hi; rw [← h_bridge_s, hgood_B i hi]
  -- Closing position: w's s-count ≠ g .s (bridge + binary total count argument)
  have hclose_s_ne : (Necklace.kStepVector w (r + (n - 1) * k₀) k₀) .s ≠ g .s := by
    intro heq; apply hclose_B
    have hj_total : (Necklace.kStepVector B (r + (n - 1) * k₀) k₀) .L +
        (Necklace.kStepVector B (r + (n - 1) * k₀) k₀) .s = ↑k₀ :=
      by exact_mod_cast kStepVector_total_count B (r + (n - 1) * k₀) k₀
    have hs_eq : (Necklace.kStepVector B (r + (n - 1) * k₀) k₀) .s = g .s := by
      rw [h_bridge_s]; exact heq
    have hL_eq : (Necklace.kStepVector B (r + (n - 1) * k₀) k₀) .L = g .L := by linarith
    exact funext fun a => by cases a <;> [exact hL_eq; exact hs_eq]
  -- Phase D: Case analysis on the stacking structure to construct hasAS.
  -- Case split: either all good-position vectors are the same, or there are ≥ 2 types.
  rcases Classical.em (∀ i : ℕ, i < n - 1 →
      Necklace.kStepVector w (r + i * k₀) k₀ = Necklace.kStepVector w r k₀) with hall_eq | hall_neq
  · -- All good vectors are the same → degenerate AS with seq 0 = seq 1
    have hQ_s : (Necklace.kStepVector w r k₀) .s = g .s := by
      have := hgood_s 0 (by omega); rwa [show r + 0 * k₀ = r from by omega] at this
    exact ⟨k₀, r, fun _ => Necklace.kStepVector w r k₀, hk₀_lt, hk₀_cop,
      fun i => hall_eq i.val i.isLt,
      fun _ heq => hclose_s_ne ((congr_fun heq .s).trans hQ_s)⟩
  · -- At least 2 distinct good-position vector types → nontrivial alternation
    push_neg at hall_neq
    obtain ⟨i₁, hi₁_lt, hi₁_ne⟩ := hall_neq
    -- At good positions, .L + .m = g .L (constant, from bridge_L)
    have hgood_Lm : ∀ i : ℕ, i < n - 1 →
        (Necklace.kStepVector w (r + i * k₀) k₀) .L +
        (Necklace.kStepVector w (r + i * k₀) k₀) .m = g .L := by
      intro i hi
      have := kStepVector_bridge_L w (r + i * k₀) k₀
      rw [hgood_B i hi] at this; linarith
    -- Good-position vectors are determined by their .L component
    have hgood_det : ∀ i j : ℕ, i < n - 1 → j < n - 1 →
        (Necklace.kStepVector w (r + i * k₀) k₀) .L =
        (Necklace.kStepVector w (r + j * k₀) k₀) .L →
        Necklace.kStepVector w (r + i * k₀) k₀ =
        Necklace.kStepVector w (r + j * k₀) k₀ := by
      intro i j hi hj hL_eq
      funext a; cases a with
      | L => exact hL_eq
      | m => linarith [hgood_Lm i hi, hgood_Lm j hj]
      | s => rw [hgood_s i hi, hgood_s j hj]
    -- Phase D: Establish ≤ 2 good-position vector types and construct hasAS.
    -- Name the two known good-position vector types
    set Q := Necklace.kStepVector w r k₀ with hQ_def
    set R := Necklace.kStepVector w (r + i₁ * k₀) k₀ with hR_def
    -- Helper: r + 0 * k₀ = r (used repeatedly to convert hgood_det index 0)
    have h0k : r + 0 * k₀ = r := by omega
    -- Q and R have different .L components (otherwise hgood_det would give Q = R)
    have hQR_L_ne : Q .L ≠ R .L := by
      intro heq; apply hi₁_ne
      have h := hgood_det i₁ 0 hi₁_lt (by omega) (by
        show (Necklace.kStepVector w (r + i₁ * k₀) k₀) .L =
            (Necklace.kStepVector w (r + 0 * k₀) k₀) .L
        rw [h0k]; exact heq.symm)
      rw [h0k] at h; exact h
    -- MOS of identifyPair w .m .s gives ≤ 2 distinct k₀-step vectors
    have hms_le2 : (distinctKStepVectors (identifyPair w .m .s) k₀).card ≤ 2 := by
      rw [distinctKStepVectors_card_eq]; exact hmosms.2 k₀ hk₀_pos hk₀_lt
    -- Any position's identifyPair k₀-step vector is in distinctKStepVectors
    have hident_mem : ∀ j : ℕ,
        Necklace.kStepVector (identifyPair w .m .s) j k₀ ∈
        distinctKStepVectors (identifyPair w .m .s) k₀ := by
      intro j; unfold distinctKStepVectors Necklace.allKStepVectors
      rw [List.mem_toFinset, List.mem_map]
      exact ⟨j % n, List.mem_range.mpr (Nat.mod_lt _ hn_pos), kStepVector_mod_n _ _ _⟩
    -- identifyPair .m .s preserves the .L component of k₀-step vectors
    have hident_L : ∀ j : ℕ,
        (Necklace.kStepVector (identifyPair w .m .s) j k₀) .L =
        (Necklace.kStepVector w j k₀) .L := by
      intro j; rw [identifyPair_kStepVector w .m .s (by decide) j k₀]
      simp [ZVector.identifyPair]
    -- identifyPair vectors at Q and R positions are distinct (different .L components)
    have hvQR_ne : Necklace.kStepVector (identifyPair w .m .s) r k₀ ≠
        Necklace.kStepVector (identifyPair w .m .s) (r + i₁ * k₀) k₀ := by
      intro heq; apply hQR_L_ne
      -- Expand Q, R abbreviations so rw can find the kStepVector pattern
      change (Necklace.kStepVector w r k₀) .L = (Necklace.kStepVector w (r + i₁ * k₀) k₀) .L
      rw [← hident_L, ← hident_L, heq]
    -- Card = 2 (two distinct elements in a set of size ≤ 2)
    have hms_eq2 : (distinctKStepVectors (identifyPair w .m .s) k₀).card = 2 := by
      have hge := Finset.card_le_card (show
          {Necklace.kStepVector (identifyPair w .m .s) r k₀,
           Necklace.kStepVector (identifyPair w .m .s) (r + i₁ * k₀) k₀} ⊆
          distinctKStepVectors (identifyPair w .m .s) k₀ from
        Finset.insert_subset_iff.mpr
          ⟨hident_mem r, Finset.singleton_subset_iff.mpr (hident_mem (r + i₁ * k₀))⟩)
      rw [Finset.card_pair hvQR_ne] at hge; omega
    -- Every good-position k₀-step vector of w is Q or R
    have h_two_types : ∀ i : ℕ, i < n - 1 →
        Necklace.kStepVector w (r + i * k₀) k₀ = Q ∨
        Necklace.kStepVector w (r + i * k₀) k₀ = R := by
      intro i hi
      have hv_mem := hident_mem (r + i * k₀)
      by_cases heq_vQ : Necklace.kStepVector (identifyPair w .m .s) (r + i * k₀) k₀ =
          Necklace.kStepVector (identifyPair w .m .s) r k₀
      · -- identifyPair vector matches Q's → .L matches → full vector matches Q
        left
        have hL_eq : (Necklace.kStepVector w (r + i * k₀) k₀) .L =
            (Necklace.kStepVector w (r + 0 * k₀) k₀) .L := by
          rw [h0k]; rw [← hident_L, ← hident_L, heq_vQ]
        have h := hgood_det i 0 hi (by omega) hL_eq
        rw [h0k] at h; exact h
      · -- identifyPair vector differs from Q's → must be R's
        right
        have h1 : ((distinctKStepVectors (identifyPair w .m .s) k₀).erase
            (Necklace.kStepVector (identifyPair w .m .s) r k₀)).card = 1 := by
          rw [Finset.card_erase_of_mem (hident_mem r)]; omega
        obtain ⟨u, hu⟩ := Finset.card_eq_one.mp h1
        have hvu := Finset.mem_singleton.mp
          (hu ▸ Finset.mem_erase.mpr ⟨heq_vQ, hv_mem⟩)
        have hRu := Finset.mem_singleton.mp
          (hu ▸ Finset.mem_erase.mpr ⟨hvQR_ne.symm, hident_mem (r + i₁ * k₀)⟩)
        have hL_eq : (Necklace.kStepVector w (r + i * k₀) k₀) .L =
            (Necklace.kStepVector w (r + i₁ * k₀) k₀) .L := by
          rw [← hident_L, ← hident_L, hvu.trans hRu.symm]
        exact hgood_det i i₁ hi hi₁_lt hL_eq
    -- Closing position differs from both Q and R (s-component mismatch)
    have hclose_ne_Q : Necklace.kStepVector w (r + (n - 1) * k₀) k₀ ≠ Q := by
      intro heq; apply hclose_s_ne; rw [heq]
      have := hgood_s 0 (by omega); rwa [h0k] at this
    have hclose_ne_R : Necklace.kStepVector w (r + (n - 1) * k₀) k₀ ≠ R := by
      intro heq; apply hclose_s_ne; rw [heq]; exact hgood_s i₁ hi₁_lt
    -- Case D2: if consecutive good vectors always differ → alternation → hasAS
    rcases Classical.em (∀ i : ℕ, i + 1 < n - 1 →
        Necklace.kStepVector w (r + i * k₀) k₀ ≠
        Necklace.kStepVector w (r + (i + 1) * k₀) k₀) with halt | hnalt
    · -- Alternation: consecutive good vectors differ → QRQR... pattern
      have h_pattern : ∀ i : ℕ, i < n - 1 →
          Necklace.kStepVector w (r + i * k₀) k₀ =
          if i % 2 = 0 then Q else R := by
        intro i
        induction i with
        | zero => intro _; simp; rfl
        | succ j ih =>
          intro hj1
          have hprev := ih (by omega)
          have hne := halt j (by omega)
          rw [hprev] at hne
          rcases Nat.mod_two_eq_zero_or_one j with hmod | hmod
          · -- j even → pos j = Q → pos j+1 ≠ Q → pos j+1 = R
            rw [if_pos hmod] at hne
            have hmod1 : (j + 1) % 2 ≠ 0 := by omega
            rw [if_neg hmod1]
            exact (h_two_types (j + 1) hj1).resolve_left (Ne.symm hne)
          · -- j odd → pos j = R → pos j+1 ≠ R → pos j+1 = Q
            rw [if_neg (show j % 2 ≠ 0 from by omega)] at hne
            have hmod0 : (j + 1) % 2 = 0 := by omega
            rw [if_pos hmod0]
            exact (h_two_types (j + 1) hj1).resolve_right (Ne.symm hne)
      -- Construct hasAS with step k₀ and alternating sequence Q, R
      exact ⟨k₀, r, fun j => if j.val = 0 then Q else R, hk₀_lt, hk₀_cop,
        fun i => by rw [h_pattern i.val i.isLt],
        fun j => by fin_cases j <;> simp <;> [exact hclose_ne_Q; exact hclose_ne_R]⟩
    · -- Non-alternation: some consecutive good-position pair has the same vector.
      push_neg at hnalt
      obtain ⟨j₀, hj₀_lt, hj₀_eq⟩ := hnalt
      have hQR_ne : Q ≠ R := fun h => hQR_L_ne (congr_fun h .L)
      -- A mixed (different-type) consecutive good pair must exist,
      -- since V(0) = Q and V(i₁) = R require a QR or RQ transition.
      have hmixed_exists : ∃ j₁ : ℕ, j₁ + 1 < n - 1 ∧
          Necklace.kStepVector w (r + j₁ * k₀) k₀ ≠
          Necklace.kStepVector w (r + (j₁ + 1) * k₀) k₀ := by
        by_contra hall; push_neg at hall
        have : ∀ i, i < n - 1 →
            Necklace.kStepVector w (r + i * k₀) k₀ = Q := by
          intro i hi; induction i with
          | zero => rw [h0k]
          | succ j ih => rw [← hall j (by omega)]; exact ih (by omega)
        exact hi₁_ne (this i₁ hi₁_lt)
      obtain ⟨j₁, hj₁_lt, hj₁_ne⟩ := hmixed_exists
      -- 2k₀ coprimality (n odd + gcd(k₀,n)=1 → gcd(2k₀,n)=1)
      have hcop_2k : Nat.Coprime (2 * k₀) n := by
        have : Nat.Coprime 2 n := by rw [Nat.coprime_two_left]; rwa [Nat.odd_iff]
        exact this.mul_left hk₀_cop
      -- 2k₀-step MOS: ≤ 2 distinct 2k₀-step identified vectors
      have hms_2k_le2 :
          (distinctKStepVectors (identifyPair w .m .s) (2 * k₀)).card ≤ 2 := by
        have hk₂_pos : 0 < (2 * k₀) % n := by
          rw [Nat.pos_iff_ne_zero]; intro h0
          have : n ∣ Nat.gcd (2 * k₀) n :=
            Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h0) dvd_rfl
          rw [hcop_2k] at this; exact absurd (Nat.le_of_dvd one_pos this) (by omega)
        have : (distinctKStepVectors (identifyPair w .m .s) (2 * k₀)).card =
            (distinctKStepVectors (identifyPair w .m .s) ((2 * k₀) % n)).card := by
          unfold distinctKStepVectors; exact kStepVectors_card_mod_n _ _
        rw [this, distinctKStepVectors_card_eq]
        exact hmosms.2 _ hk₂_pos (Nat.mod_lt _ hn_pos)
      -- 2k₀ .L decomposition: identified 2k₀ .L at stacking position j =
      -- original k₀ .L at j + original k₀ .L at j+1
      have h2k_L : ∀ j,
          (Necklace.kStepVector (identifyPair w .m .s) (r + j * k₀) (2 * k₀)) .L =
          (Necklace.kStepVector w (r + j * k₀) k₀) .L +
          (Necklace.kStepVector w (r + (j + 1) * k₀) k₀) .L := by
        intro j
        have := kStepVector_add (identifyPair w .m .s) (r + j * k₀) k₀ k₀ .L
        rw [show k₀ + k₀ = 2 * k₀ from by ring,
            show r + j * k₀ + k₀ = r + (j + 1) * k₀ from by ring] at this
        rw [this, hident_L, hident_L]
      -- All 2k₀ identified vectors are in the distinct set
      have hmem_2k : ∀ j,
          Necklace.kStepVector (identifyPair w .m .s) j (2 * k₀) ∈
          distinctKStepVectors (identifyPair w .m .s) (2 * k₀) := by
        intro j; unfold distinctKStepVectors Necklace.allKStepVectors
        rw [List.mem_toFinset, List.mem_map]
        exact ⟨j % n, List.mem_range.mpr (Nat.mod_lt _ hn_pos), kStepVector_mod_n _ _ _⟩
      -- Mixed pair .L value = Q.L + R.L (regardless of QR vs RQ order)
      have hMix_L :
          (Necklace.kStepVector (identifyPair w .m .s) (r + j₁ * k₀) (2 * k₀)) .L =
          Q .L + R .L := by
        rw [h2k_L]
        rcases h_two_types j₁ (by omega) with hj₁Q | hj₁R
        · rw [hj₁Q, (h_two_types (j₁ + 1) (by omega)).resolve_left
            (fun h => hj₁_ne (hj₁Q.trans h.symm))]
        · rw [hj₁R, (h_two_types (j₁ + 1) (by omega)).resolve_right
            (fun h => hj₁_ne (hj₁R.trans h.symm)), add_comm]
      -- QQ and RR can't coexist: would give 3 distinct .L values for 2k₀ vectors
      -- {2*Q.L, Q.L+R.L, 2*R.L} but ≤ 2 types. So: no QQ ∨ no RR.
      have hdichotomy :
          (∀ i, i + 1 < n - 1 →
            ¬ (Necklace.kStepVector w (r + i * k₀) k₀ = Q ∧
               Necklace.kStepVector w (r + (i + 1) * k₀) k₀ = Q)) ∨
          (∀ i, i + 1 < n - 1 →
            ¬ (Necklace.kStepVector w (r + i * k₀) k₀ = R ∧
               Necklace.kStepVector w (r + (i + 1) * k₀) k₀ = R)) := by
        by_contra h; push_neg at h
        obtain ⟨⟨i₂, hi₂, hiQ, hi1Q⟩, ⟨i₃, hi₃, hiR, hi1R⟩⟩ := h
        -- QQ .L at i₂ = 2*Q.L, RR .L at i₃ = 2*R.L
        have hQQ_L := h2k_L i₂; rw [hiQ, hi1Q] at hQQ_L
        have hRR_L := h2k_L i₃; rw [hiR, hi1R] at hRR_L
        -- Three pairwise distinct 2k₀ vectors (different .L values)
        have hd12 : Necklace.kStepVector (identifyPair w .m .s) (r + i₂ * k₀) (2 * k₀) ≠
            Necklace.kStepVector (identifyPair w .m .s) (r + j₁ * k₀) (2 * k₀) := by
          intro h; apply hQR_L_ne
          have := congr_fun h .L; rw [hQQ_L, hMix_L] at this; linarith
        have hd13 : Necklace.kStepVector (identifyPair w .m .s) (r + i₂ * k₀) (2 * k₀) ≠
            Necklace.kStepVector (identifyPair w .m .s) (r + i₃ * k₀) (2 * k₀) := by
          intro h; apply hQR_L_ne
          have := congr_fun h .L; rw [hQQ_L, hRR_L] at this; linarith
        have hd23 : Necklace.kStepVector (identifyPair w .m .s) (r + j₁ * k₀) (2 * k₀) ≠
            Necklace.kStepVector (identifyPair w .m .s) (r + i₃ * k₀) (2 * k₀) := by
          intro h; apply hQR_L_ne
          have := congr_fun h .L; rw [hMix_L, hRR_L] at this; linarith
        -- 3 elements in distinctKStepVectors contradicts card ≤ 2
        have hge3 : 3 ≤ (distinctKStepVectors (identifyPair w .m .s) (2 * k₀)).card :=
          calc 3 = ({Necklace.kStepVector (identifyPair w .m .s) (r + i₂ * k₀) (2 * k₀),
                     Necklace.kStepVector (identifyPair w .m .s) (r + j₁ * k₀) (2 * k₀),
                     Necklace.kStepVector (identifyPair w .m .s) (r + i₃ * k₀) (2 * k₀)}
                    : Finset _).card := by
                rw [Finset.card_insert_of_notMem (by simp [hd12, hd13]),
                    Finset.card_insert_of_notMem (by simp [hd23]),
                    Finset.card_singleton]
            _ ≤ _ := Finset.card_le_card (Finset.insert_subset_iff.mpr
                ⟨hmem_2k _, Finset.insert_subset_iff.mpr
                  ⟨hmem_2k _, Finset.singleton_subset_iff.mpr (hmem_2k _)⟩⟩)
        omega
      have htern' : isTernary w := ⟨⟨iL, hiL⟩, ⟨im, him⟩, ⟨is, his⟩⟩
      have hpwf' : isPairwisePrimMOS w := ⟨⟨hmosLm, hprimLm⟩, ⟨hmosms, hprimms⟩, ⟨hmosLs, hprimLs⟩⟩
      rcases hdichotomy with hno_QQ | hno_RR
      · -- Q is isolated (no consecutive QQ): apply nonalt helper with Qmin=Q, Qmaj=R
        exact hasAS_of_stacking_nonalt w htern' hpwf' hodd hns k₀ r hk₀_lt hk₀_cop hn_ge3
          R Q (fun i hi => (h_two_types i hi).elim Or.inr Or.inl)
          hclose_ne_R hclose_ne_Q hno_QQ heq_Lm heq_ms heq_Ls
      · -- R is isolated (no consecutive RR): apply nonalt helper with Qmin=R, Qmaj=Q
        exact hasAS_of_stacking_nonalt w htern' hpwf' hodd hns k₀ r hk₀_lt hk₀_cop hn_ge3
          Q R h_two_types hclose_ne_Q hclose_ne_R hno_RR heq_Lm heq_ms heq_Ls

/-- PWF ternary scales that aren't sporadic balanced are odd-regular.
    Reduces to: PWF → primitive (Phase A), PWF → AS (above),
    then `as_odd_isOddRegular` from MV3AS.lean assembles the result. -/
private lemma pwf_isOddRegular_of_not_sporadic (w : TernaryNecklace n)
    (htern : isTernary w) (hpwf : isPairwisePrimMOS w)
    (hodd : n % 2 = 1) (hns : ¬ isSporadicBalanced w) :
    isOddRegular w := by
  have hprim := isPrimitive_of_isPairwisePrimMOS w hpwf
  have has := pwf_hasAS w htern hpwf hodd hns
  exact as_odd_isOddRegular w hprim htern has hodd

/-- Pairwise-well-formed (PWF) ternary scales are either
    sporadic balanced or odd-regular. -/
theorem pwf_classification (w : TernaryNecklace n)
    (htern : isTernary w) (hpwf : isPairwisePrimMOS w) :
    isSporadicBalanced w ∨ isOddRegular w := by
  have hodd := pwf_n_odd w htern hpwf
  by_cases hs : isSporadicBalanced w
  · exact Or.inl hs
  · exact Or.inr (pwf_isOddRegular_of_not_sporadic w htern hpwf hodd hs)

/-- `isEvenRegular` is preserved under `applyPerm` (backward direction):
    if `applyPerm τ w` is even-regular, so is `w`. -/
private lemma isEvenRegular_of_isEvenRegular_applyPerm (τ : Equiv.Perm StepSize)
    (w : TernaryNecklace n)
    (h : isEvenRegular (Necklace.applyPerm τ w)) :
    isEvenRegular w := by
  obtain ⟨hprim', heven, σ, a, c, ha, hc, haodd, hcop, hn, hcL, hcm, hcs, hmos, hdel⟩ := h
  have hprim : Necklace.isPrimitive w := by
    have := isPrimitive_applyPerm τ.symm _ hprim'
    rwa [Necklace.applyPerm_symm_cancel] at this
  rw [← Necklace.applyPerm_mul] at hcL hcm hcs hmos hdel
  exact ⟨hprim, heven, σ * τ, a, c, ha, hc, haodd, hcop, hn, hcL, hcm, hcs, hmos, hdel⟩

/-! ### Coprime counts for balanced primitive ternary necklaces -/

/-- Length of filter-by-equality as sum of indicators (for StepSize). -/
private lemma list_filter_beq_length_as_sum (l : List StepSize) (a : StepSize) :
    ((l.filter (· == a)).length : ℤ) =
    (l.map (fun x => if x = a then (1 : ℤ) else 0)).sum := by
  induction l with
  | nil => simp
  | cons h t ih =>
    simp only [List.filter_cons, List.map_cons, List.sum_cons, beq_iff_eq]
    split_ifs with heq <;> simp_all; ring

/-- Sum of ternary k-step vector letter counts over all starting positions. -/
private lemma kStepVector_sum_all_ternary (w : TernaryNecklace n)
    (k : ℕ) (a : StepSize) :
    ∑ i ∈ Finset.range n, (Necklace.kStepVector w i k) a =
    ↑k * ↑(Necklace.count w a) := by
  -- Step 1: Express each kStepVector count as sum of indicators
  have h_expand : ∀ i, i < n →
      (Necklace.kStepVector w i k) a = ∑ m ∈ Finset.range k,
        (if w (((i + m : ℕ) : ZMod n)) = a then (1 : ℤ) else 0) := by
    intro i _hi
    unfold Necklace.kStepVector ZVector.ofList Necklace.slice
    rw [show i + k - i = k from by omega, List.map_map,
        list_filter_beq_length_as_sum, List.map_map]
    simp [pure, bind, Nat.cast_add, List.flatMap]
    rw [list_range_map_sum_eq_finset, ← Finset.sum_boole]
    apply Finset.sum_congr rfl; intro m _; simp [Function.comp]
  -- Step 2: Rewrite LHS as double Finset sum and exchange
  have h_lhs : ∑ i ∈ Finset.range n, (Necklace.kStepVector w i k) a =
      ∑ i ∈ Finset.range n, ∑ m ∈ Finset.range k,
        (if w (((i + m : ℕ) : ZMod n)) = a then (1 : ℤ) else 0) :=
    Finset.sum_congr rfl (fun i hi => h_expand i (Finset.mem_range.mp hi))
  rw [h_lhs, Finset.sum_comm]
  -- Step 3: Each inner sum equals count(w, a) by cyclic shift invariance
  have h_shift : ∀ m : ℕ, ∑ i ∈ Finset.range n,
      (if w (((i + m : ℕ) : ZMod n)) = a then (1 : ℤ) else 0) =
      ↑(Necklace.count w a) := by
    intro m
    induction m with
    | zero =>
      simp only [Nat.add_zero]
      simp_rw [show ∀ i : ℕ, (if w ((i : ℕ) : ZMod n) = a then (1 : ℤ) else 0) =
          ↑(if w ((i : ℕ) : ZMod n) = a then 1 else 0 : ℕ) from
          fun i => by split_ifs <;> simp]
      rw [← Nat.cast_sum, Finset.sum_boole]
      congr 1; unfold Necklace.count
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
      have hg_periodic : g n = g 0 := by
        simp only [hg_def, Nat.zero_add]
        have : ((n + m : ℕ) : ZMod n) = ((m : ℕ) : ZMod n) := by push_cast; simp
        rw [this]
      have h1 := Finset.sum_range_succ' g n
      have h2 := Finset.sum_range_succ g n
      linarith
  rw [Finset.sum_congr rfl (fun m _ => h_shift m), Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]

/-- If N integers sum to N·m and pairwise differ by ≤ 1, they all equal m. -/
private lemma int_sum_constant_of_close {N : ℕ} [NeZero N]
    (f : Fin N → ℤ) (m : ℤ)
    (hsum : ∑ i, f i = ↑N * m)
    (hclose : ∀ i j, Int.natAbs (f i - f j) ≤ 1) :
    ∀ i, f i = m := by
  by_contra h; push_neg at h
  obtain ⟨i₀, hi₀⟩ := h
  have hbd : ∀ j, f j ≤ f i₀ + 1 := fun j => by
    have := hclose j i₀; omega
  have hbd' : ∀ j, f i₀ - 1 ≤ f j := fun j => by
    have := hclose i₀ j; omega
  rcases lt_or_gt_of_ne hi₀ with hlt | hgt
  · have hle : ∀ j, f j ≤ m := fun j => by linarith [hbd j, Int.add_one_le_of_lt hlt]
    -- f j ≤ m for all j, and f(i₀) < m, so ∑ f < ∑ m
    have hstrict : ∑ i : Fin N, f i < ∑ _i : Fin N, m :=
      Finset.sum_lt_sum (fun j _ => hle j) ⟨i₀, Finset.mem_univ _, hlt⟩
    simp [Finset.sum_const, Fintype.card_fin] at hstrict
    linarith
  · have hge : ∀ j, m ≤ f j := fun j => by linarith [hbd' j, Int.le_sub_one_of_lt hgt]
    have hstrict : (∑ _i : Fin N, m) < ∑ i : Fin N, f i :=
      Finset.sum_lt_sum (fun j _ => hge j) ⟨i₀, Finset.mem_univ _, hgt⟩
    simp [Finset.sum_const, Fintype.card_fin] at hstrict
    linarith

/-- k-step vector at step 1 is an indicator. -/
private lemma kStepVector_one (w : TernaryNecklace n) (i : ℕ) (a : StepSize) :
    (Necklace.kStepVector w i 1) a =
    if w ((i : ℕ) : ZMod n) = a then 1 else 0 := by
  rw [kStepVector_eq_cast_count']
  simp only [Necklace.slice, show i + 1 - i = 1 from by omega, List.range_one]
  split_ifs with h <;> simp [List.count_nil, h]

/-- Balanced + primitive + ternary → gcd of all three counts is 1.
    Proof: if g=gcd>1, set k=n/g. Balance + integer average → all k-step
    subwords have the same letter counts. Window shift → w(i)=w(i+k),
    giving translational period k<n, contradicting primitivity. -/
private lemma balanced_primitive_coprime_counts (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (hprim : Necklace.isPrimitive w)
    (_htern : isTernary w) :
    Nat.gcd (Nat.gcd (Necklace.count w .L) (Necklace.count w .m))
      (Necklace.count w .s) = 1 := by
  by_contra hg
  set G := Nat.gcd (Nat.gcd (Necklace.count w .L) (Necklace.count w .m)) (Necklace.count w .s)
    with hG_def
  have hG_gt1 : G > 1 := by
    have : G ≠ 0 := by
      intro h0
      have hdvd : (0 : ℕ) ∣ Necklace.count w .s := h0 ▸ (Nat.gcd_dvd_right _ _)
      rw [zero_dvd_iff] at hdvd
      exact absurd hdvd (by have := count_pos_of_isTernary w _htern .s; omega)
    omega
  have hG_L : G ∣ Necklace.count w .L :=
    dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)
  have hG_m : G ∣ Necklace.count w .m :=
    dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
  have hG_s : G ∣ Necklace.count w .s := Nat.gcd_dvd_right _ _
  have hG_n : G ∣ n := by
    have h := count_total w
    obtain ⟨a, ha⟩ := hG_L; obtain ⟨b, hb⟩ := hG_m; obtain ⟨c, hc⟩ := hG_s
    exact ⟨a + b + c, by linarith⟩
  set k := n / G
  have hn_pos : 0 < n := NeZero.pos n
  have hk_pos : 0 < k := Nat.div_pos (Nat.le_of_dvd hn_pos hG_n) (by omega)
  have hk_lt : k < n := Nat.div_lt_self hn_pos hG_gt1
  have hk_dvd : k ∣ n := Nat.div_dvd_of_dvd hG_n
  have hkG : k * G = n := Nat.div_mul_cancel hG_n
  -- For each letter and position, kStepVector = count / G
  have hall_eq : ∀ (a : StepSize) (i : ℕ), i < n →
      (Necklace.kStepVector w i k) a = ↑(Necklace.count w a / G) := by
    intro a i hi
    -- Sum identity over Fin n
    have hfsum : ∑ j : Fin n, (Necklace.kStepVector w j.val k) a =
        ↑n * ↑(Necklace.count w a / G) := by
      rw [Fin.sum_univ_eq_sum_range (fun i => (Necklace.kStepVector w i k) a)]
      rw [kStepVector_sum_all_ternary]
      have hga : G ∣ Necklace.count w a := by cases a <;> assumption
      have : k * Necklace.count w a = n * (Necklace.count w a / G) := by
        nlinarith [Nat.div_mul_cancel hga, hkG]
      exact_mod_cast this
    -- Balance: pairwise differ by ≤ 1
    have hfclose : ∀ i j : Fin n,
        Int.natAbs ((Necklace.kStepVector w i.val k) a -
          (Necklace.kStepVector w j.val k) a) ≤ 1 := by
      intro ⟨i', hi'⟩ ⟨j', hj'⟩
      rw [kStepVector_eq_cast_count', kStepVector_eq_cast_count']
      exact hbal k hk_pos hk_lt _ _ a
        (List.mem_ofFn.mpr ⟨⟨i', hi'⟩, rfl⟩)
        (List.mem_ofFn.mpr ⟨⟨j', hj'⟩, rfl⟩)
    exact int_sum_constant_of_close _ _ hfsum hfclose ⟨i, hi⟩
  -- Extend hall_eq to all ℕ via kStepVector_mod_n
  have hall_eq' : ∀ (a : StepSize) (i : ℕ),
      (Necklace.kStepVector w i k) a = ↑(Necklace.count w a / G) := by
    intro a i; rw [← kStepVector_mod_n]; exact hall_eq a (i % n) (Nat.mod_lt _ hn_pos)
  -- Window shift: w(i) = w(i + k) for all i : ZMod n
  have hperiod : ∀ i : ZMod n, w i = w (i + (k : ZMod n)) := by
    intro i
    set j := ZMod.val i with hj_def
    have hj_lt : j < n := ZMod.val_lt i
    -- Split kStepVector at j and j+1, cancel common (k-1)-step part
    have hone_eq : ∀ a : StepSize,
        (Necklace.kStepVector w j 1) a = (Necklace.kStepVector w (j + k) 1) a := by
      intro a
      have hd1 := kStepVector_add w j 1 (k - 1) a
      rw [show 1 + (k - 1) = k from by omega] at hd1
      have hd2 := kStepVector_add w (j + 1) (k - 1) 1 a
      rw [show k - 1 + 1 = k from by omega,
          show j + 1 + (k - 1) = j + k from by omega] at hd2
      linarith [hall_eq' a j, hall_eq' a (j + 1)]
    -- Derive w ↑(j+k) = w ↑j from kStepVector_one and hone_eq
    have hwjk : w (((j + k : ℕ) : ZMod n)) = w ((j : ℕ) : ZMod n) := by
      have h1 := kStepVector_one w j (w ((j : ℕ) : ZMod n))
      rw [if_pos rfl] at h1
      have h2 := kStepVector_one w (j + k) (w ((j : ℕ) : ZMod n))
      rw [← hone_eq (w ((j : ℕ) : ZMod n)), h1] at h2
      by_contra hne; rw [if_neg hne] at h2; exact absurd h2 one_ne_zero
    -- Convert: i = ↑j and i + ↑k = ↑(j+k)
    conv_lhs => rw [show i = ((j : ℕ) : ZMod n) from (ZMod.natCast_zmod_val i).symm]
    conv_rhs => rw [show i + (k : ZMod n) = ((j + k : ℕ) : ZMod n) from by
      rw [show i = ((j : ℕ) : ZMod n) from (ZMod.natCast_zmod_val i).symm]; push_cast; ring]
    exact hwjk.symm
  exact absurd (Necklace.period_length_le_of_translational_period w k hk_pos hk_lt hk_dvd hperiod)
    (by rw [hprim]; omega)

/-- If f ∘ w is primitive, then w is primitive (local copy). -/
private lemma isPrimitive_of_comp' {α β : Type*} [DecidableEq α] [DecidableEq β]
    (w : Necklace α n) (f : α → β)
    (h : Necklace.isPrimitive (f ∘ w)) :
    Necklace.isPrimitive w := by
  by_contra h_not_prim
  set pLen := (Necklace.period w).length
  have hpLen_pos : 0 < pLen := period_length_pos w
  have hpLen_lt_n : pLen < n := by
    have := Necklace.period_length_le_n w; unfold Necklace.isPrimitive at h_not_prim; omega
  have hpLen_dvd : pLen ∣ n := period_dvd_length w
  have hw_per : ∀ j : ℕ, w ((j : ℕ) : ZMod n) = w ((j % pLen : ℕ) : ZMod n) :=
    fun j => period_pointwise w j
  have hfw_per : ∀ j : ℕ, (f ∘ w) ((j : ℕ) : ZMod n) = (f ∘ w) ((j % pLen : ℕ) : ZMod n) :=
    fun j => congrArg f (hw_per j)
  have hfw_trans : ∀ i : ZMod n, (f ∘ w) i = (f ∘ w) (i + (pLen : ZMod n)) := by
    intro i
    have h1 := hfw_per i.val
    have h2 := hfw_per (i.val + pLen)
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq] at h1
    rw [Nat.add_mod_right] at h2
    rw [h1, ← h2]; congr 1
    simp [Nat.cast_add, ZMod.natCast_val, ZMod.cast_id']
  have := Necklace.period_length_le_of_translational_period (f ∘ w) pLen hpLen_pos hpLen_lt_n
    hpLen_dvd hfw_trans
  unfold Necklace.isPrimitive at h; omega

/-- A pair identification of a balanced ternary necklace is pairwise-prim-MOS
    when its binary image has coprime counts. -/
private lemma balanced_identification_primMOS (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (htern : isTernary w)
    (x y : StepSize) (hxy : x ≠ y)
    (hcop : Nat.gcd (Necklace.count (identifiedToBinary (identifyPair w x y)) .L)
                     (Necklace.count (identifiedToBinary (identifyPair w x y)) .s) = 1) :
    isPartialPairwisePrimMOS w x y :=
  ⟨balanced_ternary_identification_hasMOS w hbal htern x y hxy,
   isPrimitive_of_comp' (identifyPair w x y) msToBinary
     (necklace_with_coprime_sig_is_primitive n _ _ hcop _ rfl rfl)⟩

/-- Binary L-count after identifying m=s equals count_L. -/
private lemma identifiedToBinary_ms_count_L (w : TernaryNecklace n) :
    Necklace.count (identifiedToBinary (identifyPair w .m .s)) .L = Necklace.count w .L := by
  unfold Necklace.count; congr 1; ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    identifiedToBinary, msToBinary, identifyPair, Function.comp]
  constructor
  · intro h; by_contra hne; cases hw : w i <;> simp_all
  · intro h; simp [h]

/-- Binary L-count after identifying L=s equals count_m. -/
private lemma identifiedToBinary_Ls_count_L (w : TernaryNecklace n) :
    Necklace.count (identifiedToBinary (identifyPair w .L .s)) .L = Necklace.count w .m := by
  unfold Necklace.count; congr 1; ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    identifiedToBinary, msToBinary, identifyPair, Function.comp]
  constructor
  · intro h; by_contra hne; cases hw : w i <;> simp_all
  · intro h; simp [h]

/-- The sporadic balanced scale (Fraenkel word `LmLsLmL`) is pairwise-prim-MOS.
    Since n = 7 is prime, all identification binary counts are coprime. -/
private lemma sporadicBalanced_isPairwisePrimMOS (w : TernaryNecklace n)
    (_hprim : Necklace.isPrimitive w)
    (hbal : Necklace.isBalanced w) (htern : isTernary w)
    (h : isSporadicBalanced w) :
    isPairwisePrimMOS w := by
  obtain ⟨hn7, _⟩ := h
  have h7_prime : Nat.Prime 7 := by decide
  have hL_pos := count_pos_of_isTernary w htern .L
  have hm_pos := count_pos_of_isTernary w htern .m
  have hs_pos := count_pos_of_isTernary w htern .s
  have htotal := count_total w
  -- For 0 < x < 7: gcd(x, 7-x) = 1 since 7 is prime
  have coprime_pair : ∀ x : ℕ, 0 < x → x < 7 → Nat.gcd x (7 - x) = 1 := by
    intro x hx hx7
    rw [← Nat.gcd_add_self_right x (7 - x), show (7 - x) + x = 7 from by omega,
        Nat.gcd_comm]
    exact h7_prime.coprime_iff_not_dvd.mpr (by omega)
  refine ⟨?_, ?_, ?_⟩
  · -- L=m: binary s = count_s, binary L = n - count_s
    exact balanced_identification_primMOS w hbal htern .L .m (by decide) (by
      have hcs := identifiedToBinary_count_s w (show Necklace.count w .s = _ from rfl)
      have htot := binary_count_total (identifiedToBinary (identifyPair w .L .m))
      have hcL : Necklace.count (identifiedToBinary (identifyPair w .L .m)) .L =
          7 - Necklace.count w .s := by rw [hcs] at htot; omega
      rw [hcL, hcs, Nat.gcd_comm]; exact coprime_pair _ hs_pos (by omega))
  · -- m=s: binary L = count_L
    exact balanced_identification_primMOS w hbal htern .m .s (by decide) (by
      have hcL := identifiedToBinary_ms_count_L w
      have htot := binary_count_total (identifiedToBinary (identifyPair w .m .s))
      have hcs : Necklace.count (identifiedToBinary (identifyPair w .m .s)) .s =
          7 - Necklace.count w .L := by rw [hcL] at htot; omega
      rw [hcL, hcs]; exact coprime_pair _ hL_pos (by omega))
  · -- L=s: binary L = count_m
    exact balanced_identification_primMOS w hbal htern .L .s (by decide) (by
      have hcL := identifiedToBinary_Ls_count_L w
      have htot := binary_count_total (identifiedToBinary (identifyPair w .L .s))
      have hcs : Necklace.count (identifiedToBinary (identifyPair w .L .s)) .s =
          7 - Necklace.count w .m := by rw [hcL] at htot; omega
      rw [hcL, hcs]; exact coprime_pair _ hm_pos (by omega))

/-- In a balanced ternary necklace with count_L = count_m, if two non-s positions
    p and p+d are separated only by s's (with 0 < d and d+1 < n), then w(p) ≠ w(p+d).
    Uses balanced_two_equal_no_x2_y0: the (d+1)-step subword has x≥2, y=0. -/
private lemma balanced_Lm_consecutive_nonS_differ (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (_htern : isTernary w)
    (hLm : Necklace.count w .L = Necklace.count w .m)
    (p d : ℕ) (hd_pos : 0 < d) (hdk_lt : d + 1 < n)
    (hp : w ((p : ℕ) : ZMod n) ≠ .s)
    (hpd : w (((p + d : ℕ) : ℕ) : ZMod n) ≠ .s)
    (hall_s : ∀ t : ℕ, 0 < t → t < d → w (((p + t : ℕ) : ℕ) : ZMod n) = .s) :
    w ((p : ℕ) : ZMod n) ≠ w (((p + d : ℕ) : ℕ) : ZMod n) := by
  intro h_same
  -- Determine which letter w(p) is (L or m, since ≠ s)
  have hv_Lm : w ((p : ℕ) : ZMod n) = .L ∨ w ((p : ℕ) : ZMod n) = .m := by
    cases h : w ((p : ℕ) : ZMod n) with | L => left; rfl | m => right; rfl | s => exact absurd h hp
  -- Every position in [p, p+d] has value w(p) or s
  have h_entries : ∀ t : ℕ, t < d + 1 →
      w (((p + t : ℕ) : ℕ) : ZMod n) = w ((p : ℕ) : ZMod n) ∨
      w (((p + t : ℕ) : ℕ) : ZMod n) = .s := by
    intro t ht
    rcases Nat.eq_zero_or_pos t with rfl | ht_pos
    · simp
    · rcases Nat.lt_or_ge t d with ht_lt | ht_ge
      · right; exact hall_s t ht_pos ht_lt
      · have : t = d := by omega
        subst this; left; exact h_same.symm
  -- kStepVector for "other" letter y = 0 (inductive, avoids slice membership)
  have hkv_other : ∀ y : StepSize, y ≠ w ((p : ℕ) : ZMod n) → y ≠ .s →
      Necklace.kStepVector w p (d + 1) y = 0 := by
    intro y hy_ne_v hy_ne_s
    have h_ne_y : ∀ t : ℕ, t < d + 1 → w (((p + t : ℕ) : ℕ) : ZMod n) ≠ y := by
      intro t ht
      rcases h_entries t ht with hv | hs
      · rw [hv]; exact Ne.symm hy_ne_v
      · rw [hs]; exact Ne.symm hy_ne_s
    suffices ∀ (m q : ℕ), (∀ t, t < m → w (((q + t : ℕ) : ℕ) : ZMod n) ≠ y) →
        Necklace.kStepVector w q m y ≤ 0 from
      le_antisymm (this (d + 1) p h_ne_y) (kStepVector_nonneg' w p (d + 1) y)
    intro m
    induction m with
    | zero =>
      intro q _
      unfold Necklace.kStepVector Necklace.slice ZVector.ofList
      simp
    | succ m ih =>
      intro q hall
      have hsplit := kStepVector_add w q m 1 y
      have hm := ih q (fun t ht => hall t (by omega))
      have h1 : Necklace.kStepVector w (q + m) 1 y ≤ 0 := by
        rw [(kStepVector_singleton w (q + m)) y]
        have hne := hall m (by omega)
        simp only [Nat.cast_add] at hne ⊢
        simp [hne]
      linarith
  -- kStepVector for w(p) letter ≥ 2 (first + middle + last)
  have hkv_ge2 : Necklace.kStepVector w p (d + 1) (w ((p : ℕ) : ZMod n)) ≥ 2 := by
    have hsplit := kStepVector_add w p 1 d (w ((p : ℕ) : ZMod n))
    rw [show 1 + d = d + 1 from by omega] at hsplit
    have hp1 : Necklace.kStepVector w p 1 (w ((p : ℕ) : ZMod n)) = 1 := by
      rw [(kStepVector_singleton w p) (w ((p : ℕ) : ZMod n))]; simp
    have hsplit2 := kStepVector_add w (p + 1) (d - 1) 1 (w ((p : ℕ) : ZMod n))
    rw [show d - 1 + 1 = d from by omega,
        show p + 1 + (d - 1) = p + d from by omega] at hsplit2
    have hpd1 : Necklace.kStepVector w (p + d) 1 (w ((p : ℕ) : ZMod n)) = 1 := by
      rw [(kStepVector_singleton w (p + d)) (w ((p : ℕ) : ZMod n))]
      simp [h_same]
    linarith [kStepVector_nonneg' w (p + 1) (d - 1) (w ((p : ℕ) : ZMod n))]
  -- Final contradiction via balanced_two_equal_no_x2_y0
  rcases hv_Lm with hv_L | hv_m
  · rw [hv_L] at hkv_ge2 hkv_other
    exact balanced_two_equal_no_x2_y0 w hbal .L .m (by decide) hLm (d + 1) (by omega) hdk_lt p
      hkv_ge2 (hkv_other .m (by decide) (by decide))
  · rw [hv_m] at hkv_ge2 hkv_other
    exact balanced_two_equal_no_x2_y0 w hbal .m .L (by decide) hLm.symm (d + 1) (by omega) hdk_lt p
      hkv_ge2 (hkv_other .L (by decide) (by decide))

/-- Balanced primitive ternary with L=m counts and c even → deletion of s gives MOS.
    This is the core of Step 6: the deletion word (L's and m's only) alternates. -/
private lemma balanced_Lm_c_even_deletionMOS (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (_hprim : Necklace.isPrimitive w)
    (htern : isTernary w)
    (hLm : Necklace.count w .L = Necklace.count w .m)
    (hc_even : Necklace.count w .s % 2 = 0) :
    isPartialDeletionMOS w .s := by
  set a := Necklace.count w .L with ha_def
  set c := Necklace.count w .s with hc_def
  set D := TernaryNecklace.orderedDeletion w .s with hD_def
  have ha_pos : a > 0 := count_pos_of_isTernary w htern .L
  have hc_pos : c > 0 := count_pos_of_isTernary w htern .s
  have hn_eq : n = 2 * a + c := by
    have h := count_total w
    change a + Necklace.count w .m + c = n at h
    linarith [hLm]
  have hn_pos : n > 0 := by omega
  haveI : NeZero n := ⟨by omega⟩
  have hDlen : D.length = 2 * a := by
    have h := orderedDeletion_length w .s
    change D.length + c = n at h; omega
  have hmem_ne_s : ∀ v ∈ D, v ≠ .s := fun v hv => by
    simp only [D, TernaryNecklace.orderedDeletion, List.mem_filter,
      decide_eq_true_eq] at hv; exact hv.2
  have hbin : ∀ i, (hi : i < D.length) → D[i] = .L ∨ D[i] = .m := by
    intro i hi
    have hne : D[i] ≠ .s := hmem_ne_s _ (List.getElem_mem hi)
    cases h : D[i] <;> simp_all
  have hDcountL : D.count .L = a := orderedDeletion_count_ne w .s .L (by decide)
  have hDcountm : D.count .m = a :=
    (orderedDeletion_count_ne w .s .m (by decide)).trans hLm.symm
  -- Define position list P: positions of non-s entries in order
  set P := (List.range n).filter (fun i => decide (w ((i : ℕ) : ZMod n) ≠ .s)) with hP_def
  -- D = P.map (fun i => w(i)): use monadic normalization trick
  have hD_eq_map : D = P.map (fun i => w ((i : ℕ) : ZMod n)) := by
    show TernaryNecklace.orderedDeletion w .s =
      ((List.range n).filter (fun i => decide (w ((i : ℕ) : ZMod n) ≠ .s))).map
        (fun i => w ((i : ℕ) : ZMod n))
    unfold TernaryNecklace.orderedDeletion
    have heq : ∀ (l : List ℕ), (do let a ← l; pure (↑a : ZMod n)) =
        l.map (Nat.cast : ℕ → ZMod n) := by
      intro l; induction l with
      | nil => rfl
      | cons a l ih => simp only [List.map_cons]; exact congrArg _ ih
    simp only [heq, List.map_map, List.filter_map, Function.comp_def]
  have hP_len : P.length = 2 * a := by
    rw [← hDlen, hD_eq_map, List.length_map]
  -- P elements are < n
  have hP_lt : ∀ i, (hi : i < P.length) → P[i] < n := by
    intro i hi
    exact List.mem_range.mp (List.mem_filter.mp (List.getElem_mem hi)).1
  -- D[i] = w(P[i])
  have hD_val : ∀ i₀, (hi₀ : i₀ < D.length) →
      D[i₀] = w ((P[i₀]'(by rw [hP_len]; omega) : ℕ) : ZMod n) := by
    intro i₀ hi₀
    simp only [hD_eq_map, List.getElem_map]
  -- P is sorted (strictly increasing)
  have hP_sorted : P.Pairwise (· < ·) :=
    List.Pairwise.filter _ List.pairwise_lt_range
  -- w(P[i]) ≠ .s for all valid i
  have hP_nonS : ∀ i, (hi : i < P.length) →
      w ((P[i] : ℕ) : ZMod n) ≠ .s := by
    intro i hi
    exact decide_eq_true_eq.mp (List.mem_filter.mp (List.getElem_mem hi)).2
  -- Gap property: between consecutive P entries, all values are s
  have hP_gap : ∀ i₀, (hi₀ : i₀ + 1 < P.length) → ∀ q : ℕ,
      P[i₀] < q → q < P[i₀ + 1] → w ((q : ℕ) : ZMod n) = .s := by
    intro i₀ hi₀ q hq_lb hq_ub
    by_contra h_not_s
    have hq_lt_n : q < n := by have := hP_lt (i₀ + 1) hi₀; omega
    have hq_mem : q ∈ P :=
      List.mem_filter.mpr ⟨List.mem_range.mpr hq_lt_n, decide_eq_true_eq.mpr h_not_s⟩
    obtain ⟨j, hj, hq_eq⟩ := List.mem_iff_getElem.mp hq_mem
    have h1 : i₀ < j := by
      by_contra hle; push_neg at hle
      rcases Nat.lt_or_eq_of_le hle with hjlt | hjeq
      · exact absurd (lt_trans
          ((List.pairwise_iff_getElem.mp hP_sorted) j i₀ hj (by omega) hjlt) hq_lb)
          (not_lt.mpr (le_of_eq hq_eq.symm))
      · subst hjeq
        exact absurd hq_lb (not_lt.mpr (le_of_eq hq_eq.symm))
    have h2 : j < i₀ + 1 := by
      by_contra hle; push_neg at hle
      rcases Nat.lt_or_eq_of_le hle with hjlt | hjeq
      · exact absurd (lt_trans hq_ub
          ((List.pairwise_iff_getElem.mp hP_sorted) (i₀ + 1) j (by omega) hj (by omega)))
          (not_lt.mpr (le_of_eq hq_eq))
      · subst hjeq
        exact absurd hq_ub (not_lt.mpr (le_of_eq hq_eq))
    omega
  -- Handle a = 1 separately: gap bound fails, but D has 2 elements and is trivially MOS
  by_cases ha_ge2 : a ≥ 2
  swap
  · have ha1 : a = 1 := by omega
    -- D is Nodup: count L = 1, count m = 1, count s = 0
    have hnodup : D.Nodup := by
      rw [List.nodup_iff_count_le_one]; intro a
      cases a with
      | L => rw [hDcountL, ha1]
      | m => rw [hDcountm, ha1]
      | s => simp [List.count_eq_zero.mpr (fun h => (hmem_ne_s .s h) rfl)]
    have hne01 : D[0]'(by omega) ≠ D[1]'(by omega) :=
      (List.pairwise_iff_getElem.mp hnodup) 0 1 (by omega) (by omega) (by omega)
    exact alternating_circular_mos D 1 (by rw [hDlen, ha1]) (by omega)
      (fun i hi => by rw [hDlen, ha1] at hi; interval_cases i <;> simp) hne01
  -- From here, a ≥ 2
  -- d+1 < n for any gap between consecutive P entries
  have hP_gap_lt : ∀ i₀, (hi₀ : i₀ + 1 < P.length) →
      P[i₀ + 1] - P[i₀] + 1 < n := by
    -- Upper bound: P[j] + (P.length - j) ≤ n
    have h_upper : ∀ j, (hj : j < P.length) → P[j] + (P.length - j) ≤ n := by
      suffices ∀ d j, (hj : j < P.length) → j + d = P.length - 1 →
          P[j] + (P.length - j) ≤ n from
        fun j hj => this (P.length - 1 - j) j hj (by omega)
      intro d; induction d with
      | zero => intro j hj hd; have := hP_lt j (by omega); omega
      | succ d ih =>
        intro j hj hd
        have := (List.pairwise_iff_getElem.mp hP_sorted) j (j + 1)
          (by omega) (by omega : j + 1 < P.length) (by omega)
        have := ih (j + 1) (by omega) (by omega)
        omega
    -- Lower bound: P[j] ≥ j
    have h_lower : ∀ j, (hj : j < P.length) → j ≤ P[j] := by
      intro j hj; induction j with
      | zero => omega
      | succ k ih =>
        have := (List.pairwise_iff_getElem.mp hP_sorted) k (k + 1) (by omega) hj (by omega)
        have := ih (by omega); omega
    intro i₀ hi₀
    have := h_lower i₀ (by omega)
    have := h_upper (i₀ + 1) hi₀
    have := (List.pairwise_iff_getElem.mp hP_sorted) i₀ (i₀ + 1) (by omega) (by omega) (by omega)
    rw [hP_len] at *; omega
  -- All consecutive D entries differ (non-wrapping)
  have hall_diff_inner : ∀ (i₀ : ℕ) (_ : i₀ + 1 < D.length),
      D[i₀] ≠ D[i₀ + 1] := by
    intro i₀ hi₀
    rw [hD_val i₀ (by omega), hD_val (i₀ + 1) (by omega)]
    have hp₀ := hP_lt i₀ (by rw [hP_len]; omega)
    have hp₁ := hP_lt (i₀ + 1) (by rw [hP_len]; omega)
    have h_inc := (List.pairwise_iff_getElem.mp hP_sorted) i₀ (i₀ + 1)
      (by rw [hP_len]; omega) (by rw [hP_len]; omega) (by omega)
    set d := P[i₀ + 1]'(by rw [hP_len]; omega) - P[i₀]'(by rw [hP_len]; omega)
    have hd_pos : 0 < d := by omega
    have hpd_eq : P[i₀ + 1]'(by rw [hP_len]; omega) =
        P[i₀]'(by rw [hP_len]; omega) + d := by omega
    rw [hpd_eq]
    exact balanced_Lm_consecutive_nonS_differ w hbal htern hLm
      (P[i₀]'(by rw [hP_len]; omega)) d hd_pos
      (hP_gap_lt i₀ (by rw [hP_len]; omega))
      (hP_nonS i₀ (by rw [hP_len]; omega))
      (by rw [← hpd_eq]; exact hP_nonS (i₀ + 1) (by rw [hP_len]; omega))
      (fun t ht_pos ht_lt => by
        exact hP_gap i₀ (by rw [hP_len]; omega)
          (P[i₀]'(by rw [hP_len]; omega) + t) (by omega) (by omega))
  -- Period 2: D[j+2] = D[j] (uses hall_diff_inner directly, no circular argument)
  have hperiod2 : ∀ j, (hj : j + 2 < D.length) → D[j + 2]'(by omega) = D[j]'(by omega) := by
    intro j hj
    have := hall_diff_inner j (by omega)
    have := hall_diff_inner (j + 1) (by omega)
    rcases hbin j (by omega), hbin (j + 1) (by omega), hbin (j + 2) (by omega) with
      ⟨h0 | h0, h1 | h1, h2 | h2⟩ <;> simp_all
  -- Alternation: D[i] = D[i % 2]
  have halt : ∀ i, (hi : i < D.length) → D[i] = D[i % 2]'(by omega) := by
    intro i hi
    exact Nat.strongRecOn i (fun m ih => by
      intro hm; match m with
      | 0 => rfl
      | 1 => rfl
      | m + 2 =>
        rw [hperiod2 m (by omega), ih m (by omega) (by omega)]
        congr 1; omega) hi
  -- D[0] ≠ D[1]
  have hne : D[0]'(by omega) ≠ D[1]'(by omega) := hall_diff_inner 0 (by omega)
  exact alternating_circular_mos D a hDlen ha_pos halt hne

/-- Balanced primitive ternary with L=m counts → isPairwisePrimMOS or isEvenRegular.
    Uses coprime counts to show all identifications are primitive MOS (c odd),
    or constructs isEvenRegular (c even). -/
private lemma balanced_Lm_isPWF (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (hprim : Necklace.isPrimitive w)
    (htern : isTernary w)
    (hLm : Necklace.count w .L = Necklace.count w .m) :
    isPairwisePrimMOS w ∨ isEvenRegular w := by
  set a := Necklace.count w .L with ha_def
  set c := Necklace.count w .s with hc_def
  -- gcd(a, c) = 1 from balanced_primitive_coprime_counts + gcd(a,a) = a
  have hcop : Nat.gcd a c = 1 := by
    have h := balanced_primitive_coprime_counts w hbal hprim htern
    rwa [show Nat.gcd a (Necklace.count w .m) = a from
      by rw [← hLm]; exact Nat.gcd_self a] at h
  have hn_eq : n = 2 * a + c := by have := count_total w; omega
  by_cases hc_odd : c % 2 = 1
  · -- c odd: all identification binary counts are coprime
    left
    -- gcd(2a, c) = 1 since gcd(a,c)=1 and c is odd
    have hcop_2ac : Nat.gcd (2 * a) c = 1 :=
      ((Nat.coprime_two_left.mpr (by rwa [Nat.odd_iff])).mul_left hcop : Nat.Coprime _ _)
    -- gcd(a, a+c) = gcd(a, c) = 1
    have hcop_aac : Nat.gcd a (a + c) = 1 := by
      rw [show a + c = c + a from by omega, Nat.gcd_add_self_right]; exact hcop
    refine ⟨?_, ?_, ?_⟩
    · -- L=m identification: binary counts (2a, c)
      exact balanced_identification_primMOS w hbal htern .L .m (by decide) (by
        rw [identifiedToBinary_count_L w rfl hLm.symm, identifiedToBinary_count_s w rfl]
        exact hcop_2ac)
    · -- m=s identification: binary L = count_L = a, binary s = a+c
      exact balanced_identification_primMOS w hbal htern .m .s (by decide) (by
        have hcL := identifiedToBinary_ms_count_L w
        have hcs : Necklace.count (identifiedToBinary (identifyPair w .m .s)) .s = a + c := by
          have := binary_count_total (identifiedToBinary (identifyPair w .m .s))
          rw [hcL] at this; omega
        rw [hcL, hcs]; exact hcop_aac)
    · -- L=s identification: binary L = count_m = a, binary s = a+c
      exact balanced_identification_primMOS w hbal htern .L .s (by decide) (by
        have hcL := identifiedToBinary_Ls_count_L w
        have hcs : Necklace.count (identifiedToBinary (identifyPair w .L .s)) .s = a + c := by
          have := binary_count_total (identifiedToBinary (identifyPair w .L .s))
          rw [hcL, ← hLm] at this; omega
        rw [hcL, ← hLm, hcs]; exact hcop_aac)
  · -- c even: construct isEvenRegular w
    right
    have hc_even : c % 2 = 0 := by omega
    have ha_pos : a > 0 := count_pos_of_isTernary w htern .L
    set c' := c / 2
    have hc_eq : c = 2 * c' := by omega
    have hc'_pos : c' > 0 := by
      have := count_pos_of_isTernary w htern .s; omega
    have ha_odd : a % 2 = 1 := by
      by_contra h; push_neg at h
      have h2 : 2 ∣ Nat.gcd a c := Nat.dvd_gcd (by omega) (by omega)
      omega
    have hcop' : Nat.Coprime a c' := by
      have h : Nat.gcd a c' ∣ Nat.gcd a c :=
        Nat.dvd_gcd (Nat.gcd_dvd_left _ _) (dvd_trans (Nat.gcd_dvd_right _ _) ⟨2, by omega⟩)
      rw [hcop] at h; exact Nat.dvd_one.mp h
    have hmos_Lm : isPartialPairwiseMOS w .L .m :=
      balanced_ternary_identification_hasMOS w hbal htern .L .m (by decide)
    have hdel_s : isPartialDeletionMOS w .s :=
      balanced_Lm_c_even_deletionMOS w hbal hprim htern hLm hc_even
    exact ⟨hprim, by omega, 1, a, c', ha_pos, hc'_pos, ha_odd, hcop', by omega,
      by rw [Necklace.applyPerm_one],
      by rw [Necklace.applyPerm_one]; exact hLm.symm,
      by rw [Necklace.applyPerm_one]; exact hc_eq,
      by rw [Necklace.applyPerm_one]; exact hmos_Lm,
      by rw [Necklace.applyPerm_one]; exact hdel_s⟩

/-- Balanced primitive ternary scales that aren't even-regular are PWF.

    **Proof**: By `balanced_primitive_coprime_counts`, the gcd of all three
    step counts is 1. For each case:
    • Two equal counts: normalize to L=m via `applyPerm`, then use coprime
      binary counts for all three identifications.
    • All three counts distinct: the scale is the Fraenkel word (sporadic balanced),
      and n=7 prime gives coprime binary counts. -/
private lemma balanced_not_even_isPWF (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (hprim : Necklace.isPrimitive w)
    (htern : isTernary w) (_hne : ¬ isEvenRegular w) :
    isPairwisePrimMOS w := by
  by_cases hLm : Necklace.count w .L = Necklace.count w .m
  · exact (balanced_Lm_isPWF w hbal hprim htern hLm).elim id
      fun h => absurd h _hne
  · by_cases hms : Necklace.count w .m = Necklace.count w .s
    · -- m = s, L ≠ m. Use swap(L,s) to normalize to L=m form.
      set σ := Equiv.swap StepSize.L StepSize.s
      set w' := Necklace.applyPerm σ w
      have hLm' : Necklace.count w' .L = Necklace.count w' .m := by
        rw [count_applyPerm_eq, count_applyPerm_eq]
        simp [show σ.symm .L = .s from by decide, show σ.symm .m = .m from by decide]
        exact hms.symm
      rcases balanced_Lm_isPWF w' (isBalanced_applyPerm σ w hbal)
        (isPrimitive_applyPerm σ w hprim) ((isTernary_applyPerm σ w).mpr htern) hLm' with h | h
      · exact isPairwisePrimMOS_of_applyPerm σ w h
      · exact absurd (isEvenRegular_of_isEvenRegular_applyPerm σ w h) _hne
    · by_cases hLs : Necklace.count w .L = Necklace.count w .s
      · -- L = s, m ≠ s. Use swap(m,s) to normalize to L=m form.
        set σ := Equiv.swap StepSize.m StepSize.s
        set w' := Necklace.applyPerm σ w
        have hLm' : Necklace.count w' .L = Necklace.count w' .m := by
          rw [count_applyPerm_eq, count_applyPerm_eq]
          simp [show σ.symm .L = .L from by decide, show σ.symm .m = .s from by decide]
          exact hLs
        rcases balanced_Lm_isPWF w' (isBalanced_applyPerm σ w hbal)
          (isPrimitive_applyPerm σ w hprim) ((isTernary_applyPerm σ w).mpr htern) hLm' with h | h
        · exact isPairwisePrimMOS_of_applyPerm σ w h
        · exact absurd (isEvenRegular_of_isEvenRegular_applyPerm σ w h) _hne
      · -- All three counts distinct → sporadic (Fraenkel word)
        exact sporadicBalanced_isPairwisePrimMOS w hprim hbal htern
          (balanced_all_distinct_isSporadicBalanced w hbal hprim htern hLm hms hLs)

/-- Classification of balanced primitive ternary scales:
    sporadic balanced, odd-regular, or even-regular. -/
theorem balanced_primitive_ternary_classification (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (hprim : Necklace.isPrimitive w)
    (htern : isTernary w) :
    isSporadicBalanced w ∨ isOddRegular w ∨ isEvenRegular w := by
  by_cases he : isEvenRegular w
  · exact Or.inr (Or.inr he)
  · have hpwf := balanced_not_even_isPWF w hbal hprim htern he
    rcases pwf_classification w htern hpwf with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

/-- A finset of integers with pairwise absolute difference ≤ 1 has at most 2 elements. -/
private lemma close_int_finset_card_le_two (T : Finset ℤ)
    (hclose : ∀ x ∈ T, ∀ y ∈ T, Int.natAbs (x - y) ≤ 1) :
    T.card ≤ 2 := by
  by_contra hgt; push_neg at hgt
  have hne : T.Nonempty := Finset.card_pos.mp (by omega)
  -- min ≠ max (otherwise card ≤ 1)
  have hne_mm : T.min' hne ≠ T.max' hne := by
    intro heq
    have : T.card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb => by
      have := Finset.min'_le T a ha; have := Finset.le_max' T a ha
      have := Finset.min'_le T b hb; have := Finset.le_max' T b hb; omega
    omega
  -- max = min + 1
  have hmin_mem := Finset.min'_mem T hne
  have hmax_mem := Finset.max'_mem T hne
  have hconsec : T.max' hne = T.min' hne + 1 := by
    have h1 : |(T.min' hne - T.max' hne : ℤ)| ≤ 1 := by
      rw [← Int.natCast_natAbs]; exact_mod_cast hclose _ hmin_mem _ hmax_mem
    have := Finset.min'_le T (T.max' hne) hmax_mem
    rw [abs_le] at h1; omega
  -- T ⊆ {min, max}, card ≤ 2
  have hT_sub : T ⊆ {T.min' hne, T.max' hne} := fun x hx => by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    have := Finset.min'_le T x hx; have := Finset.le_max' T x hx; rw [hconsec] at *; omega
  linarith [Finset.card_le_card hT_sub, Finset.card_le_two (a := T.min' hne) (b := T.max' hne)]

/-- In a finset of integers with pairwise diff ≤ 1 and card = 2, max = min + 1. -/
private lemma close_int_finset_consec {T : Finset ℤ} (hne : T.Nonempty)
    (hclose : ∀ x ∈ T, ∀ y ∈ T, Int.natAbs (x - y) ≤ 1) (hcard : T.card = 2) :
    T.max' hne = T.min' hne + 1 := by
  have hmin_mem := Finset.min'_mem T hne
  have hmax_mem := Finset.max'_mem T hne
  have hne_mm : T.min' hne ≠ T.max' hne := by
    intro heq
    have : T.card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb => by
      have := Finset.min'_le T a ha; have := Finset.le_max' T a ha
      have := Finset.min'_le T b hb; have := Finset.le_max' T b hb; omega
    omega
  have h1 : |(T.min' hne - T.max' hne : ℤ)| ≤ 1 := by
    rw [← Int.natCast_natAbs]; exact_mod_cast hclose _ hmin_mem _ hmax_mem
  have := Finset.min'_le T (T.max' hne) hmax_mem
  rw [abs_le] at h1; omega

/-- Balanced ternary scales have at most 3 k-step multisets for each k.

    **Proof outline** (5.1.2): Suppose there are at least 3 k-step multiset
    types. We may write them as (a₁, b₁, c₁), (a₁, b₁+1, c₁−1), and a third.
    By balancedness, the third must be (a₁+1, b₁, c₁−1) or (a₁−1, b₁+1, c₁).
    In both cases, balancedness implies these three are the only possible
    interval sizes, giving exactly 3. -/
private lemma balanced_ternary_kstep_le_three (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (_htern : isTernary w)
    (k : ℕ) (_hk : 0 < k) (_hk' : k < n) :
    (Necklace.allKStepMultisets w k).toFinset.card ≤ 3 := by
  -- Bridge: multiset count = vector count
  rw [← distinctKStepVectors_card_eq]
  unfold distinctKStepVectors
  set S := (Necklace.allKStepVectors w k).toFinset with hS_def
  -- Every vector in S sums to k
  have hsum : ∀ v ∈ S, v .L + v .m + v .s = ↑k := by
    intro v hv
    simp only [hS_def, List.mem_toFinset, Necklace.allKStepVectors, List.mem_map] at hv
    obtain ⟨i, _, rfl⟩ := hv
    exact kStepVector_total_count_ternary w i k
  -- Any two vectors in S have componentwise diff ≤ 1
  have hclose : ∀ v₁ ∈ S, ∀ v₂ ∈ S, ∀ a : StepSize,
      Int.natAbs (v₁ a - v₂ a) ≤ 1 := by
    intro v₁ hv₁ v₂ hv₂ a
    simp only [hS_def, List.mem_toFinset, Necklace.allKStepVectors, List.mem_map] at hv₁ hv₂
    obtain ⟨i₁, _, rfl⟩ := hv₁; obtain ⟨i₂, _, rfl⟩ := hv₂
    exact balanced_kStepVector_diff w hbal k _hk _hk' i₁ i₂ a
  -- Component-specific close conditions
  have hL_close : ∀ x ∈ S.image (fun v : ZVector StepSize => v .L),
      ∀ y ∈ S.image (fun v : ZVector StepSize => v .L), Int.natAbs (x - y) ≤ 1 := by
    intro x hx y hy
    obtain ⟨v₁, hv₁, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v₂, hv₂, rfl⟩ := Finset.mem_image.mp hy
    exact hclose v₁ hv₁ v₂ hv₂ .L
  have hm_close : ∀ x ∈ S.image (fun v : ZVector StepSize => v .m),
      ∀ y ∈ S.image (fun v : ZVector StepSize => v .m), Int.natAbs (x - y) ≤ 1 := by
    intro x hx y hy
    obtain ⟨v₁, hv₁, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v₂, hv₂, rfl⟩ := Finset.mem_image.mp hy
    exact hclose v₁ hv₁ v₂ hv₂ .m
  -- A vector is determined by its (.L, .m) components (since .s = k - .L - .m)
  set fLm : ZVector StepSize → ℤ × ℤ := fun v => (v .L, v .m) with hfLm_def
  have hfLm_inj : Set.InjOn fLm ↑S := by
    intro v₁ hv₁ v₂ hv₂ h
    simp only [hfLm_def, Prod.mk.injEq] at h
    have h1 := hsum v₁ (Finset.mem_coe.mp hv₁)
    have h2 := hsum v₂ (Finset.mem_coe.mp hv₂)
    funext a; cases a with | L => exact h.1 | m => exact h.2 | s => linarith
  -- L and m value sets
  set L_vals := S.image (fun v : ZVector StepSize => v .L)
  set m_vals := S.image (fun v : ZVector StepSize => v .m)
  have hL_card : L_vals.card ≤ 2 := close_int_finset_card_le_two L_vals hL_close
  have hm_card : m_vals.card ≤ 2 := close_int_finset_card_le_two m_vals hm_close
  -- S.card ≤ L_vals.card * m_vals.card (via injective projection into product)
  have hS_le_prod : S.card ≤ L_vals.card * m_vals.card := by
    calc S.card = (S.image fLm).card := (Finset.card_image_of_injOn hfLm_inj).symm
      _ ≤ (L_vals ×ˢ m_vals).card := Finset.card_le_card fun p hp => by
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
          exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hv, Finset.mem_image_of_mem _ hv⟩
      _ = L_vals.card * m_vals.card := Finset.card_product L_vals m_vals
  -- If product ≤ 3, done
  by_contra hS_gt; push_neg at hS_gt
  -- S.card ≥ 4, so L * m ≥ 4, but L * m ≤ 2 * 2 = 4, so both = 2
  have hprod_eq : L_vals.card * m_vals.card = 4 := by
    have hle : L_vals.card * m_vals.card ≤ 4 :=
      calc L_vals.card * m_vals.card ≤ 2 * 2 := Nat.mul_le_mul hL_card hm_card
        _ = 4 := by norm_num
    omega
  have hL_eq2 : L_vals.card = 2 := by
    interval_cases L_vals.card <;> omega
  have hm_eq2 : m_vals.card = 2 := by rw [hL_eq2] at hprod_eq; omega
  have hL_ne : L_vals.Nonempty := Finset.card_pos.mp (by omega)
  have hm_ne : m_vals.Nonempty := Finset.card_pos.mp (by omega)
  -- Consecutive: max = min + 1
  have hl_c := close_int_finset_consec hL_ne hL_close hL_eq2
  have hm_c := close_int_finset_consec hm_ne hm_close hm_eq2
  -- S.image fLm = L_vals ×ˢ m_vals (both have card 4)
  have himg_eq : S.image fLm = L_vals ×ˢ m_vals := by
    apply Finset.eq_of_subset_of_card_le
    · intro p hp
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hv, Finset.mem_image_of_mem _ hv⟩
    · rw [Finset.card_product, hL_eq2, hm_eq2, Finset.card_image_of_injOn hfLm_inj]; omega
  -- Both diagonal corners are in the image
  have hc_lo : (L_vals.min' hL_ne, m_vals.min' hm_ne) ∈ S.image fLm := by
    rw [himg_eq]
    exact Finset.mem_product.mpr ⟨Finset.min'_mem L_vals hL_ne, Finset.min'_mem m_vals hm_ne⟩
  have hc_hi : (L_vals.max' hL_ne, m_vals.max' hm_ne) ∈ S.image fLm := by
    rw [himg_eq]
    exact Finset.mem_product.mpr ⟨Finset.max'_mem L_vals hL_ne, Finset.max'_mem m_vals hm_ne⟩
  -- Extract the vectors at these corners
  obtain ⟨v_lo, hv_lo, hv_lo_eq⟩ := Finset.mem_image.mp hc_lo
  obtain ⟨v_hi, hv_hi, hv_hi_eq⟩ := Finset.mem_image.mp hc_hi
  simp only [hfLm_def, Prod.mk.injEq] at hv_lo_eq hv_hi_eq
  -- Their s-components differ by 2
  have hs_diff : v_lo .s - v_hi .s = 2 := by
    have h1 := hsum v_lo hv_lo; have h2 := hsum v_hi hv_hi
    rw [hv_lo_eq.1, hv_lo_eq.2] at h1
    rw [hv_hi_eq.1, hv_hi_eq.2, hl_c, hm_c] at h2
    linarith
  -- But balance says |s-diff| ≤ 1
  have hs_close := hclose v_lo hv_lo v_hi hv_hi .s
  rw [hs_diff] at hs_close; norm_num at hs_close

/-- All primitive balanced ternary scales are MV3. -/
theorem balanced_primitive_ternary_isMV3 (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (_hprim : Necklace.isPrimitive w)
    (htern : isTernary w) :
    isMV3 w :=
  ⟨htern, fun k hk hk' => balanced_ternary_kstep_le_three w hbal htern k hk hk'⟩

/-- Even-regular scales are not SV3: the `(a + c)`-step comes in only 2 sizes.

    **Proof outline** (5.1.3): The underlying MOS `2aX 2cZ` has only one
    `(a + c)`-step vector `aX + cZ`. The substitution replaces X with
    alternating X/Y; since `a` is odd, the two possible starting parities
    give exactly 2 sizes, not 3. -/
private lemma evenRegular_not_isSV3 (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (h : isEvenRegular w) :
    ¬ isSV3 w := by
  intro ⟨_, hsv3⟩
  obtain ⟨_, _, σ, a, c, ha, hc, ha_odd, _, hn, hcL, hcm, hcs, _, _⟩ := h
  set w' := Necklace.applyPerm σ w
  set k := a + c
  have hbal' : Necklace.isBalanced w' := isBalanced_applyPerm σ w hbal
  have hk_pos : 0 < k := by omega
  have hkn : k < n := by omega
  -- Complementarity at step k = n/2: v(i) + v(i+k) = total count
  have hcomp : ∀ (i : ℕ) (st : StepSize),
      Necklace.kStepVector w' i k st + Necklace.kStepVector w' (i + k) k st =
      ↑(Necklace.count w' st) := by
    intro i st
    have := kStepVector_add w' i k k st
    rw [show k + k = n from by omega, kStepVector_full_cycle] at this; linarith
  -- Balance gives ≤ 1 difference per component
  have hdiff : ∀ i j (st : StepSize), Int.natAbs (Necklace.kStepVector w' i k st -
      Necklace.kStepVector w' j k st) ≤ 1 :=
    fun i j st => balanced_kStepVector_diff w' hbal' k hk_pos hkn i j st
  -- s-count is constant c (even total 2c + balance → no variation)
  have hs_const : ∀ i, Necklace.kStepVector w' i k .s = ↑c := by
    intro i
    have hc_i := hcomp i .s; rw [hcs] at hc_i
    have hd_i := hdiff i (i + k) .s
    have : |(Necklace.kStepVector w' i k .s -
        Necklace.kStepVector w' (i + k) k .s)| ≤ 1 := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hd_i
    rw [abs_le] at this; omega
  -- L-count takes one of 2 values (odd total a + balance → 2*L = a ± 1)
  have hL_vals : ∀ i, 2 * Necklace.kStepVector w' i k .L = ↑a - 1 ∨
                       2 * Necklace.kStepVector w' i k .L = ↑a + 1 := by
    intro i
    have hc_i := hcomp i .L; rw [hcL] at hc_i
    have hd_i := hdiff i (i + k) .L
    have : |(Necklace.kStepVector w' i k .L -
        Necklace.kStepVector w' (i + k) k .L)| ≤ 1 := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hd_i
    rw [abs_le] at this
    have : (↑a : ℤ) % 2 = 1 := by omega
    omega
  -- L-component determines the full vector (s = c, m = k - L - s via component sum)
  have hL_det : ∀ i j, Necklace.kStepVector w' i k .L = Necklace.kStepVector w' j k .L →
      Necklace.kStepVector w' i k = Necklace.kStepVector w' j k := by
    intro i j hLeq
    funext a; cases a with
    | L => exact hLeq
    | s => exact (hs_const i).trans (hs_const j).symm
    | m =>
      have hi := kStepVector_component_sum w' i k; rw [stepSize_sum] at hi
      have hj := kStepVector_component_sum w' j k; rw [stepSize_sum] at hj
      linarith [hs_const i, hs_const j]
  -- Every vector equals one of 2 reference vectors
  have hvec : ∀ i, Necklace.kStepVector w' i k = Necklace.kStepVector w' 0 k ∨
                    Necklace.kStepVector w' i k = Necklace.kStepVector w' k k := by
    intro i
    have hLk := hcomp 0 .L; rw [hcL, show (0 : ℕ) + k = k from by omega] at hLk
    suffices Necklace.kStepVector w' i k .L = Necklace.kStepVector w' 0 k .L ∨
             Necklace.kStepVector w' i k .L = Necklace.kStepVector w' k k .L by
      rcases this with h | h
      · left; exact hL_det i 0 h
      · right; exact hL_det i k h
    rcases hL_vals i with hi | hi <;> rcases hL_vals 0 with h0 | h0 <;>
      [left; right; right; left] <;> omega
  -- Card of distinct vectors ≤ 2
  have hcard : (Necklace.allKStepMultisets w' k).toFinset.card ≤ 2 := by
    rw [← distinctKStepVectors_card_eq]
    calc (Necklace.allKStepVectors w' k).toFinset.card
      ≤ ({Necklace.kStepVector w' 0 k, Necklace.kStepVector w' k k} : Finset _).card :=
        Finset.card_le_card (fun v hv => by
          simp only [Necklace.allKStepVectors, List.mem_toFinset, List.mem_map,
            List.mem_range] at hv
          obtain ⟨i, _, rfl⟩ := hv
          exact (hvec i).elim (fun h => Finset.mem_insert.mpr (Or.inl h))
            (fun h => Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))))
      _ ≤ 2 := le_trans (Finset.card_insert_le _ _) (by simp)
  -- Card for w equals card for w' (permutation invariance), contradicting SV3
  have h3 := hsv3 k hk_pos hkn
  have : (Necklace.allKStepMultisets w k).toFinset.card ≤ 2 := by
    rw [← Necklace.allKStepMultisets_toFinset_card_applyPerm σ]; exact hcard
  linarith

/-- The concrete Fraenkel word `LmLsLmL` of length 7. -/
private def fraenkel7 : TernaryNecklace 7 := fun i =>
  match i.val with
  | 0 => StepSize.L | 1 => StepSize.m | 2 => StepSize.L | 3 => StepSize.s
  | 4 => StepSize.L | 5 => StepSize.m | 6 => StepSize.L | _ => StepSize.s

private lemma fraenkel7_sv3 (k : ℕ) (hk : 0 < k) (hkn : k < 7) :
    (Necklace.allKStepMultisets fraenkel7 k).toFinset.card = 3 := by
  interval_cases k <;> native_decide

/-- Sporadic balanced scales (Fraenkel word `abacaba`) are SV3. -/
private lemma sporadicBalanced_isSV3 (w : TernaryNecklace n)
    (_hprim : Necklace.isPrimitive w) (htern : isTernary w)
    (h : isSporadicBalanced w) :
    isSV3 w := by
  obtain ⟨hn, σ, r, h0, h1, h2, h3, h4, h5, h6⟩ := h
  subst hn
  refine ⟨htern, fun k hk hkn => ?_⟩
  -- Step 1: show w (j + r) = σ.symm (fraenkel7 j) for all j
  have key : ∀ j : ZMod 7, w (j + r) = σ.symm (fraenkel7 j) := by
    intro j; apply σ.injective; simp only [Equiv.apply_symm_apply]
    -- goal: σ (w (j + r)) = fraenkel7 j
    fin_cases j <;> simp_all [fraenkel7] <;> decide
  -- Step 2: derive w = applyPerm σ.symm (fraenkel7 ∘ (· - r))
  have hw_eq : w = fun i => σ.symm (fraenkel7 (i - r)) := by
    funext i; have := key (i - r); rwa [sub_add_cancel] at this
  -- Step 3: use permutation invariance to eliminate σ
  rw [hw_eq, show (fun i => σ.symm (fraenkel7 (i - r))) =
    Necklace.applyPerm σ.symm (fun i => fraenkel7 (i - r)) from rfl,
    Necklace.allKStepMultisets_toFinset_card_applyPerm]
  -- Step 4: use rotation invariance to eliminate r
  rw [show (fun i : ZMod 7 => fraenkel7 (i - r)) =
    (fun i => fraenkel7 (i + (-r))) from by funext i; congr 1; ring,
    allKStepMultisets_toFinset_card_rotate]
  -- Step 5: compute for the concrete Fraenkel word
  exact fraenkel7_sv3 k hk hkn

/-- A balanced primitive ternary scale is SV3 iff it is not even-regular. -/
theorem balanced_sv3_iff_not_evenRegular (w : TernaryNecklace n)
    (hbal : Necklace.isBalanced w) (hprim : Necklace.isPrimitive w)
    (htern : isTernary w) :
    isSV3 w ↔ ¬ isEvenRegular w := by
  constructor
  · intro hsv3 he
    exact evenRegular_not_isSV3 w hbal he hsv3
  · intro hne
    rcases balanced_primitive_ternary_classification w hbal hprim htern with h | h | h
    · exact sporadicBalanced_isSV3 w hprim htern h
    · have hodd := h.2.1
      exact as_odd_isSV3 w hprim htern (oddRegular_hasAS w h) hodd
    · exact absurd h hne


end TernaryNecklace
