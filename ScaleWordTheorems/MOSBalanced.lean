import Mathlib.Data.Multiset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import ScaleWordTheorems.Basic
import ScaleWordTheorems.MOS

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

/-! ### Converse: Balanced binary necklaces are MOS -/

/-- From isBalanced, any two k-step subwords have L-count difference ≤ 1 -/
private lemma balanced_L_count_diff_le_one [NeZero n] (w : BinaryNecklace n)
    (hbal : Necklace.isBalanced w) (k : ℕ) (hk_pos : 0 < k) (hk_lt : k < n)
    (i j : Fin n) :
    Int.natAbs (((Necklace.slice w i.val (i.val + k)).count BinaryStep.L : ℤ) -
                ((Necklace.slice w j.val (j.val + k)).count BinaryStep.L : ℤ)) ≤ 1 :=
  hbal k hk_pos hk_lt _ _ BinaryStep.L
    (List.mem_ofFn.mpr ⟨i, rfl⟩) (List.mem_ofFn.mpr ⟨j, rfl⟩)

/-- All L-counts of k-step subwords take at most 2 consecutive values -/
private lemma balanced_L_counts_two_valued [NeZero n] (w : BinaryNecklace n)
    (hbal : Necklace.isBalanced w) (k : ℕ) (hk_pos : 0 < k) (hk_lt : k < n) :
    ∃ v : ℕ, ∀ i : ℕ, i < n →
      (Necklace.slice w i (i + k)).count BinaryStep.L = v ∨
      (Necklace.slice w i (i + k)).count BinaryStep.L = v + 1 := by
  set c₀ := (Necklace.slice w 0 k).count BinaryStep.L
  -- For all i < n, |c_i - c₀| ≤ 1
  have hdiff : ∀ i : ℕ, i < n →
      Int.natAbs (((Necklace.slice w i (i + k)).count BinaryStep.L : ℤ) - ↑c₀) ≤ 1 := by
    intro i hi
    have h := hbal k hk_pos hk_lt
      (Necklace.slice w i (i + k))
      (Necklace.slice w 0 k)
      BinaryStep.L
      (List.mem_ofFn.mpr ⟨⟨i, hi⟩, rfl⟩)
      (List.mem_ofFn.mpr ⟨⟨0, NeZero.pos n⟩, by simp⟩)
    exact h
  -- Case split: does any position have L-count = c₀ - 1?
  by_cases h_lower : ∃ j : ℕ, j < n ∧
      (Necklace.slice w j (j + k)).count BinaryStep.L + 1 = c₀
  · -- Some position has count c₀ - 1; use that count as v
    obtain ⟨j, hj_lt, hj_eq⟩ := h_lower
    use (Necklace.slice w j (j + k)).count BinaryStep.L
    intro i hi
    have hi_diff := hdiff i hi
    -- Also |c_i - c_j| ≤ 1
    have hj_diff := hbal k hk_pos hk_lt
      (Necklace.slice w i (i + k))
      (Necklace.slice w j (j + k))
      BinaryStep.L
      (List.mem_ofFn.mpr ⟨⟨i, hi⟩, rfl⟩)
      (List.mem_ofFn.mpr ⟨⟨j, hj_lt⟩, rfl⟩)
    -- c_i ∈ {c₀-1, c₀, c₀+1} ∩ {c_j-1, c_j, c_j+1} = {c₀-1, c₀} since c_j = c₀-1
    omega
  · -- No position has count < c₀; use c₀ as v
    push_neg at h_lower
    use c₀
    intro i hi
    have hi_diff := hdiff i hi
    have h_not_lower := h_lower i hi
    omega

/-- All k-step multisets of a balanced binary necklace fall into at most 2 classes -/
private lemma balanced_binary_multisets_subset [NeZero n] (w : BinaryNecklace n)
    (hbal : Necklace.isBalanced w) (k : ℕ) (hk_pos : 0 < k) (hk_lt : k < n) :
    ∃ (m₁ m₂ : Multiset BinaryStep),
      ∀ m ∈ (Necklace.allKStepMultisets w k), m = m₁ ∨ m = m₂ := by
  obtain ⟨v, hv⟩ := balanced_L_counts_two_valued w hbal k hk_pos hk_lt
  -- Unpack membership in allKStepMultisets to position indices
  have hmem_unpack : ∀ m : Multiset BinaryStep,
      m ∈ Necklace.allKStepMultisets w k →
      ∃ i : ℕ, i < n ∧ m = ↑(Necklace.slice w i (i + k)) := by
    intro m hm
    simp only [Necklace.allKStepMultisets, Necklace.abelianize, Necklace.allKStepSubwords,
      List.mem_map, List.mem_ofFn] at hm
    obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := hm
    exact ⟨i.val, i.isLt, rfl⟩
  -- Equal L-count + equal length → equal multiset
  have heq_mset : ∀ a b : ℕ,
      (Necklace.slice w a (a + k)).count BinaryStep.L =
      (Necklace.slice w b (b + k)).count BinaryStep.L →
      (↑(Necklace.slice w a (a + k)) : Multiset BinaryStep) =
      ↑(Necklace.slice w b (b + k)) :=
    fun a b hcount => binary_multiset_eq_of_L_count_eq _ _
      (by simp [Necklace.slice_length]) hcount
  -- Case split: all L-counts equal, or some differ
  by_cases h_eq : ∀ i : ℕ, i < n →
      (Necklace.slice w i (i + k)).count BinaryStep.L =
      (Necklace.slice w 0 k).count BinaryStep.L
  · -- All equal: one representative suffices
    refine ⟨↑(Necklace.slice w 0 k), ↑(Necklace.slice w 0 k), fun m hm => ?_⟩
    obtain ⟨i, hi_lt, rfl⟩ := hmem_unpack m hm
    have := heq_mset i 0 (by rw [h_eq i hi_lt, Nat.zero_add])
    simp only [Nat.zero_add] at this
    exact Or.inl this
  · -- Some position j has different L-count
    push_neg at h_eq
    obtain ⟨j, hj_lt, hj⟩ := h_eq
    refine ⟨↑(Necklace.slice w 0 k), ↑(Necklace.slice w j (j + k)), fun m hm => ?_⟩
    obtain ⟨i, hi_lt, rfl⟩ := hmem_unpack m hm
    -- i's L-count matches either 0's or j's
    suffices (Necklace.slice w i (i + k)).count BinaryStep.L =
             (Necklace.slice w 0 k).count BinaryStep.L ∨
             (Necklace.slice w i (i + k)).count BinaryStep.L =
             (Necklace.slice w j (j + k)).count BinaryStep.L by
      rcases this with h | h
      · have := heq_mset i 0 (by rwa [Nat.zero_add])
        simp only [Nat.zero_add] at this
        exact Or.inl this
      · exact Or.inr (heq_mset i j h)
    -- 0 and j have different L-counts, both in {v, v+1}, so they cover both values
    have h0 := hv 0 (NeZero.pos n)
    simp only [Nat.zero_add] at h0
    have hj' := hv j hj_lt
    have hi' := hv i hi_lt
    omega

/-- Theorem: A balanced binary necklace is a MOS. -/
theorem balanced_binary_isMOS [NeZero n] (w : BinaryNecklace n)
    (hbin : BinaryNecklace.isBinary w) (hbal : Necklace.isBalanced w) :
    BinaryNecklace.isMOS w := by
  constructor
  · exact hbin
  · intro k hk_pos hk_lt
    obtain ⟨m₁, m₂, hmem⟩ := balanced_binary_multisets_subset w hbal k hk_pos hk_lt
    calc (Necklace.allKStepMultisets w k).toFinset.card
        ≤ ({m₁, m₂} : Finset _).card := by
          apply Finset.card_le_card
          intro m hm
          rw [List.mem_toFinset] at hm
          rcases hmem m hm with h | h <;> simp [h]
      _ ≤ 2 := le_trans (Finset.card_insert_le m₁ {m₂}) (by simp)
