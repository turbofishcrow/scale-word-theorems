import ScaleWordTheorems.MV3Balance

open BigOperators

namespace TernaryNecklace

variable {n : ℕ} [NeZero n]

/-! ## Classification of All MV3 -/

/-- Balanced at a specific step length `k`: all `k`-step subwords have letter
    counts differing by at most 1 in each coordinate.
    This is the `k`-th component of `Necklace.isBalanced`. -/
private def isBalancedAt (w : TernaryNecklace n) (k : ℕ) : Prop :=
  ∀ (w1 w2 : List StepSize) (a : StepSize),
    w1 ∈ Necklace.allKStepSubwords w k →
    w2 ∈ Necklace.allKStepSubwords w k →
    Int.natAbs ((w1.count a : ℤ) - (w2.count a : ℤ)) ≤ 1

/-- A ternary necklace of length 3 has no adjacent identical letters:
    each letter appears exactly once, so w is injective. -/
private lemma ternary_3_no_adjacent_repeat (w : TernaryNecklace 3)
    (htern : isTernary w) : ∀ p : ZMod 3, w p ≠ w (p + 1) := by
  have hcL : Necklace.count w .L = 1 := by
    have := count_total w; have := count_pos_of_isTernary w htern .L
    have := count_pos_of_isTernary w htern .m
    have := count_pos_of_isTernary w htern .s; omega
  have hcm : Necklace.count w .m = 1 := by
    have := count_total w; have := count_pos_of_isTernary w htern .L
    have := count_pos_of_isTernary w htern .m
    have := count_pos_of_isTernary w htern .s; omega
  have hcs : Necklace.count w .s = 1 := by
    have := count_total w; have := count_pos_of_isTernary w htern .L
    have := count_pos_of_isTernary w htern .m
    have := count_pos_of_isTernary w htern .s; omega
  intro p hp
  -- w p = w (p+1) with p ≠ p+1, so count (w p) ≥ 2
  have hp_ne : p ≠ p + 1 := by
    intro heq
    exact absurd (show (0 : ZMod 3) = 1 from by linear_combination heq) (by decide)
  have hcount_ge : Necklace.count w (w p) ≥ 2 := by
    unfold Necklace.count
    have h1 : p ∈ Finset.filter (fun i => w i = w p) Finset.univ :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    have h2 : p + 1 ∈ Finset.filter (fun i => w i = w p) Finset.univ :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.symm⟩
    calc (Finset.filter (fun i => w i = w p) Finset.univ).card
        ≥ ({p, p + 1} : Finset _).card := by
          apply Finset.card_le_card
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
      _ = 2 := by rw [Finset.card_pair hp_ne]
  -- But each letter count = 1, contradiction
  cases hw : w p with
  | L => rw [hw] at hcount_ge; omega
  | m => rw [hw] at hcount_ge; omega
  | s => rw [hw] at hcount_ge; omega

/-- An MV3 necklace of length 4 has no adjacent identical letters.
    If w(p) = w(p+1), then the 4 two-step multisets are all distinct
    ({a,a}, {a,b}, {b,c}, {a,c}), contradicting the MV3 bound of ≤ 3. -/
private lemma mv3_4_no_adjacent_repeat (w : TernaryNecklace 4)
    (hmv3 : isMV3 w) : ∀ p : ZMod 4, w p ≠ w (p + 1) := by
  intro p hp
  have htern := hmv3.1
  have hmv3_2 := hmv3.2 2 (by omega) (by omega : (2 : ℕ) < 4)
  -- count facts
  have htotal := count_total w
  have hcL := count_pos_of_isTernary w htern .L
  have hcm := count_pos_of_isTernary w htern .m
  have hcs := count_pos_of_isTernary w htern .s
  -- w p appears at least twice (at p and p+1), so count = 2
  have hp_ne : p ≠ p + 1 := by
    intro heq
    exact absurd (show (0 : ZMod 4) = 1 from by linear_combination heq) (by decide)
  have hcount_ge : Necklace.count w (w p) ≥ 2 := by
    unfold Necklace.count
    calc (Finset.filter (fun i => w i = w p) Finset.univ).card
        ≥ ({p, p + 1} : Finset _).card := by
          apply Finset.card_le_card
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.symm⟩
      _ = 2 := Finset.card_pair hp_ne
  have hcount_le : Necklace.count w (w p) ≤ 2 := by
    cases hw : w p with
    | L => omega
    | m => omega
    | s => omega
  have hcount_eq : Necklace.count w (w p) = 2 := le_antisymm hcount_le hcount_ge
  -- w(p+2) ≠ w(p): otherwise count ≥ 3
  have hp2_ne_p : p + 2 ≠ p := by
    intro heq
    exact absurd (show (2 : ZMod 4) = 0 from by linear_combination heq) (by decide)
  have hp2_ne_p1 : p + 2 ≠ p + 1 := by
    intro heq
    exact absurd (show (2 : ZMod 4) = 1 from by linear_combination heq) (by decide)
  have hw2 : w (p + 2) ≠ w p := by
    intro heq2
    have : Necklace.count w (w p) ≥ 3 := by
      unfold Necklace.count
      calc (Finset.filter (fun i => w i = w p) Finset.univ).card
          ≥ ({p, p + 1, p + 2} : Finset _).card := by
            apply Finset.card_le_card
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.symm⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq2⟩
        _ = 3 := by
            have h1 : p ∉ ({p + 1, p + 2} : Finset _) := by
              simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
              exact ⟨hp_ne, hp2_ne_p.symm⟩
            have h2 : p + 1 ∉ ({p + 2} : Finset _) := by
              simp only [Finset.mem_singleton]; exact hp2_ne_p1.symm
            rw [Finset.card_insert_eq_ite, if_neg h1, Finset.card_insert_eq_ite, if_neg h2,
                Finset.card_singleton]
    omega
  -- w(p+3) ≠ w(p): otherwise count ≥ 3
  have hp3_ne_p : p + 3 ≠ p := by
    intro heq
    exact absurd (show (3 : ZMod 4) = 0 from by linear_combination heq) (by decide)
  have hp3_ne_p1 : p + 3 ≠ p + 1 := by
    intro heq
    exact absurd (show (3 : ZMod 4) = 1 from by linear_combination heq) (by decide)
  have hw3 : w (p + 3) ≠ w p := by
    intro heq3
    have : Necklace.count w (w p) ≥ 3 := by
      unfold Necklace.count
      calc (Finset.filter (fun i => w i = w p) Finset.univ).card
          ≥ ({p, p + 1, p + 3} : Finset _).card := by
            apply Finset.card_le_card
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.symm⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq3⟩
        _ = 3 := by
            have h1 : p ∉ ({p + 1, p + 3} : Finset _) := by
              simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
              exact ⟨hp_ne, hp3_ne_p.symm⟩
            have h2 : p + 1 ∉ ({p + 3} : Finset _) := by
              simp only [Finset.mem_singleton]; exact hp3_ne_p1.symm
            rw [Finset.card_insert_eq_ite, if_neg h1, Finset.card_insert_eq_ite, if_neg h2,
                Finset.card_singleton]
    omega
  -- w(p+2) ≠ w(p+3): otherwise two letters each have count 2, total ≥ 5 > 4
  have hw23 : w (p + 2) ≠ w (p + 3) := by
    intro heq23
    -- w(p+2) = w(p+3) = b, w p = w(p+1) = a, a ≠ b
    -- count(a) = 2, count(b) ≥ 2, plus third letter ≥ 1 → total ≥ 5
    have hp2_ne_p3 : p + 2 ≠ p + 3 := by
      intro heq
      exact absurd (show (2 : ZMod 4) = 3 from by linear_combination heq) (by decide)
    have hcount_b_ge : Necklace.count w (w (p + 2)) ≥ 2 := by
      unfold Necklace.count
      calc (Finset.filter (fun i => w i = w (p + 2)) Finset.univ).card
          ≥ ({p + 2, p + 3} : Finset _).card := by
            apply Finset.card_le_card
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq23.symm⟩
        _ = 2 := Finset.card_pair hp2_ne_p3
    -- Two letters each ≥ 2, third ≥ 1, total ≥ 5 > 4
    cases hw : w p with
    | L =>
      cases hw2' : w (p + 2) with
      | L => exact hw2 (hw2'.trans hw.symm)
      | m => rw [hw] at hcount_eq; rw [hw2'] at hcount_b_ge; omega
      | s => rw [hw] at hcount_eq; rw [hw2'] at hcount_b_ge; omega
    | m =>
      cases hw2' : w (p + 2) with
      | L => rw [hw] at hcount_eq; rw [hw2'] at hcount_b_ge; omega
      | m => exact hw2 (hw2'.trans hw.symm)
      | s => rw [hw] at hcount_eq; rw [hw2'] at hcount_b_ge; omega
    | s =>
      cases hw2' : w (p + 2) with
      | L => rw [hw] at hcount_eq; rw [hw2'] at hcount_b_ge; omega
      | m => rw [hw] at hcount_eq; rw [hw2'] at hcount_b_ge; omega
      | s => exact hw2 (hw2'.trans hw.symm)
  -- Now build 4 distinct 2-step multisets, contradicting ≤ 3
  -- p + 3 + 1 = p in ZMod 4
  have hp4 : p + 3 + 1 = p := by
    have h4 : (4 : ZMod 4) = 0 := by decide
    linear_combination h4
  -- The four 2-step multisets
  let m₀ := Necklace.abelianize (Necklace.slice w p.val (p.val + 2))
  let m₁ := Necklace.abelianize (Necklace.slice w (p + 1).val ((p + 1).val + 2))
  let m₂ := Necklace.abelianize (Necklace.slice w (p + 2).val ((p + 2).val + 2))
  let m₃ := Necklace.abelianize (Necklace.slice w (p + 3).val ((p + 3).val + 2))
  -- Decompose slices using slice_two
  have hm₀ : m₀ = Multiset.ofList [w p, w (p + 1)] := by
    show Necklace.abelianize _ = _
    rw [slice_two]; simp [Necklace.abelianize]
  have hm₁ : m₁ = Multiset.ofList [w (p + 1), w (p + 2)] := by
    show Necklace.abelianize _ = _
    rw [slice_two]; simp [Necklace.abelianize]; ring_nf
  have hm₂ : m₂ = Multiset.ofList [w (p + 2), w (p + 3)] := by
    show Necklace.abelianize _ = _
    rw [slice_two]; simp [Necklace.abelianize]; ring_nf
  have hm₃ : m₃ = Multiset.ofList [w (p + 3), w p] := by
    show Necklace.abelianize _ = _
    rw [slice_two]; simp [Necklace.abelianize, hp4]
  -- Pairwise distinctness via counts
  -- Let a = w p. count(a) in m₀,m₁,m₂,m₃ = 2,1,0,1
  -- For m₁ vs m₃: use count(w(p+2)) = 1 vs 0
  have hne01 : m₀ ≠ m₁ := by
    apply multiset_ne_of_count_ne _ _ (w p)
    rw [hm₀, hm₁]
    simp only [Multiset.coe_count, List.count_cons, List.count_nil]
    simp [hp.symm, hw2]
  have hne02 : m₀ ≠ m₂ := by
    apply multiset_ne_of_count_ne _ _ (w p)
    rw [hm₀, hm₂]
    simp only [Multiset.coe_count, List.count_cons, List.count_nil]
    simp [hp.symm, hw2, hw3]
  have hne03 : m₀ ≠ m₃ := by
    apply multiset_ne_of_count_ne _ _ (w p)
    rw [hm₀, hm₃]
    simp only [Multiset.coe_count, List.count_cons, List.count_nil]
    simp [hp.symm, hw3]
  have hne12 : m₁ ≠ m₂ := by
    apply multiset_ne_of_count_ne _ _ (w p)
    rw [hm₁, hm₂]
    simp only [Multiset.coe_count, List.count_cons, List.count_nil]
    simp [hp.symm, hw2, hw3]
  have hne13 : m₁ ≠ m₃ := by
    apply multiset_ne_of_count_ne _ _ (w (p + 2))
    rw [hm₁, hm₃]
    simp only [Multiset.coe_count, List.count_cons, List.count_nil]
    simp [hp.symm, hw2.symm, hw23.symm]
  have hne23 : m₂ ≠ m₃ := by
    apply multiset_ne_of_count_ne _ _ (w p)
    rw [hm₂, hm₃]
    simp only [Multiset.coe_count, List.count_cons, List.count_nil]
    simp [hw2, hw3]
  -- Build a 4-element subset of toFinset
  have hmem₀ : m₀ ∈ (Necklace.allKStepMultisets w 2).toFinset :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨_, List.mem_ofFn.mpr ⟨⟨p.val, ZMod.val_lt p⟩, rfl⟩, rfl⟩)
  have hmem₁ : m₁ ∈ (Necklace.allKStepMultisets w 2).toFinset :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨_, List.mem_ofFn.mpr ⟨⟨(p+1).val, ZMod.val_lt _⟩, rfl⟩, rfl⟩)
  have hmem₂ : m₂ ∈ (Necklace.allKStepMultisets w 2).toFinset :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨_, List.mem_ofFn.mpr ⟨⟨(p+2).val, ZMod.val_lt _⟩, rfl⟩, rfl⟩)
  have hmem₃ : m₃ ∈ (Necklace.allKStepMultisets w 2).toFinset :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨_, List.mem_ofFn.mpr ⟨⟨(p+3).val, ZMod.val_lt _⟩, rfl⟩, rfl⟩)
  have h4 : ({m₀, m₁, m₂, m₃} : Finset _) ⊆ (Necklace.allKStepMultisets w 2).toFinset := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> assumption
  have hcard4 : ({m₀, m₁, m₂, m₃} : Finset _).card = 4 := by
    simp only [Finset.card_insert_eq_ite, Finset.mem_insert, Finset.mem_singleton]
    simp only [hne01, hne02, hne03, hne12, hne13, hne23,
      or_self, ite_false, Finset.card_singleton]
  have : (Necklace.allKStepMultisets w 2).toFinset.card ≥ 4 :=
    calc (Necklace.allKStepMultisets w 2).toFinset.card
        ≥ ({m₀, m₁, m₂, m₃} : Finset _).card := Finset.card_le_card h4
      _ = 4 := hcard4
  omega

/-- If no two adjacent positions have the same letter, then the necklace
    is balanced at step 2: each letter appears 0 or 1 times in every
    2-step subword, so count differences are ≤ 1. -/
private lemma balanced_at_2_of_no_adjacent_repeat (w : TernaryNecklace n)
    (h : ∀ p : ZMod n, w p ≠ w (p + 1)) : isBalancedAt w 2 := by
  intro w1 w2 a hw1 hw2
  rw [Necklace.allKStepSubwords, List.mem_ofFn] at hw1 hw2
  obtain ⟨i, rfl⟩ := hw1; obtain ⟨j, rfl⟩ := hw2
  -- Each slice [w(m), w(m+1)] has the two elements distinct (from h),
  -- so the count of any letter in each slice is ≤ 1.
  suffices hbound : ∀ m : Fin n, (Necklace.slice w m.val (m.val + 2)).count a ≤ 1 by
    have := hbound i; have := hbound j; omega
  intro m
  -- Decompose slice into [w(m), w(m+1)]
  have hdecomp : Necklace.slice w m.val (m.val + 2) =
      w (↑m.val : ZMod n) :: Necklace.slice w (m.val + 1) (m.val + 2) :=
    slice_shift_decompose w m.val 2 (by omega)
  have hdecomp2 : Necklace.slice w (m.val + 1) (m.val + 2) =
      w (↑(m.val + 1) : ZMod n) :: Necklace.slice w (m.val + 2) (m.val + 2) :=
    slice_shift_decompose w (m.val + 1) 1 (by omega)
  have hempty : Necklace.slice w (m.val + 2) (m.val + 2) = [] := by
    simp [Necklace.slice, List.range_zero]
  rw [hdecomp, hdecomp2, hempty]
  -- Goal: [w ↑m.val, w ↑(m.val + 1)].count a ≤ 1
  simp only [List.count_cons, List.count_nil]
  have hdistinct := h (↑m.val : ZMod n)
  -- w ↑m.val ≠ w (↑m.val + 1), and ↑(m.val + 1) = ↑m.val + 1
  have hcast : (↑(m.val + 1) : ZMod n) = (↑m.val : ZMod n) + 1 := by push_cast; ring
  rw [hcast]
  by_cases ha1 : w (↑m.val : ZMod n) = a <;> by_cases ha2 : w ((↑m.val : ZMod n) + 1) = a
  · exact absurd (ha1.trans ha2.symm) hdistinct
  · simp [ha1, ha2]
  · simp [ha1, ha2]
  · simp [ha1, ha2]

/-- Lower bound: MV3 + ¬balanced-at-2 forces n ≥ 5.
    At n ≤ 2 the word can't be ternary; at n = 3 and n = 4, every MV3 word
    is balanced at step 2. -/
private lemma mv3_not_balanced_at_2_n_ge_5 (w : TernaryNecklace n)
    (hmv3 : isMV3 w) (h2 : ¬ isBalancedAt w 2) :
    n ≥ 5 := by
  have hge3 := ternary_length_ge_three w hmv3.1
  by_contra hlt; push_neg at hlt
  interval_cases n
  · exact h2 (balanced_at_2_of_no_adjacent_repeat w (ternary_3_no_adjacent_repeat w hmv3.1))
  · exact h2 (balanced_at_2_of_no_adjacent_repeat w (mv3_4_no_adjacent_repeat w hmv3))

/-- MV3 + ¬balanced-at-2 + n ≥ 6 implies translational period 5:
    w(i) = w(i + 5) for all positions i.

    The proof establishes transition rules from the 2-step multiset structure
    (≤ 3 distinct multisets including {a,a} from the adjacent repeat),
    then uses MV3 at k = 3, 4 to eliminate alternatives, forcing the
    word to be a power of a 5-letter pattern aacbc. -/
-- Generic helper: if 4 distinct k-step multisets exist, the word is not MV3.
private lemma four_distinct_kstep_absurd (w : TernaryNecklace n)
    (hmv3_k : (Necklace.allKStepMultisets w k).toFinset.card ≤ 3)
    (i₁ i₂ i₃ i₄ : Fin n)
    (hne12 : Necklace.abelianize (Necklace.slice w i₁.val (i₁.val + k)) ≠
             Necklace.abelianize (Necklace.slice w i₂.val (i₂.val + k)))
    (hne13 : Necklace.abelianize (Necklace.slice w i₁.val (i₁.val + k)) ≠
             Necklace.abelianize (Necklace.slice w i₃.val (i₃.val + k)))
    (hne14 : Necklace.abelianize (Necklace.slice w i₁.val (i₁.val + k)) ≠
             Necklace.abelianize (Necklace.slice w i₄.val (i₄.val + k)))
    (hne23 : Necklace.abelianize (Necklace.slice w i₂.val (i₂.val + k)) ≠
             Necklace.abelianize (Necklace.slice w i₃.val (i₃.val + k)))
    (hne24 : Necklace.abelianize (Necklace.slice w i₂.val (i₂.val + k)) ≠
             Necklace.abelianize (Necklace.slice w i₄.val (i₄.val + k)))
    (hne34 : Necklace.abelianize (Necklace.slice w i₃.val (i₃.val + k)) ≠
             Necklace.abelianize (Necklace.slice w i₄.val (i₄.val + k))) :
    False := by
  let m₁ := Necklace.abelianize (Necklace.slice w i₁.val (i₁.val + k))
  let m₂ := Necklace.abelianize (Necklace.slice w i₂.val (i₂.val + k))
  let m₃ := Necklace.abelianize (Necklace.slice w i₃.val (i₃.val + k))
  let m₄ := Necklace.abelianize (Necklace.slice w i₄.val (i₄.val + k))
  have hmem₁ : m₁ ∈ (Necklace.allKStepMultisets w k).toFinset :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨_, List.mem_ofFn.mpr ⟨i₁, rfl⟩, rfl⟩)
  have hmem₂ : m₂ ∈ (Necklace.allKStepMultisets w k).toFinset :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨_, List.mem_ofFn.mpr ⟨i₂, rfl⟩, rfl⟩)
  have hmem₃ : m₃ ∈ (Necklace.allKStepMultisets w k).toFinset :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨_, List.mem_ofFn.mpr ⟨i₃, rfl⟩, rfl⟩)
  have hmem₄ : m₄ ∈ (Necklace.allKStepMultisets w k).toFinset :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨_, List.mem_ofFn.mpr ⟨i₄, rfl⟩, rfl⟩)
  have h4 : ({m₁, m₂, m₃, m₄} : Finset _) ⊆ (Necklace.allKStepMultisets w k).toFinset := by
    intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> assumption
  have hcard4 : ({m₁, m₂, m₃, m₄} : Finset _).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp; exact ⟨hne12, hne13, hne14⟩),
        Finset.card_insert_of_notMem (by simp; exact ⟨hne23, hne24⟩),
        Finset.card_pair hne34]
  have : (Necklace.allKStepMultisets w k).toFinset.card ≥ 4 :=
    calc (Necklace.allKStepMultisets w k).toFinset.card
        ≥ ({m₁, m₂, m₃, m₄} : Finset _).card := Finset.card_le_card h4
      _ = 4 := hcard4
  omega

private lemma mv3_translational_period_5 (w : TernaryNecklace n)
    (hmv3 : isMV3 w) (h2 : ¬ isBalancedAt w 2) (hn : n ≥ 6) :
    ∀ i : ZMod n, w i = w (i + 5) := by
  have htern := hmv3.1
  have hmv3_k := hmv3.2
  have hmv3_2 := hmv3_k 2 (by omega) (by omega)
  have hmv3_3 := hmv3_k 3 (by omega) (by omega)
  have hmv3_4 := hmv3_k 4 (by omega) (by omega)
  -- Step 1: Get adjacent repeat
  have hadj : ∃ p : ZMod n, w p = w (p + 1) := by
    by_contra hall; push_neg at hall
    exact h2 (balanced_at_2_of_no_adjacent_repeat w hall)
  obtain ⟨p, hp⟩ := hadj
  -- Name the repeated letter
  set a := w p with ha_def
  -- Step 2: w(p+2) ≠ a. If w(p+2) = a, then "aaa" appears. Combined with
  -- b,c letters (ternarity) giving other 3-step multisets, we get ≥4 distinct.
  have hw2 : w (p + 2) ≠ a := by sorry
  set c := w (p + 2) with hc_def
  -- Step 3: Determine w(p+3). It must be the third letter (not a, not c).
  have hw3_ne_a : w (p + 3) ≠ a := by sorry
  have hw3_ne_c : w (p + 3) ≠ c := by sorry
  set b := w (p + 3) with hb_def
  have hab : a ≠ b := Ne.symm hw3_ne_a
  have hac : a ≠ c := Ne.symm hw2
  have hbc : b ≠ c := hw3_ne_c
  -- Step 4: Compute w(p+4) and w(p+5)
  have hw4 : w (p + 4) = c := by sorry
  have hw5 : w (p + 5) = a := by sorry
  -- Step 5: Establish the 5 deterministic transition rules.
  -- These hold at ALL positions (not just near p) because they follow from
  -- the global MV3 constraints on 2-, 3-, and 4-step multisets.
  -- Transition 1: "aa" → c (no "aaa" at k=3)
  have htrans_aa : ∀ q : ZMod n, w q = a → w (q + 1) = a → w (q + 2) = c := by sorry
  -- Transition 2: "ac" → b (k=4 argument)
  have htrans_ac : ∀ q : ZMod n, w q = a → w (q + 1) = c → w (q + 2) = b := by sorry
  -- Transition 3: "cb" → c (only valid 2-step multiset after b is {b,c})
  have htrans_cb : ∀ q : ZMod n, w q = c → w (q + 1) = b → w (q + 2) = c := by sorry
  -- Transition 4: "bc" → a (no "bcb" at k=3)
  have htrans_bc : ∀ q : ZMod n, w q = b → w (q + 1) = c → w (q + 2) = a := by sorry
  -- Transition 5: "ca" → a (no "cac" at k=3)
  have htrans_ca : ∀ q : ZMod n, w q = c → w (q + 1) = a → w (q + 2) = a := by sorry
  -- Step 6: Every consecutive pair is one of the 5 automaton states.
  -- This follows from the 2-step multiset constraint: {a,a}, {a,c}, {b,c} only.
  have hpair : ∀ q : ZMod n,
      (w q = a ∧ w (q+1) = a) ∨ (w q = a ∧ w (q+1) = c) ∨
      (w q = c ∧ w (q+1) = a) ∨ (w q = c ∧ w (q+1) = b) ∨
      (w q = b ∧ w (q+1) = c) := by sorry
  -- Step 7: The automaton is deterministic — w(q+2) depends only on (w(q), w(q+1)).
  have hdeterm : ∀ (q r : ZMod n), w q = w r → w (q+1) = w (r+1) →
      w (q+2) = w (r+2) := by
    intro q r hqr hqr1
    rcases hpair q with ⟨h1, h2'⟩ | ⟨h1, h2'⟩ | ⟨h1, h2'⟩ | ⟨h1, h2'⟩ | ⟨h1, h2'⟩ <;>
    { have hr1 := hqr.symm.trans h1; have hr2 := hqr1.symm.trans h2'
      first
      | exact (htrans_aa q h1 h2').trans (htrans_aa r hr1 hr2).symm
      | exact (htrans_ac q h1 h2').trans (htrans_ac r hr1 hr2).symm
      | exact (htrans_ca q h1 h2').trans (htrans_ca r hr1 hr2).symm
      | exact (htrans_cb q h1 h2').trans (htrans_cb r hr1 hr2).symm
      | exact (htrans_bc q h1 h2').trans (htrans_bc r hr1 hr2).symm }
  -- Step 8: w(p + j + 5) = w(p + j) for all j, by strong induction.
  -- Base: j=0 from hw5, j=1 from the transition rules applied at p+5.
  -- Inductive step (j ≥ 2): the pair (w(p+j+3), w(p+j+4)) = (w(p+j-2), w(p+j-1))
  -- by IH, and hdeterm gives w(p+j+5) = w(p+j).
  have hshift : ∀ (j : ℕ), w (p + (↑j : ZMod n) + 5) = w (p + (↑j : ZMod n)) := by
    intro j; induction j using Nat.strongRecOn with
    | _ j ih =>
      match j with
      | 0 =>
        simp only [Nat.cast_zero, add_zero]
        rw [show p + (5 : ZMod n) = p + 5 from by ring]
        rw [hw5, ha_def]
      | 1 =>
        simp only [Nat.cast_one]
        rw [show p + (1 : ZMod n) + 5 = p + 6 from by ring,
            show p + (1 : ZMod n) = p + 1 from by ring]
        -- w(p+6) = a (transition from (c,a) at p+4,p+5: ca→a)
        have := htrans_ca (p + 4) hw4 (by rw [show p + 4 + 1 = p + 5 from by ring]; exact hw5)
        rw [show p + 4 + 2 = p + 6 from by ring] at this
        rw [this, hp]
      | j + 2 =>
        have ih0 := ih j (by omega)
        have ih1 := ih (j + 1) (by omega)
        have heq := hdeterm (p + (↑j : ZMod n) + 5) (p + (↑j : ZMod n))
          ih0
          (by rw [show p + (↑j : ZMod n) + 5 + 1 = p + (↑(j+1) : ZMod n) + 5 from by push_cast; ring,
                  show p + (↑j : ZMod n) + 1 = p + (↑(j+1) : ZMod n) from by push_cast; ring]
              exact ih1)
        rw [show p + (↑j : ZMod n) + 5 + 2 = p + (↑(j+2) : ZMod n) + 5 from by push_cast; ring,
            show p + (↑j : ZMod n) + 2 = p + (↑(j+2) : ZMod n) from by push_cast; ring] at heq
        exact heq
  -- Step 9: Convert to ∀ i, w i = w (i + 5)
  intro i
  have := hshift ((i - p).val)
  rw [show p + (↑(i - p).val : ZMod n) = i from by rw [ZMod.natCast_zmod_val]; ring] at this
  exact this.symm

/-- Upper bound: MV3 + ¬balanced-at-2 + primitive forces n ≤ 5.
    The 2-step multiset structure {a,a}, {b,c}, {a,b/c} constrains the word
    to be a power of the 5-letter pattern aacbc. Primitivity eliminates
    higher powers. The Bezout/gcd argument derives a contradiction. -/
private lemma mv3_not_balanced_at_2_prim_n_le_5 (w : TernaryNecklace n)
    (hprim : Necklace.isPrimitive w) (hmv3 : isMV3 w)
    (h2 : ¬ isBalancedAt w 2) :
    n ≤ 5 := by
  by_contra hlt; push_neg at hlt
  -- Get translational period 5
  have hper5 := mv3_translational_period_5 w hmv3 h2 hlt
  -- Iterate: w(j) = w(j + m·5)
  have hiter : ∀ (j m : ℕ), w (↑j : ZMod n) = w (↑(j + m * 5) : ZMod n) := by
    intro j m; induction m with
    | zero => simp
    | succ m ih =>
      rw [show j + (m + 1) * 5 = j + m * 5 + 5 from by ring]
      have h5 := hper5 (↑(j + m * 5) : ZMod n)
      rw [show (↑(j + m * 5) : ZMod n) + (5 : ZMod n) =
          (↑(j + m * 5 + 5) : ZMod n) from by push_cast; ring] at h5
      exact ih.trans h5
  -- Bézout: gcd(5, n) is a translational period
  have hgcd_pos : 0 < Nat.gcd 5 n :=
    Nat.pos_of_ne_zero (by intro h; rw [Nat.gcd_eq_zero_iff] at h; omega)
  have hgcd_lt : Nat.gcd 5 n < n :=
    calc Nat.gcd 5 n ≤ 5 := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left 5 n)
      _ < n := by omega
  have hbez : (↑(Nat.gcd 5 n) : ZMod n) =
      (↑5 : ZMod n) * ((Nat.gcdA 5 n : ℤ) : ZMod n) := by
    have := congr_arg (fun x : ℤ => (x : ZMod n)) (Nat.gcd_eq_gcd_ab 5 n)
    push_cast at this; rwa [ZMod.natCast_self, zero_mul, add_zero] at this
  have hperiodic_gcd : ∀ (i : ZMod n), w i = w (i + ↑(Nat.gcd 5 n)) := by
    intro i
    have hi := hiter (ZMod.val i) (ZMod.val ((Nat.gcdA 5 n : ℤ) : ZMod n))
    rw [ZMod.natCast_zmod_val i] at hi
    rw [hi]; congr 1; push_cast
    rw [ZMod.natCast_zmod_val i,
        ZMod.natCast_zmod_val ((Nat.gcdA 5 n : ℤ) : ZMod n),
        mul_comm, ← hbez]
  have hpLen_le := Necklace.period_length_le_of_translational_period w
    (Nat.gcd 5 n) hgcd_pos hgcd_lt (Nat.gcd_dvd_right 5 n) hperiodic_gcd
  rw [hprim] at hpLen_le
  omega

/-- The core length bound: a primitive MV3 scale that is not balanced at step 2
    must have length exactly 5. Combines the lower and upper bounds. -/
private lemma mv3_not_balanced_at_2_length (w : TernaryNecklace n)
    (hprim : Necklace.isPrimitive w) (hmv3 : isMV3 w)
    (h2 : ¬ isBalancedAt w 2) :
    n = 5 :=
  le_antisymm
    (mv3_not_balanced_at_2_prim_n_le_5 w hprim hmv3 h2)
    (mv3_not_balanced_at_2_n_ge_5 w hmv3 h2)

/-- Every element of ZMod 5 is one of 0, 1, 2, 3, 4. -/
private lemma zmod5_exhaust : ∀ x : ZMod 5, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by decide

/-- Every element of ZMod 5 can be written as p + k for k ∈ {0,...,4}. -/
private lemma zmod5_eq_offsets (i p : ZMod 5) :
    i = p ∨ i = p + 1 ∨ i = p + 2 ∨ i = p + 3 ∨ i = p + 4 := by
  rcases zmod5_exhaust (i - p) with h | h | h | h | h
  · left; exact sub_eq_zero.mp h
  · right; left; rw [sub_eq_iff_eq_add.mp h]; ring
  · right; right; left; rw [sub_eq_iff_eq_add.mp h]; ring
  · right; right; right; left; rw [sub_eq_iff_eq_add.mp h]; ring
  · right; right; right; right; rw [sub_eq_iff_eq_add.mp h]; ring

/-- If every consecutive pair in a length-n necklace contains letter x,
    then the necklace is balanced at step 2. -/
private lemma balanced_at_2_of_all_pairs_contain (w : TernaryNecklace n) (x : StepSize)
    (h : ∀ i : ZMod n, w i = x ∨ w (i + 1) = x) : isBalancedAt w 2 := by
  intro w1 w2 a hw1 hw2
  rw [Necklace.allKStepSubwords, List.mem_ofFn] at hw1 hw2
  obtain ⟨i, rfl⟩ := hw1; obtain ⟨j, rfl⟩ := hw2
  -- Prove bounds on count(a) in each 2-step slice
  suffices hbound : ∀ m : Fin n,
      (a ≠ x → (Necklace.slice w m.val (m.val + 2)).count a ≤ 1) ∧
      (a = x → (Necklace.slice w m.val (m.val + 2)).count a ≥ 1) by
    by_cases hax : a = x
    · have hi_ge := (hbound i).2 hax
      have hj_ge := (hbound j).2 hax
      have hi_le : (Necklace.slice w i.val (i.val + 2)).count a ≤ 2 :=
        le_trans List.count_le_length (by rw [Necklace.slice_length]; omega)
      have hj_le : (Necklace.slice w j.val (j.val + 2)).count a ≤ 2 :=
        le_trans List.count_le_length (by rw [Necklace.slice_length]; omega)
      omega
    · have hi_le := (hbound i).1 hax
      have hj_le := (hbound j).1 hax
      omega
  intro m
  -- Decompose slice into [w(m), w(m+1)] using the same pattern as balanced_at_2_of_no_adjacent_repeat
  have hdecomp : Necklace.slice w m.val (m.val + 2) =
      w (↑m.val : ZMod n) :: Necklace.slice w (m.val + 1) (m.val + 2) :=
    slice_shift_decompose w m.val 2 (by omega)
  have hdecomp2 : Necklace.slice w (m.val + 1) (m.val + 2) =
      w (↑(m.val + 1) : ZMod n) :: Necklace.slice w (m.val + 2) (m.val + 2) :=
    slice_shift_decompose w (m.val + 1) 1 (by omega)
  have hempty : Necklace.slice w (m.val + 2) (m.val + 2) = [] := by
    simp [Necklace.slice, List.range_zero]
  rw [hdecomp, hdecomp2, hempty]
  simp only [List.count_cons, List.count_nil]
  have hcast : (↑(m.val + 1) : ZMod n) = (↑m.val : ZMod n) + 1 := by push_cast; ring
  rw [hcast]
  constructor
  · intro hax
    by_cases ha1 : w (↑m.val : ZMod n) = a <;> by_cases ha2 : w ((↑m.val : ZMod n) + 1) = a
    · exfalso; rcases h (↑m.val : ZMod n) with hm | hm
      · exact hax (ha1.symm.trans hm)
      · exact hax (ha2.symm.trans hm)
    · simp [ha1, ha2]
    · simp [ha1, ha2]
    · simp [ha1, ha2]
  · intro hax
    rcases h (↑m.val : ZMod n) with hm | hm
    · simp [hm, hax]
    · simp [hm, hax]

/-- Ternarity contradiction: if only two letters appear in a length-5 necklace,
    then one letter has count 0, contradicting ternarity. -/
private lemma ternary5_two_letters_absurd (w : TernaryNecklace 5)
    (htern : isTernary w) (a b : StepSize) (hab : a ≠ b)
    (hca : Necklace.count w a ≥ 3) (hcb : Necklace.count w b ≥ 2) : False := by
  have htotal := count_total w
  have hcL := count_pos_of_isTernary w htern .L
  have hcm := count_pos_of_isTernary w htern .m
  have hcs := count_pos_of_isTernary w htern .s
  cases a <;> cases b <;> simp_all <;> omega

/-- In a length-5 MV3 necklace not balanced at step 2, if w(p) = w(p+1),
    then count(w(p)) = 2. The adjacent-repeat letter appears exactly twice. -/
private lemma mv3_5_adj_repeat_count_two (w : TernaryNecklace 5)
    (hmv3 : isMV3 w) (h2 : ¬ isBalancedAt w 2) (p : ZMod 5) (hp : w p = w (p + 1)) :
    Necklace.count w (w p) = 2 := by
  have htern := hmv3.1
  have hmv3_2 := hmv3.2 2 (by omega) (by omega : (2 : ℕ) < 5)
  have htotal := count_total w
  have hcL := count_pos_of_isTernary w htern .L
  have hcm := count_pos_of_isTernary w htern .m
  have hcs := count_pos_of_isTernary w htern .s
  -- p ≠ p+1 in ZMod 5
  have hp_ne : p ≠ p + 1 := by
    intro heq; exact absurd (show (0 : ZMod 5) = 1 from by linear_combination heq) (by decide)
  -- count(w p) ≥ 2
  have hcount_ge : Necklace.count w (w p) ≥ 2 := by
    unfold Necklace.count
    calc (Finset.filter (fun i => w i = w p) Finset.univ).card
        ≥ ({p, p + 1} : Finset _).card := by
          apply Finset.card_le_card
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.symm⟩
      _ = 2 := Finset.card_pair hp_ne
  -- count(w p) ≤ 2 by contradiction: if ≥ 3, a third position holds w p
  have hcount_le : Necklace.count w (w p) ≤ 2 := by
    by_contra hge3; push_neg at hge3
    -- w p appears at ≥ 3 of the 5 positions. Since it's at p, p+1,
    -- the third must be p+2, p+3, or p+4.
    -- Distinctness of ZMod 5 elements
    have hp2_ne_p : p + 2 ≠ p := by
      intro heq; exact absurd (show (2 : ZMod 5) = 0 from by linear_combination heq) (by decide)
    have hp2_ne_p1 : p + 2 ≠ p + 1 := by
      intro heq; exact absurd (show (2 : ZMod 5) = 1 from by linear_combination heq) (by decide)
    have hp3_ne_p : p + 3 ≠ p := by
      intro heq; exact absurd (show (3 : ZMod 5) = 0 from by linear_combination heq) (by decide)
    have hp3_ne_p1 : p + 3 ≠ p + 1 := by
      intro heq; exact absurd (show (3 : ZMod 5) = 1 from by linear_combination heq) (by decide)
    have hp3_ne_p2 : p + 3 ≠ p + 2 := by
      intro heq; exact absurd (show (3 : ZMod 5) = 2 from by linear_combination heq) (by decide)
    have hp4_ne_p : p + 4 ≠ p := by
      intro heq; exact absurd (show (4 : ZMod 5) = 0 from by linear_combination heq) (by decide)
    have hp4_ne_p1 : p + 4 ≠ p + 1 := by
      intro heq; exact absurd (show (4 : ZMod 5) = 1 from by linear_combination heq) (by decide)
    have hp4_ne_p2 : p + 4 ≠ p + 2 := by
      intro heq; exact absurd (show (4 : ZMod 5) = 2 from by linear_combination heq) (by decide)
    have hp4_ne_p3 : p + 4 ≠ p + 3 := by
      intro heq; exact absurd (show (4 : ZMod 5) = 3 from by linear_combination heq) (by decide)
    -- The 5 positions are exactly {p, p+1, p+2, p+3, p+4}
    -- If w(p+2) ≠ w(p) and w(p+3) ≠ w(p) and w(p+4) ≠ w(p), count ≤ 2
    by_cases hw2 : w (p + 2) = w p
    · -- Case: x at p, p+1, p+2 (3 consecutive). Remaining: p+3, p+4 hold non-x values.
      -- Since ternary, at least 2 other letters exist, so w(p+3) ≠ w(p+4).
      -- The 5 multisets {x,x}, {x,x}, {x,a}, {a,b}, {b,x} where a = w(p+3), b = w(p+4)
      -- with a ≠ x, b ≠ x. If a ≠ b these give 4 distinct multisets.
      -- If a = b, only 2 letters used → not ternary.
      have hwa : w (p + 3) ≠ w p := by
        intro heq3
        -- x at p,p+1,p+2,p+3 → count ≥ 4, so other letter count ≤ 1
        -- but ternary needs 2 other letters each ≥ 1, total ≥ 4+2 = 6 > 5
        have : Necklace.count w (w p) ≥ 4 := by
          unfold Necklace.count
          calc (Finset.filter (fun i => w i = w p) Finset.univ).card
              ≥ ({p, p + 1, p + 2, p + 3} : Finset _).card := by
                apply Finset.card_le_card
                intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl | rfl | rfl
                · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
                · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.symm⟩
                · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw2⟩
                · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq3⟩
            _ = 4 := by
                simp only [Finset.card_insert_eq_ite, Finset.mem_insert, Finset.mem_singleton]
                simp only [hp_ne, hp2_ne_p.symm, hp2_ne_p1.symm, hp3_ne_p.symm, hp3_ne_p1.symm,
                  hp3_ne_p2.symm, or_self, ite_false, Finset.card_singleton]
        cases hw : w p <;> simp only [hw] at this <;> omega
      have hwb : w (p + 4) ≠ w p := by
        intro heq4
        have : Necklace.count w (w p) ≥ 4 := by
          unfold Necklace.count
          calc (Finset.filter (fun i => w i = w p) Finset.univ).card
              ≥ ({p, p + 1, p + 2, p + 4} : Finset _).card := by
                apply Finset.card_le_card
                intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl | rfl | rfl
                · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
                · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.symm⟩
                · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw2⟩
                · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq4⟩
            _ = 4 := by
                simp only [Finset.card_insert_eq_ite, Finset.mem_insert, Finset.mem_singleton]
                simp only [hp_ne, hp2_ne_p.symm, hp2_ne_p1.symm, hp4_ne_p.symm, hp4_ne_p1.symm,
                  hp4_ne_p2.symm, or_self, ite_false, Finset.card_singleton]
        cases hw : w p <;> simp only [hw] at this <;> omega
      -- w(p+3) ≠ w(p+4): if equal, only 2 letters → not ternary
      have hab : w (p + 3) ≠ w (p + 4) := by
        intro heq34
        -- w(p+3) appears at p+3 and p+4, so count ≥ 2
        have hcount_wp3 : Necklace.count w (w (p + 3)) ≥ 2 := by
          unfold Necklace.count
          calc (Finset.filter (fun i => w i = w (p + 3)) Finset.univ).card
              ≥ ({p + 3, p + 4} : Finset _).card := by
                apply Finset.card_le_card
                intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl
                · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
                · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq34.symm⟩
            _ = 2 := Finset.card_pair (Ne.symm hp4_ne_p3)
        exact ternary5_two_letters_absurd w htern (w p) (w (p + 3)) (Ne.symm hwa)
          (by omega) hcount_wp3
      -- Now 4 distinct multisets: {x,x},{x,x},{x,a},{a,b},{b,x} at positions p,p+1,p+2,p+3,p+4
      -- Actually: m₀={w(p),w(p+1)}={x,x}, m₁={w(p+1),w(p+2)}={x,x},
      -- m₂={w(p+2),w(p+3)}={x,a}, m₃={w(p+3),w(p+4)}={a,b}, m₄={w(p+4),w(p)}={b,x}
      -- We need 4 distinct among 5. m₀ = m₁ = {x,x}.
      -- m₂ = {x,a} with a≠x. m₃ = {a,b} with a≠x, b≠x, a≠b. m₄ = {b,x} with b≠x.
      -- m₂ ≠ m₀ (count x: 1 vs 2), m₃ ≠ m₀ (count x: 0 vs 2),
      -- m₄ ≠ m₀ (count x: 1 vs 2), m₃ ≠ m₂ (count x: 0 vs 1),
      -- m₃ ≠ m₄ (count a: 1 vs 0 since a≠b), m₂ vs m₄: count a: 1 in m₂, ? in m₄
      -- m₄ = {b,x}. count a in m₄: if a=b impossible since a≠b. So 0. m₂ has 1. Distinct.
      -- So {m₀, m₂, m₃, m₄} are 4 distinct.
      have hp5 : p + 4 + 1 = p := by
        have h5 : (5 : ZMod 5) = 0 := by decide
        linear_combination h5
      let m₀ := Necklace.abelianize (Necklace.slice w p.val (p.val + 2))
      let m₂ := Necklace.abelianize (Necklace.slice w (p + 2).val ((p + 2).val + 2))
      let m₃ := Necklace.abelianize (Necklace.slice w (p + 3).val ((p + 3).val + 2))
      let m₄ := Necklace.abelianize (Necklace.slice w (p + 4).val ((p + 4).val + 2))
      have hm₀ : m₀ = Multiset.ofList [w p, w (p + 1)] := by
        show Necklace.abelianize _ = _; rw [slice_two]; simp [Necklace.abelianize]
      have hm₂ : m₂ = Multiset.ofList [w (p + 2), w (p + 3)] := by
        show Necklace.abelianize _ = _; rw [slice_two]; simp [Necklace.abelianize]; ring_nf
      have hm₃ : m₃ = Multiset.ofList [w (p + 3), w (p + 4)] := by
        show Necklace.abelianize _ = _; rw [slice_two]; simp [Necklace.abelianize]; ring_nf
      have hm₄ : m₄ = Multiset.ofList [w (p + 4), w p] := by
        show Necklace.abelianize _ = _; rw [slice_two]; simp [Necklace.abelianize, hp5]
      have hne02 : m₀ ≠ m₂ := by
        apply multiset_ne_of_count_ne _ _ (w p)
        rw [hm₀, hm₂]; simp only [Multiset.coe_count, List.count_cons, List.count_nil]
        simp [hp.symm, hw2, hwa]
      have hne03 : m₀ ≠ m₃ := by
        apply multiset_ne_of_count_ne _ _ (w p)
        rw [hm₀, hm₃]; simp only [Multiset.coe_count, List.count_cons, List.count_nil]
        simp [hp.symm, hwa, hwb]
      have hne04 : m₀ ≠ m₄ := by
        apply multiset_ne_of_count_ne _ _ (w p)
        rw [hm₀, hm₄]; simp only [Multiset.coe_count, List.count_cons, List.count_nil]
        simp [hp.symm, hwb]
      have hne23 : m₂ ≠ m₃ := by
        apply multiset_ne_of_count_ne _ _ (w p)
        rw [hm₂, hm₃]; simp only [Multiset.coe_count, List.count_cons, List.count_nil]
        simp [hw2, hwa, hwb]
      have hne24 : m₂ ≠ m₄ := by
        apply multiset_ne_of_count_ne _ _ (w (p + 3))
        rw [hm₂, hm₄]; simp only [Multiset.coe_count, List.count_cons, List.count_nil]
        simp [hw2, hwa.symm, hab.symm]
      have hne34 : m₃ ≠ m₄ := by
        apply multiset_ne_of_count_ne _ _ (w p)
        rw [hm₃, hm₄]; simp only [Multiset.coe_count, List.count_cons, List.count_nil]
        simp [hwa, hwb]
      have hmem₀ : m₀ ∈ (Necklace.allKStepMultisets w 2).toFinset :=
        List.mem_toFinset.mpr (List.mem_map.mpr ⟨_, List.mem_ofFn.mpr ⟨⟨p.val, ZMod.val_lt p⟩, rfl⟩, rfl⟩)
      have hmem₂ : m₂ ∈ (Necklace.allKStepMultisets w 2).toFinset :=
        List.mem_toFinset.mpr (List.mem_map.mpr ⟨_, List.mem_ofFn.mpr ⟨⟨(p+2).val, ZMod.val_lt _⟩, rfl⟩, rfl⟩)
      have hmem₃ : m₃ ∈ (Necklace.allKStepMultisets w 2).toFinset :=
        List.mem_toFinset.mpr (List.mem_map.mpr ⟨_, List.mem_ofFn.mpr ⟨⟨(p+3).val, ZMod.val_lt _⟩, rfl⟩, rfl⟩)
      have hmem₄ : m₄ ∈ (Necklace.allKStepMultisets w 2).toFinset :=
        List.mem_toFinset.mpr (List.mem_map.mpr ⟨_, List.mem_ofFn.mpr ⟨⟨(p+4).val, ZMod.val_lt _⟩, rfl⟩, rfl⟩)
      have h4 : ({m₀, m₂, m₃, m₄} : Finset _) ⊆ (Necklace.allKStepMultisets w 2).toFinset := by
        intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl | rfl <;> assumption
      have hcard4 : ({m₀, m₂, m₃, m₄} : Finset _).card = 4 := by
        simp only [Finset.card_insert_eq_ite, Finset.mem_insert, Finset.mem_singleton]
        simp only [hne02, hne03, hne04, hne23, hne24, hne34, or_self, ite_false, Finset.card_singleton]
      have : (Necklace.allKStepMultisets w 2).toFinset.card ≥ 4 :=
        calc (Necklace.allKStepMultisets w 2).toFinset.card
            ≥ ({m₀, m₂, m₃, m₄} : Finset _).card := Finset.card_le_card h4
          _ = 4 := hcard4
      omega
    · by_cases hw3 : w (p + 3) = w p
      · -- Case: x at p, p+1, p+3. Every consecutive pair contains x:
        -- (p,p+1): x,x. (p+1,p+2): x,?. (p+2,p+3): ?,x. (p+3,p+4): x,?. (p+4,p): ?,x.
        -- So balanced_at_2_of_all_pairs_contain applies → contradiction with h2.
        have : ∀ i : ZMod 5, w i = w p ∨ w (i + 1) = w p := by
          intro i
          rcases zmod5_eq_offsets i p with rfl | rfl | rfl | rfl | rfl
          · left; rfl
          · left; exact hp.symm
          · right; show w (p + 2 + 1) = w p; rw [show p + 2 + 1 = p + 3 from by ring]; exact hw3
          · left; exact hw3
          · right; show w (p + 4 + 1) = w p; rw [show p + 4 + 1 = p + 5 from by ring]
            rw [show p + 5 = p + (5 : ZMod 5) from by ring]
            rw [show (5 : ZMod 5) = 0 from by decide]; simp
        exact absurd (balanced_at_2_of_all_pairs_contain w (w p) this) h2
      · by_cases hw4 : w (p + 4) = w p
        · -- Case: x at p, p+1, p+4. Symmetric to x at p, p+1, p+2.
          -- w(p+2) ≠ x, w(p+3) ≠ x. Multisets:
          -- m₀ = {x,x}, m₁ = {x,a}, m₂ = {a,b}, m₃ = {b,x}, m₄ = {x,x}
          -- where a = w(p+2), b = w(p+3), a≠x, b≠x
          have hwa : w (p + 2) ≠ w p := hw2
          have hwb : w (p + 3) ≠ w p := hw3
          have hab : w (p + 2) ≠ w (p + 3) := by
            intro heq23
            -- w(p+2) appears at p+2 and p+3, so count ≥ 2
            have hcount_wp2 : Necklace.count w (w (p + 2)) ≥ 2 := by
              unfold Necklace.count
              calc (Finset.filter (fun i => w i = w (p + 2)) Finset.univ).card
                  ≥ ({p + 2, p + 3} : Finset _).card := by
                    apply Finset.card_le_card
                    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                    rcases hx with rfl | rfl
                    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
                    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq23.symm⟩
                _ = 2 := Finset.card_pair (Ne.symm hp3_ne_p2)
            exact ternary5_two_letters_absurd w htern (w p) (w (p + 2)) (Ne.symm hwa)
              (by omega) hcount_wp2
          -- Build 4 distinct multisets
          have hp5 : p + 4 + 1 = p := by
            have h5 : (5 : ZMod 5) = 0 := by decide
            linear_combination h5
          let m₁ := Necklace.abelianize (Necklace.slice w (p + 1).val ((p + 1).val + 2))
          let m₂ := Necklace.abelianize (Necklace.slice w (p + 2).val ((p + 2).val + 2))
          let m₃ := Necklace.abelianize (Necklace.slice w (p + 3).val ((p + 3).val + 2))
          let m₄ := Necklace.abelianize (Necklace.slice w (p + 4).val ((p + 4).val + 2))
          have hm₁ : m₁ = Multiset.ofList [w (p + 1), w (p + 2)] := by
            show Necklace.abelianize _ = _; rw [slice_two]; simp [Necklace.abelianize]; ring_nf
          have hm₂ : m₂ = Multiset.ofList [w (p + 2), w (p + 3)] := by
            show Necklace.abelianize _ = _; rw [slice_two]; simp [Necklace.abelianize]; ring_nf
          have hm₃ : m₃ = Multiset.ofList [w (p + 3), w (p + 4)] := by
            show Necklace.abelianize _ = _; rw [slice_two]; simp [Necklace.abelianize]; ring_nf
          have hm₄ : m₄ = Multiset.ofList [w (p + 4), w p] := by
            show Necklace.abelianize _ = _; rw [slice_two]; simp [Necklace.abelianize, hp5]
          -- m₁ = {x, a}, m₂ = {a, b}, m₃ = {b, x}, m₄ = {x, x}
          -- Use w(p+1) = w(p) = x, w(p+4) = x
          have hne12 : m₁ ≠ m₂ := by
            apply multiset_ne_of_count_ne _ _ (w p)
            rw [hm₁, hm₂]; simp only [Multiset.coe_count, List.count_cons, List.count_nil]
            simp [hp.symm, hwa, hwb]
          have hne13 : m₁ ≠ m₃ := by
            apply multiset_ne_of_count_ne _ _ (w (p + 2))
            rw [hm₁, hm₃]; simp only [Multiset.coe_count, List.count_cons, List.count_nil]
            simp [hp.symm, hw4, hwa.symm, hab.symm]
          have hne14 : m₁ ≠ m₄ := by
            apply multiset_ne_of_count_ne _ _ (w p)
            rw [hm₁, hm₄]; simp only [Multiset.coe_count, List.count_cons, List.count_nil]
            simp [hp.symm, hwa, hw4]
          have hne23 : m₂ ≠ m₃ := by
            apply multiset_ne_of_count_ne _ _ (w p)
            rw [hm₂, hm₃]; simp only [Multiset.coe_count, List.count_cons, List.count_nil]
            simp [hwa, hwb, hw4]
          have hne24 : m₂ ≠ m₄ := by
            apply multiset_ne_of_count_ne _ _ (w p)
            rw [hm₂, hm₄]; simp only [Multiset.coe_count, List.count_cons, List.count_nil]
            simp [hwa, hwb, hw4]
          have hne34 : m₃ ≠ m₄ := by
            apply multiset_ne_of_count_ne _ _ (w p)
            rw [hm₃, hm₄]; simp only [Multiset.coe_count, List.count_cons, List.count_nil]
            simp [hwb, hw4]
          have hmem₁ : m₁ ∈ (Necklace.allKStepMultisets w 2).toFinset :=
            List.mem_toFinset.mpr (List.mem_map.mpr ⟨_, List.mem_ofFn.mpr ⟨⟨(p+1).val, ZMod.val_lt _⟩, rfl⟩, rfl⟩)
          have hmem₂ : m₂ ∈ (Necklace.allKStepMultisets w 2).toFinset :=
            List.mem_toFinset.mpr (List.mem_map.mpr ⟨_, List.mem_ofFn.mpr ⟨⟨(p+2).val, ZMod.val_lt _⟩, rfl⟩, rfl⟩)
          have hmem₃ : m₃ ∈ (Necklace.allKStepMultisets w 2).toFinset :=
            List.mem_toFinset.mpr (List.mem_map.mpr ⟨_, List.mem_ofFn.mpr ⟨⟨(p+3).val, ZMod.val_lt _⟩, rfl⟩, rfl⟩)
          have hmem₄ : m₄ ∈ (Necklace.allKStepMultisets w 2).toFinset :=
            List.mem_toFinset.mpr (List.mem_map.mpr ⟨_, List.mem_ofFn.mpr ⟨⟨(p+4).val, ZMod.val_lt _⟩, rfl⟩, rfl⟩)
          have h4set : ({m₁, m₂, m₃, m₄} : Finset _) ⊆ (Necklace.allKStepMultisets w 2).toFinset := by
            intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
            rcases hv with rfl | rfl | rfl | rfl <;> assumption
          have hcard4 : ({m₁, m₂, m₃, m₄} : Finset _).card = 4 := by
            simp only [Finset.card_insert_eq_ite, Finset.mem_insert, Finset.mem_singleton]
            simp only [hne12, hne13, hne14, hne23, hne24, hne34, or_self, ite_false, Finset.card_singleton]
          have : (Necklace.allKStepMultisets w 2).toFinset.card ≥ 4 :=
            calc (Necklace.allKStepMultisets w 2).toFinset.card
                ≥ ({m₁, m₂, m₃, m₄} : Finset _).card := Finset.card_le_card h4set
              _ = 4 := hcard4
          omega
        · -- w(p+2) ≠ w(p), w(p+3) ≠ w(p), w(p+4) ≠ w(p): count = 2, contradiction
          have : Necklace.count w (w p) ≤ 2 := by
            unfold Necklace.count
            have : (Finset.filter (fun i => w i = w p) Finset.univ) ⊆ {p, p + 1} := by
              intro i hi
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
              simp only [Finset.mem_insert, Finset.mem_singleton]
              rcases zmod5_eq_offsets i p with rfl | rfl | rfl | rfl | rfl
              · left; rfl
              · right; rfl
              · exact absurd hi hw2
              · exact absurd hi hw3
              · exact absurd hi hw4
            calc (Finset.filter (fun i => w i = w p) Finset.univ).card
                ≤ ({p, p + 1} : Finset _).card := Finset.card_le_card this
              _ = 2 := Finset.card_pair hp_ne
          omega
  exact le_antisymm hcount_le hcount_ge

/-- At length 5, MV3 + ¬balanced-at-2 forces the XYZYX pattern.

    There are only 3^5 = 243 ternary words of length 5. Among these,
    the MV3 + ¬balanced-at-2 conditions select exactly the S₃ × Z₅
    orbit of LmsmL (the word with step signature 2L 2m 1s in the
    pattern XYZYX). -/
private lemma mv3_5_not_balanced_at_2_xyzyx (w : TernaryNecklace 5)
    (hmv3 : isMV3 w) (h2 : ¬ isBalancedAt w 2) :
    ∃ (σ : Equiv.Perm StepSize) (r : ZMod 5),
      let w' := fun i => σ (w (i + r))
      w' ((0 : ℕ) : ZMod 5) = StepSize.L ∧
      w' ((1 : ℕ) : ZMod 5) = StepSize.m ∧
      w' ((2 : ℕ) : ZMod 5) = StepSize.s ∧
      w' ((3 : ℕ) : ZMod 5) = StepSize.m ∧
      w' ((4 : ℕ) : ZMod 5) = StepSize.L := by
  -- Step 1: Get adjacent repeat from ¬balanced-at-2
  have hadj : ∃ p : ZMod 5, w p = w (p + 1) := by
    by_contra hall; push_neg at hall
    exact h2 (balanced_at_2_of_no_adjacent_repeat w hall)
  obtain ⟨p, hp⟩ := hadj
  -- Step 2: count(w p) = 2
  have hcount2 := mv3_5_adj_repeat_count_two w hmv3 h2 p hp
  have htern := hmv3.1
  have hmv3_2 := hmv3.2 2 (by omega) (by omega : (2 : ℕ) < 5)
  have htotal := count_total w
  have hcL := count_pos_of_isTernary w htern .L
  have hcm := count_pos_of_isTernary w htern .m
  have hcs := count_pos_of_isTernary w htern .s
  -- ZMod 5 distinctness
  have hp2_ne_p : p + 2 ≠ p := by
    intro heq; exact absurd (show (2 : ZMod 5) = 0 from by linear_combination heq) (by decide)
  have hp2_ne_p1 : p + 2 ≠ p + 1 := by
    intro heq; exact absurd (show (2 : ZMod 5) = 1 from by linear_combination heq) (by decide)
  have hp3_ne_p : p + 3 ≠ p := by
    intro heq; exact absurd (show (3 : ZMod 5) = 0 from by linear_combination heq) (by decide)
  have hp3_ne_p1 : p + 3 ≠ p + 1 := by
    intro heq; exact absurd (show (3 : ZMod 5) = 1 from by linear_combination heq) (by decide)
  have hp4_ne_p : p + 4 ≠ p := by
    intro heq; exact absurd (show (4 : ZMod 5) = 0 from by linear_combination heq) (by decide)
  have hp4_ne_p1 : p + 4 ≠ p + 1 := by
    intro heq; exact absurd (show (4 : ZMod 5) = 1 from by linear_combination heq) (by decide)
  -- w(p+2) ≠ w(p): if equal, count ≥ 3
  have hw2 : w (p + 2) ≠ w p := by
    intro heq2
    have : Necklace.count w (w p) ≥ 3 := by
      unfold Necklace.count
      calc (Finset.filter (fun i => w i = w p) Finset.univ).card
          ≥ ({p, p + 1, p + 2} : Finset _).card := by
            apply Finset.card_le_card
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.symm⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq2⟩
        _ = 3 := by
            have h1 : p ∉ ({p + 1, p + 2} : Finset _) := by
              simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
              constructor
              · intro heq; exact absurd (show (0 : ZMod 5) = 1 from by linear_combination heq) (by decide)
              · exact hp2_ne_p.symm
            have h2 : p + 1 ∉ ({p + 2} : Finset _) := by
              simp only [Finset.mem_singleton]; exact hp2_ne_p1.symm
            rw [Finset.card_insert_eq_ite, if_neg h1, Finset.card_insert_eq_ite, if_neg h2,
                Finset.card_singleton]
    omega
  -- w(p+3) ≠ w(p): same argument
  have hw3 : w (p + 3) ≠ w p := by
    intro heq3
    have : Necklace.count w (w p) ≥ 3 := by
      unfold Necklace.count
      calc (Finset.filter (fun i => w i = w p) Finset.univ).card
          ≥ ({p, p + 1, p + 3} : Finset _).card := by
            apply Finset.card_le_card
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.symm⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq3⟩
        _ = 3 := by
            have h1 : p ∉ ({p + 1, p + 3} : Finset _) := by
              simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
              constructor
              · intro heq; exact absurd (show (0 : ZMod 5) = 1 from by linear_combination heq) (by decide)
              · exact hp3_ne_p.symm
            have h2 : p + 1 ∉ ({p + 3} : Finset _) := by
              simp only [Finset.mem_singleton]; exact hp3_ne_p1.symm
            rw [Finset.card_insert_eq_ite, if_neg h1, Finset.card_insert_eq_ite, if_neg h2,
                Finset.card_singleton]
    omega
  -- w(p+4) ≠ w(p): same argument
  have hw4 : w (p + 4) ≠ w p := by
    intro heq4
    have : Necklace.count w (w p) ≥ 3 := by
      unfold Necklace.count
      calc (Finset.filter (fun i => w i = w p) Finset.univ).card
          ≥ ({p, p + 1, p + 4} : Finset _).card := by
            apply Finset.card_le_card
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.symm⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq4⟩
        _ = 3 := by
            have h1 : p ∉ ({p + 1, p + 4} : Finset _) := by
              simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
              constructor
              · intro heq; exact absurd (show (0 : ZMod 5) = 1 from by linear_combination heq) (by decide)
              · exact hp4_ne_p.symm
            have h2 : p + 1 ∉ ({p + 4} : Finset _) := by
              simp only [Finset.mem_singleton]; exact hp4_ne_p1.symm
            rw [Finset.card_insert_eq_ite, if_neg h1, Finset.card_insert_eq_ite, if_neg h2,
                Finset.card_singleton]
    omega
  -- Step 3: w(p+2) = w(p+4)
  have hw24 : w (p + 2) = w (p + 4) := by
    by_contra hne24
    -- 5 multisets: m₀={x,x}, m₁={x,a}, m₂={a,b}, m₃={b,c}, m₄={c,x}
    -- where a=w(p+2), b=w(p+3), c=w(p+4), x=w(p)
    -- a≠x, b≠x, c≠x, a≠c
    have hp5 : p + 4 + 1 = p := by
      have h5 : (5 : ZMod 5) = 0 := by decide
      linear_combination h5
    let m₀ := Necklace.abelianize (Necklace.slice w p.val (p.val + 2))
    let m₁ := Necklace.abelianize (Necklace.slice w (p + 1).val ((p + 1).val + 2))
    let m₂ := Necklace.abelianize (Necklace.slice w (p + 2).val ((p + 2).val + 2))
    let m₃ := Necklace.abelianize (Necklace.slice w (p + 3).val ((p + 3).val + 2))
    let m₄ := Necklace.abelianize (Necklace.slice w (p + 4).val ((p + 4).val + 2))
    have hm₀ : m₀ = Multiset.ofList [w p, w (p + 1)] := by
      show Necklace.abelianize _ = _; rw [slice_two]; simp [Necklace.abelianize]
    have hm₁ : m₁ = Multiset.ofList [w (p + 1), w (p + 2)] := by
      show Necklace.abelianize _ = _; rw [slice_two]; simp [Necklace.abelianize]; ring_nf
    have hm₂ : m₂ = Multiset.ofList [w (p + 2), w (p + 3)] := by
      show Necklace.abelianize _ = _; rw [slice_two]; simp [Necklace.abelianize]; ring_nf
    have hm₃ : m₃ = Multiset.ofList [w (p + 3), w (p + 4)] := by
      show Necklace.abelianize _ = _; rw [slice_two]; simp [Necklace.abelianize]; ring_nf
    have hm₄ : m₄ = Multiset.ofList [w (p + 4), w p] := by
      show Necklace.abelianize _ = _; rw [slice_two]; simp [Necklace.abelianize, hp5]
    -- Count of w(p) in each: m₀:2, m₁:1, m₂:0, m₃:0, m₄:1
    -- Count of w(p+2) in each: m₀:0, m₁:1, m₂:1, m₃:0/1, m₄:0/1
    -- Count of w(p+4) in each: m₀:0, m₁:0, m₂:0/1, m₃:1, m₄:1
    -- We need 4 distinct multisets.
    -- m₀ ≠ m₁ (count x: 2 vs 1), m₀ ≠ m₂ (count x: 2 vs 0), m₀ ≠ m₃ (count x: 2 vs 0), m₀ ≠ m₄ (count x: 2 vs 1)
    -- m₁ ≠ m₄: count(w(p+2)): 1 in m₁ vs ? in m₄. m₄ = {c, x}. c = w(p+4) ≠ w(p+2) = a.
    --   So count(a) in m₄ = 0 if a ≠ x (which it is). So 1 vs 0. Distinct.
    -- So {m₀, m₁, m₂, m₄} are 4 distinct if m₂ ≠ m₁ and m₂ ≠ m₄.
    -- m₁ vs m₂: count(x): 1 vs 0. Distinct.
    -- m₂ vs m₄: m₂={a,b}, m₄={c,x}. count(x): 0 vs 1. Distinct.
    -- So {m₀, m₁, m₂, m₄} are 4 distinct.
    have hne01 : m₀ ≠ m₁ := by
      apply multiset_ne_of_count_ne _ _ (w p)
      rw [hm₀, hm₁]; simp only [Multiset.coe_count, List.count_cons, List.count_nil]
      simp [hp.symm, hw2]
    have hne02 : m₀ ≠ m₂ := by
      apply multiset_ne_of_count_ne _ _ (w p)
      rw [hm₀, hm₂]; simp only [Multiset.coe_count, List.count_cons, List.count_nil]
      simp [hp.symm, hw2, hw3]
    have hne04 : m₀ ≠ m₄ := by
      apply multiset_ne_of_count_ne _ _ (w p)
      rw [hm₀, hm₄]; simp only [Multiset.coe_count, List.count_cons, List.count_nil]
      simp [hp.symm, hw4]
    have hne12 : m₁ ≠ m₂ := by
      apply multiset_ne_of_count_ne _ _ (w p)
      rw [hm₁, hm₂]; simp only [Multiset.coe_count, List.count_cons, List.count_nil]
      simp [hp.symm, hw2, hw3]
    have hne14 : m₁ ≠ m₄ := by
      apply multiset_ne_of_count_ne _ _ (w (p + 2))
      rw [hm₁, hm₄]; simp only [Multiset.coe_count, List.count_cons, List.count_nil]
      have hne42 : w (p + 4) ≠ w (p + 2) := fun h => hne24 h.symm
      simp [hp.symm, hw2.symm, hne42]
    have hne24' : m₂ ≠ m₄ := by
      apply multiset_ne_of_count_ne _ _ (w p)
      rw [hm₂, hm₄]; simp only [Multiset.coe_count, List.count_cons, List.count_nil]
      simp [hw2, hw3, hw4]
    have hmem₀ : m₀ ∈ (Necklace.allKStepMultisets w 2).toFinset :=
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨_, List.mem_ofFn.mpr ⟨⟨p.val, ZMod.val_lt p⟩, rfl⟩, rfl⟩)
    have hmem₁ : m₁ ∈ (Necklace.allKStepMultisets w 2).toFinset :=
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨_, List.mem_ofFn.mpr ⟨⟨(p+1).val, ZMod.val_lt _⟩, rfl⟩, rfl⟩)
    have hmem₂ : m₂ ∈ (Necklace.allKStepMultisets w 2).toFinset :=
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨_, List.mem_ofFn.mpr ⟨⟨(p+2).val, ZMod.val_lt _⟩, rfl⟩, rfl⟩)
    have hmem₄ : m₄ ∈ (Necklace.allKStepMultisets w 2).toFinset :=
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨_, List.mem_ofFn.mpr ⟨⟨(p+4).val, ZMod.val_lt _⟩, rfl⟩, rfl⟩)
    have h4set : ({m₀, m₁, m₂, m₄} : Finset _) ⊆ (Necklace.allKStepMultisets w 2).toFinset := by
      intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> assumption
    have hcard4 : ({m₀, m₁, m₂, m₄} : Finset _).card = 4 := by
      simp only [Finset.card_insert_eq_ite, Finset.mem_insert, Finset.mem_singleton]
      simp only [hne01, hne02, hne04, hne12, hne14, hne24', or_self, ite_false, Finset.card_singleton]
    have : (Necklace.allKStepMultisets w 2).toFinset.card ≥ 4 :=
      calc (Necklace.allKStepMultisets w 2).toFinset.card
          ≥ ({m₀, m₁, m₂, m₄} : Finset _).card := Finset.card_le_card h4set
        _ = 4 := hcard4
    omega
  -- Step 4: w(p+3) ≠ w(p+2): if equal, w(p+2)=w(p+3)=w(p+4), only 2 letters
  have hw32 : w (p + 3) ≠ w (p + 2) := by
    intro heq32
    -- w(p+2) = w(p+3) = w(p+4). count(w(p+2)) ≥ 3
    have hp3_ne_p2 : p + 3 ≠ p + 2 := by
      intro heq; exact absurd (show (3 : ZMod 5) = 2 from by linear_combination heq) (by decide)
    have hp4_ne_p2 : p + 4 ≠ p + 2 := by
      intro heq; exact absurd (show (4 : ZMod 5) = 2 from by linear_combination heq) (by decide)
    have hp4_ne_p3 : p + 4 ≠ p + 3 := by
      intro heq; exact absurd (show (4 : ZMod 5) = 3 from by linear_combination heq) (by decide)
    have hcount_wp2 : Necklace.count w (w (p + 2)) ≥ 3 := by
      unfold Necklace.count
      calc (Finset.filter (fun i => w i = w (p + 2)) Finset.univ).card
          ≥ ({p + 2, p + 3, p + 4} : Finset _).card := by
            apply Finset.card_le_card
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq32⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw24.symm⟩
        _ = 3 := by
            have h1 : p + 2 ∉ ({p + 3, p + 4} : Finset _) := by
              simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
              exact ⟨hp3_ne_p2.symm, hp4_ne_p2.symm⟩
            have h2 : p + 3 ∉ ({p + 4} : Finset _) := by
              simp only [Finset.mem_singleton]; exact hp4_ne_p3.symm
            rw [Finset.card_insert_eq_ite, if_neg h1, Finset.card_insert_eq_ite, if_neg h2,
                Finset.card_singleton]
    exact ternary5_two_letters_absurd w htern (w (p + 2)) (w p) hw2
      hcount_wp2 (by omega)
  -- Step 5: Construct σ and r
  -- Let x = w(p), a = w(p+2), b = w(p+3). x ≠ a, x ≠ b (from hw2, hw3), a ≠ b (from hw32)
  -- The word is: w(p)=x, w(p+1)=x, w(p+2)=a, w(p+3)=b, w(p+4)=a
  -- We want σ(x)=L, σ(a)=m, and then σ(b)=s.
  -- Set r = p + 1, so w'(i) = σ(w(i + p + 1)):
  --   w'(0) = σ(w(p+1)) = σ(x) = L
  --   w'(1) = σ(w(p+2)) = σ(a) = m
  --   w'(2) = σ(w(p+3)) = σ(b) = s
  --   w'(3) = σ(w(p+4)) = σ(a) = m
  --   w'(4) = σ(w(p+5)) = σ(w(p)) = σ(x) = L
  obtain ⟨σ, hσx, hσa, hσrest⟩ := exists_perm_x_to_L_y_to_m (w p) (w (p + 2)) hw2.symm
  have hσb : σ (w (p + 3)) = StepSize.s := hσrest _ hw3 hw32
  refine ⟨σ, p + 1, ?_, ?_, ?_, ?_, ?_⟩
  · -- w'(0) = σ(w(0 + p + 1)) = σ(w(p + 1)) = σ(x) = L
    show σ (w (((0 : ℕ) : ZMod 5) + (p + 1))) = StepSize.L
    rw [show ((0 : ℕ) : ZMod 5) + (p + 1) = p + 1 from by ring, ← hp, hσx]
  · -- w'(1) = σ(w(1 + p + 1)) = σ(w(p + 2)) = σ(a) = m
    show σ (w (((1 : ℕ) : ZMod 5) + (p + 1))) = StepSize.m
    rw [show ((1 : ℕ) : ZMod 5) + (p + 1) = p + 2 from by push_cast; ring]
    exact hσa
  · -- w'(2) = σ(w(2 + p + 1)) = σ(w(p + 3)) = σ(b) = s
    show σ (w (((2 : ℕ) : ZMod 5) + (p + 1))) = StepSize.s
    rw [show ((2 : ℕ) : ZMod 5) + (p + 1) = p + 3 from by push_cast; ring]
    exact hσb
  · -- w'(3) = σ(w(3 + p + 1)) = σ(w(p + 4)) = σ(a) = m
    show σ (w (((3 : ℕ) : ZMod 5) + (p + 1))) = StepSize.m
    rw [show ((3 : ℕ) : ZMod 5) + (p + 1) = p + 4 from by push_cast; ring, hw24.symm]
    exact hσa
  · -- w'(4) = σ(w(4 + p + 1)) = σ(w(p + 5)) = σ(w(p)) = σ(x) = L
    show σ (w (((4 : ℕ) : ZMod 5) + (p + 1))) = StepSize.L
    rw [show ((4 : ℕ) : ZMod 5) + (p + 1) = p + 5 from by push_cast; ring,
        show p + 5 = p + (5 : ZMod 5) from by ring,
        show (5 : ZMod 5) = 0 from by decide]
    simp [hσx]

/-- Non-balanced primitive MV3 with 2-step imbalance → sporadic non-balanced.

    **Proof outline** (Theorem 3.1, case Q = ε, Bulgakova–Buzhinsky–Goncharov 2023):
    The minimal non-balanced length is ℓ = 2, so |Q| = ℓ − 2 = 0. The
    spec₂-analysis from Claim 1 yields factors of the form `cc(ac)^m·ab` in [w].
    Since Q = ε, one shows that necessarily a ≠ b (otherwise the word would be
    balanced). The factor structure forces [w] = [ccaba]^p, and primitivity
    gives p = 1, n = 5, so w is S₃-equivalent to XYZYX. -/
private lemma mv3_twostep_unbalanced_sporadic (w : TernaryNecklace n)
    (hprim : Necklace.isPrimitive w) (hmv3 : isMV3 w)
    (h2 : ¬ isBalancedAt w 2) :
    isSporadicNonBalanced w := by
  have hn := mv3_not_balanced_at_2_length w hprim hmv3 h2
  exact ⟨hn, by subst hn; exact mv3_5_not_balanced_at_2_xyzyx w hmv3 h2⟩

/-- Construction of twisted MV3 witnesses from a non-balanced primitive MV3
    with balanced 2-steps.

    **Proof sketch** (Theorem 3.1, Q ≠ ε case, Bulgakova et al. 2022):
    ¬balanced + balanced-at-2 gives minimal imbalance ℓ > 2.
    • Claim 1: factor structure f_m^(ℓ)(Q) with |Q| = ℓ−2 > 0 forces a = b
      (the two majority letters have equal step counts).
    • Claim 2: factors are σ ∘ φ-images of boundary-twisted Christoffel word
      segments, with 10 → 01 swaps at block boundaries.
    • Claim 3: factors tile the circular word, giving [w] = [σ ∘ φ(T)] for
      T ∈ C^tw. Primitivity of w gives primitivity of c. -/
private lemma mv3_not_balanced_2_balanced_twisted_construction (w : TernaryNecklace n)
    (hprim : Necklace.isPrimitive w) (hmv3 : isMV3 w)
    (hbal : ¬ Necklace.isBalanced w) (h2 : isBalancedAt w 2) :
    ∃ (σ : Equiv.Perm StepSize) (k a b : ℕ) (c u : List BinaryStep) (s : ZMod n),
      k > 1 ∧ a > 0 ∧ b > 0 ∧ Nat.Coprime (2 * a) b ∧ n = k * (2 * a + b) ∧
      c.length = 2 * a + b ∧
      circularHasMOSProperty c ∧
      isLexFirstRotation c ∧
      c.count BinaryStep.L = 2 * a ∧
      c.count BinaryStep.s = b ∧
      TwistedConstruction.isBoundaryTwistedPower u c k ∧
      (List.ofFn (fun i : Fin n => σ (w (s + i.val : ZMod n)))) =
        TwistedConstruction.phiSubst u := sorry

/-- Non-balanced primitive MV3 with balanced 2-steps → twisted MV3.

    **Proof outline** (Theorem 3.1, case Q ≠ ε, Bulgakova–Buzhinsky–Goncharov 2023):
    The minimal non-balanced length is ℓ > 2, giving |Q| = ℓ − 2 > 0.
    • Claim 1 establishes factor structure f_m^(ℓ)(Q) = cQc(aQc)^m·aQa.
      The analysis forces a = b (equal step counts for the two majority letters).
    • Claim 2 shows these factors are σ ∘ φ-images of twisted Christoffel word
      powers from C^tw, with 10 → 01 swaps at borders between primitive factors.
    • Claim 3 shows the factors merge uniquely (the alternating factors in W_ℓ
      extend to `af_m^(ℓ)(Q)c` within [w]) to give [w] = [σ ∘ φ(T)] for some
      T ∈ C^tw, hence w is twisted MV3. -/
private lemma mv3_twostep_balanced_twisted (w : TernaryNecklace n)
    (hprim : Necklace.isPrimitive w) (hmv3 : isMV3 w)
    (hbal : ¬ Necklace.isBalanced w) (h2 : isBalancedAt w 2) :
    isTwistedMV3 w :=
  ⟨hprim, mv3_not_balanced_2_balanced_twisted_construction w hprim hmv3 hbal h2⟩

/-- Classification of primitive MV3 scales (Theorem 3.1, Bulgakova–Buzhinsky–Goncharov 2023):
    every primitive MV3 scale is balanced, sporadic non-balanced (XYZYX), or twisted.

    The proof splits on whether the word is balanced. If not, the minimal
    non-balanced length ℓ ≥ 2 determines the case:
    • ℓ = 2 (2-step balance fails): sporadic non-balanced
    • ℓ > 2 (2-step balance holds): twisted MV3 -/
theorem mv3_classification (w : TernaryNecklace n)
    (hprim : Necklace.isPrimitive w) (hmv3 : isMV3 w) :
    Necklace.isBalanced w ∨ isSporadicNonBalanced w ∨ isTwistedMV3 w := by
  by_cases hbal : Necklace.isBalanced w
  · exact Or.inl hbal
  · by_cases h2 : isBalancedAt w 2
    · exact Or.inr (Or.inr (mv3_twostep_balanced_twisted w hprim hmv3 hbal h2))
    · exact Or.inr (Or.inl (mv3_twostep_unbalanced_sporadic w hprim hmv3 h2))


end TernaryNecklace
