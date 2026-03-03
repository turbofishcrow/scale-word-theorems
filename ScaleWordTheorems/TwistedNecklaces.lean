-- Helper definitions for the Bulgakova–Buzhinsky–Goncharov construction of twisted MV3 scales.
import «ScaleWordTheorems».Basic
import «ScaleWordTheorems».MOS

/-!
# Twisted Necklaces

This file defines the alternating substitution φ used in the construction of
twisted MV3 scales (Bulgakova–Buzhinsky–Goncharov, 2023).

Given a binary word `u` over `{L, s}` (where `L` is the frequent step and `s`
is the rare step), φ replaces each `L` with alternating `StepSize.L` / `StepSize.m`
(toggling a parity flag) and each `s` with `StepSize.s` (preserving parity).
-/

namespace TwistedConstruction

/-- Helper for the alternating substitution φ with explicit parity state.
    When `parity = false`, the next `BinaryStep.L` maps to `StepSize.L`;
    when `parity = true`, it maps to `StepSize.m`.
    `BinaryStep.s` always maps to `StepSize.s` without toggling parity. -/
def phiSubstAux : Bool → List BinaryStep → List StepSize
  | _, [] => []
  | false, (BinaryStep.L :: rest) => StepSize.L :: phiSubstAux true rest
  | true, (BinaryStep.L :: rest) => StepSize.m :: phiSubstAux false rest
  | parity, (BinaryStep.s :: rest) => StepSize.s :: phiSubstAux parity rest

/-- The alternating substitution φ: given a binary word (list of `BinaryStep`),
    replace each `BinaryStep.L` with alternating `StepSize.L` / `StepSize.m`
    (starting with `StepSize.L`), and each `BinaryStep.s` with `StepSize.s`. -/
def phiSubst (u : List BinaryStep) : List StepSize :=
  phiSubstAux false u

/-- φ preserves length (auxiliary version). -/
lemma phiSubstAux_length : ∀ (p : Bool) (u : List BinaryStep),
    (phiSubstAux p u).length = u.length
  | _, [] => rfl
  | false, (BinaryStep.L :: rest) => by simp [phiSubstAux, phiSubstAux_length]
  | true, (BinaryStep.L :: rest) => by simp [phiSubstAux, phiSubstAux_length]
  | _, (BinaryStep.s :: rest) => by simp [phiSubstAux, phiSubstAux_length]

/-- φ preserves length. -/
lemma pshiSubst_length (u : List BinaryStep) : (phiSubst u).length = u.length :=
  phiSubstAux_length false u

/-- φ preserves the count of `s` (auxiliary version). -/
lemma phiSubstAux_count_s : ∀ (p : Bool) (u : List BinaryStep),
    (phiSubstAux p u).count StepSize.s = u.count BinaryStep.s
  | _, [] => rfl
  | false, (BinaryStep.L :: rest) => by
    simp [phiSubstAux, phiSubstAux_count_s]
  | true, (BinaryStep.L :: rest) => by
    simp [phiSubstAux, phiSubstAux_count_s]
  | _, (BinaryStep.s :: rest) => by
    simp [phiSubstAux, phiSubstAux_count_s]

/-- φ maps each `BinaryStep.L` to either `StepSize.L` or `StepSize.m`,
    so the total count of `L` plus `m` equals the count of `BinaryStep.L` (auxiliary). -/
lemma phiSubstAux_count_L_add_m : ∀ (p : Bool) (u : List BinaryStep),
    (phiSubstAux p u).count StepSize.L + (phiSubstAux p u).count StepSize.m =
      u.count BinaryStep.L
  | _, [] => rfl
  | false, (BinaryStep.L :: rest) => by
    simp [phiSubstAux]
    have := phiSubstAux_count_L_add_m true rest; omega
  | true, (BinaryStep.L :: rest) => by
    simp [phiSubstAux]
    have := phiSubstAux_count_L_add_m false rest; omega
  | _, (BinaryStep.s :: rest) => by
    simp [phiSubstAux]
    exact phiSubstAux_count_L_add_m _ rest

/-- φ produces `StepSize.s` whenever the input contains `BinaryStep.s` (auxiliary). -/
lemma phiSubstAux_has_s : ∀ (p : Bool) (u : List BinaryStep),
    u.count BinaryStep.s ≥ 1 → StepSize.s ∈ phiSubstAux p u
  | _, [], h => by simp at h
  | false, (BinaryStep.L :: rest), h => by
    apply List.mem_cons_of_mem
    apply phiSubstAux_has_s true rest
    have hc : (BinaryStep.L :: rest).count BinaryStep.s = rest.count BinaryStep.s := by simp
    omega
  | true, (BinaryStep.L :: rest), h => by
    apply List.mem_cons_of_mem
    apply phiSubstAux_has_s false rest
    have hc : (BinaryStep.L :: rest).count BinaryStep.s = rest.count BinaryStep.s := by simp
    omega
  | _, (BinaryStep.s :: rest), _ => List.mem_cons_self

/-- φ produces `StepSize.L` when there are enough `BinaryStep.L`s (auxiliary). -/
lemma phiSubstAux_has_L : ∀ (p : Bool) (u : List BinaryStep),
    u.count BinaryStep.L ≥ (if p then 2 else 1) → StepSize.L ∈ phiSubstAux p u
  | _, [], h => by split_ifs at h <;> simp at h
  | false, (BinaryStep.L :: rest), _ => List.mem_cons_self
  | true, (BinaryStep.L :: rest), h => by
    change (BinaryStep.L :: rest).count BinaryStep.L ≥ 2 at h
    apply List.mem_cons_of_mem
    apply phiSubstAux_has_L false rest
    show rest.count BinaryStep.L ≥ 1
    have hc : (BinaryStep.L :: rest).count BinaryStep.L = rest.count BinaryStep.L + 1 := by simp
    omega
  | p, (BinaryStep.s :: rest), h => by
    apply List.mem_cons_of_mem
    apply phiSubstAux_has_L p rest
    have hc : (BinaryStep.s :: rest).count BinaryStep.L = rest.count BinaryStep.L := by simp
    omega

/-- φ produces `StepSize.m` when there are enough `BinaryStep.L`s (auxiliary). -/
lemma phiSubstAux_has_m : ∀ (p : Bool) (u : List BinaryStep),
    u.count BinaryStep.L ≥ (if p then 1 else 2) → StepSize.m ∈ phiSubstAux p u
  | _, [], h => by split_ifs at h <;> simp at h
  | true, (BinaryStep.L :: rest), _ => List.mem_cons_self
  | false, (BinaryStep.L :: rest), h => by
    change (BinaryStep.L :: rest).count BinaryStep.L ≥ 2 at h
    apply List.mem_cons_of_mem
    apply phiSubstAux_has_m true rest
    show rest.count BinaryStep.L ≥ 1
    have hc : (BinaryStep.L :: rest).count BinaryStep.L = rest.count BinaryStep.L + 1 := by simp
    omega
  | p, (BinaryStep.s :: rest), h => by
    apply List.mem_cons_of_mem
    apply phiSubstAux_has_m p rest
    have hc : (BinaryStep.s :: rest).count BinaryStep.L = rest.count BinaryStep.L := by simp
    omega

/-- φ(u) has all three step sizes when `u` has enough of each binary step. -/
lemma phiSubst_isTernary (u : List BinaryStep)
    (hL : u.count BinaryStep.L ≥ 2) (hs : u.count BinaryStep.s ≥ 1) :
    StepSize.L ∈ phiSubst u ∧ StepSize.m ∈ phiSubst u ∧ StepSize.s ∈ phiSubst u :=
  ⟨phiSubstAux_has_L false u (show u.count BinaryStep.L ≥ 1 by omega),
   phiSubstAux_has_m false u (show u.count BinaryStep.L ≥ 2 by omega),
   phiSubstAux_has_s false u hs⟩

/-- A binary word `u` is a *boundary-twisted `k`-power* of a binary word `c`
    if `u` agrees with the `k`-fold concatenation of `c` at all positions
    except possibly the `2(k−1)` boundary positions (the last position of each
    block and the first position of the next block), and `u` has the same
    total step counts as `c` repeated `k` times.

    This captures the Bulgakova–Buzhinsky-Goncharov construction where at each boundary
    between consecutive copies of a Christoffel word, one may optionally swap
    a `(s, L)` pair to `(L, s)`. The count-preservation condition ensures that
    any modifications at boundaries are transpositions of adjacent elements. -/
def isBoundaryTwistedPower (u c : List BinaryStep) (k : ℕ) : Prop :=
  let M := c.length
  M > 0 ∧ u.length = k * M ∧
  -- Same total step counts as c repeated k times
  u.count BinaryStep.L = k * c.count BinaryStep.L ∧
  u.count BinaryStep.s = k * c.count BinaryStep.s ∧
  -- Agrees with c^k at all non-boundary positions
  ∀ (pos : ℕ), pos < k * M →
    (∀ j : ℕ, 1 ≤ j → j < k → pos ≠ j * M - 1 ∧ pos ≠ j * M) →
    u[pos]! = c[pos % M]!

end TwistedConstruction
