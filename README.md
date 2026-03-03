# Scale Word Theorems in Lean 4

Formal proofs in Lean 4 about MOS (Moment of Symmetry) scales and MV3 (Maximum Variety 3) ternary scales. Built on Mathlib.

The long-term goal is to formalize the **MV3 classification theorem**: a primitive ternary scale with at most 3 distinct `k`-step vectors for every `k` is either balanced, the sporadic word `XYZYX`, or a twisted scale. The MOS theory proved here is a key prerequisite, since balanced MV3 scales decompose into MOS patterns via pair identification and step deletion.

(Inthar's note: Yes, the work so far is AI-generated. I double-checked the major theorems' signatures to ensure that the right things were being proven.)

## Completed Results

### MOS Theory (sorry-free)

Three theorems about MOS binary necklaces are fully proven:

- **`allMOSScalesAreBalanced`** — Every MOS scale is balanced: for any letter `a` and any step size `k`, the counts of `a` in any two `k`-step subwords differ by at most 1.
- **`allMOSScalesHaveGenerator`** — Every MOS scale has a generator: a vector `g` such that the prefix vectors at some rotation are exactly the cosets `{j·g + k·p : 0 ≤ j < |p|}`, where `p` is the period vector.
- **`generatorImpliesMOS`** — Binary scales that have a generator are MOS; establishes the generator characterization for MOS scales.
- **`balanced_binary_isMOS`** — Every balanced binary necklace is MOS (converse of `allMOSScalesAreBalanced`).

The generator theorem is proved by strong induction on `n`. The base cases are `(n-1)L 1s` and `1L (n-1)s`. The inductive step decomposes the word into chunks (runs of the majority step separated by minority steps), shows the chunked word is again a MOS of shorter length, applies the induction hypothesis, and reflects the generator back via a lifted determinant argument.

### Odd-Regular Theory (sorry-free)

- **`oddRegular_hasAS`** — Every odd-regular scale has an alternating sequence.
- **`as_odd_stepSignature`** — An odd primitive ternary scale with an alternating sequence has step signature `(a, b, b)` (up to permutation) with `gcd(a, 2b) = 1`.
- **`as_odd_isSV3`** — An odd primitive ternary scale with an alternating sequence is SV3 (has at most 3 distinct `k`-step vectors for every `k`).
- **`as_odd_isOddRegular`** — An odd primitive ternary scale with an alternating sequence is odd-regular.
- **`oddRegular_isPairwisePrimMOS`** — Every odd-regular scale is pairwise-prim-MOS (each pair identification yields a primitive MOS).

### Balanced Ternary Scales (sorry-free)

- **`pairwiseMOS_implies_isBalanced`** — If all three pair identifications of a primitive ternary scale are MOS, then the scale is balanced.
- **`balanced_primitive_ternary_isPairwiseMOS`** — Every balanced primitive ternary scale is pairwise-MOS (each pair identification yields a MOS).
- **`balanced_primitive_ternary_isMV3`** — Every balanced primitive ternary scale is MV3.

### Even-Regular Theory (sorry-free)

- **`evenRegular_isBalanced`** — Every even-regular scale is balanced.
- **`evenRegular_chains_offset`** — Structure theorem for even-regular chain data.

### Partially Complete Results

The following theorems are stated and partially proved, with some `sorry`'d helper lemmas remaining:

- **`pwf_classification`** — Pairwise-prim-MOS ternary scales are either sporadic balanced or odd-regular. (9 sorry's in helpers, mostly in the two-equal-counts case of `balanced_not_even_isPWF`)
- **`balanced_primitive_ternary_classification`** — Balanced primitive ternary scales are sporadic balanced, odd-regular, or even-regular. (Depends on `pwf_classification`)
- **`mv3_classification`** — Primitive MV3 ternary scales are balanced, sporadic non-balanced (`XYZYX`), or twisted. (12 sorry's in helpers, mostly transition-rule arguments for the unbalanced case)

## File Structure

### [Basic.lean](ScaleWordTheorems/Basic.lean) (239 lines)

Core definitions for the formalization:

- **`ZVector α`** — Integer-valued vectors over an alphabet (formal Z-linear combinations of step sizes)
- **`Necklace α n`** — Circular words of length `n` over alphabet `α`, indexed by `ZMod n`
- **`Necklace.kStepVector`** — The abelianized `k`-step subword starting at position `i`
- **`Necklace.period`** / **`Necklace.isPrimitive`** — Minimal period and primitivity
- **`Necklace.isBalanced`** — Balance property (max block-balance ≤ 1)
- **`StepSize`** — Ternary alphabet (`L`, `m`, `s`)
- **`TernaryNecklace`** — Circular words over three step sizes

### [MOS.lean](ScaleWordTheorems/MOS.lean) (10502 lines)

The main file containing all definitions, lemmas, and theorems about MOS scales:

- **Definitions**: `BinaryStep` (`L`/`s`), `BinaryNecklace`, `isMOS`, `IsGenerator`, `HasGenerator`, chunk decomposition (`chunkSizesList`, `chunkSizesToBinary`), generator lifting (`liftGeneratorVectorX`)
- **Examples**: diatonic (5L 2s), oneirotonic (5L 3s), pentatonic (2L 3s)
- **Generator characterization** (`generator_iff_p_minus_one_occurrences`): `g` is a generator iff it appears at exactly `|p| - 1` positions per period
- **Chunk theory**: MOS chunk sizes come in at most 2 values differing by 1 (`mos_chunk_sizes_consecutive`); the chunked word is again MOS (`chunkSizesOfPrimMOSFormPrimMOS`)
- **Bresenham characterization**: Chunk size distribution follows a Bresenham-like formula; `k` consecutive chunk sums take at most 2 values (`kConsecutiveChunkSums_at_most_two`)
- **Scooting lemmas**: Perfect intervals can be "scooted" across chunks without changing the k-step vector (`scoot_perfect_interval`)
- **Generator lifting**: The lifted generator vector preserves det = ±1 (`det_liftGeneratorVectorX`)
- **Expansion theorems** (`generator_reflects_under_expansion_L`, `_s`): If the chunked word has a generator, so does the original word
- **Non-primitive case** (`hasGenerator_of_nonprimitive_mos`): Handles words that are `d`-fold repetitions via `mos_repetition_of_gcd_bjorklund`
- **Main theorems**: `allMOSScalesAreBalanced`, `allMOSScalesHaveGenerator`

### [MOSBalanced.lean](ScaleWordTheorems/MOSBalanced.lean) (182 lines)

- `allMOSScalesAreBalanced` (alternative proof), `balanced_binary_isMOS`

### [Permutation.lean](ScaleWordTheorems/Permutation.lean) (358 lines)

S₃-symmetry of the ternary alphabet: `applyPerm`, `isTernary_applyPerm`, `isS3Invariant_isMV3`, `isS3Invariant_isBalanced`, `wlog_perm`.

### [PairIdentificationAndDeletion.lean](ScaleWordTheorems/PairIdentificationAndDeletion.lean) (97 lines)

Definitions: `isPairwiseMOS`, `isPairwisePrimMOS`, `isPartialDeletionMOS`, `isPartialPairwiseMOS`.

### [MV3Defs.lean](ScaleWordTheorems/MV3Defs.lean) (319 lines)

Definitions for the MV3 classification: `isMV3`, `isSV3`, `hasAS`, `isOddRegular`, `isEvenRegular`, `isSporadicBalanced`, `isSporadicNonBalanced`, `isTwistedMV3`.

### [MV3AS.lean](ScaleWordTheorems/MV3AS.lean) (4429 lines)

Alternating sequence theory: `as_odd_stepSignature`, `as_odd_isSV3`, `as_odd_isOddRegular`. Proves that an odd primitive ternary scale with an alternating sequence is odd-regular by constructing its coprime deletion-MOS and pairwise-prim-MOS structure.

### [MV3OddRegular.lean](ScaleWordTheorems/MV3OddRegular.lean) (2541 lines)

Odd-regular theory: `oddRegular_hasAS`, `oddRegular_isPairwisePrimMOS`. Shows odd-regular scales have alternating sequences and are pairwise-prim-MOS.

### [MV3Balance.lean](ScaleWordTheorems/MV3Balance.lean) (4285 lines)

Classification of balanced ternary scales:
- `pairwiseMOS_implies_isBalanced`, `balanced_primitive_ternary_isPairwiseMOS` — equivalence between balanced and pairwise-MOS for primitive ternary scales
- `balanced_primitive_ternary_isMV3` — balanced primitive ternary scales are MV3
- `pwf_classification` — PWF scales are sporadic balanced or odd-regular (partially complete)
- `balanced_primitive_ternary_classification` — balanced = sporadic ∨ odd-regular ∨ even-regular (partially complete)
- All-distinct-counts case fully proved: balanced + primitive + all distinct step counts → sporadic balanced (n = 7, Fraenkel word `LmLsLmL`)

### [MV3EvenRegular.lean](ScaleWordTheorems/MV3EvenRegular.lean) (1053 lines)

Even-regular theory: `evenRegular_isBalanced`, `evenRegular_chains_offset`. Interleaving theorems stated but not yet proved.

### [MV3Classification.lean](ScaleWordTheorems/MV3Classification.lean) (1210 lines)

Top-level MV3 classification: `mv3_classification` — primitive MV3 = balanced ∨ sporadic non-balanced ∨ twisted. Partially complete; the unbalanced non-twisted case requires transition-rule arguments.

### [TwistedNecklaces.lean](ScaleWordTheorems/TwistedNecklaces.lean) (154 lines)

Twisted necklace constructions and basic properties.

## Sorry Status

| File | Sorry count | Status |
|------|------------|--------|
| Basic.lean | 0 | Complete |
| MOS.lean | 0 | Complete |
| MOSBalanced.lean | 0 | Complete |
| Permutation.lean | 0 | Complete |
| PairIdentificationAndDeletion.lean | 0 | Complete |
| TwistedNecklaces.lean | 0 | Complete |
| MV3.lean | 0 | Complete |
| MV3Defs.lean | 1 | Near-complete |
| MV3AS.lean | 1 | Near-complete |
| MV3OddRegular.lean | 0 | Complete |
| MV3Balance.lean | 9 | In progress |
| MV3EvenRegular.lean | 3 | In progress |
| MV3Classification.lean | 12 | In progress |
| **Total** | **26** | |

## Building

Requires Lean 4 and Mathlib.

```sh
lake build
```
