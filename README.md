# Scale Word Theorems in Lean 4

Formal proofs in Lean 4 about MOS (Moment of Symmetry) scales and MV3 (Maximum Variety 3) ternary scales. Built on Mathlib.

The long-term goal is to formalize the **MV3 classification theorem**: a primitive ternary scale with at most 3 distinct `k`-step vectors for every `k` is either balanced, the sporadic word `XYZYX`, or a twisted scale. The MOS theory proved here is a key prerequisite, since balanced MV3 scales decompose into MOS patterns via pair identification and step deletion.

(Inthar's note: Yes, the work so far is AI-generated. I double-checked the major theorems' signatures to ensure that the right things were being proven.)

## Completed Results

Two theorems about MOS binary necklaces are fully proven (no `sorry`s remain):

- **`allMOSScalesAreBalanced`** — Every MOS scale is balanced: for any letter `a` and any step size `k`, the counts of `a` in any two `k`-step subwords differ by at most 1.
- **`allMOSScalesHaveGenerator`** — Every MOS scale has a generator: a vector `g` such that the prefix vectors at some rotation are exactly the cosets `{j·g + k·p : 0 ≤ j < |p|}`, where `p` is the period vector.

The generator theorem is proved by strong induction on `n`. The base cases are `(n-1)L 1s` and `1L (n-1)s`. The inductive step decomposes the word into chunks (runs of the majority step separated by minority steps), shows the chunked word is again a MOS of shorter length, applies the induction hypothesis, and reflects the generator back via a lifted determinant argument.

## File Structure

### [Basic.lean](ScaleWordTheorems/Basic.lean) (243 lines)

Core definitions for the formalization:

- **`ZVector α`** — Integer-valued vectors over an alphabet (formal Z-linear combinations of step sizes)
- **`Necklace α n`** — Circular words of length `n` over alphabet `α`, indexed by `ZMod n`
- **`Necklace.kStepVector`** — The abelianized `k`-step subword starting at position `i`
- **`Necklace.period`** / **`Necklace.isPrimitive`** — Minimal period and primitivity
- **`Necklace.isBalanced`** — Balance property (max block-balance ≤ 1)
- **`StepSize`** — Ternary alphabet (`L`, `m`, `s`)
- **`TernaryNecklace`** — Circular words over three step sizes

### [MOS.lean](ScaleWordTheorems/MOS.lean) (9663 lines)

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

### [PairIdentificationAndDeletion.lean](ScaleWordTheorems/PairIdentificationAndDeletion.lean) (84 lines)

Definitions for ternary scale operations:

- **Pairwise-MOS**: A ternary necklace is pairwise-MOS if identifying any two of the three step sizes yields a MOS
- **Deletion-MOS**: A ternary necklace is deletion-MOS if deleting any step size and reading circularly yields a MOS
- **MOS substitution**: A ternary necklace is a MOS substitution necklace if it admits both a template MOS (via identification) and a filling MOS (via deletion)

### [TwistedNecklaces.lean](ScaleWordTheorems/TwistedNecklaces.lean) (3 lines)

Stub file importing `Basic` and `MOS`.

## Building

Requires Lean 4 (v4.27.0-rc1) and Mathlib.

```sh
lake build
```
