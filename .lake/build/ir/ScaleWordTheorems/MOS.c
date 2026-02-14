// Lean compiler output
// Module: ScaleWordTheorems.MOS
// Imports: public import Init public import Mathlib.Data.Multiset.Basic public import Mathlib.Data.ZMod.Basic public import Mathlib.Tactic public import ScaleWordTheorems.Basic
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_liftGeneratorVector(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_chunkSizesList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_countKStepVectorPerPeriod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_smallChunkSize(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_expandStep(uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_instDecidableEqZVectorOfFintype___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_liftGeneratorVector___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_isGenerator___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_countKStepVector___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_smallChunkSize___boxed(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_s_elim___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__0;
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_numChunks(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_oneirotonic(lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_instFintype;
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryNecklace_stepSignature___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_oneirotonic___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_isImperfectAt___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_ScaleWordTheorems_isChunkBoundary___closed__1;
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_isImperfectAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_commRing(lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_indices___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_numChunks___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_instDecidableEqZVectorOfFintype___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_isPerfectAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_chunkSizesList(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_List_scanlTR_go___at___00isChunkBoundary_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_instDecidableEqZVectorOfFintype___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_isGenerator___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_indices___redArg___lam__1(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_isGenerator___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_isGenerator___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_distinctKStepVectors___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_s_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_numSmallChunks___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_findGeneratorCoeff(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_ofNat___boxed(lean_object*);
static lean_object* lp_ScaleWordTheorems_expandWord___closed__0;
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_countKStepVector___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_instReprBinaryStep_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_countKStepVector(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_numSmallChunks(lean_object*, lean_object*);
lean_object* l_List_filterTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_countP_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_diatonic(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_indices___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_isChunkBoundary(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_isGenerator___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_isGenerator___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_BinaryStep_otherStep(uint8_t);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_chunkBoundaries(lean_object*);
static lean_object* lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__5;
LEAN_EXPORT lean_object* lp_ScaleWordTheorems___private_ScaleWordTheorems_MOS_0__chunkSizesList_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_isLargeChunk(lean_object*, lean_object*, lean_object*);
static lean_object* lp_ScaleWordTheorems_indices___redArg___closed__0;
uint8_t l_List_all___redArg(lean_object*, lean_object*);
lean_object* l_List_head_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_ctorElim___redArg(lean_object*);
static lean_object* lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__1;
lean_object* lp_mathlib_CommRing_toNonUnitalCommRing___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_instReprBinaryStep_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_liftGeneratorVectorX(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_isLargeChunk___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_indices___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems___private_ScaleWordTheorems_MOS_0__chunkSizesToBinary_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems___private_ScaleWordTheorems_MOS_0__instReprBinaryStep_repr_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_diatonic___boxed(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* l_List_range(lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_distinctKStepVectors___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_numChunks___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_scanlTR_go___at___00isChunkBoundary_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_ScaleWordTheorems_Necklace_kStepVector___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_distinctKStepVectors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryNecklace_stepSignature___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_numLargeChunks___boxed(lean_object*, lean_object*);
static lean_object* lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__2;
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_L_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_ScaleWordTheorems_Necklace_count___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_replicateTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_countKStepVectorPerPeriod___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_L_elim___redArg(lean_object*);
lean_object* lp_ScaleWordTheorems_ZVector_ofList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_isChunkBoundary___boxed(lean_object*, lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_expandStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_chunkSizesList___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_isGenerator___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems___private_ScaleWordTheorems_MOS_0__chunkSizesList_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_L_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_chunkSizesList___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_isImperfectAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_otherStep___boxed(lean_object*);
lean_object* lp_ScaleWordTheorems_Necklace_allKStepVectors___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems___private_ScaleWordTheorems_MOS_0__instReprBinaryStep_repr_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_isGenerator___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_BinaryStep_ofNat(lean_object*);
lean_object* lp_mathlib_List_dedup___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_liftedKStepSize___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_liftGeneratorVectorX___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems___private_ScaleWordTheorems_MOS_0__instReprBinaryStep_repr_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_instDecidableEqBinaryStep(uint8_t, uint8_t);
static lean_object* lp_ScaleWordTheorems_instReprBinaryStep___closed__0;
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryNecklace_stepSignature(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_numChunks___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_instDecidableEqBinaryStep___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_isGenerator___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_instInhabitedBinaryStep;
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_ctorIdx___boxed(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_val___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_isGenerator___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_s_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_s_elim(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_indices(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryNecklace_stepSignature___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_instDecidableEqZVectorOfFintype___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_instInhabitedBinaryStep_default;
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_isGenerator___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_ScaleWordTheorems_Necklace_slice___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_isPerfectAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_countLargeChunksInRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_List_mapTR_loop___at___00expandWord_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems___private_ScaleWordTheorems_MOS_0__instReprBinaryStep_repr_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_isGenerator___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_numLargeChunks(lean_object*, lean_object*);
static lean_object* lp_ScaleWordTheorems_BinaryStep_instFintype___closed__1;
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_chunkSizesList___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_indices___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_isGenerator___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__3;
static lean_object* lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__4;
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_isGenerator___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_ctorElim___redArg___boxed(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* lp_ScaleWordTheorems_BinaryStep_instFintype___closed__0;
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_isGenerator___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_expandWord(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_isPerfectAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_liftedKStepSize(lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* lp_ScaleWordTheorems_findGeneratorCoeff___closed__0;
static lean_object* lp_ScaleWordTheorems_isChunkBoundary___closed__0;
uint8_t lp_mathlib_Fintype_decidableForallFintype___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_countKStepVector___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_pentatonic(lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_largeChunkSize___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_List_mapTR_loop___at___00expandWord_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_ctorIdx(uint8_t);
uint8_t l_List_decidablePerm___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_isGenerator___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_ndinsert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_expandWord___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_countLargeChunksInRange(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00expandWord_spec__1(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_isImperfectAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems___private_ScaleWordTheorems_MOS_0__chunkSizesToBinary_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_largeChunkSize(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_distinctKStepVectors___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_pentatonic___boxed(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_chunkSizesList___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_isGenerator(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_instDecidableEqZVectorOfFintype(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_isPerfectAt___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems___private_ScaleWordTheorems_MOS_0__chunkSizesList_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_getD___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_ScaleWordTheorems_Necklace_period___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_L_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_instReprBinaryStep;
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_chunkBoundaryAt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_isGenerator___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_instDecidableEqZVectorOfFintype___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_indices___redArg___lam__0(lean_object*, uint8_t, lean_object*);
lean_object* lp_mathlib_ZMod_val(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_scanlTR_go___at___00isChunkBoundary_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_ctorIdx(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = lp_ScaleWordTheorems_BinaryStep_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_ScaleWordTheorems_BinaryStep_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = lp_ScaleWordTheorems_BinaryStep_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = lp_ScaleWordTheorems_BinaryStep_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_ScaleWordTheorems_BinaryStep_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_L_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_L_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_L_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = lp_ScaleWordTheorems_BinaryStep_L_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_L_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_ScaleWordTheorems_BinaryStep_L_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_s_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_s_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_s_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = lp_ScaleWordTheorems_BinaryStep_s_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_s_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_ScaleWordTheorems_BinaryStep_s_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_BinaryStep_ofNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_le(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_ofNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lp_ScaleWordTheorems_BinaryStep_ofNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_instDecidableEqBinaryStep(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lp_ScaleWordTheorems_BinaryStep_ctorIdx(x_1);
x_4 = lp_ScaleWordTheorems_BinaryStep_ctorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_instDecidableEqBinaryStep___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lp_ScaleWordTheorems_instDecidableEqBinaryStep(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("BinaryStep.L", 12, 12);
return x_1;
}
}
static lean_object* _init_lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("BinaryStep.s", 12, 12);
return x_1;
}
}
static lean_object* _init_lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_instReprBinaryStep_repr(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_10; 
if (x_1 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(1024u);
x_18 = lean_nat_dec_le(x_17, x_2);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__4;
x_3 = x_19;
goto block_9;
}
else
{
lean_object* x_20; 
x_20 = lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__5;
x_3 = x_20;
goto block_9;
}
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_unsigned_to_nat(1024u);
x_22 = lean_nat_dec_le(x_21, x_2);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__4;
x_10 = x_23;
goto block_16;
}
else
{
lean_object* x_24; 
x_24 = lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__5;
x_10 = x_24;
goto block_16;
}
}
block_9:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__1;
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = 0;
x_7 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
block_16:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__3;
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = 0;
x_14 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
x_15 = l_Repr_addAppParen(x_14, x_2);
return x_15;
}
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_instReprBinaryStep_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = lp_ScaleWordTheorems_instReprBinaryStep_repr(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_lp_ScaleWordTheorems_instReprBinaryStep___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_ScaleWordTheorems_instReprBinaryStep_repr___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_lp_ScaleWordTheorems_instReprBinaryStep() {
_start:
{
lean_object* x_1; 
x_1 = lp_ScaleWordTheorems_instReprBinaryStep___closed__0;
return x_1;
}
}
static uint8_t _init_lp_ScaleWordTheorems_instInhabitedBinaryStep_default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_lp_ScaleWordTheorems_instInhabitedBinaryStep() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_lp_ScaleWordTheorems_BinaryStep_instFintype___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_lp_ScaleWordTheorems_BinaryStep_instFintype___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lp_ScaleWordTheorems_BinaryStep_instFintype___closed__0;
x_2 = 0;
x_3 = lean_alloc_closure((void*)(lp_ScaleWordTheorems_instDecidableEqBinaryStep___boxed), 2, 0);
x_4 = lean_box(x_2);
x_5 = lp_mathlib_Multiset_ndinsert___redArg(x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_lp_ScaleWordTheorems_BinaryStep_instFintype() {
_start:
{
lean_object* x_1; 
x_1 = lp_ScaleWordTheorems_BinaryStep_instFintype___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_BinaryStep_otherStep(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryStep_otherStep___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = lp_ScaleWordTheorems_BinaryStep_otherStep(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryNecklace_stepSignature___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_alloc_closure((void*)(lp_ScaleWordTheorems_instDecidableEqBinaryStep___boxed), 2, 0);
x_4 = 0;
x_5 = lean_box(x_4);
lean_inc_ref(x_2);
lean_inc_ref(x_3);
x_6 = lp_ScaleWordTheorems_Necklace_count___redArg(x_1, x_3, x_2, x_5);
x_7 = 1;
x_8 = lean_box(x_7);
x_9 = lp_ScaleWordTheorems_Necklace_count___redArg(x_1, x_3, x_2, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryNecklace_stepSignature(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_ScaleWordTheorems_BinaryNecklace_stepSignature___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryNecklace_stepSignature___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_ScaleWordTheorems_BinaryNecklace_stepSignature(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_BinaryNecklace_stepSignature___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_ScaleWordTheorems_BinaryNecklace_stepSignature___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_diatonic(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(7u);
x_3 = lp_mathlib_ZMod_val(x_2, x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_dec_eq(x_3, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(3u);
x_11 = lean_nat_dec_eq(x_3, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(4u);
x_13 = lean_nat_dec_eq(x_3, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(5u);
x_15 = lean_nat_dec_eq(x_3, x_14);
lean_dec(x_3);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
else
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_3);
x_18 = 0;
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_3);
x_19 = 0;
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_3);
x_20 = 1;
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_3);
x_21 = 0;
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_3);
x_22 = 0;
return x_22;
}
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_diatonic___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lp_ScaleWordTheorems_diatonic(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_oneirotonic(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(8u);
x_3 = lp_mathlib_ZMod_val(x_2, x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_dec_eq(x_3, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(3u);
x_11 = lean_nat_dec_eq(x_3, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(4u);
x_13 = lean_nat_dec_eq(x_3, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(5u);
x_15 = lean_nat_dec_eq(x_3, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(6u);
x_17 = lean_nat_dec_eq(x_3, x_16);
lean_dec(x_3);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = 0;
return x_18;
}
else
{
uint8_t x_19; 
x_19 = 1;
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_3);
x_20 = 0;
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_3);
x_21 = 0;
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_3);
x_22 = 1;
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_3);
x_23 = 0;
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_3);
x_24 = 1;
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_3);
x_25 = 0;
return x_25;
}
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_oneirotonic___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lp_ScaleWordTheorems_oneirotonic(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_pentatonic(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(5u);
x_3 = lp_mathlib_ZMod_val(x_2, x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_dec_eq(x_3, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(3u);
x_11 = lean_nat_dec_eq(x_3, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(4u);
x_13 = lean_nat_dec_eq(x_3, x_12);
lean_dec(x_3);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
else
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_3);
x_16 = 1;
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_3);
x_17 = 0;
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_3);
x_18 = 1;
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_3);
x_19 = 1;
return x_19;
}
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_pentatonic___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lp_ScaleWordTheorems_pentatonic(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_instDecidableEqZVectorOfFintype___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_inc(x_3);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_1(x_2, x_3);
x_6 = lean_int_dec_eq(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_instDecidableEqZVectorOfFintype___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_ScaleWordTheorems_instDecidableEqZVectorOfFintype___redArg___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_instDecidableEqZVectorOfFintype___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_alloc_closure((void*)(lp_ScaleWordTheorems_instDecidableEqZVectorOfFintype___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lp_mathlib_Fintype_decidableForallFintype___redArg(x_4, x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_instDecidableEqZVectorOfFintype(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lp_ScaleWordTheorems_instDecidableEqZVectorOfFintype___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_instDecidableEqZVectorOfFintype___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lp_ScaleWordTheorems_instDecidableEqZVectorOfFintype(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_instDecidableEqZVectorOfFintype___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_ScaleWordTheorems_instDecidableEqZVectorOfFintype___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_lp_ScaleWordTheorems_findGeneratorCoeff___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_findGeneratorCoeff(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_40; 
x_5 = 0;
x_6 = lean_box(x_5);
lean_inc_ref(x_2);
x_7 = lean_apply_1(x_2, x_6);
x_8 = 1;
x_9 = lean_box(x_8);
x_10 = lean_apply_1(x_2, x_9);
x_11 = lean_box(x_5);
lean_inc_ref(x_3);
x_12 = lean_apply_1(x_3, x_11);
x_13 = lean_box(x_8);
x_14 = lean_apply_1(x_3, x_13);
x_15 = lean_box(x_5);
lean_inc_ref(x_1);
x_16 = lean_apply_1(x_1, x_15);
x_17 = lean_box(x_8);
x_18 = lean_apply_1(x_1, x_17);
x_19 = lean_int_mul(x_7, x_14);
x_20 = lean_int_mul(x_10, x_12);
x_21 = lean_int_sub(x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
x_22 = lp_ScaleWordTheorems_findGeneratorCoeff___closed__0;
x_40 = lean_int_dec_eq(x_21, x_22);
if (x_40 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_int_mul(x_16, x_10);
x_60 = lean_int_mul(x_18, x_7);
x_61 = lean_int_sub(x_59, x_60);
lean_dec(x_60);
lean_dec(x_59);
x_62 = lean_int_emod(x_61, x_21);
x_63 = lean_int_dec_eq(x_62, x_22);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_61);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
x_64 = lean_box(0);
return x_64;
}
else
{
if (x_40 == 0)
{
lean_object* x_65; uint8_t x_66; uint8_t x_72; 
x_65 = lean_int_ediv(x_61, x_21);
lean_dec(x_21);
lean_dec(x_61);
x_72 = lean_int_dec_eq(x_7, x_22);
if (x_72 == 0)
{
x_66 = x_63;
goto block_71;
}
else
{
x_66 = x_40;
goto block_71;
}
block_71:
{
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_7);
x_67 = lean_int_mul(x_65, x_14);
lean_dec(x_14);
lean_dec(x_65);
x_68 = lean_int_sub(x_18, x_67);
lean_dec(x_67);
lean_dec(x_18);
x_23 = x_68;
x_24 = x_10;
goto block_39;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_10);
x_69 = lean_int_mul(x_65, x_12);
lean_dec(x_12);
lean_dec(x_65);
x_70 = lean_int_sub(x_16, x_69);
lean_dec(x_69);
lean_dec(x_16);
x_23 = x_70;
x_24 = x_7;
goto block_39;
}
}
}
else
{
lean_object* x_73; 
lean_dec(x_61);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
x_73 = lean_box(0);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_12);
x_74 = lean_int_dec_eq(x_7, x_22);
if (x_74 == 0)
{
if (x_40 == 0)
{
goto block_58;
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_int_ediv(x_16, x_7);
x_76 = lean_int_mul(x_75, x_7);
lean_dec(x_7);
x_77 = lean_int_dec_eq(x_76, x_16);
lean_dec(x_16);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_75);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_4);
x_78 = lean_box(0);
return x_78;
}
else
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_int_mul(x_75, x_10);
lean_dec(x_10);
x_80 = lean_int_dec_eq(x_79, x_18);
lean_dec(x_18);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; 
lean_dec(x_75);
lean_dec(x_4);
x_81 = lean_box(0);
return x_81;
}
else
{
uint8_t x_82; 
x_82 = lean_int_dec_le(x_22, x_75);
if (x_82 == 0)
{
lean_object* x_83; 
lean_dec(x_75);
lean_dec(x_4);
x_83 = lean_box(0);
return x_83;
}
else
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_nat_to_int(x_4);
x_85 = lean_int_dec_lt(x_75, x_84);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; 
lean_dec(x_75);
x_86 = lean_box(0);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = l_Int_toNat(x_75);
lean_dec(x_75);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
}
}
}
}
}
else
{
goto block_58;
}
}
block_39:
{
uint8_t x_25; 
x_25 = lean_int_dec_eq(x_24, x_22);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_int_emod(x_23, x_24);
x_27 = lean_int_dec_eq(x_26, x_22);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_4);
x_28 = lean_box(0);
return x_28;
}
else
{
if (x_25 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_int_ediv(x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
x_30 = lean_int_dec_le(x_22, x_29);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_29);
lean_dec(x_4);
x_31 = lean_box(0);
return x_31;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_nat_to_int(x_4);
x_33 = lean_int_dec_lt(x_29, x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_29);
x_34 = lean_box(0);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Int_toNat(x_29);
lean_dec(x_29);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_4);
x_37 = lean_box(0);
return x_37;
}
}
}
else
{
lean_object* x_38; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_4);
x_38 = lean_box(0);
return x_38;
}
}
block_58:
{
uint8_t x_41; 
x_41 = lean_int_dec_eq(x_10, x_22);
if (x_41 == 0)
{
if (x_40 == 0)
{
lean_object* x_42; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
x_42 = lean_box(0);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_int_ediv(x_18, x_10);
x_44 = lean_int_mul(x_43, x_7);
lean_dec(x_7);
x_45 = lean_int_dec_eq(x_44, x_16);
lean_dec(x_16);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_43);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_4);
x_46 = lean_box(0);
return x_46;
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_int_mul(x_43, x_10);
lean_dec(x_10);
x_48 = lean_int_dec_eq(x_47, x_18);
lean_dec(x_18);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_43);
lean_dec(x_4);
x_49 = lean_box(0);
return x_49;
}
else
{
uint8_t x_50; 
x_50 = lean_int_dec_le(x_22, x_43);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_43);
lean_dec(x_4);
x_51 = lean_box(0);
return x_51;
}
else
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_nat_to_int(x_4);
x_53 = lean_int_dec_lt(x_43, x_52);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_43);
x_54 = lean_box(0);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = l_Int_toNat(x_43);
lean_dec(x_43);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
}
}
}
else
{
lean_object* x_57; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
x_57 = lean_box(0);
return x_57;
}
}
}
}
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_isGenerator___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_alloc_closure((void*)(lp_ScaleWordTheorems_Necklace_kStepVector___boxed), 8, 7);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, lean_box(0));
lean_closure_set(x_8, 3, x_2);
lean_closure_set(x_8, 4, x_3);
lean_closure_set(x_8, 5, x_7);
lean_closure_set(x_8, 6, x_4);
x_9 = lp_ScaleWordTheorems_instDecidableEqZVectorOfFintype___redArg(x_5, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_isGenerator___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lp_ScaleWordTheorems_isGenerator___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_isGenerator___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_alloc_closure((void*)(lp_ScaleWordTheorems_isGenerator___redArg___lam__0___boxed), 7, 6);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_7);
lean_closure_set(x_8, 4, x_4);
lean_closure_set(x_8, 5, x_5);
x_9 = l_List_any___redArg(x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_isGenerator___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lp_ScaleWordTheorems_isGenerator___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_isGenerator___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_apply_1(x_1, x_2);
x_7 = lean_apply_2(x_3, x_5, x_6);
x_8 = lean_apply_1(x_4, x_7);
x_9 = lean_unbox(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_isGenerator___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lp_ScaleWordTheorems_isGenerator___redArg___lam__2(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_isGenerator___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_8, x_10);
x_12 = lean_alloc_closure((void*)(lp_ScaleWordTheorems_Necklace_kStepVector___boxed), 8, 7);
lean_closure_set(x_12, 0, lean_box(0));
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, lean_box(0));
lean_closure_set(x_12, 3, x_2);
lean_closure_set(x_12, 4, x_3);
lean_closure_set(x_12, 5, x_9);
lean_closure_set(x_12, 6, x_11);
x_13 = lp_ScaleWordTheorems_findGeneratorCoeff(x_12, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
else
{
lean_dec_ref(x_13);
return x_7;
}
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_isGenerator___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_7);
x_10 = lp_ScaleWordTheorems_isGenerator___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_8);
lean_dec(x_8);
x_11 = lean_box(x_10);
return x_11;
}
}
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_isGenerator___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_8, x_10);
x_12 = lean_alloc_closure((void*)(lp_ScaleWordTheorems_Necklace_kStepVector___boxed), 8, 7);
lean_closure_set(x_12, 0, lean_box(0));
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, lean_box(0));
lean_closure_set(x_12, 3, x_2);
lean_closure_set(x_12, 4, x_3);
lean_closure_set(x_12, 5, x_9);
lean_closure_set(x_12, 6, x_11);
x_13 = lp_ScaleWordTheorems_findGeneratorCoeff(x_12, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_nat_dec_eq(x_15, x_7);
lean_dec(x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_isGenerator___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lp_ScaleWordTheorems_isGenerator___redArg___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
x_10 = lean_box(x_9);
return x_10;
}
}
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_isGenerator___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_alloc_closure((void*)(lp_ScaleWordTheorems_isGenerator___redArg___lam__4___boxed), 8, 7);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_4);
lean_closure_set(x_9, 4, x_5);
lean_closure_set(x_9, 5, x_6);
lean_closure_set(x_9, 6, x_8);
x_10 = l_List_any___redArg(x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_isGenerator___redArg___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lp_ScaleWordTheorems_isGenerator___redArg___lam__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_box(x_9);
return x_10;
}
}
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_isGenerator___redArg___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_alloc_closure((void*)(lp_ScaleWordTheorems_isGenerator___redArg___lam__2___boxed), 5, 4);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_3);
x_12 = lean_box(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_11);
lean_inc_ref(x_5);
lean_inc(x_4);
x_13 = lean_alloc_closure((void*)(lp_ScaleWordTheorems_isGenerator___redArg___lam__3___boxed), 8, 7);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_5);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_6);
lean_closure_set(x_13, 4, x_7);
lean_closure_set(x_13, 5, x_8);
lean_closure_set(x_13, 6, x_12);
lean_inc(x_8);
x_14 = l_List_range(x_8);
lean_inc(x_14);
x_15 = l_List_all___redArg(x_14, x_13);
if (x_15 == 0)
{
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
lean_inc(x_14);
x_16 = lean_alloc_closure((void*)(lp_ScaleWordTheorems_isGenerator___redArg___lam__5___boxed), 8, 7);
lean_closure_set(x_16, 0, x_4);
lean_closure_set(x_16, 1, x_5);
lean_closure_set(x_16, 2, x_11);
lean_closure_set(x_16, 3, x_6);
lean_closure_set(x_16, 4, x_7);
lean_closure_set(x_16, 5, x_8);
lean_closure_set(x_16, 6, x_14);
x_17 = l_List_all___redArg(x_14, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_isGenerator___redArg___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_9);
x_12 = lp_ScaleWordTheorems_isGenerator___redArg___lam__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_11, x_10);
x_13 = lean_box(x_12);
return x_13;
}
}
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_isGenerator___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_inc(x_1);
x_4 = lp_mathlib_ZMod_commRing(x_1);
lean_inc_ref(x_4);
x_5 = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(x_4);
x_6 = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(x_5);
x_7 = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lp_mathlib_Ring_toAddGroupWithOne___redArg(x_4);
x_10 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_10);
lean_dec_ref(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lp_ScaleWordTheorems_BinaryStep_instFintype;
x_13 = lean_alloc_closure((void*)(lp_ScaleWordTheorems_instDecidableEqBinaryStep___boxed), 2, 0);
lean_inc(x_1);
x_14 = l_List_range(x_1);
lean_inc(x_14);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_13);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(lp_ScaleWordTheorems_isGenerator___redArg___lam__1___boxed), 7, 6);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_13);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_12);
lean_closure_set(x_15, 4, x_3);
lean_closure_set(x_15, 5, x_14);
lean_inc(x_14);
x_16 = l_List_any___redArg(x_14, x_15);
if (x_16 == 0)
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_inc_ref(x_2);
lean_inc_ref(x_13);
lean_inc(x_1);
x_17 = lp_ScaleWordTheorems_Necklace_period___redArg(x_1, x_13, x_2);
x_18 = l_List_lengthTR___redArg(x_17);
lean_inc_ref(x_13);
x_19 = lean_alloc_closure((void*)(lp_ScaleWordTheorems_ZVector_ofList), 4, 3);
lean_closure_set(x_19, 0, lean_box(0));
lean_closure_set(x_19, 1, x_13);
lean_closure_set(x_19, 2, x_17);
x_20 = lean_box(x_16);
x_21 = lean_alloc_closure((void*)(lp_ScaleWordTheorems_isGenerator___redArg___lam__6___boxed), 10, 9);
lean_closure_set(x_21, 0, x_11);
lean_closure_set(x_21, 1, x_8);
lean_closure_set(x_21, 2, x_2);
lean_closure_set(x_21, 3, x_1);
lean_closure_set(x_21, 4, x_13);
lean_closure_set(x_21, 5, x_3);
lean_closure_set(x_21, 6, x_19);
lean_closure_set(x_21, 7, x_18);
lean_closure_set(x_21, 8, x_20);
x_22 = l_List_any___redArg(x_14, x_21);
return x_22;
}
}
}
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_isGenerator(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lp_ScaleWordTheorems_isGenerator___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_isGenerator___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lp_ScaleWordTheorems_isGenerator(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_isGenerator___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_ScaleWordTheorems_isGenerator___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_countKStepVector___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_alloc_closure((void*)(lp_ScaleWordTheorems_Necklace_kStepVector___boxed), 8, 7);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, lean_box(0));
lean_closure_set(x_8, 3, x_2);
lean_closure_set(x_8, 4, x_3);
lean_closure_set(x_8, 5, x_7);
lean_closure_set(x_8, 6, x_4);
x_9 = lp_ScaleWordTheorems_instDecidableEqZVectorOfFintype___redArg(x_5, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_countKStepVector___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lp_ScaleWordTheorems_countKStepVector___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_countKStepVector___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(lp_ScaleWordTheorems_countKStepVector___redArg___lam__0___boxed), 7, 6);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_4);
lean_closure_set(x_7, 3, x_5);
lean_closure_set(x_7, 4, x_3);
lean_closure_set(x_7, 5, x_6);
x_8 = l_List_range(x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_List_countP_go___redArg(x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_countKStepVector(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lp_ScaleWordTheorems_countKStepVector___redArg(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_countKStepVectorPerPeriod___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_4);
lean_inc_ref(x_2);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(lp_ScaleWordTheorems_countKStepVector___redArg___lam__0___boxed), 7, 6);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_4);
lean_closure_set(x_7, 3, x_5);
lean_closure_set(x_7, 4, x_3);
lean_closure_set(x_7, 5, x_6);
x_8 = lp_ScaleWordTheorems_Necklace_period___redArg(x_1, x_2, x_4);
x_9 = l_List_lengthTR___redArg(x_8);
lean_dec(x_8);
x_10 = l_List_range(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_List_countP_go___redArg(x_7, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_countKStepVectorPerPeriod(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lp_ScaleWordTheorems_countKStepVectorPerPeriod___redArg(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_distinctKStepVectors___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lp_ScaleWordTheorems_instDecidableEqZVectorOfFintype___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_distinctKStepVectors___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_ScaleWordTheorems_distinctKStepVectors___redArg___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_distinctKStepVectors___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(lp_ScaleWordTheorems_distinctKStepVectors___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_6, 0, x_3);
x_7 = lp_ScaleWordTheorems_Necklace_allKStepVectors___redArg(x_1, x_2, x_4, x_5);
x_8 = lp_mathlib_List_dedup___redArg(x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_distinctKStepVectors(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_ScaleWordTheorems_distinctKStepVectors___redArg(x_1, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_indices___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; uint8_t x_6; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_unbox(x_4);
x_6 = lp_ScaleWordTheorems_instDecidableEqBinaryStep(x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_indices___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
x_5 = lp_ScaleWordTheorems_indices___redArg___lam__0(x_1, x_4, x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_indices___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_apply_1(x_1, x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
static lean_object* _init_lp_ScaleWordTheorems_indices___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_indices___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_1);
x_4 = lp_mathlib_ZMod_commRing(x_1);
x_5 = lp_mathlib_Ring_toAddGroupWithOne___redArg(x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_box(x_2);
x_9 = lean_alloc_closure((void*)(lp_ScaleWordTheorems_indices___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_8);
x_10 = lean_alloc_closure((void*)(lp_ScaleWordTheorems_indices___redArg___lam__1), 2, 1);
lean_closure_set(x_10, 0, x_7);
x_11 = l_List_range(x_1);
x_12 = lp_ScaleWordTheorems_indices___redArg___closed__0;
x_13 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(x_10, x_11, x_12);
x_14 = lean_box(0);
x_15 = l_List_filterTR_loop___redArg(x_9, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_indices(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_ScaleWordTheorems_indices___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_indices___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
x_6 = lp_ScaleWordTheorems_indices(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_indices___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = lp_ScaleWordTheorems_indices___redArg(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_numChunks___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lp_ScaleWordTheorems_BinaryStep_otherStep(x_2);
x_5 = lp_ScaleWordTheorems_indices___redArg(x_1, x_4, x_3);
x_6 = l_List_lengthTR___redArg(x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_numChunks(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_ScaleWordTheorems_numChunks___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_numChunks___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
x_6 = lp_ScaleWordTheorems_numChunks(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_numChunks___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = lp_ScaleWordTheorems_numChunks___redArg(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_chunkSizesList___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_inc(x_1);
x_6 = l_List_get_x21Internal___redArg(x_1, x_2, x_5);
x_7 = l_List_get_x21Internal___redArg(x_1, x_2, x_3);
x_8 = lean_nat_sub(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
x_9 = lean_nat_sub(x_8, x_4);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_chunkSizesList___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_ScaleWordTheorems_chunkSizesList___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_chunkSizesList___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lp_ScaleWordTheorems_BinaryStep_otherStep(x_2);
lean_inc(x_1);
x_5 = lp_ScaleWordTheorems_indices___redArg(x_1, x_4, x_3);
x_6 = l_List_head_x3f___redArg(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(lp_mathlib_ZMod_val___boxed), 2, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_box(0);
lean_inc(x_5);
x_13 = l_List_mapTR_loop___redArg(x_11, x_5, x_12);
x_14 = lp_mathlib_ZMod_val(x_1, x_9);
lean_dec(x_9);
x_15 = lean_nat_add(x_14, x_1);
lean_dec(x_1);
lean_dec(x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
x_17 = l_List_appendTR___redArg(x_13, x_16);
x_18 = lean_alloc_closure((void*)(lp_ScaleWordTheorems_chunkSizesList___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_18, 0, x_10);
lean_closure_set(x_18, 1, x_17);
x_19 = l_List_lengthTR___redArg(x_5);
lean_dec(x_5);
x_20 = l_List_range(x_19);
x_21 = l_List_mapTR_loop___redArg(x_18, x_20, x_12);
lean_ctor_set(x_6, 0, x_21);
return x_6;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_22 = lean_ctor_get(x_6, 0);
lean_inc(x_22);
lean_dec(x_6);
x_23 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_24 = lean_alloc_closure((void*)(lp_mathlib_ZMod_val___boxed), 2, 1);
lean_closure_set(x_24, 0, x_1);
x_25 = lean_box(0);
lean_inc(x_5);
x_26 = l_List_mapTR_loop___redArg(x_24, x_5, x_25);
x_27 = lp_mathlib_ZMod_val(x_1, x_22);
lean_dec(x_22);
x_28 = lean_nat_add(x_27, x_1);
lean_dec(x_1);
lean_dec(x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
x_30 = l_List_appendTR___redArg(x_26, x_29);
x_31 = lean_alloc_closure((void*)(lp_ScaleWordTheorems_chunkSizesList___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_31, 0, x_23);
lean_closure_set(x_31, 1, x_30);
x_32 = l_List_lengthTR___redArg(x_5);
lean_dec(x_5);
x_33 = l_List_range(x_32);
x_34 = l_List_mapTR_loop___redArg(x_31, x_33, x_25);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_chunkSizesList(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_ScaleWordTheorems_chunkSizesList___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_chunkSizesList___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
x_6 = lp_ScaleWordTheorems_chunkSizesList(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_chunkSizesList___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = lp_ScaleWordTheorems_chunkSizesList___redArg(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems___private_ScaleWordTheorems_MOS_0__chunkSizesList_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems___private_ScaleWordTheorems_MOS_0__chunkSizesList_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_ScaleWordTheorems___private_ScaleWordTheorems_MOS_0__chunkSizesList_match__1_splitter___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems___private_ScaleWordTheorems_MOS_0__chunkSizesList_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_ScaleWordTheorems___private_ScaleWordTheorems_MOS_0__chunkSizesList_match__1_splitter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems___private_ScaleWordTheorems_MOS_0__instReprBinaryStep_repr_match__1_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (x_1 == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems___private_ScaleWordTheorems_MOS_0__instReprBinaryStep_repr_match__1_splitter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_ScaleWordTheorems___private_ScaleWordTheorems_MOS_0__instReprBinaryStep_repr_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems___private_ScaleWordTheorems_MOS_0__instReprBinaryStep_repr_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = lp_ScaleWordTheorems___private_ScaleWordTheorems_MOS_0__instReprBinaryStep_repr_match__1_splitter(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems___private_ScaleWordTheorems_MOS_0__instReprBinaryStep_repr_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = lp_ScaleWordTheorems___private_ScaleWordTheorems_MOS_0__instReprBinaryStep_repr_match__1_splitter___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems___private_ScaleWordTheorems_MOS_0__chunkSizesToBinary_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_2, 1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_ctor_get(x_6, 1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc_ref(x_6);
lean_dec(x_5);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec_ref(x_6);
x_12 = lean_apply_2(x_4, x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_4);
x_13 = lean_apply_3(x_5, x_2, lean_box(0), lean_box(0));
return x_13;
}
}
}
else
{
lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_apply_3(x_5, x_2, lean_box(0), lean_box(0));
return x_14;
}
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems___private_ScaleWordTheorems_MOS_0__chunkSizesToBinary_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_5, 1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc_ref(x_5);
lean_dec(x_4);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec_ref(x_5);
x_11 = lean_apply_2(x_3, x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_3);
x_12 = lean_apply_3(x_4, x_1, lean_box(0), lean_box(0));
return x_12;
}
}
}
else
{
lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_apply_3(x_4, x_1, lean_box(0), lean_box(0));
return x_13;
}
}
}
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_isPerfectAt___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_alloc_closure((void*)(lp_ScaleWordTheorems_instDecidableEqBinaryStep___boxed), 2, 0);
x_7 = lean_nat_add(x_5, x_4);
x_8 = lp_ScaleWordTheorems_Necklace_slice___redArg(x_1, x_2, x_5, x_7);
lean_dec(x_7);
x_9 = l_List_decidablePerm___redArg(x_6, x_8, x_3);
return x_9;
}
}
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_isPerfectAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lp_ScaleWordTheorems_isPerfectAt___redArg(x_1, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_isPerfectAt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lp_ScaleWordTheorems_isPerfectAt(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_isPerfectAt___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lp_ScaleWordTheorems_isPerfectAt___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_isImperfectAt___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_alloc_closure((void*)(lp_ScaleWordTheorems_instDecidableEqBinaryStep___boxed), 2, 0);
x_7 = lean_nat_add(x_5, x_4);
x_8 = lp_ScaleWordTheorems_Necklace_slice___redArg(x_1, x_2, x_5, x_7);
lean_dec(x_7);
x_9 = l_List_decidablePerm___redArg(x_6, x_8, x_3);
return x_9;
}
}
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_isImperfectAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lp_ScaleWordTheorems_isImperfectAt___redArg(x_1, x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_isImperfectAt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lp_ScaleWordTheorems_isImperfectAt(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_isImperfectAt___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lp_ScaleWordTheorems_isImperfectAt___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_largeChunkSize(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_nat_add(x_1, x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_3, x_4);
lean_dec(x_3);
x_6 = lean_nat_div(x_5, x_2);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_largeChunkSize___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_ScaleWordTheorems_largeChunkSize(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_smallChunkSize(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_div(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_smallChunkSize___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_ScaleWordTheorems_smallChunkSize(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_numLargeChunks(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_mod(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_numLargeChunks___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_ScaleWordTheorems_numLargeChunks(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_numSmallChunks(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_nat_mod(x_1, x_2);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_numSmallChunks___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_ScaleWordTheorems_numSmallChunks(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_expandStep(uint8_t x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; 
if (x_1 == 0)
{
lean_object* x_14; 
x_14 = lp_ScaleWordTheorems_largeChunkSize(x_2, x_3);
x_5 = x_14;
goto block_13;
}
else
{
lean_object* x_15; 
x_15 = lean_nat_div(x_2, x_3);
x_5 = x_15;
goto block_13;
}
block_13:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_box(x_4);
x_7 = l_List_replicateTR___redArg(x_5, x_6);
x_8 = lp_ScaleWordTheorems_BinaryStep_otherStep(x_4);
x_9 = lean_box(0);
x_10 = lean_box(x_8);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_List_appendTR___redArg(x_7, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_expandStep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
x_6 = lean_unbox(x_4);
x_7 = lp_ScaleWordTheorems_expandStep(x_5, x_2, x_3, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_lp_ScaleWordTheorems_expandWord___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_List_mapTR_loop___at___00expandWord_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; 
x_6 = l_List_reverse___redArg(x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_unbox(x_8);
lean_dec(x_8);
x_11 = lp_ScaleWordTheorems_expandStep(x_10, x_1, x_2, x_3);
lean_ctor_set(x_4, 1, x_5);
lean_ctor_set(x_4, 0, x_11);
{
lean_object* _tmp_3 = x_9;
lean_object* _tmp_4 = x_4;
x_4 = _tmp_3;
x_5 = _tmp_4;
}
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_unbox(x_13);
lean_dec(x_13);
x_16 = lp_ScaleWordTheorems_expandStep(x_15, x_1, x_2, x_3);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_5);
x_4 = x_14;
x_5 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00expandWord_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_array_to_list(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l_List_foldl___at___00Array_appendList_spec__0___redArg(x_2, x_4);
x_1 = x_5;
x_2 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_expandWord(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_box(0);
x_6 = lp_ScaleWordTheorems_List_mapTR_loop___at___00expandWord_spec__0(x_2, x_3, x_4, x_1, x_5);
x_7 = lp_ScaleWordTheorems_expandWord___closed__0;
x_8 = lp_ScaleWordTheorems___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00expandWord_spec__1(x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_expandWord___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
x_6 = lp_ScaleWordTheorems_expandWord(x_1, x_2, x_3, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_List_mapTR_loop___at___00expandWord_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = lp_ScaleWordTheorems_List_mapTR_loop___at___00expandWord_spec__0(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_isLargeChunk(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_nat_mul(x_3, x_1);
x_5 = lean_nat_div(x_4, x_2);
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_3, x_6);
x_8 = lean_nat_mul(x_7, x_1);
lean_dec(x_7);
x_9 = lean_nat_div(x_8, x_2);
lean_dec(x_8);
x_10 = lean_nat_dec_lt(x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_isLargeChunk___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_ScaleWordTheorems_isLargeChunk(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_countLargeChunksInRange(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_nat_add(x_3, x_4);
x_6 = lean_nat_mul(x_5, x_1);
lean_dec(x_5);
x_7 = lean_nat_div(x_6, x_2);
lean_dec(x_6);
x_8 = lean_nat_mul(x_3, x_1);
x_9 = lean_nat_div(x_8, x_2);
lean_dec(x_8);
x_10 = lean_nat_sub(x_7, x_9);
lean_dec(x_9);
lean_dec(x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_countLargeChunksInRange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_ScaleWordTheorems_countLargeChunksInRange(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_lp_ScaleWordTheorems_isChunkBoundary___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_lp_ScaleWordTheorems_isChunkBoundary___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_scanlTR_go___at___00isChunkBoundary_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = 1;
x_7 = lean_usize_sub(x_2, x_6);
x_8 = lean_array_uget(x_1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
x_2 = x_7;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_List_scanlTR_go___at___00isChunkBoundary_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
x_5 = lean_array_get_size(x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_dec_ref(x_3);
return x_4;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_usize_of_nat(x_5);
x_9 = 0;
x_10 = lp_ScaleWordTheorems___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_scanlTR_go___at___00isChunkBoundary_spec__0_spec__0(x_3, x_8, x_9, x_4);
lean_dec_ref(x_3);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec_ref(x_1);
x_13 = lean_nat_add(x_2, x_11);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_13, x_14);
lean_dec(x_13);
x_16 = lean_array_push(x_3, x_2);
x_1 = x_12;
x_2 = x_15;
x_3 = x_16;
goto _start;
}
}
}
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_isChunkBoundary(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lp_ScaleWordTheorems_isChunkBoundary___closed__0;
x_5 = lp_ScaleWordTheorems_List_scanlTR_go___at___00isChunkBoundary_spec__0(x_1, x_3, x_4);
x_6 = lp_ScaleWordTheorems_isChunkBoundary___closed__1;
x_7 = l_List_elem___redArg(x_6, x_2, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_isChunkBoundary___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_ScaleWordTheorems_isChunkBoundary(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_scanlTR_go___at___00isChunkBoundary_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lp_ScaleWordTheorems___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_scanlTR_go___at___00isChunkBoundary_spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_chunkBoundaries(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lp_ScaleWordTheorems_isChunkBoundary___closed__0;
x_4 = lp_ScaleWordTheorems_List_scanlTR_go___at___00isChunkBoundary_spec__0(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_chunkBoundaryAt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lp_ScaleWordTheorems_chunkBoundaries(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_List_getD___redArg(x_3, x_2, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_liftGeneratorVector(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_5 = 0;
x_6 = lean_box(x_5);
lean_inc_ref(x_1);
x_7 = lean_apply_1(x_1, x_6);
x_8 = 1;
x_9 = lean_box(x_8);
x_10 = lean_apply_1(x_1, x_9);
if (x_4 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lp_ScaleWordTheorems_largeChunkSize(x_2, x_3);
x_12 = lean_nat_div(x_2, x_3);
x_13 = lean_nat_to_int(x_11);
x_14 = lean_int_mul(x_7, x_13);
lean_dec(x_13);
lean_dec(x_7);
x_15 = lean_nat_to_int(x_12);
x_16 = lean_int_mul(x_10, x_15);
lean_dec(x_15);
lean_dec(x_10);
x_17 = lean_int_add(x_14, x_16);
lean_dec(x_16);
lean_dec(x_14);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = lean_int_add(x_7, x_10);
lean_dec(x_10);
lean_dec(x_7);
return x_18;
}
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_liftGeneratorVector___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
x_6 = lp_ScaleWordTheorems_liftGeneratorVector(x_1, x_2, x_3, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_liftGeneratorVectorX(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = 0;
x_7 = lean_box(x_6);
lean_inc_ref(x_2);
x_8 = lean_apply_1(x_2, x_7);
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_apply_1(x_2, x_10);
x_12 = lp_ScaleWordTheorems_instDecidableEqBinaryStep(x_5, x_1);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_int_add(x_8, x_11);
lean_dec(x_11);
lean_dec(x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lp_ScaleWordTheorems_largeChunkSize(x_3, x_4);
x_15 = lean_nat_div(x_3, x_4);
x_16 = lean_nat_to_int(x_14);
x_17 = lean_int_mul(x_8, x_16);
lean_dec(x_16);
lean_dec(x_8);
x_18 = lean_nat_to_int(x_15);
x_19 = lean_int_mul(x_11, x_18);
lean_dec(x_18);
lean_dec(x_11);
x_20 = lean_int_add(x_17, x_19);
lean_dec(x_19);
lean_dec(x_17);
return x_20;
}
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_liftGeneratorVectorX___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_1);
x_7 = lean_unbox(x_5);
x_8 = lp_ScaleWordTheorems_liftGeneratorVectorX(x_6, x_2, x_3, x_4, x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_liftedKStepSize(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_nat_add(x_2, x_3);
lean_inc(x_1);
x_5 = lp_ScaleWordTheorems_chunkBoundaryAt(x_1, x_4);
x_6 = lp_ScaleWordTheorems_chunkBoundaryAt(x_1, x_2);
x_7 = lean_nat_sub(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_liftedKStepSize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_ScaleWordTheorems_liftedKStepSize(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Multiset_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_ZMod_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic(uint8_t builtin);
lean_object* initialize_ScaleWordTheorems_ScaleWordTheorems_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ScaleWordTheorems_ScaleWordTheorems_MOS(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Multiset_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_ZMod_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ScaleWordTheorems_ScaleWordTheorems_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__0 = _init_lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__0();
lean_mark_persistent(lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__0);
lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__1 = _init_lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__1();
lean_mark_persistent(lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__1);
lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__2 = _init_lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__2();
lean_mark_persistent(lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__2);
lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__3 = _init_lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__3();
lean_mark_persistent(lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__3);
lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__4 = _init_lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__4();
lean_mark_persistent(lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__4);
lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__5 = _init_lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__5();
lean_mark_persistent(lp_ScaleWordTheorems_instReprBinaryStep_repr___closed__5);
lp_ScaleWordTheorems_instReprBinaryStep___closed__0 = _init_lp_ScaleWordTheorems_instReprBinaryStep___closed__0();
lean_mark_persistent(lp_ScaleWordTheorems_instReprBinaryStep___closed__0);
lp_ScaleWordTheorems_instReprBinaryStep = _init_lp_ScaleWordTheorems_instReprBinaryStep();
lean_mark_persistent(lp_ScaleWordTheorems_instReprBinaryStep);
lp_ScaleWordTheorems_instInhabitedBinaryStep_default = _init_lp_ScaleWordTheorems_instInhabitedBinaryStep_default();
lp_ScaleWordTheorems_instInhabitedBinaryStep = _init_lp_ScaleWordTheorems_instInhabitedBinaryStep();
lp_ScaleWordTheorems_BinaryStep_instFintype___closed__0 = _init_lp_ScaleWordTheorems_BinaryStep_instFintype___closed__0();
lean_mark_persistent(lp_ScaleWordTheorems_BinaryStep_instFintype___closed__0);
lp_ScaleWordTheorems_BinaryStep_instFintype___closed__1 = _init_lp_ScaleWordTheorems_BinaryStep_instFintype___closed__1();
lean_mark_persistent(lp_ScaleWordTheorems_BinaryStep_instFintype___closed__1);
lp_ScaleWordTheorems_BinaryStep_instFintype = _init_lp_ScaleWordTheorems_BinaryStep_instFintype();
lean_mark_persistent(lp_ScaleWordTheorems_BinaryStep_instFintype);
lp_ScaleWordTheorems_findGeneratorCoeff___closed__0 = _init_lp_ScaleWordTheorems_findGeneratorCoeff___closed__0();
lean_mark_persistent(lp_ScaleWordTheorems_findGeneratorCoeff___closed__0);
lp_ScaleWordTheorems_indices___redArg___closed__0 = _init_lp_ScaleWordTheorems_indices___redArg___closed__0();
lean_mark_persistent(lp_ScaleWordTheorems_indices___redArg___closed__0);
lp_ScaleWordTheorems_expandWord___closed__0 = _init_lp_ScaleWordTheorems_expandWord___closed__0();
lean_mark_persistent(lp_ScaleWordTheorems_expandWord___closed__0);
lp_ScaleWordTheorems_isChunkBoundary___closed__0 = _init_lp_ScaleWordTheorems_isChunkBoundary___closed__0();
lean_mark_persistent(lp_ScaleWordTheorems_isChunkBoundary___closed__0);
lp_ScaleWordTheorems_isChunkBoundary___closed__1 = _init_lp_ScaleWordTheorems_isChunkBoundary___closed__1();
lean_mark_persistent(lp_ScaleWordTheorems_isChunkBoundary___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
