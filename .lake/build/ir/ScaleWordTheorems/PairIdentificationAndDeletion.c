// Lean compiler output
// Module: ScaleWordTheorems.PairIdentificationAndDeletion
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_TernaryNecklace_orderedDeletion___redArg___lam__1___boxed(lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_commRing(lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_TernaryNecklace_orderedDeletion___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterTR_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_TernaryNecklace_orderedDeletion___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_TernaryNecklace_orderedDeletion___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_TernaryNecklace_orderedDeletion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lp_ScaleWordTheorems_instDecidableEqStepSize(uint8_t, uint8_t);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* l_List_range(lean_object*);
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_TernaryNecklace_orderedDeletion___redArg___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_TernaryNecklace_orderedDeletion(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_TernaryNecklace_orderedDeletion___redArg___lam__2(lean_object*, lean_object*);
static lean_object* lp_ScaleWordTheorems_TernaryNecklace_orderedDeletion___redArg___closed__0;
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_TernaryNecklace_orderedDeletion___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_TernaryNecklace_orderedDeletion___redArg___lam__0(uint8_t x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lp_ScaleWordTheorems_instDecidableEqStepSize(x_2, x_1);
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
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_TernaryNecklace_orderedDeletion___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lp_ScaleWordTheorems_TernaryNecklace_orderedDeletion___redArg___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t lp_ScaleWordTheorems_TernaryNecklace_orderedDeletion___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_apply_1(x_1, x_2);
x_4 = lean_unbox(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_TernaryNecklace_orderedDeletion___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_ScaleWordTheorems_TernaryNecklace_orderedDeletion___redArg___lam__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_TernaryNecklace_orderedDeletion___redArg___lam__2(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_lp_ScaleWordTheorems_TernaryNecklace_orderedDeletion___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_TernaryNecklace_orderedDeletion___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_1);
x_4 = lp_mathlib_ZMod_commRing(x_1);
x_5 = lp_mathlib_Ring_toAddGroupWithOne___redArg(x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_box(x_3);
x_9 = lean_alloc_closure((void*)(lp_ScaleWordTheorems_TernaryNecklace_orderedDeletion___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_alloc_closure((void*)(lp_ScaleWordTheorems_TernaryNecklace_orderedDeletion___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_10, 0, x_2);
x_11 = lean_alloc_closure((void*)(lp_ScaleWordTheorems_TernaryNecklace_orderedDeletion___redArg___lam__2), 2, 1);
lean_closure_set(x_11, 0, x_7);
x_12 = l_List_range(x_1);
x_13 = lp_ScaleWordTheorems_TernaryNecklace_orderedDeletion___redArg___closed__0;
x_14 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(x_11, x_12, x_13);
x_15 = lean_box(0);
x_16 = l_List_mapTR_loop___redArg(x_10, x_14, x_15);
x_17 = l_List_filterTR_loop___redArg(x_9, x_16, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_TernaryNecklace_orderedDeletion(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_ScaleWordTheorems_TernaryNecklace_orderedDeletion___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_TernaryNecklace_orderedDeletion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
x_6 = lp_ScaleWordTheorems_TernaryNecklace_orderedDeletion(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_TernaryNecklace_orderedDeletion___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = lp_ScaleWordTheorems_TernaryNecklace_orderedDeletion___redArg(x_1, x_2, x_4);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Multiset_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_ZMod_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic(uint8_t builtin);
lean_object* initialize_ScaleWordTheorems_ScaleWordTheorems_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ScaleWordTheorems_ScaleWordTheorems_PairIdentificationAndDeletion(uint8_t builtin) {
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
lp_ScaleWordTheorems_TernaryNecklace_orderedDeletion___redArg___closed__0 = _init_lp_ScaleWordTheorems_TernaryNecklace_orderedDeletion___redArg___closed__0();
lean_mark_persistent(lp_ScaleWordTheorems_TernaryNecklace_orderedDeletion___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
