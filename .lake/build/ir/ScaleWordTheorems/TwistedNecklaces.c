// Lean compiler output
// Module: ScaleWordTheorems.TwistedNecklaces
// Imports: public import Init public import ScaleWordTheorems.Basic public import ScaleWordTheorems.MOS
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
LEAN_EXPORT lean_object* lp_ScaleWordTheorems___private_ScaleWordTheorems_TwistedNecklaces_0__TwistedConstruction_phiSubstAux_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_TwistedConstruction_phiSubstAux(uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_TwistedConstruction_phiSubstAux___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems___private_ScaleWordTheorems_TwistedNecklaces_0__TwistedConstruction_phiSubstAux_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems___private_ScaleWordTheorems_TwistedNecklaces_0__TwistedConstruction_phiSubstAux_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems___private_ScaleWordTheorems_TwistedNecklaces_0__TwistedConstruction_phiSubstAux_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_TwistedConstruction_phiSubst(lean_object*);
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_TwistedConstruction_phiSubstAux(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_unbox(x_4);
if (x_5 == 0)
{
if (x_1 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 0);
lean_dec(x_8);
x_9 = 0;
x_10 = 1;
x_11 = lp_ScaleWordTheorems_TwistedConstruction_phiSubstAux(x_10, x_7);
x_12 = lean_box(x_9);
lean_ctor_set(x_2, 1, x_11);
lean_ctor_set(x_2, 0, x_12);
return x_2;
}
else
{
lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = 0;
x_15 = 1;
x_16 = lp_ScaleWordTheorems_TwistedConstruction_phiSubstAux(x_15, x_13);
x_17 = lean_box(x_14);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_ctor_get(x_2, 0);
lean_dec(x_21);
x_22 = 1;
x_23 = 0;
x_24 = lp_ScaleWordTheorems_TwistedConstruction_phiSubstAux(x_23, x_20);
x_25 = lean_box(x_22);
lean_ctor_set(x_2, 1, x_24);
lean_ctor_set(x_2, 0, x_25);
return x_2;
}
else
{
lean_object* x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
lean_dec(x_2);
x_27 = 1;
x_28 = 0;
x_29 = lp_ScaleWordTheorems_TwistedConstruction_phiSubstAux(x_28, x_26);
x_30 = lean_box(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_2);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_2, 1);
x_34 = lean_ctor_get(x_2, 0);
lean_dec(x_34);
x_35 = 2;
x_36 = lp_ScaleWordTheorems_TwistedConstruction_phiSubstAux(x_1, x_33);
x_37 = lean_box(x_35);
lean_ctor_set(x_2, 1, x_36);
lean_ctor_set(x_2, 0, x_37);
return x_2;
}
else
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_2, 1);
lean_inc(x_38);
lean_dec(x_2);
x_39 = 2;
x_40 = lp_ScaleWordTheorems_TwistedConstruction_phiSubstAux(x_1, x_38);
x_41 = lean_box(x_39);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_TwistedConstruction_phiSubstAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = lp_ScaleWordTheorems_TwistedConstruction_phiSubstAux(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems_TwistedConstruction_phiSubst(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = 0;
x_3 = lp_ScaleWordTheorems_TwistedConstruction_phiSubstAux(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems___private_ScaleWordTheorems_TwistedNecklaces_0__TwistedConstruction_phiSubstAux_match__1_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_7 = lean_box(x_1);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_3);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_unbox(x_9);
if (x_10 == 0)
{
lean_dec(x_6);
if (x_1 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec_ref(x_2);
x_12 = lean_apply_1(x_4, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec_ref(x_2);
x_14 = lean_apply_1(x_5, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
lean_dec(x_4);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec_ref(x_2);
x_16 = lean_box(x_1);
x_17 = lean_apply_2(x_6, x_16, x_15);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems___private_ScaleWordTheorems_TwistedNecklaces_0__TwistedConstruction_phiSubstAux_match__1_splitter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_ScaleWordTheorems___private_ScaleWordTheorems_TwistedNecklaces_0__TwistedConstruction_phiSubstAux_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems___private_ScaleWordTheorems_TwistedNecklaces_0__TwistedConstruction_phiSubstAux_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = lp_ScaleWordTheorems___private_ScaleWordTheorems_TwistedNecklaces_0__TwistedConstruction_phiSubstAux_match__1_splitter(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_ScaleWordTheorems___private_ScaleWordTheorems_TwistedNecklaces_0__TwistedConstruction_phiSubstAux_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = lp_ScaleWordTheorems___private_ScaleWordTheorems_TwistedNecklaces_0__TwistedConstruction_phiSubstAux_match__1_splitter___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ScaleWordTheorems_ScaleWordTheorems_Basic(uint8_t builtin);
lean_object* initialize_ScaleWordTheorems_ScaleWordTheorems_MOS(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ScaleWordTheorems_ScaleWordTheorems_TwistedNecklaces(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ScaleWordTheorems_ScaleWordTheorems_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ScaleWordTheorems_ScaleWordTheorems_MOS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
