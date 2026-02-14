// Lean compiler output
// Module: ScaleWordTheorems.MV3
// Imports: public import Init public import ScaleWordTheorems.Basic public import ScaleWordTheorems.MOS public import ScaleWordTheorems.Permutation public import ScaleWordTheorems.PairIdentificationAndDeletion public import ScaleWordTheorems.TwistedNecklaces
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ScaleWordTheorems_ScaleWordTheorems_Basic(uint8_t builtin);
lean_object* initialize_ScaleWordTheorems_ScaleWordTheorems_MOS(uint8_t builtin);
lean_object* initialize_ScaleWordTheorems_ScaleWordTheorems_Permutation(uint8_t builtin);
lean_object* initialize_ScaleWordTheorems_ScaleWordTheorems_PairIdentificationAndDeletion(uint8_t builtin);
lean_object* initialize_ScaleWordTheorems_ScaleWordTheorems_TwistedNecklaces(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ScaleWordTheorems_ScaleWordTheorems_MV3(uint8_t builtin) {
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
res = initialize_ScaleWordTheorems_ScaleWordTheorems_Permutation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ScaleWordTheorems_ScaleWordTheorems_PairIdentificationAndDeletion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ScaleWordTheorems_ScaleWordTheorems_TwistedNecklaces(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
