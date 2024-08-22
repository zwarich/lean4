// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.RotateRight
// Imports: Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Basic Std.Sat.AIG.CachedGatesLemmas Std.Sat.AIG.LawfulVecOperator
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVExpr_bitblast_instLawfulVecOperatorShiftTargetBlastRotateRight___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVExpr_bitblast_instLawfulVecOperatorShiftTargetBlastRotateRight___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVExpr_bitblast_instLawfulVecOperatorShiftTargetBlastRotateRight(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_nat_dec_lt(x_7, x_3);
if (x_10 == 0)
{
lean_dec(x_7);
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_nat_mod(x_6, x_3);
x_12 = lean_nat_sub(x_3, x_11);
x_13 = lean_nat_dec_lt(x_7, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
x_14 = lean_nat_sub(x_7, x_12);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_7, x_15);
lean_dec(x_7);
x_17 = lean_array_fget(x_5, x_14);
lean_dec(x_14);
x_18 = lean_array_push(x_9, x_17);
x_7 = x_16;
x_8 = lean_box(0);
x_9 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
x_20 = lean_nat_add(x_11, x_7);
lean_dec(x_11);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_7, x_21);
lean_dec(x_7);
x_23 = lean_array_fget(x_5, x_20);
lean_dec(x_20);
x_24 = lean_array_push(x_9, x_23);
x_7 = x_22;
x_8 = lean_box(0);
x_9 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Elab_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___rarg___closed__1;
x_11 = l_Lean_Elab_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___rarg(x_1, x_2, x_3, x_4, x_7, x_8, x_9, lean_box(0), x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_ctor_set(x_5, 1, x_11);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Elab_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___rarg___closed__1;
x_16 = l_Lean_Elab_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight_go___rarg(x_1, x_2, x_3, x_4, x_12, x_13, x_14, lean_box(0), x_15);
lean_dec(x_13);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVExpr_bitblast_instLawfulVecOperatorShiftTargetBlastRotateRight___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVExpr_bitblast_instLawfulVecOperatorShiftTargetBlastRotateRight(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_BVExpr_bitblast_instLawfulVecOperatorShiftTargetBlastRotateRight___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_BVExpr_bitblast_instLawfulVecOperatorShiftTargetBlastRotateRight___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_BVDecide_BVExpr_bitblast_instLawfulVecOperatorShiftTargetBlastRotateRight___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_AIG_CachedGatesLemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateRight(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_CachedGatesLemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_LawfulVecOperator(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___rarg___closed__1 = _init_l_Lean_Elab_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_BVExpr_bitblast_blastRotateRight___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
