/* 
  This file was generated by KaRaMeL <https://github.com/FStarLang/karamel>
  KaRaMeL invocation: /home/aseem/everest/karamel/krml -warn-error +9 -skip-compilation -bundle Zeta.Steel.Application=Zeta.*,Prims,FStar.*,Hacl.*,Steel.* -library Zeta.Steel.VerifierTypes -library Steel.ST.Loops -library Steel.ST.Reference -static-header Steel.ST.Reference -no-prefix Zeta.Steel.LogEntry -no-prefix Zeta.Steel.LogEntry.Spec -hand-written Steel.ST.Reference _output/FStar_Algebra_CommMonoid_Equiv.krml _output/FStar_All.krml _output/FStar_BV.krml _output/FStar_BitVector.krml _output/FStar_Calc.krml _output/FStar_Char.krml _output/FStar_Classical.krml _output/FStar_Classical_Sugar.krml _output/FStar_ErasedLogic.krml _output/FStar_Exn.krml _output/FStar_FunctionalExtensionality.krml _output/FStar_Ghost.krml _output/FStar_Heap.krml _output/FStar_IndefiniteDescription.krml _output/FStar_Int.krml _output/FStar_Int16.krml _output/FStar_Int32.krml _output/FStar_Int64.krml _output/FStar_Int8.krml _output/FStar_Int_Cast.krml _output/FStar_IntegerIntervals.krml _output/FStar_List.krml _output/FStar_List_Tot.krml _output/FStar_List_Tot_Base.krml _output/FStar_List_Tot_Properties.krml _output/FStar_Map.krml _output/FStar_Math_Lemmas.krml _output/FStar_Math_Lib.krml _output/FStar_Monotonic_Heap.krml _output/FStar_Monotonic_Pure.krml _output/FStar_Monotonic_Witnessed.krml _output/FStar_Mul.krml _output/FStar_Order.krml _output/FStar_PCM.krml _output/FStar_PartialMap.krml _output/FStar_Pervasives.krml _output/FStar_Pervasives_Native.krml _output/FStar_PredicateExtensionality.krml _output/FStar_Preorder.krml _output/FStar_PropositionalExtensionality.krml _output/FStar_Range.krml _output/FStar_Real.krml _output/FStar_Reflection.krml _output/FStar_Reflection_Builtins.krml _output/FStar_Reflection_Const.krml _output/FStar_Reflection_Data.krml _output/FStar_Reflection_Derived.krml _output/FStar_Reflection_Derived_Lemmas.krml _output/FStar_Reflection_Formula.krml _output/FStar_Reflection_Types.krml _output/FStar_ST.krml _output/FStar_Seq.krml _output/FStar_Seq_Base.krml _output/FStar_Seq_Equiv.krml _output/FStar_Seq_Permutation.krml _output/FStar_Seq_Properties.krml _output/FStar_Set.krml _output/FStar_Squash.krml _output/FStar_String.krml _output/FStar_StrongExcludedMiddle.krml _output/FStar_TSet.krml _output/FStar_Tactics.krml _output/FStar_Tactics_Builtins.krml _output/FStar_Tactics_CanonCommMonoidSimple_Equiv.krml _output/FStar_Tactics_CanonCommSwaps.krml _output/FStar_Tactics_Common.krml _output/FStar_Tactics_Derived.krml _output/FStar_Tactics_Effect.krml _output/FStar_Tactics_Logic.krml _output/FStar_Tactics_Print.krml _output/FStar_Tactics_Result.krml _output/FStar_Tactics_SyntaxHelpers.krml _output/FStar_Tactics_Types.krml _output/FStar_Tactics_Util.krml _output/FStar_UInt.krml _output/FStar_UInt16.krml _output/FStar_UInt32.krml _output/FStar_UInt64.krml _output/FStar_UInt8.krml _output/FStar_Universe.krml _output/FStar_Universe_PCM.krml _output/FStar_VConfig.krml _output/FStar_WellFounded.krml _output/Hacl_Blake2b_32.krml _output/Zeta_App.krml _output/Zeta_AppSimulate.krml _output/Zeta_BinTree.krml _output/Zeta_Ghost.krml _output/Zeta_Hash.krml _output/Zeta_IdxFn.krml _output/Zeta_Interleave.krml _output/Zeta_Key.krml _output/Zeta_KeyValueStore_Formats.krml _output/Zeta_KeyValueStore_Spec.krml _output/Zeta_KeyValueStore_StateMachine.krml _output/Zeta_MultiSet.krml _output/Zeta_SSeq.krml _output/Zeta_SeqAux.krml _output/Zeta_SeqIdx.krml _output/Zeta_Steel_AggregateEpochHashes.krml _output/Zeta_Steel_Application.krml _output/Zeta_Steel_ApplicationRecord.krml _output/Zeta_Steel_ApplicationTypes.krml _output/Zeta_Steel_BitUtils.krml _output/Zeta_Steel_EpochHashes.krml _output/Zeta_Steel_EpochMap.krml _output/Zeta_Steel_FormatsManual.krml _output/Zeta_Steel_HashAccumulator.krml _output/Zeta_Steel_HashValue.krml _output/Zeta_Steel_KeyUtils.krml _output/Zeta_Steel_LogEntry.krml _output/Zeta_Steel_LogEntry_Spec.krml _output/Zeta_Steel_LogEntry_Types.krml _output/Zeta_Steel_Parser.krml _output/Zeta_Steel_ThreadLogMap.krml _output/Zeta_Steel_ThreadStateModel.krml _output/Zeta_Steel_Util.krml _output/Zeta_Steel_VerifierTypes.krml _output/out.krml -tmpdir=_output
  F* version: c75b6da5
  KaRaMeL version: 101a7abe
 */

#ifndef __Zeta_Steel_Application_H
#define __Zeta_Steel_Application_H

#include "krmllib.h"




typedef struct Zeta_Steel_KeyUtils_u256_s
{
  uint64_t v3;
  uint64_t v2;
  uint64_t v1;
  uint64_t v0;
}
Zeta_Steel_KeyUtils_u256;

typedef struct Zeta_Steel_KeyUtils_raw_key_s
{
  Zeta_Steel_KeyUtils_u256 k;
  uint16_t significant_digits;
}
Zeta_Steel_KeyUtils_raw_key;

typedef struct Zeta_Steel_LogEntry_Types_runApp_payload_s
{
  uint8_t fid;
  uint32_t rest;
}
Zeta_Steel_LogEntry_Types_runApp_payload;

typedef struct Zeta_Steel_VerifierTypes_thread_state_t_s
Zeta_Steel_VerifierTypes_thread_state_t;

typedef void *Zeta_Steel_Application_n_out_bytes;

#define Zeta_Steel_Application_Run_app_parsing_failure 0
#define Zeta_Steel_Application_Run_app_verify_failure 1
#define Zeta_Steel_Application_Run_app_success 2

typedef uint8_t Zeta_Steel_Application_verify_runapp_result_tags;

typedef struct Zeta_Steel_Application_verify_runapp_result_s
{
  Zeta_Steel_Application_verify_runapp_result_tags tag;
  uint32_t wrote;
}
Zeta_Steel_Application_verify_runapp_result;

bool
Zeta_Steel_Application_uu___is_Run_app_parsing_failure(
  Zeta_Steel_Application_verify_runapp_result projectee
);

bool
Zeta_Steel_Application_uu___is_Run_app_verify_failure(
  Zeta_Steel_Application_verify_runapp_result projectee
);

bool
Zeta_Steel_Application_uu___is_Run_app_success(
  Zeta_Steel_Application_verify_runapp_result projectee
);

extern bool
__eq__Zeta_KeyValueStore_Formats_key_t(
  Zeta_KeyValueStore_Formats_key_t x,
  Zeta_KeyValueStore_Formats_key_t y
);

extern bool
__eq__Zeta_KeyValueStore_Formats_value_t(
  Zeta_KeyValueStore_Formats_value_t x,
  Zeta_KeyValueStore_Formats_value_t y
);

Zeta_Steel_Application_verify_runapp_result
Zeta_Steel_Application_run_app_function(
  uint32_t log_len,
  Zeta_Steel_LogEntry_Types_runApp_payload pl,
  uint32_t pl_pos,
  uint8_t *log_array,
  uint32_t out_len,
  uint32_t out_offset,
  uint8_t *out,
  Zeta_Steel_VerifierTypes_thread_state_t t
);

Zeta_Steel_KeyUtils_raw_key
Zeta_Steel_Application_key_type_to_base_key(Zeta_KeyValueStore_Formats_key_t uu___);


#define __Zeta_Steel_Application_H_DEFINED
#endif
