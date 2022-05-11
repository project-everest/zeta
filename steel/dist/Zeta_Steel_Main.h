/* 
  This file was generated by KaRaMeL <https://github.com/FStarLang/karamel>
  KaRaMeL invocation: C:\cygwin64\home\nswamy\workspace\everest\karamel\_build\src\Karamel.native -warn-error +9 -skip-compilation -bundle Zeta.Steel.Main=Zeta.*,Prims,FStar.*,Hacl.*,Steel.* -library Steel.ST.Loops -library Steel.ST.Reference -static-header Steel.ST.Reference -no-prefix Zeta.Steel.LogEntry -no-prefix Zeta.Steel.LogEntry.Spec -hand-written Steel.ST.Reference ../_output/FStar_Algebra_CommMonoid_Equiv.krml ../_output/FStar_All.krml ../_output/FStar_BV.krml ../_output/FStar_BitVector.krml ../_output/FStar_Calc.krml ../_output/FStar_Char.krml ../_output/FStar_Classical.krml ../_output/FStar_Classical_Sugar.krml ../_output/FStar_ErasedLogic.krml ../_output/FStar_Exn.krml ../_output/FStar_FunctionalExtensionality.krml ../_output/FStar_Ghost.krml ../_output/FStar_Heap.krml ../_output/FStar_IndefiniteDescription.krml ../_output/FStar_Int.krml ../_output/FStar_Int16.krml ../_output/FStar_Int32.krml ../_output/FStar_Int64.krml ../_output/FStar_Int8.krml ../_output/FStar_Int_Cast.krml ../_output/FStar_IntegerIntervals.krml ../_output/FStar_List.krml ../_output/FStar_List_Tot.krml ../_output/FStar_List_Tot_Base.krml ../_output/FStar_List_Tot_Properties.krml ../_output/FStar_Map.krml ../_output/FStar_Math_Lemmas.krml ../_output/FStar_Math_Lib.krml ../_output/FStar_Monotonic_Heap.krml ../_output/FStar_Monotonic_Pure.krml ../_output/FStar_Monotonic_Witnessed.krml ../_output/FStar_Mul.krml ../_output/FStar_Order.krml ../_output/FStar_PCM.krml ../_output/FStar_PartialMap.krml ../_output/FStar_Pervasives.krml ../_output/FStar_Pervasives_Native.krml ../_output/FStar_PredicateExtensionality.krml ../_output/FStar_Preorder.krml ../_output/FStar_PropositionalExtensionality.krml ../_output/FStar_Range.krml ../_output/FStar_Real.krml ../_output/FStar_Reflection.krml ../_output/FStar_Reflection_Builtins.krml ../_output/FStar_Reflection_Const.krml ../_output/FStar_Reflection_Data.krml ../_output/FStar_Reflection_Derived.krml ../_output/FStar_Reflection_Derived_Lemmas.krml ../_output/FStar_Reflection_Formula.krml ../_output/FStar_Reflection_Types.krml ../_output/FStar_ST.krml ../_output/FStar_Seq.krml ../_output/FStar_Seq_Base.krml ../_output/FStar_Seq_Equiv.krml ../_output/FStar_Seq_Permutation.krml ../_output/FStar_Seq_Properties.krml ../_output/FStar_Set.krml ../_output/FStar_Squash.krml ../_output/FStar_String.krml ../_output/FStar_StrongExcludedMiddle.krml ../_output/FStar_TSet.krml ../_output/FStar_Tactics.krml ../_output/FStar_Tactics_Builtins.krml ../_output/FStar_Tactics_CanonCommMonoidSimple_Equiv.krml ../_output/FStar_Tactics_CanonCommSwaps.krml ../_output/FStar_Tactics_Common.krml ../_output/FStar_Tactics_Derived.krml ../_output/FStar_Tactics_Effect.krml ../_output/FStar_Tactics_Logic.krml ../_output/FStar_Tactics_Print.krml ../_output/FStar_Tactics_Result.krml ../_output/FStar_Tactics_SyntaxHelpers.krml ../_output/FStar_Tactics_Types.krml ../_output/FStar_Tactics_Util.krml ../_output/FStar_UInt.krml ../_output/FStar_UInt16.krml ../_output/FStar_UInt32.krml ../_output/FStar_UInt64.krml ../_output/FStar_UInt8.krml ../_output/FStar_Universe.krml ../_output/FStar_Universe_PCM.krml ../_output/FStar_VConfig.krml ../_output/FStar_WellFounded.krml ../_output/Hacl_Blake2b_32.krml ../_output/Steel_ST_Array_Util.krml ../_output/Steel_ST_CancellableSpinLock.krml ../_output/Steel_ST_EphemeralHashtbl.krml ../_output/Steel_ST_Loops.krml ../_output/Steel_ST_Reference.krml ../_output/Steel_ST_SpinLock.krml ../_output/Zeta_App.krml ../_output/Zeta_AppSimulate.krml ../_output/Zeta_AppSimulate_Helper.krml ../_output/Zeta_BinTree.krml ../_output/Zeta_BinTreePtr.krml ../_output/Zeta_Correctness.krml ../_output/Zeta_EAC.krml ../_output/Zeta_GenKey.krml ../_output/Zeta_GenericVerifier.krml ../_output/Zeta_Generic_Blum.krml ../_output/Zeta_Generic_Global.krml ../_output/Zeta_Generic_Interleave.krml ../_output/Zeta_Generic_TSLog.krml ../_output/Zeta_Generic_Thread.krml ../_output/Zeta_Hash.krml ../_output/Zeta_HashCollision.krml ../_output/Zeta_HashFunction.krml ../_output/Zeta_High_Blum.krml ../_output/Zeta_High_Global.krml ../_output/Zeta_High_Interleave.krml ../_output/Zeta_High_Merkle.krml ../_output/Zeta_High_SeqConsistent.krml ../_output/Zeta_High_TSLog.krml ../_output/Zeta_High_Thread.krml ../_output/Zeta_High_Verifier.krml ../_output/Zeta_High_Verifier_EAC.krml ../_output/Zeta_IdxFn.krml ../_output/Zeta_Interleave.krml ../_output/Zeta_Intermediate_Blum.krml ../_output/Zeta_Intermediate_Correctness.krml ../_output/Zeta_Intermediate_Global.krml ../_output/Zeta_Intermediate_Interleave.krml ../_output/Zeta_Intermediate_Logs.krml ../_output/Zeta_Intermediate_SlotKeyRel.krml ../_output/Zeta_Intermediate_StateRel.krml ../_output/Zeta_Intermediate_Store.krml ../_output/Zeta_Intermediate_TSLog.krml ../_output/Zeta_Intermediate_Thread.krml ../_output/Zeta_Intermediate_Verifier.krml ../_output/Zeta_Intermediate_VerifierConfig.krml ../_output/Zeta_Key.krml ../_output/Zeta_Merkle.krml ../_output/Zeta_MultiSet.krml ../_output/Zeta_MultiSetHashDomain.krml ../_output/Zeta_MultiSet_SSeq.krml ../_output/Zeta_Record.krml ../_output/Zeta_SMap.krml ../_output/Zeta_SSeq.krml ../_output/Zeta_SeqAux.krml ../_output/Zeta_SeqIdx.krml ../_output/Zeta_SeqMachine.krml ../_output/Zeta_Steel_AddMRel.krml ../_output/Zeta_Steel_AggregateEpochHashes.krml ../_output/Zeta_Steel_AppSim.krml ../_output/Zeta_Steel_Application.krml ../_output/Zeta_Steel_ApplicationRecord.krml ../_output/Zeta_Steel_ApplicationTypes.krml ../_output/Zeta_Steel_BitUtils.krml ../_output/Zeta_Steel_EpochHashes.krml ../_output/Zeta_Steel_EpochMap.krml ../_output/Zeta_Steel_FormatsManual.krml ../_output/Zeta_Steel_GlobalRel.krml ../_output/Zeta_Steel_HashAccumulator.krml ../_output/Zeta_Steel_HashValue.krml ../_output/Zeta_Steel_KeyUtils.krml ../_output/Zeta_Steel_Log.krml ../_output/Zeta_Steel_LogEntry.krml ../_output/Zeta_Steel_LogEntry_Spec.krml ../_output/Zeta_Steel_LogEntry_Types.krml ../_output/Zeta_Steel_LogRel.krml ../_output/Zeta_Steel_Main.krml ../_output/Zeta_Steel_MultiSetHash.krml ../_output/Zeta_Steel_Parser.krml ../_output/Zeta_Steel_Rel.krml ../_output/Zeta_Steel_RelHashFunction.krml ../_output/Zeta_Steel_StoreRel.krml ../_output/Zeta_Steel_Thread.krml ../_output/Zeta_Steel_ThreadLogMap.krml ../_output/Zeta_Steel_ThreadRel.krml ../_output/Zeta_Steel_ThreadRelDef.krml ../_output/Zeta_Steel_ThreadSim.krml ../_output/Zeta_Steel_ThreadStateModel.krml ../_output/Zeta_Steel_Util.krml ../_output/Zeta_Steel_Verifier.krml ../_output/Zeta_Steel_VerifierSteps.krml ../_output/Zeta_Steel_VerifierTypes.krml ../_output/Zeta_Thread.krml ../_output/Zeta_Time.krml ../_output/out.krml -tmpdir=../_output -add-include "steel_atomics.h" -add-include "zeta_application.h"
  F* version: d80633a7
  KaRaMeL version: 8f67a79f
 */

#ifndef __Zeta_Steel_Main_H
#define __Zeta_Steel_Main_H

#include "krmllib.h"



#include "steel_atomics.h"
#include "zeta_application.h"
static inline bool Steel_ST_Reference_cas_u32(uint32_t *r, uint32_t v_old, uint32_t v_new);

typedef struct Steel_ST_CancellableSpinLock_cancellable_lock_s
{
  bool *lref;
  uint32_t *llock;
}
Steel_ST_CancellableSpinLock_cancellable_lock;

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

extern Zeta_Steel_KeyUtils_raw_key Zeta_Steel_KeyUtils_root_raw_key;

extern Zeta_Steel_KeyUtils_raw_key Zeta_Steel_KeyUtils_root_base_key;

typedef struct Zeta_Steel_LogEntry_Types_timestamp_s
{
  uint32_t epoch;
  uint32_t counter;
}
Zeta_Steel_LogEntry_Types_timestamp;

#define Zeta_Steel_LogEntry_Types_Vfalse 0
#define Zeta_Steel_LogEntry_Types_Vtrue 1

typedef uint8_t Zeta_Steel_LogEntry_Types_vbool;

typedef struct Zeta_Steel_LogEntry_Types_descendent_hash_desc_s
{
  Zeta_Steel_KeyUtils_raw_key dhd_key;
  Zeta_Steel_KeyUtils_u256 dhd_h;
  Zeta_Steel_LogEntry_Types_vbool evicted_to_blum;
}
Zeta_Steel_LogEntry_Types_descendent_hash_desc;

#define Zeta_Steel_LogEntry_Types_Dh_vnone 0
#define Zeta_Steel_LogEntry_Types_Dh_vsome 1

typedef uint8_t Zeta_Steel_LogEntry_Types_descendent_hash_tags;

typedef struct Zeta_Steel_LogEntry_Types_descendent_hash_s
{
  Zeta_Steel_LogEntry_Types_descendent_hash_tags tag;
  Zeta_Steel_LogEntry_Types_descendent_hash_desc _0;
}
Zeta_Steel_LogEntry_Types_descendent_hash;

typedef struct Zeta_Steel_LogEntry_Types_mval_value_s
{
  Zeta_Steel_LogEntry_Types_descendent_hash l;
  Zeta_Steel_LogEntry_Types_descendent_hash r;
}
Zeta_Steel_LogEntry_Types_mval_value;

#define Zeta_Steel_LogEntry_Types_InternalKey 0
#define Zeta_Steel_LogEntry_Types_ApplicationKey 1

typedef uint8_t Zeta_Steel_LogEntry_Types_key_tags;

typedef struct Zeta_Steel_LogEntry_Types_key_s
{
  Zeta_Steel_LogEntry_Types_key_tags tag;
  union {
    Zeta_Steel_KeyUtils_raw_key case_InternalKey;
    Zeta_Steel_ApplicationTypes_key_type case_ApplicationKey;
  }
  ;
}
Zeta_Steel_LogEntry_Types_key;

extern Zeta_Steel_LogEntry_Types_key Zeta_Steel_LogEntry_Types_root_key;

#define FStar_Pervasives_Native_None 0
#define FStar_Pervasives_Native_Some 1

typedef uint8_t FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type_tags;

typedef struct FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type_s
{
  FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type_tags tag;
  Zeta_Steel_ApplicationTypes_value_type v;
}
FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type;

#define Zeta_Steel_LogEntry_Types_MValue 0
#define Zeta_Steel_LogEntry_Types_DValue 1

typedef uint8_t Zeta_Steel_LogEntry_Types_value_tags;

typedef struct Zeta_Steel_LogEntry_Types_value_s
{
  Zeta_Steel_LogEntry_Types_value_tags tag;
  union {
    Zeta_Steel_LogEntry_Types_mval_value case_MValue;
    FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type case_DValue;
  }
  ;
}
Zeta_Steel_LogEntry_Types_value;

extern Zeta_Steel_KeyUtils_u256 Zeta_Steel_BitUtils_zero256;

typedef struct Zeta_Steel_HashAccumulator_ha_s
{
  uint8_t *acc;
  uint32_t *ctr;
}
Zeta_Steel_HashAccumulator_ha;

typedef struct FStar_Pervasives_Native_option__uint32_t_s
{
  FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type_tags tag;
  uint32_t v;
}
FStar_Pervasives_Native_option__uint32_t;

#define Zeta_Steel_ThreadStateModel_MAdd 0
#define Zeta_Steel_ThreadStateModel_BAdd 1

typedef uint8_t Zeta_Steel_ThreadStateModel_add_method;

typedef struct FStar_Pervasives_Native_option__uint16_t_s
{
  FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type_tags tag;
  uint16_t v;
}
FStar_Pervasives_Native_option__uint16_t;

typedef struct K___uint16_t_bool_s
{
  uint16_t fst;
  bool snd;
}
K___uint16_t_bool;

typedef struct FStar_Pervasives_Native_option__K___uint16_t_bool_s
{
  FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type_tags tag;
  K___uint16_t_bool v;
}
FStar_Pervasives_Native_option__K___uint16_t_bool;

typedef struct Zeta_Steel_ThreadStateModel_store_entry_s
{
  Zeta_Steel_LogEntry_Types_key key;
  Zeta_Steel_LogEntry_Types_value value;
  Zeta_Steel_ThreadStateModel_add_method add_method;
  FStar_Pervasives_Native_option__uint16_t l_child_in_store;
  FStar_Pervasives_Native_option__uint16_t r_child_in_store;
  FStar_Pervasives_Native_option__K___uint16_t_bool parent_slot;
}
Zeta_Steel_ThreadStateModel_store_entry;

extern Zeta_Steel_KeyUtils_u256 Zeta_Steel_ThreadStateModel_zero;

typedef struct Zeta_Steel_EpochHashes_epoch_hashes_t_s
{
  Zeta_Steel_HashAccumulator_ha hadd;
  Zeta_Steel_HashAccumulator_ha hevict;
}
Zeta_Steel_EpochHashes_epoch_hashes_t;

typedef struct K___uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t_s
{
  uint32_t fst;
  Zeta_Steel_EpochHashes_epoch_hashes_t snd;
}
K___uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t;

typedef struct
FStar_Pervasives_Native_option__K___uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t_s
{
  FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type_tags tag;
  K___uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t v;
}
FStar_Pervasives_Native_option__K___uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t;

typedef struct Steel_ST_EphemeralHashtbl_tbl__uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t_s
{
  uint32_t store_len;
  FStar_Pervasives_Native_option__K___uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t *store;
}
Steel_ST_EphemeralHashtbl_tbl__uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t;

typedef struct Zeta_Steel_AggregateEpochHashes_all_epoch_hashes_s
{
  Steel_ST_EphemeralHashtbl_tbl__uint32_t_Zeta_Steel_EpochHashes_epoch_hashes_t etbl;
  uint32_t *high;
}
Zeta_Steel_AggregateEpochHashes_all_epoch_hashes;

typedef struct K___uint32_t__bool__s
{
  uint32_t fst;
  bool *snd;
}
K___uint32_t__bool_;

typedef struct FStar_Pervasives_Native_option__K___uint32_t__bool__s
{
  FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type_tags tag;
  K___uint32_t__bool_ v;
}
FStar_Pervasives_Native_option__K___uint32_t__bool_;

typedef struct Steel_ST_EphemeralHashtbl_tbl__uint32_t__bool__s
{
  uint32_t store_len;
  FStar_Pervasives_Native_option__K___uint32_t__bool_ *store;
}
Steel_ST_EphemeralHashtbl_tbl__uint32_t__bool_;

typedef struct Zeta_Steel_AggregateEpochHashes_epoch_tid_bitmaps_s
{
  Steel_ST_EphemeralHashtbl_tbl__uint32_t__bool_ etbl;
  uint32_t *high;
}
Zeta_Steel_AggregateEpochHashes_epoch_tid_bitmaps;

typedef struct Zeta_Steel_AggregateEpochHashes_aggregate_epoch_hashes_s
Zeta_Steel_AggregateEpochHashes_aggregate_epoch_hashes;

#define Zeta_Steel_AggregateEpochHashes_Read_max_error 0
#define Zeta_Steel_AggregateEpochHashes_Read_max_none 1
#define Zeta_Steel_AggregateEpochHashes_Read_max_some 2

typedef uint8_t Zeta_Steel_AggregateEpochHashes_max_certified_epoch_result_tags;

typedef struct Zeta_Steel_AggregateEpochHashes_max_certified_epoch_result_s
{
  Zeta_Steel_AggregateEpochHashes_max_certified_epoch_result_tags tag;
  uint32_t _0;
}
Zeta_Steel_AggregateEpochHashes_max_certified_epoch_result;

typedef struct Zeta_Steel_HashValue_hasher_t_s Zeta_Steel_HashValue_hasher_t;

typedef struct FStar_Pervasives_Native_option__Zeta_Steel_ThreadStateModel_store_entry_s
{
  FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type_tags tag;
  Zeta_Steel_ThreadStateModel_store_entry v;
}
FStar_Pervasives_Native_option__Zeta_Steel_ThreadStateModel_store_entry;

typedef struct Zeta_Steel_VerifierTypes_thread_state_t_s
Zeta_Steel_VerifierTypes_thread_state_t;

typedef struct Zeta_Steel_VerifierTypes_kv_s
{
  Zeta_Steel_LogEntry_Types_key key;
  Zeta_Steel_LogEntry_Types_value value;
}
Zeta_Steel_VerifierTypes_kv;

#define Zeta_Steel_Verifier_Parsing_failure 0
#define Zeta_Steel_Verifier_App_failure 1
#define Zeta_Steel_Verifier_Verify_entry_failure 2
#define Zeta_Steel_Verifier_Verify_success 3

typedef uint8_t Zeta_Steel_Verifier_verify_result_tags;

typedef struct Zeta_Steel_Verifier_verify_result_s
{
  Zeta_Steel_Verifier_verify_result_tags tag;
  union {
    uint32_t case_Parsing_failure;
    uint32_t case_App_failure;
    uint32_t case_Verify_entry_failure;
    struct
    {
      uint32_t read;
      uint32_t wrote;
    }
    case_Verify_success;
  }
  ;
}
Zeta_Steel_Verifier_verify_result;

typedef struct Zeta_Steel_Main_thread_state_s Zeta_Steel_Main_thread_state;

typedef struct Zeta_Steel_Main_top_level_state_s Zeta_Steel_Main_top_level_state;

Zeta_Steel_Main_top_level_state *Zeta_Steel_Main_init();

typedef struct FStar_Pervasives_Native_option__Zeta_Steel_Verifier_verify_result_s
{
  FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type_tags tag;
  Zeta_Steel_Verifier_verify_result v;
}
FStar_Pervasives_Native_option__Zeta_Steel_Verifier_verify_result;

FStar_Pervasives_Native_option__Zeta_Steel_Verifier_verify_result
Zeta_Steel_Main_verify_log(
  Zeta_Steel_Main_top_level_state *r,
  uint16_t tid,
  uint32_t len,
  uint8_t *input,
  uint32_t out_len,
  uint8_t *output
);

Zeta_Steel_AggregateEpochHashes_max_certified_epoch_result
Zeta_Steel_Main_max_certified_epoch(Zeta_Steel_Main_top_level_state *r);

typedef struct FStar_Pervasives_Native_option__Zeta_Steel_VerifierTypes_kv_s
{
  FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type_tags tag;
  Zeta_Steel_VerifierTypes_kv v;
}
FStar_Pervasives_Native_option__Zeta_Steel_VerifierTypes_kv;

FStar_Pervasives_Native_option__Zeta_Steel_VerifierTypes_kv
Zeta_Steel_Main_read_store(Zeta_Steel_VerifierTypes_thread_state_t t, uint16_t slot);

void
Zeta_Steel_Main_write_store(
  Zeta_Steel_VerifierTypes_thread_state_t t,
  uint16_t slot,
  Zeta_Steel_LogEntry_Types_value v
);


#define __Zeta_Steel_Main_H_DEFINED
#endif
