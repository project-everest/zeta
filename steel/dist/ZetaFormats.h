/* 
  This file was generated by KaRaMeL <https://github.com/FStarLang/karamel>
  KaRaMeL invocation: C:\cygwin64\home\nswamy\workspace\everest\karamel\_build\src\Karamel.native -tmpdir out -skip-compilation _output/FStar_Pervasives_Native.krml _output/FStar_Pervasives.krml _output/FStar_Mul.krml _output/FStar_Squash.krml _output/FStar_Classical.krml _output/FStar_Preorder.krml _output/FStar_Calc.krml _output/FStar_StrongExcludedMiddle.krml _output/FStar_Classical_Sugar.krml _output/FStar_List_Tot_Base.krml _output/FStar_List_Tot_Properties.krml _output/FStar_List_Tot.krml _output/FStar_Seq_Base.krml _output/FStar_Seq_Properties.krml _output/FStar_Seq.krml _output/FStar_Math_Lib.krml _output/FStar_Math_Lemmas.krml _output/FStar_BitVector.krml _output/FStar_UInt.krml _output/FStar_UInt32.krml _output/FStar_Int.krml _output/FStar_Int16.krml _output/FStar_Range.krml _output/FStar_Tactics_Common.krml _output/FStar_VConfig.krml _output/FStar_Reflection_Types.krml _output/FStar_Tactics_Types.krml _output/FStar_Tactics_Result.krml _output/FStar_Tactics_Effect.krml _output/FStar_Reflection_Data.krml _output/FStar_Tactics_Builtins.krml _output/FStar_FunctionalExtensionality.krml _output/FStar_Set.krml _output/FStar_Ghost.krml _output/FStar_ErasedLogic.krml _output/FStar_PropositionalExtensionality.krml _output/FStar_PredicateExtensionality.krml _output/FStar_TSet.krml _output/FStar_Monotonic_Heap.krml _output/FStar_Heap.krml _output/FStar_Map.krml _output/FStar_Monotonic_Witnessed.krml _output/FStar_Monotonic_HyperHeap.krml _output/FStar_Monotonic_HyperStack.krml _output/FStar_HyperStack.krml _output/FStar_HyperStack_ST.krml _output/FStar_Universe.krml _output/FStar_GSet.krml _output/FStar_ModifiesGen.krml _output/FStar_Reflection_Const.krml _output/FStar_Order.krml _output/FStar_Reflection_Builtins.krml _output/FStar_Reflection_Derived.krml _output/FStar_Reflection_Derived_Lemmas.krml _output/FStar_Reflection.krml _output/FStar_Tactics_Print.krml _output/FStar_Tactics_SyntaxHelpers.krml _output/FStar_Tactics_Util.krml _output/FStar_IndefiniteDescription.krml _output/FStar_Reflection_Formula.krml _output/FStar_Tactics_Derived.krml _output/FStar_Tactics_Logic.krml _output/FStar_Tactics.krml _output/FStar_BigOps.krml _output/LowStar_Monotonic_Buffer.krml _output/LowStar_Buffer.krml _output/LowStar_Modifies.krml _output/FStar_Char.krml _output/FStar_Exn.krml _output/FStar_ST.krml _output/FStar_All.krml _output/FStar_List.krml _output/FStar_String.krml _output/FStar_UInt64.krml _output/FStar_UInt16.krml _output/FStar_UInt8.krml _output/FStar_Bytes.krml _output/Spec_Loops.krml _output/LowStar_BufferOps.krml _output/C_Loops.krml _output/FStar_Int64.krml _output/FStar_Int32.krml _output/FStar_Int8.krml _output/FStar_Int_Cast.krml _output/LowParse_Bytes.krml _output/LowParse_Norm.krml _output/LowParse_Spec_Base.krml _output/LowParse_Spec_Combinators.krml _output/LowParse_Spec_FLData.krml _output/LowStar_Comment.krml _output/LowParse_Math.krml _output/LowParse_BitFields.krml _output/LowParse_Low_ErrorCode.krml _output/LowParse_Slice.krml _output/LowParse_Low_Base_Spec.krml _output/LowParse_Low_Base.krml _output/LowStar_Failure.krml _output/LowParse_Low_Combinators.krml _output/LowParse_Low_FLData.krml _output/FStar_Endianness.krml _output/LowParse_Spec_Seq.krml _output/LowParse_Spec_Int.krml _output/LowParse_Spec_BoundedInt.krml _output/FStar_UInt128.krml _output/LowStar_Endianness.krml _output/LowParse_Low_Endianness.krml _output/LowParse_Endianness.krml _output/LowParse_Endianness_BitFields.krml _output/LowParse_Low_BoundedInt.krml _output/LowParse_Spec_SeqBytes_Base.krml _output/LowParse_Spec_DER.krml _output/LowParse_Spec_BCVLI.krml _output/LowParse_Spec_AllIntegers.krml _output/LowParse_Spec_VLData.krml _output/LowParse_Low_VLData.krml _output/LowParse_Spec_VLGen.krml _output/LowParse_Low_VLGen.krml _output/LowParse_Low_Int.krml _output/LowParse_Low_DER.krml _output/LowParse_Low_BCVLI.krml _output/LowParse_Spec_List.krml _output/LowParse_Low_List.krml _output/LowParse_Spec_Array.krml _output/LowParse_Spec_VCList.krml _output/LowParse_Low_VCList.krml _output/LowParse_Spec_IfThenElse.krml _output/LowParse_Low_IfThenElse.krml _output/LowParse_TacLib.krml _output/LowParse_Spec_Enum.krml _output/LowParse_Spec_Sum.krml _output/LowParse_Low_Enum.krml _output/LowParse_Low_Sum.krml _output/LowParse_Low_Tac_Sum.krml _output/LowParse_Spec_Option.krml _output/LowParse_Low_Option.krml _output/LowParse_Bytes32.krml _output/LowParse_Spec_Bytes.krml _output/LowParse_Low_Bytes.krml _output/LowParse_Low_Array.krml _output/LowParse_Low.krml _output/LowParse_Writers_Parser.krml _output/FStar_Monotonic_Pure.krml _output/LowParse_Writers_Effect.krml _output/LowParse_Writers_Combinators.krml _output/LowParse_Writers_Instances.krml _output/LowParse_SLow_Base.krml _output/LowParse_SLow_Combinators.krml _output/LowParse_SLow_FLData.krml _output/LowParse_SLow_VLGen.krml _output/LowParse_Spec_Endianness.krml _output/LowParse_Spec_Endianness_Instances.krml _output/LowParse_SLow_Endianness.krml _output/LowParse_SLow_BoundedInt.krml _output/LowParse_SLow_Int.krml _output/LowParse_SLow_DER.krml _output/LowParse_SLow_BCVLI.krml _output/LowParse_SLow_List.krml _output/LowParse_SLow_VCList.krml _output/LowParse_SLow_IfThenElse.krml _output/LowParse_SLow_Option.krml _output/LowParse_Spec_Tac_Enum.krml _output/LowParse_Spec_Tac_Sum.krml _output/LowParse_SLow_Enum.krml _output/LowParse_SLow_Sum.krml _output/LowParse_SLow_Tac_Enum.krml _output/LowParse_SLow_VLData.krml _output/LowParse_SLow_Bytes.krml _output/LowParse_SLow_Array.krml _output/LowParse_Spec_Tac_Combinators.krml _output/LowParse_SLow.krml _output/LowParse_Spec_SeqBytes.krml _output/LowParse_Spec.krml _output/Zeta_Formats_Aux_Timestamp.krml _output/Zeta_Formats_Aux_Slot_id.krml _output/Zeta_Formats_Aux_Evictbm_payload.krml _output/FStar_PCM.krml _output/FStar_WellFounded.krml _output/FStar_Real.krml _output/FStar_Tactics_CanonCommSwaps.krml _output/FStar_Algebra_CommMonoid_Equiv.krml _output/FStar_Tactics_CanonCommMonoidSimple_Equiv.krml _output/Zeta_Steel_Util.krml _output/Zeta_Steel_Parser.krml _output/Zeta_Formats_Lib.krml _output/Zeta_SeqAux.krml _output/Zeta_MultiSet.krml _output/Zeta_BinTree.krml _output/Zeta_Key.krml _output/Zeta_Hash.krml _output/Zeta_App.krml _output/Zeta_Steel_ApplicationTypes.krml _output/Zeta_Formats_Aux_Application_key_Spec.krml _output/Zeta_Formats_Aux_Application_key_Low.krml _output/Zeta_Steel_KeyUtils.krml _output/Zeta_Formats_Aux_Application_value_Spec.krml _output/Zeta_Formats_Aux_Application_value_Low.krml _output/Zeta_Formats_Aux_Application_value_SLow.krml _output/Zeta_Formats_Aux_Application_value_Size.krml _output/Zeta_Formats_Aux_External_App.krml _output/Zeta_Formats_Aux_Application_value.krml _output/Zeta_Formats_Aux_Application_key_SLow.krml _output/Zeta_Formats_Aux_Application_key_Size.krml _output/Zeta_Formats_Aux_Application_key.krml _output/Zeta_Steel_ApplicationRecord.krml _output/Zeta_Steel_LogEntry_Types.krml _output/Zeta_Formats_Aux_U256.krml _output/Zeta_Formats_Synth_U256.krml _output/Zeta_Formats_Aux_External.krml _output/Zeta_Formats_Aux_Significant_digits_t.krml _output/Zeta_Formats_Aux_Raw_key.krml _output/Zeta_Formats_Aux_Base_key.krml _output/Zeta_Formats_Aux_Value_kind.krml _output/Zeta_Formats_Aux_Voption.krml _output/Zeta_Formats_Aux_Vbool.krml _output/Zeta_Formats_Aux_Hash_value.krml _output/Zeta_Formats_Aux_Descendent_hash_desc.krml _output/Zeta_Formats_Aux_Descendent_hash.krml _output/Zeta_Formats_Aux_Mval_value.krml _output/Zeta_Formats_Aux_Value.krml _output/Zeta_Formats_Aux_Dvalue_kind.krml _output/Zeta_Formats_Aux_Application_record_v_payload.krml _output/Zeta_Formats_Aux_Internal_key.krml _output/Zeta_Formats_Aux_Internal_record.krml _output/Zeta_Formats_Aux_Application_record.krml _output/Zeta_Formats_Aux_Key_kind.krml _output/Zeta_Formats_Aux_Record.krml _output/Zeta_Formats_Synth.krml _output/Zeta_Formats_Aux_Thread_id.krml _output/Zeta_Formats_Aux_Stamped_record.krml _output/Zeta_Formats_Aux_Log_entry_kind.krml _output/Zeta_Formats_Aux_Runapp_payload_hdr.krml _output/Zeta_Formats_Aux_Evictb_payload.krml _output/Zeta_Formats_Aux_Evictm_payload.krml _output/Zeta_Formats_Aux_Addb_payload.krml _output/Zeta_Formats_Aux_Addm_payload.krml _output/Zeta_Formats_Aux_Log_entry_hdr.krml _output/Zeta_Formats_LogEntry.krml _output/Zeta_Steel_LogEntry_Spec.krml _output/Zeta_LowStar_Parser.krml _output/Zeta_LowStar_LogEntry.krml -warn-error @4@5@18 -fparentheses -bundle Zeta.Steel.LogEntry.Spec+Zeta.LowStar.LogEntry+Zeta.Formats.Aux.Application_key.Size+Zeta.Formats.Aux.Application_key.Low+Zeta.Formats.Aux.Application_value.Size+Zeta.Formats.Aux.Application_value.Low=*[rename=ZetaFormats] -no-prefix Zeta.LowStar.LogEntry -no-prefix Zeta.Steel.LogEntry.Spec -o zetaformats.a -add-include "ZetaFormatsApplicationTypes.h"
  F* version: d80633a7
  KaRaMeL version: 9bf6cc83
 */

#ifndef __ZetaFormats_H
#define __ZetaFormats_H

#include "krmllib.h"



#include "ZetaFormatsApplicationTypes.h"
typedef struct LowParse_Slice_slice_s
{
  uint8_t *base;
  uint32_t len;
}
LowParse_Slice_slice;

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

typedef struct Zeta_Steel_LogEntry_Types_evictM_payload_s
{
  uint16_t s;
  uint16_t s_;
}
Zeta_Steel_LogEntry_Types_evictM_payload;

typedef struct Zeta_Steel_LogEntry_Types_evictB_payload_s
{
  uint16_t s1;
  Zeta_Steel_LogEntry_Types_timestamp t;
}
Zeta_Steel_LogEntry_Types_evictB_payload;

typedef struct Zeta_Steel_LogEntry_Types_evictBM_payload_s
{
  uint16_t s2;
  uint16_t s_1;
  Zeta_Steel_LogEntry_Types_timestamp t1;
}
Zeta_Steel_LogEntry_Types_evictBM_payload;

typedef struct Zeta_Steel_LogEntry_Types_runApp_payload_s
{
  uint8_t fid;
  uint32_t rest;
}
Zeta_Steel_LogEntry_Types_runApp_payload;

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

typedef struct Zeta_Steel_LogEntry_Types_record_s
{
  Zeta_Steel_LogEntry_Types_key fst;
  Zeta_Steel_LogEntry_Types_value snd;
}
Zeta_Steel_LogEntry_Types_record;

#define Zeta_Steel_LogEntry_Types_AddM 0
#define Zeta_Steel_LogEntry_Types_AddB 1
#define Zeta_Steel_LogEntry_Types_RunApp 2
#define Zeta_Steel_LogEntry_Types_EvictM 3
#define Zeta_Steel_LogEntry_Types_EvictB 4
#define Zeta_Steel_LogEntry_Types_EvictBM 5
#define Zeta_Steel_LogEntry_Types_NextEpoch 6
#define Zeta_Steel_LogEntry_Types_VerifyEpoch 7

typedef uint8_t Zeta_Steel_LogEntry_Types_log_entry_tags;

typedef struct Zeta_Steel_LogEntry_Types_log_entry_s
{
  Zeta_Steel_LogEntry_Types_log_entry_tags tag;
  union {
    struct
    {
      uint16_t s;
      uint16_t s_;
      Zeta_Steel_LogEntry_Types_record r;
    }
    case_AddM;
    struct
    {
      uint16_t s;
      Zeta_Steel_LogEntry_Types_timestamp ts;
      uint16_t tid;
      Zeta_Steel_LogEntry_Types_record r;
    }
    case_AddB;
    Zeta_Steel_LogEntry_Types_runApp_payload case_RunApp;
    Zeta_Steel_LogEntry_Types_evictM_payload case_EvictM;
    Zeta_Steel_LogEntry_Types_evictB_payload case_EvictB;
    Zeta_Steel_LogEntry_Types_evictBM_payload case_EvictBM;
  }
  ;
}
Zeta_Steel_LogEntry_Types_log_entry;

typedef struct Zeta_Steel_LogEntry_Types_stamped_record_s
{
  Zeta_Steel_LogEntry_Types_record record;
  Zeta_Steel_LogEntry_Types_timestamp timestamp;
  uint16_t thread_id;
}
Zeta_Steel_LogEntry_Types_stamped_record;

uint32_t zeta__runapp_payload_offset(Zeta_Steel_LogEntry_Types_log_entry e);

typedef struct K___Zeta_Steel_LogEntry_Types_log_entry_uint32_t_s
{
  Zeta_Steel_LogEntry_Types_log_entry fst;
  uint32_t snd;
}
K___Zeta_Steel_LogEntry_Types_log_entry_uint32_t;

typedef struct
FStar_Pervasives_Native_option__K___Zeta_Steel_LogEntry_Types_log_entry_uint32_t_s
{
  FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type_tags tag;
  K___Zeta_Steel_LogEntry_Types_log_entry_uint32_t v;
}
FStar_Pervasives_Native_option__K___Zeta_Steel_LogEntry_Types_log_entry_uint32_t;

FStar_Pervasives_Native_option__K___Zeta_Steel_LogEntry_Types_log_entry_uint32_t
zeta__parser_log_entry(uint32_t len, uint32_t offset, uint32_t slice_len, uint8_t *a);

uint32_t
zeta__serialize_stamped_record(
  uint32_t len,
  uint32_t offset,
  uint8_t *a,
  Zeta_Steel_LogEntry_Types_stamped_record v
);

uint32_t
zeta__serialize_value(
  uint32_t len,
  uint32_t offset,
  uint8_t *a,
  Zeta_Steel_LogEntry_Types_value v
);

typedef struct K___Zeta_Steel_KeyUtils_u256_uint32_t_s
{
  Zeta_Steel_KeyUtils_u256 fst;
  uint32_t snd;
}
K___Zeta_Steel_KeyUtils_u256_uint32_t;

typedef struct FStar_Pervasives_Native_option__K___Zeta_Steel_KeyUtils_u256_uint32_t_s
{
  FStar_Pervasives_Native_option__Zeta_Steel_ApplicationTypes_value_type_tags tag;
  K___Zeta_Steel_KeyUtils_u256_uint32_t v;
}
FStar_Pervasives_Native_option__K___Zeta_Steel_KeyUtils_u256_uint32_t;

FStar_Pervasives_Native_option__K___Zeta_Steel_KeyUtils_u256_uint32_t
zeta__parser_u256(uint32_t len, uint32_t offset, uint32_t slice_len, uint8_t *a);

extern uint32_t
Zeta_Formats_Aux_Application_key_Size_application_key_size32(
  Zeta_Steel_ApplicationTypes_key_type uu___
);

extern uint64_t
Zeta_Formats_Aux_Application_key_Low_application_key_validator(
  LowParse_Slice_slice x0,
  uint64_t x1
);

extern uint32_t
Zeta_Formats_Aux_Application_key_Low_application_key_jumper(
  LowParse_Slice_slice x0,
  uint32_t x1
);

extern Zeta_Steel_ApplicationTypes_key_type
Zeta_Formats_Aux_Application_key_Low_application_key_reader(
  LowParse_Slice_slice x0,
  uint32_t x1
);

extern uint32_t
Zeta_Formats_Aux_Application_key_Low_application_key_lserializer(
  Zeta_Steel_ApplicationTypes_key_type uu___,
  uint8_t *x0,
  uint32_t x1
);

extern uint32_t
Zeta_Formats_Aux_Application_value_Size_application_value_size32(
  Zeta_Steel_ApplicationTypes_value_type uu___
);

extern uint64_t
Zeta_Formats_Aux_Application_value_Low_application_value_validator(
  LowParse_Slice_slice x0,
  uint64_t x1
);

extern uint32_t
Zeta_Formats_Aux_Application_value_Low_application_value_jumper(
  LowParse_Slice_slice x0,
  uint32_t x1
);

extern Zeta_Steel_ApplicationTypes_value_type
Zeta_Formats_Aux_Application_value_Low_application_value_reader(
  LowParse_Slice_slice x0,
  uint32_t x1
);

extern uint32_t
Zeta_Formats_Aux_Application_value_Low_application_value_lserializer(
  Zeta_Steel_ApplicationTypes_value_type uu___,
  uint8_t *x0,
  uint32_t x1
);


#define __ZetaFormats_H_DEFINED
#endif
