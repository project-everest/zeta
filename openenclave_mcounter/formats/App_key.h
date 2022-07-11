/* 
  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: /home/ishtiyaque/everparse/bin/krml -ccopt -Ofast -drop FStar.Tactics.\* -drop FStar.Tactics -drop FStar.Reflection.\* -tmpdir out -bundle LowParse.\* -add-include "kremlin/internal/compat.h" -warn-error -9 -warn-error @2 -skip-compilation kremlin/FStar_Pervasives_Native.krml kremlin/FStar_Pervasives.krml kremlin/FStar_Mul.krml kremlin/FStar_Squash.krml kremlin/FStar_Classical.krml kremlin/FStar_Preorder.krml kremlin/FStar_Calc.krml kremlin/FStar_StrongExcludedMiddle.krml kremlin/FStar_Classical_Sugar.krml kremlin/FStar_List_Tot_Base.krml kremlin/FStar_List_Tot_Properties.krml kremlin/FStar_List_Tot.krml kremlin/FStar_Seq_Base.krml kremlin/FStar_Seq_Properties.krml kremlin/FStar_Seq.krml kremlin/FStar_Math_Lib.krml kremlin/FStar_Math_Lemmas.krml kremlin/FStar_BitVector.krml kremlin/FStar_UInt.krml kremlin/FStar_UInt32.krml kremlin/FStar_Int.krml kremlin/FStar_Int16.krml kremlin/FStar_Int64.krml kremlin/FStar_Int32.krml kremlin/FStar_Int8.krml kremlin/FStar_UInt64.krml kremlin/FStar_UInt16.krml kremlin/FStar_UInt8.krml kremlin/FStar_Int_Cast.krml kremlin/FStar_Ghost.krml kremlin/FStar_Range.krml kremlin/FStar_Tactics_Common.krml kremlin/FStar_VConfig.krml kremlin/FStar_Reflection_Types.krml kremlin/FStar_Tactics_Types.krml kremlin/FStar_Tactics_Result.krml kremlin/FStar_Tactics_Effect.krml kremlin/FStar_Reflection_Data.krml kremlin/FStar_Tactics_Builtins.krml kremlin/FStar_FunctionalExtensionality.krml kremlin/FStar_Set.krml kremlin/FStar_ErasedLogic.krml kremlin/FStar_PropositionalExtensionality.krml kremlin/FStar_PredicateExtensionality.krml kremlin/FStar_TSet.krml kremlin/FStar_Monotonic_Heap.krml kremlin/FStar_Heap.krml kremlin/FStar_Map.krml kremlin/FStar_Monotonic_Witnessed.krml kremlin/FStar_Monotonic_HyperHeap.krml kremlin/FStar_Monotonic_HyperStack.krml kremlin/FStar_HyperStack.krml kremlin/FStar_HyperStack_ST.krml kremlin/Spec_Loops.krml kremlin/FStar_Universe.krml kremlin/FStar_GSet.krml kremlin/FStar_ModifiesGen.krml kremlin/FStar_Reflection_Const.krml kremlin/FStar_Order.krml kremlin/FStar_Reflection_Builtins.krml kremlin/FStar_Reflection_Derived.krml kremlin/FStar_Reflection_Derived_Lemmas.krml kremlin/FStar_Reflection.krml kremlin/FStar_Tactics_Print.krml kremlin/FStar_Tactics_SyntaxHelpers.krml kremlin/FStar_Tactics_Util.krml kremlin/FStar_IndefiniteDescription.krml kremlin/FStar_Reflection_Formula.krml kremlin/FStar_Tactics_Derived.krml kremlin/FStar_Tactics_Logic.krml kremlin/FStar_Tactics.krml kremlin/FStar_BigOps.krml kremlin/LowStar_Monotonic_Buffer.krml kremlin/LowStar_Buffer.krml kremlin/LowStar_BufferOps.krml kremlin/C_Loops.krml kremlin/LowStar_Comment.krml kremlin/LowParse_Math.krml kremlin/LowParse_BitFields.krml kremlin/LowParse_Low_ErrorCode.krml kremlin/LowParse_Bytes.krml kremlin/LowParse_Slice.krml kremlin/LowParse_Norm.krml kremlin/LowParse_Spec_Base.krml kremlin/LowParse_Low_Base_Spec.krml kremlin/LowParse_Low_Base.krml kremlin/LowParse_Spec_Combinators.krml kremlin/LowParse_Spec_List.krml kremlin/LowParse_Low_List.krml kremlin/FStar_Endianness.krml kremlin/LowParse_Spec_IfThenElse.krml kremlin/LowParse_Spec_FLData.krml kremlin/LowStar_Failure.krml kremlin/LowParse_Low_Combinators.krml kremlin/LowParse_Low_FLData.krml kremlin/LowParse_TacLib.krml kremlin/LowParse_Spec_Enum.krml kremlin/LowParse_Spec_Sum.krml kremlin/LowParse_Low_Enum.krml kremlin/LowParse_Low_Sum.krml kremlin/LowParse_Low_Tac_Sum.krml kremlin/LowParse_Spec_SeqBytes_Base.krml kremlin/LowParse_Spec_Seq.krml kremlin/LowParse_Spec_Int.krml kremlin/LowParse_Spec_BoundedInt.krml kremlin/LowParse_Spec_DER.krml kremlin/LowParse_Spec_BCVLI.krml kremlin/LowParse_Spec_AllIntegers.krml kremlin/LowParse_Spec_VLData.krml kremlin/LowParse_Spec_Array.krml kremlin/LowParse_Spec_VCList.krml kremlin/LowParse_Spec_VLGen.krml kremlin/LowStar_Modifies.krml kremlin/FStar_Char.krml kremlin/FStar_Exn.krml kremlin/FStar_ST.krml kremlin/FStar_All.krml kremlin/FStar_List.krml kremlin/FStar_String.krml kremlin/FStar_Bytes.krml kremlin/FStar_UInt128.krml kremlin/LowStar_Endianness.krml kremlin/LowParse_Low_Endianness.krml kremlin/LowParse_Endianness.krml kremlin/LowParse_Endianness_BitFields.krml kremlin/LowParse_Low_BoundedInt.krml kremlin/LowParse_Low_VLData.krml kremlin/LowParse_Low_VLGen.krml kremlin/LowParse_Low_Int.krml kremlin/LowParse_Low_DER.krml kremlin/LowParse_Low_BCVLI.krml kremlin/LowParse_Low_VCList.krml kremlin/LowParse_Low_IfThenElse.krml kremlin/LowParse_Spec_Option.krml kremlin/LowParse_Low_Option.krml kremlin/LowParse_Bytes32.krml kremlin/LowParse_Spec_Bytes.krml kremlin/LowParse_Low_Bytes.krml kremlin/LowParse_Low_Array.krml kremlin/LowParse_Low.krml kremlin/LowParse_Writers_Parser.krml kremlin/FStar_Monotonic_Pure.krml kremlin/LowParse_Writers_Effect.krml kremlin/LowParse_Writers_Combinators.krml kremlin/LowParse_Writers_Instances.krml kremlin/LowParse_Spec_SeqBytes.krml kremlin/LowParse_Spec_Tac_Enum.krml kremlin/LowParse_Spec_Tac_Sum.krml kremlin/LowParse_Spec.krml kremlin/Slot.krml kremlin/App_key.krml kremlin/Incr_counter_param.krml kremlin/New_counter_param.krml kremlin/App_val.krml kremlin/Get_counter_param.krml
  F* version: <unknown>
  KreMLin version: <unknown>
 */

#ifndef __App_key_H
#define __App_key_H
#include <kremlin/internal/compat.h>
#include "kremlib.h"


#include "LowParse.h"

typedef uint64_t App_key_app_key;

uint64_t App_key_app_key_validator(LowParse_Slice_slice sl, uint64_t pos);

uint32_t App_key_app_key_jumper(LowParse_Slice_slice input, uint32_t pos);

uint64_t App_key_app_key_reader(LowParse_Slice_slice sl, uint32_t pos);

uint32_t App_key_app_key_lserializer(uint64_t v, uint8_t *b, uint32_t pos);


#define __App_key_H_DEFINED
#endif
