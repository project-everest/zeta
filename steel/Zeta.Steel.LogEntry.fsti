module Zeta.Steel.LogEntry
include Zeta.Steel.LogEntry.Spec
open Zeta.Steel.Parser
module U32 = FStar.UInt32

val zeta__parser_log_entry : parser spec_parser_log_entry

inline_for_extraction
noextract
let parser_log_entry : parser spec_parser_log_entry = zeta__parser_log_entry

val zeta__serialize_stamped_record : serializer spec_serializer_stamped_record

inline_for_extraction
noextract
let serialize_stamped_record : serializer spec_serializer_stamped_record = zeta__serialize_stamped_record

inline_for_extraction
noextract
val zeta__serialize_value : serializer spec_serializer_value

inline_for_extraction
noextract
let serialize_value : serializer spec_serializer_value = zeta__serialize_value

val zeta__parser_u256 : parser spec_parser_u256

inline_for_extraction
noextract
let parser_u256 : parser spec_parser_u256 = zeta__parser_u256

val zeta__serialize_iv : serializer spec_serializer_iv

noextract
let timestamp_len = 8

let seq_suffix_is_zero (s:Seq.seq byte)
                       (from:nat)
  = from <= Seq.length s /\
    s `Seq.equal` Seq.append (Seq.slice s 0 from)
                             (Seq.create (Seq.length s - from) 0uy)

module A = Steel.ST.Array
open Steel.ST.Util
let serialize_iv (a:byte_array { A.length a == 96 })
                 (v: timestamp)
  : Steel.ST.Util.STT unit
    (exists_ (fun bs -> A.pts_to a full_perm bs `star` pure (seq_suffix_is_zero bs timestamp_len)))
    (fun slice_len ->
       exists_ (fun (bs:_) ->
         A.pts_to a full_perm bs `star`
         pure (
           seq_suffix_is_zero bs timestamp_len /\
           spec_serializer_iv v == bs)))
  = admit_()
