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

val zeta__serialize_timestamp : serializer spec_serialize_timestamp

noextract
let timestamp_len = 8

let seq_suffix_is_zero (s:Seq.seq byte)
                       (from:nat)
  = from <= Seq.length s /\
    s `Seq.equal` Seq.append (Seq.slice s 0 from)
                             (Seq.create (Seq.length s - from) 0uy)

module A = Steel.ST.Array
open Steel.ST.Util
let serialize_timestamp (#bs:Ghost.erased (Seq.seq FStar.UInt8.t))
                        (a:byte_array { A.length a == 8 })
                        (v: timestamp)
 : STT U32.t
    (A.pts_to a full_perm bs)
    (fun slice_len ->
       exists_ (fun (bs:_) ->
         A.pts_to a full_perm bs `star`
         pure (
           spec_serialize_timestamp v == bs)))
 = admit_(); return 0ul

let seq_suffix_is_zero_elim (s:Seq.seq byte)
                            (from:nat)
  : Lemma 
    (requires seq_suffix_is_zero s from)
    (ensures
         from <= Seq.length s /\
         Seq.slice s from (Seq.length s) `Seq.equal` Seq.create (Seq.length s - from) 0uy)
  = ()


let serialize_iv (a:byte_array { A.length a == 96 })
                 (v: timestamp)
  : Steel.ST.Util.STT unit
    (exists_ (fun bs -> A.pts_to a full_perm bs `star` pure (seq_suffix_is_zero bs timestamp_len)))
    (fun slice_len ->
       exists_ (fun (bs:_) ->
         A.pts_to a full_perm bs `star`
         pure (
           seq_suffix_is_zero bs timestamp_len /\
           spec_serialize_iv v == bs)))
  = let bs = elim_exists () in
    A.pts_to_length a bs;
    elim_pure _;
    seq_suffix_is_zero_elim bs timestamp_len;
    let adj = A.ghost_split a 8sz in
    let n = serialize_timestamp (A.split_l a 8sz) v in 
    let bs_l = elim_exists () in
    A.pts_to_length (A.split_l a 8sz) bs_l;
    elim_pure _;
    assert_ (A.pts_to (A.split_l a 8sz) full_perm bs_l `star`
             A.pts_to (A.split_r a 8sz) full_perm (Seq.slice bs 8 (Seq.length bs)));
    A.ghost_join (A.split_l a 8sz) (A.split_r a 8sz) adj;
    rewrite (A.pts_to (A.merge (A.split_l a 8sz) (A.split_r a 8sz)) _ _)
            (A.pts_to a full_perm (spec_serialize_iv v));
    intro_pure (seq_suffix_is_zero (spec_serialize_iv v) timestamp_len /\
                spec_serialize_iv v == spec_serialize_iv v);
    return ()
