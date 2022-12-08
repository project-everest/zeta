module Zeta.Steel.IV
open Zeta.Steel.LogEntry.Spec
open Zeta.Steel.LogEntry
open Zeta.Steel.Parser
open Steel.ST.Util
open Zeta.Steel.Util
module A = Steel.ST.Array
module U32 = FStar.UInt32

noextract
let timestamp_len = 8

let seq_suffix_is_zero (s:Seq.seq byte)
                       (from:nat)
  = from <= Seq.length s /\
    s `Seq.equal` Seq.append (Seq.slice s 0 from)
                             (Seq.create (Seq.length s - from) 0uy)


let serialize_timestamp (#bs:Ghost.erased (Seq.seq FStar.UInt8.t))
                        (a:byte_array { A.length a == 8 })
                        (v: timestamp)
 : STT U32.t
    (A.pts_to a full_perm bs)
    (fun slice_len ->
       exists_ (fun (bs:bytes) ->
         A.pts_to a full_perm bs `star`
         pure (
           spec_serializer_timestamp v == bs)))
 = intro_exists_erased bs (array_pts_to a);
   let n = zeta__serialize_timestamp 8ul 0ul a v in
   let bs = elim_exists () in
   elim_pure _;
   // intro_pure (eq2 #bytes (spec_serializer_timestamp v) bs);
   // intro_exists_erased bs (fun (bs:bytes) -> A.pts_to a full_perm bs `star`
   //                                        pure (spec_serializer_timestamp v == bs));
   return n
   

let seq_suffix_is_zero_elim (s:Seq.seq byte)
                            (from:nat)
  : Lemma 
    (requires seq_suffix_is_zero s from)
    (ensures
         from <= Seq.length s /\
         Seq.slice s from (Seq.length s) `Seq.equal` Seq.create (Seq.length s - from) 0uy)
  = ()

#push-options "--z3rlimit_factor 3 --fuel 0 --ifuel 0"
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
            (A.pts_to a full_perm (spec_serializer_iv v));
    intro_pure (seq_suffix_is_zero (spec_serializer_iv v) timestamp_len /\
                spec_serializer_iv v == spec_serializer_iv v);
    return ()
#pop-options
