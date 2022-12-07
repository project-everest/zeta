module Zeta.Steel.HashAccumulator
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Cast = FStar.Int.Cast
module A = Steel.ST.Array
module ZSU = Zeta.Steel.Util
open Steel.ST.Util
module AEAD = EverCrypt.AEAD
module Loops = Steel.ST.Loops
module R = Steel.ST.Reference
module G = Zeta.Steel.Globals
#push-options "--ide_id_info_off"
#push-options "--fuel 0 --ifuel 0"

let hash_len_sz = 16sz
let hash_len = SizeT.v hash_len_sz
let hash_value_t =
    Ghost.erased (Seq.lseq U8.t hash_len &
                  nat)
let hash_of (h:hash_value_t)
  : GTot (Seq.lseq U8.t hash_len)
  = fst h

let ctr_of (h:hash_value_t)
  : GTot nat
  = snd h

let hash_value_buf  = x:A.array U8.t { A.length x == hash_len /\ A.is_full_array x }


//[@@CAbstractStruct] TODO: Restore this after krml #247
noeq
type ha = {
  acc: hash_value_buf;
  ctr:R.ref U32.t;
  tmp: hash_value_buf
}


// [@@__steel_reduce__;__reduce__]
let ha_val (h:ha) (s:hash_value_t) =
  A.pts_to h.acc full_perm (hash_of s) `star`
  exists_ (fun (n:U32.t) ->
      pure (U32.v n == ctr_of s) `star`
      R.pts_to h.ctr full_perm n) `star`
  exists_ (A.pts_to h.tmp full_perm)
      
let unfold_ha_val (#o:_) (h:ha) (s:hash_value_t)
  : STGhostT unit o
    (ha_val h s)
    (fun _ -> A.pts_to h.acc full_perm (hash_of s) `star`
           exists_ (fun (n:U32.t) ->
             pure (U32.v n == ctr_of s) `star`
             R.pts_to h.ctr full_perm n) `star`
           exists_ (A.pts_to h.tmp full_perm))
  = rewrite (ha_val h s)
            (A.pts_to h.acc full_perm (hash_of s) `star`
             exists_ (fun (n:U32.t) ->
                pure (U32.v n == ctr_of s) `star`
                R.pts_to h.ctr full_perm n) `star`
             exists_ (A.pts_to h.tmp full_perm));
    ()

let fold_ha_val (#o:_) (h:ha) (s:hash_value_t)
  : STGhostT unit o
    (A.pts_to h.acc full_perm (hash_of s) `star`
     exists_ (fun (n:U32.t) ->
       pure (U32.v n == ctr_of s) `star`
       R.pts_to h.ctr full_perm n)  `star`
     exists_ (A.pts_to h.tmp full_perm))
    (fun _ -> ha_val h s)
  = rewrite (A.pts_to h.acc full_perm (hash_of s) `star`
             exists_ (fun (n:U32.t) ->
               pure (U32.v n == ctr_of s) `star`
               R.pts_to h.ctr full_perm n) `star`
             exists_ (A.pts_to h.tmp full_perm))
            (ha_val h s);
    ()


let initial_hash
  = Ghost.hide (Seq.create hash_len 0uy, 0)

let hash_one_value 
      (iv:Seq.seq U8.t { Seq.length iv == iv_len })
      (s:Seq.seq U8.t { Seq.length s <= aead_max_input_length })
  : hash_value_t
  = AEAD.spec G.aead_key iv s, 1

noextract inline_for_extraction
let xor_bytes (s1: Seq.seq U8.t)
              (s2: Seq.seq U8.t { Seq.length s1 == Seq.length s2 })
  : s3:Seq.seq U8.t { Seq.length s3 == Seq.length s1 }
  = Seq.init (Seq.length s1)
             (fun i -> Seq.index s1 i `FStar.UInt8.logxor` Seq.index s2 i)

let logxor_zero (x:U8.t)
  : Lemma (U8.logxor 0uy x == x)
  = UInt.logxor_lemma_1 (U8.v x);
    UInt.logxor_commutative (U8.v 0uy) (U8.v x)

let logxor_commutative (x y:U8.t)
  : Lemma (x `U8.logxor` y == y `U8.logxor` x)
  = UInt.logxor_commutative (U8.v x) (U8.v y)

let logxor_associative (x y z:U8.t)
  : Lemma (U8.logxor x (U8.logxor y z) ==
           U8.logxor (U8.logxor x y) z)
  = UInt.logxor_associative (U8.v x) (U8.v y) (U8.v z)

let xor_bytes_unit (s:Seq.seq U8.t)
  : Lemma (xor_bytes (Seq.create (Seq.length s) 0uy) s == s)
  = Classical.forall_intro logxor_zero;
    assert (Seq.equal (xor_bytes (Seq.create (Seq.length s) 0uy) s) s)

let xor_bytes_commutative
  (s1:Seq.seq U8.t)
  (s2:Seq.seq U8.t{Seq.length s1 == Seq.length s2})
  : Lemma (xor_bytes s1 s2 == xor_bytes s2 s1)
  = Classical.forall_intro_2 logxor_commutative;
    assert (Seq.equal (xor_bytes s1 s2) (xor_bytes s2 s1))

let xor_bytes_associative
  (s1:Seq.seq U8.t)
  (s2:Seq.seq U8.t)
  (s3:Seq.seq U8.t{Seq.length s1 == Seq.length s2 /\
                   Seq.length s2 == Seq.length s3})
  : Lemma (xor_bytes s1 (xor_bytes s2 s3) ==
           xor_bytes (xor_bytes s1 s2) s3)
  = Classical.forall_intro_3 logxor_associative;
    assert (Seq.equal (xor_bytes s1 (xor_bytes s2 s3))
                      (xor_bytes (xor_bytes s1 s2) s3))

let aggregate_hashes (h0 h1: hash_value_t)
  : hash_value_t
  = xor_bytes (hash_of h0) (hash_of h1),
    ctr_of h0 + ctr_of h1

let initial_hash_unit h = xor_bytes_unit (fst h)

let aggregate_hashes_commutative h1 h2 =
  xor_bytes_commutative (fst h1) (fst h2)

let aggregate_hashes_associative h1 h2 h3 =
  xor_bytes_associative (fst h1) (fst h2) (fst h3)

let mk_hash_value (ws:Seq.lseq U8.t hash_len) (wc:U32.t)
  : hash_value_t
  = ws, U32.v wc

let intro_ha_val (#o:_)
                 (s:ha)
                 (ws:Seq.lseq U8.t hash_len)
                 (wc:U32.t)
                 (res:hash_value_t { res == mk_hash_value ws wc })
  : STGhostT unit o
    (A.pts_to s.acc full_perm ws
      `star`
     R.pts_to s.ctr full_perm wc
      `star`
     exists_ (A.pts_to s.tmp full_perm))
    (fun _ ->
      ha_val s res)
  = let w = mk_hash_value ws wc in
    rewrite (A.pts_to s.acc _ _)
            (A.pts_to s.acc full_perm (fst w));
    intro_pure (U32.v wc == snd w);
    intro_exists #U32.t wc (fun n -> pure (U32.v n == snd w) `star` R.pts_to s.ctr full_perm n);
    fold_ha_val s w;
    rewrite (ha_val s w)
            (ha_val s res);
    ()


let elim_ha_val #o (#w:hash_value_t) (s:ha)
  : STGhost (Ghost.erased U32.t) o
    (ha_val s w)
    (fun n -> A.pts_to s.acc full_perm (fst w) `star`
           R.pts_to s.ctr full_perm n `star`
           (exists_ (A.pts_to s.tmp full_perm)))
    (requires True)
    (ensures fun n -> U32.v n == snd w)
  = unfold_ha_val s w;
    let n = elim_exists () in
    elim_pure _;
    n

let create (_:unit)
  = let acc = A.alloc 0uy hash_len_sz in
    let ctr = R.alloc 0ul in
    let tmp = A.alloc 0uy hash_len_sz in
    let ha = { acc; ctr; tmp } in
    //TODO: constructing values and transporting slprops to their fields is very tedious
    rewrite (A.pts_to acc _ _)
            (A.pts_to ha.acc full_perm (Seq.create hash_len 0uy));
    rewrite (R.pts_to ctr _ _)
            (R.pts_to ha.ctr full_perm 0ul);
    rewrite (A.pts_to tmp _ _)
            (A.pts_to ha.tmp full_perm (Seq.create hash_len 0uy));
    intro_exists _ (A.pts_to ha.tmp full_perm);
    intro_ha_val ha _ _ initial_hash;
    return ha

let reclaim (#h:hash_value_t) (s:ha)
  = let _ = elim_ha_val s in
    R.free s.ctr;
    A.free s.tmp;    
    intro_exists (fst h) (A.pts_to s.acc full_perm);
    A.free s.acc


let bytes = Seq.seq U8.t

let xor_bytes_pfx (s1:bytes)
                  (s2:bytes { Seq.length s1 == Seq.length s2 })
                  (i:nat { i <= Seq.length s1 })
  : bytes
  = Seq.append
      (xor_bytes (Seq.slice s1 0 i) (Seq.slice s2 0 i))
      (Seq.slice s1 i (Seq.length s1))

let raw_hash_t = Seq.seq U8.t

let eraw_hash_t = s:Ghost.erased raw_hash_t { Seq.length s == hash_len }

let extend_hash_value (s1 s2:bytes)
                      (i:nat)
  : Lemma (requires Seq.length s1 == Seq.length s2 /\
                    i < Seq.length s1)
          (ensures  Seq.upd (xor_bytes_pfx s1 s2 i)
                      i
                    (U8.logxor (Seq.index s1 i) (Seq.index s2 i))
                    `Seq.equal`
                    xor_bytes_pfx s1 s2 (i + 1))
  = ()

let aggregate_raw_hashes
    (s1: eraw_hash_t)
    (s2: eraw_hash_t)
    (b1: hash_value_buf)
    (b2: hash_value_buf)
  : STT unit
    (A.pts_to b1 full_perm s1 `star`
     A.pts_to b2 full_perm s2)
    (fun _ ->
     A.pts_to b1 full_perm (xor_bytes s1 s2) `star`
     A.pts_to b2 full_perm s2)
  = let inv (i:Loops.nat_at_most hash_len_sz)
      : vprop
      = A.pts_to b1 full_perm (xor_bytes_pfx s1 s2 i) `star`
        A.pts_to b2 full_perm s2
    in
    A.pts_to_length b1 _;
    A.pts_to_length b2 _;
    [@@inline_let]
    let body (i:Loops.u32_between 0sz hash_len_sz)
      : STT unit
        (inv (SizeT.v i))
        (fun _ -> inv (SizeT.v i + 1))
      = rewrite
            (inv (SizeT.v i))
            (A.pts_to b1 full_perm (xor_bytes_pfx s1 s2 (SizeT.v i)) `star`
             A.pts_to b2 full_perm s2);
        let x1 = A.read b1 i in
        let x2 = A.read b2 i in
        A.write b1 i (U8.logxor x1 x2);
        assert_ (A.pts_to b1 full_perm (Seq.upd
                                          (xor_bytes_pfx s1 s2 (SizeT.v i))
                                          (SizeT.v i)
                                          (U8.logxor x1 x2)));
        extend_hash_value s1 s2 (SizeT.v i);
        rewrite (A.pts_to b1 _ _)
                (A.pts_to b1 full_perm (xor_bytes_pfx s1 s2 (SizeT.v i + 1)));
        rewrite (A.pts_to b1 _ _ `star` A.pts_to b2 _ _)
                (inv (SizeT.v i + 1));
        return ()
    in
    assert (xor_bytes_pfx s1 s2 0 `Seq.equal` s1);
    rewrite (A.pts_to b1 _ _ `star` A.pts_to b2 _ _)
            (inv 0);
    Loops.for_loop 0sz hash_len_sz inv body;
    assert (xor_bytes_pfx s1 s2 hash_len `Seq.equal` xor_bytes s1 s2);
    rewrite (inv hash_len)
            (A.pts_to b1 _ _ `star` A.pts_to b2 _ _);
    return ()


inline_for_extraction
let narrow_uint64_to_uint32 (x:U64.t { U64.(x <=^ 0xffffffffuL) })
  : y:U32.t{U64.v x == U32.v y}
  = Cast.uint64_to_uint32 x

noeq
type ha_core = {
  acc: hash_value_buf;
  ctr:R.ref U32.t;
}

let ha_core_val (h:ha_core) (s:hash_value_t) =
  A.pts_to h.acc full_perm (hash_of s) `star`
  exists_ (fun (n:U32.t) ->
      pure (U32.v n == ctr_of s) `star`
      R.pts_to h.ctr full_perm n)

let elim_ha_core_val #o (#s:hash_value_t) (h:ha_core)
  : STGhost (Ghost.erased U32.t) o
    (ha_core_val h s)
    (fun n -> A.pts_to h.acc full_perm (hash_of s) `star`
           R.pts_to h.ctr full_perm n)
    (requires True)
    (ensures fun n -> U32.v n == snd s)
  = rewrite (ha_core_val h s)
            (A.pts_to h.acc full_perm (hash_of s) `star`
             exists_ (fun (n:U32.t) ->
               pure (U32.v n == ctr_of s) `star`
               R.pts_to h.ctr full_perm n));
    let n = elim_exists () in
    elim_pure _;
    n

let fold_ha_core_val (#o:_) (h:ha_core) (s:hash_value_t)
  : STGhostT unit o
    (A.pts_to h.acc full_perm (hash_of s) `star`
     exists_ (fun (n:U32.t) ->
       pure (U32.v n == ctr_of s) `star`
       R.pts_to h.ctr full_perm n))
    (fun _ -> ha_core_val h s)
  = rewrite (A.pts_to h.acc full_perm (hash_of s) `star`
             exists_ (fun (n:U32.t) ->
               pure (U32.v n == ctr_of s) `star`
               R.pts_to h.ctr full_perm n))
            (ha_core_val h s);
    ()

let intro_ha_core_val (#o:_)
                      (s:ha_core)
                      (ws:Seq.lseq U8.t hash_len)
                      (wc:U32.t)
                      (res:hash_value_t { res == mk_hash_value ws wc })
  : STGhostT unit o
    (A.pts_to s.acc full_perm ws
      `star`
     R.pts_to s.ctr full_perm wc)
    (fun _ ->
      ha_core_val s res)
  = let w = mk_hash_value ws wc in
    rewrite (A.pts_to s.acc _ _)
            (A.pts_to s.acc full_perm (hash_of w));
    intro_pure (U32.v wc == ctr_of w);
    intro_exists #U32.t wc (fun n -> pure (U32.v n == ctr_of w) `star` R.pts_to s.ctr full_perm n);
    fold_ha_core_val s w;
    rewrite (ha_core_val s w)
            (ha_core_val s res);
    ()

let aggregate_core (#h1 #h2:hash_value_t) (b1 b2: ha_core)
  : STT bool
    (ha_core_val b1 h1 `star` ha_core_val b2 h2)
    (fun b -> ha_core_val b1 (maybe_aggregate_hashes b h1 h2) `star` ha_core_val b2 h2)
  = let _n1 = elim_ha_core_val b1 in
    let _n2 = elim_ha_core_val b2 in
    let ctr1 = R.read b1.ctr in
    let ctr2 = R.read b2.ctr in
    let ctr = U64.(
      (Cast.uint32_to_uint64 ctr1)
      +^
      (Cast.uint32_to_uint64 ctr2)
    )
    in
    if U64.(ctr >^ 0xffffffffuL)
    then (
      intro_ha_core_val b1 _ _ (maybe_aggregate_hashes false h1 h2);
      intro_ha_core_val b2 _ _ h2;
      return false
    )
    else (
      aggregate_raw_hashes (fst h1) (fst h2) b1.acc b2.acc;
      R.write b1.ctr (narrow_uint64_to_uint32 ctr);
      intro_ha_core_val b1 _ _ (maybe_aggregate_hashes true h1 h2);
      intro_ha_core_val b2 _ _ h2;
      return true
    )

let ha_val_as_core_val #o (#w:hash_value_t) (b:ha)
  : STGhostT unit o
    (ha_val b w)
    (fun r -> ha_core_val {acc=b.acc; ctr=b.ctr} w `star`
           exists_ (A.pts_to b.tmp full_perm))
  = let c = elim_ha_val b in
    intro_ha_core_val {acc=b.acc; ctr=b.ctr} _ _ w

let ha_core_val_as_ha_val #o (#w:hash_value_t) (b:ha_core) (tmp:hash_value_buf)
  : STGhostT unit o
    (ha_core_val b w `star` exists_ (A.pts_to tmp full_perm))
    (fun r -> ha_val {acc=b.acc; ctr=b.ctr; tmp} w)
  = let c = elim_ha_core_val b in
    intro_ha_val {acc=b.acc; ctr=b.ctr; tmp} _ _ w

  
let aggregate #h1 #h2 (b1 b2: ha)
  = ha_val_as_core_val b1;
    ha_val_as_core_val b2;
    let res =
      aggregate_core {acc=b1.acc; ctr=b1.ctr}
                     {acc=b2.acc; ctr=b2.ctr} in
    ha_core_val_as_ha_val {acc=b1.acc; ctr=b1.ctr} b1.tmp;
    ha_core_val_as_ha_val {acc=b2.acc; ctr=b2.ctr} b2.tmp;    
    rewrite (ha_val {acc=b1.acc; ctr=b1.ctr; tmp=b1.tmp} _)
            (ha_val b1 (maybe_aggregate_hashes res h1 h2));
    rewrite (ha_val {acc=b2.acc; ctr=b2.ctr; tmp=b2.tmp} _)
            (ha_val b2 h2);
    return res

let compare #h1 #h2 (b1 b2:ha)
  = let _n1 = elim_ha_val b1 in
    let _n2 = elim_ha_val b2 in
    let c1 = R.read b1.ctr in
    let c2 = R.read b2.ctr in
    if c1 <> c2
    then (
      intro_ha_val b1 _ _ h1;
      intro_ha_val b2 _ _ h2;
      return false
    )
    else (
      let b = Steel.ST.Array.Util.compare b1.acc b2.acc hash_len_sz in
      assert (b <==> (fst h1 == fst h2));
      intro_ha_val b1 _ _ h1;
      intro_ha_val b2 _ _ h2;
      return b
    )

let get_aead_key (#o:_) (_:unit)
  : STGhostT perm o
      emp
      (fun p -> A.pts_to G.aead_key_buffer p G.aead_key)
  = admit_(); full_perm

let aead_with_key  
         (#iv_p:perm)
         (#iv_v:Ghost.erased (Seq.seq U8.t) { Seq.length iv_v == iv_len })
         (iv: A.array U8.t)
         (#in_p:perm)         
         (#in_v:Ghost.erased (Seq.seq U8.t))
         (input:hashable_buffer)
         (input_len:U32.t { U32.v input_len == Seq.length in_v /\
                            A.length input == Seq.length in_v })
         (out:hash_value_buf)
  : STT AEAD.error_code
    (A.pts_to iv iv_p iv_v `star`
     A.pts_to input in_p in_v `star`
     exists_ (A.pts_to out full_perm))
    (fun res -> 
     A.pts_to iv iv_p iv_v `star`
     A.pts_to input in_p in_v `star`
     exists_ (fun out_v -> 
       A.pts_to out full_perm out_v `star`
       pure (res == 0uy ==> out_v == AEAD.spec G.aead_key iv_v in_v)))
  = let k_p = get_aead_key () in
    let res =
      AEAD.encrypt_expand_aes128_gcm_no_check
           G.aead_key_buffer
           iv 96ul
           input input_len
           R.null 0ul
           R.null
           out in
    drop (A.pts_to G.aead_key_buffer _ _);
    return res

#push-options "--query_stats --z3rlimit_factor 4"
let add' (#h:hash_value_t) (ha:ha)
         (#p:perm) 
         (#ivv:Ghost.erased (Seq.seq U8.t) { Seq.length ivv == iv_len })
         (#s:Ghost.erased (Seq.seq U8.t))
         (iv: iv_buffer)
         (input:hashable_buffer)
         (l:U32.t { U32.v l == Seq.length s /\
                    A.length input == Seq.length s })
  : STT bool
        (ha_val ha h `star`
         A.pts_to iv p ivv `star`         
         A.pts_to input p s)
        (fun b -> ha_val ha 
                      (maybe_aggregate_hashes b h
                        (hash_one_value ivv (Seq.slice s 0 (U32.v l)))) `star`
               A.pts_to iv p ivv `star`         
               A.pts_to input p s)
  = R.with_local 1ul (fun ctr ->
     ha_val_as_core_val ha;                 
     let success = aead_with_key iv input l ha.tmp in
     let out_ = elim_exists () in
     elim_pure _;
     if success <> 0uy
     then (
      intro_exists_erased out_ (A.pts_to ha.tmp full_perm);
      ha_core_val_as_ha_val {acc=ha.acc; ctr=ha.ctr} ha.tmp;
      rewrite (ha_val {acc=ha.acc; ctr=ha.ctr; tmp=ha.tmp} _)
              (ha_val ha (maybe_aggregate_hashes false h
                                                  (hash_one_value ivv (Seq.slice s 0 (U32.v l)))));
      return false
     )
     else (
       let ha_core' = { acc=ha.tmp; ctr } in
       rewrite (A.pts_to ha.tmp _ _)
               (A.pts_to ha_core'.acc full_perm
                       (fst (hash_one_value ivv (Seq.slice s 0 (U32.v l)))));
       rewrite (R.pts_to ctr _ _)
               (R.pts_to ha_core'.ctr full_perm 1ul);
       //TODO: marking ha_val steel_reduce leads to a failure here
       intro_ha_core_val ha_core' 
                         (fst (hash_one_value ivv (Seq.slice s 0 (U32.v l))))
                         1ul
                         (hash_one_value ivv (Seq.slice s 0 (U32.v l)));
       let b = aggregate_core {acc=ha.acc; ctr=ha.ctr} ha_core' in
       let n = elim_ha_core_val ha_core' in
       rewrite (R.pts_to ha_core'.ctr full_perm n)
               (R.pts_to ctr full_perm n);
       rewrite (A.pts_to ha_core'.acc _ _)
               (A.pts_to ha.tmp full_perm 
                         (fst (hash_one_value ivv (Seq.slice s 0 (U32.v l)))));
       intro_exists _ (A.pts_to ha.tmp full_perm);
       ha_core_val_as_ha_val {acc=ha.acc; ctr=ha.ctr} ha.tmp;
       rewrite (ha_val {acc=ha.acc; ctr=ha.ctr; tmp=ha.tmp} _)
               (ha_val ha (maybe_aggregate_hashes b h
                                                  (hash_one_value ivv (Seq.slice s 0 (U32.v l)))));
       return b
     )
    )
#pop-options

module US = FStar.SizeT


(** Hash the (input[0, l)) into the hash accumulate s *)
let add (#h:hash_value_t) (ha:ha)
        (#p:perm) 
        (#ivv:Ghost.erased (Seq.seq U8.t) { Seq.length ivv == iv_len })
        (#s:Ghost.erased (Seq.seq U8.t))
        (iv: iv_buffer)
        (input:hashable_buffer)
        (l:U32.t { U32.v l <= Seq.length s /\
                   A.length input == Seq.length s })
  : STT bool
        (ha_val ha h `star`
         A.pts_to iv p ivv `star`         
         A.pts_to input p s)
        (fun b -> ha_val ha 
                      (maybe_aggregate_hashes b h
                        (hash_one_value ivv (Seq.slice s 0 (U32.v l)))) `star`
               A.pts_to iv p ivv `star`         
               A.pts_to input p s)
  = let l_sz = US.uint32_to_sizet l in
    let adj = A.ghost_split input l_sz in
    let res = add' ha iv (A.split_l input l_sz) l in
    A.ghost_join (A.split_l input l_sz) (A.split_r input l_sz) adj;
    assert (Seq.equal (Seq.append (Seq.slice s 0 (US.v l_sz))
                                  (Seq.slice s (US.v l_sz) (Seq.length s)))
                      s);
    rewrite (A.pts_to (A.merge (A.split_l input l_sz) (A.split_r input l_sz)) _ _)
            (A.pts_to input p s);
    rewrite (ha_val _ _)
            (ha_val ha 
                      (maybe_aggregate_hashes res h
                        (hash_one_value ivv (Seq.slice s 0 (U32.v l)))));
    return res
