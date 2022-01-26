module Zeta.Steel.HashAccumulator
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Cast = FStar.Int.Cast
module A = Steel.ST.Array
open Steel.ST.Util
module Blake = Hacl.Blake2b_32
module Loops = Steel.ST.Loops
module R = Steel.ST.Reference
#push-options "--ide_id_info_off"
#push-options "--query_stats"

let hash_value_buf  = x:A.array U8.t { A.length x == 32}

noeq
type ha = {
  acc: hash_value_buf;
  ctr:R.ref U32.t
}

//[@@__steel_reduce__;__reduce__]
let ha_val (h:ha) (s:ehash_value_t) =
  A.pts_to h.acc full_perm (fst s) `star`
  exists_ (fun (n:U32.t) ->
      pure (U32.v n == snd s) `star`
      R.pts_to h.ctr full_perm n)

let unfold_ha_val (#o:_) (h:ha) (s:ehash_value_t)
  : STGhostT unit o
    (ha_val h s)
    (fun _ -> A.pts_to h.acc full_perm (fst s) `star`
           exists_ (fun (n:U32.t) ->
             pure (U32.v n == snd s) `star`
             R.pts_to h.ctr full_perm n))
  = rewrite (ha_val h s)
            (A.pts_to h.acc full_perm (fst s) `star`
              exists_ (fun (n:U32.t) ->
                pure (U32.v n == snd s) `star`
                R.pts_to h.ctr full_perm n));
    ()

let fold_ha_val (#o:_) (h:ha) (s:ehash_value_t)
  : STGhostT unit o
    (A.pts_to h.acc full_perm (fst s) `star`
     exists_ (fun (n:U32.t) ->
       pure (U32.v n == snd s) `star`
       R.pts_to h.ctr full_perm n))
    (fun _ -> ha_val h s)
  = rewrite (A.pts_to h.acc full_perm (fst s) `star`
              exists_ (fun (n:U32.t) ->
                pure (U32.v n == snd s) `star`
                R.pts_to h.ctr full_perm n))
            (ha_val h s);
    ()



let initial_hash
  = Seq.create 32 0uy, 0

let hash_one_value (s:Seq.seq U8.t { Seq.length s <= blake2_max_input_length })
  : hash_value_t
  = Blake.spec s 0 Seq.empty 32, 1

noextract inline_for_extraction
let xor_bytes (s1: Seq.seq U8.t)
              (s2: Seq.seq U8.t { Seq.length s1 == Seq.length s2 })
  : s3:Seq.seq U8.t { Seq.length s3 == Seq.length s1 }
  = Seq.init (Seq.length s1)
             (fun i -> Seq.index s1 i `FStar.UInt8.logxor` Seq.index s2 i)

let lbytes n = Seq.lseq U8.t n
let raw_hash_t = lbytes 32
let elbytes n = Ghost.erased (lbytes n)

let exor_bytes #l (s1 s2:elbytes l)
  : elbytes l
  = xor_bytes s1 s2

let aggregate_hashes (h0 h1: hash_value_t)
  : hash_value_t
  = xor_bytes (fst h0) (fst h1),
    snd h0 + snd h1

let mk_ehash_value (ws:Seq.lseq U8.t 32) (wc:U32.t)
  : ehash_value_t
  = ws, U32.v wc

let intro_ha_val (#o:_) (s:ha) (ws:Seq.lseq U8.t 32) (wc:U32.t) (res:ehash_value_t { res == mk_ehash_value ws wc })
  : STGhostT unit o
    (A.pts_to s.acc full_perm ws
      `star`
     R.pts_to s.ctr full_perm wc)
    (fun _ ->
      ha_val s res)
  = let w = mk_ehash_value ws wc in
    rewrite (A.pts_to _ _ _)
            (A.pts_to s.acc full_perm (fst w));
    intro_pure (U32.v wc == snd w);
    intro_exists #U32.t wc (fun n -> pure (U32.v n == snd w) `star` R.pts_to s.ctr full_perm n);
    fold_ha_val s w;
    rewrite (ha_val s w)
            (ha_val s res);
    ()


let elim_ha_val #o (#w:ehash_value_t) (s:ha)
  : STGhost (Ghost.erased U32.t) o
    (ha_val s w)
    (fun n -> A.pts_to s.acc full_perm (fst w) `star`
           R.pts_to s.ctr full_perm n)
    (requires True)
    (ensures fun n -> U32.v n == snd w)
  = unfold_ha_val s w;
    let n = elim_exists () in
    elim_pure _;
    n


[@@warn_on_use "uses an axiom"]
assume
val admit__ (#a:Type)
            (#p:pre_t)
            (#q:a -> vprop)
            (_:unit)
  : STF a p q True (fun _ -> False)

let create (_:unit)
  = let acc = A.alloc 0uy 32ul in
    let ctr = R.alloc 0ul in
    let ha = { acc; ctr } in
    //TODO: constructing values and transporting slprops to their fields is very tedious
    rewrite (A.pts_to acc _ _)
            (A.pts_to ha.acc full_perm (Seq.create 32 0uy));
    rewrite (R.pts_to ctr _ _)
            (R.pts_to ha.ctr full_perm 0ul);
    intro_ha_val ha _ _ initial_hash;
    return ha

let free (#h:ehash_value_t) (s:ha)
  = let _ = elim_ha_val s in
    R.free s.ctr;
    intro_exists (fst h) (A.pts_to s.acc full_perm);
    A.free s.acc

let exor_bytes_pfx #l (s1 s2:elbytes l) (i:nat { i <= l })
  : elbytes l
  = Seq.append
      (exor_bytes #i (Seq.slice s1 0 i) (Seq.slice s2 0 i))
      (Seq.slice s1 i (Seq.length s1))


let eraw_hash_t = elbytes 32

let upd_ehash_value (x:eraw_hash_t) (i:nat{i < 32}) (v:U8.t)
  : eraw_hash_t
  = Seq.upd x i v

#push-options "--z3rlimit_factor 3"
let extend_ehash_value (s1 s2:eraw_hash_t) (i:nat { i < 32 })
  : Lemma (upd_ehash_value
                     (exor_bytes_pfx s1 s2 i)
                     i
                     (U8.logxor (Seq.index s1 i) (Seq.index s2 i)) `Seq.equal`
           exor_bytes_pfx s1 s2 (i + 1))
  = ()
#pop-options


// let hpts_to (x:hash_value_buf) (s:raw_hash_t) =
//   A.varray_pts_to x s

assume
val read_ (#t:Type) (#p:perm)
         (a:A.array t)
         (#s:Ghost.erased (Seq.seq t))
         (i:U32.t)
  : ST t
       (A.pts_to a p s)
       (fun _ -> A.pts_to a p s)
       (requires
         U32.v i < Seq.length s)
       (ensures fun v ->
         U32.v i < Seq.length s /\
         v == Seq.index s (U32.v i))

// // #push-options "--print_implicits"
// let read_hbuf (#s:eraw_hash_t) (x:hash_value_buf) (i:U32.t{U32.v i < 32})
//   : ST U8.t
//     (A.pts_to x full_perm s)
//     (fun _ -> A.pts_to x full_perm s)
//     (requires True)
//     (ensures fun v ->
//       U32.v i < A.length x /\
//       Seq.length s == A.length x /\
//       v == Seq.index s (U32.v i))
//   = A.pts_to_length x s;
//     assert (Seq.length s == A.length x);
//     assert (A.length x == 32);
//     assert (U32.v i < Seq.length s);
// //    let j : (j:U32.t { U32.v j < Seq.length s }) = i in
//     let v = read_ #U8.t#x i in
//     admit__()
//     return v

//   AT.rewrite_slprop
//          (hpts_to x s)
//          (A.varray_pts_to x (Ghost.reveal #(Seq.lseq U8.t (A.length x)) s))
//          (fun _ -> ());
//     A.elim_varray_pts_to x s;
//     let v = A.index x i in
//     let _ = A.intro_varray_pts_to x in
//     AT.change_equal_slprop (A.varray_pts_to _ _)
//                            (hpts_to x s);
//     AT.return v

// let write_hbuf (#s:eraw_hash_t) (x:hash_value_buf) (i:U32.t{U32.v i < 32}) (v:U8.t)
//   : SteelT unit
//     (hpts_to x s)
//     (fun _ -> hpts_to x (upd_ehash_value s (U32.v i) v))
//   = AT.rewrite_slprop
//          (hpts_to x s)
//          (A.varray_pts_to x (Ghost.reveal #(Seq.lseq U8.t (A.length x)) s))
//          (fun _ -> ());
//     A.elim_varray_pts_to x _;
//     A.upd x i v;
//     let _ = A.intro_varray_pts_to x in
//     AT.change_equal_slprop (A.varray_pts_to _ _)
//                            (hpts_to _ _)

// let return_ghost (#a:Type u#a)
//                  (#opened_invariants:inames)
//                  (#p:a -> vprop)
//                  (x:a)
//   : AT.SteelGhost a opened_invariants
//          (p x) p
//          (requires fun _ -> True)
//          (ensures fun _ v _ -> x == v)
//   = AT.noop(); x

// #push-options "--print_implicits --print_universes"
// let intro_hpts_to (#o:_) (x:hash_value_buf)
//   : AT.SteelGhost eraw_hash_t o
//     (A.varray x)
//     (fun v -> hpts_to x (Ghost.reveal #raw_hash_t v))
//     (requires fun _ -> True)
//     (ensures fun h v _ ->
//       A.asel x h == Ghost.reveal v)
//   = let v : A.elseq _ (A.length x) = A.intro_varray_pts_to x in
//     AT.rewrite_slprop (A.varray_pts_to x v)
//                       (hpts_to x (Ghost.reveal #raw_hash_t v))
//                       (fun _ -> ());
//     return_ghost #(Ghost.erased raw_hash_t)
//                  #_
//                  #(fun (v:Ghost.erased raw_hash_t) ->
//                    hpts_to x (Ghost.reveal v))
//                  v

// let elim_hpts_to (#o:_) (#e:eraw_hash_t) (x:hash_value_buf)
//   : AT.SteelGhost unit o
//     (hpts_to x e)
//     (fun _ -> A.varray x)
//     (requires fun _ -> True)
//     (ensures fun _ _ h ->
//       Ghost.reveal e == A.asel x h)
//   = AT.rewrite_slprop
//          (hpts_to x e)
//          (A.varray_pts_to x (Ghost.reveal #(Seq.lseq U8.t (A.length x)) e))
//          (fun _ -> ());
//     A.elim_varray_pts_to x e

#push-options "--query_stats --fuel 0 --ifuel 0"
let aggregate_raw_hashes
    (s1: eraw_hash_t)
    (s2: eraw_hash_t)
    (b1: hash_value_buf)
    (b2: hash_value_buf)
  : STT unit
    (A.pts_to b1 full_perm s1 `star`
     A.pts_to b2 full_perm s2)
    (fun _ ->
     A.pts_to b1 full_perm (exor_bytes s1 s2) `star`
     A.pts_to b2 full_perm s2)
  = let inv (i:Loops.nat_at_most 32ul)
      : vprop
      = A.pts_to b1 full_perm (exor_bytes_pfx s1 s2 i) `star`
        A.pts_to b2 full_perm s2
    in
    [@@inline_let]
    let body (i:Loops.u32_between 0ul 32ul)
      : STT unit
        (inv (U32.v i))
        (fun _ -> inv (U32.v i + 1))
      = // rewrite
        //     (inv (U32.v i))
        //     (A.pts_to b1 full_perm (exor_bytes_pfx s1 s2 (U32.v i)) `star`
        //      A.pts_to b2 full_perm s2);
        // A.pts_to_length b1 _;
        // A.pts_to_length b2 s2;
        // let x1 = A.read b1 i in
        admit_()
        // let x2 = A.read b2 i in
        // A.write b1 i (U8.logxor x1 x2);

        // assert_ (A.pts_to b1 full_perm (upd_ehash_value
        //                                   (exor_bytes_pfx s1 s2 (U32.v i))
        //                                   (U32.v i)
        //                                   (U8.logxor x1 x2)));
        // extend_ehash_value s1 s2 (U32.v i);
        // rewrite (A.pts_to b1 _ _)
        //         (A.pts_to b1 full_perm (exor_bytes_pfx s1 s2 (U32.v i + 1)));
        // rewrite (A.pts_to b1 _ _ `star` A.pts_to b2 _ _)
        //         (inv (U32.v i + 1));
        // return ()
    in
    assert (exor_bytes_pfx s1 s2 0 `Seq.equal` s1);
    rewrite (A.pts_to b1 _ _ `star` A.pts_to b2 _ _)
            (inv 0);
    Loops.for_loop 0ul 32ul inv body;
    assert (exor_bytes_pfx s1 s2 32 `Seq.equal` exor_bytes s1 s2);
    rewrite (inv 32)
            (A.pts_to b1 _ _ `star` A.pts_to b2 _ _);
    return ()


inline_for_extraction
let narrow_uint64_to_uint32 (x:U64.t { U64.(x <=^ 0xffffffffuL) })
  : y:U32.t{U64.v x == U32.v y}
  = Cast.uint64_to_uint32 x

let aggregate #h1 #h2 (b1 b2: ha)
  = let _n1 = elim_ha_val b1 in
    let _n2 = elim_ha_val b2 in
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
      intro_ha_val b1 _ _ (maybe_aggregate_hashes false h1 h2);
      intro_ha_val b2 _ _ h2;
      return false
    )
    else (
      aggregate_raw_hashes _ _ b1.acc b2.acc;
      R.write b1.ctr (narrow_uint64_to_uint32 ctr);
      intro_ha_val b1 _ _ (maybe_aggregate_hashes true h1 h2);
      intro_ha_val b2 _ _ h2;
      return true
    )

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
      let b = A.compare b1.acc b2.acc 32ul in
      intro_ha_val b1 _ _ h1;
      intro_ha_val b2 _ _ h2;
      return b
    )

let add #h (ha:ha)
        #p #s (input:hashable_buffer)
        l
  = let acc = A.alloc 0uy 32ul in //TODO:would be nice to stack allocate this
    let ctr = R.alloc 1ul in  //TODO:would be nice to stack allocate this
    Blake.blake2b 32ul acc l input;
    let ha' = { acc; ctr } in
    rewrite (A.pts_to acc _ _)
            (A.pts_to ha'.acc full_perm
                      (fst (hash_one_value (Seq.slice s 0 (U32.v l)))));
    rewrite (R.pts_to ctr _ _)
            (R.pts_to ha'.ctr full_perm 1ul);
    intro_ha_val ha' _ _ (hash_one_value (Seq.slice s 0 (U32.v l)));
    let v = aggregate ha ha' in
    free ha';  //TODO:Then we wouldn't need this
    return v
