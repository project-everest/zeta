module Veritas.Steel.HashAccumulator
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Cast = FStar.Int.Cast
module A = Steel.Array

open Steel.Memory
open Steel.Effect.Common
open Steel.Effect
module AT = Steel.Effect.Atomic
module Blake = Hacl.Blake2b_32
module Loops = Steel.Loops
module R = Steel.Reference
#push-options "--ide_id_info_off"
#push-options "--fuel 2 --ifuel 1" //to unfold t_of
#push-options "--query_stats"

let hash_value_buf  = x:A.array U8.t { A.length x == 32}

noeq
type ha = {
  acc: hash_value_buf;
  ctr:R.ref U32.t
}

[@@__steel_reduce__;__reduce__]
unfold
let ha_perm (h:ha) =
  A.varray h.acc `star` vptr h.ctr

let ha_sl x = hp_of (ha_perm x)

let ha_repr = A.contents U8.t 32 & U32.t

let ha_sel x = sel_of (ha_perm x)

let value_of x = fst x, U32.v (snd x)

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

let elbytes n = A.elseq U8.t n

let exor_bytes #l (s1 s2:elbytes l)
  : elbytes l
  = xor_bytes s1 s2

let aggregate_hashes (h0 h1: hash_value_t)
  : hash_value_t
  = xor_bytes (fst h0) (fst h1),
    snd h0 + snd h1

let intro_ha_inv (#o:_) (s:ha)
  : AT.SteelGhost unit o
    (A.varray s.acc `star` R.vptr s.ctr)
    (fun _ -> ha_inv s)
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      hash_value_of s h1 ==
        (A.asel s.acc h0,
         U32.v (R.sel s.ctr h0)))
  = AT.change_slprop_rel
       (A.varray s.acc `star` R.vptr s.ctr)
       (ha_inv s)
       (fun x y -> x == y)
       (fun m -> ())

let elim_ha_inv #o (s:ha)
  : AT.SteelGhost unit o
    (ha_inv s)
    (fun _ -> A.varray s.acc `star` R.vptr s.ctr)
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      hash_value_of s h0 ==
        (A.asel s.acc h1,
         U32.v (R.sel s.ctr h1)))
  = AT.change_slprop_rel
       (ha_inv s)
       (A.varray s.acc `star` R.vptr s.ctr)
       (fun x y -> x == y)
       (fun m -> ())

let create (_:unit)
  = let acc = A.malloc 0uy 32ul in
    let ctr = R.malloc 0ul in
    let ha = { acc; ctr } in
    //TODO: this is annoying
    AT.change_equal_slprop (A.varray acc `star` R.vptr ctr)
                           (A.varray ha.acc `star` R.vptr ha.ctr);
    intro_ha_inv ha;
    AT.return ha

let free (s:ha)
  = elim_ha_inv s;
    A.free s.acc;
    R.free s.ctr

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


let hpts_to (x:hash_value_buf) (s:eraw_hash_t) =
  A.varray_pts_to x s

let read_hbuf (#s:eraw_hash_t) (x:hash_value_buf) (i:U32.t{U32.v i < 32})
  : Steel U8.t
    (hpts_to x s)
    (fun _ -> hpts_to x s)
    (requires fun _ -> True)
    (ensures fun _ v _ ->
      v == Seq.index s (U32.v i))
  = A.elim_varray_pts_to x _;
    let v = A.index x i in
    let _ = A.intro_varray_pts_to x in
    AT.change_equal_slprop (A.varray_pts_to _ _)
                           (hpts_to x s);
    AT.return v

let write_hbuf (#s:eraw_hash_t) (x:hash_value_buf) (i:U32.t{U32.v i < 32}) (v:U8.t)
  : SteelT unit
    (hpts_to x s)
    (fun _ -> hpts_to x (upd_ehash_value s (U32.v i) v))
  = A.elim_varray_pts_to x _;
    A.upd x i v;
    let _ = A.intro_varray_pts_to x in
    AT.change_equal_slprop (A.varray_pts_to _ _)
                           (hpts_to _ _)

let intro_hpts_to (#o:_) (x:hash_value_buf)
  : AT.SteelGhost eraw_hash_t o
    (A.varray x)
    (fun v -> hpts_to x v)
    (requires fun _ -> True)
    (ensures fun h v _ ->
      A.asel x h == Ghost.reveal v)
  = A.intro_varray_pts_to x

let elim_hpts_to (#o:_) (#e:eraw_hash_t) (x:hash_value_buf)
  : AT.SteelGhost unit o
    (hpts_to x e)
    (fun _ -> A.varray x)
    (requires fun _ -> True)
    (ensures fun _ _ h ->
      Ghost.reveal e == A.asel x h)
  = A.elim_varray_pts_to x e

#push-options "--query_stats --fuel 0 --ifuel 0"
let aggregate_hash_value_pts
    (s1: eraw_hash_t)
    (s2: eraw_hash_t)
    (b1: hash_value_buf)
    (b2: hash_value_buf)
  : SteelT unit
    (hpts_to b1 s1 `star`
     hpts_to b2 s2)
    (fun _ ->
     hpts_to b1 (exor_bytes s1 s2) `star`
     hpts_to b2 s2)
  = let inv (i:Loops.nat_at_most 32ul)
      : vprop
      = hpts_to b1 (exor_bytes_pfx s1 s2 i) `star`
        hpts_to b2 s2
    in
    [@@inline_let]
    let body (i:Loops.u32_between 0ul 32ul)
      : SteelT unit
        (inv (U32.v i))
        (fun _ -> inv (U32.v i + 1))
      = AT.change_equal_slprop
            (inv (U32.v i))
            (hpts_to b1 (exor_bytes_pfx s1 s2 (U32.v i)) `star`
             hpts_to b2 s2);
        let x1 = read_hbuf b1 i in
        let x2 = read_hbuf b2 i in
        write_hbuf b1 i (U8.logxor x1 x2);
        AT.slassert (hpts_to b1 (upd_ehash_value
                                          (exor_bytes_pfx s1 s2 (U32.v i))
                                          (U32.v i)
                                          (U8.logxor x1 x2)));
        extend_ehash_value s1 s2 (U32.v i);
        AT.change_equal_slprop (hpts_to b1 _)
                               (hpts_to b1 (exor_bytes_pfx s1 s2 (U32.v i + 1)));
        AT.change_equal_slprop (hpts_to b1 _ `star` hpts_to b2 _)
                               (inv (U32.v i + 1));
        AT.return ()
    in
    assert (exor_bytes_pfx s1 s2 0 `Seq.equal` s1);
    AT.change_equal_slprop (hpts_to b1 _ `star` hpts_to b2 _)
                           (inv 0);
    Loops.for_loop 0ul 32ul inv body;
    assert (exor_bytes_pfx s1 s2 32 `Seq.equal` exor_bytes s1 s2);
    AT.change_equal_slprop (inv 32)
                           (hpts_to b1 _ `star` hpts_to b2 _);
    AT.return ()

let aggregate_raw_hashes (b1: hash_value_buf) (b2: hash_value_buf)
  : Steel unit
    (A.varray b1 `star` A.varray b2)
    (fun _ -> A.varray b1 `star` A.varray b2)
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
      A.asel b2 h0 == A.asel b2 h1 /\
      A.asel b1 h1 == xor_bytes (A.asel b1 h0) (A.asel b2 h0))
  = let _ = intro_hpts_to b1 in
    let _ = intro_hpts_to b2 in
    aggregate_hash_value_pts _ _ b1 b2;
    elim_hpts_to b1;
    elim_hpts_to b2


inline_for_extraction
let narrow_uint64_to_uint32 (x:U64.t { U64.(x <=^ 0xffffffffuL) })
  : y:U32.t{U64.v x == U32.v y}
  = Cast.uint64_to_uint32 x

let aggregate (b1 b2: ha)
  = elim_ha_inv b1;
    elim_ha_inv b2;
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
      intro_ha_inv b1;
      intro_ha_inv b2;
      AT.return false
    )
    else (
      aggregate_raw_hashes b1.acc b2.acc;
      R.write b1.ctr (narrow_uint64_to_uint32 ctr);
      intro_ha_inv b1;
      intro_ha_inv b2;
      AT.return true
    )

let compare (b1 b2:ha)
  = elim_ha_inv b1;
    elim_ha_inv b2;
    let c1 = R.read b1.ctr in
    let c2 = R.read b2.ctr in
    if c1 <> c2
    then (
      intro_ha_inv b1;
      intro_ha_inv b2;
      AT.return false
    )
    else (
      let b = A.compare b1.acc b2.acc 32ul in
      intro_ha_inv b1;
      intro_ha_inv b2;
      AT.return b
    )

let add (s:ha) (input:hashable_buffer) (l:U32.t)
  = let acc = A.malloc 0uy 32ul in //TODO:would be nice to stack allocate this
    let ctr = R.malloc 1ul in  //TODO:would be nice to stack allocate this
    Blake.blake2b 32ul acc l input;
    let ha' = { acc; ctr } in
    AT.change_equal_slprop
      (A.varray acc `star` R.vptr ctr)
      (A.varray ha'.acc `star` R.vptr ha'.ctr);
    intro_ha_inv ha';
    let v = aggregate s ha' in
    free ha';  //TODO:Then we wouldn't need this
    AT.return v

let ha_val (r:ha) (v:Ghost.erased hash_value_t)
  : vprop
  = A.varray_pts_to r.acc (fst v) `star`
    AT.h_exists (fun (i:Ghost.erased U32.t) ->
      pure (U32.v i == (snd v)) `star`
      R.pts_to r.ctr Steel.FractionalPermission.full_perm i)


let intro_ha_val #o (r:ha) (v:Ghost.erased hash_value_t)
    : AT.SteelGhostT unit o
      (A.varray_pts_to r.acc (fst v) `star`
       AT.h_exists (fun (i:Ghost.erased U32.t) ->
         pure (U32.v i == (snd v)) `star`
         R.pts_to r.ctr Steel.FractionalPermission.full_perm i))
      (fun _ -> ha_val r v)
    = assert_spinoff
         ((A.varray_pts_to r.acc (fst v) `star`
            AT.h_exists (fun (i:Ghost.erased U32.t) ->
              pure (U32.v i == (snd v)) `star`
              R.pts_to r.ctr Steel.FractionalPermission.full_perm i)) ==
          (ha_val r v));
      AT.change_equal_slprop
      (A.varray_pts_to r.acc (fst v) `star`
       AT.h_exists (fun (i:Ghost.erased U32.t) ->
         pure (U32.v i == (snd v)) `star`
         R.pts_to r.ctr Steel.FractionalPermission.full_perm i))
      (ha_val r v)

let ha_val_of_ha_inv (#o:_) (s:ha)
  : AT.SteelGhost (Ghost.erased hash_value_t) o
    (ha_inv s)
    (fun v -> ha_val s v)
    (requires fun _ -> True)
    (ensures fun h0 x _ ->
       Ghost.reveal x == hash_value_of s h0)
  = elim_ha_inv s;
    let i = R.elim_vptr s.ctr _ in
    let raw_hash = A.intro_varray_pts_to s.acc in
    let v : Ghost.erased hash_value_t =
        Ghost.hide (Ghost.reveal raw_hash, U32.v i)
    in
    AT.change_equal_slprop
      (A.varray_pts_to s.acc raw_hash)
      (A.varray_pts_to s.acc (fst v));
    AT.intro_pure (U32.v i == snd v);
    AT.intro_exists #(Ghost.erased U32.t) i
      (fun i ->
         pure (U32.v i == (snd v)) `star`
         R.pts_to s.ctr Steel.FractionalPermission.full_perm i);
    intro_ha_val s v;
    v


let elim_ha_val #o (r:ha) (v:Ghost.erased hash_value_t)
    : AT.SteelGhostT unit o
      (ha_val r v)
      (fun _ -> A.varray_pts_to r.acc (fst v) `star`
       AT.h_exists (fun (i:Ghost.erased U32.t) ->
         pure (U32.v i == (snd v)) `star`
         R.pts_to r.ctr Steel.FractionalPermission.full_perm i))
    = assert_spinoff
         ((A.varray_pts_to r.acc (fst v) `star`
            AT.h_exists (fun (i:Ghost.erased U32.t) ->
              pure (U32.v i == (snd v)) `star`
              R.pts_to r.ctr Steel.FractionalPermission.full_perm i)) ==
          (ha_val r v));
      AT.change_equal_slprop
      (ha_val r v)
      (A.varray_pts_to r.acc (fst v) `star`
       AT.h_exists (fun (i:Ghost.erased U32.t) ->
         pure (U32.v i == (snd v)) `star`
         R.pts_to r.ctr Steel.FractionalPermission.full_perm i))

let ha_inv_of_ha_val #o #v (s:ha)
  = elim_ha_val s v;
    let i = AT.witness_exists () in
    AT.elim_pure _;
    A.elim_varray_pts_to s.acc _;
    R.intro_vptr s.ctr _ _;
    intro_ha_inv s
