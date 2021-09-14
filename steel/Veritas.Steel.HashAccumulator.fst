module Veritas.Steel.HashAccumulator
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module A = Veritas.Steel.Array

open Steel.Memory
open Steel.Effect.Common
open Steel.Effect
open Steel.Reference
module AT = Steel.Effect.Atomic
module Blake = Hacl.Blake2b_32
module Loops = Veritas.Steel.Loops
#push-options "--fuel 0 --ifuel 0"

let initial_hash
  = Seq.create 32 0uy

let hash_value (s:Seq.seq U8.t { Seq.length s <= blake2_max_input_length })
  : hash_value_t
  = Blake.spec s 0 Seq.empty 32

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

let aggregate_hash_value (h0 h1: hash_value_t)
  : hash_value_t
  = xor_bytes h0 h1

let create_in (_:unit) = A.malloc 0uy 32ul

let exor_bytes_pfx #l (s1 s2:elbytes l) (i:nat { i <= l })
  : elbytes l
  = Seq.append
      (exor_bytes #i (Seq.slice s1 0 i) (Seq.slice s2 0 i))
      (Seq.slice s1 i (Seq.length s1))

let ehash_value_t = elbytes 32

let upd_ehash_value (x:ehash_value_t) (i:nat{i < 32}) (v:U8.t)
  : ehash_value_t
  = Seq.upd x i v

#push-options "--z3rlimit_factor 3"
let extend_ehash_value (s1 s2:ehash_value_t) (i:nat { i < 32 })
  : Lemma (upd_ehash_value
                     (exor_bytes_pfx s1 s2 i)
                     i
                     (U8.logxor (Seq.index s1 i) (Seq.index s2 i)) `Seq.equal`
           exor_bytes_pfx s1 s2 (i + 1))
  = ()
#pop-options

let hpts_to (x:hash_value_buf) (s:ehash_value_t) =
  A.varray_pts_to x s

let read_hbuf (#s:ehash_value_t) (x:hash_value_buf) (i:U32.t{U32.v i < 32})
  : Steel U8.t
    (hpts_to x s)
    (fun _ -> hpts_to x s)
    (requires fun _ -> True)
    (ensures fun _ v _ ->
      v == Seq.index s (U32.v i))
  = let v = A.read_pt x i in AT.return v

let write_hbuf (#s:ehash_value_t) (x:hash_value_buf) (i:U32.t{U32.v i < 32}) (v:U8.t)
  : SteelT unit
    (hpts_to x s)
    (fun _ -> hpts_to x (upd_ehash_value s (U32.v i) v))
  = A.write_pt x i v;
    AT.change_equal_slprop (A.varray_pts_to _ _)
                           (hpts_to _ _)

let intro_hpts_to (#o:_) (x:hash_value_buf)
  : AT.SteelGhost ehash_value_t o
    (A.varray x)
    (fun v -> hpts_to x v)
    (requires fun _ -> True)
    (ensures fun h v _ ->
      as_hash_value x h == Ghost.reveal v)
  = A.intro_varray_pts_to x

let elim_hpts_to (#o:_) (#e:ehash_value_t) (x:hash_value_buf)
  : AT.SteelGhost unit o
    (hpts_to x e)
    (fun _ -> A.varray x)
    (requires fun _ -> True)
    (ensures fun _ _ h ->
      Ghost.reveal e == as_hash_value x h)
  = A.elim_varray_pts_to x e

#push-options "--query_stats --fuel 0 --ifuel 0"
let aggregate_hash_value_pts
    (s1: ehash_value_t)
    (s2: ehash_value_t)
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

let aggregate_hash_value_buf (b1: hash_value_buf) (b2: hash_value_buf)
  = let _ = intro_hpts_to b1 in
    let _ = intro_hpts_to b2 in
    aggregate_hash_value_pts _ _ b1 b2;
    elim_hpts_to b1;
    elim_hpts_to b2


let add (s:hash_value_buf) (input:hashable_buffer) (l:U32.t)
  = let tmp = A.malloc 0uy 32ul in
    Blake.blake2b 32ul tmp l input;
    aggregate_hash_value_buf s tmp;
    A.free tmp;
    let h1 = AT.get() in //Weird to need this
    assert (A.asel s h1 == v_hash s h1);
    AT.return ()

let get' (#e0 #e1:ehash_value_t)
         (s:state)
         (out:hash_value_buf)
  : SteelT unit
    (hpts_to s e0 `star` A.varray_pts_to out e1)
    (fun _ ->
      hpts_to s e0 `star` A.varray_pts_to out (A.coerce e0))
  = AT.change_equal_slprop (hpts_to s _)
                           (A.varray_pts_to s e0);
    A.memcpy s out 32ul;
    AT.change_equal_slprop (A.varray_pts_to s _)
                           (hpts_to s _)

let get (s:state) (out:hash_value_buf)
  : Steel unit
    (A.varray s `star` A.varray out)
    (fun _ -> A.varray s `star` A.varray out)
    (requires fun _ -> True)
    (ensures fun h0 _ h1 ->
       v_hash s h0 == as_hash_value out h1 /\
       v_hash s h1 == v_hash s h0)
  = let _ = intro_hpts_to s in
    let _ = A.intro_varray_pts_to out in
    get' s out;
    elim_hpts_to s;
    A.elim_varray_pts_to out _;
    AT.return ()

let free (s:state) = A.free s
