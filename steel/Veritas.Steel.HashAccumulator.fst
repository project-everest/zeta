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

let elseq a (n:nat) = Ghost.erased (Seq.lseq a n)
let elbytes n = elseq U8.t n

let exor_bytes #l (s1 s2:elbytes l)
  : elbytes l
  = xor_bytes s1 s2

let aggregate_hash_value (h0 h1: hash_value_t)
  : hash_value_t
  = xor_bytes h0 h1

let create_in (_:unit) = A.malloc 0uy 32ul
//open FStar.Ghost

let exor_bytes_pfx #l (s1 s2:elbytes l) (i:nat { i <= l })
  : elbytes l
  = Seq.append
      (exor_bytes #i (Seq.slice s1 0 i) (Seq.slice s2 0 i))
      (Seq.slice s1 i (Seq.length s1))

assume
val varray_pts_to (#t:Type) (a:A.array t) (x:elseq t (A.length a)) : vprop

assume
val intro_varray_pts_to (#t:_)
                        (#opened:inames)
                        (a:A.array t)
  : AT.SteelGhost (elseq t (A.length a)) opened
    (A.varray a)
    (fun x -> varray_pts_to a x)
    (requires fun _ -> True)
    (ensures fun h0 x h1 ->
      Ghost.reveal x == A.asel a h0)

assume
val elim_varray_pts_to (#t:_)
                       (#opened:inames)
                       (a:A.array t)
                       (c:elseq t (A.length a))
  : AT.SteelGhost unit opened
    (varray_pts_to a c)
    (fun _ -> A.varray a)
    (requires fun _ -> True)
    (ensures fun _ _ h1 ->
      A.asel a h1 == Ghost.reveal c)

assume
val read_pt (#t:_)
            (a:A.array t)
            (#r:elseq t (A.length a))
            (i:U32.t { U32.v i < A.length a })
  : Steel t
    (varray_pts_to a r)
    (fun _ -> varray_pts_to a r)
    (requires fun _ -> True)
    (ensures fun h0 v h1 ->
      v == Seq.index r (U32.v i))

assume
val write_pt (#t:_)
            (a:A.array t)
            (#r:elseq t (A.length a))
            (i:U32.t { U32.v i < A.length a })
            (v:t)
  : SteelT unit
    (varray_pts_to a r)
    (fun _ -> varray_pts_to a (Seq.upd r (U32.v i) v))

let ehash_value_t = elbytes 32

let upd_ehash_value (x:ehash_value_t) (i:nat{i < 32}) (v:U8.t)
  : ehash_value_t
  = Seq.upd x i v

let extend_ehash_value (s1 s2:ehash_value_t) (i:nat { i < 32 })
  : Lemma (upd_ehash_value
                     (exor_bytes_pfx s1 s2 i)
                     i
                     (U8.logxor (Seq.index s1 i) (Seq.index s2 i)) `Seq.equal`
           exor_bytes_pfx s1 s2 (i + 1))
  = ()

let hpts_to (x:hash_value_buf) (s:ehash_value_t) =
  varray_pts_to x s

let read_hbuf (#s:ehash_value_t) (x:hash_value_buf) (i:U32.t{U32.v i < 32})
  : Steel U8.t
    (hpts_to x s)
    (fun _ -> hpts_to x s)
    (requires fun _ -> True)
    (ensures fun _ v _ ->
      v == Seq.index s (U32.v i))
  = let v = read_pt x i in AT.return v

let write_hbuf (#s:ehash_value_t) (x:hash_value_buf) (i:U32.t{U32.v i < 32}) (v:U8.t)
  : SteelT unit
    (hpts_to x s)
    (fun _ -> hpts_to x (upd_ehash_value s (U32.v i) v))
  = write_pt x i v;
    AT.change_equal_slprop (varray_pts_to _ _)
                           (hpts_to _ _)

let intro_hpts_to (#o:_) (x:hash_value_buf)
  : AT.SteelGhost ehash_value_t o
    (A.varray x)
    (fun v -> hpts_to x v)
    (requires fun _ -> True)
    (ensures fun h v _ ->
      as_hash_value x h == Ghost.reveal v)
  = intro_varray_pts_to x

let elim_hpts_to (#o:_) (#e:ehash_value_t) (x:hash_value_buf)
  : AT.SteelGhost unit o
    (hpts_to x e)
    (fun _ -> A.varray x)
    (requires fun _ -> True)
    (ensures fun _ _ h ->
      Ghost.reveal e == as_hash_value x h)
  = elim_varray_pts_to x e

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


let size_t = U32.t
let max_output = 64

assume
val blake2b:
    nn:size_t{1 <= UInt32.v nn /\ UInt32.v nn <= max_output}
  -> output: A.array U8.t
  -> ll: size_t
  -> d: A.array U8.t
  -> Steel unit
  (A.varray output `star` A.varray d)
  (fun _ -> A.varray output `star` A.varray d)
  (requires fun _ ->
    A.length d >= U32.v ll /\
    A.length output = U32.v nn)
  (ensures fun h0 _ h1 ->
    A.length d >= U32.v ll /\
    A.length output = U32.v nn /\
    A.asel d h0 == A.asel d h1 /\
    A.asel output h1 ==
      Blake.spec
        (Seq.slice (A.asel d h0) 0 (U32.v ll))
        0 Seq.empty (UInt32.v nn))

let add (s:hash_value_buf) (input:hashable_buffer) (l:U32.t)
  = let tmp = A.malloc 0uy 32ul in
    blake2b 32ul tmp l input;
    aggregate_hash_value_buf s tmp;
    A.free tmp;
    let h1 = AT.get() in //Weird to need this
    assert (A.asel s h1 == v_hash s h1);
    AT.return ()


let coerce #t (#l0 #l1:_) (e:elseq t l0 { l0 = l1}) : elseq t l1 = e

let prefix_copied #t #l0 #l1
                  (e0:elseq t l0)
                  (e1:elseq t l1)
                  (i:nat { i <= l0 /\ l0 == l1})
   : elseq t l1
   = (Seq.append (Seq.slice e0 0 i) (Seq.slice e1 i (Seq.length e1)))

let slice_lem (#t:_)
              (#l0 #l1:_)
              (e0:elseq t l0)
              (e1:elseq t l1)
  : Lemma
    (requires l0 == l1)
    (ensures prefix_copied e0 e1 l0 `Seq.equal`
             coerce #t #l0 #l1 e0)
  = ()

let memcpy #t (a0 a1:A.array t)
              (#e0:elseq t (A.length a0))
              (#e1:elseq t (A.length a1))
              (i:U32.t{ U32.v i == A.length a0 /\ A.length a0 == A.length a1 })
  : SteelT unit
    (varray_pts_to a0 e0 `star` varray_pts_to a1 e1)
    (fun _ -> varray_pts_to a0 e0 `star` varray_pts_to a1 (coerce e0))
  = let inv (j:Loops.nat_at_most i)
      : vprop
      = varray_pts_to a0 e0 `star`
        varray_pts_to a1 (prefix_copied e0 e1 j)
    in
    let body (j:Loops.u32_between 0ul i)
      : SteelT unit
        (inv (U32.v j))
        (fun _ -> inv (U32.v j + 1))
      = AT.change_equal_slprop
            (inv (U32.v j))
            (varray_pts_to a0 e0 `star`
             varray_pts_to a1 (prefix_copied e0 e1 (U32.v j)));
        let z = read_pt a0 j in
        write_pt a1 j z;
        assert (Seq.upd (prefix_copied e0 e1 (U32.v j)) (U32.v j) z `Seq.equal`
                prefix_copied e0 e1 (U32.v j + 1));
        AT.change_equal_slprop (varray_pts_to a0 e0 `star` varray_pts_to a1 _)
                               (inv (U32.v j + 1));
        AT.return ()
    in
    assert (prefix_copied e0 e1 0 `Seq.equal` e1);
    AT.change_equal_slprop (varray_pts_to a1 _)
                           (varray_pts_to a1 (prefix_copied e0 e1 (U32.v 0ul)));
    AT.change_equal_slprop (varray_pts_to a0 e0 `star` varray_pts_to a1 _)
                           (inv (U32.v 0ul));
    Loops.for_loop 0ul i inv body;
    AT.slassert (inv (U32.v i));
    AT.change_equal_slprop (inv (U32.v i))
                           (varray_pts_to a0 e0 `star`
                            varray_pts_to a1 (prefix_copied e0 e1 (U32.v i)));
    slice_lem e0 e1;
    AT.change_equal_slprop (varray_pts_to a1 (prefix_copied e0 e1 (U32.v i)))
                           (varray_pts_to a1 (coerce e0));
    AT.return ()

let get' (#e0 #e1:ehash_value_t)
         (s:state)
         (out:hash_value_buf)
  : SteelT unit
    (hpts_to s e0 `star` varray_pts_to out e1)
    (fun _ ->
      hpts_to s e0 `star` varray_pts_to out (coerce e0))
  = AT.change_equal_slprop (hpts_to s _)
                           (varray_pts_to s e0);
    memcpy s out 32ul;
    AT.change_equal_slprop (varray_pts_to s _)
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
    let _ = intro_varray_pts_to out in
    get' s out;
    elim_hpts_to s;
    elim_varray_pts_to out _;
    AT.return ()

let free (s:state) = A.free s
