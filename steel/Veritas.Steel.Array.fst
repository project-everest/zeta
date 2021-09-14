module Veritas.Steel.Array
open Steel.Memory
open Steel.Effect
open FStar.Ghost
module U32 = FStar.UInt32
module A = Steel.Array
module AT = Steel.Effect.Atomic
module Loops = Veritas.Steel.Loops

let varray_pts_to (#t:Type) (a:A.array t) (x:elseq t (A.length a))
  : vprop
  = admit()

let intro_varray_pts_to (#t:_)
                        (#opened:inames)
                        (a:A.array t)
  = AT.sladmit()

let elim_varray_pts_to (#t:_)
                       (#opened:inames)
                       (a:A.array t)
                       (c:elseq t (A.length a))
  = AT.sladmit()

let read_pt (#t:_)
            (a:A.array t)
            (#r:elseq t (A.length a))
            (i:U32.t { U32.v i < A.length a })
  = AT.sladmit();
    let v = magic #t () in
    AT.return  v


let write_pt (#t:_)
            (a:A.array t)
            (#r:elseq t (A.length a))
            (i:U32.t { U32.v i < A.length a })
            (v:t)
  = AT.sladmit()

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
