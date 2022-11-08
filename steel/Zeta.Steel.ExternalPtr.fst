module Zeta.Steel.ExternalPtr

open Steel.ST.GenElim

let extern_ptr = A.array U8.t

[@@__reduce__]
let buffers_maybe_disjoint_case1
  (b2: A.array U8.t)
  (b2_len: nat)
: Tot vprop
= exists_ (fun (b2_contents: Seq.lseq U8.t b2_len) -> A.pts_to b2 full_perm b2_contents)

let buffer_includes
  (larger: A.array U8.t)
  (smaller: A.array U8.t)
: Tot prop
= exists (b1 b2: A.array U8.t) .
  A.adjacent b1 smaller /\
  A.adjacent smaller b2 /\
  A.merge_into (A.merge b1 smaller) b2 larger /\
  FStar.UInt.fits (A.length larger) 32 // to extract the offset of each subbuffer in the larger buffer

let tagl (#t: Type) (x: t) : Tot t = x
let tagr (#t: Type) (x: t) : Tot t = x

let buffers_maybe_disjoint_case2_prop
  (b1: A.array U8.t)
  (b2: A.array U8.t)
  (b2_len: nat)
  (bl: A.array U8.t)
  (br: A.array U8.t)
: Tot prop
= 
      A.adjacent bl b1 /\ A.adjacent b1 br /\
      buffer_includes (A.merge (A.merge bl b1) br) b2 /\
      A.length b2 == b2_len

[@@__reduce__]
let buffers_maybe_disjoint_case2
  (b1: A.array U8.t)
  (b2: A.array U8.t)
  (b2_len: nat)
: Tot vprop
= exists_ (fun (bl: A.array U8.t) -> exists_ (fun cl -> exists_ (fun (br: A.array U8.t) -> exists_ (fun cr ->
    A.pts_to (tagl bl) full_perm cl `star`
    A.pts_to (tagr br) full_perm cr `star`
    pure (buffers_maybe_disjoint_case2_prop b1 b2 b2_len bl br)
  ))))

let buffers_maybe_disjoint_cases
  (b1: A.array U8.t)
  (b2: A.array U8.t)
  (b2_len: nat)
  (case: bool)
: Tot vprop
= if case
  then buffers_maybe_disjoint_case1 b2 b2_len
  else buffers_maybe_disjoint_case2 b1 b2 b2_len

[@@__reduce__]
let buffers_maybe_disjoint'
  (b1: A.array U8.t)
  (b1_contents: Seq.seq U8.t)
  (b2: A.array U8.t)
  (b2_len: nat)
: Tot vprop
= A.pts_to b1 full_perm b1_contents `star`
  exists_ (buffers_maybe_disjoint_cases b1 b2 b2_len)

let buffers_maybe_disjoint
  (b1: A.array U8.t)
  (b1_contents: Seq.seq U8.t)
  (b2: A.array U8.t)
  (b2_len: nat)
: Tot vprop
= buffers_maybe_disjoint' b1 b1_contents b2 b2_len

[@@__reduce__]
let extern_in_out_pts_to_unwritten
  (e1: extern_ptr)
  (e2: extern_ptr)
  (w1: Seq.seq U8.t)
  (l2: SizeT.t)
: Tot vprop
= buffers_maybe_disjoint e1 w1 e2 (SizeT.v l2)

[@@__reduce__]
let extern_in_out_pts_to_written
  (e1: extern_ptr)
  (e2: extern_ptr)
  (l1: nat)
  (w2: Seq.seq U8.t)
: Tot vprop
= buffers_maybe_disjoint e2 w2 e1 l1

let extern_in_out_pts_to
  (e1: extern_ptr)
  (e2: extern_ptr)
  (w1: Seq.seq U8.t)
  (s: state)
: Tot vprop
= match s with
  | Unread l2 
  | Read l2
    -> extern_in_out_pts_to_unwritten e1 e2 w1 l2
  | Written w2
    -> extern_in_out_pts_to_written e1 e2 (Seq.length w1) w2

let array_ghost_split
  (#opened: _)
  (a a1 a2: A.array U8.t) (c: Seq.seq U8.t)
  (sq: squash (A.merge_into a1 a2 a))
: STGhost (squash (Seq.length c == A.length a1 + A.length a2)) opened
    (A.pts_to a full_perm c)
    (fun _ -> A.pts_to a1 full_perm (Seq.slice c 0 (A.length a1)) `star` A.pts_to a2 full_perm (Seq.slice c (A.length a1) (Seq.length c)))
    (FStar.UInt.fits (A.length a) 32)
    (fun _ -> True)
= A.pts_to_length a c;
  assume (SizeT.fits (A.length a1));
  let i = SizeT.uint_to_t (A.length a1) in
  A.ptr_base_offset_inj (dfst a2) (dfst (A.split_r a i));
  A.ghost_split a i;
  rewrite (A.pts_to (A.split_l _ _) _ _) (A.pts_to a1 full_perm (Seq.slice c 0 (A.length a1)));
  rewrite (A.pts_to (A.split_r _ _) _ _) (A.pts_to a2 full_perm (Seq.slice c (A.length a1) (Seq.length c)));
  ()

#push-options "--z3rlimit 32"
#restart-solver

let swap_buffers_maybe_disjoint
  (#opened: _)
  (e1: extern_ptr)
  (w1: Seq.seq U8.t)
  (l1: nat)
  (e2: extern_ptr)
  (l2: nat)
: STGhost (Ghost.erased (Seq.seq U8.t)) opened
    (buffers_maybe_disjoint e1 w1 e2 l2)
    (fun w2 -> buffers_maybe_disjoint e2 w2 e1 l1)
    (l1 == A.length e1 \/ l1 == Seq.length w1)
    (fun w2 -> Seq.length w2 == l2)
= rewrite (buffers_maybe_disjoint e1 w1 e2 l2) (buffers_maybe_disjoint' e1 w1 e2 l2);
  A.pts_to_length e1 w1;
  let test = elim_exists () in
  if test
  then begin
    rewrite (buffers_maybe_disjoint_cases _ _ _ _) (buffers_maybe_disjoint_case1 e2 l2);
    let _ = gen_elim () in
    let w2 = vpattern_replace_erased (A.pts_to e2 full_perm) in
    rewrite (buffers_maybe_disjoint_case1 e1 l1) (buffers_maybe_disjoint_cases e2 e1 l1 test);
    A.pts_to_length e2 _;
    rewrite (buffers_maybe_disjoint' e2 w2 e1 l1) (buffers_maybe_disjoint e2 w2 e1 l1);
    w2
  end else begin
    rewrite (buffers_maybe_disjoint_cases _ _ _ _) (buffers_maybe_disjoint_case2 e1 e2 l2);
    let _ = gen_elim () in
    let bl = vpattern_replace #_ #_ #(tagl _) (fun x -> A.pts_to x _ _) in
    let br = vpattern_replace #_ #_ #(tagr _) (fun x -> A.pts_to x _ _) in
    A.ghost_join bl e1 ();
    A.ghost_join _ br ();
    let b0 = A.merge (A.merge bl e1) br in
    vpattern_rewrite (fun x -> A.pts_to x _ _) b0;
    let b1 = FStar.IndefiniteDescription.indefinite_description_ghost (A.array U8.t) (fun b1 ->
      exists (b2: A.array U8.t) .
      A.adjacent b1 e2 /\
      A.adjacent e2 b2 /\
      A.merge_into (A.merge b1 e2) b2 b0 /\
      FStar.UInt.fits (A.length b0) 32 // to extract the offset of each subbuffer in the larger buffer
    )
    in
    let b2 = FStar.IndefiniteDescription.indefinite_description_ghost (A.array U8.t) (fun b2 ->
      A.adjacent b1 e2 /\
      A.adjacent e2 b2 /\
      A.merge_into (A.merge b1 e2) b2 b0 /\
      FStar.UInt.fits (A.length b0) 32 // to extract the offset of each subbuffer in the larger buffer
    )
    in
    let _ = array_ghost_split b0 (A.merge b1 e2) (tagr b2) _ () in
    let _ = array_ghost_split (A.merge b1 e2) (tagl b1) e2 _ () in
    let w2 = vpattern_replace_erased (A.pts_to e2 _) in
    assert (A.adjacent bl e1 /\ A.adjacent e1 br /\ A.merge_into (A.merge bl e1) br b0 /\ FStar.UInt.fits (A.length b0) 32);
    noop ();
    rewrite (buffers_maybe_disjoint_case2 e2 e1 l1) (buffers_maybe_disjoint_cases e2 e1 l1 test);
    A.pts_to_length e2 _;
    rewrite (buffers_maybe_disjoint' e2 w2 e1 l1) (buffers_maybe_disjoint e2 w2 e1 l1);
    w2
  end

#pop-options

assume val enclave_check_valid_ptrs // implemented by enclave primitives. Need not check for disjointness
  (e1: extern_ptr)
  (n1: SizeT.t)
  (e2: extern_ptr)
  (n2: SizeT.t)
: ST bool
    emp
    (fun cases' -> is_valid_state e1 n1 e2 n2 cases')
    True
    (fun cases' ->
      (cases' == true ==> (
        SizeT.v n1 == A.length e1 /\
        SizeT.v n2 == A.length e2
      ))
    )

let extern_in_out_pts_to_is_valid
  e1 n1 e2 n2
=
  enclave_check_valid_ptrs e1 n1 e2 n2

let copy_extern_input_ptr
  e1 w1 e2 n out_len a
=
  let _ = gen_elim () in
  rewrite
    (extern_in_out_pts_to e1 e2 w1 (Unread out_len))
    (buffers_maybe_disjoint' e1 w1 e2 (SizeT.v out_len));
  A.pts_to_length e1 _;
  A.memcpy e1 a n;
  rewrite
    (buffers_maybe_disjoint' e1 w1 e2 (SizeT.v out_len))
    (extern_in_out_pts_to e1 e2 w1 (Read out_len))

let copy_extern_output_ptr
  e1 w1 e2 n a p contents
=
  let _ = gen_elim () in
  rewrite
    (extern_in_out_pts_to e1 e2 w1 (Read n))
    (buffers_maybe_disjoint' e1 w1 e2 (SizeT.v n));
  rewrite
    (buffers_maybe_disjoint' e1 w1 e2 (SizeT.v n))
    (buffers_maybe_disjoint e1 w1 e2 (SizeT.v n));
  let w2 = swap_buffers_maybe_disjoint e1 w1 (Seq.length w1) e2 (SizeT.v n) in
  rewrite
    (buffers_maybe_disjoint e2 w2 e1 (Seq.length w1))
    (buffers_maybe_disjoint' e2 w2 e1 (Seq.length w1));
  A.pts_to_length e2 _;
  A.memcpy a e2 n;
  rewrite
    (buffers_maybe_disjoint' e2 contents e1 (Seq.length w1))
    (extern_in_out_pts_to e1 e2 w1 (Written contents))
