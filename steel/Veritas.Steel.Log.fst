module Veritas.Steel.Log
module T = Veritas.Formats.Types
module A = Steel.Array
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module EP = Veritas.Formats
module R = Steel.Reference
module AT = Steel.Effect.Atomic

let contents #t (a:A.array t) = A.contents t (A.length a)

assume
val varray_pts_to (#t:_) (a:A.array t) (bs:Ghost.erased (contents a)) : vprop


assume
val intro_varray_pts_to (#t:_)
                        (#opened:inames)
                        (a:A.array t)
  : AT.SteelGhost (Ghost.erased (contents a)) opened
    (A.varray a)
    (fun x -> varray_pts_to a x `star` emp)
    (requires fun _ -> True)
    (ensures fun h0 x h1 ->
      Ghost.reveal x == A.asel a h0)

assume
val elim_varray_pts_to (#t:_)
                       (#opened:inames)
                       (a:A.array t)
                       (c:Ghost.erased (contents a))
  : AT.SteelGhost unit opened
    (varray_pts_to a c)
    (fun _ -> A.varray a)
    (requires fun _ -> True)
    (ensures fun _ _ h1 ->
      A.asel a h1 == Ghost.reveal c)

let bytes_repr (l:nat) = Ghost.erased (Seq.lseq U8.t l)

let rec parsed_raw (s:Seq.seq U8.t) (r: repr)
  : Tot Type
    (decreases (Seq.length s))
  = if Seq.length r = 0
    then Seq.length s == 0
    else (
      exists (to:nat{0 < to /\ to <= Seq.length s}).
           EP.valid_entry s 0 to (Seq.head r) /\
           parsed_raw (Seq.slice s to (Seq.length s)) (Seq.tail r)
    )

let parsed_raw_until
      (#len:nat)
      (pos:EP.bounded_u32 len)
      (s:bytes_repr len)
      (r:repr)
  : prop
  = parsed_raw (Seq.slice s 0 (U32.v pos)) r

let parsed s r = parsed_raw s (FStar.Ghost.reveal r)

#push-options "--fuel 1 --ifuel 0 --z3rlimit_factor 4"
let rec parsed_raw_append (s0 s1:Seq.seq U8.t) (r0 r1:repr)
  : Lemma
    (requires
      parsed_raw s0 r0 /\
      parsed_raw s1 r1)
    (ensures
      parsed_raw (Seq.append s0 s1) (Seq.append r0 r1))
    (decreases (Seq.length r0))
  = if Seq.length r0 = 0
    then (
      assert (Seq.append r0 r1 `Seq.equal` r1);
      assert (Seq.append s0 s1 `Seq.equal` s1)
    )
    else (
     assert (exists (to:nat{0 < to /\ to <= Seq.length s0}).
               EP.valid_entry s0 0 to (Seq.head r0) /\
               parsed_raw (Seq.slice s0 to (Seq.length s0)) (Seq.tail r0));

     let to = FStar.IndefiniteDescription.indefinite_description_ghost
                 (to:nat{0 < to /\ to <= Seq.length s0})
                 (fun to ->
                   EP.valid_entry s0 0 to (Seq.head r0) /\
                   parsed_raw (Seq.slice s0 to (Seq.length s0)) (Seq.tail r0))
     in
     let s0_tail = (Seq.slice s0 to (Seq.length s0)) in
     parsed_raw_append s0_tail s1 (Seq.tail r0) r1;
     let s0s1 = (Seq.append s0 s1) in
     let r0r1 = Seq.append r0 r1 in
     assert (Seq.slice s0s1 to (Seq.length s0s1)
            `Seq.equal`
             Seq.append s0_tail s1);
     assert (Seq.tail (Seq.append r0 r1)
            `Seq.equal`
             Seq.append (Seq.tail r0) r1);
     assert (parsed_raw (Seq.slice s0s1 to (Seq.length s0s1))
                        (Seq.tail r0r1));
     assert (EP.valid_entry s0 0 to (Seq.head r0r1));
     EP.valid_entry_slice s0 s0s1 0 to 0 to (Seq.head r0r1)
    )
#pop-options

let parsed_raw_singleton (#len:nat)
                         (s:Seq.lseq U8.t len)
                         (pos pos': EP.bounded_u32 len)
                         (e:T.vlog_entry)
  : Lemma
    (requires
      EP.valid_entry s (U32.v pos) (U32.v pos') e)
    (ensures
      U32.v pos < U32.v pos' /\
      parsed_raw (Seq.slice s (U32.v pos) (U32.v pos')) (Seq.create 1 e))
  = EP.valid_entry_pos_lt s (U32.v pos) (U32.v pos') e;
    let s' = (Seq.slice s (U32.v pos) (U32.v pos')) in
    let len = Seq.length s' in
    let r = Seq.create 1 e in
    assert (Seq.tail r `Seq.equal` Seq.empty);
    assert (parsed_raw (Seq.slice s' len len) (Seq.tail r));
    EP.valid_entry_slice s s' (U32.v pos) (U32.v pos') 0 len (Seq.head r)

let extend_parsed_raw_util
      (#len:nat)
      (pos:EP.bounded_u32 len)
      (s:bytes_repr len)
      (r:repr)
      (pos':EP.bounded_u32 len)
      (e:T.vlog_entry)
  : Lemma
    (requires
      parsed_raw_until pos s r /\
      EP.valid_entry s (U32.v pos) (U32.v pos') e)
    (ensures
      parsed_raw_until pos' s (snoc_log r e))
    (decreases (Seq.length s))
  = assert (parsed_raw (Seq.slice s 0 (U32.v pos)) r);
    EP.valid_entry_pos_lt s (U32.v pos) (U32.v pos') e;
    parsed_raw_singleton s pos pos' e;
    parsed_raw_append (Seq.slice s 0 (U32.v pos))
                      (Seq.slice s (U32.v pos) (U32.v pos'))
                      r (Seq.create 1 e);
    assert (Seq.equal
                  (Seq.append (Seq.slice s 0 (U32.v pos))
                              (Seq.slice s (U32.v pos) (U32.v pos')))
                  (Seq.slice s 0 (U32.v pos')));
    assert (Seq.equal (Seq.append r (Seq.create 1 e))
                      (snoc_log r e))

let parsed_raw_until_empty (len:_)
                           (pos:EP.bounded_u32 (U32.v len) { pos == 0ul })
                           (s:bytes_repr (U32.v len))
  : Lemma (parsed_raw_until pos s Seq.empty)
  = assert (parsed_raw (Seq.slice s 0 0) Seq.empty)

let parsed_raw_until_full
      (#len:nat)
      (pos:EP.bounded_u32 len)
      (s:bytes_repr len)
      (r:repr)
  : Lemma
    (requires
      U32.v pos == len /\
      parsed_raw_until pos s r)
    (ensures
      parsed s r)
  = assert (Seq.slice s 0 len `Seq.equal` s)

noeq
type log = {
  len   : U32.t;
  arr   : EP.larray U8.t len;
  pos   : R.ref (EP.bounded_u32 (U32.v len));
  ghost : R.ghost_ref (Seq.seq T.vlog_entry)
}

let log_len l = l.len
let log_array l = l.arr

let log_length l = U32.v (log_len l)



let varray_pts_to_u8 (#len:_)
                     (a:EP.larray U8.t len)
                     (bs:bytes_repr (U32.v len))
  : vprop
  = varray_pts_to a bs

let intro_varray_pts_to_u8 (#opened:inames)
                           (#len: U32.t)
                           (arr: EP.larray U8.t len)
  : AT.SteelGhost (bytes_repr (U32.v len)) opened
    (A.varray arr)
    (fun x -> varray_pts_to_u8 arr x)
    (requires fun _ -> True)
    (ensures fun h0 x h1 ->
      Ghost.reveal x == A.asel arr h0)
  = intro_varray_pts_to arr

let elim_varray_pts_to_u8 (#opened:inames)
                          (#len: U32.t)
                          (arr: EP.larray U8.t len)
                          (b: bytes_repr (U32.v len))
  : AT.SteelGhost unit opened
    (varray_pts_to_u8 arr b)
    (fun x -> A.varray arr)
    (requires fun _ -> True)
    (ensures fun h0 x h1 ->
      Ghost.reveal b == A.asel arr h1)
  = elim_varray_pts_to arr b

module Perm = Steel.FractionalPermission
[@@__reduce__; __steel_reduce__]
let log_with_parsed_prefix_raw
       (len: U32.t)
       (arr: EP.larray U8.t len)
       (pos: R.ref (EP.bounded_u32 (U32.v len)))
       (ghost: R.ghost_ref (Seq.seq T.vlog_entry))
       (pos_val: EP.bounded_u32 (U32.v len))
       (bs : bytes_repr (U32.v len))
       (s  : repr)
  : vprop
  = R.pts_to pos Perm.full_perm pos_val `star`
    varray_pts_to_u8 arr bs `star`
    R.ghost_pts_to ghost Perm.full_perm s `star`
    pure (parsed_raw_until pos_val bs s)

//[@@__reduce__; __steel_reduce__]
let log_with_parsed_prefix (l:log) (s:repr)
  = AT.h_exists (fun p ->
    AT.h_exists (fun bs ->
    log_with_parsed_prefix_raw l.len l.arr l.pos l.ghost p bs s))

let coerce_bounded_u32 (l:log) (len:U32.t) (x:EP.bounded_u32 (U32.v len))
  : Pure
     (EP.bounded_u32 (U32.v l.len))
     (requires l.len == len)
     (fun _ -> True)
  = x

let coerce_bytes_repr (l:log) (len:U32.t) (x:bytes_repr (U32.v len))
  : Pure
     (bytes_repr (U32.v l.len))
     (requires l.len == len)
     (fun _ -> True)
  = x

let coerce_eq (#a:Type) (#t: a -> Type) (x:a) (y:a) (v:t x)
  : Pure (t y)
     (requires x==y)
     (fun _ -> True)
  = v

//module T = FStar.Tactics
let intro_log_with_parsed_prefix
     (l:log)
     (len:U32.t)
     (arr:EP.larray U8.t len)
     (pos:R.ref (EP.bounded_u32 (U32.v len)))
     (ghost: R.ghost_ref (Seq.seq T.vlog_entry))
     (pos_val: EP.bounded_u32 (U32.v len))
     (bs : bytes_repr (U32.v len))
     (s  : repr)
     (_  : squash (l.len == len))
 : Steel unit
   (log_with_parsed_prefix_raw len arr pos ghost pos_val bs s)
   (fun _ -> log_with_parsed_prefix l s)
   (requires fun _ ->
     l.len == len /\
     l.arr == arr /\
     l.pos == pos /\
     l.ghost == ghost)
   (ensures fun _ _ _ -> True)
 = let h = AT.get () in
   assert (l.len == len);
   let pos_val' : EP.bounded_u32 (U32.v l.len) = coerce_bounded_u32 l len pos_val in
   let bs' : bytes_repr (U32.v l.len) = coerce_bytes_repr l len bs in
   assert_spinoff(log_with_parsed_prefix_raw len arr pos ghost pos_val bs s ==
                  log_with_parsed_prefix_raw l.len l.arr l.pos l.ghost pos_val' bs' s);
   AT.change_equal_slprop
     (log_with_parsed_prefix_raw len arr pos ghost pos_val bs s)
     (log_with_parsed_prefix_raw l.len l.arr l.pos l.ghost pos_val' bs' s);
   AT.intro_exists bs'
                   (fun bs' -> log_with_parsed_prefix_raw l.len l.arr l.pos l.ghost pos_val' bs' s);
   AT.intro_exists pos_val'
                   (fun pos_val' ->
                     AT.h_exists
                     (fun bs' -> log_with_parsed_prefix_raw l.len l.arr l.pos l.ghost pos_val' bs' s));
   AT.return ()

let initialize_log' (len:U32.t) (a:EP.larray U8.t len)
  : Steel log
    (A.varray a)
    (fun l -> log_with_parsed_prefix l empty_log)
    (requires fun _ ->
      A.length a == U32.v len)
    (ensures fun _ l _ ->
      log_len l == len /\
      log_array l == a)
  = let pos = R.alloc_pt 0ul in
    let ghost = R.ghost_alloc_pt (Ghost.hide Seq.empty) in
    let contents = intro_varray_pts_to_u8 a in
    parsed_raw_until_empty len 0ul contents;
    AT.intro_pure (parsed_raw_until #(U32.v len) 0ul contents (Ghost.hide Seq.empty));
    let log = {
      len = len;
      arr = a;
      pos = pos;
      ghost = ghost
    } in
    AT.slassert (log_with_parsed_prefix_raw len a pos ghost 0ul contents (Ghost.hide Seq.empty));
    let s : squash (log.len == len) = () in
    intro_log_with_parsed_prefix log len a pos ghost 0ul contents (Ghost.hide Seq.empty) s;
    AT.return log

let initialize_log len a = initialize_log' len a

let parsed_log (l:log) (s:repr) : vprop =
   R.ghost_pts_to l.ghost Perm.full_perm s

let parsed_log_inv l s =
  let open AT in
  (exists (bs:bytes_repr (U32.v l.len)). parsed bs s) /\
  (exists (i:iname). i >--> parsed_log l s)

#push-options "--query_stats"
#push-options "--ide_id_info_off"
let elim_log_with_parsed_prefix
     (l:log)
     (s  : repr)
 : SteelT (Ghost.erased (EP.bounded_u32 (U32.v l.len)) &
           bytes_repr (U32.v l.len))
   (log_with_parsed_prefix l s)
   (fun r -> log_with_parsed_prefix_raw l.len l.arr l.pos l.ghost (fst r) (snd r) s)
 = let p =
       AT.witness_exists
         #_ #_
         #(fun (p:EP.bounded_u32 (U32.v l.len)) ->
           AT.h_exists (fun bs -> log_with_parsed_prefix_raw l.len l.arr l.pos l.ghost p bs s))
         ()
   in
   let bs = AT.witness_exists #_ #_
     #(fun bs -> log_with_parsed_prefix_raw l.len l.arr l.pos l.ghost p bs s)
     ()
   in
   AT.return (p, Ghost.reveal bs)

[@@__reduce__; __steel_reduce__]
let log_inv (l:log) (p: EP.bounded_u32 (U32.v l.len)) (bs: bytes_repr (U32.v l.len)) (s:repr) =
    log_with_parsed_prefix_raw l.len l.arr l.pos l.ghost p bs s


(* Unconditionally drop the log and ghost state and
   return permission to the underlying array *)
val free (#s:repr)
         (l:log)
         (#p:Ghost.erased (EP.bounded_u32 (U32.v l.len)))
         (#bs: bytes_repr (U32.v l.len))
         (_:unit)
  : SteelT unit
    (log_inv l p bs s)
    (fun _ -> A.varray (log_array l))
let free #s l #p #bs _ =
  AT.elim_pure _;
  R.ghost_free_pt l.ghost;
  R.free_pt l.pos;
  elim_varray_pts_to_u8 l.arr _

let intro_read_next_provides_failed
    (s:repr)
    (r:read_result)
    (l:log)
  : Steel unit
    (A.varray (log_array l))
    (fun _ -> read_next_provides s l r)
    (requires fun _ -> Failed? r)
    (ensures fun _ _ _ -> True)
  = AT.change_equal_slprop (A.varray (log_array l))
                           (read_next_provides s l r);
    AT.return ()

val fail (#s:repr)
         (l:log)
         (#p:Ghost.erased (EP.bounded_u32 (U32.v l.len)))
         (#bs: bytes_repr (U32.v l.len))
         (pos:U32.t)
  : Steel read_result
    (log_inv l p bs s)
    (fun r -> read_next_provides s l r)
    (requires fun _ -> U32.v pos <= U32.v l.len)
    (ensures fun _ r _ -> Failed? r /\ Failed?.pos r == pos)
let fail #s l #p #bs pos
  = free l ();
    let res = Failed pos "" in
    intro_read_next_provides_failed s res l;
    AT.return res

let read_pt (#a:Type) (#p:Perm.perm) (#v:Ghost.erased a) (r:R.ref a)
  : Steel a (R.pts_to r p v) (fun x -> R.pts_to r p v)
           (requires fun _ -> True)
           (ensures fun _ x _ -> x == Ghost.reveal v)
  = let x = R.read_pt r in
    assert_spinoff (R.pts_to r p (Ghost.hide x) ==
                    R.pts_to r p v);
    AT.change_equal_slprop (R.pts_to r p (Ghost.hide x))
                           (R.pts_to r p v);
    AT.return x

let extract_log_entry_from (len: U32.t)
                           (buf: EP.larray U8.t len)
                           (#bs: bytes_repr (U32.v len))
                           (p: EP.bounded_u32 (U32.v len))
  : Steel (either (T.vlog_entry & EP.bounded_u32 (U32.v len))
                  (EP.bounded_u32 (U32.v len) & string))
    (varray_pts_to_u8 buf bs)
    (fun _ -> varray_pts_to_u8 buf bs)
    (requires fun _ -> True)
    (ensures fun h0 x h1 ->
      (match x with
       | Inl (e, p') ->
         EP.valid_entry bs (U32.v p) (U32.v p') e
       | Inr (p', _) ->
         True))
  = elim_varray_pts_to_u8 buf _;
    let res = EP.extract_log_entry_from len buf p in
    let bs' = intro_varray_pts_to_u8 buf in
    AT.change_equal_slprop (varray_pts_to_u8 buf bs')
                           (varray_pts_to_u8 buf bs);
    AT.return res

let st_extend_parsed_raw_util
      (#len:nat) #o
      (pos:EP.bounded_u32 len)
      (s:bytes_repr len)
      (r:repr)
      (pos':EP.bounded_u32 len)
      (e:T.vlog_entry)
  : AT.SteelGhost unit o
     (pure (parsed_raw_until pos s r))
     (fun _ -> pure (parsed_raw_until pos' s (snoc_log r e)))
     (requires fun _ ->
       EP.valid_entry s (U32.v pos) (U32.v pos') e)
     (ensures fun _ _ _ -> True)
  = AT.elim_pure _;
    extend_parsed_raw_util pos s r pos' e;
    AT.intro_pure _

let parsed_array s l (h1:rmem (read_next_provides s l Finished)) =
  parsed (A.asel l.arr h1) s

let coerce_rmem p q (h:rmem p) (_:squash (p==q)) : rmem q = h
let read_next_ensures s l (o:read_result) (h1:rmem (read_next_provides s l o)) =
    match o with
    | Finished ->
      //The entries we parsed is stable and fixed to s
      parsed_log_inv l s /\
      //and s is the parse of the contents of the array in state h1
      parsed_array s l (coerce_rmem _ _ h1 ())
    | Parsed_with_maybe_more e -> True
    | Failed pos _ -> U32.(pos <^ log_len l) == true

let intro_read_next_provides_success #s (l:log) (e:T.vlog_entry)
  : Steel read_result
    (log_with_parsed_prefix l (snoc_log s e))
    (fun res -> read_next_provides s l res)
    (requires fun _ -> True)
    (ensures fun _ o h -> read_next_ensures s l o h)
  = let res = Parsed_with_maybe_more e in
    AT.change_equal_slprop (log_with_parsed_prefix l (snoc_log s e))
                           (read_next_provides s l res);
    AT.return res

let read_next_maybe_more (#s:repr)
                         (l:log)
                         (#p:Ghost.erased (EP.bounded_u32 (U32.v l.len)))
                         (#bs:Ghost.erased _)
                         (pos:EP.bounded_u32 (U32.v l.len))
  : Steel read_result
    (log_inv l p bs s)
    (read_next_provides s l)
    (requires fun _ -> pos == Ghost.reveal p /\ U32.v pos < U32.v l.len)
    (ensures fun _ o h1 -> read_next_ensures s l o h1)
  = let h = AT.get () in
    assert (U32.v pos < U32.v l.len);
    let eopt = extract_log_entry_from l.len l.arr pos in
    match eopt with
    | Inr (p, _) ->
      let r = fail l pos in
      AT.return r
    | Inl (e, p') ->
      st_extend_parsed_raw_util p _ s p' e;
      R.ghost_write_pt l.ghost (snoc_log s e);
      R.write_pt l.pos p';
      intro_log_with_parsed_prefix l _ _ _ _ _ _ _ ();
      intro_read_next_provides_success l e

val intro_read_next_provides_finished (#s:_) (l:log)
  : Steel read_result
    (A.varray l.arr)
    (fun res -> read_next_provides s l res)
    (requires fun h0 ->
      parsed (A.asel l.arr h0) s /\
      parsed_log_inv l s)
    (ensures fun _ o h ->
      read_next_ensures s l o h)
let intro_read_next_provides_finished #s l
  = let h0 = AT.get () in
    AT.change_equal_slprop (A.varray l.arr)
                           (read_next_provides s l Finished);
    let h1 = AT.get () in
    assert (parsed_array s l h1);
    assert_spinoff (read_next_ensures s l Finished h1);
    AT.return Finished

let read_next_finished (#s:repr)
                       (l:log)
                       (#p:Ghost.erased (EP.bounded_u32 (U32.v l.len)))
                       (#bs:Ghost.erased _)
                       (pos:EP.bounded_u32 (U32.v l.len))
  : Steel read_result
    (log_inv l p bs s)
    (read_next_provides s l)
    (requires fun _ -> pos == Ghost.reveal p /\ pos == l.len)
    (ensures fun _ o h1 -> read_next_ensures s l o h1)
  =   AT.elim_pure (parsed_raw_until #(U32.v l.len) p bs s);
      parsed_raw_until_full pos bs s;
      assert (parsed bs s);
      let i = AT.new_invariant (parsed_log l s) in
      assert (parsed_log_inv l s);
      elim_varray_pts_to_u8 l.arr _;
      let h = AT.get () in
      assert (parsed (A.asel l.arr h) s);
      let res = Finished in
      R.free_pt l.pos;
      intro_read_next_provides_finished l

val read_next' (#s:repr) (l:log)
  : Steel read_result
    (log_with_parsed_prefix l s)
    (read_next_provides s l)
    (requires fun _ -> True)
    (ensures fun _ o h1 -> read_next_ensures s l o h1)
let read_next' #s l
  = let h = AT.get () in
    let pbs = elim_log_with_parsed_prefix l s in
    let pos = read_pt l.pos in
    if pos = l.len
    then (
      let x = read_next_finished l pos in
      AT.return x
    )
    else (
      let x = read_next_maybe_more l pos in
      AT.return x
    )

let read_next #s l = read_next' #s l

let dispose #s l =
  let h = AT.get () in
  let pbs = elim_log_with_parsed_prefix l s in
  free l ()
