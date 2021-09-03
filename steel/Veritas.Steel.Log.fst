module Veritas.Steel.Log
module T = Veritas.Formats.Types
module A = Steel.Array
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module EP = Veritas.Formats
module R = Steel.Reference

let bytes_repr (l:nat) = Ghost.erased (Seq.lseq U8.t l)

let rec parsed_raw (s:Seq.seq U8.t) (r: repr)
  : Tot Type
    (decreases (Seq.length s))
  = if Seq.length r = 0 then True
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
  = parsed_raw (Seq.slice s 0 (U32.v pos)) r

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
  = admit()

let parsed s r = parsed_raw s (FStar.Ghost.reveal r)

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

let contents #t (a:A.array t) = A.contents t (A.length a)

assume
val varray_pts_to (#t:_) (a:A.array t) (bs:Ghost.erased (contents a)) : vprop

let raw_log_pts_to (a:A.array U8.t) (bs:bytes_repr (A.length a)) =
  varray_pts_to a bs

module AT = Steel.Effect.Atomic

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
val varray_pts_to_u8 (#len:_)
                     (a:EP.larray U8.t len)
                     (bs:bytes_repr (U32.v len))
  : vprop

assume
val intro_varray_pts_to_u8 (#opened:inames)
                           (#len: U32.t)
                           (arr: EP.larray U8.t len)
  : AT.SteelGhost (bytes_repr (U32.v len)) opened
    (A.varray arr)
    (fun x -> varray_pts_to_u8 arr x `star` emp)
    (requires fun _ -> True)
    (ensures fun h0 x h1 ->
      Ghost.reveal x == A.asel arr h0)

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

let parsed_raw_until_empty (len:_)
                           (pos:EP.bounded_u32 (U32.v len) { pos == 0ul })
                           (s:bytes_repr (U32.v len))
  : Lemma (parsed_raw_until pos s Seq.empty)
  = admit()

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
   pure (U32.v l.len == Seq.length s) `star`
   R.ghost_pts_to l.ghost Perm.full_perm s

let parsed_log_inv l s =
  let open AT in
  (U32.v l.len == Seq.length s) /\
  (exists (i:iname). i >--> parsed_log l s)

#push-options "--query_stats --log_queries"
let dummy () = ()

#restart-solver
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


(* And dispose to unconditionally just drop the log and
   return the underlying array *)
assume
val free (#s:repr)
         (l:log)
         (#p:Ghost.erased (EP.bounded_u32 (U32.v l.len)))
         (#bs: bytes_repr (U32.v l.len))
         (_:unit)
  : SteelT unit
    (log_inv l p bs s)
    (fun _ -> A.varray (log_array l))


let intro_read_next_provides_finished
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
    intro_read_next_provides_finished s res l;
    AT.return res

assume
val read_pt (#a:Type) (#p:Perm.perm) (#v:Ghost.erased a) (r:R.ref a)
  : Steel a (R.pts_to r p v) (fun x -> R.pts_to r p v)
           (requires fun _ -> True)
           (ensures fun _ x _ -> x == Ghost.reveal v)

assume
val extract_log_entry_from (len: U32.t)
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
  = AT.sladmit()

let extend_ghost_log (#s:repr) (g:R.ghost_ref _) (e:T.vlog_entry)
  : SteelT unit
    (R.ghost_pts_to g Perm.full_perm s)
    (fun _ -> R.ghost_pts_to g Perm.full_perm (snoc_log s e))
  = AT.sladmit(); AT.return ()

let read_next_ensures s l (o:read_result) (h1:rmem (read_next_provides s l o)) =
    match o with
    | Finished ->
      //The entries we parsed is stable and fixed to s
      parsed_log_inv l s /\
      //and s is the parse of the contents of the array in state h1
      parsed (array_sel (log_array l) (rmem_coerce h1)) s
    | Parsed_with_maybe_more e -> True
    | Failed pos _ -> U32.(pos <^ log_len l) == true

val read_next' (#s:repr) (l:log)
  : Steel read_result
    (log_with_parsed_prefix l s)
    (read_next_provides s l)
    (requires fun _ -> True)
    (ensures fun _ o h1 -> read_next_ensures s l o h1)
      // match o with
      // | Finished ->
      //   //The entries we parsed is stable and fixed to s
      //   parsed_log_inv l s /\
      //   //and s is the parse of the contents of the array in state h1
      //   parsed (array_sel (log_array l) (rmem_coerce h1)) s
      // | Parsed_with_maybe_more e -> True
      // | Failed pos _ -> U32.(pos <^ log_len l))

let read_next' #s l
  = let h = AT.get () in
    let pbs = elim_log_with_parsed_prefix l s in
    let pos = read_pt l.pos in
    if pos = l.len
    then (
      AT.sladmit();
      AT.return Finished
    )
    else (
      let eopt = extract_log_entry_from l.len l.arr pos in
      match eopt with
      | Inr (p, _) -> let r = fail l pos in AT.return r
      | Inl (e, p') ->
        st_extend_parsed_raw_util (fst pbs) _ s p' e;
        extend_ghost_log l.ghost e;
        R.write_pt l.pos p';
        intro_log_with_parsed_prefix l _ _ _ _ _ _ _ ();
        let res = Parsed_with_maybe_more e in
        AT.change_equal_slprop (log_with_parsed_prefix _ _)
                               (read_next_provides s l res);
        let h = AT.get() in
        assert (read_next_ensures s l res h);
        AT.return res
    )

    // if pos = l.len
    // then (
    // )
