module Zeta.Steel.Util
open Steel.ST.Util
open Steel.ST.CancellableSpinLock
module G = FStar.Ghost
module A = Steel.ST.Array
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Cast = FStar.Int.Cast
let coerce_eq (#a:Type) (#b:Type) (_:squash (a == b)) (x:a) : b = x

let full = Steel.FractionalPermission.full_perm
let half = Steel.FractionalPermission.half_perm full
let larray t (n:U32.t) = A.larray t (U32.v n)
[@@__steel_reduce__;__reduce__]
let array_pts_to #t (a:A.array t) (v:Seq.seq t) = A.pts_to a full_perm v

let sum_halves : squash (sum_perm half half == full) = ()

[@@warn_on_use "uses an axiom"]
assume
val admit__ (#a:Type)
            (#p:pre_t)
            (#q:a -> vprop)
            (_:unit)
  : STF a p q True (fun _ -> False)

[@@warn_on_use "uses an axiom"]
assume
val admit___ (#opened:_)
             (#a:Type)
             (#p:pre_t)
             (#q:a -> vprop)
             (_:unit)
  : STAtomicF a opened p q True (fun _ -> False)

let cancellable_lock (v:vprop) = cancellable_lock v

let can_release (#v:vprop) (c:cancellable_lock v) = can_release c

let new_cancellable_lock (v:vprop)
  : STT (cancellable_lock v) v (fun _ -> emp)
  = new_cancellable_lock v

let maybe_acquired (b:bool) (#v:vprop) (c:cancellable_lock v)
  = maybe_acquired b c

let acquire (#v:vprop) (c:cancellable_lock v)
  : STT bool emp (fun b -> maybe_acquired b c)
  = acquire c

let release (#v:vprop) (c:cancellable_lock v)
  : STT unit (v `star` can_release c) (fun _ -> emp)
  = release c

let cancel (#v:vprop) (c:cancellable_lock v)
  : STT unit (can_release c) (fun _ -> emp)
  = cancel c

let check_overflow_add32 (x y:U32.t)
  : Pure (option U32.t)
    (requires True)
    (ensures fun res ->
        if FStar.UInt.fits (U32.v x + U32.v y) 32
        then Some? res /\
             Some?.v res == U32.add x y
        else None? res)
 = let open U64 in
   let res = U64.(Cast.uint32_to_uint64 x +^
                  Cast.uint32_to_uint64 y)
   in
   if res >^ 0xffffffffuL
   then None
   else (assert (U64.v res  == U32.v x + U32.v y);
         assert (U64.v res <= pow2 32);
         let res = Cast.uint64_to_uint32 res in
         assert (U32.v res  == U32.v x + U32.v y);
         Some res)


let check_overflow_add (x y:U64.t)
  : res:option U64.t {
        if FStar.UInt.fits (U64.v x + U64.v y) 64
        then Some? res /\
             Some?.v res == U64.add x y
        else None? res
    }
 = let open U64 in
   let res = U64.add_mod x y in
   if res <^ x then None
   else if res -^ x = y then Some res
   else None


let st_check_overflow_add32 (x y:U32.t)
  : ST (option U32.t)
       emp
       (fun _ -> emp)
       (requires True)
       (ensures fun res ->
         if FStar.UInt.fits (U32.v x + U32.v y) 32
         then Some? res /\
              Some?.v res == U32.add x y
         else None? res)
  = let r = check_overflow_add32 x y in return r

let update_if (b:bool) (default_ upd_: 'a)
  : 'a
  = if b then upd_ else default_


module R = Steel.ST.Reference
module Loops = Steel.ST.Loops
let repeat_until (p: bool -> vprop)
                 ($body: (unit -> STT bool (p true) (fun b -> p b)))
  : STT unit (p true) (fun _ -> p false)
  = let r = R.alloc true in
    let inv : bool -> vprop = fun b -> R.pts_to r full b `star` p b in
    let cond (_:unit)
      : STT bool (exists_ inv)
                 inv
      = let _b = elim_exists () in
        rewrite (inv _b)
                (R.pts_to r full _b `star` p _b);
        let b = R.read r in
        rewrite (R.pts_to r full _b `star` p _b)
                (inv b);
        return b
    in
    let body (_:unit)
      : STT unit
        (inv true)
        (fun _ -> exists_ inv)
      = rewrite (inv true)
                (R.pts_to r full true `star` p true);
        let b = body () in
        R.write r b;
        rewrite (R.pts_to r full b `star` p b)
                (inv b);
        intro_exists b inv
    in
    rewrite (R.pts_to r full true `star` p true)
            (inv true);
    intro_exists true inv;
    Steel.ST.Loops.while_loop inv cond body;
    rewrite (inv false)
            (R.pts_to r full false `star` p false);
    R.free r

(***** Utility for creating an array literal *****)

private
let array_literal_invariant_pure
  (#a:Type0)
  (n:U32.t)
  (f:(i:U32.t{U32.v i < U32.v n} -> a))
  (i:Loops.nat_at_most n)
  (s:Seq.seq a)
  : prop
  = forall (j:nat). (j < i /\ j < Seq.length s) ==> Seq.index s j == f (U32.uint_to_t j)

[@@ __reduce__]
private
let array_literal_invariant
  (#a:Type0)
  (n:U32.t)
  (arr:A.array a)
  (f:(i:U32.t{U32.v i < U32.v n} -> a))
  (i:Loops.nat_at_most n)
  : Seq.seq a -> vprop
  = fun s ->
    A.pts_to arr full_perm s
      `star`
    pure (array_literal_invariant_pure n f i s)

inline_for_extraction
let array_literal_loop_body
  (#a:Type0)
  (n:U32.t)
  (arr:A.array a{A.length arr == U32.v n})
  (f:(i:U32.t{U32.v i < U32.v n} -> a))
  : i:Loops.u32_between 0ul n ->
    STT unit (exists_ (array_literal_invariant n arr f (U32.v i)))
             (fun _ -> exists_ (array_literal_invariant n arr f (U32.v i + 1)))
  = fun i ->
    let s = elim_exists () in
    A.pts_to_length arr s;
    elim_pure (array_literal_invariant_pure n f (U32.v i) s);
    A.write arr i (f i);
    intro_pure
      (array_literal_invariant_pure n f (U32.v i + 1) (Seq.upd s (U32.v i) (f i)));
    intro_exists
      (Seq.upd s (U32.v i) (f i))
      (array_literal_invariant n arr f (U32.v i + 1))

let array_literal
  (#a:Type0)
  (n:U32.t)
  (f:(i:U32.t{U32.v i < U32.v n} -> a))
  : ST
    (A.array a)
    emp
    (fun arr -> A.pts_to arr full_perm (Seq.init (U32.v n) (fun i -> f (U32.uint_to_t i))))
    (requires U32.v n > 0)
    (ensures fun arr -> A.length arr == U32.v n)
  = let arr = A.alloc (f 0ul) n in
    intro_pure (array_literal_invariant_pure n f 1 (Seq.create (U32.v n) (f 0ul)));
    intro_exists (Seq.create (U32.v n) (f 0ul)) (array_literal_invariant n arr f 1);
    Loops.for_loop
      1ul
      n
      (fun i -> exists_ (array_literal_invariant n arr f i))
      (array_literal_loop_body n arr f);
    let s = elim_exists () in
    A.pts_to_length arr s;
    elim_pure (array_literal_invariant_pure n f (U32.v n) s);
    assert (Seq.equal s (Seq.init (U32.v n) (fun i -> f (U32.uint_to_t i))));
    rewrite (A.pts_to arr full_perm s) _;
    return arr

(***** End ******)

(***** Checking a predicate on array elements *****)

let check_forall_pure
  (#a:Type0)
  (n:U32.t)
  (p:a -> bool)
  (s:Seq.seq a)
  (_:squash (Seq.length s == U32.v n))
  (i:U32.t)
  : prop
  = i `U32.lte` n /\ (forall (j:nat). j < U32.v i ==> p (Seq.index s j))

let check_forall_pure_b
  (#a:Type0)
  (n:U32.t)
  (p:a -> bool)
  (s:Seq.seq a)
  (_:squash (Seq.length s == U32.v n))
  (i:U32.t)
  (b:bool)
  : prop
  = b == (i `U32.lt` n && p (Seq.index s (U32.v i)))

[@@ __reduce__]
let check_forall_pred
  (#a:Type0)
  (n:U32.t)
  (arr:A.array a)
  (p:a -> bool)
  (r:R.ref U32.t)
  (s:Seq.seq a)
  (_:squash (Seq.length s == U32.v n))
  (b:bool)
  : U32.t -> vprop
  = fun i ->
    A.pts_to arr full_perm s
      `star`
    R.pts_to r full_perm i
      `star`
    pure (check_forall_pure n p s () i)
      `star`
    pure (check_forall_pure_b n p s () i b)

[@@ __reduce__]
let check_forall_inv
  (#a:Type0)
  (n:U32.t)
  (arr:A.array a)
  (p:a -> bool)
  (r:R.ref U32.t)
  (s:Seq.seq a)
  (_:squash (Seq.length s == U32.v n))
  : bool -> vprop
  = fun b -> exists_ (check_forall_pred n arr p r s () b)

inline_for_extraction
let check_forall_cond
  (#a:Type0)
  (n:U32.t)
  (arr:A.array a)
  (p:a -> bool)
  (r:R.ref U32.t)
  (s:G.erased (Seq.seq a))
  (_:squash (Seq.length s == U32.v n))
  : unit ->
    STT bool
        (exists_ (check_forall_inv n arr p r s ()))
        (fun b -> check_forall_inv n arr p r s () b)
  = fun _ ->
    let _ = elim_exists () in
    let _ = elim_exists () in
    elim_pure _;
    elim_pure _;

    let i = R.read r in
    let b = i = n in
    let res =
      if b then return false
      else let elt = A.read arr i in
           return (p elt) in

    intro_pure (check_forall_pure n p s () i);
    intro_pure (check_forall_pure_b n p s () i res);
    intro_exists i (check_forall_pred n arr p r s () res);
    return res

inline_for_extraction
let check_forall_body
  (#a:Type0)
  (n:U32.t)
  (arr:A.array a)
  (p:a -> bool)
  (r:R.ref U32.t)
  (s:G.erased (Seq.seq a))
  (_:squash (Seq.length s == U32.v n))
  : unit ->
    STT unit
        (check_forall_inv n arr p r s () true)
        (fun _ -> exists_ (check_forall_inv n arr p r s ()))
  = fun _ ->
    let _ = elim_exists () in
    elim_pure _;
    elim_pure _;

    //atomic increment?
    let i = R.read r in
    R.write r (U32.add i 1ul);

    intro_pure (check_forall_pure n p s () (U32.add i 1ul));
    intro_pure (check_forall_pure_b n p s ()
      (U32.add i 1ul)
      ((U32.add i 1ul) `U32.lt` n && p (Seq.index s (U32.v (U32.add i 1ul)))));
    intro_exists
      (U32.add i 1ul)
      (check_forall_pred n arr p r s ()
         ((U32.add i 1ul) `U32.lt` n && p (Seq.index s (U32.v (U32.add i 1ul)))));
    intro_exists
      ((U32.add i 1ul) `U32.lt` n && p (Seq.index s (U32.v (U32.add i 1ul))))
      (check_forall_inv n arr p r s ())

let check_array_forall
  (#a:Type0)
  (#s:G.erased (Seq.seq a))
  (n:U32.t)
  (arr:A.array a)
  (p:a -> bool)
  : ST bool
       (A.pts_to arr full_perm s)
       (fun _ -> A.pts_to arr full_perm s)
       (requires A.length arr == U32.v n)
       (ensures fun b -> b <==> (forall (i:nat). i < Seq.length s ==>
                                      p (Seq.index s i)))
  = A.pts_to_length arr s;
   
    let b = n = 0ul in
    if b returns ST bool
                    _
                    (fun _ -> A.pts_to arr full_perm s)
                    (requires A.length arr == U32.v n)
                    (ensures fun b -> b <==> (forall (i:nat). i < Seq.length s ==>
                                                   p (Seq.index s i)))
    then return true
    else begin
      //This could be stack allocated
      let r = R.alloc 0ul in

      intro_pure (check_forall_pure n p s () 0ul);
      intro_pure (check_forall_pure_b n p s () 0ul
        (0ul `U32.lt` n && p (Seq.index s (U32.v 0ul))));
      intro_exists 0ul
        (check_forall_pred n arr p r s ()
           (0ul `U32.lt` n && p (Seq.index s (U32.v 0ul))));
      intro_exists
        (0ul `U32.lt` n && p (Seq.index s (U32.v 0ul)))
        (check_forall_inv n arr p r s ());

      Loops.while_loop
        (check_forall_inv n arr p r s ())
        (check_forall_cond n arr p r s ())
        (check_forall_body n arr p r s ());

      let _ = elim_exists () in
      let _ = elim_pure _ in
      let _ = elim_pure _ in

      let i = R.read r in

      //This free would go away if we had stack allocations
      R.free r;

      return (i = n)
    end

(***** End *****)
