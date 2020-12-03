module LayeredEffect

open FStar.Integers

module HS = FStar.HyperStack
open FStar.HyperStack.ST

module B = LowStar.Buffer

type u8 = uint_8
type u32 = uint_32


/// A Low* st type, containing two buffers and their lengths
///
/// Disjointness of the buffers is part of the type itself

noeq
type st = {
  len1 : u32;
  b1   : B.lbuffer u8 (v len1);
  len2 : u32;
  b2   : B.lbuffer u8 (v len2);
  inv  : squash (B.(loc_disjoint (loc_buffer b1) (loc_buffer b2)))
}


/// The spec level counterpart of the st type, containing pure sequences

type sst = {
  n1 : nat;
  s1 : Seq.lseq u8 n1;
  n2 : nat;
  s2 : Seq.lseq u8 n2
}


/// Begin the effect definition


/// Pre- and postconditions are sst predicates

type req_t = sst -> Type0
type ens_t (a:Type) = sst -> a -> sst -> Type0


/// Spec-level view of the st type in a memory

let sst_of_st (s:st) (m:HS.mem) : GTot sst = {
  n1 = v s.len1;
  s1 = B.as_seq m s.b1;
  n2 = v s.len2;
  s2 = B.as_seq m s.b2;
}


/// Representation of the layered effect
///
/// equal_domains in the postcondition forbids heap allocations
/// Computations in the effect only modify the st state

type repr (a:Type) (req:req_t) (ens:ens_t a) =
  s:st -> ST a
  (fun m ->
    B.live m s.b1 /\
    B.live m s.b2 /\
    req (sst_of_st s m))
  (fun m0 x m1 ->
    B.live m1 s.b1 /\
    B.live m1 s.b2 /\
    equal_domains m0 m1 /\
    B.(modifies (loc_union (loc_buffer s.b1) (loc_buffer s.b2)) m0 m1) /\
    ens (sst_of_st s m0) x (sst_of_st s m1))


/// Effect combinators


let return (a:Type) (x:a)
: repr a (fun _ -> True) (fun s0 y s1 -> y == x /\ s0 == s1)
= fun _ -> x


unfold
let bind_req (#a:Type) (req_f:req_t) (ens_f:ens_t a) (req_g:a -> req_t)
: req_t
= fun s0 -> req_f s0 /\ (forall (x:a) (s1:sst). ens_f s0 x s1 ==> req_g x s1)

unfold
let bind_ens (#a:Type) (#b:Type) (req_f:req_t) (ens_f:ens_t a) (ens_g:(x:a -> ens_t b))
: ens_t b
= fun s0 y s2 -> req_f s0 /\ (exists (x:a) (s1:sst). ens_f s0 x s1 /\ (ens_g x) s1 y s2)

let bind (a:Type) (b:Type)
  (req_f:req_t) (ens_f:ens_t a)
  (req_g:a -> req_t) (ens_g:(x:a -> ens_t b))
  (f:repr a req_f ens_f) (g:(x:a -> repr b (req_g x) (ens_g x)))
: repr b
    (bind_req req_f ens_f req_g)
    (bind_ens req_f ens_f ens_g)
= fun s ->
  let x = f s in
  (g x) s


let subcomp (a:Type)
  (req_f:req_t) (ens_f:ens_t a)
  (req_g:req_t) (ens_g:ens_t a)
  (f:repr a req_f ens_f)
: Pure (repr a req_g ens_g)
  (requires
    (forall (s:sst). req_g s ==> req_f s) /\
    (forall (s0:sst) (x:a) (s1:sst). (req_g s0 /\ ens_f s0 x s1) ==> ens_g s0 x s1))
  (ensures fun _ -> True)
= f


let if_then_else (a:Type)
  (req_then:req_t) (ens_then:ens_t a)
  (req_else:req_t) (ens_else:ens_t a)
  (f:repr a req_then ens_then) (g:repr a req_else ens_else)
  (p:Type0)
: Type
= repr a
    (fun s -> (p ==> req_then s) /\ ((~ p) ==> req_else s))
    (fun s0 x s1 -> (p ==> ens_then s0 x s1) /\ ((~ p) ==> ens_else s0 x s1))


reifiable reflectable
layered_effect {
  MSTATE : a:Type -> req_t -> ens_t a -> Effect
  with
  repr = repr;
  return = return;
  bind = bind;
  subcomp = subcomp;
  if_then_else = if_then_else
}


/// An abbreviation that allows assuming req for the well-formedness of ens

effect MST (a:Type) (req:req_t) (ens:(s:sst{req s} -> a -> sst -> Type0)) =
  MSTATE a req (fun st0 x st1 -> req st0 /\ ens st0 x st1)


/// Lift from PURE

let lift_pure_mst (a:Type) (wp:pure_wp a) (f:unit -> PURE a wp)
: repr a (fun _ -> as_requires wp) (fun s0 x s1 -> s0 == s1 /\ (as_ensures wp) x)
= FStar.Monotonic.Pure.wp_monotonic_pure ();
  fun _ -> f ()

sub_effect PURE ~> MSTATE = lift_pure_mst



/// Helper functions for writing postconditions

let with_s1 (st:sst) (s:Seq.lseq u8 st.n1) = { st with s1 = s }
let with_s2 (st:sst) (s:Seq.lseq u8 st.n2) = { st with s2 = s }


/// Effect actions for reading and writing

let read_b1 (i:u32)
: MST u8
  (fun st -> v i < st.n1)
  (fun st0 x st1 -> x == Seq.index st0.s1 (v i) /\ st0 == st1)
= MST?.reflect (fun st -> B.index st.b1 i)

let read_b2 (i:u32)
: MST u8
  (fun st -> v i < st.n2)
  (fun st0 x st1 -> x == Seq.index st0.s2 (v i) /\ st0 == st1)
= MST?.reflect (fun st -> B.index st.b2 i)

// f x y -- x `f` y

let write_b1 (i:u32) (x:u8)
: MST unit
  (fun st -> v i < st.n1)
  (fun st0 _ st1 -> st1 == st0 `with_s1` Seq.upd st0.s1 (v i) x)
= MST?.reflect (fun st -> B.upd st.b1 i x)

let write_b2 (i:u32) (x:u8)
: MST unit
  (fun st -> v i < st.n2)
  (fun st0 _ st1 -> st1 == st0 `with_s2` Seq.upd st0.s2 (v i) x)
= MST?.reflect (fun st -> B.upd st.b2 i x)


/// A swap example

let swap (i j:u32)
: MST unit
  (fun st -> v i < st.n1 /\ v i < st.n2 /\ v j < st.n1 /\ v j < st.n2)
  (fun st0 _ st1 ->
    st1 == st0 `with_s1` Seq.upd st0.s1 (v i) (Seq.index st0.s2 (v j))
               `with_s2` Seq.upd st0.s2 (v j) (Seq.index st0.s1 (v i)))
= let x1 = read_b1 i in
  let x2 = read_b2 j in
  write_b2 j x1;
  write_b1 i x2



// assume val s : Type

// type m (a:Type) = s -> (a * s)

// let return (x:'a) : m 'a = fun s -> x, s

// let bind (f:m 'a) (g:'a -> m 'b) : m 'b = 
//   fun s ->
//   let x, s1 = f s in
//   (g x) s1

// let get () : m s = ...

// let put (st:s) : m unit = ...

// bind f (fun x -> bind g (fun y -> ...))

// Haskell:

// do x <- f;
//    y <- g;
//    ...

// FStar:

// let x = f in
// let y = g in
// ...


// bind f (bind g h) =equiv= bind (bind f g) h

// bind (return x) f =equiv= f x

// bind f (fun x -> return x) =equiv= f
