module LowStar.Exception

open FStar.HyperStack
open FStar.HyperStack.ST

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

assume PURE_WP_monotonic:
  forall (a:Type) (wp:pure_wp a).
    (forall p q. (forall x. p x ==> q x) ==>
            (wp p ==> wp q))

assume ST_WP_monotonic:
  forall (a:Type) (wp:st_wp a).
    (forall p q. (forall x m1. p x m1 ==> q x m1) ==>
            (forall m0. wp p m0 ==> wp q m0))

type repr (a:Type) (wp:st_wp a) =
  unit ->
  STATE
    (option a)
    (fun p m0 -> (forall m1. p None m1) /\ (wp (fun x m1 -> p (Some x) m1) m0))

let return (a:Type) (x:a) : repr a (fun p m0 -> p x m0) = fun _ -> Some x

let bind (a:Type) (b:Type)
  (wp_f:st_wp a) (wp_g:a -> st_wp b)
  (f:repr a wp_f) (g:(x:a -> repr b (wp_g x)))
  : repr b (fun p -> wp_f (fun x -> (wp_g x) p))
  = fun _ ->
    let r = f () in
    match r with
    | None -> None
    | Some x -> (g x) ()

let subcomp (a:Type)
  (wp_f:st_wp a) (wp_g:st_wp a)
  (f:repr a wp_f)
  : Pure
      (repr a wp_g)
      (requires forall p m0. wp_g p m0 ==> wp_f p m0)
      (ensures fun _ -> True)
  = f

let if_then_else (a:Type)
  (wp_then:st_wp a) (wp_else:st_wp a)
  (f:repr a wp_then) (g:repr a wp_else)
  (b:bool)
  : Type
  = repr a
      (fun p m0 -> (b ==> wp_then p m0) /\
                ((~ b) ==> wp_else p m0))

reifiable
reflectable
layered_effect {
  STEXN : a:Type -> wp:st_wp a -> Effect
  with
  repr = repr;
  return = return;
  bind = bind;
  subcomp = subcomp;
  if_then_else = if_then_else
}

let lift_div_stexn (a:Type) (wp:pure_wp a) (f:eqtype_as_type unit -> DIV a wp)
  : repr a (fun p m0 -> wp (fun x -> p x m0))
  = fun _ -> Some (f ())

sub_effect DIV ~> STEXN = lift_div_stexn

let raise (#a:Type) (s:string) : STEXN a (fun p m0 -> True) =
  STEXN?.reflect (fun _ -> None)

let test (n:nat) : STEXN nat (fun p m0 -> p (n+1) m0) =
  if n = 0 then raise "error"
  else begin
    assert (n > 0);
    n+1
  end

let test2 (n:nat) : STEXN nat (fun p m0 -> p (n+2) m0) =
  let n = test n in
  test n
