module Zeta.Formats.Lib

val classical_forall_intro_2_requires
      (#a: Type)
      (#b: (a -> Type))
      (#p #q: (x: a -> b x -> GTot Type0))
      ($u: (x: a -> y: b x -> Lemma (requires (p x y)) (ensures (q x y))))
    : Lemma (forall (x: a) (y: b x). p x y ==> q x y)

let classical_forall_intro_2_requires
  #a #b #p #q u
= let phi (x: a) (y: b x) : Lemma
    (p x y ==> q x y)
  = Classical.move_requires (u x) y
  in
  Classical.forall_intro_2 phi

open LowParse.Spec.Base

module P = Zeta.Steel.Parser

// TODO: move to LowParse.Spec.Base
let parser_injective_intro
  (#t: Type)
  (p: bare_parser t)
  (phi:
    (b1: bytes) ->
    (b2: bytes) ->
    Lemma
    (requires (injective_precond p b1 b2))
    (ensures (injective_postcond p b1 b2))
  )
: Lemma
  (injective p)
= classical_forall_intro_2_requires phi

let no_lookahead_intro
  (#t: Type)
  (p: bare_parser t)
  (phi:
    (b1: bytes) ->
    (b2: bytes) ->
    Lemma
    (requires (no_lookahead_on_precond p b1 b2))
    (ensures (no_lookahead_on_postcond p b1 b2))
  )
: Lemma
  (no_lookahead p)
= classical_forall_intro_2_requires phi

unfold
let parser_kind_prop0 (#t: Type) (k: parser_kind) (f: bare_parser t) : GTot Type0 =
  injective f /\
  (Some? k.parser_kind_subkind ==> parser_subkind_prop (Some?.v k.parser_kind_subkind) f) /\
  parses_at_least k.parser_kind_low f /\
  (Some? k.parser_kind_high ==> (parses_at_most (Some?.v k.parser_kind_high) f)) /\
  parser_kind_metadata_prop k f

let bare_parser_of_spec_parser
  (#t: Type)
  (p: P.spec_parser t)
: Tot (bare_parser t)
= fun x -> match p x with
  | None -> None
  | Some (res, consumed) -> Some (res, consumed)

let spec_parser_of_bare_parser
  (#t: Type)
  (p: bare_parser t)
: Tot (P.spec_parser t)
= fun x -> match parse p x with
  | None -> None
  | Some (res, consumed) -> Some (res, consumed)

let parser_intro
  (typ : Type0)
  (spec_parser : P.spec_parser typ)
  (spec_serializer : P.spec_serializer spec_parser)
  (spec_parser_injective : (b1: bytes) -> (b2: bytes) -> Lemma
    (requires (match spec_parser b1, spec_parser b2 with
    | Some (v1, n1), Some (v2, n2) -> v1 == v2
    | _ -> False
    ))
    (ensures (match spec_parser b1, spec_parser b2 with
    | Some (v1, n1), Some (v2, n2) -> (n1 <: nat) == n2 /\ Seq.slice b1 0 n1 == Seq.slice b2 0 n2
    | _ -> True
  )))
  (spec_parser_strong_prefix: (b1: bytes) -> (b2: bytes) -> Lemma
    (requires (
      match spec_parser b1 with
      | Some (_, n1) -> n1 <= Seq.length b2 /\ Seq.slice b1 0 n1 == Seq.slice b2 0 n1
      | _ -> False
    ))
    (ensures (
      match spec_parser b1, spec_parser b2 with
      | Some (v1, _), Some (v2, _) -> v1 == v2
      | _ -> False
  )))
  (lo: nat)
  (hi: nat { lo <= hi })
  (serialized_length : (v:typ) ->
    Lemma (let l = Seq.length (spec_serializer v) in lo <= l /\ l <= hi))
: Lemma
  (parser_kind_prop (strong_parser_kind lo hi None) (bare_parser_of_spec_parser spec_parser))
=
  let parser_bounds (b: bytes) : Lemma
  (match spec_parser b with
  | None -> True
  | Some (_, l) -> lo <= l /\ l <= hi)
= match spec_parser b with
  | None -> ()
  | Some (x, l) ->
    spec_parser_injective b (spec_serializer x);
    serialized_length x
  in
  let spec_parser' = bare_parser_of_spec_parser spec_parser in
  parser_injective_intro spec_parser' (fun b1 b2 -> spec_parser_injective b1 b2);
  no_lookahead_intro spec_parser' (fun b1 b2 ->
    spec_parser_strong_prefix b1 b2;
    spec_parser_injective b1 b2
  );
  Classical.forall_intro parser_bounds;
  assert (parser_kind_prop0 (strong_parser_kind lo hi None) spec_parser');
  LowParse.Spec.Base.parser_kind_prop_equiv (strong_parser_kind lo hi None) spec_parser'

let default_strong_parser_kind : parser_kind = {
  parser_kind_subkind = Some ParserStrong;
  parser_kind_metadata = None;
  parser_kind_low = 0;
  parser_kind_high = None;
}

let parser_intro_default
  (typ : Type0)
  (spec_parser : P.spec_parser typ)
  (spec_parser_injective : (b1: bytes) -> (b2: bytes) -> Lemma
    (requires (match spec_parser b1, spec_parser b2 with
    | Some (v1, n1), Some (v2, n2) -> v1 == v2
    | _ -> False
    ))
    (ensures (match spec_parser b1, spec_parser b2 with
    | Some (v1, n1), Some (v2, n2) -> (n1 <: nat) == n2 /\ Seq.slice b1 0 n1 == Seq.slice b2 0 n2
    | _ -> True
  )))
  (spec_parser_strong_prefix: (b1: bytes) -> (b2: bytes) -> Lemma
    (requires (
      match spec_parser b1 with
      | Some (_, n1) -> n1 <= Seq.length b2 /\ Seq.slice b1 0 n1 == Seq.slice b2 0 n1
      | _ -> False
    ))
    (ensures (
      match spec_parser b1, spec_parser b2 with
      | Some (v1, _), Some (v2, _) -> v1 == v2
      | _ -> False
  )))
: Lemma
  (parser_kind_prop (default_strong_parser_kind) (bare_parser_of_spec_parser spec_parser))
=
  let spec_parser' = bare_parser_of_spec_parser spec_parser in
  parser_injective_intro spec_parser' (fun b1 b2 -> spec_parser_injective b1 b2);
  no_lookahead_intro spec_parser' (fun b1 b2 ->
    spec_parser_strong_prefix b1 b2;
    spec_parser_injective b1 b2
  );
  assert (parser_kind_prop0 (default_strong_parser_kind) spec_parser');
  LowParse.Spec.Base.parser_kind_prop_equiv (default_strong_parser_kind) spec_parser'
