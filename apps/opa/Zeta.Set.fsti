module Zeta.Set

module S = FStar.Seq
module SA = Zeta.SeqAux

val set (a: eqtype) : eqtype

val empty (#a: eqtype) : set a

val contains (#a: _) (s: set a) (e: a)
  : bool

let in_set (#a: eqtype) (e: a) (s: set a)
  = s `contains` e

let subset (#a:_) (s1 s2: set a)
  = forall e. contains s1 e ==> contains s2 e

val extensionality (#a:eqtype) (s1 s2 : set a)
  : Lemma ((s1 `subset` s2 /\ s2 `subset` s1) <==> s1 == s2)

val lemma_equal (#a:_) (s1 s2: set a)
  : Lemma (ensures ((subset s1 s2 /\ subset s2 s1) ==> s1 = s2))

val add_elem (#a: _) (s: set a) (e: a)
  : s': set a {forall e'. contains s' e' <==> (e' = e \/ contains s e')}

val union (#a:_) (s1 s2 : set a)
  : s3 : set a {forall e. (s1 `contains` e \/ s2 `contains` e <==> s3 `contains` e)}

val is_empty (#a: eqtype) (s: set a)
  : b:bool { b <==> s = empty #a }

val empty_contains_nothing (#a:eqtype) (e: a)
  : Lemma (ensures (let emt = empty #a in
		    not (contains emt e)))

val empty_universal_subset (#a: eqtype) (s: set a)
  : Lemma (ensures (empty `subset` s))

val contains_implies_not_empty (#a: eqtype) (s: set a) (e: a)
  : Lemma (ensures (s `contains` e ==> not (is_empty s)))
	  [SMTPat (e `in_set` s)]

val subset_of_empty_empty (#a: eqtype) (s: set a)
  : Lemma (ensures (s `subset` empty ==> is_empty s))

(* convert a sequence with distinct elements into a set *)
val to_set (#a: eqtype) (sq: S.seq a { SA.distinct_elems sq } )
  : s: set a {(forall e. S.mem e sq <==> e `in_set` s) }

val to_set_elim_dup (#a: eqtype) (sq: S.seq a)
    : s: set a { forall e. S.mem e sq <==> e `in_set` s }
