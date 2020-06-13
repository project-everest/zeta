module Veritas.MultiSet

val mset (a:eqtype): Type0

val equal (#a:eqtype) (s1:mset a) (s2:mset a): Tot bool

(* membership: how many copies of x are in multiset s *)
val mem (#a:eqtype) (x:a) (s:mset a): Tot nat

(* empty set *)
val empty (#a:eqtype): Tot (mset a)


