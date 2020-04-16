module Veritas.MultisetHash

open FStar.Seq

type multiset_incr_hashfn = (elem_dom: Type) -> (hash_dom: Type) -> (h: hash_dom) -> (e: elem_dom ) -> Tot hash_dom


