module Zeta.SMap

open FStar.Seq
open Zeta.SeqAux

(* A mapping from one sequence to another *)
let smap (#a:_) (s1 s2: seq a) = f:(seq_index s1 -> seq_index s2){
  forall (i: seq_index s1). index s1 i == index s2 (f i)
}

(* injectivity property on smaps *)
let into_prop (#a:Type) (#s1 #s2: seq a) (f:smap s1 s2)
  = forall (i j: seq_index s1). (i <> j) ==> f i <> f j

let into_smap (#a:Type) (s1 s2: seq a) = f:smap s1 s1 {into_prop f}

let monotonic_prop (#a:_) (#s1 #s2:seq a) (f: smap s1 s2)
  = forall (i j: seq_index s1). i < j ==> f i < f j

let mono_smap (#a:_) (s1 s2: seq a) = f:smap s1 s2 {monotonic_prop f}

let monotonic_implies_into (#a:_) (#s1 #s2: seq a) (f: smap s1 s2)
  : Lemma (ensures (monotonic_prop f ==> into_prop f))
  = ()

val monotonic_bijection_implies_equal (#a:_) (s1 s2: seq a)
  (f12: mono_smap s1 s2)
  (f21: mono_smap s2 s1)
  : Lemma (ensures (s1 == s2))
