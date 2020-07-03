module Veritas.SeqOps

open FStar.List.Tot
open FStar.Seq
//open Veritas.SeqAux

(* append a single element to the end of a sequence *)
let append1 (#a:eqtype) (s:seq a) (x:a): s':(seq a){length s' = length s + 1} = 
  Seq.append s (create 1 x)

val interleave (#a:eqtype): seq a -> seq a -> seq a -> Type

(*
(* interleave s s1 s2 indicates s1 is an interleaving of s1 and s2 *)
(* TODO: Can we hide this definition from users? *)
type interleave (#a:eqtype): seq a -> seq a -> seq a -> Type =
  | IntEmpty: interleave #a (empty #a) (empty #a) (empty #a)
  | IntLeft: s: seq a -> s1: seq a 
                      -> s2: seq a 
                      -> prf: interleave s s1 s2 
                      -> x:a 
                      -> interleave (append1 s x) (append1 s1 x) s2
  | IntRight: s: seq a -> s1: seq a 
                       -> s2: seq a 
                       -> prf:interleave s s1 s2 
                       -> x:a
                       -> interleave (append1 s x) s1 (append1 s x)

*)

(* interleaving is commutative *)
val lemma_interleave_comm (#a:eqtype) (s s1 s2: seq a):
  Lemma (requires (interleave s s1 s2))
        (ensures (interleave s s2 s1))

let aux (#a:eqtype) (s s1 s2: seq a) (prf: interleave s s1 s2):
  Lemma (false) = admit()

let lemma_something (#a:eqtype) (s s1: seq a) (s2:seq a{interleave s s1 s2}):
  Lemma (requires (True))
        (ensures (false)) = 
  let s':squash (interleave s s1 s2) = () in 
  FStar.Squash.bind_squash s' (aux s s1 s2) 
  

(* map an index of interleaved sequence to an index of source sequence *)
val interleave_map (#a:eqtype) (s:seq a) (s1 s2: seq a) (prf: interleave s s1 s2) (i:seq_index s):
  Tot (j: (nat*nat){fst j = 0 /\ snd j < length s1 /\ index s i = index s1 (snd j) \/
                  fst j = 1 /\ snd j < length s2 /\ index s i = index s2 (snd j)})

(* map an index of left sequence to its index in the interleaved sequence *)
val interleave_inv_map_left (#a:eqtype) (s s1 s2: seq a) (prf: interleave s s1 s2) (i: seq_index s1):
  Tot (j: seq_index s{index s j = index s1 i /\ interleave_map s s1 s2 prf j = (0,i)})

(* map an index of left sequence to its index in the interleaved sequence *)
val interleave_inv_map_right (#a:eqtype) (s s1 s2: seq a) (prf: interleave s s1 s2) (i: seq_index s2):
  Tot (j: seq_index s{index s j = index s2 i /\ interleave_map s s1 s2 prf j = (1,i)})

val lemma_interleave_map_monotonic_left (#a:eqtype) 
  (s s1 s2: seq a) (prf:interleave s s1 s2) (i1 i2: seq_index s1):
  Lemma (requires (i1 < i2))
        (ensures (interleave_inv_map_left s s1 s2 prf i1 < interleave_inv_map_left s s1 s2 prf i2))

val lemma_interleave_map_monotonic_right (#a:eqtype)
  (s s1 s2: seq a) (prf:interleave s s1 s2) (i1 i2: seq_index s2):
  Lemma (requires (i1 < i2))
        (ensures (interleave_inv_map_right s s1 s2 prf i1 < interleave_inv_map_right s s1 s2 prf i2))

(* generalize interleaving to a list of sequences *)
type interleave_l (#a:eqtype): seq a -> list (seq a) -> Type = 
  | IntNil: interleave_l #a (empty #a) []
  | IntApp: s: seq a -> h: seq a -> ts: seq a -> tl: list (seq a) -> prf1: interleave_l ts tl -> 
            prf2: interleave s h ts -> interleave_l s (h::tl)

module L = FStar.List.Tot

(* interleaving for sequences *)
type interleave_s (#a:eqtype) (#p:pos): seq a -> ss:(seq (seq a)){length ss = p} -> Type = 
  | IntSeq: s:seq a -> l: list (seq a){L.length l = p} -> prf:interleave_l s l -> 
    interleave_s #a #p s (seq_of_list l)

(* projection of a seq obtained by removing some elements *)
type project (#a:eqtype): seq a -> seq a -> Type = 
  | PrjEmpty: project (empty #a) (empty #a)
  | PrjIncl: s:seq a -> s':seq a -> prf:project s s' -> x:a -> project (append1 s x) (append1 s' x)
  | PrjSkip: s:seq a -> s':seq a -> prf:project s s' -> x:a -> project (append1 s x) s'

(* projection and interleaving are isomorphic *)
val lemma_interleave_implies_project (#a:eqtype) (s s1 s2: seq a):
  Lemma (requires (interleave s s1 s2))
        (ensures (project s s1))

val project_to_interleave (#a:eqtype) (s s1: seq a) (prf: project s s1): s2:_ {interleave s s1 s2}



(*
val flat_length (#a:Type) (ss: seq (seq a)): Tot nat


(* append a single element to the i'th seq in a sequence of sequences *)
let append1seq (#a:eqtype)
               (ss: seq (seq a)) 
               (x:a) (i:seq_index ss) =
  let si = index ss i in
  let si' = append1 si x in
  upd ss i si'

(*
 * interleave s [s0 s1 ... sp-1] represents that 
 * s is an interleaving of sequences s0 ... sp-1
 *)
type interleave (#a:eqtype) (#p:pos): seq a -> ss:(seq (seq a)){length ss = p} -> Type =  
  | IntEmpty: interleave #a #p (empty #a) (create p (empty #a))
  | IntAdd: s:seq a -> ss:(seq (seq a)){length ss = p} -> prf: interleave #a #p s ss 
                    -> x:a -> i:nat{i < p} 
                    -> interleave #a #p (append1 s x) (append1seq #a ss x i)     

(* map every element of the interleaved sequence to its source *)
val interleave_map (#a:eqtype) 
                   (#p:pos) 
                   (s:seq a) 
                   (ss: seq (seq a){length ss = p}) 
                   (prf: interleave #a #p s ss)
                   (i:seq_index s): 
  Tot (j:(nat*nat){fst j < p /\ 
            snd j < length (index ss (fst j)) /\
            index (index ss (fst j)) (snd j) = index s i} )

val interleave_inv_map (#a:eqtype)
                       (#p:pos)
                       (s:seq a)
                       (ss: seq (seq a){length ss = p})
                       (prf:interleave #a #p s ss)
                       (j:(nat*nat){fst j < p /\ 
                                  snd j < length (index ss (fst j))}): 
    Tot (i:(seq_index s){index (index ss (fst j)) (snd j) = index s i})

(* partition a sequence into independent sequences based on a partition function pf *)
val partition (#a:eqtype) (#p:pos) (s:seq a) (pf: a -> (i:nat{i < p})): 
  ss:seq (seq a){length ss = p /\ interleave #a #p s ss}

(* sortedness of a sequence *)
type sorted (#a:eqtype) (lte: a -> a -> bool) (s: seq a)  = 
  forall (i:seq_index s). i > 0 ==> index s (i - 1) `lte` index s i

(* type of a sequence of sequences where each individual sequence is sorted *)
type all_sorted (#a:eqtype) (lte: a -> a -> bool) (ss: seq (seq a)) = 
  forall (i: seq_index ss). sorted #a lte (index ss i)

(* merged interleaving of a sequence of sorted sequences *)
val merge_interleave (#a:eqtype) (lte: a -> a -> bool) 
                     (ss: seq (seq a) {all_sorted #a lte ss /\ length ss > 0}):
  s:seq a {interleave #a #(length ss) s ss /\ sorted #a lte s} 
*)

