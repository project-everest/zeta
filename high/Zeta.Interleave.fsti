module Zeta.Interleave

open FStar.Seq
open FStar.Squash
open Zeta.SeqAux
open Zeta.SSeq

module S = FStar.Seq
module SA = Zeta.SeqAux

(* interleaving of n sequences *)
type interleave (#a:eqtype): seq a -> ss:sseq a -> Type0 = 
  | IntEmpty: interleave (empty #a) (empty #(seq a))
  | IntAdd: s:seq a -> ss: sseq a -> prf:interleave s ss -> interleave s (append1 ss (empty #a))
  | IntExtend: s:seq a -> ss: sseq a -> prf:interleave s ss -> x:a -> i:seq_index ss ->
               interleave (append1 s x) (sseq_extend ss x i)

(* length of an interleaving is the sum of the lengths of the individual sequences *)
val lemma_interleave_length (#a:eqtype) (s: seq a) (ss: sseq a{interleave s ss}):
  Lemma (length s = flat_length ss)
  [SMTPat (interleave #a s ss)]

(* if we have a proof of interleaving we can construct a mapping from 
 * interleaved sequence to the sources *)
val interleave_map (#a:eqtype) (s: seq a) (ss: sseq a)
     (prf:interleave #a s ss) (i: seq_index s): 
  Tot (j: (sseq_index ss){indexss ss j = index s i})
  
(* inverse of interleave map *)
val interleave_map_inv (#a:eqtype) (s: seq a) (ss: sseq a)
      (prf:interleave #a s ss) (i: sseq_index ss):
  Tot (j: seq_index s{index s j = indexss ss i})

(* 
 * interleaving: a triple that holds interleaved sequence, source sequences, and 
 * proof of interleaving *
 *)
noeq type interleaving (a:eqtype) = 
  | IL: s:seq a -> ss: sseq a -> prf:interleave s ss -> interleaving a

(* interleaved sequence *)
let i_seq (#a:eqtype) (il: interleaving a): seq a = 
  IL?.s il

(* source sequences *)
let s_seq (#a:eqtype) (il: interleaving a): sseq a = 
  IL?.ss il

let lemma_interleaving_correct (#a:eqtype) (il:interleaving a):
  Lemma (interleave (i_seq il) (s_seq il)) = 
  return_squash (IL?.prf il)

let length (#a:eqtype) (il: interleaving a): nat = 
  S.length (i_seq il)

let seq_index (#a:eqtype) (il: interleaving a) = i:nat{i < length il}

let index (#a: eqtype) (il: interleaving a) (i: seq_index il): a =
  (index (i_seq il) i)

let prefix_of (#a:eqtype) (s0 s1:seq a) = SA.is_prefix s1 s0

let sseq_all_prefix_of (#a:eqtype) 
                       (ss0 ss1: sseq a)
  = S.length ss0 = S.length ss1 /\
    (forall (tid:SA.seq_index ss1). (Seq.index ss0 tid) `prefix_of` (Seq.index ss1 tid))

val interleave_empty_n (#a:eqtype) (n:nat) 
  : interleave #a empty (Seq.create n empty)

val interleave_empty (#a:_) (#ss:_) (i:interleave #a Seq.empty ss)
  : Lemma (ensures ss `Seq.equal` Seq.create (Seq.length ss) empty)

val prefix (#a:eqtype) (il: interleaving a) (i:nat{i <= length il}): 
  Tot (il':interleaving a{i_seq il' = SA.prefix (i_seq il) i /\ 
                          S.length (s_seq il) = S.length (s_seq il')})

val per_thread_prefix (#a:eqtype) (il: interleaving a) (i:nat{i <= length il})
  : Lemma (let ss = s_seq il in
           let il' = prefix il i in
           let ss' = s_seq il' in
           ss' `sseq_all_prefix_of` ss)


val i2s_map (#a:eqtype) (il:interleaving a) (i:seq_index il): 
  (si:sseq_index (s_seq il){index il i = indexss (s_seq il) si})

val s2i_map (#a:eqtype) (il:interleaving a) (si: sseq_index (s_seq il)):
  (i:seq_index il{index il i = indexss (s_seq il) si /\
                  i2s_map il i = si})

val lemma_i2s_s2i (#a:eqtype) (il:interleaving a) (i:seq_index il):
  Lemma (requires True)
        (ensures (s2i_map il (i2s_map il i) = i))
        [SMTPat (i2s_map il i)]

val i2s_map_int_add (#a:_) (il:interleaving a)
  : Lemma 
    (ensures (forall (i:seq_index il).{:pattern (i2s_map il i)} i2s_map il i == i2s_map (IL _ _ (IntAdd _ _ (IL?.prf il))) i))

val i2s_map_int_extend (#a:eqtype) (s:seq a) (ss: sseq a) (prf:interleave s ss) (x:a) (i:SA.seq_index ss) (j:nat)
  : Lemma 
    (ensures (let il = IL _ _ (IntExtend _ _ prf x i) in
              if j = length il - 1
              then i2s_map il j == (i, Seq.length (Seq.index ss i))
              else if j < length il - 1
              then i2s_map il j == i2s_map (IL _ _ prf) j
              else True))

let hprefix (#a:eqtype) (il:interleaving a {length il > 0}): interleaving a =
  prefix il (length il - 1)

let telem (#a:eqtype) (il:interleaving a {length il > 0}): a =
  SA.telem (i_seq il)

val prefix_identity (#a:eqtype) (il:interleaving a)
  : Lemma (ensures prefix il (length il) == il)

val prefix_int_add (#a:eqtype) (i:interleaving a { IntAdd? (IL?.prf i) }) (n:nat{n <= length i})
  : Lemma 
    (let IL _ _ (IntAdd _ _ prf) = i in
     prefix i n == 
     IL _ _ (IntAdd _ _ (IL?.prf (prefix (IL _ _ prf) n))))
  
val prefix_int_extend (#a:eqtype) (i:interleaving a { IntExtend? (IL?.prf i) }) (n:nat{n <= length i})
  : Lemma
    (let IL _ _ (IntExtend s ss prf x j) = i in
     (if n <= Seq.length s
      then prefix i n == prefix (IL s ss prf) n
      else prefix i n == i))

val hprefix_extend (#a:eqtype) (s:seq a) (ss:sseq a)
                    (il:interleave s ss)
                    (x:a)
                    (i:SA.seq_index ss)
  : Lemma (hprefix (IL _ _ (IntExtend s ss il x i)) == IL _ _ il)

val lemma_prefix_index (#a:eqtype) (il:interleaving a) (i:nat{i <= length il}) (j:nat{j < i}):
  Lemma (requires True)
        (ensures (index (prefix il i) j = index il j))
        [SMTPat (index (prefix il i) j)]

val lemma_prefix_prefix (#a:eqtype) (il:interleaving a) (i:nat{i <= length il}) (j:nat{j <= i}):
  Lemma (requires (True))
        (ensures (prefix (prefix il i) j == prefix il j))
        [SMTPat (prefix (prefix il i) j)]

val filter_interleaving (#a:eqtype) (f:a -> bool) (#s:seq a) (#ss:sseq a) (i:interleave s ss)
  : interleave (filter f s) (map (filter f) ss)

let filter (#a:eqtype) (f:a -> bool) (il:interleaving a)
  : interleaving a 
  = let IL is ss prf = il in
    IL (filter f is) (map (filter f) ss) (filter_interleaving f prf)

val lemma_i2s_map_prefix (#a:eqtype) (il: interleaving a) (i: nat{i <= length il}) (j:nat{j < i}):
  Lemma (i2s_map il j = i2s_map (prefix il i) j)

(* every component sequence j of a prefix of il is a prefix of the corresponding component sequence of il *)
val lemma_prefix_interleaving (#a:eqtype) 
  (il: interleaving a) 
  (i:nat{ i <= length il}) 
  (j:nat{j < S.length (s_seq il)}):
  Lemma ((S.index (s_seq (prefix il i)) j) `prefix_of` (S.index (s_seq il) j))

val lemma_prefix_snoc (#a:eqtype) (il:interleaving a) (i:seq_index il)
  : Lemma (let tid, j = i2s_map il i in
           let il_i = prefix il i in
           let il_i' = prefix il (i + 1) in
           Seq.index (s_seq il_i') tid == Seq.snoc (Seq.index (s_seq il_i) tid) (index il i) /\
           (forall tid'. tid' <> tid ==> Seq.index (s_seq il_i') tid' `Seq.equal` Seq.index (s_seq il_i) tid'))



val map_interleave (#a #b:eqtype) (f:a -> b) (s:seq a) (ss:sseq a) (i:interleave s ss)
   : Tot (interleave (map f s) (map (map f) ss))
         (decreases i)

val map_interleave_i2s (#a #b:eqtype) (f:a -> b) (prf:interleaving a) (i:seq_index prf)
  : Lemma (ensures (i2s_map prf i == i2s_map (IL _ _ (map_interleave f _ _ (IL?.prf prf))) i))

val filter_map_interleaving (#a #b:eqtype)
                            (filter: a -> bool)
                            (f:(refine filter -> b))
                            (#s:seq a)
                            (#ss:sseq a)
                            (i:interleave s ss)
  : interleave (filter_map filter f s)
               (map (SA.filter_map filter f) ss)

val interleave_step (#a:eqtype) (il:interleaving a { length il > 0 })
  : Lemma 
    (let i = length il - 1 in
     let il' = prefix il i in
     let tid, _ = i2s_map il i in
     let tl' = Seq.index (s_seq il') tid in
     let tl = Seq.index (s_seq il) tid in
     let v = index il i in
     tl `Seq.equal` Seq.snoc tl' v /\
     (forall (tid':SA.seq_index (s_seq il)).
        tid <> tid' ==>
        Seq.index (s_seq il) tid' ==
        Seq.index (s_seq il') tid'))

val lemma_fullprefix_equal (#a:eqtype) (il: interleaving a):
  Lemma (requires True)
        (ensures (prefix il (length il) == il))

val interleave_sseq_index (#a:eqtype) (il:interleaving a) (i:seq_index il)
  : Lemma (
    let il_i = prefix il i in
    let tid, j = i2s_map il i in
    Seq.index (s_seq il_i) tid `Seq.equal`
    SA.prefix (Seq.index (s_seq il) tid) j)

val interleave_sseq_index_next (#a:eqtype) (il:interleaving a) (i:seq_index il)
  : Lemma (ensures  (
    let il_i = prefix il (i + 1) in
    let tid, j = i2s_map il i in
    Seq.index (s_seq il_i) tid `Seq.equal`
    SA.prefix (Seq.index (s_seq il) tid) (j + 1)))

val some_interleaving (#a: eqtype) (ss: sseq a)
  : il: interleaving a {s_seq il = ss}
