module Zeta.Generic.Interleave

open FStar.Seq
open Zeta.SeqAux
open Zeta.Time
open Zeta.IdxFn
open Zeta.SIdxFn
open Zeta.GenericVerifier
open Zeta.Generic.Thread
open Zeta.Generic.Global
open Zeta.Interleave

module V = Zeta.GenericVerifier
module T = Zeta.Generic.Thread
module G = Zeta.Generic.Global
module I = Zeta.Interleave
module S = FStar.Seq
module SA = Zeta.SeqAux
module IF = Zeta.IdxFn
module SF = Zeta.SIdxFn

let ilog (vspec: verifier_spec) (n:nat) = interleaving (verifier_log_entry vspec) n

(* valid thread ids of an interleaving *)
let thread_id #vspec #n (il: ilog vspec n) = t:nat{t < n}

(* to sequence of individual thread-level logs *)
let to_glog #vspec #n (il: ilog vspec n): G.vlog _
  = I.s_seq il

let seq_index #vspec #n (il: ilog vspec n) = SA.seq_index il
let length #vspec #n (il: ilog vspec n) = S.length il

(* an interleaving is verifiable is the source logs are verifiable *)
let verifiable #vspec #n (il: ilog vspec n) =
  G.verifiable (to_glog il)

let verifiable_log vspec n = il:ilog vspec n {verifiable il}

val lemma_prefix_verifiable (#vspec:_) (n:_) (il:verifiable_log vspec n) (i:nat{i <= S.length il}):
  Lemma (ensures (verifiable (I.prefix il i)))
        [SMTPat (I.prefix il i)]

let prefix #vspec #n (il: verifiable_log vspec n) (i:nat{i <= S.length il})
  : il': verifiable_log vspec n{S.length il' = i}
  = I.prefix il i

let gen_seq (vspec:verifier_spec) (n:nat) : gen_seq_spec = {
  IF.seq_t = verifiable_log vspec n;
  IF.length = S.length;
  IF.prefix = prefix
}

let idxfn_base #vspec #n #b (tfn: T.idxfn_t vspec b)
  (il: verifiable_log vspec n) (i: seq_index il)
  : b
  = G.idxfn #vspec tfn (to_glog il) (i2s_map il i)

val idxn_has_prefix_prop (#vspec:_) (#n:nat) (#b:_) (tfn: T.idxfn_t vspec b)
  : Lemma (ensures (IF.prefix_property #(gen_seq vspec n) (idxfn_base #_ #n #_ tfn)))
          [SMTPat (idxfn_base #_ #n #_ tfn)]

let idxfn #vspec #n #b (tfn: T.idxfn_t vspec b)
  : IF.idxfn_t (gen_seq vspec n) _
  = idxfn_base tfn

let cond_idxfn_base #vspec #n #b #f (m: T.cond_idxfn_t b f)
  (il: verifiable_log vspec n) (i: seq_index il{idxfn f il i})
  = G.cond_idxfn m (to_glog il) (i2s_map il i)

val cond_idxfn_has_prefix_prop (#vspec #n #b #f:_) (m: T.cond_idxfn_t b f)
  : Lemma (ensures (IF.cond_prefix_property #(gen_seq vspec n) #_ #(idxfn f) (cond_idxfn_base m)))
          [SMTPat (cond_idxfn_base #vspec #n #b #f m)]

let cond_idxfn (#vspec #n #b #f:_) (m: T.cond_idxfn_t b f)
  : IF.cond_idxfn_t b (idxfn f)
  = cond_idxfn_base #vspec #n m

(* the clock value at every index *)
let clock #vspec #n = idxfn #_ #n (T.clock #vspec)
