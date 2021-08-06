module Veritas.Intermediate.Thread

open Veritas.BinTree
open Veritas.MultiSetHash
open Veritas.MultiSetHashDomain
open Veritas.Record
open Veritas.SeqAux
open Veritas.Intermediate.Logs
open Veritas.Intermediate.Store
open Veritas.Intermediate.Verify
open Veritas.Intermediate.VerifierConfig

module S = FStar.Seq
module SA = Veritas.SeqAux
module IntV = Veritas.Intermediate.Verify

let thread_id_logS vcfg = thread_id & logS vcfg

let thread_id_of #vcfg (tl: thread_id_logS vcfg): nat = fst tl

let logS_of #vcfg (tl: thread_id_logS vcfg): logS _ = snd tl

let length #vcfg (tl: thread_id_logS vcfg): nat =
  Seq.length (logS_of tl)

let seq_index #vcfg (tl: thread_id_logS vcfg) = (i:nat{i < length tl})

let tl_idx #vcfg (tl: thread_id_logS vcfg) = i:nat{i < length tl}

let index #vcfg (tl: thread_id_logS vcfg) (i:tl_idx tl): logS_entry _ =
  Seq.index (logS_of tl) i

let prefix #vcfg (tl: thread_id_logS vcfg) (i:nat{i <= length tl}): thread_id_logS _ =
  (thread_id_of tl), (SA.prefix (logS_of tl) i)

let init_store vcfg (tid:thread_id): vstore _ =
  let st = empty_store vcfg in
  if tid = 0 then
    madd_to_store_root st 0 (init_value Root)
  else
    st

val lemma_init_store_ismap (vcfg:verifier_config) (tid:thread_id)
  : Lemma (ensures (is_map (init_store vcfg tid)))
          [SMTPat (init_store vcfg tid)]

val lemma_init_store_slot_points_to_is_merkle_points_to (vcfg:verifier_config) (tid:thread_id)
  : Lemma (ensures (slot_points_to_is_merkle_points_to (init_store vcfg tid)))
          [SMTPat (init_store vcfg tid)]

let verify #vcfg (tl:thread_id_logS vcfg): vtls _ =
  let (tid,l) = tl in
  let st = init_store vcfg tid in
  let vs = IntV.init_thread_state tid st in
  IntV.verify vs l

let verifiable #vcfg (tl:thread_id_logS vcfg) =
  IntV.Valid? (verify tl)

let verifiable_log vcfg = tl:thread_id_logS vcfg{verifiable tl}

val verifiable_implies_prefix_verifiable
  (#vcfg:_) (tl:verifiable_log vcfg) (i:nat{i <= length tl}):
  Lemma (ensures (verifiable (prefix tl i)))
        [SMTPat (prefix tl i)]

(* clock after processing the i'th entry *)
let clock #vcfg (tl:verifiable_log vcfg) (i:tl_idx tl): timestamp =
  let vs = verify (prefix tl (i + 1)) in
  Valid?.clock (verify (prefix tl (i + 1)))

(* get the blum add element from an index *)
let blum_add_elem #vcfg (e:logS_entry vcfg {is_blum_add e}):
  ms_hashfn_dom =
  match e with
  | AddB_S s r t j -> MHDom r t j

val blum_add_seq (#vcfg:_) (ep: epoch) (tl: verifiable_log vcfg): S.seq ms_hashfn_dom

val add_seq_map (#vcfg:_) (tl: verifiable_log vcfg) (i: seq_index tl{is_blum_add (index tl i)}):
  (let be = blum_add_elem (index tl i) in
   let ep = epoch_of be in
   let add_seq = blum_add_seq ep tl in

   j: SA.seq_index add_seq {S.index add_seq j = be})

val add_seq_inv_map (#vcfg:_) (ep: epoch) (tl: verifiable_log vcfg) (j: SA.seq_index (blum_add_seq ep tl)):
  (i: seq_index tl {is_blum_add (index tl i) /\
                    blum_add_elem (index tl i) = S.index (blum_add_seq ep tl) j /\
                    epoch_of (blum_add_elem (index tl i)) = ep /\
                    add_seq_map tl i = j})

val lemma_add_seq_inv (#vcfg:_) (tl: verifiable_log vcfg) (i: seq_index tl{is_blum_add (index tl i)}):
  Lemma (ensures (let be = blum_add_elem (index tl i) in
                  let ep = epoch_of be in
                  add_seq_inv_map ep tl (add_seq_map tl i) = i))
        [SMTPat (add_seq_map tl i)]

(* aggregated hash upto current epoch *)
let hadd #vcfg (tl: verifiable_log vcfg) (ep: epoch): ms_hash_value =
  Valid?.hadd (verify tl) ep

(* the verifier state after processing i entries *)
let state_at #vcfg (tl: verifiable_log vcfg) (i:nat{i <= length tl}): st:vtls _{Valid? st} =
  (verify (prefix tl i))

val lemma_state_transition (#vcfg:_)
                           (tl: verifiable_log vcfg)
                           (i: tl_idx tl):
  Lemma (state_at tl (i + 1) ==
         verify_step (state_at tl i) (index tl i))

val lemma_hadd_correct (#vcfg:_) (ep: epoch) (tl: verifiable_log vcfg):
  Lemma (ensures (hadd tl ep = ms_hashfn (blum_add_seq ep tl)))

let blum_evict_elem (#vcfg:_) (tl: verifiable_log vcfg) (i:seq_index tl{is_evict_to_blum (index tl i)}): ms_hashfn_dom =
  let (tid, _) = tl in
  let tli = prefix tl i in
  let tli' = prefix tl (i + 1) in
  let e = index tl i in
  let vs = verify tli in
  IntV.blum_evict_elem vs e tid

val blum_evict_seq (#vcfg:_) (ep: epoch) (tl: verifiable_log vcfg): S.seq ms_hashfn_dom

let hevict #vcfg (tl: verifiable_log vcfg) (ep: epoch): ms_hash_value =
  Valid?.hevict (verify tl) ep

val lemma_hevict_correct (#vcfg:_) (ep: epoch) (tl: verifiable_log vcfg):
  Lemma (hevict tl ep = ms_hashfn (blum_evict_seq ep tl))

val evict_seq_map (#vcfg:_) (tl: verifiable_log vcfg) (i: seq_index tl{is_evict_to_blum (index tl i)}):
  (let be = blum_evict_elem tl i in
   let ep = epoch_of be in
   let evict_seq = blum_evict_seq ep tl in

   j: SA.seq_index (blum_evict_seq ep tl) {S.index evict_seq j = be})

val evict_seq_inv_map (#vcfg:_) (ep: epoch) (tl: verifiable_log vcfg) (j: SA.seq_index (blum_evict_seq ep tl)):
  (i: seq_index tl{is_evict_to_blum (index tl i) /\
                   blum_evict_elem tl i = S.index (blum_evict_seq ep tl) j /\
                   epoch_of (blum_evict_elem tl i) = ep /\
                   evict_seq_map tl i = j})

val lemma_evict_seq_inv (#vcfg:_) (tl: verifiable_log vcfg) (i: seq_index tl{is_evict_to_blum (index tl i)}):
  Lemma (ensures (let be = blum_evict_elem tl i in
                  let ep = epoch_of be in
                  evict_seq_inv_map ep tl (evict_seq_map tl i) = i))
        [SMTPat (evict_seq_map tl i)]

val lemma_blum_evict_elem_prefix (#vcfg:_) (tl: verifiable_log vcfg) (i: nat{i <= length tl})
  (j: nat{j < i && is_evict_to_blum (index tl j)}):
  Lemma (blum_evict_elem tl j = blum_evict_elem (prefix tl i) j)

val lemma_add_clock (#vcfg:_) (tl: verifiable_log vcfg) (i: seq_index tl{is_blum_add (index tl i)}):
  Lemma (timestamp_of (blum_add_elem (index tl i)) `ts_lt`  clock tl i)

val lemma_evict_clock (#vcfg:_) (tl: verifiable_log vcfg) (i: seq_index tl{is_evict_to_blum (index tl i)}):
  Lemma (timestamp_of (blum_evict_elem tl i) = clock tl i)

val lemma_evict_elem_tid (#vcfg:_) (ep: epoch) (tl:verifiable_log vcfg):
  Lemma (all (is_of_thread_id (thread_id_of tl)) (blum_evict_seq ep tl))

val lemma_clock_monotonic (#vcfg:_) (tl: verifiable_log vcfg) (i:seq_index tl) (j:seq_index tl{j >= i}):
  Lemma (clock tl i `ts_leq` clock tl j)

val lemma_evict_elem_unique (#vcfg:_)
  (ep: epoch)
  (tl: verifiable_log vcfg)
  (i1 i2: SA.seq_index (blum_evict_seq ep tl)):
  Lemma (i1 <> i2 ==> S.index (blum_evict_seq ep tl) i1 <> S.index (blum_evict_seq ep tl) i2)

(* Get the maximal prefix of log upto epoch "ep" *)
val prefix_upto_epoch (#vcfg:_) (ep: epoch) (tl: verifiable_log vcfg): verifiable_log vcfg

val lemma_prefix_upto_epoch (#vcfg:_) (ep: epoch) (tl: verifiable_log vcfg):
  Lemma (ensures (let tl' = prefix_upto_epoch ep tl in
                  let tid, l = tl in
                  let tid', l' = tl' in
                  let MkTimestamp ep' _ = Valid?.clock (verify tl') in
                  tid = tid' /\
                  SA.is_prefix l l' /\
                  ep' <= ep /\
                  (length tl' < length tl ==> (let MkTimestamp ep'' _ = clock tl (length tl') in
                                               ep'' > ep))))
        [SMTPat (prefix_upto_epoch ep tl)]
