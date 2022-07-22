module Zeta.Generic.Thread

open Zeta.Time
open Zeta.MultiSetHashDomain
open Zeta.GenericVerifier

module S = FStar.Seq
module SA = Zeta.SeqAux
module MSD = Zeta.MultiSetHashDomain
module GV = Zeta.GenericVerifier

(* a verifier log attached to a thread id *)
let vlog (vspec: verifier_spec) = thread_id & verifier_log vspec

let length #vspec (tl: vlog vspec) =
  let _, l = tl in
  S.length l

let seq_index #vspec (tl: vlog vspec) = i:nat {i < length tl}

let index #vspec (tl: vlog vspec) (i: seq_index tl) =
  let _, l = tl in
  S.index l i

let prefix_base #vspec (tl: vlog vspec) (i: nat {i <= length tl}): vlog _ =
  let tid, l = tl in
  tid, SA.prefix l i

let verify #vspec (tl: vlog vspec): vspec.vtls_t =
  let tid, l = tl in
  Zeta.GenericVerifier.verify tid l

(* the verifier state after processing a log *)
let state #vspec (tl:vlog vspec)
  : vspec.vtls_t
  = verify tl

let state_pre (#vspec: verifier_spec) (tl: vlog vspec) (i: seq_index tl)
  = let tl' = prefix_base tl i in
    state tl'

let state_post (#vspec: verifier_spec) (tl: vlog vspec) (i: seq_index tl)
  = let tl' = prefix_base tl (i+1) in
    state tl'

(* the state after processing i'th entry is obtained by applying the verify
 * step to the state before processing the i'th entry *)
val lemma_state_transition (#vspec:verifier_spec) (tl: vlog vspec) (i: seq_index tl):
  Lemma (ensures (state_post tl i ==
                  verify_step (index tl i) (state_pre tl i)))
        [SMTPat (state_post tl i)]

let verifiable #vspec (tl: vlog vspec) = vspec.valid (verify tl)

let verifiable_log vspec = tl: vlog vspec { verifiable tl }

(* if a thread log is verifiable, its prefix is verifiable *)
val verifiable_implies_prefix_verifiable (#vspec:verifier_spec)
  (tl:verifiable_log vspec) (i:nat{i <= length tl}):
  Lemma (ensures (verifiable (prefix_base tl i)))
        [SMTPat (prefix_base tl i)]

let prefix #vspec (tl: verifiable_log vspec) (i: nat {i <= length tl})
  : tl': verifiable_log _ {length tl' = i}
  = prefix_base tl i

let clock_base (#vspec:_) (tl: verifiable_log vspec): timestamp
  = let vs = state tl in
    vspec.clock vs

let clock (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl)
  = let tl' = prefix tl (i+1) in
    clock_base tl'

let clock_post #vspec = clock #vspec

let clock_pre (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl)
  = let tl' = prefix tl i in
    clock_base tl'

let clock_lek_base (#vspec:_) (tl: verifiable_log vspec)
  = let vs = state tl in
    GV.clock_evict_key vs

let clock_lek_post #vspec (tl: verifiable_log vspec) (i: seq_index tl)
  = let tl' = prefix tl (i+1) in
    clock_lek_base tl'

let clock_lek_pre #vspec (tl: verifiable_log vspec) (i: seq_index tl)
  = let tl' = prefix tl i in
    clock_lek_base tl'

let clock_lek #vspec = clock_lek_post #vspec

(* the epoch of the i'th entry *)
let epoch_of #vspec (tl: verifiable_log vspec) (i: seq_index tl)
  = let t = clock tl i in
    t.e

(* is the i'th entry within epoch ep *)
let is_within_epoch #vspec (ep: epoch)
  (tl: verifiable_log vspec) (i: seq_index tl)
  = epoch_of tl i <= ep

val lemma_clock_lek_monotonic (#vspec: verifier_spec)
  (tl: verifiable_log vspec) (i:nat) (j: seq_index tl {j >= i})
  : Lemma (ensures (clock_lek tl i `Zeta.TimeKey.lte` clock_lek tl j))

(* clock is monotonic *)
val lemma_clock_monotonic (#vspec:verifier_spec)
  (tl: verifiable_log vspec) (i:nat) (j: seq_index tl {j >= i}):
  Lemma (ensures (clock tl i `ts_leq` clock tl j))

(* the thread id in the state is always the one specified in the parameter *)
val lemma_thread_id_state (#vspec:verifier_spec) (tl: verifiable_log vspec):
  Lemma (ensures (let tid, _ = tl in
                  vspec.tid (verify tl) = tid))

let is_blum_add (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl)
  = GV.is_blum_add (index tl i)

let blum_add_elem (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl{is_blum_add tl i})
  : ms_hashfn_dom vspec.app
  = match (index tl i) with
    | AddB r _ t tid ->
      MHDom r t tid

let is_blum_add_ep (#vspec:_) (ep: epoch) (tl: verifiable_log vspec) (i: seq_index tl)
  : bool
  = is_blum_add tl i &&
    (let be = blum_add_elem tl i in be.t.e = ep)

val add_seq (#vspec:_) (ep: epoch) (tl: verifiable_log vspec)
  : S.seq (ms_hashfn_dom vspec.app)

val add_seq_empty (#vspec:_) (ep: epoch) (tl: verifiable_log vspec)
  : Lemma (ensures (length tl = 0 ==> S.length (add_seq ep tl) = 0))

val add_seq_snoc
  (#vspec:_)
  (ep: epoch)
  (tl: verifiable_log vspec {length tl > 0})
  : Lemma (ensures (let i = length tl - 1 in
                    let tl' = prefix tl i in
                    let as' = add_seq ep tl' in
                    let a_s = add_seq ep tl in
                    if is_blum_add_ep ep tl i then
                      a_s == SA.append1 as' (blum_add_elem tl i)
                    else
                      a_s == as'))

val add_seq_map (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl {is_blum_add tl i})
  : (let be = blum_add_elem tl i in
     let ep = be.t.e in
     let a_s = add_seq ep tl in
     j: SA.seq_index a_s { S.index a_s j = be })

val add_seq_invmap (#vspec:_) (ep: epoch) (tl: verifiable_log vspec) (j: SA.seq_index (add_seq ep tl))
  : i:seq_index tl { is_blum_add_ep ep tl i /\ add_seq_map tl i = j  }

val lemma_add_seq_map (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl {is_blum_add tl i})
  : Lemma (ensures (let be = blum_add_elem tl i in
                    let ep = be.t.e in
                    let a_s = add_seq ep tl in
                    let j = add_seq_map tl i in
                    add_seq_invmap ep tl j = i))
          [SMTPat (add_seq_map tl i)]

val add_seq_map_monotonic (#vspec:_) (tl: verifiable_log vspec) (i1 i2: (i:seq_index tl {is_blum_add tl i}))
  : Lemma (requires (let be1 = blum_add_elem tl i1 in
                     let be2 = blum_add_elem tl i2 in
                     be1.t.e = be2.t.e))
          (ensures ((i1 < i2 ==> add_seq_map tl i1 < add_seq_map tl i2) /\
                    (i2 < i1 ==> add_seq_map tl i2 < add_seq_map tl i1)))

val add_seq_invmap_monotonic (#vspec:_) (ep: epoch) (tl: verifiable_log vspec) (j1 j2: SA.seq_index (add_seq ep tl))
  : Lemma (ensures ((j1 < j2 ==> add_seq_invmap ep tl j1 < add_seq_invmap ep tl j2) /\
                    (j2 < j1 ==> add_seq_invmap ep tl j2 < add_seq_invmap ep tl j1)))

let is_blum_evict (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl)
  = GV.is_blum_evict (index tl i)

val blum_evict_elem (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl{is_blum_evict tl i})
  : be:ms_hashfn_dom vspec.app {let e = index tl i in
                                let s = evict_slot e in
                                let vs_pre = state_pre tl i in
                                let open Zeta.MultiSetHashDomain in
                                Some? (vspec.get s vs_pre) /\
                                be.r = Some?.v (vspec.get s vs_pre) /\
                                be.t = blum_evict_timestamp e /\
                                be.tid = fst tl}

let is_blum_evict_ep (#vspec:_) (ep: epoch) (tl: verifiable_log vspec) (i: seq_index tl)
  : bool
  = is_blum_evict tl i &&
    (let be = blum_evict_elem tl i in be.t.e = ep)

val evict_seq (#vspec:_) (ep: epoch) (tl: verifiable_log vspec)
  : S.seq (ms_hashfn_dom vspec.app)

val evict_seq_empty (#vspec:_) (ep: epoch) (tl: verifiable_log vspec)
  : Lemma (ensures (length tl = 0 ==> S.length (evict_seq ep tl) = 0))

val evict_seq_snoc
  (#vspec:_)
  (ep: epoch)
  (tl: verifiable_log vspec {length tl > 0})
  : Lemma (ensures (let i = length tl - 1 in
                    let tl' = prefix tl i in
                    let es' = evict_seq ep tl' in
                    let es = evict_seq ep tl in
                    if is_blum_evict_ep ep tl i then
                      es == SA.append1 es' (blum_evict_elem tl i)
                    else
                      es == es'))

val evict_seq_map (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl {is_blum_evict tl i})
  : (let be = blum_evict_elem tl i in
     let ep = be.t.e in
     let es = evict_seq ep tl in
     j: SA.seq_index es { S.index es j = be })

val evict_seq_invmap (#vspec:_) (ep: epoch) (tl: verifiable_log vspec) (j: SA.seq_index (evict_seq ep tl))
  : i:seq_index tl { is_blum_evict_ep ep tl i /\ evict_seq_map tl i = j  }

val lemma_evict_seq_map (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl {is_blum_evict tl i})
  : Lemma (ensures (let be = blum_evict_elem tl i in
                    let ep = be.t.e in
                    let a_s = evict_seq ep tl in
                    let j = evict_seq_map tl i in
                    evict_seq_invmap ep tl j = i))
          [SMTPat (evict_seq_map tl i)]

val evict_seq_map_monotonic (#vspec:_) (tl: verifiable_log vspec) (i1 i2: (i:seq_index tl {is_blum_evict tl i}))
  : Lemma (requires (let be1 = blum_evict_elem tl i1 in
                     let be2 = blum_evict_elem tl i2 in
                     be1.t.e = be2.t.e))
          (ensures ((i1 < i2 ==> evict_seq_map tl i1 < evict_seq_map tl i2) /\
                    (i2 < i1 ==> evict_seq_map tl i2 < evict_seq_map tl i1)))

val evict_seq_invmap_monotonic (#vspec:_) (ep: epoch) (tl: verifiable_log vspec) (j1 j2: SA.seq_index (evict_seq ep tl))
  : Lemma (ensures ((j1 < j2 ==> evict_seq_invmap ep tl j1 < evict_seq_invmap ep tl j2) /\
                    (j2 < j1 ==> evict_seq_invmap ep tl j2 < evict_seq_invmap ep tl j1)))

val lemma_add_clock (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl{is_blum_add tl i})
  : Lemma (ensures (let be = blum_add_elem tl i in
                    be.t `ts_lt` clock tl i))
          [SMTPat (blum_add_elem tl i)]

val lemma_evict_clock (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl{is_blum_evict tl i})
  : Lemma (ensures (let be = blum_evict_elem tl i in
                    be.t = clock tl i))
          [SMTPat (blum_evict_elem tl i)]

val evict_elem_unique (#vspec:_) (ep: epoch) (tl: verifiable_log vspec) (i1 i2: SA.seq_index (evict_seq ep tl))
  : Lemma (ensures (let es = evict_seq ep tl in
                    i1 <> i2 ==>  S.index es i1 <> S.index es i2))

val evict_elem_tid (#vspec:_) (ep: epoch) (tl: verifiable_log vspec) (i: SA.seq_index (evict_seq ep tl))
  : Lemma (ensures (let es = evict_seq ep tl in
                    let be = S.index es i in
                    let t,_ = tl in
                    be.tid = t))

(* is the i'th entry an app function *)
let is_appfn (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl)
  = GV.is_appfn (index tl i)

open Zeta.AppSimulate

let is_appfn_within_epoch #vspec (ep: epoch) (tl: verifiable_log vspec) (i: seq_index tl)
  = is_appfn tl i && is_within_epoch ep tl i

(* for an appfn entry, return the function call params and result *)
let to_app_fcr (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl{is_appfn tl i})
  : appfn_call_res vspec.app
  = let e = index tl i in
    let st' = state_pre tl i in
    let st = state_post tl i in
    assert(vspec.valid st);
    GV.appfn_result e st'

val app_fcrs (#vspec:_) (tl: verifiable_log vspec)
  : S.seq (appfn_call_res vspec.app)

val app_fcrs_map (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl{is_appfn tl i})
  : j:SA.seq_index (app_fcrs tl) { to_app_fcr tl i = S.index (app_fcrs tl) j}

val app_fcrs_invmap (#vspec:_) (tl: verifiable_log vspec) (j: SA.seq_index (app_fcrs tl))
  : i: seq_index tl { is_appfn tl i /\ app_fcrs_map tl i = j}

val lemma_add_fcrs_map (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl{is_appfn tl i})
  : Lemma (ensures (let fcrs = app_fcrs tl in
                    let j = app_fcrs_map tl i in
                    app_fcrs_invmap tl j = i))
          [SMTPat (app_fcrs_map tl i)]

val app_fcrs_map_monotonic (#vspec:_) (tl: verifiable_log vspec) (i1 i2: (i:seq_index tl{is_appfn tl i}))
  : Lemma (ensures ((i1 < i2 ==> app_fcrs_map tl i1 < app_fcrs_map tl i2) /\
                    (i2 < i1 ==> app_fcrs_map tl i2 < app_fcrs_map tl i1)))

val app_fcrs_invmap_monotonic (#vspec:_) (tl: verifiable_log vspec) (j1 j2: SA.seq_index (app_fcrs tl))
  : Lemma (ensures ((j1 < j2 ==> app_fcrs_invmap tl j1 < app_fcrs_invmap tl j2) /\
                    (j2 < j1 ==> app_fcrs_invmap tl j2 < app_fcrs_invmap tl j1)))

val app_fcrs_within_ep
  (#vspec:_)
  (ep: epoch)
  (tl: verifiable_log vspec)
  : S.seq (appfn_call_res vspec.app)

val app_fcrs_empty (#vspec:_) (ep: epoch) (tl: verifiable_log vspec)
  : Lemma (ensures (length tl = 0 ==> S.length (app_fcrs_within_ep ep tl) = 0))

val app_fcrs_snoc (#vspec:_) (ep: epoch) (tl: verifiable_log vspec {length tl > 0})
  : Lemma (ensures (let i = length tl - 1 in
                    let tl' = prefix tl i in
                    let fcrs' = app_fcrs_within_ep ep tl' in
                    let fcrs = app_fcrs_within_ep ep tl in
                    if is_appfn_within_epoch ep tl i then
                      fcrs == SA.append1 fcrs' (to_app_fcr tl i)
                    else
                      fcrs == fcrs'))

val app_fcrs_ep_map (#vspec:_)
    (ep: epoch)
    (tl: verifiable_log vspec)
    (i: seq_index tl{is_appfn_within_epoch ep tl i})
  : j:SA.seq_index (app_fcrs_within_ep ep tl) { to_app_fcr tl i = S.index (app_fcrs_within_ep ep tl) j}

val app_fcrs_ep_invmap (#vspec:_)
  (ep: epoch)
  (tl: verifiable_log vspec)
  (j: SA.seq_index (app_fcrs_within_ep ep tl))
  : i: seq_index tl { is_appfn_within_epoch ep tl i /\ app_fcrs_ep_map ep tl i = j}

val lemma_app_fcrs_ep_map (#vspec:_)
  (ep: epoch)
  (tl: verifiable_log vspec)
  (i: seq_index tl{is_appfn_within_epoch ep tl i})
  : Lemma (ensures (let fcrs = app_fcrs_within_ep ep tl in
                    let j = app_fcrs_ep_map ep tl i in
                    app_fcrs_ep_invmap ep tl j = i))
          [SMTPat (app_fcrs_ep_map ep tl i)]

val app_fcrs_ep_map_monotonic (#vspec:_)
  (ep: epoch)
  (tl: verifiable_log vspec)
  (i1 i2: (i:seq_index tl{is_appfn_within_epoch ep tl i}))
  : Lemma (ensures ((i1 < i2 ==> app_fcrs_ep_map ep tl i1 < app_fcrs_ep_map ep tl i2) /\
                    (i2 < i1 ==> app_fcrs_ep_map ep tl i2 < app_fcrs_ep_map ep tl i1)))

val app_fcrs_ep_invmap_monotonic (#vspec:_)
  (ep: epoch)
  (tl: verifiable_log vspec)
  (j1 j2: SA.seq_index (app_fcrs_within_ep ep tl))
  : Lemma (ensures ((j1 < j2 ==> app_fcrs_ep_invmap ep tl j1 < app_fcrs_ep_invmap ep tl j2) /\
                    (j2 < j1 ==> app_fcrs_ep_invmap ep tl j2 < app_fcrs_ep_invmap ep tl j1)))

let prefix_of (#vspec:_) (tl1 tl2: verifiable_log vspec)
  = length tl1 <= length tl2 &&
    tl1 = prefix tl2 (length tl1)

val prefix_within_epoch (#vspec:_) (ep: epoch) (tl: verifiable_log vspec)
  : tl': verifiable_log vspec {tl' `prefix_of` tl}

val prefix_within_epoch_correct (#vspec:_) (ep: epoch) (tl: verifiable_log vspec) (i: seq_index tl)
  : Lemma (ensures (let tl' = prefix_within_epoch ep tl in
                    let l' = length tl' in
                    (i < l' ==> (clock tl i).e <= ep) /\
                    (i >= l' ==> (clock tl i).e > ep)))

val lemma_app_fcrs_ep_prefix (#vspec:_)
  (ep: epoch)
  (tl: verifiable_log vspec)
  : Lemma (ensures (let tl' = prefix_within_epoch ep tl in
                    app_fcrs tl' == app_fcrs_within_ep ep tl))
