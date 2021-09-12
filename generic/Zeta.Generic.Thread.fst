module Zeta.Generic.Thread

(* if a thread log is verifiable, its prefix is verifiable *)
let rec verifiable_implies_prefix_verifiable (#vspec:verifier_spec)
  (tl:verifiable_log vspec) (i:nat{i <= length tl}):
  Lemma (ensures (verifiable (prefix tl i)))
        (decreases (length tl))
  = let n = length tl in
    if n = i then ()
    else verifiable_implies_prefix_verifiable (prefix tl (n-1)) i

(* the state after processing i'th entry is obtained by applying the verify
 * step to the state before processing the i'th entry *)
let lemma_state_transition (#vspec:verifier_spec) (tl: verifiable_log vspec) (i: seq_index tl):
  Lemma (ensures (state_post tl i ==
                  verify_step (index tl i) (state_pre tl i)))
        [SMTPat (state_post tl i)]
  = ()

(* clock after processing i entries of the log *)
let clock_base #vspec (tl: verifiable_log vspec)
  = let vs = state tl in
    vspec.clock vs

#push-options "--z3rlimit_factor 3"

let rec lemma_clock_monotonic (#vspec:verifier_spec)
  (tl: verifiable_log vspec) (i:nat) (j: seq_index tl {j >= i}):
  Lemma (ensures (clock tl i `ts_leq` clock tl j))
  (decreases (i + j + length tl))
  = let n = length tl - 1 in
    let tl' = prefix tl n in
    if j < n
    then lemma_clock_monotonic tl' i j
    else if i = j then ()
    else lemma_clock_monotonic tl i (j-1)

#pop-options

(* the thread id in the state is always the one specified in the parameter *)
let rec lemma_thread_id_state (#vspec:verifier_spec) (tl: verifiable_log vspec):
  Lemma (ensures (let tid, _ = tl in
                  vspec.tid (verify tl) = tid))
        (decreases (length tl))
  = let n = length tl in
    if n = 0 then ()
    else lemma_thread_id_state (prefix tl (n-1))

let blum_evict_elem (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl{is_blum_evict tl i})
  : be:ms_hashfn_dom vspec.app {let e = index tl i in
                                let s = evict_slot e in
                                let vs_pre = state_pre tl i in
                                let open Zeta.MultiSetHashDomain in
                                Some? (vspec.get s vs_pre) /\
                                be.r = Some?.v (vspec.get s vs_pre) /\
                                be.t = blum_evict_timestamp e /\
                                be.tid = fst tl}
  = let e = index tl i in
    let st' = state_pre tl i in
    let st = state_post tl i in
    let s = evict_slot e in
    let t = blum_evict_timestamp e in
    lemma_state_transition tl i;
    let r = Some?.v (vspec.get s st') in
    let tid = fst tl in
    MHDom r t tid

let to_appfn_call_res (#vspec:_)
    (tl: verifiable_log vspec) (i: seq_index tl {is_appfn tl i})
  = let e = index tl i in
    let st' = state_pre tl i in
    let st = state_post tl i in
    assert(vspec.valid st);
    GV.appfn_result e st'

let lemma_add_clock (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl{is_blum_add tl i})
  : Lemma (ensures (let be = blum_add_elem tl i in
                    be.t `ts_lt` clock tl i))
  = admit()

let lemma_evict_clock (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl{is_blum_evict tl i})
  : Lemma (ensures (let be = blum_evict_elem tl i in
                    be.t = clock tl i))
  = admit()
