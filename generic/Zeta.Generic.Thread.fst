module Zeta.Generic.Thread

(* if a thread log is verifiable, its prefix is verifiable *)
let rec verifiable_implies_prefix_verifiable (#vspec:verifier_spec)
  (tl:verifiable_log vspec) (i:nat{i <= length tl}):
  Lemma (ensures (verifiable (prefix_base tl i)))
        (decreases (length tl))
  = let n = length tl in
    if n = i then ()
    else verifiable_implies_prefix_verifiable (prefix_base tl (n-1)) i

(* the state after processing i'th entry is obtained by applying the verify
 * step to the state before processing the i'th entry *)
let lemma_state_transition (#vspec:verifier_spec) (tl: verifiable_log vspec) (i: seq_index tl):
  Lemma (ensures (state_post_base tl i ==
                  verify_step (index tl i) (state_pre_base tl i)))
  = ()

(* clock after processing i entries of the log *)
let clock_base #vspec (tl: verifiable_log vspec) (i: seq_index tl)
  = vspec.clock (verify (prefix tl (i+1)))

let clock #vspec: (idxfn_t vspec timestamp) = clock_base #vspec

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

let is_blum_add #vspec (tl: verifiable_log vspec) (i: seq_index tl)
  = GV.is_blum_add (index tl i)

let blum_add_elem #vspec (tl: verifiable_log vspec) (i: seq_index tl{is_blum_add tl i})
  : ms_hashfn_dom vspec.app
  = match (index tl i) with
    | AddB r _ t tid ->
      MHDom r t tid

let is_blum_evict #vspec (tl: verifiable_log vspec) (i: seq_index tl)
  = GV.is_blum_evict (index tl i)

let blum_evict_elem #vspec (tl: verifiable_log vspec) (i: seq_index tl{is_blum_evict tl i})
  : ms_hashfn_dom vspec.app
  = let e = index tl i in
    let st' = state_pre tl i in
    let st = state_post tl i in
    assert(vspec.valid st);
    let s = evict_slot e in
    let t = blum_evict_timestamp e in
    let r = Some?.v (vspec.get s st') in
    let tid = vspec.tid st' in
    MHDom r t tid

let is_appfn (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl)
  = GV.is_appfn (index tl i)

let to_appfn_call_res (#vspec:_)
    (tl: verifiable_log vspec) (i: seq_index tl {is_appfn tl i})
  = let e = index tl i in
    let st' = state_pre tl i in
    let st = state_post tl i in
    assert(vspec.valid st);
    GV.appfn_result e st'
