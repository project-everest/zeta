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
  Lemma (ensures (state_at tl (i + 1) ==
                  verify_step (index tl i) (state_at tl i)))
  = ()

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

let is_blum_add_base #vspec (tl: verifiable_log vspec) (i: seq_index tl)
  = GV.is_blum_add (index tl i)

let blum_add_elem_base #vspec (tl: verifiable_log vspec) (i: seq_index tl{is_blum_add_base tl i})
  : ms_hashfn_dom vspec.app
  = match (index tl i) with
    | AddB r _ t tid ->
      MHDom r t tid

let is_blum_add #vspec (ep:epoch) (tl: verifiable_log vspec) (i:seq_index tl)
  = is_blum_add_base tl i &&
    (let be = blum_add_elem_base tl i in be.t.e = ep)

let blum_add_elem (#vspec:_) (#ep: epoch) (tl: verifiable_log vspec) (i: seq_index tl { is_blum_add ep tl i })
  = blum_add_elem_base tl i

let is_blum_evict_base #vspec (tl: verifiable_log vspec) (i: seq_index tl)
  = GV.is_blum_evict (index tl i)

let blum_evict_elem_base #vspec (tl: verifiable_log vspec) (i: seq_index tl{is_blum_evict_base tl i})
  : ms_hashfn_dom vspec.app
  = match (index tl i) with
    | EvictB s t -> admit()
    | EvictBM s s' t -> admit()
