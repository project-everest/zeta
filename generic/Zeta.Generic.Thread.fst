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

(* the thread id in the state is always the one specified in the parameter *)
let rec lemma_thread_id_state (#vspec:verifier_spec) (tl: verifiable_log vspec):
  Lemma (ensures (let tid, _ = tl in
                  vspec.tid (verify tl) = tid))
        (decreases (length tl))
  = let n = length tl in
    if n = 0 then ()
    else lemma_thread_id_state (prefix tl (n-1))


let blum_add_elem (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl { is_blum_add tl i })
  : ms_hashfn_dom vspec.app
  = admit()

let blum_evict_elem (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl { is_blum_evict tl i }):
  ms_hashfn_dom vspec.app
  = admit()
