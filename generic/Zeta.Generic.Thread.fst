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
  = ()

let conj_is_idxfn (#vspec:_) (f1 f2: idxfn_t vspec bool)
  : Lemma (ensures (prefix_property (conj f1 f2)))
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
  = let e = index tl i in
    let st' = state_pre tl i in
    let st = state_post tl i in
    assert(vspec.valid st);
    let s = evict_slot e in
    let t = blum_evict_timestamp e in
    let r = Some?.v (vspec.get s st') in
    let tid = vspec.tid st' in
    MHDom r t tid

let is_blum_evict #vspec (ep: epoch) (tl: verifiable_log vspec) (i: seq_index tl)
  = is_blum_evict_base tl i &&
    (let be = blum_evict_elem_base tl i in be.t.e = ep)

let blum_evict_cond_prefix_prop vspec (ep: epoch)
  : Lemma (ensures (cond_prefix_property #vspec
                                         #(ms_hashfn_dom vspec.app)
                                         #(is_blum_evict ep)
                                         blum_evict_elem_base))
  = ()

let blum_evict_elem #vspec (#ep: epoch) (tl: verifiable_log vspec) (i: seq_index tl {is_blum_evict ep tl i})
  = blum_evict_cond_prefix_prop vspec ep;
    blum_evict_elem_base tl i

let is_appfn (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl)
  = GV.is_appfn (index tl i)

let appfn_call_res (#vspec:_) (ep: epoch)
    (tl: verifiable_log vspec) (i: seq_index tl {is_appfn tl i && is_within_epoch ep tl i})
  = let e = index tl i in
    let st' = state_pre tl i in
    let st = state_post tl i in
    assert(vspec.valid st);
    GV.appfn_result e st'

let rec filter_map (#vspec:_) (#b:_)
  (fm: fm_t vspec b)
  (tl: verifiable_log vspec)
  : Tot (S.seq b)
    (decreases length tl)
  = let n = length tl in
    if n = 0
    then S.empty #b
    else
      let tl' = prefix tl (n - 1) in
      let ms' = filter_map fm tl' in
      if fm.f tl (n-1)
      then SA.append1 ms' (fm.m tl (n - 1))
      else ms'

let rec filter_map_map (#vspec:_) (#b:_)
  (fm: fm_t vspec b)
  (tl: verifiable_log vspec)
  (i: seq_index tl {fm.f tl i})
  : Tot(j: (SA.seq_index (filter_map fm tl)) {S.index (filter_map fm tl) j == fm.m tl i})
    (decreases (length tl))
  = let n = length tl - 1 in
    let tl' = prefix tl n in
    let ms' = filter_map fm tl' in
    if i = n
    then S.length ms'
    else filter_map_map fm tl' i

let rec filter_map_invmap (#vspec:_) (#b:_)
  (fm: fm_t vspec b)
  (tl: verifiable_log vspec)
  (j: SA.seq_index (filter_map fm tl))
  : Tot(i:(seq_index tl){fm.f tl i /\ filter_map_map fm tl i = j })
    (decreases (length tl))
  = let n = length tl - 1 in
    let tl' = prefix tl n in
    let ms' = filter_map fm tl' in
    if j = S.length ms'
    then n
    else filter_map_invmap fm tl' j

let rec lemma_filter_map (#vspec:_) (#b:_)
  (fm: fm_t vspec b)
  (tl: verifiable_log vspec)
  (i: seq_index tl {fm.f tl i})
  : Lemma (ensures (let j = filter_map_map fm tl i in
                    i = filter_map_invmap fm tl j))
          (decreases (length tl))
  = let n = length tl - 1 in
    let tl' = prefix tl n in
    if i = n then ()
    else lemma_filter_map fm tl' i

let lemma_filter_map_extend_sat
  (#vspec:_)
  (#b:eqtype)
  (fm: fm_t vspec b)
  (tl: verifiable_log vspec {length tl > 0 /\ fm.f tl (length tl - 1)})
  : Lemma (ensures (let fms = filter_map fm tl in
                    let fms' = filter_map fm (prefix tl (length tl - 1)) in
                    let me = fm.m tl (length tl - 1) in
                    fms == SA.append1 fms' me))
  = ()

let lemma_filter_map_extend_unsat
  (#vspec:_)
  (#b:eqtype)
  (fm: fm_t vspec b)
  (tl: verifiable_log vspec {length tl > 0 /\ not (fm.f tl (length tl - 1))})
  : Lemma (ensures (let fms = filter_map fm tl in
                    let fms' = filter_map fm (prefix tl (length tl - 1)) in
                    fms == fms'))
  = ()

let lemma_filter_map_empty
  (#vspec:_)
  (#b:eqtype)
  (fm: fm_t vspec b)
  (tl: verifiable_log vspec {length tl = 0})
  : Lemma (ensures S.length (filter_map fm tl) = 0)
  = ()
