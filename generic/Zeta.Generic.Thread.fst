module Zeta.Generic.Thread

module IF = Zeta.IdxFn

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

let gen_seq (vspec: verifier_spec) = {
  IF.seq_t = verifiable_log vspec;
  IF.length = length;
  IF.prefix = prefix;
}

let is_blum_add_ifn (#vspec:_)
  : IF.idxfn_t (gen_seq vspec) bool
  = is_blum_add

let is_blum_add_epoch_ifn (#vspec:_) (ep: epoch)
  : IF.idxfn_t (gen_seq vspec) bool
  = is_blum_add_ep ep

let blum_add_elem_ifn (#vspec:_)
  : IF.cond_idxfn_t (ms_hashfn_dom vspec.app) (is_blum_add_ifn #vspec)
  = blum_add_elem #vspec

let add_seq (#vspec:_) (ep: epoch) (tl: verifiable_log vspec)
  : S.seq (ms_hashfn_dom vspec.app)
  = let fm = IF.to_fm (is_blum_add_epoch_ifn #vspec ep) (blum_add_elem_ifn #vspec) in
    IF.filter_map fm tl

let add_seq_map (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl {is_blum_add tl i})
  : (let be = blum_add_elem tl i in
     let ep = be.t.e in
     let as = add_seq ep tl in
     j: SA.seq_index as { S.index as j = be })
  = let be = blum_add_elem tl i in
    let ep = be.t.e in
    let fm = IF.to_fm (is_blum_add_epoch_ifn #vspec ep) (blum_add_elem_ifn #vspec) in
    IF.filter_map_map fm tl i

let add_seq_invmap (#vspec:_) (ep: epoch) (tl: verifiable_log vspec) (j: SA.seq_index (add_seq ep tl))
  : i:seq_index tl { is_blum_add_ep ep tl i /\ add_seq_map tl i = j  }
  = let fm = IF.to_fm (is_blum_add_epoch_ifn #vspec ep) (blum_add_elem_ifn #vspec) in
    IF.filter_map_invmap fm tl j

let lemma_add_seq_map (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl {is_blum_add tl i})
  : Lemma (ensures (let be = blum_add_elem tl i in
                    let ep = be.t.e in
                    let as = add_seq ep tl in
                    let j = add_seq_map tl i in
                    add_seq_invmap ep tl j = i))
  = ()

let add_seq_map_monotonic (#vspec:_) (tl: verifiable_log vspec) (i1 i2: (i:seq_index tl {is_blum_add tl i}))
  : Lemma (requires (let be1 = blum_add_elem tl i1 in
                     let be2 = blum_add_elem tl i2 in
                     be1.t.e = be2.t.e))
          (ensures ((i1 < i2 ==> add_seq_map tl i1 < add_seq_map tl i2) /\
                    (i2 < i1 ==> add_seq_map tl i2 < add_seq_map tl i1)))
  = let be1 = blum_add_elem tl i1 in
    let ep = be1.t.e in
    let fm = IF.to_fm (is_blum_add_epoch_ifn #vspec ep) (blum_add_elem_ifn #vspec) in
    IF.lemma_filter_map_map_monotonic fm tl i1 i2

let add_seq_invmap_monotonic (#vspec:_) (ep: epoch) (tl: verifiable_log vspec) (j1 j2: SA.seq_index (add_seq ep tl))
  : Lemma (ensures ((j1 < j2 ==> add_seq_invmap ep tl j1 < add_seq_invmap ep tl j2) /\
                    (j2 < j1 ==> add_seq_invmap ep tl j2 < add_seq_invmap ep tl j1)))
  = let fm = IF.to_fm (is_blum_add_epoch_ifn #vspec ep) (blum_add_elem_ifn #vspec) in
    IF.filter_map_invmap_monotonic fm tl j1 j2

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

let is_blum_evict_ifn (#vspec:_)
  : IF.idxfn_t (gen_seq vspec) bool
  = is_blum_evict

let is_blum_evict_epoch_ifn (#vspec:_) (ep: epoch)
  : IF.idxfn_t (gen_seq vspec) bool
  = is_blum_evict_ep ep

let blum_evict_elem_ifn (#vspec:_)
  : IF.cond_idxfn_t (ms_hashfn_dom vspec.app) (is_blum_evict_ifn #vspec)
  = blum_evict_elem #vspec

let evict_seq (#vspec:_) (ep: epoch) (tl: verifiable_log vspec)
  : S.seq (ms_hashfn_dom vspec.app)
  = let fm = IF.to_fm (is_blum_evict_epoch_ifn #vspec ep) (blum_evict_elem_ifn #vspec) in
    IF.filter_map fm tl

let evict_seq_map (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl {is_blum_evict tl i})
  : (let be = blum_evict_elem tl i in
     let ep = be.t.e in
     let es = evict_seq ep tl in
     j: SA.seq_index es { S.index es j = be })
  = let be = blum_evict_elem tl i in
    let ep = be.t.e in
    let fm = IF.to_fm (is_blum_evict_epoch_ifn #vspec ep) (blum_evict_elem_ifn #vspec) in
    IF.filter_map_map fm tl i

let evict_seq_invmap (#vspec:_) (ep: epoch) (tl: verifiable_log vspec) (j: SA.seq_index (evict_seq ep tl))
  : i:seq_index tl { is_blum_evict_ep ep tl i /\ evict_seq_map tl i = j  }
  = let fm = IF.to_fm (is_blum_evict_epoch_ifn #vspec ep) (blum_evict_elem_ifn #vspec) in
    IF.filter_map_invmap fm tl j

#push-options "--fuel 0 --ifuel 1 --query_stats"

let lemma_evict_seq_map (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl {is_blum_evict tl i})
  : Lemma (ensures (let be = blum_evict_elem tl i in
                    let ep = be.t.e in
                    let as = evict_seq ep tl in
                    let j = evict_seq_map tl i in
                    evict_seq_invmap ep tl j = i))
  = ()

#pop-options

let evict_seq_map_monotonic (#vspec:_) (tl: verifiable_log vspec) (i1 i2: (i:seq_index tl {is_blum_evict tl i}))
  : Lemma (requires (let be1 = blum_evict_elem tl i1 in
                     let be2 = blum_evict_elem tl i2 in
                     be1.t.e = be2.t.e))
          (ensures ((i1 < i2 ==> evict_seq_map tl i1 < evict_seq_map tl i2) /\
                    (i2 < i1 ==> evict_seq_map tl i2 < evict_seq_map tl i1)))
  = let be1 = blum_evict_elem tl i1 in
    let ep = be1.t.e in
    let fm = IF.to_fm (is_blum_evict_epoch_ifn #vspec ep) (blum_evict_elem_ifn #vspec) in
    IF.lemma_filter_map_map_monotonic fm tl i1 i2

let evict_seq_invmap_monotonic (#vspec:_) (ep: epoch) (tl: verifiable_log vspec) (j1 j2: SA.seq_index (evict_seq ep tl))
  : Lemma (ensures ((j1 < j2 ==> evict_seq_invmap ep tl j1 < evict_seq_invmap ep tl j2) /\
                    (j2 < j1 ==> evict_seq_invmap ep tl j2 < evict_seq_invmap ep tl j1)))
  = let fm = IF.to_fm (is_blum_evict_epoch_ifn #vspec ep) (blum_evict_elem_ifn #vspec) in
    IF.filter_map_invmap_monotonic fm tl j1 j2

let lemma_add_clock (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl{is_blum_add tl i})
  : Lemma (ensures (let be = blum_add_elem tl i in
                    be.t `ts_lt` clock tl i))
  = ()

let lemma_evict_clock (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl{is_blum_evict tl i})
  : Lemma (ensures (let be = blum_evict_elem tl i in
                    be.t = clock tl i))
  = ()

#push-options "--z3rlimit_factor 4 --query_stats"

let evict_elem_unique_aux (#vspec:_) (ep: epoch) (tl: verifiable_log vspec) (j1 j2: SA.seq_index (evict_seq ep tl))
  : Lemma (ensures (let es = evict_seq ep tl in
                    j1 <  j2 ==>  S.index es j1 <> S.index es j2))
  = if j1 < j2 then (
      let i1 = evict_seq_invmap ep tl j1 in
      let i2 = evict_seq_invmap ep tl j2 in
      evict_seq_invmap_monotonic ep tl j1 j2;
      assert(i1 < i2);

      (* the clock increases during the evict processing *)
      let i2' = i2 - 1 in
      lemma_state_transition tl i2;
      assert(clock tl i2' `ts_lt` clock tl i2);

      (* the clock is monotonic => the clock after the first evict < clock after the second *)
      assert(i1 <= i2');
      lemma_clock_monotonic tl i1 i2';
      assert(clock tl i1 `ts_lt` clock tl i2)
    )

#pop-options

let evict_elem_unique (#vspec:_) (ep: epoch) (tl: verifiable_log vspec) (i1 i2: SA.seq_index (evict_seq ep tl))
  : Lemma (ensures (let es = evict_seq ep tl in
                    i1 <> i2 ==>  S.index es i1 <> S.index es i2))
  = if i1 < i2 then
      evict_elem_unique_aux ep tl i1 i2
    else if i2 < i1 then
      evict_elem_unique_aux ep tl i2 i1

let evict_elem_tid (#vspec:_) (ep: epoch) (tl: verifiable_log vspec) (i: SA.seq_index (evict_seq ep tl))
  : Lemma (ensures (let es = evict_seq ep tl in
                    let be = S.index es i in
                    let t,_ = tl in
                    be.tid = t))
  = ()

let is_appfn_ifn (#vspec:_)
  : IF.idxfn_t (gen_seq vspec) bool
  = is_appfn #vspec

let to_app_fcr_ifn (#vspec:_)
  : IF.cond_idxfn_t (appfn_call_res vspec.app) (is_appfn_ifn #vspec)
  = to_app_fcr #vspec

let app_fcrs (#vspec:_) (tl: verifiable_log vspec)
  : S.seq (appfn_call_res vspec.app)
  = let fm = IF.to_fm (is_appfn_ifn #vspec) (to_app_fcr #vspec) in
    IF.filter_map fm tl

let is_appfn_within_ep_ifn (#vspec:_) (ep: epoch)
  : IF.idxfn_t (gen_seq vspec) bool
  = is_appfn_within_epoch ep

let app_fcrs_within_ep
  (#vspec:_)
  (ep: epoch)
  (tl: verifiable_log vspec)
  : S.seq (appfn_call_res vspec.app)
  = let fm = IF.to_fm (is_appfn_within_ep_ifn #vspec ep) (to_app_fcr #vspec) in
    IF.filter_map fm tl
