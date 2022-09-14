module Zeta.Generic.Thread

open FStar.Classical
open Zeta.SMap
module IF = Zeta.IdxFn

(* the state after processing i'th entry is obtained by applying the verify
 * step to the state before processing the i'th entry *)
let lemma_state_transition (#vspec:verifier_spec) (tl: vlog vspec) (i: seq_index tl):
  Lemma (ensures (state_post tl i ==
                  verify_step (index tl i) (state_pre tl i)))
        [SMTPat (state_post tl i)]
  = ()

(* if a thread log is verifiable, its prefix is verifiable *)
let rec verifiable_implies_prefix_verifiable (#vspec:verifier_spec)
  (tl:verifiable_log vspec) (i:nat{i <= length tl}):
  Lemma (ensures (verifiable (prefix_base tl i)))
        (decreases (length tl))
  = let n = length tl in
    if n = i then ()
    else verifiable_implies_prefix_verifiable (prefix_base tl (n-1)) i

#push-options "--fuel 1 --ifuel 1 --query_stats"

let lemma_clock_lek_monotonic_aux (#vspec: verifier_spec)
  (tl: verifiable_log vspec) (i: seq_index tl)
  : Lemma (ensures ((clock_lek_pre tl i) `Zeta.TimeKey.lte` (clock_lek_post tl i)))
          [SMTPat (clock_lek tl i)]
  = lemma_state_transition tl i

let rec lemma_clock_lek_monotonic (#vspec: verifier_spec)
  (tl: verifiable_log vspec) (i:nat) (j: seq_index tl {j >= i})
  : Lemma (ensures (clock_lek tl i `Zeta.TimeKey.lte` clock_lek tl j))
          (decreases (i + j + length tl))
  = let n = length tl - 1 in
    let tl' = prefix tl n in
    let lte = Zeta.TimeKey.lte in
    if i <> j then
      if j < n then lemma_clock_lek_monotonic tl' i j
      else
      begin
        lemma_clock_lek_monotonic tl' i (j-1);
        Zeta.TimeKey.lt_is_transitive (clock_lek tl i) (clock_lek tl (j-1)) (clock_lek tl j)
      end

#pop-options

let lemma_clock_monotonic (#vspec:verifier_spec)
  (tl: verifiable_log vspec) (i:nat) (j: seq_index tl {j >= i}):
  Lemma (ensures (clock tl i `ts_leq` clock tl j))
  (decreases (i + j + length tl))
  = lemma_clock_lek_monotonic tl i j

(* the thread id in the state is always the one specified in the parameter *)
let rec lemma_thread_id_state (#vspec:verifier_spec) (tl: verifiable_log vspec):
  Lemma (ensures (let tid, _ = tl in
                  vspec.tid (verify tl) = tid))
        (decreases (length tl))
  = let n = length tl in
    if n = 0 then ()
    else lemma_thread_id_state (prefix tl (n-1))

let gen_seq (vspec:verifier_spec) (tid:thread_id) = {
  IF.a = verifier_log_entry vspec;
  IF.phi = (fun s -> verifiable (tid, s));
  IF.phi_commutes_with_prefix = (fun s i ->
    verifiable_implies_prefix_verifiable (tid, s) i);
}

let is_blum_add_ifn (#vspec:_) (tid:thread_id)
  : IF.idxfn_t (gen_seq vspec tid) bool
  = fun (s:IF.seq_t (gen_seq vspec tid)) -> is_blum_add (tid, s)

let is_blum_add_epoch_ifn (#vspec:_) (tid:thread_id) (ep: epoch)
  : IF.idxfn_t (gen_seq vspec tid) bool
  = fun (s:IF.seq_t (gen_seq vspec tid)) -> is_blum_add_ep ep (tid, s)

let blum_add_elem_ifn (#vspec:_) (tid:thread_id)
  : IF.cond_idxfn_t (ms_hashfn_dom vspec.app) (is_blum_add_ifn #vspec tid)
  = fun (s:IF.seq_t (gen_seq vspec tid)) -> blum_add_elem #vspec (tid, s)

let add_seq (#vspec:_) (ep: epoch) (tl: verifiable_log vspec)
  : S.seq (ms_hashfn_dom vspec.app)
  = let fm = IF.to_fm (is_blum_add_epoch_ifn #vspec (fst tl) ep) (blum_add_elem_ifn #vspec (fst tl)) in
    IF.filter_map fm (snd tl)

let add_seq_empty (#vspec:_) (ep: epoch) (tl: verifiable_log vspec)
  : Lemma (ensures (length tl = 0 ==> S.length (add_seq ep tl) = 0))
  = if length tl = 0 then ()

let add_seq_snoc
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
  = let fm = IF.to_fm (is_blum_add_epoch_ifn #vspec (fst tl) ep) (blum_add_elem_ifn #vspec (fst tl)) in
    let i = length tl - 1 in
    if is_blum_add_ep ep tl i then
      IF.lemma_filter_map_snoc fm (snd tl)

let add_seq_map (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl {is_blum_add tl i})
  : (let be = blum_add_elem tl i in
     let ep = be.t.e in
     let a_s = add_seq ep tl in
     j: SA.seq_index a_s { S.index a_s j = be })
  = let be = blum_add_elem tl i in
    let ep = be.t.e in
    let fm = IF.to_fm (is_blum_add_epoch_ifn #vspec (fst tl) ep) (blum_add_elem_ifn #vspec (fst tl)) in
    IF.filter_map_map fm (snd tl) i

let add_seq_invmap (#vspec:_) (ep: epoch) (tl: verifiable_log vspec) (j: SA.seq_index (add_seq ep tl))
  : i:seq_index tl { is_blum_add_ep ep tl i /\ add_seq_map tl i = j  }
  = let fm = IF.to_fm (is_blum_add_epoch_ifn #vspec (fst tl) ep) (blum_add_elem_ifn #vspec (fst tl)) in
    IF.filter_map_invmap fm (snd tl) j

let lemma_add_seq_map (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl {is_blum_add tl i})
  : Lemma (ensures (let be = blum_add_elem tl i in
                    let ep = be.t.e in
                    let a_s = add_seq ep tl in
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
    let fm = IF.to_fm (is_blum_add_epoch_ifn #vspec (fst tl) ep) (blum_add_elem_ifn #vspec (fst tl)) in
    IF.lemma_filter_map_map_monotonic fm (snd tl) i1 i2

let add_seq_invmap_monotonic (#vspec:_) (ep: epoch) (tl: verifiable_log vspec) (j1 j2: SA.seq_index (add_seq ep tl))
  : Lemma (ensures ((j1 < j2 ==> add_seq_invmap ep tl j1 < add_seq_invmap ep tl j2) /\
                    (j2 < j1 ==> add_seq_invmap ep tl j2 < add_seq_invmap ep tl j1)))
  = let fm = IF.to_fm (is_blum_add_epoch_ifn #vspec (fst tl) ep) (blum_add_elem_ifn #vspec (fst tl)) in
    IF.filter_map_invmap_monotonic fm (snd tl) j1 j2

let blum_evict_elem (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl{is_blum_evict tl i})
  : GTot (be:ms_hashfn_dom vspec.app {let e = index tl i in
                                      let s = evict_slot e in
                                      let vs_pre = state_pre tl i in
                                      let open Zeta.MultiSetHashDomain in
                                      Some? (vspec.get s vs_pre) /\
                                      be.r = Some?.v (vspec.get s vs_pre) /\
                                      be.t = blum_evict_timestamp e /\
                                      be.tid = fst tl})
  = let e = index tl i in
    let st' = state_pre tl i in
    let st = state_post tl i in
    let s = evict_slot e in
    let t = blum_evict_timestamp e in
    lemma_state_transition tl i;
    let r = Some?.v (vspec.get s st') in
    let tid = fst tl in
    MHDom r t tid

let is_blum_evict_ifn (#vspec:_) (tid:thread_id)
  : IF.idxfn_t (gen_seq vspec tid) bool
  = fun (s:IF.seq_t (gen_seq vspec tid)) -> is_blum_evict (tid, s)

let is_blum_evict_epoch_ifn (#vspec:_) (tid:thread_id) (ep: epoch)
  : GTot (IF.idxfn_t (gen_seq vspec tid) bool)
  = hoist_ghost2 (fun (s:IF.seq_t (gen_seq vspec tid)) i -> is_blum_evict_ep ep (tid, s) i)

let blum_evict_elem_ifn (#vspec:_) (tid:thread_id)
  : GTot (IF.cond_idxfn_t (ms_hashfn_dom vspec.app) (is_blum_evict_ifn #vspec tid))
  = hoist_ghost2 (fun (s:IF.seq_t (gen_seq vspec tid)) i -> blum_evict_elem #vspec (tid, s) i)

let evict_seq (#vspec:_) (ep: epoch) (tl: verifiable_log vspec) =
  let fm = IF.to_fm (is_blum_evict_epoch_ifn #vspec (fst tl) ep) (blum_evict_elem_ifn #vspec (fst tl)) in
  IF.filter_map fm (snd tl)

let evict_seq_empty (#vspec:_) (ep: epoch) (tl: verifiable_log vspec)
  : Lemma (ensures (length tl = 0 ==> S.length (evict_seq ep tl) = 0))
  = if length tl = 0 then ()

let evict_seq_snoc
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
  = let fm = IF.to_fm (is_blum_evict_epoch_ifn #vspec (fst tl) ep) (blum_evict_elem_ifn #vspec (fst tl)) in
    let i = length tl - 1 in
    let tl' = prefix tl i in
    let es' = evict_seq ep tl' in
    let es = evict_seq ep tl in

    if is_blum_evict_ep ep tl i then
      IF.lemma_filter_map_snoc fm (snd tl)

let evict_seq_map (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl {is_blum_evict tl i}) =
  let be = blum_evict_elem tl i in
  let ep = be.t.e in
  let fm = IF.to_fm (is_blum_evict_epoch_ifn #vspec (fst tl) ep) (blum_evict_elem_ifn #vspec (fst tl)) in
  IF.filter_map_map fm (snd tl) i

let evict_seq_invmap (#vspec:_) (ep: epoch) (tl: verifiable_log vspec) (j: SA.seq_index (evict_seq ep tl)) =
  let fm = IF.to_fm (is_blum_evict_epoch_ifn #vspec (fst tl) ep) (blum_evict_elem_ifn #vspec (fst tl)) in
  IF.filter_map_invmap fm (snd tl) j

#push-options "--fuel 0 --ifuel 1 --query_stats"

let lemma_evict_seq_map (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl {is_blum_evict tl i})
  : Lemma (ensures (let be = blum_evict_elem tl i in
                    let ep = be.t.e in
                    let es = evict_seq ep tl in
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
    let fm = IF.to_fm (is_blum_evict_epoch_ifn #vspec (fst tl) ep) (blum_evict_elem_ifn #vspec (fst tl)) in
    IF.lemma_filter_map_map_monotonic fm (snd tl) i1 i2

let evict_seq_invmap_monotonic (#vspec:_) (ep: epoch) (tl: verifiable_log vspec) (j1 j2: SA.seq_index (evict_seq ep tl))
  : Lemma (ensures ((j1 < j2 ==> evict_seq_invmap ep tl j1 < evict_seq_invmap ep tl j2) /\
                    (j2 < j1 ==> evict_seq_invmap ep tl j2 < evict_seq_invmap ep tl j1)))
  = let fm = IF.to_fm (is_blum_evict_epoch_ifn #vspec (fst tl) ep) (blum_evict_elem_ifn #vspec (fst tl)) in
    IF.filter_map_invmap_monotonic fm (snd tl) j1 j2

let lemma_add_clock (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl{is_blum_add tl i})
  : Lemma (ensures (let be = blum_add_elem tl i in
                    be.t `ts_lt` clock tl i))
  = ()

let lemma_evict_clock (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl{is_blum_evict tl i})
  : Lemma (ensures (let be = blum_evict_elem tl i in
                    be.t = clock tl i))
  = ()

#push-options "--fuel 1 --ifuel 1  --query_stats"

let lemma_evictb_prop (#vspec: verifier_spec) (tl: verifiable_log vspec) (i: seq_index tl)
  : Lemma (requires (is_blum_evict tl i))
          (ensures (let c1,k1 = clock_lek_pre tl i in
                    let c2,k2 = clock_lek_post tl i in
                    let e = index tl i in
                    let MHDom (k,_) t tid = blum_evict_elem tl i in
                    (c1,k1) `Zeta.TimeKey.lt` (c2,k2) /\
                    t = blum_evict_timestamp e /\
                    Zeta.GenKey.to_base_key k = k2))
  = lemma_state_transition tl i

let blum_evict_clock_lek (#vspec: verifier_spec) (tl: verifiable_log vspec) (i: seq_index tl)
  : Lemma (requires (is_blum_evict tl i))
          (ensures (let c,k = clock_lek tl i in
                    let MHDom (gk,_) c' _ = blum_evict_elem tl i in
                    c = c' /\ k = Zeta.GenKey.to_base_key gk))
  = ()

let lemma_clock_lek_neq_implies_blum_evict_elem_neq
  (#vspec: verifier_spec)
  (tl: verifiable_log vspec)
  (i1 i2: seq_index tl)
  : Lemma (requires (is_blum_evict tl i1 /\ is_blum_evict tl i2 /\ clock_lek tl i1 <> clock_lek tl i2))
          (ensures (blum_evict_elem tl i1 <> blum_evict_elem tl i2))
  = blum_evict_clock_lek tl i1;
    blum_evict_clock_lek tl i2;
    ()

let evict_elem_unique_aux (#vspec:verifier_spec)
                          (ep: epoch) (tl: verifiable_log vspec) (j1 j2: SA.seq_index (evict_seq ep tl))
  : Lemma (ensures (let es = evict_seq ep tl in
                    j1 <  j2 ==>  S.index es j1 <> S.index es j2))
  = let lt = Zeta.TimeKey.lt in
    if j1 < j2 then
    begin
      let i1 = evict_seq_invmap ep tl j1 in
      let i2 = evict_seq_invmap ep tl j2 in
      evict_seq_invmap_monotonic ep tl j1 j2;
      assert(i1 < i2);

      (* the clock increases during the evict processing *)
      let i2' = i2 - 1 in
      lemma_state_transition tl i2;
      let _st = state_pre tl i2 in
      let e = index tl i2 in
      let st_ = state_post tl i2 in
      assert (GV.is_blum_evict e);
      assert (st_ == verify_step e _st);
      assert (vspec.valid st_);
      lemma_evictb_prop tl i2;
      assert(clock_lek tl i2' `lt` clock_lek tl i2);

      assert(i1 <= i2');
      lemma_clock_lek_monotonic tl i1 i2';
      Zeta.TimeKey.lt_is_transitive (clock_lek tl i1) (clock_lek tl i2') (clock_lek tl i2);
      assert(clock_lek tl i1 `lt` clock_lek tl i2);

      lemma_clock_lek_neq_implies_blum_evict_elem_neq tl i1 i2;

      ()
    end

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

let is_appfn_ifn (#vspec:_) (tid:thread_id)
  : IF.idxfn_t (gen_seq vspec tid) bool
  = fun (s:IF.seq_t (gen_seq vspec tid)) -> is_appfn #vspec (tid, s)

let to_app_fcr_ifn (#vspec:_) (tid:thread_id)
  : GTot (IF.cond_idxfn_t (appfn_call_res vspec.app) (is_appfn_ifn #vspec tid))
  = hoist_ghost2 (fun (s:IF.seq_t (gen_seq vspec tid)) -> to_app_fcr #vspec (tid, s))

let app_fcrs (#vspec:_) (tl: verifiable_log vspec) =
  let fm = IF.to_fm (is_appfn_ifn #vspec (fst tl))
                    (hoist_ghost2 (fun (s:IF.seq_t (gen_seq vspec (fst tl))) -> to_app_fcr #vspec (fst tl, s))) in
  IF.filter_map fm (snd tl)

let app_fcrs_map (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl{is_appfn tl i}) =
  let fm = IF.to_fm (is_appfn_ifn #vspec (fst tl))
                    (hoist_ghost2 (fun (s:IF.seq_t (gen_seq vspec (fst tl))) -> to_app_fcr #vspec (fst tl, s))) in
  IF.filter_map_map fm (snd tl) i

let app_fcrs_invmap (#vspec:_) (tl: verifiable_log vspec) (j: SA.seq_index (app_fcrs tl)) =
  let fm = IF.to_fm (is_appfn_ifn #vspec (fst tl))
                    (hoist_ghost2 (fun (s:IF.seq_t (gen_seq vspec (fst tl))) -> to_app_fcr #vspec (fst tl, s))) in
  IF.filter_map_invmap fm (snd tl) j

let lemma_add_fcrs_map (#vspec:_) (tl: verifiable_log vspec) (i: seq_index tl{is_appfn tl i})
  : Lemma (ensures (let fcrs = app_fcrs tl in
                    let j = app_fcrs_map tl i in
                    app_fcrs_invmap tl j = i))
  = ()

let app_fcrs_map_monotonic (#vspec:_) (tl: verifiable_log vspec) (i1 i2: (i:seq_index tl{is_appfn tl i}))
  : Lemma (ensures ((i1 < i2 ==> app_fcrs_map tl i1 < app_fcrs_map tl i2) /\
                    (i2 < i1 ==> app_fcrs_map tl i2 < app_fcrs_map tl i1)))
  = let fm = IF.to_fm (is_appfn_ifn #vspec (fst tl))
                      (hoist_ghost2 (fun (s:IF.seq_t (gen_seq vspec (fst tl))) -> to_app_fcr #vspec (fst tl, s))) in
    IF.lemma_filter_map_map_monotonic fm (snd tl) i1 i2

let app_fcrs_invmap_monotonic (#vspec:_) (tl: verifiable_log vspec) (j1 j2: SA.seq_index (app_fcrs tl))
  : Lemma (ensures ((j1 < j2 ==> app_fcrs_invmap tl j1 < app_fcrs_invmap tl j2) /\
                    (j2 < j1 ==> app_fcrs_invmap tl j2 < app_fcrs_invmap tl j1)))
  = let fm = IF.to_fm (is_appfn_ifn #vspec (fst tl))
                      (hoist_ghost2 (fun (s:IF.seq_t (gen_seq vspec (fst tl))) -> to_app_fcr #vspec (fst tl, s))) in
    IF.filter_map_invmap_monotonic fm (snd tl) j1 j2

let is_appfn_within_ep_ifn (#vspec:_) (tid:thread_id) (ep: epoch)
  : GTot (IF.idxfn_t (gen_seq vspec tid) bool)
  = hoist_ghost2 (fun (s:IF.seq_t (gen_seq vspec tid)) -> is_appfn_within_epoch ep (tid, s))

let fm_app_fcrs (#vspec:_) (tid:thread_id) (ep:epoch) =
  IF.to_fm (is_appfn_within_ep_ifn #vspec tid ep)
           (hoist_ghost2 (fun (s:IF.seq_t (gen_seq vspec tid)) -> to_app_fcr #vspec (tid, s)))

let app_fcrs_within_ep
  (#vspec:_)
  (ep: epoch)
  (tl: verifiable_log vspec)
  : GTot (S.seq (appfn_call_res vspec.app))
  = IF.filter_map (fm_app_fcrs (fst tl) ep) (snd tl)

let app_fcrs_empty (#vspec:_) (ep: epoch) (tl: verifiable_log vspec)
  : Lemma (ensures (length tl = 0 ==> S.length (app_fcrs_within_ep ep tl) = 0))
  = ()

let app_fcrs_snoc (#vspec:_) (ep: epoch) (tl: verifiable_log vspec {length tl > 0})
  : Lemma (ensures (let i = length tl - 1 in
                    let tl' = prefix tl i in
                    let fcrs' = app_fcrs_within_ep ep tl' in
                    let fcrs = app_fcrs_within_ep ep tl in
                    if is_appfn_within_epoch ep tl i then
                      fcrs == SA.append1 fcrs' (to_app_fcr tl i)
                    else
                      fcrs == fcrs'))
  = let i = length tl - 1 in
    if is_appfn_within_epoch ep tl i then begin
      IF.lemma_filter_map_snoc #(gen_seq vspec (fst tl)) #_ (fm_app_fcrs (fst tl) ep) (snd tl)
    end

let app_fcrs_ep_map (#vspec:_)
    (ep: epoch)
    (tl: verifiable_log vspec)
    (i: seq_index tl{is_appfn_within_epoch ep tl i})
  = IF.filter_map_map (fm_app_fcrs (fst tl) ep) (snd tl) i

let app_fcrs_ep_invmap (#vspec:_)
  (ep: epoch)
  (tl: verifiable_log vspec)
  (j: SA.seq_index (app_fcrs_within_ep ep tl))
  = IF.filter_map_invmap (fm_app_fcrs (fst tl) ep) (snd tl) j

let lemma_app_fcrs_ep_map (#vspec:_)
  (ep: epoch)
  (tl: verifiable_log vspec)
  (i: seq_index tl{is_appfn_within_epoch ep tl i})
  : Lemma (ensures (let j = app_fcrs_ep_map ep tl i in
                    app_fcrs_ep_invmap ep tl j = i))
  = ()

let app_fcrs_ep_map_monotonic (#vspec:_)
  (ep: epoch)
  (tl: verifiable_log vspec)
  (i1 i2: (i:seq_index tl{is_appfn_within_epoch ep tl i}))
  : Lemma (ensures ((i1 < i2 ==> app_fcrs_ep_map ep tl i1 < app_fcrs_ep_map ep tl i2) /\
                    (i2 < i1 ==> app_fcrs_ep_map ep tl i2 < app_fcrs_ep_map ep tl i1)))
  = IF.lemma_filter_map_map_monotonic (fm_app_fcrs (fst tl) ep) (snd tl) i1 i2

let app_fcrs_ep_invmap_monotonic (#vspec:_)
  (ep: epoch)
  (tl: verifiable_log vspec)
  (j1 j2: SA.seq_index (app_fcrs_within_ep ep tl))
  : Lemma (ensures ((j1 < j2 ==> app_fcrs_ep_invmap ep tl j1 < app_fcrs_ep_invmap ep tl j2) /\
                    (j2 < j1 ==> app_fcrs_ep_invmap ep tl j2 < app_fcrs_ep_invmap ep tl j1)))
  = IF.filter_map_invmap_monotonic (fm_app_fcrs (fst tl) ep) (snd tl) j1 j2

#push-options "--fuel 0 --ifuel 1 --query_stats"

let rec  find_epoch_boundary (#vspec:_) (ep: epoch) (tl: verifiable_log vspec) (i:seq_index tl)
  : GTot(o:option nat {(None = o ==> (clock tl i).e <= ep) /\
                (Some? o ==> (let j = Some?.v o in
                              j <= i /\
                              (clock tl j).e > ep /\
                              (j = 0 \/ (clock tl (j-1)).e <= ep)))})
    (decreases i)
  = if i = 0 then
      if (clock tl i).e <= ep then None
      else Some i
    else
      let i' = i - 1 in
      let o = find_epoch_boundary ep tl i' in
      if None = o then
        if (clock tl i).e <= ep then None
        else Some i
      else o

let prefix_within_epoch (#vspec:_) (ep: epoch) (tl: verifiable_log vspec)
  : GTot (tl': verifiable_log vspec {tl' `prefix_of` tl})
  = if length tl = 0 then tl
    else
      let o = find_epoch_boundary ep tl (length tl - 1) in
      if o = None then tl
      else
        let j = Some?.v o in
        prefix tl j

let prefix_within_epoch_correct (#vspec:_) (ep: epoch) (tl: verifiable_log vspec) (i: seq_index tl)
  : Lemma (ensures (let tl' = prefix_within_epoch ep tl in
                    let l' = length tl' in
                    (i < l' ==> (clock tl i).e <= ep) /\
                    (i >= l' ==> (clock tl i).e > ep)))
  = let n' = length tl - 1 in
    let o = find_epoch_boundary ep tl n' in
    let tl' = prefix_within_epoch ep tl in
    let l' = length tl' in
    if o = None then
      lemma_clock_monotonic tl i n'
    else (
      assert((clock tl l').e > ep);
      if i >= l' then
        lemma_clock_monotonic tl l' i
      else if l' > 0 then
        lemma_clock_monotonic tl i (l' - 1)
    )

let ep_pre_fcrs (#vspec:_) (ep: epoch) (tl: verifiable_log vspec)
  = let tl' = prefix_within_epoch ep tl in
    app_fcrs tl'

let ep_pre_fcrs2ep_fcrs (#vspec:_) (ep: epoch) (tl: verifiable_log vspec) (i: SA.seq_index (ep_pre_fcrs ep tl))
  : GTot (j: SA.seq_index (app_fcrs_within_ep ep tl) {S.index (ep_pre_fcrs ep tl) i = S.index (app_fcrs_within_ep ep tl) j})
  = let tl' = prefix_within_epoch ep tl in
    let ep_fcrs1 = ep_pre_fcrs ep tl in
    let i1 = app_fcrs_invmap tl' i in
    assert(i1 < length tl');
    assert(is_appfn tl i1);
    prefix_within_epoch_correct ep tl i1;
    assert((clock tl i1).e <= ep);
    assert(is_appfn_within_epoch ep tl i1);
    let i2 = app_fcrs_ep_map ep tl i1 in
    i2

let ep_pre_fcrs2ep_fcrs_mono(#vspec:_) (ep: epoch) (tl: verifiable_log vspec)
  : Lemma (ensures (monotonic_prop (hoist_ghost (ep_pre_fcrs2ep_fcrs ep tl))))
          [SMTPat (ep_pre_fcrs2ep_fcrs ep tl)]
  = let tl' = prefix_within_epoch ep tl in
    let ep_fcrs1 = ep_pre_fcrs ep tl in
    let f = ep_pre_fcrs2ep_fcrs ep tl in
    let aux (i j: SA.seq_index ep_fcrs1)
      : Lemma (ensures (i < j ==> f i < f j))
      = if i < j then (
          let i1 = app_fcrs_invmap tl' i in
          let j1 = app_fcrs_invmap tl' j in
          app_fcrs_invmap_monotonic tl' i j;
          assert(i1 < j1);
          prefix_within_epoch_correct ep tl i1;
          prefix_within_epoch_correct ep tl j1;
          app_fcrs_ep_map_monotonic ep tl i1 j1
        )
    in
    forall_intro_2 aux

let ep_fcrs2ep_pre_fcrs (#vspec:_) (ep: epoch) (tl: verifiable_log vspec)
  (j: SA.seq_index (app_fcrs_within_ep ep tl))
  : GTot (i: SA.seq_index (ep_pre_fcrs ep tl) {S.index (ep_pre_fcrs ep tl) i = S.index (app_fcrs_within_ep ep tl) j})
  = let tl' = prefix_within_epoch ep tl in
    let i1 = app_fcrs_ep_invmap ep tl j in
    prefix_within_epoch_correct ep tl i1;
    assert(i1 < length tl');
    let i = app_fcrs_map tl' i1 in
    i

let ep_fcrs2ep_pre_fcrs_mono (#vspec:_) (ep: epoch) (tl: verifiable_log vspec)
  : Lemma (ensures (monotonic_prop (hoist_ghost (ep_fcrs2ep_pre_fcrs ep tl))))
          [SMTPat (ep_fcrs2ep_pre_fcrs ep tl)]
  = let tl' = prefix_within_epoch ep tl in
    let ep_fcrs = app_fcrs_within_ep ep tl in
    let f = ep_fcrs2ep_pre_fcrs ep tl in
    let aux (i j: SA.seq_index ep_fcrs)
      : Lemma (ensures (i < j ==> f i < f j))
      = if i < j then (
          let i1 = app_fcrs_ep_invmap ep tl i in
          let j1 = app_fcrs_ep_invmap ep tl j in
          app_fcrs_ep_invmap_monotonic ep tl i j;
          assert(i1 < j1);
          prefix_within_epoch_correct ep tl i1;
          prefix_within_epoch_correct ep tl j1;
          app_fcrs_map_monotonic tl' i1 j1
        )
    in
    forall_intro_2 aux

let lemma_app_fcrs_ep_prefix (#vspec:_)
  (ep: epoch)
  (tl: verifiable_log vspec)
  : Lemma (ensures (let tl' = prefix_within_epoch ep tl in
                    app_fcrs tl' == app_fcrs_within_ep ep tl))
  = monotonic_bijection_implies_equal
    (ep_pre_fcrs ep tl)
    (app_fcrs_within_ep ep tl)
    (hoist_ghost (ep_pre_fcrs2ep_fcrs ep tl))
    (hoist_ghost (ep_fcrs2ep_pre_fcrs ep tl))

#pop-options
