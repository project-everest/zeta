module Zeta.Generic.Interleave

open FStar.Classical
module SS = Zeta.SSeq

#push-options "--fuel 0 --ifuel 1 --query_stats"

let apply_per_thread_prefix (#vspec:_) (#n:_) (il: verifiable_log vspec n) (i:nat{i <= length il})
  : Lemma (ensures (let ss = s_seq il in
                    let il' = prefix il i in
                    let ss' = s_seq il' in
                    ss' `SS.sseq_all_prefix_of` ss))
          [SMTPat (prefix il i)]
  = per_thread_prefix il i

let lemma_prefix_verifiable (#vspec:_) (n:_) (il:verifiable_log vspec n) (i:nat{i <= S.length il}):
  Lemma (ensures (verifiable (prefix il i)))
  = let il' = prefix il i in
    let gl' = s_seq il' in
    let gl = s_seq il in
    let aux (t:_)
      : Lemma (ensures (T.verifiable (t, S.index gl' t)))
      = let tl = G.index gl t in
        let tl' = t,S.index gl' t in
        eliminate
        forall tid. (S.index gl' tid) `prefix_of` (S.index gl tid)
        with t;
        T.verifiable_implies_prefix_verifiable tl (T.length tl')
    in
    forall_intro aux

let clock_prefix_prop (#vspec #n:_) (il: verifiable_log vspec n) (i: seq_index il) (j:nat{j <= length il /\ j > i})
  : Lemma (ensures (clock il i = clock (prefix il j) i))
  = ()

//#push-options "--query_stats --debug Zeta.Generic.Interleave --debug_level SMTQuery"
let lemma_cur_thread_state_extend (#vspec: verifier_spec) (#n:_)
  (il: verifiable_log vspec n) (i: seq_index il)
  : Lemma (ensures (let st_pre = cur_thread_state_pre il i in
                    let st_post = cur_thread_state_post il i in
                    st_post == V.verify_step (I.index il i) st_pre))
  = let gl = to_glog il in
    let il_post = prefix il (i+1) in
    interleaving_snoc il_post;
    let t,j = i2s_map il i in
    let tl = G.index gl t in
    T.lemma_state_transition tl j
//#pop-options

let lemma_non_cur_thread_state_extend (#vspec: verifier_spec) (#n:_) (tid: nat{tid < n})
  (il: verifiable_log vspec n) (i: seq_index il)
  : Lemma (requires (tid <> src il i))
          (ensures (let st_pre = thread_state_pre tid il i in
                    let st_post = thread_state_post tid il i in
                    st_pre == st_post))
  = let gl = to_glog il in
    let il_post = prefix il (i+1) in
    interleaving_snoc il_post

let lemma_thread_state_prefix (#vspec: verifier_spec) (#n:_)
  (il: verifiable_log vspec n) (i:seq_index il)
  : Lemma (ensures (let t,j = i2s_map il i in
                    let tl = G.index (to_glog il) t in
                    cur_thread_state_pre il i == T.state_pre tl j))
  = let gl = to_glog il in
    let il_post = prefix il (i+1) in
    interleaving_snoc il_post;
    let t,j = i2s_map il i in
    let tl = G.index gl t in
    T.lemma_state_transition tl j

let is_blum_add_prefix_prop
  (#vspec #n:_)
  (il: verifiable_log vspec n)
  (i: seq_index il)
  (j:nat{j <= length il /\ j > i})
  : Lemma (ensures (is_blum_add il i = is_blum_add (prefix il j) i))
  = ()

let blum_add_elem_prefix_prop
  (#vspec #n:_)
  (il: verifiable_log vspec n)
  (i: seq_index il{is_blum_add il i})
  (j:nat{j <= length il /\ j > i})
  : Lemma (ensures (blum_add_elem il i = blum_add_elem (prefix il j) i))
  = ()

let blum_evict_elem_prefix_prop
  (#vspec #n:_)
  (il: verifiable_log vspec n)
  (i: seq_index il{is_blum_evict il i})
  (j:nat{j <= length il /\ j > i})
  : Lemma (ensures (blum_evict_elem il i = blum_evict_elem (prefix il j) i))
  = ()

module IF = Zeta.IdxFn

let gen_seq (vspec n:_) = {
  IF.seq_t = verifiable_log vspec n;
  IF.length = length;
  IF.prefix = prefix;
  }

let is_appfn_ifn (#vspec #n:_)
  : IF.idxfn_t (gen_seq vspec n) bool
  = is_appfn #vspec #n

let to_app_fcr_src (#vspec #n:_) (il: verifiable_log vspec n) (i: seq_index il{is_appfn il i})
  : elem_src (appfn_call_res vspec.app) n
  = let e = to_app_fcr il i in
    let s = src il i in
    {e;s}

let to_app_fcr_src_ifn (#vspec #n:_)
  : IF.cond_idxfn_t (elem_src (appfn_call_res vspec.app) n) (is_appfn_ifn #vspec #n)
  = to_app_fcr_src #vspec #n

let app_fcrs_il (#vspec: verifier_spec) (#n:_) (il: verifiable_log vspec n)
  : interleaving (Zeta.AppSimulate.appfn_call_res vspec.app) n
  = let fm = IF.to_fm (is_appfn_ifn #vspec #n) (to_app_fcr_src_ifn #vspec #n) in
    IF.filter_map fm il

let lemma_app_fcrs_interleave (#app #n:_) (il: verifiable_log app n)
  : Lemma (ensures (let fcrs_il = app_fcrs_il il in
                    let gl = to_glog il in
                    s_seq fcrs_il = G.app_fcrs gl))
  = admit()

let app_fcrs_empty (#app #n:_) (il: verifiable_log app n)
  : Lemma (ensures (length il = 0 ==> S.length (app_fcrs il) = 0))
  = admit()

let appfn_calls_snoc (#app #n:_) (il: verifiable_log app n {length il > 0})
  : Lemma (ensures (let i = length il - 1 in
                    let e = index il i in
                    let il' = prefix il i in
                    let cr = app_fcrs il in
                    let cr' = app_fcrs il' in
                    match e with
                    | RunApp _ _ _ -> cr == SA.append1 cr' (to_app_fcr il i)
                    | _ -> cr == cr'))
  = admit()
