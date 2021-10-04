module Zeta.Generic.Interleave

open FStar.Classical
open Zeta.SMap
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
        forall tid. (S.index gl' tid) `SA.prefix_of` (S.index gl tid)
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

let t_fcrs_il (#vspec #n:_) (il: verifiable_log vspec n) (t:nat{t < n})
  = let fcrs = app_fcrs_il il in
    let ss = s_seq fcrs in
    S.index ss t

let t_fcrs_gl (#vspec #n:_) (il: verifiable_log vspec n) (t:nat{t < n})
  = let gl = to_glog il in
    let tl = G.index gl t in
    T.app_fcrs tl

let t_fcrs_i2g (#vspec #n:_) (il: verifiable_log vspec n) (t:nat{t < n})
  (i: SA.seq_index (t_fcrs_il il t))
  :j:SA.seq_index (t_fcrs_gl il t){S.index (t_fcrs_il il t) i = S.index (t_fcrs_gl il t) j}
  = let tfcrs_il = t_fcrs_il il t in
    let tfcrs_gl = t_fcrs_gl il t in
    let fm = IF.to_fm (is_appfn_ifn #vspec #n) (to_app_fcr_src_ifn #vspec #n) in
    let fcrs_il = app_fcrs_il il in
    let gl = to_glog il in
    let tl = G.index gl t in

    let i1 = s2i_map fcrs_il (t,i) in
    let i2 = IF.filter_map_invmap fm il i1 in
    let _,i3 = i2s_map il i2 in
    T.app_fcrs_map tl i3

let t_fcrs_i2g_mono (#vspec #n:_) (il: verifiable_log vspec n) (t:nat{t < n})
  : Lemma (ensures (monotonic_prop (t_fcrs_i2g il t)))
          [SMTPat (t_fcrs_i2g il t)]
  = let tfcrs_il = t_fcrs_il il t in
    let tfcrs_gl = t_fcrs_gl il t in
    let fm = IF.to_fm (is_appfn_ifn #vspec #n) (to_app_fcr_src_ifn #vspec #n) in
    let fcrs_il = app_fcrs_il il in
    let gl = to_glog il in
    let tl = G.index gl t in

    let f = t_fcrs_i2g il t in

    let aux (i j: SA.seq_index tfcrs_il)
      : Lemma (ensures (i < j ==> f i < f j))
      = if i < j then (
          let i1 = s2i_map fcrs_il (t,i) in
          let j1 = s2i_map fcrs_il (t,j) in
          s2i_map_monotonic fcrs_il (t,i) (t,j);
          assert(i1 < j1);

          let i2 = IF.filter_map_invmap fm il i1 in
          let j2 = IF.filter_map_invmap fm il j1 in
          IF.filter_map_invmap_monotonic fm il i1 j1;
          assert(i2 < j2);

          let _,i3 = i2s_map il i2 in
          let _,j3 = i2s_map il j2 in
          i2s_map_monotonic il i2 j2;
          assert(i3 < j3);

          T.app_fcrs_map_monotonic tl i3 j3
        )
    in
    forall_intro_2 aux

let t_fcrs_g2i (#vspec #n:_) (il: verifiable_log vspec n) (t:nat{t < n})
  (j: SA.seq_index (t_fcrs_gl il t))
  : i:SA.seq_index (t_fcrs_il il t){S.index (t_fcrs_il il t) i = S.index (t_fcrs_gl il t) j}
  = let tfcrs_il = t_fcrs_il il t in
    let tfcrs_gl = t_fcrs_gl il t in
    let fm = IF.to_fm (is_appfn_ifn #vspec #n) (to_app_fcr_src_ifn #vspec #n) in
    let fcrs_il = app_fcrs_il il in
    let gl = to_glog il in
    let tl = G.index gl t in
    let j1 = T.app_fcrs_invmap tl j in
    let j2 = s2i_map il (t,j1) in
    let j3 = IF.filter_map_map fm il j2 in
    let _,j4 = i2s_map fcrs_il j3 in
    j4

let t_fcrs_g2i_mono (#vspec #n:_) (il: verifiable_log vspec n) (t:nat{t < n})
  : Lemma (ensures (monotonic_prop (t_fcrs_g2i il t)))
  = let tfcrs_il = t_fcrs_il il t in
    let tfcrs_gl = t_fcrs_gl il t in
    let fm = IF.to_fm (is_appfn_ifn #vspec #n) (to_app_fcr_src_ifn #vspec #n) in
    let fcrs_il = app_fcrs_il il in
    let gl = to_glog il in
    let tl = G.index gl t in

    let f = t_fcrs_g2i il t in
    let aux (i j: SA.seq_index tfcrs_gl)
      : Lemma (ensures (i < j ==> f i < f j))
      = if i < j then (
          let i1 = T.app_fcrs_invmap tl i in
          let j1 = T.app_fcrs_invmap tl j in
          T.app_fcrs_invmap_monotonic tl i j;
          assert(i1 < j1);

          let i2 = s2i_map il (t,i1) in
          let j2 = s2i_map il (t,j1) in
          s2i_map_monotonic il (t,i1) (t,j1);
          assert(i2 < j2);

          let i3 = IF.filter_map_map fm il i2 in
          let j3 = IF.filter_map_map fm il j2 in
          IF.lemma_filter_map_map_monotonic fm il i2 j2;
          assert(i3 < j3);

          i2s_map_monotonic fcrs_il i3 j3
        )
    in
    forall_intro_2 aux

#push-options "--z3rlimit_factor 3"

let fcrs_identical_thread (#vspec #n:_) (il: verifiable_log vspec n) (t: nat{t < n})
  : Lemma (ensures (t_fcrs_il il t == t_fcrs_gl il t))
   = monotonic_bijection_implies_equal
      (t_fcrs_il il t)
      (t_fcrs_gl il t)
      (t_fcrs_i2g il t)
      (t_fcrs_g2i il t)

#pop-options

let lemma_app_fcrs_interleave (#vspec #n:_) (il: verifiable_log vspec n)
  : Lemma (ensures (let fcrs_il = app_fcrs_il il in
                    let gl = to_glog il in
                    s_seq fcrs_il = G.app_fcrs gl))
  = let fcrs_il = app_fcrs_il il in
    let gl = to_glog il in
    let ss1 = s_seq fcrs_il in
    let ss2 = G.app_fcrs gl in
    let aux (t:_)
      : Lemma (ensures (S.index ss1 t = S.index ss2 t))
      = fcrs_identical_thread il t
    in
    forall_intro aux;
    assert(S.equal ss1 ss2)

let app_fcrs_empty (#app #n:_) (il: verifiable_log app n)
  : Lemma (ensures (length il = 0 ==> S.length (app_fcrs il) = 0))
  = ()

let appfn_calls_snoc (#vspec #n:_) (il: verifiable_log vspec n {length il > 0})
  : Lemma (ensures (let i = length il - 1 in
                    let e = index il i in
                    let il' = prefix il i in
                    let cr = app_fcrs il in
                    let cr' = app_fcrs il' in
                    match e with
                    | RunApp _ _ _ -> cr == SA.append1 cr' (to_app_fcr il i)
                    | _ -> cr == cr'))
  = let fm = IF.to_fm (is_appfn_ifn #vspec #n) (to_app_fcr_src_ifn #vspec #n) in
    IF.lemma_filter_map_snoc fm il;
    let i = length il - 1 in
    let e = index il i in
    let il' = prefix il i in
    let fcrs'_il = app_fcrs_il il' in
    match e with
    | RunApp _ _ _ ->
      lemma_iseq_append1 fcrs'_il (fm.m il i)
    | _ -> ()
