module Zeta.Generic.Interleave

let lemma_prefix_verifiable (#vspec:_) (n:_) (il:verifiable_log vspec n) (i:nat{i <= S.length il}):
  Lemma (ensures (verifiable (I.prefix il i)))
  = admit()

//#push-options "--query_stats --debug Zeta.Generic.Interleave --debug_level SMTQuery"
let lemma_cur_thread_state_extend (#vspec: verifier_spec) (#n:_)
  (il: verifiable_log vspec n) (i: seq_index il)
  : Lemma (ensures (let st_pre = cur_thread_state_pre il i in
                    let st_post = cur_thread_state_post il i in
                    st_post == V.verify_step (I.index il i) st_pre))
  = admit()

//#pop-options
let lemma_non_cur_thread_state_extend (#vspec: verifier_spec) (#n:_) (tid: nat{tid < n})
  (il: verifiable_log vspec n) (i: seq_index il)
  : Lemma (requires (tid <> src il i))
          (ensures (let st_pre = thread_state_pre tid il i in
                    let st_post = thread_state_post tid il i in
                    st_pre == st_post))
  = admit()

let appfn_calls_il (#vspec: verifier_spec) (#n:_) (il: verifiable_log vspec n)
  : interleaving (Zeta.AppSimulate.appfn_call_res vspec.app) n
  = admit()

(*
let idxfn_base #vspec #n #b (tfn: T.idxfn_t vspec b)
  (il: verifiable_log vspec n) (i: seq_index il)
  : b
  = G.idxfn #vspec tfn (to_glog il) (i2s_map il i)

val idxn_has_prefix_prop (#vspec:_) (#n:nat) (#b:_) (tfn: T.idxfn_t vspec b)
  : Lemma (ensures (IF.prefix_property #(gen_seq vspec n) (idxfn_base #_ #n #_ tfn)))
          [SMTPat (idxfn_base #_ #n #_ tfn)]

let idxfn #b #vspec #n (tfn: T.idxfn_t vspec b)
  : IF.idxfn_t (gen_seq vspec n) _
  = idxfn_base tfn

let idxfn_il_base #vspec #n (#b:eqtype) (tfn: T.idxfn_t vspec b)
  (il: verifiable_log vspec n) (i: seq_index il)
  : elem_src b n
  = {e = idxfn tfn il i; s = src il i}

let idxfn_il (#b:eqtype) #vspec #n (tfn: T.idxfn_t vspec b)
  : IF.idxfn_t (gen_seq vspec n) _
  = idxfn_il_base tfn

(* this should be =() proof but does not work since some pattern matching does not kick-in *)
val idxfn_prefix_property (#vspec:_) (#n:_) (#b:_) (tfn: T.idxfn_t vspec b)
  (il: verifiable_log vspec n) (j:nat{j <= S.length il}) (i: nat{i < j})
  : Lemma (ensures (idxfn tfn il i == idxfn tfn (prefix il j) i))
          [SMTPat (idxfn tfn (prefix il j) i)]

val idxfnil_prefix_property (#vspec:_) (#n:_) (#b:eqtype) (tfn: T.idxfn_t vspec b)
  (il: verifiable_log vspec n) (j:nat{j <= S.length il}) (i: nat{i < j})
  : Lemma (ensures (idxfn_il tfn il i == idxfn_il tfn (prefix il j) i))
          [SMTPat (idxfn_il tfn (prefix il j) i)]

let cond_idxfn_base #vspec #n #b #f (m: T.cond_idxfn_t b f)
  (il: verifiable_log vspec n) (i: seq_index il{idxfn f il i})
  = G.cond_idxfn m (to_glog il) (i2s_map il i)

val cond_idxfn_has_prefix_prop (#vspec #n #b #f:_) (m: T.cond_idxfn_t b f)
  : Lemma (ensures (IF.cond_prefix_property #(gen_seq vspec n) #_ #(idxfn f) (cond_idxfn_base m)))
          [SMTPat (cond_idxfn_base #vspec #n #b #f m)]

let cond_idxfn (#vspec #n #b #f:_) (m: T.cond_idxfn_t b f)
  : IF.cond_idxfn_t b (idxfn f)
  = cond_idxfn_base #vspec #n m

let cond_idxfn_il_base #vspec #n (#b:eqtype) #f (m: T.cond_idxfn_t b f)
  (il: verifiable_log vspec n) (i: seq_index il{idxfn f il i})
  : elem_src b n
  = {e = cond_idxfn m il i; s = src il i}

let cond_idxfn_il #vspec #n (#b:eqtype) #f (m: T.cond_idxfn_t b f)
  : IF.cond_idxfn_t (elem_src b n) (idxfn f)
  = cond_idxfn_il_base #vspec #n #b #f m

val lemma_cond_idxfn (#vspec #n:_) (#b: eqtype) (f:_) (m: T.cond_idxfn_t b f)
  (il: verifiable_log vspec n)
  : Lemma (ensures (let fm_il = to_fm (idxfn f) (cond_idxfn_il #vspec #n #_ #_ m) in
                    let ilb = IF.filter_map fm_il il in
                    let fm_s = to_fm (idxfn f) (cond_idxfn #vspec #n #_ #_ m) in
                    let sb = IF.filter_map fm_s il in
                    sb = i_seq ilb))

val lemma_filter_map (#vspec #n:_) (#b:eqtype) (#f:_) (m: T.cond_idxfn_t b f)
    (il: verifiable_log vspec n) (i: seq_index il)
  : Lemma (ensures (let fmil = to_fm (idxfn f) (cond_idxfn_il #vspec #n #_ #_ m) in
                    let ilb = IF.filter_map fmil il in
                    let fm = to_fm f m in
                    let ssb = SF.filter_map (G.gen_sseq vspec) fm (to_glog il) in
                    ssb = s_seq ilb))

val lemma_cond_idxfn_interleave (#vspec #n:_) (#b: eqtype) (#f:_) (m: T.cond_idxfn_t b f)
  (il: verifiable_log vspec n)
  : Lemma (ensures (let fm_s = to_fm (idxfn f) (cond_idxfn #vspec #n #_ #_ m) in
                    let sb = IF.filter_map fm_s il in
                    let fm = to_fm f m in
                    let ssb = SF.filter_map (G.gen_sseq vspec) fm (to_glog il) in
                    I.interleave #b sb ssb))
*)
