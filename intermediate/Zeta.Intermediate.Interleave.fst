module Zeta.Intermediate.Interleave

open FStar.Classical

module S = FStar.Seq
module SS = Zeta.SSeq
module GT = Zeta.Generic.Thread
module GV = Zeta.GenericVerifier

let lemma_slot_is_merkle_points_to (#vcfg:_) (il: verifiable_log vcfg) (i: seq_index il):
  Lemma (ensures (slot_points_to_is_merkle_points_to (thread_store_pre (src il i) il i)))
  = let open Zeta.Intermediate.Thread in
    let t = src il i in
    let il' = prefix il i in
    let gl' = to_glog il' in
    let tl' = GG.index gl' t in
    lemma_slot_is_merkle_points_to tl'

let to_logk_src (#vcfg:_) (il: verifiable_log vcfg) (i: seq_index il)
  : GTot (elem_src (logK_entry vcfg.app) vcfg.thread_count)
  = let e = to_logk_entry il i in
    let s = src il i in
    {e; s}

let to_logk (#vcfg:_) (il: verifiable_log vcfg)
  = init (length il) (GV.hoist_ghost (to_logk_src il))

let lemma_to_logk_length (#vcfg:_) (il: verifiable_log vcfg)
  : Lemma (ensures (length il = length (to_logk il)))
  = ()

let lemma_to_logk_src (#vcfg:_) (il: verifiable_log vcfg) (i: seq_index il)
  : Lemma (ensures src il i == src (to_logk il) i)
  = ()

let lemma_to_logk_index (#vcfg:_) (ils: verifiable_log vcfg) (i: seq_index ils)
  : Lemma (ensures (index (to_logk ils) i == to_logk_entry ils i))
  = ()

let apply_per_thread_prefix (#vcfg:_) (il: verifiable_log vcfg) (i:nat{i <= length il})
  : Lemma (ensures (let ss = s_seq il in
                    let il' = prefix il i in
                    let ss' = s_seq il' in
                    ss' `SS.sseq_all_prefix_of` ss))
          [SMTPat (prefix il i)]
  = per_thread_prefix il i

let to_logk_entry_pp (#vcfg:_) (il: verifiable_log vcfg) (l:nat{l <= length il}) (i:nat{i < l})
  : Lemma (ensures (let il' = prefix il l in
                    to_logk_entry il i = to_logk_entry il' i))
  = ()

let lemma_to_logk_prefix_commute (#vcfg:_)
  (il:verifiable_log vcfg)
  (i:nat{i <= length il})
  : Lemma (to_logk (prefix il i) == SA.prefix (to_logk il) i)
  = let il' = prefix il i in
    let ilk1 = to_logk il' in
    let ilk = to_logk il in
    let ilk2 = SA.prefix ilk i in
    assert(length ilk1 = length ilk2);
    let aux (j:_)
      : Lemma (ensures (S.index ilk1 j = S.index ilk2 j))
      = to_logk_entry_pp il i j
    in
    forall_intro aux;
    assert(S.equal ilk1 ilk2)

(* every store of every prefix of every thread is a map *)
let forall_store_ismap (#vcfg:_) (il: verifiable_log vcfg): prop
  = forall t. is_map (thread_store t il) /\
    (forall l t. is_map (thread_store_pre t il l))

let elim_forall_store_ismap_aux (#vcfg:_) (il: verifiable_log vcfg) (t:nat{t < vcfg.thread_count})
  : Lemma (requires (forall_store_ismap il))
          (ensures (let st = thread_store t il in
                             is_map st))
  = eliminate forall t. is_map (thread_store t il)
    with t

let elim_forall_store_ismap (#vcfg:_) (il: verifiable_log vcfg) (t:nat{t < vcfg.thread_count})
  : Lemma (ensures (forall_store_ismap il ==> (let st = thread_store t il in
                                               is_map st)))
  = introduce forall_store_ismap il ==> (let st = thread_store t il in is_map st)
    with _. (elim_forall_store_ismap_aux il t)

let forall_store_ismap_prefix_aux (#vcfg:_) (il: verifiable_log vcfg) (l:nat{l <= length il})
  : Lemma (requires (forall_store_ismap il))
          (ensures (let il' = prefix il l in
                    forall_store_ismap il'))
  = let il' = prefix il l in
    let aux (t:_)
      : Lemma (ensures (is_map (thread_store t il')))
      = if l < length il then
          eliminate forall l t. is_map (thread_store_pre t il l)
          with l t
    in
    forall_intro aux;
    let aux (l t:_)
      : Lemma (ensures (is_map (thread_store_pre t il' l)))
      = eliminate forall l t. is_map (thread_store_pre t il l)
        with l t
    in
    forall_intro_2 aux

let forall_store_ismap_prefix (#vcfg:_) (il: verifiable_log vcfg) (l:nat{l <= length il})
  : Lemma (ensures (forall_store_ismap il ==> (let il' = prefix il l in
                                               forall_store_ismap il')))
  = introduce forall_store_ismap il ==> (let il' = prefix il l in forall_store_ismap il')
    with _. (forall_store_ismap_prefix_aux il l)

#push-options "--fuel 0 --ifuel 1 --query_stats"

let lemma_forall_store_ismap_snoc (#vcfg:_) (il: verifiable_log vcfg{length il > 0})
  : Lemma (requires (let i = length il - 1 in
                     let il' = prefix il i in
                     let t = src il i in
                     forall_store_ismap il' /\
                     is_map (thread_store t il)))
          (ensures forall_store_ismap il)
  = let i = length il - 1 in
    let il' = prefix il i in
    let t = src il i in
    let aux (t':_)
      : Lemma (ensures (is_map (thread_store t' il)))
      = if t' <> t then
          lemma_non_cur_thread_state_extend t' il i
    in
    forall_intro aux;
    let aux (l t':_)
      : Lemma (ensures (is_map (thread_store_pre t' il l)))
      = if l = i then
          elim_forall_store_ismap il' t'
        else (
          let il_l = prefix il l in
          forall_store_ismap_prefix_aux il' l;
          lemma_prefix_prefix_property il i l;
          elim_forall_store_ismap il_l t'
        )
    in
    forall_intro_2 aux

#pop-options

let forall_vtls_rel_base (#vcfg:_) (il: verifiable_log vcfg)
  = let ilk = to_logk il in
    forall t. (let vss = thread_state t il in
          let vsk = thread_state t ilk in
          vtls_rel vss vsk)

(* every state of every prefix is related to high-level state *)
let forall_vtls_rel (#vcfg:_) (il: verifiable_log vcfg): prop
  = forall_vtls_rel_base il /\
    (forall l. forall_vtls_rel_base (prefix il l))

let elim_forall_vtls_rel_aux (#vcfg:_) (il: verifiable_log vcfg) (t: nat{t < vcfg.thread_count})
  : Lemma (requires (forall_vtls_rel il))
          (ensures (let ilk = to_logk il in
                    let vsi = thread_state t il in
                    let vst = thread_state t ilk in
                    vtls_rel vsi vst))
  = let ilk = to_logk il in
    eliminate
    forall t. (let vss = thread_state t il in
          let vsk = thread_state t ilk in
          vtls_rel vss vsk)
    with t

let elim_forall_vtls_rel (#vcfg:_) (il: verifiable_log vcfg) (t: nat{t < vcfg.thread_count})
  : Lemma (requires (forall_vtls_rel il))
          (ensures (let ilk = to_logk il in
                    let vsi = thread_state t il in
                    let vst = thread_state t ilk in
                    vtls_rel vsi vst))
  = elim_forall_vtls_rel_aux il t

let forall_vtls_rel_prefix_aux (#vcfg:_) (il: verifiable_log vcfg) (i:nat{i <= length il})
  : Lemma (requires (forall_vtls_rel il))
          (ensures (let il' = prefix il i in
                    forall_vtls_rel il'))
  = let il' = prefix il i in
    eliminate forall l. forall_vtls_rel_base (prefix il l)
    with i;
    let aux (l:_)
      : Lemma (ensures (forall_vtls_rel_base (prefix il' l)))
      = eliminate forall l. forall_vtls_rel_base (prefix il l)
        with l;
        lemma_prefix_prefix_property il i l
    in
    forall_intro aux

let forall_vtls_rel_prefix (#vcfg:_) (il: verifiable_log vcfg) (i:nat{i <= length il})
  : Lemma (ensures (let il' = prefix il i in
                    forall_vtls_rel il ==> forall_vtls_rel il'))
  = let il' = prefix il i in
    introduce forall_vtls_rel il ==> forall_vtls_rel il'
    with _. (forall_vtls_rel_prefix_aux il i)

#push-options "--fuel 0 --ifuel 1 --query_stats"

let forall_vtls_rel_snoc (#vcfg:_) (il: verifiable_log vcfg{length il > 0})
  : Lemma (requires (let i = length il - 1 in
                     let il' = prefix il i in
                     let ilk = to_logk il in
                     let t = src il i in
                     forall_vtls_rel il' /\
                     vtls_rel (thread_state t il) (thread_state t ilk)))
          (ensures (forall_vtls_rel il))
  = let i = length il - 1 in
    let il' = prefix il i in
    let t = src il i in
    let ilk = to_logk il in
    let aux (t':_)
      : Lemma (ensures (vtls_rel (thread_state t' il) (thread_state t' ilk)))
      = if t' <> t then (
          lemma_non_cur_thread_state_extend t' il i;
          lemma_non_cur_thread_state_extend t' ilk i
        )
    in
    forall_intro aux;
    assert(forall_vtls_rel_base il);
    let aux (l:_)
      : Lemma (ensures (forall_vtls_rel_base (prefix il l)))
      = if l = length il then ()
        else (
          eliminate forall l. forall_vtls_rel_base (prefix il' l)
          with l;
          lemma_prefix_prefix_property il i l
        )
    in
    forall_intro aux

#pop-options

let lemma_forall_vtls_rel_implies_spec_verifiable_aux (#vcfg:_) (il: verifiable_log vcfg)
  : Lemma (requires (forall_vtls_rel il))
          (ensures (let ilk = to_logk il in
                    GI.verifiable ilk))
  = let ilk = to_logk il in
    let glk = s_seq ilk in
    let aux (t:_)
      : Lemma (ensures (let tl = t,S.index glk t in
                        GT.verifiable tl))
      = elim_forall_vtls_rel_aux il t
    in
    forall_intro aux

(* vtls_rel implies every high-level thread is valid, so (to_logk il) is verifiable *)
let lemma_forall_vtls_rel_implies_spec_verifiable (#vcfg:_) (il: verifiable_log vcfg)
  : Lemma (ensures (let ilk = to_logk il in
                    forall_vtls_rel il ==> GI.verifiable (to_logk il)))
  = let ilk = to_logk il in
    introduce
    forall_vtls_rel il ==> GI.verifiable (to_logk il)
    with _. (lemma_forall_vtls_rel_implies_spec_verifiable_aux il)

module IT = Zeta.Intermediate.Thread
module GT = Zeta.Generic.Thread
module HV = Zeta.High.Verifier

let lemma_empty_implies_ismap (#vcfg:_) (il: verifiable_log vcfg)
  : Lemma (ensures (length il = 0 ==> forall_store_ismap il))
  = let gl = to_glog il in
    if length il = 0 then (
      lemma_length0_implies_empty il;
      let aux (t:_)
        : Lemma (ensures (is_map (thread_store t il)))
        = let tl = GG.index gl t in
          lemma_empty_sseq (logS_entry vcfg) vcfg.thread_count t;
          IT.empty_log_is_map tl
      in
      forall_intro aux
    )

let lemma_empty_implies_forall_vtls_rel (#vcfg:_) (il: verifiable_log vcfg)
  : Lemma (ensures (length il = 0 ==> forall_vtls_rel il))
  = let gl = to_glog il in
    let ilk = to_logk il in
    let glk = s_seq ilk in
    if length il = 0 then (
      lemma_length0_implies_empty il;
      lemma_length0_implies_empty ilk;
      let aux (t:_)
        : Lemma (ensures (let vss = thread_state t il in
                          let vsk = thread_state t ilk in
                          vtls_rel vss vsk))
        = lemma_empty_sseq (logS_entry vcfg) vcfg.thread_count t;
          lemma_empty_sseq (logK_entry vcfg.app) vcfg.thread_count t;
          lemma_empty_vtls_rel #vcfg t
      in
      forall_intro aux
    )

let lemma_empty_implies_spec_rel (#vcfg:_) (il:verifiable_log vcfg)
  : Lemma (ensures (length il = 0 ==> spec_rel il))
  = lemma_empty_implies_ismap il;
    lemma_empty_implies_forall_vtls_rel il

let lemma_spec_rel_implies_prefix_spec_rel (#vcfg:_) (il:verifiable_log vcfg) (i:nat{i <= length il})
 : Lemma (requires spec_rel il)
         (ensures (let il' = prefix il i in
                   spec_rel il'))
  = forall_vtls_rel_prefix il i;
    forall_store_ismap_prefix il i

#push-options "--fuel 0 --ifuel 1 --query_stats"

let rec lemma_same_shape (#vcfg:_) (il: verifiable_log vcfg) (t:nat{t < vcfg.thread_count})
  : Lemma (ensures (let ilk = to_logk il in
                    let ss = S.index (s_seq il) t in
                    let sk = S.index (s_seq ilk) t in
                    S.length ss = S.length sk))
          (decreases (length il))
  = let ilk = to_logk il in
    if length il = 0 then (
      lemma_length0_implies_empty il;
      lemma_length0_implies_empty ilk;
      lemma_empty_sseq (logS_entry vcfg) vcfg.thread_count t;
      lemma_empty_sseq (logK_entry vcfg.app) vcfg.thread_count t
    )
    else (
      let i = length il - 1 in
      let il' = prefix il i in
      lemma_same_shape il' t;
      interleaving_snoc il;
      interleaving_snoc ilk
    )

let rec lemma_to_logk_i2smap (#vcfg:_) (ils: verifiable_log vcfg) (i: seq_index ils)
  : Lemma (ensures (let ilk = to_logk ils in
                    i2s_map ils i = i2s_map ilk i))
          (decreases (length ils))
  = let n' = length ils - 1 in
    let t = src ils n' in
    let ils' = prefix ils n' in
    let ilk = to_logk ils in

    if i < n' then (
      lemma_to_logk_i2smap ils' i;
      lemma_i2s_prefix_property ils n' i;
      lemma_i2s_prefix_property ilk n' i
    )
    else (
      interleaving_snoc ils;
      interleaving_snoc ilk;
      lemma_same_shape ils' t
    )

#pop-options

module IG = Zeta.Intermediate.Global

#push-options "--fuel 1 --ifuel 1 --query_stats"

let lemma_spec_rel_implies_thread_rel (#vcfg:_) (il: verifiable_log vcfg {spec_rel il}) (t:nat{t < vcfg.thread_count})
  : Lemma (ensures (let gls = to_glog il in
                    let ilk = to_logk il in
                    let glk = to_glog ilk in
                    let tls = GG.index gls t in
                    let tlk = GG.index glk t in
                    IT.thread_rel tls tlk))
  = let gls = to_glog il in
    let ilk = to_logk il in
    let glk = to_glog ilk in
    let tls = GG.index gls t in
    let tlk = GG.index glk t in

    lemma_same_shape il t;
    assert(GT.length tls = GT.length tlk);

    elim_forall_vtls_rel il t;
    assert(vtls_rel (thread_state t il) (thread_state t ilk));
    assert(GT.state tls == thread_state t il);
    assert(GT.state tlk == thread_state t ilk);

    let aux (j:_)
      : Lemma (ensures (vtls_rel (GT.state_pre tls j) (GT.state_pre tlk j)))
      = let i = s2i_map il (t,j) in
        assert(i2s_map il i = (t,j));
        lemma_to_logk_i2smap il i;
        assert(i2s_map ilk i = (t,j));
        lemma_thread_state_prefix il i;
        assert(GT.state_pre tls j == thread_state_pre t il i);
        lemma_thread_state_prefix ilk i;
        assert(GT.state_pre tlk j == thread_state_pre t ilk i);
        forall_vtls_rel_prefix il i;
        let il' = prefix il i in
        assert(forall_vtls_rel il');
        elim_forall_vtls_rel il' t
    in
    forall_intro aux;

    let aux (j:_)
      : Lemma (ensures (GT.index tlk j = IT.to_logk_entry tls j))
      = let i = s2i_map il (t,j) in
        assert(i2s_map il i = (t,j));
        lemma_to_logk_i2smap il i;
        ()
    in
    forall_intro aux

#pop-options

let lemma_spec_rel_implies_global_rel (#vcfg:_) (il: verifiable_log vcfg {spec_rel il})
  : Lemma (ensures (let gls = to_glog il in
                    let ilk = to_logk il in
                    let glk = to_glog ilk in
                    IG.global_rel gls glk))
  = let gls = to_glog il in
    let ilk = to_logk il in
    let glk = to_glog ilk in
    assert(S.length gls = S.length glk);
    let aux (t:_)
      : Lemma (ensures (IT.thread_rel (GG.index gls t) (GG.index glk t)))
      = lemma_spec_rel_implies_thread_rel il t
    in
    forall_intro aux

let lemma_spec_rel_implies_appfn_identical (#vcfg:_) (il: verifiable_log vcfg {spec_rel il})
  : Lemma (ensures (let gl = to_glog il in
                    let ilk = to_logk il in
                    let glk = to_glog ilk in
                    GG.app_fcrs gl = GG.app_fcrs glk))
  = lemma_spec_rel_implies_global_rel il;
    let gls = to_glog il in
    let glk = to_glog (to_logk il) in
    IG.global_rel_implies_appfn_identical gls glk


#push-options "--fuel 0 --ifuel 1 --query_stats"

let lemma_vtls_rel_implies_same_clock (#vcfg:_) (ils: verifiable_log vcfg) (i: seq_index ils)
  : Lemma (requires (forall_vtls_rel ils))
          (ensures (let ilk = to_logk ils in
                    clock ils i = clock ilk i))
  = let t = src ils i in
    let ils_ = prefix ils (i+1) in
    interleaving_snoc ils_;
    let vss_ = thread_state_post t ils i in
    assert(clock ils i = vss_.clock);


    let ilk = to_logk ils in
    let ilk_ = prefix ilk (i+1) in
    interleaving_snoc ilk_;
    let vsk_:HV.vtls_t vcfg.app = thread_state_post t ilk i in
    per_thread_prefix ilk (i+1);
    assert(clock ilk i = vsk_.clock);

    ()

#pop-options
