module Zeta.Intermediate.Interleave

open FStar.Classical

let lemma_slot_is_merkle_points_to (#vcfg:_) (il: verifiable_log vcfg) (i: seq_index il):
  Lemma (ensures (slot_points_to_is_merkle_points_to (thread_store_pre (src il i) il i)))
  = let open Zeta.Intermediate.Thread in
    let t = src il i in
    let il' = prefix il i in
    let gl' = to_glog il' in
    let tl' = GG.index gl' t in
    lemma_slot_is_merkle_points_to tl'

let to_logk_src (#vcfg:_) (il: verifiable_log vcfg) (i: seq_index il)
  : elem_src (logK_entry vcfg.app) vcfg.thread_count
  = let e = to_logk_entry il i in
    let s = src il i in
    {e; s}

(* TODO: Odd, how did F* figure out the same_shape part? *)
let to_logk (#vcfg:_) (il: verifiable_log vcfg)
  : hil:HI.ilog vcfg.app vcfg.thread_count {same_shape il hil}
  = init (length il) (to_logk_src il)

let lemma_to_logk_length (#vcfg:_) (il: verifiable_log vcfg)
  : Lemma (ensures (length il = length (to_logk il)))
  = ()

let lemma_to_logk_src (#vcfg:_) (il: verifiable_log vcfg) (i: seq_index il)
  : Lemma (ensures src il i == src (to_logk il) i)
  = ()

let lemma_to_logk_index (#vcfg:_) (ils: verifiable_log vcfg) (i: seq_index ils)
  : Lemma (ensures (index (to_logk ils) i == to_logk_entry ils i))
  = ()

module S = FStar.Seq
module SS = Zeta.SSeq

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

(* vtls_rel implies every high-level thread is valid, so (to_logk il) is verifiable *)
let lemma_forall_vtls_rel_implies_spec_verifiable (#vcfg:_) (il: verifiable_log vcfg)
  : Lemma (ensures (let ilk = to_logk il in
                    forall_vtls_rel il ==> GI.verifiable (to_logk il)))
  = admit()

let elim_forall_vtls_rel (#vcfg:_) (il: verifiable_log vcfg) (t: nat{t < vcfg.thread_count})
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

let forall_vtls_rel_prefix (#vcfg:_) (il: verifiable_log vcfg) (i:nat{i <= length il})
  : Lemma (ensures (let il' = prefix il i in
                    forall_vtls_rel il ==> forall_vtls_rel il'))
  = admit()

let forall_vtls_rel_snoc (#vcfg:_) (il: verifiable_log vcfg{length il > 0})
  : Lemma (requires (let i = length il - 1 in
                     let il' = prefix il i in
                     let ilk = to_logk il in
                     let t = src il i in
                     forall_vtls_rel il' /\
                     vtls_rel (thread_state t il) (thread_state t ilk)))
          (ensures (forall_vtls_rel il))
  = admit()

let lemma_vtls_rel_implies_ms_verifiable (#vcfg:_) (ep: epoch) (ils:verifiable_log vcfg)
  : Lemma (requires (forall_vtls_rel ils))
          (ensures (let ilk = to_logk ils in
                    GG.aems_equal_upto ep (to_glog ils) ==> GG.aems_equal_upto ep (to_glog ilk)))
  = admit()

let lemma_empty_implies_spec_rel (#vcfg:_) (il:verifiable_log vcfg)
  : Lemma (ensures (length il = 0 ==> spec_rel il))
  = admit()

let lemma_spec_rel_implies_prefix_spec_rel (#vcfg:_) (il:verifiable_log vcfg) (i:nat{i <= length il})
 : Lemma (requires spec_rel il)
         (ensures (let il' = prefix il i in
                   spec_rel il'))
  = admit()

let lemma_spec_rel_implies_appfn_identical (#vcfg:_) (il: verifiable_log vcfg {spec_rel il})
  : Lemma (ensures (let gl = to_glog il in
                    let ilk = to_logk il in
                    let glk = to_glog ilk in
                    GG.app_fcrs gl = GG.app_fcrs glk))
  = admit()
