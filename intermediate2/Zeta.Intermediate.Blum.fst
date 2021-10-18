module Zeta.Intermediate.Blum

open Zeta.Intermediate.Store
open Zeta.Intermediate.StateRel

module SA = Zeta.SeqAux
module GV = Zeta.GenericVerifier
module HV = Zeta.High.Verifier
module IV = Zeta.Intermediate.Verifier

#push-options "--fuel 0 --ifuel 1 --query_stats"

let lemma_spec_rel_implies_same_add_elem (#vcfg:_)
  (il: verifiable_log vcfg {spec_rel il})
  (i: seq_index il {is_blum_add il i})
  : Lemma (ensures (let ilk = to_logk il in
                    is_blum_add ilk i /\
                    blum_add_elem il i = blum_add_elem ilk i))
  = lemma_spec_rel_implies_prefix_spec_rel il i

#push-options "--z3rlimit_factor 3"

let lemma_spec_rel_implies_same_evict_elem (#vcfg:_)
  (il: verifiable_log vcfg {spec_rel il})
  (i: seq_index il {is_blum_evict il i})
  : Lemma (ensures (let ilk = to_logk il in
                    is_blum_evict ilk i /\
                    blum_evict_elem il i = blum_evict_elem ilk i))
  = let _il = prefix il i in
    let t = src il i in
    let _vss:IV.vtls_t vcfg = thread_state_pre t il i in
    let _sts = _vss.st in
    let e = index il i in
    let s = GV.evict_slot e in

    lemma_cur_thread_state_extend il i;

    let ilk = to_logk il in
    let _ilk = SA.prefix ilk i in
    let _vsk: HV.vtls_t vcfg.app = thread_state_pre t ilk i in
    let _stk = _vsk.st in
    let ek = index ilk i in
    assert(is_blum_evict ilk i);
    let k = GV.evict_slot ek in

    elim_forall_vtls_rel _il t;
    lemma_ismap_correct _sts s (slot_of_key _sts k);
    elim_key_store_rel _sts _stk k

#pop-options

#pop-options

let lemma_spec_rel_implies_same_add_seq (#vcfg:_) (ep: epoch) (il: verifiable_log vcfg)
  : Lemma (requires (spec_rel il))
          (ensures (let ilk = to_logk il in
                    add_seq ep il == add_seq ep ilk))
  = admit()

let lemma_spec_rel_implies_same_evict_seq (#vcfg:_) (ep: epoch) (il: verifiable_log vcfg)
  : Lemma (requires (spec_rel il))
          (ensures (let ilk = to_logk il in
                    evict_seq ep il == evict_seq ep ilk))
  = admit()

let lemma_spec_rel_implies_same_add_set (#vcfg:_) (ep: epoch) (il: verifiable_log vcfg)
  : Lemma (requires (spec_rel il))
          (ensures (let ilk = to_logk il in
                    add_set ep il == add_set ep ilk))
  = admit()

let lemma_spec_rel_implies_same_evict_set (#vcfg:_) (ep: epoch) (il: verifiable_log vcfg)
  : Lemma (requires (spec_rel il))
          (ensures (let ilk = to_logk il in
                    evict_set ep il == evict_set ep ilk))
  = admit()

let lemma_vtls_rel_implies_ms_verifiable (#vcfg:_) (ep: epoch) (ils:verifiable_log vcfg)
  : Lemma (requires (forall_vtls_rel ils))
          (ensures (let ilk = to_logk ils in
                    GG.aems_equal_upto ep (to_glog ils) ==> GG.aems_equal_upto ep (to_glog ilk)))
  = admit()
