module Zeta.Intermediate.Blum

open Zeta.Intermediate.Store
open Zeta.Intermediate.StateRel
open FStar.Classical

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

let lemma_spec_rel_implies_is_blum_evict_identical (#vcfg:_)
  (il: verifiable_log vcfg {spec_rel il})
  (i: seq_index il)
  : Lemma (ensures (let ilk = to_logk il in
                    is_blum_evict il i = is_blum_evict ilk i))
  = let _il = prefix il i in
    let t = src il i in
    let _vss:IV.vtls_t vcfg = thread_state_pre t il i in
    let _sts = _vss.st in
    let e = index il i in
    //let s = GV.evict_slot e in

    lemma_cur_thread_state_extend il i;

    let ilk = to_logk il in
    let _ilk = SA.prefix ilk i in
    let _vsk: HV.vtls_t vcfg.app = thread_state_pre t ilk i in
    let _stk = _vsk.st in
    let ek = index ilk i in
    ()

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

#push-options "--fuel 1 --ifuel 1 --z3rlimit_factor 3 --query_stats"

let rec lemma_spec_rel_implies_same_add_seq (#vcfg:_) (ep: epoch) (il: verifiable_log vcfg)
  : Lemma (requires (spec_rel il))
          (ensures (let ilk = to_logk il in
                    add_seq ep il == add_seq ep ilk))
          (decreases (length il))
  = let ilk = to_logk il in
    if length il = 0 then (
      add_seq_empty ep il;
      add_seq_empty ep ilk
    )
    else (
      let i = length il - 1 in
      let il' = prefix il i in
      let ilk' = to_logk il' in
      lemma_spec_rel_implies_same_add_seq ep il';
      add_seq_snoc ep il;
      add_seq_snoc ep ilk
    )

#pop-options

let rec lemma_spec_rel_implies_same_evict_seq (#vcfg:_) (ep: epoch) (il: verifiable_log vcfg)
  : Lemma (requires (spec_rel il))
          (ensures (let ilk = to_logk il in
                    evict_seq ep il == evict_seq ep ilk))
          (decreases (length il))
  = let ilk = to_logk il in
    let ess = evict_seq ep il in
    let esk = evict_seq ep ilk in
    if length il = 0 then (
      evict_seq_empty ep il;
      evict_seq_empty ep ilk
    )
    else (
      let i = length il - 1 in
      let il' = prefix il i in
      let ess' = evict_seq ep il' in
      let ilk' = to_logk il' in
      let esk' = evict_seq ep ilk' in
      lemma_spec_rel_implies_same_evict_seq ep il';
      assert(ess' == esk');
      evict_seq_snoc ep il;
      evict_seq_snoc ep ilk;
      if is_blum_evict il i then
        lemma_spec_rel_implies_same_evict_elem il i
      else
        lemma_spec_rel_implies_is_blum_evict_identical il i
    )

let lemma_spec_rel_implies_same_add_set (#vcfg:_) (ep: epoch) (il: verifiable_log vcfg)
  : Lemma (requires (spec_rel il))
          (ensures (let ilk = to_logk il in
                    add_set ep il == add_set ep ilk))
  = ()

let lemma_spec_rel_implies_same_evict_set (#vcfg:_) (ep: epoch) (il: verifiable_log vcfg)
  : Lemma (requires (spec_rel il))
          (ensures (let ilk = to_logk il in
                    evict_set ep il == evict_set ep ilk))
  = ()
