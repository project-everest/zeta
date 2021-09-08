module Zeta.High.Interleave

let mk_vlog_entry_ext (#app: app_params) (#n:nat)
  : IF.idxfn_t (gen_seq app n) (vlog_entry_ext app)
  = admit()

let is_eac_post (#app: app_params) (#n:nat)
  (il: verifiable_log app n) (i: seq_index il)
  : bool
  = let il' = prefix il (i+1) in
    let l' = vlog_ext_of_il_log il' in
    is_eac_log l'

let is_eac #app #n (il: verifiable_log app n)
  = is_eac_log (vlog_ext_of_il_log il)

let lemma_eac_empty #app #n (il: verifiable_log app n{S.length il = 0})
  : Lemma (ensures (is_eac il))
  = let le = vlog_ext_of_il_log il in
    eac_empty_log le

let eac_boundary (#app #n:_) (il: neac_log app n)
  : (i: seq_index il{is_eac (prefix il i) /\
                     ~ (is_eac (prefix il (i+1)))})
  = let open Zeta.IdxFn in
    let le = vlog_ext_of_il_log il in
    let i = max_eac_prefix le in
    lemma_map_prefix mk_vlog_entry_ext il i;
    lemma_map_prefix mk_vlog_entry_ext il (i+1);
    i

let lemma_eac_implies_prefix_eac (#app #n:_) (il: verifiable_log app n) (i: nat{i <= S.length il})
  : Lemma (ensures (is_eac il ==> is_eac (prefix il i)))
  = let open Zeta.IdxFn in
    if is_eac il then
      lemma_map_prefix mk_vlog_entry_ext il i
    else ()

let lemma_eac_implies_appfn_calls_seq_consistent (#app #n:_) (il: eac_log app n)
  : Lemma (ensures (let gl = to_glog il in
                    Zeta.AppSimulate.seq_consistent (G.appfn_calls gl)))
  = admit()
