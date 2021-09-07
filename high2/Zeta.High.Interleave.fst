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
  = admit()
