module Zeta.Generic.Thread

(* if a thread log is verifiable, its prefix is verifiable *)
let rec verifiable_implies_prefix_verifiable (#vspec:verifier_spec)
  (tl:verifiable_log vspec) (i:nat{i <= length tl}):
  Lemma (ensures (verifiable (prefix tl i)))
        (decreases (length tl))
  = let n = length tl in
    if n = i then ()
    else verifiable_implies_prefix_verifiable (prefix tl (n-1)) i

(* the state after processing i'th entry is obtained by applying the verify
 * step to the state before processing the i'th entry *)
let lemma_state_transition (#vspec:verifier_spec) (tl: verifiable_log vspec) (i: seq_index tl):
  Lemma (ensures (state_at tl (i + 1) ==
                  verify_step (index tl i) (state_at tl i)))
  = ()

let rec lemma_clock_monotonic (#vspec:verifier_spec)
  (tl: verifiable_log vspec) (i:nat) (j: seq_index tl {j >= i}):
  Lemma (ensures (clock tl i `ts_leq` clock tl j))
  (decreases (i + j + length tl))
  = let n = length tl - 1 in
    let tl' = prefix tl n in
    if j < n
    then lemma_clock_monotonic tl' i j
    else if i = j then ()
    else lemma_clock_monotonic tl i (j-1)

(* the thread id in the state is always the one specified in the parameter *)
let rec lemma_thread_id_state (#vspec:verifier_spec) (tl: verifiable_log vspec):
  Lemma (ensures (let tid, _ = tl in
                  vspec.tid (verify tl) = tid))
        (decreases (length tl))
  = let n = length tl in
    if n = 0 then ()
    else lemma_thread_id_state (prefix tl (n-1))

let add_epoch_filter #vspec (ep: epoch) (tl: verifiable_log vspec): ((seq_index tl) -> bool)
  = let _,l = tl in
    let f = fun (i: SA.seq_index l) ->
            let e = S.index l i in
            is_blum_add e &&
            (let be = blum_add_elem e in
            epoch_of be = ep) in
    f

let to_blum_add_elem #vspec (ep: epoch) (tl: verifiable_log vspec):
  (i:seq_index tl{add_epoch_filter ep tl i} -> ms_hashfn_dom vspec.app)
  = let _,l = tl in
    let f = add_epoch_filter ep tl in
    let m = fun (i: SA.seq_index l { f i }) ->
            let e = S.index l i in
            blum_add_elem e in
    m

let blum_add_seq (#vspec: verifier_spec) (ep: epoch) (tl: verifiable_log vspec):
  S.seq (ms_hashfn_dom vspec.app)
  = let _,l = tl in
    let f = add_epoch_filter ep tl in
    let m = to_blum_add_elem ep tl in
    SA.indexed_filter_map l f m

let add_seq_map
  (#vspec: verifier_spec)
  (tl: verifiable_log vspec)
  (i: seq_index tl {is_blum_add (index tl i)}):
  (let be = blum_add_elem (index tl i) in
   let ep = epoch_of be in
   let add_seq = blum_add_seq ep tl in
   j: SA.seq_index add_seq{S.index add_seq j = be})
  = let be = blum_add_elem (index tl i) in
    let ep = epoch_of be in
    let _,l = tl in
    let f = add_epoch_filter ep tl in
    let m = to_blum_add_elem ep tl in
    SA.indexed_filter_map_map l f m i

let add_seq_inv_map
  (#vspec: verifier_spec)
  (ep: epoch)
  (tl: verifiable_log vspec)
  (j: SA.seq_index (blum_add_seq ep tl)):
  (i: seq_index tl {is_blum_add (index tl i) /\
                    blum_add_elem (index tl i) = S.index (blum_add_seq ep tl) j /\
                    epoch_of (blum_add_elem (index tl i)) = ep /\
                    add_seq_map tl i = j})
 = let _,l = tl in
   let f = add_epoch_filter ep tl in
   let m = to_blum_add_elem ep tl in
   SA.indexed_filter_map_invmap l f m j


let lemma_add_seq_inv
  (#vspec:_)
  (tl: verifiable_log vspec)
  (i: seq_index tl{is_blum_add (index tl i)}):
  Lemma (ensures (let be = blum_add_elem (index tl i) in
                  let ep = epoch_of be in
                  add_seq_inv_map ep tl (add_seq_map tl i) = i))
  = ()
