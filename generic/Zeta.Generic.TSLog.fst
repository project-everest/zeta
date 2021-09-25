module Zeta.Generic.TSLog

open Zeta.SSeq
module T = Zeta.Generic.Thread

(* clock is idxfn_t, so has the prefix property *)
let lemma_prefix_clock_sorted (#vspec #n:_) (itsl: its_log vspec n) (i:nat{i <= length itsl}):
  Lemma (ensures (clock_sorted (prefix itsl i)))
  = admit()

let lemma_empty_verifiable_clock_sorted (vspec: verifier_spec) (n:_)
  : Lemma (ensures (let il = empty_interleaving (verifier_log_entry vspec) n in
                    verifiable il /\ clock_sorted il))
          [SMTPat (empty_interleaving (verifier_log_entry vspec) n)]
  = admit()

let lemma_empty_interleaving_empty_sseq (vspec: verifier_spec) (n:_)
  : Lemma (ensures (let il = empty_interleaving (verifier_log_entry vspec) n in
                    let gl = empty (verifier_log_entry vspec) n in
                    to_glog il == gl))
  = admit()

(* a thread with at least one entry *)
let non_empty_thread
  (#vspec:_)
  (gl: G.verifiable_log vspec)
  (tid: SA.seq_index gl)
  = S.length (S.index gl tid) > 0

(* return the max clock in a thread - the last log entry in the thread *)
let max_clock_in_thread
  (#vspec:_)
  (gl: G.verifiable_log vspec)
  (tid: _ {non_empty_thread gl tid})
  : timestamp
  = let l = S.index gl tid in
    let n = S.length l in
    G.clock gl (tid, n-1)

(* for any index within a thread, the max_clock is indeed max *)
let lemma_max_clock_in_thread_correct
  (#vspec:_)
  (gl: G.verifiable_log vspec)
  (ti: sseq_index gl)
  : Lemma (ensures(let t,_ = ti in                        (* thread id*)
                   let c = G.clock gl ti in               (* clock of entry ti *)
                   c `ts_leq` max_clock_in_thread gl t))
  = admit()

(* a thread tid has max clock property if it has the max clock overall *)
let max_clock_prop (#vspec) (gl: G.verifiable_log vspec) (tid: _)
  = non_empty_thread gl tid /\
    (forall tid'.
      {:pattern (max_clock_in_thread gl tid' `ts_leq` max_clock_in_thread gl tid)}
    (non_empty_thread gl tid' ==> max_clock_in_thread gl tid' `ts_leq` max_clock_in_thread gl tid))

let find_max_clock_thread (#vspec:_) (gl: G.verifiable_log vspec {flat_length gl > 0})
  : tid: _ {max_clock_prop gl tid}
  = admit()

let gl_thread_prefix_verifiable
  (#vspec:_)
  (gl: G.verifiable_log vspec)
  (tid: _ {non_empty_thread gl tid})
  : Lemma (ensures (G.verifiable (sseq_prefix gl tid)))
          [SMTPat (sseq_prefix gl tid)]
  = admit()

let rec create
  (#vspec:_) 
  (gl: G.verifiable_log vspec):
  Tot (itsl:its_log vspec (S.length gl){to_glog itsl == gl})
  (decreases (flat_length gl))
  = let m = flat_length gl in
    let n = S.length gl in
    if m = 0 then
    (
      (* if gl has flat_length zero, then it is empty *)
      lemma_flat_length_zero gl;
      assert(gl == empty _ n);

      (* empty interleaving has the required properties *)
      let itsl = empty_interleaving (verifier_log_entry vspec) n in
      lemma_empty_verifiable_clock_sorted vspec n;
      lemma_empty_interleaving_empty_sseq vspec n;
      itsl
    )
    else
    (
      let tid = find_max_clock_thread gl in
      let tl = G.index gl tid in
      let tn = T.length tl in
      //assert(T.clock tl (tn - 1) = max_clock_in_thread gl tid);

      (* get a "prefix" of gl by eliminating the last log entry of thread tid *)
      let gl' = sseq_prefix gl tid in

      (* recursively construct the interleaving for gl' *)
      let itsl' = create gl' in

      let itsl: interleaving _ n = interleaving_extend itsl' (G.indexss gl (tid,tn-1)) tid in
      assert(to_glog itsl = gl);
      assert(verifiable itsl);
      assert(clock_sorted itsl');

      let aux(i j: seq_index itsl)
        : Lemma (ensures (i <= j ==> clock itsl i `ts_leq` clock itsl j))
        = admit()
      in
      FStar.Classical.forall_intro_2 aux;
      assert(clock_sorted itsl);

      itsl
    )

let prefix_within_epoch (#vspec #n:_) (ep: epoch) (itsl: its_log vspec n)
  : itsl': its_log vspec n {itsl' `prefix_of` itsl}
  = admit()

let prefix_within_epoch_correct (#vspec #n:_) (ep: epoch) (itsl: its_log vspec n) (i: seq_index itsl)
  : Lemma (ensures (let il' = prefix_within_epoch ep itsl in
                    let l' = S.length il' in
                    (i < l' ==> (clock itsl i).e <= ep) /\
                    (i >= l' ==> (clock itsl i).e > ep)))
  = admit()

let lemma_fcrs_within_epoch (#vspec #n:_) (ep: epoch) (itsl: its_log vspec n)
  : Lemma (ensures (let itsl_ep = prefix_within_epoch ep itsl in
                    let gl_ep = to_glog itsl_ep in
                    let gl = to_glog itsl in
                    G.app_fcrs gl_ep = G.app_fcrs_within_ep ep gl))
  = admit()
