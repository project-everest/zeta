module Zeta.Generic.TSLog

open Zeta.SSeq
open FStar.Classical
module T = Zeta.Generic.Thread

#push-options "--fuel 0 --ifuel 1 --query_stats"

(* clock is idxfn_t, so has the prefix property *)
let lemma_prefix_clock_sorted (#vspec #n:_) (itsl: its_log vspec n) (i:nat{i <= length itsl}):
  Lemma (ensures (clock_sorted (prefix itsl i)))
  = let itsl' = prefix itsl i in
    let aux (i j:_)
      : Lemma (ensures (i <= j ==> clock itsl' i `ts_leq` clock itsl' j))
      = ()
    in
    forall_intro_2 aux

#pop-options

let lemma_empty_verifiable_clock_sorted (vspec: verifier_spec) (n:_)
  : Lemma (ensures (let il = empty_interleaving (verifier_log_entry vspec) n in
                    verifiable il /\ clock_sorted il))
          [SMTPat (empty_interleaving (verifier_log_entry vspec) n)]
  = let il = empty_interleaving (verifier_log_entry vspec) n in
    let gl = s_seq il in
    let aux (t:_)
      : Lemma (ensures (T.verifiable (t, S.index gl t)))
      = lemma_empty_sseq (verifier_log_entry vspec) n t
    in
    forall_intro aux;
    assert(verifiable il);

    let aux (i j:_)
      : Lemma (ensures (i <= j ==> clock il i `ts_leq` clock il j))
      = ()
    in
    forall_intro_2 aux

let lemma_empty_interleaving_empty_sseq (vspec: verifier_spec) (n:_)
  : Lemma (ensures (let il = empty_interleaving (verifier_log_entry vspec) n in
                    let gl = empty (verifier_log_entry vspec) n in
                    to_glog il == gl))
  = let il = empty_interleaving (verifier_log_entry vspec) n in
    let gl = empty (verifier_log_entry vspec) n in
    let gl2 = to_glog il in

    let aux (i:_)
      : Lemma (ensures (S.index gl i == S.index gl2 i))
      = lemma_empty_sseq (verifier_log_entry vspec) n i
    in
    forall_intro aux;
    assert(S.equal gl gl2)

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
  : GTot timestamp
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
  = let t,i = ti in
    let tl = G.index gl t in
    let n = T.length tl in
    T.lemma_clock_monotonic tl i (n-1)

(* a thread tid has max clock property if it has the max clock overall *)
let max_clock_prop (#vspec) (gl: G.verifiable_log vspec) (tid: _)
  = non_empty_thread gl tid /\
    (forall tid'.
    (non_empty_thread gl tid' ==> max_clock_in_thread gl tid' `ts_leq` max_clock_in_thread gl tid))

#push-options "--fuel 0 --ifuel 1 --query_stats"

let rec find_max_clock_aux  (#vspec:_) (gl: G.verifiable_log vspec {flat_length gl > 0})
  (i: nat{i <= S.length gl})
  : GTot (ot:option nat {(None = ot ==> (forall tid. tid < i ==> S.length (S.index gl tid) = 0)) /\
                 (Some? ot ==> (let tid = Some?.v ot in
                                tid < i /\
                                non_empty_thread gl tid /\
                                (forall tid'.
                                    tid' < i ==>
                                    non_empty_thread gl tid' ==>
                                    max_clock_in_thread gl tid' `ts_leq` max_clock_in_thread gl tid)))})
  = if i = 0 then None
    else (
      let i' = i - 1 in
      let ot = find_max_clock_aux gl i' in
      let s = S.index gl i' in

      if S.length s = 0 then (
        if ot = None then (
          let aux(tid:_)
            : Lemma (ensures (tid < i ==> S.length (S.index gl tid) = 0))
            = if tid < i' then
                eliminate forall tid. tid < i' ==> S.length (S.index gl tid) = 0
                with tid
          in
          forall_intro aux;
          None
        )
        else (
          let tid = Some?.v ot in
          let aux(tid':_)
            : Lemma (ensures (tid' < i ==>
                              non_empty_thread gl tid' ==>
                              max_clock_in_thread gl tid' `ts_leq` max_clock_in_thread gl tid))
            = if tid' < i' && non_empty_thread gl tid' then
                eliminate forall tid'. tid' < i' ==>
                                   non_empty_thread gl tid' ==>
                                   max_clock_in_thread gl tid' `ts_leq` max_clock_in_thread gl tid
                with tid'
          in
          forall_intro aux;
          Some tid
        )
      )
      else (
        if ot = None then (
          let tid = i' in

          let aux(tid':_)
            : Lemma (ensures (tid' < i ==>
                              non_empty_thread gl tid' ==>
                              max_clock_in_thread gl tid' `ts_leq` max_clock_in_thread gl tid))
            = if tid' < i' && non_empty_thread gl tid' then
                eliminate forall tid'. tid' < i' ==>
                                   non_empty_thread gl tid' ==>
                                   max_clock_in_thread gl tid' `ts_leq` max_clock_in_thread gl tid
                with tid'
          in
          forall_intro aux;
          Some tid
        )
        else (
          let tid1 = Some?.v ot in
          if max_clock_in_thread gl i' `ts_leq` max_clock_in_thread gl tid1 then (
            let tid = tid1 in

            let aux(tid':_)
              : Lemma (ensures (tid' < i ==>
                               non_empty_thread gl tid' ==>
                               max_clock_in_thread gl tid' `ts_leq` max_clock_in_thread gl tid))
              = if tid' < i' && non_empty_thread gl tid' then
                   eliminate forall tid'. tid' < i' ==>
                                     non_empty_thread gl tid' ==>
                                     max_clock_in_thread gl tid' `ts_leq` max_clock_in_thread gl tid
                   with tid'
            in
            forall_intro aux;
            Some tid
          )
          else (
            let tid = i' in

            let aux(tid':_)
              : Lemma (ensures (tid' < i ==>
                               non_empty_thread gl tid' ==>
                               max_clock_in_thread gl tid' `ts_leq` max_clock_in_thread gl tid))
              = if tid' < i' && non_empty_thread gl tid' then
                   eliminate forall tid'. tid' < i' ==>
                                     non_empty_thread gl tid' ==>
                                     max_clock_in_thread gl tid' `ts_leq` max_clock_in_thread gl tid
                   with tid'
            in
            forall_intro aux;
            Some tid
          ))))

#pop-options

let find_max_clock_thread (#vspec:_) (gl: G.verifiable_log vspec {flat_length gl > 0})
  : GTot (tid: _ {max_clock_prop gl tid})
  = let ot = find_max_clock_aux gl (S.length gl) in
    if None = ot then (
      assert(forall tid. S.length (S.index gl tid) = 0);
      nonzero_flatlen_implies_nonempty gl;
      0
    )
    else
      Some?.v ot

#push-options "--fuel 0 --ifuel 1 --query_stats"

let gl_thread_prefix_verifiable
  (#vspec:_)
  (gl: G.verifiable_log vspec)
  (tid: _ {non_empty_thread gl tid})
  : Lemma (ensures (G.verifiable (sseq_prefix gl tid)))
          [SMTPat (sseq_prefix gl tid)]
  = let gl' = sseq_prefix gl tid in
    let aux (t:_)
      : Lemma (ensures (T.verifiable (t, S.index gl' t)))
      = eliminate forall tid. T.verifiable (thread_log_base gl tid)
        with t;
        let s' = S.index gl' t in
        if t = tid then
          let tl = G.index gl tid in
          T.verifiable_implies_prefix_verifiable tl (S.length s')
    in
    forall_intro aux

#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit_factor 3 --query_stats"

let rec create
  (#vspec:_) 
  (gl: G.verifiable_log vspec):
  GTot (itsl:its_log vspec (S.length gl){to_glog itsl == gl})
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
      let e = G.indexss gl (tid,tn-1) in

      (* interleaving we are interested in ... *)
      let itsl: interleaving _ n = SA.append1 itsl' ({e; s = tid}) in
      interleaving_snoc itsl;
      interleaving_flat_length itsl;
      lemma_prefix1_append itsl' ({e;s=tid});
      lemma_interleave_extend gl tid itsl';

      assert(s_seq itsl == gl);
      assert(clock_sorted itsl');

      let aux(i j: seq_index itsl)
        : Lemma (ensures (i <= j ==> clock itsl i `ts_leq` clock itsl j))
        = if i < j then (
            clock_prefix_prop itsl i (m-1);

            if j = m - 1 then (
              assert(i2s_map itsl j = (tid,tn-1));
              let t',i' = i2s_map itsl i in
              lemma_max_clock_in_thread_correct gl (t',i');
              eliminate
                forall tid'. (non_empty_thread gl tid' ==> max_clock_in_thread gl tid' `ts_leq` max_clock_in_thread gl tid)
              with t'
            )
            else (
              clock_prefix_prop itsl j (m-1);
              eliminate forall (i j: seq_index itsl'). i <= j ==> clock itsl' i `ts_leq` clock itsl' j
              with i j
            )
          )
      in
      FStar.Classical.forall_intro_2 aux;
      assert(clock_sorted itsl);

      itsl
    )

#pop-options

#push-options "--fuel 0 --ifuel 1 --query_stats"

let rec  find_epoch_boundary (#vspec #n:_) (ep: epoch) (itsl: its_log vspec n) (i:seq_index itsl)
  : GTot(o:option nat {(None = o ==> (clock itsl i).e <= ep) /\
                (Some? o ==> (let j = Some?.v o in
                              j <= i /\
                              (clock itsl j).e > ep /\
                              (j = 0 \/ (clock itsl (j-1)).e <= ep)))})
    (decreases i)
  = if i = 0 then
      if (clock itsl i).e <= ep then None
      else Some i
    else
      let i' = i - 1 in
      let o = find_epoch_boundary ep itsl i' in
      if None = o then
        if (clock itsl i).e <= ep then None
        else Some i
      else o

let prefix_within_epoch (#vspec #n:_) (ep: epoch) (itsl: its_log vspec n)
  = if length itsl = 0 then itsl
    else
      let o = find_epoch_boundary ep itsl (length itsl - 1) in
      if o = None then itsl
      else
        let j = Some?.v o in
        prefix itsl j

let prefix_within_epoch_correct (#vspec #n:_) (ep: epoch) (itsl: its_log vspec n) (i: seq_index itsl)
  : Lemma (ensures (let il' = prefix_within_epoch ep itsl in
                    let l' = S.length il' in
                    (i < l' ==> (clock itsl i).e <= ep) /\
                    (i >= l' ==> (clock itsl i).e > ep)))
  = let n' = length itsl - 1 in
    let o = find_epoch_boundary ep itsl n' in
    let il' = prefix_within_epoch ep itsl in
    let l' = S.length il' in
    if o = None then
      eliminate forall (i j: seq_index itsl). i <= j ==> clock itsl i `ts_leq` clock itsl j
      with i n'
    else (
      assert((clock itsl l').e > ep);
      if i >= l' then
        eliminate forall (i j: seq_index itsl). i <= j ==> clock itsl i `ts_leq` clock itsl j
        with l' i
      else if l' > 0 then
        eliminate forall (i j: seq_index itsl). i <= j ==> clock itsl i `ts_leq` clock itsl j
        with i (l' - 1)
    )

#push-options "--z3rlimit_factor 3"

let lemma_thread_prefix_within_epoch (#vspec #n:_) (ep: epoch) (itsl: its_log vspec n) (t:nat{t<n})
  : Lemma (ensures (let itsl_ep = prefix_within_epoch ep itsl in
                    let gl_ep = to_glog itsl_ep in
                    let tl_ep = G.index gl_ep t in
                    let gl = to_glog itsl in
                    let tl = G.index gl t in
                    tl_ep = T.prefix_within_epoch ep tl))
  = let itsl_ep = prefix_within_epoch ep itsl in
    let gl_ep = to_glog itsl_ep in
    let tl_ep = G.index gl_ep t in
    let l1 = T.length tl_ep in

    let gl = to_glog itsl in
    let tl = G.index gl t in
    let tl' = T.prefix_within_epoch ep tl in
    let l2 = T.length tl' in

    per_thread_prefix itsl (length itsl_ep);
    assert(tl_ep `T.prefix_of` tl);

    if l1 < l2 then (
      let l2' = l2 - 1 in
      T.prefix_within_epoch_correct ep tl l2';
      assert((T.clock tl l2').e <= ep);
      let i2 = s2i_map itsl (t,l2') in
      let _ = i2s_map itsl i2 in
      assert(clock itsl i2 = T.clock tl l2');
      prefix_within_epoch_correct ep itsl i2;
      assert(i2 < length itsl_ep);
      let _ = i2s_map itsl_ep i2 in
      ()
    )
    else if l2 < l1 then (
      let l1' = l1 - 1 in
      T.prefix_within_epoch_correct ep tl l1';
      assert((T.clock tl l1').e > ep);
      let i1 = s2i_map itsl_ep (t,l1') in
      let _ = i2s_map itsl_ep i1 in
      let _ = i2s_map itsl i1 in
      assert(clock itsl i1 = T.clock tl l1');
      assert(i1 < length itsl_ep);
      prefix_within_epoch_correct ep itsl i1
    )

let lemma_fcrs_within_epoch (#vspec #n:_) (ep: epoch) (itsl: its_log vspec n)
  : Lemma (ensures (let itsl_ep = prefix_within_epoch ep itsl in
                    let gl_ep = to_glog itsl_ep in
                    let gl = to_glog itsl in
                    G.app_fcrs gl_ep = G.app_fcrs_within_ep ep gl))
  = let itsl_ep = prefix_within_epoch ep itsl in
    let gl_ep = to_glog itsl_ep in
    let gl = to_glog itsl in
    let fcrs1 = G.app_fcrs gl_ep in
    let fcrs2 = G.app_fcrs_within_ep ep gl in

    let aux (t:_)
      : Lemma (ensures (S.index fcrs1 t = S.index fcrs2 t))
      = let tl = G.index gl t in
        lemma_thread_prefix_within_epoch ep itsl t;
        T.lemma_app_fcrs_ep_prefix ep tl
    in
    forall_intro aux;
    assert(S.equal fcrs1 fcrs2)

#pop-options
