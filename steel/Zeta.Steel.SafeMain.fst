module Zeta.Steel.SafeMain
open Zeta.Steel.SafeMain.Handle

module Lock = Steel.ST.SpinLock
module R = Steel.ST.Reference

open Steel.ST.GenElim

[@@__reduce__]
let handle_pts_to0
  (ts: M.top_level_state false)
: Tot vprop
= handle_pts_to_body handle.state `star`
  pure (ts == Ghost.reveal handle.state.tl_state)

let handle_pts_to
  (ts: M.top_level_state false)
: Tot vprop
= handle_pts_to0 ts
  
let gather ts ts' =
  rewrite (handle_pts_to ts) (handle_pts_to0 ts);
  let _ = gen_elim () in
  rewrite (handle_pts_to ts') (handle_pts_to0 ts');
  let _ = gen_elim () in
  gather_body _;
  rewrite (handle_pts_to0 ts) (handle_pts_to ts)

let share
  ts
= rewrite (handle_pts_to ts) (handle_pts_to0 ts);
  let _ = gen_elim () in
  share_body _;
  rewrite (handle_pts_to0 ts) (handle_pts_to ts);
  noop ();
  rewrite (handle_pts_to0 ts) (handle_pts_to ts)

let with_invariant_g (#a:Type)
                     (#fp:vprop)
                     (#fp':a -> vprop)
                     (#opened_invariants:inames)
                     (#p:vprop)
                     (i:inv p{not (mem_inv opened_invariants i)})
                     (f:unit -> STGhostT a (add_inv opened_invariants i)
                                         (p `star` fp)
                                         (fun x -> p `star` fp' x))
  : STGhostT a opened_invariants fp fp'
= with_invariant_g i f

let handle_pts_to_body_intro
  (#opened: _)
  ()
: STGhost unit opened
    emp
    (fun _ -> handle_pts_to_body handle.state)
    (not (mem_inv opened handle._inv))
    (fun _ -> True)
= with_invariant_g
    #unit
    #emp
    #(fun _ -> handle_pts_to_body handle.state)
    #_
    #(handle_pts_to_body handle.state)
    handle._inv
    (fun _ ->
      share_body _
    )

#push-options "--z3rlimit 32 --query_stats --ifuel 6"
#restart-solver

let m_verify_post_failure_eq
  (#opened: _)
  (t:M.top_level_state false)
  (tid:AT.tid)
  (entries:Ghost.erased AEH.log)
  (log_perm:perm)
  (log_bytes:Ghost.erased AT.bytes)
  (len: U32.t)
  (input:U.larray U8.t len)
  (out_len: U32.t)
  (out_bytes:Ghost.erased AT.bytes)
  (output:U.larray U8.t out_len)
  (res: (option (v:V.verify_result { V.verify_result_complete len v })))
: STGhost unit opened
  (
    M.verify_post t tid entries log_perm log_bytes len input out_len out_bytes output res
  )
  (fun _ ->
    M.core_inv t `star`
    A.pts_to input log_perm log_bytes `star`
       exists_ (fun s -> A.pts_to output full_perm s)
  )
  (match res with
  | Some (V.Verify_success _ _) -> False
  | _ -> True
  )
  (fun _ -> True)
= rewrite
    (M.verify_post t tid entries log_perm log_bytes len input out_len out_bytes output res)
    (M.core_inv t `star`
    A.pts_to input log_perm log_bytes `star` (
       exists_ (fun s -> A.pts_to output full_perm s) `star`
       emp))

let verify_log_some_concl
  (#opened: _)
               (tid:U16.t)
               (#log_perm:perm)
               (#log_bytes:Ghost.erased AT.bytes)
               (len: U32.t)
               (input: EXT.extern_ptr)
               (out_len: U32.t)
               (#out_bytes:Ghost.erased AT.bytes)
               (output: EXT.extern_ptr)
               (sq: squash (check_verify_input tid len input out_len output))
               (input': U.larray U8.t len)
               (output' : U.larray U8.t out_len)
               (entries: Ghost.erased AEH.log)
  (p1: perm)
  (v: option (M.verify_result len))
: STGhost unit opened
    (R.pts_to handle.state.state p1 handle.state.tl_state `star` M.verify_post handle.state.tl_state tid entries log_perm log_bytes len input' out_len out_bytes output' v)
    (fun _ -> verify_post tid log_perm log_bytes len input out_len out_bytes output v)
    (input' == EXT.gtake input /\ output' == EXT.gtake output)
    (fun _ -> True)
= if (Some? v && V.Verify_success? (Some?.v v))
  then begin
    let Some (V.Verify_success read wrote) = v in
    rewrite
      (M.verify_post _ tid entries log_perm log_bytes len input' out_len out_bytes output' _)
      (M.core_inv handle.state.tl_state `star`
        A.pts_to (EXT.gtake input) log_perm log_bytes `star`
        exists_ (M.verify_post_success_pred handle.state.tl_state tid entries log_bytes out_len out_bytes output' read wrote)
      );
    let _ = gen_elim () in
    rewrite (handle_pts_to_body0 handle.state) (handle_pts_to_body handle.state);
    rewrite (M.log_of_tid_gen _ _ _) emp;
    rewrite (handle_pts_to0 handle.state.tl_state) (handle_pts_to handle.state.tl_state);
    let out_bytes' = vpattern_replace_erased (A.pts_to output' _) in
    vpattern_rewrite #_ #_ #output' (fun output -> A.pts_to output _ _) (EXT.gtake output);
    assert_ (verify_post_some_m_success_body tid log_perm log_bytes len input out_len out_bytes output v () handle.state.tl_state read wrote out_bytes');
    rewrite
      (verify_post_some_m_success tid log_perm log_bytes len input out_len out_bytes output v () handle.state.tl_state read wrote)
      (verify_post_some_m tid log_perm log_bytes len input out_len out_bytes output v handle.state.tl_state);
    rewrite
      (verify_post_some tid log_perm log_bytes len input out_len out_bytes output _)
      (verify_post tid log_perm log_bytes len input out_len out_bytes output v)
  end else begin
    m_verify_post_failure_eq handle.state.tl_state tid entries log_perm log_bytes len input' out_len out_bytes output' v;
    let _ = gen_elim () in
    rewrite (handle_pts_to_body0 handle.state) (handle_pts_to_body handle.state);
    rewrite (handle_pts_to0 handle.state.tl_state) (handle_pts_to handle.state.tl_state);
    vpattern_rewrite #_ #_ #output' (fun output -> A.pts_to output _ _) (EXT.gtake output);
    rewrite
      (verify_post_some_m_failure output)
      (verify_post_some_m tid log_perm log_bytes len input out_len out_bytes output v handle.state.tl_state);
    vpattern_rewrite #_ #_ #input' (fun input -> A.pts_to input _ _) (EXT.gtake input);
    rewrite
      (verify_post_some tid log_perm log_bytes len input out_len out_bytes output _)
      (verify_post tid log_perm log_bytes len input out_len out_bytes output v)
  end

let verify_log_some
               (tid:U16.t)
               (#log_perm:perm)
               (#log_bytes:Ghost.erased AT.bytes)
               (len: U32.t)
               (input: EXT.extern_ptr)
               (out_len: U32.t)
               (#out_bytes:Ghost.erased AT.bytes)
               (output: EXT.extern_ptr)
  : ST (option (v:V.verify_result { V.verify_result_complete len v }))
    (handle_pts_to_body handle.state `star` verify_pre log_perm log_bytes input out_bytes output)
    (fun res -> verify_post tid log_perm log_bytes len input out_len out_bytes output res)
    (check_verify_input tid len input out_len output)
    (fun _ -> True)
=
  rewrite (handle_pts_to_body handle.state) (handle_pts_to_body0 handle.state);
  let _ = gen_elim () in
  rewrite emp (M.log_of_tid_gen handle.state.tl_state tid Seq.empty);
  let input' = EXT.take input len in
  let output' = EXT.take output out_len in
  vpattern_rewrite (fun a -> A.pts_to a log_perm log_bytes) input';
  vpattern_rewrite (fun a -> A.pts_to a full_perm out_bytes) output';
  let v = M.verify_log _ tid len input' out_len output' in
  let _ = verify_log_some_concl tid len input out_len output () input' output' _ _ v in
  return v

let verify_log
  tid #log_perm #log_bytes len input out_len #out_bytes output
=
  let t = handle.state.tl_state in
  handle_pts_to_body_intro ();
  if not (check_verify_input tid len input out_len output) returns STT (option (M.verify_result len))
    (handle_pts_to_body handle.state `star` verify_pre log_perm log_bytes input out_bytes output)
    (fun res -> verify_post tid log_perm log_bytes len input out_len out_bytes output res)
  then begin
    noop ();
    rewrite (handle_pts_to0 t) (handle_pts_to t);
    rewrite (verify_post_some_m_failure output) (verify_post_some_m tid log_perm log_bytes len input out_len out_bytes output None t);
    rewrite (verify_post_some tid log_perm log_bytes len input out_len out_bytes output None)
      (verify_post tid log_perm log_bytes len input out_len out_bytes output None);
    return None
  end else
  begin
    noop ();
    verify_log_some tid len input out_len output
  end

let max_certified_epoch
  ()
=
    handle_pts_to_body_intro ();
    rewrite (handle_pts_to_body handle.state) (handle_pts_to_body0 handle.state);
    let _ = gen_elim () in
    let t = handle.state.tl_state in
    let r = M.max_certified_epoch handle.state.state in
    vpattern_rewrite (fun t -> M.read_max_post t _) t;
    rewrite (handle_pts_to_body0 handle.state) (handle_pts_to_body handle.state);
    rewrite (handle_pts_to0 t) (handle_pts_to t);
    return r

#pop-options
