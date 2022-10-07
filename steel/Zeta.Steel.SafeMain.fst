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
  gather_body handle.state;
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

#restart-solver
let verify_log_some_concl
               (tid:U16.t)
               (log_perm:perm)
               (log_bytes:Ghost.erased AT.bytes)
               (len: U32.t)
               (input: EXT.extern_ptr)
               (out_len: U32.t)
               (out_bytes:Ghost.erased AT.bytes)
               (output: EXT.extern_ptr)
               (sq: squash (check_verify_input tid len))
               (input': U.larray U8.t len)
               (output' : U.larray U8.t out_len)
               (entries: Ghost.erased AEH.log)
  (p1: perm)
  (v: option (M.verify_result len))
: STT unit
    (R.pts_to handle.state.state p1 handle.state.tl_state `star` M.verify_post handle.state.tl_state tid entries log_perm log_bytes len input' out_len out_bytes output' v `star` EXT.extern_in_out_pts_to input output (EXT.Read log_bytes out_len))
    (fun _ -> verify_post log_bytes tid len input output v `star` A.pts_to input' log_perm log_bytes `star` (exists_ (A.pts_to output' full_perm)))
= if (Some? v && V.Verify_success? (Some?.v v))
  then begin
    let Some (V.Verify_success read wrote) = v in
    rewrite
      (M.verify_post _ tid entries log_perm log_bytes len input' out_len out_bytes output' _)
      (M.core_inv handle.state.tl_state `star`
        A.pts_to input' log_perm log_bytes `star`
        exists_ (M.verify_post_success_pred handle.state.tl_state tid entries log_bytes out_len out_bytes output' read wrote)
      );
    let _ = gen_elim () in
    rewrite (handle_pts_to_body0 handle.state) (handle_pts_to_body handle.state);
    rewrite (M.log_of_tid_gen _ _ _) emp;
    EXT.copy_extern_output_ptr _ _ _ out_len output' _ _;
    rewrite (handle_pts_to0 handle.state.tl_state) (handle_pts_to handle.state.tl_state);
    rewrite
      (verify_post_some_m_success log_bytes tid len input output () handle.state.tl_state read wrote)
      (verify_post_some_m log_bytes tid len input output v handle.state.tl_state);
    rewrite
      (verify_post_some log_bytes tid len input output _)
      (verify_post log_bytes tid len input output v)
  end else begin
    m_verify_post_failure_eq handle.state.tl_state tid entries log_perm log_bytes len input' out_len out_bytes output' v;
    let _ = gen_elim () in
    rewrite (handle_pts_to_body0 handle.state) (handle_pts_to_body handle.state);
    rewrite (handle_pts_to0 handle.state.tl_state) (handle_pts_to handle.state.tl_state);
    rewrite
      (verify_post_some_m_failure log_bytes input output)
      (verify_post_some_m log_bytes tid len input output v handle.state.tl_state);
    rewrite
      (verify_post_some log_bytes tid len input output _)
      (verify_post log_bytes tid len input output v)
  end

let verify_log_some
               (log_bytes:Ghost.erased AT.bytes)
               (tid:U16.t)
               (len: U32.t)
               (input: EXT.extern_ptr)
               (input': U.larray U8.t len)
               (out_len: U32.t)
               (output: EXT.extern_ptr)
               (output': A.array U8.t)
  : ST (option (M.verify_result len))
    (handle_pts_to_body handle.state `star`
      EXT.extern_in_out_pts_to input output (EXT.Read log_bytes out_len) `star`
      A.pts_to input' full_perm log_bytes `star`
      exists_ (A.pts_to output' full_perm)
    )
    (fun res -> verify_post log_bytes tid len input output res)
    (check_verify_input tid len /\
      A.is_full_array input' /\
      U32.v out_len == A.length output' /\
      (if U32.v out_len > 0
       then A.is_full_array input' /\ A.is_full_array output'
       else A.adjacent input' output' /\ A.is_full_array (A.merge input' output')
      )
    )
    (fun _ -> True)
=
  rewrite (handle_pts_to_body handle.state) (handle_pts_to_body0 handle.state);
  let _ = gen_elim () in
  rewrite emp (M.log_of_tid_gen handle.state.tl_state tid Seq.empty);
  let v = M.verify_log _ tid len input' out_len output' in
  let p = vpattern_replace_erased (fun p -> R.pts_to handle.state.state p _) in
  let _ = verify_log_some_concl tid full_perm log_bytes len input out_len _ output () input' output' _ p v in
  let _ = gen_elim () in
  if 0ul `U32.lt` out_len
  then begin
    noop ();
    A.free input';
    A.free output';
    return v
  end else begin
    let a = A.join input' output' in
    A.free a;
    return v
  end

inline_for_extraction
noextract
let steel_ifthenelse
  (#t: Type)
  (#vpre: vprop)
  (#vpost: (t -> vprop))
  (b: bool)
  (ttrue: (squash (b == true) -> STT t vpre vpost))
  (tfalse: (squash (b == false) -> STT t vpre vpost))
: STF t vpre vpost True (fun _ -> True)
= if b then ttrue () else tfalse ()

#restart-solver
let verify_log
  log_bytes tid len out_len input output
=
  let t = handle.state.tl_state in
  handle_pts_to_body_intro ();
  steel_ifthenelse
    (not (check_verify_input tid len))
  (fun _ ->
    noop ();
    rewrite (handle_pts_to0 t) (handle_pts_to t);
    rewrite (verify_post_some_m_failure log_bytes input output) (verify_post_some_m log_bytes tid len input output None t);
    rewrite (verify_post_some log_bytes tid len input output None)
      (verify_post log_bytes tid len input output None);
    return None
  )
  (fun _ ->
    let check_valid = EXT.extern_in_out_pts_to_is_valid input _ len output out_len in
    steel_ifthenelse check_valid
      (fun _ ->
        vpattern_rewrite (EXT.extern_in_out_pts_to input output) (EXT.Unread log_bytes out_len);
        let a = A.alloc 0uy len in
        EXT.copy_extern_input_ptr input _ output len out_len a;
        let _ = gen_elim () in
        steel_ifthenelse (0ul `U32.lt` out_len)
          (fun _ ->
            let output' = A.alloc 0uy out_len in
            verify_log_some log_bytes tid len input a out_len output output'
          )
          (fun _ ->
            let _ = A.ghost_split a len in
            noop ();
            verify_log_some log_bytes tid len input (A.split_l a len) out_len output (A.split_r a len)
          )
      )
      (fun _ ->
        vpattern_rewrite (EXT.extern_in_out_pts_to input output) (EXT.Unknown log_bytes);
        rewrite (handle_pts_to0 t) (handle_pts_to t);
        rewrite (verify_post_some_m_failure log_bytes input output) (verify_post_some_m log_bytes tid len input output None t);
        rewrite (verify_post_some log_bytes tid len input output None)
          (verify_post log_bytes tid len input output None);
        return None
      )
  )

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
