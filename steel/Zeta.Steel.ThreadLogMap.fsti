module Zeta.Steel.ThreadLogMap
(* Main interface to ghost state in Zeta *)
open FStar.Ghost
open FStar.Seq
open Zeta.Steel.FormatsManual
open Zeta.Steel.ApplicationTypes
open Steel.ST.Util
module M = Zeta.Steel.ThreadStateModel

/// A sequence of entries processed by a thread
let log = Seq.seq log_entry

/// A preorder on describing append-only logs
let log_grows :Preorder.preorder log
  = let open FStar.Seq in
    fun (s1 s2:log) ->
      length s1 <= length s2 /\
      (forall (i:nat).{:pattern (Seq.index s1 i) \/ (Seq.index s2 i)}
         i < length s1 ==> index s1 i == index s2 i)

/// The type of a handle to ghost state maintaining logs for all
/// threads
[@@erasable]
val t : Type0

/// A logical abstraction of that ghost state:
///    Map from thread ids to an optional log for that thread
///    - option because we'll sometimes take out some logs to operate on them in isolation
///    - FStar.Map has a notion of domain, which we don't use here---so, it'll always be the universal set
let repr = x:FStar.Map.t tid (option log) { Map.domain x `Set.equal` Set.complement Set.empty }

(*** Several ownership predicates **)

/// [global_anchor x m]
///    The last synchronized state of all threads is [m]
val global_anchor (x:t)
                  ([@@@smt_fallback] m:repr)
  : vprop

/// [tids_pts_to x f m with_anchor]
///
///    Indicates ownership of the all threads logs in [m] with
///    fraction [f]. Their state may be ahead of the global anchor.
///
///    If [with_anchor] is set and [frac == full_perm], then this
///    indicates exclusive ownership of that thread's log---no other
///    thread owns an anchor on the thread
val tids_pts_to (x:t)
                ([@@@smt_fallback] frac:perm)
                ([@@@smt_fallback] m:repr)
                (with_anchor:bool)
  : vprop

/// [tid_pts_to x t f l with_anchor]: A local version of [tids_pts_to]
///    Ownership of the log for thread [t]
val tid_pts_to (x:t)
               (t:tid)
               ([@@@smt_fallback] frac:perm)
               ([@@@smt_fallback] l:log)
               (with_anchor:bool)
  : vprop

/// [global_snapshot]
///    The state of all threads is at least [m]
val global_snapshot (x:t)
                    ([@@@smt_fallback] m: repr)
  : vprop

(*** Operations using the predicates **)

/// presented roughly in lifecycle order of their usage in Zeta

/// [alloc] : Initialize the ghost state
///
///  -- Get an anchor on the empty state. this is used to allocate the
///     aggregate epoch hash lock
///
///  -- And a full fraction on the all the thread logs initialize to empty
val alloc (#o:_) (_:unit)
  : STGhostT t o
    emp
    (fun t -> tids_pts_to t full_perm (Map.const (Some Seq.empty)) false `star`
           global_anchor t (Map.const (Some Seq.empty)))

/// [share_tids_pts_to]
///
/// Having allocated the state, share the [tids_pts_to] part so that
/// half can be given to the top-level client and the rest given to
/// each thread
val share_tids_pts_to (#o:_)
                      (#f:perm)
                      (x:t)
                      (m:repr)
  : STGhostT unit o
    (tids_pts_to x f m false)
    (fun _ -> tids_pts_to x (half_perm f) m false `star`
           tids_pts_to x (half_perm f) m false)

/// [take_tid]
///
/// We extract a singleton ownership predicate and hand it to each thread
val take_tid (#o:_)
             (#f:perm)
             (x:t)
             (m:repr)
             (t:tid { Some? (Map.sel m t) })
  : STGhostT unit o
    (tids_pts_to x f m false)
    (fun _ -> tid_pts_to x t f (Some?.v (Map.sel m t)) false `star`
           tids_pts_to x f (Map.upd m t None) false)

/// [gather_tids_pts_to]
///   This one isn't likely to be used in Zeta
///   It's the converse of [share_tids_pts_to]
val gather_tids_pts_to (#o:_)
                       (#f0 #f1:perm)
                       (x:t)
                       (m:repr)
  : STGhostT unit o
    (tids_pts_to x f0 m false `star` tids_pts_to x f1 m false)
    (fun _ -> tids_pts_to x (sum_perm f0 f1) m false)

/// [gather_tid_pts_to]
///   For a singleton onwership predicate, gather their fractions.
///
///   This is used when calling into Zeta.Main.verify_entries
///   to combine the half ownership passed by the client with the
///   half held in the top-level lock on each thread state.
val gather_tid_pts_to (#o:_)
                      (#tid:tid)
                      (#f0 #f1:perm)
                      (#l0 #l1:log)
                      (x:t)
  : STGhost unit o
    (tid_pts_to x tid f0 l0 false `star` tid_pts_to x tid f1 l1 false)
    (fun _ -> tid_pts_to x tid (sum_perm f0 f1) l0 false)
    (requires True)
    (ensures fun _ -> l0 == l1)

/// [share_tid_pts_to]
///   This is called when returning from Zeta.Main.verify_entries to
///   return half ownership back to the client
val share_tid_pts_to (#o:_) (#tid:tid) (#f:perm) (#l:log) (x:t)
  : STGhostT unit o
    (tid_pts_to x tid f l false)
    (fun _ -> tid_pts_to x tid (half_perm f) l false `star`
           tid_pts_to x tid (half_perm f) l false)

/// [l1 `compat_with_any_anchor_of` l0]
let compat_with_any_anchor_of (l1 l0:log)
  = forall (anchor:log).
      anchor == M.committed_log_entries l0 ==>
      anchor == M.committed_log_entries l1

/// [update_tid_log]
///
///    This is used in the Zeta.Steel.Verifier, when extending the log
///    with an entry that is *not verifyepoch*.
///
///    In this case, the thread is free to extend the log without
///    synchronizing with the anchor
val update_tid_log (#o:_)
                   (x:t)
                   (t:tid)
                   (l0 l1:log)
  : STGhost unit o
    (tid_pts_to x t full_perm l0 false)
    (fun _ -> tid_pts_to x t full_perm l1 false)
    (requires
      l1 `compat_with_any_anchor_of` l0 /\
      l0 `log_grows` l1)
    (ensures fun _ -> True)

/// In contrast, when trying to extend the log with a verifyepoch
/// entry, the verifier thread has to:
///
///   - acquire the aggregate epoch hash lock to obtain the global_anchor
///
///   - use take_anchor_tid to gain exclusive ownership on its entry
///
///   - update its log with the verifyepoch entry
///
///   - use put_anchor_tid to update and return the anchor to
///     aggregate epoch hashes


/// [extract_anchor_invariant]
///   Owning a thread's log and the anchor for that thread tells you
///   that the thread's log is not too far ahead of the anchor. In fact,
///   the anchor is the log's committed prefix
///
///   Note, the postcondition is the "main property"
val extract_anchor_invariant (#o:_)
                             (x:t)
                             (m:repr)
                             (t:tid)
                             (f:perm)
                             (l:log)
  : STGhost unit o
    (tid_pts_to x t f l false `star` global_anchor x m)
    (fun _ ->  tid_pts_to x t f l false `star` global_anchor x m)
    (requires
      Some? (Map.sel m t))
    (ensures fun _ ->
      Some? (Map.sel m t) /\
      M.committed_log_entries l == Some?.v (Map.sel m t))

/// [take_anchor_tid]
///   Taking ownership of the anchor for [t]
///
///   Note, the postcondition is the "main property". It relates the
///   anchor to the current state---the anchor is the committed
///   current log [l]
val take_anchor_tid (#o:_)
                    (x:t)
                    (m:repr)
                    (t:tid)
                    (f:perm)
                    (l:log)
  : STGhost unit o
    (tid_pts_to x t f l false `star` global_anchor x m)
    (fun _ -> tid_pts_to x t f l true `star`
           global_anchor x (Map.upd m t None))
    (requires
      Some? (Map.sel m t))
    (ensures fun _ ->
      Some? (Map.sel m t) /\
      M.committed_log_entries l == Some?.v (Map.sel m t))

/// [update_anchored_tid_log]
///
///    With exclusive ownership, you can update a the log of [t] to
///    [l1] so long as [l1] is itself committed.
val update_anchored_tid_log (#o:_)
                            (x:t)
                            (t:tid)
                            (l0 l1:log)
  : STGhost unit o
    (tid_pts_to x t full_perm l0 true)
    (fun _ -> tid_pts_to x t full_perm l1 true)
    (requires
      l0 `log_grows` l1 /\
      M.committed_log_entries l1 == l1)
    (ensures fun _ -> True)

/// [put_anchor_tid]
///    Returning ownership of the anchor for [t] to the [global_anchor]
val put_anchor_tid (#o:_)
                   (x:t)
                   (m:repr)
                   (t:tid)
                   (f:perm)
                   (l:log)
  : STGhost unit o
    (tid_pts_to x t f l true `star` global_anchor x m)
    (fun _ -> tid_pts_to x t f l false `star`
           global_anchor x (Map.upd m t (Some l)))
    (requires
      M.committed_log_entries l == l)
    (ensures fun _ -> True)

/// Finally, snapshots are used in Zeta.Main.max_certified_epoch

/// [take_snapshot]
///   We compute the max_certified_epoch from the aggregated state
///   and return a snapshot of that state to the client to attest
///   that the max is compatible with a valid history of the system
val take_snapshot (#o:_)
                  (x:t)
                  (m:repr)
  : STGhostT unit o
    (global_anchor x m)
    (fun _ -> global_anchor x m `star` global_snapshot x m)

/// [dup_snapshot]
///   Snapshots are stable, hence duplicable
val dup_snapshot (#o:_)
                 (x:t)
                 (m:repr)
  : STGhostT unit o
    (global_snapshot x m)
    (fun _ -> global_snapshot x m `star` global_snapshot x m)

/// [recall_snapshot]
///    And snaphots are compatible with the preorder
///    The current state of any thread is at least the snapshot
val recall_snapshot (#o:_)
                    (x:t)
                    (m:repr)
                    (f:perm)
                    (t:tid)
                    (l:log)
                    (with_anchor:bool)
  : STGhost unit o
    (global_snapshot x m `star` tid_pts_to x t f l with_anchor)
    (fun _ -> global_snapshot x m `star` tid_pts_to x t f l with_anchor)
    (requires True)
    (ensures fun _ ->
      Some? (Map.sel m t) ==>
      Some?.v (Map.sel m t) `log_grows` l)


/// [global_anchor_committed]
///
/// Finally, an auxiliary lemma.
///
/// Every log in global anchor [m] has the property that it
/// M.committed_log_entries l == l
val global_anchor_committed (#o:_) (#m:repr) (x:t)
  : STGhost unit o
    (global_anchor x m)
    (fun _ -> global_anchor x m)
    (requires True)
    (ensures fun _ ->
      forall tid. match Map.sel m tid with
             | None -> True
             | Some l -> M.committed_log_entries l == l)
