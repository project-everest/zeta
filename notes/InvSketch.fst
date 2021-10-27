(*** Version 1: With several 
     coarse-grained locks ***)

////////////////////////////////////////////////////////////////////////////////

(** The top-level state and invariant: Not much, since most of the
    invariant is held in the locks.
  **)    

//A global witness for the read-only local_states array
//It's erased---so, spec only
val ls_repr : erased (tid -> local_state)

//A reference containing handles to
// -- the local_state for each thread
// -- a per-thread lock
// -- etc.
[@@static] //just a marker to say that this is static in C
val local_state_hdl : local_states

//A record containing
// - an array of aggregate epoch hashes, 
// - max_certified_epoch
// - a single big lock
//
//The aggregate state depends on some ghost refs in the
//local state, so the type is indexed by it
[@@static]
val aehs_handle : aggregate_epoch_hashes ls_repr

//The top-level invariant: 
// -- Holds some non-zero permission to read the local_state_hdl
//
//This invariant allows multiple entry points into the system to each
//extract some read permission to the local_state_hdl, and states that the
//contents of the local_state_hdl is immutable---it always points to ls_repr
let top_level_inv = exists perm > 0. local_state_hdl -perm-> ls_repr

////////////////////////////////////////////////////////////////////////////////

(** The local_states type and its internal invariant **)

/// local_states: An array mapping each (tid < n_threads) to the
/// local_state for that thread
let local_states = array n_threads local_state

/// where,
///
/// local_state is a record containing
type local_state = 
{

  //A ghost ref holding all the log entries processed by this thread
  mylogref : ghost_ref (seq log_entry);

  //A ghost ref holding a prefix of the log entries that have
  //been "committed" to the aggregated state
  logref : ghost_ref (seq log_entry);

  //vtls: thread_local_state, like the store, the clock, etc.
  vtls   : vtls;

  //A logically infinite array, indexed by epoch id, of triples, 
  //of add hash, evict hash, and a bool marking when the epoch is
  //ready for aggregation
  hashes : iarray epoch_id (ha & ha & bool); //the bool marks when the epoch is ready for aggregation

  //The main invariant of the local state is held in lock.
  //This lock will have to be acquired before calling the verifier
  lock   : lock (
     exists entries committed_entries tls epoch_hashes.
        //full term on mylogref and all the entries process so far
        mylogref -1-> entries `star`
        
        //half perm on log ref (the other half perm is held in the aggregate hash lock)
        logref -0.5-> committed_entries `star`       
        
        //relating concrete state handle (vtls) to its spec-level counterpart (tls)
        thread_state_inv vtls tls `star`  
        
         //the hashes iarray is modeled by the infinite array of epoch_hashes
        iarray_repr hashes epoch_hashes `star`
        
        //tls is obtained by running the verifier from the initial state on all the entries
        pure (tls == run_verifier initial_state entries) `star`

        //epoch_hashes are correct for all epochs
        // where `epoch_hash i entries` is a spec-level function computing
        // the hashes for epoch i after processing entries
        pure (forall i. epoch_hash i entries == epoch_hashes.[i]) `star`

        //committed_entries is a prefix of entries
        //where the extra elements in entries do not contain a VerifyEpoch
        pure (exists tl. committed_entries @ tl == entries /\
                    (forall e. e \in tl ==> e <> VerifyEpoch))
  )
}
////////////////////////////////////////////////////////////////////////////////

(** The aggregate_epoch_hashes type and its internal invariant **)

/// The type of a aggregated hash entry for a single epoch
/// 
///  -- It's possible to collapse hadd and hevict into a single entry,
///     but this version is meant to be as simple as possible
/// 
type aeh = {
  hadd         : ha;
  
  hevict       : ha;

  //A bit vector with at least N_THREADS bits
  // -- bv.(i) is set when tid has contributed its share
  //    to both hadd and hevict
  tid_complete : bv n_threads;

  //An erased boolean marks if the epoch has been certfied
  certified    : erased bool
}  

/// Now, the type of the main shared state among all the threads
///
/// -- It is indexed by a value representing the contents of the
///    local_states array
type aggregate_epoch_hashes (ls_repr: (tid -> local_state)) = {
    //aehs: A logically infinite array indexed by epoch_id
    //      holding the aggregated hashes for each epoch
    aehs      : iarray epoch_id aeh;

    //Another but it concrete state memoizing the id of the
    //last epoch that has been certified
    max_certified_epoch: ref epoch_id;

    //Some ghost state holding a map that records, for each epoch, 
    //each thread's contribution to the aggregate hash for that epoch
    aehs_ghost: ghost_ref (epoch_id -> tid -> (hadd & hevict));

    //A single big lock protects all this shared state, protecting an
    //invariant ..
    lock:lock (
        exists epoch_hashes epoch_hashes_ghost.

          //aehs contains epoch_hashes
          iarray_repr aehs epoch_hashes `star`

          //we have full ownership on the ghost state
          aehs_ghost -1-> epoch_hashes_ghost `star`

          //the aggregate epoch hash for eid is 
          //exactly the aggregate over all hashes for a given epoch
          //stored in aehs_ghost
          pure (forall eid. epoch_hashes.[eid] == aggregate_over_tid (epoch_hashes_ghost eid)) `star`

          //the certified flag in each aeh is correct
          pure (forall eid. epoch_hashes.[eid].certified ==>
                       epoch_hashes.[eid].hadd == epoch_hashes.[eid].hevict /\
                       epoch_hashes.[eid].tid_complete == all_ones) `star`

          //This is the most interesting part: It connects the epoch
          //hashes of each thread back to the thread local state and
          //log entries seen so far by a given thread
          (forall tid. 
            //logref is the ghostref holding the entries seen by thread tid
            let logref = ls_repr tid in
            exists entries.
               //this lock holds half permission to that logref
               logref -0.5-> entries `star`
               //and ...
               pure (forall eid.  //for every epoch
                        //if you compute the hashes for that epoch by runnin the 
                        //verifier on entries
                        let (hadd, hevict, agg) = epoch_hash eid entries in
                        if agg 
                        then (
                          //Then, if that epoch has been marked for aggregation
                          //the ghost state includes exactly those hashes for eid, tid
                          epoch_hashes_ghost eid tid = (hadd, hevict)
                        )
                        else (
                          //Otherwise, this epoch eid is not yet ready for aggregation 
                          //in thread tid, and so the ghost hashes are both just zero
                          epoch_hashes_ghost eid tid = (zero, zero))) `star`
                        )
          //Finally,
          (exists n. 
            //the lock protects full ownership of the max_certified_epoch ref
            max_certified_epoch -1-> n `star`

            //epoch n is certified
            pure (epoch_hashes.[n].certified) `star`
            
            //and all epochs that are certified are no greater than n
            pure (forall eid. certified (epoch_hashes.[eid]) <==> eid <= n))
    );
}

////////////////////////////////////////////////////////////////////////////////
// Working with these invariants 
////////////////////////////////////////////////////////////////////////////////

(* The general idea to keep in mind is that this whole thing works
   like an Owicki-Gries parallel increment of a counter, where 
   
    1. there is a variable shared among several thread
    
    2. the current value of that variable is combination of all
       threads' "contributions"

    3. We keep track of each thread's contribution in a per-thread
       ghost variable, and each thread owns "half" of its contribution
       ghost variable.

    4. A lock/invariant owns the other half of each thread's
       contribution variable and relates the concrete shared variable
       to all the contribution ghost variables.

In our setting, the workflow goes something like this. 

We have two main API calls:

  - val verify_log tid (len:u32) (entries: array len bytes)
                       (len': _ ) (out: array len' bytes)
      : bool
      
  - val get_max_certified_epoch ()
      : option int

*)

let verify_log tid len entries = 
  {emp}
  let p = with_invariant top_level_inv ( .. ) in
  {local_state_hdl -p-> ls_repr}
  let tid_state = local_state_hdl.[tid] in
  acquire (tid_state.lock);
  {local_state_hdl -p-> ls_repr `star` ... lock invariant ..}
     { ... lock invariant ... }
    verify_log_entries  //we pass it all the tid_state minus the lock
      tid_state.mylogref
      tid_state.logref  
      tid_state.vtls
      tid_states.epoch_hashes
      len
      entries
     { ... lock invariant ... }      
  release (tid_state.lock)

// Now, in verify_log_entries, we encounter at some point a verify_epoch entry
// At that point, we will propagate the hashes to the aggregate state.
// It looks something like this:

let verify_log_entry mylogref logref vtls hashes entry =
  if (entry = Verify_next_epoch)
  then (
    let eid = bump_epoch vtls in
    set_aggregate_flag hashes eid;
    mylogref := !logref @ [entry];
    
    let sh = aehs_handle in
    acquire (sh.lock);

    //update ghost state with this thread's contribution
    sh.aehs_ghost := 
      upd (!sh.aehs_ghost)
          vtls.tid
          (hashes.[eid].hadd, 
           hashes.[eid].hevict);

    //concretely update the hadd and hevict
    ha.aggregate sh.aehs.[eid].hadd hashes.[eid].hadd;
    ha.aggregate sh.aehs.[eid].hevict hashes.[eid].hevict;    
    set_bit vtls.tid sh.aehs.[eid].tid_complete;

    //update the logref to commit all of logref
    logref := !mylogref;
    
    release (sh.lock);
  )
  else (
    ... handle as usual and extend mylogref ...
    
    mylogref := !logref @ [entry]
  )
  
////////////////////////////////////////////////////////////////////////////////

let get_max_certified_epoch () = 
    let sh = aehs_handle in
    let result = new_local 0 in
    acquire (sh.lock);
    let next = new_local (!sh.max_certified_epoch + 1) in
    while (sh.aehs.[next].tid_complete == all_ones)
    {
      if sh.aehs.[next].hadd == sh.aehs.[next].hevict
      then (
        sh.aehs.next.certified := true;
        sh.max_certified_epoch := next;
        free_epoch sh.aehs next;
        next := next + 1;
      ) 
      else (
        release sh.lock;
        raise (Failed_epoch next)
      )
    };
    result :=  !sh.max_certified_epoch;
    release sh.lock;
    result

  


    
  

