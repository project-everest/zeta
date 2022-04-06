# A Proof of Correctness of the Zeta Protocol in Steel

Joint work with

Arvind Arasu, Aseem Rastogi, Tahina Ramananandro, and many others

including

Esha Ghosh, Kesha Hietala, Bryan Parno, Aymeric Fromherz, Jonathan
Protzenko, Ravi Ramamurthy, Srinath Setty, Donald Kossman, Johannes
Gehrke, Badrish Chandramouli, Alexander van Renen, Min Xu

# What is Zeta?


```
   Client  <--------------->  Stateful
                              Service

                              (E.g.,
                                  a database (Key-Value store, SQL, etc),
                                  a authentication-token service (password service, KeyVault...))

```

Skeptical client:

Is the service managing my data in a correct way?

  * Correctness in the sense of safety

For example: Key-Value store:

  * Client makes many `get(k)` and `put(k, v)` requests

  * Wants assurance that `get(k)` returns the value of the last `put(k, v)`

#  Many clients and many service threads/instances


```
  Client_0 <------.
   ...             \  .------> Service Instance 0
   ...              \/          ...
   ...              /\.------> Service Instance M
  Client_N <------./
```

There's a trace of requests made to each service instance

     Log 0: op_{0,0}, ..., op_{0, L0)
     ...
     Log M: op_{0,0}, ..., op_{0, LM)

Client wants an assurance that their response is compatible with a
sequentially consistent reading of the input logs. i.e.,

Given logs `L0, ... LM`
there exists an interleaving of the log entries,
compatible with the observed result of each operation.

E.g., for Key-Value stores, this means that there is an interleaving
of the logs such that each `get(k)` returns the value of the most
recent `put(k,v)` preceding it.

# Generic

Each operation

 * has some application-specific, operation-specific arity
 * can additinally read and write some abstract state
 * can perform some pure operations (arithmetic, comparisons etc.)
 * can declare success or failure

I.e., the application's operations define an abstract state machine

And we want to ensure that

 * There is an intervleaving of logs L0,...,LM

 * The forms a sentence in the language accepted by the abstract state machine
    i.e., no operation fails

# How does Zeta ensure this? With a high-assurance runtime monitor


```
.-> Client_0 <------.
|    ...             \  .------> Service Instance 0 ----.  ------> Monitor 0 ----.
     ...              \/          ...                    \/                      |
|    ...              /\.------> Service Instance M ---- /\------> Monitor K ----.
.-> Client_N <------./                                                           |
|                                                                                |
|                                                                                |
.--------------------------------------------------------------------------------.
```

Augment the service with several runtime monitors
  (e.g., one per service thread, or some other config)

Monitor maintains authenticated data structure that is an relational
abstraction of the state of the service, i.e.,

- The state of the service is a modeled as a set of relations, with
  the total size of the relations being bounded by a very large
  constant, e.g., 2^256 records

The Monitor runs in a trusted execution environment (e.g, SGX,
TrustZone etc.)

 * on a small TCB (so no reliance on an OS stack etc)

 * and all its executable code is formally verified for correctness
   (more on that later)

## Memory integrity: Authenticated state abstraction

The state is authenticated using the following techniques:

1. Enclave memory: A small amount of integrity-protected memory (~ 32K
   memory slots, each a few bytes)

2. A sparse Merkle tree with incremental updates

     - lots of recent work on many variants of Merkle trees,
       often for append-only workloads.

     - We have a new one, that is sparse and optimized also for
       updates

3. Deferred memory verification based on multiset hashing

     - Evolving an idea from Blum et al. 1991,
       then Concerto (Arasu et al, 2017), ...

## Some intuition for how these techniques work together

* System is initialized with a cryptographic summary of the entire
  state of the service

* When service instance `I` receives an operation `o` from a client,
  it services the operation as usual and returns the result `v` to the
  client. But, as it does it issues a "shadow" operation to the
  monitor as

    - Suppose the operation `o` needs to read or write some records R
      in the system

    - The service issues commands to one of the monitor threads to
      load those records into its enclave memory:

        * In order to do this, the service will have to prove to the
          monitor that the records it is loading are accurate with
          respect to the current authenticated abstraction of those
          records

          E.g., it'll have to prove that the hash of those records is
          compatible with the Merkle root hash

              -- But instead of computing a chain up to the root, our
                 "incremental" Merkle tree allows it to compute
                 something much smaller and more efficient

     - Then, once those records are loaded into enclave memory, it
       asks the monitor to perform an abstraction of operation `o`
       and to certify that the result of running `o` is `v`

     - When the application decides that a particular record has gone
       "cold" it can unload it from the enclave memory, but the
       Monitor will insist to  "move the record" to one of the
       cryptographic mechanisms (e.g., add it back to the Merkle
       tree), to ensure that that record is still integrity protected.

     - Periodically, at configurable "epoch" boundaries, some hashes
       from the individual Monitor threads are aggregated, and if the
       hashes check out then:

         - All operations up to that epoch are provably sequentially
           consistent, except with a negligible probability of a hash
           collision

         - Further, once an epoch is certified, the monitor can issue
           a cryptographic signature (actually, a keyed MAC, for
           efficiency) to the client attesting that all their
           operations in the epoch were executed correctly.

         - Otherwise, the monitor has detected a potential safety
           violation of the system and can report it.

# FastVer

At SIGMOD 2021, we described using an initial version of this Zeta to
add integrity protections to the FASTER key-value store

* Baseline: FASTER throughput is around 100 million operations/sec
  with 32 worker threads

* With out integrity protections, FastVer with 32 monitor threads (one
  per worker) has a throughput of

   * 50 million operations/sec, with an epoch window of ~10 seconds

   * 38 million operations/sec, with an epoch window of ~1 seconds

So, at around a 2-4x overhead, we Zeta offers safety protections for a
state of the art high-performance key-value store

Compare, e.g., with other approaches, e.g., based on Merkle trees
alone, where overheads for memory protection are multiple orders of
magnitude.

Also, 50M op/s is already faster than many other off-the-shelf
key-value stores

# Proving the correctness of the Zeta monitor using F*

## Aka, verifying the Zeta verifier

  A stepwise refinement proof, in 4 steps
```
  ------------------------------------------------.---------------------------
                |                                 |
  High-level    | High-level repr of records      | Verifiers accept
  spec          | 256 bit record identifiers      | only sequentially consistent logs
                |                                 | except for Merkle collision
  --------------.---------------------------------.----------------------------
                |                                 |
  Intermediate  | Add a sub protocol to bind      | Verifiers accept
  verifier      | record ids to shorter 16-bit    | only S.C logs
                | ids.                            | except for Merkle collision
                |                                 |
  --------------.---------Simulation proof--------.-----------------------------
                |                                 |
  Low-level     | Move to low-level binary        | ... S.C. logs
  verifier      | reprs (using EverParse)         | except for Merkle collision
                | Add multiset hashes             | or multiset hash collision
                |                                 |
  --------------.-------Functional correctness----.------------------------------
                |                                 |
  Imperative    | Executable imperative code      | ... S.C. logs
  code (Steel)  | Epoch management                | except for Merkle collision
                | Explicit state aggregation      | or multiset hash collision
                |                                 |
  ----||--------.----------------------------------------------------------------
      ||
      || F* + Karamel
      ||
      \/
     Zeta.{c,h} +
     Formats.{c,h} + (EverParse)
     Hacl.{c,h}      (HACL* crypto)
```

 Zeta.{c,h}    ~ 4,000 LOC
 Formats.{c,h} ~ 3,000 LOC (Auto-generated from EverParse spec,
                            spec carefully designed by Tahina)

 Total F* + Steel code & proof: About 43 KLOC

 About 6 KLOC is utils (probably end up as additions to F* stlib)

 About 22 KLOC is just the protocol proof High/Intermediate part

  - Proof almost all done by Arvind!

  - But, with some contributions from Kesha Hietala and me (Nik) from
    Kesha's internship in 2020/2021

 Remaining 16 KLOC is Steel + Low Level verifier
  - Aseem, Arvind, and me (Nik), in the last ~6 months


# High-level takeaways (1)

Proof experience:

  - Incredibly subtle protocol proof.

  - Many small design-level bugs found and fixed as part of the proof.

  - And even at Steel implementaion level, many bit-fiddling tricks
    etc., impossible (at least for me) to get right without proofs.

  - The use of the tool around the math proof (High, Intermediate) was
    pretty good. This was Arvind's first real F* development and he
    was very productive, very quickly

      - Several earlier versions of the proof involved a lot of
        repeated boilerplate

      - Arvind's newer version got rid of ~1/3 of the code and made it
        much more generic

      - But, still, a lot of the proof is juggling things across
        different representations, and maybe there's some way to
        systematically automate such proofs (homotopy, cough???!!)

  - Steel part of the proof also involved several versions, wrestling
    with prover performance until we settled on a style that is
    predictable and efficient though quite verbose

       - Now, trying to automate some parts of it (new experiments
         with Tahina)

  - But, the overall modular structure of the proof and the way in
    which we managed ownership, locks, invariants etc. was very
    modular and clean.

# High-level takeaways (2)

Applications:

We think Zeta is a very flexible, general purpose, cryptographic
safety monitor

It can be used to retrofit existing services, for which verification
is impossible/too costly, with strong safety guarantees

FastVer was a great proof of concept, that this can work, and can come
at not too great cost

  - E.g., compare against Amazon's QLDB, which offers much weaker guarantees

Some things we are looking at:

  - Azure Purview: Governance of Data Estates

    Can we use Zeta to ensure that the correct access control policies are enforced?


# A dive into an interesting part of the proof

## Top-level theorem in Steel

Two main functions in the API


1. Feed a monitor a `input` of log entries

```
val verify_log (#p:perm)
               (#t:erased top_level_state)
               (#entries:erased AEH.log)
               (#log_perm:perm)
               (#log_bytes:erased bytes)
               (#out_bytes:erased bytes)
               (r:R.ref top_level_state)
               (tid:tid)
               (len: U32.t { len <> 0ul })
               (input:larray U8.t len)
               (out_len: U32.t)
               (output:larray U8.t out_len)
  : STT
    (option (v:V.verify_result { V.verify_result_complete len v }))
    (R.pts_to r p t `star`
     core_inv t `star`
     A.pts_to input log_perm log_bytes `star`
     A.pts_to output full_perm out_bytes `star`
     log_of_tid t tid entries)
    (fun res ->
       R.pts_to r p t `star`
       //Roughly states functinoal correctness,
       //that the verifier processed the logs according to the low-level spec
       //and that in doing so it maintained `core_inv t`
       verify_post t tid entries log_perm log_bytes len input out_len out_bytes output res)
```


2. Query a monitor thread to find out the maximum certified epoch


```
val max_certified_epoch (#p:perm) (#t:erased top_level_state) //implicit ghost args
                        (r:R.ref top_level_state)
  : STT // Steel function: Can read / write state, use locks, create and run threads etc.
    AEH.max_certified_epoch_result
        (R.pts_to r p t)
        (fun res ->
           R.pts_to r p t `star`
           (match res with
            | AEH.Read_max_none ->
              //no epoch has been certified yet
              emp

            | AEH.Read_max_error ->
             //underspecified low-level error:
             //e.g., processing this request would trigger integer overflow
             emp

            | AEH.Read_max_some max ->
              exists_ (fun logs ->
                //All monitor threads have processed at least logs
                snapshot t (AEH.map_of_seq logs)
                 `star`
                //And those logs are S.C up to epoch max, except if hash collision
                pure (sequentially_consistent_app_entries_except_if_hash_collision logs max))))
```

# A glimpse into one part of the proof

  N verifier threads, each with their state

## Per-thread state:

      `epoch_map         : Map.t epoch_id hashes`
      `processed_entries : seq log_entry` //ghost

   Per-thread invariant:

      `spec_verifier processed_entries == epoch_map`

   Every time the service call `verify_log` on a given thread, we
   process each `log_entry` one by one, accumulating them in
   `processed_entries` and proving that we maintain the per-thread
   invariant


## Shared state:

   Periodically, when a thread processes an "EpochFinished" log entry,
   it has to propagate some of its local state from `epoch_map` to a
   shared `aggregate_epoch_map`.

   We call this "committing" its entries up to that epoch to the
   shared state.

   Shared state:

   ```
      aggregate_epoch_map   : Map.t epoch_id hashes
      all_committed_entries : Map.t thread_id (seq processed_entries)
   ```

   Global invariant:

      ```
       let all_epoch_maps = run_all_verifiers all_committed_entries in

       aggregate_epoch_map == aggregate all_epoch_maps /\
       forall tid. all_processed_entries tid <= "processed_entries of tid"
      ```
                                                       ^
                                                       |
                                                    informal
# How to make this formal?

## First, a bit about Steel: Ownership

   Steel is a concurrent separation logic (CSL)

   In CSL, if you have a procedure `f` with a pre-condition `P` and postcondition `Q`

   Then, it means that when you call `f`:

     * you must currenly have ownership of whatever resource is described by `P`,
       and give-up permission to that resource to `f`

     * and when `f` returns, you can continue with `Q`

   Ownership on a resource can come in many flavors. A common one is
   fractional permissions

     - `p -1.0-> v` : Means that pointer `p` points to `v` and you have
                      full permission on `p`, and no one else has any
                      permission on it

     - `p -f-> v` : for `f < 1.0`, means that pointer `p` points to `v`
                    and you only have read permission on it

     - And you can split and combine permissions
         `p -f-> v * p -g-> v <==>  f+g<=1.0 `star` p -f+g-> v


# Back to Zeta thread invariants:

  How to make it formal? Main challenge

     * Ownership and synchronization

         Individual threads need to be able to update their processed_entries

         And they should be able to do so without synchronizing with other threads

           - so, you might think they need full permission on processed_entries

         But, to even state the global invariant, we need read permission on each
         threads processed_entries field

           - so, if the global invariant has some read permission, how can the
             individual threads retain full write permission

     * Also, don't forget, at the top-level we also have

          `snapshot t (AEH.map_of_seq logs)`

       which says that all threads processed_entries are ahead of the `logs`

           So, some kind of read permission has to be given up in the post-condition
           of max_certified_epoch

  Fractional permissions are not going to cut it

# Stable knowledge

  But, if what we're saying in the global invariant is

    * That every thread's processed entries is ahead of what's record in all_committed_entries

    * A thread never changes its committed prefix and only keeps extending its log

    * Then everything should be fine: A thread can independently extend its log without
      breaking what is committed in the shared invariant, since the shared invariant
      is stable with respect to extension-only updates by individual threads.

    * An additional subtlety: But we don't want a thread to proceed
      indefinitely without committing some of its entries. So, what we want to say is

      "a thread's processed entries can be ahead of its committed entries,
       but not too far ahead", e.g., every time the thread's processed entries
       has an EpochFinished entry, it *MUST* commit to the shared state.

  Snapshot:

    * It's also fine to take a snapshot of all the thread states, so long as what
      is in the snapshot remains true

# Encoding Sharing Disciplines with Partial Commutative Monoids

  What is a PCM? A algebraic gadget that's become a popular way of
  structure sharing disciplines in separation logic

   - Since around 2009--2012
       (Separation Algebras; Dockins, Hobor, Appel at al.;
        Fictional Separation Logic; Jensen and Birkedal)

   - Now, also in Iris, Steel, etc.

## PCM
```
  type pcm a = {
    u: a;       //unit element
    composable: a -> a -> prop;
    op : x:a -> y:a{composable x y} -> a;
    associative_op: ...;
    commutative_op: ...;
    is_unit: ...;
  }
```

  A core rule of the Steel logic is that you can store, in ghost
  state, a value from any user-chosen PCM.

  And the rule we saw earlier about fractional permissions is actually
  a special case of the rule for any PCM.

  The main "points to" predicate from Steel actually looks like this:


  ```
    r -p-> v
  ```

   where `r:ref a`
         `p:pcm a`
         `v:a`

  And says that `r:ref a` points to `v:a`, where `p:pcm a` governs
  ownership of `r`.

  In particular, now we have this rule:


  ```
    (r -p-> v0 `star` r -p-> v1)

       <==>

    p.composable v0 v1 `star` r -p-> (p.op v0 v1)
  ```

  Compare this with the fractional permission rule, shown again here;

```
    p -f-> v * p -g-> v
       <==>
    f+g<=1.0 `star` p -f+g-> v
```

   where I'd define `p -f-> v` as `p -frac-> (f,v)`, i.e., in teh `frac` PCM,
   `p` points to `v` with `f`-permission.

# Ok, cool generalization, but what is this PCM stuff useful for?

We'll encode our "stable knowledge" sharing discipline for Zeta by
designing a new PCM that I'm calling "Fractional Preorders with
Snapshots and Anchors" PCM (FPSA)

# The FPSA PCM

## Fractions

   Ownership of the state is controlled by a fractional permission, so
   multiple threads may share read-only privileges on the state, but
   only one can have write permission.

## Preorders

   The state is governed by a preorder `p` and all updates to the
   state must respect the preorder (a reflexive, transitive relation
   on the state)

     - In our case, the preorder will be "append only updates to the log"


## Snapshots

   Since the state always evolves by a preorder, it is possible to
   take a snapshot of the state. A snapshot does not confer any
   particular ownership on the state, except knowledge of a snapshot
   ensures that the current state is related to the snapshot by the
   preorder.

     - If we take a snapshot of the logs, we know that the current logs
       of each thread will always be ahead of the snapshot

## Anchors

   Anchors are a kind of refinement of the preorder. If a thread
   owns an anchored value `v`, then no other thread, even a thread
   owning a full fractional permission, can advance the state "too
   far" from the anchor.

   In particular, the PCM is parameterized by a binary relation on
   values, `anchors:anchor_relation`. If a thread owns the anchor `v`,
   then the current value `cur` of the state must be in relation
   `anchors v cur`.

   This can be used to ensure that the knowledge of one thread is
   never too stale.

   - In Zeta, we'll say that the global invariant owns an anchor on
     the committed prefix and the anchor relation prevents any
     thread's log from advancing too far beyond the anchored prefix.

# Abstract predicates derived from FPSA

First, a map from threads to their logs

```
let logs = Map.t tid (option log)
```

And the type of a handle to ghost state maintaining logs for all
threads

```
  val t : Type
```

Concretely, the type of a reference to a map from thread_ids to
element of an FPSA PCM over Zeta logs.


## Global anchor

The last commited state of all threads is `m`

```
val global_anchor (x:t)
                  (m:logs)
  : vprop
```

## Single-thread ownership

Indicates ownership of the log `l` for thread `d`

The state may be ahead of the global anchor.

If `with_anchor` is set and `frac == full_perm`, then this indicates
exclusive ownership of that thread's log---no other thread owns an
anchor on the thread and this grants full permission to the owner to
update the log.

```
val tid_pts_to (x:t)
               (t:tid)
               (frac:perm)
               (l:log)
               (with_anchor:bool)
  : vprop
```

## Multi-thread ownership

Same as above, but for a `logs` map:

```
val tids_pts_to (x:t)
                (frac:perm)
                (l:logs)
                (with_anchor:bool)
  : vprop
```


## Snapshot

The state of all threads is at least `m`:

```
val global_snapshot (x:t) (m: logs)
  : vprop
```

# The invariant again, now with FPSA

   Shared state:

      `aggregate_epoch_map   : epoch_id -> hashes`
      `all_committed_entries : thread_id -> seq processed_entries`

   Global invariant:

   ```
     val all_logs_hdl : t
     val aggregate_epoch_hashes : array epoch_id hashes

     let global_invariant =
         exists_ (fun logs ->
          global_anchor all_logs_hdl logs `star`
          aggregate_epoch_hashes -1.0-> aggregate (run_all_verifiers logs))
   ```

   Per-thread invariant:

    ```
      val local_epoch_map : array epoch_id hashes

      exists_ (fun log ->
        tid_maps_to all_logs_hdl tid log false `star`
        local_epoch_map -1.0-> spec_verifier log)
    ```

# Ghost Operations

## Allocation

```
/// [alloc] : Initialize the ghost state
///
///  -- Get an anchor on the empty state. this is used to allocate the
///     aggregate epoch hash lock
///
///  -- And a full fraction on the all the thread logs initialize to empty
val alloc (_:unit)
  : STGhostT t
    emp
    (fun t -> tids_pts_to t 1.0 (Map.const (Some Seq.empty)) false `star`
              global_anchor t (Map.const (Some Seq.empty)))
```

## Sharing (fractions)

```
//// [share_tids_pts_to]
///
/// Having allocated the state, share the [tids_pts_to] part so that
/// half can be given to the top-level client and the rest given to
/// each thread
val share_tids_pts_to (#f:perm)
                      (x:t)
                      (m:logs)
  : STGhostT unit
    (tids_pts_to x f m false)
    (fun _ -> tids_pts_to x (half_perm f) m false `star`
              tids_pts_to x (half_perm f) m false)
```

## Taking a single thread

`take_tid`: Extract a singleton ownership predicate for thread `t:tid`

```
val take_tid (#o:_)
             (#f:perm)
             (x:t)
             (m:logs)
             (t:tid { Some? (Map.sel m t) })
  : STGhostT unit o
    (tids_pts_to x f m false)
    (fun _ -> tid_pts_to x t f (Some?.v (Map.sel m t)) false `star`
              tids_pts_to x f (Map.upd m t None) false)
```

`put_tid`: Give up a singleton ownership predicate for `t:tid` (converse)

## Updating a log, without advancing too far

This is used in the Zeta.Steel.Verifier, when extending the log
with an entry that is not finishing an epoch.

In this case, the thread is free to extend the log without
synchronizing with the shared state and commiting anything

```
val update_tid_log (#o:_)
                   (x:t)
                   (t:tid)
                   (l0 l1:log)
  : STGhost unit o
    (tid_pts_to x t full_perm l0 false)
    (fun _ -> tid_pts_to x t full_perm l1 false)
    (requires
      l0 `log_grows` l1 /\  //we're only extending (preorder)
      l1 `compat_with_any_anchor_of` l0 //but not too far
     )
    (ensures fun _ -> True)
```

## Update a log and commit, but requires full ownership including the anchor


Taking ownership of the anchor for `t`


Note, the postcondition is the "main property". It relates the
anchor to the current state---the anchor is the committed
current log `l`

```
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
```

And now you can update:

With exclusive ownership, you can update a the log of `t` to
`l1` so long as `l1` is itself committed.

```
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
```

# PCM takeaway

* They're fun!

* They're very expressive

   - Can use them to encode spatial and temporal ownership over
     resources

* Find the right PCM to structure your ghost state and the rest of the
  proof just flows
