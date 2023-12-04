# Zeta: Provably Correct, Concurrent Runtime Monitors for Stateful Services


See the following resources:

* [Project Zeta](https://www.microsoft.com/en-us/research/project/zeta-2/)

* [FastVer](https://dl.acm.org/doi/10.1145/3448016.3457312) at SIGMOD 2021

* [FastVer2](https://www.fstar-lang.org/papers/fastver2.pdf) at CPP 2022

* [Proof Outline](./notes/ProofOutline.md)

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

Technically, this is expressive enough to capture all safety
properties. Our hypothesis is that this is also useful to capture
aspects of real-world services.

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

* Note: there does not need to be a one-one correspondence between
  operation `o` and the monitor calls

  - for example, `o` might want to add up a payload of 6 records

  - we might do 6 monitor calls while storing the intermediate running
    sum in "verified memory", the same abstraction that protects the
    service state.

# Instantiating Zeta for a key-value store

```
state: {(k,v)}

put (k, v) {
  let r = read_record k in
  check(r.v = null); // or anything here (check (r.v <= v)
  write_record {r with v}
}

get (k) {
  let r = read_record k in
  sign({op_id; cur_epoch; get(k); r.v}) // attest that `op_id: get(k)` returns `r.v` in `cur_epoch`
}
```

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
