# Structure of Refinement from Spec --> Low* Code

## Overview

The goal is to connect the high-level math proof (in the top-level directory) to an implementation that can be run on a machine (in the `low-level` sub-directory). We will do this by showing that the low-level code simulates the high-level formalism, via a series intermediate steps that reduce proof complexity. The stages of moving from the high-level specification to the low-level code are shown below.
1. **Spec** The high-level model where the proof of correctness is given. The store is modelled as a functional map from keys to values.
2. **InterSKC** Intermediate representation with Slots, Keys, and runtime Checks for duplicate entries. The store is modelled as a sequence of (key, value, add_method) triples. Log entries record both keys and the "slot_id" used to index into the sequence. At every add, it performs a search through the entire store to see if a key has been added previously.
3. **InterSK** Intermediate representation with Slots and Keys. Stores extra information in merkle nodes to determine if a key is already present, but relies on hash validation to eventually find the case where a key has been added multiple times using Blum.
4. **InterS** Intermediate representation with Slots. Logs do not contain keys.
5. **Low**  Low* implementation. Same as **InterS** except it uses C-compatible data types (e.g. Buffer instead of Seq).

**TODO:** All the levels of the current formalization assume a single epoch (i.e. one "offline" verification step). The Low* code should be modified to support multiple epochs, and we should add another layer after **InterS** (e.g. **InterE**) that introduces epochs.

## Log Types

In the intermediate levels above, we use a few different types of logs. For reference, the **Spec** level uses the following definition of log entries (in Veritas.Verifier).
```
type vlog_entry =
  | Get: k:data_key -> v:data_value -> vlog_entry
  | Put: k:data_key -> v:data_value -> vlog_entry
  | AddM: r:record -> k':merkle_key -> vlog_entry
  | EvictM: k:key -> k':merkle_key -> vlog_entry
  | AddB: r:record -> t:timestamp -> j:thread_id -> vlog_entry
  | EvictB: k:key -> t:timestamp -> vlog_entry
  | EvictBM: k:key -> k':merkle_key -> t:timestamp -> vlog_entry
```
**InterSKC** and **InterSK** use log entries with both keys and their corresponding slots. **InterS** and **Low** use log entries that only reference slots. For logs that reference both slots and keys, we need a predicate `skc` ("slot-key consistent") that says that the two are consistent.

**TODO:** I haven't worked out the details yet, but the definition of `skc` will likely be similar to `eac` -- we need to make sure that if an entry says that key k is at slot s then k was most recently written to s & has not been evicted.

We call logs with keys `logK`, logs with keys and slots `logSK`, and logs with only slots `logS`. Assume we provide functions `add_consistent_keys : logS -> logSK` and `drop_slots : logSK -> logK`.

## Proof Structure

The property proved of **Spec** (Veritas.Correctness.fst) is:
```
let lemma_verifier_correct (gl: VG.hash_verifiable_log { ~ (seq_consistent (to_state_op_gvlog gl))}):
  hash_collision_gen
```
In English: if a global log is verifiable then if a (i.e. the events are sequentially consistent, modulo hash collisions). *Sequential consistency* says that there exists an ordering among the different thread's events such that any "Get k" reads the most recent value written to k.

The property we want for **Low** is similar, but uses a different notion of consistency since elements are accessed via slot id rather than key. If a (global) log is verifiable, then any "Get s" reads the most recent value written to `key_of`(s), where `key_of` can be determined by looking at the log (--> likely related to `skc`).

The property above for **Spec** implies the property we want for **Low** *provided* that we can prove the following: If **Low** says `log` is verifiable
* then **InterS** says `log` is verifiable where
* then **InterSK** says `log2` is verifiable where `log2=add_consistent_keys(log)`
* then **InterSKC** says `log2` is verifiable
* then **Spec** says the `log3` is verifiable where `log3=drop_slots(log2)`

Note that may be possible to prove equality rather than implication for some (all?) of these levels. For example, `InterSKC.verifiable log2 = Spec.verifiable log3`.

## Directory Contents

* Veritas.Intermediate.Logs.fst(i) - A definition of logs with keys and slots (vlogKS) and a definition with only slots (vlogS); utilities for converting between the two.
* Veritas.Intermediate.StoreSKC.fst(i) - Functions for manipulating a sequence of (key, value, add_method) triples. Used in VerifySKC.
* Veritas.Intermediate.VerifySKC.fst(i) - Description of **InterSKC** verification and proof that this simulates **Spec** verification.