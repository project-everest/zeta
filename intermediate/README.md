# Structure of Refinement from Spec --> Low* Code

## Overview

The goal is to connect the high-level math proof (in the top-level directory) to an implementation that can be run on a machine (in the `low-level` sub-directory). We will do this by showing that the low-level code simulates the high-level formalism, via a series intermediate steps that reduce proof complexity. The stages of moving from the high-level specification to the low-level code are shown below.
1. **Spec** The high-level model where the proof of correctness is given. The store is modelled as a functional map from keys to values.
2. **InterSC** Intermediate representation with Slots and runtime Checks for duplicate entries. The store is modelled as a sequence of (key, value, add_method) triples. Log entries record "slot_id"s used to index into the sequence; adds, gets, and puts also include argument keys. At every add, it performs a search through the entire store to see if a key has been added previously.
3. **InterS** Intermediate representation with Slots, without inefficient checks for existing keys. Stores extra information in merkle nodes to determine if a key is already present, but relies on hash validation to eventually find the case where a key has been added multiple times using Blum.
4. **Low**  Low* implementation. Same as **InterS** except it uses C-compatible data types (e.g. Buffer instead of Seq).

**TODO:** All the levels of the current formalization assume a single epoch (i.e. one "offline" verification step). The Low* code should be modified to support multiple epochs, and we should add another layer after **InterS** (e.g. **InterE**) that introduces epochs.

## Log Types

In the intermediate levels above, we use a three different types of logs. The **Spec** level uses the following definition of log entries (in Veritas.Verifier).
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
The **InterSC** and **InterS** levels use log entries with "slot ids" (in Veritas.Intermediate.Logs).
```
type logS_entry =
  | Get_S: s:slot_id -> k:data_key -> v:data_value -> logS_entry
  | Put_S: s:slot_id -> k:data_key -> v:data_value -> logS_entry
  | AddM_S: s:slot_id -> r:record -> s':slot_id -> logS_entry
  | EvictM_S: s:slot_id -> s':slot_id -> logS_entry
  | AddB_S: s:slot_id -> r:record -> t:timestamp -> j:thread_id -> logS_entry
  | EvictB_S: s:slot_id -> t:timestamp -> logS_entry
  | EvictBM_S: s:slot_id -> s':slot_id -> t:timestamp -> logS_entry
```
The **Low** level also uses a log with slot ids, but additionally uses C-compatible data types (TODO).

We call logs with keys `logK`, logs with slots `logK`, and low-level logs `logL`. We provide a function `logS_to_logK : logS -> logK` that converts from a `logS` to a `logK` using the **InterSC** level verifier. Assume we also provide a `logL_to_logS` function, which should e a simple conversion.

## Proof Structure

The property proved of **Spec** (Veritas.Correctness.fst) is:
```
let lemma_verifier_correct (gl: VG.hash_verifiable_log { ~ (seq_consistent (to_state_op_gvlog gl))}):
  hash_collision_gen
```
In English: if a global log is verifiable then if a (i.e. the events are sequentially consistent, modulo hash collisions). *Sequential consistency* says that there exists an ordering among the different thread's events such that any "Get k" reads the most recent value written to k.

The property we want for **Low** is identical: If a log is verifiable, then any "Get s k" reads the most recent value written to k. (Intermediate level verification will also check that k is stored at slot s, but this can be ignore in the final statement of correctness.)

The property above for **Spec** implies the property we want for **Low** *provided* that we can prove the following: If **Low** says `log` is verifiable
* then **InterS** says `log2` is verifiable where `log2=logL_to_logS(log)`
* then **InterSC** says `log2` is verifiable
* then **Spec** says the `log3` is verifiable where `log3=logS_to_logK(log2)`

Note that may be possible to prove equality rather than implication for some of these levels. For example, `InterS.verifiable log2 = InterSC.verifiable log2`.

## Directory Contents

* Veritas.Intermediate.Logs.fst - A definition of logs with slots (logS) and wrappers around high- and low-level logs (logK and logL) 
* Veritas.Intermediate.StoreSC.fst(i) - Functions for manipulating a sequence of (key, value, add_method) triples. Used in VerifySC.
* Veritas.Intermediate.VerifySC.fst(i) - Description of **InterSC** verification and proof that this simulates **Spec** verification.
* Veritas.Intermediate.StoreS.fst(i) - Functions for manipulating a sequence of (key, value, add_method, l_child_in_store, r_child_in_store) records. Used in VerifyS.
* Veritas.Intermediate.VerifyS.fst(i) - Description of **InterS** verification and proof that this simulates **InterSC** verification.
