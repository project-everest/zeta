# Structure of Refinement from Spec --> Low* Code

## Overview

The goal is to connect the high-level math proof (in the 'high' directory) to an implementation that can be run on a machine (in the `low` directory). We will do this by showing that the low-level code simulates the high-level formalism, via a single intermediate step that reduce proof complexity. The stages of moving from the high-level specification to the low-level code are shown below.
1. **Spec** The high-level model where the proof of correctness is given. The store is modelled as a functional map from keys to values.
2. **Inter** The store is modelled as a sequence of (key, value, add_method) entries, with two extra bits to determine if a key has been added to the store via Merkle. Log entries record "slot_id"s used to index into the sequence; adds, gets, and puts also include argument keys.
3. **Low**  Low* implementation. Same as **Inter** except it uses C-compatible data types (e.g. Buffer instead of Seq).

**TODO:** All the levels of the current formalization assume a single epoch (i.e. one "offline" verification step). The Low* code should be modified to support multiple epochs, and we should add another layer after **Inter** (e.g. **InterE**) that introduces epochs.

## Log Types

The **Spec** level uses the following definition of log entries (in Veritas.Verifier).
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
The **Inter** level uses log entries with "slot ids" (in Veritas.Intermediate.Logs).
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

We call logs with keys `logK`, logs with slots `logK`, and low-level logs `logL`. We provide a function `logS_to_logK : logS -> logK` that converts from a `logS` to a `logK` using the **InterSC** level verifier. Assume we also provide a `logL_to_logS` function, which should be a simple conversion.

## Proof Structure

The property proved of **Spec** (Veritas.Correctness.fst) is:
```
let lemma_verifier_correct (gl: VG.hash_verifiable_log { ~ (seq_consistent (to_state_op_gvlog gl))}):
  hash_collision_gen
```
In English: if a global log is verifiable then if a (i.e. the events are sequentially consistent, modulo hash collisions). *Sequential consistency* says that there exists an ordering among the different thread's events such that any "Get k" reads the most recent value written to k.

The property we want for **Low** is identical: If a log is verifiable, then any "Get s k" reads the most recent value written to k. (Intermediate level verification will also check that k is stored at slot s, but this can be ignored in the final statement of correctness.)

[TODO]

## Directory Contents

* Veritas.Intermediate.Logs.fst - A definition of logs with slots (logS) and wrappers around high- and low-level logs (logK and logL) 
* Veritas.Intermediate.Store.fst(i) - Functions for manipulating a sequence of (key, value, add_method, l-bit, r-bit) records. Used in Intermediate.Verify.
* Veritas.Intermediate.Verify.fst(i) - Description of **Inter** verification and proof that this simulates **Spec** verification.
