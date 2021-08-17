module Zeta.Time

(**
 * Time in zeta is two dimensional, consisting of (epoch, counter). All verifier threads have
 * internal clocks tracking time of this format and these clocks are used to associate
 * timestamps to "events" - state machine transitions - which ultimately are used to
 * characterize correctness.
 *)

(**
 * The first component of time in zeta. An epoch is the unit of verification in the sense
 * all events in an epoch are verified to be correct only after all threads transition
 * to the next epoch.
 *)
let epoch = nat

(**
 * A counter within an epoch.
 *)
let counter = nat

type timestamp = {
  e: epoch;
  c: counter;
}

(* next timestamp *)
let next (t: timestamp)
  = { e = t.e; c = t.c + 1 }

(* return the epoch of a timestamp *)
let epoch_of (t: timestamp)
  = t.e

(* first timestamp of an epoch *)
let first (e: epoch): timestamp
  = { e; c = 0 }

(* < relation of timestamps *)
let ts_lt (t1 t2: timestamp) =
  t1.e < t2.e || t1.e = t2.e && t1.c < t2.c

(* >= relation of timestamps *)
let ts_geq (t1 t2: timestamp) =
  not (ts_lt t1 t2)

(* <= relation of timestamps *)
let ts_leq (t1 t2: timestamp) =
  t1 = t2 || t1 `ts_lt` t2

(* > relation of timestamps *)
let ts_gt (t1 t2: timestamp): bool =
  not (t1 `ts_leq` t2)

let max (t1 t2: timestamp) =
  if t1 `ts_lt` t2 then t2 else t1
