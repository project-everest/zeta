module Zeta.TimeKey

open Zeta.Time
open Zeta.Key

let timestamp_key = timestamp & base_key

(* < *)
let lt (tk1 tk2: timestamp_key)
  = let t1,k1 = tk1 in
    let t2,k2 = tk2 in
    t1 `ts_lt` t2 || t1 = t2 && k1 `Zeta.BinTree.lt` k2

(* <= *)
let lte tk1 tk2 = tk1 = tk2 || tk1 `lt` tk2

(* > *)
let gt tk1 tk2 = tk2 `lt` tk1

(* >= *)
let gte tk1 tk2 = not (tk1 `lt` tk2)

val lt_is_total (tk1 tk2: timestamp_key)
  : Lemma (ensures (tk1 = tk2 /\ ~ (tk1 `lt` tk2) /\ ~ (tk2 `lt` tk1) \/
                    tk1 <> tk2 /\ (tk1 `lt` tk2 \/ tk2 `lt` tk1)))
          [SMTPat (tk1 `lt` tk2)]

val lt_is_transitive (tk1 tk2 tk3: _)
  : Lemma (ensures (tk1 `lt` tk2 ==> tk2 `lt` tk3 ==> tk1 `lt` tk3))
