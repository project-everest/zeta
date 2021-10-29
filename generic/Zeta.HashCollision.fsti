module Zeta.HashCollision

open FStar.Seq
open Zeta.App
open Zeta.HashFunction
open Zeta.Record

(* a hash collision *)
type hash_collision (app: app_params) =
  | ValueCollision: v1: value app ->
                    v2: value app {v1 <> v2 /\ hashfn v1 = hashfn v2} -> hash_collision app
  | KeyCollision: k1: app_key app.adm ->
                  k2: app_key app.adm {k1 <> k2 /\ app.keyhashfn k1 = app.keyhashfn k2} -> hash_collision app

let hash_collision_contra (app:app_params{False})
  : hash_collision app
  = ValueCollision (AppV Null) (AppV Null)
