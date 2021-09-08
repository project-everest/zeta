module Zeta.HashCollision

open FStar.Seq
open Zeta.App
open Zeta.HashFunction
open Zeta.Record

(* a hash collision *)
type hash_collision (app: app_params) =
  | Collision: v1: value app ->
               v2: value app {v1 <> v2 /\ hashfn v1 = hashfn v2} -> hash_collision app

let hash_collision_contra (app:app_params{False})
  : hash_collision app
  = Collision (AppV Null) (AppV Null)
