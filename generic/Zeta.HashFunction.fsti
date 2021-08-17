module Zeta.HashFunction

open Zeta.Hash
open Zeta.App
open Zeta.Record

val hashfn (#aprm: app_params) (v: value aprm): Tot hash_value
