module Veritas.Intermediate.Thread

open Veritas.Intermediate.Logs
open Veritas.Intermediate.VerifierConfig
open Veritas.Intermediate.Store

open Veritas.MultiSetHashDomain

let thread_id_logS vcfg = thread_id & logS vcfg
