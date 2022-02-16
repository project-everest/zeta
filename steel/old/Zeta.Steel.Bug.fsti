module Zeta.Steel.Bug
open Zeta.Steel.VerifierTypes
open Steel.ST.Util
open Zeta.Steel.FormatsManual
module M = Zeta.Steel.ThreadStateModel

val create (tid:tid)
  : STT thread_state_t
    emp
    (fun t -> thread_state_inv t (M.init_thread_state_model tid))
