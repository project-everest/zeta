module Zeta.EAC

open Zeta.SeqMachine
open Zeta.SeqAux

let eac_state_of_base_key
  (#app: app_params)
  (l: vlog_ext app)
  (k: base_key): eac_state app k
  = seq_machine_run (eac_smk app k) l

let eac_state_transition_aux
  (#app: app_params)
  (l: vlog_ext app {length l > 0})
  (k: base_key)
  : Lemma (ensures (let open Zeta.SeqAux in
                    let n = length l - 1 in
                    let l' = prefix l n in
                    let ee = index l n in
                    let es' = eac_state_of_base_key l' k in
                    let es = eac_state_of_base_key l k in
                    es = eac_add ee es'))
          [SMTPat (eac_state_of_base_key l k)]
  = admit()

let eac_state_transition
  (#app: app_params)
  (l: vlog_ext app {length l > 0})
  (k: key app)
  : Lemma (ensures (let open Zeta.SeqAux in
                    let n = length l - 1 in
                    let l' = prefix l n in
                    let ee = index l n in
                    let es' = eac_state_of_key l' k in
                    let es = eac_state_of_key l k in
                    es = eac_add ee es'))
  =

  admit()

let eac_empty_log
  (#app: app_params)
  (l: vlog_ext app {length l = 0})
  : Lemma (ensures (eac l))
          [SMTPat (eac l)]
  = admit()

let eac_induction_step_helper
  (#app: app_params)
  (l: vlog_ext app)
  (i: seq_index l {eac (prefix l i)})
  : o: (option base_key)
    {
      o = None /\ eac (prefix l (i + 1))
          \/
      (let k = Some?.v o in
       eac_state_of_key (prefix l (i + 1)) k = EACFail)
    }
  = admit()

let rec max_eac_prefix_aux
  (#app: app_params)
  (l:vlog_ext app)
  : Tot (ki: (base_key & nat) {
      let k,i = ki in
      eac l /\ i = length l
          \/
      i < length l /\
      eac (prefix l i) /\
      ~ (eac (prefix l (i + 1))) /\
      ~ (valid (eac_smk app k) (prefix l (i + 1)))
      })
     (decreases (length l))
  = let n = length l in
    if n = 0 then Zeta.BinTree.Root (* any key since eac*), 0
    else
      let n = n - 1 in
      let l' = prefix l n in
      let ee = index l n in
      let i' = max_eac_prefix_aux l' in
      admit()


let eac_implies_prefix_eac
  (#app: app_params)
  (l: eac_log app)
  (i: nat {i <= length l})
  : Lemma (ensures (eac (prefix l i)))
  =

  admit()

let max_eac_prefix
  (#app: app_params)
  (l:vlog_ext app)
  : (i:nat{eac l /\ i = length l
          \/
          i < length l /\
          eac (prefix l i) /\
          ~ (eac (prefix l (i + 1)))})
  = admit()

(* computable version of eac *)
let is_eac_log (#app: app_params) (l:vlog_ext app): (r:bool{r <==> eac l})
  = let i = max_eac_prefix l in
    if i = length l
    then true
    else false
