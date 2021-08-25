module Zeta.EAC

open Zeta.SeqMachine
open Zeta.SeqAux

let eac_state_of_base_key
  (#app: app_params)
  (k: base_key)
  (l: vlog_ext app)
  : eac_state app k
  = seq_machine_run (eac_smk app k) l

let eac_state_transition_aux
  (#app: app_params)
  (k: base_key)
  (l: vlog_ext app {length l > 0})
  : Lemma (ensures (let open Zeta.SeqAux in
                    let n = length l - 1 in
                    let l' = prefix l n in
                    let ee = index l n in
                    let es' = eac_state_of_base_key k l' in
                    let es = eac_state_of_base_key k l in
                    es = eac_add ee es'))
          [SMTPat (eac_state_of_base_key k l)]
  = let n = length l - 1 in
    let l' = prefix l n in
    let ee = index l n in
    let smk = eac_smk app k in
    lemma_hprefix_append_telem l;
    lemma_reduce_append (init_state smk) (trans_fn smk) l' ee

let eac_state_transition
  (#app: app_params)
  (k: key app)
  (l: vlog_ext app {length l > 0})
  : Lemma (ensures (let open Zeta.SeqAux in
                    let n = length l - 1 in
                    let l' = prefix l n in
                    let ee = index l n in
                    let es' = eac_state_of_key k l' in
                    let es = eac_state_of_key k l in
                    es = eac_add ee es'))
  = let bk = to_base_key k in
    eac_state_transition_aux bk l

let eac_empty_log
  (#app: app_params)
  (l: vlog_ext app {length l = 0})
  : Lemma (ensures (eac l))
          [SMTPat (eac l)]
  = lemma_empty l;
    let aux (k: base_key)
        : Lemma (ensures (valid (eac_smk app k) l))
                  [SMTPat (valid (eac_smk app k) l)]
      = lemma_empty_seq_valid (eac_smk app k)
    in
    ()


let rec search_keys_subtree (f: base_key -> bool) (k: base_key)
  : Tot (o: (option base_key)
    {
      o = None /\ (forall (k': base_key). Zeta.BinTree.is_desc k' k ==> f k')
        \/
      Some? o /\ not ( f (Some?.v o) )
    })
    (decreases (height k))
    = let open Zeta.BinTree in
      if not (f k) then Some k
      else if height k = 0 then (
        let aux (k':base_key)
          : Lemma (ensures (is_desc k' k ==> f k'))
          = if k' = k then ()
            else if not (is_desc k' k) then ()
            else assert(is_proper_desc k' k)
        in
        FStar.Classical.forall_intro aux;
        None
      )
      else
        let ol = search_keys_subtree f (LeftChild k) in
        let or = search_keys_subtree f (RightChild k) in
        if Some? ol then ol
        else if Some? or then or
        else (
          let aux (k': base_key)
            : Lemma (ensures (is_desc k' k ==> f k'))
            = if k' = k then ()
              else if not (is_desc k' k) then ()
              else
                let d = desc_dir k' k in
                if d = Left then ()
                else ()
          in
          FStar.Classical.forall_intro aux;
          None
        )

(* since the space of keys is finite, we can computationally determine if a property is true for all keys
 * or find a key if this is not the case *)
let search_keys (f: base_key -> bool)
  : o: (option base_key)
    {
      o = None /\ (forall (k: base_key). f k)
        \/
      Some? o /\ not (f (Some?.v o))
    }
  = let open Zeta.BinTree in
    let o = search_keys_subtree f Root in
    if None = o then (
      let aux (k: base_key)
        : Lemma (ensures (f k))
                [SMTPat (f k)]
        = lemma_root_is_univ_ancestor k
      in
      o
    )
    else o

let eac_induction_step_helper
  (#app: app_params)
  (l: vlog_ext app{let n = length l in n > 0 /\ eac (prefix l (n - 1))})
  : o: (option base_key)
    {let n = length l in
      o = None /\ eac l
          \/
          Some? o /\
          (let k = Some?.v o in
           eac_state_of_base_key k l = EACFail)
    }
  = let n = length l - 1 in
    let l' = prefix l n in
    let ee = index l n in
    let e = to_vlog_entry ee in
    let f = fun (k: base_key) -> valid (eac_smk app k) l in
    search_keys f

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
    if n = 0 then (
      eac_empty_log l;
      Zeta.BinTree.Root (* the returned key is don't care for eac l *), 0
    )
    else
      let l' = prefix l (n - 1) in
      let k,i' = max_eac_prefix_aux l' in
      if i' = n - 1 then
        let o = eac_induction_step_helper l in
        if None = o
        then Zeta.BinTree.Root, n
        else (
          let k = Some?.v o in
          let smk = eac_smk app k in
          assert(~ (valid smk l));
          k,n-1
        )
      else k,i'

let rec eac_implies_prefix_eac
  (#app: app_params)
  (l: eac_log app)
  (i: nat {i <= length l})
  : Lemma (ensures (eac (prefix l i)))
          (decreases (length l))
  = if i = length l then ()
    else
      let n = length l - 1 in
      let l' = prefix l n in
      let k,i' = max_eac_prefix_aux l' in
      if i' = n
      then
        eac_implies_prefix_eac l' i
      else
        let smk = eac_smk app k in
        lemma_valid_prefix smk l (i' + 1)

let lemma_eac_state_of_key
  (#app: app_params)
  (l: eac_log app)
  (k: key app)
  : Lemma (ensures (eac_state_of_key k l <> EACFail))
  = let bk = to_base_key k in
    let smk = eac_smk app bk in
    assert(valid smk l);
    ()

let max_eac_prefix
  (#app: app_params)
  (l:vlog_ext app)
  : (i:nat{eac l /\ i = length l
          \/
          i < length l /\
          eac (prefix l i) /\
          ~ (eac (prefix l (i + 1)))})
  = let _,i = max_eac_prefix_aux l in
    i

(* computable version of eac *)
let is_eac_log (#app: app_params) (l:vlog_ext app): (r:bool{r <==> eac l})
  = let i = max_eac_prefix l in
    if i = length l
    then true
    else false

let eac_value_base (#app: app_params) (k: key app) (l: eac_log app)
  : value app
  = let es = eac_state_of_key k l in
    match es with
    | EACInit -> init_value k
    | EACInStore _ v -> v
    | EACEvictedMerkle v -> v
    | EACEvictedBlum v _ _ -> v

let rec lemma_eac_value_compatible (#app: app_params) (k: key app) (l: eac_log app)
  : Lemma (ensures (Zeta.Record.compatible k (eac_value_base k l)))
          (decreases (length l))
          [SMTPat (eac_value_base k l)]
  = let n = length l in
    let bk = to_base_key k in
    let smk = eac_smk app bk in
    lemma_eac_state_of_key l k;
    if n = 0 then
      lemma_empty_seq_init smk l
    else (
      let l' = prefix l (n - 1) in
      let es' = eac_state_of_base_key bk l' in
      let ee = index l (n - 1) in
      let e = to_vlog_entry ee in
      lemma_eac_value_compatible k l';
      if not (e `refs_key` bk)
      then ()
      else
        match es' with
        | EACInit -> (
          match ee with
          | NEvict (AddM (k2,v) _ _) -> ()
          | _ -> ()
        )
        | _ -> ()
    )

let eac_value (#app: app_params) (k: key app) (l: eac_log app)
  : value_t k
  = eac_value_base k l

let eac_implies_valid_simulation (#app: app_params) (l: eac_log app)
  : Lemma (ensures (let fs = appfn_call_seq l in
                    Some? (simulate fs)))
  = admit()

let eac_state_is_app_state (#app: app_params) (l: eac_log app) (k: app_key app.adm)
  : Lemma (ensures (let fs = appfn_call_seq l in
                    let app_state,_ = Some?.v (simulate fs) in
                    let gk = AppK k in
                    eac_value gk l = AppV (app_state k)))
  = admit()
