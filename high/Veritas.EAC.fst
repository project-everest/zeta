module Veritas.EAC

open Veritas.StateSeqMachine
module S = Veritas.State

//Allow the solver to unroll recursive functions at most once (fuel)
#push-options "--max_fuel 1 --max_ifuel 1 --initial_fuel 1 --initial_ifuel 1"

let lemma_comm_empty (le:vlog_ext{length le = 0}) (k:data_key):
  Lemma (to_state_op_vlog (to_vlog (partn eac_sm k le)) =
                  partn ssm k (to_state_op_vlog (to_vlog le)))
  =
  let lek = partn eac_sm k le in
  let lk = to_vlog lek in
  let lks = to_state_op_vlog lk in
  let l = to_vlog le in
  let ls = to_state_op_vlog l in
  let lsk = partn ssm k ls in
  lemma_empty le;

  (* since le is empty, lek & lk = filter on k le is empty *)
  lemma_filter_empty (iskey vlog_entry_ext_key k);
  //assert(length lek = 0);
  //assert(length lk = 0);

  (* since lk is empty, lks is empty *)
  lemma_filter_empty is_state_op;
  lemma_empty lk;
  //assert(length lks = 0);
  lemma_empty lks;

  //assert(length l = 0);
  lemma_empty l;
  //assert(length ls = 0);
  lemma_empty ls;
  lemma_filter_empty (iskey S.key_of k);
  //assert(length lsk = 0);
  lemma_empty lsk

let lemma_partn_state_append (le:vlog_ext{length le > 0}) (k:data_key):
  Lemma (requires (is_state_op (to_vlog_entry (index le (length le - 1))) /\
                   iskey vlog_entry_ext_key k (index le (length le - 1))))
        (ensures (to_state_op_vlog (to_vlog (partn eac_sm k le)) =
                  append1 (to_state_op_vlog (to_vlog (partn eac_sm k (prefix le (length le - 1)))))
                          (to_state_op (to_vlog_entry (index le (length le - 1)))))) =
  let n = length le in
  let lek = partn eac_sm k le in
  let lk = to_vlog lek in
  let lksr = filter_refine is_state_op lk in
  let lks = to_state_op_vlog lk in
  let le' = prefix le (n - 1) in
  let lek' = partn eac_sm k le' in
  let lk' = to_vlog lek' in
  let lksr' = filter_refine is_state_op lk' in
  let lks' = to_state_op_vlog lk' in

  let ee = index le (n - 1) in
  let e = to_vlog_entry ee in
  let op = to_state_op e in
  //assert(is_state_op e);
  //assert(vlog_entry_ext_key ee = k);

  lemma_filter_extend2 (iskey vlog_entry_ext_key k) le;
  lemma_prefix1_append lek' ee;
  //assert(lek = append1 lek' ee);

  lemma_map_extend to_vlog_entry lek;
  lemma_prefix1_append lk' e;
  //assert(lk = append1 lk' e);

  lemma_filter_extend2 is_state_op lk;
  assert(equal lksr (append1 lksr' e));
  lemma_prefix1_append lksr' e;

  lemma_map_extend to_state_op lksr;
  //assert(lks = append1 lks' op);
  ()

let lemma_partn_state_same (le:vlog_ext{length le > 0}) (k:data_key):
  Lemma (requires (not (is_state_op (to_vlog_entry (index le (length le - 1)))) \/
                   not (iskey vlog_entry_ext_key k (index le (length le - 1)))))
        (ensures (to_state_op_vlog (to_vlog (partn eac_sm k le)) =
                  to_state_op_vlog (to_vlog (partn eac_sm k (prefix le (length le - 1)))))) =

  let n = length le in
  let lek = partn eac_sm k le in
  let lk = to_vlog lek in
  let lksr = filter_refine is_state_op lk in
  let lks = to_state_op_vlog lk in
  let le' = prefix le (n - 1) in
  let lek' = partn eac_sm k le' in
  let lk' = to_vlog lek' in
  let lksr' = filter_refine is_state_op lk' in
  let lks' = to_state_op_vlog lk' in

  let ee = index le (n - 1) in
  let e = to_vlog_entry ee in
  if vlog_entry_ext_key ee <> k then (
    lemma_filter_extend1 (iskey vlog_entry_ext_key k) le;
    //assert(lek' = lek);
    ()
  )
  else (
    lemma_filter_extend2 (iskey vlog_entry_ext_key k) le;
    lemma_prefix1_append lek' ee;
    //assert(lek = append1 lek' ee);

    lemma_map_extend to_vlog_entry lek;
    lemma_prefix1_append lk' e;
    //assert(lk = append1 lk' e);

    lemma_filter_extend1 is_state_op lk;
    //assert(lksr = lksr');
    ()
  )

let lemma_state_partn_append (le:vlog_ext{length le > 0}) (k:data_key):
  Lemma (requires (is_state_op (to_vlog_entry (index le (length le - 1))) /\
                   iskey vlog_entry_ext_key k (index le (length le - 1))))
        (ensures (partn ssm k (to_state_op_vlog (to_vlog le)) =
                  append1 (partn ssm k (to_state_op_vlog (to_vlog (prefix le (length le - 1)))))
                          (to_state_op (to_vlog_entry (index le (length le - 1)))))) =
  let n = length le in
  let l = to_vlog le in
  let lsr = filter_refine is_state_op l in
  let ls = to_state_op_vlog l in
  let lsk = partn ssm k ls in
  let le' = prefix le (n - 1) in
  let l' = to_vlog le' in
  let ls' = to_state_op_vlog l' in
  let lsr' = filter_refine is_state_op l' in
  let lsk' = partn ssm k ls' in
  let ee = index le (n - 1) in
  let e = to_vlog_entry ee in
  let op = to_state_op e in
  //assert(is_state_op e);
  //assert(vlog_entry_ext_key ee = k);

  lemma_map_extend to_vlog_entry le;
  lemma_prefix1_append l' e;
  //assert(l = append1 l' e);

  lemma_filter_extend2 is_state_op l;
  assert(equal lsr (append1 lsr' e));
  lemma_prefix1_append lsr' e;

  lemma_map_extend to_state_op lsr;
  lemma_prefix1_append ls' op;
  //assert(ls = append1 ls' op);

  lemma_filter_extend2 (iskey S.key_of k) ls;
  //assert(lsk = append1 lsk' op);
  ()

let lemma_state_partn_same (le:vlog_ext{length le > 0}) (k:data_key):
  Lemma (requires (not (is_state_op (to_vlog_entry (index le (length le - 1)))) \/
                   not (iskey vlog_entry_ext_key k (index le (length le - 1)))))
        (ensures (partn ssm k (to_state_op_vlog (to_vlog le)) =
                  partn ssm k (to_state_op_vlog (to_vlog (prefix le (length le - 1)))))) =
  let n = length le in
  let l = to_vlog le in
  let lsr = filter_refine is_state_op l in
  let ls = to_state_op_vlog l in
  let lsk = partn ssm k ls in
  let le' = prefix le (n - 1) in
  let l' = to_vlog le' in
  let ls' = to_state_op_vlog l' in
  let lsr' = filter_refine is_state_op l' in
  let lsk' = partn ssm k ls' in
  let ee = index le (n - 1) in
  let e = to_vlog_entry ee in

  lemma_map_extend to_vlog_entry le;
  lemma_prefix1_append l' e;
  //assert(l = append1 l' e);

  if not (is_state_op e) then (
    lemma_filter_extend1 is_state_op l;
    //assert (lsr = lsr');
    ()
  )
  else (
    let op = to_state_op e in
    lemma_filter_extend2 is_state_op l;
    assert(equal lsr (append1 lsr' e));
    lemma_prefix1_append lsr' e;

    lemma_map_extend to_state_op lsr;
    lemma_prefix1_append ls' op;
    //assert(ls = append1 ls' op);

    lemma_filter_extend1 (iskey S.key_of k) ls;
    //assert(lsk = lsk');
    ()
  )


let rec lemma_comm (le:vlog_ext) (k:data_key):
  Lemma (requires True)
        (ensures (to_state_op_vlog (to_vlog (partn eac_sm k le)) =
                  partn ssm k (to_state_op_vlog (to_vlog le))))
        (decreases (length le)) =
  let n = length le in
  let lek = partn eac_sm k le in
  let lk = to_vlog lek in
  let lks = to_state_op_vlog lk in
  let l = to_vlog le in
  let ls = to_state_op_vlog l in
  let lsk = partn ssm k ls in
  if n = 0 then
    lemma_comm_empty le k
  else (
    let le' = prefix le (n - 1) in
    let lek' = partn eac_sm k le' in
    let lk' = to_vlog lek' in
    let lks' = to_state_op_vlog lk' in
    let l' = to_vlog le' in
    let ls' = to_state_op_vlog l' in
    let lsk' = partn ssm k ls' in

    lemma_comm le' k;
    //assert (lks' = lsk');

    let ee = index le (n - 1) in
    let e = to_vlog_entry ee in
    if is_state_op e && vlog_entry_ext_key ee = k then (
      let op = to_state_op e in
      lemma_partn_state_append le k;
      //assert(lks = append1 lks' op);

      lemma_state_partn_append le k;
      //assert(lsk = append1 lsk' op);
      ()
    )
    else (
      lemma_partn_state_same le k;
      //assert(lks = lks');

      lemma_state_partn_same le k;
      //assert(lsk = lsk');
      ()
    )
  )

let has_some_put (l:vlog) =
  exists_sat_elems Put? l

let last_put_idx (l:vlog{has_some_put l}) =
  last_index Put? l

let last_put_value_or_null (l:vlog) =
  if has_some_put l then Put?.v (index l (last_put_idx l))
  else Null

let eac_closure_pred1 (st: eac_state): bool =
  EACFail = st ||  is_eac_state_active st && DVal? (value_of st)

let eac_closure_pred2 (st: eac_state): bool =
  EACFail = st ||  is_eac_state_active st && MVal? (value_of st)

let lemma_eac_add_closure1 (e:vlog_entry_ext) (st: eac_state):
  Lemma (eac_closure_pred1 st ==> eac_closure_pred1 (eac_add e st)) = ()

let lemma_eac_add_closure2 (e:vlog_entry_ext) (st: eac_state):
  Lemma (eac_closure_pred2 st ==> eac_closure_pred2 (eac_add e st)) = ()

let eac_closure_pred3 (st: eac_state): bool =
  EACFail = st || EACRoot = st

let lemma_eac_add_closure3 (e: vlog_entry_ext) (st: eac_state):
  Lemma (eac_closure_pred3 st ==> eac_closure_pred3 (eac_add e st)) = ()

let lemma_value_type (le:vlog_ext {length le > 0}):
  Lemma (EACFail = seq_machine_run eac_smk le \/
         EACRoot = seq_machine_run eac_smk le \/
         is_eac_state_active (seq_machine_run eac_smk (prefix le 1)) /\
         is_eac_state_active (seq_machine_run eac_smk le) /\
         DVal? (value_of (seq_machine_run eac_smk le)) =
         DVal? (value_of (seq_machine_run eac_smk (prefix le 1)))) =

  let n = length le in
  let st = seq_machine_run eac_smk le in

  if EACFail = st then ()
  else if EACRoot = st then ()
  else (

    // st1 is valid (and not init)
    lemma_valid_prefix eac_smk le 1;
    lemma_notempty_implies_noninit eac_smk (prefix le 1);
    let st1 = seq_machine_run eac_smk (prefix le 1) in

    lemma_reduce_prefix EACInit eac_add le 1;
    //assert(st = reduce st1 eac_add (suffix le (n - 1)));

    let aux ():
      Lemma (st1 <> EACRoot) =
      if st1 = EACRoot then
        lemma_reduce_property_closure eac_closure_pred3 st1 eac_add (suffix le (n - 1))
      else ()
    in
    aux();

    //assert(is_eac_state_active st1);
    if DVal? (value_of st1) then
      lemma_reduce_property_closure eac_closure_pred1 st1 eac_add (suffix le (n - 1))
    else
      lemma_reduce_property_closure eac_closure_pred2 st1 eac_add (suffix le (n - 1))
  )

let lemma_first_entry_is_madd (le:vlog_ext):
  Lemma (requires (valid eac_smk le /\ length le > 0 /\ EACRoot <> seq_machine_run eac_smk le))
        (ensures (AddM? (to_vlog_entry (index le 0)))) =
  let n = length le in
  let le1 = prefix le 1 in
  let st1 = seq_machine_run eac_smk le1 in
  lemma_valid_prefix eac_smk le 1;
  lemma_reduce_singleton EACInit eac_add le1;
  assert(st1 = eac_add (index le 0) EACInit);

  if st1 = EACRoot then (
    lemma_reduce_prefix EACInit eac_add le 1;
    lemma_reduce_property_closure eac_closure_pred3 st1 eac_add (suffix le (n - 1));
    ()
  )
  else ()

let rec lemma_active_implies_prefix_active (le: vlog_ext) (i: nat{i <= length le /\ i > 0}):
  Lemma (requires (let st = seq_machine_run eac_smk le in
                   is_eac_state_active st))
        (ensures (let lei = prefix le i in
                  let sti = seq_machine_run eac_smk lei in
                  is_eac_state_active sti))
        (decreases (length le))
        [SMTPat (prefix le i)] =
  let n = length le in
  if i = n then ()
  else (
    let le' = prefix le (n - 1) in
    let st' = seq_machine_run eac_smk le' in
    lemma_valid_prefix eac_smk le (n - 1);
    // assert(st' <> EACFail);

    lemma_reduce_append2 EACInit eac_add le;
    // assert(st' <> EACRoot);
    lemma_notempty_implies_noninit eac_smk le';
    // assert(st' <> EACInit);
    lemma_active_implies_prefix_active le' i
  )

let rec lemma_eacroot_implies_prefix_eacroot (le: vlog_ext) (i: nat{i <= length le}):
  Lemma (requires (EACRoot = seq_machine_run eac_smk le))
        (ensures (let lei = prefix le i in
                  let sti = seq_machine_run eac_smk lei in
                  i = 0 /\ sti = EACInit \/
                  i > 0 /\ sti = EACRoot))
        (decreases (length le))
        [SMTPat (prefix le i)] =
  let n = length le in
  let st = seq_machine_run eac_smk le in
  let lei = prefix le i in
  let sti = seq_machine_run eac_smk lei in
  if n = 0 then (
    lemma_reduce_empty EACInit eac_add;
    lemma_empty le;
    ()
  )
  else if i = n then ()
  else if i = 0 then (
    lemma_reduce_empty EACInit eac_add;
    lemma_empty lei
  )
  else (

    let le' = prefix le (n - 1) in
    let st' = seq_machine_run eac_smk le' in
    lemma_reduce_append2 EACInit eac_add le;
    lemma_notempty_implies_noninit eac_smk le';
    lemma_eacroot_implies_prefix_eacroot le' i
  )

let rec lemma_data_val_state_implies_last_put (le:vlog_ext):
  Lemma (requires (is_eac_state_active (seq_machine_run eac_smk le) /\
                   DVal? (value_of (seq_machine_run eac_smk le))))
        (ensures (DVal?.v (value_of (seq_machine_run eac_smk le)) =
                  last_put_value_or_null (to_vlog le)))
        (decreases (length le)) =
  let l = to_vlog le in
  let n = length le in
  let st = seq_machine_run eac_smk le in

  if n = 0 then (
    lemma_reduce_empty EACInit eac_add;
    lemma_empty le;
    //assert (EACInit = seq_machine_run eac_smk le);
    ()
  )

  else if n = 1 then (
    assert(st <> EACRoot);
    lemma_first_entry_is_madd le;
    lemma_reduce_singleton EACInit eac_add le;

    if has_some_put l then (
      let i = last_put_idx l in
      ()
    )
    else match (index le 0) with
    | NEvict (AddM (k, v) _ ) ->
      //assert(value_of st = v);
      ()
  )

  else (

    let le' = prefix le (n - 1) in
    let l' = prefix l (n - 1) in
    lemma_map_prefix to_vlog_entry le (n - 1);
    lemma_valid_prefix eac_smk le (n - 1);

    // le and le' have the same value type
    lemma_value_type le;
    lemma_value_type le';
    //assert(DVal? (value_of (seq_machine_run eac_smk le')));

    // induction
    lemma_data_val_state_implies_last_put le';

    // IH
    let st' = seq_machine_run eac_smk le' in
    //assert(DVal?.v (value_of st') = last_put_value_or_null (to_vlog le'));

    lemma_reduce_append2 EACInit eac_add le;
    //assert(st = eac_add (index le (n - 1)) st');

    if Put? (to_vlog_entry (index le (n - 1))) then
      lemma_last_index_last_elem_sat Put? l

    else (
      //assert(value_of st' = value_of st);
      lemma_last_index_last_elem_nsat Put? l;

      if has_some_put l' then
        lemma_last_index_prefix Put? l (n - 1)
      else ()

    )
  )

let lemma_get_implies_data_val_state (le:vlog_ext) (i:seq_index le):
  Lemma (requires (valid eac_smk le /\ Get? (to_vlog_entry (index le i))))
        (ensures (valid eac_smk (prefix le i) /\
                  EACInStore? (seq_machine_run eac_smk (prefix le i)) /\
                  DVal? (value_of (seq_machine_run eac_smk (prefix le i))))) =
  let lei = prefix le i in
  let lei' = prefix le (i + 1) in

  lemma_valid_prefix eac_smk le i;
  lemma_valid_prefix eac_smk le (i + 1);
  lemma_reduce_append2 EACInit eac_add lei';
  ()

let lemma_keyedentry_implies_nonroot (le: vlog_ext) (i:seq_index le):
  Lemma (requires (valid eac_smk le /\ is_keyed_entry (to_vlog_entry (index le i))))
        (ensures (let st = seq_machine_run eac_smk le in
                  is_eac_state_active st))
        [SMTPat (index le i)]

                  =
  let st = seq_machine_run eac_smk le in
  lemma_notempty_implies_noninit eac_smk le;
  assert(st <> EACFail && st <> EACInit);
  if st = EACRoot then (
    let lei = prefix le i in
    let sti = seq_machine_run eac_smk lei in

    let lei' = prefix le (i + 1) in
    let sti' = seq_machine_run eac_smk lei' in
    lemma_valid_prefix eac_smk le (i + 1);
    lemma_reduce_append2 EACInit eac_add lei'
  )
  else ()

let lemma_eac_k_implies_valid_get (le:vlog_ext) (i:seq_index le):
  Lemma (requires (valid eac_smk le /\ Get? (to_vlog_entry (index le i))))
        (ensures (Get?.v (to_vlog_entry (index le i)) =
                  last_put_value_or_null (to_vlog (prefix le i)))) =
  let n = length le in
  let lei = prefix le i in

  lemma_first_entry_is_madd le;
  //assert(n > 1);

  lemma_get_implies_data_val_state le i;
  //assert(valid eac_smk lei);
  //assert(DVal? (value_of (seq_machine_run eac_smk lei)));

  lemma_data_val_state_implies_last_put lei;
  let sti = seq_machine_run eac_smk lei in
  //assert(DVal? (value_of sti));

  let lei' = prefix le (i + 1) in
  lemma_valid_prefix eac_smk le (i + 1);
  //assert(EACFail <> (seq_machine_run eac_smk lei'));

  lemma_reduce_append2 EACInit eac_add lei';
  //assert(seq_machine_run eac_smk lei' = eac_add (index le i) sti);
  ()

let state_op_map (l:vlog) (i:seq_index (to_state_op_vlog l)):
  Tot (j:(seq_index l){is_state_op (index l j) /\
                       to_state_op (index l j) =  index (to_state_op_vlog l) i /\
                       to_state_op_vlog (prefix l j) = prefix (to_state_op_vlog l) i}) =
  let ls = to_state_op_vlog l in
  let j = filter_index_map is_state_op l i in
  lemma_filter_prefix_comm is_state_op l j;
  lemma_map_prefix to_state_op (filter_refine is_state_op l) i;
  assert(equal (prefix (filter_refine is_state_op l) i) (filter_refine is_state_op (prefix l j)));
  j

let lemma_last_put_map (l:vlog):
  Lemma (last_put_value_or_null l =
         last_put_value_or_null_k (to_state_op_vlog l)) =
  let ls = to_state_op_vlog l in
  if has_some_put l then (
    let j = last_put_idx l in
    let i = filter_index_inv_map is_state_op l j in
    //assert(index ls i = to_state_op (index l j));
    lemma_last_index_correct2 Veritas.State.Put? ls i;
    let i' = last_put_idx_k ls in
    if i' = i then ()
    else (
      let j' = filter_index_map is_state_op l i' in
      lemma_filter_index_map_monotonic is_state_op l i i';
      lemma_filter_maps_correct is_state_op l j;
      lemma_last_index_correct2 Put? l j'
    )
  )
  else if has_some_put_k ls then
    let i = last_put_idx_k ls in
    let j = state_op_map l i in
    lemma_last_index_correct2 Put? l j
  else ()

let lemma_eac_k_implies_ssm_k_valid (le:eac_log) (k:data_key):
  Lemma (valid ssm_k (to_state_op_vlog (to_vlog (partn eac_sm k le)))) =
  let lek = partn eac_sm k le in
  let lk = to_vlog lek in
  let lks = to_state_op_vlog lk in
  if valid ssm_k lks then ()
  else (
    let i = max_valid_prefix ssm_k lks in
    let op = index lks i in

    lemma_first_invalid_implies_invalid_get (prefix lks (i + 1));
    //assert(Veritas.State.Get?.v op <> last_put_value_or_null_k (prefix lks i));

    // index of entry in lk/lek that corresponds to i
    let j = (state_op_map lk i) in
    //assert(to_state_op(index lk j) = op);
    lemma_eac_k_implies_valid_get lek j;
    lemma_map_prefix to_vlog_entry lek j;
    lemma_last_put_map (prefix lk j)
  )

(* evict add consistency implies rw-consistency *)
let lemma_eac_implies_rw_consistent (le:eac_log):
  Lemma (rw_consistent (to_state_op_vlog (to_vlog le))) =
  let l = to_vlog le in
  let s = to_state_op_vlog l in
  let rwc = valid_all_comp ssm s in
  lemma_state_sm_equiv_rw_consistent s;
  if rwc then () // nothing to prove if rw_consistent
  else (
    (* invalidating key *)
    let k = invalidating_key ssm s in
    lemma_eac_k_implies_ssm_k_valid le k;
    lemma_comm le k
  )

let is_eac (l:vlog_ext)
  : b:bool{b <==> eac l}
  = valid_all_comp eac_sm l
