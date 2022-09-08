module Zeta.Steel.ApplicationResult

module LP = LowParse.Spec
module LIB = Zeta.Formats.Lib

(* A generic parser from type codes *)

let rec generic_parse_from_code
  (adm: A.app_data_model)
  (adm_parse_key: LP.parser LIB.default_strong_parser_kind adm.key)
  (adm_parse_value: LP.parser LIB.default_strong_parser_kind adm.value)
  (c: A.code)
: Tot (LP.parser LIB.default_strong_parser_kind (A.interp_code adm c))
  (decreases c)
= match c with
  | A.TUnit -> LP.weaken _ LP.parse_empty
  | A.TUInt8 -> LP.weaken _ LP.parse_u8
  | A.TUInt16 -> LP.weaken _ LP.parse_u16
  | A.TUInt32 -> LP.weaken _ LP.parse_u32
  | A.TUInt64 -> LP.weaken _ LP.parse_u64
  | A.TKey -> LP.weaken _ adm_parse_key
  | A.TValue -> LP.weaken _ adm_parse_value
  | A.TPair c1 c2 ->
    LP.weaken _ 
      (LP.nondep_then
        (generic_parse_from_code adm adm_parse_key adm_parse_value c1)
        (generic_parse_from_code adm adm_parse_key adm_parse_value c2)
      )

let rec generic_serialize_from_code
  (adm: A.app_data_model)
  (#adm_parse_key: LP.parser LIB.default_strong_parser_kind adm.key)
  (adm_serialize_key: LP.serializer adm_parse_key)
  (#adm_parse_value: LP.parser LIB.default_strong_parser_kind adm.value)
  (adm_serialize_value: LP.serializer adm_parse_value)
  (c: A.code)
: Tot (LP.serializer (generic_parse_from_code adm adm_parse_key adm_parse_value c))
  (decreases c)
= match c with
  | A.TUnit -> LP.serialize_weaken _ LP.serialize_empty
  | A.TUInt8 -> LP.serialize_weaken _ LP.serialize_u8
  | A.TUInt16 -> LP.serialize_weaken _ LP.serialize_u16
  | A.TUInt32 -> LP.serialize_weaken _ LP.serialize_u32
  | A.TUInt64 -> LP.serialize_weaken _ LP.serialize_u64
  | A.TKey -> adm_serialize_key
  | A.TValue -> adm_serialize_value
  | A.TPair c1 c2 ->
    LP.serialize_weaken _ 
      (LP.serialize_nondep_then
        (generic_serialize_from_code adm adm_serialize_key adm_serialize_value c1)
        (generic_serialize_from_code adm adm_serialize_key adm_serialize_value c2)
      )

let adm_parse_key : LP.parser LIB.default_strong_parser_kind aprm.adm.key =
  LIB.parser_intro_default _ spec_parser_key spec_parser_key_injective spec_parser_key_strong_prefix;
  LIB.bare_parser_of_spec_parser spec_parser_key

let adm_serialize_key : LP.serializer adm_parse_key =
  (fun x -> spec_serializer_key x)

let adm_parse_value : LP.parser LIB.default_strong_parser_kind aprm.adm.value =
  LIB.parser_intro_default _ spec_parser_value spec_parser_value_injective spec_parser_value_strong_prefix;
  LIB.bare_parser_of_spec_parser spec_parser_value

let adm_serialize_value : LP.serializer adm_parse_value =
  (fun x -> spec_serializer_value x)

let parse_from_code
: (c: A.code) ->
  Tot (LP.parser LIB.default_strong_parser_kind (A.interp_code aprm.adm c))
= generic_parse_from_code aprm.adm adm_parse_key adm_parse_value

let serialize_from_code
: (c: A.code) ->
  Tot (LP.serializer (parse_from_code c))
= generic_serialize_from_code aprm.adm adm_serialize_key adm_serialize_value

let parse_app_args
  (fid: A.appfn_id aprm)
: Tot (LP.parser LIB.default_strong_parser_kind (app_args fid))
= let fsig = Map.sel aprm.A.tbl fid in
  parse_from_code fsig.farg_t

let serialize_app_args
  (fid: A.appfn_id aprm)
: Tot (LP.serializer (parse_app_args fid))
= let fsig = Map.sel aprm.A.tbl fid in
  serialize_from_code fsig.farg_t

let bool_enum : LP.enum bool FStar.UInt8.t = [
  false, 0uy;
  true,  1uy;
]

let app_value_nullable_sum = LP.Sum
  _ _ bool_enum
  (A.app_value_nullable aprm.adm)
  (A.DValue?)
  (fun x -> if x then value_type else unit)
  (function
    | true -> (fun x -> A.DValue x)
    | false -> (fun _ -> A.Null)
  )
  (function
    | true -> A.DValue?.v
    | _ -> (fun _ -> ())
  )
  (fun _ _ -> ())
  (fun _ -> ())

let adm_parse_value_nullable : LP.parser LIB.default_strong_parser_kind (A.app_value_nullable aprm.adm) =
  LP.weaken _ (LP.parse_sum app_value_nullable_sum LP.parse_u8 (fun x -> if x then (| _, adm_parse_value |) else (| _, LP.parse_empty |)))

let adm_serialize_value_nullable : LP.serializer adm_parse_value_nullable =
  LP.serialize_weaken
    _
    (LP.serialize_sum
      app_value_nullable_sum
      LP.serialize_u8
      (fun c -> if c then adm_serialize_value else LP.serialize_empty)
    )

let parse_app_record : LP.parser LIB.default_strong_parser_kind (A.app_record aprm.adm) =
  LP.nondep_then
    adm_parse_key
    adm_parse_value_nullable

let serialize_app_record : LP.serializer parse_app_record =
  LP.serialize_nondep_then
    adm_serialize_key
    adm_serialize_value_nullable

#push-options "--z3rlimit 32"
#restart-solver

let rec filter_app_records_correct_aux_lt
  (x: list (A.app_record aprm.adm))
  (i1: Zeta.SeqAux.seq_index (Seq.seq_of_list x))
  (i2: Zeta.SeqAux.seq_index (Seq.seq_of_list x))
: Lemma
  (ensures (
    (List.Tot.noRepeats (List.Tot.map fst x) /\
    i1 < i2) ==> (
    let k1, _ = Seq.index (Seq.seq_of_list x) i1 in
    let k2, _ = Seq.index (Seq.seq_of_list x) i2 in
    k1 <> k2
  )))
  (decreases x)
= Seq.lemma_seq_of_list_induction x;
  match x with
  | [] -> ()
  | a :: q ->
    if i1 >= i2
    then ()
    else begin
      assert (Seq.index (Seq.seq_of_list q) (i2 - 1) == Seq.index (Seq.seq_of_list x) i2);
      if i1 = 0
      then begin
        List.Tot.memP_map_intro fst (Seq.index (Seq.seq_of_list q) (i2 - 1)) q
      end else begin
        assert (Seq.index (Seq.seq_of_list q) (i1 - 1) == Seq.index (Seq.seq_of_list x) i1);
        filter_app_records_correct_aux_lt q (i1 - 1) (i2 - 1)
      end
    end

#pop-options

let filter_app_records_correct_aux
  (x: list (A.app_record aprm.adm))
  (i1: Zeta.SeqAux.seq_index (Seq.seq_of_list x))
  (i2: Zeta.SeqAux.seq_index (Seq.seq_of_list x))
: Lemma
  (ensures (
    (List.Tot.noRepeats (List.Tot.map fst x) /\
    i1 <> i2) ==> (
    let k1, _ = Seq.index (Seq.seq_of_list x) i1 in
    let k2, _ = Seq.index (Seq.seq_of_list x) i2 in
    k1 <> k2
  )))
= filter_app_records_correct_aux_lt x i1 i2;
  filter_app_records_correct_aux_lt x i2 i1

let filter_app_records
  (fid: A.appfn_id aprm)
  (x: LP.nlist (Map.sel aprm.tbl fid).arity (A.app_record aprm.adm))
: Tot bool
= List.Tot.noRepeats (List.Tot.map fst x)

let filter_app_records_correct
  (fid: A.appfn_id aprm)
  (x: LP.parse_filter_refine (filter_app_records fid))
: Lemma
  (ensures (A.distinct_keys (Seq.seq_of_list x)))
= Classical.forall_intro_2 (filter_app_records_correct_aux x)

let synth_app_records
  (fid: A.appfn_id aprm)
  (x: LP.parse_filter_refine (filter_app_records fid))
: Tot (app_records fid)
= filter_app_records_correct fid x;
  Seq.seq_of_list x

let synth_app_records_injective
  (fid: A.appfn_id aprm)
: Lemma
  (LP.synth_injective (synth_app_records fid))
  [SMTPat (LP.synth_injective (synth_app_records fid))]
= Classical.forall_intro (Seq.lemma_list_seq_bij #(A.app_record aprm.adm));
  LP.synth_injective_intro (synth_app_records fid)

let parse_app_records
  (fid: A.appfn_id aprm)
: Tot (LP.parser LIB.default_strong_parser_kind (app_records fid))
= LP.weaken _
    (LP.parse_synth
      (LP.parse_filter
        (LP.parse_nlist (Map.sel aprm.tbl fid).arity parse_app_record)
        (filter_app_records fid)
      )
      (synth_app_records fid)
    )

let rec lemma_index_memP_recip (#t:Type) (l:list t) (x: t) :
  Ghost nat
    (requires (x `List.Tot.memP` l))
    (ensures (fun i -> i < List.Tot.length l /\ x == List.Tot.index l i))
= match l with
  | [] -> 0
  | a :: q ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (x == a)
    then 0
    else 1 + lemma_index_memP_recip q x

let rec filter_app_records_correct_recip_aux
  (x: list (A.app_record aprm.adm))
: Lemma
  (requires (
    forall
      (i1: Zeta.SeqAux.seq_index (Seq.seq_of_list x))
      (i2: Zeta.SeqAux.seq_index (Seq.seq_of_list x)) .
    i1 <> i2 ==> (
    let k1, _ = Seq.index (Seq.seq_of_list x) i1 in
    let k2, _ = Seq.index (Seq.seq_of_list x) i2 in
    k1 <> k2
  )))
  (ensures (List.Tot.noRepeats (List.Tot.map fst x)
  ))
= 
  Seq.lemma_seq_of_list_induction x;
  match x with
  | [] -> ()
  | a :: q ->
    filter_app_records_correct_recip_aux q;
    assert (a == Seq.index (Seq.seq_of_list x) 0);
    if List.Tot.mem (fst a) (List.Tot.map fst q)
    then begin
      FStar.List.Tot.memP_map_elim fst (fst a) q;
      let a' = FStar.IndefiniteDescription.indefinite_description_ghost (A.app_record aprm.adm) (fun a' -> List.Tot.memP a' q /\ fst a' == fst a) in
      let i' = lemma_index_memP_recip q a' in
      assert (a' == Seq.index (Seq.seq_of_list x) (i' + 1))
    end else ()

let filter_app_records_correct_recip
  (fid: A.appfn_id aprm)
  (x: app_records fid)
: Lemma
  (filter_app_records fid (Seq.seq_to_list x))
= Seq.lemma_seq_list_bij x;
  filter_app_records_correct_recip_aux (Seq.seq_to_list x)

let synth_app_records_recip
  (fid: A.appfn_id aprm)
  (x: app_records fid)
: Tot (LP.parse_filter_refine (filter_app_records fid))
= filter_app_records_correct_recip fid x;
  Seq.seq_to_list x

let synth_app_records_recip_inverse
  (fid: A.appfn_id aprm)
: Lemma
  (LP.synth_inverse (synth_app_records fid) (synth_app_records_recip fid))
  [SMTPat (LP.synth_inverse (synth_app_records fid) (synth_app_records_recip fid))]
= Classical.forall_intro (Seq.lemma_seq_list_bij #(A.app_record aprm.adm))

let serialize_app_records
  (fid: A.appfn_id aprm)
: Tot (LP.serializer (parse_app_records fid))
= LP.serialize_weaken _
    (LP.serialize_synth
      _
      _
      (LP.serialize_filter
        (LP.serialize_nlist (Map.sel aprm.tbl fid).arity serialize_app_record)
        (filter_app_records fid)
      )
      (synth_app_records_recip fid)
      ()
    )

let parse_app_result
  (fid: A.appfn_id aprm)
: Tot (LP.parser LIB.default_strong_parser_kind (app_result fid))
= let fsig = Map.sel aprm.A.tbl fid in
  parse_from_code fsig.fres_t

let serialize_app_result
  (fid: A.appfn_id aprm)
: Tot (LP.serializer (parse_app_result fid))
= let fsig = Map.sel aprm.A.tbl fid in
  serialize_from_code fsig.fres_t

let parse_fn_id : LP.parser LIB.default_strong_parser_kind (A.appfn_id aprm) =
  LP.weaken _ (LP.parse_filter LP.parse_u8 (Map.contains aprm.tbl))

let serialize_fn_id : LP.serializer parse_fn_id =
  LP.serialize_weaken _ (LP.serialize_filter LP.serialize_u8 (Map.contains aprm.tbl))

let parse_app_result_entry : LP.parser LIB.default_strong_parser_kind app_result_entry =
  LP.weaken _
    (LP.parse_synth
      (LP.parse_dtuple2
        parse_fn_id
        (fun fid ->
          LP.nondep_then
            (parse_app_args fid)
            (LP.nondep_then
              (parse_app_records fid)
              (parse_app_result fid)
            )
        )
      )
      (fun (| fid, (args, (record, result)) |) ->
        (| fid, args, record, result |)
      )
    )

let serialize_app_result_entry : LP.serializer parse_app_result_entry =
  LP.serialize_weaken _
    (LP.serialize_synth
      _
      _
      (LP.serialize_dtuple2
        serialize_fn_id
        (fun fid ->
          LP.serialize_nondep_then
            (serialize_app_args fid)
            (LP.serialize_nondep_then
              (serialize_app_records fid)
              (serialize_app_result fid)
            )
        )
      )
      (fun (| fid, args, record, result |) ->
        (| fid, (args, (record, result)) |)
      )
      ()
    )

let spec_result_parser fid =
  fun b -> match LP.parse (parse_app_result fid) b with
  | None -> None
  | Some (x, len) -> Some (x, len)

let spec_result_serializer fid =
  fun x -> serialize_app_result fid x

let spec_app_result_entry_parser =
  fun b -> match LP.parse (parse_app_result_entry) b with
  | None -> None
  | Some (x, len) -> Some (x, len)

let spec_app_result_entry_serializer =
  fun x -> serialize_app_result_entry x
