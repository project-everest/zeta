module Zeta.Steel.LogEntry.Spec
include Zeta.Steel.LogEntry.Types
open Zeta.Steel.Parser
module U32 = FStar.UInt32
val spec_parser_log_entry : spec_parser log_entry

let can_parse_log_entry (log_bytes:bytes)
                        (log_pos:U32.t)
  = U32.v log_pos <= Seq.length log_bytes &&
    Some? (spec_parser_log_entry (Zeta.Steel.Parser.bytes_from log_bytes log_pos))

let spec_parse_log_entry (log_bytes:bytes)
                         (log_pos:U32.t{
                            can_parse_log_entry log_bytes log_pos
                          })
  : GTot (log_entry & nat)
  = parse_result log_bytes log_pos spec_parser_log_entry

let maybe_parse_log_entry (log_bytes:bytes)
                          (log_pos:U32.t)
  : GTot (option (log_entry & nat))
  = if can_parse_log_entry log_bytes log_pos
    then Some (spec_parse_log_entry log_bytes log_pos)
    else None

val spec_parser_log_entry_consumes_at_least_one_byte
  (log_bytes: bytes)
: Lemma
  (requires (Some? (spec_parser_log_entry log_bytes)))
  (ensures (
    let Some (_, consumed) = spec_parser_log_entry log_bytes in
    consumed >= 1
  ))

val spec_parser_log_entry_strong_prefix (l:bytes)
  : Lemma
    (requires
       Some? (spec_parser_log_entry l))
    (ensures (
       let Some (le, pos) = spec_parser_log_entry l in
       (forall (l1:bytes).{:pattern spec_parser_log_entry l1}
         pos <= Seq.length l1 /\
         Seq.slice l 0 pos `Seq.equal` Seq.slice l1 0 pos ==>
         (match spec_parser_log_entry l1 with
          | None -> False
          | Some (le', pos') -> le' == le /\ eq2 #nat pos' pos /\ pos > 0))))

val runapp_payload_offset
  (e: log_entry)
  (b: Ghost.erased bytes)
: Pure U32.t
  (requires (
    RunApp? e /\
    begin match spec_parser_log_entry b with
    | Some (e', _) -> e' == e
    | _ -> False
    end
  ))
  (ensures (fun res ->
    let Some (_, len) = spec_parser_log_entry b in
    let off = U32.v res in
    let RunApp pl = e in
    off <= len /\
    Ghost.reveal pl.rest.ebytes == Seq.slice b off len
  ))


let rec parse_full_log (l:bytes)
  : GTot (option (Seq.seq log_entry))
         (decreases (Seq.length l))
  = if Seq.length l = 0 then Some Seq.empty
    else match spec_parser_log_entry l with
         | None -> None
         | Some (le, n) ->
           spec_parser_log_entry_consumes_at_least_one_byte l;
           match parse_full_log (Seq.slice l n (Seq.length l)) with
           | None -> None
           | Some out -> Some (Seq.cons le out)

let full_parse_log_entry (l:bytes) =
  match spec_parser_log_entry l with
  | None -> False
  | Some (le, n) -> n == Seq.length l

#push-options "--query_stats --fuel 2 --ifuel 1 --z3rlimit_factor 4 --using_facts_from '* -FStar.Seq.Properties.slice_slice'"
let rec parse_full_log_trans (l0 l1:bytes)
  : Lemma
    (requires
      Some? (parse_full_log l0) /\
      full_parse_log_entry l1)
    (ensures (
      let Some les = parse_full_log l0 in
      let Some (le, _) = spec_parser_log_entry l1 in
      match parse_full_log (l0 `Seq.append` l1) with
      | None -> False
      | Some s -> s `Seq.equal` Seq.snoc les le))
    (decreases (Seq.length l0))
  = let Some les = parse_full_log l0 in
    let Some (le, pos) = spec_parser_log_entry l1 in
    spec_parser_log_entry_strong_prefix l1;
    assert (pos > 0);
    assert (Seq.length l1 = pos);
    if Seq.length l0 = 0
    then (
      assert (Seq.append l0 l1 `Seq.equal` l1)
    )
    else (
      let Some (le, n) = spec_parser_log_entry l0 in
      spec_parser_log_entry_strong_prefix l0;
      parse_full_log_trans (Seq.slice l0 n (Seq.length l0)) l1;
      assert (l0 `Seq.append` l1 `Seq.equal`
              (Seq.slice l0 0 n `Seq.append` (Seq.slice l0 n (Seq.length l0) `Seq.append` l1)));
      assert (Seq.slice (l0 `Seq.append` l1) n (Seq.length (Seq.append l0 l1)) `Seq.equal`
             (Seq.slice l0 n (Seq.length l0) `Seq.append` l1))
    )

let parse_log_up_to (l:bytes) (pos:nat) =
  if pos > Seq.length l then None
  else parse_full_log (Seq.slice l 0 pos)

let parse_log_up_to_trans (l:bytes) (pos:nat) (les:Seq.seq log_entry)
  : Lemma
    (requires
      parse_log_up_to l pos == Some les /\
      Some? (spec_parser_log_entry (Seq.slice l pos (Seq.length l))))
    (ensures (
      let Some (le, pos') = spec_parser_log_entry (Seq.slice l pos (Seq.length l)) in
      match parse_log_up_to l (pos + pos') with
      | None -> False
      | Some les' -> les' `Seq.equal` Seq.snoc les le))
  = let Some (le, pos') = spec_parser_log_entry (Seq.slice l pos (Seq.length l)) in
    spec_parser_log_entry_strong_prefix (Seq.slice l pos (Seq.length l));
    parse_full_log_trans (Seq.slice l 0 pos) (Seq.slice l pos (pos + pos'));
    assert (Seq.slice l 0 (pos + pos') `Seq.equal`
            Seq.append (Seq.slice l 0 pos) (Seq.slice l pos (pos + pos')))
#pop-options

val spec_parser_stamped_record : spec_parser stamped_record
val spec_serializer_stamped_record : spec_serializer spec_parser_stamped_record

/// This is an ad hoc bound due to a bound on Blake hashable inputs
val serialized_stamped_record_length (s:stamped_record)
  : Lemma (Seq.length (spec_serializer_stamped_record s) <= 4096)
