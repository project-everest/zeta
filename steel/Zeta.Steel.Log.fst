module Zeta.Steel.Log
include Zeta.Steel.LogEntry.Spec
open Zeta.Steel.Parser
module U32 = FStar.UInt32

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
