module Zeta.Steel.LogRel

module GV = Zeta.GenericVerifier

let rec map_ghost (p:'a -> Type0) 
                  (s:Seq.seq 'a { forall (i:Zeta.SeqAux.seq_index s). p (Seq.index s i) })
                  (f: (x:'a { p x } -> GTot 'b))
  : GTot (s':Seq.seq 'b { Seq.length s == Seq.length s' /\
                         (forall (i:Zeta.SeqAux.seq_index s). Seq.index s' i == f (Seq.index s i)) })
         (decreases (Seq.length s))
  = if Seq.length s = 0 then Seq.empty
    else (
      let prefix, last = Seq.un_snoc s in
      Seq.snoc (map_ghost p prefix f) (f last)
    )
                           
let lift_slots (s:Seq.seq s_slot_id { forall (i:Zeta.SeqAux.seq_index s). valid_slot (Seq.index s i)  })
  : GTot (is:Seq.seq i_slot_id  { Seq.length s = Seq.length is /\
                                  (forall i. related_slot (Seq.index s i) (Seq.index is i)) })
         (decreases (Seq.length s))
  = map_ghost (fun x -> valid_slot x) s lift_slot
  
let lift_log_entry (se: s_log_entry {valid_log_entry se})
  : GTot (ie: i_log_entry { related_log_entry se ie })
  = let open Zeta.Steel.LogEntry.Types in
    let open Zeta.Steel.Rel in
    match se with
    | AddM s s' r ->
      let i_r = lift_record r in
      let i_s = lift_slot s in
      let i_s' = lift_slot s' in
      GV.AddM i_r i_s i_s'

    | AddB s t tid r ->
      let i_r = lift_record r in
      let i_s = lift_slot s in
      let i_t = lift_timestamp t in
      let i_tid = lift_tid tid in
      GV.AddB i_r i_s i_t i_tid

    | EvictM p ->
      GV.EvictM (lift_slot p.s) (lift_slot p.s_)

    
    | EvictB p ->
      GV.EvictB (lift_slot p.s) (lift_timestamp p.t)

    | EvictBM p ->
      GV.EvictBM (lift_slot p.s) (lift_slot p.s_) (lift_timestamp p.t)

    | NextEpoch ->
      GV.NextEpoch

    | VerifyEpoch ->
      GV.VerifyEpoch

    | RunApp p ->
      GV.RunApp p.fid (parse_arg p.fid p.rest) (lift_slots (parse_slots p.fid p.rest))

let lift_log (sl: s_log {valid_log sl})
  : GTot (il:i_log {related_log sl il})
  = map_ghost valid_log_entry sl lift_log_entry

let lift_log_snoc (sl: s_log {valid_log sl}) (se: s_log_entry {valid_log_entry se})
  : Lemma (requires (let sl_ = Seq.snoc sl se in
                     valid_log sl_))
          (ensures (let il = lift_log sl in
                    let ie = lift_log_entry se in
                    let sl_ = Seq.snoc sl se in
                    let il_ = lift_log sl_ in
                    let i = Seq.length sl in
                    il_ == Seq.snoc il ie /\
                    Seq.index il_ i = ie))
  = let sl_ = Seq.snoc sl se in
    let prefix, last = Seq.un_snoc sl_ in
    assert (prefix `Seq.equal` sl)

let prefix_of_valid_valid (l: s_log {valid_log l}) (i: nat{ i <= Seq.length l})
  : Lemma (ensures (let l' = SA.prefix l i in
                    valid_log l'))
  = ()

let lift_prefix_commute (l: s_log {valid_log l}) (i: nat{ i <= Seq.length l})
  : Lemma (ensures (lift_log (SA.prefix l i) == SA.prefix (lift_log l) i))
  = assert (lift_log (SA.prefix l i) `Seq.equal` SA.prefix (lift_log l) i)
