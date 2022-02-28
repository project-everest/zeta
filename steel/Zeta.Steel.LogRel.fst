module Zeta.Steel.LogRel

let lift_log_entry (se: s_log_entry {valid_log_entry se})
  : ie: i_log_entry { related_log_entry se ie }
  = admit()

let lift_log (sl: s_log {valid_log sl})
  : il:i_log {related_log sl il}
  = admit()

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
  = admit()

let prefix_of_valid_valid (l: s_log {valid_log l}) (i: nat{ i <= Seq.length l})
  : Lemma (ensures (let l' = SA.prefix l i in
                    valid_log l'))
  = admit()

let lift_prefix_commute (l: s_log {valid_log l}) (i: nat{ i <= Seq.length l})
  : Lemma (ensures (lift_log (SA.prefix l i) == SA.prefix (lift_log l) i))
  = admit()
