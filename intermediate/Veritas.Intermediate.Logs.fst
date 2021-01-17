module Veritas.Intermediate.Logs



let to_logk (#vcfg:_) (tl:thread_id_logS vcfg{consistent_logS tl}): logK
 = admit()


(*
(* Reproducing definitions from Veritas.Verifier.Thread *)


let thread_id_of #vcfg (tl: thread_id_logS vcfg): nat = fst tl

let logS_of #vcfg (tl: thread_id_logS vcfg): logS _ = snd tl

let tl_length #vcfg (tl: thread_id_logS vcfg): nat =
  Seq.length (logS_of tl)

let tl_idx #vcfg (tl: thread_id_logS vcfg) = i:nat{i < tl_length tl}

let tl_index #vcfg (tl: thread_id_logS vcfg) (i:tl_idx tl): logS_entry _ =
  Seq.index (logS_of tl) i

let tl_prefix #vcfg (tl: thread_id_logS vcfg) (i:nat{i <= tl_length tl}): thread_id_logS _ =
  (thread_id_of tl), (prefix (logS_of tl) i)

(* Reproducing definitions from Veritas.Verifier.Global *)

let g_logS vcfg = Seq.seq (logS vcfg)

let thread_log #vcfg (gl:g_logS vcfg) (tid:seq_index gl): thread_id_logS _ = 
   (tid, Seq.index gl tid)

let to_state_op_glogS #vcfg (gl:g_logS vcfg) =
  map to_state_op_logS gl

(* Reproducing definitions from Veritas.Verifier.TSLog *)

let il_logS vcfg = interleaving (logS_entry vcfg)

let thread_count #vcfg (il:il_logS vcfg) = Seq.length (s_seq il)

let valid_tid #vcfg (il:il_logS vcfg) = tid:nat{tid < thread_count il}

let g_logS_of #vcfg (il:il_logS vcfg): g_logS _ = s_seq il

let state_ops #vcfg (itsl:il_logS vcfg): Seq.seq (state_op) =
  to_state_op_logS (i_seq itsl)

let lemma_logS_interleave_implies_state_ops_interleave #vcfg (l: logS vcfg) (gl: g_logS vcfg{interleave #(logS_entry vcfg) l gl})
  : Lemma (interleave #state_op (to_state_op_logS l) (to_state_op_glogS gl)) 
  = FStar.Squash.bind_squash
      #(interleave l gl)
      #(interleave (to_state_op_logS l) (to_state_op_glogS gl))
      ()
      (fun i -> 
        let i' = filter_map_interleaving is_state_op to_state_op i in
        FStar.Squash.return_squash i')
*)
