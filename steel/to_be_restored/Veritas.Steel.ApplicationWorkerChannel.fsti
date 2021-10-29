module Veritas.Steel.ApplicationWorkerChannel

module G = FStar.Ghost

open Steel.Effect

module VTypes = Veritas.Formats.Types

val ch : Type0

val reader (c:ch) (n:nat) : vprop
val writer (c:ch) (n:nat) : vprop

val sent (c:ch) (e:VTypes.vlog_entry) (n:nat) : prop

unfold
let write_pure_post (c:ch) (e:VTypes.vlog_entry) (b:bool) (n m:nat) : prop =
  (b ==> (m == n+1 /\ sent c e n)) /\
  (~ b ==> m == n)

val write (#n:G.erased nat) (c:ch) (e:VTypes.vlog_entry)
  : SteelT (bool & G.erased nat)
      (writer c n)
      (fun (b, m) ->
       pure (write_pure_post c e b n m) `star`
       writer c m)

val read (#n:G.erased nat) (c:ch)
  : SteelT VTypes.vlog_entry
      (reader c n)
      (fun e -> pure (sent c e n) `star` reader c (n+1))

let sent_s (c:ch) (s:Seq.seq VTypes.vlog_entry) (n:nat) : prop =
  forall (i:nat{i < Seq.length s}). sent c (Seq.index s i) (n+i)

val trace_n_m (c:ch) (n:nat) (m:nat)
  : s:G.erased (Seq.lseq VTypes.vlog_entry m){sent_s c s n}
