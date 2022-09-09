module Zeta.SIdxFn

open FStar.Seq
open Zeta.SeqAux
open Zeta.SSeq
open Zeta.IdxFn

module S = FStar.Seq
module SA = Zeta.SeqAux
module SS = Zeta.SSeq

noeq
type gen_sseq_base = {

  (* outer sequence specification *)
  gso: gen_seq_spec;

  (* inner sequence specification *)
  gsi: gen_seq_spec;

  (* construct the inner sequence i *)
  index: s:seq_t gso -> i:nat{i < Seq.length s} -> seq_t gsi;
}

let index_prefix_prop (gs:gen_sseq_base)
  = forall (s:seq_t gs.gso) (j:nat{j <= Seq.length s}) (i: nat{i < j}).
    {:pattern gs.index (SA.prefix s j) i}
    (gs.gso.phi_commutes_with_prefix s j;
     gs.index (SA.prefix s j) i = gs.index s i)

let gen_sseq = gs: gen_sseq_base {index_prefix_prop gs}

let sseq_index (#gs:gen_sseq) (ss: seq_t gs.gso)
  = ij:(nat & nat) {let i,j = ij in i < Seq.length ss /\ j < Seq.length (gs.index ss i)}

let idxfn (#b:_) (gs:gen_sseq) (f: idxfn_t gs.gsi b) (ss: seq_t gs.gso) (ij: sseq_index ss)
  : b
  = let i,j = ij in
    let s = gs.index ss i in
    f s j

let cond_idxfn (#b:_) (#gs:gen_sseq) (#f: idxfn_t gs.gsi bool)
  (m: cond_idxfn_t b f) (ss: seq_t gs.gso) (ij: sseq_index ss{idxfn gs f ss ij})
  : b
  = let i,j = ij in
    let s = gs.index ss i in
    m s j

val filter_map (#b:_) (gs:gen_sseq)
  (fm: fm_t gs.gsi b)
  (s: seq_t gs.gso)
  : s':sseq b {S.length s' = Seq.length s}

(* map an index of the original sequence to the filter-mapped sequence *)
val filter_map_map (#b:_) (gs:gen_sseq)
  (fm: fm_t gs.gsi b)
  (ss: seq_t gs.gso)
  (ii: sseq_index ss {idxfn gs fm.f ss ii})
  : jj: (SS.sseq_index (filter_map gs fm ss))
    {indexss (filter_map gs fm ss) jj == cond_idxfn fm.m ss ii /\
     fst ii = fst jj}

(* map an index of the filter-map back to the original sequence *)
val filter_map_invmap (#b:_) (gs:gen_sseq)
  (fm: fm_t gs.gsi b)
  (ss: seq_t gs.gso)
  (jj: SS.sseq_index (filter_map gs fm ss))
  : ii:(sseq_index ss){idxfn gs fm.f ss ii /\ filter_map_map gs fm ss ii = jj }

val lemma_filter_map (#b:_) (gs:gen_sseq)
  (fm: fm_t gs.gsi b)
  (ss: seq_t gs.gso)
  (ii: sseq_index ss {idxfn gs fm.f ss ii})
  : Lemma (ensures (let jj = filter_map_map gs fm ss ii in
                    ii = filter_map_invmap gs fm ss jj))
          [SMTPat (filter_map_map gs fm ss ii)]

val lemma_filter_map_idx (#b:_) (gs:gen_sseq)
  (fm: fm_t gs.gsi b)
  (s: seq_t gs.gso)
  (i: nat{i < Seq.length s})
  : Lemma (ensures (S.index (filter_map gs fm s) i == Zeta.IdxFn.filter_map fm (gs.index s i)))
