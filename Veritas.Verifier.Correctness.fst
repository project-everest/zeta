module Veritas.Verifier.Correctness

open FStar.Seq
open Veritas.Hash
open Veritas.Key
open Veritas.MultiSetHash
open Veritas.Record
open Veritas.SeqAux
open Veritas.State
open Veritas.Verifier

//Allow the solver to unroll recursive functions at most once (fuel)
//Allow the solver to invert inductive definitions at most once (ifuel)
#push-options "--max_fuel 1 --max_ifuel 1 --initial_fuel 1 --initial_ifuel 1"

(* type of thread ids *)
type tid (p:pos) = id:nat{id < p}

(* does the log leave the verifier thread in a valid state *)
let t_verifiable (#p:pos) (id: tid p)  (l: vlog #p) = Valid? (t_verify id l)

(* refinement types of valid thread-level logs *)
type t_verifiable_log (#p:pos) (id: tid p) = l:(vlog #p){t_verifiable id l}

(* Full collection of verifier logs one per thread *)
type g_vlog (#p:pos) = ss:seq (vlog #p){length ss <= p}

(* globally verifiable logs *)
type g_verifiable (#p:pos) (lg:g_vlog #p) = 
  forall (i:nat{i < length lg}). {:pattern t_verifiable #p i (index lg i)} 
  t_verifiable i (index lg i)

(* Refinement type of logs that are verifiable *)
type g_verifiable_log (#p:pos) = l:g_vlog{g_verifiable #p l}

(* aggregate hadd over all verifier threads *)
let rec g_hadd (#p:pos) (lg:g_verifiable_log #p) (e:nat)
  : Tot ms_hash_value (decreases (length lg)) = 
  let n = length lg in
  if n = 0 then empty_hash_value
  else 
    let lg' = prefix lg (n - 1) in
    let hv' = g_hadd lg' e in
    let l = index lg (n - 1) in
    // TODO: how to remove this side-effect assert?
    assert(t_verifiable (n - 1) l);
    let h = thread_hadd (t_verify (n-1) l) e in
    ms_hashfn_agg hv' h  

(* aggregate hadd over all verifier threads *)
let rec g_hevict (#p:pos) (lg:g_verifiable_log #p) (e:nat)
  : Tot ms_hash_value (decreases (length lg)) = 
  let n = length lg in
  if n = 0 then empty_hash_value
  else 
    let lg' = prefix lg (n - 1) in
    let hv' = g_hevict lg' e in
    let l = index lg (n - 1) in
    // TODO: how to remove this side-effect assert?
    assert(t_verifiable  (n - 1) l);
    let h = thread_hevict (t_verify (n- 1) l) e in
    ms_hashfn_agg hv' h  

(* verifiable logs where the first e epochs have identical hadd and hevict *)
let ep_verifieable_log (#p:pos) (ep:pos) = 
  l:(g_verifiable_log #p){forall (e:nat{e < ep}). g_hadd l e = g_hevict l e}

(* the clock of a verifier thread after processing a verfiable log *)
let clock_after (#p:pos) (#id:tid p) (l:t_verifiable_log id) = 
  let vs = t_verify id l in
  Valid?.clk vs

let rec lemma_verifiable_implies_prefix_verifiable
  (#p:pos) (id:tid p) (l:t_verifiable_log id) (i:nat{i <= length l}):
  Lemma (requires (True))
        (ensures (t_verifiable id (prefix l i)))
        (decreases (length l)) 
        =
  let n = length l in
  if n = 0 then ()
  else if i = n then ()
  else
    lemma_verifiable_implies_prefix_verifiable id (prefix l (n - 1)) i

(* TODO: Adding SMTPat (prefix l i) does not work in the lemma_above *)
let t_vprefix (#p:pos) (#id:tid p) (l:t_verifiable_log id) (i:nat{i <= length l}): 
  l':(t_verifiable_log id){l' = prefix l i} = 
  let l' = prefix l i in
  lemma_verifiable_implies_prefix_verifiable id l i;
  l'

(* the clock of a verifier is monotonic *)
let rec lemma_clock_monotonic (#p:pos) (#id:tid p) (l:t_verifiable_log id)
                          (i:nat{i <= length l}):
  Lemma (requires(True))
        (ensures (clock_after (t_vprefix l i) `ts_leq` clock_after l)) 
  (decreases (length l))        
        = 
  let n = length l in
  if n = 0 then ()
  else if i = n then ()
  else
    let l' = t_vprefix l (n - 1) in
    lemma_clock_monotonic l' i

type clocked_vlog_entry (#p:nat) = vlog_entry #p * timestamp

type clocked_vlog (#p:nat) = seq (clocked_vlog_entry #p)

let rec attach_clock (#p:pos) (id:tid p) (l:t_verifiable_log id): 
  Tot (clocked_vlog #p) 
  (decreases (length l)) = 
  let n = length l in
  if n = 0 then empty 
  else 
    let l' = t_vprefix l (n - 1) in
    let cl' = attach_clock id l' in
    let t = clock_after l in
    let e = index l (n - 1) in
    append cl' (create 1 (e, t))

(* is s' a prefix of s *)
let is_prefix (#a:eqtype) (s':seq a) (s:seq a) = 
  length s' <= length s && prefix s (length s') = s'

