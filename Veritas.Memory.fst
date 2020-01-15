module Veritas.Memory

open FStar.BitVector
open FStar.Classical
open FStar.Seq
open Veritas.SubSeq

(* address is a 256 bit value *)
let addr_size = 256
type addr = bv_t addr_size

(*
 * Payload of an address is either Null, a special initial value,
 * or an integer (TODO: replace integer with something more general)
 *)
type payload =
  | Null: payload
  | Value: v:int -> payload

(* Memory operation is either a read or a write *)
type memory_op =
  (* Read operation reading a value v at address a *)
  | Read: a:addr -> v:payload -> memory_op
  (* Write operation writing a value v at address a *)
  | Write: a:addr -> v:payload -> memory_op

(* Return address of a memory operator *)
let address_of (o: memory_op): Tot addr =
  match o with
  | Read a _ -> a
  | Write a _ -> a

(* Log is a sequence of memory operations *)
type memory_op_log = seq memory_op

(* type of an index into a log *)
type log_index (l:memory_op_log) = seq_index l

(* Address of log entry at position i *)
let address_at_idx (l:memory_op_log) (i:log_index l): Tot addr =
  address_of (index l i)

(* Is an operation at index i a read op *)
let is_read_op (l:memory_op_log) (i:log_index l): Tot bool =
  Read? (index l i)

(* For a read operation, return the read value *)
let read_value (l:memory_op_log) (i:log_index l{is_read_op l i}): Tot payload =
  Read?.v (index l i)

(* Is an operation at index i a write op *)
let is_write_op (l:memory_op_log) (i:log_index l): Tot bool =
  Write? (index l i)

(* For a write operation, return the written value *)
let written_value (l:memory_op_log) (i:log_index l{is_write_op l i}): Tot payload =
  Write?.v (index l i)

(*
 * Our goal is to define a notion of read-write consistency
 * for a memory_op_log. We do so using a naive verifier
 * that materializes the entire memory and checks if every
 * read operation reads the current value of that address
 *)

(* Memory: mapping from address to payload *)
type memory = addr -> payload

(* The state of the naive verifier as it processes the log *)
(* TODO: Learn about noeq - this does not seem to compile without it *)
noeq type naive_verifier_state =
  | NFailed: naive_verifier_state
  | NValid: m:memory -> naive_verifier_state

(* apply function for memory *)
let apply (m:memory) (o:memory_op{Write? o}): Tot memory =
  let a = Write?.a o in
  let v = Write?.v o in
  fun a' -> if a' = a then v else m a'

(* Naive verifier that verifies read-write consistency of a log given an initial memory *)
let rec naive_verifier (m:memory) (l:memory_op_log): Tot naive_verifier_state
  (decreases (length l)) =
  let n = length l in
  if n = 0 then NValid m
  else
    let l' = slice l 0 (n - 1) in
    // Recursively verify prefix
    let vs = naive_verifier m l' in
    // Propagate prefix failures
    if NFailed? vs then NFailed
    else
      let o = index l (n - 1) in
      let m' = NValid?.m vs in
      if Read? o then
        // Check value read is value in memory 
        if Read?.v o = m' (Read?.a o) then vs else NFailed
      else
        // Apply write changes
        NValid (apply m' o)

(* Initial state of memory - all addresses have Null *)
let init_memory:memory = fun _ -> Null

(*
 * read-write consistency starting from the initial state where all
 * addresses are initialized to Null
 *)
let rw_consistent (l:memory_op_log): Tot bool = NValid? (naive_verifier init_memory l)

(*
 * We next prove that a particular property of the log - every read 
 * corresponds to the most recent write - implies read write 
 * consistency as defined above
 *)

(* is this a write to address a *)
let is_write_to_addr (a:addr) (o:memory_op) = 
  Write? o && Write?.a o = a

(* 
 * last_write to an address a if it exists
 *)
let last_write (l:memory_op_log) (a:addr):
  Tot (option (i:(log_index l){is_write_to_addr a (index l i)})) =
  let f = is_write_to_addr a in
  let optwi = last_index l f in
  if None? optwi then None
  else
    let wi = Some?.v optwi in
    (last_index_correct1 l f; Some wi)

(*
 * Given an index of the log, return the most recent previous write
 * to the address in the index if it exists
 *)
let prev_write_of_idx (l:memory_op_log) (i:log_index l):
  Tot (option (j:log_index l{j < i && address_at_idx l j = address_at_idx l i && is_write_op l j})) =
  let l' = slice l 0 i in
  let a = address_at_idx l i in
  let optj = last_write l' a in
  if None? optj then None
  else
    let j = Some?.v optj in
    (
      lemma_len_slice l 0 i;
      lemma_index_slice l 0 i j;
      Some j
    )

(*
 * Does an address have a write in a log?
 *)
let has_some_write (l:memory_op_log) (a:addr): Tot bool =
  Some? (last_write l a)

(* Given an address with some write, return the value of the last write *)
let last_write_value (l:memory_op_log) (a:addr{has_some_write l a}): Tot payload =
  let i = Some?.v (last_write l a) in
  written_value l i

(* 
 * If an address has a write, then the memory of the naive verifier 
 * stores (and returns) the last write value for this address
 *)
let rec memory_is_last_write (l:memory_op_log) (m:memory) (a:addr):
  Lemma (requires (has_some_write l a && NValid? (naive_verifier m l)))
        (ensures (NValid?.m (naive_verifier m l) a = last_write_value l a))
        (decreases (length l)) =
  let n = length l in
  let f = is_write_to_addr a in
  if n = 0 then ()
  else 
    let l' = prefix l (n - 1) in
    if f (index l (n - 1)) then ()      
    else (
        memory_is_last_write l' m a;
        last_index_prefix l f
    )

(*
 * If we start with initial memory (all addresses null), then the 
 * memory of the naive verifier stores and returns Null for an address
 * that has no writes in the log 
 *)
let rec memory_is_null_without_write (l:memory_op_log) (a:addr):
  Lemma (requires (has_some_write l a = false /\ NValid? (naive_verifier init_memory l)))
        (ensures (NValid?.m (naive_verifier init_memory l) a = Null))
        (decreases (length l)) =
  let n = length l in
  let f = is_write_to_addr a in
  if n = 0 then ()
  else
    let l' = slice l 0 (n - 1) in
    if is_write_op l (n - 1) then
      if address_at_idx l (n - 1) = a then
        exists_implies_last_index l f (n - 1)
      else
        memory_is_null_without_write l' a
    else
      memory_is_null_without_write l' a

(* Has there been a previous write to address at index i *)
let has_prev_write (l:memory_op_log) (i:log_index l): Tot bool =
  Some? (prev_write_of_idx l i)

(* not (has_prev_write) *)
let has_no_prev_write (l:memory_op_log) (i:log_index l): Tot bool =
  None? (prev_write_of_idx l i)

(* 
 * If every read, reads the previous write, then we have read-write
 * consistency as defined by the naive verifier
 *)
let rec read_last_write_implies_rwconsistent (l:memory_op_log):
  Lemma (requires (forall (i:log_index l).
                        is_read_op l i ==>
                          has_no_prev_write l i && read_value l i = Null ||
                          has_prev_write l i && read_value l i = written_value l (Some?.v (prev_write_of_idx l i))))
       (ensures (rw_consistent l))
       (decreases (length l))
       =
  let n = length l in
  if n = 0 then ()
  else
    let l' = slice l 0 (n - 1) in
    let o = index l (n - 1) in
    let vs' = naive_verifier init_memory l' in
    let aux (i:log_index l'):
      Lemma(is_read_op l' i ==>
                       has_no_prev_write l' i && read_value l' i = Null ||
                       has_prev_write l' i && read_value l' i = written_value l' (Some?.v (prev_write_of_idx l' i))) =
      lemma_index_slice l 0 (n - 1) i;
      if is_read_op l' i then
        if has_no_prev_write l' i then
          // TODO: Do asserts have side-effects? The proof
          // goes through with the assert, but fails when the assert
          // is commented out; some kind of forall_intro better here?
          assert (has_no_prev_write l i)
        else
          assert (has_prev_write l i)        
      else ()
      in
    forall_intro aux; read_last_write_implies_rwconsistent l';
    assert (NValid? vs');
    let m' = (NValid?.m vs') in
    if Write? o then ()
    else
      let a = address_of o in
      if has_some_write l' a then (
        memory_is_last_write l' init_memory a;
        assert (is_read_op l (n - 1))
      )
      else (
        memory_is_null_without_write l' a;
        assert (is_read_op l (n - 1))
      )

