module Veritas.Memory

open FStar.BitVector
open FStar.Seq
open Veritas.SeqAux

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
    let l' = prefix l (n - 1) in
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

(* last write to address a in log if it exists *)
let last_write_idxopt (l:memory_op_log) (a:addr) = last_index_opt (is_write_to_addr a) l

(* does there exist some write to address a in log *)
let has_some_write (l:memory_op_log) (a:addr) = exists_sat_elems (is_write_to_addr a) l

(* index of last write to a if we know it exists *)
let last_write_idx (l:memory_op_log) (a:addr{has_some_write l a}) = last_index (is_write_to_addr a) l

(* last written value if exists or null *)
let last_write_value_or_null (l:memory_op_log) (a:addr): Tot payload = 
  if has_some_write l a then
    written_value l (last_write_idx l a)
  else
    Null

(* operational definition of read-write consistency *)
type rw_consistent_operational = 
  l:memory_op_log{forall (i:log_index l). 
                    is_read_op l i ==> 
                    read_value l i = last_write_value_or_null (prefix l i) (address_at_idx l i)}

(* operational consistency implies rw_consistency based on naive verifier *)
val lemma_rw_consistent_operational_correct (l:rw_consistent_operational):
  Lemma (rw_consistent l)
