module Veritas.Memory

open FStar.BitVector

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

(* Memory: mapping from address to payload *)
type memory = addr -> payload

(* Memory operation is either a read or a write *)
type memory_op = 
  (* Read operation reading a value v at address a *)
  | Read: a:addr -> v:payload -> memory_op  
  (* Write operation writing a value v at address a *)
  | Write: a:addr -> v:payload -> memory_op

(* Log is a sequence (list) of memory operations *)
type memory_op_log = list memory_op

(* Initial state of memory - all addresses have Null *)
let init_memory:memory = fun _ -> Null

(* apply function for memory *)
let apply (m:memory) (o:memory_op): Tot memory = 
match o with
  | Read a v -> m
  | Write a v -> (fun a' -> if a' = a then v else m a') 

(* read-write consistency of a log with respect to an initial state of memory*)
let rec rw_consistent_helper (m:memory) (l:memory_op_log): Tot bool =
match l with
  | [] -> true
  | op::l' -> if Read? op 
             then (Read?.v op = m (Read?.a op)) && rw_consistent_helper m l'
             else rw_consistent_helper (apply m op) l'

(*
 * read-write consistency starting from the initial state where all 
 * addresses are initialized to Null
 *)
let rw_consistent (l:memory_op_log): Tot bool = rw_consistent_helper init_memory l

