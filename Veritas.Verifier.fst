module Veritas.Verifier

open FStar.Seq
open FStar.BitVector
open FStar.Classical
open Veritas.SeqAux
open Veritas.Memory
open Veritas.BinTree
open Veritas.BinTreePtr
open Veritas.MerkleAddr

(* Size of a hash value *)
let hash_size = 256

(* hash_value - bit vector of a specified size *)
type hash_value = bv_t hash_size

(* 
 * information stored in a merkle node about a descendant
 * either Empty indicating no descendants or a descendant addr and hash
 * When not empty, there is also a bit storing if the descendant was evicted 
 * into blum scheme
 *)
type desc_hash = 
  | Empty: desc_hash
  | Desc: a:merkle_addr -> h:hash_value -> b:bool -> desc_hash

(* payload of a merkle addr *)
type merkle_payload = 
  | SMkLeaf: value:payload -> merkle_payload
  | SMkInternal: left:desc_hash -> right:desc_hash -> merkle_payload

(* merkle hash function maps a merkle payload to a hash value *)
val mhashfn (m:merkle_payload): Tot hash_value

let is_payload_of_addr (a:merkle_addr) (p:merkle_payload): Tot bool =
  if is_merkle_leaf a then SMkLeaf? p 
  else SMkInternal? p

(* merkle payload type conditioned on the address *)
type merkle_payload_of_addr (a:merkle_addr) = 
  p:merkle_payload{is_payload_of_addr a p}

(* An internal node merkle payload *)
type merkle_payload_internal = p:merkle_payload {SMkInternal? p}

(* get descendant hash of a specified direction (left|right) *)
let desc_hash_dir (c: bin_tree_dir) (p:merkle_payload_internal): desc_hash = 
  match c with
  | Left -> SMkInternal?.left p
  | Right -> SMkInternal?.right p



(*
 * The verifier consumes a log that consists of memory operations and
 * additional "proof" objects and returns success of failure; we prove
 * that if the verifier returns success, then the underlying memory
 * operations are read-write consistent
 *)

(* Each entry of the verifier log *)
type verifier_log_entry =
  | MemoryOp: o:memory_op -> verifier_log_entry
  | MAdd: a:merkle_addr -> v:merkle_payload -> a':merkle_addr -> verifier_log_entry
  | MEvict: a:merkle_addr -> a':merkle_addr -> verifier_log_entry


type verifier_log = seq verifier_log_entry

(* index in the verifier log *)
type vl_index (l:verifier_log) = seq_index l
