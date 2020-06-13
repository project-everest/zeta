module Veritas.Verifier

open FStar.Seq
open FStar.BitVector
open FStar.Classical
open Veritas.SeqAux
open Veritas.Memory
open Veritas.BinTree
open Veritas.BinTreePtr
open Veritas.MerkleAddr
open Veritas.Verifier.Defs

(*
 * The verifier consumes a log that consists of memory operations and
 * additional "proof" objects and returns success of failure; we prove
 * that if the verifier returns success, then the underlying memory
 * operations are read-write consistent
 *)

(* Each entry of the verifier log *)
type verifier_log_entry =
  | MemoryOp: o:memory_op -> verifier_log_entry
  | AddM: a:merkle_addr -> v:merkle_payload -> a':merkle_addr -> verifier_log_entry
  | EvictM: a:merkle_addr -> a':merkle_addr -> verifier_log_entry

(* single verifier log *)
type verifier_log = seq verifier_log_entry

(* index in the verifier log *)
type vl_index (l:verifier_log) = seq_index l

(* verifier state is a subset of merkle_addr, merkle_payloads *)
type verifier_state = (a:merkle_addr) -> option (merkle_payload_of_addr a)
