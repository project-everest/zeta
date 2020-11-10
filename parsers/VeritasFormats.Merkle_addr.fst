module VeritasFormats.Merkle_addr

module V = Veritas.MerkleAddr
module VM = Veritas.Memory
module BT = Veritas.BinTree
module BV = FStar.BitVector
module LPB = LowParse.SLow.BitVector
module Seq = FStar.Seq

let dbt (depth: nat) : Tot Type0 = (x: BT.bin_tree_node { BT.depth x == depth })

let rec synth_merkle_addr'
  (n: nat)
  (x: BV.bv_t n)
: Tot (dbt n)
= if n = 0
  then BT.Root
  else if Seq.index x 0
  then BT.LeftChild (synth_merkle_addr' (n - 1) (Seq.slice x 1 n))
  else BT.RightChild (synth_merkle_addr' (n - 1) (Seq.slice x 1 n))

let rec synth_merkle_addr_recip'
  (n: nat)
  (x: dbt n)
: Tot (BV.bv_t n)
= match x with
  | BT.Root -> Seq.empty
  | BT.LeftChild x' -> Seq.cons true (synth_merkle_addr_recip' (n - 1) x')
  | BT.RightChild x' -> Seq.cons false (synth_merkle_addr_recip' (n - 1) x')

#push-options "--z3rlimit 16"

let rec synth_merkle_addr'_synth_merkle_addr_recip'
  (n: nat)
  (x: dbt n)
: Lemma
  (synth_merkle_addr' n (synth_merkle_addr_recip' n x) == x)
= match x with
  | BT.Root -> ()
  | BT.LeftChild x' ->
    synth_merkle_addr'_synth_merkle_addr_recip' (n - 1) x' ;
    assert (Seq.slice (synth_merkle_addr_recip' n x) 1 n `Seq.equal` synth_merkle_addr_recip' (n - 1) x')
  | BT.RightChild x' ->
    synth_merkle_addr'_synth_merkle_addr_recip' (n - 1) x' ;
    assert (Seq.slice (synth_merkle_addr_recip' n x) 1 n `Seq.equal` synth_merkle_addr_recip' (n - 1) x')

let rec synth_merkle_addr_recip'_synth_merkle_addr'
  (n: nat)
  (x: BV.bv_t n)
: Lemma
  (synth_merkle_addr_recip' n (synth_merkle_addr' n x) `Seq.equal` x)
= if n = 0
  then ()
  else synth_merkle_addr_recip'_synth_merkle_addr' (n - 1) (Seq.slice x 1 n)

#pop-options

module U32 = FStar.UInt32

let synth_merkle_addr
  (x: LPB.bounded_bv_t 0 VM.addr_size)
: Tot merkle_addr
= synth_merkle_addr' (U32.v (dfst x)) (dsnd x)

let synth_merkle_addr_recip
  (x: merkle_addr)
: Tot (LPB.bounded_bv_t 0 VM.addr_size)
= let depth = BT.depth x in
  (| U32.uint_to_t depth, synth_merkle_addr_recip' depth x |)

module LP = LowParse.SLow.Combinators

let synth_merkle_addr_injective : squash (LP.synth_injective synth_merkle_addr) =
  LP.synth_inverse_intro' synth_merkle_addr_recip synth_merkle_addr (fun (x: LPB.bounded_bv_t 0 VM.addr_size) ->
    synth_merkle_addr_recip'_synth_merkle_addr' (U32.v (dfst x)) (dsnd x)
  )

let synth_merkle_addr_inverse : squash (LP.synth_inverse synth_merkle_addr synth_merkle_addr_recip) =
  LP.synth_inverse_intro' synth_merkle_addr synth_merkle_addr_recip (fun (x: merkle_addr) ->
    synth_merkle_addr'_synth_merkle_addr_recip' (BT.depth x) x
  )

module LPI = LowParse.SLow.BoundedInt

let merkle_addr_parser =
  LP.parse_synth (LPB.parse_bounded_bv 0 VM.addr_size (LPI.parse_bounded_int32 0 VM.addr_size)) synth_merkle_addr

let merkle_addr_serializer =
  LP.serialize_synth
    _
    synth_merkle_addr
    (LPB.serialize_bounded_bv 0 VM.addr_size (LPI.serialize_bounded_int32 0 VM.addr_size))
    synth_merkle_addr_recip
    ()

let merkle_addr_bytesize x = Seq.length (LP.serialize merkle_addr_serializer x)

let merkle_addr_bytesize_eq x = ()

let merkle_addr_parser32 =
  LP.parse32_synth'
    _
    synth_merkle_addr
    (LPB.parse32_bounded_bv 0 VM.addr_size (LPI.parse32_bounded_int32 0ul (U32.uint_to_t VM.addr_size)))
    ()

let merkle_addr_serializer32 =
  LP.serialize32_synth
    _
    synth_merkle_addr
    _
    (LPB.serialize32_bounded_bv 0 VM.addr_size (LPI.serialize32_bounded_int32 0ul (U32.uint_to_t VM.addr_size)))
    synth_merkle_addr_recip
    (fun x -> synth_merkle_addr_recip x)
    ()

let merkle_addr_size32 =
  LP.size32_synth
    _
    synth_merkle_addr
    _
    (LPB.size32_bounded_bv 0 VM.addr_size (LPI.size32_constant (LPI.serialize_bounded_int32 0 VM.addr_size) 2ul ()))
    synth_merkle_addr_recip
    (fun x -> synth_merkle_addr_recip x)
    ()
