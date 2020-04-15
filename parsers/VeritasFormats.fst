module VeritasFormats

module LP = LowParse.SLow.Combinators

let lp_payload_to_payload
  (x: VeritasFormats.Payload.payload)
: Tot Veritas.Memory.payload
= match x with
  | VeritasFormats.Payload.Body_Null _ -> Veritas.Memory.Null
  | VeritasFormats.Payload.Body_Value v -> Veritas.Memory.Value v

let payload_to_lp_payload
  (x: Veritas.Memory.payload)
: Tot VeritasFormats.Payload.payload
= match x with
  | Veritas.Memory.Null -> VeritasFormats.Payload.Body_Null ()
  | Veritas.Memory.Value v -> VeritasFormats.Payload.Body_Value v

let lp_payload_to_payload_injective : squash (LP.synth_injective lp_payload_to_payload) = ()

let lp_payload_to_payload_inverse : squash (LP.synth_inverse lp_payload_to_payload payload_to_lp_payload) = ()

let lp_memory_op_to_memory_op
  (x: VeritasFormats.Memory_op.memory_op)
: Tot Veritas.Memory.memory_op
= match x.VeritasFormats.Memory_op.kind with
  | VeritasFormats.Memory_op_kind.Read -> Veritas.Memory.Read (x.VeritasFormats.Memory_op.a) (lp_payload_to_payload x.VeritasFormats.Memory_op.v)
  | VeritasFormats.Memory_op_kind.Write -> Veritas.Memory.Write (x.VeritasFormats.Memory_op.a) (lp_payload_to_payload x.VeritasFormats.Memory_op.v)

let lp_memory_op_to_memory_op_injective : squash (LP.synth_injective lp_memory_op_to_memory_op) = ()

let memory_op_to_lp_memory_op
  (x: Veritas.Memory.memory_op)
: Tot VeritasFormats.Memory_op.memory_op
= match x with
  | Veritas.Memory.Read a v -> ({
      VeritasFormats.Memory_op.kind = VeritasFormats.Memory_op_kind.Read;
      VeritasFormats.Memory_op.a = a;
      VeritasFormats.Memory_op.v = payload_to_lp_payload v;
    })
  | Veritas.Memory.Write a v -> ({
      VeritasFormats.Memory_op.kind = VeritasFormats.Memory_op_kind.Write;
      VeritasFormats.Memory_op.a = a;
      VeritasFormats.Memory_op.v = payload_to_lp_payload v;
    })

let lp_memory_op_to_memory_op_inverse : squash (LP.synth_inverse lp_memory_op_to_memory_op memory_op_to_lp_memory_op) = ()

let lp_desc_hash_to_desc_hash
  (x: VeritasFormats.Desc_hash.desc_hash)
: Tot Veritas.SparseMerkle.desc_hash
= match x with
  | VeritasFormats.Desc_hash.Body_EmptyHash _ ->
    Veritas.SparseMerkle.Empty
  | VeritasFormats.Desc_hash.Body_Desc d ->
    Veritas.SparseMerkle.Desc (d.VeritasFormats.Desc_hash_desc.a) (d.VeritasFormats.Desc_hash_desc.hash)

let desc_hash_to_lp_desc_hash
  (x: Veritas.SparseMerkle.desc_hash)
: Tot VeritasFormats.Desc_hash.desc_hash
= match x with
  | Veritas.SparseMerkle.Empty ->
    VeritasFormats.Desc_hash.Body_EmptyHash ()
  | Veritas.SparseMerkle.Desc a hash ->
    VeritasFormats.Desc_hash.Body_Desc ({
      VeritasFormats.Desc_hash_desc.a = a;
      VeritasFormats.Desc_hash_desc.hash = hash;
    })

let lp_desc_hash_to_desc_hash_injective : squash (LP.synth_injective lp_desc_hash_to_desc_hash) = ()

let lp_desc_hash_to_desc_hash_inverse : squash (LP.synth_inverse lp_desc_hash_to_desc_hash desc_hash_to_lp_desc_hash) = ()

let lp_merkle_payload_to_merkle_payload
  (x: VeritasFormats.Merkle_payload.merkle_payload)
: Tot Veritas.SparseMerkle.merkle_payload
= match x with
  | VeritasFormats.Merkle_payload.Body_SMkLeaf pl ->
    Veritas.SparseMerkle.SMkLeaf (lp_payload_to_payload pl)
  | VeritasFormats.Merkle_payload.Body_SMkInternal pi ->
    Veritas.SparseMerkle.SMkInternal
      (lp_desc_hash_to_desc_hash pi.VeritasFormats.Merkle_payload_internal.left)
      (lp_desc_hash_to_desc_hash pi.VeritasFormats.Merkle_payload_internal.right)

let lp_merkle_payload_to_merkle_payload_injective : squash (LP.synth_injective lp_merkle_payload_to_merkle_payload) = ()

let merkle_payload_to_lp_merkle_payload
  (x: Veritas.SparseMerkle.merkle_payload)
: Tot VeritasFormats.Merkle_payload.merkle_payload
= match x with
  | Veritas.SparseMerkle.SMkLeaf pl ->
    VeritasFormats.Merkle_payload.Body_SMkLeaf  (payload_to_lp_payload pl)
  | Veritas.SparseMerkle.SMkInternal left right ->
    VeritasFormats.Merkle_payload.Body_SMkInternal ({
      VeritasFormats.Merkle_payload_internal.left = desc_hash_to_lp_desc_hash left;
      VeritasFormats.Merkle_payload_internal.right = desc_hash_to_lp_desc_hash right;
    })

let lp_merkle_payload_to_merkle_payload_inverse : squash (LP.synth_inverse lp_merkle_payload_to_merkle_payload merkle_payload_to_lp_merkle_payload) = ()

let lp_verifier_log_entry_to_verifier_log_entry
  (x: VeritasFormats.Verifier_log_entry.verifier_log_entry)
: Tot Veritas.SparseMerkleVerifier.verifier_log_entry
= match x with
  | VeritasFormats.Verifier_log_entry.Body_MemoryOp op ->
    Veritas.SparseMerkleVerifier.MemoryOp (lp_memory_op_to_memory_op op)
  | VeritasFormats.Verifier_log_entry.Body_Add y ->
    Veritas.SparseMerkleVerifier.Add
      (y.VeritasFormats.Verifier_log_entry_add.a)
      (lp_merkle_payload_to_merkle_payload y.VeritasFormats.Verifier_log_entry_add.v)
      (y.VeritasFormats.Verifier_log_entry_add.b)
  | VeritasFormats.Verifier_log_entry.Body_Evict y ->
    Veritas.SparseMerkleVerifier.Evict
      (y.VeritasFormats.Verifier_log_entry_evict.a)
      (y.VeritasFormats.Verifier_log_entry_evict.b)

let lp_verifier_log_entry_to_verifier_log_entry_injective : squash (LP.synth_injective lp_verifier_log_entry_to_verifier_log_entry) = ()

let verifier_log_entry_to_lp_verifier_log_entry
  (x: Veritas.SparseMerkleVerifier.verifier_log_entry)
: Tot VeritasFormats.Verifier_log_entry.verifier_log_entry
= match x with
  | Veritas.SparseMerkleVerifier.MemoryOp op ->
    VeritasFormats.Verifier_log_entry.Body_MemoryOp (memory_op_to_lp_memory_op op)
  | Veritas.SparseMerkleVerifier.Add a v b -> 
    VeritasFormats.Verifier_log_entry.Body_Add ({
      VeritasFormats.Verifier_log_entry_add.a = a;
      VeritasFormats.Verifier_log_entry_add.v = merkle_payload_to_lp_merkle_payload v;
      VeritasFormats.Verifier_log_entry_add.b = b;
    })
  | Veritas.SparseMerkleVerifier.Evict a b ->
    VeritasFormats.Verifier_log_entry.Body_Evict ({
      VeritasFormats.Verifier_log_entry_evict.a = a;
      VeritasFormats.Verifier_log_entry_evict.b = b;
    })

let lp_verifier_log_entry_to_verifier_log_entry_inverse : squash (LP.synth_inverse lp_verifier_log_entry_to_verifier_log_entry verifier_log_entry_to_lp_verifier_log_entry) = ()

let parse_entry_kind = VeritasFormats.Verifier_log_entry.verifier_log_entry_parser_kind

let parse_entry_spec =
  VeritasFormats.Verifier_log_entry.verifier_log_entry_parser `LP.parse_synth` lp_verifier_log_entry_to_verifier_log_entry

let serialize_entry_spec =
  LP.serialize_synth
    VeritasFormats.Verifier_log_entry.verifier_log_entry_parser
    lp_verifier_log_entry_to_verifier_log_entry
    VeritasFormats.Verifier_log_entry.verifier_log_entry_serializer
    verifier_log_entry_to_lp_verifier_log_entry
    ()

let parse_entry =
  LP.parse32_synth
    VeritasFormats.Verifier_log_entry.verifier_log_entry_parser
    lp_verifier_log_entry_to_verifier_log_entry
    (fun x -> lp_verifier_log_entry_to_verifier_log_entry x)
    VeritasFormats.Verifier_log_entry.verifier_log_entry_parser32
    ()

let serialize_entry =
  LP.serialize32_synth
    VeritasFormats.Verifier_log_entry.verifier_log_entry_parser
    lp_verifier_log_entry_to_verifier_log_entry
    VeritasFormats.Verifier_log_entry.verifier_log_entry_serializer
    VeritasFormats.Verifier_log_entry.verifier_log_entry_serializer32
    verifier_log_entry_to_lp_verifier_log_entry
    (fun x -> verifier_log_entry_to_lp_verifier_log_entry x)
    ()

// type verifier_log = (l: Veritas.SparseMerkleVerifier.verifier_log { FStar.Seq.length l <= 8388608 })