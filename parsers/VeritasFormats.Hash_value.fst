module VeritasFormats.Hash_value

module V = Veritas.SparseMerkle
module LP = LowParse.Spec.Combinators
module LPB = LowParse.SLow.BitVector

let hash_value_parser = LP.weaken hash_value_parser_kind (LPB.parse_bv V.hash_size)

let hash_value_serializer = LP.serialize_weaken hash_value_parser_kind (LPB.serialize_bv V.hash_size)

let hash_value_bytesize x = Seq.length (LP.serialize hash_value_serializer x)

let hash_value_bytesize_eq x = ()

module LS = LowParse.SLow.Combinators

let hash_value_parser32 = LS.parse32_weaken hash_value_parser_kind (LPB.parse32_bv V.hash_size)

let hash_value_serializer32 = LS.serialize32_weaken hash_value_parser_kind (LPB.serialize32_bv V.hash_size)

let hash_value_size32 = LS.size32_weaken hash_value_parser_kind (LPB.size32_bv V.hash_size)
