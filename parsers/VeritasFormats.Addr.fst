module VeritasFormats.Addr

module V = Veritas.Memory
module LP = LowParse.Spec.Combinators
module LPB = LowParse.SLow.BitVector

let addr_parser = LP.weaken addr_parser_kind (LPB.parse_bv V.addr_size)

let addr_serializer = LP.serialize_weaken addr_parser_kind (LPB.serialize_bv V.addr_size)

let addr_bytesize x = Seq.length (LP.serialize addr_serializer x)

let addr_bytesize_eq x = ()

module LS = LowParse.SLow.Combinators

let addr_parser32 = LS.parse32_weaken addr_parser_kind (LPB.parse32_bv V.addr_size)

let addr_serializer32 = LS.serialize32_weaken addr_parser_kind (LPB.serialize32_bv V.addr_size)

let addr_size32 = LS.size32_weaken addr_parser_kind (LPB.size32_bv V.addr_size)
