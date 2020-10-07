module Veritas.VCell

/// JP: technically VCell is in the VerifierTr and can be specialized at
/// compile-time. However, there's only two ways in the C++ code to create a
/// VerifierTr, and that's either VerifierTrBuild (veritas/utils/utils.h) or
/// DummyServerTrBuilder (duplicated in a couple places). Both of these builders
/// always pick ``using VCell = VCellInt64Int64<HashTr>`` so let's not be
/// over-generic and let's simply implement VCell here. We can always
/// parameterize the verified development over the representation of VCell
/// later.
///
/// Implementation of a VCell, from veritas/utils/tvcell.h
///
/// This C++ module makes a number of interesting assumptions, for instance, it
/// hardcodes the use of a 256-bit hash function.

let payload = UInt64.t
let addr = UInt64.t

let null_payload: payload = 0UL

/// Hasher and HashValue appear as template parameters in the C++ code but they
/// are not used for the choice of representation, so this saves us from having
/// to use an index for this type.
type t = {
  addr: addr;
  payload: payload
}

