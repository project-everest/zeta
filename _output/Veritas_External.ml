open Hacl_star

let sha2_256 (input: FStar_Bytes.bytes): FStar_Bytes.bytes =
  let out = Bytes.make 256 'x' in
  EverCrypt.SHA2_256.hash (Bytes.unsafe_of_string input) out;
  Bytes.unsafe_to_string out
