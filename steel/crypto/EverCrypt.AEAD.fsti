module EverCrypt.AEAD
open Steel.ST.Util
module R = Steel.Reference
module A = Steel.ST.Array
module U32 = FStar.UInt32
module S = FStar.SizeT
module U8 = FStar.UInt8

let error_code = U8.t

inline_for_extraction noextract
let key_size = 16

inline_for_extraction noextract
let iv_size = 96

inline_for_extraction noextract
let tag_size = 16

inline_for_extraction noextract
let bytes = Seq.seq U8.t

inline_for_extraction noextract
let ebytes = Ghost.erased bytes

inline_for_extraction noextract
let lbytes l = s:bytes { Seq.length s = l }

inline_for_extraction noextract
let max_input_length = pow2 31 - 1

val spec (k_bytes:lbytes key_size)
         (iv_bytes:lbytes 96)
         (in_bytes:bytes { Seq.length in_bytes <=  max_input_length })
  : GTot (lbytes tag_size)


(* This is the C interface that we're trying to call from Steel 

  EverCrypt_Error_error_code
  EverCrypt_AEAD_encrypt_expand_aes128_gcm_no_check(
    uint8_t *k,
    uint8_t *iv,
    uint32_t iv_len,
    uint8_t *ad,
    uint32_t ad_len,
    uint8_t *plain,
    uint32_t plain_len,
    uint8_t *cipher,
    uint8_t *tag
  );
*)

val encrypt_expand_aes128_gcm_no_check
      (#k_p:perm)
      (#k_bytes:ebytes { Seq.length k_bytes == key_size })
      (k:A.array U8.t)
      (#iv_p:perm)
      (#iv_bytes:ebytes { Seq.length iv_bytes == iv_size })
      (iv:A.array U8.t)
      (iv_len:U32.t { U32.v iv_len == iv_size } )
      (#in_p:perm)
      (#in_bytes:ebytes)
      (input:A.array U8.t)  //Any constraint on size of input?
      (input_len:U32.t { A.length input == U32.v input_len /\
                         U32.v input_len <= max_input_length /\ 
                         Seq.length in_bytes == U32.v input_len })
      (plain_unused:R.ref U8.t { plain_unused == R.null }) (* We're not using plain *)
      (plain_len:U32.t { plain_len = 0ul })
      (cipher_unused:R.ref U8.t { cipher_unused == R.null }) (* We're not using cipher *)
      (tag:A.array U8.t { A.length tag == 16 })
  : STT error_code
    (requires
       A.pts_to k k_p k_bytes `star`
       A.pts_to iv iv_p iv_bytes `star`
       A.pts_to input in_p in_bytes `star`
       exists_ (A.pts_to tag full_perm))
    (ensures fun res ->
      A.pts_to k k_p k_bytes `star`
      A.pts_to iv iv_p iv_bytes `star`
      A.pts_to input in_p in_bytes `star`
      exists_ (fun out ->
        A.pts_to tag full_perm out `star`
        pure (res == 0uy ==>  out == spec k_bytes iv_bytes in_bytes)))
