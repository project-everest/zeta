module EverCrypt.AEAD
open Steel.ST.Util
module StRef = Steel.ST.Reference
module NullableRef = Steel.Reference
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




// /**
// Create the required AEAD state for the algorithm.

// Note: The caller must free the AEAD state by calling `EverCrypt_AEAD_free`.

// @param a The argument `a` must be either of:
//   * `Spec_Agile_AEAD_AES128_GCM` (KEY_LEN=16),
//   * `Spec_Agile_AEAD_AES256_GCM` (KEY_LEN=32), or
//   * `Spec_Agile_AEAD_CHACHA20_POLY1305` (KEY_LEN=32).
// @param dst Pointer to a pointer where the address of the allocated AEAD state will be written to.
// @param k Pointer to `KEY_LEN` bytes of memory where the key is read from. The size depends on the used algorithm, see above.

// @return The function returns `EverCrypt_Error_Success` on success or
//   `EverCrypt_Error_UnsupportedAlgorithm` in case of a bad algorithm identifier.
//   (See `EverCrypt_Error.h`.)
// */
// EverCrypt_Error_error_code
// EverCrypt_AEAD_create_in(Spec_Agile_AEAD_alg a, EverCrypt_AEAD_state_s **dst, uint8_t *k);

val state_s : Type0

val state_inv (s:NullableRef.ref state_s)
              (k_bytes:bytes)
  : vprop

val dup_state_inv (#o:_)
                  (s:NullableRef.ref state_s)
                  (k:bytes)
  : STGhostT unit o
    (state_inv s k)
    (fun _ -> state_inv s k `star` state_inv s k)
    
let maybe_vprop (b:bool) (p:vprop) = if b then p else emp

val create_in (#a:_ { a == 0uy (* Spec.Agile.AEAD.AES128_GCM *) })
              (dst:StRef.ref (NullableRef.ref state_s))
              (#k_bytes:ebytes { Seq.length k_bytes == key_size })
              (#k_p:perm)
              (k:A.array U8.t)
  : STT error_code
        (A.pts_to k k_p k_bytes `star`
         exists_ (StRef.pts_to dst full_perm))
        (fun err ->
          A.pts_to k k_p k_bytes `star`
          exists_ (fun s_ptr -> 
            StRef.pts_to dst full_perm s_ptr `star`
            maybe_vprop (err = 0uy) (state_inv s_ptr k_bytes)))
          

// /**
// Encrypt and authenticate a message (`plain`) with associated data (`ad`).

// @param s Pointer to the The AEAD state created by `EverCrypt_AEAD_create_in`. It already contains the encryption key.
// @param iv Pointer to `iv_len` bytes of memory where the nonce is read from.
// @param iv_len Length of the nonce. Note: ChaCha20Poly1305 requires a 12 byte nonce.
// @param ad Pointer to `ad_len` bytes of memory where the associated data is read from.
// @param ad_len Length of the associated data.
// @param plain Pointer to `plain_len` bytes of memory where the to-be-encrypted plaintext is read from.
// @param plain_len Length of the to-be-encrypted plaintext.
// @param cipher Pointer to `plain_len` bytes of memory where the ciphertext is written to.
// @param tag Pointer to `TAG_LEN` bytes of memory where the tag is written to.
//   The length of the `tag` must be of a suitable length for the chosen algorithm:
//   * `Spec_Agile_AEAD_AES128_GCM` (TAG_LEN=16)
//   * `Spec_Agile_AEAD_AES256_GCM` (TAG_LEN=16)
//   * `Spec_Agile_AEAD_CHACHA20_POLY1305` (TAG_LEN=16)

// @return `EverCrypt_AEAD_encrypt` may return either `EverCrypt_Error_Success` or `EverCrypt_Error_InvalidKey` (`EverCrypt_error.h`). The latter is returned if and only if the `s` parameter is `NULL`.
// */
// EverCrypt_Error_error_code
// EverCrypt_AEAD_encrypt(
//   EverCrypt_AEAD_state_s *s,
//   uint8_t *iv,
//   uint32_t iv_len,
//   uint8_t *ad,
//   uint32_t ad_len,
//   uint8_t *plain,
//   uint32_t plain_len,
//   uint8_t *cipher,
//   uint8_t *tag
// );


val encrypt (#k_bytes:ebytes { Seq.length k_bytes == key_size })
            (s:NullableRef.ref state_s)
            (#iv_p:perm)
            (#iv_bytes:ebytes { Seq.length iv_bytes == iv_size })
            (iv:A.array U8.t)
            (iv_len:U32.t { U32.v iv_len == iv_size } )
            (#in_p:perm)
            (#in_bytes:ebytes)
            (input:A.array U8.t)
            (input_len:U32.t { A.length input == U32.v input_len /\
                               U32.v input_len <= max_input_length /\ 
                               Seq.length in_bytes == U32.v input_len })
            (plain_unused:NullableRef.ref U8.t { plain_unused == NullableRef.null }) (* We're not using plain *)
            (plain_len:U32.t { plain_len = 0ul })
            (cipher_unused:NullableRef.ref U8.t { cipher_unused == NullableRef.null }) (* We're not using cipher *)
            (tag:A.array U8.t { A.length tag == 16 })
  : STT error_code
    (requires
       state_inv s k_bytes `star`
       A.pts_to iv iv_p iv_bytes `star`
       A.pts_to input in_p in_bytes `star`
       exists_ (A.pts_to tag full_perm))
    (ensures fun res ->
       state_inv s k_bytes `star`
       A.pts_to iv iv_p iv_bytes `star`
       A.pts_to input in_p in_bytes `star`
       exists_ (fun out ->
         A.pts_to tag full_perm out `star`
         pure (res == 0uy ==>  out == spec k_bytes iv_bytes in_bytes)))


(** THE NO CHECK INTERFACE **)

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
      (plain_unused:NullableRef.ref U8.t { plain_unused == NullableRef.null }) (* We're not using plain *)
      (plain_len:U32.t { plain_len = 0ul })
      (cipher_unused:NullableRef.ref U8.t { cipher_unused == NullableRef.null }) (* We're not using cipher *)
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
