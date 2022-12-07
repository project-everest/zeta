module Zeta.Steel.Globals
open Steel.ST.Util
module A = Steel.ST.Array
module U8 = FStar.UInt8

let aead_key_len = 16
let aead_key_t = Seq.lseq U8.t aead_key_len
let aead_key_buffer_t = k:A.array U8.t { A.length k == aead_key_len }

val aead_key : k:Ghost.erased (Seq.seq U8.t) { Seq.length k == aead_key_len }
val aead_key_buffer : aead_key_buffer_t
val aead_key_inv : inv (exists_ (fun p -> A.pts_to aead_key_buffer p aead_key))

let blake_key_len = 32
let blake_key_t = Seq.lseq U8.t blake_key_len
let blake_key_buffer_t = k:A.array U8.t { A.length k == blake_key_len }

val blake_key : k:Ghost.erased (Seq.seq U8.t) { Seq.length k == blake_key_len }
val blake_key_buffer : blake_key_buffer_t
val blake_key_inv : inv (exists_ (fun p -> A.pts_to blake_key_buffer p blake_key))
