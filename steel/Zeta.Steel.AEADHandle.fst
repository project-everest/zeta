module Zeta.Steel.AEADHandle
module G = Zeta.Steel.Globals
module AEAD = EverCrypt.AEAD
module R = Steel.ST.Reference
module A = Steel.ST.Array
module NullableRef = Steel.Reference
open Steel.ST.Util

inline_for_extraction
noextract
let get_aead_key (_:unit)
  : STAtomicUT perm Set.empty
      emp
      (fun p -> A.pts_to G.aead_key_buffer p G.aead_key)
  =  let open G in
     let body (_:unit)
       : STGhostT perm (add_inv Set.empty aead_key_inv)
           (exists_ (fun p -> A.pts_to aead_key_buffer p aead_key) `star` emp)
           (fun q -> exists_ (fun p -> A.pts_to aead_key_buffer p aead_key) `star` 
                  A.pts_to aead_key_buffer q aead_key)
       = let p = elim_exists () in
         A.share G.aead_key_buffer p (half_perm p) (half_perm p);
         intro_exists (half_perm p) (fun p -> A.pts_to aead_key_buffer p aead_key);
         half_perm p
     in
     let x = with_invariant_g aead_key_inv body in Ghost.reveal x


noeq
type aead_handle_t = {
   aead_state : NullableRef.ref AEAD.state_s;
   aead_state_inv : inv (AEAD.state_inv aead_state G.aead_key)
}

let init_aead_handle () 
  : STT aead_handle_t emp (fun _ -> emp)
  = R.with_local #(NullableRef.ref AEAD.state_s) NullableRef.null (fun dst ->
       assert_ (R.pts_to dst full_perm NullableRef.null);
       let p = get_aead_key () in
       let err = AEAD.create_in #0uy dst G.aead_key_buffer in
       drop (A.pts_to G.aead_key_buffer _ _);       
       let _st = elim_exists () in
       let st = R.read dst in
       intro_exists_erased _st (R.pts_to dst full_perm);       
       if err = 0uy
       then (
         rewrite (AEAD.maybe_vprop _ _)
                 (AEAD.state_inv st G.aead_key);
         let inv = new_invariant (AEAD.state_inv st G.aead_key) in
         let hdl = {
             aead_state = st;
             aead_state_inv = inv
         } in
         return hdl
       )
       else (
         rewrite (AEAD.maybe_vprop _ _) emp;
         let _ = G.abort "Failed AEAD initialization" in
         return (false_elim ())
       )
    )
    

#push-options "--warn_error '-272'" //intentional top-level effect
let aead_handle : aead_handle_t = init_aead_handle ()
#pop-options

let get_aead_state (_:unit)
  : STT (NullableRef.ref AEAD.state_s)
        emp
        (fun p -> AEAD.state_inv p G.aead_key)
  =  let body (_:unit)
       : STGhostT unit
                  (add_inv Set.empty aead_handle.aead_state_inv)
                  (AEAD.state_inv aead_handle.aead_state G.aead_key `star` emp)
                  (fun _ -> AEAD.state_inv aead_handle.aead_state G.aead_key `star`
                         AEAD.state_inv aead_handle.aead_state G.aead_key)
       = AEAD.dup_state_inv _ _
     in
     let _ = with_invariant_g aead_handle.aead_state_inv body in
     return aead_handle.aead_state
