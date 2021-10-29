module Zeta.Steel.Log
module T = Zeta.Formats.Types
module A = Steel.Array
module U8 = FStar.UInt8
module U32 = FStar.UInt32
open Steel.Memory
open Steel.Effect

(* Some utilities *)
let rmem_coerce (#p #q:vprop) (h:rmem p { p == q}) : rmem q = h
let array_sel (a:A.array U8.t) (h:rmem (A.varray a))
  : GTot (Seq.seq U8.t)
  = A.asel a h

(* The underlying spec-level representation of a log *)
let repr = Ghost.erased (Seq.seq T.vlog_entry)

(* Some utilities to work with reprs *)
let empty_log : repr = Seq.empty
let snoc_log (r:repr) (e:T.vlog_entry) : repr = Seq.snoc r e

(* A relation between raw bytes and their repr *)
val parsed (s:Seq.seq U8.t) (r:repr) : Type0


(* [log] : The main abstract type of this module

   Internally, it is represented as a quadruple
     * a: An array of bytes
     * l: length of the array
     * p: ref (n:U32.t{n <= l}), a mutable current position in the array,
     * g: A ghost reference of a sequence of log entries
*)
val log : Type0

val log_len (l:log) : U32.t

val log_array (l:log) : A.array U8.t

(* [log_with_parsed_prefix] : The main representation predicate

   Internally, it states:
     * varray a: Permission on the underlying array

     * vptr p: Permision on the current position

     * vghostpr g: Permission on the ghost ref

     * an invariant stating that the array is validated from 0 to p,
       and current value of g is parsed prefix of a
*)
val log_with_parsed_prefix (l:log) (s:repr) : vprop

(* To create a log, call initialize log with an array of bytes *)
val initialize_log (len:U32.t) (a:A.array U8.t)
  : Steel log
    (A.varray a)
    (fun l -> log_with_parsed_prefix l empty_log)
    (requires fun _ ->
      A.length a == U32.v len)
    (ensures fun _ l _ ->
      log_len l == len /\
      log_array l == a)

(* The main idea of the interface is that one can repeatedly call
   read_next to try to read the next entry from the log.

   When the log is fully read, we return a **pure predicate**
   [parsed_log l s] which witnesses that the content of the log was
   exactly s.
*)

(*
  [parsed_log_inv l s]: This is implemented as a Steel invariant.

      exists (i:iname). i >--> parsed_log l s

  where parsed_log l s : slprop =
        pure (Seq.length s = log_len l) `star` l.g `pts_to` s

  i.e., that the ghost ref of l points to the sequence

  Because I need this invariant, I'm using indexed slprops
  rather than selectors
*)
val parsed_log_inv (l:log)
                   (s:repr)
  : Type0

(* [read_result]: Three potential results from trying to read an entry *)
noeq
type read_result =
  | Finished
  | Parsed_with_maybe_more of T.vlog_entry
  | Failed:  pos:U32.t -> msg:string -> read_result

let read_next_provides (s:repr) (l:log) (o:read_result)
  : vprop
  = match o with
    | Finished -> A.varray (log_array l)
    | Parsed_with_maybe_more e -> log_with_parsed_prefix l (snoc_log s e)
    | Failed pos _ -> A.varray (log_array l)

(* [read_next]:
    - To call [read_next], the caller needs to own the `log_with_parsed_prefix` permission
    - In return, there are three cases

      * If the log is finished, we return an invariant showing that
        the log contained s and return back permission on the
        underyling array to the caller. Internally, we will also
        deallocate any other state, notably the pointer to the current
        position

      * If we successfully parse another entry, we return it,
        extending the parsed prefix.

      * If parsing fails, we deallocate our internal state, return
        permission to the underlying array, and signal back a position
        at which parsing failed and an error message.
*)
val read_next (#s:repr)
              (l:log)
  : Steel read_result
    (log_with_parsed_prefix l s)
    (read_next_provides s l)
    (requires fun _ -> True)
    (ensures fun _ o h1 ->
      match o with
      | Finished ->
        //The entries we parsed is stable and fixed to s
        parsed_log_inv l s /\
        //and s is the parse of the contents of the array in state h1
        parsed (array_sel (log_array l) (rmem_coerce h1)) s
      | Parsed_with_maybe_more e -> True
      | Failed pos _ -> U32.(pos <^ log_len l))

(* And dispose to unconditionally just drop the log and
   return the underlying array *)
val dispose (#s:repr)
            (l:log)
  : SteelT unit
    (log_with_parsed_prefix l s)
    (fun _ -> A.varray (log_array l))
