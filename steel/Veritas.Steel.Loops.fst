module Veritas.Steel.Loops
open Steel.Memory
open Steel.Effect.Common
open Steel.Effect
open Steel.Reference
module AT = Steel.Effect.Atomic
module U32 = FStar.UInt32
let nat_at_most (f:U32.t) = x:nat{ x <= U32.v f }
let u32_between (s f:U32.t) = x:U32.t { U32.v s <= U32.v x /\ U32.v x < U32.v f}

let as_nat_at_most #start #finish (i:u32_between start finish)
  : nat_at_most finish
  = U32.v i

let next_nat_at_most #start #finish (i:u32_between start finish)
  : nat_at_most finish
  = U32.v i + 1

// let coerce_body_next (start:U32.t)
//                      (finish:U32.t { U32.v start < U32.v finish })
//                      (inv: nat_at_most finish -> vprop)
//                      (body:
//                        (i:u32_between start finish ->
//                                       SteelT unit
//                                       (inv (U32.v i)) //(as_nat_at_most i))
//                                       (fun _ -> inv (U32.v i + 1))))
//                      (start':U32.t {U32.v start' >= U32.v start /\

//                                    }
//                      (i:u32_between (
//     :
//               (inv: nat_at_most finish -> vprop)
//               (body:
//                     (i:u32_between start finish ->
//                           SteelT unit
//                           (inv (U32.v i)) //(as_nat_at_most i))
//                           (fun _ -> inv (U32.v i + 1)))) ///next_nat_at_most i))))

let u32_between_closed start finish =
  u:U32.t{ U32.v start <= U32.v u /\
           U32.v u <= U32.v finish }

val for_loop' (start:U32.t)
              (finish:U32.t { U32.v start <= U32.v finish })
              (current:u32_between_closed start finish)
              (inv: nat_at_most finish -> vprop)
              (body:
                    (i:u32_between start finish ->
                          SteelT unit
                          (inv (U32.v i)) //(as_nat_at_most i))
                          (fun _ -> inv (U32.v i + 1)))) ///next_nat_at_most i))))
  : SteelT unit
      (inv (U32.v current))
      (fun _ -> inv (U32.v finish))

#push-options "--print_implicits --fuel 0 --ifuel 0 --query_stats"

let rec for_loop' start finish current inv body
  = if current = finish then (
       AT.change_equal_slprop (inv _) (inv _);
       AT.return ()
    )
    else (
      let _: squash (U32.v current < U32.v finish) = () in
      body current;
      AT.slassert (inv (U32.v current + 1));
      let current' = U32.(current +^ 1ul) in
      AT.change_equal_slprop (inv (U32.v current + 1))
                             (inv (U32.v current'));
      for_loop' start finish current' inv body
    )


val for_loop (start:U32.t)
             (finish:U32.t { U32.v start <= U32.v finish })
             (inv: nat_at_most finish -> vprop)
             (body:
                    (i:u32_between start finish ->
                          SteelT unit
                          (inv (U32.v i))
                          (fun _ -> inv (U32.v i + 1))))
  : SteelT unit
      (inv (U32.v start))
      (fun _ -> inv (U32.v finish))
(* produces 11 queries *)
let for_loop start finish inv body = for_loop' start finish start inv body
